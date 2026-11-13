# SPDX-FileCopyrightText: 2026 BigBlueButton Inc. and by respective authors
#
# SPDX-License-Identifier: GPL-3.0-or-later

"""Draw the frame that goes around the media of a recording video.

The output is a full size picture with transparent holes where the
presentation, the screen sharing and the webcams are composited by the caller.
Everything is laid out in a 1080 lines tall coordinate system and scaled to the
real video size, so the same numbers work for any output resolution.
"""

import colorsys
import hashlib
import io
import math
import os
import tempfile
import time
import urllib.request
import zlib
from dataclasses import dataclass
from datetime import datetime, timezone
from typing import Any, Dict, List, Optional, Tuple

import cairo
import gi

gi.require_version("GdkPixbuf", "2.0")
gi.require_version("Pango", "1.0")
gi.require_version("PangoCairo", "1.0")
from gi.repository import GdkPixbuf, Pango, PangoCairo

from bbb_presentation_video.overlay.events import ActivityItem, OverlayEvents

try:
    import segno
except ImportError:  # The QR codes of the links are optional
    segno = None

RGB = Tuple[float, float, float]

REFERENCE_HEIGHT = 1080

TEXT: RGB = (0.957, 0.965, 0.980)
TEXT_SOFT: RGB = (0.878, 0.898, 0.933)
MUTED: RGB = (0.604, 0.647, 0.722)
BACKGROUND: RGB = (0.055, 0.075, 0.122)
PANEL: RGB = (0.078, 0.102, 0.153)
CARD: RGB = (0.118, 0.149, 0.220)
SHADE: RGB = (0.04, 0.055, 0.086)
GREEN: RGB = (0.271, 0.851, 0.627)
GREEN_DARK: RGB = (0.020, 0.160, 0.110)
BLUE: RGB = (0.431, 0.659, 0.996)
AMBER: RGB = (0.949, 0.714, 0.353)
RED: RGB = (0.898, 0.282, 0.302)

# Pictures of the users are downloaded once per recording; these keep a slow or
# huge file from holding the video back
AVATAR_TIMEOUT = 5
AVATAR_MAX_BYTES = 4 * 1024 * 1024

AREA_RADIUS = 12
TILE_RADIUS = 10
# How long a new timeline entry takes to slide in, in seconds
ENTER_DURATION = 0.35
COMPACT_KINDS = ("join", "leave", "raise_hand", "reaction")
PRESENCE_KINDS = ("join", "leave")

STRINGS: Dict[str, Dict[str, Any]] = {
    "en": {
        "speaking": "Speaking now",
        "more_webcams": ("+{n} camera", "+{n} cameras"),
        "more_speakers": ("+{n} person", "+{n} people"),
        "activity": "Session activity",
        "participants": ("{n} participant", "{n} participants"),
        "poll": "POLL RESULT",
        "votes": ("{n} vote", "{n} votes"),
        "external_video": "EXTERNAL VIDEO STARTED",
        "shared_by": "Shared by {name}",
        "join": "joined",
        "leave": "left",
        "raise_hand": "raised hand",
        "reaction": "reacted",
        "reaction_chat": "reacted to a message",
        "months": "Jan Feb Mar Apr May Jun Jul Aug Sep Oct Nov Dec".split(),
        "date": "{month} {day}, {year}",
    },
    "pt": {
        "speaking": "Falando agora",
        "more_webcams": ("+{n} câmera", "+{n} câmeras"),
        "more_speakers": ("+{n} pessoa", "+{n} pessoas"),
        "activity": "Atividade da sessão",
        "participants": ("{n} participante", "{n} participantes"),
        "poll": "RESULTADO DA ENQUETE",
        "votes": ("{n} voto", "{n} votos"),
        "external_video": "VÍDEO EXTERNO INICIADO",
        "shared_by": "Compartilhado por {name}",
        "join": "entrou",
        "leave": "saiu",
        "raise_hand": "levantou a mão",
        "reaction": "reagiu",
        "reaction_chat": "reagiu a uma mensagem",
        "months": [],
        "date": "{day:02d}/{month_number:02d}/{year}",
    },
}

WEIGHTS = {
    400: Pango.Weight.NORMAL,
    500: Pango.Weight.MEDIUM,
    600: Pango.Weight.SEMIBOLD,
    700: Pango.Weight.BOLD,
}


def parse_color(value: Optional[str], default: RGB) -> RGB:
    if not value:
        return default
    value = value.lstrip("#")
    if len(value) != 6:
        return default
    try:
        return (
            int(value[0:2], 16) / 255,
            int(value[2:4], 16) / 255,
            int(value[4:6], 16) / 255,
        )
    except ValueError:
        return default


def avatar_color(key: str) -> RGB:
    """A stable, muted color for each user."""
    hue = (zlib.crc32(key.encode("utf-8")) % 360) / 360
    return colorsys.hls_to_rgb(hue, 0.36, 0.32)


def initials(name: str) -> str:
    words = [word for word in name.replace(".", " ").split() if word[0].isalnum()]
    if not words:
        return "?"
    if len(words) == 1:
        return words[0][:2].upper()
    return (words[0][0] + words[1][0]).upper()


def format_clock(seconds: float) -> str:
    total = max(0, int(seconds))
    return f"{total // 3600:02d}:{total % 3600 // 60:02d}:{total % 60:02d}"


def rounded_rect(
    ctx: "cairo.Context[Any]", x: float, y: float, w: float, h: float, r: float
) -> None:
    r = max(0.0, min(r, w / 2, h / 2))
    ctx.new_sub_path()
    ctx.arc(x + w - r, y + r, r, -math.pi / 2, 0)
    ctx.arc(x + w - r, y + h - r, r, 0, math.pi / 2)
    ctx.arc(x + r, y + h - r, r, math.pi / 2, math.pi)
    ctx.arc(x + r, y + r, r, math.pi, math.pi * 3 / 2)
    ctx.close_path()


def bars_icon(
    ctx: "cairo.Context[Any]",
    x: float,
    y: float,
    height: float,
    color: RGB,
    levels: Tuple[float, ...] = (0.45, 1.0, 0.65, 0.3),
) -> float:
    """Draw a small equalizer; returns its width."""
    bar = height / 6
    gap = bar * 1.1
    ctx.save()
    ctx.set_source_rgb(*color)
    ctx.set_line_width(bar)
    ctx.set_line_cap(cairo.LINE_CAP_ROUND)
    for i, level in enumerate(levels):
        bx = x + bar / 2 + i * (bar + gap)
        half = (height - bar) * level / 2
        ctx.move_to(bx, y + height / 2 - half)
        ctx.line_to(bx, y + height / 2 + half)
        ctx.stroke()
    ctx.restore()
    return len(levels) * bar + (len(levels) - 1) * gap


@dataclass
class Rect:
    x: float
    y: float
    width: float
    height: float

    @classmethod
    def from_config(cls, config: Optional[Dict[str, Any]], scale: float) -> "Rect":
        config = config or {}
        return cls(
            config.get("x", 0) / scale,
            config.get("y", 0) / scale,
            config.get("width", 0) / scale,
            config.get("height", 0) / scale,
        )


class OverlayRenderer:
    def __init__(
        self,
        events: OverlayEvents,
        width: int,
        height: int,
        config: Dict[str, Any],
    ):
        self.events = events
        self.width = width
        self.height = height
        self.scale = height / REFERENCE_HEIGHT
        self.config = config

        self.font = str(config.get("font") or "Noto Sans")
        # Colors: the frame (optionally a top to bottom gradient), the activity
        # panel and the cards inside it
        self.background = parse_color(config.get("background"), BACKGROUND)
        self.background_end = parse_color(config.get("background_end"), self.background)
        self.panel = parse_color(config.get("panel"), PANEL)
        self.card = parse_color(config.get("card"), CARD)
        locale = str(config.get("locale") or "en").replace("_", "-").split("-")[0]
        # The texts of the locale; any of them can be replaced in the config
        # ("strings"), which is also how to add a language that is not here
        self.strings = dict(STRINGS.get(locale.lower(), STRINGS["en"]))
        for key, value in (config.get("strings") or {}).items():
            if key in STRINGS["en"]:
                self.strings[key] = value

        scale = self.scale
        self.top_bar = Rect.from_config(config.get("top_bar"), scale)
        self.activity = Rect.from_config(config.get("activity"), scale)
        # Own place for who is speaking; without it, the right of the top bar
        self.speakers = (
            Rect.from_config(config.get("speakers"), scale)
            if config.get("speakers")
            else None
        )
        self.areas = [
            Rect.from_config(area, scale)
            for area in config.get("areas", [])
            if area.get("name") != "webcam"
        ]
        self.webcams = [
            (str(tile.get("user_id") or ""), Rect.from_config(tile, scale))
            for tile in config.get("webcams", [])
        ]
        self.tile_gap = float(config.get("tile_gap", 8))
        # Webcams left out of the video because there are too many of them
        self.hidden_webcams = int(config.get("hidden_webcams") or 0)
        # A small QR code next to the links, to open them with a phone
        self.link_qr_code = bool(config.get("link_qr_code", True))
        # Show the picture of the user (avatarURL of the join request) in the chat
        self.avatars = bool(config.get("avatars", True))
        self.cache_dir = str(
            config.get("cache_dir")
            or os.path.join(tempfile.gettempdir(), "bbb-recording-overlay")
        )
        self._avatars: Dict[str, Optional[cairo.ImageSurface]] = {}
        self.logo = self._load_logo(config.get("logo"))
        self.logo_height = float(config.get("logo_height", 40))
        self.logo_opacity = float(config.get("logo_opacity", 0.9))

        self.surface = cairo.ImageSurface(cairo.FORMAT_ARGB32, width, height)
        self.ctx = cairo.Context(self.surface)
        self.ctx.scale(scale, scale)

        self.date = self._format_date(config.get("timezone"))
        self._state: Any = None
        self._item_cache: Dict[int, cairo.ImageSurface] = {}

    @staticmethod
    def _load_image(filename: str, size: int = 0) -> cairo.ImageSurface:
        """Any image GdkPixbuf can read; with a size, cropped to a square."""
        pixbuf = GdkPixbuf.Pixbuf.new_from_file(filename)
        if size > 0:
            side = min(pixbuf.get_width(), pixbuf.get_height())
            pixbuf = pixbuf.new_subpixbuf(
                (pixbuf.get_width() - side) // 2,
                (pixbuf.get_height() - side) // 2,
                side,
                side,
            ).scale_simple(size, size, GdkPixbuf.InterpType.BILINEAR)
        _ok, data = pixbuf.save_to_bufferv("png", [], [])
        return cairo.ImageSurface.create_from_png(io.BytesIO(data))

    def _load_logo(self, filename: Optional[str]) -> Optional[cairo.ImageSurface]:
        if not filename:
            return None
        try:
            return self._load_image(str(filename))
        except Exception as error:
            print(f"Could not load the logo {filename}: {error}")
            return None

    def _avatar(
        self, user_id: Optional[str], size: float
    ) -> Optional[cairo.ImageSurface]:
        """The picture of the user as a square of the size given, if there is one.

        The file is downloaded to the cache directory the first time. A failed
        download leaves an empty file there, so it is not tried again for every
        cut of the same recording.
        """
        user = self.events.users.get(user_id or "")
        url = user.avatar_url if user is not None and self.avatars else ""
        if not url.lower().startswith(("http://", "https://")):
            return None
        if url in self._avatars:
            return self._avatars[url]

        surface: Optional[cairo.ImageSurface] = None
        name = "avatar-" + hashlib.sha1(url.encode("utf-8")).hexdigest()
        filename = os.path.join(self.cache_dir, name)
        try:
            if not os.path.exists(filename):
                os.makedirs(self.cache_dir, exist_ok=True)
                data = b""
                try:
                    request = urllib.request.Request(
                        url, headers={"User-Agent": "bbb-recording-overlay"}
                    )
                    with urllib.request.urlopen(
                        request, timeout=AVATAR_TIMEOUT
                    ) as response:
                        data = response.read(AVATAR_MAX_BYTES + 1)
                    if len(data) > AVATAR_MAX_BYTES:
                        data = b""
                except Exception as error:
                    print(f"Could not download the avatar {url}: {error}")
                temporary = f"{filename}.{os.getpid()}"
                with open(temporary, "wb") as file:
                    file.write(data)
                os.replace(temporary, filename)
            if os.path.getsize(filename) > 0:
                surface = self._load_image(filename, math.ceil(size * self.scale))
        except Exception as error:
            print(f"Could not use the avatar {url}: {error}")
        self._avatars[url] = surface
        return surface

    # Text helpers

    def _layout(
        self,
        ctx: "cairo.Context[Any]",
        text: str,
        size: float,
        weight: int = 400,
        width: Optional[float] = None,
        lines: int = 1,
        letter_spacing: float = 0,
    ) -> Pango.Layout:
        layout = PangoCairo.create_layout(ctx)
        description = Pango.FontDescription()
        description.set_family(self.font)
        description.set_absolute_size(size * Pango.SCALE)
        description.set_weight(WEIGHTS.get(weight, Pango.Weight.NORMAL))
        layout.set_font_description(description)
        layout.set_text(text, -1)
        if width is not None:
            layout.set_width(int(max(1.0, width) * Pango.SCALE))
            layout.set_wrap(Pango.WrapMode.WORD_CHAR)
            layout.set_ellipsize(Pango.EllipsizeMode.END)
            layout.set_height(-lines)
        if letter_spacing:
            attributes = Pango.AttrList()
            attributes.insert(
                Pango.attr_letter_spacing_new(int(letter_spacing * Pango.SCALE))
            )
            layout.set_attributes(attributes)
        return layout

    @staticmethod
    def _show(
        ctx: "cairo.Context[Any]",
        layout: Pango.Layout,
        x: float,
        y: float,
        color: RGB,
        alpha: float = 1.0,
    ) -> None:
        ctx.set_source_rgba(*color, alpha)
        ctx.move_to(x, y)
        PangoCairo.show_layout(ctx, layout)

    @staticmethod
    def _size(layout: Pango.Layout) -> Tuple[float, float]:
        width, height = layout.get_size()
        return width / Pango.SCALE, height / Pango.SCALE

    def _plural(self, key: str, n: int) -> str:
        singular, plural = self.strings[key]
        return str(singular if n == 1 else plural).format(n=n)

    def _format_date(self, timezone_name: Optional[str]) -> str:
        start = self.events.recording_start_utc()
        if start is None:
            return ""
        tz = None
        if timezone_name:
            try:
                from zoneinfo import ZoneInfo

                tz = ZoneInfo(str(timezone_name))
            except Exception:
                tz = None
        date = datetime.fromtimestamp(start, timezone.utc).astimezone(tz)
        months = self.strings["months"]
        day = str(self.strings["date"]).format(
            day=date.day,
            month=months[date.month - 1] if months else "",
            month_number=date.month,
            year=date.year,
        )
        # The time the recording started, which is not the same as the clock
        # of the elapsed time shown next to the recording mark
        return f"{day} · {date.hour:02d}:{date.minute:02d}"

    def _draw_elapsed(
        self, clock: int, x: float, middle: float, align_right: bool
    ) -> float:
        """The recording mark with the elapsed time. Returns the width."""
        ctx = self.ctx
        layout = self._layout(ctx, format_clock(clock), 15.5, 600)
        text_w, text_h = self._size(layout)
        # Digits change width; keep the pill steady
        text_w = math.ceil(text_w / 6) * 6
        width = 12 + 10 + 8 + text_w + 14
        height = 28.0
        if align_right:
            x -= width
        rounded_rect(ctx, x, middle - height / 2, width, height, height / 2)
        ctx.set_source_rgba(*SHADE, 0.50)
        ctx.fill()
        ctx.arc(x + 12 + 5, middle, 5, 0, 2 * math.pi)
        ctx.set_source_rgb(*RED)
        ctx.fill()
        self._show(ctx, layout, x + 12 + 10 + 8, middle - text_h / 2, TEXT)
        return width

    def _name(self, user_id: str) -> str:
        user = self.events.users.get(user_id)
        return user.name if user is not None and user.name else user_id

    # Frame state

    def _frame_state(self, timestamp: float) -> Any:
        """Everything the picture depends on. Equal states give equal frames."""
        events = self.events
        talking = tuple(events.talking_at(timestamp))
        visible = 0
        entering: List[float] = []
        for item in events.items:
            if item.timestamp > timestamp:
                break
            visible += 1
            age = timestamp - item.timestamp
            if age < ENTER_DURATION:
                entering.append(round(age, 3))
        return (
            int(events.recording_time(timestamp)),
            talking,
            events.participants_at(timestamp),
            visible,
            tuple(entering),
        )

    def render(self, timestamp: float) -> bool:
        """Draw the frame for a meeting timestamp.

        Returns False when the picture is the same as the last one drawn.
        """
        state = self._frame_state(timestamp)
        if state == self._state:
            return False
        self._state = state
        clock, talking, participants, visible, _entering = state

        ctx = self.ctx
        ctx.save()
        ctx.set_operator(cairo.OPERATOR_SOURCE)
        if self.background_end != self.background:
            gradient = cairo.LinearGradient(0, 0, 0, REFERENCE_HEIGHT)
            gradient.add_color_stop_rgb(0, *self.background)
            gradient.add_color_stop_rgb(1, *self.background_end)
            ctx.set_source(gradient)
        else:
            ctx.set_source_rgb(*self.background)
        ctx.paint()

        # Open the holes for the media composited underneath
        ctx.set_operator(cairo.OPERATOR_CLEAR)
        for area in self.areas:
            rounded_rect(ctx, area.x, area.y, area.width, area.height, AREA_RADIUS)
            ctx.fill()
        for _user_id, tile in self.webcams:
            hole = self._tile_hole(tile)
            rounded_rect(ctx, hole.x, hole.y, hole.width, hole.height, TILE_RADIUS)
            ctx.fill()
        ctx.restore()

        self._draw_top_bar(clock, talking)
        self._draw_speakers(talking)
        self._draw_activity(timestamp, participants, visible)
        self._draw_webcam_labels(set(talking))

        self.surface.flush()
        return True

    def _tile_hole(self, tile: Rect) -> Rect:
        inset = self.tile_gap / 2
        return Rect(
            tile.x + inset,
            tile.y + inset,
            tile.width - 2 * inset,
            tile.height - 2 * inset,
        )

    # Top bar

    def _draw_top_bar(self, clock: int, talking: Tuple[str, ...]) -> None:
        bar = self.top_bar
        if bar.width <= 0 or bar.height <= 0:
            return
        ctx = self.ctx
        middle = bar.y + bar.height / 2
        left = bar.x + 24
        right = bar.x + bar.width - 24

        # Who is speaking goes on the right of the bar, unless it has its own place
        if self.speakers is None and bar.width >= 900:
            used = self._draw_speaker_row(
                talking, left + 420, middle - 21, right - left - 420, align_right=True
            )
            if used > 0:
                right -= used + 32
        if bar.width < 900:
            self._draw_top_bar_stacked(clock)
            return

        if self.logo is not None:
            logo_scale = self.logo_height / self.logo.get_height()
            logo_w = self.logo.get_width() * logo_scale
            ctx.save()
            ctx.translate(left, middle - self.logo_height / 2)
            ctx.scale(logo_scale, logo_scale)
            ctx.set_source_surface(self.logo, 0, 0)
            ctx.get_source().set_filter(cairo.FILTER_BEST)
            ctx.paint_with_alpha(self.logo_opacity)
            ctx.restore()
            left += logo_w + 20

        when_layout = self._layout(ctx, self.date, 16.5, 500)
        when_w, when_h = self._size(when_layout)

        title_width = max(120.0, right - left - when_w - 18 - 150)
        title = self._layout(ctx, self.events.meeting_name, 27, 700, width=title_width)
        title_w, title_h = self._size(title)
        title_w = min(title_w, title_width)
        self._show(ctx, title, left, middle - title_h / 2, TEXT)
        self._show(
            ctx, when_layout, left + title_w + 18, middle - when_h / 2 + 3, TEXT, 0.68
        )
        self._draw_elapsed(clock, left + title_w + 18 + when_w + 18, middle + 2, False)

    def _draw_top_bar_stacked(self, clock: int) -> None:
        """A narrow bar: the name, the date and time below it, the logo in the corner."""
        bar = self.top_bar
        ctx = self.ctx
        width = bar.width - 4

        if self.logo is not None:
            logo_scale = self.logo_height / self.logo.get_height()
            logo_w = self.logo.get_width() * logo_scale
            ctx.save()
            ctx.translate(bar.x + bar.width - logo_w, bar.y)
            ctx.scale(logo_scale, logo_scale)
            ctx.set_source_surface(self.logo, 0, 0)
            ctx.get_source().set_filter(cairo.FILTER_BEST)
            ctx.paint_with_alpha(self.logo_opacity)
            ctx.restore()
            width -= logo_w + 16

        title = self._layout(
            ctx, self.events.meeting_name, 21, 700, width=width, lines=2
        )
        _title_w, title_h = self._size(title)
        self._show(ctx, title, bar.x + 4, bar.y - 3, TEXT)

        when_layout = self._layout(ctx, self.date, 16.5, 500)
        _when_w, when_h = self._size(when_layout)
        when_y = bar.y - 3 + title_h + 6
        self._show(ctx, when_layout, bar.x + 4, when_y, TEXT, 0.68)
        # Elapsed time of the recording, on the right of the same line
        self._draw_elapsed(clock, bar.x + bar.width, when_y + when_h / 2, True)

    # Who is speaking

    def _speaker_chip(
        self,
        ctx: "cairo.Context[Any]",
        user_id: str,
        x: float,
        y: float,
        max_width: float,
        draw: bool = True,
        full_width: bool = False,
    ) -> float:
        """One person speaking: picture (or initials) and name. Returns the width."""
        height = 42.0
        avatar = 30.0
        name = self._name(user_id)
        layout = self._layout(
            ctx, name, 16.5, 700, width=max_width - avatar - 6 - 10 - 16
        )
        text_w, text_h = self._size(layout)
        text_w = min(text_w, max_width - avatar - 6 - 10 - 16)
        width = max_width if full_width else 6 + avatar + 10 + text_w + 16
        if not draw:
            return width

        rounded_rect(ctx, x, y, width, height, height / 2)
        ctx.set_source_rgba(*SHADE, 0.60)
        ctx.fill_preserve()
        ctx.set_source_rgba(*GREEN, 0.12)
        ctx.fill_preserve()
        ctx.set_source_rgba(*GREEN, 0.85)
        ctx.set_line_width(1.5)
        ctx.stroke()

        center_x = x + 6 + avatar / 2
        center_y = y + height / 2
        picture = self._avatar(user_id, avatar)
        ctx.arc(center_x, center_y, avatar / 2, 0, 2 * math.pi)
        if picture is not None:
            ctx.save()
            ctx.set_source_rgb(0.93, 0.94, 0.96)
            ctx.fill_preserve()
            ctx.clip()
            ctx.translate(center_x - avatar / 2, center_y - avatar / 2)
            ctx.scale(avatar / picture.get_width(), avatar / picture.get_height())
            ctx.set_source_surface(picture, 0, 0)
            ctx.paint()
            ctx.restore()
        else:
            ctx.set_source_rgb(*avatar_color(user_id or name))
            ctx.fill()
            letters = self._layout(ctx, initials(name), 12, 700)
            letters_w, letters_h = self._size(letters)
            self._show(
                ctx, letters, center_x - letters_w / 2, center_y - letters_h / 2, TEXT
            )
        self._show(ctx, layout, x + 6 + avatar + 10, center_y - text_h / 2, TEXT)
        return width

    def _draw_speaker_row(
        self,
        talking: Tuple[str, ...],
        x: float,
        y: float,
        width: float,
        align_right: bool = False,
    ) -> float:
        """A line with one chip per person speaking. Returns the width used."""
        if not talking or width < 200:
            return 0.0
        ctx = self.ctx
        gap = 10.0
        icon_h = 18.0
        icon_w = icon_h / 6 * 4 + icon_h / 6 * 1.1 * 3
        label = self._layout(ctx, str(self.strings["speaking"]), 14.5, 600)
        label_w, label_h = self._size(label)
        used = icon_w + 10 + label_w + 14

        # As many chips as fit; the others are counted in a last "+N"
        chip_max = 330.0
        widths: List[float] = []
        for index, user_id in enumerate(talking):
            chip_w = self._speaker_chip(ctx, user_id, 0, 0, chip_max, draw=False)
            reserve = 58 if index < len(talking) - 1 else 0
            if used + sum(widths) + gap * len(widths) + chip_w + reserve > width:
                break
            widths.append(chip_w)
        more = len(talking) - len(widths)
        total = used + sum(widths) + gap * max(0, len(widths) - 1)
        if more > 0:
            total += gap + 48

        cursor = x + width - total if align_right else x
        bars_icon(ctx, cursor, y + 21 - icon_h / 2, icon_h, GREEN)
        self._show(
            ctx, label, cursor + icon_w + 10, y + 21 - label_h / 2, (0.72, 0.95, 0.85)
        )
        cursor += used
        for user_id, chip_w in zip(talking, widths):
            self._speaker_chip(ctx, user_id, cursor, y, chip_max)
            cursor += chip_w + gap
        if more > 0:
            rounded_rect(ctx, cursor, y, 48, 42, 21)
            ctx.set_source_rgba(*SHADE, 0.60)
            ctx.fill()
            count = self._layout(ctx, f"+{more}", 15.5, 700)
            count_w, count_h = self._size(count)
            self._show(
                ctx, count, cursor + 24 - count_w / 2, y + 21 - count_h / 2, TEXT
            )
        return total

    def _draw_speakers(self, talking: Tuple[str, ...]) -> None:
        """Who is speaking, in the place given by the layout.

        A short and wide place gets a line of chips; a taller one gets a panel
        with one person per line.
        """
        area = self.speakers
        if area is None or area.width <= 0 or area.height <= 0:
            return
        ctx = self.ctx
        if area.height < 100:
            self._draw_speaker_row(
                talking, area.x, area.y + area.height / 2 - 21, area.width
            )
            return

        rounded_rect(ctx, area.x, area.y, area.width, area.height, AREA_RADIUS)
        ctx.set_source_rgb(*self.panel)
        ctx.fill()
        icon_h = 15.0
        icon_w = icon_h / 6 * 4 + icon_h / 6 * 1.1 * 3
        color = GREEN if talking else MUTED
        bars_icon(ctx, area.x + 16, area.y + 14, icon_h, color)
        label = self._layout(ctx, str(self.strings["speaking"]), 14, 700)
        self._show(ctx, label, area.x + 16 + icon_w + 9, area.y + 12, color)

        y = area.y + 42
        rows = max(1, int((area.y + area.height - 8 - y + 6) // 48))
        shown = talking[:rows] if len(talking) <= rows else talking[: rows - 1]
        for user_id in shown:
            self._speaker_chip(
                ctx, user_id, area.x + 12, y, area.width - 24, full_width=True
            )
            y += 48
        more = len(talking) - len(shown)
        if more > 0:
            count = self._layout(ctx, self._plural("more_speakers", more), 14.5, 600)
            self._show(ctx, count, area.x + 24, y + 10, TEXT_SOFT)

    # Webcams

    def _draw_webcam_labels(self, talking: "set[str]") -> None:
        ctx = self.ctx
        for user_id, tile in self.webcams:
            hole = self._tile_hole(tile)
            speaking = user_id in talking
            if speaking:
                rounded_rect(
                    ctx,
                    hole.x + 1.5,
                    hole.y + 1.5,
                    hole.width - 3,
                    hole.height - 3,
                    TILE_RADIUS - 1,
                )
                ctx.set_source_rgb(*GREEN)
                ctx.set_line_width(3)
                ctx.stroke()

            name = self._name(user_id)
            if not name:
                continue
            icon_h = 13
            icon_w = (icon_h / 6 * 4 + icon_h / 6 * 1.1 * 3 + 6) if speaking else 0
            max_width = hole.width - 16 - 16 - icon_w
            if max_width < 30:
                continue
            layout = self._layout(ctx, name, 14, 600, width=max_width)
            text_w, text_h = self._size(layout)
            text_w = min(text_w, max_width)
            label_w = text_w + 16 + icon_w
            label_h = text_h + 6
            x = hole.x + 8
            y = hole.y + hole.height - 8 - label_h
            rounded_rect(ctx, x, y, label_w, label_h, 6)
            if speaking:
                ctx.set_source_rgb(*GREEN)
            else:
                ctx.set_source_rgba(*SHADE, 0.80)
            ctx.fill()
            text_x = x + 8
            if speaking:
                bars_icon(ctx, text_x, y + (label_h - icon_h) / 2, icon_h, GREEN_DARK)
                text_x += icon_w
            self._show(ctx, layout, text_x, y + 3, GREEN_DARK if speaking else TEXT)

        # How many webcams did not fit, on the corner of the last tile
        if self.hidden_webcams > 0 and self.webcams:
            hole = self._tile_hole(self.webcams[-1][1])
            layout = self._layout(
                ctx, self._plural("more_webcams", self.hidden_webcams), 13.5, 600
            )
            text_w, text_h = self._size(layout)
            label_w = text_w + 18
            label_h = text_h + 6
            x = hole.x + hole.width - 8 - label_w
            y = hole.y + 8
            if label_w < hole.width - 16:
                rounded_rect(ctx, x, y, label_w, label_h, label_h / 2)
                ctx.set_source_rgba(*SHADE, 0.80)
                ctx.fill()
                self._show(ctx, layout, x + 9, y + 3, TEXT)

    # Session activity

    def _draw_activity(self, timestamp: float, participants: int, visible: int) -> None:
        panel = self.activity
        if panel.width <= 0 or panel.height <= 0:
            return
        ctx = self.ctx
        header_h = 58

        rounded_rect(ctx, panel.x, panel.y, panel.width, panel.height, AREA_RADIUS)
        ctx.set_source_rgb(*self.panel)
        ctx.fill()

        count = self._layout(ctx, self._plural("participants", participants), 14, 500)
        count_w, count_h = self._size(count)
        title = self._layout(
            ctx,
            str(self.strings["activity"]),
            19,
            700,
            width=panel.width - 40 - count_w - 12,
        )
        _title_w, title_h = self._size(title)
        self._show(ctx, title, panel.x + 20, panel.y + (header_h - title_h) / 2, TEXT)
        if participants > 0:
            self._show(
                ctx,
                count,
                panel.x + panel.width - 20 - count_w,
                panel.y + (header_h - count_h) / 2 + 1,
                MUTED,
            )
        ctx.set_source_rgba(1, 1, 1, 0.07)
        ctx.rectangle(panel.x, panel.y + header_h, panel.width, 1)
        ctx.fill()

        # The timeline grows from the bottom; older entries scroll out at the top
        padding = 16
        list_top = panel.y + header_h + 1
        list_bottom = panel.y + panel.height - padding
        item_x = panel.x + padding
        item_width = panel.width - 2 * padding

        ctx.save()
        ctx.rectangle(panel.x, list_top, panel.width, list_bottom - list_top)
        ctx.clip()

        y = list_bottom
        used: List[int] = []
        for index in range(visible - 1, -1, -1):
            item = self.events.items[index]
            item_surface = self._item_surface(index, item, item_width)
            height = item_surface.get_height() / self.scale
            age = timestamp - item.timestamp
            progress = min(1.0, max(0.0, age / ENTER_DURATION))
            eased = 1 - (1 - progress) ** 3
            # One-line entries sit closer together than messages and cards
            if item.kind in PRESENCE_KINDS:
                item_gap = 3.0
            elif item.kind in COMPACT_KINDS:
                item_gap = 8.0
            else:
                item_gap = 14.0
            y -= (height + item_gap) * eased
            used.append(index)

            ctx.save()
            ctx.translate(item_x, y)
            ctx.scale(1 / self.scale, 1 / self.scale)
            ctx.set_source_surface(item_surface, 0, 0)
            ctx.paint_with_alpha(eased)
            ctx.restore()

            if y < list_top:
                break

        # Fade the entries which are leaving at the top
        if y < list_top + 6:
            fade = cairo.LinearGradient(0, list_top, 0, list_top + 44)
            fade.add_color_stop_rgba(0, *self.panel, 1)
            fade.add_color_stop_rgba(1, *self.panel, 0)
            ctx.set_source(fade)
            ctx.rectangle(panel.x, list_top, panel.width, 44)
            ctx.fill()
        ctx.restore()

        for index in list(self._item_cache):
            if index not in used:
                del self._item_cache[index]

    def _item_surface(
        self, index: int, item: ActivityItem, width: float
    ) -> cairo.ImageSurface:
        cached = self._item_cache.get(index)
        if cached is not None:
            return cached

        # Draw once on a scratch surface to measure, then crop to the height used
        scratch = cairo.ImageSurface(
            cairo.FORMAT_ARGB32,
            math.ceil(width * self.scale),
            math.ceil(900 * self.scale),
        )
        ctx = cairo.Context(scratch)
        ctx.scale(self.scale, self.scale)
        clock = format_clock(self.events.recording_time(item.timestamp))
        if item.kind == "chat":
            height = self._draw_chat(ctx, item, width, clock)
        elif item.kind == "poll":
            height = self._draw_poll(ctx, item, width, clock)
        elif item.kind in PRESENCE_KINDS:
            height = self._draw_presence(ctx, item, width, clock)
        elif item.kind in COMPACT_KINDS:
            height = self._draw_compact(ctx, item, width, clock)
        else:
            height = self._draw_external_video(ctx, item, width, clock)
        scratch.flush()

        surface = cairo.ImageSurface(
            cairo.FORMAT_ARGB32,
            scratch.get_width(),
            max(1, math.ceil(min(height, 900) * self.scale)),
        )
        crop = cairo.Context(surface)
        crop.set_source_surface(scratch, 0, 0)
        crop.paint()
        surface.flush()
        self._item_cache[index] = surface
        return surface

    def _draw_chat(
        self, ctx: "cairo.Context[Any]", item: ActivityItem, width: float, clock: str
    ) -> float:
        avatar = 36
        text_x = avatar + 14

        picture = self._avatar(item.user_id, avatar)
        ctx.arc(avatar / 2, avatar / 2 + 2, avatar / 2, 0, 2 * math.pi)
        if picture is not None:
            ctx.save()
            # A picture with transparency gets a light background
            ctx.set_source_rgb(0.93, 0.94, 0.96)
            ctx.fill_preserve()
            ctx.clip()
            ctx.translate(0, 2)
            ctx.scale(avatar / picture.get_width(), avatar / picture.get_height())
            ctx.set_source_surface(picture, 0, 0)
            ctx.paint()
            ctx.restore()
        else:
            # Without a picture, the initials over a color of the user
            ctx.set_source_rgb(*avatar_color(item.user_id or item.name))
            ctx.fill()
            letters = self._layout(ctx, initials(item.name), 13.5, 700)
            letters_w, letters_h = self._size(letters)
            self._show(
                ctx,
                letters,
                (avatar - letters_w) / 2,
                2 + (avatar - letters_h) / 2,
                TEXT,
            )

        when = self._layout(ctx, clock, 13, 400)
        when_w, _when_h = self._size(when)
        name_width = width - text_x - when_w - 10
        name = self._layout(ctx, item.name, 15, 700, width=name_width)
        name_w, name_h = self._size(name)
        name_w = min(name_w, name_width)
        self._show(ctx, name, text_x, 0, TEXT)
        self._show(ctx, when, text_x + name_w + 10, 2.5, MUTED)

        qr_size = 92.0 if self._has_qr_code(item.url) else 0.0
        message_width = width - text_x - (qr_size + 12 if qr_size else 0)
        message = self._layout(ctx, item.text, 16.5, 400, width=message_width, lines=8)
        if item.markup:
            # Markdown of the message: bold, italic, code, lists, quotes, links
            try:
                _ok, attributes, text, _accel = Pango.parse_markup(
                    item.markup, -1, "\0"
                )
                message.set_text(text, -1)
                message.set_attributes(attributes)
            except Exception as error:
                print(f"Could not format a chat message: {error}")
        message.set_spacing(int(2 * Pango.SCALE))
        _message_w, message_h = self._size(message)
        self._show(ctx, message, text_x, name_h + 3, TEXT_SOFT)
        if qr_size:
            self._draw_qr_code(ctx, item.url, width - qr_size, name_h + 6, qr_size)
            message_h = max(message_h, qr_size + 5)
        return max(avatar + 4, name_h + 3 + message_h)

    def _has_qr_code(self, url: str) -> bool:
        return bool(url) and self.link_qr_code and segno is not None

    def _draw_qr_code(
        self, ctx: "cairo.Context[Any]", url: str, x: float, y: float, size: float
    ) -> None:
        """A QR code on a white tile, with the modules on whole pixels."""
        try:
            matrix = [list(row) for row in segno.make(url, error="l").matrix]
        except Exception as error:
            print(f"Could not make the QR code of {url}: {error}")
            return
        rounded_rect(ctx, x, y, size, size, 6)
        ctx.set_source_rgb(1, 1, 1)
        ctx.fill()
        modules = len(matrix)
        # Leave a quiet zone of at least 2 modules inside the tile
        module = math.floor(size * self.scale / (modules + 4)) / self.scale
        if module <= 0:
            return
        offset = (size - modules * module) / 2
        ctx.set_source_rgb(0, 0, 0)
        for row_index, row in enumerate(matrix):
            for column_index, dark in enumerate(row):
                if dark:
                    ctx.rectangle(
                        x + offset + column_index * module,
                        y + offset + row_index * module,
                        module,
                        module,
                    )
        ctx.save()
        ctx.set_antialias(cairo.ANTIALIAS_NONE)
        ctx.fill()
        ctx.restore()

    def _draw_presence(
        self, ctx: "cairo.Context[Any]", item: ActivityItem, width: float, clock: str
    ) -> float:
        """Who joined or left: a quiet line, so it does not compete with the chat."""
        height = 20.0
        icon = 36.0
        text_x = icon + 14
        middle = height / 2
        joined = item.kind == "join"

        # Small arrow pointing in for who joined, out for who left
        direction = 1 if joined else -1
        ctx.set_source_rgba(*(GREEN if joined else MUTED), 0.75)
        ctx.set_line_width(1.5)
        ctx.set_line_cap(cairo.LINE_CAP_ROUND)
        ctx.set_line_join(cairo.LINE_JOIN_ROUND)
        ctx.move_to(icon / 2 - 4.5 * direction, middle)
        ctx.line_to(icon / 2 + 4.5 * direction, middle)
        ctx.move_to(icon / 2 + 1.5 * direction, middle - 3)
        ctx.line_to(icon / 2 + 4.5 * direction, middle)
        ctx.line_to(icon / 2 + 1.5 * direction, middle + 3)
        ctx.stroke()

        when = self._layout(ctx, clock, 11.5, 400)
        when_w, when_h = self._size(when)
        self._show(ctx, when, width - when_w, middle - when_h / 2, MUTED, 0.7)

        action = self._layout(ctx, str(self.strings[item.kind]), 12.5, 400)
        action_w, action_h = self._size(action)
        name_width = width - text_x - when_w - 12 - action_w - 5
        name = self._layout(ctx, item.name, 12.5, 500, width=name_width)
        name_w, name_h = self._size(name)
        name_w = min(name_w, name_width)
        self._show(ctx, name, text_x, middle - name_h / 2, MUTED)
        self._show(ctx, action, text_x + name_w + 5, middle - action_h / 2, MUTED, 0.7)
        return height

    def _draw_compact(
        self, ctx: "cairo.Context[Any]", item: ActivityItem, width: float, clock: str
    ) -> float:
        """One line: who raised the hand or sent a reaction."""
        # A reaction is all about the emoji, so it is drawn larger
        reaction = item.kind == "reaction"
        height = 52.0 if reaction else 26.0
        icon = 48.0 if reaction else 36.0
        text_x = icon + (10 if reaction else 14)
        middle = height / 2

        emoji = self._layout(ctx, item.emoji or "\u270b", 40 if reaction else 19)
        emoji_w, emoji_h = self._size(emoji)
        self._show(ctx, emoji, (icon - emoji_w) / 2, middle - emoji_h / 2, TEXT)

        when = self._layout(ctx, clock, 12.5, 400)
        when_w, when_h = self._size(when)
        self._show(ctx, when, width - when_w, middle - when_h / 2, MUTED)

        # A long name is shortened; what the user did is always readable
        key = "reaction_chat" if item.kind == "reaction" and item.text else item.kind
        action = self._layout(ctx, str(self.strings[key]), 14.5, 400)
        action_w, action_h = self._size(action)
        name_width = width - text_x - when_w - 12 - action_w - 6
        name = self._layout(ctx, item.name, 14.5, 600, width=name_width)
        name_w, name_h = self._size(name)
        name_w = min(name_w, name_width)
        self._show(ctx, name, text_x, middle - name_h / 2, TEXT_SOFT)
        self._show(ctx, action, text_x + name_w + 6, middle - action_h / 2, MUTED)
        return height

    def _card_header(
        self,
        ctx: "cairo.Context[Any]",
        width: float,
        label: str,
        color: RGB,
        clock: str,
        icon: str,
    ) -> float:
        """Paint the card background later; returns the y below the header."""
        padding = 16
        x = padding
        y = padding
        if icon == "bars":
            x += bars_icon(ctx, x, y + 1, 15, color, (0.5, 1.0, 0.7)) + 9
        else:
            rounded_rect(ctx, x + 0.75, y + 2, 17, 13, 3)
            ctx.set_source_rgb(*color)
            ctx.set_line_width(1.5)
            ctx.stroke()
            ctx.move_to(x + 7, y + 5.5)
            ctx.line_to(x + 12, y + 8.5)
            ctx.line_to(x + 7, y + 11.5)
            ctx.close_path()
            ctx.fill()
            x += 18.5 + 9
        when = self._layout(ctx, clock, 13, 400)
        when_w, _when_h = self._size(when)
        title = self._layout(
            ctx,
            label,
            12.5,
            700,
            width=width - x - padding - when_w - 8,
            letter_spacing=0.9,
        )
        self._show(ctx, title, x, y, color)
        self._show(ctx, when, width - padding - when_w, y - 0.5, MUTED)
        return y + 28

    def _card_background(
        self, ctx: "cairo.Context[Any]", width: float, height: float
    ) -> None:
        ctx.save()
        ctx.set_operator(cairo.OPERATOR_DEST_OVER)
        rounded_rect(ctx, 0, 0, width, height, 10)
        ctx.set_source_rgb(*self.card)
        ctx.fill()
        ctx.restore()

    def _draw_poll(
        self, ctx: "cairo.Context[Any]", item: ActivityItem, width: float, clock: str
    ) -> float:
        padding = 16
        inner = width - 2 * padding
        y = self._card_header(
            ctx, width, str(self.strings["poll"]), BLUE, clock, "bars"
        )

        if item.text:
            question = self._layout(ctx, item.text, 17.5, 700, width=inner, lines=4)
            _question_w, question_h = self._size(question)
            self._show(ctx, question, padding, y, TEXT)
            y += question_h + 12

        total = sum(answer.votes for answer in item.answers)
        label_w = inner * 0.36
        value_w = 86.0
        bar_x = padding + label_w + 10
        bar_w = inner - label_w - 10 - value_w - 8
        for answer in item.answers[:10]:
            share = answer.votes / total if total > 0 else 0.0
            key = f"\u2713 {answer.key}" if answer.correct else answer.key
            label = self._layout(ctx, key, 15, 500, width=label_w)
            _label_w, label_h = self._size(label)
            self._show(ctx, label, padding, y, GREEN if answer.correct else TEXT_SOFT)

            bar_y = y + label_h / 2 - 4
            rounded_rect(ctx, bar_x, bar_y, bar_w, 8, 4)
            ctx.set_source_rgba(1, 1, 1, 0.09)
            ctx.fill()
            if share > 0:
                rounded_rect(ctx, bar_x, bar_y, max(8.0, bar_w * share), 8, 4)
                ctx.set_source_rgb(*(GREEN if answer.correct else BLUE))
                ctx.fill()

            value = self._layout(
                ctx, f"{answer.votes} · {round(share * 100)}%", 15, 500
            )
            value_width, _value_h = self._size(value)
            self._show(ctx, value, width - padding - value_width, y, TEXT_SOFT)
            y += label_h + 7

        votes = self._layout(
            ctx, self._plural("votes", max(item.responders, total)), 13, 400
        )
        _votes_w, votes_h = self._size(votes)
        self._show(ctx, votes, padding, y + 5, MUTED)
        height = y + 5 + votes_h + padding
        self._card_background(ctx, width, height)
        return height

    def _draw_external_video(
        self, ctx: "cairo.Context[Any]", item: ActivityItem, width: float, clock: str
    ) -> float:
        padding = 16
        inner = width - 2 * padding
        y = self._card_header(
            ctx, width, str(self.strings["external_video"]), AMBER, clock, "play"
        )

        qr_size = 104.0 if self._has_qr_code(item.url) else 0.0
        top = y
        if qr_size:
            self._draw_qr_code(ctx, item.url, width - padding - qr_size, top, qr_size)
            inner -= qr_size + 14
        url = self._layout(ctx, item.url, 15.5, 500, width=inner, lines=4)
        attributes = Pango.AttrList()
        attributes.insert(Pango.attr_underline_new(Pango.Underline.SINGLE))
        url.set_attributes(attributes)
        _url_w, url_h = self._size(url)
        self._show(ctx, url, padding, y, (0.541, 0.722, 1.0))
        y += url_h

        if item.name:
            shared = self._layout(
                ctx,
                str(self.strings["shared_by"]).format(name=item.name),
                13,
                400,
                width=inner,
            )
            _shared_w, shared_h = self._size(shared)
            self._show(ctx, shared, padding, y + 8, MUTED)
            y += 8 + shared_h

        height = max(y, top + qr_size) + padding
        self._card_background(ctx, width, height)
        return height


def render_stream(
    renderer: OverlayRenderer,
    output: str,
    start: float,
    end: float,
    framerate: float,
) -> None:
    """Write raw BGRA (premultiplied alpha) frames for the section requested."""
    frame = 0
    drawn = 0
    data = b""
    began = time.perf_counter()
    with open(output, "wb", buffering=0) as stream:
        while True:
            timestamp = start + frame / framerate
            if timestamp >= end:
                break
            if renderer.render(timestamp) or not data:
                data = bytes(renderer.surface.get_data())
                drawn += 1
            try:
                stream.write(data)
            except BrokenPipeError:
                # The reader already has all the frames it wanted
                break
            frame += 1
    elapsed = time.perf_counter() - began
    print(f"Wrote {frame} frames ({drawn} drawn) in {elapsed:.1f}s")
