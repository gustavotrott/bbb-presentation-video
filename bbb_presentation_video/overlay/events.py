# SPDX-FileCopyrightText: 2026 BigBlueButton Inc. and by respective authors
#
# SPDX-License-Identifier: GPL-3.0-or-later

"""Read the parts of events.xml that give context to a recording video.

The presentation renderer only cares about slides and annotations. The overlay
needs a different slice of the meeting: who was talking, what was written in
the chat, which polls were published and which external videos were shared.
"""

import html
import json
import re
from bisect import bisect_right
from dataclasses import dataclass, field
from html.parser import HTMLParser
from os import path
from typing import Any, Dict, List, Optional, Tuple

from lxml import etree

# Two talking bursts of the same user closer than this are shown as one
TALK_MERGE_GAP = 0.8
# Talking bursts shorter than this are noise (a cough, a key press)
TALK_MIN_LENGTH = 0.25
# Keep the indicator on for a moment after the user stops talking
TALK_HOLD = 0.4
# Somebody who comes back within this time did not really leave: it was a
# reconnection, a page reload or a second tab
REJOIN_GRACE = 120.0


@dataclass
class User:
    user_id: str
    name: str
    role: str = "VIEWER"
    # Picture of the user, when the join request had one (avatarURL)
    avatar_url: str = ""


@dataclass
class TalkInterval:
    start: float
    end: float
    user_id: str


@dataclass
class PollAnswer:
    key: str
    votes: int
    # In a quiz whose answer was revealed
    correct: bool = False


@dataclass
class ChatReaction:
    """A reaction to a chat message, from when it was sent until it was removed."""

    start: float
    emoji: str
    user_id: str
    end: Optional[float] = None


@dataclass
class ActivityItem:
    """One entry of the session activity timeline."""

    # "chat", "poll", "external_video", or one of the one-line entries:
    # "join", "leave", "raise_hand", "reaction" and "chat_clear"
    kind: str
    timestamp: float
    user_id: Optional[str] = None
    name: str = ""
    text: str = ""
    url: str = ""
    emoji: str = ""
    # The chat message with its formatting, as Pango markup
    markup: str = ""
    answers: List[PollAnswer] = field(default_factory=list)
    responders: int = 0
    # When the entry goes away (the public chat was cleared)
    end: Optional[float] = None
    # Chat: the message this one answers, shown as a quote above it
    reply_to: Optional["ActivityItem"] = None
    # Chat: reactions to the message, which come and go during the meeting
    reactions: List[ChatReaction] = field(default_factory=list)
    # Chat: a moderator message the meeting is configured to emphasize
    emphasized: bool = False

    def reactions_at(self, timestamp: float) -> Tuple[Tuple[str, int], ...]:
        """Emoji and count of the reactions at the timestamp, as the client
        orders them: the most used first, then the one used first."""
        counts: Dict[str, List[float]] = {}
        for reaction in self.reactions:
            if reaction.start <= timestamp and (
                reaction.end is None or timestamp < reaction.end
            ):
                entry = counts.setdefault(reaction.emoji, [0, reaction.start])
                entry[0] += 1
                entry[1] = min(entry[1], reaction.start)
        ordered = sorted(counts.items(), key=lambda kv: (-kv[1][0], kv[1][1]))
        return tuple((emoji, int(entry[0])) for emoji, entry in ordered)


@dataclass
class PinnedMessage:
    """A chat message kept at the top of the chat by a moderator."""

    start: float
    end: float
    item: ActivityItem
    pinned_by: str = ""


@dataclass
class ExternalVideo:
    """A video from a link, played in the place of the presentation."""

    start: float
    end: float
    url: str
    shared_by: str = ""


@dataclass
class TimerState:
    """The timer (or stopwatch) of the meeting from a timestamp on."""

    timestamp: float
    active: bool = False
    stopwatch: bool = True
    running: bool = False
    # Length of the countdown and time already counted, in seconds
    time: float = 0.0
    accumulated: float = 0.0

    def value(self, timestamp: float) -> Tuple[float, bool]:
        """Seconds shown at the timestamp, and whether a countdown is over."""
        counted = self.accumulated
        if self.running:
            counted += max(0.0, timestamp - self.timestamp)
        if self.stopwatch:
            return counted, False
        remaining = self.time - counted
        return max(0.0, remaining), self.running and remaining <= 0


@dataclass
class OverlayEvents:
    meeting_name: str
    # Unix time (seconds) of the first event of the meeting
    start_utc: Optional[float]
    length: float
    users: Dict[str, User]
    # Intervals of the meeting which were recorded, in meeting time
    record_intervals: List[Tuple[float, float]]
    talk_intervals: List[TalkInterval]
    # (timestamp, number of users in the meeting from that point on)
    participants: List[Tuple[float, int]]
    items: List[ActivityItem]
    pinned: List[PinnedMessage] = field(default_factory=list)
    external_videos: List[ExternalVideo] = field(default_factory=list)
    timer: List[TimerState] = field(default_factory=list)
    # Moments in which something already on screen changes (a reaction, a
    # pinned message, the chat being cleared), sorted
    changes: List[float] = field(default_factory=list)

    def recording_time(self, timestamp: float) -> float:
        """Convert a meeting timestamp to a position in the recording."""
        position = 0.0
        for start, end in self.record_intervals:
            if timestamp <= start:
                break
            position += min(timestamp, end) - start
        return position

    def recorded(self, timestamp: float) -> bool:
        return any(start <= timestamp < end for start, end in self.record_intervals)

    def recording_start_utc(self) -> Optional[float]:
        if self.start_utc is None:
            return None
        if self.record_intervals:
            return self.start_utc + self.record_intervals[0][0]
        return self.start_utc

    def participants_at(self, timestamp: float) -> int:
        i = bisect_right(self.participants, (timestamp, 1 << 30))
        return self.participants[i - 1][1] if i > 0 else 0

    def pinned_at(self, timestamp: float) -> Optional[PinnedMessage]:
        for pinned in self.pinned:
            if pinned.start <= timestamp < pinned.end:
                return pinned
        return None

    def external_video_at(self, timestamp: float) -> Optional[ExternalVideo]:
        for video in self.external_videos:
            if video.start <= timestamp < video.end:
                return video
        return None

    def timer_at(self, timestamp: float) -> Optional[TimerState]:
        """The timer shown at the timestamp, if it is on the screen."""
        state: Optional[TimerState] = None
        for candidate in self.timer:
            if candidate.timestamp > timestamp:
                break
            state = candidate
        return state if state is not None and state.active else None

    def talking_at(self, timestamp: float) -> List[str]:
        """Users talking at the timestamp, the one talking for longest first."""
        active = [
            interval
            for interval in self.talk_intervals
            if interval.start <= timestamp < interval.end
        ]
        active.sort(key=lambda interval: interval.start)
        return [interval.user_id for interval in active]


def _text(event: etree._Element, *names: str) -> Optional[str]:
    for name in names:
        element = event.find(name)
        if element is not None and element.text is not None:
            return element.text
    return None


def _milliseconds(value: Optional[str]) -> float:
    try:
        return int(value or "0") / 1000
    except ValueError:
        return 0.0


_BLOCK_END = re.compile(r"</(p|div|li|h[1-6]|blockquote|pre)\s*>|<br\s*/?>", re.I)
_TAG = re.compile(r"<[^>]+>")


def plain_text(message: str) -> str:
    """Chat messages are stored as HTML; the video shows them as plain text."""
    message = _BLOCK_END.sub("\n", message)
    message = _TAG.sub("", message)
    message = html.unescape(message)
    lines = [re.sub(r"[ \t\r\f\v]+", " ", line).strip() for line in message.split("\n")]
    return "\n".join(line for line in lines if line)


class _ChatMarkup(HTMLParser):
    """Convert the HTML of a chat message to Pango markup.

    The messages are written in Markdown, which the server stores as HTML
    (CommonMark): paragraphs, emphasis, code, lists, quotes, headings, links.
    """

    INLINE = {
        "strong": "<b>",
        "b": "<b>",
        "em": "<i>",
        "i": "<i>",
        "del": "<s>",
        "s": "<s>",
        "code": '<span font_family="monospace" background="#ffffff" bgalpha="11%">',
        "a": '<span foreground="#8ab8ff" underline="single">',
        "h1": '<span weight="bold" size="larger">',
        "h2": '<span weight="bold" size="larger">',
        "h3": "<b>",
        "h4": "<b>",
        "h5": "<b>",
        "h6": "<b>",
        "blockquote": '<span style="italic" alpha="72%">',
    }
    BLOCKS = ("p", "div", "li", "pre", "blockquote", "h1", "h2", "h3", "h4", "h5", "h6")

    def __init__(self) -> None:
        super().__init__(convert_charrefs=True)
        self.out: List[str] = []
        # Open inline tags, to close them at the end of each line: the lines
        # are joined later and each one must be valid markup on its own
        self.open: List[str] = []
        self.lists: List[Optional[int]] = []
        self.pre = 0
        self.quote = 0
        self.line_start = True

    def _newline(self) -> None:
        if self.line_start:
            return
        for tag in reversed(self.open):
            self.out.append(self._close(tag))
        self.out.append("\n")
        self.line_start = True

    @staticmethod
    def _close(tag: str) -> str:
        opening = _ChatMarkup.INLINE[tag]
        return "</" + opening[1:].split(" ")[0].rstrip(">") + ">"

    def _text(self, text: str) -> None:
        if not text:
            return
        if self.line_start:
            if self.quote:
                self.out.append("\u258e ")
            for tag in self.open:
                self.out.append(self.INLINE[tag])
            self.line_start = False
        self.out.append(html.escape(text, quote=False))

    def handle_starttag(self, tag: str, attrs: Any) -> None:
        if tag == "br":
            self._newline()
            return
        if tag == "hr":
            self._newline()
            self._text("\u2500" * 12)
            self._newline()
            return
        if tag in self.BLOCKS:
            self._newline()
        if tag in ("ul", "ol"):
            start = dict(attrs).get("start") or "1"
            self.lists.append(
                (int(start) if start.isdigit() else 1) if tag == "ol" else None
            )
        elif tag == "li":
            depth = "   " * max(0, len(self.lists) - 1)
            number = self.lists[-1] if self.lists else None
            if number is None:
                self._text(f"{depth}\u2022 ")
            else:
                self._text(f"{depth}{number}. ")
                self.lists[-1] = number + 1
        elif tag == "pre":
            self.pre += 1
        if tag == "blockquote":
            self.quote += 1
        if tag in self.INLINE:
            if not self.line_start:
                self.out.append(self.INLINE[tag])
            self.open.append(tag)

    def handle_endtag(self, tag: str) -> None:
        if tag in self.INLINE and tag in self.open:
            # Tolerate bad nesting: close up to the matching tag
            while self.open:
                last = self.open.pop()
                if not self.line_start:
                    self.out.append(self._close(last))
                if last == tag:
                    break
        if tag in ("ul", "ol") and self.lists:
            self.lists.pop()
        elif tag == "pre":
            self.pre = max(0, self.pre - 1)
        elif tag == "blockquote":
            self.quote = max(0, self.quote - 1)
        if tag in self.BLOCKS:
            self._newline()

    def handle_data(self, data: str) -> None:
        if self.pre:
            lines = data.split("\n")
            for index, line in enumerate(lines):
                if index:
                    self._newline()
                self._text(line)
            return
        data = re.sub(r"\s+", " ", data)
        if self.line_start:
            data = data.lstrip()
        self._text(data)

    def result(self) -> str:
        self._newline()
        return "".join(self.out).strip("\n")


def chat_markup(message: str) -> str:
    """The chat message as Pango markup; empty if it cannot be converted."""
    parser = _ChatMarkup()
    try:
        parser.feed(message)
        parser.close()
        return parser.result()
    except Exception:
        return ""


def first_line_markup(markup: str) -> str:
    """The first line of a message, which is what a quote of it shows."""
    return markup.split("\n", 1)[0]


def _is_emoji_char(char: str) -> bool:
    code = ord(char)
    return (
        0x1F000 <= code <= 0x1FAFF
        or 0x2600 <= code <= 0x27BF
        or 0x2B00 <= code <= 0x2BFF
        or 0x2190 <= code <= 0x21FF
        or 0x2300 <= code <= 0x23FF
        or code in (0x00A9, 0x00AE, 0x203C, 0x2049, 0x2122, 0x2139, 0x3030, 0x303D)
    )


# Up to this many emoji alone in a message are shown larger, as in the client
MAX_JUMBOMOJI_COUNT = 3


def is_jumbomoji(text: str) -> bool:
    """Whether the message is nothing but one to three emoji."""
    condensed = re.sub(r"\s+", "", text)
    if not condensed:
        return False
    count = 0
    joined = False
    index = 0
    while index < len(condensed):
        char = condensed[index]
        code = ord(char)
        if code == 0x200D:  # Zero width joiner: the next emoji is the same one
            joined = True
        elif code == 0xFE0F or 0x1F3FB <= code <= 0x1F3FF or code == 0x20E3:
            pass  # Variation selector, skin tone, keycap
        elif 0x1F1E6 <= code <= 0x1F1FF:
            # A flag is a pair of regional indicators
            if index + 1 >= len(condensed) or not (
                0x1F1E6 <= ord(condensed[index + 1]) <= 0x1F1FF
            ):
                return False
            index += 1
            count += 1
        elif _is_emoji_char(char) or (
            char in "0123456789#*"
            and condensed[index + 1 : index + 3].endswith("\u20e3")
        ):
            if not joined:
                count += 1
            joined = False
        else:
            return False
        index += 1
    return 1 <= count <= MAX_JUMBOMOJI_COUNT


_HREF = re.compile(r"""href\s*=\s*["']([^"']+)["']""", re.I)
_URL = re.compile(r"https?://[^\s<>\"']+", re.I)


def first_link(message: str) -> str:
    """The first link of a chat message (as stored, in HTML), if any."""
    match = _HREF.search(message)
    if match is not None and match.group(1).lower().startswith(("http://", "https://")):
        return html.unescape(match.group(1))
    match = _URL.search(html.unescape(_TAG.sub(" ", message)))
    return match.group(0).rstrip(".,;:!?)") if match is not None else ""


def _talk_intervals(raw: List[TalkInterval]) -> List[TalkInterval]:
    by_user: Dict[str, List[TalkInterval]] = {}
    for interval in raw:
        by_user.setdefault(interval.user_id, []).append(interval)

    result: List[TalkInterval] = []
    for intervals in by_user.values():
        intervals.sort(key=lambda interval: interval.start)
        merged: List[TalkInterval] = []
        for interval in intervals:
            if merged and interval.start - merged[-1].end <= TALK_MERGE_GAP:
                merged[-1].end = max(merged[-1].end, interval.end)
            else:
                merged.append(interval)
        for interval in merged:
            if interval.end - interval.start >= TALK_MIN_LENGTH:
                interval.end += TALK_HOLD
                result.append(interval)

    result.sort(key=lambda interval: interval.start)
    return result


def _presence_items(
    transitions: List[Tuple[float, str, bool, str, str]], rejoin_grace: float
) -> List[ActivityItem]:
    """Timeline entries for who joined and who left.

    The events are per session: a user who reloads the page or loses the
    connection for a moment shows up as a new session joining and the old one
    leaving some seconds later. The transitions received here are per person
    (the first session to join, the last one to leave), and a person who is
    back within the grace period never left as far as the viewer is concerned.
    """
    by_person: Dict[str, List[Tuple[float, bool, str, str]]] = {}
    for timestamp, person, joined, user_id, name in transitions:
        by_person.setdefault(person, []).append((timestamp, joined, user_id, name))

    items: List[ActivityItem] = []
    for person_transitions in by_person.values():
        kept: List[Tuple[float, bool, str, str]] = []
        for transition in person_transitions:
            timestamp, joined = transition[0], transition[1]
            if (
                joined
                and kept
                and not kept[-1][1]
                and timestamp - kept[-1][0] <= rejoin_grace
            ):
                # Back soon after leaving: drop both entries
                kept.pop()
                continue
            kept.append(transition)
        for timestamp, joined, user_id, name in kept:
            items.append(
                ActivityItem("join" if joined else "leave", timestamp, user_id, name)
            )
    return items


def parse_overlay_events(
    directory: str, rejoin_grace: float = REJOIN_GRACE
) -> OverlayEvents:
    tree = etree.parse(path.join(directory, "events.xml"))
    root = tree.getroot()
    events = root.findall("event")
    if not events:
        raise ValueError("events.xml does not contain any event")

    first = int(events[0].get("timestamp", "0"))
    last = int(events[-1].get("timestamp", "0"))
    length = (last - first) / 1000

    meeting = root.find("meeting")
    metadata = root.find("metadata")
    meeting_name = ""
    if metadata is not None:
        meeting_name = metadata.get("meetingName", "")
    if not meeting_name and meeting is not None:
        meeting_name = meeting.get("name", "")

    start_utc: Optional[float] = None
    users: Dict[str, User] = {}
    # Sessions of each person in the meeting. A person is the external user
    # id given by the integration (plus the name, as some integrations use the
    # same id for every guest), which is kept when the user joins again.
    person_of: Dict[str, str] = {}
    sessions: Dict[str, "set[str]"] = {}
    presence: List[Tuple[float, str, bool, str, str]] = []
    participants: List[Tuple[float, int]] = []
    record_marks: List[Tuple[float, bool]] = []
    talk_start: Dict[str, float] = {}
    talk_raw: List[TalkInterval] = []
    items: List[ActivityItem] = []
    chat_by_id: Dict[str, ActivityItem] = {}
    deleted: "set[int]" = set()
    pinned: List[PinnedMessage] = []
    external_videos: List[ExternalVideo] = []
    timer: List[TimerState] = []
    changes: List[float] = []
    presenter: Optional[str] = None

    def unpin(timestamp: float) -> None:
        if pinned and pinned[-1].end > timestamp:
            pinned[-1].end = timestamp
            changes.append(timestamp)

    def stop_external_video(timestamp: float) -> None:
        if external_videos and external_videos[-1].end > timestamp:
            external_videos[-1].end = timestamp

    def timer_change(timestamp: float, **fields: Any) -> None:
        """A new state of the timer, with what was counted so far settled."""
        last = timer[-1] if timer else TimerState(timestamp)
        counted = last.accumulated
        if last.running:
            counted += max(0.0, timestamp - last.timestamp)
            # A countdown stops by itself at zero, and starts over
            if not last.stopwatch and counted >= last.time:
                last = TimerState(last.timestamp, last.active, False, False, last.time)
                counted = 0.0
        state = TimerState(
            timestamp, last.active, last.stopwatch, last.running, last.time, counted
        )
        for key, value in fields.items():
            setattr(state, key, value)
        timer.append(state)

    def stop_talking(user_id: str, timestamp: float) -> None:
        start = talk_start.pop(user_id, None)
        if start is not None:
            talk_raw.append(TalkInterval(start, timestamp, user_id))

    for event in events:
        timestamp = (int(event.get("timestamp", "0")) - first) / 1000
        module = event.get("module")
        name = event.get("eventname")

        if start_utc is None:
            utc = _text(event, "timestampUTC")
            if utc is not None and utc.isdigit():
                start_utc = int(utc) / 1000 - timestamp

        if name == "ParticipantJoinEvent":
            user_id = _text(event, "userId")
            if user_id is None:
                continue
            users[user_id] = User(
                user_id,
                (_text(event, "name") or "").strip(),
                _text(event, "role") or "VIEWER",
                (_text(event, "avatarURL") or "").strip(),
            )
            external_id = (_text(event, "externalUserId") or "").strip()
            person = f"{external_id}\n{users[user_id].name}" if external_id else user_id
            person_of[user_id] = person
            person_sessions = sessions.setdefault(person, set())
            if not person_sessions:
                participants.append((timestamp, len(sessions)))
                presence.append((timestamp, person, True, user_id, users[user_id].name))
            person_sessions.add(user_id)

        elif name == "ParticipantLeftEvent":
            if module == "VOICE":
                user_id = _text(event, "participant")
                if user_id is not None:
                    stop_talking(user_id, timestamp)
            else:
                user_id = _text(event, "userId")
                if user_id is None:
                    continue
                stop_talking(user_id, timestamp)
                person = person_of.get(user_id, user_id)
                person_sessions = sessions.get(person, set())
                if user_id in person_sessions:
                    person_sessions.discard(user_id)
                    if not person_sessions:
                        del sessions[person]
                        participants.append((timestamp, len(sessions)))
                        presence.append(
                            (timestamp, person, False, user_id, users[user_id].name)
                        )

        elif name == "ParticipantStatusChangeEvent":
            user_id = _text(event, "userId")
            status = _text(event, "status")
            value = (_text(event, "value") or "").strip()
            if user_id is None or user_id not in users:
                continue
            if status == "raiseHand" and value.lower() == "true":
                items.append(
                    ActivityItem("raise_hand", timestamp, user_id, users[user_id].name)
                )
            elif status == "reactionEmoji" and value and value.lower() != "none":
                items.append(
                    ActivityItem(
                        "reaction",
                        timestamp,
                        user_id,
                        users[user_id].name,
                        emoji=value,
                    )
                )

        elif name == "SendPublicChatMessageReactionRecordEvent":
            user_id = _text(event, "senderId")
            emoji = (_text(event, "reactionEmoji") or "").strip()
            item_opt = chat_by_id.get(_text(event, "messageId") or "")
            if user_id is not None and item_opt is not None and emoji:
                # As in the client, each user reacts once with each emoji
                if not any(
                    reaction.end is None
                    and reaction.user_id == user_id
                    and reaction.emoji == emoji
                    for reaction in item_opt.reactions
                ):
                    item_opt.reactions.append(ChatReaction(timestamp, emoji, user_id))
                    changes.append(timestamp)

        elif name == "DeletePublicChatMessageReactionRecordEvent":
            user_id = _text(event, "senderId")
            emoji = (_text(event, "reactionEmoji") or "").strip()
            item_opt = chat_by_id.get(_text(event, "messageId") or "")
            if item_opt is not None:
                for reaction in item_opt.reactions:
                    if (
                        reaction.end is None
                        and reaction.user_id == user_id
                        and reaction.emoji == emoji
                    ):
                        reaction.end = timestamp
                        changes.append(timestamp)
                        break

        elif name == "ParticipantTalkingEvent":
            user_id = _text(event, "participant")
            if user_id is None:
                continue
            if (_text(event, "talking") or "").lower() == "true":
                talk_start.setdefault(user_id, timestamp)
            else:
                stop_talking(user_id, timestamp)

        elif name == "ParticipantMutedEvent":
            user_id = _text(event, "participant")
            if user_id is not None and (_text(event, "muted") or "").lower() == "true":
                stop_talking(user_id, timestamp)

        elif name == "RecordStatusEvent":
            record_marks.append(
                (timestamp, (_text(event, "status") or "").lower() == "true")
            )

        elif name == "AssignPresenterEvent":
            presenter = _text(event, "userid", "userId") or presenter

        elif name == "PublicChatEvent":
            user_id = _text(event, "senderId")
            raw_message = _text(event, "message") or ""
            message = plain_text(raw_message)
            # Messages without a known sender are system messages (for example
            # the copy of a poll result), which have their own entry.
            if user_id is None or user_id not in users or not message:
                continue
            item = ActivityItem(
                "chat",
                timestamp,
                user_id,
                users[user_id].name,
                message,
                url=first_link(raw_message),
                markup=chat_markup(raw_message),
                reply_to=chat_by_id.get(_text(event, "replyToMessageId") or ""),
                emphasized=(_text(event, "chatEmphasizedText") or "").lower() == "true",
            )
            items.append(item)
            message_id = _text(event, "messageId")
            if message_id is not None:
                chat_by_id[message_id] = item

        elif name == "EditPublicChatMessageRecordEvent":
            item_opt = chat_by_id.get(_text(event, "messageId") or "")
            raw_message = _text(event, "message") or ""
            message = plain_text(raw_message)
            if item_opt is not None and message:
                item_opt.text = message
                item_opt.url = first_link(raw_message)
                item_opt.markup = chat_markup(raw_message)

        elif name == "DeletePublicChatMessageRecordEvent":
            item_opt = chat_by_id.pop(_text(event, "messageId") or "", None)
            if item_opt is not None:
                # A deleted message is not shown at any moment of the video,
                # and neither is it quoted or kept pinned
                items.remove(item_opt)
                deleted.add(id(item_opt))

        elif name == "ClearPublicChatEvent":
            # The messages go away for everybody, and so they do in the video
            for item in items:
                if item.kind == "chat" and item.end is None:
                    item.end = timestamp
            chat_by_id.clear()
            unpin(timestamp)
            items.append(ActivityItem("chat_clear", timestamp))
            changes.append(timestamp)

        elif name == "PinPublicChatMessageRecordEvent":
            item_opt = chat_by_id.get(_text(event, "messageId") or "")
            user_id = _text(event, "senderId") or ""
            unpin(timestamp)
            if item_opt is not None:
                pinned.append(
                    PinnedMessage(
                        timestamp,
                        length + 1,
                        item_opt,
                        users[user_id].name if user_id in users else "",
                    )
                )
                changes.append(timestamp)

        elif name == "UnpinPublicChatMessageRecordEvent":
            unpin(timestamp)

        elif name == "ActivateTimerEvent":
            timer.append(
                TimerState(
                    timestamp,
                    True,
                    (_text(event, "stopwatch") or "").lower() == "true",
                    (_text(event, "running") or "").lower() == "true",
                    _milliseconds(_text(event, "time")),
                    _milliseconds(_text(event, "accumulated")),
                )
            )

        elif name == "DeactivateTimerEvent":
            timer.append(TimerState(timestamp))

        elif name == "StartTimerEvent":
            timer_change(timestamp, running=True)

        elif name == "StopTimerEvent":
            timer_change(timestamp, running=False)
            accumulated = _text(event, "accumulated")
            if accumulated is not None:
                timer[-1].accumulated = _milliseconds(accumulated)

        elif name == "SwitchTimerEvent":
            timer_change(
                timestamp,
                stopwatch=(_text(event, "stopwatch") or "").lower() == "true",
                running=False,
                accumulated=0.0,
            )

        elif name == "SetTimerEvent":
            timer_change(timestamp, time=_milliseconds(_text(event, "time")))

        elif name == "ResetTimerEvent":
            timer_change(timestamp, accumulated=0.0)

        elif name == "TimerEndedEvent":
            timer_change(timestamp, running=False, accumulated=0.0)

        elif name == "PollPublishedRecordEvent":
            answers: List[PollAnswer] = []
            reveal = (_text(event, "showCorrectAnswer") or "").lower() == "true"
            try:
                for answer in json.loads(_text(event, "answers") or "[]"):
                    answers.append(
                        PollAnswer(
                            str(answer.get("key", "")),
                            int(answer.get("numVotes", 0)),
                            reveal and bool(answer.get("isCorrectAnswer")),
                        )
                    )
            except (ValueError, AttributeError):
                answers = []
            responders = _text(event, "numResponders") or ""
            items.append(
                ActivityItem(
                    "poll",
                    timestamp,
                    text=plain_text(_text(event, "question") or ""),
                    answers=answers,
                    responders=(
                        int(responders)
                        if responders.isdigit()
                        else sum(answer.votes for answer in answers)
                    ),
                )
            )

        elif name == "StartExternalVideoRecordEvent":
            url = (_text(event, "externalVideoUrl") or "").strip()
            if not url:
                continue
            shared_by = users[presenter].name if presenter in users else ""
            items.append(
                ActivityItem("external_video", timestamp, presenter, shared_by, url=url)
            )
            stop_external_video(timestamp)
            external_videos.append(ExternalVideo(timestamp, length + 1, url, shared_by))

        elif name == "StopExternalVideoRecordEvent":
            stop_external_video(timestamp)

    for user_id in list(talk_start):
        stop_talking(user_id, length)

    for item in items:
        if item.reply_to is not None and id(item.reply_to) in deleted:
            item.reply_to = None
    pinned = [entry for entry in pinned if id(entry.item) not in deleted]

    items.extend(_presence_items(presence, rejoin_grace))
    items.sort(key=lambda item: item.timestamp)

    record_intervals: List[Tuple[float, float]] = []
    record_start: Optional[float] = None
    for timestamp, status in record_marks:
        if status and record_start is None:
            record_start = timestamp
        elif not status and record_start is not None:
            record_intervals.append((record_start, timestamp))
            record_start = None
    if record_start is not None:
        record_intervals.append((record_start, length))
    if not record_marks:
        record_intervals.append((0.0, length))

    overlay_events = OverlayEvents(
        meeting_name=meeting_name,
        start_utc=start_utc,
        length=length,
        users=users,
        record_intervals=record_intervals,
        talk_intervals=_talk_intervals(talk_raw),
        participants=participants,
        items=[],
        pinned=pinned,
        external_videos=external_videos,
        timer=timer,
        changes=sorted(changes),
    )
    # What happened while the recording was paused is not part of the video
    overlay_events.items = [
        item for item in items if overlay_events.recorded(item.timestamp)
    ]
    return overlay_events
