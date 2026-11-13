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
class ActivityItem:
    """One entry of the session activity timeline."""

    # "chat", "poll", "external_video", or one of the one-line entries:
    # "join", "leave", "raise_hand" and "reaction"
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
    presenter: Optional[str] = None

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
            if user_id is not None and user_id in users and emoji:
                items.append(
                    ActivityItem(
                        "reaction",
                        timestamp,
                        user_id,
                        users[user_id].name,
                        emoji=emoji,
                        text="chat",
                    )
                )

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
                items.remove(item_opt)

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

    for user_id in list(talk_start):
        stop_talking(user_id, length)

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
    )
    # What happened while the recording was paused is not part of the video
    overlay_events.items = [
        item for item in items if overlay_events.recorded(item.timestamp)
    ]
    return overlay_events
