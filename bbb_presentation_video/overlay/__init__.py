# SPDX-FileCopyrightText: 2026 BigBlueButton Inc. and by respective authors
#
# SPDX-License-Identifier: GPL-3.0-or-later

"""Render the context overlay of a BigBlueButton recording video.

The overlay is the frame drawn around the presentation and the webcams: the
meeting name, date and elapsed time, who is speaking, the name of each webcam
and a timeline with the chat messages, published polls and external videos.
It also shows the timer of the meeting and, while a video from a link is being
played, its address in the place of the presentation.

The output is raw video with an alpha channel (BGRA, premultiplied), meant to
be composited over the media by the recording scripts.
"""

import argparse
import json
import signal
import sys
from fractions import Fraction
from typing import Any, Dict

from bbb_presentation_video.overlay.events import parse_overlay_events
from bbb_presentation_video.overlay.renderer import OverlayRenderer, render_stream

__all__ = ["main"]


def main() -> None:
    parser = argparse.ArgumentParser(
        description="Render the context overlay of a BigBlueButton recording video",
        add_help=False,
    )
    parser.add_argument("--help", action="help", help="show this help message and exit")
    parser.add_argument("-w", "--width", type=int, default=1920, help="video width")
    parser.add_argument("-h", "--height", type=int, default=1080, help="video height")
    parser.add_argument(
        "-r", "--framerate", type=Fraction, default=Fraction(24), help="video framerate"
    )
    parser.add_argument(
        "-i", "--input", type=str, default=".", help="raw recording directory"
    )
    parser.add_argument(
        "-o", "--output", type=str, required=True, help="output file (raw BGRA frames)"
    )
    parser.add_argument(
        "-s", "--start", type=Fraction, default=Fraction(0), help="start, in seconds"
    )
    parser.add_argument("-e", "--end", type=Fraction, help="end, in seconds")
    parser.add_argument(
        "--config",
        type=str,
        default="{}",
        help="JSON with the layout: top_bar, activity, areas, webcams, locale, ...",
    )
    parser.add_argument(
        "--png",
        type=str,
        help="write a single frame at the start time to a PNG file and exit",
    )
    args = parser.parse_args()

    # The reader closes the pipe as soon as it has enough frames
    signal.signal(signal.SIGTERM, lambda _signum, _frame: sys.exit(0))

    config: Dict[str, Any] = json.loads(args.config)
    # Who comes back within this many seconds is not shown as leaving and joining
    rejoin_grace = config.get("rejoin_grace")
    events = (
        parse_overlay_events(args.input)
        if rejoin_grace is None
        else parse_overlay_events(args.input, float(rejoin_grace))
    )
    print(
        f"Parsed events: {len(events.users)} users, {len(events.items)} activity "
        f"entries, {len(events.talk_intervals)} talking intervals"
    )

    # Each kind of timeline entry can be turned off: {"events": {"join": false}}
    shown = config.get("events") or {}
    # The notice of the chat being cleared and the pinned message go with the chat
    events.items = [
        item
        for item in events.items
        if shown.get("chat" if item.kind == "chat_clear" else item.kind, True)
    ]
    if not shown.get("chat", True):
        events.pinned = []

    renderer = OverlayRenderer(events, args.width, args.height, config)

    if args.png:
        renderer.render(float(args.start))
        renderer.surface.write_to_png(args.png)
        return

    end = float(args.end) if args.end is not None else events.length
    render_stream(renderer, args.output, float(args.start), end, float(args.framerate))


if __name__ == "__main__":
    main()
