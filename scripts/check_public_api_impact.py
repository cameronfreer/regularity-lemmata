#!/usr/bin/env python3
# Copyright (c) 2026 Cameron Freer. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
"""Validate the required Public API impact section in a pull-request body."""

from __future__ import annotations

import argparse
import os
import re
import sys


HEADER = re.compile(r"(?mi)^#{1,6}[ \t]+Public API impact[ \t]*$")
NEXT_HEADER = re.compile(r"(?m)^#{1,6}[ \t]+")
COMMENT = re.compile(r"<!--.*?-->", re.DOTALL)
ENTRY = re.compile(
    r"(?mi)^\s*(?:[-*]\s*)?(?:"
    r"Added:\s*\S.*|"
    r"Changed:\s*\S.*|"
    r"Deprecated/removed:\s*\S.*|"
    r"None\s*)$"
)


def validate(body: str) -> str | None:
    """Return an error message, or ``None`` when ``body`` satisfies the contract."""
    match = HEADER.search(body)
    if match is None:
        return "missing '## Public API impact' section"
    section = body[match.end() :]
    next_header = NEXT_HEADER.search(section)
    if next_header is not None:
        section = section[: next_header.start()]
    section = COMMENT.sub("", section).strip()
    if not section:
        return "the Public API impact section is blank"
    if ENTRY.search(section) is None:
        return (
            "the Public API impact section must contain 'Added: ...', 'Changed: ...', "
            "'Deprecated/removed: ...', or an explicit 'None'"
        )
    return None


def self_test() -> None:
    invalid = [
        "## Summary\nNothing",
        "## Public API impact\n<!-- Added: ... -->",
        "## Public API impact\nAdded:\n## Checklist\n- [x] done",
        "## Public API impact\nNo public changes",
    ]
    valid = [
        "## Public API impact\nAdded: `foo`.",
        "## Public API impact\n- Changed: `foo` now returns `bar`.\n## Checklist",
        "## Public API impact\nDeprecated/removed: `oldFoo`.",
        "## Public API impact\nNone",
    ]
    for body in invalid:
        assert validate(body) is not None, body
    for body in valid:
        assert validate(body) is None, body


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--self-test", action="store_true")
    parser.add_argument("--body-file")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        print("check_public_api_impact: self-test passed")
        return 0
    if args.body_file:
        with open(args.body_file, encoding="utf-8") as stream:
            body = stream.read()
    else:
        body = os.environ.get("PR_BODY", "")
    error = validate(body)
    if error is not None:
        print(f"check_public_api_impact: FAIL — {error}", file=sys.stderr)
        return 1
    print("check_public_api_impact: OK")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
