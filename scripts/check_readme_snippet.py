#!/usr/bin/env python3
# Copyright (c) 2026 Cameron Freer. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
"""The README's displayed example must be `examples/ReadmeSnippet.lean` exactly, with only the
license header omitted.

The README marks the block with a line `<!-- readme-snippet -->` immediately followed by the
```lean fence. The comparison removes the source file's leading license header, which must be
exactly the repository's copyright/SPDX block (`HEADER` below; any other leading comment, a
malformed header, or a missing header fails), and the single newline that ends it, and nothing
else. Both files are read as bytes, so whitespace, indentation, blank lines, and line endings
are compared literally with no normalization. The marker must occur exactly once. Exit 1 with a
unified diff (or the header/marker problem) on any difference.

    python3 scripts/check_readme_snippet.py            # check the repository
    python3 scripts/check_readme_snippet.py --self-test
"""
import difflib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MARK = b"<!-- readme-snippet -->"
HEADER = re.compile(
    rb"\A/-\nCopyright \(c\) 20[0-9]{2} Cameron Freer\. All rights reserved\.\n"
    rb"SPDX-License-Identifier: Apache-2\.0\n-/\n"
)


def displayed(readme: bytes) -> bytes:
    n = readme.count(MARK)
    if n != 1:
        raise SystemExit(f"check_readme_snippet: expected exactly one marker '{MARK.decode()}', found {n}")
    i = readme.index(MARK)
    m = re.match(re.escape(MARK) + rb"\n```lean\n(.*?)\n```\n", readme[i:], re.S)
    if m is None:
        raise SystemExit("check_readme_snippet: the marker must be immediately followed by a ```lean block")
    return m.group(1) + b"\n"


def source_without_header(src: bytes) -> bytes:
    m = HEADER.match(src)
    if m is None:
        raise SystemExit("check_readme_snippet: the example must begin with the repository's copyright/SPDX "
                         "header exactly; it is missing, malformed, or replaced by another comment")
    return src[m.end():]


def compare(readme: bytes, src: bytes) -> tuple[bool, str]:
    shown, actual = displayed(readme), source_without_header(src)
    if shown == actual:
        return True, ""
    a = actual.decode("utf-8", "replace").splitlines(True)
    b = shown.decode("utf-8", "replace").splitlines(True)
    return False, "".join(difflib.unified_diff(a, b, "examples/ReadmeSnippet.lean (header omitted)", "README.md block"))


def self_test() -> int:
    header = b"/-\nCopyright (c) 2026 Cameron Freer. All rights reserved.\nSPDX-License-Identifier: Apache-2.0\n-/\n"
    body = b"import A\n\nexample : True :=\n  trivial"
    src = header + body + b"\n"
    good = b"# T\n\n" + MARK + b"\n```lean\n" + body + b"\n```\n\ntext\n"
    problems = []
    if compare(good, src) != (True, ""):
        problems.append("exact match rejected")
    ok, _ = compare(good.replace(b"  trivial", b" trivial"), src)
    if ok:
        problems.append("an indentation difference was tolerated")
    ok, _ = compare(good.replace(b"import A\n\n", b"import A\n"), src)
    if ok:
        problems.append("a removed blank line was tolerated")
    ok, _ = compare(good.replace(b"example : True :=\n", b"example : True :=\r\n"), src)
    if ok:
        problems.append("a line-ending difference was tolerated")
    for bad, label in ((good.replace(MARK + b"\n", b""), "missing marker"), (good + MARK + b"\n```lean\nx\n```\n", "duplicate marker"),
                       (good.replace(MARK + b"\n```lean", MARK + b"\n\n```lean"), "marker not immediately followed by the block")):
        try:
            compare(bad, src)
            problems.append(f"{label} was accepted")
        except SystemExit:
            pass
    for bad_src, label in ((b"/-\nSome other comment\n-/\n" + body + b"\n", "an unexpected leading comment"),
                           (body + b"\n", "a missing header"),
                           (b"/-\nCopyright (c) 2026 Cameron Freer. All rights reserved.\n-/\n" + body + b"\n", "a malformed header (no SPDX line)"),
                           (b"/- x -/\n" + header + body + b"\n", "a comment before the header")):
        try:
            compare(good, bad_src)
            problems.append(f"{label} was accepted as the license header")
        except SystemExit:
            pass
    for line in problems:
        print("check_readme_snippet: self-test:", line)
    print(f"check_readme_snippet: self-test {'FAILED' if problems else 'passed'}")
    return 1 if problems else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    ok, diff = compare((ROOT / "README.md").read_bytes(), (ROOT / "examples" / "ReadmeSnippet.lean").read_bytes())
    if ok:
        print("check_readme_snippet: README example matches examples/ReadmeSnippet.lean (license header omitted)")
        return 0
    sys.stdout.write(diff)
    print("check_readme_snippet: MISMATCH")
    return 1


if __name__ == "__main__":
    sys.exit(main())
