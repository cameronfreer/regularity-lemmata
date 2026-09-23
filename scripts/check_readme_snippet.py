#!/usr/bin/env python3
# Copyright (c) 2026 Cameron Freer. All rights reserved.
# SPDX-License-Identifier: Apache-2.0
"""The README's displayed example must be `examples/ReadmeSnippet.lean` exactly, with only the
license header omitted.

The README marks the block with a line `<!-- readme-snippet -->` immediately followed by the
```lean fence. The comparison removes the source file's leading block comment (the
copyright/SPDX header) and the single newline that ends it, and nothing else: whitespace,
indentation, and blank lines inside the code are compared byte for byte. The marker must occur
exactly once. Exit 1 with a unified diff (or the marker problem) on any difference.

    python3 scripts/check_readme_snippet.py            # check the repository
    python3 scripts/check_readme_snippet.py --self-test
"""
import difflib
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
MARK = "<!-- readme-snippet -->"


def displayed(readme: str) -> str:
    n = readme.count(MARK)
    if n != 1:
        raise SystemExit(f"check_readme_snippet: expected exactly one marker '{MARK}', found {n}")
    i = readme.index(MARK)
    m = re.match(re.escape(MARK) + r"\n```lean\n(.*?)\n```\n", readme[i:], re.S)
    if m is None:
        raise SystemExit("check_readme_snippet: the marker must be immediately followed by a ```lean block")
    return m.group(1) + "\n"


def source_without_header(src: str) -> str:
    if not src.startswith("/-"):
        raise SystemExit("check_readme_snippet: the example does not start with a license header")
    end = src.index("-/\n") + len("-/\n")
    return src[end:]


def compare(readme: str, src: str) -> tuple[bool, str]:
    shown, actual = displayed(readme), source_without_header(src)
    if shown == actual:
        return True, ""
    return False, "".join(difflib.unified_diff(actual.splitlines(True), shown.splitlines(True),
                                              "examples/ReadmeSnippet.lean (header omitted)", "README.md block"))


def self_test() -> int:
    src = "/-\nCopyright.\nSPDX-License-Identifier: Apache-2.0\n-/\nimport A\n\nexample : True :=\n  trivial\n"
    body = "import A\n\nexample : True :=\n  trivial"
    good = f"# T\n\n{MARK}\n```lean\n{body}\n```\n\ntext\n"
    problems = []
    if compare(good, src) != (True, ""):
        problems.append("exact match rejected")
    ok, _ = compare(good.replace("  trivial", " trivial"), src)
    if ok:
        problems.append("an indentation difference was tolerated")
    ok, _ = compare(good.replace("import A\n\n", "import A\n"), src)
    if ok:
        problems.append("a removed blank line was tolerated")
    for bad, label in ((good.replace(MARK + "\n", ""), "missing marker"), (good + MARK + "\n```lean\nx\n```\n", "duplicate marker"),
                       (good.replace(MARK + "\n```lean", MARK + "\n\n```lean"), "marker not immediately followed by the block")):
        try:
            compare(bad, src)
            problems.append(f"{label} was accepted")
        except SystemExit:
            pass
    for line in problems:
        print("check_readme_snippet: self-test:", line)
    print(f"check_readme_snippet: self-test {'FAILED' if problems else 'passed'}")
    return 1 if problems else 0


def main() -> int:
    if "--self-test" in sys.argv:
        return self_test()
    ok, diff = compare((ROOT / "README.md").read_text(), (ROOT / "examples" / "ReadmeSnippet.lean").read_text())
    if ok:
        print("check_readme_snippet: README example matches examples/ReadmeSnippet.lean (license header omitted)")
        return 0
    sys.stdout.write(diff)
    print("check_readme_snippet: MISMATCH")
    return 1


if __name__ == "__main__":
    sys.exit(main())
