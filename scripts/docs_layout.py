#!/usr/bin/env python3
"""Helpers for scripts/deploy_docs.sh: search-data rewriting and link checking.

  docs_layout.py rewrite-version <version-dir> <deps-rel> <dep-dirs...>
      In the version's `declarations/declaration-data.bmp`, route every docLink and module
      url whose top-level directory is a dependency directory into the shared tree at
      `<deps-rel>` (a path relative to the version root, e.g. `../deps/<key>`); library
      targets stay version-local.

  docs_layout.py strip-library <deps-dir>
      In the shared tree's `declarations/declaration-data.bmp`, remove every entry that
      belongs to the library (declarations under `./RegularityLemmata/`, modules named
      `RegularityLemmata.*`, and their occurrences in instance and importedBy lists), so the
      shared index never dangles into a version directory.

  docs_layout.py check-links <version-dir>
      Resolve every relative href/src of every HTML page under the version directory, and
      every docLink and module url of its search data, against the file system; report and
      fail on any target that does not exist. External (`http`, `mailto`, `data:`) and
      fragment-only links are skipped; fragments are stripped before resolving.
"""
import html.parser
import json
import pathlib
import re
import sys
import urllib.parse

LIB = "RegularityLemmata"


def load(p: pathlib.Path):
    return json.loads(p.read_text())


def dump(p: pathlib.Path, data) -> None:
    p.write_text(json.dumps(data, separators=(",", ":")))


def rewrite_version(argv: list[str]) -> int:
    ver, deps_rel, deps = pathlib.Path(argv[0]), argv[1], set(argv[2:])
    p = ver / "declarations" / "declaration-data.bmp"
    data = load(p)
    pat = re.compile(r"^\./(" + "|".join(map(re.escape, sorted(deps))) + r")/")
    n = 0
    for entry in data.get("declarations", {}).values():
        link = entry.get("docLink", "")
        if pat.match(link):
            entry["docLink"] = pat.sub(f"./{deps_rel}/\\1/", link)
            n += 1
    for entry in data.get("modules", {}).values():
        url = entry.get("url", "")
        if pat.match(url):
            entry["url"] = pat.sub(f"./{deps_rel}/\\1/", url)
            n += 1
    dump(p, data)
    print(f"docs_layout: rewrote {n} search targets into {deps_rel}")
    return 0


def strip_navbar(text: str) -> tuple[str, int]:
    """Remove the library's (nested) navigation sections and stray library links."""
    removed = 0
    while True:
        m = re.search(r'<details[^>]*data-path="\./RegularityLemmata[^"]*"[^>]*>', text)
        if not m:
            break
        depth, i = 1, m.end()
        for tag in re.finditer(r"<details\b|</details>", text[m.end():]):
            depth += 1 if tag.group().startswith("<details") else -1
            if depth == 0:
                i = m.end() + tag.end()
                break
        text = text[: m.start()] + text[i:]
        removed += 1
    text, n = re.subn(r'<div class="nav_link"><a href="\./RegularityLemmata[^"]*">[^<]*</a></div>', "", text)
    return text, removed + n


def strip_library(argv: list[str]) -> int:
    deps = pathlib.Path(argv[0])
    nav = deps / "navbar.html"
    if nav.exists():
        text, n = strip_navbar(nav.read_text())
        nav.write_text(text)
        print(f"docs_layout: stripped {n} library navigation entries from the shared navbar")
    p = deps / "declarations" / "declaration-data.bmp"
    data = load(p)
    decls = data.get("declarations", {})
    removed = {
        name for name, e in decls.items()
        if e.get("docLink", "").startswith((f"./{LIB}/", f"./{LIB}.html", f"./{LIB}Gates"))
    }
    for name in removed:
        del decls[name]
    mods = data.get("modules", {})
    lib_mods = {m for m in mods if m == LIB or m.startswith(LIB + ".")}
    for m in lib_mods:
        del mods[m]
    for e in mods.values():
        if "importedBy" in e:
            e["importedBy"] = [m for m in e["importedBy"] if m not in lib_mods]
    for key in ("instances", "instancesFor"):
        table = data.get(key, {})
        for k in list(table):
            table[k] = [x for x in table[k] if x not in removed]
            if k in removed or not table[k]:
                del table[k]
    dump(p, data)
    print(f"docs_layout: stripped {len(removed)} library declarations and {len(lib_mods)} modules from the shared index")
    return 0


class LinkCollector(html.parser.HTMLParser):
    def __init__(self):
        super().__init__()
        self.links: list[str] = []

    def handle_starttag(self, tag, attrs):
        for k, v in attrs:
            if k in ("href", "src") and v:
                self.links.append(v)


def resolve(base: pathlib.Path, link: str) -> pathlib.Path | None:
    if re.match(r"^[a-z][a-z0-9+.-]*:", link) or link.startswith("//") or link.startswith("#"):
        return None
    path = urllib.parse.unquote(link.split("#", 1)[0].split("?", 1)[0])
    if not path:
        return None
    return (base / path).resolve()


def check_links(argv: list[str]) -> int:
    shared = "--shared" in argv
    ver = pathlib.Path([a for a in argv if not a.startswith("--")][0]).resolve()
    broken: list[str] = []
    upstream: list[str] = []
    checked = 0
    lib_link = re.compile(r'(href|src)="[^"]*(^|/)RegularityLemmata(/|\.html|Gates)[^"]*"')
    for page in sorted(ver.rglob("*.html")):
        text = page.read_text(errors="replace")
        toplevel = page.parent == ver
        if shared:
            for m in lib_link.finditer(text):
                broken.append(f"{page.relative_to(ver)} -> {m.group(0)} (library link in the shared tree)")
        parser = LinkCollector()
        parser.feed(text)
        for link in parser.links:
            target = resolve(page.parent, link)
            if target is None:
                continue
            checked += 1
            if not target.exists():
                if shared and not toplevel:
                    upstream.append(f"{page.relative_to(ver)} -> {link}")
                else:
                    broken.append(f"{page.relative_to(ver)} -> {link}")
    data = load(ver / "declarations" / "declaration-data.bmp")
    for name, e in data.get("declarations", {}).items():
        target = resolve(ver, e.get("docLink", ""))
        if target is not None:
            checked += 1
            if not target.exists():
                broken.append(f"search: {name} -> {e['docLink']}")
    for name, e in data.get("modules", {}).items():
        target = resolve(ver, e.get("url", ""))
        if target is not None:
            checked += 1
            if not target.exists():
                broken.append(f"module: {name} -> {e['url']}")
    for line in broken[:200]:
        print("docs_layout: broken", line)
    if len(broken) > 200:
        print(f"docs_layout: ... {len(broken) - 200} more")
    if upstream:
        print(f"docs_layout: {len(upstream)} broken links inside dependency page bodies (doc-gen4 output, not failing), e.g. {upstream[0]}")
    print(f"docs_layout: checked {checked} links and search targets, {len(broken)} broken")
    return 1 if broken else 0


def self_test(argv: list[str]) -> int:
    import contextlib
    import io
    import shutil
    import tempfile
    problems: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        root = pathlib.Path(tmp)
        (root / "RegularityLemmata" / "Finite").mkdir(parents=True)
        (root / "Mathlib").mkdir()
        (root / "declarations").mkdir()
        (root / "RegularityLemmata" / "Finite" / "A.html").write_text('<a href="../../Mathlib/B.html">B</a>')
        (root / "Mathlib" / "B.html").write_text('<a href="../style.css">s</a><a href="../missing.html">x</a>')
        (root / "style.css").write_text("")
        (root / "RegularityLemmata.html").write_text("")
        (root / "navbar.html").write_text(
            '<nav><details class="nav_sect" data-path="./Mathlib.html"><summary>Mathlib</summary>'
            '<div class="nav_link"><a href="./Mathlib/B.html">B</a></div></details>'
            '<details class="nav_sect" data-path="./RegularityLemmata.html"><summary>RegularityLemmata</summary>'
            '<details class="nav_sect" data-path="./RegularityLemmata/Finite.html"><summary>Finite</summary>'
            '<div class="nav_link"><a href="./RegularityLemmata/Finite/A.html">A</a></div></details></details>'
            '<div class="nav_link"><a href="./RegularityLemmata/Finite/A.html">stray</a></div></nav>')
        dump(root / "declarations" / "declaration-data.bmp", {
            "declarations": {"RegularityLemmata.a": {"docLink": "./RegularityLemmata/Finite/A.html#a"},
                             "Mathlib.b": {"docLink": "./Mathlib/B.html#b"},
                             "Mathlib.gone": {"docLink": "./Mathlib/Gone.html#gone"}},
            "instances": {"Foo": ["RegularityLemmata.a", "Mathlib.b"]},
            "instancesFor": {"RegularityLemmata.a": ["Mathlib.b"]},
            "modules": {"RegularityLemmata.Finite.A": {"url": "./RegularityLemmata/Finite/A.html", "importedBy": []},
                        "Mathlib.B": {"url": "./Mathlib/B.html", "importedBy": ["RegularityLemmata.Finite.A"]}}})
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check_links([str(root)])
        out = buf.getvalue()
        if rc == 0 or "missing.html" not in out or "Mathlib.gone" not in out:
            problems.append("check-links did not report the planted broken page link and search target")
        (root / "Mathlib" / "B.html").write_text('<a href="../style.css">s</a>')
        (root / "Mathlib" / "Gone.html").write_text("")
        with contextlib.redirect_stdout(io.StringIO()):
            strip_library([str(root)])
        nav = (root / "navbar.html").read_text()
        if "RegularityLemmata" in nav or "Mathlib/B.html" not in nav:
            problems.append("strip-library left library navigation or removed dependency navigation")
        data = load(root / "declarations" / "declaration-data.bmp")
        if (any("RegularityLemmata" in k for k in data["declarations"])
                or "RegularityLemmata.Finite.A" in data["modules"]
                or data["modules"]["Mathlib.B"]["importedBy"]
                or "RegularityLemmata.a" in data["instances"].get("Foo", [])
                or "RegularityLemmata.a" in data["instancesFor"]):
            problems.append("strip-library left library entries in the search index")
        (root / "RegularityLemmata.html").unlink()
        shutil.rmtree(root / "RegularityLemmata")
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc != 0:
            problems.append("stripped shared tree does not pass check-links --shared")
        (root / "Mathlib" / "B.html").write_text('<a href="../RegularityLemmata.html">lib</a>')
        (root / "RegularityLemmata.html").write_text("")
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc == 0:
            problems.append("check-links --shared accepted a library link in the shared tree")
        (root / "RegularityLemmata.html").unlink()
        (root / "Mathlib" / "B.html").write_text('<a href="../Mathlib/Absent.html">upstream</a>')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc != 0:
            problems.append("check-links --shared failed on a broken link inside a dependency page body")
        nav = (root / "navbar.html").read_text()
        (root / "navbar.html").write_text(nav + '<div class="nav_link"><a href="./Mathlib/Nowhere.html">n</a></div>')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc == 0:
            problems.append("check-links --shared accepted a broken navigation link")
    for line in problems:
        print("docs_layout: self-test:", line)
    print(f"docs_layout: self-test {'FAILED' if problems else 'passed'}")
    return 1 if problems else 0


def main() -> int:
    cmd, rest = sys.argv[1], sys.argv[2:]
    return {"rewrite-version": rewrite_version, "strip-library": strip_library,
            "check-links": check_links, "self-test": self_test}[cmd](rest)


if __name__ == "__main__":
    sys.exit(main())
