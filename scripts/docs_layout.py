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


def strip_library(argv: list[str]) -> int:
    deps = pathlib.Path(argv[0])
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
    ver = pathlib.Path(argv[0]).resolve()
    broken: list[str] = []
    checked = 0
    for page in sorted(ver.rglob("*.html")):
        parser = LinkCollector()
        parser.feed(page.read_text(errors="replace"))
        for link in parser.links:
            target = resolve(page.parent, link)
            if target is None:
                continue
            checked += 1
            if not target.exists():
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
    print(f"docs_layout: checked {checked} links and search targets, {len(broken)} broken")
    return 1 if broken else 0


def main() -> int:
    cmd, rest = sys.argv[1], sys.argv[2:]
    return {"rewrite-version": rewrite_version, "strip-library": strip_library, "check-links": check_links}[cmd](rest)


if __name__ == "__main__":
    sys.exit(main())
