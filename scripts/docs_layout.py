#!/usr/bin/env python3
"""Helpers for scripts/deploy_docs.sh: search-data rewriting, navbar stripping, link checking.

  docs_layout.py rewrite-version <version-dir> <deps-rel> <dep-dirs...>
      In the version's `declarations/declaration-data.bmp`, route every docLink and module
      url whose top-level directory is a dependency directory into the shared tree at
      `<deps-rel>` (a path relative to the version root, e.g. `../deps/<key>`); library
      targets stay version-local.

  docs_layout.py strip-library <deps-dir>
      In the shared tree's `declarations/declaration-data.bmp`, remove every entry that
      belongs to the library (declarations under `./RegularityLemmata/`, modules named
      `RegularityLemmata.*`, and their occurrences in instance and importedBy lists), and in
      the shared tree's `navbar.html` remove the library's navigation sections (the nested
      `<details data-path="./RegularityLemmata*.html">` blocks and any stray library link),
      so the shared tree never dangles into a version directory.

  docs_layout.py merge-deps <deps-dir> <doc-gen output dir> <dep-dirs...>
      Bring an already published shared tree up to date with a new build without assuming the
      build's import closure contains the published one (it can grow, and it can shrink when
      an older release is rebuilt or an import is removed). Dependency pages and `find/`
      redirects are only ever added, never overwritten or removed; the shared search index
      becomes the union of the published and the built indexes (published entries kept,
      `importedBy` and instance lists unioned); the navigation tree becomes the union of both
      module trees; the remaining top-level files (assets, general pages) come from the build.
      `strip-library` is expected to run afterwards.

  docs_layout.py deploy-test
      End-to-end test of scripts/deploy_docs.sh on synthetic trees: a first publication, a
      later version with a larger import closure (the new dependency page, search entry, and
      navigation entry appear in the shared tree), an older version with a smaller closure
      rebuilt afterwards (the pages, search entries, and navigation entries of the larger
      closure are preserved and the layout still passes the link check), and the `latest`
      guard (a non-release version name and a missing release-tag verification are refused,
      a lower release does not move `latest`). Exit status 1 on any failure.

  docs_layout.py check-links <dir> [--shared [--source <doc-gen output dir>]]
      Resolve every relative href/src of every HTML page under the directory, and every
      docLink and module url of its search data, against the file system; report and fail
      on any target that does not exist. External (`http`, `mailto`, `data:`) and
      fragment-only links are skipped; fragments are stripped before resolving. With
      `--shared` (the dependency tree) the failing conditions are: any link into
      `RegularityLemmata` anywhere, any broken link in the navigation (`navbar.html`) or in
      the top-level pages, any broken search target, and any broken link inside a dependency
      page body that is NOT already broken in the untouched doc-gen4 output given by
      `--source`: the exact (page, target) pairs are compared, so doc-gen4's own defects are
      tolerated while a defect introduced by the layout fails. Without `--source`, every
      broken body link fails.

  docs_layout.py self-test
      Build a small synthetic tree (a library page, a dependency page, a navbar with a nested
      library section, a search index with both) and require that: check-links reports a
      planted broken page link and a planted broken search target; strip-library removes
      every library entry from the navbar and the index while keeping the dependency ones;
      the stripped tree passes check-links --shared; check-links --shared rejects a library
      link and a broken navigation link; a dependency-body defect that is also broken in the
      `--source` output is tolerated while a newly introduced one fails, and without
      `--source` every such defect fails. Exit status 1 on any failure.
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


# ---- shared-tree merging -------------------------------------------------------------------

_SECT = re.compile(r'<details class="nav_sect"(?: data-path="([^"]*)")?><summary>(.*?)</summary>', re.S)
_LINK = re.compile(r'<div class="nav_link"><a href="([^"]*)">([^<]*)</a></div>')
_END = re.compile(r"</details>")


def _summary_name(summary: str) -> str:
    return re.sub(r"<[^>]*>", "", summary).split(" (")[0].strip()


def parse_module_list(text: str) -> tuple[int, int, dict]:
    """Locate `<div class="module_list">...</div>` in a navbar and parse it into a tree
    `{name: node}` with `node = {"kind": "sect"|"link", "path"|"href", "summary"|"label",
    "children"}`. Returns (start, end) offsets of the list's inner html and the tree."""
    open_tag = '<div class="module_list">'
    i = text.index(open_tag)
    depth, end = 0, None
    for m in re.finditer(r"<div\b|</div>", text[i:]):
        depth += 1 if m.group().startswith("<div") else -1
        if depth == 0:
            end = i + m.start()
            break
    if end is None:
        raise ValueError("unbalanced module_list")
    inner = text[i + len(open_tag):end]
    root: dict = {}
    stack: list[dict] = [root]
    pos = 0
    token = re.compile(r'<details class="nav_sect"|<div class="nav_link">|</details>')
    while True:
        m = token.search(inner, pos)
        if not m:
            break
        if m.group() == "</details>":
            stack.pop()
            pos = m.end()
        elif m.group().startswith("<details"):
            ms = _SECT.match(inner, m.start())
            if not ms:
                raise ValueError("unrecognized navigation section")
            name = _summary_name(ms.group(2))
            node = {"kind": "sect", "path": ms.group(1), "summary": ms.group(2), "children": {}}
            stack[-1][name] = node
            stack.append(node["children"])
            pos = ms.end()
        else:
            ml = _LINK.match(inner, m.start())
            if not ml:
                raise ValueError("unrecognized navigation link")
            stack[-1][ml.group(2)] = {"kind": "link", "href": ml.group(1), "label": ml.group(2)}
            pos = ml.end()
    return i + len(open_tag), end, root


def _sect_with_page(name: str, href: str, children: dict) -> dict:
    """A section that also carries the module's own page, in doc-gen4's form."""
    return {"kind": "sect", "path": href, "summary": f'{name} (<a href="{href}">file</a>)',
            "children": children}


def merge_trees(old: dict, new: dict) -> dict:
    """Union of two navigation trees, symmetric in what it keeps: sections merge their
    children; a module link met by a directory-only section of the same name becomes a
    section that carries the page link; of two sections, the one with a page link supplies
    the path and summary (the published one when both have it)."""
    out: dict = {}
    for name in sorted(set(old) | set(new)):
        a, b = old.get(name), new.get(name)
        if a is None or b is None:
            out[name] = a or b
        elif a["kind"] == "sect" and b["kind"] == "sect":
            with_page = a if a["path"] else (b if b["path"] else a)
            out[name] = {"kind": "sect", "path": with_page["path"], "summary": with_page["summary"],
                         "children": merge_trees(a["children"], b["children"])}
        elif a["kind"] == "sect" or b["kind"] == "sect":
            sect, link = (a, b) if a["kind"] == "sect" else (b, a)
            if sect["path"]:
                out[name] = sect
            else:
                out[name] = _sect_with_page(name, link["href"], sect["children"])
        else:
            out[name] = a
    return out


def serialize_tree(tree: dict) -> str:
    parts = []
    for name in sorted(tree):
        node = tree[name]
        if node["kind"] == "link":
            parts.append(f'<div class="nav_link"><a href="{node["href"]}">{node["label"]}</a></div>')
        else:
            attr = f' data-path="{node["path"]}"' if node.get("path") else ""
            parts.append(f'<details class="nav_sect"{attr}><summary>{node["summary"]}</summary>'
                         + serialize_tree(node["children"]) + "</details>")
    return "".join(parts)


def merge_navbars(published: str, built: str) -> str:
    """The built navbar's chrome with the union of both module trees."""
    _, _, old = parse_module_list(published)
    i, j, new = parse_module_list(built)
    return built[:i] + serialize_tree(merge_trees(old, new)) + built[j:]


def merge_index(published: dict, built: dict) -> dict:
    out = {k: v for k, v in published.items()}
    decls = dict(published.get("declarations", {}))
    for k, v in built.get("declarations", {}).items():
        decls.setdefault(k, v)
    out["declarations"] = decls
    mods = {k: dict(v) for k, v in published.get("modules", {}).items()}
    for k, v in built.get("modules", {}).items():
        if k in mods:
            seen = list(mods[k].get("importedBy", []))
            for x in v.get("importedBy", []):
                if x not in seen:
                    seen.append(x)
            mods[k]["importedBy"] = seen
        else:
            mods[k] = dict(v)
    out["modules"] = mods
    for key in ("instances", "instancesFor"):
        table = {k: list(v) for k, v in published.get(key, {}).items()}
        for k, v in built.get(key, {}).items():
            cur = table.setdefault(k, [])
            for x in v:
                if x not in cur:
                    cur.append(x)
        out[key] = table
    for k, v in built.items():
        out.setdefault(k, v)
    return out


def merge_deps(argv: list[str]) -> int:
    deps, source, names = pathlib.Path(argv[0]), pathlib.Path(argv[1]), argv[2:]
    added = 0
    for n in names + ["find"]:
        src = source / n
        if not src.is_dir():
            continue
        for f in sorted(src.rglob("*")):
            if not f.is_file():
                continue
            target = deps / f.relative_to(source)
            if not target.exists():
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(f.read_bytes())
                added += 1
    for f in sorted(source.iterdir()):
        if f.is_file() and not f.name.startswith(LIB) and f.name != "navbar.html":
            (deps / f.name).write_bytes(f.read_bytes())
    nav_old, nav_new = deps / "navbar.html", source / "navbar.html"
    if nav_old.exists() and nav_new.exists():
        nav_old.write_text(merge_navbars(nav_old.read_text(), nav_new.read_text()))
    elif nav_new.exists():
        nav_old.write_text(nav_new.read_text())
    idx_old, idx_new = deps / "declarations" / "declaration-data.bmp", source / "declarations" / "declaration-data.bmp"
    if idx_old.exists() and idx_new.exists():
        merged = merge_index(load(idx_old), load(idx_new))
        dump(idx_old, merged)
        print(f"docs_layout: merged shared index: {len(merged['declarations'])} declarations, {len(merged['modules'])} modules")
    elif idx_new.exists():
        idx_old.parent.mkdir(parents=True, exist_ok=True)
        idx_old.write_bytes(idx_new.read_bytes())
    print(f"docs_layout: merged the shared tree: {added} dependency page(s)/redirect(s) added, none overwritten")
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


def body_broken_pairs(source: pathlib.Path) -> set[tuple[str, str]]:
    """The (page, link) pairs of broken relative links inside the bodies of the dependency pages
    of an untouched doc-gen4 output directory (pages outside `RegularityLemmata/` and below the
    top level)."""
    pairs: set[tuple[str, str]] = set()
    for page in sorted(source.rglob("*.html")):
        rel = page.relative_to(source)
        if page.parent == source or rel.parts[0] == LIB:
            continue
        parser = LinkCollector()
        parser.feed(page.read_text(errors="replace"))
        for link in parser.links:
            target = resolve(page.parent, link)
            if target is not None and not target.exists():
                pairs.add((str(rel), link))
    return pairs


def check_links(argv: list[str]) -> int:
    shared = "--shared" in argv
    valued = ("--source", "--allowances")
    positional = [a for i, a in enumerate(argv) if not a.startswith("--") and (i == 0 or argv[i - 1] not in valued)]
    ver = pathlib.Path(positional[0]).resolve()
    source = pathlib.Path(argv[argv.index("--source") + 1]).resolve() if "--source" in argv else None
    allowances = pathlib.Path(argv[argv.index("--allowances") + 1]) if "--allowances" in argv else None
    baseline = body_broken_pairs(source) if (shared and source is not None) else None
    if baseline is not None and allowances is not None and allowances.exists():
        # Previously validated exact pairs, kept only for retained pages that this build does
        # not cover (their content is unchanged: pages are never overwritten). A page the build
        # does cover is judged against the build alone, so a newly introduced defect fails.
        covered = {str(p.relative_to(source)) for p in source.rglob("*.html")}
        for page, link in json.loads(allowances.read_text()):
            if page not in covered:
                baseline.add((page, link))
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
                    pair = (str(page.relative_to(ver)), link)
                    if baseline is not None and pair not in baseline:
                        broken.append(f"{pair[0]} -> {link} (broken dependency-body link not present in the doc-gen4 output)")
                    elif baseline is None:
                        broken.append(f"{pair[0]} -> {link} (broken dependency-body link; no --source baseline given)")
                    else:
                        upstream.append(f"{pair[0]} -> {link}")
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
        print(f"docs_layout: {len(upstream)} broken links inside dependency page bodies, each also broken in the doc-gen4 output (tolerated), e.g. {upstream[0]}")
    print(f"docs_layout: checked {checked} links and search targets, {len(broken)} broken")
    if not broken and allowances is not None and baseline is not None:
        pairs = sorted({tuple(x.split(" -> ", 1)) for x in upstream})
        allowances.write_text(json.dumps(pairs))
        print(f"docs_layout: recorded {len(pairs)} validated upstream-defect allowance(s) in {allowances.name}")
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
        src = pathlib.Path(tempfile.mkdtemp())  # outside the checked tree
        (src / "Mathlib").mkdir(parents=True)
        (src / "RegularityLemmata").mkdir()
        (src / "Mathlib" / "B.html").write_text('<a href="../Mathlib/Absent.html">upstream</a>')
        (src / "RegularityLemmata" / "X.html").write_text('<a href="../Nope.html">library defect, not a baseline entry</a>')
        (root / "Mathlib" / "B.html").write_text('<a href="../Mathlib/Absent.html">upstream</a>')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared", "--source", str(src)])
        if rc != 0:
            problems.append("check-links --shared failed on a baseline dependency-body defect")
        (root / "Mathlib" / "B.html").write_text('<a href="../Mathlib/Absent.html">upstream</a><a href="../Mathlib/New.html">new</a>')
        buf = io.StringIO()
        with contextlib.redirect_stdout(buf):
            rc = check_links([str(root), "--shared", "--source", str(src)])
        if rc == 0 or "New.html" not in buf.getvalue():
            problems.append("check-links --shared accepted a newly introduced broken dependency-body link")
        (root / "Mathlib" / "B.html").write_text('<a href="../Mathlib/Absent.html">upstream</a>')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc == 0:
            problems.append("check-links --shared without --source accepted a broken dependency-body link")
        shutil.rmtree(src)
        nav = (root / "navbar.html").read_text()
        (root / "navbar.html").write_text(nav + '<div class="nav_link"><a href="./Mathlib/Nowhere.html">n</a></div>')
        with contextlib.redirect_stdout(io.StringIO()):
            rc = check_links([str(root), "--shared"])
        if rc == 0:
            problems.append("check-links --shared accepted a broken navigation link")
    # merge-deps: navigation and index unions in both directions
    nav_a = ('<html><body><nav><div class="module_list">'
             '<details class="nav_sect" data-path="./Mathlib.html"><summary>Mathlib (<a href="./Mathlib.html">file</a>)</summary>'
             '<div class="nav_link"><a href="./Mathlib/A.html">A</a></div>'
             '<div class="nav_link"><a href="./Mathlib/B.html">B</a></div></details></div><div id="settings"></div></nav></body></html>')
    nav_b = ('<html><body><nav><div class="module_list">'
             '<details class="nav_sect" data-path="./Mathlib.html"><summary>Mathlib (<a href="./Mathlib.html">file</a>)</summary>'
             '<div class="nav_link"><a href="./Mathlib/A.html">A</a></div>'
             '<details class="nav_sect" data-path="./Mathlib/C.html"><summary>C</summary>'
             '<div class="nav_link"><a href="./Mathlib/C/D.html">D</a></div></details></details></div><div id="settings"></div></nav></body></html>')
    merged = merge_navbars(nav_a, nav_b)
    for needle in ('Mathlib/A.html', 'Mathlib/B.html', 'Mathlib/C.html', 'Mathlib/C/D.html'):
        if needle not in merged:
            problems.append(f"merge-deps navbar union lost {needle}")
    if merge_navbars(nav_b, nav_a) != merged.replace('', ''):
        # the union must not depend on which side was published
        if set(re.findall(r'href="([^"]*)"', merge_navbars(nav_b, nav_a))) != set(re.findall(r'href="([^"]*)"', merged)):
            problems.append("merge-deps navbar union is not symmetric")
    _, _, tree = parse_module_list(merged)
    if serialize_tree(tree) != serialize_tree(merge_trees(tree, {})):
        problems.append("merge-deps navbar serialization is not stable")
    # a module link on one side, a directory-only section on the other: both survive, either order
    link_side = {"Foo": {"kind": "link", "href": "./Mathlib/Foo.html", "label": "Foo"}}
    dir_side = {"Foo": {"kind": "sect", "path": None, "summary": "Foo",
                        "children": {"Bar": {"kind": "link", "href": "./Mathlib/Foo/Bar.html", "label": "Bar"}}}}
    for x, y in ((link_side, dir_side), (dir_side, link_side)):
        t = merge_trees(x, y)
        html_out = serialize_tree(t)
        if 'data-path="./Mathlib/Foo.html"' not in html_out or "Mathlib/Foo/Bar.html" not in html_out \
                or 'href="./Mathlib/Foo.html">file' not in html_out:
            problems.append("merge-deps lost the module link or the children when a link met a directory section")
    paged = {"Foo": _sect_with_page("Foo", "./Mathlib/Foo.html", {"Baz": {"kind": "link", "href": "./Mathlib/Foo/Baz.html", "label": "Baz"}})}
    for x, y in ((paged, dir_side), (dir_side, paged)):
        html_out = serialize_tree(merge_trees(x, y))
        if 'data-path="./Mathlib/Foo.html"' not in html_out or "Foo/Bar.html" not in html_out or "Foo/Baz.html" not in html_out:
            problems.append("merge-deps lost the page link or a child when only one section had a page link")
    idx = merge_index(
        {"declarations": {"a": {"docLink": "./Mathlib/A.html#a"}}, "modules": {"Mathlib.A": {"url": "./Mathlib/A.html", "importedBy": ["X"]}},
         "instances": {"I": ["a"]}, "instancesFor": {}},
        {"declarations": {"b": {"docLink": "./Mathlib/B.html#b"}, "a": {"docLink": "./elsewhere.html#a"}},
         "modules": {"Mathlib.A": {"url": "./Mathlib/A.html", "importedBy": ["Y"]}, "Mathlib.B": {"url": "./Mathlib/B.html", "importedBy": []}},
         "instances": {"I": ["b"], "J": ["b"]}, "instancesFor": {"b": ["I"]}})
    if (idx["declarations"]["a"]["docLink"] != "./Mathlib/A.html#a" or "b" not in idx["declarations"]
            or idx["modules"]["Mathlib.A"]["importedBy"] != ["X", "Y"] or "Mathlib.B" not in idx["modules"]
            or idx["instances"]["I"] != ["a", "b"] or idx["instances"].get("J") != ["b"] or idx["instancesFor"].get("b") != ["I"]):
        problems.append("merge-deps index union is wrong")
    for line in problems:
        print("docs_layout: self-test:", line)
    print(f"docs_layout: self-test {'FAILED' if problems else 'passed'}")
    return 1 if problems else 0


def _fixture(root: pathlib.Path, modules: list[str], defects: dict[str, str] | None = None) -> None:
    """A synthetic doc-gen4 output: one library page linking to every dependency module page,
    the dependency pages, a navbar, a search index, `find/` redirects, and assets."""
    import shutil
    if root.exists():
        shutil.rmtree(root)
    (root / LIB / "Finite").mkdir(parents=True)
    (root / "Mathlib").mkdir()
    (root / "declarations").mkdir()
    (root / "find").mkdir()
    (root / "style.css").write_text("")
    (root / "index.html").write_text('<a href="./navbar.html">n</a>')
    (root / "Mathlib.html").write_text('<a href="./style.css">s</a>')
    (root / f"{LIB}.html").write_text('<a href="./style.css">s</a>')
    (root / "find" / "index.html").write_text('<a href=".././style.css">s</a>')
    # doc-gen4 links carry the site-root prefix followed by `./<top-level>/...`
    (root / LIB / "Finite" / "A.html").write_text(
        "".join(f'<a href="../.././Mathlib/{m}.html#Mathlib.{m}.thm">{m}</a>' for m in modules))
    for m in modules:
        extra = f'<a href="{defects[m]}">upstream</a>' if defects and m in defects else ""
        (root / "Mathlib" / f"{m}.html").write_text('<a href=".././style.css">s</a>' + extra)
    links = "".join(f'<div class="nav_link"><a href="./Mathlib/{m}.html">{m}</a></div>' for m in modules)
    (root / "navbar.html").write_text(
        '<html><body><nav><div class="module_list">'
        '<details class="nav_sect" data-path="./Mathlib.html"><summary>Mathlib (<a href="./Mathlib.html">file</a>)</summary>'
        + links + '</details>'
        f'<details class="nav_sect" data-path="./{LIB}.html"><summary>{LIB}</summary>'
        f'<div class="nav_link"><a href="./{LIB}/Finite/A.html">A</a></div></details>'
        '</div><div id="settings"></div></nav></body></html>')
    decls = {f"Mathlib.{m}.thm": {"docLink": f"./Mathlib/{m}.html#Mathlib.{m}.thm", "kind": "theorem"} for m in modules}
    decls[f"{LIB}.a"] = {"docLink": f"./{LIB}/Finite/A.html#a", "kind": "theorem"}
    mods = {f"Mathlib.{m}": {"url": f"./Mathlib/{m}.html", "importedBy": [f"{LIB}.Finite.A"]} for m in modules}
    mods[f"{LIB}.Finite.A"] = {"url": f"./{LIB}/Finite/A.html", "importedBy": []}
    dump(root / "declarations" / "declaration-data.bmp",
         {"declarations": decls, "instances": {}, "instancesFor": {}, "modules": mods})


def deploy_test(argv: list[str]) -> int:
    import os
    import shutil
    import subprocess
    import tempfile
    script = pathlib.Path(__file__).resolve().parent / "deploy_docs.sh"
    problems: list[str] = []
    with tempfile.TemporaryDirectory() as tmp:
        tmp = pathlib.Path(tmp)
        src, pages = tmp / "src", tmp / "pages"
        pages.mkdir()

        def run(version: str, modules: list[str], defects: dict[str, str] | None = None,
                **extra: str) -> tuple[int, str]:
            _fixture(src, modules, defects)
            env = {**os.environ, "DOCS_SRC": str(src), "DOCS_VERSION": version, "DEPS_KEY": "k1",
                   "PAGES_DIR": str(pages), "SIZE_LIMIT_BYTES": "900000000"}
            env.pop("DOCS_UPDATE_LATEST", None)
            env.pop("DOCS_RELEASE_TAG_OK", None)
            env.update(extra)
            r = subprocess.run(["bash", str(script)], env=env, capture_output=True, text=True)
            return r.returncode, r.stdout + r.stderr

        deps = pages / "docs" / "deps" / "k1"

        def shared_has(module: str) -> tuple[bool, bool, bool]:
            page = (deps / "Mathlib" / f"{module}.html").exists()
            nav = f"Mathlib/{module}.html" in (deps / "navbar.html").read_text()
            idx = f"Mathlib.{module}.thm" in load(deps / "declarations" / "declaration-data.bmp")["declarations"]
            return page, nav, idx

        rc, out = run("v0.0.1", ["A", "B"], DOCS_UPDATE_LATEST="1", DOCS_RELEASE_TAG_OK="1")
        if rc != 0:
            problems.append("first publication failed:\n" + out)
        if "latest -> v0.0.1" not in out:
            problems.append("first release did not set latest")
        # 1. a larger closure: the new page, its search entry, and its navigation entry appear;
        #    the new page C carries an upstream defect (also broken in the doc-gen4 output)
        upstream = {"C": ".././Mathlib/Absent.html"}
        rc, out = run("v0.0.2", ["A", "B", "C"], upstream, DOCS_UPDATE_LATEST="1", DOCS_RELEASE_TAG_OK="1")
        if rc != 0:
            problems.append("growing closure failed:\n" + out)
        if shared_has("C") != (True, True, True):
            problems.append(f"growing closure did not add page/navigation/search for C: {shared_has('C')}")
        if "1 dependency page(s)/redirect(s) added" not in out:
            problems.append("growing closure did not report exactly one added page")
        if "1 broken links inside dependency page bodies" not in out:
            problems.append("growing closure did not tolerate the upstream defect of the new page")
        if not (deps / "upstream-defects.json").exists() or "Mathlib/C.html" not in (deps / "upstream-defects.json").read_text():
            problems.append("the validated upstream-defect allowance was not recorded")
        # 2. an older, smaller closure rebuilt afterwards: nothing is lost, and the retained page's
        #    validated upstream defect (no longer covered by the build) stays tolerated
        rc, out = run("v0.0.1", ["A"])
        if rc != 0:
            problems.append("smaller closure rebuild failed:\n" + out)
        if "1 broken links inside dependency page bodies" not in out:
            problems.append("smaller closure rebuild did not carry the retained page's allowance forward")
        # a defect that was never validated is still rejected on a retained page
        (deps / "Mathlib" / "B.html").write_text('<a href=".././style.css">s</a><a href=".././Mathlib/Never.html">new</a>')
        rc, out = run("v0.0.1", ["A"])
        if rc == 0 or "Never.html" not in out:
            problems.append("a newly introduced defect on a retained page was tolerated")
        (deps / "Mathlib" / "B.html").write_text('<a href=".././style.css">s</a>')
        for m in ("B", "C"):
            if shared_has(m) != (True, True, True):
                problems.append(f"smaller closure rebuild lost page/navigation/search for {m}: {shared_has(m)}")
        if (deps / f"{LIB}.html").exists() or LIB in (deps / "navbar.html").read_text():
            problems.append("library material leaked into the shared tree")
        if "latest -> " in out:
            problems.append("a rebuild without DOCS_UPDATE_LATEST moved latest")
        # 3. the latest guard
        rc, out = run("zz-preview", ["A"], DOCS_UPDATE_LATEST="1", DOCS_RELEASE_TAG_OK="1")
        if rc == 0:
            problems.append("a non-release version name was allowed to update latest")
        rc, out = run("v0.0.3", ["A"], DOCS_UPDATE_LATEST="1")
        if rc == 0:
            problems.append("latest update without release-tag verification was allowed")
        rc, out = run("v0.0.1", ["A"], DOCS_UPDATE_LATEST="1", DOCS_RELEASE_TAG_OK="1")
        if rc != 0 or "latest left unchanged" not in out:
            problems.append("a lower release moved latest or failed:\n" + out)
        if "v0.0.2" not in (pages / "docs" / "latest" / "index.html").read_text():
            problems.append("latest no longer points at the newest release")
        for d in ("zz-preview", "v0.0.3"):
            shutil.rmtree(pages / "docs" / d, ignore_errors=True)
    for line in problems:
        print("docs_layout: deploy-test:", line)
    print(f"docs_layout: deploy-test {'FAILED' if problems else 'passed'}")
    return 1 if problems else 0


def main() -> int:
    cmd, rest = sys.argv[1], sys.argv[2:]
    return {"rewrite-version": rewrite_version, "strip-library": strip_library,
            "merge-deps": merge_deps, "check-links": check_links, "self-test": self_test,
            "deploy-test": deploy_test}[cmd](rest)


if __name__ == "__main__":
    sys.exit(main())
