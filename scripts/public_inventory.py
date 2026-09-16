#!/usr/bin/env python3
"""Mechanical public inventory: every non-private top-level declaration in the modules
reachable from the public root `RegularityLemmata`, one line each, sorted.

    python3 scripts/public_inventory.py > inventory.txt

Diffing the output of two commits gives the public-API delta of a change (declarations
added, removed, or moved between modules). The inventory is syntactic (it reads the sources
of the reachable modules), so it counts exactly the names a reader can refer to; the axiom
audit's total, which includes private and compiler-generated constants, is not a public-API
count. Examples, gates-umbrella modules, and `private` declarations are excluded.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PUBLIC_ROOT = "RegularityLemmata"
DECL = re.compile(
    r"^(?:@\[[^\]]*\]\s*)*(?:(?:noncomputable|protected|nonrec|scoped)\s+)*"
    r"(theorem|lemma|def|abbrev|structure|inductive|class|instance|opaque|axiom)\s+([^\s:({\[]+)"
)


def module_path(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def imports(mod: str) -> list[str]:
    path = module_path(mod)
    if not path.exists():
        return []
    return re.findall(r"^import (RegularityLemmata\S*)", path.read_text(), re.M)


def closure(start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        for dep in imports(stack.pop()):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def declarations(mod: str) -> list[str]:
    out: list[str] = []
    namespace: list[str] = []
    in_block = False
    for line in module_path(mod).read_text().split("\n"):
        stripped = line.strip()
        if in_block:
            if "-/" in stripped:
                in_block = False
            continue
        if stripped.startswith("/-") and not stripped.startswith("/--") and "-/" not in stripped:
            in_block = True
            continue
        m = re.match(r"^namespace (\S+)", line)
        if m:
            namespace.append(m.group(1))
            continue
        m = re.match(r"^end (\S+)", line)
        if m and namespace and namespace[-1] == m.group(1):
            namespace.pop()
            continue
        m = DECL.match(line)
        if not m:
            continue
        head = line[: m.start(2)]
        if re.search(r"\bprivate\b", head):
            continue
        kind, name = m.group(1), m.group(2)
        if kind == "instance" and not re.match(r"[A-Za-z_]", name):
            continue
        full = ".".join(namespace + [name]) if not name.startswith("RegularityLemmata.") else name
        out.append(f"{mod}: {kind} {full}")
    return out


def main() -> int:
    mods = sorted(closure(PUBLIC_ROOT) | {PUBLIC_ROOT})
    lines: list[str] = []
    for mod in mods:
        if module_path(mod).exists():
            lines.extend(declarations(mod))
    for line in sorted(lines):
        print(line)
    print(f"# {len(lines)} public declarations in {len(mods)} modules", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
