#!/usr/bin/env python3
"""Gate: the two library roots partition the modules, and the public root never reaches a
module that only the gates umbrella imports.

Checks, on the import graph of `RegularityLemmata/`:
  1. every module under `RegularityLemmata/` is reachable from `RegularityLemmata` or
     `RegularityLemmataGates` (no orphan modules);
  2. no module reachable from the public root imports a module reachable only from the
     gates umbrella (`ARCHITECTURE.md`, "Two library roots, one namespace");
  3. every module whose name contains `Proxy`, `Gate`, or `Probe` is gates-only, except the
     documented exception `Relational.DiagonalGate`, a public counting bridge.
Exit status 1 on any violation.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PUBLIC_EXCEPTIONS = {"RegularityLemmata.Relational.DiagonalGate"}


def imports(mod: str) -> list[str]:
    path = ROOT / (mod.replace(".", "/") + ".lean")
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


def main() -> int:
    public = closure("RegularityLemmata")
    gates = closure("RegularityLemmataGates")
    gates_only = gates - public
    every = {
        "RegularityLemmata." + str(p.relative_to(ROOT / "RegularityLemmata"))[:-5].replace("/", ".")
        for p in (ROOT / "RegularityLemmata").rglob("*.lean")
    }
    failures: list[str] = []
    for orphan in sorted(every - public - gates):
        failures.append(f"orphan module (in neither root): {orphan}")
    for mod in sorted(public):
        for dep in imports(mod):
            if dep in gates_only:
                failures.append(f"public module {mod} imports gates-only module {dep}")
    for mod in sorted(public):
        if re.search(r"Proxy|Gate|Probe", mod) and mod not in PUBLIC_EXCEPTIONS:
            failures.append(f"probe/gate-named module on the public root: {mod}")
    for line in failures:
        print("check_roots:", line)
    print(f"check_roots: {len(public)} public modules, {len(gates_only)} gates-only modules")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
