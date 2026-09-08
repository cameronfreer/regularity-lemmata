#!/usr/bin/env python3
"""Gate 5: the two library roots and the gates umbrella.

The classification is *recorded*, not inferred: `scripts/gates_only_modules.txt` lists the
modules that must be reachable only from `RegularityLemmataGates`. Against the import graph
under `RegularityLemmata/` the gate checks:

  1. no recorded gates-only module is reachable from the public root `RegularityLemmata`
     (this is the boundary rule of `ARCHITECTURE.md`, "Two library roots, one namespace");
  2. every recorded gates-only module is reachable from `RegularityLemmataGates`;
  3. every module reachable from the umbrella but not from the public root is recorded
     (a new gates module must be added to the list);
  4. every module under `RegularityLemmata/` is reachable from at least one root;
  5. every module whose name contains `Proxy`, `Gate`, or `Probe` is recorded as gates-only,
     except the documented public exception `Relational.DiagonalGate`.

`--self-test` runs the checker on modified copies of the graph in which a public module gains
an import of a gates-only module (with and without a `Proxy`/`Gate`/`Probe` name) and asserts
that each is reported; the gate runs the self-test first.
"""
import pathlib
import re
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
PUBLIC_ROOT = "RegularityLemmata"
GATES_ROOT = "RegularityLemmataGates"
RECORDED = ROOT / "scripts" / "gates_only_modules.txt"
PUBLIC_EXCEPTIONS = {"RegularityLemmata.Relational.DiagonalGate"}


def module_path(mod: str) -> pathlib.Path:
    return ROOT / (mod.replace(".", "/") + ".lean")


def read_graph() -> dict[str, list[str]]:
    graph: dict[str, list[str]] = {}
    for root in (PUBLIC_ROOT, GATES_ROOT):
        graph[root] = re.findall(r"^import (RegularityLemmata\S*)", module_path(root).read_text(), re.M)
    for path in (ROOT / "RegularityLemmata").rglob("*.lean"):
        mod = "RegularityLemmata." + str(path.relative_to(ROOT / "RegularityLemmata"))[:-5].replace("/", ".")
        graph[mod] = re.findall(r"^import (RegularityLemmata\S*)", path.read_text(), re.M)
    return graph


def closure(graph: dict[str, list[str]], start: str) -> set[str]:
    seen: set[str] = set()
    stack = [start]
    while stack:
        for dep in graph.get(stack.pop(), []):
            if dep not in seen:
                seen.add(dep)
                stack.append(dep)
    return seen


def read_recorded() -> set[str]:
    lines = RECORDED.read_text().splitlines()
    return {l.strip() for l in lines if l.strip() and not l.startswith("#")}


def violations(graph: dict[str, list[str]], recorded: set[str]) -> list[str]:
    public = closure(graph, PUBLIC_ROOT)
    gates = closure(graph, GATES_ROOT)
    every = {m for m in graph if m not in (PUBLIC_ROOT, GATES_ROOT)}
    out: list[str] = []
    for mod in sorted(recorded & public):
        importers = sorted(m for m in public | {PUBLIC_ROOT} if mod in graph.get(m, []))
        out.append(f"gates-only module reachable from the public root: {mod} (imported by {', '.join(importers)})")
    for mod in sorted(recorded - gates):
        out.append(f"recorded gates-only module not reachable from the umbrella: {mod}")
    for mod in sorted((gates - public) - recorded):
        out.append(f"umbrella-only module not recorded in {RECORDED.name}: {mod}")
    for mod in sorted(every - public - gates):
        out.append(f"orphan module (in neither root): {mod}")
    for mod in sorted(every):
        if re.search(r"Proxy|Gate|Probe", mod) and mod not in recorded and mod not in PUBLIC_EXCEPTIONS:
            out.append(f"probe/gate-named module not recorded as gates-only: {mod}")
    return out


def self_test(graph: dict[str, list[str]], recorded: set[str]) -> list[str]:
    """Inject forbidden imports and require that each is caught."""
    problems: list[str] = []
    base = violations(graph, recorded)
    if base:
        return ["self-test skipped: the real graph already has violations"]
    named = sorted(m for m in recorded if re.search(r"Proxy|Gate|Probe", m))
    unnamed = sorted(m for m in recorded if not re.search(r"Proxy|Gate|Probe", m))
    if not named or not unnamed:
        problems.append("self-test needs a recorded gates-only module with and without a Proxy/Gate/Probe name")
    for target in named[:1] + unnamed[:2]:
        mutated = {k: list(v) for k, v in graph.items()}
        mutated["RegularityLemmata.Finite.Density"].append(target)
        if not any(target in v for v in violations(mutated, recorded)):
            problems.append(f"self-test: injected public import of {target} was not reported")
    # A public module of a new name that is not recorded must also be caught by rule 5.
    mutated = {k: list(v) for k, v in graph.items()}
    mutated["RegularityLemmata.Relational.NewProbe"] = []
    mutated[PUBLIC_ROOT].append("RegularityLemmata.Relational.NewProbe")
    if not any("NewProbe" in v for v in violations(mutated, recorded)):
        problems.append("self-test: an unrecorded probe-named public module was not reported")
    return problems


def main(argv: list[str]) -> int:
    graph = read_graph()
    recorded = read_recorded()
    if "--self-test" in argv:
        problems = self_test(graph, recorded)
        for line in problems:
            print("check_roots:", line)
        print(f"check_roots: self-test {'FAILED' if problems else 'passed'}")
        return 1 if problems else 0
    out = violations(graph, recorded)
    for line in out:
        print("check_roots:", line)
    public = closure(graph, PUBLIC_ROOT)
    print(f"check_roots: {len(public)} public modules, {len(recorded)} recorded gates-only modules")
    return 1 if out else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
