#!/usr/bin/env python3
"""Namespace-aware public-declaration collision check for the gq2 campaign.

Wave 59 lost an umbrella build to two sibling lanes independently defining the same
predicate; wave 60 caught the same thing before the build.  This is that check.

The NAIVE version of this check is worse than useless, and the three ways it goes wrong
are all recorded here as requirements:

  1.  It must track enclosing namespaces.  Otherwise `SqU4.commP_a` false-matches
      `SqU5.commP_a` and the report is pure noise.
  2.  It must skip `private` declarations.  Lean module-mangles them, and the tree
      legitimately contains two private `selPar_two`.
  3.  It must skip docstring and comment prose.  Declaration keywords appear constantly
      inside `/-! ... -/` module docs.

Usage:

    python3 scripts/name_diff.py <path> [<path> ...]

Each path is a file or a directory (directories are walked for `*.lean`).  With no
arguments it scans `GQ2/`.  Exit status is 1 if any fully-qualified public name is
declared in more than one file, 0 otherwise.

To check a wave's lanes against the trunk before merging, run it over the union of the
trunk tree and each lane worktree's new files.
"""

from __future__ import annotations

import os
import re
import sys
from collections import defaultdict

# Declaration keywords that introduce a name we care about colliding.
DECL_KEYWORDS = (
    "theorem",
    "lemma",
    "def",
    "abbrev",
    "structure",
    "inductive",
    "class",
    "instance",
    "opaque",
    "axiom",
)

# Modifiers that may sit between the start of the line and the declaration keyword.
# The attribute entry must be a literal `@[...]`: writing it as `@[.*?]` makes the
# brackets a character class, which silently drops every `@[simp] theorem` in the tree.
MODIFIERS = (
    "protected",
    "noncomputable",
    "partial",
    "unsafe",
    "nonrec",
    "scoped",
    "local",
    r"@\[[^\]]*\]",
)

_MOD = r"(?:(?:" + "|".join(MODIFIERS) + r")\s+)*"
_KW = r"(?P<kw>" + "|".join(DECL_KEYWORDS) + r")"
# A name: identifier characters Lean allows, including dots for namespaced declarations
# and the usual unicode subscripts/primes the campaign uses.
_NAME = r"(?P<name>[^\s:{\[(⦃⟦]+)"

DECL_RE = re.compile(r"^" + _MOD + _KW + r"\s+" + _NAME)
PRIVATE_RE = re.compile(r"^" + _MOD + r"private\b")
NAMESPACE_RE = re.compile(r"^namespace\s+(?P<name>\S+)")
SECTION_RE = re.compile(r"^section\b(?:\s+(?P<name>\S+))?")
END_RE = re.compile(r"^end\b(?:\s+(?P<name>\S+))?")


def strip_comments(text: str) -> str:
    """Blank out block comments and line comments, preserving line structure.

    Lean block comments nest, so this tracks depth rather than matching greedily.
    Newlines are preserved so that reported line numbers stay honest.
    """
    out = []
    i = 0
    depth = 0
    n = len(text)
    while i < n:
        if depth == 0 and text.startswith("--", i):
            # Line comment: blank to end of line.
            j = text.find("\n", i)
            if j == -1:
                out.append(" " * (n - i))
                break
            out.append(" " * (j - i))
            i = j
            continue
        if text.startswith("/-", i):
            depth += 1
            out.append("  ")
            i += 2
            continue
        if depth > 0 and text.startswith("-/", i):
            depth -= 1
            out.append("  ")
            i += 2
            continue
        ch = text[i]
        out.append(ch if (depth == 0 or ch == "\n") else " ")
        i += 1
    return "".join(out)


def declarations(path: str):
    """Yield (fully_qualified_name, line_number) for each public declaration in `path`.

    Only declarations starting at column 0 are considered: that is the campaign's style
    for every top-level declaration, and it keeps `where` clauses, tactic blocks and
    nested terms out of the report.
    """
    with open(path, encoding="utf-8") as handle:
        raw = handle.read()

    stack: list[str | None] = []  # namespace name, or None for a section
    for lineno, line in enumerate(strip_comments(raw).splitlines(), start=1):
        if not line or line[0].isspace():
            continue

        m = NAMESPACE_RE.match(line)
        if m:
            # `namespace A.B` opens two levels but is closed by a single `end A.B`.
            stack.append(m.group("name"))
            continue

        m = SECTION_RE.match(line)
        if m:
            stack.append(None)
            continue

        if END_RE.match(line):
            if stack:
                stack.pop()
            continue

        if PRIVATE_RE.match(line):
            continue

        m = DECL_RE.match(line)
        if not m:
            continue

        name = m.group("name")
        if name in ("where", "extends", ":=", "|"):
            continue
        # Anonymous instances (`instance : Foo := ...`) have no name to collide.
        if m.group("kw") == "instance" and (name.startswith(":") or name.startswith("(")):
            continue

        prefix = ".".join(part for part in stack if part is not None)
        yield (f"{prefix}.{name}" if prefix else name), lineno


def collect(paths: list[str]) -> list[str]:
    files: list[str] = []
    for path in paths:
        if os.path.isdir(path):
            for root, _dirs, names in os.walk(path):
                if ".lake" in root.split(os.sep):
                    continue
                files.extend(
                    os.path.join(root, name) for name in sorted(names) if name.endswith(".lean")
                )
        elif path.endswith(".lean"):
            files.append(path)
    return sorted(set(files))


def main(argv: list[str]) -> int:
    paths = argv[1:] or ["GQ2"]
    files = collect(paths)

    owners: dict[str, list[tuple[str, int]]] = defaultdict(list)
    total = 0
    for path in files:
        for name, lineno in declarations(path):
            owners[name].append((path, lineno))
            total += 1

    collisions = {
        name: sites
        for name, sites in owners.items()
        if len({site[0] for site in sites}) > 1
    }

    print(f"name_diff: {len(files)} files, {total} public declarations, "
          f"{len(owners)} distinct names")

    if not collisions:
        print("name_diff: OK - no fully-qualified public name is declared in two files")
        return 0

    print(f"name_diff: FAIL - {len(collisions)} colliding name(s)")
    for name in sorted(collisions):
        print(f"  {name}")
        for path, lineno in sorted(collisions[name]):
            print(f"      {path}:{lineno}")
    return 1


if __name__ == "__main__":
    sys.exit(main(sys.argv))
