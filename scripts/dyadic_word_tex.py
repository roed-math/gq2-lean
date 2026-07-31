#!/usr/bin/env python3
r"""One-expression-tree TeX generator and hash gate (dyadic campaign, ticket WW5).

Merge gate 7 (`docs/dyadic/plan.md` §7) says the branch words' TeX and Lean must be
generated from **one** expression tree, with that tree's content hash emitted into both
and compared mechanically.  This script is the TeX half and the comparison;
`GQ2/Dyadic/Word/Export.lean` is the Lean half.

The hash rule of the house
--------------------------
There is exactly one definition of a word's identity, and it is the *simplification*
campaign's, frozen in ``~/claude/general_2adic/dyadic_search/words/ast.py`` (ticket S1.1)::

    canonical_json(word) = json.dumps(to_json(word), sort_keys=True,
                                      separators=(",", ":"), ensure_ascii=True)
    content_hash(word)   = sha256(canonical_json(word).encode("utf-8")).hexdigest()

This module mirrors those two lines **exactly** — not approximately.  `AST_SCHEMA_VERSION`
travels in the envelope and is deliberately *not* hashed.  Three node-level
canonicalizations happen on load, because `ast.from_json` rebuilds through the
constructors and the constructors normalize:

* ``EtaHat(num, den)`` → positive denominator, divided by ``gcd(|num|, den)`` (ticket
  S1.M).  Both entries must be odd.  So ``EtaHat(3, 9)`` and ``EtaHat(-1, -3)`` load as
  ``EtaHat(1, 3)`` and hash as it.
* ``Shadow.parameters`` → sorted by key, duplicate keys rejected.
* every node → exactly its declared field set, nothing more, nothing less.

Everything else round-trips byte-for-byte, which is why this module can work directly on
the JSON rather than on a second tree class: **a second tree encoding is precisely what
merge gate 7 exists to prevent.**

The interchange format
----------------------
An *interchange file* is a JSON object carrying the frozen ``word_ast`` payload plus
envelope metadata.  The payload field name, its encoding, and the ``word_hash`` companion
are the simplification campaign's S1.8 certificate fields verbatim, so **an S1.8
certificate is itself a valid interchange file** — that is the whole point, and it is what
lets this gate consume ``general_2adic/artifacts/candidates/*.json`` and the
``generated/{lean,latex}`` artifacts of ticket S5.G without translation::

    {
      "interchange_version": 1,
      "ast_schema_version": 1,            # envelope only, never hashed
      "name":   "rNalpha0",               # Lean identifier; names the artifacts
      "branch": "N0",                     # one of BRANCHES (plan §1 / ledger §7)
      "source": "draft eq:Ncompact-word", # provenance, free text
      "lean": {"module": "GQ2.Dyadic.Words.N0", "declaration": "rNalpha0Raw"},
      "names": {"sigma2": "\\sigma_2"},   # optional per-word LaTeX name overrides
      "aux_style": "macro",               # "macro" | "inline"
      "word_ast": { ... },                # THE tree, S1.1 encoding
      "word_hash": "…"                    # optional; verified when present
    }

Unknown top-level keys are ignored (a certificate has ~15 of them).  ``word_ast`` is
validated strictly: unknown ops, missing fields and extra fields all raise.

Relation to the simplification campaign's printers
--------------------------------------------------
``to_latex`` here is a faithful re-implementation of
``dyadic_search.words.pretty_latex.to_latex``, and its output is asserted **byte
identical** — that is what ``--self-test`` checks against pinned goldens, and what
``--self-test --simp-root PATH`` re-checks against the live module when the
simplification repo is present.  The re-implementation exists only because this repo must
stay standalone (stdlib, ``python3``, no ``sage``, no cross-repo import); the header line
of a generated ``.tex`` names ``pretty_latex`` because the bytes are its bytes.

Per the campaign's standing rule, **python is regression and tooling only**: nothing this
script prints is ever cited by a Lean proof.  The Lean side's obligations are discharged
in `GQ2/Dyadic/Word/Export.lean`, which is axiom-clean and kernel-checked.

Usage
-----
::

    python3 scripts/dyadic_word_tex.py hash      FILE...     # content hash of each tree
    python3 scripts/dyadic_word_tex.py latex     FILE        # the .tex artifact, stdout
    python3 scripts/dyadic_word_tex.py appendix  FILE        # ledger §7 skeleton, stdout
    python3 scripts/dyadic_word_tex.py emit      FILE...     # write generated/ artifacts
    python3 scripts/dyadic_word_tex.py check                 # the D4 / merge-gate-7 check
    python3 scripts/dyadic_word_tex.py self-test             # goldens + cross-repo pins

``check`` is what `scripts/check_dyadic.sh`'s D4 extension point calls; it exits non-zero
with a diagnostic on any mismatch, and — deliberately — also when generated artifacts are
present without a manifest, since that is exactly the "shipped with the gate skipped" case
the placeholder was written to catch.

Activating D4
-------------
WW5 does not own `scripts/check_dyadic.sh`.  Its D4 block fails loudly the moment
artifacts appear; to turn it into the real comparison, the orchestrator replaces that
failure branch — the three ``echo "FAIL: one-tree hash check — NOT IMPLEMENTED …"`` lines
and the ``fail=1`` under them — with this **single line**, and changes nothing else::

    if hash_out=$(python3 scripts/dyadic_word_tex.py check 2>&1); then echo "OK:   one-tree hash check (merge gate 7)"; else echo "FAIL: one-tree hash check (merge gate 7):"; printf '%s\n' "$hash_out" | sed 's/^/          /'; fail=1; fi

The surrounding ``if [ -d "$GENERATED_LATEX" ] || [ -f "$HASH_MANIFEST" ]; then … else …
fi`` already has the right shape and its ``else`` branch's SKIP message stays correct.
The line follows D5's own idiom (capture the output, indent it under a FAIL, set
``fail=1``), so the two hooks read alike.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import sys
from math import gcd

# ---------------------------------------------------------------------------
# Frozen constants
# ---------------------------------------------------------------------------

#: Version of *this* envelope (not of the tree grammar).
INTERCHANGE_VERSION = 1

#: The S1.1 tree-grammar version.  Recorded in envelopes, never hashed.
AST_SCHEMA_VERSION = 1

#: Version of the manifest this script writes and `check` reads.
MANIFEST_VERSION = 1

#: Default artifact root, matching `scripts/check_dyadic.sh`'s GENERATED_LATEX /
#: HASH_MANIFEST and the simplification campaign's `certificates/emit.py` layout.
DEFAULT_ROOT = "generated"
MANIFEST_NAME = "hash-manifest.json"

#: Gate-A marker (`pretty_latex.HASH_COMMENT_PREFIX`).  Both sides look for this exact
#: spelling rather than re-guessing it.
HASH_COMMENT_PREFIX = "% ast-hash: "

#: Suffix of the Lean-side hash constant (`pretty_lean.HASH_SUFFIX`).
LEAN_HASH_SUFFIX = "_astHash"

#: The five frozen branch rows (`artifacts/reports/selection-freeze.md`, plan §1).
BRANCHES = ("L", "N0", "Npc", "M0", "Mpc")

#: Ledger §7's ten acceptance-appendix items, verbatim.
LEDGER_SEVEN_ITEMS = (
    "the exact syntax tree",
    "the two specialization reductions",
    "the evaluated Fox Jacobian",
    "a list of invertible row and column operations",
    "the reduced normal matrix",
    "the Stokes chain identity",
    "the extraspecial Hessian",
    "the change of variables to quadratic normal form",
    "the affine phase-cover certificate",
    "a hash tying the generated TeX formula to the Lean syntax tree",
)

#: Ledger §7's expected quadratic endpoints, per branch — the pre-filled target of
#: appendix item 8.  Wave 2 replaces "the nonsingular core matrices below" with the
#: actual matrices (ledger §7's closing sentence).
BRANCH_ENDPOINTS = {
    "L": r"existing $n=1$ core plus hyperbolic handles",
    "N0": r"$q(c_0)+b_q(c_0,c_1)$",
    "Npc": r"$Q_0(c_0)+b_q(c_1,L_c c_0)$, with explicit invertible $L_c$",
    "M0": r"the two projector cases claimed in the draft, "
          r"each with explicit change of variables",
    "Mpc": r"self-replicated raw determinant cancellation plus canonical split form, "
           r"including every $T$-dependent central term",
}

#: Human-readable branch titles (selection-freeze.md headings, condensed).
BRANCH_TITLES = {
    "L": r"Type $L$ ($n$ odd) --- $L_{\mathrm{sq}}$, the stabilized square commutator",
    "N0": r"Compact $N$ ($r = 0$) --- $R_{N,\alpha,0}$",
    "Npc": r"Noncompact / procyclic $N$ ($r \ge 1$) --- $R_{N,\alpha,r,\eta}$ "
           r"with $E_{r,\eta}$",
    "M0": r"Compact $M$ ($r = 0$) --- $R_{M,0}$ with the reversed "
          r"$\mathcal{E}$-correction",
    "Mpc": r"Procyclic $M$ ($r \ge 1$, $\eta$ odd) --- $R_{M,\mathrm{pc}}$",
}


class WordError(ValueError):
    """The interchange payload is not a well-formed S1.1 tree."""


class LatexError(ValueError):
    """The word cannot be displayed unambiguously."""


class GateError(Exception):
    """A merge-gate-7 comparison failed."""


# ---------------------------------------------------------------------------
# Part 1.  The frozen tree: strict validation + constructor-level canonicalization
# ---------------------------------------------------------------------------
#
# `canon_word` is `ast.to_json(ast.from_json(data))` computed in place.  Field sets are
# `ast._take_fields`'s; the normalizations are the ones the dataclass constructors apply.

#: op -> required field names, exactly `ast.to_json`'s emission (and `from_json`'s
#: `_take_fields` requirement).
WORD_FIELDS = {
    "Generator": ("name",),
    "Identity": (),
    "Multiply": ("children",),
    "Inverse": ("word",),
    "IntegerPower": ("word", "exponent"),
    "ZhatPower": ("word", "exponent_spec"),
    "Omega2Power": ("word",),
    "Conjugate": ("word", "conjugator"),
    "Commutator": ("left", "right"),
    "OrbitNorm": ("step", "length", "word"),
    "Shadow": ("kind", "parameters", "word"),
    "HyperbolicHandles": ("start_index", "count"),
    "Auxiliary": ("name", "definition"),
}

#: The symbolic integer-exponent expression grammar (`ExponentExpr`).
EXPR_FIELDS = {
    "Int": ("value",),
    "Param": ("name",),
    "Add": ("left", "right"),
    "Sub": ("left", "right"),
    "Mul": ("left", "right"),
    "Pow2": ("exponent",),
}

#: The finite (profinite) exponent-spec grammar (`FiniteExponentSpec`).
SPEC_FIELDS = {
    "Int": ("value",),
    "Omega2": (),
    "EtaHat": ("num", "den"),
}

#: Nodes with no `PWord` counterpart at all (see the Export.lean gap table).
NODES_WITHOUT_PWORD = ("OrbitNorm", "HyperbolicHandles", "Shadow", "Auxiliary")


def _plain_int(value, what):
    """Require an honest int (`ast._check_plain_int`: bool is excluded on purpose)."""
    if not isinstance(value, int) or isinstance(value, bool):
        raise WordError("%s must be an int, got %r" % (what, value))
    return value


def _nonempty_str(value, what):
    if not isinstance(value, str) or not value:
        raise WordError("%s must be a nonempty str, got %r" % (what, value))
    return value


def _tagged(data, tag_key, table, what):
    if not isinstance(data, dict) or tag_key not in data:
        raise WordError("%s must be a dict with a %r tag, got %r"
                        % (what, tag_key, data))
    tag = data[tag_key]
    if tag not in table:
        raise WordError("unknown %s %r (known: %s)"
                        % (what, tag, ", ".join(sorted(table))))
    expected = {tag_key} | set(table[tag])
    if set(data) != expected:
        raise WordError("%s %s: expected fields %s, got %s"
                        % (what, tag, sorted(expected), sorted(data)))
    return tag


def canon_expr(data):
    """Canonical JSON dict of an exponent *expression* (`Int | Param | Add | Sub |
    Mul | Pow2`).  Expressions are never simplified — `Int(2)` and `Add(Int(1),
    Int(1))` are different syntax and therefore different hashes (S1.1, "write what
    you mean")."""
    tag = _tagged(data, "type", EXPR_FIELDS, "exponent expression")
    if tag == "Int":
        return {"type": "Int", "value": _plain_int(data["value"], "Int.value")}
    if tag == "Param":
        return {"type": "Param", "name": _nonempty_str(data["name"], "Param.name")}
    if tag == "Pow2":
        return {"type": "Pow2", "exponent": canon_expr(data["exponent"])}
    return {"type": tag, "left": canon_expr(data["left"]),
            "right": canon_expr(data["right"])}


def canon_spec(data):
    """Canonical JSON dict of a finite exponent spec, applying the ticket-S1.M
    ``EtaHat`` canonicalization (positive denominator, gcd-reduced).  Both entries
    must be odd; zero is even, so it is rejected like any other even input."""
    tag = _tagged(data, "type", SPEC_FIELDS, "finite exponent spec")
    if tag == "Int":
        return {"type": "Int", "value": _plain_int(data["value"], "Int.value")}
    if tag == "Omega2":
        return {"type": "Omega2"}
    num = _plain_int(data["num"], "EtaHat.num")
    den = _plain_int(data["den"], "EtaHat.den")
    for name, value in (("num", num), ("den", den)):
        if value % 2 == 0:
            raise WordError("EtaHat.%s must be odd, got %d" % (name, value))
    if den < 0:
        num, den = -num, -den
    divisor = gcd(abs(num), den)
    if divisor > 1:
        num, den = num // divisor, den // divisor
    return {"type": "EtaHat", "num": num, "den": den}


def canon_word(data):
    """Canonical JSON dict of a word node: `ast.to_json(ast.from_json(data))`.

    Strict — unknown ops, missing fields and extra fields all raise — and
    normalizing exactly where the S1.1 constructors normalize (``EtaHat``, and
    ``Shadow.parameters``' sort).  Nothing else is rewritten: no factor is reordered,
    no power folded, no block expanded.  Whatever normal form the caller wants is the
    caller's business and travels in the tree.
    """
    op = _tagged(data, "op", WORD_FIELDS, "word node")
    if op == "Generator":
        return {"op": "Generator",
                "name": _nonempty_str(data["name"], "Generator.name")}
    if op == "Identity":
        return {"op": "Identity"}
    if op == "Multiply":
        children = data["children"]
        if not isinstance(children, list):
            raise WordError("Multiply.children must be a list")
        return {"op": "Multiply", "children": [canon_word(c) for c in children]}
    if op == "Inverse":
        return {"op": "Inverse", "word": canon_word(data["word"])}
    if op == "IntegerPower":
        return {"op": "IntegerPower", "word": canon_word(data["word"]),
                "exponent": canon_expr(data["exponent"])}
    if op == "ZhatPower":
        return {"op": "ZhatPower", "word": canon_word(data["word"]),
                "exponent_spec": canon_spec(data["exponent_spec"])}
    if op == "Omega2Power":
        return {"op": "Omega2Power", "word": canon_word(data["word"])}
    if op == "Conjugate":
        return {"op": "Conjugate", "word": canon_word(data["word"]),
                "conjugator": canon_word(data["conjugator"])}
    if op == "Commutator":
        return {"op": "Commutator", "left": canon_word(data["left"]),
                "right": canon_word(data["right"])}
    if op == "OrbitNorm":
        return {"op": "OrbitNorm", "step": canon_word(data["step"]),
                "length": canon_expr(data["length"]),
                "word": canon_word(data["word"])}
    if op == "Shadow":
        return {"op": "Shadow", "kind": _nonempty_str(data["kind"], "Shadow.kind"),
                "parameters": _canon_shadow_parameters(data["parameters"]),
                "word": canon_word(data["word"])}
    if op == "HyperbolicHandles":
        start = _plain_int(data["start_index"], "HyperbolicHandles.start_index")
        if start < 0:
            raise WordError("HyperbolicHandles.start_index must be >= 0")
        return {"op": "HyperbolicHandles", "start_index": start,
                "count": canon_expr(data["count"])}
    # op == "Auxiliary"
    return {"op": "Auxiliary", "name": _nonempty_str(data["name"], "Auxiliary.name"),
            "definition": canon_word(data["definition"])}


def _canon_shadow_parameters(parameters):
    """`Shadow.parameters` as stored: `[key, value]` pairs sorted by key, values
    either a bare string tag or an exponent expression."""
    if not isinstance(parameters, list):
        raise WordError("Shadow.parameters must be a list of [key, value] pairs")
    pairs = []
    seen = set()
    for entry in parameters:
        if not isinstance(entry, list) or len(entry) != 2:
            raise WordError("Shadow parameter entries must be [key, value] pairs, "
                            "got %r" % (entry,))
        key, value = entry
        _nonempty_str(key, "Shadow parameter key")
        if key in seen:
            raise WordError("duplicate Shadow parameter key %r" % key)
        seen.add(key)
        pairs.append([key, value if isinstance(value, str) else canon_expr(value)])
    pairs.sort(key=lambda kv: kv[0])
    return pairs


def canonical_json(word):
    """The exact byte string `content_hash` digests (`ast.canonical_json`)."""
    return json.dumps(canon_word(word), sort_keys=True, separators=(",", ":"),
                      ensure_ascii=True)


def content_hash(word):
    """SHA-256 hex digest of `canonical_json(word)` (UTF-8) — `ast.content_hash`."""
    return hashlib.sha256(canonical_json(word).encode("utf-8")).hexdigest()


def walk(word):
    """Yield every node of a canonicalized tree, parents before children."""
    yield word
    op = word["op"]
    for field in WORD_FIELDS[op]:
        if op == "Multiply" and field == "children":
            for child in word["children"]:
                for node in walk(child):
                    yield node
        elif field in ("word", "conjugator", "left", "right", "step", "definition"):
            value = word[field]
            if isinstance(value, dict) and "op" in value:
                for node in walk(value):
                    yield node


def node_census(word):
    """`{op: count}` over a canonicalized tree — appendix item 1's summary."""
    census = {}
    for node in walk(word):
        census[node["op"]] = census.get(node["op"], 0) + 1
    return census


# ---------------------------------------------------------------------------
# Part 2.  LaTeX (a byte-faithful port of dyadic_search.words.pretty_latex)
# ---------------------------------------------------------------------------

OMEGA2_LATEX = r"\omega_2"
ETAHAT_LATEX = r"\widehat{\eta}"

DEFAULT_NAME_MAP = {
    "sigma": r"\sigma",
    "sigma2": r"\sigma_2",
    "tau": r"\tau",
    "x0": "x_0",
    "x1": "x_1",
    "x2": "x_2",
    "x3": "x_3",
}

GREEK_NAMES = frozenset("""
alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa
lambda mu nu xi pi varpi rho varrho sigma varsigma tau upsilon phi varphi chi
psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega
""".split())

_ATOM_RE = re.compile(r"\A([A-Za-z0-9]|\\[A-Za-z]+)\Z")
_TRAILING_LETTER_RE = re.compile(r"[A-Za-z]\Z")
_LEADING_LETTER_RE = re.compile(r"\A[A-Za-z]")
_TRAILING_CONTROL_WORD_RE = re.compile(r"\\[A-Za-z]+\Z")
_LETTER_DIGITS_RE = re.compile(r"\A([A-Za-z])([0-9]+)\Z")
_GREEK_INDEX_RE = re.compile(r"\A([A-Za-z]+?)([0-9]*)\Z")
_ESCAPES = {"\\": r"\textbackslash{}", "{": r"\{", "}": r"\}", "$": r"\$",
            "&": r"\&", "#": r"\#", "^": r"\textasciicircum{}", "_": r"\_",
            "%": r"\%", "~": r"\textasciitilde{}"}

_PREC_SUM = 1
_PREC_PRODUCT = 2
_PREC_ATOM = 3


def _escape(text):
    return "".join(_ESCAPES.get(ch, ch) for ch in text)


def _script(body):
    """Brace a super/subscript body unless it is a single atom."""
    return body if _ATOM_RE.match(body) else "{%s}" % body


def _glue_word(left, right):
    r"""Separator between juxtaposed factors: ``\,`` exactly when the left one ends in
    a letter and the right one starts with a letter (readability *and* tokenization —
    without it ``\sigma`` + ``c_0`` would concatenate into ``\sigmac_0``)."""
    if _TRAILING_LETTER_RE.search(left) and _LEADING_LETTER_RE.match(right):
        return r"\,"
    return ""


def _glue_exponent(left, right):
    """Separator inside a superscript: only what tokenization forces, so that the
    §7.3 conjugator product stays ``hg``."""
    if _TRAILING_CONTROL_WORD_RE.search(left) and re.match(r"\A[A-Za-z]", right):
        return r"\,"
    return ""


def _join(parts, glue):
    out = ""
    for part in parts:
        out = part if not out else out + glue(out, part) + part
    return out


def render_name(name, names=None):
    r"""LaTeX for a generator / auxiliary / parameter name: ``names`` override first,
    then :data:`DEFAULT_NAME_MAP`, then Greek-with-index, letter+digits, bare letter,
    ``\mathrm{...}``.  The campaign's displays deliberately do not distinguish the
    three kinds of name, so they share one renderer."""
    if not isinstance(name, str) or not name:
        raise LatexError("name must be a nonempty str, got %r" % (name,))
    if names and name in names:
        return names[name]
    if name in DEFAULT_NAME_MAP:
        return DEFAULT_NAME_MAP[name]
    match = _GREEK_INDEX_RE.match(name)
    if match and match.group(1) in GREEK_NAMES:
        stem, index = match.groups()
        base = "\\" + stem
        return base if not index else "%s_%s" % (base, _script(index))
    match = _LETTER_DIGITS_RE.match(name)
    if match:
        letter, digits = match.groups()
        return "%s_%s" % (letter, _script(digits))
    if len(name) == 1 and name.isalpha():
        return name
    return r"\mathrm{%s}" % _escape(name)


def _exponent(expr, names):
    """Return ``(latex, precedence)`` for an exponent expression."""
    kind = expr["type"]
    if kind == "Int":
        return str(expr["value"]), _PREC_ATOM
    if kind == "Param":
        return render_name(expr["name"], names), _PREC_ATOM
    if kind in ("Add", "Sub"):
        left = _wrap_exponent(expr["left"], names, _PREC_SUM)
        right = _wrap_exponent(expr["right"], names, _PREC_SUM + 1)
        if kind == "Add" and right.startswith("-"):
            return "%s%s" % (left, right), _PREC_SUM
        return "%s%s%s" % (left, "+" if kind == "Add" else "-", right), _PREC_SUM
    if kind == "Mul":
        left = _wrap_exponent(expr["left"], names, _PREC_PRODUCT)
        right = _wrap_exponent(expr["right"], names, _PREC_PRODUCT)
        return left + _glue_exponent(left, right) + right, _PREC_PRODUCT
    if kind == "Pow2":
        body, _ = _exponent(expr["exponent"], names)
        return "2^%s" % _script(body), _PREC_ATOM
    raise LatexError("not an exponent expression: %r" % (expr,))


def _wrap_exponent(expr, names, minimum):
    body, prec = _exponent(expr, names)
    return body if prec >= minimum else "(%s)" % body


def render_exponent(expr, names=None):
    """LaTeX for an exponent expression."""
    return _exponent(expr, names)[0]


def _handle_index(offset):
    """Subscript of the ``j``-th handle generator ``x_{offset+2j}``."""
    return "2j" if offset == 0 else "%d+2j" % offset


class _Renderer:
    """Renders one word, collecting provenance comments as it goes.

    Note ordering is load-bearing: the ``% shadow:`` / ``% etahat:`` comments come out
    in exactly the order `pretty_latex` produces them, which is first-use order under
    that module's own argument-evaluation order (a spec's note precedes its base's
    notes; a conjugator's precede the conjugated word's).
    """

    def __init__(self, aux_style="macro", names=None):
        if aux_style not in ("macro", "inline"):
            raise LatexError("aux_style must be 'macro' or 'inline', got %r"
                             % (aux_style,))
        self.aux_style = aux_style
        self.names = names
        self.notes = []
        self.definitions = []
        self._defined = {}
        self._emitted = set()
        self._tight = 0

    def note(self, line):
        if line not in self.notes:
            self.notes.append(line)

    def name(self, name):
        return render_name(name, self.names)

    def exponent(self, expr):
        return render_exponent(expr, self.names)

    def base(self, word):
        """Render ``word`` ready to carry a superscript."""
        body = self.word(word)
        return body if self._atomic(word) else "(%s)" % body

    def _atomic(self, word):
        op = word["op"]
        if op in ("Generator", "Identity", "Commutator", "OrbitNorm", "Shadow"):
            return True
        if op == "Auxiliary":
            return (True if self.aux_style == "macro"
                    else self._atomic(word["definition"]))
        if op == "Multiply":
            children = word["children"]
            if not children:
                return True
            if len(children) == 1:
                return self._atomic(children[0])
        return False

    def power(self, word, script):
        return "%s^%s" % (self.base(word), _script(script))

    def superscript_word(self, word):
        r"""Render a word destined for a superscript: products inside a script are set
        tight (``\delta_1^{hg}``, campaign §7.3)."""
        self._tight += 1
        try:
            return self.word(word)
        finally:
            self._tight -= 1

    def word(self, node):
        op = node["op"]
        if op == "Generator":
            return self.name(node["name"])
        if op == "Identity":
            return "1"
        if op == "Multiply":
            children = node["children"]
            if not children:
                return "1"
            glue = _glue_exponent if self._tight else _glue_word
            return _join([self.word(c) for c in children], glue)
        if op == "Inverse":
            return self.power(node["word"], "-1")
        if op == "IntegerPower":
            script = self.exponent(node["exponent"])
            return self.power(node["word"], script)
        if op == "ZhatPower":
            script = self.spec(node["exponent_spec"])
            return self.power(node["word"], script)
        if op == "Omega2Power":
            return self.power(node["word"], OMEGA2_LATEX)
        if op == "Conjugate":
            script = self.superscript_word(node["conjugator"])
            return self.power(node["word"], script)
        if op == "Commutator":
            return "[%s,%s]" % (self.word(node["left"]), self.word(node["right"]))
        if op == "OrbitNorm":
            return r"\mathcal{N}_{%s,%s}(%s)" % (
                self.word(node["step"]), self.exponent(node["length"]),
                self.word(node["word"]))
        if op == "HyperbolicHandles":
            return self.handles(node)
        if op == "Shadow":
            return self.shadow(node)
        if op == "Auxiliary":
            return self.auxiliary(node)
        raise LatexError("unknown word node %r" % (node,))

    def spec(self, spec):
        kind = spec["type"]
        if kind == "Int":
            return str(spec["value"])
        if kind == "Omega2":
            return OMEGA2_LATEX
        if kind == "EtaHat":
            self.note("%% etahat: %s = %d/%d  (num/den exactly as stored; the "
                      "display shows only the symbol, campaign 3)"
                      % (ETAHAT_LATEX, spec["num"], spec["den"]))
            return ETAHAT_LATEX
        raise LatexError("unknown finite exponent spec %r" % (spec,))

    def handles(self, node):
        start = node["start_index"]
        count = node["count"]
        if count["type"] == "Int":
            upper = str(count["value"] - 1)
        else:
            upper = "%s-1" % _wrap_exponent(count, self.names, _PREC_SUM + 1)
        return r"\prod_{j=0}^%s[x_{%s},x_{%s}]" % (
            _script(upper), _handle_index(start), _handle_index(start + 1))

    def shadow(self, node):
        params = ", ".join(
            "%s=%s" % (key, value if isinstance(value, str)
                       else self.exponent(value))
            for key, value in node["parameters"])
        self.note("%% shadow: kind=%s parameters={%s}  (display and semantics "
                  "are provisional; ticket S4.2 owns them, campaign 7.4)"
                  % (node["kind"], params))
        return r"\operatorname{Sh}_%s(%s)" % (
            _script(_escape(node["kind"])), self.word(node["word"]))

    def auxiliary(self, node):
        digest = content_hash(node["definition"])
        previous = self._defined.get(node["name"])
        if previous is not None and previous != digest:
            raise LatexError(
                "auxiliary %r has two different definitions in one word; the "
                "definitions block would be ambiguous (S1.1's complexity counter "
                "rejects this too)" % (node["name"],))
        self._defined[node["name"]] = digest
        if self.aux_style == "inline":
            return self.word(node["definition"])
        body = self.word(node["definition"])      # walked first: dependency order
        if node["name"] not in self._emitted:
            self._emitted.add(node["name"])
            self.definitions.append((self.name(node["name"]), body))
        return self.name(node["name"])


def render_word(word, aux_style="macro", names=None):
    """The bare inline-math body of ``word`` (no ``$``, no comments)."""
    return _Renderer(aux_style, names).word(canon_word(word))


def auxiliary_definitions(word, names=None):
    """``[(name_latex, body_latex), ...]`` in dependency order."""
    renderer = _Renderer("macro", names)
    renderer.word(canon_word(word))
    return list(renderer.definitions)


def ast_hash_comment(word):
    """The gate-A trailer: ``% ast-hash: <sha256>``."""
    return HASH_COMMENT_PREFIX + content_hash(word)


def to_latex(word, aux_style="macro", names=None):
    r"""The LaTeX **artifact** for ``word`` — byte identical to
    ``dyadic_search.words.pretty_latex.to_latex`` (asserted by ``self-test``)::

        % generated by ... ; do not hand-edit.
        % aux-style: macro
        % auxiliary definitions ...:
        a = (x_0^{-3}\tau)^{\omega_2}
        % displayed relation:
        (x_0^\sigma)^{-1}a\,x_1^2c
        % etahat: ...
        % ast-hash: <sha256>

    The hash is always that of the **input** tree, including under
    ``aux_style="inline"``: it identifies the AST, not the expanded display.
    """
    canonical = canon_word(word)
    renderer = _Renderer(aux_style, names)
    body = renderer.word(canonical)
    lines = ["% generated by dyadic_search.words.pretty_latex (ticket S1.8); "
             "do not hand-edit.",
             "%% aux-style: %s" % aux_style]
    if renderer.definitions:
        lines.append("% auxiliary definitions (campaign 9.3: the complexity "
                     "counter charges each one once):")
        lines.extend("%s = %s" % pair for pair in renderer.definitions)
    lines.append("% displayed relation:")
    lines.append(body)
    lines.extend(renderer.notes)
    lines.append(HASH_COMMENT_PREFIX + content_hash(canonical))
    return "\n".join(lines) + "\n"


# ---------------------------------------------------------------------------
# Part 3.  Interchange envelopes
# ---------------------------------------------------------------------------

_IDENT_RE = re.compile(r"\A[A-Za-z_][A-Za-z0-9_']*\Z")
_HEX64_RE = re.compile(r"\A[0-9a-f]{64}\Z")


class Interchange(object):
    """One parsed interchange file: envelope metadata plus the canonicalized tree."""

    __slots__ = ("path", "name", "branch", "source", "lean_module",
                 "lean_declaration", "names", "aux_style", "word", "word_hash",
                 "declared_hash")

    def __init__(self, path, data):
        self.path = path
        if not isinstance(data, dict):
            raise WordError("%s: interchange file must be a JSON object" % path)
        if "word_ast" not in data:
            raise WordError("%s: no 'word_ast' field (an S1.8 certificate or an "
                            "interchange envelope is expected)" % path)
        self.word = canon_word(data["word_ast"])
        self.word_hash = content_hash(self.word)

        self.declared_hash = data.get("word_hash")
        if self.declared_hash is not None:
            if not (isinstance(self.declared_hash, str)
                    and _HEX64_RE.match(self.declared_hash)):
                raise WordError("%s: word_hash must be a 64-char lowercase hex "
                                "digest, got %r" % (path, self.declared_hash))
            if self.declared_hash != self.word_hash:
                raise WordError(
                    "%s: declared word_hash %s does not hash its own word_ast "
                    "(%s).  Either the tree was edited without updating the hash, "
                    "or the canonicalization diverged — the second is a merge "
                    "gate 7 stop condition." % (path, self.declared_hash,
                                                self.word_hash))

        default_name = os.path.splitext(os.path.basename(path))[0]
        self.name = data.get("name") or data.get("candidate_id") or default_name
        if not _IDENT_RE.match(str(self.name)):
            # Certificate ids ("L-sq-n1-v001") are not Lean identifiers; keep them as
            # the artifact name but sanitize for the Lean-facing constant.
            self.name = str(self.name)
        self.branch = data.get("branch") or data.get("family") or "?"
        self.source = data.get("source") or data.get("notes") or ""
        lean = data.get("lean") or {}
        if not isinstance(lean, dict):
            lean = {}
        self.lean_module = lean.get("module")
        self.lean_declaration = lean.get("declaration")
        names = data.get("names")
        self.names = names if isinstance(names, dict) else None
        self.aux_style = data.get("aux_style", "macro")
        if self.aux_style not in ("macro", "inline"):
            raise WordError("%s: aux_style must be 'macro' or 'inline'" % path)

    @property
    def artifact_stem(self):
        """File stem of the generated artifacts (LaTeX and appendix)."""
        return re.sub(r"[^A-Za-z0-9_.-]", "-", str(self.name))

    @property
    def lean_hash_constant(self):
        """Name of the Lean-side gate-A constant, `pretty_lean`'s convention."""
        base = self.lean_declaration or self.name
        return "%s%s" % (base, LEAN_HASH_SUFFIX)

    def latex(self):
        return to_latex(self.word, aux_style=self.aux_style, names=self.names)


def load_interchange(path):
    """Read and validate one interchange file (or S1.8 certificate)."""
    with open(path, "r", encoding="utf-8") as stream:
        try:
            data = json.load(stream)
        except ValueError as exc:
            raise WordError("%s: not valid JSON: %s" % (path, exc))
    return Interchange(path, data)


# ---------------------------------------------------------------------------
# Part 4.  The acceptance appendix (ledger §7's ten items)
# ---------------------------------------------------------------------------

_SLOT = (r"\dyadicAppendixTODO{%s}{%s}"
         "\n"
         r"%% WW5 slot: wave-2 ticket %s fills this in.")

#: Which wave-2 ticket owns each of the ten items, by lane suffix.  `X` is the branch
#: lane (WN0, WM0, WNP, WMP, WL); `-a` is the word ticket, `-b` the Fox certificate,
#: `-c` the Stokes/scalar/Hessian/phase certificates (tickets.md, wave 2).
_ITEM_OWNER = ("WW5 (this generator)", "X-a", "X-b", "X-b", "X-b",
               "X-c", "X-c", "X-c", "X-c", "WW5 (this generator)")

APPENDIX_PREAMBLE = r"""% WW5 acceptance-appendix skeleton -- ledger section 7, ten items.
% Generated by scripts/dyadic_word_tex.py; the FILLED items are generated and must not
% be hand-edited, the SLOTS are wave-2 fill-in points (one per branch lane).
%
% Requires, once in the document preamble:
%   \newcommand{\dyadicAppendixTODO}[2]{\textbf{[TODO #1]}\quad\emph{#2}}
"""


def appendix(entry):
    """The ledger §7 acceptance appendix for one branch word.

    Items 1 and 10 are **generated and complete** — they are precisely what WW5 owns
    (the exact syntax tree, and the hash tying the generated TeX to the Lean syntax
    tree).  Items 2--9 are explicit per-branch fill-in slots carrying the ticket that
    owns them and, for item 8, the ledger's expected quadratic endpoint for this
    branch.  A slot is a visible ``[TODO ...]`` in the compiled appendix on purpose:
    the skeleton's job is to show what is still missing.
    """
    branch = entry.branch
    title = BRANCH_TITLES.get(branch, branch)
    lane = {"L": "WL", "N0": "WN0", "Npc": "WNP", "M0": "WM0",
            "Mpc": "WMP"}.get(branch, "X")
    canonical = entry.word
    digest = entry.word_hash
    renderer = _Renderer(entry.aux_style, entry.names)
    body = renderer.word(canonical)

    out = [APPENDIX_PREAMBLE,
           r"\section{Acceptance appendix: %s}" % title,
           r"\label{sec:appendix-%s}" % branch,
           "",
           r"Word \texttt{%s}, branch \texttt{%s}%s."
           % (_escape(str(entry.name)), _escape(str(branch)),
              (", source " + r"\texttt{%s}" % _escape(str(entry.source)))
              if entry.source else ""),
           ""]

    # -- item 1: the exact syntax tree (GENERATED) --------------------------
    out.append(r"\subsection{1. %s}" % LEDGER_SEVEN_ITEMS[0])
    if renderer.definitions:
        out.append(r"\begin{align*}")
        out.extend("  %s &= %s\\\\" % pair for pair in renderer.definitions)
        out.append(r"\end{align*}")
    out.append(r"\[ %s = 1 \]" % body)
    census = node_census(canonical)
    out.append(r"Node census: %s; canonical serialization %d bytes."
               % (", ".join(r"\texttt{%s} $\times$ %d" % (op, census[op])
                            for op in sorted(census)),
                  len(canonical_json(canonical).encode("utf-8"))))
    out.append("")

    # -- items 2..9: per-branch fill-in slots ------------------------------
    for index in range(1, 9):
        number = index + 1
        item = LEDGER_SEVEN_ITEMS[index]
        owner = _ITEM_OWNER[index].replace("X", lane)
        out.append(r"\subsection{%d. %s}" % (number, item))
        hint = item
        if number == 8:
            hint = "%s --- expected endpoint: %s" % (item,
                                                     BRANCH_ENDPOINTS.get(branch, "?"))
        if number == 5:
            hint = (item + r" (ledger section 7: the phrase ``the nonsingular core "
                           r"matrices below'' must be replaced by the actual matrices)")
        out.append(_SLOT % (owner, hint, owner))
        out.append("")

    # -- item 10: the hash (GENERATED) -------------------------------------
    out.append(r"\subsection{10. %s}" % LEDGER_SEVEN_ITEMS[9])
    out.append(r"\begin{center}\texttt{%s}\end{center}" % digest)
    out.append(r"This digest is \texttt{sha256} of the S1.1 canonical JSON of the tree "
               r"above.  It is emitted into the generated \LaTeX{} as the "
               r"\texttt{\%% ast-hash} trailer and into Lean as "
               r"\texttt{%s}; \texttt{scripts/check\_dyadic.sh} (check D4) compares "
               r"them, which is merge gate 7." % _escape(entry.lean_hash_constant))
    if entry.lean_module:
        out.append(r"Lean module \texttt{%s}, declaration \texttt{%s}."
                   % (_escape(entry.lean_module),
                      _escape(str(entry.lean_declaration or "?"))))
    else:
        out.append(_SLOT % (lane + "-a", "Lean module and declaration not yet "
                                         "recorded in the interchange envelope",
                            lane + "-a"))
    out.append("")
    out.append(HASH_COMMENT_PREFIX + digest)
    return "\n".join(out) + "\n"


# ---------------------------------------------------------------------------
# Part 5.  Artifact writing (atomic, mirroring certificates/emit.py)
# ---------------------------------------------------------------------------

def _atomic_write(path, text):
    directory = os.path.dirname(path) or "."
    if not os.path.isdir(directory):
        os.makedirs(directory)
    temporary = path + ".part"
    try:
        with open(temporary, "w", encoding="utf-8", newline="\n") as stream:
            stream.write(text)
            stream.flush()
            os.fsync(stream.fileno())
        os.replace(temporary, path)
    except BaseException:
        if os.path.exists(temporary):
            os.remove(temporary)
        raise
    return path


def manifest_path(root=DEFAULT_ROOT):
    return os.path.join(root, MANIFEST_NAME)


def latex_path(entry, root=DEFAULT_ROOT):
    return os.path.join(root, "latex", "%s.tex" % entry.artifact_stem)


def appendix_path(entry, root=DEFAULT_ROOT):
    return os.path.join(root, "appendix", "%s.tex" % entry.artifact_stem)


def emit(entries, root=DEFAULT_ROOT, with_appendix=True):
    """Write the LaTeX artifacts, the appendices, and the hash manifest."""
    rows = []
    for entry in entries:
        _atomic_write(latex_path(entry, root), entry.latex())
        row = {
            "name": str(entry.name),
            "branch": str(entry.branch),
            "word_hash": entry.word_hash,
            "latex": latex_path(entry, root),
            "interchange": entry.path,
            "lean": {
                "module": entry.lean_module,
                "declaration": entry.lean_declaration,
                "hash_constant": entry.lean_hash_constant,
            },
            "source": str(entry.source),
        }
        if with_appendix:
            _atomic_write(appendix_path(entry, root), appendix(entry))
            row["appendix"] = appendix_path(entry, root)
        rows.append(row)
    rows.sort(key=lambda r: (r["branch"], r["name"]))
    manifest = {
        "manifest_version": MANIFEST_VERSION,
        "ast_schema_version": AST_SCHEMA_VERSION,
        "generator": "scripts/dyadic_word_tex.py (dyadic ticket WW5)",
        "hash_rule": "sha256 of dyadic_search.words.ast.canonical_json (ticket S1.1)",
        "entries": rows,
    }
    _atomic_write(manifest_path(root),
                  json.dumps(manifest, sort_keys=True, indent=2,
                             ensure_ascii=True) + "\n")
    return manifest


# ---------------------------------------------------------------------------
# Part 6.  The D4 check (merge gate 7, hash half)
# ---------------------------------------------------------------------------

def _latex_trailer_hash(text):
    """The ``% ast-hash:`` value of a generated ``.tex``, or None."""
    found = None
    for line in text.splitlines():
        if line.startswith(HASH_COMMENT_PREFIX):
            found = line[len(HASH_COMMENT_PREFIX):].strip()
    return found


def _lean_constant_hash(text, constant):
    """The value of ``def <constant> : String := "…"`` in a Lean source, or None.

    Also accepts a bare ``-- ast-hash: <digest>`` marker line, which is what a
    hand-written words file may carry before its generated companion exists.
    """
    pattern = re.compile(
        r"def\s+%s\s*:\s*String\s*:=\s*\"([0-9a-f]{64})\"" % re.escape(constant))
    match = pattern.search(text)
    if match:
        return match.group(1)
    match = re.search(r"--\s*ast-hash:\s*([0-9a-f]{64})", text)
    return match.group(1) if match else None


def _module_path(module):
    """`GQ2.Dyadic.Words.N0` -> `GQ2/Dyadic/Words/N0.lean`."""
    return os.path.join(*module.split(".")) + ".lean"


def check(root=DEFAULT_ROOT, repo_root="."):
    """Merge gate 7's hash half.  Returns a list of failure strings (empty = pass).

    For every manifest entry:

    1. the recorded ``word_hash`` is re-derived from the interchange source, if that
       source is still readable — so a tree edited without regenerating fails here;
    2. the generated ``.tex`` exists and its ``% ast-hash`` trailer matches;
    3. the generated Lean artifact, when present, carries the same digest in its
       ``<name>_astHash`` constant;
    4. the in-repo Lean module named by the entry carries the same digest.

    A missing manifest with generated LaTeX present is a failure, not a skip: that is
    exactly the "wave shipped with the gate silently off" case.
    """
    failures = []
    manifest_file = os.path.join(repo_root, manifest_path(root))
    latex_dir = os.path.join(repo_root, root, "latex")
    if not os.path.exists(manifest_file):
        if os.path.isdir(latex_dir) and os.listdir(latex_dir):
            failures.append(
                "%s is missing but %s/ contains generated artifacts; merge gate 7 "
                "cannot be evaluated (regenerate with `dyadic_word_tex.py emit`)"
                % (manifest_path(root), os.path.join(root, "latex")))
        return failures
    with open(manifest_file, "r", encoding="utf-8") as stream:
        try:
            manifest = json.load(stream)
        except ValueError as exc:
            return ["%s: not valid JSON: %s" % (manifest_path(root), exc)]
    if manifest.get("manifest_version") != MANIFEST_VERSION:
        failures.append("%s: manifest_version %r, expected %d"
                        % (manifest_path(root), manifest.get("manifest_version"),
                           MANIFEST_VERSION))
    rows = manifest.get("entries")
    if not isinstance(rows, list) or not rows:
        failures.append("%s: no entries" % manifest_path(root))
        return failures

    for row in rows:
        name = row.get("name", "?")
        digest = row.get("word_hash", "")
        if not (isinstance(digest, str) and _HEX64_RE.match(digest)):
            failures.append("%s: word_hash is not a sha256 digest (%r)"
                            % (name, digest))
            continue

        source = row.get("interchange")
        if source and os.path.exists(os.path.join(repo_root, source)):
            try:
                recomputed = load_interchange(os.path.join(repo_root, source))
            except WordError as exc:
                failures.append("%s: interchange source rejected: %s" % (name, exc))
            else:
                if recomputed.word_hash != digest:
                    failures.append(
                        "%s: manifest hash %s but %s now hashes to %s -- the tree "
                        "changed without regenerating"
                        % (name, digest, source, recomputed.word_hash))

        latex_file = row.get("latex")
        if not latex_file or not os.path.exists(os.path.join(repo_root, latex_file)):
            failures.append("%s: generated LaTeX %r is missing" % (name, latex_file))
        else:
            with open(os.path.join(repo_root, latex_file), "r",
                      encoding="utf-8") as stream:
                trailer = _latex_trailer_hash(stream.read())
            if trailer is None:
                failures.append("%s: %s has no %r trailer"
                                % (name, latex_file, HASH_COMMENT_PREFIX.strip()))
            elif trailer != digest:
                failures.append("%s: LaTeX trailer %s != manifest %s"
                                % (name, trailer, digest))

        lean = row.get("lean") or {}
        constant = lean.get("hash_constant")
        module = lean.get("module")
        if not module or not constant:
            failures.append(
                "%s: no Lean module/declaration recorded; merge gate 7 needs BOTH "
                "sides of the tree, so an entry without a Lean home cannot pass"
                % name)
            continue
        lean_file = os.path.join(repo_root, _module_path(module))
        if not os.path.exists(lean_file):
            failures.append("%s: Lean module %s (%s) does not exist"
                            % (name, module, _module_path(module)))
            continue
        with open(lean_file, "r", encoding="utf-8") as stream:
            lean_hash = _lean_constant_hash(stream.read(), constant)
        if lean_hash is None:
            failures.append(
                "%s: %s declares no `def %s : String := \"<sha256>\"` (nor an "
                "`-- ast-hash:` marker)" % (name, _module_path(module), constant))
        elif lean_hash != digest:
            failures.append("%s: Lean %s = %s != manifest %s -- the TeX and the Lean "
                            "are NOT the same tree (merge gate 7 stop condition)"
                            % (name, constant, lean_hash, digest))

        generated_lean = os.path.join(repo_root, root, "lean",
                                      "%s.lean" % _capitalize(str(name)))
        if os.path.exists(generated_lean):
            with open(generated_lean, "r", encoding="utf-8") as stream:
                emitted = _lean_constant_hash(stream.read(), "%s%s"
                                              % (name, LEAN_HASH_SUFFIX))
            if emitted is not None and emitted != digest:
                failures.append("%s: generated Lean artifact hash %s != manifest %s"
                                % (name, emitted, digest))
    return failures


def _capitalize(name):
    """`pretty_lean.lean_file_name`'s capitalization."""
    return name[0].upper() + name[1:] if name else name


# ---------------------------------------------------------------------------
# Part 7.  Self-test: goldens, and the cross-repo hash pins
# ---------------------------------------------------------------------------
#
# Two kinds of pin.
#
# * GOLDEN_* — the simplification campaign's own AST fixtures
#   (`dyadic_search/tests/test_words_ast.py`), stored here as their canonical byte
#   strings.  Pinning the *bytes* rather than only the digest means a divergence is
#   reported as a diff, not as an opaque hash mismatch.
# * CROSS_REPO_PINS — the frozen selection rows (`artifacts/reports/selection-freeze.md`)
#   by certificate path and digest.  These run only when the simplification repo is
#   present (`--simp-root`, default `~/claude/general_2adic`); when it is absent they
#   are reported as skipped, never as passed.

GOLDEN_SQUARE_COMMUTATOR_JSON = (
    '{"children":[{"op":"Inverse","word":{"conjugator":{"name":"sigma","op":"Generat'
    'or"},"op":"Conjugate","word":{"name":"x0","op":"Generator"}}},{"definition":{"o'
    'p":"Omega2Power","word":{"children":[{"exponent":{"type":"Int","value":-3},"op"'
    ':"IntegerPower","word":{"name":"x0","op":"Generator"}},{"name":"tau","op":"Gene'
    'rator"}],"op":"Multiply"}},"name":"a","op":"Auxiliary"},{"exponent":{"type":"In'
    't","value":2},"op":"IntegerPower","word":{"name":"x1","op":"Generator"}},{"defi'
    'nition":{"left":{"name":"x1","op":"Generator"},"op":"Commutator","right":{"defi'
    'nition":{"conjugator":{"definition":{"op":"Omega2Power","word":{"name":"sigma",'
    '"op":"Generator"}},"name":"sigma2","op":"Auxiliary"},"op":"Conjugate","word":{"'
    'name":"x1","op":"Generator"}},"name":"y1","op":"Auxiliary"}},"name":"c","op":"A'
    'uxiliary"}],"op":"Multiply"}')

GOLDEN_HASH_SQUARE_COMMUTATOR = \
    "d129037ce96177524c5798cbe0c13d7844ab513d136360d1270dbd89e81051cb"

GOLDEN_SQUARE_COMMUTATOR_LATEX = (
    "% generated by dyadic_search.words.pretty_latex (ticket S1.8); "
    "do not hand-edit.\n"
    "% aux-style: macro\n"
    "% auxiliary definitions (campaign 9.3: the complexity counter charges "
    "each one once):\n"
    "a = (x_0^{-3}\\tau)^{\\omega_2}\n"
    "\\sigma_2 = \\sigma^{\\omega_2}\n"
    "y_1 = x_1^{\\sigma_2}\n"
    "c = [x_1,y_1]\n"
    "% displayed relation:\n"
    "(x_0^\\sigma)^{-1}a\\,x_1^2c\n"
    "% ast-hash: " + GOLDEN_HASH_SQUARE_COMMUTATOR + "\n")

#: Golden tree 2 — Shadow, OrbitNorm, EtaHat, ZhatPower, HyperbolicHandles, Pow2,
#: Param and Identity in one tree, i.e. every constructor `PWord` does *not* have.
GOLDEN_EXOTIC_JSON = (
    '{"kind":"M","op":"Shadow","parameters":[["alpha",{"type":"Int","value":2}],["mo'
    'de","rev"]],"word":{"length":{"name":"m","type":"Param"},"op":"OrbitNorm","step'
    '":{"name":"sigma2","op":"Generator"},"word":{"children":[{"exponent_spec":{"den'
    '":5,"num":3,"type":"EtaHat"},"op":"ZhatPower","word":{"name":"x0","op":"Generat'
    'or"}},{"count":{"left":{"name":"h","type":"Param"},"right":{"type":"Int","value'
    '":1},"type":"Add"},"op":"HyperbolicHandles","start_index":2},{"exponent":{"expo'
    'nent":{"name":"r","type":"Param"},"type":"Pow2"},"op":"IntegerPower","word":{"n'
    'ame":"x1","op":"Generator"}},{"op":"Identity"}],"op":"Multiply"}}}')

GOLDEN_HASH_EXOTIC = \
    "138294d6c1cb2a775795d9f002c1920dee8ccbee85ab4b831f8a31ed67cdbf6d"

GOLDEN_EXOTIC_LATEX = (
    "% generated by dyadic_search.words.pretty_latex (ticket S1.8); "
    "do not hand-edit.\n"
    "% aux-style: macro\n"
    "% displayed relation:\n"
    "\\operatorname{Sh}_M(\\mathcal{N}_{\\sigma_2,m}(x_0^{\\widehat{\\eta}}"
    "\\prod_{j=0}^{(h+1)-1}[x_{2+2j},x_{3+2j}]x_1^{2^r}1))\n"
    "% shadow: kind=M parameters={alpha=2, mode=rev}  (display and semantics are "
    "provisional; ticket S4.2 owns them, campaign 7.4)\n"
    "% etahat: \\widehat{\\eta} = 3/5  (num/den exactly as stored; the display "
    "shows only the symbol, campaign 3)\n"
    "% ast-hash: " + GOLDEN_HASH_EXOTIC + "\n")

#: The ticket-S1.M canonicalization, pinned: `EtaHat(3, 9)` *is* `EtaHat(1, 3)`.
ETAHAT_NONCANONICAL_JSON = (
    '{"exponent_spec":{"den":9,"num":3,"type":"EtaHat"},"op":"ZhatPower",'
    '"word":{"name":"x0","op":"Generator"}}')
ETAHAT_CANONICAL_JSON = (
    '{"exponent_spec":{"den":3,"num":1,"type":"EtaHat"},"op":"ZhatPower",'
    '"word":{"name":"x0","op":"Generator"}}')
ETAHAT_CANONICAL_HASH = \
    "44beb02490409778af2087f08d576048d43f79df8f6db7a1a1cafd13db69e64f"

DEFAULT_SIMP_ROOT = os.path.expanduser("~/claude/general_2adic")

#: The frozen selection rows, by certificate path (relative to the simplification
#: repo) and digest — `artifacts/reports/selection-freeze.md`, 2026-07-31.  Row 3
#: (noncompact `N`) is deliberately absent: its Sage certificates are still
#: `experimental` and the freeze doc lists no hash for it.
CROSS_REPO_PINS = (
    ("L", "artifacts/candidates/L-sq-n1-v001.json",
     "d129037ce96177524c5798cbe0c13d7844ab513d136360d1270dbd89e81051cb"),
    ("N0", "artifacts/candidates/N-compact-alpha2-h0-v001.json",
     "a940b6ad06d9728a6b0b5d20f27c76994d83103e65accc6b844fe6174755fc10"),
    ("M0", "artifacts/candidates/M-compact-alpha2-h0-q2-v001.json",
     "7c9005f50f9e1d5ddfa8880a3a3168d1a47661efdaae81339ab968055bbf036a"),
    ("Mpc", "artifacts/candidates/M-procyclic-alpha2-r1-eps1-eta1-h0-q2-v001.json",
     "55b24a4b141274bc30d09468096f4fa021184c5dc22c17823e423457928a26cf"),
)


def self_test(simp_root=None, verbose=True):
    """Goldens, round trips, and (when available) the cross-repo pins.

    Returns ``(passed, failed, skipped)`` counts and prints one line per check.
    """
    passed = failed = skipped = 0
    messages = []

    def check_eq(label, got, want):
        nonlocal passed, failed
        if got == want:
            passed += 1
            messages.append("ok    %s" % label)
        else:
            failed += 1
            messages.append("FAIL  %s\n        got  %r\n        want %r"
                            % (label, got, want))

    # -- golden tree 1: bytes, hash, LaTeX, round trip ----------------------
    tree = json.loads(GOLDEN_SQUARE_COMMUTATOR_JSON)
    check_eq("golden square-commutator canonical bytes",
             canonical_json(tree), GOLDEN_SQUARE_COMMUTATOR_JSON)
    check_eq("golden square-commutator content hash",
             content_hash(tree), GOLDEN_HASH_SQUARE_COMMUTATOR)
    check_eq("golden square-commutator LaTeX artifact",
             to_latex(tree), GOLDEN_SQUARE_COMMUTATOR_LATEX)

    # -- golden tree 2: every node PWord lacks ------------------------------
    exotic = json.loads(GOLDEN_EXOTIC_JSON)
    check_eq("golden exotic canonical bytes",
             canonical_json(exotic), GOLDEN_EXOTIC_JSON)
    check_eq("golden exotic content hash", content_hash(exotic), GOLDEN_HASH_EXOTIC)
    check_eq("golden exotic LaTeX artifact", to_latex(exotic), GOLDEN_EXOTIC_LATEX)

    # -- ticket S1.M: EtaHat canonicalizes on load --------------------------
    noncanonical = json.loads(ETAHAT_NONCANONICAL_JSON)
    check_eq("S1.M EtaHat(3,9) canonicalizes to EtaHat(1,3)",
             canonical_json(noncanonical), ETAHAT_CANONICAL_JSON)
    check_eq("S1.M EtaHat canonical hash",
             content_hash(noncanonical), ETAHAT_CANONICAL_HASH)

    # -- strictness ---------------------------------------------------------
    for label, payload in (
            ("unknown op", '{"op":"Nope"}'),
            ("extra field", '{"op":"Identity","x":1}'),
            ("missing field", '{"op":"Generator"}'),
            ("bool as Int", '{"op":"IntegerPower","word":{"op":"Identity"},'
                            '"exponent":{"type":"Int","value":true}}'),
            ("even EtaHat", '{"op":"ZhatPower","word":{"op":"Identity"},'
                            '"exponent_spec":{"type":"EtaHat","num":2,"den":3}}'),
            ("Omega2 in an integer slot",
             '{"op":"IntegerPower","word":{"op":"Identity"},'
             '"exponent":{"type":"Omega2"}}'),
            ("negative handle start",
             '{"op":"HyperbolicHandles","start_index":-1,'
             '"count":{"type":"Int","value":1}}')):
        try:
            canon_word(json.loads(payload))
        except WordError:
            passed += 1
            messages.append("ok    rejects %s" % label)
        else:
            failed += 1
            messages.append("FAIL  accepted %s (%s)" % (label, payload))

    # -- cross-repo pins ----------------------------------------------------
    root = simp_root or DEFAULT_SIMP_ROOT
    for branch, relative, digest in CROSS_REPO_PINS:
        label = "cross-repo pin %s (%s)" % (branch, os.path.basename(relative))
        path = os.path.join(root, relative)
        if not os.path.exists(path):
            skipped += 1
            messages.append("skip  %s -- %s not present" % (label, path))
            continue
        try:
            entry = load_interchange(path)
        except WordError as exc:
            failed += 1
            messages.append("FAIL  %s -- %s" % (label, exc))
            continue
        check_eq(label, entry.word_hash, digest)

    # -- optional: the live simplification module ---------------------------
    module = os.path.join(root, "dyadic_search", "words", "ast.py")
    if os.path.exists(module):
        sys.path.insert(0, root)
        try:
            from dyadic_search.words.ast import (      # noqa: E402
                content_hash as simp_hash, from_json as simp_from_json)
            from dyadic_search.words.pretty_latex import (  # noqa: E402
                to_latex as simp_to_latex)
        except Exception as exc:                       # pragma: no cover
            skipped += 1
            messages.append("skip  live simp cross-check -- import failed: %s" % exc)
        else:
            for label, payload in (("square commutator",
                                    GOLDEN_SQUARE_COMMUTATOR_JSON),
                                   ("exotic", GOLDEN_EXOTIC_JSON),
                                   ("noncanonical etahat",
                                    ETAHAT_NONCANONICAL_JSON)):
                tree = json.loads(payload)
                theirs = simp_from_json(tree)
                check_eq("live simp hash agrees (%s)" % label,
                         content_hash(tree), simp_hash(theirs))
                check_eq("live simp LaTeX agrees (%s)" % label,
                         to_latex(tree), simp_to_latex(theirs))
        finally:
            if sys.path and sys.path[0] == root:
                sys.path.pop(0)
    else:
        skipped += 1
        messages.append("skip  live simp cross-check -- %s not present" % module)

    if verbose:
        for message in messages:
            print(message)
        print("\n%d passed, %d failed, %d skipped" % (passed, failed, skipped))
    return passed, failed, skipped


# ---------------------------------------------------------------------------
# CLI
# ---------------------------------------------------------------------------

def _load_all(paths):
    entries = []
    for path in paths:
        entries.append(load_interchange(path))
    return entries


def main(argv=None):
    parser = argparse.ArgumentParser(
        prog="dyadic_word_tex.py",
        description="One-expression-tree TeX generator and hash gate (ticket WW5).")
    parser.add_argument("--root", default=DEFAULT_ROOT,
                        help="artifact root (default: %s)" % DEFAULT_ROOT)
    parser.add_argument("--repo-root", default=None,
                        help="repository root (default: the parent of scripts/)")
    subparsers = parser.add_subparsers(dest="command")

    for name, help_text in (
            ("hash", "print the content hash of each interchange file"),
            ("latex", "print the .tex artifact for one interchange file"),
            ("appendix", "print the ledger section 7 appendix skeleton"),
            ("emit", "write generated/ artifacts and the hash manifest")):
        sub = subparsers.add_parser(name, help=help_text)
        sub.add_argument("files", nargs="+")

    subparsers.add_parser("check", help="merge gate 7 hash check (check_dyadic.sh D4)")
    test_parser = subparsers.add_parser("self-test",
                                        help="goldens and cross-repo hash pins")
    test_parser.add_argument("--simp-root", default=None,
                             help="simplification repo (default: %s)"
                                  % DEFAULT_SIMP_ROOT)

    args = parser.parse_args(argv)
    repo_root = args.repo_root or os.path.dirname(os.path.dirname(
        os.path.abspath(__file__)))

    if args.command in (None, "check"):
        failures = check(root=args.root, repo_root=repo_root)
        if failures:
            print("one-tree hash check FAILED (merge gate 7):")
            for failure in failures:
                print("  - %s" % failure)
            return 1
        print("one-tree hash check passed (merge gate 7)")
        return 0

    if args.command == "self-test":
        _, failed, _ = self_test(simp_root=args.simp_root)
        return 1 if failed else 0

    entries = _load_all(args.files)
    if args.command == "hash":
        for entry in entries:
            print("%s  %s" % (entry.word_hash, entry.path))
        return 0
    if args.command == "latex":
        for entry in entries:
            sys.stdout.write(entry.latex())
        return 0
    if args.command == "appendix":
        for entry in entries:
            sys.stdout.write(appendix(entry))
        return 0
    if args.command == "emit":
        # Artifact and interchange paths are recorded relative to the repository
        # root, because that is what `check` resolves them against.
        for entry in entries:
            absolute = os.path.abspath(entry.path)
            if absolute.startswith(os.path.abspath(repo_root) + os.sep):
                entry.path = os.path.relpath(absolute, repo_root)
        previous = os.getcwd()
        os.chdir(repo_root)
        try:
            manifest = emit(entries, root=args.root)
        finally:
            os.chdir(previous)
        for row in manifest["entries"]:
            print("%s  %s" % (row["word_hash"], row["latex"]))
        return 0
    parser.error("unknown command %r" % args.command)


if __name__ == "__main__":
    sys.exit(main())
