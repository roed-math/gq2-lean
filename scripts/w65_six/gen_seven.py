"""W65-SIX: write `GQ2/Dyadic/SqCore/GradedSeven.lean`, the class-six carrier `SqU7 = U_7`.

The coordinate law is a printout of `u7lib`'s honest matrix arithmetic (product and back
substitution), whose `n = 6` instance is certified field by field against the committed `SqU6`
law in `derive_six.py` section 1.  So no formula in the emitted file is hand-transcribed.
"""

import sys

sys.path.insert(0, "/Users/roed/claude/cla/worktrees/w65-six/scripts/w65_six")

from emit_u7 import FIELD, ORDER, lean_poly, sym
from u7lib import PolyRing, minv, mmul

OUT = "/Users/roed/claude/cla/worktrees/w65-six/GQ2/Dyadic/SqCore/GradedSeven.lean"

CLASS_OF = {rc: rc[1] - rc[0] for rc in ORDER}

HEADER = '''/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.SqCore.GradedFive

/-!
# W65-SIX: the class-six test group `SqU7 = U_7`

The campaign's class-`N` test group is `U_{N+1}`: `SqHeis = U_3` is class two, `SqU4` class
three, `SqU5` class four and `SqU6` class five, carried on the fifteen strictly-upper entries of
a `6 x 6` unitriangular matrix with the class-five coordinate at `(1,6)`.  Class **six**
therefore needs a seventh index, and the tree had no such group: every class-six commutator
vanishes identically in `SqU6`, so a class-six statement written there is vacuous.

This file supplies the missing layer, and nothing else.  `SqU7 R` is the unitriangular `7 x 7`
group over a commutative ring `R`, carried on its twenty-one strictly-upper entries named after
their cells, `e12 ... e67` at class one up to the single class-six coordinate `e17`.

## Provenance of the coordinate law

⚠ Not hand-transcribed.  `scripts/w65_six/u7lib.py` implements `U_n(R)` as honest `n x n`
matrices with matrix multiplication and back-substitution inverse, generic in `n`;
`scripts/w65_six/derive_six.py` section 1 certifies its `n = 6` instance field by field against
the **committed** `SqU6` law of `GradedFive.lean` (all fifteen fields agree for both the product
and the inverse, symbolically over `Z[vars]`); and `scripts/w65_six/gen_seven.py` prints this
file from the `n = 7` instance of the same arithmetic.  So the law below is the law the campaign
already trusts, one index wider.

## What this file does NOT contain

⚠ No separation statement, no marking, no `sqWord` fact.  Those live in
`GQ2/Dyadic/SqCore/GradedSepSix.lean`, which is the only consumer.  This file is a carrier: the
group, its coordinate projections, and decidable equality.
-/

namespace GQ2

namespace Dyadic

namespace SqCore

/-! ## 1 The class-six test group `SqU7 R` -/

section U7Group

/-- **The class-six test group** over `R`: the unitriangular `7 x 7` group, carried on the
twenty-one strictly-upper entries `e<r><c>`, the `(r,c)` entry of the matrix. -/
@[ext]
structure SqU7 (R : Type) [CommRing R] where
'''

FOOTER = '''
/-! ## 2 Finiteness, the discrete topology, and pro-`2`-ness

Transposed from `SqU6`'s block (`GradedFive.lean` section 3): the same six declarations with
`15` replaced by `21`.  They exist so that a relator-killing marking into `SqU7` classifies a
continuous homomorphism through `sqLiftHom`, which needs `IsProP 2`. -/

/-- The underlying twenty-one-tuple, as an equivalence. -/
def equivProd : SqU7 R ≃
    %(prodty)s where
  toFun p := (%(tofun)s)
  invFun v := ⟨%(invfun)s⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite R] : Finite (SqU7 R) := Finite.of_equiv _ equivProd.symm

/-- The cardinality of the class-six test group. -/
theorem nat_card [Finite R] : Nat.card (SqU7 R) = Nat.card R ^ 21 := by
  rw [Nat.card_congr equivProd,
    %(cardprod)s]
  ring

instance : TopologicalSpace (SqU7 R) := ⊥

instance : DiscreteTopology (SqU7 R) := ⟨rfl⟩

/-- **The class-six test group is pro-2** whenever the coefficient ring is a finite 2-ring:
its order is `(#R)^21`. -/
theorem isProP_two [Finite R] {mm : ℕ} (hR : Nat.card R = 2 ^ mm) : IsProP 2 (SqU7 R) :=
  isProP_of_isPGroup (IsPGroup.of_card (n := 21 * mm) (by rw [nat_card, hR, ← pow_mul, mul_comm]))

/-- The twenty-one coordinates of a `SqU7` element determine triviality. -/
theorem eq_one_iff {p : SqU7 R} :
    p = 1 ↔ %(conj)s := by
  constructor
  · rintro rfl
    exact ⟨%(rfls)s⟩
  · rintro ⟨%(names)s⟩
    ext <;> simpa

instance instDecidableEq {R : Type} [CommRing R] [DecidableEq R] : DecidableEq (SqU7 R) :=
  fun _ _ => decidable_of_iff _ SqU7.ext_iff.symm

end SqU7

end U7Group

end SqCore

end Dyadic

end GQ2
'''


def main():
    P, Q = sym("p"), sym("q")
    prod = mmul(P, Q, PolyRing)
    invm = minv(P, PolyRing)

    L = [HEADER]

    # --- structure fields
    ordinals = {1: "first", 2: "second", 3: "third", 4: "fourth", 5: "fifth", 6: "sixth"}
    for rc in ORDER:
        f, cl = FIELD[rc], CLASS_OF[rc]
        idx = sum(1 for o in ORDER if CLASS_OF[o] == cl and ORDER.index(o) <= ORDER.index(rc))
        which = ordinals.get(idx, f"{idx}th")
        if cl == 6:
            doc = f"The `({rc[0] + 1},{rc[1] + 1})` entry: the class-six coordinate."
        else:
            doc = (f"The `({rc[0] + 1},{rc[1] + 1})` entry: the {which} class-{cl} "
                   f"coordinate." if cl > 1 else
                   f"The `({rc[0] + 1},{rc[1] + 1})` entry: the {which} abelian coordinate.")
        L.append(f"  /-- {doc} -/\n  {f} : R\n")

    L.append("\nnamespace SqU7\n\nvariable {R : Type} [CommRing R]\n\n")

    # --- One
    zeros = ", ".join(["0"] * len(ORDER))
    L.append(f"instance : One (SqU7 R) := ⟨⟨{zeros}⟩⟩\n\n")

    # --- Mul
    L.append("instance : Mul (SqU7 R) :=\n  ⟨fun p q => ⟨")
    body = []
    for rc in ORDER:
        body.append(lean_poly(prod[rc[0]][rc[1]]))
    L.append(wrap_ctor(body))
    L.append("⟩⟩\n\n")

    # --- Inv
    L.append("instance : Inv (SqU7 R) :=\n  ⟨fun p => ⟨")
    body = [lean_poly(invm[rc[0]][rc[1]]) for rc in ORDER]
    L.append(wrap_ctor(body))
    L.append("⟩⟩\n\n")

    # --- simp lemmas
    for rc in ORDER:
        L.append(f"@[simp] theorem one_{FIELD[rc]} : (1 : SqU7 R).{FIELD[rc]} = 0 := rfl\n")
    L.append("\n")
    for rc in ORDER:
        f = FIELD[rc]
        rhs = lean_poly(prod[rc[0]][rc[1]])
        stmt = f"@[simp] theorem mul_{f} (p q : SqU7 R) : (p * q).{f} = {rhs} := rfl"
        L.append(fmt_thm(stmt, f"@[simp] theorem mul_{f} (p q : SqU7 R) :",
                         f"(p * q).{f} = {rhs} := rfl"))
    L.append("\n")
    for rc in ORDER:
        f = FIELD[rc]
        rhs = lean_poly(invm[rc[0]][rc[1]])
        L.append(fmt_thm(f"@[simp] theorem inv_{f} (p : SqU7 R) : p⁻¹.{f} = {rhs} := rfl",
                         f"@[simp] theorem inv_{f} (p : SqU7 R) :",
                         f"p⁻¹.{f} = {rhs} := rfl"))
    L.append("\n")

    muls = ", ".join(f"mul_{FIELD[rc]}" for rc in ORDER)
    invs = ", ".join(f"inv_{FIELD[rc]}" for rc in ORDER)
    ones = ", ".join(f"one_{FIELD[rc]}" for rc in ORDER)
    L.append("instance : Group (SqU7 R) where\n")
    L.append("  mul_assoc p q r := by\n")
    L.append(indent_list("    ext <;> simp only [", muls, "] <;> ring\n"))
    L.append("  one_mul p := by ext <;> simp\n")
    L.append("  mul_one p := by ext <;> simp\n")
    L.append("  inv_mul_cancel p := by\n")
    L.append("    ext <;>\n")
    L.append(indent_list("      simp only [", muls + ", " + invs + ", " + ones,
                         "] <;> ring\n"))

    conj = " ∧ ".join(f"p.{FIELD[rc]} = 0" for rc in ORDER)
    n = len(ORDER)
    proj = ["v" + ".2" * i + (".1" if i < n - 1 else "") for i in range(n)]
    L.append(FOOTER % {
        "prodty": wrap_expr(" × ".join(["R"] * n), width=90, lead="    "),
        "tofun": wrap_expr(", ".join(f"p.{FIELD[rc]}" for rc in ORDER), width=88,
                           lead="    "),
        "invfun": wrap_expr(", ".join(proj), width=88, lead="    "),
        "cardprod": wrap_expr(", ".join(["Nat.card_prod"] * (n - 1)), width=88,
                              lead="    "),
        "conj": wrap_conj(conj),
        "rfls": wrap_expr(", ".join(["rfl"] * len(ORDER)), width=88, lead="      "),
        "names": wrap_expr(", ".join(f"h{FIELD[rc]}" for rc in ORDER), width=88,
                           lead="      "),
    })

    with open(OUT, "w") as fh:
        fh.write("".join(L))
    print(f"wrote {OUT}")
    with open(OUT) as fh:
        txt = fh.read()
    print(f"  {len(txt.splitlines())} lines, {len(txt)} chars")
    over = [(i + 1, len(ln)) for i, ln in enumerate(txt.splitlines()) if len(ln) > 100]
    print(f"  lines over 100 cols: {len(over)}")
    for i, w in over[:15]:
        print(f"    line {i}: {w}")


def wrap_ctor(body, width=94, lead="    "):
    """One constructor component per line, each wrapped internally with a deeper indent."""
    out = []
    for i, b in enumerate(body):
        piece = b + ("," if i < len(body) - 1 else "")
        out.append(wrap_expr(piece, width=width - len(lead), lead=lead + "  "))
    return ("\n" + lead).join(out)


def fmt_thm(one_line, head, tail, width=100):
    if len(one_line) <= width:
        return one_line + "\n"
    return head + "\n    " + wrap_expr(tail, lead="      ") + "\n\n"


def wrap_expr(expr, width=94, lead="      "):
    toks = expr.split(" ")
    out, cur = [], ""
    for t in toks:
        if cur and len(cur) + 1 + len(t) > width:
            out.append(cur)
            cur = t
        else:
            cur = (cur + " " + t).strip()
    if cur:
        out.append(cur)
    return ("\n" + lead).join(out)


def wrap_conj(conj, width=92, lead="      "):
    """Wrap a `∧`-chain, breaking only at the connectives."""
    parts = conj.split(" ∧ ")
    lines, cur = [], ""
    for i, p in enumerate(parts):
        piece = p + (" ∧" if i < len(parts) - 1 else "")
        if cur and len(cur) + 1 + len(piece) > width:
            lines.append(cur)
            cur = piece
        else:
            cur = (cur + " " + piece).strip()
    if cur:
        lines.append(cur)
    return ("\n" + lead).join(lines)


def indent_list(prefix, items, suffix, width=94, lead="      "):
    """`prefix` + a comma list + `suffix`, wrapped so no line exceeds `width`."""
    txt = prefix + items + suffix
    if len(txt) <= width:
        return txt
    parts = [p + "," for p in items.split(", ")]
    parts[-1] = parts[-1][:-1]
    lines, cur = [], prefix
    for p in parts:
        cand = (cur + " " + p) if not cur.endswith("[") else (cur + p)
        if len(cand) > width:
            lines.append(cur)
            cur = lead + p
        else:
            cur = cand
    if len(cur + suffix) > width:
        lines.append(cur)
        cur = lead + suffix.lstrip()
    else:
        cur = cur + suffix
    lines.append(cur)
    return "\n".join(lines)


if __name__ == "__main__":
    main()
