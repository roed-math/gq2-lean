"""W60-STAGE4 step 3: the parity chain that bounds `gamma_3` of the image.

The stage-four shift's class-five row is affine in the dressing, with each term one dressing
coordinate against a frame quantity.  So the exclusion needs a bound on the PARITIES of the
achievable `gamma_3`-dressings, one level lower than wave 59's `forceLcs_three_le_forceN4`,
which bounds `gamma_4`.  This script prints the exact commutator coordinates the chain has to
control, with the frame hypotheses substituted in, so the Lean subgroups can be read off rather
than guessed:

    N1  : an even (1,2)-column AND an even (3,4)-column          [both letters' hypotheses]
    N2  : gamma_2-shaped, with f, h and j even                   [what a commutator of N1's is]
    N3  : gamma_3-shaped, with j, k, l and m even                [what [N2, N1] is]

The last is the object the exclusion reads.

BRACKET CONVENTION.  [PAPER]
This script computes brackets in the paper convention, and its Lean target is written
with commP, the same convention.
Paper convention: commP x y = x^-1 y^-1 x y (GQ2/Words.lean:59, and every python commP
in scripts/).  Mathlib convention: [x, y] = x y x^-1 y^-1.  They are DIFFERENT families,
[x, y]_mathlib = commP x^-1 y^-1 (GradedFiveForce.commutatorElement_eq_commP), so a
paper-convention computation certifies a commP-written Lean statement and MIS-certifies a
[.,.]-written one.  Normal-closure and subgroup sifts are convention-IMMUNE.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))

import u6poly as P                                            # noqa: E402
from u6poly import U6, pvar, pzero, poly_str                  # noqa: E402

COORDS = P.COORDS


def zero_out(z, cos):
    for co in cos:
        setattr(z, co, pzero())
    return z


def parity_report(name, poly, evens):
    """Print the polynomial and say whether every monomial meets an even generator."""
    bad = [mon for mon in poly if not any(v in evens for v in mon)]
    print("   %s : %d terms, %s" % (name, len(poly),
                                    "EVEN" if not bad else "NOT forced even"))
    if bad:
        print("        the terms that escape: %s" % poly_str({m: poly[m] for m in bad}))


print("== A. a commutator of two general letters ==")
p, q = U6.gen("p"), U6.gen("q")
c = P.commP(p, q)
print("   abelian columns of a commutator all vanish: %s"
      % all(not getattr(c, co) for co in "abcde"))
# the letters' hypotheses: a and c columns even
EVEN_LETTER = {"p_a", "p_c", "q_a", "q_c"}
for co in ("f", "g", "h", "i", "j", "k", "l"):
    parity_report("[p, q]." + co, getattr(c, co), EVEN_LETTER)
print()

print("== B. a commutator of a gamma_2-element against a letter ==")
w = zero_out(U6.gen("w"), ["a", "b", "c", "d", "e"])
c2 = P.commP(w, q)
print("   the class-<= 2 coordinates of [w, q] vanish: %s"
      % all(not getattr(c2, co) for co in "abcdefghi"))
EVEN2 = {"q_a", "q_c", "w_f", "w_h", "w_j"}
for co in ("j", "k", "l", "m", "n"):
    parity_report("[w, q]." + co, getattr(c2, co), EVEN2)
print()
print("   the exact class-four rows, for the record:")
print("     [w, q].m = %s" % poly_str(c2.m))
print("     [w, q].n = %s" % poly_str(c2.n))
print()

print("== C. a commutator of a gamma_3-element against a letter (wave 59's level) ==")
z = zero_out(U6.gen("z"), ["a", "b", "c", "d", "e", "f", "g", "h", "i"])
c3 = P.commP(z, q)
print("   [z, q] is gamma_4-shaped: %s"
      % all(not getattr(c3, co) for co in "abcdefghijkl"))
for co in ("m", "n", "o"):
    print("     [z, q].%s = %s" % (co, poly_str(getattr(c3, co))))
print()

print("== D. the three subgroup conditions, closed under the group law ==")
u, v = U6.gen("u"), U6.gen("v")
prod = u * v
print("   (u*v).f = %s" % poly_str(prod.f))
print("   (u*v).j = %s" % poly_str(prod.j))
print("   (u*v).m = %s" % poly_str(prod.m))
uw = zero_out(U6.gen("u"), ["a", "b", "c", "d", "e"])
vw = zero_out(U6.gen("v"), ["a", "b", "c", "d", "e"])
pw = uw * vw
print("   gamma_2-shaped: (u*v).f = %s, (u*v).h = %s, (u*v).j = %s"
      % (poly_str(pw.f), poly_str(pw.h), poly_str(pw.j)))
uz = zero_out(U6.gen("u"), list("abcdefghi"))
vz = zero_out(U6.gen("v"), list("abcdefghi"))
pz = uz * vz
print("   gamma_3-shaped: (u*v).j = %s, (u*v).m = %s, (u*v).o = %s"
      % (poly_str(pz.j), poly_str(pz.m), poly_str(pz.o)))
print("   gamma_3-shaped inverse: (u^-1).j = %s, (u^-1).m = %s"
      % (poly_str(uz.inv().j), poly_str(uz.inv().m)))
