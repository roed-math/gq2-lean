"""W61-WIDER step 8: emit the Lean soundness lemmas with their certified witnesses.

Each lemma below says "this block is even on the achievable lattice", and its proof is
`refine <half>, by rw [...]; ring` where `<half>` is the exact integer half computed in
`parity_blocks.py`.  Nothing is guessed and nothing is hand-transcribed.
"""
import sys
import os

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, os.path.join(os.path.dirname(HERE), "w59_defect5"))
sys.path.insert(0, HERE)

import parity_blocks as B                                     # noqa: E402

HALF = B.HALF
render = B.render
namer = B.namer

CORE_HYPS = [("hsa", "s.a", "sa"), ("hsc", "s.c", "sc"), ("hxa", "x.a", "xa"),
             ("hxc", "x.c", "xc"), ("hya", "y.a", "ya"), ("hyc", "y.c", "yc"),
             ("h0f", "z₀.f", "zf0"), ("h0h", "z₀.h", "zh0"), ("h0j", "z₀.j", "zj0"),
             ("h1f", "z₁.f", "zf1"), ("h1h", "z₁.h", "zh1"), ("h1j", "z₁.j", "zj1"),
             ("h2f", "z₂.f", "zf2"), ("h2h", "z₂.h", "zh2"), ("h2j", "z₂.j", "zj2")]

HANDLE_HYPS = [("hpa", "p.a", "pa"), ("hpc", "p.c", "pc"), ("hqa", "q.a", "qa"),
               ("hqc", "q.c", "qc"),
               ("hzf", "z.f", "zf"), ("hzh", "z.h", "zh"), ("hzj", "z.j", "zj"),
               ("hwf", "w.f", "wf"), ("hwh", "w.h", "wh"), ("hwj", "w.j", "wj")]

PAIR_HYPS = [("hLa", "L.a", "La"), ("hLc", "L.c", "Lc"),
             ("hzf", "z.f", "zf"), ("hzh", "z.h", "zh"), ("hzj", "z.j", "zj")]


def hypline(hyps, indent="    "):
    out, cur = [], ""
    for nm, coord, _ in hyps:
        piece = "(%s : (2 : R) ∣ %s)" % (nm, coord)
        add = piece if not cur else cur + " " + piece
        if len(add) + len(indent) > 96 and cur:
            out.append(cur)
            cur = piece
        else:
            cur = add
    out.append(cur)
    return ("\n" + indent).join(out)


def obtains(hyps, indent="  "):
    return "\n".join("%sobtain ⟨%s, %s⟩ := %s" % (indent, half, nm, nm)
                     for nm, _, half in hyps)


def rwline(hyps, extra, indent="  ", tac="rw"):
    names = [extra] + [nm for nm, _, _ in hyps]
    out, cur = [], ""
    for nm in names:
        add = nm if not cur else cur + ", " + nm
        if len(add) + len(indent) + 6 > 96 and cur:
            out.append(cur + ",")
            cur = nm
        else:
            cur = add
    out.append(cur)
    return indent + tac + " [" + ("\n" + indent + "  ").join(out) + "]"


def lemma(name, hyps, statement, defname, key, doc):
    return """%s
theorem %s {R : Type} [CommRing R] {s x y z₀ z₁ z₂ : SqU6 R}
    %s :
    %s := by
%s
  refine ⟨%s, ?_⟩
%s
  ring
""" % (doc, name, hypline(hyps), statement, obtains(hyps),
       render(HALF[key], namer, width=92, indent=4), rwline(hyps, defname))


BLOCKS = []

BLOCKS.append(lemma(
    "SqU6.gaTwoQuadO_even", CORE_HYPS,
    "(2 : R) ∣ SqU6.gaTwoQuadO s x y z₀ z₁ z₂", "SqU6.gaTwoQuadO", "quadO",
    """/-- ⭐⭐⭐ **THE HEADLINE: the class-five quadratic block is EVEN on the achievable
lattice.**  At a marking whose slots have even `(1,2)`- and `(3,4)`-columns, and for dressings
in the honest `gamma_2` of the image (which `GradedFiveStageFour.stageN2_of_commutator` puts
inside `f`, `h`, `j` all even), every one of the fifty-two terms of `SqU6.gaTwoQuadO` is even.
So the `gamma_2` transport at class five is **affine mod two**, exactly as wave 54 found one
class down, and the difficulty the campaign had been anticipating collapses.  ⚠ The class-four
RIGHT row does not share this: `SqU6.gaTwoQuadN` is generically odd there
(`scripts/w61_wider/results/parity_blocks.txt`). -/"""))

BLOCKS.append(lemma(
    "SqU6.gaTwoCorrO_even", CORE_HYPS,
    "(2 : R) ∣ SqU6.gaTwoCorrO s x y z₀ z₁ z₂", "SqU6.gaTwoCorrO", "corrO",
    """/-- ⭐⭐ **The class-five correction block is even on the achievable lattice.**  Nine of
its twenty-one coefficient blocks are killed by the dressing's even `f`, `h`, `j`; the other
twelve have every monomial carrying a frame `(1,2)`- or `(3,4)`-column. -/"""))

BLOCKS.append("""/-- **The three channels the frame does not close**: the class-five pairing
form's terms against the letter's fifth abelian column, its class-three row, and its class-two
row.  Wave 60's stage-four analogue closes two of five channels with the frame and three with
the dressing; here the same three survive, one filtration step wider. -/
def SqU6.gaTwoChannel {R : Type} [CommRing R] (z L : SqU6 R) : R :=
  z.m * L.e + z.i * L.j + z.l * L.f
""")

BLOCKS.append("""/-- ⭐ **The class-five pairing form is even modulo the three channels.** -/
theorem SqU6.gaTwoPairO_channel_even {R : Type} [CommRing R] {z L : SqU6 R}
    %s :
    (2 : R) ∣ (SqU6.gaTwoPairO z L - SqU6.gaTwoChannel z L) := by
%s
  refine ⟨%s, ?_⟩
%s
  ring
""" % (hypline(PAIR_HYPS), obtains(PAIR_HYPS),
       render(HALF["pairO"], namer, width=92, indent=4),
       rwline(PAIR_HYPS, "SqU6.gaTwoPairO, SqU6.gaTwoChannel")))

BLOCKS.append("""/-- **The first class-three pairing form is even**, which is what kills the
collection element and the cross-handle term. -/
theorem SqU6.gaTwoPairJ_even {R : Type} [CommRing R] {z L : SqU6 R}
    (hzf : (2 : R) ∣ z.f) (hLa : (2 : R) ∣ L.a) : (2 : R) ∣ SqU6.gaTwoPairJ z L := by
  obtain ⟨zf, hzf⟩ := hzf
  obtain ⟨La, hLa⟩ := hLa
  exact ⟨zf * L.c - z.g * La, by rw [SqU6.gaTwoPairJ, hzf, hLa]; ring⟩
""")

BLOCKS.append("""/-- ⭐ **The handle shift's class-five row is even modulo its two channels.** -/
theorem SqU6.gaTwoHandle_o_channel_even {R : Type} [CommRing R] {p q z w : SqU6 R}
    %s :
    (2 : R) ∣ ((SqU6.gaTwoHandle p q z w).o
      - (SqU6.gaTwoChannel z q - SqU6.gaTwoChannel w p)) := by
%s
  refine ⟨%s, ?_⟩
%s
  ring
""" % (hypline(HANDLE_HYPS), obtains(HANDLE_HYPS),
       render(HALF["handleO"], namer, width=92, indent=4),
       rwline(HANDLE_HYPS,
              "SqU6.gaTwoHandle, SqU6.gaTwoHandleX, SqU6.gaTwoChannel, SqU6.gaTwoPairO,\n"
              "    SqU6.u6Comm3L, SqU6.u6Comm3R", tac="simp only")))

with open(os.path.join(HERE, "results", "lean_soundness.txt"), "w") as fh:
    fh.write("\n".join(BLOCKS))
print("wrote results/lean_soundness.txt (%d blocks)" % len(BLOCKS))
