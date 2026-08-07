# W50 — the class-three selection among class-two-admissible dressings

**Wave W50, worker W50-SELECT.**  Companion to `GQ2/Dyadic/SqCore/GradedSelect.lean` §5–§7
(all committed, std-3, census unchanged).  Reads the depth sweep's memo
(`docs/dyadic/w50-depth-sweep.md`) where the two overlap.

The residual is `SqLamMarkTransitivity h` ⟺ `SqClearingStep h` ⟺ `SqArbRelWord h`.  W48/W49
established that the class-three gate passes the arbitrary-dressing frame with the class-two
forced dressing, while sampling said class three *selects* among class-two-admissible
dressings.  This memo records what the selection **is** — as linear algebra, as a single
𝔽₂-form, and as a constraint a future construction can consult instead of searching.

---

## 0.  Headline

| ticket question | answer |
|---|---|
| express the class-three defect of the dressed frame as an affine-linear function of the γ₂-components of the dressings | **Done**: `sqRelWord_selRefine`.  The refinement action translates the relator by a *central* element, affine-linear in the dressings, with closed form `−4·w₁.f + 2·w₂.f + (z₃.d·(m V).c − z₃.e·(m V).a) + ((m U).a·z₄.e − (m U).c·z₄.d)` |
| is the linear part surjective onto the class-three defect space? | **No — nowhere on the uncleared locus.**  Its image lies in `2·ℤ/8` at *every* uncleared selected marking.  The **cokernel functional is reduction mod 2** (`selCross_even`, `selPair_even`, `selPair_even'`): the parity of the class-three residue — the **selection bit** — is invariant under every achievable refinement |
| does non-surjectivity refute anything? | No: it is the slice shadow of the sweep's *structural containment* (`im δ` has corank `d+1` at every level, and the actual defect always lands inside).  The right formalization target is the containment, not surjectivity — confirmed independently here |
| characterize the survivor set | On the live locus (`2`-pairing witness present): **a class-two-admissible tuple is refinable to a class-three survivor iff its residue is even** — obstruction `sqRelWord_selRefine_ne_one`, completion `sqRelWord_selRefine_eq_one` (one explicit γ₂-move).  The bit itself is the explicit 𝔽₂-form of §3 below |
| does the selection actually bite? | **Yes, machine-checked on `sqArbFrame`**: the legal dressing `a₃ = t = x₁x₀⁻²` (λ- and ν′-trivial, class-two-invisible) has residue `1` at the κ₃-odd hom `(A,B,C,D,P,Q) = (4,1,2,1,2,1)` — dead under *every* refinement — and residue `6` at the committed hom `(2,1,2,1,7,1)` — repaired by one explicit move.  Same marking, same dressing, two fates (§6c of the Lean file) |
| the sweep's σ-slot forcing | **The slice provably cannot see it**: `sqRelWord_selHom_sqArbFrame_sigma` shows `a₀ = a₁ = U⁻¹` (the sweep's universal witness shape) passes every hom of the family, exactly as the committed `a₀ = 1` does.  §5 below gives the wider-slice design that could see it |

---

## 1.  The linear algebra of the γ₂-dressing action (ticket goal 1)

Fix a hom `Φ = selHom h ν′ j A B C D P Q` of the selection family (b-column = ν′, x₀ ↦ 1,
adjacency parities `2P + (AS − BT) = 0`, `2Q + (TD − SC) = 0` with `T = ν′(u_j)`,
`S = ν′(v_j)` mod 8).  Write `m` for the image tuple of a dressed frame.

**The action.**  Multiplying the dressing of a slot on the right by an element of `γ₂(D_sq)`
multiplies the slot image by an element of `γ₂(im Φ)`.  In `SqU4`:

* γ₂-shaped elements (`a = b = c = 0`) leave all abelian columns fixed;
* the `(d,e)`-image of `γ₂(im Φ)` is exactly the lattice
  `Λ = ⟨(−A, C), (−B, D), (−2P, −2Q)⟩` — the pairings `[σ,u]`, `[σ,v]`, `[u,v]` of the
  marking's generators (conjugation fixes `(d,e)` on γ₂, products add);
* the `f`-image is `Λ₃ = ⟨2AC, AD+BC, 2BD, 2(QA−PC), 2(QB−PD)⟩` (pairings of `Λ` against
  the generator columns).

**The closed form** (`sqRelWord_selRefine`, over any commutative ring): refining the two
exponent slots by γ₃-elements `w₁, w₂` and the two `j`-handle slots by γ₂-elements `z₃, z₄`
translates the relator by the central element with `f`-value

```text
Δ = −4·w₁.f + 2·w₂.f + (z₃.d·(m V).c − z₃.e·(m V).a) + ((m U).a·z₄.e − (m U).c·z₄.d).
```

Every class-`≤2` row is untouched — the refinement acts *within* the class-two solution set,
by translations on the class-three residue.  The "matrix" of the linear part is therefore the
pairing of `Λ ⊕ Λ ⊕ Λ₃` against the handle columns and the exponent weights `(−4, 2)`.

**Non-surjectivity, and the cokernel.**  The achievable handle columns lie in the affine
lattice `W = {(Au + Bv, Cu + Dv)}` (the two free characters evaluated on the abelianized
dressing lattice `K̄`; `t̄` and the other handles are invisible to both characters).  The two
adjacency parities force

```text
A·D + B·C ≡ 0 (mod 2)      at every uncleared row type            (selCross_even)
```

— mod 2 the three uncleared types give `(A,C) ≡ (0,0)`, or `(B,D) ≡ (0,0)`, or
`(A,C) ≡ (B,D)`, and each kills `AD + BC` — and with it **every** `Λ`-against-`W` pairing is
even (`selPair_even`, `selPair_even'`; the `(−2P,−2Q)`-generator and `−4w₁.f + 2w₂.f` are
even outright).  So

> **im(linear part) ⊆ 2·ℤ/8, and the cokernel functional is reduction mod 2.**

The parity of the class-three residue is an invariant of the whole refinement orbit — the
**selection bit**.  This is the exact slice shadow of the sweep's corank-`(d+1)` finding: one
`ℤ/8`-row of the slice sees one 𝔽₂-functional of the sweep's six (at `h = 1`); the other five
live on the wider layer the slice's single test hom cannot span.

**Sharpness.**  The containment is an equality on the live locus: if some achievable `V`-column
`(x, y) ∈ W`-coset has `B·y + D·x = 2·unit` (e.g. `B, D` odd at the `(0,1)` type), the
`(−B,D)`-generator alone reaches all of `2·ℤ/8` — that is the completion's hypothesis
`rr·(B·(m V).c + D·(m V).a) = 2` and it is *checked live* at both instance homs.  At
degenerate weight tuples `J` can shrink to `4·ℤ/8` or `0`; the selection then reads finer
residues than the bit.  (Not formalized; the two instance homs both have `J = 2·ℤ/8`.)

---

## 2.  The selection iff (ticket goal 2)

On the live locus the survivor structure among class-two-admissible dressings is exactly:

```text
tuple m (five lower rows zero)  is refinable to a relator-killing tuple
        ⟺   residue (sqRelWord m).f ∈ J  =  2·ℤ/8
        ⟺   the selection bit  selPar (sqRelWord m).f  =  0
```

* (⇐) `sqRelWord_selRefine_eq_one`: one γ₂-move on the `U`-handle slot, `(d,e) =
  rr·res·(−B, D)`, with `Λ`-membership `selLam_completion_move`.  Constructive.
* (⇒) `sqRelWord_selRefine_ne_one`: odd residue survives every refinement.  The only
  hypotheses on `m` are achievability of its two handle columns — the five lower rows are
  *not* consumed, so the obstruction also kills inadmissible tuples.

**The refinement-orbit picture.**  The class-two solution set fibers over its *level-one*
(abelian) data; each fiber is a torsor under the γ₂/γ₃-refinements; the relator residue is
constant mod `J` on each fiber (that is `sqRelWord_selRefine` again); and the selection bit is
a function of the level-one data alone.  A future construction should therefore **choose the
level-one data to zero the bit, then solve the linear system** — never search the fiber.

⚠ **Scope note.**  The formalized action refines the two handle slots by γ₂ and the two
exponent slots by γ₃.  Slot-0 γ₂-moves and joint `(z₁, z₂)`-exponent-γ₂ moves (compensated to
preserve rows 4–5) also exist; the same `Λ`-vs-`W` computation shows their increments even as
well (hand-checked, §3's derivation covers them), so the bit is invariant under the *full*
achievable action — but only the four-slot case is Lean-certified.  A fifth-slot extension is
mechanical if ever needed.

---

## 3.  The selection bit as an explicit 𝔽₂-form (derivation, unformalized)

Mod 2, write each dressing `a_i` by its `K̄`-components: `m_i` (Ū), `n_i` (V̄), `k_i` (t̄);
γ₂-parts drop out by §1.  Imposing the five lower rows mod 2 (`α₁ ≡ γ₁ ≡ 0` from rows d,e;
`α₂, γ₂ ≡ 0` from rows a,c) and expanding `sqU4Core + Σ u4Comm3` at the achievable values,
every term collapses onto three coefficients:

```text
bit  =  κ₁·( m₀n₁ + n₀m₁ + (1+m₃)(1+n₄) + n₃m₄ )
      + κ₂·( (1+m₃)k₄ + m₄k₃ + k₁m₀ )
      + κ₃·( n₃k₄ + (1+n₄)k₃ + k₁n₀ )          (mod 2)

κ₁ = (A+B)·T·D      κ₂ = A·Q + C·P      κ₃ = B·Q + D·P
```

(the `1+m₃`, `1+n₄` shifts are the undressed base letters `U`, `V` in their own slots).

**What the residue reads** (ticket goal 2's "which coordinates"): only
`(m₀, n₀, m₁, n₁, k₁, m₃, n₃, k₃, m₄, n₄, k₄)` — the σ- and x₀-slot abelian data, and the
handle-slot data.  The x₁-slot dressing and all `k₀`-, γ₂-, γ₃-parts are invisible.

**The κ-arithmetic.**  Under the adjacency parities:

* `κ₁ ≡ 0` at *every* uncleared type — the quadratic block never fires in this slice;
* at type `(0,1)`: `κ₂ ≡ 0` and `κ₃ ≡ B·(C/2) + D·(A/2)` — **not forced zero**; it is odd
  iff `B·(C/2) + D·(A/2)` is odd (mod-4 data of the weights!  `P, Q`'s parities are the
  *halves* of `BT − AS`, `SC − TD`: second-order data, the same "the first-order variations
  vanish" pattern as W46's Fox-derivative finding, one level up);
* type `(1,0)` mirrors with κ₂; type `(1,1)`: both can fire.

**Consequences, all verified in the instances:**

* the committed hom `(2,1,2,1,7,1)` has `κ₂ ≡ κ₃ ≡ 0`: the bit is *identically zero* on
  achievable admissible data — every legal dressing is refinable there, which is why W48's
  witness needed no correction;
* the κ₃-odd hom `(4,1,2,1,2,1)` (`B·(C/2) + D·(A/2) = 1·1 + 1·0 = 1`) has
  `bit = n₃k₄ + (1+n₄)k₃ + k₁n₀`: the **t-components are selected**.  `k₃ = 1` alone
  (dressing the `U`-handle slot by `t`) flips the bit — the Lean instance — and the form
  says exactly how to repair it *at level one*: flip `n₄` (dress the `V`-slot by `V`), or
  pair it with `k₄`, etc.  The selection couples the `t̄`-component of one handle dressing to
  the `V̄`-component of the other: a *rule*, not a search;
* the forced-alone tuple (`all zero`) has bit `κ₁·1 = 0` in this slice: the slice never
  obstructs the forced dressing — consistent with the sweep, whose 60/63 forced-alone
  failures at class 3 are *universal*-quotient facts (σ-slot!), not slice facts.

---

## 4.  What the slice provably cannot see, and the wider-slice design

**The σ-slot forcing is invisible — now a theorem.**  The sweep: universal level-one
survivors have `a₀ = a₁ = U^{−s}V^{t}` mod squares (σ-slot forced, *new*).  The slice: both
`a₀ = 1` (§4's committed witness) and `a₀ = a₁ = U⁻¹` (`sqRelWord_selHom_sqArbFrame_sigma`)
kill the relator at **every** hom of the family.  The bit-form explains it: σ-data enters only
through `κ₂k₁m₀ + κ₃k₁n₀`, and the forced branch has `k₁ = 0`.  So no refinement of the
current marking design can decide the σ-slot; blindness is structural.

**Design of a σ-sensitive gate (W51 candidate).**  Give the σ- and x₀-slots nonzero `a`- and
`c`-weights: `σ ↦ ⟨A₀, 1, C₀, ·, ·, ·⟩`, `x₀ ↦ ⟨A₁, 0, C₁, ·, ·, ·⟩`.  Costs and constraints,
from the committed closed forms:

1. the pivot `w = σ·x₀^{−c₀}` now has abelian image `(A₀ − c₀A₁, 1, C₀ − c₀C₁)` — the
   `sqPivotExp`-dependence returns.  Mitigation: choose `A₁, C₁ ∈ 4·ℤ/8` so `c₀·A₁` depends
   only on `c₀ mod 2` (`c₀` is a unit, so `c₀A₁ = A₁ mod 8` when `A₁ ∈ 4ℤ`); or run the gate
   at both values of the relevant residue of `c₀` — the committed `sqPivotExp` facts
   (`Certificate.lean`) pin it mod small powers;
2. `zpowZtwo`-linearity of the pivot (`SqU4.zpowZtwo_of_flat`) needs the three flatness
   conditions on the new pivot image — `a·b = b·c = 0` forces `A₀ − c₀A₁ ≡ 0` and
   `C₀ − c₀C₁ ≡ 0` mod the annihilator of 1... i.e. the *honest* wider slice must either drop
   the `b = ν′`-column design or accept non-flat pivots and carry the binomial corrections.
   The second is the real work item;
3. the realizability system acquires the analogues of `hd`, `he` **plus** conditions coupling
   `(A₀, C₀, A₁, C₁)` to the handle weights.  The sweep's marking-dependent `im δ` says these
   will not assemble into one clean parity — expect a small family of gates rather than one.

Payoff if built: the κ₂/κ₃-analogues acquire terms reading `m₀, n₀, k₀` *without* the `k₁`
factor, and the σ-forcing becomes a slice statement of exactly the
`sqArbFrame_x0_dressing_forced` kind, one slot over — the sweep's #2 recommended commitment.

---

## 5.  The lift design: stage `k`, and where pro-2 input must enter (ticket goal 3)

**The stage-`k` pattern, as now understood.**

* *Class 2* (W46/W47): first-order variations vanish (all Fox derivatives in the augmentation
  ideal); the balance is second-order; one slot forced (x₀; σ too, but invisibly to the
  class-2 slice), realizability parity `ℤ/4`, `2·χ` trick mandatory.
* *Class 3* (W48–W50): handle-slot γ₂-dressings act **linearly** (`u4Comm3`'s bilinear
  terms) — the first-order layer is alive but its image has a mod-2 cokernel; the selection
  is the cokernel bit; `2·χ` is forbidden, the gate needs an odd free character, permitted
  exactly on uncleared handles; `ℤ/4` already fires, `ℤ/8` sharpens.
* *Class `k` conjecture*: the dressing action on the class-`k` residue is affine-linear in
  the `γ_{k−1}`-components with abelian coefficients; its image is the pairing lattice of the
  marking's `γ_{k−1}`-image against the achievable columns; the sweep measures its corank as
  **exactly `d + 1 = sqRank h + 1` at every level and marking** (`w50-depth-sweep.md` §6.3).
  The `d + 1` unreachable functionals are marking-dependent — there is no universal
  obstruction space — and the relator's defect lands in the image every time.

**What replaces `U₄`.**  `U₅(R)` (ten coordinates) is the mechanical next test group; the
class-4 analogue of the middle-column asymmetry is the pair of *interior* columns, and the
adjacency-parity pattern should become one parity per adjacent column pair (three parities),
none on non-adjacent pairs.  But the sweep's uniform-corank finding suggests the better
formalization target is not another gate layer: it is the **containment identity**

> at every selected marking and level, the relator's layer defect lies in the image of the
> dressing map δ,

whose slice form this wave proved constructively (obstruction + completion).  A general proof
of the containment — even just at class 3 for *all* markings over `ℤ/2^c` — would be the
first genuinely level-uniform positive statement, and §1–§2's machinery (the translation
identity plus the pairing lattice) is exactly its skeleton.

**Where pro-2 input must genuinely enter.**  The discrete group provably fails
marking-transitivity (SL₂(ℤ)-invariant on the ν′-rows), and every finite-2-quotient argument
applies verbatim to the discrete group; the sweep sharpens *where* the divergence lives:

* it is **not** in the row orbit: λ-preserving automorphisms act transitively on selected
  ν′-rows at class 3/4/5 — the discrete SL₂-invariant leaves no shadow on rows in any
  measured nilpotent quotient;
* it **is** in the slot decomposition: handle-only dressings (= the discrete/SL₂ regime, and
  every refuted family in some register) are infeasible at almost all markings; the pro-2
  escape is an irreducibly **joint core+handle move**, with the σ- and x₀-slots carrying the
  same forced `U^{−s}V^{t}` and the corrections spread across all five slots;
* consequently no slot-by-slot induction can close the residual: the stage-`k` step must
  solve core and handle coordinates simultaneously, and the "one slot forced, rest free"
  narrative of class 2 was an artefact of the smallest layer.  The class the discrete group
  cannot follow is the *joint* one: `SL₂(ℤ) → SL₂(ℤ₂)` is not surjective on the relevant
  congruence data at level `2^c` for `c ≥ 3` (index grows), and the sweep's per-level
  affine-coset dimensions (17/66/192) quantify the room the pro-2 side keeps.

**Recommended W51 tickets**, in value order:

1. formalize the containment at class 3 over `ℤ/4` for the whole marking binder (`ν′` rows
   `(t, s)` mod 4, all weights): the slice machinery generalizes — the statement is
   `∃` level-one data with bit 0, and §3's form makes it finite;
2. the σ-sensitive gate of §4 (costed there);
3. the fifth-slot extension of `selRefine` (mechanical, only if 1 needs it).

---

## 6.  Corrections and errata

* **`GradedThree` §6's `u4WitBad` gloss.**  The docstring says "both class-two defects stay
  in `2·ℤ/8`, so class two admits it".  True as stated about the *defects*, but the tuple
  also fails the two abelian rows (`−4·(m 1).a + 2·(m 2).a = 2 ≠ 0`): dressing the x₁-slot
  by `V` alone is not class-≤2-admissible, only defect-admissible.  The clean
  class-two-admissible/class-three-dead witnesses are this wave's `selTW2` (odd residue,
  five lower rows exactly zero) and its frame-level source `selDressT`.  No committed
  *theorem* is affected — the gloss is prose.  Owner of `GradedThree.lean` may want a
  one-line docstring amendment.
* **The ticket's surjectivity question** presupposed the linear part might be onto; it never
  is on the uncleared locus.  As the brief requested, the cokernel functional (reduction
  mod 2) is exhibited and is the selection invariant; the sweep's containment reframing is
  adopted.
* `nuLam` rows used here: `λ(σ, x₀, x₁, u_j, v_j) = (c₀, 1, 2, 0, 0)`; `t = x₁(x₀x₀)⁻¹` is
  λ- and ν′-trivial — the committed `nuLam_selTee`, `nu_selTee` are the citable forms.
