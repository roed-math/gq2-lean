# R7 — Route L lead design: `D_R`, Demushkin/orientation/marked skeletons

Ticket R7 of `roe-verification-plan.md` (§3 Route L, §4 P2). 2026-07-24, branch `roe`.
Statement-design memo for the P2 fills (R8–R15). Source of truth:
`paper/roe-presentation-verification.tex` §3; independent re-derivation + numerics:
`docs/orchestration/roe-r2-spike.md`.

## Delivered files

| File | Status | Contents |
|---|---|---|
| `GQ2/Roe/DRPresentation.lean` | **complete, sorry-free** | `drWord`, `map_drWord`, `drWord_comm`; `drRelator`, `DRFull`, `DR`, generators `drFullS/X/Y`, `drS/X/Y`; `drFull_relation`, `dr_relation`(+`_expanded`), `isProP_DR`; universal property `drLiftHom` + `drLiftHom_S/X/Y`; `decide` stress tests `drWord_zmod8(_y1)`, `drWord_d4` |
| `GQ2/Roe/CrossedDerivation.lean` | skeleton (6 sorries) | **proved**: `conjP_wordLift`, `commP_wordLift` ⟦eq:commderivative⟧, `not_isLabuteOrientationDatum_one`; coefficient defs `cxR`/`csR`/`cyR`; **sorried**: `drWord_wordLift`, `isLabuteOrientationDatum_iff`, `_of_root`, `_solution`, `_unique`, `isLabuteOrientation_ext`; defs `IsLabuteOrientationDatum`, `IsLabuteOrientation` |
| `GQ2/Roe/DRDemushkin.lean` | skeleton (14 sorries) | **proved/def-complete**: trivial-action instances + `drSmul_trivial`, `isProP_two_multZMod2_roe`, `drCharM` + value simps, `drZ1`, `drH1`, `drSStar/XStar/YStar`, `finite_H1_DR`, `demushkinRank_DR` (both modulo the sorried cards); **sorried**: `drH1_bijective`, `card_H1_DR`, `card_H2_DR`, nine Gram entries `drCup_{ss,sx,sy,xs,xx,xy,ys,yx,yy}`, `isDemushkin_DR` (only the two `nondegen` fields), `demushkinQ_DR` |
| `GQ2/Roe/MarkedPro2.lean` | skeleton (2 sorries) | **proved/def-complete**: `nuR` + `nuR_drS/X/Y`; `BLabHypothesis` (in `section Draft`, b9a precedent); **sorried**: `nuR_surjective`, `markedPro2_R` |
| `GQ2.lean` | 4 import lines appended under the `-- Roe-candidate verification` comment (swept into R5's commit 30feeb6 while R7 was in flight; this commit supplies the four files those imports reference) | |

Full `lake build` green (sorry warnings only, all in the three skeleton files).

## Keystone design decision: `drWord`

The relator's *shape* `drWord s x y = (x^s)⁻¹·(x³)⁻¹·y²·[y,y^s]` is a computable word defined
over any group, with unconditional naturality `map_drWord` (no `ω₂`). One definition is
evaluated in every regime: the relator (`drRelator := drWord (of 0) (of 1) (of 2)`), the
relation lemmas (one-line `map_drWord` transports), finite quotients (`decide` stress tests;
R12/R13 witnesses), the abelianization (`drWord_comm : drWord s x y = (x⁴)⁻¹y²` — the
⟦eq:BR⟧ exponents), the `𝔽₂`-characters, `ν_R`, `χ_R` (via `drLiftHom`'s `hrel` in `drWord`
form), and the χ-twisted derivation calculus (`drWord` at `WordLift ℤ₂ ℤ₂ˣ` lifts **is**
`(D(r₂), χ(r₂))`). Fills should never re-expand the word by hand.

`drLiftHom` (the `d0LiftHom` clone, placed in the presentation file because every character in
P2 consumes it) turns a triple killing `drWord` in a pro-2 group into a continuous hom out of
`DR`, with `@[simp]` generator values.

## R8 — abelianization bookkeeping (`BDecomposition` clone)

New file suggestion `GQ2/Roe/BRDecomposition.lean`. Target statements, mirroring
`BDecomposition` (`GQ2/SectionThree.lean:422`) with coordinates `(t, s̄, x̄)`, `t = ȳ − 2x̄`
⟦eq:tR⟧, torsion first ⟦eq:BRsplit⟧:

```lean
structure BRDecomposition where
  e : ContinuousMulEquiv (topAbelianization (DR : Type))
        (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
  map_t : e (abMk (drY * (drX ^ 2)⁻¹)) = Multiplicative.ofAdd (1, 0, 0)
  map_s : e (abMk drS) = Multiplicative.ofAdd (0, 1, 0)
  map_x : e (abMk drX) = Multiplicative.ofAdd (0, 0, 1)
theorem br_decomposition : Nonempty BRDecomposition
```

Consequences to prove alongside (all consumed downstream): `ȳ`-row
`e (abMk drY) = ofAdd (1, 0, 2)` (forced: `ȳ = t + 2x̄`); the defining relation
`−4x̄ + 2ȳ = 0` (from `dr_relation` + `drWord_comm` pushed through `abMk`); **topological
generation** of `DR` by `{drS, drX, drY}` (pushforward of generation of the free profinite
group through the two quotient maps — this is the lemma `drH1_bijective`-surjectivity,
`isLabuteOrientation_ext`, and R15's hom-extensionality all cite; recommend proving it against
`DR` directly, not only the abelianization); pro-2 instances for `topAbelianization (DR:Type)`
cloned from the `local instance` block at `GQ2/SectionThree.lean:112–160` (note the warning
there: direct `local instance`, do **not** wrap the `CommGroup` in a `def`); a
`drab_hom_ext` analogue of `d0ab_hom_ext` (hom out of `B_R` determined by the three generator
values); and the torsion count feeding `demushkinQ_DR = 2` (`DRDemushkin.lean`, sorried
there, ⟦eq:BR⟧–⟦eq:BRsplit⟧). Proof pattern for the torsion count:
`demushkinQ_cyclicTwo` (`GQ2/Demushkin.lean:461`) shows the `Nat.card`-of-torsion bookkeeping;
transport along `BRDecomposition.e` and count torsion of `ZMod 2 × ℤ₂ × ℤ₂` (= the `ZMod 2`
factor; `ℤ₂` is torsion-free).

The construction route for `e` mirrors how `b_decomposition` was proved for `D₀` (coordinate
homs out of the abelianization via `abLiftG` + `drLiftHom` at targets `Multiplicative ℤ₂` /
`Multiplicative (ZMod 2)`, then bijectivity via an inverse hom; see `sHom`/`yHom`/`tHom`,
`GQ2/SectionThree.lean:543–570`). For the `t`-coordinate the relator check mod 2 is
`drWord_comm` + squares-vanish, exactly as in `drCharM`.

## R9 — CrossedDerivation fills

Owns the six sorries of `GQ2/Roe/CrossedDerivation.lean`. In dependency order:

1. `drWord_wordLift` (the master evaluation). `ext`; the `.g`-component is `drWord_comm` in
   `ℤ₂ˣ`. For `.u`: rewrite `drWord` and evaluate factor-by-factor using the **proved**
   `conjP_wordLift`, `commP_wordLift`, plus `WordLift.mul_u/inv_u/pow_u` and
   `Units.smul_def, smul_eq_mul, Units.val_mul`; finish with `linear_combination` over the
   unit-cancellation facts `Units.inv_mul`/`Units.mul_inv` (the pattern that closed
   `commP_wordLift`; plain `ring` cannot cancel `↑(u⁻¹) * ↑u`). The raw coefficients were
   re-derived independently in the spike (§2.1) and match `csR`/`cxR`/`cyR` as defined:
   raw `Cs = S⁻¹(−X⁻¹(X−1) + X⁻⁴(Y−1)²)`, raw `Cy = X⁻⁴((1+Y) + (Y−1)(S⁻¹−1))`; the note's
   (3.11)/(3.12) are these after `Y² = X⁴` (docstrings flag this).
2. `isLabuteOrientationDatum_iff`: rewrite by (1). Forward: instantiate `(Ds,Dx,Dy)` at
   `(1,0,0),(0,1,0),(0,0,1)` for the coefficients and read the `.g`-component (via
   `congrArg WordLift.g` and `WordLift.one_g`; `Units.ext` for `Y² = X⁴` from
   `(X⁴)⁻¹Y² = 1`). Backward: substitute and `ring_nf`/`simp`.
3. `isLabuteOrientationDatum_of_root` / `_solution` / `_unique`: pure `ℤ₂ˣ`/`ℤ₂` algebra
   through (2); the cleared-denominator identities to prove are (spike §2.1):
   `Cs·S·X⁴ = X³+2X²+1` on the branch `Y = −X²`, and `Cy·X⁷ = (X+1)(X³+2X²+1)` after
   substituting `S`; branch `Y = X²` dies on `(X−1)(X²−X−1) = 0` (second factor odd — R10's
   `isUnit_sq_sub_self_sub_one_of_odd` is exactly this fact) then `Cy = 2 ≠ 0`.
   `linear_combination` with multipliers built from `rootX_spec`/`Sval_spec` is the right
   tool; work with coerced values and `Units.ext` at the end.
4. `isLabuteOrientation_ext`: datum-uniqueness (3) + R8's generation lemma + the density
   argument (`MonoidHom` agreeing on a topologically generating set, both continuous —
   the `multPadicIntHom_ext`/`d0ab_hom_ext` proof shape).

## R10 — consumption map (LANDED, reconcile names)

R10 committed `GQ2/Roe/OrientationRoot.lean` (1f4b265) *while R7 was in flight*, working at
the `ℤ_[2]`-element level with `IsUnit` witnesses. My skeleton statements deliberately consume
the root facts as **hypothesis binders on units**, so no edit is needed; R9/R11 instantiate:

| CrossedDerivation hypothesis (on `X S Y : ℤ_[2]ˣ`) | discharged by (OrientationRoot) |
|---|---|
| `X := rootX_isUnit.unit`, `(↑X : ℤ_[2]) = rootX` | `rootX_isUnit`, `IsUnit.unit_spec` |
| `rootX_spec : ↑X^3 + 2↑X^2 + 1 = 0` | `rootX_isRoot` |
| `Sval_spec : ↑S * (↑X^2 + ↑X + 1) = −↑X^3` | `Sval_mul_denom` (S := unit of `Sval`; `Sval` is a unit by `Sval_toZModPow_four = 13` — if R10 has no `Sval_isUnit`, derive via `isUnit_of_toZModPow_one_eq_one`) |
| `hY : ↑Y = −↑X^2` | `Yval_eq` (Y := unit of `Yval`; unit-ness from `Yval_toZModPow_four = 7`) |
| `rootX_unique : ∀ a b : ℤ₂ˣ, root → root → a = b` | `rootX_unique` (both coerced roots equal `rootX`, then `Units.ext`) |
| (R11) exact level `↑X − 1 = 4·(unit)` | `rootX_sub_one_eq` (∃-form; matches `zpowZtwo_injective_of_exact_level`'s input after choice) |
| (R15 numerics) `X ≡ 5, S ≡ 13 (mod 16)` | `rootX_toZModPow_four`, `Sval_toZModPow_four` |

Residual R10-side nice-to-haves (tiny; R11 can add them in its own file if absent):
`Sval_isUnit`, `Yval_isUnit`, and unit-bundled `rootXU/SvalU/YvalU : ℤ_[2]ˣ` abbreviations.

## R11 — `χ_R` and `im χ_R = {±1}×(1+4ℤ₂)`

New file suggestion `GQ2/Roe/ChiR.lean` (imports `CrossedDerivation` + `OrientationRoot`).

1. `chiR : ContinuousMonoidHom (DR : Type) ℤ_[2]ˣ :=
   drLiftHom isProP_two_unitsPadicInt ![SvalU, rootXU, YvalU] h` where `h` unfolds
   `drWord_comm` in the abelian `ℤ₂ˣ` and reduces to `Y² = X⁴` + the coefficient identities —
   or, cleaner, via `IsLabuteOrientationDatum → drWord-value = 1` specialized at
   `Ds = Dx = Dy = 0`… note the base-component of `drWord_wordLift` gives exactly
   `(X⁴)⁻¹Y² = 1`. (`isProP_two_unitsPadicInt` : `GQ2/ZtwoPowering.lean:559`; the
   `TotallyDisconnectedSpace ℤ₂ˣ` instances live there too.)
2. `isLabuteOrientation_chiR : IsLabuteOrientation chiR` — from
   `isLabuteOrientationDatum_of_root` + the value simps (`drLiftHom_S/X/Y`).
3. `chiR_surjective : Function.Surjective chiR` — **the image statement**. Note the f = 2
   accident: `{±1} × (1 + 4ℤ₂) = ℤ₂ˣ` (all units are ≡ ±1 mod 4), so "image" = surjectivity,
   the same encoding as B3c's `surjective_chiTwo`. Proof sketch: `χ_R(t̄) = Y·X⁻² = −1`
   ⟦prop:orientation, last display⟧ and `χ_R(x) = X` with exact level 2
   (`rootX_sub_one_eq`), so the closed image contains `−1` and the closure of `X^ℤ`; by
   `zpowZtwo` (`zpowZtwo_zpowZtwo`, continuity, and `zpowZtwo_injective_of_exact_level`-style
   level bookkeeping — `GQ2/ZtwoPowering.lean:600–680`) that closure is `1 + 4ℤ₂`; together
   with `−1` they generate `ℤ₂ˣ` (mod-8 decomposition `mod8_sq`, `GQ2/SectionThree.lean:869`,
   is a convenient finisher: any unit is `±1·(1+4ℤ₂)-element` times a square, and squares lie
   in `1+4ℤ₂`… simplest closed-form: `u ∈ ℤ₂ˣ` ⟹ `±u ∈ 1+4ℤ₂` by mod-4 case split).
   The image of a continuous hom from a compact group is closed — same fact `nuR_surjective`
   uses.

## R12/R13 — Demushkin fills

R12 (`drH1_bijective`, `card_H1_DR`): H¹ ≅ continuous characters (trivial action;
`ContCoh.H1equivZ1OfTrivial` + the wrapper-free evaluation pattern of
`GQ2/Demushkin.lean:275–301`); characters are determined by generator values (R8 generation)
and every triple is realized (`drCharM`) with `drCharM_drS/X/Y` giving injectivity after
evaluation. `card_H1_DR` then transports `Nat.card (Fin 3 → ZMod 2) = 8`.

R13 (`card_H2_DR` + nine `drCup_*`): the board maps R13 to `GQ2/Roe/DRH2.lean`; the
*statements* live in `DRDemushkin.lean` (this ticket's file assignment) — R13 should put its
witness machinery in `DRH2.lean` and fill the `DRDemushkin.lean` sorries by citing it, or
inline-fill if small. Routes per plan §3 Route L step 2: upper bound `dim H² ≤ 1` from the
one-relator presentation via the `WordCoh2` bridge; lower bound from any nonzero Gram entry.
For the Gram entries the `𝔽₂`-cochain evaluation route of `CardH2GammaA.lean` (concrete
central-extension witnesses over small 2-group quotients, everything `decide`d) is the
house pattern; note `drWord_d4` already exhibits `D₄` as a quotient (the `s ↦ r 2, x ↦ r 1,
y ↦ sr 0` marking), and `D₄`-covers detect `s*∪x*`. **Heed the R2-spike pitfall (docstring in
`DRDemushkin.lean`)**: the matrix is the Gram of the symmetric bilinear cup form with
Bockstein diagonal — do not route through `QuadraticForm`/Arf. `isDemushkin_DR`'s two
`nondegen` fields follow from the Gram entries + `drH1_bijective` coordinates (matrix
`[[0,1,0],[1,0,0],[0,0,1]]` is invertible: a nonzero `(a,b,c)` cups nontrivially with `x*`,
`s*`, or `y*` according to the first nonzero of `(a,b,c)`).
`demushkinQ_DR` fills from R8 (see above).

## R14 — B-Lab flip (owner-gated)

The draft statement for owner review is `GQ2/Roe/MarkedPro2.lean`, `section Draft`,
`def BLabHypothesis : Prop`, verbatim:

```lean
def BLabHypothesis : Prop :=
  IsDemushkin 2 (DR : Type) →
    demushkinRank 2 (DR : Type) = 3 →
      demushkinQ (DR : Type) = 2 →
        (∃ χ : (DR : Type) →* ℤ_[2]ˣ,
          Continuous χ ∧ IsLabuteOrientation χ ∧ Function.Surjective χ) →
          Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type))
```

Citation: J. P. Labute, *Classification of Demushkin Groups*, Canad. J. Math. **19** (1967),
106–132 — Théorème 4 (canonical orientation: existence/uniqueness via descent of crossed
derivations, and the `q = 2` image classification) + Théorème 8 (classification by
`(n, q, im χ)`; odd rank `n = 3`, `q = 2`, `f = 2` normal form = `D₀`). Note Cor. 3.4
⟦cor:abstractD0⟧.

Design choices flagged for the owner (statement shape, decided in this draft):
1. **Specialized to `G := D_R`**, not abstract `G`. Rationale: the descent-characterized
   orientation (`IsLabuteOrientation`) is defined through `D_R`'s presentation; an abstract-`G`
   statement would need either (a) presentation data bundled into the hypothesis (heavy, and
   Labute's theorem is presentation-independent, so the bundling is artificial), or (b) the
   abstract dualizing-module characterization — exactly the deferred route (i) of
   `GQ2/Orientation.lean`, i.e. the multi-week fallback of plan §3. The single-instance form
   matches the plan's wording and the B3c precedent ("axiomatizes the G_ℚ₂(2) package only").
   If the owner prefers abstract `G`, the clean shape is over a bundled
   `(G, gens : Fin 3 → G, relator-kill, generation)` with `IsLabuteOrientationDatum` at the
   `χ`-values of `gens` — the CrossedDerivation vocabulary supports it without change, but
   then B-Lab quantifies over presented pro-2 groups with *this particular relator*, which is
   no more general in practice.
2. Image invariant encoded as `Function.Surjective χ` (the `f = 2` case:
   `{±1}×(1+4ℤ₂)` **is** `ℤ₂ˣ`), matching `DyadicOrientation.surjective_chiTwo`.
3. Hypothesis-arrows form (antecedents will be theorems): consuming code is
   `hBLab isDemushkin_DR demushkinRank_DR demushkinQ_DR ⟨chiR, chiR_continuous,
   isLabuteOrientation_chiR, chiR_surjective⟩`.

R14 execution: quarantine as `axiom` in `GQ2/Foundations/Axioms.lean` **only after owner
sign-off**, with the b9a T5 flip checklist (AxiomLedger entry, `check_axioms.sh` expected-set,
docs/literature-axioms.md section, docstring carrying the convention block above); then
replace `BLabHypothesis` consumers by the axiom or keep the `Prop` + a one-line
`theorem bLab : BLabHypothesis := fun _ _ _ _ => (axiom …)`-style discharge (recommended:
keep `BLabHypothesis` as the interface and discharge it once, so the marked statement's
hypothesis surface never changes).

## R15 — marked assembly (`markedPro2_R`, `nuR_surjective`)

Fills the two `MarkedPro2.lean` sorries. Route (note §3.3 proof, ⟦prop:markedpro2⟧):

1. Get `f : D_R ≅ D₀` from `BLabHypothesis` (antecedents: R11–R13 + `demushkinQ_DR`).
2. Unique `b` with `S = X^b`: `zpowZtwo` on `ℤ₂ˣ` (`zpowZtwo_bijective` at the exact-level-2
   generator `X`; injectivity side `zpowZtwo_injective_of_exact_level` with
   `rootX_sub_one_eq`). Unique `u` with `η^u = X`, `η = (−3)⁻¹`
   (`zpowZtwo_injective_neg_three_inv`, `GQ2/ZtwoPowering.lean:679`;
   `norm_inv_neg_three_sub_one`-adjacent facts are already in-tree). Shear `k = s̄ − b·x̄` in
   `B_R` (R8 coordinates); `φ_ab : B_R ≅ D₀^{ab}` by `t ↦ t₀, k ↦ S̄₀, x̄ ↦ u·Ȳ₀`
   ⟦eq:desiredab⟧, ν- and χ-compatible by construction (χ-rows `(−1, 1, X)` vs `(−1, 1, η)`).
3. `φ_ab ∘ f_ab⁻¹` is a `χ₀`-preserving automorphism of `D₀^{ab}` (functoriality of the
   descent-characterized orientation across an iso — for the formal proof, phrase as: both
   `χ_R` and `χ₀ ∘ f` are Labute orientations of `D_R`, so `isLabuteOrientation_ext` equates
   them; `χ₀`'s datum property for `D₀` is the same computation at `(A,S,Y)`-values
   `(−1, 1, η)` — a small D₀-side lemma R15 will need, provable by the same
   `drWord`-style evaluation on `d0Relator`, or imported from the B3c bundle's value facts).
   Correct by `prop_3_8_classification` + `prop_3_8_lift`
   (`GQ2/AnabelianBridge/Classification.lean:342`, `Construction.lean:1089` — D₀-side, as-is).
4. Compose with B3c/`prop_1_1` (`GQ2/PropOneOneAssembly.lean:298`) and the
   `prop_3_10_local_marked` `ι`-bridge pattern (`GQ2/SectionThreeMarked.lean:60`,
   `ztwoEquivPadic` machinery in `GQ2/ZtwoPowering.lean:362`) to land the exact statement.
   `nuR_surjective` = the `nuTwo_surjective` argument (`GQ2/Prop32.lean`) verbatim.

Cross-check numerics (R2 spike §2.4, mod 2²⁰): `b ≡ 91367` (`b ≡ 3 mod 4`),
`u ≡ 898793` (`u ≡ 1 mod 4`); mod-2 Gram-isometry seed `s̄ ↦ S̄+Ȳ, x̄ ↦ Ȳ, ȳ ↦ Ā`
(spike §2.7) — useful sanity targets, not needed by the proofs.

## Deviations / coordination notes

* `ν_R` is built through `drLiftHom` (= the `maxProPHomEquiv` universal property packaged
  once) rather than a literal clone of `nuTwo`'s two-step `presentationLift`/`quotientLift`;
  same construction, factored. Values and target (`Ztwo`, `ztwoOne`) match `nuTwo` exactly.
* `csR`/`cyR` are the **raw** evaluation coefficients (statement-faithful to the word
  calculus); the note's (3.11)/(3.12) forms are recovered under ⟦eq:charrelation⟧ — flagged
  in docstrings. `cxR` is the note's (3.10) verbatim.
* Demushkin statements all live in `GQ2/Roe/DRDemushkin.lean` (per the R7 file assignment);
  the board's R13 row maps to `DRH2.lean` — R13 should treat `DRDemushkin.lean`'s `H²`/Gram
  sorries as its fill surface and put machinery in its own file (single-writer per file
  preserved: R12 owns the `H¹` sorries, R13 the `H²`/Gram sorries, in disjoint declaration
  sets; if simultaneous dispatch is planned, orchestrator should serialize or split the file).
* `isLabuteOrientationDatum_unique`/`_ext` carry the root-uniqueness fact as a hypothesis
  binder (`rootX_unique`, pairwise-units form) — R10 landed mid-ticket with `ℤ_[2]`-level
  `rootX_unique {z} : z³+2z²+1 = 0 → z = rootX`; the reconciliation is a two-line
  instantiation (see the R10 table). No file edit needed; R9/R11 discharge at use sites.
* `GQ2.lean` timing: the four R7 import lines were appended in the shared working tree and
  were swept into R5's commit (30feeb6) before this commit landed — so 30feeb6 alone imports
  four then-untracked modules; this commit adds the files and restores a self-consistent
  tree. No further `GQ2.lean` edit is staged here (R21's `FoxBasic`/`WildRow` lines remain
  that worker's pending edit).
* The Γ_R-side half of ⟦lem:pro2word⟧ (`maxProPQuotient 2 GammaR ≅ DR`, generator-matching,
  the `prop_3_10_gammaA` analogue) is **not** in these skeletons: it needs R3's `GammaR`
  (landed mid-ticket) and belongs with the boundary assembly (R15 or a small dedicated
  ticket; the proof is the τ-dies + `ω₂`-collapse word computation of note Lemma 3.1
  ⟦lem:pro2word⟧ against `maxProPMk_tameTau` (`GQ2/TameTwoQuotient.lean:63`) and
  `zpowZtwo` laws).
