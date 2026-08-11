/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Hessian
import GQ2.GaussZ.FinalGammaA

/-!
# Proposition 6.1: the `r_R` base word expansion and its Gauss signs  (⟦prop:quadratic⟧, ⟦cor:gauss⟧)

The `Γ_R` counterpart of the `Γ_A` quadratic seam (`GQ2.SectionSix` §6.2 + `GQ2.GaussZ.FinalGammaA`):
the **word-quadratic layer** that the full `GaussZ/FinalGammaR` package (ticket R31) instantiates.
It sits one class-two degree above R24's mixed Hessian (`GQ2.Roe.Hessian`): where R24 traces the
Roe wild word `r_R = (x₀^σ)⁻¹ · aR · x₁² · cR` to the **linear** central coordinate
`λ(d)` / `λ((1+U+U⁻¹)d)`, this file traces it to the **quadratic** base determinant class
`Q_R⁰(d)` of the note's Proposition 6.1 ⟦prop:quadratic⟧, ⟦eq:QR⟧:

  `Q_R⁰(d) = q(d)`                    if `T = 1`   (unramified/split, `U = 1`),
  `Q_R⁰(d) = q(d) + b_q(d, U⁻¹d)`     if `V^T = 0` (ramified),   `U = σ₂ = Marking.sigma2`.

The two summands mirror R24's ledger **1:1** (the note's "R24's ledger gives both terms directly"):
the diagonal `q(d)` is the quadratic shadow of `heisMarking_x1_sq_z` (`x₁²`), and the symplectic
`b_q(d, U⁻¹d) = polar q d (U⁻¹•d)` is the quadratic shadow of the `heisMarking_cR_z` entry
`λ(U⁻¹d) + λ(Ud)` (`cR = [x₁, x₁^{σ₂}]`) — `b_q(·, U⁻¹·)`'s polar recovers exactly that symmetric
pair.  We take `Q_R⁰ := QZeroR q U` as this two-term form (`QZeroR_apply`, definitional ⟦eq:QR⟧).

The main content (⟦prop:quadratic⟧, the note's "differs only by the wild-coordinate renaming `c ↦ d`"):

* **the base word expansion** identifies `QZeroR` with the shape the `Γ_A` side feeds Prop 6.9:
  `QZeroR_split` (`= q`, split, via the collapse `b_q(d,d) = 0`) and `QZeroR_eq_qDouble`
  (`= qDouble q U`, ramified, via `polar_smul_inv_eq`'s `b_q(d, U⁻¹d) = b_q(d, Ud)`) — so **all** of
  the `Γ_A` Arf/Gauss computations (`SectionSix.lemma_6_6`/`lemma_6_8`/`prop_6_9_*`,
  `GaussZ.FinalGammaA.Action`) apply to `Q_R⁰` unchanged;
* **the polar form** ⟦eq:polar⟧ `b_R(d,d') = b_q(d, (1+U+U⁻¹)d')` (`polar_QZeroR`) whose operator
  `1 + U + U⁻¹` is R24's `pairingR_operator_injective` — giving perfectness of the ramified base
  form (`QZeroR_nonsingular_ramified`, "Both operators are invertible.");
* **the Gauss signs** ⟦cor:gauss⟧ `#(Q_R⁰)⁻¹(0) = 2^{n-1} ∓ 2^{n/2-1}`: `QZeroR_zeroCount_unramified`
  (`−`, via `prop_6_9_unramified`) and `QZeroR_zeroCount_ramified` (`+`, via `prop_6_9_ramified`
  through `lemma_6_6`/`lemma_6_8`), with the ∓2^m finales `QZeroR_finsum_sign_*` the residue layer
  consumes.

Scope: this is the **presentation-dependent** word-level layer.  The heavy quadratic-Heisenberg word
evaluation (`κ⁰`/`QZero`, `GaussZ/RelatorGammaA`) and the full `Γ_R` residue assembly are ticket
**R31** (`GaussZ/FinalGammaR`), which instantiates the identifications here to reuse the generic
`GaussZ.FinalGammaA.Action` count lemmas verbatim (they are `Γ`-agnostic — abstract `q`/`qDouble q U`).
-/

namespace GQ2

namespace FoxH

open QuadraticFp2
open SectionEight.AffineTLift

/-! ### The Roe base determinant form and the base word expansion (⟦prop:quadratic⟧, ⟦eq:QR⟧)

The evaluated base word value on the normalized `x₁`-supported class `(0,0,0,d)` (⟦lem:normalforms⟧,
`x1Supported`), in the two-term ⟦eq:QR⟧ shape.  The wild coordinate is renamed `c ↦ d` from the
`Γ_A` `x₀`-supported gauge (the only difference, per the note). -/

section BaseForm

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **The Roe base determinant form** `Q_R⁰` (⟦eq:QR⟧, ramified two-term shape): on the normalized
`x₁`-supported class, the diagonal `q(d)` (from `x₁²`, R24's `heisMarking_x1_sq_z`) plus the
symplectic `b_q(d, U⁻¹d) = polar q d (U⁻¹•d)` (from `cR = [x₁, x₁^{σ₂}]`, R24's `heisMarking_cR_z`),
`U = σ₂`.  This is the exact `Γ_A` base form `κ_q⁰` (`SectionSix` §6.2) with the wild coordinate
renamed `c ↦ d`. -/
def QZeroR (q : V → ZMod 2) (U : C) (d : V) : ZMod 2 := q d + polar q d (U⁻¹ • d)

/-- **⟦eq:QR⟧ made explicit**: the base word value is the two-term sum `q(d) + b_q(d, U⁻¹d)`. -/
theorem QZeroR_apply (q : V → ZMod 2) (U : C) (d : V) :
    QZeroR q U d = q d + polar q d (U⁻¹ • d) := rfl

/-- **⟦prop:quadratic⟧, split case** (⟦eq:QR⟧, `T = 1`): when `U = σ₂` acts trivially the base form
collapses to the honest diagonal `Q_R⁰(d) = q(d)`.  The symplectic term dies by `b_q(d,d) = 0`
(`polar_self`, the alternating law in char 2) — the note's "these two commutator terms cancel", one
class-two degree up from R24's `heisMarking_cR_z_split_cancels`.  `hU` is the split `σ₂`-triviality
(the `Γ_A` `powOmega2_smul_eq_of_gen`, discharged by R31 as for R24's split pairing). -/
theorem QZeroR_split (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    (U : C) (hU : ∀ v : V, U • v = v) (d : V) :
    QZeroR q U d = q d := by
  have hUinv : U⁻¹ • d = d := inv_smul_eq_iff.mpr (hU d).symm
  rw [QZeroR_apply, hUinv, polar_self q hq h2 d, add_zero]

/-- **⟦prop:quadratic⟧, ramified identification** (⟦eq:QR⟧, `V^T = 0`): the two-term base form is
the `Γ_A` Wall double `Q_R⁰ = qDouble q U`, `U = σ₂`.  The bridge is `polar_smul_inv_eq`
(`b_q(d, U⁻¹d) = b_q(d, Ud)` for `U`-invariant `q`, char 2), the note's "`B(x, U⁻¹x) = B(x, Ux)`":
so `q(d) + b_q(d, U⁻¹d) = q(d) + b_q(d, Ud) = qDouble q U (d)`.  This is what makes **all** the
`Γ_A` Arf/Gauss computations (`SectionSix.lemma_6_6`/`lemma_6_8`/`prop_6_9_ramified`) apply to `Q_R⁰`
verbatim. -/
theorem QZeroR_eq_qDouble (q : V → ZMod 2) (U : C) (hUq : ∀ v : V, q (U • v) = q v) :
    QZeroR q U = qDouble q (fun v => U • v) := by
  funext d
  rw [QZeroR_apply, polar_smul_inv_eq q U hUq d]
  rfl

/-! ### The polar form and its perfect operator (⟦eq:polar⟧; "Both operators are invertible.")

The polar of the ramified base form is `b_R(d,d') = b_q(d, (1+U+U⁻¹)d')` — the R24 mixed Hessian
operator, whose nondegeneracy is `pairingR_operator_injective`.  The `AddEquiv` bridge below turns
the `C`-action `U` into the `V ≃+ V` form `polar_qDouble_eq` consumes. -/

/-- `⇑(toAddEquiv V U) = (U • ·)`, definitionally. -/
theorem toAddEquiv_smul (U : C) (v : V) :
    (DistribMulAction.toAddEquiv V U) v = U • v := rfl

/-- `(toAddEquiv V U).symm = (U⁻¹ • ·)`: the inverse additive automorphism is the `U⁻¹`-action. -/
theorem toAddEquiv_symm_smul (U : C) (v : V) :
    (DistribMulAction.toAddEquiv V U).symm v = U⁻¹ • v := by
  rw [AddEquiv.symm_apply_eq]
  show v = U • (U⁻¹ • v)
  rw [smul_inv_smul]

/-- **⟦eq:polar⟧, the polar form of the ramified base form**:
`b_R(d,d') = b_q(d, (1+U+U⁻¹)d') = polar q d (d' + U•d' + U⁻¹•d')`, `U = σ₂`.  Via the identification
`QZeroR_eq_qDouble` and `polar_qDouble_eq`.  The operator `d' ↦ d' + U•d' + U⁻¹•d'` is exactly R24's
degree-one Hessian operator (`mixedB_R_pairing_ramified`, ⟦eq:pairingoperator⟧). -/
theorem polar_QZeroR (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (U : C)
    (hUq : ∀ v : V, q (U • v) = q v) (d d' : V) :
    polar (QZeroR q U) d d' = polar q d (d' + U • d' + U⁻¹ • d') := by
  have hUq' : ∀ v : V, q ((DistribMulAction.toAddEquiv V U) v) = q v := hUq
  rw [QZeroR_eq_qDouble q U hUq]
  show polar (qDouble q ⇑(DistribMulAction.toAddEquiv V U)) d d' = _
  rw [polar_qDouble_eq q (DistribMulAction.toAddEquiv V U) hq hUq' d d',
    toAddEquiv_smul U d', toAddEquiv_symm_smul U d']

/-- **"Both operators are invertible.", ramified** (⟦prop:quadratic⟧ perfectness): the ramified base
form `Q_R⁰ = qDouble q σ₂` is nonsingular.  Proved **via `pairingR_operator_injective`**: through
⟦eq:polar⟧ the polar radical is the kernel of `1 + U + U⁻¹`, which is injective (R24's operator,
`U = σ₂`), hence surjective on the finite `V`, so it hits any `q`-nondegenerate partner of `d`. -/
theorem QZeroR_nonsingular_ramified [Finite C] [Finite V] (t : Marking C) (q : V → ZMod 2)
    (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q)
    (hUq : ∀ v : V, q (t.sigma2 • v) = q v) :
    Nonsingular (QZeroR q t.sigma2) := by
  intro d hd
  obtain ⟨w, hw⟩ := hns d hd
  have hsurj := Finite.injective_iff_surjective.mp (pairingR_operator_injective (V := V) t h2)
  obtain ⟨d', hd'⟩ := hsurj w
  refine ⟨d', ?_⟩
  rw [polar_QZeroR q hq t.sigma2 hUq d d', show d' + t.sigma2 • d' + t.sigma2⁻¹ • d' = w from hd']
  exact hw

/-! ### Stress test: the split symplectic collapse (the note's `b_q(d,d) = 0`)

Isolate why the split base form is the honest diagonal `q(d)` and the ramified one is not: with `σ₂`
acting trivially the symplectic term `b_q(d, U⁻¹d)` vanishes by the alternating law `b_q(d,d) = 0`,
exactly the quadratic shadow of R24's `heisMarking_cR_z_split_cancels`. -/
theorem QZeroR_symplectic_split_cancels (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (U : C) (hU : ∀ v : V, U • v = v) (d : V) :
    polar q d (U⁻¹ • d) = 0 := by
  rw [show U⁻¹ • d = d from inv_smul_eq_iff.mpr (hU d).symm, polar_self q hq h2 d]

end BaseForm

/-! ### The Gauss signs (⟦cor:gauss⟧, eq. zero counts `2^{n-1} ∓ 2^{n/2-1}`)

Instantiations of `SectionSix.prop_6_9_{unramified,ramified}` (through the `Γ`-agnostic
`GaussZ.FinalGammaA.Action` actionization) with `Q_R⁰` in place of `q`/`qDouble q U`, via the base
word expansion.  These are shaped to match what the residue supply layer consumes: `zeroCount (Q_R⁰)`
counts, then the ∓2^m sign finales.  The `Γ_A` originals cite `prop_6_9_unramified` (Hermitian line,
minus) and `lemma_6_6`/`lemma_6_8` + `prop_6_9_ramified` (Wall double, `Arf = 0`, plus); the same
originals stand here, `Q_R⁰` being their form on the nose. -/

section GaussSigns

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]

/-- **⟦cor:gauss⟧, unramified count** (negative Gauss sign): `#(Q_R⁰)⁻¹(0) = 2^{2m-1} − 2^{m-1}`.
Split branch `Q_R⁰ = q` (`QZeroR_split`, `hU` the split `σ₂`-triviality) fed to
`prop_6_9_unramified` through `zeroCount_unramified_of_action`. -/
theorem QZeroR_zeroCount_unramified
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0) (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (h2 : ∀ v : V, v + v = 0) (hU : ∀ v : V, powOmega2 (c tameSigma) • v = v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (QZeroR q (powOmega2 (c tameSigma))) = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  have hQ : QZeroR q (powOmega2 (c tameSigma)) = q := by
    funext d; exact QZeroR_split q hq h2 _ hU d
  rw [hQ]
  exact zeroCount_unramified_of_action c hc hsimple hV hunram q hq hns hinv m hm hcard

/-- **⟦cor:gauss⟧, ramified count** (positive Gauss sign): `#(Q_R⁰)⁻¹(0) = 2^{2m-1} + 2^{m-1}`.
Ramified branch `Q_R⁰ = qDouble q σ₂` (`QZeroR_eq_qDouble`, `σ₂ = powOmega2 (c σ)`) fed to
`prop_6_9_ramified` (through `lemma_6_6`/`lemma_6_8`'s `Arf(q_U) = 0`) via
`zeroCount_qDouble_ramified_of_action`. -/
theorem QZeroR_zeroCount_ramified
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (QZeroR q (powOmega2 (c tameSigma))) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  have hUq : ∀ v : V, q (powOmega2 (c tameSigma) • v) = q v :=
    fun v => hinv (powOmega2 (c tameSigma)) v
  have hQ : QZeroR q (powOmega2 (c tameSigma)) = qDouble q (powOmega2 (c tameSigma) • ·) :=
    QZeroR_eq_qDouble q (powOmega2 (c tameSigma)) hUq
  rw [hQ]
  exact zeroCount_qDouble_ramified_of_action c hc hsimple hram q hq hns hinv m hm hcard

/-- **⟦cor:gauss⟧, unramified sign finale**: `∑ᶠ sign(Q_R⁰) = −2^m` — the minus value the `Γ_R`
residue layer (R31) consumes. -/
theorem QZeroR_finsum_sign_unramified
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0) (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (h2 : ∀ v : V, v + v = 0) (hU : ∀ v : V, powOmega2 (c tameSigma) • v = v)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, SectionEight.sign (QZeroR q (powOmega2 (c tameSigma)) v) = -(2 ^ m : ℤ) :=
  finsum_sign_eq_neg_of_zeroCount _ m hm
    (QZeroR_zeroCount_unramified c hc hsimple hV hunram q hq hns hinv h2 hU m hm hcard) hcard

/-- **⟦cor:gauss⟧, ramified sign finale**: `∑ᶠ sign(Q_R⁰) = +2^m` — the plus value the `Γ_R`
residue layer (R31) consumes. -/
theorem QZeroR_finsum_sign_ramified
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, SectionEight.sign (QZeroR q (powOmega2 (c tameSigma)) v) = (2 ^ m : ℤ) :=
  finsum_sign_eq_pos_of_zeroCount _ m hm
    (QZeroR_zeroCount_ramified c hc hsimple hram q hq hns hinv m hm hcard) hcard

end GaussSigns

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition 6.1 (Base word expansion) = ⟦prop:quadratic⟧/⟦eq:QR⟧ — the base form `QZeroR`
    (`QZeroR_apply` the two-term ⟦eq:QR⟧ `q(d) + b_q(d, U⁻¹d)`); the branch identifications are
    `QZeroR_split` (`= q`, split) and `QZeroR_eq_qDouble` (`= qDouble q U`, ramified, the note's
    "differs only by the wild-coordinate renaming `c ↦ d`").  The polar form ⟦eq:polar⟧
    `b_R(d,d') = b_q(d, (1+U+U⁻¹)d')` is `polar_QZeroR`; "Both operators are invertible."
    (perfectness) is `QZeroR_nonsingular_ramified`, via R24's `pairingR_operator_injective`.
  * Corollary 6.2 (Gauss signs) = ⟦cor:gauss⟧ — the zero counts `2^{n-1} ∓ 2^{n/2-1}`:
    `QZeroR_zeroCount_unramified` (`−`, `prop_6_9_unramified`) and `QZeroR_zeroCount_ramified`
    (`+`, `prop_6_9_ramified` through `lemma_6_6`/`lemma_6_8`); the ∓2^m finales are
    `QZeroR_finsum_sign_unramified`/`QZeroR_finsum_sign_ramified`.
  * The full `Γ_R` residue package (the `κ⁰`/`QZero` word-quadratic evaluation identifying the
    honest word value with `QZeroR`, and the `∓2^m` residue assembly) is ticket R31
    (`GaussZ/FinalGammaR`), which instantiates the identifications above.
-/
