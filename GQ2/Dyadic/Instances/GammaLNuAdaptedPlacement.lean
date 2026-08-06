/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageMarkedFrame

/-!
# The fully `ν`-adapted Witt frame: placing **every** row of `ν̄`

`GammaLSylowPreimageMarkedFrame` §3 places the mod-two unramified class `ν̄` at the middle-plane
coordinates `(1, 0)`, which is exactly the two rows `SqNuForwardSupply` names.  The full-row
residual `MarkingAudit.SqFullNuForwardSupply` needs **all** `2h + 3` rows: `ν(σ) = 1`,
`ν(x₀) = ν(x₁) = 0`, and every handle letter in `ker ν_ur`.  This file settles the placement
question for the whole marking.

## The dimension count

Write `W = H¹(G_K(2), 𝔽₂)`, `b` the Frattini cup form, `κ` the Labute vector (`b κ x = b x x`,
`b κ κ = 1` in odd degree), `τ` Serre's `ω` row.  The cup adaptation pins the Gram of `b` in the
basis dual to a frame's generators to be the improved relator's quadratic initial Gram
`κ 2 2 + (κ 0 1 + κ 1 0) + Σ_j (κ U_j V_j + κ V_j U_j)`, i.e. `⟨1⟩ ⊥ H ⊥ H^{⊥ h}` with the
`⟨1⟩`-slot at frame index `2` and the first hyperbolic plane at indices `(0, 1)`.  A frame's
cyclotomic constructor table already forces the coordinate vectors of `κ` and `τ`: `κ` is the
`x₁`-dual `(0,0,1,0,…,0)` and `τ` is `(1,1,0,0,…,0)`.

The full-row demand is that `ν̄`'s coordinate vector be the `σ`-dual `(1,0,0,0,…,0)`.  Reading
that against the model Gram gives three statements and no more:

* `b(κ, ν̄) = ν̄`'s `x₁`-row `= 0` — i.e. `ν̄ ∈ ker(x ↦ b x x)`, the diagonal kernel;
* `b(τ, ν̄) = ν̄`'s `σ`-row `+ ν̄`'s `x₀`-row `= 1` — the datum `NuUrOmegaCupOne` of §4 there;
* the handle rows vanish — *no* cup condition at all, because `κ` and `τ` are blind to the
  handle planes.

So the system is **consistent**, and its exact content is: the first hyperbolic pair of the Witt
splitting must be `(ν̄, ν̄ + τ)`.  That is legitimate precisely when `ν̄` lies in the diagonal
kernel and pairs to `1` with `τ` — the two `𝔽₂` data above.  In particular the `2h` handle rows,
which naively look like `2h` new linear conditions on a single functional, are **free**: they only
say that the handle planes are chosen inside `⟨ν̄, τ⟩^⊥`, and an orthogonal complement of a
hyperbolic plane always exists.  Nothing is over-determined.

## What is proved

* **§1 `frattiniFrameAdaptedModelEquiv_fullPlaced`** — the Witt adaptation with `n` placed at the
  *full* `σ`-dual vector `(0, ((1, 0), 0))`, not merely at its two middle-plane coordinates.  The
  hypotheses are exactly the two cup values `b n t = 1` and `b e n = 0`; the auxiliary
  `t ≠ 0` of `frattiniFrameAdaptedModelEquiv_placed` is no longer needed, since `b n t = 1`
  supplies it.  The proof is the placed one with the hyperbolic partner taken to be `n` itself.
* **§2 `frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted`** — the `κ`-side sharpness, the
  exact analogue of the `ω`-side statement of the frame file: in *every* cup-adapted frame,
  `b(κ, ν̄)` **is** `ν̄`'s `x₁`-row.  So the second datum is necessary as well as sufficient, and
  §1's hypotheses cannot be weakened.
* **§3 `NuUrKappaCupZero`** — the second `𝔽₂` datum as a `def`-shaped `Prop` (never an axiom),
  with the refutation form `not_isCupAdapted_and_fullNuRows_of_kappaCup_ne_zero`.

## Axioms

§1 is std-3.  §2–§3 pick up `tateDualityAt` (**B6**) definitionally through `FieldData.cupFormK`,
exactly as the frame file's §4 does.  No `sorry`, no new axiom, no `native_decide`.  Census
unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.Certificates.LSqStokes
open FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace NuAdapted

/-! ## §1 The fully placed Witt adaptation

`frattiniFrameAdaptedModelEquiv_placed` chooses the hyperbolic partner `w'` of `t` to miss `n`;
here we take the partner to be `n` itself, which is legitimate as soon as `n` lies in the
diagonal kernel (`b e n = 0`) and pairs to `1` with `t`.  The middle plane is then `⟨n, n + t⟩`,
`t` still has coordinates `(1,1)` and `n` acquires the *complete* coordinate vector
`(0, ((1, 0), 0))`: `⟨1⟩`-slot zero, middle plane `(1, 0)`, and every handle plane zero. -/

section Placed

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- **The fully placed adapted normal form.**  The `⟨1⟩` slot is the Labute vector `e`, the
`ω`-vector `t` spans the diagonal `(1,1)` of the first hyperbolic plane, and the third vector `n`
is the *whole* first dual basis vector: it evaluates to `1` on the dual `σ`-generator and to `0`
on every other dual generator, the `x₁`-slot and all `2h` handle slots included.

The two hypotheses `b e n = 0` and `b n t = 1` are the two `𝔽₂` cup values §2 shows to be
necessary; nothing else about `n` enters, and `t ≠ 0` is a consequence rather than an input. -/
theorem frattiniFrameAdaptedModelEquiv_fullPlaced [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e t n : W}
    (he : ∀ w, b e w = b w w) (he1 : b e e = 1) (hte : b t e = 0)
    (hen : b e n = 0) (hnt : b n t = 1) {h : ℕ} (hcard : Nat.card W = 2 ^ (2 * h + 3)) :
    ∃ Φ : W ≃ₗ[ZMod 2] Model h,
      (∀ x y, b x y = modelGram h (Φ x) (Φ y)) ∧
        Φ e = (1, 0) ∧ Φ t = (0, ((1, 1), 0)) ∧ Φ n = (0, ((1, 0), 0)) := by
  classical
  have h2W : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
  have htt : b t t = 0 := by rw [← he t, hb.symm]; exact hte
  have het : b e t = 0 := by rw [hb.symm]; exact hte
  have hnn : b n n = 0 := by rw [← he n]; exact hen
  have htn : b t n = 1 := by rw [hb.symm]; exact hnt
  set tK : cupKer hb := ⟨t, htt⟩ with htKdef
  set nK : cupKer hb := ⟨n, hnn⟩ with hnKdef
  have hbK := isSymplectic_cupKer hb hnd he he1
  -- the first hyperbolic pair is `(n, n + t)`
  have hvw : b ((nK : cupKer hb) : W) ((nK + tK : cupKer hb) : W) = 1 := by
    show b n (n + t) = 1
    rw [hb.add_right, hnn, zero_add]
    exact hnt
  set e1 := hypSplitEquiv hbK hvw with he1def
  have hPsymp := isSymplectic_restrict hbK hvw
  haveI : Finite (cupKer hb) := Subtype.finite
  haveI : Finite (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK nK (nK + tK)) :=
    Subtype.finite
  obtain ⟨m, φ', hφ'⟩ := exists_symplectic_equiv _ hPsymp
  have hm : m = h := by
    have hc1 : Nat.card W = 2 * Nat.card (cupKer hb) := by
      rw [Nat.card_congr (cupSplitEquiv hb he he1).toEquiv, Nat.card_prod]
      simp
    have hc2 : Nat.card (cupKer hb) = 4 *
        Nat.card (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK nK (nK + tK)) := by
      rw [Nat.card_congr e1.toEquiv, Nat.card_prod]
      simp
    have hc3 : Nat.card
        (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK nK (nK + tK)) = 4 ^ m := by
      rw [Nat.card_congr φ'.toEquiv]
      simp
    have hchain : (2 : ℕ) ^ (2 * m + 3) = 2 ^ (2 * h + 3) := by
      rw [← hcard, hc1, hc2, hc3, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]
      ring
    have := Nat.pow_right_injective (le_refl 2) hchain
    omega
  have hm' : h = m := hm.symm
  subst hm'
  set φ₀ := cupSplitEquiv hb he he1 with hφ₀
  set Φ : W ≃ₗ[ZMod 2] Model h := φ₀.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr
    (e1.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr φ'))) with hΦ
  have hΦapp : ∀ u : W, Φ u = ((φ₀ u).1, ((e1 (φ₀ u).2).1, φ' (e1 (φ₀ u).2).2)) := by
    intro u
    rw [hΦ]
    simp only [LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply, LinearEquiv.refl_apply]
  have hsplit2 : ∀ k k' : cupKer hb, b (k : W) (k' : W) =
      ((e1 k).1.1 * (e1 k').1.2 + (e1 k).1.2 * (e1 k').1.1) +
        hypGram (φ' (e1 k).2) (φ' (e1 k').2) := by
    intro k k'
    have hg1 := hypSplit_gram hbK hvw k k'
    have hg2 := hφ' (e1 k).2 (e1 k').2
    refine hg1.trans ?_
    rw [← hg2]
    rfl
  refine ⟨Φ, ?_, ?_, ?_, ?_⟩
  · intro x y
    have hx : (φ₀ x).1 • e + ((φ₀ x).2 : W) = x := φ₀.left_inv x
    have hy : (φ₀ y).1 • e + ((φ₀ y).2 : W) = y := φ₀.left_inv y
    have hsplit : b x y = (φ₀ x).1 * (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) := by
      calc b x y = b ((φ₀ x).1 • e + ((φ₀ x).2 : W)) ((φ₀ y).1 • e + ((φ₀ y).2 : W)) := by
            rw [hx, hy]
        _ = (φ₀ x).1 * (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) :=
            cupSplit_gram hb he he1 _ _ _ _
    rw [hΦapp x, hΦapp y]
    show b x y = (φ₀ x).1 * (φ₀ y).1 +
      ((e1 (φ₀ x).2).1.1 * (e1 (φ₀ y).2).1.2 + (e1 (φ₀ x).2).1.2 * (e1 (φ₀ y).2).1.1) +
        hypGram (φ' (e1 (φ₀ x).2).2) (φ' (e1 (φ₀ y).2).2)
    rw [hsplit, hsplit2 (φ₀ x).2 (φ₀ y).2]
    ring
  · have h0 : φ₀ e = (1, 0) := by
      refine Prod.ext he1 (Subtype.ext ?_)
      show e + (b e e) • e = 0
      rw [he1, one_smul, h2W]
    rw [hΦapp e, h0]
    simp
  · have h0 : φ₀ t = (0, tK) := by
      refine Prod.ext het (Subtype.ext ?_)
      show t + (b e t) • e = t
      rw [het, zero_smul, add_zero]
    have h1 : e1 tK = ((1, 1), 0) := by
      have hwtK : b ((nK + tK : cupKer hb) : W) ((tK : cupKer hb) : W) = 1 := by
        show b (n + t) t = 1
        rw [hb.add_left, hnt, htt, add_zero]
      have hvtK : b ((nK : cupKer hb) : W) ((tK : cupKer hb) : W) = 1 := hnt
      refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext ?_)
      · exact hwtK
      · exact hvtK
      · show tK + (b ((nK + tK : cupKer hb) : W) ((tK : cupKer hb) : W)) • nK +
          (b ((nK : cupKer hb) : W) ((tK : cupKer hb) : W)) • (nK + tK) = 0
        rw [hwtK, hvtK, one_smul, one_smul]
        have hh : tK + nK + (nK + tK) = (tK + tK) + (nK + nK) := by abel
        rw [hh, GQ2.Dyadic.Certificates.module_zmod2_two_torsion,
          GQ2.Dyadic.Certificates.module_zmod2_two_torsion, add_zero]
    rw [hΦapp t, h0, h1]
    simp
  · have h0 : φ₀ n = (0, nK) := by
      refine Prod.ext hen (Subtype.ext ?_)
      show n + (b e n) • e = n
      rw [hen, zero_smul, add_zero]
    have h1 : e1 nK = ((1, 0), 0) := by
      have hwnK : b ((nK + tK : cupKer hb) : W) ((nK : cupKer hb) : W) = 1 := by
        show b (n + t) n = 1
        rw [hb.add_left, hnn, htn, zero_add]
      have hvnK : b ((nK : cupKer hb) : W) ((nK : cupKer hb) : W) = 0 := hnn
      refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext ?_)
      · exact hwnK
      · exact hvnK
      · show nK + (b ((nK + tK : cupKer hb) : W) ((nK : cupKer hb) : W)) • nK +
          (b ((nK : cupKer hb) : W) ((nK : cupKer hb) : W)) • (nK + tK) = 0
        rw [hwnK, hvnK, one_smul, zero_smul, add_zero]
        exact GQ2.Dyadic.Certificates.module_zmod2_two_torsion nK
    rw [hΦapp n, h0, h1]
    simp

end Placed

/-! ## §2 The `κ`-side sharpness: the `x₁`-row of `ν̄` *is* a cup value

The frame file's §4 shows `b(τ, ν̄)` is the sum of `ν̄`'s two core rows.  The same computation
against the mod-four row shows `b(κ, ν̄)` is `ν̄`'s `x₁`-row, because the constructor table pins
`κ` at the `⟨1⟩`-slot: `ε(S) = ε(X) = 0`, `ε(Y) = 1`, `ε(1) = 0`. -/

section Sharp

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The mod-four parity row of an element with cyclotomic value `≡ 1 (mod 4)`. -/
theorem toAdd_modFourCharacterKTwo_of_chi_one {g : maxProPQuotient 2 (GalK K)} {u : ℤ_[2]ˣ}
    (hg : chiCycKTwo (K := K) g = u)
    (hu : PadicInt.toZModPow 2 ((u : ℤ_[2]ˣ) : ℤ_[2]) = 1) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) g) = 0 := by
  show Multiplicative.toAdd (unitsModFourParity
    (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g))) = 0
  rw [hg]
  exact frattiniFrame_parity_of_val_one hu

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- The mod-four parity row of an element with cyclotomic value `≡ 3 (mod 4)`. -/
theorem toAdd_modFourCharacterKTwo_of_chi_three {g : maxProPQuotient 2 (GalK K)} {u : ℤ_[2]ˣ}
    (hg : chiCycKTwo (K := K) g = u)
    (hu : PadicInt.toZModPow 2 ((u : ℤ_[2]ˣ) : ℤ_[2]) = 3) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) g) = 1 := by
  show Multiplicative.toAdd (unitsModFourParity
    (Units.map (PadicInt.toZModPow 2).toMonoidHom (chiCycKTwo (K := K) g))) = 1
  rw [hg]
  exact frattiniFrame_parity_of_val_three hu

variable {h : ℕ}

theorem frame_kappa_sigma (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) (F.generators 0)) = 0 :=
  toAdd_modFourCharacterKTwo_of_chi_one F.sigma frattiniFrame_Sval_modFour

theorem frame_kappa_x0 (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) (F.generators 1)) = 0 :=
  toAdd_modFourCharacterKTwo_of_chi_one F.x0 frattiniFrame_rootX_modFour

theorem frame_kappa_x1 (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) (F.generators 2)) = 1 :=
  toAdd_modFourCharacterKTwo_of_chi_three F.x1 frattiniFrame_Yval_modFour

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
theorem frame_kappa_ker {g : maxProPQuotient 2 (GalK K)}
    (hg : g ∈ (chiCycKTwo (K := K)).toMonoidHom.ker) :
    Multiplicative.toAdd (cyclotomicModFourCharacterKTwo (K := K) g) = 0 := by
  have hone : PadicInt.toZModPow 2 (((1 : ℤ_[2]ˣ) : ℤ_[2])) = (1 : ZMod 4) := by
    rw [Units.val_one, map_one]
  exact toAdd_modFourCharacterKTwo_of_chi_one (MonoidHom.mem_ker.mp hg) hone

/-- **The `κ`-side sharp identity.**  In any cup-adapted frame the cup value of the mod-four row
against the unramified class is exactly the unramified class's `x₁`-row.  The `κ`-coordinates
`(0,0,1,0,…,0)` come from `ε(S) = ε(X) = 0`, `ε(Y) = 1`, `ε(1) = 0`; nothing about `ν̄` is used. -/
theorem frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
        (MarkedFrame.nuUrModTwoClassKTwo B) =
      frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 2) := by
  have hc := hcup (cyclotomicModFourCharacterKTwo (K := K)) (MarkedFrame.nuUrModTwoKTwo B)
  refine hc.trans ?_
  rw [GQ2.ContCoh.sqRelatorQuadraticInitialGram_eq]
  simp only [frame_kappa_sigma F, frame_kappa_x0 F, frame_kappa_x1 F,
    frame_kappa_ker (F.handleU _), frame_kappa_ker (F.handleV _), zero_mul, one_mul,
    add_zero, Finset.sum_const_zero]
  rfl

/-- **The `x₁`-row forces the `κ`-cup value.**  A cup-adapted frame on which `ν̄` vanishes at the
`x₁`-generator exists only if `b(κ, ν̄) = 0`. -/
theorem frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_eval (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hx1 : frattiniFrameEval (MarkedFrame.nuUrModTwoClassKTwo B) (F.generators 2) = 0) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (MarkedFrame.nuUrModTwoClassKTwo B) = 0 := by
  rw [frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted B F hcup, hx1]

/-- The exact-`ν` form: a cup-adapted frame carrying the standard `x₁`-row `ν(x₁) = 0` exists
only if `b(κ, ν̄) = 0`. -/
theorem frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_nuRow (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hx1 : nuUrKTwo B (F.generators 2) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (MarkedFrame.nuUrModTwoClassKTwo B) = 0 := by
  refine frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_eval B F hcup ?_
  rw [MarkedFrame.frattiniFrameEval_nuUrModTwoClassKTwo, hx1, toAdd_ofAdd, map_zero]

end Sharp

/-! ## §3 The second `𝔽₂` datum, and its refutation form -/

section Datum

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- **The second residual arithmetic input**, as a `def`-shaped `Prop` (never an axiom): the cup
value `b_K([−1], [u]) = 0`, i.e. the Hilbert symbol `(u, −1)_K = +1` for `u` the unramified unit.
Equivalently, by the Labute identity `b(κ, x) = b(x, x)`, it is the isotropy of `ν̄` itself.

Arithmetically `−1` is a unit, hence a norm from the unramified quadratic extension `K(√u)`, so
the value is `0` for every `K`; `GammaLNuAdaptedKappaValue` proves it. -/
def NuUrKappaCupZero (B : MarkedRecip R K) : Prop :=
  frattiniFrameCup (cyclotomicModFourClassKTwo (K := K)) (MarkedFrame.nuUrModTwoClassKTwo B) = 0

omit [T2Space (GalK K)] in
/-- The datum re-read as isotropy of the unramified class: `b(ν̄, ν̄) = 0`. -/
theorem nuUrModTwoClassKTwo_self_eq_zero_of_kappaCupZero (B : MarkedRecip R K)
    (hkappa : NuUrKappaCupZero B) :
    frattiniFrameCup (MarkedFrame.nuUrModTwoClassKTwo B)
      (MarkedFrame.nuUrModTwoClassKTwo B) = 0 :=
  (frattiniFrameCup_kappa (K := K) _).symm.trans hkappa

/-- **Necessity, refutation form.**  If the `κ`-cup value is nonzero then *no* cup-adapted frame
carries even the single row `ν(x₁) = 0`, hence none carries the full marking. -/
theorem not_isCupAdapted_and_fullNuRows_of_kappaCup_ne_zero (B : MarkedRecip R K)
    (hne : frattiniFrameCup (cyclotomicModFourClassKTwo (K := K))
      (MarkedFrame.nuUrModTwoClassKTwo B) = 1) {h : ℕ} (F : SqCyclotomicFrattiniFrame K h) :
    ¬ (F.IsCupAdapted ∧ nuUrKTwo B (F.generators 2) = Multiplicative.ofAdd (0 : ℤ_[2])) := by
  rintro ⟨hcup, hx1⟩
  have hzero := frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_nuRow B F hcup hx1
  rw [hne] at hzero
  exact absurd hzero (by decide)

end Datum

end NuAdapted

end

#print axioms NuAdapted.frattiniFrameAdaptedModelEquiv_fullPlaced
#print axioms NuAdapted.toAdd_modFourCharacterKTwo_of_chi_one
#print axioms NuAdapted.toAdd_modFourCharacterKTwo_of_chi_three
#print axioms NuAdapted.frame_kappa_sigma
#print axioms NuAdapted.frame_kappa_x0
#print axioms NuAdapted.frame_kappa_x1
#print axioms NuAdapted.frame_kappa_ker
#print axioms NuAdapted.frattiniFrameCup_kappa_nuUrModTwo_eq_of_isCupAdapted
#print axioms NuAdapted.frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_eval
#print axioms NuAdapted.frattiniFrameCup_kappa_nuUrModTwo_eq_zero_of_nuRow
#print axioms NuAdapted.NuUrKappaCupZero
#print axioms NuAdapted.nuUrModTwoClassKTwo_self_eq_zero_of_kappaCupZero
#print axioms NuAdapted.not_isCupAdapted_and_fullNuRows_of_kappaCup_ne_zero

end GQ2.Dyadic.LSquare
