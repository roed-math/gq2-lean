/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimagePivotNu
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFrattiniFrame
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldRigidity

/-!
# P3-frame — placing the unramified mod-two row inside the Frattini frame

`SqMarkedForwardSupply` (`GammaLSylowPreimagePivotNu.lean` §4) asks for an oriented equivalence
`f : D_sq(h) ≃ₜ* G_K(2)` whose two core generators carry the standard unramified rows
`ν(f σ) = 1`, `ν(f x₀) = 0`.  P3 proved that the *exact* rows cost nothing beyond their **mod-2**
shadows (`exists_squareShift_nuUrKTwo_eq_one` / `_eq_zero`), and that the mod-2 rows are a
statement about where the unramified class `ν̄ = [u] ∈ H¹(G_K(2), 𝔽₂)` sits against the frame's
dual basis.  This file settles that placement question.

## What is proved

* **§1** the mod-two shadow `ν̄` of `ν_ur`, as a degree-one class, and the dictionary between its
  frame evaluations and the two parity clauses `toMarkedOfParities` consumes.
* **§2 `nuUrModTwoClassKTwo_ne_smul_add_smul`** — `ν̄ ∉ span{κ, τ}`, unconditionally in the
  ramification type and the degree: at the type-`L` level `r = 0` the clause `nu_ker_chi_ge`
  produces an element `q` with `χ q = 1` and `ν q = 1`; both cyclotomic rows are functions of
  `χ`, so both vanish at `q` while `ν̄ q = 1`.  (The design note of `GammaLSylowPreimagePivotNu`
  reached the same conclusion through Kummer theory and the ramified-`i` hypothesis; the level
  clause is a much shorter road, and needs neither.)
* **§3 `frattiniFrameAdaptedModelEquiv_placed`** — the Witt adaptation of the frame refined by a
  third vector: if `b n t = 1` then the hyperbolic splitting can be chosen so that `n` acquires
  the middle-plane coordinates `(1, 0)`, i.e. lands on the `σ`-slot and misses the `x₀`-slot.
  The hypothesis is used through `exists_pairing_one_zero`, `𝔽₂`-duality inside the diagonal
  kernel; nothing else about `n` is needed (in particular `ν̄ ∉ span{κ,τ}` is a *consequence*
  of `b n t = 1`, not a further input).
* **§4 `frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted`** — the **sharpness** statement,
  and the reason §3's hypothesis cannot be weakened: for *every* cup-adapted frame,
  `b(τ, ν̄) = ν̄(gens 0) + ν̄(gens 1)`.  The constructor table pins `τ` at the middle-plane
  coordinates `(1,1)` (through `ω(S) = ω(X) = 1`, `ω(Y) = 0`), so a frame carrying the two
  marked rows `(1, 0)` **forces** `b(τ, ν̄) = 1`.  Independence of `ν̄` from `κ` and `τ` is
  therefore *not* sufficient: the placement is equivalent to one cup value.  This corrects the
  frame ticket recorded in `GammaLSylowPreimagePivotNu`, which priced the placement as the
  `w'`-freedom of the hyperbolic splitting alone.
* **§5 `exists_isCupAdapted_nuRows_of_cupOne`** — the marked frame supply over that single cup
  value, exact `ν`-rows included: the Frattini-coset square shift of
  `GammaLSylowPreimagePivotNu` §2 moves each generator to the exact value without touching its
  cyclotomic row, its level-two class, or the cup adaptation (`squareShiftFrame`).
* **§6 `oddDegreeGalKSqMarkedForwardSupply`** — the assembly.  Odd-degree Demushkin rigidity
  makes a forward-generator package's forward map bijective and *is* the equivalence, so
  `σ ↦ generators 0` and `x₀ ↦ generators 1` hold definitionally
  (`sqMarkedForwardSupply_of_forwardGeneratorData`), and `SqMarkedForwardSupply` follows.

## The two residuals

* `NuUrOmegaCupOne B` (§4) — the single `𝔽₂` value `b_K([2], [u]) = 1`, i.e. the Hilbert symbol
  `(2, u)_K = −1` for `u` the unramified unit.  Arithmetically `(2, u)_K = (−1)^{v(2)}` and
  `v(2) = e(K/ℚ₂)` is odd in odd degree; formalizing it needs the Kummer identification of `ν̄`
  with `[u]` together with the norm criterion for the *unramified* quadratic extension.  Neither
  exists in the repository: `CyclotomicKummerBridge*` names only `[−1]` and `[2]`, census axiom
  **B11a** is a vanishing criterion with no value formula, and the Artin/Kummer compatibility
  `χ_x(rec_K a) = inv_K(x ⌣ κ(a))` is still the hypothesis `ModTwoTateKummerArtinCompatibility`.
  §4 shows the datum is **necessary**, not merely convenient.
* `SqCupAdaptedFramePresentation K` (§6) — the improved relator and topological generation *on a
  cup-adapted frame's own generators*.  This one is P3-independent (it never mentions `ν`) and
  its level-three shadow is already a theorem.  It is stated frame-first because the compactness
  selection inside `forwardGeneratorData_of_finiteLevel` forgets which generators it chose, so
  the existing stage chain cannot be asked to keep a pre-chosen marked pair.

Both are `def`-shaped `Prop`s, never axioms.

## Axioms

§1–§3 are std-3.  From §4 on, `tateDualityAt` (**B6**) enters definitionally through
`FieldData.cupFormK`; §5 adds `hilbertSymbol_normCriterion_finiteDyadic` (**B11a**),
`absGalQ2_isTopologicallyFinitelyGenerated` (**B1**) and `absGalQ2_localEulerCharacteristic`
(**B7**).  `markedRecipAt` (**B5-K**) and `localReciprocity` (**B5**) do *not* appear: every
consumer is fed the caller's own `B : MarkedRecip R K` instead of the axiom, so this file's
footprint is strictly smaller than `oddDegreeSqCyclotomicFrattiniFrameSupply_holds`'s.  The
`#print axioms` block at the end of the file is the record.  No `sorry`, no new axiom, no
`native_decide`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.Certificates.LSqStokes
open FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace MarkedFrame

/-! ## §1 The mod-two shadow of the unramified character

`ν mod 2` is a continuous mod-two character of `G_K(2)`, hence a degree-one class; the frame's
evaluation pairing reads it at the dual generators, and the two values are exactly the parity
clauses that `OddDegreeGalKSqCyclotomicCoreTable.toMarkedOfParities` consumes. -/

section Shadow

/-- Reduction `ℤ₂ ↠ 𝔽₂` (the target `ZMod (2 ^ 1)` *is* `ZMod 2`). -/
def redTwo : ℤ_[2] →+* ZMod 2 := PadicInt.toZModPow (p := 2) 1

theorem redTwo_two : redTwo 2 = 0 := by
  have hmem : (2 : ℤ_[2]) ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := by
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton]
    exact_mod_cast dvd_refl (2 : ℤ_[2])
  exact hmem

/-- Mod-two reduction detects the maximal ideal: `red y = 0` exactly when `y ∈ 2ℤ₂`. -/
theorem redTwo_eq_zero_iff (y : ℤ_[2]) : redTwo y = 0 ↔ ∃ m : ℤ_[2], y = 2 * m := by
  constructor
  · intro h
    have hk : y ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := h
    rw [PadicInt.ker_toZModPow, pow_one, Ideal.mem_span_singleton] at hk
    obtain ⟨m, hm⟩ := hk
    exact ⟨m, by rw [hm]; push_cast; ring⟩
  · rintro ⟨m, rfl⟩
    rw [map_mul, redTwo_two, zero_mul]

/-- Mod-two reduction detects units: `red y = 1` exactly when `y` is a unit. -/
theorem redTwo_eq_one_iff (y : ℤ_[2]) : redTwo y = 1 ↔ IsUnit y := by
  constructor
  · intro h
    by_contra hcon
    have hmem : y ∈ IsLocalRing.maximalIdeal ℤ_[2] := hcon
    rw [PadicInt.maximalIdeal_eq_span_p] at hmem
    have hker : y ∈ RingHom.ker (PadicInt.toZModPow (p := 2) 1) := by
      rw [PadicInt.ker_toZModPow, pow_one]
      exact hmem
    rw [RingHom.mem_ker] at hker
    rw [show redTwo y = PadicInt.toZModPow (p := 2) 1 y from rfl, hker] at h
    exact absurd h (by decide)
  · rintro ⟨u, rfl⟩
    obtain ⟨w, hw⟩ := GQ2.two_dvd_val_sub_one u
    have hval : ((u : ℤ_[2]) : ℤ_[2]) = 1 + 2 * w := by linear_combination hw
    rw [hval, map_add, map_mul, map_one, redTwo_two, zero_mul, add_zero]

/-- Mod-two reduction, as a continuous character of `Multiplicative ℤ₂`. -/
def redTwoChar : ContinuousMonoidHom (Multiplicative ℤ_[2]) (Multiplicative (ZMod 2)) where
  toFun x := Multiplicative.ofAdd (redTwo (Multiplicative.toAdd x))
  map_one' := by
    show Multiplicative.ofAdd (redTwo (0 : ℤ_[2])) = 1
    rw [map_zero]
    rfl
  map_mul' x y := by
    show Multiplicative.ofAdd (redTwo (Multiplicative.toAdd x + Multiplicative.toAdd y)) = _
    rw [map_add]
    rfl
  continuous_toFun := by
    have hred : Continuous (PadicInt.toZModPow (p := 2) 1) := by
      rw [continuous_def]
      intro T _
      exact GQ2.isOpen_preimage_toZModPow 1 T
    exact continuous_ofAdd.comp (hred.comp continuous_toAdd)

@[simp] theorem toAdd_redTwoChar (x : Multiplicative ℤ_[2]) :
    Multiplicative.toAdd (redTwoChar x) = redTwo (Multiplicative.toAdd x) := rfl

end Shadow

section Class

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The mod-two shadow `ν̄` of the unramified character, as a continuous mod-two character. -/
def nuUrModTwoKTwo (B : MarkedRecip R K) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
  redTwoChar.comp (nuUrKTwo B)

@[simp] theorem toAdd_nuUrModTwoKTwo (B : MarkedRecip R K) (g : maxProPQuotient 2 (GalK K)) :
    Multiplicative.toAdd (nuUrModTwoKTwo B g) =
      redTwo (Multiplicative.toAdd (nuUrKTwo B g)) := rfl

/-- **The unramified class `ν̄ = [u]`** in `H¹(G_K(2), 𝔽₂)`. -/
def nuUrModTwoClassKTwo (B : MarkedRecip R K) : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  SqCyclotomicFrattiniFrame.characterClass (K := K) (nuUrModTwoKTwo B)

@[simp] theorem frattiniFrameEval_nuUrModTwoClassKTwo (B : MarkedRecip R K)
    (g : maxProPQuotient 2 (GalK K)) :
    frattiniFrameEval (nuUrModTwoClassKTwo B) g =
      redTwo (Multiplicative.toAdd (nuUrKTwo B g)) := rfl

/-- Frame value `1` on the `σ`-slot is the `σ`-parity clause of `toMarkedOfParities`. -/
theorem isUnit_toAdd_nuUrKTwo_of_eval_eq_one (B : MarkedRecip R K)
    {g : maxProPQuotient 2 (GalK K)}
    (hg : frattiniFrameEval (nuUrModTwoClassKTwo B) g = 1) :
    IsUnit (Multiplicative.toAdd (nuUrKTwo B g)) :=
  (redTwo_eq_one_iff _).mp hg

/-- Frame value `0` on the `x₀`-slot is the `x₀`-parity clause of `toMarkedOfParities`. -/
theorem even_toAdd_nuUrKTwo_of_eval_eq_zero (B : MarkedRecip R K)
    {g : maxProPQuotient 2 (GalK K)}
    (hg : frattiniFrameEval (nuUrModTwoClassKTwo B) g = 0) :
    ∃ m : ℤ_[2], Multiplicative.toAdd (nuUrKTwo B g) = 2 * m :=
  (redTwo_eq_zero_iff _).mp hg

/-! ## §2 `ν̄` is independent of the two cyclotomic rows -/

omit [FiniteDimensional ℚ_[2] K] in
/-- Both cyclotomic rows vanish on a `χ`-trivial element. -/
theorem frattiniFrameEval_modFour_eq_zero {g : maxProPQuotient 2 (GalK K)}
    (hg : chiCycKTwo (K := K) g = 1) :
    frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g = 0 := by
  rw [frattiniFrameEval_modFour, hg, map_one, map_one, toAdd_one]

omit [FiniteDimensional ℚ_[2] K] in
theorem frattiniFrameEval_modEight_eq_zero {g : maxProPQuotient 2 (GalK K)}
    (hg : chiCycKTwo (K := K) g = 1) :
    frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) g = 0 := by
  rw [frattiniFrameEval_modEight, hg, map_one, map_one, toAdd_one]

/-- **`ν̄ ∉ span{κ, τ}`.**  At the type-`L` level `r = 0` the marked bundle's level clause
supplies an element `q` of `ker χ` with `ν q = 1`; the two cyclotomic rows are functions of `χ`,
so they vanish at `q` while `ν̄ q = 1`.  Neither odd degree nor ramified `i` is needed.

This is the independence recorded as the frame ticket's arithmetic input.  §4 shows it is *not*
sufficient for the placement: what the placement needs is the sharper cup value `b(τ, ν̄) = 1`. -/
theorem nuUrModTwoClassKTwo_ne_smul_add_smul (B : MarkedRecip R K) (hr : B.r = 0)
    (a c : ZMod 2) :
    nuUrModTwoClassKTwo B ≠
      a • cyclotomicModFourClassKTwo (K := K) +
        c • cyclotomicModEightOmegaClassKTwo (K := K) := by
  obtain ⟨q, hqchi, hqnu⟩ := exists_chiCycKTwo_eq_one_and_nuUrKTwo_eq B hr 1
  intro hcon
  have hval : frattiniFrameEval (nuUrModTwoClassKTwo B) q =
      frattiniFrameEval (a • cyclotomicModFourClassKTwo (K := K) +
        c • cyclotomicModEightOmegaClassKTwo (K := K)) q := by
    rw [hcon]
  rw [frattiniFrameEval_nuUrModTwoClassKTwo, hqnu, toAdd_ofAdd, map_one,
    frattiniFrameEval_add, frattiniFrameEval_smul, frattiniFrameEval_smul,
    frattiniFrameEval_modFour_eq_zero hqchi, frattiniFrameEval_modEight_eq_zero hqchi,
    mul_zero, mul_zero, add_zero] at hval
  exact absurd hval (by decide)

end Class

/-! ## §3 The placed Witt adaptation

`frattiniFrameAdaptedModelEquiv` splits the first hyperbolic plane on the pair `(w', w' + τ)`
for an *arbitrary* `w'` with `b τ w' = 1`.  That freedom is exactly enough to place a third
vector `n` at the middle-plane coordinates `(1, 0)` — provided `b n t = 1`, which §4 shows is
also necessary. -/

section Placed

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

omit [Module (ZMod 2) W] in
/-- **`𝔽₂` separation in a symplectic space.**  If `p ≠ 0` and `p + q ≠ 0` then some vector
pairs to `1` with `p` and to `0` with `q`.  Over `𝔽₂` two functionals are dependent exactly when
they are equal or one vanishes, and nondegeneracy rules both out. -/
theorem exists_pairing_one_zero {bV : W → W → ZMod 2} (hbV : IsSymplecticFp2 bV) {p q : W}
    (hp : p ≠ 0) (hpq : p + q ≠ 0) : ∃ w : W, bV p w = 1 ∧ bV q w = 0 := by
  have hne : ∀ z : W, z ≠ 0 → ∃ w, bV z w = 1 := by
    intro z hz
    by_contra hcon
    push Not at hcon
    refine hz (hbV.nondeg z fun w ↦ ?_)
    rcases ZMod.eq_zero_or_eq_one (bV z w) with h0 | h1
    · exact h0
    · exact absurd h1 (hcon w)
  obtain ⟨y, hy⟩ := hne p hp
  rcases ZMod.eq_zero_or_eq_one (bV q y) with h0 | h1
  · exact ⟨y, hy, h0⟩
  obtain ⟨z, hz⟩ := hne (p + q) hpq
  rw [hbV.add_left] at hz
  rcases ZMod.eq_zero_or_eq_one (bV q z) with h0' | h1'
  · refine ⟨z, ?_, h0'⟩
    rw [h0', add_zero] at hz
    exact hz
  · have hpz : bV p z = 0 := by
      rw [h1'] at hz
      have hcancel : bV p z + 1 = 0 + 1 := by rw [zero_add]; exact hz
      exact add_right_cancel hcancel
    refine ⟨y + z, ?_, ?_⟩
    · rw [hbV.add_right, hy, hpz, add_zero]
    · rw [hbV.add_right, h1, h1']
      exact CharTwo.add_self_eq_zero 1

/-- **The placed adapted normal form.**  `frattiniFrameAdaptedModelEquiv` with a third vector
`n` steered into the middle plane: the `⟨1⟩` slot is still the Labute vector `e`, the `ω`-vector
`t` still spans the diagonal `(1,1)` of the first hyperbolic plane, and `n` now has middle-plane
coordinates `(1, 0)` — i.e. it evaluates to `1` on the dual `σ`-generator and to `0` on the dual
`x₀`-generator.

The single extra hypothesis is `b n t = 1`.  It already forces the independence of `n` from `e`
and `t` (a vector in `span{e, t}` pairs to `0` with `t`), so no separate independence input is
needed; §4 shows it is also necessary. -/
theorem frattiniFrameAdaptedModelEquiv_placed [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e t n : W}
    (he : ∀ w, b e w = b w w) (he1 : b e e = 1) (hte : b t e = 0) (htne : t ≠ 0)
    (hnt : b n t = 1) {h : ℕ} (hcard : Nat.card W = 2 ^ (2 * h + 3)) :
    ∃ Φ : W ≃ₗ[ZMod 2] Model h,
      (∀ x y, b x y = modelGram h (Φ x) (Φ y)) ∧
        Φ e = (1, 0) ∧ Φ t = (0, ((1, 1), 0)) ∧
          (Φ n).2.1.1 = 1 ∧ (Φ n).2.1.2 = 0 := by
  classical
  have h2W : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
  have hsq : ∀ c : ZMod 2, c * c = c := by decide
  -- `t` and the diagonal-kernel component of `n` both lie in the kernel
  have htt : b t t = 0 := by rw [← he t, hb.symm]; exact hte
  have het : b e t = 0 := by rw [hb.symm]; exact hte
  set tK : cupKer hb := ⟨t, htt⟩ with htKdef
  have htKne : tK ≠ 0 := fun hzero ↦ htne (congrArg Subtype.val hzero)
  have hnKmem : n + (b e n) • e ∈ cupKer hb := by
    show b _ _ = 0
    rw [hb.diag_add, hb.smul_left, hb.smul_right, he1, mul_one, hsq, he,
      CharTwo.add_self_eq_zero]
  set nK : cupKer hb := ⟨n + (b e n) • e, hnKmem⟩ with hnKdef
  have hnKt : b (nK : W) t = 1 := by
    show b (n + (b e n) • e) t = 1
    rw [hb.add_left, hb.smul_left, het, mul_zero, add_zero]
    exact hnt
  have hbK := isSymplectic_cupKer hb hnd he he1
  have hsumne : tK + nK ≠ 0 := by
    intro hzero
    have hzeroW : t + ((nK : W)) = 0 := congrArg Subtype.val hzero
    have hval : b (t + (nK : W)) t = 0 := by rw [hzeroW]; exact hb.zero_left t
    rw [hb.add_left, htt, hnKt, zero_add] at hval
    exact absurd hval (by decide)
  -- the hyperbolic partner, chosen to miss `nK`
  obtain ⟨w', hw', hw'n⟩ := exists_pairing_one_zero hbK htKne hsumne
  have hw't : b (w' : W) t = 1 := by rw [hb.symm]; exact hw'
  have hw'nK : b (w' : W) (nK : W) = 0 := by rw [hb.symm]; exact hw'n
  -- split along the pair `(v, w) = (w', w' + t)`, which sees `t` at coordinates `(1, 1)`
  set v : cupKer hb := w' with hvdef
  set w : cupKer hb := w' + tK with hwdef
  have hvw : b (v : W) (w : W) = 1 := by
    show b (w' : W) ((w' : W) + t) = 1
    rw [hb.add_right, hw't]
    have hself : b (w' : W) (w' : W) = 0 := w'.2
    rw [hself, zero_add]
  set e1 := hypSplitEquiv hbK hvw with he1def
  have hPsymp := isSymplectic_restrict hbK hvw
  haveI : Finite (cupKer hb) := Subtype.finite
  haveI : Finite (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK v w) := Subtype.finite
  obtain ⟨m, φ', hφ'⟩ := exists_symplectic_equiv _ hPsymp
  have hm : m = h := by
    have hc1 : Nat.card W = 2 * Nat.card (cupKer hb) := by
      rw [Nat.card_congr (cupSplitEquiv hb he he1).toEquiv, Nat.card_prod]
      simp
    have hc2 : Nat.card (cupKer hb) = 4 *
        Nat.card (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK v w) := by
      rw [Nat.card_congr e1.toEquiv, Nat.card_prod]
      simp
    have hc3 : Nat.card
        (hypPerp (fun x y : cupKer hb ↦ b (x : W) (y : W)) hbK v w) = 4 ^ m := by
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
  have hφ₀n : φ₀ n = (b e n, nK) := by
    refine Prod.ext rfl (Subtype.ext ?_)
    rfl
  have he1nK : e1 nK = ((1, 0), (e1 nK).2) := by
    refine Prod.ext (Prod.ext ?_ ?_) rfl
    · show b (w : W) (nK : W) = 1
      show b ((w' : W) + t) (nK : W) = 1
      rw [hb.add_left, hw'nK, hb.symm t (nK : W), hnKt, zero_add]
    · show b (v : W) (nK : W) = 0
      exact hw'nK
  refine ⟨Φ, ?_, ?_, ?_, ?_, ?_⟩
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
      have hwtK : b (w : W) (tK : W) = 1 := by
        show b ((w' : W) + t) t = 1
        rw [hb.add_left, hw't, htt, add_zero]
      have hvtK : b (v : W) (tK : W) = 1 := hw't
      refine Prod.ext (Prod.ext ?_ ?_) (Subtype.ext ?_)
      · exact hwtK
      · exact hvtK
      · show tK + (b (w : W) (tK : W)) • v + (b (v : W) (tK : W)) • w = 0
        rw [hwtK, hvtK, one_smul, one_smul]
        show tK + w' + (w' + tK) = 0
        have hh : tK + w' + (w' + tK) = (tK + tK) + (w' + w') := by abel
        rw [hh, GQ2.Dyadic.Certificates.module_zmod2_two_torsion,
          GQ2.Dyadic.Certificates.module_zmod2_two_torsion, add_zero]
    rw [hΦapp t, h0, h1]
    simp
  · rw [hΦapp n, hφ₀n]
    show (e1 nK).1.1 = 1
    rw [he1nK]
  · rw [hΦapp n, hφ₀n]
    show (e1 nK).1.2 = 0
    rw [he1nK]

end Placed

/-! ## §4 Sharpness: the two marked rows *are* one cup value

For every cup-adapted frame the constructor table pins `τ`'s middle-plane coordinates at
`(1, 1)`; the model Gram therefore reads `b(τ, ν̄)` as the *sum* of `ν̄`'s two middle-plane
coordinates.  So the marked rows `(1, 0)` are attainable exactly when `b(τ, ν̄) = 1`.  In
particular §2's independence statement, while true, is **not** sufficient. -/

section Sharp

open GQ2.HilbertSymbol

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- Serre's `ω` row of an element, read off its cyclotomic value. -/
theorem toAdd_omegaCharacterKTwo_of_chi {g : maxProPQuotient 2 (GalK K)} {u : ℤ_[2]ˣ}
    {r : ZMod 8} (hg : chiCycKTwo (K := K) g = u)
    (hu : PadicInt.toZModPow 3 ((u : ℤ_[2]ˣ) : ℤ_[2]) = r) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterKTwo (K := K) g) = omegaResidue r := by
  show Multiplicative.toAdd (unitsModEightOmega
    (Units.map (PadicInt.toZModPow 3).toMonoidHom (chiCycKTwo (K := K) g))) = _
  rw [hg]
  exact frattiniFrame_omega_of_val hu

variable {h : ℕ}

theorem frame_omega_sigma (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterKTwo (K := K) (F.generators 0)) = 1 := by
  rw [toAdd_omegaCharacterKTwo_of_chi F.sigma frattiniFrame_Sval_modEight]
  exact omegaResidue_table.2.2.1

theorem frame_omega_x0 (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterKTwo (K := K) (F.generators 1)) = 1 := by
  rw [toAdd_omegaCharacterKTwo_of_chi F.x0 frattiniFrame_rootX_modEight]
  exact omegaResidue_table.2.2.1

theorem frame_omega_x1 (F : SqCyclotomicFrattiniFrame K h) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterKTwo (K := K) (F.generators 2)) = 0 := by
  rw [toAdd_omegaCharacterKTwo_of_chi F.x1 frattiniFrame_Yval_modEight]
  exact omegaResidue_table.2.2.2

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
theorem frame_omega_ker {g : maxProPQuotient 2 (GalK K)}
    (hg : g ∈ (chiCycKTwo (K := K)).toMonoidHom.ker) :
    Multiplicative.toAdd (cyclotomicModEightOmegaCharacterKTwo (K := K) g) = 0 := by
  have hone : PadicInt.toZModPow 3 (((1 : ℤ_[2]ˣ) : ℤ_[2])) = (1 : ZMod 8) := by
    rw [Units.val_one, map_one]
  rw [toAdd_omegaCharacterKTwo_of_chi (MonoidHom.mem_ker.mp hg) hone]
  exact omegaResidue_table.1

/-- **The sharp identity.**  In any cup-adapted frame the cup value of the `ω` row against the
unramified class is the sum of the unramified class's two core rows.  The `τ`-coordinates
`(1,1)` come from `ω(S) = ω(X) = 1`, `ω(Y) = 0` and `ω(1) = 0`; nothing about `ν̄` is used. -/
theorem frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted) :
    frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K)) (nuUrModTwoClassKTwo B) =
      frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) +
        frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 1) := by
  have hc := hcup (cyclotomicModEightOmegaCharacterKTwo (K := K)) (nuUrModTwoKTwo B)
  refine hc.trans ?_
  rw [GQ2.ContCoh.sqRelatorQuadraticInitialGram_eq]
  simp only [frame_omega_sigma F, frame_omega_x0 F, frame_omega_x1 F,
    frame_omega_ker (F.handleU _), frame_omega_ker (F.handleV _), zero_mul, one_mul,
    add_zero, zero_add, Finset.sum_const_zero]
  show Multiplicative.toAdd (nuUrModTwoKTwo B (F.generators 1)) +
      Multiplicative.toAdd (nuUrModTwoKTwo B (F.generators 0)) = _
  exact add_comm _ _

/-- **The two marked rows force the cup value** (frame form). -/
theorem frattiniFrameCup_omega_nuUrModTwo_eq_one_of_evals (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hsigma : frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) = 1)
    (hx0 : frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 1) = 0) :
    frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K)) (nuUrModTwoClassKTwo B) = 1 := by
  rw [frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted B F hcup, hsigma, hx0, add_zero]

/-- **The two marked rows force the cup value** (exact-`ν` form): a cup-adapted frame whose two
core generators carry the standard unramified rows exists only if `b(τ, ν̄) = 1`. -/
theorem frattiniFrameCup_omega_nuUrModTwo_eq_one_of_nuRows (B : MarkedRecip R K)
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hsigma : nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (F.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K)) (nuUrModTwoClassKTwo B) = 1 := by
  refine frattiniFrameCup_omega_nuUrModTwo_eq_one_of_evals B F hcup ?_ ?_
  · rw [frattiniFrameEval_nuUrModTwoClassKTwo, hsigma, toAdd_ofAdd, map_one]
  · rw [frattiniFrameEval_nuUrModTwoClassKTwo, hx0, toAdd_ofAdd, map_zero]

/-- **Independence is not sufficient.**  If the cup value is `0` then *no* cup-adapted frame
carries the two marked rows, however `ν̄` sits relative to `κ` and `τ`.  Together with §3 (which
places the rows as soon as the cup value is `1`) this makes the placement *equivalent* to the
single `𝔽₂` datum `b(τ, ν̄)`. -/
theorem not_isCupAdapted_and_nuRows_of_cup_eq_zero (B : MarkedRecip R K)
    (hzero : frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K))
      (nuUrModTwoClassKTwo B) = 0) (F : SqCyclotomicFrattiniFrame K h) :
    ¬ (F.IsCupAdapted ∧ nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2])) := by
  rintro ⟨hcup, hsigma, hx0⟩
  have hone := frattiniFrameCup_omega_nuUrModTwo_eq_one_of_nuRows B F hcup hsigma hx0
  rw [hzero] at hone
  exact absurd hone (by decide)

/-- **The residual arithmetic input**, as a `def`-shaped `Prop` (never an axiom): the cup value
`b_K([2], [u]) = 1`, i.e. the Hilbert symbol `(2, u)_K = −1` for `u` the unramified unit.
Arithmetically `(2, u)_K = (−1)^{v(2)} = (−1)^{e(K/ℚ₂)}`, and `e` is odd whenever `[K : ℚ₂]` is;
§4 shows the datum is *necessary*, §5 that it is sufficient. -/
def NuUrOmegaCupOne (B : MarkedRecip R K) : Prop :=
  frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K)) (nuUrModTwoClassKTwo B) = 1

omit [T2Space (GalK K)] in
/-- The cup datum re-proves §2 on its own: every element of `span{κ, τ}` pairs to `0` with `τ`
(`b(τ, κ) = 0` is `cupFormK_cyclotomicModEightOmega_modFour`, and `b(τ, τ) = b(κ, τ) = 0` by the
Labute identity), so `b(τ, ν̄) = 1` already separates `ν̄` from the span.  This is why §3 needs no
independence hypothesis beyond its cup value. -/
theorem nuUrModTwoClassKTwo_ne_smul_add_smul_of_cupOne (B : MarkedRecip R K)
    (hcup : NuUrOmegaCupOne B) (a c : ZMod 2) :
    nuUrModTwoClassKTwo B ≠
      a • cyclotomicModFourClassKTwo (K := K) +
        c • cyclotomicModEightOmegaClassKTwo (K := K) := by
  have hb := isCupFormFp2_frattiniFrameCup (K := K)
  have hτκ : frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K))
      (cyclotomicModFourClassKTwo (K := K)) = 0 := frattiniFrameCup_omega_modFour (K := K)
  have hττ : frattiniFrameCup (cyclotomicModEightOmegaClassKTwo (K := K))
      (cyclotomicModEightOmegaClassKTwo (K := K)) = 0 := by
    rw [← frattiniFrameCup_kappa (K := K), hb.symm]
    exact hτκ
  intro hcon
  rw [NuUrOmegaCupOne, hcon, hb.add_right, hb.smul_right, hb.smul_right, hτκ, hττ,
    mul_zero, mul_zero, add_zero] at hcup
  exact absurd hcup (by decide)

end Sharp

/-! ## §5 The marked Frattini-frame supply

The placed adaptation of §3, run through the frame construction, gives the two **mod-2** rows;
the Frattini-coset square shift of `GammaLSylowPreimagePivotNu` §2 upgrades them to the exact
rows without moving any cyclotomic value, any level-two class, or the cup adaptation. -/

section Supply

open GQ2.HilbertSymbol

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Every element of `Multiplicative 𝔽₂` squares to `1`; this is why mod-two characters cannot
see a square shift. -/
theorem mul_self_multiplicative_zmodTwo (x : Multiplicative (ZMod 2)) : x * x = 1 := by
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_mul, toAdd_one]
  exact CharTwo.add_self_eq_zero _

/-- **Square shift of a Frattini frame.**  Multiplying the generators by squares moves nothing
the frame records: squares die in `λ₂` (`frattiniFrame_levelTwo_sq`), so the level-two range and
hence generation are literally unchanged, and the cyclotomic table is preserved by hypothesis —
which is exactly the shape `exists_squareShift_nuUrKTwo_eq_*` delivers. -/
def squareShiftFrame {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (s : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i)) :
    SqCyclotomicFrattiniFrame K h where
  generators i := F.generators i * (s i * s i)
  sigma := (hs 0).trans F.sigma
  x0 := (hs 1).trans F.x0
  x1 := (hs 2).trans F.x1
  handleU j := by
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (F.generators (SqCore.sqHandleIdxU j) *
      (s (SqCore.sqHandleIdxU j) * s (SqCore.sqHandleIdxU j))) = 1
    rw [hs]
    exact MonoidHom.mem_ker.mp (F.handleU j)
  handleV j := by
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (F.generators (SqCore.sqHandleIdxV j) *
      (s (SqCore.sqHandleIdxV j) * s (SqCore.sqHandleIdxV j))) = 1
    rw [hs]
    exact MonoidHom.mem_ker.mp (F.handleV j)
  levelTwoGen := by
    have hlevel : ∀ i, levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i * (s i * s i)) =
        levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i) := by
      intro i
      rw [map_mul, map_mul, frattiniFrame_levelTwo_sq, mul_one]
    rw [show (Set.range fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2
          (F.generators i * (s i * s i))) =
        Set.range (fun i ↦ levelMk (maxProPQuotient 2 (GalK K)) 2 (F.generators i)) from
      congrArg Set.range (funext hlevel)]
    exact F.levelTwoGen

@[simp] theorem squareShiftFrame_generators {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (s : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i)) (i : Fin (SqCore.sqRank h)) :
    (squareShiftFrame F s hs).generators i = F.generators i * (s i * s i) := rfl

/-- Cup adaptation survives a square shift: it is a statement about mod-two characters, and
those are blind to squares. -/
theorem isCupAdapted_squareShiftFrame {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (s : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K))
    (hs : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i)) (hcup : F.IsCupAdapted) :
    (squareShiftFrame F s hs).IsCupAdapted := by
  have hval : ∀ (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
      (i : Fin (SqCore.sqRank h)),
      c ((squareShiftFrame F s hs).generators i) = c (F.generators i) := by
    intro c i
    rw [squareShiftFrame_generators, map_mul, map_mul, mul_self_multiplicative_zmodTwo, mul_one]
  intro c d
  simp only [hval]
  exact hcup c d

/-- **From the mod-2 rows to the exact rows.**  A cup-adapted frame whose unramified evaluations
on the two core generators are `1` and `0` can be square-shifted to one carrying the *exact*
rows `ν(σ) = 1`, `ν(x₀) = 0`. -/
theorem exists_isCupAdapted_nuRows_of_evals (B : MarkedRecip R K) (hr : B.r = 0) {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hcup : F.IsCupAdapted)
    (hsigma : frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) = 1)
    (hx0 : frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 1) = 0) :
    ∃ F' : SqCyclotomicFrattiniFrame K h, F'.IsCupAdapted ∧
      nuUrKTwo B (F'.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F'.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
  classical
  obtain ⟨g0, hg0chi, hg0nu⟩ := exists_squareShift_nuUrKTwo_eq_one B hr (F.generators 0)
    (isUnit_toAdd_nuUrKTwo_of_eval_eq_one B hsigma)
  obtain ⟨m, hm⟩ := even_toAdd_nuUrKTwo_of_eval_eq_zero B hx0
  obtain ⟨g1, hg1chi, hg1nu⟩ := exists_squareShift_nuUrKTwo_eq_zero B hr (F.generators 1) m hm
  have hzne : (0 : Fin (SqCore.sqRank h)) ≠ 1 := by
    intro hcon
    have hval := congrArg Fin.val hcon
    rw [SqCore.sqVal_zero, SqCore.sqVal_one] at hval
    exact absurd hval (by decide)
  set s : Fin (SqCore.sqRank h) → maxProPQuotient 2 (GalK K) :=
    fun i ↦ if i = 0 then g0 else if i = 1 then g1 else 1 with hsdef
  have hs0 : s 0 = g0 := by rw [hsdef]; exact if_pos rfl
  have hs1 : s 1 = g1 := by
    rw [hsdef]
    show (if (1 : Fin (SqCore.sqRank h)) = 0 then g0 else
      if (1 : Fin (SqCore.sqRank h)) = 1 then g1 else 1) = g1
    rw [if_neg (Ne.symm hzne), if_pos rfl]
  have hchi : ∀ i, chiCycKTwo (K := K) (F.generators i * (s i * s i)) =
      chiCycKTwo (K := K) (F.generators i) := by
    intro i
    by_cases h0 : i = 0
    · subst h0
      rw [hs0]
      exact hg0chi
    · by_cases h1 : i = 1
      · subst h1
        rw [hs1]
        exact hg1chi
      · have hsi : s i = 1 := by
          rw [hsdef]
          show (if i = 0 then g0 else if i = 1 then g1 else 1) = 1
          rw [if_neg h0, if_neg h1]
        rw [hsi, map_mul, map_mul, map_one, one_mul, mul_one]
  refine ⟨squareShiftFrame F s hchi, isCupAdapted_squareShiftFrame F s hchi hcup, ?_, ?_⟩
  · rw [squareShiftFrame_generators, hs0]
    exact hg0nu
  · rw [squareShiftFrame_generators, hs1]
    exact hg1nu

/-- **The placed frame supply.**  For every odd-degree `K`, over the cup datum
`NuUrOmegaCupOne`, there is a cup-adapted Frattini frame whose unramified evaluations on the two
core generators are `1` and `0`.  This is `oddDegreeSqCyclotomicFrattiniFrameSupply_holds` with
the hyperbolic splitting chosen by §3 instead of arbitrarily. -/
theorem exists_isCupAdapted_evals_of_cupOne (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hcup : NuUrOmegaCupOne B) :
    ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2), F.IsCupAdapted ∧
      frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 0) = 1 ∧
        frattiniFrameEval (nuUrModTwoClassKTwo B) (F.generators 1) = 0 := by
  classical
  obtain ⟨k, hk⟩ := id hodd
  rw [show (Module.finrank ℚ_[2] K - 1) / 2 = k from by omega]
  have hfin : Finite (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) := by
    apply Nat.finite_of_card_ne_zero
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K)]
    positivity
  haveI := hfin
  have hcard : Nat.card (H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)) = 2 ^ (2 * k + 3) := by
    rw [card_H1_zmodTwo_maxProTwoGalK (K := K),
      show Module.finrank ℚ_[2] K + 2 = 2 * k + 3 from by omega]
  have hnt : frattiniFrameCup (K := K) (nuUrModTwoClassKTwo B)
      (cyclotomicModEightOmegaClassKTwo (K := K)) = 1 := by
    rw [(isCupFormFp2_frattiniFrameCup (K := K)).symm]
    exact hcup
  obtain ⟨Φ, hGram, hΦκ, hΦτ, hΦν0, hΦν1⟩ :=
    frattiniFrameAdaptedModelEquiv_placed (isCupFormFp2_frattiniFrameCup (K := K))
      (nondegFp2_frattiniFrameCup (K := K)) (frattiniFrameCup_kappa (K := K))
      (frattiniFrameCup_kappa_self (K := K) hodd) (frattiniFrameCup_omega_modFour (K := K))
      (cyclotomicModEightOmegaClassKTwo_ne_zero B hodd) hnt hcard
  choose gens' hgens' using fun i : Fin (SqCore.sqRank k) ↦
    frattiniFrameEval_realizable (K := K) hfin
      ((modelCoordL k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)).comp Φ.toLinearMap)
  have hD : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens' i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x ↦ hgens' i x
  have hsupply := SqCyclotomicStageTuple.oddDegreeGalKSq_sharpExactLevelFibreLiftSupply B hodd
  have hmatch4 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModFourParity
          (Units.map (PadicInt.toZModPow 2).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦκ]
    exact frattiniFrame_match_parity k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  have hmatch8 : ∀ i : Fin (SqCore.sqRank k),
      frattiniFrameEval (cyclotomicModEightOmegaClassKTwo (K := K)) (gens' i) =
        Multiplicative.toAdd (unitsModEightOmega
          (Units.map (PadicInt.toZModPow 3).toMonoidHom (frattiniFrameTarget k i))) := by
    intro i
    rw [hD i, hΦτ]
    exact frattiniFrame_match_omega k (GQ2.ContCoh.sqInitialAlphabetEquiv k i)
  choose gens hχ hlevel using fun i : Fin (SqCore.sqRank k) ↦
    frattiniFrameExactLift (K := K) hsupply (gens' i) (frattiniFrameTarget k i)
      (hmatch4 i) (hmatch8 i)
  have hD2 : ∀ (i : Fin (SqCore.sqRank k)) (x : H1 (maxProPQuotient 2 (GalK K)) (ZMod 2)),
      frattiniFrameEval x (gens i) =
        modelCoordAt k (GQ2.ContCoh.sqInitialAlphabetEquiv k i) (Φ x) := fun i x ↦
    (frattiniFrameEval_eq_of_levelMk_eq x (hlevel i)).trans (hD i x)
  refine ⟨⟨gens, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [hχ 0, frattiniFrameTarget_zero]
  · rw [hχ 1, frattiniFrameTarget_one]
  · rw [hχ 2, frattiniFrameTarget_two]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxU j)) = 1
    rw [hχ (SqCore.sqHandleIdxU j), frattiniFrameTarget_handleU]
  · intro j
    rw [MonoidHom.mem_ker]
    show chiCycKTwo (K := K) (gens (SqCore.sqHandleIdxV j)) = 1
    rw [hχ (SqCore.sqHandleIdxV j), frattiniFrameTarget_handleV]
  · by_contra hne
    haveI hFfin : Finite (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      finite_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K) isProP_maxProPQuotient 2
    haveI hFdisc : DiscreteTopology (levelQuot (maxProPQuotient 2 (GalK K)) 2) :=
      discreteTopology_levelQuot _ (maxProTwoGalK_isTopologicallyFinGen K)
        isProP_maxProPQuotient 2
    obtain ⟨c, hcH, hcne⟩ := frattiniFrame_exists_modTwo_character
      (frattiniFrame_levelTwo_mul_comm (maxProPQuotient 2 (GalK K)))
      (frattiniFrame_levelTwo_sq (maxProPQuotient 2 (GalK K))) hne
    set cQ : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)) :=
      ⟨c.comp (levelMk (maxProPQuotient 2 (GalK K)) 2), by
        have h1 : Continuous c := continuous_of_discreteTopology
        exact h1.comp (continuous_levelMk (maxProPQuotient 2 (GalK K)) 2)⟩ with hcQ
    have hvanish : ∀ i, frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) (gens i) = 0 := by
      intro i
      rw [frattiniFrameEval_characterClass]
      show Multiplicative.toAdd (c (levelMk (maxProPQuotient 2 (GalK K)) 2 (gens i))) = 0
      rw [hcH _ (Subgroup.subset_closure ⟨i, rfl⟩)]
      rfl
    have hΦ0 : Φ (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) = 0 := by
      apply modelCoordAt_eq_zero
      intro s
      have hs := hvanish ((GQ2.ContCoh.sqInitialAlphabetEquiv k).symm s)
      rw [hD2] at hs
      rwa [Equiv.apply_symm_apply] at hs
    have hcc0 : SqCyclotomicFrattiniFrame.characterClass (K := K) cQ = 0 := by
      have hs := congrArg Φ.symm hΦ0
      rwa [LinearEquiv.symm_apply_apply, map_zero] at hs
    apply hcne
    apply MonoidHom.ext
    intro f
    obtain ⟨g, rfl⟩ := levelMk_surjective (maxProPQuotient 2 (GalK K)) 2 f
    have hg : frattiniFrameEval
        (SqCyclotomicFrattiniFrame.characterClass (K := K) cQ) g =
          Multiplicative.toAdd (cQ g) := frattiniFrameEval_characterClass cQ g
    rw [hcc0, frattiniFrameEval_zero] at hg
    show c (levelMk (maxProPQuotient 2 (GalK K)) 2 g) = 1
    have hone : cQ g = 1 := by
      apply Multiplicative.toAdd.injective
      rw [← hg]
      rfl
    exact hone
  · show ∀ c d : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)),
      FieldData.cupFormK K
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
          (h1MaxProTwoEquivGalK (K := K)
            (SqCyclotomicFrattiniFrame.characterClass (K := K) d)) =
        GQ2.ContCoh.sqRelatorQuadraticInitialGram k
          (fun i j ↦ Multiplicative.toAdd (c (gens i)) * Multiplicative.toAdd (d (gens j)))
    intro c d
    have h1 := hGram (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) d)
    refine h1.trans ?_
    rw [← sqRelatorQuadraticInitialGram_modelCoord]
    congr 1
    funext i j
    rw [← hD2 i (SqCyclotomicFrattiniFrame.characterClass (K := K) c),
      ← hD2 j (SqCyclotomicFrattiniFrame.characterClass (K := K) d),
      frattiniFrameEval_characterClass, frattiniFrameEval_characterClass]
  · show frattiniFrameEval (nuUrModTwoClassKTwo B) (gens 0) = 1
    rw [hD2 0, GQ2.ContCoh.sqInitialAlphabetEquiv_zero, modelCoordAt_inl_zero]
    exact hΦν0
  · show frattiniFrameEval (nuUrModTwoClassKTwo B) (gens 1) = 0
    rw [hD2 1, GQ2.ContCoh.sqInitialAlphabetEquiv_one, modelCoordAt_inl_one]
    exact hΦν1

/-- **The marked Frattini-frame supply**, exact rows included: for every odd-degree `K` at the
type-`L` level `r = 0`, over `NuUrOmegaCupOne`, there is a cup-adapted Frattini frame whose two
core generators carry `ν(σ) = 1` and `ν(x₀) = 0`.

By §4 the cup hypothesis is not only sufficient but necessary, so this is the exact frame-level
form of the P3 selection. -/
theorem exists_isCupAdapted_nuRows_of_cupOne (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (hcup : NuUrOmegaCupOne B) :
    ∃ F : SqCyclotomicFrattiniFrame K ((Module.finrank ℚ_[2] K - 1) / 2), F.IsCupAdapted ∧
      nuUrKTwo B (F.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]) ∧
        nuUrKTwo B (F.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2]) := by
  obtain ⟨F, hFcup, hFsigma, hFx0⟩ := exists_isCupAdapted_evals_of_cupOne B hodd hcup
  exact exists_isCupAdapted_nuRows_of_evals B hr F hFcup hFsigma hFx0

end Supply

/-! ## §6 Assembly: `SqMarkedForwardSupply`

Odd-degree Demushkin rigidity makes the forward map of a generator package bijective and *is*
the equivalence, so the package's generators are literally the images of `σ` and `x₀`.  The
marked supply is therefore a marked forward-generator package, and §5 supplies everything about
such a package except the two presentation clauses (the improved relator and topological
generation) which the campaign's stage lane owns. -/

section Assembly

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- **The assembly step.**  A forward-generator package whose two core generators carry the
standard unramified rows produces `SqMarkedForwardSupply`: in odd degree the forward map is
bijective by equal-rank Demushkin rigidity, the bundled equivalence is that very map, and
`forward_gen` sends `σ ↦ generators 0`, `x₀ ↦ generators 1`. -/
theorem sqMarkedForwardSupply_of_forwardGeneratorData (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (D : SqCyclotomicForwardGeneratorData ((Module.finrank ℚ_[2] K - 1) / 2)
      (chiCycKTwo (K := K)))
    (hsigma : nuUrKTwo B (D.generators 0) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (D.generators 1) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) := by
  have hgen : ∀ i, D.forwardContinuousMulEquiv_oddDegree hodd (SqCore.sqGen _ i) =
      D.generators i := fun i ↦ D.forward_gen isProP_maxProPQuotient i
  refine ⟨D.forwardContinuousMulEquiv_oddDegree hodd, ?_, ?_, ?_⟩
  · refine (orientationMatches_chiSq_iff_generatorValues (chiCycKTwo (K := K)) _).2 ?_
    exact
      { sigma := by rw [SqCore.dsqSigma, hgen]; exact D.sigma
        x0 := by rw [SqCore.dsqX0, hgen]; exact D.x0
        x1 := by rw [SqCore.dsqX1, hgen]; exact D.x1
        handleU := fun j ↦ by rw [hgen]; exact D.handleU j
        handleV := fun j ↦ by rw [hgen]; exact D.handleV j }
  · rw [SqCore.dsqSigma, hgen]
    exact hsigma
  · rw [SqCore.dsqX0, hgen]
    exact hx0

/-- A Frattini frame promotes to a forward-generator package as soon as its own generators kill
the improved relator and generate topologically. -/
def forwardGeneratorDataOfFrame {h : ℕ} (F : SqCyclotomicFrattiniFrame K h)
    (hrel : SqCore.sqRelWord F.generators = 1)
    (htop : (Subgroup.closure (Set.range F.generators)).topologicalClosure = ⊤) :
    SqCyclotomicForwardGeneratorData h (chiCycKTwo (K := K)) where
  generators := F.generators
  relation := hrel
  topGen := htop
  sigma := F.sigma
  x0 := F.x0
  x1 := F.x1
  handleU j := MonoidHom.mem_ker.mp (F.handleU j)
  handleV j := MonoidHom.mem_ker.mp (F.handleV j)

@[simp] theorem forwardGeneratorDataOfFrame_generators {h : ℕ}
    (F : SqCyclotomicFrattiniFrame K h) (hrel : SqCore.sqRelWord F.generators = 1)
    (htop : (Subgroup.closure (Set.range F.generators)).topologicalClosure = ⊤) :
    (forwardGeneratorDataOfFrame F hrel htop).generators = F.generators := rfl

/-- **The open presentation clause, in the shape §5 feeds it**: a cup-adapted Frattini frame's
own generators kill the improved relator globally and generate topologically.

Its level-three shadow is already a theorem (`OddDegreeSqLevelThreeRelationRealization`); the
remaining stages are the campaign's `SqKernelAdaptedDefectSupply` lane, which is orthogonal to
P3 and does not mention `ν`.  The point of stating it *frame-first* is that the compactness
selection inside `forwardGeneratorData_of_finiteLevel` forgets which generators it chose, so the
existing chain cannot be asked to keep the marked pair. -/
def SqCupAdaptedFramePresentation (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)] : Prop :=
  ∀ (h : ℕ) (F : SqCyclotomicFrattiniFrame K h), F.IsCupAdapted →
    SqCore.sqRelWord F.generators = 1 ∧
      (Subgroup.closure (Set.range F.generators)).topologicalClosure = ⊤

/-- **The marked forward supply for odd-degree `K`.**  Over the two named residuals — the cup
datum `NuUrOmegaCupOne` (shown *necessary* in §4) and the presentation clause
`SqCupAdaptedFramePresentation` (P3-independent, owned by the stage lane) — every odd-degree
field at the type-`L` level `r = 0` carries `SqMarkedForwardSupply`, and hence, with the handle
binder, the `L_sq` marked-core certificate. -/
theorem oddDegreeGalKSqMarkedForwardSupply (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (hcup : NuUrOmegaCupOne B)
    (hpres : SqCupAdaptedFramePresentation K) :
    SqMarkedForwardSupply B ((Module.finrank ℚ_[2] K - 1) / 2) := by
  obtain ⟨F, hFcup, hFsigma, hFx0⟩ := exists_isCupAdapted_nuRows_of_cupOne B hodd hr hcup
  obtain ⟨hrel, htop⟩ := hpres _ F hFcup
  exact sqMarkedForwardSupply_of_forwardGeneratorData B hodd
    (forwardGeneratorDataOfFrame F hrel htop) hFsigma hFx0

/-- The certificate over the same residuals, with the strengthened (core-fixing) handle
binder — the endpoint `marked_matching_certificate_KTwoSq_of_supply` consumes. -/
theorem nonempty_markedCoreCertificate_of_cupOne_of_presentation (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (c : ℤ_[2])
    (hMix : SqCore.SqHandleMixFixesCore ((Module.finrank ℚ_[2] K - 1) / 2) c)
    (hcup : NuUrOmegaCupOne B) (hpres : SqCupAdaptedFramePresentation K) :
    Nonempty (MarkedCoreCertificateKTwoSq B ((Module.finrank ℚ_[2] K - 1) / 2)) :=
  marked_matching_certificate_KTwoSq_of_supply B _ c hMix
    (oddDegreeGalKSqMarkedForwardSupply B hodd hr hcup hpres)

end Assembly

end MarkedFrame

end

#print axioms MarkedFrame.redTwo_eq_zero_iff
#print axioms MarkedFrame.redTwo_eq_one_iff
#print axioms MarkedFrame.nuUrModTwoClassKTwo
#print axioms MarkedFrame.nuUrModTwoClassKTwo_ne_smul_add_smul
#print axioms MarkedFrame.exists_pairing_one_zero
#print axioms MarkedFrame.frattiniFrameAdaptedModelEquiv_placed
#print axioms MarkedFrame.frattiniFrameCup_omega_nuUrModTwo_eq_of_isCupAdapted
#print axioms MarkedFrame.frattiniFrameCup_omega_nuUrModTwo_eq_one_of_nuRows
#print axioms MarkedFrame.not_isCupAdapted_and_nuRows_of_cup_eq_zero
#print axioms MarkedFrame.NuUrOmegaCupOne
#print axioms MarkedFrame.nuUrModTwoClassKTwo_ne_smul_add_smul_of_cupOne
#print axioms MarkedFrame.squareShiftFrame
#print axioms MarkedFrame.isCupAdapted_squareShiftFrame
#print axioms MarkedFrame.exists_isCupAdapted_nuRows_of_evals
#print axioms MarkedFrame.exists_isCupAdapted_evals_of_cupOne
#print axioms MarkedFrame.exists_isCupAdapted_nuRows_of_cupOne
#print axioms MarkedFrame.forwardGeneratorDataOfFrame
#print axioms MarkedFrame.SqCupAdaptedFramePresentation
#print axioms MarkedFrame.sqMarkedForwardSupply_of_forwardGeneratorData
#print axioms MarkedFrame.oddDegreeGalKSqMarkedForwardSupply
#print axioms MarkedFrame.nonempty_markedCoreCertificate_of_cupOne_of_presentation

end GQ2.Dyadic.LSquare
