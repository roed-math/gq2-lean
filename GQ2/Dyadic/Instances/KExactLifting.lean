/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.KAnalytic

/-!
# The `liftsOver_card` clause at `G_K`  (package P5, clause 1)

`ExactLiftingSemantics`'s first conjunct — `#LiftsOverK(ρ) = SN.mMult #M_B` — over an arbitrary
profinite source carrying Tate duality at `2` and a degree-`d` local Euler characteristic, and
its specialization to `G_K` for every finite-dimensional `K/ℚ₂`.

## Why this is not the `ℚ₂` proof retyped

`GQ2/MStageCount.lean`'s `liftsOver_card_local` proves `#LiftsOver(ρ) = #M_B²`.  The `²` is
`d + 1` at `d = 1`; at `[K : ℚ₂] = n` the correct value is `#M_B^{n+1}`, so a verbatim `K`-clone
of the `ℚ₂` statement is **false** for `n > 1` (`GQ2/Dyadic/LiftingDualityG.lean:274` states the
refutation, and `card_Z1_zmod2_galK_eq_eight_iff` Lean-checks it).  The degree enters through
exactly one step, `card_Z1_eqG`, and the packet's numeric leaf that absorbs it is
`SourceNumerics.mMult`, which at `standardNumerics n` is `M ↦ M^{n+1}`.

## The two halves

The `ℚ₂` proof splits into nonemptiness of the lift fibre and a `Z¹`-torsor count, and the split
survives verbatim:

* **nonemptiness** (§1) — `#H²(Γ, M_B) = #(M_B^∨)^{Y_C} = 1`, so the factor set of a continuous
  set-section of `π_{BC}` is a coboundary and the correction is a genuine lift.  This half is
  **degree-free**: `card_H2_eq_fixedPtsG` uses the Euler hypothesis only to finitize `H²`, and
  `card_fixedPts_MB_dual` is the source-free `lemma_7_1_dual` bridge.
* **the count** (§2) — `card_liftsOverK_eq_card_Z1` (already source-generic, CB-3) followed by
  `card_Z1_eqG`, which is where `d` appears.

Nothing here re-derives the `M_B` module pack: CB-3's public copies (`mbCommGroup`, `mbSec`,
`mbConjActC`, `mbConjEq`, `mb_add_self`, `card_fixedPts_MB_dual`) are imported and used.

## Relation to `liftsOver_cardN`

`GQ2/Dyadic/Count/Lifts.lean`'s `liftsOver_cardN` proves the same value from the **word** side:
an admissible marked presentation of `Γ` plus a Stokes-duality payload.  That route is
unavailable at `G_K` — the whole campaign exists to prove that `Γ_{R_K}` presents `G_K` — so the
arithmetic side needs the duality route, which is this file.  The two agree on the value, which
is the point of the comparison.

Axioms: every declaration in this file is parametrized over the bundle `Dl` and the hypothesis
`hE`, so all of them print exactly the standard three (measured).  B6 and B7 enter only at the
`G_K` instantiation, in `KExactLiftingGalK.lean`.  No new axiom, no `sorry`.
-/

namespace GQ2.Dyadic.Count

open GQ2 GQ2.SectionEight GQ2.FoxH ContCoh
open LiftingDualityG

/-! ## §0 A continuity helper

The one-line factorization used at every module below: an action pulled back along a continuous
map to a discrete group is continuous.  (`Count/LocalDuality.lean` has a `private` twin.) -/

private theorem continuousSMul_of_pullback {G C A : Type}
    [Monoid G] [TopologicalSpace G] [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A] [SMul G A]
    (theta : ContinuousMonoidHom G C) (hcomp : ∀ (g : G) (a : A), g • a = theta g • a) :
    ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A => p.1 • p.2) =
      (fun p : C × A => p.1 • p.2) ∘ (fun p : G × A => (theta p.1, p.2)) := by
    funext p
    exact hcomp p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

section Generic

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
  {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
  {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
  {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]

/-! ## §1 Nonemptiness of the lift fibre

The `ℚ₂` argument (`GQ2/MStageCount.lean:458`) with `AbsGalQ2 ⇝ Γ` and
`card_H2_eq_fixedPts ⇝ card_H2_eq_fixedPtsG`.  No degree appears: the Euler hypothesis is
consumed only as the finiteness of `H²` inside `card_H2_eq_fixedPtsG`. -/

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`#H²(Γ, M_B) = 1`** over any source carrying Tate duality at `2`.

Tate `(0,2)` identifies `H²(Γ, M_B)` with the `Y_C`-invariant `𝔽₂`-functionals on `M_B`, and
`lemma_7_1_dual` (through CB-3's `card_fixedPts_MB_dual`) says there are none but zero. -/
theorem card_H2_MB_eq_one_of_tateDualityG {d : ℕ}
    (Dl : TateDualityG Γ 2) (hE : LocalEulerChar Γ d) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    letI := mbCommGroup RF
    letI := mbConjActC RF
    letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
    letI : DistribMulAction Γ (Additive ↥RF.MB) :=
      DistribMulAction.compHom _ ρ.1.1.toMonoidHom
    Nat.card (H2 Γ (Additive ↥RF.MB)) = 1 := by
  classical
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actG : DistribMulAction Γ (Additive ↥RF.MB) :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  have hcomp : ∀ (γ : Γ) (a : Additive ↥RF.MB), γ • a = ρ.1.1 γ • a := fun _ _ => rfl
  haveI : ContinuousSMul Γ (Additive ↥RF.MB) :=
    continuousSMul_of_pullback ρ.1.1 hcomp
  exact (card_H2_eq_fixedPtsG ρ.1.2 hcomp Dl hE (mb_add_self RF)).trans
    (card_fixedPts_MB_dual RF)

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **The lift fibre is nonempty** over any source carrying Tate duality at `2`: every lower
boundary lift `ρ : Γ ↠ C` lifts through `π_{BC}`.

The extension obstruction is the class of the factor set of a continuous set-section of
`π_{BC}`, and it lives in `#H²(Γ, M_B) = 1`. -/
theorem nonempty_liftsOverK_of_tateDualityG {d : ℕ}
    (Dl : TateDualityG Γ 2) (hE : LocalEulerChar Γ d) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nonempty (LiftsOverK RF b F ρ) := by
  classical
  haveI hMBn : RF.MB.Normal := RF.MB_normal
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actG : DistribMulAction Γ (Additive ↥RF.MB) :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  have hcomp : ∀ (γ : Γ) (a : Additive ↥RF.MB), γ • a = ρ.1.1 γ • a := fun _ _ => rfl
  haveI : ContinuousSMul Γ (Additive ↥RF.MB) :=
    continuousSMul_of_pullback ρ.1.1 hcomp
  haveI : IsTopologicalAddGroup (Additive ↥RF.MB) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  have hA₂ : ∀ a : Additive ↥RF.MB, a + a = 0 := mb_add_self RF
  -- a continuous set-section of `Y_B ↠ Y_C` under the lower map
  set sρ : Γ → RF.YB := fun γ => mbSec RF (ρ.1.1 γ) with hsρdef
  have hsρ_cont : Continuous sρ :=
    (continuous_of_discreteTopology (f := mbSec RF)).comp ρ.1.1.continuous_toFun
  have hsρ_mk : ∀ γ, RF.piBC (sρ γ) = ρ.1.1 γ := fun γ => mbSec_spec RF _
  have hsmul_s : ∀ (γ : Γ) (a : Additive ↥RF.MB),
      γ • a = Additive.ofMul (⟨sρ γ * (Additive.toMul a).1 * (sρ γ)⁻¹,
          hMBn.conj_mem _ (Additive.toMul a).2 _⟩ : ↥RF.MB) := fun _ _ => rfl
  -- the factor set `c(γ,δ) = sρ γ · sρ δ · sρ(γδ)⁻¹ ∈ M_B`
  have hc_mem : ∀ p : Γ × Γ, sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹ ∈ RF.MB := by
    intro p
    rw [← RF.ker_piBC]
    exact MonoidHom.mem_ker.mpr (by
      rw [map_mul, map_mul, map_inv, hsρ_mk, hsρ_mk, hsρ_mk, ← map_mul, mul_inv_cancel])
  set c : Γ × Γ → Additive ↥RF.MB :=
    fun p => Additive.ofMul ⟨sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹, hc_mem p⟩ with hcdef
  have hc_Z2 : c ∈ Z2 Γ (Additive ↥RF.MB) := by
    rw [mem_Z2_iff]
    refine ⟨?_, ?_⟩
    · have hg : Continuous (fun p : Γ × Γ => sρ p.1 * sρ p.2 * (sρ (p.1 * p.2))⁻¹) :=
        (continuous_of_discreteTopology (f := fun t : RF.YB × RF.YB × RF.YB =>
            t.1 * t.2.1 * t.2.2⁻¹)).comp
          ((hsρ_cont.comp continuous_fst).prodMk ((hsρ_cont.comp continuous_snd).prodMk
            (hsρ_cont.comp (continuous_fst.mul continuous_snd))))
      exact hg.subtype_mk _
    · intro x y z
      rw [hsmul_s x (c (y, z))]
      apply Additive.toMul.injective
      show (⟨sρ x * (sρ y * sρ z * (sρ (y * z))⁻¹) * (sρ x)⁻¹, _⟩ : ↥RF.MB)
          * ⟨sρ x * sρ (y * z) * (sρ (x * (y * z)))⁻¹, _⟩
        = ⟨sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹, _⟩
          * ⟨sρ x * sρ y * (sρ (x * y))⁻¹, _⟩
      rw [mul_comm (⟨sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹, _⟩ : ↥RF.MB) _]
      apply Subtype.ext
      show sρ x * (sρ y * sρ z * (sρ (y * z))⁻¹) * (sρ x)⁻¹
          * (sρ x * sρ (y * z) * (sρ (x * (y * z)))⁻¹)
        = sρ x * sρ y * (sρ (x * y))⁻¹ * (sρ (x * y) * sρ z * (sρ ((x * y) * z))⁻¹)
      rw [mul_assoc x y z]; group
  -- `#H² = 1` ⟹ `c` is a coboundary
  have hH2 : Nat.card (H2 Γ (Additive ↥RF.MB)) = 1 :=
    card_H2_MB_eq_one_of_tateDualityG Dl hE RF b F ρ
  haveI : Subsingleton (H2 Γ (Additive ↥RF.MB)) := (Nat.card_eq_one_iff_unique.mp hH2).1
  have hcB2 : c ∈ B2 Γ (Additive ↥RF.MB) := by
    have h0 : H2mk Γ (Additive ↥RF.MB) ⟨c, hc_Z2⟩ = 0 := Subsingleton.elim _ _
    exact AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨ψ, hψc, hψ⟩ := hcB2
  -- the lift `f γ = (toMul (ψ γ))⁻¹ · sρ γ`
  set ψ' : Γ → RF.YB := fun γ => (Additive.toMul (ψ γ)).1 with hψ'def
  have hψ'mem : ∀ γ, ψ' γ ∈ RF.MB := fun γ => (Additive.toMul (ψ γ)).2
  have hrel : ∀ x y : Γ,
      sρ x * ψ' y * (sρ x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x = sρ x * sρ y * (sρ (x * y))⁻¹ := by
    intro x y
    have hxy_eq : x • ψ y - ψ (x * y) + ψ x = c (x, y) := congrFun hψ (x, y)
    rw [hsmul_s x (ψ y)] at hxy_eq
    have hxy := congrArg (fun a : Additive ↥RF.MB => (Additive.toMul a).1) hxy_eq
    simpa [hcdef, hψ'def, div_eq_mul_inv, mul_assoc] using hxy
  refine ⟨⟨MonoidHom.mk' (fun γ => (ψ' γ)⁻¹ * sρ γ) (fun x y => ?_), ?_⟩, ?_⟩
  · have hcm : Commute (ψ' (x * y)) (ψ' x) := RF.MB_comm _ (hψ'mem (x * y)) _ (hψ'mem x)
    show (ψ' (x * y))⁻¹ * sρ (x * y) = (ψ' x)⁻¹ * sρ x * ((ψ' y)⁻¹ * sρ y)
    have hs_xy : sρ (x * y) = (ψ' x)⁻¹ * ψ' (x * y) * sρ x * (ψ' y)⁻¹ * sρ y := by
      have e : sρ (x * y)
          = (sρ x * ψ' y * (sρ x)⁻¹ * (ψ' (x * y))⁻¹ * ψ' x)⁻¹ * (sρ x * sρ y) := by
        rw [hrel x y]; group
      rw [e]; group
    rw [hs_xy]
    rw [show (ψ' (x * y))⁻¹ * ((ψ' x)⁻¹ * ψ' (x * y) * sρ x * (ψ' y)⁻¹ * sρ y)
        = ((ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y)) * (sρ x * (ψ' y)⁻¹ * sρ y) from by group,
      show (ψ' (x * y))⁻¹ * (ψ' x)⁻¹ * ψ' (x * y) = (ψ' x)⁻¹ from by
        rw [mul_assoc, (hcm.symm.inv_left).eq, ← mul_assoc, inv_mul_cancel, one_mul]]
    group
  · have hψ'cont : Continuous ψ' :=
      (continuous_of_discreteTopology
        (f := fun a : Additive ↥RF.MB => (Additive.toMul a).1)).comp hψc
    exact (continuous_of_discreteTopology (f := fun p : RF.YB × RF.YB => p.1⁻¹ * p.2)).comp
      (hψ'cont.prodMk hsρ_cont)
  · intro γ
    show RF.piBC ((ψ' γ)⁻¹ * sρ γ) = ρ.1.1 γ
    rw [map_mul, map_inv, MonoidHom.mem_ker.mp (RF.ker_piBC ▸ hψ'mem γ), inv_one, one_mul,
      hsρ_mk]

/-! ## §2 The count

CB-3's source-generic `Z¹`-torsor bridge, then `card_Z1_eqG`.  **This** is the step carrying the
degree: the exponent is `d + 1`, not `2`. -/

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **`#LiftsOverK(ρ) = #M_B^{d+1}`** over any source carrying Tate duality at `2` and a
degree-`d` local Euler characteristic.

⚠ The exponent is `d + 1`.  The `ℚ₂` ancestor's `#M_B²` is the `d = 1` case. -/
theorem liftsOver_card_of_tateDualityG {d : ℕ}
    (Dl : TateDualityG Γ 2) (hE : LocalEulerChar Γ d) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F ρ) = Nat.card ↥RF.MB ^ (d + 1) := by
  classical
  letI := mbCommGroup RF
  letI := mbConjActC RF
  letI : TopologicalSpace (Additive ↥RF.MB) := (inferInstance : TopologicalSpace ↥RF.MB)
  haveI : DiscreteTopology (Additive ↥RF.MB) :=
    ⟨(inferInstance : DiscreteTopology ↥RF.MB).eq_bot⟩
  haveI : Finite (Additive ↥RF.MB) := (inferInstance : Finite ↥RF.MB)
  letI actG : DistribMulAction Γ (Additive ↥RF.MB) :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  have hcomp : ∀ (γ : Γ) (a : Additive ↥RF.MB), γ • a = ρ.1.1 γ • a := fun _ _ => rfl
  haveI : ContinuousSMul Γ (Additive ↥RF.MB) :=
    continuousSMul_of_pullback ρ.1.1 hcomp
  have htorsor := card_liftsOverK_eq_card_Z1 RF b F ρ
    (nonempty_liftsOverK_of_tateDualityG Dl hE RF b F ρ)
  rw [htorsor, card_Z1_eqG ρ.1.2 hcomp Dl hE (mb_add_self RF), card_fixedPts_MB_dual RF, mul_one]
  rfl

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- **Degree-one regression.**  At `d = 1` the generic value is the frozen `ℚ₂` one, `#M_B²`
(`SectionEight.RecursionFrame.liftsOver_card_local`).  Recorded so that the exponent correction
is visibly a *generalization* of the model and not a change to it. -/
theorem liftsOver_card_of_tateDualityG_one
    (Dl : TateDualityG Γ 2) (hE : LocalEulerChar Γ 1) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F ρ) = Nat.card ↥RF.MB ^ 2 :=
  liftsOver_card_of_tateDualityG Dl hE RF b F ρ

omit [TopologicalSpace Y] [DiscreteTopology Y] in
/-- `liftsOver_card_of_tateDualityG` in the exact `SourceDataN.liftsOver_card` numeric shape:
`SN.mMult` at `SN = standardNumerics d` is `M ↦ M^{d+1}`. -/
theorem liftsOver_card_standard_of_tateDualityG {d : ℕ}
    (Dl : TateDualityG Γ 2) (hE : LocalEulerChar Γ d) (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F ρ) = (standardNumerics d).mMult (Nat.card ↥RF.MB) :=
  liftsOver_card_of_tateDualityG Dl hE RF b F ρ

end Generic

/-! ## §3 The clause, in the certificate's vocabulary -/

section FieldClause

variable {Gam : ProfiniteGrp} {d q : ℕ} {P : ProfiniteGrp}
  {nuP : ContinuousMonoidHom P Ztwo}
  [DistribMulAction (Gam : Type) (MuN 2)] [ContinuousSMul (Gam : Type) (MuN 2)]

/-- **The first `ExactLiftingSemantics` conjunct**, at a bundled profinite carrier, from a Tate
bundle and a degree-`d` local Euler characteristic. -/
theorem liftsOver_card_field_of_localDualityG
    (Dl : TateDualityG (Gam : Type) 2) (hE : LocalEulerChar (Gam : Type) d)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk)
    (b : ContinuousMonoidHom Gam ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (LiftsOverK RF b F ρ) = (standardNumerics d).mMult (Nat.card ↥RF.MB) :=
  liftsOver_card_standard_of_tateDualityG Dl hE RF b F ρ

end FieldClause

end GQ2.Dyadic.Count
