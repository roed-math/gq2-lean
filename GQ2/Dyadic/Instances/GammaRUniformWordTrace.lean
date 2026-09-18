/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaRUniformStokesSupply
import GQ2.Dyadic.Instances.WordPhaseSeam

/-!
# Scalar trace orientation for an arbitrary uniformly Stokes source

At every nonzero even resolving level the tame scalar row is the tau indicator. The endpoint
forces the second row to agree with it. Thus the scalar word trace and its flexible continuous
comparison are independent of both the branch word and the resolving level. Uniform Stokes
duality supplies the scalar H2 cardinality, making the trace an actual orientation.
-/

namespace GQ2.Dyadic.UniformStokesSupply
noncomputable section

open GQ2 GQ2.FoxH GQ2.ContCoh
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates GQ2.Dyadic.RowActionImage GQ2.Dyadic.LSquare
open GQ2.Dyadic.Instances.WordPhaseSeam

attribute [local instance] Count.heisTopologicalSpace Count.heisDiscreteTopology

variable {n q : ℕ} {R : PWord (Generator n)}
  {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

private theorem two_dvd_level {N : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) :
    2 ∣ N := (Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hN).mpr
      (Nat.one_le_iff_ne_zero.mpr hNtwo)

/-- Any level resolver has the same mod-two exponent row at all nonzero even levels. -/
theorem level_heisEps_eq (L : LevelResolver n q R wOf)
    {N N' : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0)
    (hN' : N' ≠ 0) (hN'two : N'.factorization 2 ≠ 0)
    (k : Fin 2) (i : Generator n) : heisEps i (wOf N k) = heisEps i (wOf N' k) := by
  have hres := L.resolves (Multiplicative (ZMod 2)) N hN
    (fun x ↦ (CycTest.orderOf_dvd 2 x).trans (two_dvd_level hN hNtwo))
  have hres' := L.resolves (Multiplicative (ZMod 2)) N' hN'
    (fun x ↦ (CycTest.orderOf_dvd 2 x).trans (two_dvd_level hN' hN'two))
  exact (hres (fun j ↦ Multiplicative.ofAdd (if j = i then 1 else 0)) k).trans
    (hres' (fun j ↦ Multiplicative.ofAdd (if j = i then 1 else 0)) k).symm

/-- The resolved tame row is the tau indicator, without restrictions on the branch word. -/
theorem level_tame_heisEps (L : LevelResolver n q R wOf) (hq : Even q)
    {N : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0) (i : Generator n) :
    Multiplicative.toAdd (heisEps i (wOf N 0)) =
      if Generator.tau = i then (1 : ZMod 2) else 0 := by
  have hres := L.resolves (Multiplicative (ZMod 2)) N hN
    (fun x ↦ (CycTest.orderOf_dvd 2 x).trans (two_dvd_level hN hNtwo))
  have H := hres (fun j ↦ Multiplicative.ofAdd (if j = i then 1 else 0)) 0
  change heisEps i (wOf N 0) = _ at H
  rw [H, gammaFam_zero, tameRelW, PWord.eval_mul,
    PWord.eval_conj, PWord.eval_inv, PWord.eval_zpow, PWord.eval_gen, PWord.eval_gen,
    conjR_eq_self_of_comm]
  change Multiplicative.toAdd ((Multiplicative.ofAdd (if Generator.tau = i then 1 else 0) :
    Multiplicative (ZMod 2)) * (Multiplicative.ofAdd (if Generator.tau = i then 1 else 0) ^
      (q : ℤ))⁻¹) = _
  simp only [toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, neg_zero, add_zero]

/-- The endpoint identifies both scalar rows with the tame tau indicator. -/
theorem level_heisEps (L : LevelResolver n q R wOf) (hq : Even q)
    {N : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0)
    (k : Fin 2) (i : Generator n) :
    Multiplicative.toAdd (heisEps i (wOf N k)) =
      if Generator.tau = i then (1 : ZMod 2) else 0 := by
  have hzero := level_tame_heisEps L hq hN hNtwo i
  have hend := L.endpoint N hN hNtwo i
  rw [Fin.sum_univ_two, hzero] at hend
  fin_cases k
  · exact hzero
  · exact wPs_eq_of_add_eq_zero _ _ hend

/-- The entire scalar differential is the pair of tau coordinates. -/
theorem level_scalar_d1 (L : LevelResolver n q R wOf) (hq : Even q)
    {N : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0)
    {C : Type*} [Group C] [DistribMulAction C (ZMod 2)]
    (c : Generator n → C) (x : Generator n → ZMod 2) :
    heisD1 c (wOf N) x = ![x Generator.tau, x Generator.tau] := by
  funext k
  rw [heisD1_zmod2_apply_eq_eps]
  have hsum : ∀ i : Generator n,
      Multiplicative.toAdd (heisEps i (wOf N k)) * x i =
        if Generator.tau = i then x i else 0 := by
    intro i
    rw [level_heisEps L hq hN hNtwo k i]
    split <;> simp
  rw [Finset.sum_congr rfl (fun i _ ↦ hsum i), Finset.sum_ite_eq,
    if_pos (Finset.mem_univ Generator.tau)]
  fin_cases k <;> simp

/-- Coordinate sum is the scalar word-H2 trace at every nonzero even level. -/
def levelWordH2TraceEquiv (L : LevelResolver n q R wOf) (hq : Even q)
    {N : ℕ} (hN : N ≠ 0) (hNtwo : N.factorization 2 ≠ 0)
    {C : Type*} [Group C] [DistribMulAction C (ZMod 2)] (c : Generator n → C)
    (hr : ∀ k, FreeGroup.lift c (wOf N k) = 1) :
    WordH2 c (wOf N) (ZMod 2) ≃+ ZMod 2 :=
  wPsWordH2TraceEquiv c _ hr (L.endpoint N hN hNtwo)
    ⟨fun i ↦ if i = Generator.tau then 1 else 0, by
      rw [level_scalar_d1 L hq hN hNtwo c]
      simp⟩

section Orientation

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((GammaR n q R) : Type) (ZMod 2)]
  [ContinuousSMul ((GammaR n q R) : Type) (ZMod 2)]
  [DistribMulAction C (ZMod 2)]

/-- The scalar flexible resolver system follows from the uniform level interface alone. -/
def scalarFlexibleResolverSystem (L : LevelResolver n q R wOf)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C) :
    ∀ (V : OpenNormalSubgroup ((GammaR n q R) : Type))
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (((GammaR n q R) : Type) ⧸ V.toSubgroup) (ZMod 2) :=
        DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := ZMod 2) (gammaFam n q R)
        (fun i ↦ rho (gammaGen n q R i)) (wOf (4 * Monoid.exponent C))
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gammaGen n q R i)) := by
  intro V hV
  letI : DistribMulAction (((GammaR n q R) : Type) ⧸ V.toSubgroup) (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
  let Q := WordLift (ZMod 2) (((GammaR n q R) : Type) ⧸ V.toSubgroup)
  have hlevel := fourMulExponent_ne_zero_and_even Q
  refine
    { word := wOf (4 * Monoid.exponent Q)
      resolves := L.resolves Q _ hlevel.1
        (fun x ↦ (Monoid.order_dvd_exponent x).trans (dvd_mul_left _ _))
      range_eq := ?_ }
  exact congrArg AddMonoidHom.range
    (heisD1_zmod2_eq_of_eps _ _ _ _ (fun k i ↦ level_heisEps_eq L
      hlevel.1 hlevel.2 (fourMulExponent_ne_zero_and_even C).1
        (fourMulExponent_ne_zero_and_even C).2 k i))

/-- The word-generic continuous-to-word scalar H2 map. -/
def scalarH2WordFlexible (L : LevelResolver n q R wOf)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C)
    (hcompat : ∀ (g : ((GammaR n q R) : Type)) (s : ZMod 2), g • s = rho g • s) :
    H2 ((GammaR n q R) : Type) (ZMod 2) →+
      WordH2 (fun i ↦ rho (gammaGen n q R i)) (wOf (4 * Monoid.exponent C)) (ZMod 2) :=
  globalModuleH2WordFlexible (isAdmissibleMarkedPresentation_gammaR n q R)
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (scalarFlexibleResolverSystem L rho)

theorem scalarH2WordFlexible_injective (L : LevelResolver n q R wOf)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C)
    (hcompat : ∀ (g : ((GammaR n q R) : Type)) (s : ZMod 2), g • s = rho g • s) :
    Function.Injective (scalarH2WordFlexible L rho hcompat) :=
  globalModuleH2WordFlexible_injective (isAdmissibleMarkedPresentation_gammaR n q R)
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (scalarFlexibleResolverSystem L rho)

end Orientation

section CanonicalOrientation

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

local instance : TopologicalSpace (ZMod 2) := ⊥
local instance : DiscreteTopology (ZMod 2) := ⟨rfl⟩
local instance : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
local instance : DistribMulAction ((GammaR n q R) : Type) (ZMod 2) := scalarActionZmodTwo _
local instance : ContinuousSMul ((GammaR n q R) : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- Uniform Stokes supply makes the canonical scalar trace an actual H2 orientation. -/
def scalarH2TraceEquiv (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R) (hq : Even q)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C) :
    H2 ((GammaR n q R) : Type) (ZMod 2) ≃+ ZMod 2 := by
  let f := scalarH2WordFlexible S.level rho (fun _ _ ↦ rfl)
  have hinj : Function.Injective f := scalarH2WordFlexible_injective S.level rho (fun _ _ ↦ rfl)
  have hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gammaGen n q R i))
      (wOf (4 * Monoid.exponent C) k) = 1 :=
    lower_rel (A := ZMod 2) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR n q R) (S.resolvesWord (by decide))
  let trace := levelWordH2TraceEquiv S.level hq
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
    (fun i ↦ rho (gammaGen n q R i)) hr
  letI : Finite (H2 ((GammaR n q R) : Type) (ZMod 2)) := Finite.of_injective f hinj
  letI : Fintype (H2 ((GammaR n q R) : Type) (ZMod 2)) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (gammaGen n q R i))
      (wOf (4 * Monoid.exponent C)) (ZMod 2)) := Fintype.ofFinite _
  have hcard : Nat.card (H2 ((GammaR n q R) : Type) (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (gammaGen n q R i))
        (wOf (4 * Monoid.exponent C)) (ZMod 2)) := by
    calc
      _ = 2 := S.cardH2 hspec
      _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
      _ = _ := (Nat.card_congr trace.toEquiv).symm
  have hbij : Function.Bijective f :=
    (Fintype.bijective_iff_injective_and_card f).mpr
      ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩
  exact (AddEquiv.ofBijective f hbij).trans trace

/-- The canonical orientation reads the sum of the actual profinite relator obstructions. -/
@[simp] theorem scalarH2TraceEquiv_mk (S : UniformStokesSupply n q R wOf)
    (hspec : TameSpec.TameSpecializes n q R) (hq : Even q)
    (rho : ContinuousMonoidHom ((GammaR n q R) : Type) C)
    (f : Z2 ((GammaR n q R) : Type) (ZMod 2)) :
    scalarH2TraceEquiv S hspec hq rho (H2mk ((GammaR n q R) : Type) (ZMod 2) f) =
      ∑ k, moduleObsFun (gammaFam n q R) (gammaGen n q R) rho (fun _ _ ↦ rfl) f k := rfl

end CanonicalOrientation

#print axioms level_heisEps_eq
#print axioms level_scalar_d1
#print axioms levelWordH2TraceEquiv
#print axioms scalarH2WordFlexible_injective
#print axioms scalarH2TraceEquiv
#print axioms scalarH2TraceEquiv_mk

end
end GQ2.Dyadic.UniformStokesSupply
