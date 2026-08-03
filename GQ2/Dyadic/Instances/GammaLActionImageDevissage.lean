/-
Copyright (c) 2026 Geoffrey Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Geoffrey Roe
-/
import GQ2.Dyadic.Instances.GammaLActionImage
import GQ2.Dyadic.Instances.LExact

/-!
# Action-image devissage for the improved L presentation

The canonical simple Stokes theorems use the actual finite action image of each coefficient.
Composition-series devissage, however, needs one fixed target and one fixed word.  The comparison
below maps two acting groups into a common action group.  Resolutions at the two original
Heisenberg targets then identify all three Stokes maps, even when the resolving integer and the
acting group change.

This lets us devissse inside the action image of an arbitrary elementary `GammaL`-module and
then transport the result to every ambient finite quotient.  The result is the previously
hypothetical `UniformPushedHsimp`, with no Tate-duality input.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count
open GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.LSqStokes

local instance actionImageHeisTopology
    {C A : Type} [Group C] [AddCommGroup A] : TopologicalSpace (HeisLift A C) := ⊥

local instance actionImageHeisDiscrete
    {C A : Type} [Group C] [AddCommGroup A] : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

section ActionTransport

variable {L C D A : Type} [Group L] [Group C] [Group D] [AddCommGroup A]
  [Finite L] [Finite C] [Finite D] [Finite A]
  [DistribMulAction L A] [DistribMulAction C A] [DistribMulAction D A]

private theorem dual_smul_eq_of_action_map (pi : L →* D)
    (hact : ∀ (g : L) (a : A), g • a = pi g • a) :
    ∀ (g : L) (lam : ElemDual A), g • lam = pi g • lam := by
  intro g lam
  apply ElemDual.ext
  intro a
  simp only [ElemDual.smul_apply]
  rw [hact]
  simp

private noncomputable def heisActionMap (pi : L →* D)
    (hact : ∀ (g : L) (a : A), g • a = pi g • a) :
    HeisLift A L →* HeisLift A D where
  toFun p := ⟨p.a, p.l, p.z, pi p.g⟩
  map_one' := by ext <;> simp
  map_mul' p r := by
    ext
    · simp [hact]
    · simp [dual_smul_eq_of_action_map pi hact]
    · simp [hact]
    · simp

set_option maxHeartbeats 800000 in
/-- Two resolved Stokes complexes with the same generator actions are identical, even when
their finite acting groups and their resolving free words differ.  A common action target is
enough; no map between the two original groups is required. -/
theorem stokesDuality_iff_of_resolvers_action_maps
    {iota rel : Type*} [Fintype iota] [DecidableEq iota] [Fintype rel]
    {W : rel → PWord iota} {m : iota → L} {c : iota → C}
    {wL wC : rel → FreeGroup iota}
    (piL : L →* D) (piC : C →* D)
    (hactL : ∀ (g : L) (a : A), g • a = piL g • a)
    (hactC : ∀ (g : C) (a : A), g • a = piC g • a)
    (hc : ∀ i, piL (m i) = piC (c i))
    (hresL : ResolvesAt W wL (HeisLift A L))
    (hresC : ResolvesAt W wC (HeisLift A C)) :
    StokesDuality m wL A ↔ StokesDuality c wC A := by
  have hd0 : heisD0 (A := A) m = heisD0 c := by
    ext a i
    simp only [heisD0_apply]
    rw [hactL, hc, ← hactC]
  have hd0D : heisD0 (A := ElemDual A) m = heisD0 c := by
    ext lam i
    simp only [heisD0_apply]
    rw [dual_smul_eq_of_action_map piL hactL,
      dual_smul_eq_of_action_map piC hactC, hc]
  have hd1 : heisD1 (A := A) m wL = heisD1 c wC := by
    apply AddMonoidHom.ext
    intro x
    funext k
    simp only [heisD1_apply]
    rw [hresL (heisGen m x 0) k, hresC (heisGen c x 0) k]
    let FL : ContinuousMonoidHom (HeisLift A L) (HeisLift A D) :=
      ⟨heisActionMap piL hactL, continuous_of_discreteTopology⟩
    let FC : ContinuousMonoidHom (HeisLift A C) (HeisLift A D) :=
      ⟨heisActionMap piC hactC, continuous_of_discreteTopology⟩
    have hmL := PWord.map_eval FL (heisGen m x 0) (W k)
    have hmC := PWord.map_eval FC (heisGen c x 0) (W k)
    have hgen : (fun i ↦ FL (heisGen m x 0 i)) =
        (fun i ↦ FC (heisGen c x 0 i)) := by
      funext i
      change heisActionMap piL hactL (heisGen m x 0 i) =
        heisActionMap piC hactC (heisGen c x 0 i)
      ext <;> simp [heisActionMap, hc]
    rw [hgen] at hmL
    have haL := congrArg HeisLift.a hmL
    have haC := congrArg HeisLift.a hmC
    change (PWord.eval (heisGen m x 0) (W k)).a =
      (PWord.eval (fun i ↦ FC (heisGen c x 0 i)) (W k)).a at haL
    change (PWord.eval (heisGen c x 0) (W k)).a =
      (PWord.eval (fun i ↦ FC (heisGen c x 0 i)) (W k)).a at haC
    exact haL.trans haC.symm
  have hd1D : heisD1 (A := ElemDual A) m wL = heisD1 c wC := by
    apply AddMonoidHom.ext
    intro y
    funext k
    rw [heisD1_apply, ← heisWord_l_eq_dual_a m 0 y,
      heisD1_apply, ← heisWord_l_eq_dual_a c 0 y]
    rw [hresL (heisGen m 0 y) k, hresC (heisGen c 0 y) k]
    let FL : ContinuousMonoidHom (HeisLift A L) (HeisLift A D) :=
      ⟨heisActionMap piL hactL, continuous_of_discreteTopology⟩
    let FC : ContinuousMonoidHom (HeisLift A C) (HeisLift A D) :=
      ⟨heisActionMap piC hactC, continuous_of_discreteTopology⟩
    have hmL := PWord.map_eval FL (heisGen m 0 y) (W k)
    have hmC := PWord.map_eval FC (heisGen c 0 y) (W k)
    have hgen : (fun i ↦ FL (heisGen m 0 y i)) =
        (fun i ↦ FC (heisGen c 0 y i)) := by
      funext i
      change heisActionMap piL hactL (heisGen m 0 y i) =
        heisActionMap piC hactC (heisGen c 0 y i)
      ext <;> simp [heisActionMap, hc]
    rw [hgen] at hmL
    have hlL := congrArg HeisLift.l hmL
    have hlC := congrArg HeisLift.l hmC
    change (PWord.eval (heisGen m 0 y) (W k)).l =
      (PWord.eval (fun i ↦ FC (heisGen c 0 y i)) (W k)).l at hlL
    change (PWord.eval (heisGen c 0 y) (W k)).l =
      (PWord.eval (fun i ↦ FC (heisGen c 0 y i)) (W k)).l at hlC
    exact hlL.trans hlC.symm
  have heta : heisEta1 (A := A) m wL = heisEta1 c wC := by
    apply AddMonoidHom.ext
    intro x
    apply ElemDual.ext
    intro y
    simp only [heisEta1_apply]
    apply Finset.sum_congr rfl
    intro k _
    rw [hresL (heisGen m x y) k, hresC (heisGen c x y) k]
    let FL : ContinuousMonoidHom (HeisLift A L) (HeisLift A D) :=
      ⟨heisActionMap piL hactL, continuous_of_discreteTopology⟩
    let FC : ContinuousMonoidHom (HeisLift A C) (HeisLift A D) :=
      ⟨heisActionMap piC hactC, continuous_of_discreteTopology⟩
    have hmL := PWord.map_eval FL (heisGen m x y) (W k)
    have hmC := PWord.map_eval FC (heisGen c x y) (W k)
    have hgen : (fun i ↦ FL (heisGen m x y i)) =
        (fun i ↦ FC (heisGen c x y i)) := by
      funext i
      change heisActionMap piL hactL (heisGen m x y i) =
        heisActionMap piC hactC (heisGen c x y i)
      ext <;> simp [heisActionMap, hc]
    rw [hgen] at hmL
    have hzL := congrArg HeisLift.z hmL
    have hzC := congrArg HeisLift.z hmC
    change (PWord.eval (heisGen m x y) (W k)).z =
      (PWord.eval (fun i ↦ FC (heisGen c x y i)) (W k)).z at hzL
    change (PWord.eval (heisGen c x y) (W k)).z =
      (PWord.eval (fun i ↦ FC (heisGen c x y i)) (W k)).z at hzC
    exact hzL.trans hzC.symm
  unfold StokesDuality
  rw [hd0, hd0D, hd1, hd1D, heta]

end ActionTransport

set_option maxHeartbeats 1200000 in
/-- A simple elementary `GammaL`-module is either unramified (`tau` acts trivially) or
ramified (`tau` has no nonzero fixed vector). -/
theorem finiteActionImage_tau_split_or_ramified_simple
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma h q : Type) M) :
    (∀ m : M, gammaGen (2 * h + 1) q (lSqW h) .tau • m = m) ∨
      (∀ m : M, gammaGen (2 * h + 1) q (lSqW h) .tau • m = m → m = 0) := by
  let t := finiteActionImageMarking h q M
  let W : AddSubgroup M :=
    { carrier := {m | t.τ • m = m}
      zero_mem' := smul_zero _
      add_mem' := fun {a b} ha hb ↦ by
        change t.τ • (a + b) = a + b
        rw [smul_add, ha, hb]
      neg_mem' := fun {a} ha ↦ by
        change t.τ • (-a) = -a
        rw [smul_neg, ha] }
  have ht : t.TameRelAt q := finiteActionImage_tameRelAt
  have hwild : ∀ (i : Fin (2 * h + 1 + 1)) (m : M), t.x i • m = m :=
    finiteActionImage_wild_smul hM₂ hsimple
  let S : Subgroup (FiniteActionImage h q M) :=
    { carrier := {c | ∀ m : M, m ∈ W → c • m ∈ W}
      one_mem' := fun m hm ↦ by simpa using hm
      mul_mem' := fun {a b} ha hb m hm ↦ by rw [mul_smul]; exact ha _ (hb m hm)
      inv_mem' := fun {a} ha m hm ↦ by
        have hφinj : Function.Injective (fun u : W ↦ (⟨a • u.1, ha u.1 u.2⟩ : W)) := by
          intro x y hxy
          exact Subtype.ext (MulAction.injective a (congrArg Subtype.val hxy))
        obtain ⟨⟨u, hu⟩, hux⟩ :=
          (Finite.injective_iff_surjective.mp hφinj) ⟨m, hm⟩
        have hum : a • u = m := congrArg Subtype.val hux
        show t.τ • (a⁻¹ • m) = a⁻¹ • m
        rw [show a⁻¹ • m = u from by rw [← hum, inv_smul_smul]]
        exact hu }
  have hσ : t.σ ∈ S := by
    intro m hm
    change t.τ • (t.σ • m) = t.σ • m
    exact tau_fixed_sigma_stable_of_tameRelAt t ht hm
  have hτ : t.τ ∈ S := by
    intro m hm
    change t.τ • m = m at hm
    show t.τ • (t.τ • m) = t.τ • m
    exact congrArg (fun x ↦ t.τ • x) hm
  have hx : ∀ i, t.x i ∈ S := by
    intro i m hm
    change t.τ • (t.x i • m) = t.x i • m
    rw [hwild i m]
    exact hm
  have hgenS : Subgroup.closure (Set.range (finiteActionImageGenerators h q M)) ≤ S := by
    rw [Subgroup.closure_le]
    rintro _ ⟨g, rfl⟩
    cases g with
    | sigma => exact hσ
    | tau => exact hτ
    | wild i => exact hx i
  rw [finiteActionImageGenerators_generate] at hgenS
  have hstable : ∀ (c : FiniteActionImage h q M) (m : M), m ∈ W → c • m ∈ W := by
    intro c
    exact hgenS (Subgroup.mem_top c)
  rcases (isSimpleModTwo_finiteActionImage hsimple).2 W hstable with hbot | htop
  · right
    intro m hm
    have hmW : m ∈ W := hm
    rw [hbot, AddSubgroup.mem_bot] at hmW
    exact hmW
  · left
    intro m
    have hmW : m ∈ W := by rw [htop]; exact AddSubgroup.mem_top m
    exact hmW

/-- The canonical action-image Stokes theorem for every simple elementary coefficient. -/
theorem finiteActionImage_stokesDuality_simple
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (gamma h q : Type) M)
    (hq : Even q) :
    StokesDuality (finiteActionImageGenerators h q M)
      (lSqFam h q
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q M)))) M := by
  rcases finiteActionImage_tau_split_or_ramified_simple hM₂ hsimple with hτ | hτfpf
  · exact finiteActionImage_stokesDuality_unramified_simple hM₂ hsimple hτ hq
  · exact finiteActionImage_stokesDuality_ramified_simple hM₂ hsimple hτfpf hq

private theorem continuousSMul_comp_finite
    {G C A : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace A] [DiscreteTopology A] [SMul C A]
    (rho : ContinuousMonoidHom G C) [SMul G A]
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) : ContinuousSMul G A := by
  constructor
  have hfac : (fun p : G × A ↦ p.1 • p.2) =
      (fun p : C × A ↦ p.1 • p.2) ∘ (fun p : G × A ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

set_option maxHeartbeats 2400000 in
/-- Fixed-word devissage on the action image of an arbitrary finite elementary `GammaL`-module. -/
theorem finiteActionImage_stokesDuality
    {h q : ℕ} {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((gamma h q : Type)) M]
    [ContinuousSMul ((gamma h q : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hq : Even q) :
    StokesDuality (finiteActionImageGenerators h q M)
      (lSqFam h q
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q M)))) M := by
  let C₀ := FiniteActionImage h q M
  let c₀ := finiteActionImageGenerators h q M
  let w₀ := lSqFam h q (omega2Exp (4 * Monoid.exponent C₀))
  have hb := resolvesAt_and_endpoint_lSqFam_uniformHeis
    (C := C₀) (A := M) hM₂ (h := h) (q := q) hq
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h)) w₀
      (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift c₀ (w₀ k) = 1 := fun k ↦
    lower_rel (A := M) (finiteActionImageHom h q M) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 * h + 1) q (lSqW h)) hresWord k
  apply stokesDuality_of_simple c₀ w₀ hr hb.2
  · intro V _ _ _ hV₂ hsimple
    letI : TopologicalSpace V := ⊥
    letI : DiscreteTopology V := ⟨rfl⟩
    letI : ContinuousSMul C₀ V := ⟨continuous_of_discreteTopology⟩
    letI : DistribMulAction ((gamma h q : Type)) V :=
      DistribMulAction.compHom V (finiteActionImageHom h q M).toMonoidHom
    letI : ContinuousSMul ((gamma h q : Type)) V :=
      continuousSMul_comp_finite (finiteActionImageHom h q M) (fun _ _ ↦ rfl)
    have hsimpleGamma : IsSimpleModTwo (gamma h q : Type) V := by
      refine ⟨hsimple.1, fun W hW ↦ hsimple.2 W ?_⟩
      intro c v hv
      obtain ⟨g, rfl⟩ :=
        (finiteActionHom (G := (gamma h q : Type)) (M := M)).toMonoidHom.rangeRestrict_surjective c
      exact hW g v hv
    have hdV := finiteActionImage_stokesDuality_simple hV₂ hsimpleGamma hq
    let D := Multiplicative (AddAut V)
    let piV : FiniteActionImage h q V →* D := Subgroup.subtype _
    let pi₀ : C₀ →* D :=
      (finiteActionHom (G := C₀) (M := V)).toMonoidHom
    have hc : ∀ i, piV (finiteActionImageGenerators h q V i) = pi₀ (c₀ i) := by
      intro i
      apply Multiplicative.toAdd.injective
      ext v
      rfl
    have hresV : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
        (lSqFam h q
          (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q V))))
        (HeisLift V (FiniteActionImage h q V)) :=
      resolvesAt_lSqFam_uniformHeis hV₂ h q
    have hres₀ : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h)) w₀
        (HeisLift V C₀) := resolvesAt_lSqFam_uniformHeis hV₂ h q
    exact (stokesDuality_iff_of_resolvers_action_maps piV pi₀
      (fun _ _ ↦ rfl) (fun g v ↦ (finiteActionHom_smul g v).symm)
      hc hresV hres₀).mp hdV
  · exact hM₂

set_option maxHeartbeats 2400000 in
/-- The proved canonical simple branches and exact word-level devissage discharge the uniform
Stokes residue used by the L exact-lifting assembly. -/
theorem uniformPushedHsimp_of_actionImage {h q : ℕ} (hq : Even q) :
    UniformPushedHsimp h q := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction ((gamma h q : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((gamma h q : Type)) A :=
    continuousSMul_comp_finite rho (fun _ _ ↦ rfl)
  have hdA := finiteActionImage_stokesDuality (h := h) (q := q) (M := A) hA₂ hq
  letI : ContinuousSMul C A := ⟨continuous_of_discreteTopology⟩
  let D := Multiplicative (AddAut A)
  let piA : FiniteActionImage h q A →* D := Subgroup.subtype _
  let piC : C →* D := (finiteActionHom (G := C) (M := A)).toMonoidHom
  have hc : ∀ i, piA (finiteActionImageGenerators h q A i) =
      piC (rho (gammaGen (2 * h + 1) q (lSqW h) i)) := by
    intro i
    apply Multiplicative.toAdd.injective
    ext a
    rfl
  have hresA : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q
        (omega2Exp (4 * Monoid.exponent (FiniteActionImage h q A))))
      (HeisLift A (FiniteActionImage h q A)) :=
    resolvesAt_lSqFam_uniformHeis hA₂ h q
  have hresC : ResolvesAt (gammaFam (2 * h + 1) q (lSqW h))
      (lSqFam h q (omega2Exp (4 * Monoid.exponent C))) (HeisLift A C) :=
    resolvesAt_lSqFam_uniformHeis hA₂ h q
  exact (stokesDuality_iff_of_resolvers_action_maps piA piC
    (fun _ _ ↦ rfl) (by
      intro g a
      change g • a = finiteActionHom (G := C) (M := A) g • a
      exact (finiteActionHom_smul g a).symm)
    hc hresA hresC).mp hdA

end


end GQ2.Dyadic.LSquare
