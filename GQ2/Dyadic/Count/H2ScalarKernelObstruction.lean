/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SylowPreimageDevissage

/-!
# The explicit cocycle obstruction behind degree-two coefficient right exactness

The scalar-kernel endpoint of the Sylow-preimage devissage is a genuine degree-three
condition.  This file expresses that condition without introducing an `H³` API.

Given a surjective equivariant coefficient map `g : A →+ B` and a continuous `B`-valued
two-cocycle `z`, choose a pointwise lift `l : G × G → A`.  Its defect `dTwo l` takes values
in `ker g`.  The class of `z` has an `A`-valued lift precisely when this defect is the `dTwo`
of a continuous kernel-valued two-cochain.  The main theorem below proves that vanishing of
this explicit obstruction for every `z` is equivalent to `H2RightExactAt g`.

No cardinality or two-torsion hypothesis is needed for the equivalence.  In the scalar-kernel
application, `ker g` has two elements, so this is exactly the cochain-level form of the
connecting obstruction in `H³(G, ZMod 2)`.
-/

namespace GQ2.ContCoh

noncomputable section

variable {G A B : Type*}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [DistribMulAction G B] [ContinuousSMul G B]

/-- A chosen pointwise coefficient lift of a two-cocycle along a surjection.  It need not be
a cocycle: its `dTwo` is the obstruction studied below. -/
def h2CoeffLiftFun (g : A →+ B) (hsurj : Function.Surjective g) (z : Z2 G B) : G × G → A :=
  fun p ↦ (hsurj (z.1 p)).choose

@[simp] theorem g_h2CoeffLiftFun
    (g : A →+ B) (hsurj : Function.Surjective g) (z : Z2 G B) (p : G × G) :
    g (h2CoeffLiftFun g hsurj z p) = z.1 p :=
  (hsurj (z.1 p)).choose_spec

theorem h2CoeffLiftFun_continuous
    (g : A →+ B) (hsurj : Function.Surjective g) (z : Z2 G B) :
    Continuous (h2CoeffLiftFun g hsurj z) :=
  by
    change Continuous (fun p ↦ (hsurj (z.1 p)).choose)
    have hlift : Continuous (fun b : B ↦ (hsurj b).choose : B → A) :=
      continuous_of_discreteTopology
    exact hlift.comp (mem_Z2_iff.mp z.2).1

/-- Representative-level liftability of a continuous two-cocycle. -/
def H2CocycleLiftable (g : A →+ B) (z : Z2 G B) : Prop :=
  ∃ w : Z2 G A, ∀ p : G × G, g (w.1 p) = z.1 p

/-- The explicit obstruction attached to a chosen pointwise lift of `z` vanishes.

The witness `k` is kernel-valued and has the same `dTwo` as the chosen lift.  Therefore
`h2CoeffLiftFun g hsurj z - k` is an actual `A`-valued cocycle lifting `z`. -/
def H2LiftObstructionVanishesAt
    (g : A →+ B) (hsurj : Function.Surjective g) (z : Z2 G B) : Prop :=
  ∃ k : G × G → A, Continuous k ∧
    (∀ p : G × G, g (k p) = 0) ∧
    dTwo G A k = dTwo G A (h2CoeffLiftFun g hsurj z)

/-- Vanishing of the explicit lift defect for every continuous two-cocycle. -/
def H2LiftObstructionVanishes
    (g : A →+ B) (hsurj : Function.Surjective g) : Prop :=
  ∀ z : Z2 G B, H2LiftObstructionVanishesAt g hsurj z

/-- The differential of a continuous two-cochain is continuous. -/
theorem continuous_dTwo (phi : G × G → A) (hphi : Continuous phi) :
    Continuous (dTwo G A phi) := by
  exact (((continuous_fst.smul (hphi.comp continuous_snd)).sub
    (hphi.comp ((continuous_fst.mul (continuous_fst.comp continuous_snd)).prodMk
      (continuous_snd.comp continuous_snd)))).add
    (hphi.comp (continuous_fst.prodMk
      ((continuous_fst.comp continuous_snd).mul (continuous_snd.comp continuous_snd))))).sub
    (hphi.comp (continuous_fst.prodMk (continuous_fst.comp continuous_snd)))

/-- Naturality of `dTwo` under an equivariant additive coefficient map. -/
theorem map_dTwo_apply
    (g : A →+ B) (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (phi : G × G → A) (t : G × G × G) :
    g (dTwo G A phi t) = dTwo G B (fun p ↦ g (phi p)) t := by
  change g (t.1 • phi (t.2.1, t.2.2) - phi (t.1 * t.2.1, t.2.2) +
      phi (t.1, t.2.1 * t.2.2) - phi (t.1, t.2.1)) =
    t.1 • g (phi (t.2.1, t.2.2)) - g (phi (t.1 * t.2.1, t.2.2)) +
      g (phi (t.1, t.2.1 * t.2.2)) - g (phi (t.1, t.2.1))
  rw [map_sub, map_add, map_sub, hg]

/-- The next inhomogeneous differential, introduced locally in order to state the exact
chain-level vanishing condition needed by the scalar-kernel tail. -/
def dThree : (G × G × G → A) →+ (G × G × G × G → A) where
  toFun phi := fun t ↦
    t.1 • phi (t.2.1, t.2.2.1, t.2.2.2) -
      phi (t.1 * t.2.1, t.2.2.1, t.2.2.2) +
      phi (t.1, t.2.1 * t.2.2.1, t.2.2.2) -
      phi (t.1, t.2.1, t.2.2.1 * t.2.2.2) +
      phi (t.1, t.2.1, t.2.2.1)
  map_zero' := by funext t; simp
  map_add' a b := by funext t; simp only [smul_add, Pi.add_apply]; abel

/-- `dThree ∘ dTwo = 0`, the chain-complex identity that makes a chosen-lift defect a
three-cocycle. -/
theorem dThree_comp_dTwo : (dThree (G := G) (A := A)).comp (dTwo G A) = 0 := by
  ext phi t
  simp only [AddMonoidHom.comp_apply, dThree, dTwo, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    mul_smul, smul_sub, smul_add, mul_assoc, AddMonoidHom.zero_apply, Pi.zero_apply]
  abel

/-- The defect of a pointwise lift of a cocycle is kernel-valued. -/
theorem g_h2CoeffLiftDefect
    (g : A →+ B) (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) (z : Z2 G B) (t : G × G × G) :
    g (dTwo G A (h2CoeffLiftFun g hsurj z) t) = 0 := by
  rw [map_dTwo_apply g hg]
  change t.1 • g (h2CoeffLiftFun g hsurj z (t.2.1, t.2.2)) -
      g (h2CoeffLiftFun g hsurj z (t.1 * t.2.1, t.2.2)) +
      g (h2CoeffLiftFun g hsurj z (t.1, t.2.1 * t.2.2)) -
      g (h2CoeffLiftFun g hsurj z (t.1, t.2.1)) = 0
  rw [g_h2CoeffLiftFun, g_h2CoeffLiftFun, g_h2CoeffLiftFun, g_h2CoeffLiftFun]
  change dTwo G B z.1 t = 0
  exact congrFun (AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp z.2).2) t

/-- A concrete, presentation/chain-level version of `H³(G, ker g) = 0`: every continuous
kernel-valued three-cocycle is the `dTwo` of a continuous kernel-valued two-cochain.

This avoids postulating an abstract `H³` object, while retaining exactly the cocycle and
continuity conditions needed by the long-exact-sequence argument. -/
def KernelHThreeCocyclesExact (g : A →+ B) : Prop :=
  ∀ F : G × G × G → A, Continuous F → dThree (G := G) (A := A) F = 0 →
    (∀ t, g (F t) = 0) →
    ∃ k : G × G → A, Continuous k ∧ (∀ p, g (k p) = 0) ∧ dTwo G A k = F

/-- The explicit defect vanishes exactly when the cocycle has a representative-level lift. -/
theorem h2CocycleLiftable_iff_obstructionVanishesAt
    (g : A →+ B) (hsurj : Function.Surjective g) (z : Z2 G B) :
    H2CocycleLiftable g z ↔ H2LiftObstructionVanishesAt g hsurj z := by
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨h2CoeffLiftFun g hsurj z - w.1,
      (h2CoeffLiftFun_continuous g hsurj z).sub (mem_Z2_iff.mp w.2).1, ?_, ?_⟩
    · intro p
      rw [Pi.sub_apply, map_sub, g_h2CoeffLiftFun, hw, sub_self]
    · rw [map_sub]
      have hwzero : dTwo G A w.1 = 0 :=
        AddMonoidHom.mem_ker.mp (AddSubgroup.mem_inf.mp w.2).2
      rw [hwzero, sub_zero]
  · rintro ⟨k, hkC, hgk, hk⟩
    let w : Z2 G A := ⟨h2CoeffLiftFun g hsurj z - k, by
      refine AddSubgroup.mem_inf.mpr ⟨(h2CoeffLiftFun_continuous g hsurj z).sub hkC, ?_⟩
      rw [AddMonoidHom.mem_ker, map_sub, hk, sub_self]⟩
    refine ⟨w, fun p ↦ ?_⟩
    change g (h2CoeffLiftFun g hsurj z p - k p) = z.1 p
    rw [map_sub, g_h2CoeffLiftFun, hgk, sub_zero]

/-- Exactness of the kernel complex in degree three kills every chosen-lift obstruction. -/
theorem H2LiftObstructionVanishes.of_kernelHThreeCocyclesExact
    (g : A →+ B) (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) (hkernel : KernelHThreeCocyclesExact (G := G) g) :
    H2LiftObstructionVanishes (G := G) g hsurj := by
  intro z
  exact hkernel (dTwo G A (h2CoeffLiftFun g hsurj z))
    (continuous_dTwo _ (h2CoeffLiftFun_continuous g hsurj z))
    (by
      rw [← AddMonoidHom.comp_apply, dThree_comp_dTwo, AddMonoidHom.zero_apply])
    (g_h2CoeffLiftDefect g hg hsurj z)

section Equivariant

/-- For a surjective coefficient map, surjectivity on `H²` is equivalent to lifting every
continuous two-cocycle on the nose.  In the reverse direction, equality modulo a `B`-valued
coboundary is upgraded to equality of cocycles by pointwise lifting its continuous
one-cochain. -/
theorem h2RightExactAt_iff_forall_cocycleLiftable
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) :
    H2RightExactAt g hgC hg ↔ ∀ z : Z2 G B, H2CocycleLiftable g z := by
  constructor
  · intro hright z
    obtain ⟨x, hx⟩ := hright (H2mk G B z)
    obtain ⟨w, rfl⟩ := H2mk_surjective (G := G) (M := A) x
    rw [mapCoeff2_H2mk_coeff] at hx
    let gw : Z2 G B :=
      Z2comap (ContinuousMonoidHom.id G) g hgC (fun c a ↦ hg c a) w
    change H2mk G B gw = H2mk G B z at hx
    change (QuotientAddGroup.mk gw : H2 G B) = QuotientAddGroup.mk z at hx
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at hx
    change (gw - z).1 ∈ B2 G B at hx
    obtain ⟨psi, hpsiC, hpsi⟩ := hx
    let psiLift : G → A := fun c ↦ (hsurj (psi c)).choose
    have hpsiLiftC : Continuous psiLift := by
      have hlift : Continuous (fun b : B ↦ (hsurj b).choose : B → A) :=
        continuous_of_discreteTopology
      exact hlift.comp hpsiC
    have hgpsiLift : ∀ c : G, g (psiLift c) = psi c :=
      fun c ↦ (hsurj (psi c)).choose_spec
    have hbmem : dOne G A psiLift ∈ B2 G A :=
      ⟨psiLift, hpsiLiftC, rfl⟩
    let b : Z2 G A := ⟨dOne G A psiLift, B2_le_Z2 hbmem⟩
    let w' : Z2 G A := w - b
    refine ⟨w', fun p ↦ ?_⟩
    have hdOne : g (dOne G A psiLift p) = dOne G B psi p := by
      change g (p.1 • psiLift p.2 - psiLift (p.1 * p.2) + psiLift p.1) =
        p.1 • psi p.2 - psi (p.1 * p.2) + psi p.1
      rw [map_add, map_sub, hg, hgpsiLift, hgpsiLift, hgpsiLift]
    have hpsiPoint := congrFun hpsi p
    change dOne G B psi p = gw.1 p - z.1 p at hpsiPoint
    change g (w.1 p - dOne G A psiLift p) = z.1 p
    rw [map_sub, hdOne, hpsiPoint]
    change gw.1 p - (gw.1 p - z.1 p) = z.1 p
    abel
  · intro hlift y
    obtain ⟨z, rfl⟩ := H2mk_surjective (G := G) (M := B) y
    obtain ⟨w, hw⟩ := hlift z
    refine ⟨H2mk G A w, ?_⟩
    rw [mapCoeff2_H2mk_coeff]
    apply congrArg (H2mk G B)
    apply Subtype.ext
    funext p
    exact hw p

/-- The degree-two right-exactness tail is exactly vanishing of the explicit chosen-lift
defect for every continuous two-cocycle.  This is the sharp `H³`-free endpoint of the
current degree-`≤ 2` cohomology API. -/
theorem h2RightExactAt_iff_obstructionVanishes
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) :
    H2RightExactAt g hgC hg ↔ H2LiftObstructionVanishes (G := G) g hsurj := by
  rw [h2RightExactAt_iff_forall_cocycleLiftable g hgC hg hsurj]
  constructor
  · intro h z
    exact (h2CocycleLiftable_iff_obstructionVanishesAt g hsurj z).mp (h z)
  · intro h z
    exact (h2CocycleLiftable_iff_obstructionVanishesAt g hsurj z).mpr (h z)

/-- The explicit degree-three kernel criterion implies degree-two coefficient right
exactness. -/
theorem H2RightExactAt.of_kernelHThreeCocyclesExact
    (g : A →+ B) (hgC : Continuous g)
    (hg : ∀ (c : G) (a : A), g (c • a) = c • g a)
    (hsurj : Function.Surjective g) (hkernel : KernelHThreeCocyclesExact (G := G) g) :
    H2RightExactAt g hgC hg :=
  (h2RightExactAt_iff_obstructionVanishes g hgC hg hsurj).mpr
    (H2LiftObstructionVanishes.of_kernelHThreeCocyclesExact g hg hsurj hkernel)

end Equivariant

end

noncomputable section

variable {G C : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The residual scalar-kernel tail phrased using the smallest explicit obstruction: only
chosen lift defects of continuous two-cocycles are required to have kernel primitives. -/
def TwoGroupActionScalarKernelObstructionTail
    (rho : ContinuousMonoidHom G C) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
    [DistribMulAction C A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
    [DistribMulAction C B]
    (g : A →+ B)
    (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      ∀ hsurj : Function.Surjective g, Nat.card ↑g.ker = 2 →
        H2LiftObstructionVanishes (G := G) g hsurj

/-- The scalar-kernel `H²` tail is equivalent, not merely reducible, to vanishing of the
explicit chosen-lift defects. -/
theorem twoGroupActionScalarKernelH2Tail_iff_obstructionTail
    (rho : ContinuousMonoidHom G C) :
    TwoGroupActionScalarKernelH2Tail rho ↔
      TwoGroupActionScalarKernelObstructionTail rho := by
  constructor
  · intro T A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG hgC hcompatA hcompatB
      hA₂ hB₂ hsurj hker
    exact (h2RightExactAt_iff_obstructionVanishes
      g continuous_of_discreteTopology hgG hsurj).mp
      (T A B g hgG hgC hcompatA hcompatB hA₂ hB₂ hsurj hker)
  · intro T A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG hgC hcompatA hcompatB
      hA₂ hB₂ hsurj hker
    exact (h2RightExactAt_iff_obstructionVanishes
      g continuous_of_discreteTopology hgG hsurj).mpr
      (T A B g hgG hgC hcompatA hcompatB hA₂ hB₂ hsurj hker)

/-- The scalar-kernel tail restated as an explicit degree-three kernel-complex condition.

The finite-image compatibility and two-element-kernel hypotheses match
`TwoGroupActionScalarKernelH2Tail` exactly.  They are retained here so that a presentation or
duality argument can target the precise endpoint left by the Sylow devissage. -/
def TwoGroupActionScalarKernelHThreeCocyclesExact
    (rho : ContinuousMonoidHom G C) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
    [DistribMulAction C A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
    [DistribMulAction C B]
    (g : A →+ B)
    (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective g → Nat.card ↑g.ker = 2 →
        KernelHThreeCocyclesExact (G := G) g

/-- Exactness of the explicit kernel complex in degree three discharges the residual
scalar-kernel `H²` tail. -/
theorem twoGroupActionScalarKernelH2Tail_of_kernelHThreeCocyclesExact
    (rho : ContinuousMonoidHom G C)
    (T : TwoGroupActionScalarKernelHThreeCocyclesExact rho) :
    TwoGroupActionScalarKernelH2Tail rho := by
  intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG hgC hcompatA hcompatB
    hA₂ hB₂ hsurj hker
  exact H2RightExactAt.of_kernelHThreeCocyclesExact
    g continuous_of_discreteTopology hgG hsurj
    (T A B g hgG hgC hcompatA hcompatB hA₂ hB₂ hsurj hker)

end

end GQ2.ContCoh
