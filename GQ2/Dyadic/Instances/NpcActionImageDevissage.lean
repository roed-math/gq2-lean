/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaRActionImage
import GQ2.Dyadic.Instances.GammaLActionImageDevissage
import GQ2.Dyadic.Instances.NpcExact

/-!
# Fixed-word action-image devissage, and the procyclic-`N` instance

`GammaRActionImage` states the row-independent half of the `L` row's action-image argument for an
arbitrary branch word: the canonical finite action image of a coefficient, its wild triviality
and its `tau`-dichotomy on simple modules.  This file adds the second row-independent half — the
*devissage* itself — and then instantiates both at the corrected procyclic-`N` word.

The devissage is parameterized by a level-indexed resolver family
`wOf : ℕ → Fin 2 → FreeGroup (Generator n)` rather than by a single integer resolver.  That is
what the two procyclic rows need and the `L` row does not: the procyclic-`N` family carries an
`η̂` node as well as `ω₂`, so its resolver is genuinely two-valued (`Count.npcResolver`), and
the procyclic-`M` family is display-dependent on top of that.  Nothing in the devissage sees the
difference, because `LSquare.stokesDuality_iff_of_resolvers_action_maps` compares two Stokes
complexes with different acting groups *and different words*.

For the same reason the conclusion is not tied to the level `4 * Monoid.exponent C` that the `L`
row uses: `pushedStokesDuality_of_actionImage` concludes at every level killing the Heisenberg
target, which is what keeps the procyclic rows' `heisLevel`-indexed count chain reachable.

The row-specific residue left over is `SimpleActionImageStokes`, split along the `tau`-dichotomy
into an unramified and a ramified obligation.  `eq_one_of_pro2Core_sigma_offset` records why the
`L` row's unramified route (Roe's degree-one core) does not transfer to either procyclic row.

The second half of the file adds the procyclic-`N` pushed residue layer:
`NProcyclic.PushedHsimp` and `NProcyclic.UniformPushedHsimp`, both implied by the historical
`NProcyclic.Hsimp`, together with pushed replacements for `NProcyclic.stokesDuality` and
`NProcyclic.stokesDuality_T` that leave every other hypothesis and conclusion unchanged.
`NProcyclic.UniformPushedHsimp` is a re-export: its statement is `NProcyclic.UniformHsimp` in
`NpcExact`, the upstream file which restates the row's whole clause stack over the uniform
residue and therefore cannot name a definition living here.
-/

namespace GQ2.Dyadic.RowActionImage

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.Dyadic.Count GQ2.Dyadic.Certificates
open GQ2.Dyadic.LSquare (finiteActionHom finiteActionHom_smul
  stokesDuality_iff_of_resolvers_action_maps)

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The procyclic shape of the unramified branch -/

/-- **The unramified branch has a procyclic target.**  When `tau` and every wild letter act
trivially, faithfulness of the action image collapses it onto the single letter `sigma`.  This
is the structural reason the unramified obligation below is a statement about a procyclic
target and nothing more. -/
theorem actionImage_unramified_closure_sigma
    {n q : ℕ} {R : PWord (Generator n)} {M : Type}
    [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) (hsimple : IsSimpleModTwo (GammaR n q R : Type) M)
    (hτ : ∀ m : M, gammaGen n q R .tau • m = m) :
    Subgroup.closure {(actionImageMarking n q R M).σ} = ⊤ := by
  let t := actionImageMarking n q R M
  have hwild : ∀ (i : Fin (n + 1)) (m : M), t.x i • m = m :=
    actionImage_wild_smul hM₂ hsimple
  have hwild_one : ∀ i : Fin (n + 1), t.x i = 1 :=
    fun i ↦ actionImage_eq_one_of_smul_eq (t.x i) (hwild i)
  have hτ_one : t.τ = 1 := actionImage_eq_one_of_smul_eq t.τ (fun m ↦ hτ m)
  apply top_unique
  rw [← actionImageGenerators_generate (n := n) (q := q) (R := R) (M := M),
    Subgroup.closure_le]
  rintro _ ⟨g, rfl⟩
  cases g with
  | sigma => exact Subgroup.subset_closure (Set.mem_singleton _)
  | tau =>
      rw [show actionImageGenerators n q R M .tau = t.τ from rfl, hτ_one]
      exact (Subgroup.closure {t.σ}).one_mem
  | wild i =>
      rw [show actionImageGenerators n q R M (.wild i) = t.x i from rfl, hwild_one i]
      exact (Subgroup.closure {t.σ}).one_mem

/-! ## The sigma-offset obstruction to the `L` row's unramified route -/

private theorem eq_one_of_dvd_two_pow_of_odd {d k : ℕ} (hd : d ∣ 2 ^ k) (hodd : Odd d) :
    d = 1 := by
  obtain ⟨i, -, rfl⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
  rcases Nat.eq_zero_or_pos i with hi | hi
  · rw [hi, pow_zero]
  · exact absurd (Nat.even_pow.mpr ⟨even_two, hi.ne'⟩) (Nat.not_even_iff_odd.mpr hodd)

/-- **Why the `L` row's unramified route does not transfer to a sigma-offset core.**

On the `L` row the unramified branch is routed through Roe's degree-one core: with `tau` and
every wild letter acting trivially, `LSquare.finiteActionImage_core_admissibleR` gets
`x₀ = x₁ = 1`, so Roe's `Marking.Pro2Core` clause asks only that the normal closure of `{1, 1}`
be a `2`-group, which is free.  Both procyclic rows reach their core through a *triangular*
change of generators, and the offset survives the collapse of the wild letters: the
procyclic-`N` dictionary puts `x₁ * σ^(2^r)` in a wild slot
(`Instances.NProcyclicCore.npcTwistOne`), and the procyclic-`M` dictionary puts `x₁ * σ^p` and
`x₂ * σ^s` there (`Instances.MProcyclicCore.mpcUnitTwist`).  Once the wild letters die those
slots are *powers of `σ`*, and by `actionImage_unramified_closure_sigma` the ambient group is
exactly `⟨σ⟩`.

The theorem records what Roe's clause then demands: the procyclic image must be trivial as soon
as its order is odd.  Nothing in the unramified branch supplies that — the tame relation at
`tau = 1` is vacuous, so `orderOf σ` is unconstrained — hence the branch cannot be imported from
the `L` row and has to be proved directly on the procyclic target. -/
theorem eq_one_of_pro2Core_sigma_offset {C : Type*} [Group C] [Finite C] {s : C} {r : ℕ}
    (hodd : Odd (orderOf s))
    (hpro : IsPGroup 2 (Subgroup.normalClosure ({1, s ^ (2 ^ r)} : Set C))) : s = 1 := by
  have hmem : s ^ (2 ^ r) ∈ Subgroup.normalClosure ({1, s ^ (2 ^ r)} : Set C) :=
    Subgroup.subset_normalClosure (by simp)
  obtain ⟨k, hk⟩ := hpro ⟨s ^ (2 ^ r), hmem⟩
  have hk' : (s ^ (2 ^ r)) ^ (2 ^ k) = 1 := by
    have hval := congrArg (Subtype.val) hk
    simpa using hval
  have hdvd : orderOf (s ^ (2 ^ r)) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  have hsub : orderOf (s ^ (2 ^ r)) ∣ orderOf s := orderOf_pow_dvd _
  have h2 : ¬ (2 ∣ orderOf s) := Nat.two_dvd_ne_zero.mpr (Nat.odd_iff.mp hodd)
  have hoddSub : Odd (orderOf (s ^ (2 ^ r))) := by
    rcases Nat.even_or_odd (orderOf (s ^ (2 ^ r))) with hev | hod
    · exact absurd (hev.two_dvd.trans hsub) h2
    · exact hod
  have hone : s ^ (2 ^ r) = 1 :=
    orderOf_eq_one_iff.mp (eq_one_of_dvd_two_pow_of_odd hdvd hoddSub)
  exact orderOf_eq_one_iff.mp
    (eq_one_of_dvd_two_pow_of_odd (orderOf_dvd_of_pow_eq_one hone) hodd)

/-! ## The row inputs: a level-indexed resolver and a simple-module Stokes branch -/

/-- A level-indexed resolver family for the intrinsic relators of `Γ_R(n, q, R)`.

Every row produces one of these: `resolves` is the row's `resolvesAt_*` theorem at an arbitrary
killing level, and `endpoint` is its `IsStokesEndpoint` twin.  Nothing here fixes a single
integer resolver, which is exactly what the `η̂`-carrying rows cannot supply. -/
structure LevelResolver (n q : ℕ) (R : PWord (Generator n))
    (wOf : ℕ → Fin 2 → FreeGroup (Generator n)) : Prop where
  /-- Every level that kills the target resolves the intrinsic family there. -/
  resolves : ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]
    (N : ℕ), N ≠ 0 → (∀ x : Q, orderOf x ∣ N) → ResolvesAt (gammaFam n q R) (wOf N) Q
  /-- Every level with a nontrivial two-part is a Stokes endpoint. -/
  endpoint : ∀ N : ℕ, N ≠ 0 → N.factorization 2 ≠ 0 → IsStokesEndpoint (wOf N)

/-- **The row-specific residue left by action-image devissage.**  Stokes duality at the
canonical action-image marking of a *simple* elementary coefficient, at that image's own uniform
level.  For the `L` row this is `LSquare.finiteActionImage_stokesDuality_simple`, a theorem. -/
def SimpleActionImageStokes (n q : ℕ) (R : PWord (Generator n))
    (wOf : ℕ → Fin 2 → FreeGroup (Generator n)) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo ((GammaR n q R : Type)) M →
      StokesDuality (actionImageGenerators n q R M)
        (wOf (4 * Monoid.exponent (ActionImage n q R M))) M

/-- The unramified half of the residue: `tau` acts trivially, so by
`actionImage_unramified_closure_sigma` the target is procyclic. -/
def UnramifiedActionImageStokes (n q : ℕ) (R : PWord (Generator n))
    (wOf : ℕ → Fin 2 → FreeGroup (Generator n)) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo ((GammaR n q R : Type)) M →
      (∀ m : M, gammaGen n q R .tau • m = m) →
        StokesDuality (actionImageGenerators n q R M)
          (wOf (4 * Monoid.exponent (ActionImage n q R M))) M

/-- The ramified half of the residue: `tau` is fixed-point-free. -/
def RamifiedActionImageStokes (n q : ℕ) (R : PWord (Generator n))
    (wOf : ℕ → Fin 2 → FreeGroup (Generator n)) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M],
    (∀ m : M, m + m = 0) → IsSimpleModTwo ((GammaR n q R : Type)) M →
      (∀ m : M, gammaGen n q R .tau • m = m → m = 0) →
        StokesDuality (actionImageGenerators n q R M)
          (wOf (4 * Monoid.exponent (ActionImage n q R M))) M

/-- The `tau`-dichotomy splits the residue into its two branches, for every branch word. -/
theorem simpleActionImageStokes_of_branches {n q : ℕ} {R : PWord (Generator n)}
    {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}
    (hunram : UnramifiedActionImageStokes n q R wOf)
    (hram : RamifiedActionImageStokes n q R wOf) :
    SimpleActionImageStokes n q R wOf := by
  intro M _ _ _ _ _ _ hM₂ hsimple
  rcases actionImage_tau_split_or_ramified_simple hM₂ hsimple with hτ | hτfpf
  · exact hunram M hM₂ hsimple hτ
  · exact hram M hM₂ hsimple hτfpf

/-! ## Fixed-word devissage and its pushed conclusion -/

section Devissage

variable {n q : ℕ} {R : PWord (Generator n)} {wOf : ℕ → Fin 2 → FreeGroup (Generator n)}

/-- The uniform level of a finite target resolves every elementary Heisenberg lift over it. -/
theorem LevelResolver.heis (hlv : LevelResolver n q R wOf) {C A : Type} [Group C] [Finite C]
    [AddCommGroup A] [DistribMulAction C A] [Finite A] (hA₂ : ∀ a : A, a + a = 0) :
    ResolvesAt (gammaFam n q R) (wOf (4 * Monoid.exponent C)) (HeisLift A C) :=
  hlv.resolves (HeisLift A C) (4 * Monoid.exponent C)
    (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂ (fun g : C ↦ Monoid.order_dvd_exponent g))

set_option maxHeartbeats 2400000 in
/-- **Fixed-word devissage on the action image of an arbitrary finite elementary coefficient.**
Only the simple-module branch is row-specific; the composition series is traversed at one fixed
word, and each simple constituent is compared with its own action image through the action-map
transport theorem. -/
theorem actionImage_stokesDuality (hlv : LevelResolver n q R wOf)
    (hsimp : SimpleActionImageStokes n q R wOf)
    {M : Type} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction ((GammaR n q R : Type)) M]
    [ContinuousSMul ((GammaR n q R : Type)) M] [Finite M]
    (hM₂ : ∀ m : M, m + m = 0) :
    StokesDuality (actionImageGenerators n q R M)
      (wOf (4 * Monoid.exponent (ActionImage n q R M))) M := by
  let C₀ := ActionImage n q R M
  let c₀ := actionImageGenerators n q R M
  let w₀ := wOf (4 * Monoid.exponent C₀)
  have hres₀ : ResolvesAt (gammaFam n q R) w₀ (HeisLift M C₀) := hlv.heis hM₂
  have hend₀ : IsStokesEndpoint w₀ :=
    hlv.endpoint _ (fourMulExponent_ne_zero_and_even C₀).1
      (fourMulExponent_ne_zero_and_even C₀).2
  letI : TopologicalSpace (WordLift M C₀) := ⊥
  letI : DiscreteTopology (WordLift M C₀) := ⟨rfl⟩
  have hresWord : ResolvesAt (gammaFam n q R) w₀ (WordLift M C₀) := by
    let incl : ContinuousMonoidHom (WordLift M C₀) (HeisLift M C₀) :=
      ⟨heisPrim (A := M) (C := C₀), continuous_of_discreteTopology⟩
    exact hres₀.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift c₀ (w₀ k) = 1 := fun k ↦
    lower_rel (A := M) (actionImageHom n q R M) (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR n q R) hresWord k
  apply stokesDuality_of_simple c₀ w₀ hr hend₀
  · intro V _ _ _ hV₂ hsimple
    letI : TopologicalSpace V := ⊥
    letI : DiscreteTopology V := ⟨rfl⟩
    letI : ContinuousSMul C₀ V := ⟨continuous_of_discreteTopology⟩
    letI : DistribMulAction ((GammaR n q R : Type)) V :=
      DistribMulAction.compHom V (actionImageHom n q R M).toMonoidHom
    letI : ContinuousSMul ((GammaR n q R : Type)) V :=
      continuousSMul_of_comp_finite (actionImageHom n q R M) (fun _ _ ↦ rfl)
    have hsimpleGamma : IsSimpleModTwo ((GammaR n q R : Type)) V := by
      refine ⟨hsimple.1, fun U hU ↦ hsimple.2 U ?_⟩
      intro c v hv
      obtain ⟨g, rfl⟩ :=
        (finiteActionHom (G := (GammaR n q R : Type))
          (M := M)).toMonoidHom.rangeRestrict_surjective c
      exact hU g v hv
    have hdV := hsimp V hV₂ hsimpleGamma
    let D := Multiplicative (AddAut V)
    let piV : ActionImage n q R V →* D := Subgroup.subtype _
    let pi₀ : C₀ →* D := (finiteActionHom (G := C₀) (M := V)).toMonoidHom
    have hc : ∀ i, piV (actionImageGenerators n q R V i) = pi₀ (c₀ i) := by
      intro i
      apply Multiplicative.toAdd.injective
      ext v
      rfl
    have hresV : ResolvesAt (gammaFam n q R)
        (wOf (4 * Monoid.exponent (ActionImage n q R V)))
        (HeisLift V (ActionImage n q R V)) := hlv.heis hV₂
    have hresC : ResolvesAt (gammaFam n q R) w₀ (HeisLift V C₀) := hlv.heis hV₂
    exact (stokesDuality_iff_of_resolvers_action_maps piV pi₀
      (fun _ _ ↦ rfl) (fun g v ↦ (finiteActionHom_smul g v).symm)
      hc hresV hresC).mp hdV
  · exact hM₂

set_option maxHeartbeats 2400000 in
/-- **The pushed action-image theorem, at every admissible level.**

The transport theorem compares two Stokes complexes with different acting groups *and different
words*, so the ambient level is not forced to be the action image's own.  Every level `N` killing
`HeisLift A C` gives the conclusion at `wOf N`; taking `N = 4 * Monoid.exponent C` recovers the
uniform form used by the `L` row. -/
theorem pushedStokesDuality_of_actionImage (hlv : LevelResolver n q R wOf)
    (hsimp : SimpleActionImageStokes n q R wOf)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((GammaR n q R : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : HeisLift A C, orderOf x ∣ N) :
    StokesDuality (fun g ↦ rho (gammaGen n q R g)) (wOf N) A := by
  letI : TopologicalSpace A := ⊥
  letI : DiscreteTopology A := ⟨rfl⟩
  letI : DistribMulAction ((GammaR n q R : Type)) A :=
    DistribMulAction.compHom A rho.toMonoidHom
  letI : ContinuousSMul ((GammaR n q R : Type)) A :=
    continuousSMul_of_comp_finite rho (fun _ _ ↦ rfl)
  have hdA := actionImage_stokesDuality (R := R) hlv hsimp (M := A) hA₂
  letI : ContinuousSMul C A := ⟨continuous_of_discreteTopology⟩
  let D := Multiplicative (AddAut A)
  let piA : ActionImage n q R A →* D := Subgroup.subtype _
  let piC : C →* D := (finiteActionHom (G := C) (M := A)).toMonoidHom
  have hc : ∀ i, piA (actionImageGenerators n q R A i) = piC (rho (gammaGen n q R i)) := by
    intro i
    apply Multiplicative.toAdd.injective
    ext a
    rfl
  have hresA : ResolvesAt (gammaFam n q R)
      (wOf (4 * Monoid.exponent (ActionImage n q R A)))
      (HeisLift A (ActionImage n q R A)) := hlv.heis hA₂
  have hresC : ResolvesAt (gammaFam n q R) (wOf N) (HeisLift A C) :=
    hlv.resolves (HeisLift A C) N hN hord
  exact (stokesDuality_iff_of_resolvers_action_maps piA piC
    (fun _ _ ↦ rfl) (by
      intro g a
      change g • a = finiteActionHom (G := C) (M := A) g • a
      exact (finiteActionHom_smul g a).symm)
    hc hresA hresC).mp hdA

/-- The uniform-level specialization, the exact shape of `LSquare.UniformPushedHsimp`. -/
theorem uniformPushedStokesDuality_of_actionImage (hlv : LevelResolver n q R wOf)
    (hsimp : SimpleActionImageStokes n q R wOf)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((GammaR n q R : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality (fun g ↦ rho (gammaGen n q R g)) (wOf (4 * Monoid.exponent C)) A :=
  pushedStokesDuality_of_actionImage hlv hsimp rho A hA₂
    (fourMulExponent_ne_zero_and_even C).1
    (orderOf_heisLift_dvd_four_mul hA₂ (fun g : C ↦ Monoid.order_dvd_exponent g))

end Devissage

end

end GQ2.Dyadic.RowActionImage

namespace GQ2.Dyadic.NProcyclic

noncomputable section

open GQ2 GQ2.SectionEight GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Certificates
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The row's level-indexed resolver -/

/-- The corrected procyclic-`N` row supplies a level-indexed resolver: `resolvesAt_npcFamOf`
resolves both the `ω₂` node and the `η̂` node at every killing level, and
`npcResolver_isStokesEndpoint` supplies the endpoint condition at every even level.  This is
where the row's two-valued resolver replaces the `L` row's single integer. -/
theorem levelResolver {alpha r h q : ℕ} (d : EtaData) (hα : 1 ≤ alpha) (hqe : Even q) :
    LevelResolver (2 + 2 * h) q (Words.Npc.npcW alpha r h d) (resolvedFamily alpha r h q d) where
  resolves := fun _ _ _ _ _ _ hN hord ↦ resolvesAt_npcFamOf hN hord alpha r h q d (fun _ ↦ 0)
  endpoint := fun _ hN hv ↦ npcResolver_isStokesEndpoint hα hqe hN hv d (fun _ ↦ 0)

/-! ## The pushed residues -/

/-- The source-facing residue for the corrected procyclic-`N` row.  It ranges only over markings
pushed forward from the candidate group, and asks for bijectivity of the three induced
word-cohomology maps rather than for the six clauses of `StokesDuality`.

The restriction is mathematically essential for the same reason as on the `L` row: `Hsimp` ranges
over *all* finite markings at which the two resolved relators die, including non-wild markings
which need not extend across `GammaR`. -/
def PushedHsimp (alpha r h q : ℕ) (d : EtaData) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
        (resolvedFamily alpha r h q d N k) = 1)
      (hend : IsStokesEndpoint (resolvedFamily alpha r h q d N))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
          (resolvedFamily alpha r h q d N) V hr hend

/-- The coefficient-independent residue at the uniform level `4 * Monoid.exponent C`, in the
shape produced by action-image devissage.

The statement itself is written once, upstream, as `NProcyclic.UniformHsimp` in
`GQ2/Dyadic/Instances/NpcExact.lean`: that is the file which restates the whole clause stack over
the uniform residue, and it cannot name a definition living here because this file imports it.
This declaration is the row-uniform *name* for that one statement, matching the other rows
(`LSquare.UniformPushedHsimp`, `MCompact.UniformPushedHsimp`, `NCompact.UniformPushedHsimp`).  The
two names denote the same proposition, so a term of either type is accepted where the other is
expected and every existing consumer of this name is unaffected. -/
def UniformPushedHsimp (alpha r h q : ℕ) (d : EtaData) : Prop :=
  UniformHsimp alpha r h q d

/-- The historical all-markings residue implies the pushed cohomological one.  The converse is
intentionally absent: relator-killing markings need not be wild, hence need not be pushed. -/
theorem pushedHsimp_of_hsimp {alpha r h q : ℕ} {d : EtaData} (hsimp : Hsimp alpha r h q d) :
    PushedHsimp alpha r h q d := by
  intro C _ _ _ _ rho N hN hv hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g)⟩ with ht
  exact (stokesDuality_iff_cohomologyBijections ⇑t (resolvedFamily alpha r h q d N) V hr
    hend).mp (hsimp C t N hN hv hr V hV₂ hsimple)

/-! ## The pushed replacements for the two chain entry points -/

/-- The devissage step of the pushed residue, once relator death at the pushed marking is in
hand.  Both wrappers below differ only in which split target supplies that death. -/
private theorem stokesDuality_of_pushed_of_relators {alpha r h q : ℕ} {d : EtaData}
    (hsimp : PushedHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hr : ∀ k, FreeGroup.lift
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N k) = 1)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N) A := by
  have hend : IsStokesEndpoint (resolvedFamily alpha r h q d N) :=
    npcResolver_isStokesEndpoint hα hqe hN hv d (fun _ ↦ 0)
  exact stokesDuality_of_simple _ (resolvedFamily alpha r h q d N) hr hend
    (fun V _ _ _ hV₂ hsimple ↦
      (stokesDuality_iff_cohomologyBijections _ (resolvedFamily alpha r h q d N) V hr hend).mpr
        (hsimp C rho N hN hv hr hend V hV₂ hsimple)) A hA₂

/-- `NProcyclic.stokesDuality` with its `Hsimp` binder weakened to `PushedHsimp`.  Every other
hypothesis, and the conclusion, are unchanged, so the count chain's entry point is a literal
binder swap. -/
theorem stokesDuality_of_pushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : PushedHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N) A :=
  stokesDuality_of_pushed_of_relators hsimp hα hqe rho hN hv
    (fun k ↦ lower_rel (A := ZMod 2) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
        (Words.Npc.npcW alpha r h d)) hres k) A hA₂

/-- `NProcyclic.stokesDuality_T` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_T_of_pushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : PushedHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_npcFamOf
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) heisLevel_ne_zero heisLevel_even
    orderOf_dvd_heisLevel_scal (α := alpha) (r := r) (h := h) (q := q)
    hα hqe d (fun _ ↦ 0)
  exact stokesDuality_of_pushed hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## The uniform residue, and the action-image route to it -/

/-- The pushed residue supplies the uniform one. -/
theorem uniformPushedHsimp_of_pushedHsimp {alpha r h q : ℕ} {d : EtaData}
    (hsimp : PushedHsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d (4 * Monoid.exponent C)) (WordLift A C) := by
    refine resolvesAt_npcFamOf (fourMulExponent_ne_zero_and_even C).1 ?_
      alpha r h q d (fun _ ↦ 0)
    intro x
    refine (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) x).trans ?_
    exact mul_dvd_mul_right (by norm_num) (Monoid.exponent C)
  exact stokesDuality_of_pushed_of_relators hsimp hα hqe rho
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
    (fun k ↦ lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q
        (Words.Npc.npcW alpha r h d)) hres k) A hA₂

/-- Both weakenings composed: the historical residue supplies the uniform one. -/
theorem uniformPushedHsimp_of_hsimp {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r h q d :=
  uniformPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp) hα hqe

/-- **The action-image route for the corrected procyclic-`N` row, at every admissible level.**
The only remaining input is the simple-module branch at the canonical action image. -/
theorem stokesDuality_of_actionImage {alpha r h q : ℕ} {d : EtaData} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d))
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : HeisLift A C, orderOf x ∣ N) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N) A :=
  pushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂ hN hord

/-- The uniform residue from the action image. -/
theorem uniformPushedHsimp_of_actionImage {alpha r h q : ℕ} {d : EtaData} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d)) :
    UniformPushedHsimp alpha r h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  exact uniformPushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂

/-- The residue split along the `tau`-dichotomy, at the corrected procyclic-`N` word. -/
theorem uniformPushedHsimp_of_branches {alpha r h q : ℕ} {d : EtaData} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d))
    (hram : RamifiedActionImageStokes (2 + 2 * h) q (Words.Npc.npcW alpha r h d)
      (resolvedFamily alpha r h q d)) :
    UniformPushedHsimp alpha r h q d :=
  uniformPushedHsimp_of_actionImage hα hqe (simpleActionImageStokes_of_branches hunram hram)

/-! ## Regression: the historical entry points factor through the pushed ones -/

/-- `NProcyclic.stokesDuality`, re-derived through `PushedHsimp`.  The statement is literally the
frozen one, so swapping the `Hsimp` binder in the count chain changes no consumer. -/
theorem stokesDuality_via_pushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW alpha r h d))
      (resolvedFamily alpha r h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d N) A :=
  stokesDuality_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho hN hv hres A hA₂

/-- `NProcyclic.stokesDuality_T`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_T_via_pushed {alpha r h q : ℕ} {d : EtaData}
    (hsimp : Hsimp alpha r h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (Words.Npc.npcW alpha r h d) g))
      (resolvedFamily alpha r h q d (heisLevel D)) (Additive ↥D.T) :=
  stokesDuality_T_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho

end

/-! ## Axiom footprint -/

#print axioms GQ2.Dyadic.RowActionImage.actionImage_unramified_closure_sigma
#print axioms GQ2.Dyadic.RowActionImage.eq_one_of_pro2Core_sigma_offset
#print axioms GQ2.Dyadic.RowActionImage.actionImage_stokesDuality
#print axioms GQ2.Dyadic.RowActionImage.pushedStokesDuality_of_actionImage
#print axioms GQ2.Dyadic.RowActionImage.simpleActionImageStokes_of_branches
#print axioms GQ2.Dyadic.NProcyclic.levelResolver
#print axioms GQ2.Dyadic.NProcyclic.pushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.NProcyclic.uniformPushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.NProcyclic.stokesDuality_of_actionImage
#print axioms GQ2.Dyadic.NProcyclic.uniformPushedHsimp_of_actionImage
#print axioms GQ2.Dyadic.NProcyclic.uniformPushedHsimp_of_branches
#print axioms GQ2.Dyadic.NProcyclic.stokesDuality_via_pushed
#print axioms GQ2.Dyadic.NProcyclic.stokesDuality_T_via_pushed

end GQ2.Dyadic.NProcyclic
