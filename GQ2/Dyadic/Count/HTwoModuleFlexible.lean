/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleAssembly

/-!
# Flexible finite-level resolvers for the module-valued degree-two obstruction

The first module-valued `H²` assembly used one fixed free-word family `w` at every
action-compatible finite quotient.  That hypothesis is stronger than the proof needs:
at a finite quotient one only needs some resolving word family, together with an
identification of its word-coboundary range with the range defining the fixed target
`WordH2`.

`ModuleFlexibleResolverAt` is that minimal interface.  Its `word` may depend on the
finite quotient.  The field `range_eq` records exactly the transport used by descent
and reflection; no equality of words is asserted.  The constructor
`ModuleFlexibleResolverAt.of_differential_eq` exposes the stronger, and usually easier
to prove, sufficient condition that the two `heisD1` homomorphisms are equal.
More importantly, `ModuleFlexibleResolverAt.of_resolvers` proves that equality from a
local resolver and a target resolver by `PWord.eval` naturality.  Thus applications do
not need a separate exponent-invariance lemma for quotient-dependent words.

The remainder of the file repeats no finite extension algebra.  It feeds the selected
word to `moduleRelFam_coboundary_mem_range` for descent and to
`mem_B2_of_moduleRelFam_mem_range_at_factor` for reflection, transporting only range
membership.  The resulting map is an injection; no surjectivity or cardinal equality
is claimed.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## 1. The per-level flexible resolver interface -/

section ResolverAt

variable {iota rel : Type*} {A C L : Type}
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C A]
  [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [DistribMulAction L A]

/-- A quotient-dependent resolving word whose differential has the same range as the
fixed differential defining the target word cokernel.

Equality of ranges is the weakest datum used by both directions of the comparison:
descent transports local range membership to the target, while reflection transports
target range membership back to the chosen finite level. -/
structure ModuleFlexibleResolverAt (W : rel → PWord iota) (c : iota → C)
    (w : rel → FreeGroup iota) (m : iota → L) where
  /-- The free-word family selected at this finite target. -/
  word : rel → FreeGroup iota
  /-- The selected word really resolves the profinite relator at this target. -/
  resolves : ResolvesAt W word (WordLift A L)
  /-- Its word-coboundary subgroup is the fixed target word-coboundary subgroup. -/
  range_eq : (heisD1 (A := A) m word).range = (heisD1 (A := A) c w).range

/-- **Resolver comparison across an action-compatible base map.**  Two possibly
different word families resolving the same profinite relator induce the same word
differential after base change.

This removes the apparent need for a separate exponent-invariance calculation.  Both
differentials are fibre coordinates of the same `PWord.eval`; naturality of that
evaluation under `baseMap` identifies them. -/
theorem heisD1_eq_of_resolvers_action_map {W : rel → PWord iota}
    {c : iota → C} {w : rel → FreeGroup iota} {m : iota → L}
    (word : rel → FreeGroup iota)
    (rhoL : L →* C) (hact : ∀ (g : L) (a : A), g • a = rhoL g • a)
    (hc : ∀ i, rhoL (m i) = c i)
    (hlocal : ResolvesAt W word (WordLift A L))
    (htarget : ResolvesAt W w (WordLift A C)) :
    heisD1 (A := A) m word = heisD1 (A := A) c w := by
  ext a k
  rw [heisD1_eq_lift_foxLift_u, heisD1_eq_lift_foxLift_u,
    hlocal (foxLift m a) k, htarget (foxLift c a) k]
  let F : ContinuousMonoidHom (WordLift A L) (WordLift A C) :=
    ⟨baseMap rhoL hact, continuous_of_discreteTopology⟩
  have hmap := PWord.map_eval F (foxLift m a) (W k)
  have hgen : (fun i ↦ F (foxLift m a i)) = foxLift c a := by
    funext i
    exact baseMap_foxLift rhoL hact hc a i
  rw [hgen] at hmap
  exact congrArg WordLift.u hmap

namespace ModuleFlexibleResolverAt

/-- Equality of the local and target differentials is a convenient sufficient
condition for the flexible resolver interface. -/
def of_differential_eq {W : rel → PWord iota} {c : iota → C}
    {w : rel → FreeGroup iota} {m : iota → L}
    (word : rel → FreeGroup iota)
    (hres : ResolvesAt W word (WordLift A L))
    (hd : heisD1 (A := A) m word = heisD1 (A := A) c w) :
    ModuleFlexibleResolverAt (A := A) W c w m where
  word := word
  resolves := hres
  range_eq := by rw [hd]

/-- The old fixed-word hypothesis is a special case once base change identifies the
two actions on the generator marking. -/
def of_fixed {W : rel → PWord iota} {c : iota → C}
    {w : rel → FreeGroup iota} {m : iota → L}
    (hres : ResolvesAt W w (WordLift A L))
    (hd : heisD1 (A := A) m w = heisD1 (A := A) c w) :
    ModuleFlexibleResolverAt (A := A) W c w m :=
  of_differential_eq w hres hd

/-- Fixed words with a compatible change of acting base automatically define a
flexible resolver.  This is the adapter from the original all-level fixed-word API. -/
def of_fixed_action_map {W : rel → PWord iota} {c : iota → C}
    {w : rel → FreeGroup iota} {m : iota → L}
    (rhoL : L →* C) (hact : ∀ (g : L) (a : A), g • a = rhoL g • a)
    (hc : ∀ i, rhoL (m i) = c i)
    (hres : ResolvesAt W w (WordLift A L)) :
    ModuleFlexibleResolverAt (A := A) W c w m :=
  of_fixed hres (heisD1_eq_of_action_map rhoL hact m c hc w)

/-- A local resolver and a target resolver for the same profinite relator automatically
form a flexible resolver, even when their free-word families differ. -/
def of_resolvers {W : rel → PWord iota} {c : iota → C}
    {w : rel → FreeGroup iota} {m : iota → L}
    (word : rel → FreeGroup iota)
    (rhoL : L →* C) (hact : ∀ (g : L) (a : A), g • a = rhoL g • a)
    (hc : ∀ i, rhoL (m i) = c i)
    (hlocal : ResolvesAt W word (WordLift A L))
    (htarget : ResolvesAt W w (WordLift A C)) :
    ModuleFlexibleResolverAt (A := A) W c w m :=
  of_differential_eq word hlocal
    (heisD1_eq_of_resolvers_action_map word rhoL hact hc hlocal htarget)

end ModuleFlexibleResolverAt

end ResolverAt

/-! ## 2. Flexible global descent -/

section FlexibleDescent

variable {iota rel : Type*} {G C A : Type}
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]
  {gen : iota → G} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C} {J : Set iota}

local instance flexibleQuotientDiscreteTopology (V : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

/-- Adapter from the original fixed-word resolver system to the flexible system.
Thus the existing API is a literal special case, while quotient-dependent words can
be supplied directly without passing through this definition. -/
def flexibleResolverSystemOfFixed
    (rho : ContinuousMonoidHom G C) (hc : ∀ i, rho (gen i) = c i)
    (hresLevel : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ResolvesAt W w (WordLift A (G ⧸ V.toSubgroup))) :
    ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) := by
  intro V hV
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  apply ModuleFlexibleResolverAt.of_fixed_action_map rhoV (fun _ _ ↦ rfl)
  · intro i
    rw [quotientActionHom_mk rho V hV (gen i)]
    exact hc i
  · exact hresLevel V hV

/-- Build the flexible system from mere existence of a resolver at each finite level,
plus a resolver for the fixed target.  The local and target words may be unrelated as
syntax: `heisD1_eq_of_resolvers_action_map` proves their differentials agree because
both resolve the same `PWord` family. -/
noncomputable def flexibleResolverSystemOfResolvers
    (rho : ContinuousMonoidHom G C) (hc : ∀ i, rho (gen i) = c i)
    (htarget : ResolvesAt W w (WordLift A C))
    (hresLevel : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ∃ word : rel → FreeGroup iota,
        ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup))) :
    ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) := by
  intro V hV
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  let word := Classical.choose (hresLevel V hV)
  have hword : ResolvesAt W word (WordLift A (G ⧸ V.toSubgroup)) :=
    Classical.choose_spec (hresLevel V hV)
  apply ModuleFlexibleResolverAt.of_resolvers word rhoV (fun _ _ ↦ rfl)
  · intro i
    rw [quotientActionHom_mk rho V hV (gen i)]
    exact hc i
  · exact hword
  · exact htarget

/-- Flexible global `map_coboundary`: the finite quotient chosen by the splitting
cochain may use its own resolving word.  Only the resulting differential range is
transported to the fixed target. -/
theorem moduleObsFam_B2_mem_range_flexible
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    {f : Z2 G A} (hf : f.1 ∈ B2 G A) :
    moduleObsFam W gen rho hcompat f ∈ (heisD1 (A := A) c w).range := by
  rw [B2, AddSubgroup.mem_map] at hf
  obtain ⟨psi, hpsiC1, hpsiEq⟩ := hf
  have hpsi : Continuous psi := mem_C1_iff.mp hpsiC1
  have hf1 : f.1 = dOne G A psi := hpsiEq.symm
  let psi0 : G → A := fun g ↦ psi g - psi 1
  obtain ⟨V, hV, lam, hlam⟩ :=
    exists_moduleOneCochain_factor rho psi0 (hpsi.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlam 1
    rw [show QuotientGroup.mk' V.toSubgroup (1 : G) = 1 from map_one _] at h
    change psi 1 - psi 1 = lam 1 at h
    simpa using h.symm
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  have hfactor : ∀ x y : G, moduleNormalize f.1 (x, y) =
      (ModuleTwoCocycle.coboundary lam hlam1).κ
        (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y) := by
    intro x y
    change moduleNormalize f.1 (x, y) =
      rhoV (QuotientGroup.mk' V.toSubgroup x) •
          lam (QuotientGroup.mk' V.toSubgroup y) -
        lam (QuotientGroup.mk' V.toSubgroup (x * y)) +
          lam (QuotientGroup.mk' V.toSubgroup x)
    rw [show rhoV (QuotientGroup.mk' V.toSubgroup x) = rho x from
      quotientActionHom_mk rho V hV x]
    rw [← hcompat]
    rw [← hlam x, ← hlam y, ← hlam (x * y), hf1]
    simp [moduleNormalize, psi0, dOne, smul_sub]
    abel
  let Fcb : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := ModuleTwoCocycle.coboundary lam hlam1
      hfact := hfactor }
  change moduleObsFun W gen rho hcompat f ∈ (heisD1 (A := A) c w).range
  rw [moduleObsFun_eq W gen rho hcompat f Fcb]
  let m : iota → G ⧸ V.toSubgroup :=
    fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)
  have hrel : ∀ k, PWord.eval m (W k) = 1 :=
    fun k ↦ hpres.rel (GQ2.quotientMk V.toSubgroup) k
  let R := hresolve V hV
  have hfinite := moduleRelFam_coboundary_mem_range W R.word m lam hlam1
    R.resolves hrel
  rw [R.range_eq] at hfinite
  exact hfinite

/-- The flexible global obstruction and descent law, packaged for subsequent
reflection. -/
noncomputable def globalModuleH2WordDescentDataFlexible
    (hpres : IsAdmissibleMarkedPresentation G gen W J)
    (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a)
    (hresolve : ∀ (V : OpenNormalSubgroup G)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (G ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) :
    ModuleH2WordDescentData (Gamma := G) (A := A) c w where
  obstruction := moduleObsFam W gen rho hcompat
  map_coboundary := fun _ hf ↦
    moduleObsFam_B2_mem_range_flexible hpres rho hcompat hresolve hf

end FlexibleDescent

/-! ## 3. Flexible reflection and final assembly -/

section FlexibleAssembly

variable {iota rel : Type*} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {Gamma A C : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A] [DistribMulAction C A]
  {gen : iota → Gamma} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {c : iota → C} {J : Set iota}

local instance flexibleAssemblyQuotientDiscreteTopology (V : OpenNormalSubgroup Gamma) :
    DiscreteTopology (Gamma ⧸ V.toSubgroup) :=
  Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup

omit [Fintype iota] [Fintype rel] [DecidableEq iota] [Finite C] in
/-- Flexible reflection: range membership for the fixed target differential is
transported to the quotient-dependent resolver chosen at the factor supplied by the
continuous cocycle. -/
theorem reflects_coboundary_of_moduleFactor_read_flexible
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (obstruction : Z2 Gamma A →+ (rel → A))
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hread : ∀ (f : Z2 Gamma A) (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ∀ z : ModuleTwoCocycle (Gamma ⧸ V.toSubgroup) A,
        (∀ x y : Gamma, moduleNormalize f.1 (x, y) =
          z.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y)) →
        obstruction f = fun k ↦ moduleRel (W k)
          (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) :
    ∀ f : Z2 Gamma A,
      obstruction f ∈ (heisD1 (A := A) c w).range → f.1 ∈ B2 Gamma A := by
  intro f hf
  obtain ⟨V, hV, z, hfactor⟩ := exists_moduleTwoCocycle_factor rho hcompat f
  let rhoV : (Gamma ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  let R := hresolve V hV
  let piV : ContinuousMonoidHom Gamma (Gamma ⧸ V.toSubgroup) :=
    GQ2.quotientMk V.toSubgroup
  have hcompatV : ∀ (g : Gamma) (a : A), g • a = piV g • a := by
    intro g a
    change g • a = rhoV (QuotientGroup.mk' V.toSubgroup g) • a
    rw [quotientActionHom_mk rho V hV g]
    exact hcompat g a
  have hobsTarget :
      (fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) ∈
        (heisD1 (A := A) c w).range := by
    rw [← hread f V hV z hfactor]
    exact hf
  have hobsLocal :
      (fun k ↦ moduleRel (W k)
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z) ∈
        (heisD1 (A := A) (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) R.word).range := by
    rw [R.range_eq]
    exact hobsTarget
  exact mem_B2_of_moduleRelFam_mem_range_at_factor hpres piV hcompatV R.resolves
    (hwildLevel V) hA₂ z f hfactor hobsLocal

/-- Full coefficient-generic comparison data using quotient-dependent resolvers. -/
noncomputable def globalModuleH2WordDataFlexible
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) :
    ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w := by
  let D := globalModuleH2WordDescentDataFlexible hpres rho hcompat hresolve
  refine D.withReflection ?_
  apply reflects_coboundary_of_moduleFactor_read_flexible hpres rho hcompat
    hwildLevel hA₂ D.obstruction hresolve
  intro f V hV
  dsimp only
  let rhoV : (Gamma ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  intro z hfactor
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := z
      hfact := hfactor }
  change moduleObsFun W gen rho hcompat f =
    fun k ↦ moduleRel (W k)
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z
  rw [moduleObsFun_eq W gen rho hcompat f F]
  rfl

/-- The flexible coefficient-generic map from continuous `H²` to the fixed word
cokernel. -/
noncomputable def globalModuleH2WordFlexible
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) :
    H2 Gamma A →+ WordH2 c w A :=
  moduleH2Word
    (globalModuleH2WordDataFlexible hpres rho hcompat hwildLevel hA₂ hresolve)

/-- Representative regression: the flexible map is still exactly the quotient class
of the canonical global obstruction. -/
@[simp] theorem globalModuleH2WordFlexible_mk
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (f : Z2 Gamma A) :
    globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve
        (H2mk Gamma A f) =
      QuotientAddGroup.mk' (heisD1 (A := A) c w).range
        (moduleObsFam W gen rho hcompat f) := rfl

/-- The flexible arbitrary-coefficient `H²` word map is injective. -/
theorem globalModuleH2WordFlexible_injective
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := A) W c w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) :
    Function.Injective
      (globalModuleH2WordFlexible hpres rho hcompat hwildLevel hA₂ hresolve) :=
  moduleH2Word_injective _

end FlexibleAssembly

end GQ2.Dyadic.Count
