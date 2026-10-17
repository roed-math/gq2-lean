/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable 5.1
-/
module

public import TauCeti.Topology.Algebra.Group.ClosedSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicPow
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.Presentation.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Component
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Ring
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Decomposition
public import TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP
public import GQ2.Statement
public import GQ2.PeripheralAction
public import GQ2.DyadicPresentation
public import GQ2.AppendixB

@[expose] public section

/-!
# P1: the pro-`p`, free, presentation and `ℤ̂` dictionary (gq2 ↔ Tau Ceti)

Ticket P1 of `docs/orchestration/tauceti-tickets.md`.  This file identifies gq2's profinite
group theory with Tau Ceti's, for the Wave 2 adapters B3c (dyadic orientation), B8 (peripheral
cyclotomic action) and B10 (oriented tame quotient):

* **pro-`p`**: `isProP_iff_tauCeti` (`GQ2.IsProP p G ↔ TauCeti.IsProP p G`), `proPKernel_eq`,
  and the continuous isomorphism `maxProPEquiv p G : ↥(GQ2.maxProPQuotient p G) ≃ₜ*
  TauCeti.maximalProPQuotient p G` commuting with the two quotient maps
  (`maxProPEquiv_maxProPMk`); its instance `absGalQ2ProPEquiv` at `G = GQ2.AbsGalQ2` lands in
  `TauCeti.absoluteGaloisGroupProP 2 ℚ_[2]` (B3c);
* **free groups**: `GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X` (`rfl`) and
  `freeProfiniteGroup_of_eq` for the generators (not `rfl`: Tau Ceti's `of` is not exposed);
* **presentations**: `presentationEquiv rels : ↥(GQ2.profinitePresentation rels) ≃ₜ*
  TauCeti.presentedProfiniteGroup X rels`, the equivalence
  `maxProPPresentedEquiv p rels : TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels)
  ≃ₜ* TauCeti.presentedProP p X (fromFreeProfiniteGroup p X '' rels)` that Tau Ceti lacks (it
  only has the surjection `toPresentedProP`), and their composite `maxProPPresentationEquiv`
  from gq2's pro-`p` presentations `maxProPQuotient p (profinitePresentation rels)`;
* **`D₀`**: `d0Equiv : ↥GQ2.D0 ≃ₜ* TauCeti.demushkinD0` with `d0A ↦ d0A`, `d0S ↦ d0S`,
  `d0Y ↦ d0Y` (B3c);
* **`Δ`**: `deltaEquiv : ↥GQ2.Delta ≃ₜ* TauCeti.freeProP 2 (Fin 2)` with `deltaP ↦ of 0`,
  `deltaT ↦ of 1` (B8);
* **`ℤ̂`**: `zhatEquiv : ↥GQ2.Zhat ≃ₜ* ↥TauCeti.zHat.{0}` with `Zhat.ofInt n ↦ zHat.ofInt (ofAdd n)`,
  `zhatProjTwo_eq_component` identifying gq2's projection to `ℤ₂` with `TauCeti.zHat.component 2`,
  and the `ℤ₂`-section `zhatSectionTwo` of that component (value `zHat.idem 2` at `1`), which B8
  uses to build `ι`;
* **`ℤ₂`-powers**: `zpowZtwo_eq_padicPow` (`GQ2.zpowZtwo hP x u = hP'.padicPow x u`) and
  `zpowHat_eq_padicPow`; and `zpowHat_omega2_eq_self_of_isProP_two`, a `module`-importable copy of
  `GQ2.zpowHat_omega2_eq_self` (whose home `GQ2/AnabelianBridge/Construction.lean` is not a
  `module`), with its consequences `zhatProjTwo_omega2` and `component_two_zhatEquiv_omega2`.

## Spelling

Tau Ceti's definitions are not exposed, so every identification goes through Tau Ceti's stated
lemmas (`isProP_iff`, `mem_proPKernel_iff`, `fromFreeGroup_of`, `mk_apply`, …), never through
`rfl` on a Tau Ceti definition.  The carriers agree definitionally (`GQ2.FreeProfiniteGroup X`
is `TauCeti.freeProfiniteGroup X`, both `ProfiniteGrp.{u}` objects; gq2's quotients are
`ProfiniteGrp.of` of the same quotient types), but instances, `simp` and `rw` keyed on one
spelling miss the other.  The API is therefore stated on **Tau Ceti spellings** (relators as
`Set (TauCeti.freeProfiniteGroup X)`, pro-`p` quotients as Tau Ceti `Type`s) and each gq2 element
is transported once through an `abbrev` (`d0RelatorT`), then rewritten to a Tau Ceti word
(`d0RelatorT_eq`) before hom lemmas are applied.  The cross-spelling generator equation
`freeProfiniteGroup_of_eq` is deliberately *not* a `simp` lemma; use it in `simp only`/`rw`.
-/

universe u

open Multiplicative

namespace GQ2.TauCetiBridge

/-! ## Pro-`p` groups and the pro-`p` kernel -/

/-- gq2's and Tau Ceti's pro-`p` predicates agree (same definition; `Iff.rfl` is unavailable
because `TauCeti.IsProP` is not exposed). -/
theorem isProP_iff_tauCeti (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    GQ2.IsProP p G ↔ TauCeti.IsProP p G :=
  TauCeti.isProP_iff.symm

/-- Transport of a gq2 pro-`p` hypothesis to Tau Ceti's predicate. -/
theorem toTauCetiIsProP {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (hG : GQ2.IsProP p G) : TauCeti.IsProP p G :=
  (isProP_iff_tauCeti p G).1 hG

/-- Transport of a Tau Ceti pro-`p` hypothesis to gq2's predicate. -/
theorem ofTauCetiIsProP {p : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
    (hG : TauCeti.IsProP p G) : GQ2.IsProP p G :=
  (isProP_iff_tauCeti p G).2 hG

/-- gq2's and Tau Ceti's pro-`p` kernels agree (same `⨅` over the open normal subgroups with
`p`-group quotient; `rfl` is unavailable because `TauCeti.proPKernel` is not exposed). -/
theorem proPKernel_eq (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] :
    GQ2.proPKernel p G = TauCeti.proPKernel p G := by
  ext x
  rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩

/-! ## The maximal pro-`p` quotient -/

section MaxProP

variable (p : ℕ) (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **The maximal pro-`p` quotient dictionary**: gq2's `maxProPQuotient p G` (a `ProfiniteGrp`
object) is Tau Ceti's `maximalProPQuotient p G` (a `Type` with instances), as topological groups.
It is the identity of `G` descended along `proPKernel_eq`. -/
noncomputable def maxProPEquiv :
    ↥(GQ2.maxProPQuotient p G) ≃ₜ* TauCeti.maximalProPQuotient p G :=
  (ContinuousMulEquiv.refl G).quotientCongr (GQ2.proPKernel p G) (TauCeti.proPKernel p G)
    (by rw [proPKernel_eq]; exact Subgroup.map_id _)

/-- `maxProPEquiv` commutes with the two quotient maps. -/
@[simp]
theorem maxProPEquiv_maxProPMk (g : G) :
    maxProPEquiv p G (GQ2.maxProPMk p G g) = TauCeti.maximalProPQuotient.mk p G g :=
  ContinuousMulEquiv.quotientCongr_mk _ _ _ _ g

/-- The inverse of `maxProPEquiv` commutes with the two quotient maps (Tau Ceti side written in
its `simp` normal form, the class `↑g`). -/
@[simp]
theorem maxProPEquiv_symm_mk (g : G) :
    (maxProPEquiv p G).symm (g : TauCeti.maximalProPQuotient p G) = GQ2.maxProPMk p G g :=
  ContinuousMulEquiv.quotientCongr_symm_mk _ _ _ _ g

end MaxProP

/-- **B3c's Galois-group instance**: gq2's `G_{ℚ₂}(2)` is Tau Ceti's
`absoluteGaloisGroupProP 2 ℚ_[2]` (the compactness and total disconnectedness of `AbsGalQ2` are
Tau Ceti's instances on `Field.absoluteGaloisGroup ℚ_[2]`; being `Prop`s, they agree with any
others). -/
noncomputable def absGalQ2ProPEquiv :
    ↥(GQ2.maxProPQuotient 2 GQ2.AbsGalQ2) ≃ₜ* TauCeti.absoluteGaloisGroupProP 2 ℚ_[2] :=
  maxProPEquiv 2 GQ2.AbsGalQ2

@[simp]
theorem absGalQ2ProPEquiv_maxProPMk (g : GQ2.AbsGalQ2) :
    absGalQ2ProPEquiv (GQ2.maxProPMk 2 GQ2.AbsGalQ2 g) =
      TauCeti.maximalProPQuotient.mk 2 (Field.absoluteGaloisGroup ℚ_[2]) g :=
  maxProPEquiv_maxProPMk 2 GQ2.AbsGalQ2 g

@[simp]
theorem absGalQ2ProPEquiv_symm_mk (g : GQ2.AbsGalQ2) :
    absGalQ2ProPEquiv.symm (g : TauCeti.absoluteGaloisGroupProP 2 ℚ_[2]) =
      GQ2.maxProPMk 2 GQ2.AbsGalQ2 g :=
  maxProPEquiv_symm_mk 2 GQ2.AbsGalQ2 g

/-! ## Free profinite groups -/

/-- The free profinite groups are the same `ProfiniteGrp` object (Tau Ceti's is an exposed
`abbrev` of the profinite completion of `FreeGroup X`, gq2's an `@[expose]` def of the functor
applied to the same object). -/
theorem freeProfiniteGroup_eq (X : Type u) :
    GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X :=
  rfl

/-- The generators agree.  Not `rfl` (Tau Ceti's `of` is not exposed) and deliberately not a
`simp` lemma: it rewrites a gq2-typed word into a Tau Ceti-typed one, so use it in `simp only`
or `rw`, followed by `rfl` to realign the ambient instances (as in `d0RelatorT_eq`). -/
theorem freeProfiniteGroup_of_eq {X : Type u} (x : X) :
    GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := by
  rw [← TauCeti.freeProfiniteGroup.fromFreeGroup_of, TauCeti.freeProfiniteGroup.coe_fromFreeGroup]
  rfl

/-! ## Profinite presentations -/

/-- gq2's `(relatorSubgroup rels).Normal` instance, re-keyed on relators typed against Tau Ceti's
carrier (gq2's own instance is not found for them: the two carriers are definitionally but not
reducibly equal, memo P1 "Hardest seam").  It is gq2's instance applied to a gq2-typed binder. -/
instance instNormalRelatorSubgroupTauCeti {X : Type u} (rels : Set (TauCeti.freeProfiniteGroup X)) :
    (GQ2.relatorSubgroup rels).Normal :=
  (fun rels' : Set ↥(GQ2.FreeProfiniteGroup X) =>
    (inferInstance : (GQ2.relatorSubgroup rels').Normal)) rels

section Presentation

variable {X : Type u} (rels : Set (TauCeti.freeProfiniteGroup X))

/-- gq2's presented profinite group is Tau Ceti's: the same quotient of the same free profinite
group by the closed normal closure of `rels`.  State the relators on Tau Ceti's carrier (for a
gq2-typed relator, transport it through an `abbrev` first, cf. `d0RelatorT`). -/
theorem profinitePresentation_eq :
    (GQ2.profinitePresentation rels : Type u) = TauCeti.presentedProfiniteGroup X rels :=
  rfl

/-- **The presentation dictionary**: the identity, as a continuous isomorphism between gq2's
`profinitePresentation rels` and Tau Ceti's `presentedProfiniteGroup X rels`. -/
noncomputable def presentationEquiv :
    ↥(GQ2.profinitePresentation rels) ≃ₜ* TauCeti.presentedProfiniteGroup X rels :=
  ContinuousMulEquiv.refl _

/-- `presentationEquiv` sends gq2's quotient class of `x` to Tau Ceti's. -/
@[simp]
theorem presentationEquiv_quotientMk (x : TauCeti.freeProfiniteGroup X) :
    presentationEquiv rels (GQ2.quotientMk (GQ2.relatorSubgroup rels) x) =
      TauCeti.presentedProfiniteGroup.mk rels x := by
  rw [TauCeti.presentedProfiniteGroup.mk_apply]
  rfl

/-- `presentationEquiv` sends gq2's generator classes to Tau Ceti's generators. -/
@[simp]
theorem presentationEquiv_quotientMk_of (x : X) :
    presentationEquiv rels (GQ2.quotientMk (GQ2.relatorSubgroup rels) (GQ2.FreeProfiniteGroup.of x)) =
      TauCeti.presentedProfiniteGroup.of rels x := by
  rw [← TauCeti.presentedProfiniteGroup.mk_of, freeProfiniteGroup_of_eq]
  exact presentationEquiv_quotientMk rels _

@[simp]
theorem presentationEquiv_symm_mk (x : TauCeti.freeProfiniteGroup X) :
    (presentationEquiv rels).symm (TauCeti.presentedProfiniteGroup.mk rels x) =
      GQ2.quotientMk (GQ2.relatorSubgroup rels) x :=
  (presentationEquiv rels).symm_apply_eq.mpr (presentationEquiv_quotientMk rels x).symm

@[simp]
theorem presentationEquiv_symm_of (x : X) :
    (presentationEquiv rels).symm (TauCeti.presentedProfiniteGroup.of rels x) =
      GQ2.quotientMk (GQ2.relatorSubgroup rels) (GQ2.FreeProfiniteGroup.of x) :=
  (presentationEquiv rels).symm_apply_eq.mpr (presentationEquiv_quotientMk_of rels x).symm

end Presentation

/-! ## Pro-`p` presentations: `(F̂/⟨⟨R⟩⟩)(p) ≅ F̂(p)/⟨⟨R̄⟩⟩`

Tau Ceti presents pro-`p` groups as quotients of the free pro-`p` group (`presentedProP`), gq2
as maximal pro-`p` quotients of profinite presentations (`maxProPQuotient p (profinitePresentation
rels)`).  Tau Ceti has only the comparison surjection `presentedProfiniteGroup.toPresentedProP`;
the equivalence is built here from the two universal properties. -/

section ProPPresentation

variable (p : ℕ) {X : Type u} (rels : Set (TauCeti.freeProfiniteGroup X))

/-- Forward map `(F̂/⟨⟨R⟩⟩)(p) → F̂(p)/⟨⟨R̄⟩⟩`: Tau Ceti's comparison surjection
`presentedProfiniteGroup.toPresentedProP`, descended to the maximal pro-`p` quotient. -/
noncomputable def maxProPPresentedToProP :
    TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels) →ₜ*
      TauCeti.presentedProP p X (TauCeti.freeProP.fromFreeProfiniteGroup p X '' rels) :=
  ⟨TauCeti.maximalProPQuotient.lift (TauCeti.presentedProP.isProP p X _)
      (TauCeti.presentedProfiniteGroup.toPresentedProP p rels).toMonoidHom
      (TauCeti.presentedProfiniteGroup.toPresentedProP p rels).continuous,
    TauCeti.maximalProPQuotient.continuous_lift _ _ _⟩

/-- `F̂(p) → (F̂/⟨⟨R⟩⟩)(p)`, the pro-`p` descent of `F̂ → F̂/⟨⟨R⟩⟩ → (F̂/⟨⟨R⟩⟩)(p)`. -/
noncomputable def freeProPToMaxProPPresented :
    TauCeti.freeProP p X →ₜ*
      TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels) :=
  ⟨TauCeti.maximalProPQuotient.lift TauCeti.isProP_maximalProPQuotient
      ((TauCeti.maximalProPQuotient.mk p (TauCeti.presentedProfiniteGroup X rels)).comp
        (TauCeti.presentedProfiniteGroup.mk rels).toMonoidHom)
      ((TauCeti.maximalProPQuotient.continuous_mk p _).comp
        (TauCeti.presentedProfiniteGroup.mk rels).continuous),
    TauCeti.maximalProPQuotient.continuous_lift _ _ _⟩

theorem freeProPToMaxProPPresented_fromFreeProfiniteGroup (x : TauCeti.freeProfiniteGroup X) :
    freeProPToMaxProPPresented p rels (TauCeti.freeProP.fromFreeProfiniteGroup p X x) =
      TauCeti.maximalProPQuotient.mk p (TauCeti.presentedProfiniteGroup X rels)
        (TauCeti.presentedProfiniteGroup.mk rels x) := by
  rw [TauCeti.freeProP.fromFreeProfiniteGroup_apply]
  exact TauCeti.maximalProPQuotient.lift_mk _ _ _ x

/-- Backward map `F̂(p)/⟨⟨R̄⟩⟩ → (F̂/⟨⟨R⟩⟩)(p)`: `freeProPToMaxProPPresented` kills the images of
the relators. -/
noncomputable def maxProPPresentedOfProP :
    TauCeti.presentedProP p X (TauCeti.freeProP.fromFreeProfiniteGroup p X '' rels) →ₜ*
      TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels) :=
  TauCeti.presentedProP.lift (freeProPToMaxProPPresented p rels) (by
    rintro _ ⟨r, hr, rfl⟩
    rw [freeProPToMaxProPPresented_fromFreeProfiniteGroup,
      TauCeti.presentedProfiniteGroup.mk_relator r hr, map_one])

theorem maxProPPresentedToProP_mk (x : TauCeti.freeProfiniteGroup X) :
    maxProPPresentedToProP p rels
        (TauCeti.maximalProPQuotient.mk p _ (TauCeti.presentedProfiniteGroup.mk rels x)) =
      TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x) := by
  show TauCeti.maximalProPQuotient.lift _ _ _ (QuotientGroup.mk _) = _
  rw [TauCeti.maximalProPQuotient.lift_mk]
  exact TauCeti.presentedProfiniteGroup.toPresentedProP_mk p rels x

theorem maxProPPresentedOfProP_mk (x : TauCeti.freeProfiniteGroup X) :
    maxProPPresentedOfProP p rels
        (TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x)) =
      TauCeti.maximalProPQuotient.mk p _ (TauCeti.presentedProfiniteGroup.mk rels x) := by
  rw [maxProPPresentedOfProP, TauCeti.presentedProP.lift_mk,
    freeProPToMaxProPPresented_fromFreeProfiniteGroup]

/-- **The pro-`p` presentation equivalence** Tau Ceti lacks: the maximal pro-`p` quotient of the
profinite group presented by `rels` is the pro-`p` group presented by the images of `rels` in
the free pro-`p` group.  Both directions are lifts along universal properties; the round trips
hold on the dense image of the free profinite group. -/
noncomputable def maxProPPresentedEquiv :
    TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels) ≃ₜ*
      TauCeti.presentedProP p X (TauCeti.freeProP.fromFreeProfiniteGroup p X '' rels) where
  toFun := maxProPPresentedToProP p rels
  invFun := maxProPPresentedOfProP p rels
  left_inv y := by
    obtain ⟨z, rfl⟩ := TauCeti.maximalProPQuotient.mk_surjective p _ y
    obtain ⟨x, rfl⟩ := TauCeti.presentedProfiniteGroup.mk_surjective rels z
    rw [maxProPPresentedToProP_mk, maxProPPresentedOfProP_mk]
  right_inv y := by
    obtain ⟨z, rfl⟩ := TauCeti.presentedProP.mk_surjective p _ y
    obtain ⟨x, rfl⟩ := TauCeti.freeProP.fromFreeProfiniteGroup_surjective (p := p) (X := X) z
    rw [maxProPPresentedOfProP_mk, maxProPPresentedToProP_mk]
  map_mul' := map_mul (maxProPPresentedToProP p rels)
  continuous_toFun := (maxProPPresentedToProP p rels).continuous
  continuous_invFun := (maxProPPresentedOfProP p rels).continuous

/-- `maxProPPresentedEquiv` on the class of the class of `x ∈ F̂` (Tau Ceti `simp` normal form on
the left: the pro-`p` class is written `↑_`). -/
@[simp]
theorem maxProPPresentedEquiv_mk_mk (x : TauCeti.freeProfiniteGroup X) :
    maxProPPresentedEquiv p rels
        ((TauCeti.presentedProfiniteGroup.mk rels x :
          TauCeti.presentedProfiniteGroup X rels) :
            TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels)) =
      TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x) := by
  show TauCeti.maximalProPQuotient.lift _ _ _ (QuotientGroup.mk _) = _
  rw [TauCeti.maximalProPQuotient.lift_mk]
  exact TauCeti.presentedProfiniteGroup.toPresentedProP_mk p rels x

/-- `maxProPPresentedEquiv` on generators. -/
@[simp]
theorem maxProPPresentedEquiv_mk_of (x : X) :
    maxProPPresentedEquiv p rels
        ((TauCeti.presentedProfiniteGroup.of rels x : TauCeti.presentedProfiniteGroup X rels) :
          TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels)) =
      TauCeti.presentedProP.of p _ x := by
  rw [← TauCeti.presentedProfiniteGroup.mk_of, maxProPPresentedEquiv_mk_mk,
    TauCeti.freeProP.fromFreeProfiniteGroup_of, TauCeti.presentedProP.mk_of]

@[simp]
theorem maxProPPresentedEquiv_symm_mk (x : TauCeti.freeProfiniteGroup X) :
    (maxProPPresentedEquiv p rels).symm
        (TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x)) =
      ((TauCeti.presentedProfiniteGroup.mk rels x : TauCeti.presentedProfiniteGroup X rels) :
        TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels)) := by
  show TauCeti.presentedProP.lift _ _ (TauCeti.presentedProP.mk p _ _) = _
  rw [TauCeti.presentedProP.lift_mk, freeProPToMaxProPPresented_fromFreeProfiniteGroup]
  rfl

@[simp]
theorem maxProPPresentedEquiv_symm_of (x : X) :
    (maxProPPresentedEquiv p rels).symm (TauCeti.presentedProP.of p _ x) =
      ((TauCeti.presentedProfiniteGroup.of rels x : TauCeti.presentedProfiniteGroup X rels) :
        TauCeti.maximalProPQuotient p (TauCeti.presentedProfiniteGroup X rels)) :=
  (maxProPPresentedEquiv p rels).symm_apply_eq.mpr (maxProPPresentedEquiv_mk_of p rels x).symm

/-- **gq2's pro-`p` presentations in Tau Ceti's form**: `maxProPQuotient p (profinitePresentation
rels)` is `presentedProP p X (fromFreeProfiniteGroup p X '' rels)`. -/
noncomputable def maxProPPresentationEquiv :
    ↥(GQ2.maxProPQuotient p (GQ2.profinitePresentation rels)) ≃ₜ*
      TauCeti.presentedProP p X (TauCeti.freeProP.fromFreeProfiniteGroup p X '' rels) :=
  (maxProPEquiv p (GQ2.profinitePresentation rels)).trans (maxProPPresentedEquiv p rels)

/-- `maxProPPresentationEquiv` on gq2's class of the class of `x ∈ F̂`. -/
@[simp]
theorem maxProPPresentationEquiv_maxProPMk_quotientMk (x : TauCeti.freeProfiniteGroup X) :
    maxProPPresentationEquiv p rels
        (GQ2.maxProPMk p (GQ2.profinitePresentation rels)
          (GQ2.quotientMk (GQ2.relatorSubgroup rels) x)) =
      TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x) := by
  have h := maxProPPresentedEquiv_mk_mk p rels x
  rw [TauCeti.presentedProfiniteGroup.mk_apply] at h
  -- `rw` cannot abstract across the two spellings of the presentation; use the terms directly.
  exact (congrArg (maxProPPresentedEquiv p rels) (maxProPEquiv_maxProPMk p
    (GQ2.profinitePresentation rels) (GQ2.quotientMk (GQ2.relatorSubgroup rels) x))).trans h

/-- `maxProPPresentationEquiv` on gq2's generator classes. -/
@[simp]
theorem maxProPPresentationEquiv_maxProPMk_quotientMk_of (x : X) :
    maxProPPresentationEquiv p rels
        (GQ2.maxProPMk p (GQ2.profinitePresentation rels)
          (GQ2.quotientMk (GQ2.relatorSubgroup rels) (GQ2.FreeProfiniteGroup.of x))) =
      TauCeti.presentedProP.of p _ x := by
  rw [freeProfiniteGroup_of_eq, maxProPPresentationEquiv_maxProPMk_quotientMk,
    TauCeti.freeProP.fromFreeProfiniteGroup_of, TauCeti.presentedProP.mk_of]

@[simp]
theorem maxProPPresentationEquiv_symm_mk (x : TauCeti.freeProfiniteGroup X) :
    (maxProPPresentationEquiv p rels).symm
        (TauCeti.presentedProP.mk p _ (TauCeti.freeProP.fromFreeProfiniteGroup p X x)) =
      GQ2.maxProPMk p (GQ2.profinitePresentation rels)
        (GQ2.quotientMk (GQ2.relatorSubgroup rels) x) :=
  (maxProPPresentationEquiv p rels).symm_apply_eq.mpr
    (maxProPPresentationEquiv_maxProPMk_quotientMk p rels x).symm

@[simp]
theorem maxProPPresentationEquiv_symm_of (x : X) :
    (maxProPPresentationEquiv p rels).symm (TauCeti.presentedProP.of p _ x) =
      GQ2.maxProPMk p (GQ2.profinitePresentation rels)
        (GQ2.quotientMk (GQ2.relatorSubgroup rels) (GQ2.FreeProfiniteGroup.of x)) :=
  (maxProPPresentationEquiv p rels).symm_apply_eq.mpr
    (maxProPPresentationEquiv_maxProPMk_quotientMk_of p rels x).symm

/-- Relator sets with the same closed normal closure: the induced isomorphism fixes the
generators (Tau Ceti states this on `mk` only). -/
@[simp]
theorem presentedProP_congrOfClosureEq_of {p : ℕ} {X : Type u}
    {rels rels₂ : Set (TauCeti.freeProP p X)}
    (h : (Subgroup.normalClosure rels).topologicalClosure =
      (Subgroup.normalClosure rels₂).topologicalClosure) (x : X) :
    TauCeti.presentedProP.congrOfClosureEq h (TauCeti.presentedProP.of p rels x) =
      TauCeti.presentedProP.of p rels₂ x := by
  rw [← TauCeti.presentedProP.mk_of, TauCeti.presentedProP.congrOfClosureEq_mk,
    TauCeti.presentedProP.mk_of]

end ProPPresentation

/-! ## `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩` (B3c)

gq2's `D0` is `(F̂₃/⟨⟨r⟩⟩)(2)`, Tau Ceti's `demushkinD0` is `F̂₃(2)/⟨⟨r̄⟩⟩`; the relator words agree
(commutator `x⁻¹y⁻¹xy` on both sides, generators `A, S, Y = of 0, of 1, of 2`). -/

/-- gq2's Demushkin relator, read in Tau Ceti's free profinite group on `Fin 3` (the one-time
transport of the spelling). -/
noncomputable abbrev d0RelatorT : TauCeti.freeProfiniteGroup (Fin 3) := GQ2.d0Relator

open TauCeti.freeProfiniteGroup in
/-- gq2's relator as a Tau Ceti word: `A²S⁴(S⁻¹Y⁻¹SY)`. -/
theorem d0RelatorT_eq :
    d0RelatorT =
      (of 0 ^ 2 * of 1 ^ 4 * ((of 1)⁻¹ * (of 2)⁻¹ * of 1 * of 2) :
        TauCeti.freeProfiniteGroup (Fin 3)) := by
  simp only [d0RelatorT, GQ2.d0Relator, GQ2.commP, freeProfiniteGroup_of_eq]
  rfl

/-- The image of gq2's relator in the free pro-`2` group is Tau Ceti's `d0Relator`. -/
theorem fromFreeProfiniteGroup_d0RelatorT :
    TauCeti.freeProP.fromFreeProfiniteGroup 2 (Fin 3) d0RelatorT = TauCeti.d0Relator := by
  rw [TauCeti.d0Relator_def, d0RelatorT_eq]
  simp only [map_mul, map_pow, map_inv, TauCeti.freeProP.fromFreeProfiniteGroup_of]

theorem image_d0RelatorT :
    TauCeti.freeProP.fromFreeProfiniteGroup 2 (Fin 3) '' {d0RelatorT} = {TauCeti.d0Relator} := by
  rw [Set.image_singleton, fromFreeProfiniteGroup_d0RelatorT]

/-- **The `D₀` dictionary**: gq2's `D0` is Tau Ceti's `demushkinD0`, generators to generators
(`d0Equiv_d0A`, `d0Equiv_d0S`, `d0Equiv_d0Y`). -/
noncomputable def d0Equiv : ↥GQ2.D0 ≃ₜ* TauCeti.demushkinD0 :=
  (maxProPPresentationEquiv 2 {d0RelatorT}).trans
    (TauCeti.presentedProP.congrOfClosureEq (by rw [image_d0RelatorT]))

/-- `d0Equiv` on gq2's generators: `maxProPMk (quotientMk (of i)) ↦ presentedProP.of i`. -/
theorem d0Equiv_apply_gen (i : Fin 3) :
    d0Equiv (GQ2.maxProPMk 2 GQ2.D0Full
        (GQ2.quotientMk (GQ2.relatorSubgroup {GQ2.d0Relator}) (GQ2.FreeProfiniteGroup.of i))) =
      TauCeti.presentedProP.of 2 {TauCeti.d0Relator} i :=
  -- `rw` cannot abstract across the two spellings of the presentation; use the terms directly.
  (congrArg (TauCeti.presentedProP.congrOfClosureEq _)
    (maxProPPresentationEquiv_maxProPMk_quotientMk_of 2 {d0RelatorT} i)).trans
    (presentedProP_congrOfClosureEq_of _ i)

@[simp] theorem d0Equiv_d0A : d0Equiv GQ2.d0A = TauCeti.d0A :=
  (d0Equiv_apply_gen 0).trans TauCeti.presentedProP_of_d0Relator_zero
@[simp] theorem d0Equiv_d0S : d0Equiv GQ2.d0S = TauCeti.d0S :=
  (d0Equiv_apply_gen 1).trans TauCeti.presentedProP_of_d0Relator_one
@[simp] theorem d0Equiv_d0Y : d0Equiv GQ2.d0Y = TauCeti.d0Y :=
  (d0Equiv_apply_gen 2).trans TauCeti.presentedProP_of_d0Relator_two

@[simp] theorem d0Equiv_symm_d0A : d0Equiv.symm TauCeti.d0A = GQ2.d0A :=
  d0Equiv.symm_apply_eq.mpr d0Equiv_d0A.symm
@[simp] theorem d0Equiv_symm_d0S : d0Equiv.symm TauCeti.d0S = GQ2.d0S :=
  d0Equiv.symm_apply_eq.mpr d0Equiv_d0S.symm
@[simp] theorem d0Equiv_symm_d0Y : d0Equiv.symm TauCeti.d0Y = GQ2.d0Y :=
  d0Equiv.symm_apply_eq.mpr d0Equiv_d0Y.symm

/-! ## `Δ = F̂₂(2)` (B8) -/

/-- **The `Δ` dictionary**: gq2's `Delta = maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))` is Tau
Ceti's free pro-`2` group `freeProP 2 (Fin 2)`. -/
noncomputable def deltaEquiv : ↥GQ2.Delta ≃ₜ* TauCeti.freeProP 2 (Fin 2) :=
  maxProPEquiv 2 (GQ2.FreeProfiniteGroup (Fin 2))

/-- `deltaEquiv` on a generator class. -/
theorem deltaEquiv_maxProPMk_of (i : Fin 2) :
    deltaEquiv (GQ2.maxProPMk 2 (GQ2.FreeProfiniteGroup (Fin 2)) (GQ2.FreeProfiniteGroup.of i)) =
      TauCeti.freeProP.of i := by
  rw [← TauCeti.freeProP.fromFreeProfiniteGroup_of, TauCeti.freeProP.fromFreeProfiniteGroup_apply,
    ← freeProfiniteGroup_of_eq]
  exact maxProPEquiv_maxProPMk 2 _ _

@[simp] theorem deltaEquiv_deltaP : deltaEquiv GQ2.deltaP = TauCeti.freeProP.of 0 :=
  deltaEquiv_maxProPMk_of 0
@[simp] theorem deltaEquiv_deltaT : deltaEquiv GQ2.deltaT = TauCeti.freeProP.of 1 :=
  deltaEquiv_maxProPMk_of 1
@[simp] theorem deltaEquiv_deltaC :
    deltaEquiv GQ2.deltaC = (TauCeti.freeProP.of 0 * TauCeti.freeProP.of 1)⁻¹ := by
  rw [GQ2.deltaC, map_inv, map_mul, deltaEquiv_deltaP, deltaEquiv_deltaT]

@[simp] theorem deltaEquiv_symm_of_zero : deltaEquiv.symm (TauCeti.freeProP.of 0) = GQ2.deltaP :=
  deltaEquiv.symm_apply_eq.mpr deltaEquiv_deltaP.symm
@[simp] theorem deltaEquiv_symm_of_one : deltaEquiv.symm (TauCeti.freeProP.of 1) = GQ2.deltaT :=
  deltaEquiv.symm_apply_eq.mpr deltaEquiv_deltaT.symm

/-- `Δ` is pro-`2` in Tau Ceti's sense (the `hF` of
`TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two`). -/
theorem isProP_tauCeti_delta : TauCeti.IsProP 2 GQ2.Delta :=
  toTauCetiIsProP GQ2.isProP_maxProPQuotient

/-! ## `ℤ̂` -/

/-- `ℤ̂ → ℤ̂`, gq2 to Tau Ceti: `γ ↦ gen ^ᶻ γ`. -/
noncomputable def zhatToTauCeti : GQ2.Zhat →ₜ* TauCeti.zHat.{0} :=
  (GQ2.zpowHatHom (G := TauCeti.zHat.{0}) TauCeti.zHat.gen).hom

/-- `ℤ̂ → ℤ̂`, Tau Ceti to gq2: the lift of `ofInt 1`. -/
noncomputable def zhatOfTauCeti : TauCeti.zHat.{0} →ₜ* GQ2.Zhat :=
  TauCeti.zHat.lift (GQ2.Zhat.ofInt 1)

theorem zhatToTauCeti_ofInt (n : ℤ) :
    zhatToTauCeti (GQ2.Zhat.ofInt n) = TauCeti.zHat.ofInt (ofAdd n) := by
  rw [TauCeti.zHat.ofInt_ofAdd]
  exact GQ2.zpowHat_ofInt (G := TauCeti.zHat.{0}) TauCeti.zHat.gen n

theorem zhatOfTauCeti_gen : zhatOfTauCeti TauCeti.zHat.gen = GQ2.Zhat.ofInt 1 :=
  TauCeti.zHat.lift_gen _

/-- **The `ℤ̂` dictionary**: gq2's `Zhat` (completion of `Multiplicative ℤ`) is Tau Ceti's
`zHat.{0}` (completion of `ULift.{0} (Multiplicative ℤ)`; not `rfl`, `ULift` is a structure),
via the universal properties on both sides. -/
noncomputable def zhatEquiv : ↥GQ2.Zhat ≃ₜ* ↥TauCeti.zHat.{0} where
  toFun := zhatToTauCeti
  invFun := zhatOfTauCeti
  left_inv γ := by
    have h := GQ2.Zhat.funext_ofInt (f := fun γ => zhatOfTauCeti (zhatToTauCeti γ)) (g := id)
      (zhatOfTauCeti.continuous.comp zhatToTauCeti.continuous) continuous_id (fun n => by
        simp only [id, zhatToTauCeti_ofInt, TauCeti.zHat.ofInt_ofAdd, map_zpow, zhatOfTauCeti_gen,
          GQ2.Zhat.ofInt_one_zpow])
    exact congrFun h γ
  right_inv x := by
    have h : zhatToTauCeti.comp zhatOfTauCeti = ContinuousMonoidHom.id _ := by
      refine TauCeti.zHat.hom_ext ?_
      simp only [ContinuousMonoidHom.comp_toFun, ContinuousMonoidHom.id_toFun]
      rw [zhatOfTauCeti_gen, zhatToTauCeti_ofInt, TauCeti.zHat.ofInt_ofAdd, zpow_one]
    exact DFunLike.congr_fun h x
  map_mul' := map_mul zhatToTauCeti
  continuous_toFun := zhatToTauCeti.continuous
  continuous_invFun := zhatOfTauCeti.continuous

@[simp]
theorem zhatEquiv_ofInt (n : ℤ) : zhatEquiv (GQ2.Zhat.ofInt n) = TauCeti.zHat.ofInt (ofAdd n) :=
  zhatToTauCeti_ofInt n

theorem zhatEquiv_ofInt_one : zhatEquiv (GQ2.Zhat.ofInt 1) = TauCeti.zHat.gen := by
  rw [zhatEquiv_ofInt, TauCeti.zHat.ofInt_ofAdd, zpow_one]

@[simp]
theorem zhatEquiv_symm_ofInt (n : ℤ) :
    zhatEquiv.symm (TauCeti.zHat.ofInt (ofAdd n)) = GQ2.Zhat.ofInt n :=
  zhatEquiv.symm_apply_eq.mpr (zhatEquiv_ofInt n).symm

@[simp]
theorem zhatEquiv_symm_gen : zhatEquiv.symm TauCeti.zHat.gen = GQ2.Zhat.ofInt 1 :=
  zhatEquiv.symm_apply_eq.mpr zhatEquiv_ofInt_one.symm

/-- **gq2's projection `ℤ̂ → ℤ₂` is Tau Ceti's `2`-adic component** (memo Answer 6): both are the
continuous extension of `n ↦ n`, gq2's as `(ofAdd 1) ^ᶻ ·`, Tau Ceti's as
`zHat.component 2 = toAdd ∘ lift (ofAdd 1)`. -/
theorem zhatProjTwo_eq_component (γ : GQ2.Zhat) :
    GQ2.zhatProjTwo γ = ofAdd (TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ))) := by
  have h := GQ2.Zhat.funext_ofInt (f := fun γ => GQ2.zhatProjTwo γ)
    (g := fun γ => ofAdd (TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ))))
    GQ2.zhatProjTwo.continuous
    (continuous_ofAdd.comp ((TauCeti.zHat.continuous_component 2).comp
      (continuous_ofMul.comp zhatEquiv.continuous))) (fun n => by
        simp only [zhatEquiv_ofInt, TauCeti.zHat.ofMul_ofInt, map_intCast, toAdd_ofAdd]
        show GQ2.zpowHat (ofAdd (1 : ℤ_[2])) (GQ2.Zhat.ofInt n) = _
        rw [GQ2.zpowHat_ofInt, ← ofAdd_zsmul, zsmul_eq_mul, mul_one])
  exact congrFun h γ

theorem toAdd_zhatProjTwo_eq_component (γ : GQ2.Zhat) :
    (GQ2.zhatProjTwo γ).toAdd = TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ)) := by
  rw [zhatProjTwo_eq_component, toAdd_ofAdd]

/-! ### The `ℤ₂`-section of `zHat.component 2`

Tau Ceti has no named section `ℤ₂ → ℤ̂`; `zhatSectionTwo v` is the profinite integer with
`2`-adic component `v` and all odd components `0`, through the product decomposition
`zHat.ringEquivPiPadicInt`.  At `v = 1` it is Tau Ceti's idempotent `zHat.idem 2`. -/

/-- The family `(v at 2, 0 at every odd prime)`. -/
noncomputable def padicIntSingleTwo (v : ℤ_[2]) : ∀ ℓ : Nat.Primes, ℤ_[(ℓ : ℕ)] :=
  Pi.single (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) (⟨2, Nat.prime_two⟩ : Nat.Primes) v

theorem padicIntSingleTwo_two (v : ℤ_[2]) : padicIntSingleTwo v ⟨2, Nat.prime_two⟩ = v :=
  Pi.single_eq_same (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) _ _

theorem padicIntSingleTwo_of_ne (v : ℤ_[2]) {ℓ : Nat.Primes} (h : ℓ ≠ ⟨2, Nat.prime_two⟩) :
    padicIntSingleTwo v ℓ = 0 :=
  Pi.single_eq_of_ne (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) h _

@[simp] theorem padicIntSingleTwo_zero : padicIntSingleTwo 0 = 0 :=
  Pi.single_zero (M := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) _

theorem padicIntSingleTwo_add (u v : ℤ_[2]) :
    padicIntSingleTwo (u + v) = padicIntSingleTwo u + padicIntSingleTwo v :=
  Pi.single_add (f := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) _ _ _

theorem continuous_padicIntSingleTwo : Continuous padicIntSingleTwo := by
  unfold padicIntSingleTwo
  exact continuous_single (A := fun ℓ : Nat.Primes => ℤ_[(ℓ : ℕ)]) (⟨2, Nat.prime_two⟩ : Nat.Primes)

/-- **The `ℤ₂`-section of `TauCeti.zHat.component 2`**: `v ↦ (v, 0, 0, …)` under the product
decomposition `ℤ̂ ≅ ∏ ℤ_ℓ`. -/
noncomputable def zhatSectionTwo (v : ℤ_[2]) : Additive TauCeti.zHat.{0} :=
  TauCeti.zHat.ringEquivPiPadicInt.symm (padicIntSingleTwo v)

/-- The `2`-adic component of `zhatSectionTwo v` is `v`. -/
@[simp]
theorem component_two_zhatSectionTwo (v : ℤ_[2]) :
    TauCeti.zHat.component 2 (zhatSectionTwo v) = v := by
  rw [zhatSectionTwo]
  exact (TauCeti.zHat.component_ringEquivPiPadicInt_symm _ ⟨2, Nat.prime_two⟩).trans
    (padicIntSingleTwo_two v)

/-- The odd components of `zhatSectionTwo v` vanish. -/
theorem component_zhatSectionTwo_of_ne {ℓ : ℕ} [Fact ℓ.Prime] (h : ℓ ≠ 2) (v : ℤ_[2]) :
    TauCeti.zHat.component ℓ (zhatSectionTwo v) = 0 := by
  rw [zhatSectionTwo]
  exact (TauCeti.zHat.component_ringEquivPiPadicInt_symm _ ⟨ℓ, Fact.out⟩).trans
    (padicIntSingleTwo_of_ne v fun h' => h (Subtype.mk_eq_mk.mp h'))

theorem continuous_zhatSectionTwo : Continuous zhatSectionTwo :=
  TauCeti.zHat.continuous_ringEquivPiPadicInt_symm.comp continuous_padicIntSingleTwo

@[simp] theorem zhatSectionTwo_zero : zhatSectionTwo 0 = 0 := by
  rw [zhatSectionTwo, padicIntSingleTwo_zero, map_zero]

theorem zhatSectionTwo_add (u v : ℤ_[2]) :
    zhatSectionTwo (u + v) = zhatSectionTwo u + zhatSectionTwo v := by
  rw [zhatSectionTwo, zhatSectionTwo, zhatSectionTwo, padicIntSingleTwo_add, map_add]

/-- At `v = 1` the section is Tau Ceti's idempotent `ω₂ = zHat.idem 2`. -/
@[simp] theorem zhatSectionTwo_one : zhatSectionTwo 1 = TauCeti.zHat.idem 2 :=
  TauCeti.zHat.ext_of_component fun ℓ _ => by
    rw [TauCeti.zHat.component_idem]
    split_ifs with h
    · subst h
      exact component_two_zhatSectionTwo 1
    · exact component_zhatSectionTwo_of_ne h 1

/-! ## `ℤ₂`-powers (`zpowZtwo = padicPow`) and `x ^ᶻ ω₂ = x` -/

section ZpowZtwo

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
  [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]

/-- **gq2's `ℤ₂`-power is Tau Ceti's `padicPow`**, by Tau Ceti's uniqueness of the continuous
extension of `k ↦ x ^ k` from `ℕ` (`eq_padicPow_of_continuous`). -/
theorem zpowZtwo_eq_padicPow (hP : GQ2.IsProP 2 P) (x : P) (u : ℤ_[2]) :
    GQ2.zpowZtwo hP x u = (toTauCetiIsProP hP).padicPow x u :=
  TauCeti.IsProP.eq_padicPow_of_continuous _ (GQ2.continuous_zpowZtwo hP x)
    (GQ2.zpowZtwo_natCast hP x) u

/-- On a pro-`2` group, gq2's `ẑ`-power `x ^ᶻ γ` is Tau Ceti's `2`-adic power at the `2`-adic
component of `γ` (via `zhatEquiv`). -/
theorem zpowHat_eq_padicPow (hP : GQ2.IsProP 2 P) (x : P) (γ : GQ2.Zhat) :
    x ^ᶻ γ = (toTauCetiIsProP hP).padicPow x
      (TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv γ))) := by
  rw [GQ2.zpowHat_eq_zpowZtwo hP x γ, toAdd_zhatProjTwo_eq_component, zpowZtwo_eq_padicPow]

/-- **`x ^ᶻ ω₂ = x` on pro-`2` groups**: a `module`-importable copy of
`GQ2.zpowHat_omega2_eq_self` (`GQ2/AnabelianBridge/Construction.lean`, not a `module`, so B8
cannot import it).  Through every finite quotient (a `2`-group) `ω₂` acts as `powOmega2`, which
is the identity on elements of `2`-power order. -/
theorem zpowHat_omega2_eq_self_of_isProP_two (hP : GQ2.IsProP 2 P) (x : P) :
    x ^ᶻ GQ2.omega2 = x := by
  have hmem : ∀ U : OpenNormalSubgroup P, (x ^ᶻ GQ2.omega2) * x⁻¹ ∈ U := by
    intro U
    have : DiscreteTopology (P ⧸ U.toSubgroup) := by
      refine discreteTopology_of_isOpen_singleton_one ?_
      have hpre : (QuotientGroup.mk : P → P ⧸ U.toSubgroup) ⁻¹' {1}
          = (U.toSubgroup : Set P) := by
        ext δ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          QuotientGroup.eq_one_iff]
      rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
      exact U.isOpen'
    have : Finite (P ⧸ U.toSubgroup) := Subgroup.quotient_finite_of_isOpen _ U.isOpen'
    have hω := GQ2.map_zpowHat_omega2 (P := P ⧸ U.toSubgroup)
      { toMonoidHom := QuotientGroup.mk' U.toSubgroup
        continuous_toFun := continuous_quot_mk } x
    have hω' : QuotientGroup.mk' U.toSubgroup (x ^ᶻ GQ2.omega2)
        = GQ2.powOmega2 (QuotientGroup.mk' U.toSubgroup x) := hω
    obtain ⟨k, hk⟩ := (hP U) (QuotientGroup.mk' U.toSubgroup x)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    have hself : GQ2.powOmega2 (QuotientGroup.mk' U.toSubgroup x)
        = QuotientGroup.mk' U.toSubgroup x := GQ2.powOmega2_eq_self_of_orderOf_two_pow hj
    have hone : QuotientGroup.mk' U.toSubgroup ((x ^ᶻ GQ2.omega2) * x⁻¹) = 1 := by
      rw [map_mul, map_inv, hω', hself, mul_inv_cancel]
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hone
  have hprod := GQ2.eq_one_of_forall_mem_openNormalSubgroup hmem
  rwa [mul_inv_eq_one] at hprod

end ZpowZtwo

/-- gq2's `ω₂` projects to `1 ∈ ℤ₂` (the `hι_proj`/`hι_one` compatibility B8 needs). -/
theorem zhatProjTwo_omega2 : GQ2.zhatProjTwo GQ2.omega2 = ofAdd (1 : ℤ_[2]) :=
  zpowHat_omega2_eq_self_of_isProP_two GQ2.PropOneOne.isProP_two_multPadicInt (ofAdd (1 : ℤ_[2]))

/-- The `2`-adic component of (the Tau Ceti image of) gq2's `ω₂` is `1`. -/
@[simp]
theorem component_two_zhatEquiv_omega2 :
    TauCeti.zHat.component 2 (Additive.ofMul (zhatEquiv GQ2.omega2)) = 1 := by
  have h := zhatProjTwo_omega2
  rw [zhatProjTwo_eq_component] at h
  exact ofAdd.injective h

end GQ2.TauCetiBridge
