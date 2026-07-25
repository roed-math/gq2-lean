/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Prop23
import GQ2.Roe.AdmissibleLimit

/-!
# Proposition 2.3 for `Γ_R`: `|Sur(Γ_R, G)| = admissibleCountR G`  (Roe note Definition 1.1)

The Roe-candidate twin of `GQ2/Prop23.lean` (paper **Prop. 2.3** ⟦prop-epi-semantics⟧, §2.2): for
every finite discrete group `G`, continuous surjections `Γ_R ↠ G` correspond bijectively to
*`R`-admissible* marked generating quadruples in `G` (note Definition 1.1 ⟦def:GammaR⟧), so

  `prop_2_3_R : Nat.card (ContSurj GammaR G) = admissibleCountR G`.

This is the `Γ_R` half of the surjection-count semantics; `prop_2_3_R` is stated in exactly the
shape the Roe main-presentation schematic (ticket R32) consumes, mirroring how `prop_2_3` feeds
`main_presentation` (`GQ2/Statement.lean`, via `GQ2/PresentationLiteral.lean`).

## What is cloned and what is reused

Only the parts where the **Roe wild relation** actually enters are re-derived with an `R`-suffix;
the word-independent round-trip scaffolding is imported and reused verbatim:

* **reused** (word-independent, from `GQ2/GammaA.lean` and `GQ2/Prop23.lean`): `univMarking`,
  `Marking.toHom`, `univMarking_map_toHom`, `Marking.toHom_hom_univMarking_map`, `quotientMk`,
  `quotientLift`, `surjective_of_map_generates`, and — crucially — `Marking.classify` itself (the
  classified hom of a marking is `toHom`-only, no relator enters);
* **cloned** (the Roe wild relation enters through `AdmissibleR`/`N_R`): `admissibleR_of_NR_le_ker`
  (converse of R3's `NR_le_ker`, proved from R3's `isAdmissibleUR_of_NR_le` +
  `Marking.map_admissibleR`), `Marking.pushR`, `Marking.pushR_admissible`, `Marking.classifyR_ker`
  (via `NR_le_ker`), `Marking.descendR` and its round trips, `contSurjEquivAdmissibleR`, and
  `prop_2_3_R`.

## §5-duality supply input

The section `markC_R` / `markC_admissible_R` (the Roe twin of `GQ2.WordCohBridge.markC` /
`markC_admissible`, `GQ2/WordCohBridge.lean`) is colocated here for convenience — it is *not* a
`prop_2_3_R` dependency, but the input the §5 word-cohomology self-duality (`prop_5_15_R`, tickets
R26/R31) consumes at `markC_R θ`, in the same `adm.1 / adm.2.1 / adm.2.2.1 / adm.2.2.2` projection
shape (`Generates / TameRel / WildRelR / Pro2Core`) as `GQ2/MStageCountGammaA.lean`.

Everything is at the standard three axioms (`Ax = ∅`).
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## The universal property, uniqueness half — REUSED

`Marking.toHom_hom_univMarking_map` (`GQ2/Prop23.lean`) is word-independent (it mentions only
`univMarking`/`Marking.toHom`), so it is imported and reused; no `R`-suffix twin is needed. -/

/-! ## The converse of `NR_le_ker` -/

/-- **Converse of R3's `NR_le_ker`** (Roe twin of `GQ2.admissible_of_NA_le_ker`): if a continuous
homomorphism `f : F₄ → G` into a finite discrete group is surjective and kills `N_R`, then the
pushed universal marking of `G` is `R`-admissible.  Proof cloned verbatim from the `Γ_A` case,
swapping `isAdmissibleU_of_NA_le → isAdmissibleUR_of_NR_le`, `IsAdmissibleU → IsAdmissibleUR` and
`Marking.map_admissible → Marking.map_admissibleR`: `ker f` is then an open normal subgroup above
`N_R`, hence `R`-admissible (`isAdmissibleUR_of_NR_le`, `GQ2/Roe/AdmissibleLimit.lean`), and
`R`-admissibility transfers to `G` along `F₄ ⧸ ker f ≃* G` (`Marking.map_admissibleR`,
`GQ2/Roe/GammaR.lean`).  Together with `NR_le_ker` this is the note's "quotients of `Γ_R` = the
`R`-admissible quotients". -/
theorem admissibleR_of_NR_le_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [Finite G] (f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) G)
    (hsurj : Function.Surjective f) (hker : NR ≤ f.toMonoidHom.ker) :
    (univMarking.map f.toMonoidHom).AdmissibleR := by
  -- the kernel, as an (`R`-admissible) open normal subgroup
  have hker_open :
      IsOpen ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = f ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set G)).preimage f.continuous_toFun
  have hadmU : IsAdmissibleUR
      { toSubgroup := f.toMonoidHom.ker, isOpen' := hker_open :
          OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) } :=
    isAdmissibleUR_of_NR_le hker
  -- transfer along the induced isomorphism `F₄ ⧸ ker f ≃* G`
  set e : (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hsurj with he
  haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) :=
    Finite.of_equiv G e.symm.toEquiv
  have hpush : univMarking.map f.toMonoidHom
      = (univMarking.map (QuotientGroup.mk' f.toMonoidHom.ker)).map e.toMonoidHom := rfl
  rw [IsAdmissibleUR] at hadmU
  rw [hpush]
  exact Marking.map_admissibleR e.toMonoidHom e.surjective _ hadmU

/-! ## The two directions of the bijection, as named constructions -/

section Bijection

variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- The marking of `G` pushed forward from the universal marking along `φ : F₄ ⧸ N_R → G`.  Roe
twin of `GQ2.Marking.push`. -/
noncomputable def Marking.pushR (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) G) :
    Marking G :=
  univMarking.map ((φ.comp (quotientMk NR)).toMonoidHom)

/-- The pushed marking of a continuous **surjection** is `R`-admissible (forward direction of
`prop_2_3_R`).  Roe twin of `GQ2.Marking.push_admissible`. -/
theorem Marking.pushR_admissible
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) G)
    (hφ : Function.Surjective φ) : (Marking.pushR φ).AdmissibleR := by
  refine admissibleR_of_NR_le_ker _ (hφ.comp (quotientMk_surjective NR)) fun x hx => ?_
  rw [MonoidHom.mem_ker]
  show φ (quotientMk NR x) = 1
  rw [(quotientMk_eq_one_iff NR).mpr hx, map_one]

/-- The kernel certificate of an `R`-admissible marking's classified hom (Roe twin of the private
`GQ2.Marking.classify_ker`; `Marking.classify` itself is word-independent and reused). -/
private lemma Marking.classifyR_ker (t : Marking G) (ht : t.AdmissibleR) :
    NR ≤ (Marking.classify t).toMonoidHom.ker := by
  refine NR_le_ker _ ?_
  rwa [Marking.classify, univMarking_map_toHom]

/-- The descended hom `Γ_R → G` of an `R`-admissible marking (backward direction of `prop_2_3_R`).
Roe twin of `GQ2.Marking.descend`. -/
noncomputable def Marking.descendR (t : Marking G) (ht : t.AdmissibleR) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) G :=
  quotientLift NR (Marking.classify t) (Marking.classifyR_ker t ht)

@[simp] private lemma Marking.descendR_quotientMk (t : Marking G) (ht : t.AdmissibleR)
    (x : FreeProfiniteGroup (Fin 4)) :
    Marking.descendR t ht (quotientMk NR x) = Marking.classify t x := rfl

theorem Marking.descendR_surjective (t : Marking G) (ht : t.AdmissibleR) :
    Function.Surjective (Marking.descendR t ht) := by
  have hsurj : Function.Surjective (Marking.classify t) := by
    refine surjective_of_map_generates _ ?_
    rw [Marking.classify, univMarking_map_toHom]
    exact ht.1
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨quotientMk NR x, hx⟩

/-- Pushing the descended hom recovers the marking (round-trip 1).  Roe twin of
`GQ2.Marking.push_descend`. -/
theorem Marking.pushR_descendR (t : Marking G) (ht : t.AdmissibleR) :
    Marking.pushR (Marking.descendR t ht) = t := by
  have hcomp : ((Marking.descendR t ht).comp (quotientMk NR)).toMonoidHom
      = (Marking.classify t).toMonoidHom := rfl
  rw [Marking.pushR, hcomp, Marking.classify, univMarking_map_toHom]

/-- Descending the pushed marking recovers the surjection (round-trip 2, via the uniqueness half of
the universal property `Marking.toHom_hom_univMarking_map`).  Roe twin of
`GQ2.Marking.descend_push`. -/
theorem Marking.descendR_pushR
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) G)
    (hφ : Function.Surjective φ) :
    Marking.descendR (Marking.pushR φ) (Marking.pushR_admissible φ hφ) = φ := by
  ext y
  obtain ⟨x, rfl⟩ := quotientMk_surjective NR y
  rw [Marking.descendR_quotientMk]
  exact DFunLike.congr_fun (Marking.toHom_hom_univMarking_map (φ.comp (quotientMk NR))) x

end Bijection

/-! ## Prop 2.3 for `Γ_R` -/

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- **Prop. 2.3 for `Γ_R`, bijection form** (paper §2.2 ⟦prop-epi-semantics⟧ / note Definition 1.1
⟦def:GammaR⟧): continuous surjections `Γ_R ↠ G` correspond to `R`-admissible markings of `G`.
(Stated on the underlying quotient `F₄ ⧸ N_R`, to which `GammaR` is definitionally equal.) -/
noncomputable def contSurjEquivAdmissibleR :
    ContSurj (FreeProfiniteGroup (Fin 4) ⧸ NR) G ≃ {t : Marking G // t.AdmissibleR} where
  toFun φ := ⟨Marking.pushR φ.1, Marking.pushR_admissible φ.1 φ.2⟩
  invFun t := ⟨Marking.descendR t.1 t.2, Marking.descendR_surjective t.1 t.2⟩
  left_inv φ := Subtype.ext (Marking.descendR_pushR φ.1 φ.2)
  right_inv t := Subtype.ext (Marking.pushR_descendR t.1 t.2)

/-- **Proposition 2.3 for `Γ_R`** (paper §2.2 ⟦prop-epi-semantics⟧ / note Definition 1.1
⟦def:GammaR⟧): the number of continuous surjections `Γ_R ↠ G` onto a finite discrete group equals
`admissibleCountR G`, the number of `R`-admissible marked generating quadruples in `G`.  Stated in
exactly the `hΓR` shape the Roe `main_presentation` schematic (ticket R32) consumes, mirroring how
`prop_2_3` feeds `main_presentation`. -/
theorem prop_2_3_R : Nat.card (ContSurj GammaR G) = admissibleCountR G :=
  Nat.card_congr (contSurjEquivAdmissibleR G)

/-! ## §5-duality supply: `markC_R` and `markC_admissible_R`

Not a `prop_2_3_R` dependency — colocated for the §5 word-cohomology self-duality (`prop_5_15_R`,
tickets R26/R31).  `markC_R` is the Roe twin of `GQ2.WordCohBridge.markC` (there `markC q =
Marking.push q`), and `markC_admissible_R` wraps `Marking.pushR_admissible`, matching the
`adm.1 / adm.2.1 / adm.2.2.1 / adm.2.2.2` projection shape (`Generates / TameRel / WildRelR /
Pro2Core`) that `GQ2/MStageCountGammaA.lean` feeds to `prop_5_15`. -/

section MarkC

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The pushed marking `t_q : Marking C` of a continuous surjection `q : Γ_R ↠ C` — the Roe twin of
`GQ2.WordCohBridge.markC`, against which the §5 word complex is formed. -/
noncomputable def markC_R (q : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) C) :
    Marking C :=
  Marking.pushR q

/-- The pushed marking of a continuous surjection `q : Γ_R ↠ C` is `R`-admissible — the §5-duality
supply input (`prop_5_15_R`, tickets R26/R31), Roe twin of `GQ2.WordCohBridge.markC_admissible`. -/
theorem markC_admissible_R (q : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) C)
    (hq : Function.Surjective q) : (markC_R q).AdmissibleR :=
  Marking.pushR_admissible q hq

/-- **Stress test (consumption shape).**  The four projections of `markC_admissible_R` land in the
Roe clauses `Generates / TameRel / WildRelR / Pro2Core`, in the `adm.1 / adm.2.1 / adm.2.2.1 /
adm.2.2.2` order that `GQ2/MStageCountGammaA.lean` feeds to `prop_5_15` — so `prop_5_15_R`'s callers
(R26/R31) reuse `markC_admissible_R θ hθs` verbatim.  Pins the Roe wild relation `WildRelR` (not the
`Γ_A` `WildRel`) at the `.2.2.1` slot. -/
theorem markC_admissible_R_clauses
    (q : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NR) C) (hq : Function.Surjective q) :
    (markC_R q).Generates ∧ (markC_R q).TameRel ∧ (markC_R q).WildRelR ∧ (markC_R q).Pro2Core :=
  ⟨(markC_admissible_R q hq).1, (markC_admissible_R q hq).2.1,
    (markC_admissible_R q hq).2.2.1, (markC_admissible_R q hq).2.2.2⟩

end MarkC

end GQ2

/-! ### Paper-tag ledger (paper §2.2 + Roe note `paper/roe-presentation-verification.tex`;
hand-maintained)

  * Proposition 2.3 = ⟦prop-epi-semantics⟧   (the epi-semantics cloned for `Γ_R`)
  * Definition 1.1 = ⟦def:GammaR⟧
-/
