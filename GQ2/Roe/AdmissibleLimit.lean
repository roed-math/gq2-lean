/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.GammaR
public import GQ2.MaxProP
public import GQ2.AdmissibleLimit

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The universal marking is `R`-admissible in the limit  (Roe note Definition 1.1 ⟦def:GammaR⟧)

`Γ_R = F₄ ⧸ N_R` (`GQ2/Roe/GammaR.lean`) is the largest quotient of the free profinite group `F₄`
all of whose finite quotients are `R`-admissible.  This file is the Roe-candidate clone of
`GQ2/AdmissibleLimit.lean`: it proves the three facts the Roe Prop. 2.3 (ticket R4) needs about
`Γ_R` itself:

* **relators die in the limit**: `tameRelator_mem_NR` / `wildRelatorR_mem_NR` — the profinite
  relator words of the universal marking (the tame relation and the Roe wild relation) lie in
  `N_R`, i.e. their images in `Γ_R` are `1` (`quotientMk_NR_tameRelator_eq_one` /
  `quotientMk_wildRelatorR_eq_one`);
* **the `R`-admissible opens are exactly the opens above `N_R`** (`isAdmissibleUR_iff_NR_le`) — the
  order-theoretic form of "`Γ_R`'s finite quotients are the `R`-admissible quotients";
* **the wild pair's closed normal closure is pro-2 in the limit** (`isProP_wildCoreR`).

## Design note

The word-independent engine is reused verbatim from `GQ2/AdmissibleLimit.lean` (imported): the
generation clause `generates_univMarking_map`, the subdirect 2-core lemma
`isPGroup_normalClosure_image_inf`, and `Marking.map_map` are shared with `Γ_A`.  Only the
wild-relation-carrying and `N_R`/`IsAdmissibleUR`-carrying statements are re-derived here with an
`R` suffix — the Roe bridge `map_wildRelatorR_eq_one_iff` (`GQ2/Roe/GammaR.lean`) replaces
`map_wildRelator_eq_one_iff`, and `map_admissibleR` replaces `map_admissible` in the domination
pushforward.  No new axioms (`#print axioms` = the standard three throughout).
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## The relator words lie in `N_R`  (result (i))

Each `R`-admissible open normal `U` kills both relator words (the finite-level relations of
`IsAdmissibleUR` read back through the profinite⟺finite bridges — `map_tameRelator_eq_one_iff` of
`GQ2/GammaA.lean` for the shared tame relation, `map_wildRelatorR_eq_one_iff` of
`GQ2/Roe/GammaR.lean` for the Roe wild relation), so the words lie in the intersection `N_R`. -/

section Relators

/-- An `R`-admissible open normal subgroup contains the tame relator word. -/
theorem tameRelator_mem_of_isAdmissibleUR {U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))}
    (hU : IsAdmissibleUR U) : univMarking.tameRelator ∈ U.toSubgroup :=
  (QuotientGroup.eq_one_iff _).mp
    ((Marking.map_tameRelator_eq_one_iff (quotientMk U.toSubgroup) univMarking).mpr hU.2.1)

/-- An `R`-admissible open normal subgroup contains the Roe wild relator word. -/
theorem wildRelatorR_mem_of_isAdmissibleUR {U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))}
    (hU : IsAdmissibleUR U) : univMarking.wildRelatorR ∈ U.toSubgroup :=
  (QuotientGroup.eq_one_iff _).mp
    ((Marking.map_wildRelatorR_eq_one_iff (quotientMk U.toSubgroup) univMarking).mpr hU.2.2.1)

/-- **The tame relator word lies in `N_R`** — the tame relation holds in `Γ_R`. -/
theorem tameRelator_mem_NR : univMarking.tameRelator ∈ NR := by
  rw [NR, Subgroup.mem_iInf]
  exact fun U => tameRelator_mem_of_isAdmissibleUR U.2

/-- **The Roe wild relator word lies in `N_R`** — the Roe wild relation holds in `Γ_R`. -/
theorem wildRelatorR_mem_NR : univMarking.wildRelatorR ∈ NR := by
  rw [NR, Subgroup.mem_iInf]
  exact fun U => wildRelatorR_mem_of_isAdmissibleUR U.2

/-- The tame relation in `Γ_R`: the image of the tame relator word is trivial. -/
@[simp] theorem quotientMk_NR_tameRelator_eq_one :
    quotientMk NR univMarking.tameRelator = 1 :=
  (quotientMk_eq_one_iff NR).mpr tameRelator_mem_NR

/-- The Roe wild relation in `Γ_R`: the image of the Roe wild relator word is trivial. -/
@[simp] theorem quotientMk_wildRelatorR_eq_one :
    quotientMk NR univMarking.wildRelatorR = 1 :=
  (quotientMk_eq_one_iff NR).mpr wildRelatorR_mem_NR

end Relators

/-! ## Directedness of the `R`-admissible family  (Roe Lemma 2.1 in the limit)

The `R`-admissible open normal subgroups form a *directed* family: the trivial quotient is
`R`-admissible, and `R`-admissibility is closed under `⊓`.  Compactness then gives **`R`-admissible
domination**: every open normal subgroup above `N_R` contains an `R`-admissible one, hence is
itself `R`-admissible — the `R`-admissible opens are *exactly* the opens above `N_R`. -/

section Directed

/-- **The trivial quotient is `R`-admissible**: all four clauses are trivial in a subsingleton. -/
theorem isAdmissibleUR_top :
    IsAdmissibleUR (topOpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) := by
  haveI hsub : Subsingleton (FreeProfiniteGroup (Fin 4) ⧸
      (topOpenNormalSubgroup (FreeProfiniteGroup (Fin 4))).toSubgroup) :=
    QuotientGroup.subsingleton_quotient_top
  refine ⟨?_, Subsingleton.elim _ _, Subsingleton.elim _ _, fun g => ⟨0, Subtype.ext ?_⟩⟩
  · rw [Marking.Generates, Subgroup.eq_top_iff']
    exact fun x => (Subsingleton.elim 1 x) ▸ one_mem _
  · exact Subsingleton.elim _ _

/-- The wild pair of a pushed marking is the image of the wild pair (word-independent; re-declared
here since `GQ2.AdmissibleLimit`'s copy is private). -/
private lemma image_wild_pair {H : Type*} [Group H] (f : FreeProfiniteGroup (Fin 4) →* H) :
    ({(univMarking.map f).x₀, (univMarking.map f).x₁} : Set H)
      = f '' {univMarking.x₀, univMarking.x₁} := by
  rw [Set.image_pair]
  rfl

/-- **`R`-admissibility is closed under intersections** (Roe Lemma 2.1, subdirect closure). -/
theorem isAdmissibleUR_inf {U V : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))}
    (hU : IsAdmissibleUR U) (hV : IsAdmissibleUR V) : IsAdmissibleUR (U ⊓ V) := by
  refine ⟨generates_univMarking_map _, ?_, ?_, ?_⟩
  · -- tame relation: the tame relator word lies in `U ⊓ V`
    exact (Marking.map_tameRelator_eq_one_iff (quotientMk (U ⊓ V).toSubgroup) univMarking).mp
      ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_inf.mpr
        ⟨tameRelator_mem_of_isAdmissibleUR hU, tameRelator_mem_of_isAdmissibleUR hV⟩))
  · -- Roe wild relation: the Roe wild relator word lies in `U ⊓ V`
    exact (Marking.map_wildRelatorR_eq_one_iff (quotientMk (U ⊓ V).toSubgroup) univMarking).mp
      ((QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_inf.mpr
        ⟨wildRelatorR_mem_of_isAdmissibleUR hU, wildRelatorR_mem_of_isAdmissibleUR hV⟩))
  · -- 2-core, subdirectly (word-independent engine reused from `GQ2/AdmissibleLimit.lean`)
    have hA := hU.2.2.2
    have hB := hV.2.2.2
    rw [Marking.Pro2Core, image_wild_pair] at hA hB
    rw [Marking.Pro2Core, image_wild_pair]
    exact isPGroup_normalClosure_image_inf {univMarking.x₀, univMarking.x₁}
      U.toSubgroup V.toSubgroup hA hB

/-- **`R`-admissible domination.**  Every open normal subgroup of `F₄` containing `N_R` contains an
*`R`-admissible* open normal subgroup. -/
theorem exists_isAdmissibleUR_le {W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))}
    (hle : NR ≤ W.toSubgroup) :
    ∃ U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)),
      IsAdmissibleUR U ∧ U.toSubgroup ≤ W.toSubgroup := by
  by_contra hcon
  replace hcon : ∀ U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)), IsAdmissibleUR U →
      ¬ U.toSubgroup ≤ W.toSubgroup := fun U hU h => hcon ⟨U, hU, h⟩
  set ι := {U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) // IsAdmissibleUR U} with hι
  haveI : Nonempty ι := ⟨⟨topOpenNormalSubgroup _, isAdmissibleUR_top⟩⟩
  set t : ι → Set (FreeProfiniteGroup (Fin 4)) :=
    fun U => (U.1 : Set (FreeProfiniteGroup (Fin 4))) ∩ (W.toSubgroup : Set _)ᶜ with ht
  have htn : ∀ U, (t U).Nonempty :=
    fun U => SetLike.not_le_iff_exists.mp (hcon U.1 U.2)
  have htcl : ∀ U, IsClosed (t U) :=
    fun U => (U.1.toOpenSubgroup.isClosed).inter W.toOpenSubgroup.isOpen.isClosed_compl
  have htc : ∀ U, IsCompact (t U) := fun U => (htcl U).isCompact
  have htd : Directed (· ⊇ ·) t := by
    intro U V
    exact ⟨⟨U.1 ⊓ V.1, isAdmissibleUR_inf U.2 V.2⟩,
      Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr inf_le_left),
      Set.inter_subset_inter_left _ (SetLike.coe_subset_coe.mpr inf_le_right)⟩
  obtain ⟨x, hx⟩ :=
    IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed t htd htn htc htcl
  rw [Set.mem_iInter] at hx
  have hxNR : x ∈ NR := by
    rw [NR, Subgroup.mem_iInf]
    exact fun U => (hx U).1
  exact (hx (Classical.arbitrary ι)).2 (hle hxNR)

/-- Every open normal subgroup above `N_R` is itself `R`-admissible: push the marking forward from
a dominating `R`-admissible `U` along `F₄ ⧸ U ↠ F₄ ⧸ W` (Roe Lemma 2.2, `Marking.map_admissibleR`). -/
theorem isAdmissibleUR_of_NR_le {W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))}
    (hle : NR ≤ W.toSubgroup) : IsAdmissibleUR W := by
  obtain ⟨U, hU, hUW⟩ := exists_isAdmissibleUR_le hle
  have hcomap : U.toSubgroup ≤ Subgroup.comap (MonoidHom.id _) W.toSubgroup := by
    simpa using hUW
  set π : (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) →*
      (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup) :=
    QuotientGroup.map U.toSubgroup W.toSubgroup (MonoidHom.id _) hcomap with hπ
  have hπs : Function.Surjective π := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W.toSubgroup y
    refine ⟨QuotientGroup.mk' U.toSubgroup g, ?_⟩
    rw [hπ, QuotientGroup.map_mk']
    rfl
  have hcomp : π.comp (QuotientGroup.mk' U.toSubgroup) = QuotientGroup.mk' W.toSubgroup := by
    ext x
    rw [MonoidHom.comp_apply, hπ, QuotientGroup.map_mk']
    rfl
  have hpush : univMarking.map (QuotientGroup.mk' W.toSubgroup)
      = (univMarking.map (QuotientGroup.mk' U.toSubgroup)).map π := by
    rw [Marking.map_map, hcomp]
  rw [IsAdmissibleUR, hpush]
  exact Marking.map_admissibleR π hπs _ hU

/-- **The `R`-admissible opens are exactly the opens above `N_R`** — the order-theoretic form of
"`Γ_R = F₄ ⧸ N_R` is the largest quotient all of whose finite quotients are `R`-admissible".  This
is the interface the Roe Prop. 2.3 (ticket R4) consumes. -/
theorem isAdmissibleUR_iff_NR_le (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) :
    IsAdmissibleUR U ↔ NR ≤ U.toSubgroup :=
  ⟨fun h => iInf_le (fun V : {V : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) //
      IsAdmissibleUR V} => V.1.toSubgroup) ⟨U, h⟩, isAdmissibleUR_of_NR_le⟩

end Directed

/-! ## The wild pair's closed normal closure is pro-2  (result (ii))

The pro-2 clause holds *in the limit* for `Γ_R`: the closed normal subgroup of `Γ_R` generated by
the images of `x₀, x₁` is a pro-2 group.  Same limit argument as `GQ2/AdmissibleLimit.lean`, now
routed through the `R`-admissible family. -/

section WildCore

/-- **The wild core of `Γ_R`**: the closed normal closure `⟨⟨x₀, x₁⟩⟩ ≤ Γ_R` of the images of the
wild generators — the subgroup that Definition 1.1 requires to be pro-2.  Roe counterpart of
`GQ2.wildCore`. -/
noncomputable def wildCoreR : Subgroup (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  (Subgroup.normalClosure
    {quotientMk NR univMarking.x₀, quotientMk NR univMarking.x₁}).topologicalClosure

instance wildCoreR_normal : wildCoreR.Normal :=
  Subgroup.is_normal_topologicalClosure _

lemma wildCoreR_isClosed : IsClosed (wildCoreR : Set (FreeProfiniteGroup (Fin 4) ⧸ NR)) :=
  Subgroup.isClosed_topologicalClosure _

/-- **The wild core is pro-2** (Definition 1.1's pro-2 clause, in the limit): every finite
continuous quotient of `⟨⟨x₀, x₁⟩⟩ ≤ Γ_R` is a 2-group.  Roe counterpart of `GQ2.isProP_wildCore`;
same limit argument (see the `GQ2/AdmissibleLimit.lean` module docstring), routed through the
`R`-admissible family. -/
theorem isProP_wildCoreR : IsProP 2 wildCoreR := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  intro V x
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective x
  -- Step A: an open normal `W ≤ Γ_R` with `W ∩ wildCoreR ≤ V`
  obtain ⟨O, hOopen, hOV⟩ := isOpen_induced_iff.mp V.toOpenSubgroup.isOpen
  have h1O : (1 : FreeProfiniteGroup (Fin 4) ⧸ NR) ∈ O := by
    have h1V : (1 : wildCoreR) ∈ Subtype.val ⁻¹' O := by
      rw [hOV]
      exact one_mem V.toOpenSubgroup
    exact h1V
  obtain ⟨W, hWO⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  -- Step B: pull `W` back to an `R`-admissible open normal subgroup `Ŵ ≥ N_R` of `F₄`
  set Ŵ : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := Subgroup.comap (QuotientGroup.mk' NR) W.toSubgroup
      isOpen' := W.toOpenSubgroup.isOpen.preimage continuous_quotient_mk'
      isNormal' := W.isNormal'.comap _ } with hŴ
  have hNRle : NR ≤ Ŵ.toSubgroup := by
    intro g hg
    show QuotientGroup.mk' NR g ∈ W.toSubgroup
    have h1 : QuotientGroup.mk' NR g = 1 := (QuotientGroup.eq_one_iff g).mpr hg
    rw [h1]
    exact one_mem _
  have hcore := (isAdmissibleUR_of_NR_le hNRle).2.2.2
  rw [Marking.Pro2Core, image_wild_pair] at hcore
  -- Step C: `m` agrees modulo `W` with an element of the abstract normal closure
  have hmcl : (m : FreeProfiniteGroup (Fin 4) ⧸ NR) ∈ closure
      ((Subgroup.normalClosure
        {quotientMk NR univMarking.x₀, quotientMk NR univMarking.x₁} :
          Subgroup (FreeProfiniteGroup (Fin 4) ⧸ NR)) : Set (FreeProfiniteGroup (Fin 4) ⧸ NR)) := by
    rw [← Subgroup.topologicalClosure_coe]
    exact m.2
  have himg : (QuotientGroup.mk' W.toSubgroup) (m : FreeProfiniteGroup (Fin 4) ⧸ NR)
      ∈ closure ((QuotientGroup.mk' W.toSubgroup) ''
          ((Subgroup.normalClosure
            {quotientMk NR univMarking.x₀, quotientMk NR univMarking.x₁} :
              Subgroup (FreeProfiniteGroup (Fin 4) ⧸ NR)) :
                Set (FreeProfiniteGroup (Fin 4) ⧸ NR))) :=
    image_closure_subset_closure_image continuous_quotient_mk' ⟨_, hmcl, rfl⟩
  rw [closure_discrete] at himg
  obtain ⟨nΓ, hnM, hnm⟩ := himg
  -- Step D: lift to the abstract normal closure in `F₄`
  have hMmap : (Subgroup.normalClosure
      {quotientMk NR univMarking.x₀, quotientMk NR univMarking.x₁} :
        Subgroup (FreeProfiniteGroup (Fin 4) ⧸ NR))
      = Subgroup.map (QuotientGroup.mk' NR)
          (Subgroup.normalClosure {univMarking.x₀, univMarking.x₁}) := by
    rw [Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _), Set.image_pair]
    rfl
  rw [SetLike.mem_coe, hMmap] at hnM
  obtain ⟨n', hn', rfl⟩ := hnM
  -- Step E: the 2-core clause of the `R`-admissible `Ŵ` bounds `n'`
  have hmem : (QuotientGroup.mk' Ŵ.toSubgroup) n'
      ∈ Subgroup.normalClosure
          ((QuotientGroup.mk' Ŵ.toSubgroup) '' {univMarking.x₀, univMarking.x₁}) := by
    rw [← Subgroup.map_normalClosure _ _ (QuotientGroup.mk'_surjective _)]
    exact ⟨n', hn', rfl⟩
  obtain ⟨k, hk⟩ := hcore ⟨_, hmem⟩
  refine ⟨k, ?_⟩
  -- Step F: transfer the 2-power bound back through `W` and `V`
  have hn'W : (QuotientGroup.mk' NR n') ^ 2 ^ k ∈ W.toSubgroup := by
    have h := congrArg Subtype.val hk
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one, ← map_pow] at h
    have hŴmem : n' ^ 2 ^ k ∈ Ŵ.toSubgroup := (QuotientGroup.eq_one_iff _).mp h
    rw [← map_pow]
    exact hŴmem
  have hmW : (m : FreeProfiniteGroup (Fin 4) ⧸ NR) ^ 2 ^ k ∈ W.toSubgroup := by
    have h : (QuotientGroup.mk' W.toSubgroup)
        ((m : FreeProfiniteGroup (Fin 4) ⧸ NR) ^ 2 ^ k) = 1 := by
      rw [map_pow, ← hnm, ← map_pow]
      exact (QuotientGroup.eq_one_iff _).mpr hn'W
    exact (QuotientGroup.eq_one_iff _).mp h
  have hmV : m ^ 2 ^ k ∈ V.toSubgroup := by
    have hpre : (m ^ 2 ^ k : wildCoreR) ∈ Subtype.val ⁻¹' O :=
      hWO (by rw [SubgroupClass.coe_pow]; exact hmW)
    rwa [hOV] at hpre
  have h1 : (QuotientGroup.mk' V.toSubgroup) (m ^ 2 ^ k) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hmV
  rw [map_pow] at h1
  exact h1

end WildCore

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Definition 1.1 = ⟦def:GammaR⟧
-/
