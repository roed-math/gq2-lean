import GQ2.AdmissibleLimit

/-!
# Proposition 2.3: `|Sur(Γ_A, G)| = N(G)`  (ticket P-05)

The paper's **Prop. 2.3** (§2.2): for every finite group `G`, continuous surjections
`Γ_A ↠ G` correspond bijectively to *admissible marked generating quadruples* in `G`, so
`Nat.card (ContSurj Γ_A G) = admissibleCount G`.  This is the `Γ_A` half of the
surjection-count Theorem 1.2 (the `G_{ℚ₂}` half is `main_surjection_count`, Track B); together
with Lemma 2.5 (`reconstruction`, P-02) and t.f.g. (P-03) it yields the literal presentation
form in P-19.

## The bijection

`contSurjEquivAdmissible : ContSurj (F₄ ⧸ N_A) G ≃ {t : Marking G // t.Admissible}`

* **forward**: push the universal marking through `φ ∘ π` (`π : F₄ → F₄ ⧸ N_A` the projection).
  Admissibility is `admissible_of_NA_le_ker` — the **converse of `NA_le_ker`** (T-21): for a
  continuous `f : F₄ → G` into a finite discrete group, *surjective with `N_A ≤ ker f`*, the
  pushed marking is admissible.  Proof: `ker f` is an admissible open normal subgroup
  (`isAdmissibleU_of_NA_le`, P-04), and admissibility transfers along the induced isomorphism
  `F₄ ⧸ ker f ≃* G` (Lemma 2.2, `Marking.map_admissible`).  Together `NA_le_ker` and
  `admissible_of_NA_le_ker` say: *for surjective continuous `f`, the pushed marking is
  admissible iff `N_A ≤ ker f`* — the paper's "quotients of `Γ_A` = admissible quotients".
* **backward** (`Marking.descend`): an admissible `t` classifies `t.toHom : F₄ ⟶ G` (universal
  property of `F₄`), which kills `N_A` by `NA_le_ker`, hence descends along `quotientLift`;
  surjectivity from `t.Generates` (`surjective_of_map_generates`).
* **round-trips**: `univMarking_map_toHom` (T-21) in one direction; in the other, the
  **uniqueness half of the universal property** (`Marking.toHom_univMarking_map`: any morphism
  out of `F₄` is `toHom` of its own pushed marking) plus surjectivity of `π`.
  *Deviation from the board sketch*: topological finite generation (P-03) is **not needed** —
  `homEquiv`-injectivity replaces the density argument for "agreeing on generators ⇒ equal".

The count `Nat.card (ContSurj GammaA G) = admissibleCount G` (`prop_2_3`) is stated in exactly
the `hΓA` shape consumed by `main_presentation` (`GQ2/Statement.lean`), so P-19 can pass it
through verbatim.  Everything is at the standard three axioms (`Ax = ∅`).
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## The universal property, uniqueness half -/


section FiniteTarget

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- `ContinuousMonoidHom`-level form of the uniqueness half: classifying the pushforward of the
universal marking along `c` recovers `c`. -/
lemma Marking.toHom_hom_univMarking_map
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) G) :
    (Marking.toHom (P := ProfiniteGrp.of G) (univMarking.map c.toMonoidHom)).hom = c := by
  have h : Marking.toHom (P := ProfiniteGrp.of G) (univMarking.map c.toMonoidHom)
      = ConcreteCategory.ofHom (C := ProfiniteGrp) c := by
    rw [Marking.toHom, Equiv.symm_apply_eq]
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply]
    fin_cases i <;> rfl
  rw [h]
  rfl

end FiniteTarget

/-! ## The converse of `NA_le_ker` -/

/-- **Converse of `NA_le_ker`** (with it: the paper's characterization of the admissible finite
quotients of `F₄` as exactly the surjections killing `N_A`, §2.1–2.2).  If a continuous
homomorphism `f : F₄ → G` into a finite discrete group is surjective and kills `N_A`, then the
pushed universal marking of `G` is admissible: `ker f` is then an open normal subgroup above
`N_A`, hence admissible (`isAdmissibleU_of_NA_le`, P-04), and admissibility transfers to `G`
along `F₄ ⧸ ker f ≃* G` (Lemma 2.2). -/
theorem admissible_of_NA_le_ker {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G]
    [Finite G] (f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) G)
    (hsurj : Function.Surjective f) (hker : NA ≤ f.toMonoidHom.ker) :
    (univMarking.map f.toMonoidHom).Admissible := by
  -- the kernel, as an (admissible) open normal subgroup
  have hker_open :
      IsOpen ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = f ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set G)).preimage f.continuous_toFun
  have hadmU : IsAdmissibleU
      { toSubgroup := f.toMonoidHom.ker, isOpen' := hker_open :
          OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) } :=
    isAdmissibleU_of_NA_le hker
  -- transfer along the induced isomorphism `F₄ ⧸ ker f ≃* G`
  set e : (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) ≃* G :=
    QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hsurj with he
  haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) :=
    Finite.of_equiv G e.symm.toEquiv
  have hpush : univMarking.map f.toMonoidHom
      = (univMarking.map (QuotientGroup.mk' f.toMonoidHom.ker)).map e.toMonoidHom := rfl
  rw [IsAdmissibleU] at hadmU
  rw [hpush]
  exact Marking.map_admissible e.toMonoidHom e.surjective _ hadmU

/-! ## The two directions of the bijection, as named constructions -/

section Bijection

variable {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- The marking of `G` pushed forward from the universal marking along `φ : F₄ ⧸ N_A → G`. -/
noncomputable def Marking.push (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) G) :
    Marking G :=
  univMarking.map ((φ.comp (quotientMk NA)).toMonoidHom)

/-- The pushed marking of a continuous **surjection** is admissible (forward direction of
Prop 2.3). -/
theorem Marking.push_admissible
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) G)
    (hφ : Function.Surjective φ) : (Marking.push φ).Admissible := by
  refine admissible_of_NA_le_ker _ (hφ.comp (quotientMk_surjective NA)) fun x hx => ?_
  rw [MonoidHom.mem_ker]
  show φ (quotientMk NA x) = 1
  rw [(quotientMk_eq_one_iff NA).mpr hx, map_one]

/-- The classified hom of an admissible marking, as a continuous homomorphism out of `F₄`
(the `gammaA_surjective_s3` ascription pattern). -/
noncomputable def Marking.classify (t : Marking G) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) G :=
  (Marking.toHom (P := ProfiniteGrp.of G) t).hom

lemma Marking.classify_ker (t : Marking G) (ht : t.Admissible) :
    NA ≤ (Marking.classify t).toMonoidHom.ker := by
  refine NA_le_ker _ ?_
  rwa [Marking.classify, univMarking_map_toHom]

/-- The descended hom `Γ_A → G` of an admissible marking (backward direction of Prop 2.3). -/
noncomputable def Marking.descend (t : Marking G) (ht : t.Admissible) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) G :=
  quotientLift NA (Marking.classify t) (Marking.classify_ker t ht)

@[simp] lemma Marking.descend_quotientMk (t : Marking G) (ht : t.Admissible)
    (x : FreeProfiniteGroup (Fin 4)) :
    Marking.descend t ht (quotientMk NA x) = Marking.classify t x := rfl

theorem Marking.descend_surjective (t : Marking G) (ht : t.Admissible) :
    Function.Surjective (Marking.descend t ht) := by
  have hsurj : Function.Surjective (Marking.classify t) := by
    refine surjective_of_map_generates _ ?_
    rw [Marking.classify, univMarking_map_toHom]
    exact ht.1
  intro y
  obtain ⟨x, hx⟩ := hsurj y
  exact ⟨quotientMk NA x, hx⟩

/-- Pushing the descended hom recovers the marking (round-trip 1). -/
theorem Marking.push_descend (t : Marking G) (ht : t.Admissible) :
    Marking.push (Marking.descend t ht) = t := by
  have hcomp : ((Marking.descend t ht).comp (quotientMk NA)).toMonoidHom
      = (Marking.classify t).toMonoidHom := rfl
  rw [Marking.push, hcomp, Marking.classify, univMarking_map_toHom]

/-- Descending the pushed marking recovers the surjection (round-trip 2, via the uniqueness
half of the universal property). -/
theorem Marking.descend_push
    (φ : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA) G)
    (hφ : Function.Surjective φ) :
    Marking.descend (Marking.push φ) (Marking.push_admissible φ hφ) = φ := by
  ext y
  obtain ⟨x, rfl⟩ := quotientMk_surjective NA y
  rw [Marking.descend_quotientMk]
  exact DFunLike.congr_fun (Marking.toHom_hom_univMarking_map (φ.comp (quotientMk NA))) x

end Bijection

/-! ## Prop 2.3 -/

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- **Prop. 2.3, bijection form** (paper §2.2): continuous surjections `Γ_A ↠ G` correspond to
admissible markings of `G`.  (Stated on the underlying quotient `F₄ ⧸ N_A`, to which `GammaA`
is definitionally equal.) -/
noncomputable def contSurjEquivAdmissible :
    ContSurj (FreeProfiniteGroup (Fin 4) ⧸ NA) G ≃ {t : Marking G // t.Admissible} where
  toFun φ := ⟨Marking.push φ.1, Marking.push_admissible φ.1 φ.2⟩
  invFun t := ⟨Marking.descend t.1 t.2, Marking.descend_surjective t.1 t.2⟩
  left_inv φ := Subtype.ext (Marking.descend_push φ.1 φ.2)
  right_inv t := Subtype.ext (Marking.push_descend t.1 t.2)

/-- **Proposition 2.3** (paper §2.2): the number of continuous surjections `Γ_A ↠ G` onto a
finite discrete group equals the number of admissible marked generating quadruples in `G` —
in exactly the `hΓA` shape that `main_presentation` (`GQ2/Statement.lean`) consumes. -/
theorem prop_2_3 : Nat.card (ContSurj GammaA G) = admissibleCount G :=
  Nat.card_congr (contSurjEquivAdmissible G)

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 2.2 = ⟦lem-cofinal⟧
  * Lemma 2.5 = ⟦lem-reconstruction⟧
  * Proposition 2.3 = ⟦prop-epi-semantics⟧
  * Theorem 1.2 = ⟦thm-main⟧
-/
