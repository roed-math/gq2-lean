import Mathlib

/-!
# Lemma 2.5 — one-sided profinite reconstruction

Paper Lemma 2.5: *Let `P` be a topologically finitely generated profinite group and `Q` any
profinite group. If `|Sur(P, H)| = |Sur(Q, H)|` for every finite group `H`, then `P ≅ Q`.*

The proof (paper): finiteness of `Sur(P, Pₙ)` gives, by compactness, an epimorphism `Q ↠ P`;
symmetrically `P ↠ Q`; the composite `P ↠ Q ↠ P` is a surjective endomorphism of a
topologically finitely generated profinite group, which is **Hopfian**, hence an isomorphism.

This is grade **F′**: reachable from `ProfiniteGrp` once the Hopfian property of topologically
f.g. profinite groups is packaged. Stated here; proof deferred.
-/

namespace GQ2

open scoped Classical
open CategoryTheory

/-- Continuous surjections from a topological group `P` onto a finite (discrete) group `H`. -/
def ContSurj (P : Type*) [Group P] [TopologicalSpace P]
    (H : Type*) [Group H] [TopologicalSpace H] : Type _ :=
  {f : ContinuousMonoidHom P H // Function.Surjective f}

/-- A bijective continuous group homomorphism from a compact group to a Hausdorff group is a
topological isomorphism.  (Mirrors `ProfiniteGrp.continuousMulEquivLimittoFiniteQuotientFunctor`,
but stated for bare types so it can be used on the reconstruction hypotheses.) -/
noncomputable def continuousMulEquivOfBijective
    {P Q : Type*} [Group P] [TopologicalSpace P] [Group Q] [TopologicalSpace Q]
    [CompactSpace P] [T2Space Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Bijective f) :
    ContinuousMulEquiv P Q :=
  { Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ hf) f.continuous_toFun with
    map_mul' := f.map_mul' }

/-- For a topologically finitely generated profinite group `P` and a finite discrete group `H`,
there are only finitely many continuous homomorphisms `P → H`: such a hom is determined by its
values on a topological generating set (it is continuous, and two continuous homs agreeing on a
dense subgroup agree everywhere), giving an injection into `s → H`. -/
theorem finite_continuousMonoidHom
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (H : Type*) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H] :
    Finite (ContinuousMonoidHom P H) := by
  obtain ⟨s, hs⟩ := hPfg
  have hdense : Dense (↑(Subgroup.closure (s : Set P)) : Set P) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, hs, Subgroup.coe_top]
  refine Finite.of_injective (fun (φ : ContinuousMonoidHom P H) => fun (x : s) => φ (x : P)) ?_
  intro φ ψ hφψ
  have heq : Set.EqOn (⇑φ.toMonoidHom) (⇑ψ.toMonoidHom) (s : Set P) := by
    intro x hx
    exact congrFun hφψ ⟨x, hx⟩
  have hcl : Set.EqOn (⇑φ.toMonoidHom) (⇑ψ.toMonoidHom) (↑(Subgroup.closure (s : Set P))) :=
    MonoidHom.eqOn_closure heq
  have hfun : (⇑φ : P → H) = ⇑ψ :=
    Continuous.ext_on hdense φ.continuous_toFun ψ.continuous_toFun hcl
  exact DFunLike.coe_injective hfun

/-- **Profinite Hopfian property** (paper Lemma 2.5, key input): a continuous surjective
endomorphism of a *topologically finitely generated* profinite group is injective.  Non-standard;
absent from Mathlib.  Proof idea: a topologically f.g. profinite group has only finitely many open
subgroups of each index, so a surjective endomorphism acts as a surjection — hence a bijection — on
each finite quotient level, forcing injectivity in the limit.  Stated here; proof deferred. -/
theorem profinite_hopfian
    {P : Type*} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (φ : ContinuousMonoidHom P P) (hφ : Function.Surjective φ) :
    Function.Injective φ := by
  rw [injective_iff_map_eq_one]
  intro x hx
  by_contra hx1
  -- Separate `x` from `1` by an open normal subgroup `U`, so `x ∉ U`.
  obtain ⟨U, hUsub⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (U := ({x}ᶜ : Set P)) isOpen_compl_singleton
    (Set.mem_compl_singleton_iff.mpr fun h => hx1 h.symm)
  haveI : DiscreteTopology (P ⧸ U.toSubgroup) := inferInstance
  haveI : Finite (P ⧸ U.toSubgroup) := inferInstance
  -- The (continuous, surjective) projection `π : P ↠ P ⧸ U` onto the finite discrete quotient.
  let π : ContinuousMonoidHom P (P ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩
  have hπx : π x ≠ 1 := by
    intro hcontra
    have hxmem : x ∈ U.toSubgroup := (QuotientGroup.eq_one_iff x).mp hcontra
    exact absurd (hUsub hxmem) (by simp)
  -- `Hom(P, P⧸U)` is finite, and precomposition by the surjection `φ` is injective on it,
  -- hence (finite pigeonhole) surjective: some `β` satisfies `β ∘ φ = π`.
  haveI : Finite (ContinuousMonoidHom P (P ⧸ U.toSubgroup)) :=
    finite_continuousMonoidHom hPfg (P ⧸ U.toSubgroup)
  have hprecomp_inj :
      Function.Injective (fun α : ContinuousMonoidHom P (P ⧸ U.toSubgroup) => α.comp φ) := by
    intro a b hab
    have hcoe : (⇑a : P → _) ∘ ⇑φ = (⇑b : P → _) ∘ ⇑φ := by
      have := congrArg (fun γ : ContinuousMonoidHom P (P ⧸ U.toSubgroup) => (⇑γ : P → _)) hab
      simpa only [ContinuousMonoidHom.coe_comp] using this
    exact DFunLike.coe_injective (hφ.injective_comp_right hcoe)
  obtain ⟨β, hβ⟩ := (Finite.injective_iff_surjective.mp hprecomp_inj) π
  -- Then `π x = β (φ x) = β 1 = 1`, contradicting `π x ≠ 1`.
  apply hπx
  have hβ' : β.comp φ = π := hβ
  rw [← hβ']
  simp only [ContinuousMonoidHom.coe_comp, Function.comp_apply, hx, map_one]

/-- The arithmetic heart of `exists_contSurj_of_card_le`, isolated and proved: under its hypotheses,
`S` continuously surjects onto **every finite quotient** `R ⧸ V` of `R`, and only finitely many
ways.  (The projection witnesses `ContSurj R (R ⧸ V)`, which is finite by `hRfin`, so its count is
`≥ 1`; the count hypothesis `h` transports this to `S`, and `Nat.card_pos_iff` unpacks it as
nonempty-and-finite — the latter automatically, since an infinite level set would have count `0`.)
These level sets, over `V : OpenNormalSubgroup R` (a `SemilatticeInf`, hence cofiltered), are the
nonempty finite objects fed to König in the deferred assembly. -/
theorem contSurj_quotient_nonempty_finite
    {S R : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
      [CompactSpace S] [TotallyDisconnectedSpace S]
    [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
      [CompactSpace R] [TotallyDisconnectedSpace R]
    (hRfin : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Finite (ContSurj R H))
    (h : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nat.card (ContSurj R H) ≤ Nat.card (ContSurj S H))
    (V : OpenNormalSubgroup R) :
    Nonempty (ContSurj S (R ⧸ V.toSubgroup)) ∧ Finite (ContSurj S (R ⧸ V.toSubgroup)) := by
  haveI : Finite (R ⧸ V.toSubgroup) := inferInstance
  haveI : DiscreteTopology (R ⧸ V.toSubgroup) := inferInstance
  -- the projection `R ↠ R ⧸ V` witnesses `ContSurj R (R ⧸ V)`
  have hproj : Nonempty (ContSurj R (R ⧸ V.toSubgroup)) :=
    ⟨⟨⟨QuotientGroup.mk' V.toSubgroup, QuotientGroup.continuous_mk⟩, QuotientGroup.mk_surjective⟩⟩
  haveI : Finite (ContSurj R (R ⧸ V.toSubgroup)) := hRfin _
  have hposR : 0 < Nat.card (ContSurj R (R ⧸ V.toSubgroup)) := Nat.card_pos_iff.mpr ⟨hproj, ‹_›⟩
  have hposS : 0 < Nat.card (ContSurj S (R ⧸ V.toSubgroup)) := lt_of_lt_of_le hposR (h _)
  exact Nat.card_pos_iff.mp hposS

/-! ### König assembly for `exists_contSurj_of_card_le`

The compatible surjections onto the finite quotients are organized by the functor `konigFunctor`
below (`U ↦ {S ↠ R/U}`), whose level sets are nonempty and finite by
`contSurj_quotient_nonempty_finite`; `nonempty_sections_of_finite_cofiltered_system` (König) then
picks a *compatible* choice.  The compatible family is assembled into the surjection `S ↠ R` by an
elementary embedding of `R` into the product of its finite quotients + two applications of Cantor's
intersection theorem — see the `exists_contSurj_of_card_le` proof. -/

section KonigAssembly

variable {R : Type} [Group R] [TopologicalSpace R]

/-- The projection `R/U ↠ R/U'` for `U ≤ U'` (both open normal, so the quotients are discrete). -/
noncomputable def projMap {U U' : Subgroup R} [U.Normal] [U'.Normal]
    [DiscreteTopology (R ⧸ U)] (hle : U ≤ U') :
    ContinuousMonoidHom (R ⧸ U) (R ⧸ U') :=
  ⟨QuotientGroup.map U U' (MonoidHom.id R) hle, continuous_of_discreteTopology⟩

@[simp] theorem projMap_mk {U U' : Subgroup R} [U.Normal] [U'.Normal]
    [DiscreteTopology (R ⧸ U)] (hle : U ≤ U') (x : R) :
    projMap hle (QuotientGroup.mk x) = QuotientGroup.mk x := rfl

theorem projMap_surjective {U U' : Subgroup R} [U.Normal] [U'.Normal]
    [DiscreteTopology (R ⧸ U)] (hle : U ≤ U') :
    Function.Surjective (projMap hle) := by
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  exact ⟨QuotientGroup.mk x, rfl⟩

@[simp] theorem projMap_id {U : Subgroup R} [U.Normal] [DiscreteTopology (R ⧸ U)] (hle : U ≤ U) :
    projMap hle = ContinuousMonoidHom.id (R ⧸ U) := by
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

@[simp] theorem projMap_comp_apply {U U' U'' : Subgroup R} [U.Normal] [U'.Normal] [U''.Normal]
    [DiscreteTopology (R ⧸ U)] [DiscreteTopology (R ⧸ U')]
    (hle : U ≤ U') (hle' : U' ≤ U'') (y : R ⧸ U) :
    projMap hle' (projMap hle y) = projMap (hle.trans hle') y := by
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  rfl

variable {S : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
  [CompactSpace S] [TotallyDisconnectedSpace S]
  [IsTopologicalGroup R] [CompactSpace R] [TotallyDisconnectedSpace R]

/-- The König functor: `U ↦ {continuous surjections S ↠ R/U}`, with restriction along `U ≤ U'`
(post-composition with `projMap`).  Its sections are the compatible families of surjections. -/
noncomputable def konigFunctor : OpenNormalSubgroup (ProfiniteGrp.of R) ⥤ Type where
  obj U := {f : ContinuousMonoidHom S (R ⧸ U.toSubgroup) // Function.Surjective f}
  map {U U'} hh :=
    ↾(fun φ => ⟨(projMap (leOfHom hh)).comp φ.1, (projMap_surjective (leOfHom hh)).comp φ.2⟩)
  map_id U := by ext φ; simp
  map_comp {U U' U''} hh hh' := by ext φ; simp

end KonigAssembly

/-- **Surjection assembly from surjection counts** (paper Lemma 2.5, compactness input): if a
profinite group `S` continuously surjects onto at least as many finite groups (counted with
multiplicity) as a profinite group `R` **whose surjection sets are all finite** (`hRfin`), then
`S` continuously surjects onto `R`.  Finiteness of the *target* level sets is essential: without it
`Nat.card` collapses an infinite level set to `0` and the count hypothesis becomes vacuous (e.g.
`R = (ℤ/2)^ℕ`, `S = 1`).

This is *standard* profinite group theory (Ribes–Zalesskiĭ, *Profinite Groups*, Ch. 1–2).  Proof:
* For each `V : OpenNormalSubgroup R`, `contSurj_quotient_nonempty_finite` gives the level set
  `{S ↠ R/V}` nonempty **and finite** (from `hRfin` + the count hypothesis `h`).  These, with the
  restriction maps `projMap` for `V' ≤ V`, form `konigFunctor : OpenNormalSubgroup R ⥤ Type`, a
  cofiltered system of nonempty finite sets; `nonempty_sections_of_finite_cofiltered_system` (König)
  supplies a **compatible** family of surjections `σ V : S ↠ R/V`.
* `R` embeds into `Q := ∏_V R/V` via `e = (mk_V)_V` (injective since the open normal subgroups meet
  in `1`; a closed embedding as `R` is compact and `Q` is Hausdorff).  Cantor's intersection theorem
  in the compact `R` realizes each compatible family `(σ V s)_V` as `e r`, so `ψ := e⁻¹ ∘ Φ`
  (`Φ = (σ V)_V : S → Q`) is a well-defined continuous homomorphism with `mk_V ∘ ψ = σ V`.
* A second Cantor intersection, in the compact `S`, shows `ψ` surjective: for each `r`, the
  compatible closed sets `{s | σ V s = mk_V r}` meet, giving `s` with `ψ s = r`. -/
theorem exists_contSurj_of_card_le
    {S R : Type} [Group S] [TopologicalSpace S] [IsTopologicalGroup S]
      [CompactSpace S] [TotallyDisconnectedSpace S]
    [Group R] [TopologicalSpace R] [IsTopologicalGroup R]
      [CompactSpace R] [TotallyDisconnectedSpace R]
    (hRfin : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Finite (ContSurj R H))
    (h : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nat.card (ContSurj R H) ≤ Nat.card (ContSurj S H)) :
    Nonempty (ContSurj S R) := by
  classical
  haveI hne : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      Nonempty ((konigFunctor (S := S) (R := R)).obj U) :=
    fun U => (contSurj_quotient_nonempty_finite hRfin h U).1
  haveI hfin : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      Finite ((konigFunctor (S := S) (R := R)).obj U) :=
    fun U => (contSurj_quotient_nonempty_finite hRfin h U).2
  obtain ⟨sec, hsec⟩ :=
    nonempty_sections_of_finite_cofiltered_system (konigFunctor (S := S) (R := R))
  -- `σ U : S ↠ R/U`, with compatibility `projMap ∘ σ U = σ U'` for `U ≤ U'`.
  set σ : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R), ContinuousMonoidHom S (R ⧸ U.toSubgroup) :=
    fun U => (sec U).1 with hσ
  have hσsurj : ∀ U, Function.Surjective (σ U) := fun U => (sec U).2
  have hcompat : ∀ {U U' : OpenNormalSubgroup (ProfiniteGrp.of R)} (hle : U ≤ U') (s : S),
      projMap hle (σ U s) = σ U' s := by
    intro U U' hle s
    have := hsec hle.hom
    exact congrArg (fun (t : {f : ContinuousMonoidHom S (R ⧸ U'.toSubgroup) // Function.Surjective f})
      => t.1 s) this
  -- Embed `R` into the product of its finite quotients.
  let Q : Type := ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R), R ⧸ U.toSubgroup
  let e : R →* Q := MonoidHom.pi fun U => QuotientGroup.mk' U.toSubgroup
  let Φ : S →* Q := MonoidHom.pi fun U => (σ U).toMonoidHom
  have he_cont : Continuous e := continuous_pi fun U => continuous_quotient_mk'
  have hΦ_cont : Continuous Φ := continuous_pi fun U => (σ U).continuous_toFun
  haveI : Nonempty (OpenNormalSubgroup (ProfiniteGrp.of R)) := ⟨⟨⊤, Subgroup.normal_top⟩⟩
  haveI hdisc : ∀ U : OpenNormalSubgroup (ProfiniteGrp.of R),
      DiscreteTopology (R ⧸ U.toSubgroup) := fun U => inferInstance
  have he_inj : Function.Injective e := by
    intro x y hxy
    rw [← inv_mul_eq_one]
    by_contra hne1
    obtain ⟨U, hU⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
      (U := ({x⁻¹ * y}ᶜ : Set R)) isOpen_compl_singleton
      (Set.mem_compl_singleton_iff.mpr fun hc => hne1 hc.symm)
    have hmk : QuotientGroup.mk x = QuotientGroup.mk (s := U.toSubgroup) y := congrFun hxy U
    rw [QuotientGroup.eq] at hmk
    exact hU hmk rfl
  have he_emb : Topology.IsClosedEmbedding e := he_cont.isClosedEmbedding he_inj
  -- Every `Φ s` is realised by a point of `R` (Cantor intersection over the finite quotients).
  have hrealise : ∀ s : S, ∃ r : R, e r = Φ s := by
    intro s
    have : (⋂ U, {r : R | QuotientGroup.mk r = σ U s}).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U U'
        refine ⟨U ⊓ U', fun r hr => ?_, fun r hr => ?_⟩ <;>
          simp only [Set.mem_setOf_eq] at hr ⊢
        · rw [← hcompat inf_le_left s, ← hr, projMap_mk]
        · rw [← hcompat inf_le_right s, ← hr, projMap_mk]
      · exact fun U => QuotientGroup.mk_surjective (σ U s)
      · exact fun U => (isClosed_singleton.preimage continuous_quotient_mk').isCompact
      · exact fun U => isClosed_singleton.preimage continuous_quotient_mk'
    obtain ⟨r, hr⟩ := this
    refine ⟨r, funext fun U => ?_⟩
    exact Set.mem_iInter.mp hr U
  -- `ψ := e⁻¹ ∘ Φ` is a continuous homomorphism with `mk_U ∘ ψ = σ U`.
  let ψ : S → R := fun s => Function.invFun e (Φ s)
  have hψe : ∀ s, e (ψ s) = Φ s := fun s => by
    obtain ⟨r, hr⟩ := hrealise s
    show e (Function.invFun e (Φ s)) = Φ s
    rw [← hr, Function.leftInverse_invFun he_inj r]
  have hψ_hom : ∀ a b, ψ (a * b) = ψ a * ψ b := by
    intro a b
    apply he_inj
    rw [hψe, map_mul, map_mul, hψe, hψe]
  have hψ_cont : Continuous ψ := by
    rw [he_emb.isEmbedding.continuous_iff]
    exact hΦ_cont.congr fun s => (hψe s).symm
  -- `ψ` is surjective: for any `r`, Cantor intersection in `S` finds `s` with `ψ s = r`.
  have hψ_surj : Function.Surjective ψ := by
    intro r
    have : (⋂ U, {s : S | σ U s = QuotientGroup.mk r}).Nonempty := by
      apply IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed
      · intro U U'
        refine ⟨U ⊓ U', fun s hs => ?_, fun s hs => ?_⟩ <;>
          simp only [Set.mem_setOf_eq] at hs ⊢
        · rw [← hcompat inf_le_left s, hs, projMap_mk]
        · rw [← hcompat inf_le_right s, hs, projMap_mk]
      · exact fun U => (hσsurj U (QuotientGroup.mk r)).imp fun s hs => hs
      · exact fun U => (isClosed_singleton.preimage (σ U).continuous_toFun).isCompact
      · exact fun U => isClosed_singleton.preimage (σ U).continuous_toFun
    obtain ⟨s, hs⟩ := this
    refine ⟨s, he_inj ?_⟩
    rw [hψe]
    refine funext fun U => ?_
    have : σ U s = QuotientGroup.mk r := Set.mem_iInter.mp hs U
    simpa [e, Φ, MonoidHom.pi] using this
  exact ⟨⟨⟨MonoidHom.mk' ψ hψ_hom, hψ_cont⟩, hψ_surj⟩⟩

/-- **Lemma 2.5 (equinumerosity form).**  `P` is a topologically finitely generated profinite group,
`Q` is profinite, and for every finite group `H` the continuous-surjection sets are *equinumerous*
(`ContSurj P H ≃ ContSurj Q H`); then `P ≅ Q` as topological groups.  Equinumerosity, unlike equality
of `Nat.card`, forces the counts to be genuinely finite (via `P`'s finiteness) and so is not vacuous
on infinite level sets; it is the most general faithful reading of "the same *number* of surjections"
and does not need `Q` finitely generated as a separate hypothesis (it follows).  Proved in full
modulo the standard compactness input `exists_contSurj_of_card_le`. -/
theorem reconstruction_of_equinum
    {P Q : Type}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (hequiv : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nonempty (ContSurj P H ≃ ContSurj Q H)) :
    Nonempty (ContinuousMulEquiv P Q) := by
  -- `P` topologically f.g. ⇒ `ContSurj P H` finite; transport along the equiv ⇒ `ContSurj Q H` too.
  have hPfin : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
      Finite (ContSurj P H) := by
    intro H _ _ _ _
    haveI := finite_continuousMonoidHom hPfg H
    exact Finite.of_injective (fun s : ContSurj P H => s.val) (fun _ _ h => Subtype.ext h)
  have hQfin : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
      Finite (ContSurj Q H) := by
    intro H _ _ _ _
    haveI := hPfin H
    exact Finite.of_equiv _ (hequiv H).some
  -- Equinumerosity ⇒ equal counts.
  have hcard : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
      Nat.card (ContSurj P H) = Nat.card (ContSurj Q H) := by
    intro H _ _ _ _
    exact Nat.card_congr (hequiv H).some
  -- Surjections both ways (each target has finite level sets, so the counts are not vacuous).
  obtain ⟨⟨g, hg⟩⟩ : Nonempty (ContSurj Q P) :=
    exists_contSurj_of_card_le hPfin (fun H => (hcard H).le)
  obtain ⟨⟨f, hf⟩⟩ : Nonempty (ContSurj P Q) :=
    exists_contSurj_of_card_le hQfin (fun H => (hcard H).ge)
  -- The composite `P → Q → P` is a surjective endomorphism of the top. f.g. profinite `P`.
  have hcoe : (⇑(g.comp f) : P → P) = ⇑g ∘ ⇑f := rfl
  have hcomp : Function.Surjective (g.comp f : ContinuousMonoidHom P P) := by
    rw [hcoe]; exact hg.comp hf
  -- Hopfian ⇒ the composite is injective ⇒ `f` is injective; `f` is a continuous bijection.
  have hginj : Function.Injective (⇑(g.comp f) : P → P) := profinite_hopfian hPfg _ hcomp
  rw [hcoe] at hginj
  have hfinj : Function.Injective (f : P → Q) := hginj.of_comp
  exact ⟨continuousMulEquivOfBijective f ⟨hfinj, hf⟩⟩

/-- **Lemma 2.5 (one-sided profinite reconstruction).**  `P` and `Q` are topologically finitely
generated profinite groups with the same (finite) number of continuous surjections onto every finite
group; then `P ≅ Q` as topological groups.

Both `P` and `Q` are assumed topologically finitely generated (`hPfg`, `hQfg`).  The finite
generation of `Q` is essential and *cannot* be dropped while keeping the `Nat.card` hypothesis: for
`Q` not finitely generated some `ContSurj Q H` is infinite, so `Nat.card` reads it as `0` and the
count equality no longer means "equally many".  (Counterexample without `hQfg`: `P = Unit`,
`Q = (ℤ/2)^ℕ` satisfy `hcount` but are not isomorphic.)  With both groups finitely generated the
counts are genuinely finite, so `hcount` is real equinumerosity and this reduces to
`reconstruction_of_equinum`. -/
theorem reconstruction
    {P Q : Type}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
      [CompactSpace Q] [TotallyDisconnectedSpace Q]
    (hPfg : ∃ s : Finset P, (Subgroup.closure (s : Set P)).topologicalClosure = ⊤)
    (hQfg : ∃ s : Finset Q, (Subgroup.closure (s : Set Q)).topologicalClosure = ⊤)
    (hcount : ∀ (H : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H],
        Nat.card (ContSurj P H) = Nat.card (ContSurj Q H)) :
    Nonempty (ContinuousMulEquiv P Q) := by
  refine reconstruction_of_equinum hPfg (fun H _ _ _ _ => ?_)
  -- both surjection sets are finite (both groups top. f.g.), so equal `Nat.card` gives an equiv
  haveI := finite_continuousMonoidHom hPfg H
  haveI := finite_continuousMonoidHom hQfg H
  haveI : Finite (ContSurj P H) :=
    Finite.of_injective (fun s : ContSurj P H => s.val) (fun _ _ h => Subtype.ext h)
  haveI : Finite (ContSurj Q H) :=
    Finite.of_injective (fun s : ContSurj Q H => s.val) (fun _ _ h => Subtype.ext h)
  haveI := Fintype.ofFinite (ContSurj P H)
  haveI := Fintype.ofFinite (ContSurj Q H)
  refine Fintype.card_eq.mp ?_
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
  exact hcount H

/-- **Finite core of the reconstruction lemma.**  For *finite* groups, having the same number of
surjections onto every finite group forces an isomorphism.  This is the counting heart of
Lemma 2.5 (the profinite case reduces to it, level by level, along the finite quotient system):
`|Sur(P,P)| ≥ 1` gives a surjection `Q ↠ P`, symmetrically `P ↠ Q`, so `|P| = |Q|`, and a
surjection between equinumerous finite groups is an isomorphism. -/
theorem reconstruction_finite {P Q : Type} [Group P] [Group Q] [Finite P] [Finite Q]
    (hcount : ∀ (H : Type) [Group H] [Finite H],
        Nat.card {f : P →* H // Function.Surjective f}
          = Nat.card {f : Q →* H // Function.Surjective f}) :
    Nonempty (P ≃* Q) := by
  classical
  haveI : Finite (P →* P) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Q →* P) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (P →* Q) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (Q →* Q) := Finite.of_injective _ DFunLike.coe_injective
  -- A surjection `Q ↠ P` exists, since `|Sur(Q,P)| = |Sur(P,P)| ≥ 1` (identity).
  have hposP : 0 < Nat.card {f : P →* P // Function.Surjective f} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨MonoidHom.id P, Function.surjective_id⟩⟩, inferInstance⟩
  obtain ⟨g, hg⟩ : Nonempty {f : Q →* P // Function.Surjective f} :=
    (Nat.card_pos_iff.mp (by rw [← hcount P]; exact hposP)).1
  -- Symmetrically a surjection `P ↠ Q`.
  have hposQ : 0 < Nat.card {f : Q →* Q // Function.Surjective f} :=
    Nat.card_pos_iff.mpr ⟨⟨⟨MonoidHom.id Q, Function.surjective_id⟩⟩, inferInstance⟩
  obtain ⟨f, hf⟩ : Nonempty {f : P →* Q // Function.Surjective f} :=
    (Nat.card_pos_iff.mp (by rw [hcount Q]; exact hposQ)).1
  -- Mutual surjections between finite groups force equal cardinality.
  have hcard : Nat.card Q = Nat.card P :=
    le_antisymm (Nat.card_le_card_of_surjective f hf) (Nat.card_le_card_of_surjective g hg)
  -- A surjection between equinumerous finite groups is bijective.
  haveI : Fintype P := Fintype.ofFinite P
  haveI : Fintype Q := Fintype.ofFinite Q
  have hbij : Function.Bijective g :=
    (Fintype.bijective_iff_surjective_and_card g).mpr
      ⟨hg, by rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcard]⟩
  exact ⟨(MulEquiv.ofBijective g hbij).symm⟩

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 2.5 = ⟦lem-reconstruction⟧
-/
