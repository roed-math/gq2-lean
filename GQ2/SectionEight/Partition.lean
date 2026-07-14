import GQ2.SectionEight.ScalarCount

/-!
# §8: the eight-lift partition (Lemma 8.3) and the half-torsor count (Lemma 8.6)

**Lemma 8.3** (display (124)): the eight-lift partition of the master set of cover lifts.
**Lemma 8.6** (displays (127)/(128)): the radical-edge half-torsor count, per source.
Split out of `GQ2.SectionEight` (wave 38a).
-/

open scoped Pointwise

namespace GQ2

namespace SectionEight

open QuadraticFp2

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]


/-! ## Lemma 8.3: the eight-lift partition  (display (124))

The proof assembles two fibrations of the **master set** `R = {g : Γ →ₜ* Ỹ // (p∘g).range = J
∧ boundary-framed}`: by *image* `g ↦ g.range` (a `Nat.card_sigma` over subgroups `J' ≤ Ỹ` with
`p(J') = J`, each fibre `≃ BoundaryLifts(stratum J')` by corestriction) — this is the RHS; and
by *projection* `g ↦ p∘g` (each fibre the torsor `≃ Hom_cont(Γ,𝔽₂) = 8` of `fiberLiftEquiv`) —
this is `8 · u^β`.  Needs `Γ` topologically finitely generated (`hfg`), the
`finite_boundaryLifts` shape, to finitize the counted sets. -/

section Lemma83

variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
  (T : MarkedTarget H E Y) (C : CentralCover Y) (J : Subgroup Y)

/-- The master set of Lemma 8.3: cover lifts whose projection has image exactly `J` and is
boundary-framed for `T`.  The two fibrations of this set (by image `g ↦ g.range` and by
projection `g ↦ p∘g`) give the two sides of (124). -/
abbrev masterLifts : Type :=
  {g : ContinuousMonoidHom Γ C.cover //
    (C.pCont.comp g).toMonoidHom.range = J ∧ IsBoundaryLift b F T (C.pCont.comp g)}

variable {b F T C J}

omit [TopologicalSpace H] [DiscreteTopology H] [Finite H] [TopologicalSpace E]
  [DiscreteTopology E] [Finite E] [TopologicalSpace Y] [DiscreteTopology Y] in
/-- A subgroup of the cover projecting onto `J` also projects onto `H` — so its pullback
stratum is well-defined. -/
lemma stratum_surj (hJ : Function.Surjective (T.piY.comp J.subtype))
    {J' : Subgroup C.cover} (hJ' : J'.map C.p = J) :
    Function.Surjective ((C.pullTarget T).piY.comp J'.subtype) := by
  intro h
  obtain ⟨y, hy⟩ := hJ h
  have hyJ' : (y : Y) ∈ J'.map C.p := by rw [hJ']; exact y.2
  obtain ⟨x, hxJ', hxy⟩ := Subgroup.mem_map.mp hyJ'
  exact ⟨⟨x, hxJ'⟩, by
    show T.piY (C.p x) = h
    rw [hxy]; exact hy⟩

end Lemma83

theorem lemma_8_3
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) (C : CentralCover Y)
    (hscalar : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = 8)
    (J : Subgroup Y) (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    8 * liftableCount b F T C J hJ
      = ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
          exactImageCountOn b F (C.pullTarget T) J' := by
  -- Scaffolding for the O-finish (all landed above): `masterLifts` (the master set `R`),
  -- `stratum_surj`, the corestriction layer (`cmhCodRestrict`/`cmhInclude`/`cmhSubgroupEquiv`),
  -- `pCont`, and the torsor core (`fiberLiftEquiv` etc.).  Remaining: the two `Nat.card_sigma`
  -- fibrations of `R` (by projection → `8·u^β` via `fiberLiftEquiv`; by image → the RHS via
  -- corestriction).  `hfg` finitizes the counted sets (`finite_continuousMonoidHom`).
  classical
  haveI : Finite (ContinuousMonoidHom Γ C.cover) := finite_continuousMonoidHom hfg C.cover
  haveI : Finite (masterLifts b F T C J) := Subtype.finite
  -- membership: `p∘g` lands in `J` for any master lift.
  have hmemJ : ∀ (g : masterLifts b F T C J) (γ : Γ), C.p (g.1 γ) ∈ J := fun g γ => by
    have hmem : (C.pCont.comp g.1).toMonoidHom γ ∈ (C.pCont.comp g.1).toMonoidHom.range := ⟨γ, rfl⟩
    rw [g.2.1] at hmem; exact hmem
  haveI : Finite (BoundaryLifts b F (T.stratum J hJ)) :=
    finite_boundaryLifts b F (T.stratum J hJ) hfg
  set L := {f : BoundaryLifts b F (T.stratum J hJ) //
    ∃ g : ContinuousMonoidHom Γ C.cover, ∀ γ : Γ, C.p (g γ) = (f.1.1 γ : Y)} with hLdef
  haveI : Finite L := Subtype.finite
  haveI : Fintype L := Fintype.ofFinite L
  -- **Projection fibration**: `projB g = ` the corestriction of `p∘g` to `↥J`.
  set projB : masterLifts b F T C J → L := fun g =>
    ⟨⟨⟨cmhCodRestrict (C.pCont.comp g.1) J (hmemJ g), fun y => by
        have hy : (y : Y) ∈ (C.pCont.comp g.1).toMonoidHom.range := by rw [g.2.1]; exact y.2
        obtain ⟨γ, hγ⟩ := hy
        exact ⟨γ, Subtype.ext hγ⟩⟩, g.2.2⟩, g.1, fun γ => rfl⟩ with hprojBdef
  have hfibB : ∀ f : L, Nat.card {g : masterLifts b F T C J // projB g = f}
      = Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) := by
    intro f
    obtain ⟨g₀, hg₀⟩ := f.2
    refine Nat.card_congr (Equiv.trans ?_ (fiberLiftEquiv C g₀).symm)
    refine
      { toFun := fun g => ⟨g.1.1, fun γ => ?_⟩
        invFun := fun g' => ⟨⟨g'.1, ?_, ?_⟩, ?_⟩
        left_inv := fun g => ?_
        right_inv := fun g' => ?_ }
    · -- `projB g.1 = f` ⇒ `C.p (g.1.1 γ) = ↑(f.1.1.1 γ) = C.p (g₀ γ)`
      have h1 : C.p (g.1.1 γ) = (f.1.1.1 γ : Y) :=
        congrArg (fun w : L => (w.1.1.1 γ : Y)) g.2
      rw [h1, ← hg₀]
    · -- range = J for the included lift `g'`
      show (C.pCont.comp g'.1).toMonoidHom.range = J
      apply le_antisymm
      · rintro _ ⟨γ, rfl⟩
        show C.p (g'.1 γ) ∈ J
        rw [g'.2 γ, hg₀]; exact (f.1.1.1 γ).2
      · intro y hy
        obtain ⟨γ, hγ⟩ := f.1.1.2 ⟨y, hy⟩
        refine ⟨γ, ?_⟩
        show C.p (g'.1 γ) = y
        rw [g'.2 γ, hg₀, hγ]
    · -- boundary-framed for the included lift
      have heq : C.pCont.comp g'.1 = C.pCont.comp g₀ := by ext γ; exact g'.2 γ
      rw [heq]
      intro γ
      show (T.piY (C.p (g₀ γ)), T.thetaY (C.p (g₀ γ))) = F.frameMap (b γ)
      rw [hg₀ γ]
      exact f.1.2 γ
    · -- `projB (include g'.1) = f`, from `∀γ, C.p(g'.1 γ) = ↑(f.1.1.1 γ)`
      apply Subtype.ext; apply Subtype.ext; apply Subtype.ext
      ext γ
      show C.p (g'.1 γ) = (f.1.1.1 γ : Y)
      rw [g'.2 γ, hg₀]
    · rfl
    · rfl
  have hB : Nat.card (masterLifts b F T C J) = 8 * liftableCount b F T C J hJ := by
    calc Nat.card (masterLifts b F T C J)
        = Nat.card (Σ f : L, {g : masterLifts b F T C J // projB g = f}) :=
          (Nat.card_congr (Equiv.sigmaFiberEquiv projB)).symm
      _ = ∑ f : L, Nat.card {g : masterLifts b F T C J // projB g = f} := Nat.card_sigma
      _ = ∑ _f : L, 8 := Finset.sum_congr rfl (fun f _ => (hfibB f).trans hscalar)
      _ = 8 * Nat.card L := by
          rw [Finset.sum_const, Finset.card_univ, Nat.card_eq_fintype_card,
            smul_eq_mul, mul_comm]
  -- **Image fibration** (→ RHS).
  have hrange : ∀ (g : ContinuousMonoidHom Γ C.cover),
      (C.pCont.comp g).toMonoidHom.range = g.toMonoidHom.range.map C.p := fun g =>
    MonoidHom.range_comp _ _
  haveI : Finite (Subgroup C.cover) :=
    Finite.of_injective (fun H : Subgroup C.cover => (H : Set C.cover)) SetLike.coe_injective
  haveI : Fintype (Subgroup C.cover) := Fintype.ofFinite _
  set imageMap : masterLifts b F T C J → {J' : Subgroup C.cover // J'.map C.p = J} :=
    fun g => ⟨g.1.toMonoidHom.range, by rw [← hrange, g.2.1]⟩ with himapdef
  haveI : Fintype {J' : Subgroup C.cover // J'.map C.p = J} := Fintype.ofFinite _
  have hfibA : ∀ J' : {J' : Subgroup C.cover // J'.map C.p = J},
      Nat.card {g : masterLifts b F T C J // imageMap g = J'}
        = exactImageCountOn b F (C.pullTarget T) J'.1 := by
    intro J'
    have hsurj := stratum_surj hJ J'.2
    rw [exactImageCountOn, dif_pos hsurj, exactImageCount]
    apply Nat.card_congr
    refine
      { toFun := fun g => ?_
        invFun := fun gt => ?_
        left_inv := fun g => ?_
        right_inv := fun gt => ?_ }
    · -- forward: corestrict `g.1.1` to `↥J'.1`
      have hrgK : g.1.1.toMonoidHom.range = J'.1 := congrArg Subtype.val g.2
      have hmemK : ∀ γ, g.1.1 γ ∈ J'.1 := fun γ => hrgK ▸ ⟨γ, rfl⟩
      refine ⟨⟨cmhCodRestrict g.1.1 J'.1 hmemK, ?_⟩, ?_⟩
      · -- surjective onto `↥J'.1`
        rintro ⟨y, hy⟩
        rw [← hrgK] at hy
        obtain ⟨γ, hγ⟩ := hy
        exact ⟨γ, Subtype.ext hγ⟩
      · -- boundary-framed for the stratum
        intro γ
        show ((C.pullTarget T).piY (g.1.1 γ), (C.pullTarget T).thetaY (g.1.1 γ)) = F.frameMap (b γ)
        exact g.1.2.2 γ
    · -- backward: include `gt.1.1` back to `C.cover`
      have hsurj_gt : Function.Surjective ⇑gt.1.1.toMonoidHom := gt.1.2
      have hincl : (cmhInclude J'.1 gt.1.1).toMonoidHom.range = J'.1 := by
        show (J'.1.subtype.comp gt.1.1.toMonoidHom).range = J'.1
        rw [MonoidHom.range_eq_map, ← Subgroup.map_map, ← MonoidHom.range_eq_map,
          MonoidHom.range_eq_top.mpr hsurj_gt, ← MonoidHom.range_eq_map J'.1.subtype,
          Subgroup.range_subtype]
      refine ⟨⟨cmhInclude J'.1 gt.1.1, ?_, ?_⟩, ?_⟩
      · rw [hrange, hincl]; exact J'.2
      · intro γ
        show (T.piY (C.p (gt.1.1 γ : C.cover)), T.thetaY (C.p (gt.1.1 γ : C.cover)))
          = F.frameMap (b γ)
        exact gt.2 γ
      · exact Subtype.ext hincl
    · apply Subtype.ext; apply Subtype.ext; ext γ; rfl
    · apply Subtype.ext; apply Subtype.ext; ext γ; rfl
  -- assemble the image fibration and convert the sum shape.
  have hsumeq : ∑ᶠ J' ∈ {J' : Subgroup C.cover | J'.map C.p = J},
      exactImageCountOn b F (C.pullTarget T) J'
      = ∑ J' : {J' : Subgroup C.cover // J'.map C.p = J},
          exactImageCountOn b F (C.pullTarget T) J'.1 := by
    have hset : {J' : Subgroup C.cover | J'.map C.p = J}
        = ↑(Finset.univ.filter (fun J' : Subgroup C.cover => J'.map C.p = J)) := by
      ext J'; simp
    rw [hset, finsum_mem_coe_finset]
    exact Finset.sum_subtype _ (fun J' => by simp) _
  rw [hsumeq, ← hB, ← Nat.card_congr (Equiv.sigmaFiberEquiv imageMap), Nat.card_sigma]
  exact Finset.sum_congr rfl (fun J' _ => hfibA J')

/-! ## Lemma 8.6: radical edge and the half-torsor count

The §8 datum: a central double cover of `B` whose restriction to the elementary abelian
`M ◁ B` is a quadratic form (the square map into `⟨z⟩`) with polar radical `T` and vanishing
on `T`.  The `H¹`-valued edge class of (128) is carried **operationally**: the cover
descends to `B/T` iff `p⁻¹(T)` has a normal complement missing `z` (the paper's own descent
clause), and "edge ≠ 0" is the negation. -/

/- `polarMul`, `RadicalCoverData` (+`instNormalM`, `NoDescent`), `two_mul_card_fiber`,
`MLifts`, and `MLifts.Central` moved to `GQ2/RadicalEdgeData.lean` (P-16a def-layer
relocation, 2026-07-04; see `docs/p16-ticket-split.md`). -/

section HalfTorsor

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]

/-- **Lemma 8.6 (half-torsor count), candidate source**: with a nonzero radical edge, for
every lower *epimorphism* `ρ : Γ_A ↠ B/M`, exactly half of the unrestricted `M`-lifts of
`ρ` satisfy the central relation.  (The degree-one duality making the variation functional
(127) nonzero is §5 content for `Γ_A` — B7 enters through 5.15/5.16.)
[P-16 statement; proof = O-half.] -/
theorem lemma_8_6_gammaA (D : RadicalCoverData Bg)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GammaA (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  LedgerGammaA.half_torsor_gammaA D hedge ρ hρ

/-- **Lemma 8.6 (half-torsor count), local source**: as `lemma_8_6_gammaA`, for `G_ℚ₂`
(degree-one duality = B6).  **Amended (P-16b, 2026-07-05, documented)** with the standing
§8 side conditions, per the `lemma_8_2_local` (compactness) and `lemma_8_3` (`hfg`
topological finite generation, the B1-shaped input) precedents — they finitize the counted
`MLifts`.  Proof: P-16a's central-obstruction engine + the B6 twist of
`GQ2/RadicalEdgeLocal.lean` (`half_torsor_local`).  Ax: B6, B7. -/
theorem lemma_8_6_local (D : RadicalCoverData Bg)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfg : ∃ s : Finset AbsGalQ2,
      (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  RadicalEdgeLocal.half_torsor_local D hfg hedge ρ hρ

end HalfTorsor

end SectionEight

end GQ2
