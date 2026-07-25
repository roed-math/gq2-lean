/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.SectionThree
public import GQ2.Roe.DRPresentation

@[expose] public section

/-!
# The abelianization `B_R = D_R^{ab}`  (Roe note §3.1, eq. (3.4)–(3.6))

The marked pro-2 abelianization of the Roe group `D_R` (`GQ2/Roe/DRPresentation.lean`):

  `B_R = D_R^{ab} = ⟨s̄, x̄, ȳ | −4x̄ + 2ȳ = 0⟩_{ℤ₂} = C₂·t ⊕ ℤ₂·s̄ ⊕ ℤ₂·x̄`,
  `t = ȳ·x̄⁻²`   (⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧),

a 1:1 clone of `GQ2/SectionThree.lean`'s `BDecomposition` for `D₀` (the `B = D₀^{ab}` bundle of
paper eq. (11)).  The abelianized relation is `drWord_comm`: in `B_R` the relator collapses to
`(x̄⁴)⁻¹ȳ² = 1`, i.e. `2ȳ = 4x̄`.  In the coordinate system `(t, s̄, x̄)` the torsion generator
`t = ȳ·x̄⁻²` is 2-torsion and `ȳ ↦ t·x̄²` is forced (`ȳ`-row `(1, 0, 2)`).

## Contents

* `BRDecomposition` / `br_decomposition`: the continuous isomorphism
  `B_R ≅ Multiplicative (ZMod 2 × ℤ₂ × ℤ₂)` pinning `t ↦ (1,0,0)`, `s̄ ↦ (0,1,0)`,
  `x̄ ↦ (0,0,1)` (and `ȳ ↦ (1,0,2)`, forced).  Built from the coordinate homs
  `sHomR`/`xHomR`/`tHomR` (`abLiftG ∘ drLiftHom`), shown bijective — the `phiEquiv` route.
* **Topological generation** `dr_topGen`: `{s, x, y}` topologically generate `D_R`; the
  hom-extensionality corollaries `dr_hom_ext` (homs out of `D_R`) and `drab_hom_ext` (homs out
  of `B_R`).  Consumed by R9 (`isLabuteOrientation_ext`), R12 (`drH1_bijective`), R15.
* `demushkinQ_DR_eq_two`: the `q`-invariant feed for `DRDemushkin.demushkinQ_DR` — the torsion
  subgroup of `B_R` is `C₂` (`ℤ₂` is torsion-free), so `demushkinQ D_R = 2`.

The pro-2 `topAbelianization` instances are cloned `local` from `GQ2/SectionThree.lean:112–160`
(direct `local instance`, **not** wrapped in a `def` — that breaks the group structure).
-/

open CategoryTheory Multiplicative

namespace GQ2

open SectionThree

/-! ## Pro-2 instances on `B_R = topAbelianization D_R`

Cloned `local` from `GQ2/SectionThree.lean:112–160` (the block there is file-scoped, so it does
not leak to importers; we re-register for `topAbelianization D_R`). -/

/-- `G^{ab}` is commutative (local clone). -/
noncomputable local instance instCommGroupTopAbR {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

local instance instCompactSpaceTopAbR {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAbR {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAbR {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

/-- `B_R = topAbelianization D_R` is pro-2 (image of the pro-2 group `D_R` under `abMk`). -/
theorem isProP_two_topAb_DR : IsProP 2 (topAbelianization (DR : Type)) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective isProP_DR

/-! ## Topological generation of `D_R` by `{s, x, y}` -/

/-- The composite surjection `F₃ ↠ D_R` (through the full presentation and the pro-2 quotient),
sending `of 0, of 1, of 2` to `drS, drX, drY`. -/
noncomputable def qDR : FreeProfiniteGroup (Fin 3) →* (DR : Type) :=
  (maxProPMk 2 DRFull).toMonoidHom.comp (quotientMk (relatorSubgroup {drRelator})).toMonoidHom

lemma qDR_of (i : Fin 3) : qDR (FreeProfiniteGroup.of i) = ![drS, drX, drY] i := by
  fin_cases i <;> rfl

lemma continuous_qDR : Continuous qDR :=
  (maxProPMk 2 DRFull).continuous_toFun.comp
    (quotientMk (relatorSubgroup {drRelator})).continuous_toFun

lemma qDR_surjective : Function.Surjective qDR :=
  (quotientMk_surjective (proPKernel 2 DRFull)).comp
    (quotientMk_surjective (relatorSubgroup {drRelator}))

/-- The free generators of `F₃` topologically generate. -/
lemma freeProfinite_topGen :
    (Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin 3)))).topologicalClosure = ⊤ := by
  set g : FreeGroup (Fin 3) →* FreeProfiniteGroup (Fin 3) :=
    (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin 3)))).hom with hg
  have hrange : Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin 3))) = g.range := by
    have h1 : Set.range (FreeProfiniteGroup.of (X := Fin 3))
        = ⇑g '' Set.range (FreeGroup.of : Fin 3 → FreeGroup (Fin 3)) := by
      rw [← Set.range_comp]; rfl
    rw [h1, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
  rw [hrange]
  have hdense : DenseRange g := ProfiniteGrp.ProfiniteCompletion.denseRange _
  rw [SetLike.ext'_iff]
  simpa only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, MonoidHom.coe_range]
    using hdense.closure_range

/-- **Topological generation of `D_R`** ⟦lem:pro2word⟧: the marked generators `{s, x, y}`
topologically generate `D_R`.  This is the pushforward of `freeProfinite_topGen` through the
surjection `qDR : F₃ ↠ D_R`.  Consumed by R9 (`isLabuteOrientation_ext`), R12 (`drH1`
surjectivity), R15, and by `dr_hom_ext`/`drab_hom_ext` below. -/
theorem dr_topGen :
    (Subgroup.closure ({drS, drX, drY} : Set (DR : Type))).topologicalClosure = ⊤ := by
  have himg : qDR '' Set.range (FreeProfiniteGroup.of (X := Fin 3)) = {drS, drX, drY} := by
    rw [← Set.range_comp]
    ext z
    simp only [Set.mem_range, Function.comp, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      have := qDR_of i
      fin_cases i <;> simp_all
    · rintro (rfl | rfl | rfl)
      exacts [⟨0, by rw [qDR_of]; rfl⟩, ⟨1, by rw [qDR_of]; rfl⟩, ⟨2, by rw [qDR_of]; rfl⟩]
  have := qDR_surjective.denseRange.topologicalClosure_map_subgroup continuous_qDR
    freeProfinite_topGen
  rwa [MonoidHom.map_closure, himg] at this

/-- **Hom-extensionality for `D_R`**: two continuous homs into a pro-2 (Hausdorff) group agreeing
on `s, x, y` agree everywhere (`{s, x, y}` topologically generate, `dr_topGen`).  The DR-level
density argument consumed by R9's `isLabuteOrientation_ext` and R15's marked matching. -/
theorem dr_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (φ ψ : ContinuousMonoidHom (DR : Type) A)
    (hS : φ drS = ψ drS) (hX : φ drX = ψ drX) (hY : φ drY = ψ drY) : φ = ψ := by
  have hgens : Set.EqOn φ ψ ({drS, drX, drY} : Set (DR : Type)) := by
    rintro w (rfl | rfl | rfl)
    exacts [hS, hX, hY]
  have hsub : Set.EqOn φ ψ (Subgroup.closure ({drS, drX, drY} : Set (DR : Type))) := by
    intro w hw
    induction hw using Subgroup.closure_induction with
    | mem x hx => exact hgens hx
    | one => simp
    | mul a b _ _ ha hb => rw [map_mul, map_mul, ha, hb]
    | inv a _ ha => rw [map_inv, map_inv, ha]
  have hdense : Dense ((Subgroup.closure ({drS, drX, drY} : Set (DR : Type))) : Set (DR : Type)) := by
    rw [dense_iff_closure_eq, ← Subgroup.topologicalClosure_coe, dr_topGen, Subgroup.coe_top]
  refine ContinuousMonoidHom.ext (fun z => ?_)
  exact (hsub.closure φ.continuous_toFun ψ.continuous_toFun) (hdense z)

/-! ## The coordinate surjection `Φ_R : ℤ₂³ → B_R` and coordinate surjectivity -/

/-- The coordinate hom `Φ_R(s,x,y) = s̄^s · x̄^x · ȳ^y` on `B_R`. -/
noncomputable def PhiR : Multiplicative (ℤ_[2] × ℤ_[2] × ℤ_[2]) →* topAbelianization (DR : Type) where
  toFun p := zpowZtwo isProP_two_topAb_DR (abMk drS) p.toAdd.1
    * zpowZtwo isProP_two_topAb_DR (abMk drX) p.toAdd.2.1
    * zpowZtwo isProP_two_topAb_DR (abMk drY) p.toAdd.2.2
  map_one' := by
    show zpowZtwo _ (abMk drS) 0 * zpowZtwo _ (abMk drX) 0 * zpowZtwo _ (abMk drY) 0 = 1
    rw [zpowZtwo_zero, zpowZtwo_zero, zpowZtwo_zero, mul_one, mul_one]
  map_mul' p q := by
    show zpowZtwo _ (abMk drS) (p.toAdd.1 + q.toAdd.1)
        * zpowZtwo _ (abMk drX) (p.toAdd.2.1 + q.toAdd.2.1)
        * zpowZtwo _ (abMk drY) (p.toAdd.2.2 + q.toAdd.2.2)
      = (zpowZtwo _ (abMk drS) p.toAdd.1 * zpowZtwo _ (abMk drX) p.toAdd.2.1
          * zpowZtwo _ (abMk drY) p.toAdd.2.2)
        * (zpowZtwo _ (abMk drS) q.toAdd.1 * zpowZtwo _ (abMk drX) q.toAdd.2.1
          * zpowZtwo _ (abMk drY) q.toAdd.2.2)
    rw [zpowZtwo_add, zpowZtwo_add, zpowZtwo_add]
    ac_rfl

private lemma continuous_PhiR : Continuous PhiR := by
  show Continuous fun p : Multiplicative (ℤ_[2] × ℤ_[2] × ℤ_[2]) =>
    zpowZtwo isProP_two_topAb_DR (abMk drS) p.toAdd.1
      * zpowZtwo isProP_two_topAb_DR (abMk drX) p.toAdd.2.1
      * zpowZtwo isProP_two_topAb_DR (abMk drY) p.toAdd.2.2
  refine ((?_ : Continuous _).mul (?_ : Continuous _)).mul (?_ : Continuous _)
  · exact (continuous_zpowZtwo _ _).comp (continuous_fst.comp continuous_toAdd)
  · exact (continuous_zpowZtwo _ _).comp
      ((continuous_fst.comp continuous_snd).comp continuous_toAdd)
  · exact (continuous_zpowZtwo _ _).comp
      ((continuous_snd.comp continuous_snd).comp continuous_toAdd)

/-- **Coordinate surjectivity of `B_R`**: every element is `s̄^s x̄^x ȳ^y`. -/
lemma DRab_coord (z : topAbelianization (DR : Type)) :
    ∃ s x y : ℤ_[2], z = zpowZtwo isProP_two_topAb_DR (abMk drS) s
      * zpowZtwo isProP_two_topAb_DR (abMk drX) x
      * zpowZtwo isProP_two_topAb_DR (abMk drY) y := by
  have hgen : (Subgroup.closure
      (abMk '' {drS, drX, drY})).topologicalClosure = (⊤ : Subgroup (topAbelianization (DR : Type))) := by
    have := abMk_surjective.denseRange.topologicalClosure_map_subgroup
      (continuous_abMk (G := (DR : Type))) dr_topGen
    rwa [MonoidHom.map_closure] at this
  have hΦclosed : IsClosed (PhiR.range : Set (topAbelianization (DR : Type))) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range continuous_PhiR).isClosed
  have hsub : Subgroup.closure (abMk '' {drS, drX, drY}) ≤ PhiR.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨w, hw, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    rcases hw with rfl | rfl | rfl
    · exact ⟨ofAdd (1, 0, 0), by
        show zpowZtwo _ (abMk drS) 1 * zpowZtwo _ (abMk drX) 0 * zpowZtwo _ (abMk drY) 0 = abMk drS
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, mul_one, mul_one]⟩
    · exact ⟨ofAdd (0, 1, 0), by
        show zpowZtwo _ (abMk drS) 0 * zpowZtwo _ (abMk drX) 1 * zpowZtwo _ (abMk drY) 0 = abMk drX
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, one_mul, mul_one]⟩
    · exact ⟨ofAdd (0, 0, 1), by
        show zpowZtwo _ (abMk drS) 0 * zpowZtwo _ (abMk drX) 0 * zpowZtwo _ (abMk drY) 1 = abMk drY
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, one_mul, one_mul]⟩
  have hΦtop : PhiR.range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Subgroup.topologicalClosure_minimal _ hsub hΦclosed
  have hz : z ∈ PhiR.range := by rw [hΦtop]; exact Subgroup.mem_top z
  rw [MonoidHom.mem_range] at hz
  obtain ⟨p, hp⟩ := hz
  exact ⟨p.toAdd.1, p.toAdd.2.1, p.toAdd.2.2, hp.symm⟩

/-- **Hom-extensionality for `B_R`**: continuous homs `B_R → A` (`A` pro-2) agreeing on
`s̄, x̄, ȳ` agree everywhere (the `d0ab_hom_ext` analogue, via `DRab_coord`). -/
lemma drab_hom_ext {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [CompactSpace A] [T2Space A] [TotallyDisconnectedSpace A]
    (hA : IsProP 2 A) (φ ψ : ContinuousMonoidHom (topAbelianization (DR : Type)) A)
    (hS : φ (abMk drS) = ψ (abMk drS)) (hX : φ (abMk drX) = ψ (abMk drX))
    (hY : φ (abMk drY) = ψ (abMk drY)) (z : topAbelianization (DR : Type)) : φ z = ψ z := by
  obtain ⟨s, x, y, rfl⟩ := DRab_coord z
  rw [map_mul, map_mul, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_DR hA φ (abMk drS) s,
    map_zpowZtwo isProP_two_topAb_DR hA φ (abMk drX) x,
    map_zpowZtwo isProP_two_topAb_DR hA φ (abMk drY) y,
    map_zpowZtwo isProP_two_topAb_DR hA ψ (abMk drS) s,
    map_zpowZtwo isProP_two_topAb_DR hA ψ (abMk drX) x,
    map_zpowZtwo isProP_two_topAb_DR hA ψ (abMk drY) y, hS, hX, hY]

/-! ## The three coordinate homs `s̄`-coord, `x̄`-coord, `t`-coord

Each is `abLiftG (drLiftHom …)`; the relator check is `drWord_comm` (`drWord = (x⁴)⁻¹y²`), which
holds because the generator values `(s, x, y)` satisfy `−4x + 2y = 0`. -/

/-- The `s̄`-coordinate hom `B_R → ℤ₂`, with `s̄ ↦ 1`, `x̄ ↦ 0`, `ȳ ↦ 0`. -/
noncomputable def sHomR : ContinuousMonoidHom (topAbelianization (DR : Type)) (Multiplicative ℤ_[2]) :=
  abLiftG (drLiftHom PropOneOne.isProP_two_multPadicInt
    ![ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2])] (by
      rw [drWord_comm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring))

/-- The `x̄`-coordinate hom `B_R → ℤ₂`, with `s̄ ↦ 0`, `x̄ ↦ 1`, `ȳ ↦ 2`. -/
noncomputable def xHomR : ContinuousMonoidHom (topAbelianization (DR : Type)) (Multiplicative ℤ_[2]) :=
  abLiftG (drLiftHom PropOneOne.isProP_two_multPadicInt
    ![ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (2 : ℤ_[2])] (by
      rw [drWord_comm]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring))

/-- The `t`-coordinate hom `B_R → ZMod 2`, with `s̄ ↦ 0`, `x̄ ↦ 0`, `ȳ ↦ 1`. -/
noncomputable def tHomR : ContinuousMonoidHom (topAbelianization (DR : Type)) (Multiplicative (ZMod 2)) :=
  abLiftG (drLiftHom isProP_two_multZMod2
    ![ofAdd (0 : ZMod 2), ofAdd (0 : ZMod 2), ofAdd (1 : ZMod 2)] (by
      rw [drWord_comm]; decide))

@[simp] private lemma sHomR_S : sHomR (abMk drS) = ofAdd (1 : ℤ_[2]) := by simp [sHomR]
@[simp] private lemma sHomR_X : sHomR (abMk drX) = ofAdd (0 : ℤ_[2]) := by simp [sHomR]
@[simp] private lemma sHomR_Y : sHomR (abMk drY) = ofAdd (0 : ℤ_[2]) := by simp [sHomR]
@[simp] private lemma xHomR_S : xHomR (abMk drS) = ofAdd (0 : ℤ_[2]) := by simp [xHomR]
@[simp] private lemma xHomR_X : xHomR (abMk drX) = ofAdd (1 : ℤ_[2]) := by simp [xHomR]
@[simp] private lemma xHomR_Y : xHomR (abMk drY) = ofAdd (2 : ℤ_[2]) := by simp [xHomR]
@[simp] private lemma tHomR_S : tHomR (abMk drS) = ofAdd (0 : ZMod 2) := by simp [tHomR]
@[simp] private lemma tHomR_X : tHomR (abMk drX) = ofAdd (0 : ZMod 2) := by simp [tHomR]
@[simp] private lemma tHomR_Y : tHomR (abMk drY) = ofAdd (1 : ZMod 2) := by simp [tHomR]

/-! ## The combined coordinate hom `φ_R = (t, s̄, x̄)` -/

/-- The combined coordinate map `φ_R : B_R → ZMod 2 × ℤ₂ × ℤ₂`. -/
noncomputable def phiHomR :
    topAbelianization (DR : Type) →* Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) where
  toFun z := ofAdd ((tHomR z).toAdd, (sHomR z).toAdd, (xHomR z).toAdd)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul]
    rw [← ofAdd_add]
    rfl

lemma continuous_phiHomR : Continuous phiHomR := by
  show Continuous fun z => ofAdd ((tHomR z).toAdd, (sHomR z).toAdd, (xHomR z).toAdd)
  exact continuous_ofAdd.comp
    ((continuous_toAdd.comp tHomR.continuous_toFun).prodMk
      ((continuous_toAdd.comp sHomR.continuous_toFun).prodMk
        (continuous_toAdd.comp xHomR.continuous_toFun)))

@[simp] private lemma phiHomR_S :
    phiHomR (abMk drS) = ofAdd ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2])) := by
  simp only [phiHomR, MonoidHom.coe_mk, OneHom.coe_mk, sHomR_S, tHomR_S, xHomR_S, toAdd_ofAdd]

@[simp] private lemma phiHomR_X :
    phiHomR (abMk drX) = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])) := by
  simp only [phiHomR, MonoidHom.coe_mk, OneHom.coe_mk, sHomR_X, tHomR_X, xHomR_X, toAdd_ofAdd]

@[simp] private lemma phiHomR_Y :
    phiHomR (abMk drY) = ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), (2 : ℤ_[2])) := by
  simp only [phiHomR, MonoidHom.coe_mk, OneHom.coe_mk, sHomR_Y, tHomR_Y, xHomR_Y, toAdd_ofAdd]

/-! ### Coordinate computations on `s̄^s x̄^x ȳ^y` -/

/-- Abbreviation for the coordinate word. -/
private noncomputable def wordR (s x y : ℤ_[2]) : topAbelianization (DR : Type) :=
  zpowZtwo isProP_two_topAb_DR (abMk drS) s * zpowZtwo isProP_two_topAb_DR (abMk drX) x
    * zpowZtwo isProP_two_topAb_DR (abMk drY) y

private lemma sHomR_word (s x y : ℤ_[2]) : sHomR (wordR s x y) = ofAdd s := by
  rw [wordR, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt sHomR,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt sHomR,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt sHomR,
    sHomR_S, sHomR_X, sHomR_Y, zpowZtwo_ofAdd, zpowZtwo_ofAdd, zpowZtwo_ofAdd,
    ← ofAdd_add, ← ofAdd_add]
  congr 1; ring

private lemma xHomR_word (s x y : ℤ_[2]) : xHomR (wordR s x y) = ofAdd (x + 2 * y) := by
  rw [wordR, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt xHomR,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt xHomR,
    map_zpowZtwo isProP_two_topAb_DR PropOneOne.isProP_two_multPadicInt xHomR,
    xHomR_S, xHomR_X, xHomR_Y, zpowZtwo_ofAdd, zpowZtwo_ofAdd, zpowZtwo_ofAdd,
    ← ofAdd_add, ← ofAdd_add]
  congr 1; ring

private lemma tHomR_word (s x y : ℤ_[2]) :
    tHomR (wordR s x y) = zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) y := by
  rw [wordR, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_DR isProP_two_multZMod2 tHomR,
    map_zpowZtwo isProP_two_topAb_DR isProP_two_multZMod2 tHomR,
    map_zpowZtwo isProP_two_topAb_DR isProP_two_multZMod2 tHomR,
    tHomR_S, tHomR_X, tHomR_Y]
  rw [show ofAdd (0 : ZMod 2) = 1 from ofAdd_zero, zpowZtwo_one_base, zpowZtwo_one_base,
    one_mul, one_mul]

/-! ### `φ_R` is injective -/

/-- The abelianized relation `x̄⁴ = ȳ²` in `B_R` (from `dr_relation` + `drWord_comm`). -/
lemma abMk_relR : (abMk drX) ^ 4 = (abMk drY) ^ 2 := by
  have h : drWord (abMk drS) (abMk drX) (abMk drY) = 1 := by
    rw [← map_drWord, dr_relation, map_one]
  rw [drWord_comm, inv_mul_eq_one] at h
  exact h

/-- `t = ȳ·x̄⁻²` is 2-torsion (`t² = ȳ²x̄⁻⁴ = 1`). -/
lemma tbarR_sq : ((abMk drX) ^ (-2 : ℤ) * abMk drY) ^ 2 = 1 := by
  have hrel : abMk drY * abMk drY = (abMk drX) ^ (4 : ℤ) := by
    rw [← sq, abMk_relR.symm]; norm_cast
  rw [sq, mul_mul_mul_comm, hrel, ← zpow_add, ← zpow_add,
    show (-2 : ℤ) + -2 + 4 = 0 by norm_num, zpow_zero]

lemma phiHomR_injective : Function.Injective phiHomR := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨s, x, y, rfl⟩ := DRab_coord z
  change phiHomR (wordR s x y) = 1 at hz
  have hv : ((tHomR (wordR s x y)).toAdd, (sHomR (wordR s x y)).toAdd, (xHomR (wordR s x y)).toAdd)
      = (0, 0, 0) := by
    have h1 : (ofAdd ((tHomR (wordR s x y)).toAdd, (sHomR (wordR s x y)).toAdd,
        (xHomR (wordR s x y)).toAdd) : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) = ofAdd 0 := by
      rw [ofAdd_zero]; exact hz
    exact Multiplicative.ofAdd.injective h1
  rw [Prod.mk.injEq, Prod.mk.injEq] at hv
  obtain ⟨hvt, hvs, hvx⟩ := hv
  -- `sHomR`: `s = 0`
  have hsval : sHomR (wordR s x y) = 1 := by rw [← ofAdd_toAdd (sHomR (wordR s x y)), hvs, ofAdd_zero]
  rw [sHomR_word] at hsval
  have hs0 : s = 0 := Multiplicative.ofAdd.injective (hsval.trans ofAdd_zero.symm)
  -- `xHomR`: `x = -2y`
  have hxval : xHomR (wordR s x y) = 1 := by rw [← ofAdd_toAdd (xHomR (wordR s x y)), hvx, ofAdd_zero]
  rw [xHomR_word] at hxval
  have hx : x = ((-2 : ℤ) : ℤ_[2]) * y := by
    have := Multiplicative.ofAdd.injective (hxval.trans ofAdd_zero.symm)
    push_cast
    linear_combination this
  -- `tHomR`: `y` even
  have htval : tHomR (wordR s x y) = 1 := by rw [← ofAdd_toAdd (tHomR (wordR s x y)), hvt, ofAdd_zero]
  rw [tHomR_word, zpowZtwo_of_sq_eq_one isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (by decide) y]
    at htval
  have hval0 : (PadicInt.toZModPow 1 y).val = 0 := by
    have hlt : (PadicInt.toZModPow (p := 2) 1 y).val < 2 := by
      have := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 y); simpa using this
    rcases (by lia : (PadicInt.toZModPow 1 y).val = 0 ∨ (PadicInt.toZModPow 1 y).val = 1)
      with h0 | h1
    · exact h0
    · rw [h1, pow_one] at htval
      exact absurd (Multiplicative.ofAdd.injective htval) (by decide)
  -- conclude `wordR s x y = 1`
  show wordR s x y = 1
  rw [wordR, hs0, hx, zpowZtwo_zero, one_mul,
    ← zpowZtwo_zpowZtwo isProP_two_topAb_DR (abMk drX) ((-2 : ℤ) : ℤ_[2]) y,
    ← zpowZtwo_mul_base]
  rw [zpowZtwo_of_sq_eq_one isProP_two_topAb_DR _ (by rw [zpowZtwo_intCast]; exact tbarR_sq) y,
    hval0, pow_zero]

/-! ### `φ_R` is surjective -/

lemma phiHomR_surjective : Function.Surjective phiHomR := by
  intro w
  rw [← ofAdd_toAdd w]
  obtain ⟨c, s, x⟩ := w.toAdd
  refine ⟨wordR s (x - 2 * (c.val : ℤ_[2])) ((c.val : ℤ_[2])), ?_⟩
  show ofAdd ((tHomR (wordR _ _ _)).toAdd, (sHomR (wordR _ _ _)).toAdd, (xHomR (wordR _ _ _)).toAdd)
    = ofAdd (c, s, x)
  rw [tHomR_word, sHomR_word, xHomR_word, zpowZtwo_ofAdd_one_zmod2]
  congr 1
  refine Prod.ext (by simp) (Prod.ext (by simp) ?_)
  simp only [toAdd_ofAdd]
  ring

/-! ### Assembly: the coordinate isomorphism -/

/-- The coordinate isomorphism `φ_R : B_R ≃ₜ* ZMod 2 × ℤ₂ × ℤ₂`. -/
noncomputable def phiEquivR :
    ContinuousMulEquiv (topAbelianization (DR : Type)) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) :=
  continuousMulEquivOfBijective ⟨phiHomR, continuous_phiHomR⟩
    ⟨phiHomR_injective, phiHomR_surjective⟩

@[simp] private lemma phiEquivR_apply (z : topAbelianization (DR : Type)) : phiEquivR z = phiHomR z :=
  rfl

/-! ## The bundled decomposition ⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧ -/

/-- **Equation (3.4)–(3.6), bundled**: a continuous isomorphism
`B_R = D_R^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂` sending the torsion generator `t = ȳ·x̄⁻²`, `s̄`, `x̄` to the
standard basis.  In coordinates `(t, s̄, x̄)` the row `ȳ ↦ (1, 0, 2)` is forced
(`ȳ = t·x̄²`). -/
structure BRDecomposition where
  /-- The coordinate isomorphism `B_R ≅ C₂ ⊕ ℤ₂ ⊕ ℤ₂` of ⟦eq:BRsplit⟧. -/
  e : ContinuousMulEquiv (topAbelianization (DR : Type)) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
  /-- The torsion coordinate: `t = ȳ·x̄⁻² ↦ (1,0,0)` ⟦eq:tR⟧. -/
  map_t : e (abMk (drY * (drX ^ 2)⁻¹)) = Multiplicative.ofAdd (1, 0, 0)
  /-- `s̄ ↦ (0,1,0)`. -/
  map_s : e (abMk drS) = Multiplicative.ofAdd (0, 1, 0)
  /-- `x̄ ↦ (0,0,1)`. -/
  map_x : e (abMk drX) = Multiplicative.ofAdd (0, 0, 1)

/-- **The Roe abelianization decomposition exists** ⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧: the marked
pro-2 abelianization `B_R ≅ ℤ/2 × ℤ₂ × ℤ₂` via the coordinate homs `t, s̄, x̄`. -/
theorem br_decomposition : Nonempty BRDecomposition :=
  ⟨{ e := phiEquivR
     map_t := by
       rw [phiEquivR_apply]
       simp only [map_mul, map_inv, map_pow, phiHomR_Y, phiHomR_X]
       rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
       congr 1
       simp only [Prod.smul_mk, Prod.neg_mk, Prod.mk_add_mk, smul_zero]
       refine Prod.ext ?_ (Prod.ext ?_ ?_)
       · decide
       · push_cast; ring
       · push_cast; ring
     map_s := by rw [phiEquivR_apply, phiHomR_S]
     map_x := by rw [phiEquivR_apply, phiHomR_X] }⟩

/-- The `ȳ`-row of the decomposition, forced: `ȳ ↦ (1, 0, 2)` (`ȳ = t·x̄²`). -/
theorem br_decomposition_Y (B : BRDecomposition) :
    B.e (abMk drY) = Multiplicative.ofAdd (1, 0, 2) := by
  have h := B.map_t
  simp only [map_mul, map_inv, map_pow] at h
  rw [B.map_x, mul_inv_eq_iff_eq_mul] at h
  rw [h, ← ofAdd_nsmul, ← ofAdd_add]
  congr 1
  simp only [Prod.smul_mk, Prod.mk_add_mk, smul_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · decide
  · push_cast; ring
  · push_cast; ring

/-! ## Stress lemmas -/

/-- **Stress test (four explicit generators)**: `φ_R` sends `s̄, x̄, ȳ, t` to their coordinate
vectors `(0,1,0), (0,0,1), (1,0,2), (1,0,0)`. -/
theorem phiEquivR_generators :
    phiEquivR (abMk drS) = ofAdd (0, 1, 0) ∧ phiEquivR (abMk drX) = ofAdd (0, 0, 1) ∧
      phiEquivR (abMk drY) = ofAdd (1, 0, 2) ∧
      phiEquivR (abMk (drY * (drX ^ 2)⁻¹)) = ofAdd (1, 0, 0) := by
  refine ⟨by rw [phiEquivR_apply, phiHomR_S], by rw [phiEquivR_apply, phiHomR_X],
    by rw [phiEquivR_apply, phiHomR_Y], ?_⟩
  rw [phiEquivR_apply]
  simp only [map_mul, map_inv, map_pow, phiHomR_Y, phiHomR_X]
  rw [← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
  congr 1
  simp only [Prod.smul_mk, Prod.neg_mk, Prod.mk_add_mk, smul_zero]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · decide
  · push_cast; ring
  · push_cast; ring

/-- **Stress test (relation collapses to the `ZMod 2` component)** ⟦eq:BR⟧: the abelianized
relator `x̄⁴ = ȳ²` maps to the identity, i.e. `2ȳ = 4x̄` holds — and modulo `s̄, x̄` (the
torsion-free part) the only surviving content is the 2-torsion of `t`. -/
theorem phiEquivR_relation :
    phiEquivR ((abMk drX ^ 4)⁻¹ * (abMk drY) ^ 2) = 1 := by
  rw [abMk_relR, inv_mul_cancel, map_one]

/-! ## The `C₂`-torsion identification and the `demushkinQ` feed

The torsion subgroup of `B_R ≅ ZMod 2 × ℤ₂ × ℤ₂` is the `ZMod 2` factor (`ℤ₂` is torsion-free),
so `q = #torsion = 2`.  This feeds `DRDemushkin.demushkinQ_DR`. -/

/-- Torsion in `ℤ₂` is trivial: `n • b = 0` with `0 < n` forces `b = 0`. -/
private lemma padicInt_nsmul_eq_zero {n : ℕ} (hn : 0 < n) {b : ℤ_[2]} (h : n • b = 0) : b = 0 := by
  rw [nsmul_eq_mul] at h
  have hnz : (n : ℤ_[2]) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 hnz
  · exact h1

/-- A finite-order element of `Multiplicative (ZMod 2 × ℤ₂ × ℤ₂)` has zero `ℤ₂`-components. -/
private lemma finOrder_zmod2_prod {a : ZMod 2} {b c : ℤ_[2]}
    (h : IsOfFinOrder (Multiplicative.ofAdd (a, b, c))) : b = 0 ∧ c = 0 := by
  rw [isOfFinOrder_iff_pow_eq_one] at h
  obtain ⟨n, hn, hpow⟩ := h
  rw [← ofAdd_nsmul, ← ofAdd_zero] at hpow
  have hz := Multiplicative.ofAdd.injective hpow
  rw [Prod.smul_mk, Prod.smul_mk, Prod.ext_iff, Prod.ext_iff] at hz
  obtain ⟨_, hb, hc⟩ := hz
  exact ⟨padicInt_nsmul_eq_zero hn hb, padicInt_nsmul_eq_zero hn hc⟩

/-- **Torsion of the model** `ZMod 2 × ℤ₂ × ℤ₂`: the finite-order subtype is in bijection with
`ZMod 2` (the torsion is exactly the `ZMod 2` factor). -/
noncomputable def torsionEquivZMod2 :
    {z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) // IsOfFinOrder z} ≃ ZMod 2 where
  toFun z := z.1.toAdd.1
  invFun a := ⟨Multiplicative.ofAdd (a, 0, 0), by
    have hv : (2 : ℕ) • ((a : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2])) = 0 := by
      refine Prod.ext ?_ (Prod.ext ?_ ?_)
      · show (2 : ℕ) • a = 0
        rw [two_nsmul]; exact (by decide : ∀ b : ZMod 2, b + b = 0) a
      · show (2 : ℕ) • (0 : ℤ_[2]) = 0; exact smul_zero _
      · show (2 : ℕ) • (0 : ℤ_[2]) = 0; exact smul_zero _
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [← ofAdd_nsmul, hv]; exact ofAdd_zero⟩⟩
  left_inv := by
    rintro ⟨z, hz⟩
    apply Subtype.ext
    have hz' : IsOfFinOrder
        (Multiplicative.ofAdd (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2)) := by
      rw [show (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2) = z.toAdd from rfl, ofAdd_toAdd]; exact hz
    obtain ⟨hb, hc⟩ := finOrder_zmod2_prod hz'
    show Multiplicative.ofAdd ((z.toAdd.1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2])) = z
    conv_rhs => rw [← ofAdd_toAdd z]
    refine congrArg Multiplicative.ofAdd ?_
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · exact hb.symm
    · exact hc.symm
  right_inv a := by
    show (Multiplicative.ofAdd (a, (0 : ℤ_[2]), (0 : ℤ_[2]))).toAdd.1 = a
    rw [toAdd_ofAdd]

/-- **`q`-invariant feed for `demushkinQ_DR`**: `demushkinQ D_R = 2` ⟦eq:BR⟧/⟦eq:BRsplit⟧.  The
topological abelianization is `B_R ≅ C₂ ⊕ ℤ₂ ⊕ ℤ₂`, whose torsion subgroup is the `C₂` factor
(order 2).  Consumed by `GQ2/Roe/DRDemushkin.lean`'s `demushkinQ_DR`. -/
theorem demushkinQ_DR_eq_two : demushkinQ (DR : Type) = 2 := by
  rw [demushkinQ]
  have e : {x : topAbelianization (DR : Type) // IsOfFinOrder x}
      ≃ {z : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) // IsOfFinOrder z} :=
    Equiv.subtypeEquiv phiEquivR.toMulEquiv.toEquiv (fun x => by
      show IsOfFinOrder x ↔ IsOfFinOrder (phiEquivR.toMulEquiv x)
      rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
      refine ⟨fun ⟨n, hn, hp⟩ => ⟨n, hn, ?_⟩, fun ⟨n, hn, hp⟩ => ⟨n, hn, ?_⟩⟩
      · rw [← map_pow, hp, map_one]
      · exact phiEquivR.toMulEquiv.injective (by rw [map_pow, map_one]; exact hp))
  rw [Nat.card_congr e, Nat.card_congr torsionEquivZMod2, Nat.card_zmod]

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (3.4) = ⟦eq:BR⟧ (`abMk_relR`, `phiEquivR_relation`)
  * eq. (3.5) = ⟦eq:tR⟧ (`t = ȳ·x̄⁻²`; `map_t`, `tbarR_sq`)
  * eq. (3.6) = ⟦eq:BRsplit⟧ (`BRDecomposition`, `br_decomposition`, `demushkinQ_DR_eq_two`)
-/
