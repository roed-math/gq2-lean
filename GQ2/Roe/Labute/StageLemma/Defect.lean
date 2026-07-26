/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.StageLemma.Congruence

/-!
# The shift formula, modification stability, and the span theorem

Piece 2/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  Contains the transported shift formulas `defectR0_mul` /
`defectR2_mul`, the level-`k` modification facts feeding `sPR0_mul_mem` / `sPR2_mul_mem`,
the Frattini generation transfer, and the span theorem `span_free_*` / `span_descent_*`.
-/

namespace GQ2.Roe.Labute

/-! ## Shift formula and modification stability (spike §2.1–2.2; concrete towers) -/

/-- **The transported shift formula, direction 1** (spike §2.2, machine-verified 24/24):
modifying a level-`k` triple by the projection of a `λ_{k-1}`-modification `w` shifts the
defect by exactly `d̄(w)` at the canonical lift.  No relator hypothesis: the identity is
pure `k ≥ 3` λ-calculus.  Fill: L4a. -/
theorem defectR0_mul (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    {w : Fin 3 → levelQuot (DR : Type) (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)) :
    defectR0 k (fun i => T i * levelProj (DR : Type) k (w i)) =
      defectR0 k T *
        dbarWordR0 (canonLift (DR : Type) k (T 0)) (canonLift (DR : Type) k (T 1))
          (canonLift (DR : Type) k (T 2)) w := by
  have hlift : ∀ i, levelProj (DR : Type) k (canonLift (DR : Type) k (T i) * w i) =
      T i * levelProj (DR : Type) k (w i) := by
    intro i; rw [map_mul, levelProj_canonLift]
  rw [← defectR0_eq_of_lift k _ (fun i => canonLift (DR : Type) k (T i) * w i) hlift, defectR0]
  exact d0Word_mul_lambdaImage k hk _ _ _ hw

/-- The transported shift formula, direction 2.  Fill: L4a. -/
theorem defectR2_mul (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    {w : Fin 3 → levelQuot (D0 : Type) (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)) :
    defectR2 k (fun i => T i * levelProj (D0 : Type) k (w i)) =
      defectR2 k T *
        dbarWordR2 (canonLift (D0 : Type) k (T 0)) (canonLift (D0 : Type) k (T 1))
          (canonLift (D0 : Type) k (T 2)) w := by
  have hlift : ∀ i, levelProj (D0 : Type) k (canonLift (D0 : Type) k (T i) * w i) =
      T i * levelProj (D0 : Type) k (w i) := by
    intro i; rw [map_mul, levelProj_canonLift]
  rw [← defectR2_eq_of_lift k _ (fun i => canonLift (D0 : Type) k (T i) * w i) hlift, defectR2]
  exact drWord_mul_lambdaImage k hk _ _ _ hw

/-! ### Level-`k` modification facts (L4a fill helpers)

At its *own* level a `λ_{k-1}`-modification is already central of exponent 2 in `Qₖ` — both
`v²` and `commP v g` land in `λₖ`, which is trivial in `Qₖ`.  So the relator clause of `S⁰ₖ`
is preserved for the cheapest possible reason, and the χ-clause survives because
`χ(λ_{k-1}) ⊆ 1 + 2^kℤ₂` — one digit sharper than `chiShadow_eq_one_of_mem` gives, which is
exactly the design reason the invariant `P` is stated at modulus `2^k`. -/

section LevelShift

variable {H : Type*} [Group H]

/-- The `r₀` word is blind to central involutive shifts of its slots. -/
private theorem d0Word_central_shift {z₀ z₁ z₂ : H}
    (h₀ : ∀ t : H, Commute z₀ t) (h₁ : ∀ t : H, Commute z₁ t) (h₂ : ∀ t : H, Commute z₂ t)
    (e₀ : z₀ ^ 2 = 1) (e₁ : z₁ ^ 2 = 1) (_e₂ : z₂ ^ 2 = 1) (a s y : H) :
    d0Word (a * z₀) (s * z₁) (y * z₂) = d0Word a s y := by
  have hz4 : z₁ ^ 4 = 1 := by rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, e₁, one_pow]
  rw [d0Word, d0Word, (h₀ a).symm.mul_pow, e₀, mul_one, (h₁ s).symm.mul_pow, hz4, mul_one,
    ← (h₁ s).eq, ← (h₂ y).eq, commP_central_left h₁, commP_central_right h₂]

/-- The `r₂` word is blind to central involutive shifts of its slots. -/
private theorem drWord_central_shift {z₀ z₁ z₂ : H}
    (h₀ : ∀ t : H, Commute z₀ t) (h₁ : ∀ t : H, Commute z₁ t) (h₂ : ∀ t : H, Commute z₂ t)
    (e₁ : z₁ ^ 2 = 1) (e₂ : z₂ ^ 2 = 1) (s x y : H) :
    drWord (s * z₀) (x * z₁) (y * z₂) = drWord s x y := by
  have hconj : ∀ (u : H) (z : H), (∀ t : H, Commute z t) →
      conjP (u * z) (s * z₀) = conjP u s * z := by
    intro u z hz
    rw [← (hz u).eq, ← (h₀ s).eq, conjP_central_left hz, conjP_central_right h₀, (hz _).eq]
  have hz3 : z₁ ^ 3 = z₁ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_add, e₁, one_mul, pow_one]
  rw [drWord, drWord, hconj x z₁ h₁, hconj y z₂ h₂, (h₁ x).symm.mul_pow, hz3,
    (h₂ y).symm.mul_pow, e₂, mul_one, ← (h₂ y).eq, commP_central_left h₂,
    ← (h₂ (conjP y s)).eq, commP_central_right h₂,
    ← (h₁ (conjP x s)).eq, ← (h₁ (x ^ 3)).eq,
    inv_mul_inv_central h₁ (by rw [← pow_two]; exact e₁)]

end LevelShift

section LevelFacts

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- At its own level a `λ_{k-1}`-modification squares to `1`. -/
private theorem lambdaImage_pred_sq (k : ℕ) (hk : 1 ≤ k) {v : levelQuot G k}
    (hv : v ∈ lambdaImage G (k - 1) k) : v ^ 2 = 1 := by
  obtain ⟨x, hx, rfl⟩ := hv
  rw [← map_pow]
  refine (QuotientGroup.eq_one_iff _).mpr ?_
  have h := sq_mem_twoCentralSeries_succ G hx
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- At its own level a `λ_{k-1}`-modification is central. -/
private theorem lambdaImage_pred_commute (k : ℕ) (hk : 1 ≤ k) {v : levelQuot G k}
    (hv : v ∈ lambdaImage G (k - 1) k) (g : levelQuot G k) : Commute v g := by
  have hgt : g ∈ lambdaImage G 1 k := by rw [lambdaImage_one_eq_top]; trivial
  have h := commP_mem_lambdaImage_add hv hgt
  rw [show k - 1 + 1 = k by omega, lambdaImage_self] at h
  have hc : commP v g = 1 := by simpa using h
  simp only [commP] at hc
  refine (commute_iff_eq v g).mpr ?_
  calc v * g = g * v * (v⁻¹ * g⁻¹ * v * g) := by group
    _ = g * v := by rw [hc, mul_one]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The χ-clause survives** (spike §2.1's design reason for the modulus `2^k`): a character
kills `λ_{k-1}` to precision `2^k`, one digit sharper than the generic layer bound, because
`λ_{k-1}(ℤ₂ˣ) ⊆ 1 + 2^kℤ₂` (`twoCentralSeries_units_le` at index `k - 1`). -/
theorem chiLevel_lambdaImage_pred (χ : ContinuousMonoidHom G ℤ_[2]ˣ) (k : ℕ)
    (hk : 3 ≤ k) {v : levelQuot G k} (hv : v ∈ lambdaImage G (k - 1) k) :
    chiLevel χ k v = 1 := by
  obtain ⟨g, hg, rfl⟩ := hv
  rw [chiLevel_levelMk]
  have h1 : χ g ∈ twoCentralSeries ℤ_[2]ˣ (k - 1) :=
    map_twoCentralSeries_le χ.toMonoidHom χ.continuous_toFun (k - 1) ⟨g, hg, rfl⟩
  have h2 := twoCentralSeries_units_le (k - 1) (by omega) h1
  rw [show k - 1 + 1 = k by omega] at h2
  exact MonoidHom.mem_ker.mp h2

end LevelFacts

/-- `D_R` is topologically generated by `{s, x, y}`, `Finset` form (private replica of the
Assembly-file packaging of `dr_topGen`; needed here for the tower instance pack). -/
theorem drTopGenFinset :
    ∃ s : Finset (DR : Type),
      (Subgroup.closure (s : Set (DR : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{drS, drX, drY}, ?_⟩
  have h : (({drS, drX, drY} : Finset (DR : Type)) : Set (DR : Type))
      = ({drS, drX, drY} : Set (DR : Type)) := by simp
  rw [h]
  exact dr_topGen

/-- `D₀` is topologically generated by `{A, S, Y}`, `Finset` form (private replica). -/
theorem d0TopGenFinset :
    ∃ s : Finset (D0 : Type),
      (Subgroup.closure (s : Set (D0 : Type))).topologicalClosure = ⊤ := by
  classical
  refine ⟨{d0A, d0S, d0Y}, ?_⟩
  have h : (({d0A, d0S, d0Y} : Finset (D0 : Type)) : Set (D0 : Type))
      = ({d0A, d0S, d0Y} : Set (D0 : Type)) := by simp
  rw [h]
  exact SectionThree.topGen_d0

/-! ### Frattini generation transfer (the non-generator argument at the level quotients) -/

section FrattiniTransfer

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]

open scoped commutatorElement in
/-- **`λ₂` is Frattini in every level quotient**: the image `λ₂λₘ/λₘ ≤ Qₘ` lies in the
Frattini-like subgroup `Φ(Qₘ) = Qₘ²[Qₘ, Qₘ]` (`SectionSeven.frattiniLike ⊤`).  Immediate
from the atomization principle `lambdaImage_induction` at `j = 1` (`λ₁ = ⊤`): `λ₂` is
verbally generated by squares and commutators of `λ₁`-elements, and both kinds of residue
are Frattini generators. -/
theorem lambdaImage_two_le_frattiniLike
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) (m : ℕ) :
    lambdaImage G 2 m ≤ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) := by
  intro q hq
  refine lambdaImage_induction G hfg hpro (j := 1) le_rfl
    (p := fun x => x ∈ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)))
    ?_ ?_ (one_mem _) (fun _ _ hx hy => mul_mem hx hy) (fun _ hx => inv_mem hx) hq
  · intro v _
    rw [map_pow, pow_two]
    exact sq_mem_frattiniLike (Subgroup.mem_top _)
  · intro v _ g
    rw [map_commutatorElement, commutatorElement_def]
    exact comm_mem_frattiniLike (Subgroup.mem_top _) (Subgroup.mem_top _)

/-- **Generation transfer** (Frattini non-generation): a generating family `T` of a level
quotient `Qₘ` stays generating after each member is multiplied by an element of the
`λ₂`-image.  Indeed `T i = (T i · u i) · (u i)⁻¹` puts `⟨T⟩ = ⊤` inside `H ⊔ λ₂`, where
`H = ⟨T · u⟩`; since `Qₘ` is a finite `2`-group and `λ₂ ≤ Φ(Qₘ)`, Frattini non-generation
(`frattiniLike_nongen`) upgrades `H ⊔ Φ(Qₘ) = ⊤` to `H = ⊤`. -/
theorem closure_range_mul_eq_top_of_mem_lambdaImage_two
    (hfg : ∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤)
    (hpro : IsProP 2 G) {m : ℕ} {ι : Type*} (T u : ι → levelQuot G m)
    (hgen : Subgroup.closure (Set.range T) = ⊤)
    (hu : ∀ i, u i ∈ lambdaImage G 2 m) :
    Subgroup.closure (Set.range fun i => T i * u i) = ⊤ := by
  haveI := finite_levelQuot G hfg hpro m
  have h2 : IsPGroup 2 ↥(⊤ : Subgroup (levelQuot G m)) :=
    (isPGroup_levelQuot G hfg hpro m).of_equiv Subgroup.topEquiv.symm
  have hΦ := lambdaImage_two_le_frattiniLike G hfg hpro m
  have hle : Subgroup.closure (Set.range T) ≤
      Subgroup.closure (Set.range fun i => T i * u i) ⊔
        SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨i, rfl⟩
    have h1 : T i * u i ∈ Subgroup.closure (Set.range fun i => T i * u i) :=
      Subgroup.subset_closure ⟨i, rfl⟩
    have h3 : (u i)⁻¹ ∈ SectionSeven.frattiniLike (⊤ : Subgroup (levelQuot G m)) :=
      inv_mem (hΦ (hu i))
    have h4 : T i = T i * u i * (u i)⁻¹ := by group
    rw [SetLike.mem_coe, h4]
    exact Subgroup.mul_mem_sup h1 h3
  rw [hgen] at hle
  exact frattiniLike_nongen h2 le_top (le_antisymm le_top hle)

end FrattiniTransfer

/-- **Modification stability of `S^P_ₖ`, direction 1** (spike §2.1 + §2.4): `λ_{k-1}`-moves
preserve all three clauses — relator kill (the shift lands in `λₖ`), generation
(Frattini: `λ_{k-1} ⊆ λ₂` for `k ≥ 3`), and the χ-clause (`χ(λ_{k-1}) ⊆ 1 + 2^k ℤ₂` — the
design reason `P` survives the calculus).  Fill: L4a. -/
theorem sPR0_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (DR : Type) k}
    (hT : T ∈ sPR0 k) {w : Fin 3 → levelQuot (DR : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR0 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hcen : ∀ i, ∀ g, Commute (w i) g :=
    fun i => lambdaImage_pred_commute k (by omega) (hw i)
  have hsq : ∀ i, w i ^ 2 = 1 := fun i => lambdaImage_pred_sq k (by omega) (hw i)
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · rw [d0Word_central_shift (hcen 0) (hcen 1) (hcen 2) (hsq 0) (hsq 1) (hsq 2)]
    exact hrel
  · exact closure_range_mul_eq_top_of_mem_lambdaImage_two (DR : Type) drTopGenFinset isProP_DR
      T w hgen fun i => lambdaImage_le_of_le (by omega) (hw i)
  · rw [map_mul, hchi i, chiLevel_lambdaImage_pred chiR k hk (hw i), mul_one]

/-- Modification stability, direction 2.  Fill: L4a. -/
theorem sPR2_mul_mem (k : ℕ) (hk : 3 ≤ k) {T : Fin 3 → levelQuot (D0 : Type) k}
    (hT : T ∈ sPR2 k) {w : Fin 3 → levelQuot (D0 : Type) k}
    (hw : ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) k) :
    (fun i => T i * w i) ∈ sPR2 k := by
  obtain ⟨⟨hrel, hgen⟩, hchi⟩ := hT
  have hcen : ∀ i, ∀ g, Commute (w i) g :=
    fun i => lambdaImage_pred_commute k (by omega) (hw i)
  have hsq : ∀ i, w i ^ 2 = 1 := fun i => lambdaImage_pred_sq k (by omega) (hw i)
  refine ⟨⟨?_, ?_⟩, fun i => ?_⟩
  · rw [drWord_central_shift (hcen 0) (hcen 1) (hcen 2) (hsq 1) (hsq 2)]
    exact hrel
  · exact closure_range_mul_eq_top_of_mem_lambdaImage_two (D0 : Type) d0TopGenFinset
      SectionThree.d0_isProP T w hgen fun i => lambdaImage_le_of_le (by omega) (hw i)
  · rw [map_mul, hchi i, chiLevel_lambdaImage_pred chiD0pres k hk (hw i), mul_one]

/-! ## The span theorem (spike §2.3; L4b) -/

/-- **The span theorem, free form, `r₀`-shape** (spike §2.3; Serre 252 §7 p. 151 with the
`2^{h-1}` erratum): for `k ≥ 3`, the graded layer `Zₖ(F₃)` is contained in the subgroup
generated by the `d̄`-image over `λ_{k-1}`-modifications at the standard generators
together with the two adapted tails `g₁^{2^{k-1}}, g₂^{2^{k-1}}` (the non-π'd generators
`(S, Y)`-slots = generators 1, 2).  Machine-verified `k ≤ 5` free / `k ≤ 6` towers
(20/20 rank rows).  Fill: L4b — via the structural reduction of spike §2.5(a); on a snag,
plan §7 O1/O2 apply (owner gate). -/
theorem span_free_r0 (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤
      Subgroup.closure
        ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
            dbarWordR0 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
          {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
        {levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1),
          levelMk (freeProTwo : Type) (k + 1) (freeGen 2) ^ 2 ^ (k - 1)}) :=
  span_free_r0_proof k hk

/-- The span theorem, free form, `r₂`-shape: tails at the `(s, x)`-slots = generators
0, 1 (the relator-adapted pair — spike §2.3's caught wrong-pair failure makes this
placement load-bearing).  Fill: L4b. -/
theorem span_free_r2 (k : ℕ) (hk : 3 ≤ k) :
    zLayer (freeProTwo : Type) k ≤
      Subgroup.closure
        ((fun w : Fin 3 → levelQuot (freeProTwo : Type) (k + 1) =>
            dbarWordR2 (levelMk (freeProTwo : Type) (k + 1) (freeGen 0))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 1))
              (levelMk (freeProTwo : Type) (k + 1) (freeGen 2)) w) ''
          {w | ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (k - 1) (k + 1)} ∪
        {levelMk (freeProTwo : Type) (k + 1) (freeGen 0) ^ 2 ^ (k - 1),
          levelMk (freeProTwo : Type) (k + 1) (freeGen 1) ^ 2 ^ (k - 1)}) :=
  span_free_r2_proof k hk

/-- **Span descent, direction 1** (spike §2.3: λ is verbal, so the statement descends
along `F₃ ↠ D_R` and holds *at any generating triple* of `Q_{k+1}(D_R)`; tails at the
`(S, Y)`-slots of the triple).  Fill: L4b (from `span_free_r0` + `map_twoCentralSeries_eq`
+ the congruence calculus).  -/
theorem span_descent_r0 (k : ℕ) (hk : 3 ≤ k)
    (T' : Fin 3 → levelQuot (DR : Type) (k + 1))
    (hgen : Subgroup.closure (Set.range T') = ⊤) :
    zLayer (DR : Type) k ≤
      Subgroup.closure
        ((fun w => dbarWordR0 (T' 0) (T' 1) (T' 2) w) ''
          {w : Fin 3 → levelQuot (DR : Type) (k + 1) |
            ∀ i, w i ∈ lambdaImage (DR : Type) (k - 1) (k + 1)} ∪
        {T' 1 ^ 2 ^ (k - 1), T' 2 ^ 2 ^ (k - 1)}) := by
  -- Instance pack on the finite discrete target `Q := Q_{k+1}(D_R)`.
  haveI := discreteTopology_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1)
  haveI : Finite (levelQuot (DR : Type) (k + 1)) :=
    finite_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1)
  have hproQ : IsProP 2 (levelQuot (DR : Type) (k + 1)) :=
    isProP_of_isPGroup (isPGroup_levelQuot (DR : Type) drTopGenFinset isProP_DR (k + 1))
  -- The classifying epi `φ : F₃ → Q` at the triple `T'`, and its λ-level factorization `ψ`.
  set φ := freeProTwoLift hproQ T' with hφ
  have hφs : Function.Surjective φ.toMonoidHom := by
    rw [← MonoidHom.range_eq_top, ← top_le_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨freeGen i, freeProTwoLift_freeGen hproQ T' i⟩
  have hkill : twoCentralSeries (freeProTwo : Type) (k + 1) ≤ φ.toMonoidHom.ker := by
    rw [← Subgroup.map_eq_bot_iff (f := φ.toMonoidHom), ← le_bot_iff,
      ← twoCentralSeries_levelQuot_self (DR : Type) drTopGenFinset isProP_DR (k + 1)]
    exact map_twoCentralSeries_le φ.toMonoidHom φ.continuous_toFun (k + 1)
  set ψ : levelQuot (freeProTwo : Type) (k + 1) →* levelQuot (DR : Type) (k + 1) :=
    QuotientGroup.lift _ φ.toMonoidHom hkill with hψ
  have hψmk : ψ.comp (levelMk (freeProTwo : Type) (k + 1)) = φ.toMonoidHom := by
    ext x
    exact QuotientGroup.lift_mk' _ hkill x
  -- λ-transport: `ψ` carries the free `lambdaImage` onto the tower `lambdaImage`, level-wise.
  have htrans : ∀ j : ℕ,
      (lambdaImage (freeProTwo : Type) j (k + 1)).map ψ = lambdaImage (DR : Type) j (k + 1) := by
    intro j
    rw [lambdaImage, Subgroup.map_map, hψmk,
      map_twoCentralSeries_eq φ.toMonoidHom φ.continuous_toFun hφs j,
      lambdaImage_eq_twoCentralSeries_levelQuot (DR : Type) drTopGenFinset isProP_DR j (k + 1)]
  -- Evaluation of `ψ` on the marked residues.
  have heval : ∀ j : Fin 3, ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = T' j := by
    intro j
    have h1 : ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = φ (freeGen j) :=
      QuotientGroup.lift_mk' _ hkill (freeGen j)
    rw [h1, hφ]
    exact freeProTwoLift_freeGen hproQ T' j
  -- Chase: lift a layer element, apply the free span theorem, push the generators forward.
  intro z hz
  rw [show zLayer (DR : Type) k = lambdaImage (DR : Type) k (k + 1) from rfl, ← htrans k] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hmap := Subgroup.mem_map_of_mem (K := Subgroup.closure _) ψ (span_free_r0 k hk hz₀)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rw [Set.image_union]
  refine Set.union_subset_union ?_ ?_
  · -- d̄-image terms: naturality of the shift word + λ-transport of the modifications.
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => ψ (w i), fun i => (htrans (k - 1)) ▸ Subgroup.mem_map_of_mem ψ (hw i), ?_⟩
    rw [map_dbarWordR0, heval 0, heval 1, heval 2]
  · -- Tail terms.
    rintro _ ⟨x, hx | hx, rfl⟩ <;> subst hx
    · exact Or.inl (by rw [map_pow, heval 1])
    · exact Or.inr (show _ = T' 2 ^ 2 ^ (k - 1) by rw [map_pow, heval 2])

/-- Span descent, direction 2 (tails at the `(s, x)`-slots).  Fill: L4b. -/
theorem span_descent_r2 (k : ℕ) (hk : 3 ≤ k)
    (T' : Fin 3 → levelQuot (D0 : Type) (k + 1))
    (hgen : Subgroup.closure (Set.range T') = ⊤) :
    zLayer (D0 : Type) k ≤
      Subgroup.closure
        ((fun w => dbarWordR2 (T' 0) (T' 1) (T' 2) w) ''
          {w : Fin 3 → levelQuot (D0 : Type) (k + 1) |
            ∀ i, w i ∈ lambdaImage (D0 : Type) (k - 1) (k + 1)} ∪
        {T' 0 ^ 2 ^ (k - 1), T' 1 ^ 2 ^ (k - 1)}) := by
  -- Mirror of `span_descent_r0` in the `D₀`-tower with the `r₂`-shape and `(s, x)`-tails.
  haveI := discreteTopology_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)
  haveI : Finite (levelQuot (D0 : Type) (k + 1)) :=
    finite_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)
  have hproQ : IsProP 2 (levelQuot (D0 : Type) (k + 1)) :=
    isProP_of_isPGroup (isPGroup_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1))
  set φ := freeProTwoLift hproQ T' with hφ
  have hφs : Function.Surjective φ.toMonoidHom := by
    rw [← MonoidHom.range_eq_top, ← top_le_iff, ← hgen, Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    exact ⟨freeGen i, freeProTwoLift_freeGen hproQ T' i⟩
  have hkill : twoCentralSeries (freeProTwo : Type) (k + 1) ≤ φ.toMonoidHom.ker := by
    rw [← Subgroup.map_eq_bot_iff (f := φ.toMonoidHom), ← le_bot_iff,
      ← twoCentralSeries_levelQuot_self (D0 : Type) d0TopGenFinset isProP_maxProPQuotient (k + 1)]
    exact map_twoCentralSeries_le φ.toMonoidHom φ.continuous_toFun (k + 1)
  set ψ : levelQuot (freeProTwo : Type) (k + 1) →* levelQuot (D0 : Type) (k + 1) :=
    QuotientGroup.lift _ φ.toMonoidHom hkill with hψ
  have hψmk : ψ.comp (levelMk (freeProTwo : Type) (k + 1)) = φ.toMonoidHom := by
    ext x
    exact QuotientGroup.lift_mk' _ hkill x
  have htrans : ∀ j : ℕ,
      (lambdaImage (freeProTwo : Type) j (k + 1)).map ψ = lambdaImage (D0 : Type) j (k + 1) := by
    intro j
    rw [lambdaImage, Subgroup.map_map, hψmk,
      map_twoCentralSeries_eq φ.toMonoidHom φ.continuous_toFun hφs j,
      lambdaImage_eq_twoCentralSeries_levelQuot (D0 : Type) d0TopGenFinset isProP_maxProPQuotient j (k + 1)]
  have heval : ∀ j : Fin 3, ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = T' j := by
    intro j
    have h1 : ψ (levelMk (freeProTwo : Type) (k + 1) (freeGen j)) = φ (freeGen j) :=
      QuotientGroup.lift_mk' _ hkill (freeGen j)
    rw [h1, hφ]
    exact freeProTwoLift_freeGen hproQ T' j
  intro z hz
  rw [show zLayer (D0 : Type) k = lambdaImage (D0 : Type) k (k + 1) from rfl, ← htrans k] at hz
  obtain ⟨z₀, hz₀, rfl⟩ := hz
  have hmap := Subgroup.mem_map_of_mem (K := Subgroup.closure _) ψ (span_free_r2 k hk hz₀)
  rw [MonoidHom.map_closure] at hmap
  refine Subgroup.closure_mono ?_ hmap
  rw [Set.image_union]
  refine Set.union_subset_union ?_ ?_
  · rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    refine ⟨fun i => ψ (w i), fun i => (htrans (k - 1)) ▸ Subgroup.mem_map_of_mem ψ (hw i), ?_⟩
    rw [map_dbarWordR2, heval 0, heval 1, heval 2]
  · rintro _ ⟨x, hx | hx, rfl⟩ <;> subst hx
    · exact Or.inl (by rw [map_pow, heval 0])
    · exact Or.inr (show _ = T' 1 ^ 2 ^ (k - 1) by rw [map_pow, heval 1])

end GQ2.Roe.Labute
