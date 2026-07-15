/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.OrbitData
public import GQ2.Corestriction
public import GQ2.EvensKahn

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# The free-orbit Shapiro ledger and transversal changes

The cocycle, coboundary, free-orbit, and arbitrary-transversal comparison layers.

See `GQ2.Shapiro.Ledger` for the paper-facing overview, source citations, and deviations.
-/

open scoped Pointwise

namespace GQ2

open ContCoh Corestriction

namespace ShapiroLedger

/-! ## `ZMod 2` actions are trivial (`Aut(𝔽₂) = 1`) -/

section Triv

variable {H : Type*} [Group H] [DistribMulAction H (ZMod 2)]

/-- Case split on `𝔽₂`. -/
theorem zmodTwo_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- Every `DistribMulAction` on `𝔽₂` is trivial: `ℤ/2` has no nontrivial additive
automorphism. -/
theorem smul_zmodTwo (h : H) (m : ZMod 2) : h • m = m := by
  rcases zmodTwo_cases m with rfl | rfl
  · exact smul_zero h
  · rcases zmodTwo_cases (h • (1 : ZMod 2)) with hc | hc
    · exact absurd (MulAction.injective h (hc.trans (smul_zero h).symm)) (by decide)
    · exact hc

end Triv

/-! ## `Z¹(N, 𝔽₂)` cocycles are homomorphisms -/

section Z1Hom

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- A `Z¹(N, 𝔽₂)`-cocycle is additive (the action is trivial). -/
theorem z1_mul (α : Z1 N (ZMod 2)) (x y : N) : α.1 (x * y) = α.1 x + α.1 y := by
  rw [(mem_Z1_iff.mp α.2).2 x y, smul_zmodTwo]

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- `α(1) = 0`. -/
theorem z1_one (α : Z1 N (ZMod 2)) : α.1 1 = 0 :=
  left_eq_add.mp (show α.1 1 = α.1 1 + α.1 1 by simpa using z1_mul N α 1 1)

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- `α(x⁻¹) = α(x)` in `𝔽₂`. -/
theorem z1_inv (α : Z1 N (ZMod 2)) (x : N) : α.1 x⁻¹ = α.1 x := by
  have h := z1_mul N α x x⁻¹
  rw [mul_inv_cancel, z1_one] at h
  exact (CharTwo.add_eq_zero.mp h.symm).symm

end Z1Hom

/-! ## `H2ofFun` collapses coboundary differences -/

section Coboundary

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- If two raw 2-cochains differ by a **continuous coboundary**, their `H2ofFun` classes agree.
Because `H2ofFun` is junk-total (`0` off `Z²`), a coboundary difference forces
`φ ∈ Z² ↔ ψ ∈ Z²` and, when both hold, equal classes. -/
theorem H2ofFun_eq_of_sub_mem_B2 {φ ψ : G × G → ZMod 2}
    (h : φ - ψ ∈ B2 G (ZMod 2)) : H2ofFun G φ = H2ofFun G ψ := by
  by_cases hφ : φ ∈ Z2 G (ZMod 2)
  · have hψ : ψ ∈ Z2 G (ZMod 2) := by simpa using sub_mem hφ (B2_le_Z2 h)
    rw [H2ofFun_of_mem hφ, H2ofFun_of_mem hψ]
    have hmem : (⟨φ, hφ⟩ : Z2 G (ZMod 2)) - ⟨ψ, hψ⟩
        ∈ (B2 G (ZMod 2)).addSubgroupOf (Z2 G (ZMod 2)) :=
      AddSubgroup.mem_addSubgroupOf.mpr h
    rw [← sub_eq_zero, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hmem
  · have hψ : ψ ∉ Z2 G (ZMod 2) := fun hψ =>
      hφ (by simpa using add_mem (B2_le_Z2 h) hψ)
    rw [H2ofFun, H2ofFun, dif_neg hφ, dif_neg hψ]

end Coboundary

/-! ## The transversal 1-cochain is a cocycle; the `ĝ`-shift correction -/

section Transversal

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The `G`-action on `G ⧸ N` is left multiplication by the image: `g • z = ḡ · z`. -/
theorem quot_smul_eq_mk_mul (g : G) (z : G ⧸ N) : g • z = (g : G ⧸ N) * z :=
  QuotientGroup.induction_on z fun z₀ => (QuotientGroup.mk_mul N g z₀).symm

omit [N.Normal] in
/-- **Transversal 1-cocycle identity**: `ℓ_h(γη) = ℓ_h(γ) · ℓ_{γ⁻¹•h}(η)` (in `G`). -/
theorem lWord_mul (h : G ⧸ N) (γ η : G) :
    lWord N h (γ * η) = lWord N h γ * lWord N (γ⁻¹ • h) η := by
  simp only [lWord]
  rw [show ((γ * η)⁻¹ • h) = η⁻¹ • (γ⁻¹ • h) by rw [← mul_smul, mul_inv_rev]]
  group

/-- The `.out`-representative discrepancy of the `ĝ`-shift: `c(k) = (k̃·ĝ)⁻¹·(k·ḡ)~ ∈ N`. -/
noncomputable def shiftCorr (ghat : G) (k : G ⧸ N) : G :=
  (k.out * ghat)⁻¹ * (k * (ghat : G ⧸ N)).out

/-- `shiftCorr` lands in `N` (both factors are lifts of `k·ḡ`). -/
theorem shiftCorr_mem (ghat : G) (k : G ⧸ N) : shiftCorr N ghat k ∈ N := by
  have h1 : (((k.out * ghat : G)) : G ⧸ N) = k * (ghat : G ⧸ N) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq']
  exact (QuotientGroup.eq (s := N)).mp (h1.trans (QuotientGroup.out_eq' _).symm)

/-- The shift factorization of the transversal word:
`ℓ_{kḡ}(η) = c(k)⁻¹ · (ĝ⁻¹·ℓ_k(η)·ĝ) · c(η⁻¹•k)`. -/
theorem lWord_shift (ghat : G) (k : G ⧸ N) (η : G) :
    lWord N (k * (ghat : G ⧸ N)) η
      = (shiftCorr N ghat k)⁻¹ * (ghat⁻¹ * lWord N k η * ghat)
        * shiftCorr N ghat (η⁻¹ • k) := by
  have hsmul : η⁻¹ • (k * (ghat : G ⧸ N)) = (η⁻¹ • k) * (ghat : G ⧸ N) := by
    rw [quot_smul_eq_mk_mul, quot_smul_eq_mk_mul, mul_assoc]
  simp only [lWord, shiftCorr, hsmul]
  group

end Transversal

/-! ## Lemma 6.15, free orbits (104) -/

section Free

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G) [N.Normal] [Finite (G ⧸ N)]

/-- The shift-correction scalar `Δ(k) = β(c(k))`. -/
noncomputable def freeCorr (β : Z1 N (ZMod 2)) (ghat : G) (k : G ⧸ N) : ZMod 2 :=
  β.1 ⟨shiftCorr N ghat k, shiftCorr_mem N ghat k⟩

/-- The coboundary 1-cochain `Λ(γ) = Σ_h α(ℓ_h(γ))·Δ(γ⁻¹•h)`. -/
noncomputable def freeLambda (α β : Z1 N (ZMod 2)) (ghat : G) : G → ZMod 2 :=
  fun γ => ∑ᶠ h : G ⧸ N, α.1 (lTrans N h γ) * freeCorr N β ghat (γ⁻¹ • h)


omit [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `γ ↦ γ⁻¹ • h : G → G ⧸ N` is continuous (into the discrete quotient). -/
theorem continuous_inv_smul (_hNo : IsOpen (N : Set G)) (h : G ⧸ N) :
    Continuous fun γ : G => γ⁻¹ • h := by
  haveI := QuotientGroup.discreteTopology (N := N) _hNo
  have he : (fun γ : G => γ⁻¹ • h) = (fun γ : G => ((γ : G ⧸ N))⁻¹ * h) := by
    funext γ; rw [quot_smul_eq_mk_mul]; rfl
  rw [he]
  exact (continuous_mul_const h).comp (continuous_inv.comp QuotientGroup.continuous_mk)

omit [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- `γ ↦ lTrans N h γ : G → ↥N` is continuous. -/
theorem continuous_lTrans (hNo : IsOpen (N : Set G)) (h : G ⧸ N) :
    Continuous fun γ : G => lTrans N h γ := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  have hcont : Continuous fun γ : G => lWord N h γ := by
    simp only [lWord]
    exact (continuous_const_mul h.out⁻¹).mul
      ((continuous_of_discreteTopology (f := fun u : G ⧸ N => u.out)).comp
        (continuous_inv_smul N hNo h))
  exact hcont.subtype_mk _

omit [ContinuousSMul G (ZMod 2)] in
/-- `freeLambda` is continuous. -/
theorem freeLambda_continuous (hNo : IsOpen (N : Set G)) (α β : Z1 N (ZMod 2)) (ghat : G) :
    Continuous (freeLambda N α β ghat) := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hα : Continuous α.1 := (mem_Z1_iff.mp α.2).1
  have hEq : freeLambda N α β ghat
      = fun γ => ∑ h : G ⧸ N, α.1 (lTrans N h γ) * freeCorr N β ghat (γ⁻¹ • h) :=
    funext fun γ => finsum_eq_sum_of_fintype _
  rw [hEq]
  refine continuous_finsetSum Finset.univ (fun h _ => ?_)
  exact (hα.comp (continuous_lTrans N hNo h)).mul
    ((continuous_of_discreteTopology (f := freeCorr N β ghat)).comp
      (continuous_inv_smul N hNo h))

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The conjugate `ĝ⁻¹·ℓ_k(η)·ĝ` lands in `N` (`N` normal). -/
theorem conjN_mem (ghat : G) (k : G ⧸ N) (η : G) :
    ghat⁻¹ * lWord N k η * ghat ∈ N := by
  simpa using ‹N.Normal›.conj_mem _ (lWord_mem N k η) ghat⁻¹

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- **Per-term shift**: `β(ℓ_{kḡ}(η)) = Δ(k) + β(ĝ⁻¹ℓ_k(η)ĝ) + Δ(η⁻¹•k)`, absorbing the
`.out` discrepancy into the two corrections (`β` a hom). -/
theorem beta_lTrans_shift (β : Z1 N (ZMod 2)) (ghat : G) (k : G ⧸ N) (η : G) :
    β.1 (lTrans N (k * (ghat : G ⧸ N)) η)
      = freeCorr N β ghat k + β.1 ⟨ghat⁻¹ * lWord N k η * ghat, conjN_mem N ghat k η⟩
        + freeCorr N β ghat (η⁻¹ • k) := by
  have hsub : lTrans N (k * (ghat : G ⧸ N)) η
      = ⟨shiftCorr N ghat k, shiftCorr_mem N ghat k⟩⁻¹
        * ⟨ghat⁻¹ * lWord N k η * ghat, conjN_mem N ghat k η⟩
        * ⟨shiftCorr N ghat (η⁻¹ • k), shiftCorr_mem N ghat (η⁻¹ • k)⟩ := by
    apply Subtype.ext
    simp only [lTrans, Subgroup.coe_mul, InvMemClass.coe_inv]
    exact lWord_shift N ghat k η
  rw [hsub, z1_mul N β, z1_mul N β, z1_inv N β]
  rfl

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The free graph pullback, unfolded to an explicit sum over `G ⧸ N`. -/
theorem phi_free_eq (α β : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat)) (QuotientGroup.mk' N)
        (fun δ ↦ (shapiroFun N α.1 δ, shapiroFun N β.1 δ)) (γ, η)
      = ∑ᶠ h : G ⧸ N, α.1 (lTrans N h γ)
          * β.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (h * QuotientGroup.mk' N ghat)) η) :=
  add_zero _

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- The corestriction side, unfolded to an explicit sum over `G ⧸ N` (definitional). -/
theorem psi_free_eq (α β : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    cor2Fun N (fun p ↦ α.1 p.1 * β.1 ⟨ghat⁻¹ * (p.2 : G) * ghat,
        (by simpa using ‹N.Normal›.conj_mem _ p.2.2 ghat⁻¹ : ghat⁻¹ * (p.2 : G) * ghat ∈ N)⟩)
        (γ, η)
      = ∑ᶠ u : G ⧸ N, α.1 (lTrans N u γ)
          * β.1 ⟨ghat⁻¹ * lWord N (γ⁻¹ • u) η * ghat, conjN_mem N ghat (γ⁻¹ • u) η⟩ := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] [DistribMulAction G (ZMod 2)]
  [ContinuousSMul G (ZMod 2)] [Finite (G ⧸ N)] in
/-- Reindexing over `G ⧸ N` by left translation. -/
theorem sum_reindex_smul [Fintype (G ⧸ N)] (γ : G) (F : G ⧸ N → ZMod 2) :
    ∑ h : G ⧸ N, F (γ • h) = ∑ h : G ⧸ N, F h :=
  Fintype.sum_equiv (Equiv.mulLeft (γ : G ⧸ N)) (fun h => F (γ • h)) F
    (fun h => by rw [quot_smul_eq_mk_mul]; rfl)

/-- **Lemma 6.15, free orbits (104)**: proved via the coboundary `δ¹Λ` with the explicit
`Λ = freeLambda`.  (the §§6–7 statement; the Shapiro-ledger proof, `Ax = ∅`.) -/
theorem lemma_6_15_free_aux (hNo : IsOpen (N : Set G)) (α β : Z1 N (ZMod 2)) (ghat : G) :
    H2ofFun G (graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat))
        (QuotientGroup.mk' N) (fun γ ↦ (shapiroFun N α.1 γ, shapiroFun N β.1 γ)))
      = H2ofFun G (cor2Fun N (fun p ↦ α.1 p.1 *
          β.1 ⟨ghat⁻¹ * (p.2 : G) * ghat, by
            simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ p.2.2 ghat⁻¹⟩)) := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  apply H2ofFun_eq_of_sub_mem_B2
  simp only [B2, AddSubgroup.mem_map]
  refine ⟨freeLambda N α β ghat, mem_C1_iff.mpr (freeLambda_continuous N hNo α β ghat), ?_⟩
  funext p
  obtain ⟨γ, η⟩ := p
  -- `(γ̄)⁻¹ · h = γ⁻¹•h`
  have hact : ∀ h : G ⧸ N, (QuotientGroup.mk' N γ)⁻¹ * h = γ⁻¹ • h := fun h => by
    rw [quot_smul_eq_mk_mul, QuotientGroup.mk_inv]; rfl
  -- LHS: δ¹Λ, char-2 normalized
  have hL : dOne G (ZMod 2) (freeLambda N α β ghat) (γ, η)
      = freeLambda N α β ghat η + freeLambda N α β ghat (γ * η) + freeLambda N α β ghat γ := by
    show γ • freeLambda N α β ghat η - freeLambda N α β ghat (γ * η) + freeLambda N α β ghat γ = _
    rw [smul_zmodTwo, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hL, Pi.sub_apply, phi_free_eq, psi_free_eq N α β ghat γ η]
  -- index rewrite on the φ-sum: `(γ̄)⁻¹·(h·ḡ) = (γ⁻¹•h)·ḡ`
  have hidx : ∀ h : G ⧸ N,
      (QuotientGroup.mk' N γ)⁻¹ * (h * QuotientGroup.mk' N ghat)
        = (γ⁻¹ • h) * (ghat : G ⧸ N) := fun h => by
    rw [← mul_assoc, hact, QuotientGroup.mk'_apply]
  simp only [hidx]
  -- unfold Λ, convert to Fintype sums
  simp only [freeLambda, finsum_eq_sum_of_fintype]
  -- combine the two RHS sums, then per term
  rw [← Finset.sum_sub_distrib]
  have hpt : ∀ h : G ⧸ N,
      α.1 (lTrans N h γ) * β.1 (lTrans N ((γ⁻¹ • h) * (ghat : G ⧸ N)) η)
        - α.1 (lTrans N h γ)
            * β.1 ⟨ghat⁻¹ * lWord N (γ⁻¹ • h) η * ghat, conjN_mem N ghat (γ⁻¹ • h) η⟩
        = α.1 (lTrans N h γ)
            * (freeCorr N β ghat (γ⁻¹ • h) + freeCorr N β ghat (η⁻¹ • (γ⁻¹ • h))) := by
    intro h
    rw [beta_lTrans_shift N β ghat (γ⁻¹ • h) η]
    ring
  rw [Finset.sum_congr rfl (fun h _ => hpt h)]
  -- split, reindex
  simp only [mul_add]
  rw [Finset.sum_add_distrib]
  have hcompose : ∀ h : G ⧸ N, η⁻¹ • (γ⁻¹ • h) = (γ * η)⁻¹ • h := fun h => by
    rw [← mul_smul, mul_inv_rev]
  simp only [hcompose]
  -- `α(ℓ_h(γ)) = α(ℓ_h(γη)) + α(ℓ_{γ⁻¹h}(η))`, then reindex to `Λη`
  have hsplit : ∀ h : G ⧸ N,
      α.1 (lTrans N h γ) * freeCorr N β ghat ((γ * η)⁻¹ • h)
      = α.1 (lTrans N h (γ * η)) * freeCorr N β ghat ((γ * η)⁻¹ • h)
        + α.1 (lTrans N (γ⁻¹ • h) η) * freeCorr N β ghat ((γ * η)⁻¹ • h) := fun h => by
    have hBAD : α.1 (lTrans N h (γ * η))
        = α.1 (lTrans N h γ) + α.1 (lTrans N (γ⁻¹ • h) η) := by
      rw [show lTrans N h (γ * η) = lTrans N h γ * lTrans N (γ⁻¹ • h) η from
        Subtype.ext (lWord_mul N h γ η), z1_mul N α]
    rw [hBAD, add_mul, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [Finset.sum_congr rfl (fun h _ => hsplit h), Finset.sum_add_distrib]
  have hreindex :
      ∑ h : G ⧸ N, α.1 (lTrans N (γ⁻¹ • h) η) * freeCorr N β ghat ((γ * η)⁻¹ • h)
        = ∑ h : G ⧸ N, α.1 (lTrans N h η) * freeCorr N β ghat (η⁻¹ • h) := by
    rw [← sum_reindex_smul N γ
      (fun h => α.1 (lTrans N (γ⁻¹ • h) η) * freeCorr N β ghat ((γ * η)⁻¹ • h))]
    refine Finset.sum_congr rfl (fun h _ => ?_)
    rw [inv_smul_smul γ h,
      show (γ * η)⁻¹ • (γ • h) = η⁻¹ • h from by rw [← mul_smul]; congr 1; group]
  rw [hreindex]
  -- `Λη + Λ(γη) + Λγ = Λγ + (Λ(γη) + Λη)`
  abel

end Free

/-! ## Abstract cocycle twist (any group, char 2) -/

section Twist

variable {A : Type*} [Group A]

/-- Per-slot transversal correction: `M(a; c, d) = ν(c⁻¹, a·d) + ν(a, d) + ν(d, d⁻¹)`. -/
noncomputable def twistCorr (ν : A × A → ZMod 2) (a c d : A) : ZMod 2 :=
  ν (c⁻¹, a * d) + ν (a, d) + ν (d, d⁻¹)

/-- **Cocycle twist**: conjugating a composable pair `(x, y)` by corrections `c₀, c₁, c₂`
changes a right-normalized char-2 2-cocycle by three `twistCorr` reads. -/
theorem cocycle_twist (ν : A × A → ZMod 2)
    (hcoc : ∀ a b c : A, ν (b, c) + ν (a * b, c) + ν (a, b * c) + ν (a, b) = 0)
    (hr1 : ∀ z : A, ν (z, 1) = 0) (x y c₀ c₁ c₂ : A) :
    ν (c₀⁻¹ * x * c₁, c₁⁻¹ * y * c₂)
      = ν (x, y) + twistCorr ν x c₀ c₁ + twistCorr ν y c₁ c₂ + twistCorr ν (x * y) c₀ c₂ := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  have hI1 := hcoc (c₀⁻¹ * x * c₁) c₁⁻¹ (y * c₂)
  have hI2 := hcoc (c₀⁻¹ * x) c₁ c₁⁻¹
  have hI3 := hcoc c₀⁻¹ x c₁
  have hI4 := hcoc c₀⁻¹ x (y * c₂)
  have hI5 := hcoc x y c₂
  rw [show c₀⁻¹ * x * c₁ * c₁⁻¹ = c₀⁻¹ * x by group,
    show c₁⁻¹ * (y * c₂) = c₁⁻¹ * y * c₂ by group] at hI1
  rw [mul_inv_cancel, hr1 (c₀⁻¹ * x)] at hI2
  rw [show x * (y * c₂) = x * y * c₂ by group] at hI4
  simp only [twistCorr]
  linear_combination hI1 + hI2 + hI3 + hI4 + hI5
    - (ν (x, y) + ν (c₀⁻¹, x * c₁) + ν (x, c₁) + ν (c₁, c₁⁻¹) + ν (c₁⁻¹, y * c₂)
        + ν (y, c₂) + ν (c₂, c₂⁻¹) + ν (c₀⁻¹, x * y * c₂) + ν (x * y, c₂)
        + ν (c₀⁻¹ * x, y * c₂) + ν (c₀⁻¹ * x * c₁, c₁⁻¹) + ν (c₀⁻¹ * x, c₁)
        + ν (c₀⁻¹, x) + ν (x, y * c₂)) * h2

end Twist

/-! ## Corestriction along an arbitrary transversal -/

section TransversalChange

variable {G : Type*} [Group G]
variable (U : Subgroup G)

/-- `ℓ`-word along an arbitrary transversal lift `T : G ⧸ U → G`. -/
noncomputable def lWordT (T : G ⧸ U → G) (v : G ⧸ U) (γ : G) : G :=
  (T v)⁻¹ * γ * T (γ⁻¹ • v)

private theorem lWordT_mem (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) (γ : G) : lWordT U T v γ ∈ U := by
  have h1 : ((T (γ⁻¹ • v) : G) : G ⧸ U) = γ⁻¹ • v := hT _
  have h2 : ((γ⁻¹ * T v : G) : G ⧸ U) = γ⁻¹ • v := by
    conv_rhs => rw [← hT v]
    exact MulAction.Quotient.smul_mk U γ⁻¹ (T v)
  have h4 : (γ⁻¹ * T v)⁻¹ * T (γ⁻¹ • v) = lWordT U T v γ := by
    rw [lWordT]; group
  exact h4 ▸ (QuotientGroup.eq (s := U)).mp (h2.trans h1.symm)

/-- The transversal 1-cochain along `T`, valued in `↥U`. -/
noncomputable def lTransT (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) (γ : G) : U := ⟨lWordT U T v γ, lWordT_mem U T hT v γ⟩

/-- The `ℓ^T`-cocycle identity (transversal-independent telescoping). -/
theorem lWordT_mul (T : G ⧸ U → G) (v : G ⧸ U) (γ η : G) :
    lWordT U T v (γ * η) = lWordT U T v γ * lWordT U T (γ⁻¹ • v) η := by
  have h : (γ * η)⁻¹ • v = η⁻¹ • (γ⁻¹ • v) := by rw [← mul_smul, mul_inv_rev]
  simp only [lWordT, h]
  group

/-- The canonical transversal is the `T = Quotient.out` special case. -/
theorem lWordT_out (v : G ⧸ U) (γ : G) :
    lWordT U (fun w => (w.out : G)) v γ = lWord U v γ := rfl

/-- `ℓ`-cocycle identity for the canonical transversal (normality-free). -/
theorem lTrans_mul' (v : G ⧸ U) (γ η : G) :
    lTrans U v (γ * η) = lTrans U v γ * lTrans U (γ⁻¹ • v) η := by
  apply Subtype.ext
  rw [Subgroup.coe_mul]
  show lWord U v (γ * η) = lWord U v γ * lWord U (γ⁻¹ • v) η
  rw [← lWordT_out, ← lWordT_out, ← lWordT_out]
  exact lWordT_mul U _ v γ η

/-- The `.out`-vs-`T` transversal correction at `v`: `T v = v.out · tCorr v`. -/
noncomputable def tCorr (T : G ⧸ U → G) (v : G ⧸ U) : G := (v.out : G)⁻¹ * T v

private theorem tCorr_mem (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v) (v : G ⧸ U) :
    tCorr U T v ∈ U := by
  have h1 : ((v.out : G) : G ⧸ U) = v := QuotientGroup.out_eq' v
  exact (QuotientGroup.eq (s := U)).mp (h1.trans (hT v).symm)

/-- `tCorr` as an element of `↥U`. -/
noncomputable def tCorrEl (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) : U := ⟨tCorr U T v, tCorr_mem U T hT v⟩

/-- **Factorization**: the `T`-word sandwiches the canonical word between corrections. -/
theorem lTransT_factor (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) (γ : G) :
    lTransT U T hT v γ
      = (tCorrEl U T hT v)⁻¹ * lTrans U v γ * tCorrEl U T hT (γ⁻¹ • v) := by
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, InvMemClass.coe_inv]
  show lWordT U T v γ = (tCorr U T v)⁻¹ * lWord U v γ * tCorr U T (γ⁻¹ • v)
  simp only [lWordT, tCorr, lWord]
  group

/-- Corestriction of `ν : U × U → 𝔽₂` along the transversal `T`. -/
noncomputable def cor2FunT (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (ν : U × U → ZMod 2) : G × G → ZMod 2 :=
  fun p ↦ ∑ᶠ v : G ⧸ U, ν (lTransT U T hT v p.1, lTransT U T hT (p.1⁻¹ • v) p.2)

/-- The transversal-change 1-cochain `Λ`. -/
noncomputable def twistLambda (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (ν : U × U → ZMod 2) : G → ZMod 2 :=
  fun γ ↦ ∑ᶠ v : G ⧸ U,
    twistCorr ν (lTrans U v γ) (tCorrEl U T hT v) (tCorrEl U T hT (γ⁻¹ • v))

/-- Reindex a `G ⧸ U`-sum along `v ↦ γ⁻¹ • v` (normality-free). -/
theorem sum_reindex_smul' [Fintype (G ⧸ U)] (γ : G) (F : G ⧸ U → ZMod 2) :
    ∑ v : G ⧸ U, F (γ⁻¹ • v) = ∑ v : G ⧸ U, F v :=
  Fintype.sum_equiv (MulAction.toPerm (γ⁻¹ : G)) (fun v => F (γ⁻¹ • v)) F (fun _ => rfl)

section Topological

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- `γ ↦ γ⁻¹ • v : G → G ⧸ U` is locally constant when `U` is open (fibers are open). -/
theorem locallyConstant_inv_smul (hUo : IsOpen (U : Set G)) (v : G ⧸ U) :
    IsLocallyConstant fun γ : G => γ⁻¹ • v := by
  rw [IsLocallyConstant.iff_isOpen_fiber]
  intro w
  have hmk : ∀ γ : G, ((γ⁻¹ * (v.out : G) : G) : G ⧸ U) = γ⁻¹ • v := fun γ => by
    conv_rhs => rw [← QuotientGroup.out_eq' v]
    exact MulAction.Quotient.smul_mk U γ⁻¹ v.out
  have hset : (fun γ : G => γ⁻¹ • v) ⁻¹' {w}
      = (fun γ : G => (γ⁻¹ * (v.out : G))⁻¹ * (w.out : G)) ⁻¹' (U : Set G) := by
    ext γ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · intro h
      exact (QuotientGroup.eq (s := U)).mp (by rw [hmk, h, QuotientGroup.out_eq'])
    · intro h
      rw [← hmk γ, (QuotientGroup.eq (s := U)).mpr h, QuotientGroup.out_eq']
  rw [hset]
  exact ((continuous_mul_const _).comp (continuous_inv.comp
    ((continuous_mul_const _).comp continuous_inv))).isOpen_preimage _ hUo

/-- Any function of `γ⁻¹ • v` is continuous (`U` open). -/
theorem continuous_comp_inv_smul {X : Type*} [TopologicalSpace X]
    (hUo : IsOpen (U : Set G)) (v : G ⧸ U) (f : G ⧸ U → X) :
    Continuous fun γ : G => f (γ⁻¹ • v) :=
  ((locallyConstant_inv_smul U hUo v).comp f).continuous

/-- `γ ↦ ℓ_v(γ) : G → ↥U` is continuous (normality-free). -/
theorem continuous_lTrans' (hUo : IsOpen (U : Set G)) (v : G ⧸ U) :
    Continuous fun γ : G => lTrans U v γ := by
  have hw : Continuous fun γ : G => lWord U v γ := by
    simp only [lWord]
    exact (continuous_const_mul _).mul
      (continuous_comp_inv_smul U hUo v (fun w => (w.out : G)))
  exact hw.subtype_mk _

/-- `twistLambda` is continuous. -/
theorem twistLambda_continuous [Finite (G ⧸ U)] (hUo : IsOpen (U : Set G))
    (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (ν : U × U → ZMod 2) (hνc : Continuous ν) :
    Continuous (twistLambda U T hT ν) := by
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  have hEq : twistLambda U T hT ν = fun γ => ∑ v : G ⧸ U,
      twistCorr ν (lTrans U v γ) (tCorrEl U T hT v) (tCorrEl U T hT (γ⁻¹ • v)) :=
    funext fun γ => finsum_eq_sum_of_fintype _
  rw [hEq]
  refine continuous_finsetSum Finset.univ (fun v _ => ?_)
  have ha : Continuous fun γ : G => lTrans U v γ := continuous_lTrans' U hUo v
  have hd : Continuous fun γ : G => tCorrEl U T hT (γ⁻¹ • v) :=
    continuous_comp_inv_smul U hUo v _
  simp only [twistCorr]
  exact ((hνc.comp (continuous_const.prodMk (ha.mul hd))).add
    (hνc.comp (ha.prodMk hd))).add
    (hνc.comp (hd.prodMk hd.inv))

variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

omit [ContinuousSMul G (ZMod 2)] in
/-- **Transversal change for corestriction**: the `T`-corestriction of a right-normalized
2-cocycle `ν` on the open finite-index `U` differs from the canonical one by a coboundary. -/
theorem cor2FunT_sub_cor2Fun_mem_B2 [Finite (G ⧸ U)] (hUo : IsOpen (U : Set G))
    (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (ν : U × U → ZMod 2) (hνc : Continuous ν)
    (hcoc : ∀ a b c : U, ν (b, c) + ν (a * b, c) + ν (a, b * c) + ν (a, b) = 0)
    (hr1 : ∀ z : U, ν (z, 1) = 0) :
    cor2FunT U T hT ν - cor2Fun U ν ∈ B2 G (ZMod 2) := by
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  simp only [B2, AddSubgroup.mem_map]
  refine ⟨twistLambda U T hT ν,
    mem_C1_iff.mpr (twistLambda_continuous U hUo T hT ν hνc), ?_⟩
  funext p
  obtain ⟨γ, η⟩ := p
  have hL : dOne G (ZMod 2) (twistLambda U T hT ν) (γ, η)
      = twistLambda U T hT ν η + twistLambda U T hT ν (γ * η)
        + twistLambda U T hT ν γ := by
    show γ • twistLambda U T hT ν η - twistLambda U T hT ν (γ * η)
        + twistLambda U T hT ν γ = _
    rw [smul_zmodTwo, sub_eq_add_neg, CharTwo.neg_eq]
  rw [hL, Pi.sub_apply]
  show _ = cor2FunT U T hT ν (γ, η) - cor2Fun U ν (γ, η)
  simp only [cor2FunT, cor2Fun, twistLambda, finsum_eq_sum_of_fintype]
  rw [← Finset.sum_sub_distrib]
  -- per-position twist
  have hpt : ∀ v : G ⧸ U,
      ν (lTransT U T hT v γ, lTransT U T hT (γ⁻¹ • v) η)
          - ν (lTrans U v γ, lTrans U (γ⁻¹ • v) η)
        = twistCorr ν (lTrans U v γ) (tCorrEl U T hT v) (tCorrEl U T hT (γ⁻¹ • v))
          + twistCorr ν (lTrans U (γ⁻¹ • v) η) (tCorrEl U T hT (γ⁻¹ • v))
              (tCorrEl U T hT ((γ * η)⁻¹ • v))
          + twistCorr ν (lTrans U v (γ * η)) (tCorrEl U T hT v)
              (tCorrEl U T hT ((γ * η)⁻¹ • v)) := by
    intro v
    have hcompose : η⁻¹ • (γ⁻¹ • v) = (γ * η)⁻¹ • v := by
      rw [← mul_smul, mul_inv_rev]
    have hfac1 := lTransT_factor U T hT v γ
    have hfac2 := lTransT_factor U T hT (γ⁻¹ • v) η
    rw [hcompose] at hfac2
    rw [hfac1, hfac2,
      cocycle_twist ν hcoc hr1 (lTrans U v γ) (lTrans U (γ⁻¹ • v) η)
        (tCorrEl U T hT v) (tCorrEl U T hT (γ⁻¹ • v)) (tCorrEl U T hT ((γ * η)⁻¹ • v)),
      ← lTrans_mul' U v γ η]
    abel
  rw [Finset.sum_congr rfl (fun v _ => hpt v)]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  -- reindex the η-sum
  have hreindex :
      ∑ v : G ⧸ U, twistCorr ν (lTrans U (γ⁻¹ • v) η) (tCorrEl U T hT (γ⁻¹ • v))
          (tCorrEl U T hT ((γ * η)⁻¹ • v))
        = ∑ v : G ⧸ U, twistCorr ν (lTrans U v η) (tCorrEl U T hT v)
            (tCorrEl U T hT (η⁻¹ • v)) := by
    have hcong : ∀ v : G ⧸ U,
        twistCorr ν (lTrans U (γ⁻¹ • v) η) (tCorrEl U T hT (γ⁻¹ • v))
            (tCorrEl U T hT ((γ * η)⁻¹ • v))
          = (fun w => twistCorr ν (lTrans U w η) (tCorrEl U T hT w)
              (tCorrEl U T hT (η⁻¹ • w))) (γ⁻¹ • v) := fun v => by
      simp only [← mul_smul, mul_inv_rev]
    rw [Finset.sum_congr rfl (fun v _ => hcong v)]
    simpa using sum_reindex_smul' U γ (fun w => twistCorr ν (lTrans U w η) (tCorrEl U T hT w)
      (tCorrEl U T hT (η⁻¹ • w)))
  rw [hreindex]
  abel

end Topological

end TransversalChange

end ShapiroLedger

end GQ2
