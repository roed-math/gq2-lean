import GQ2.SectionSix

/-!
# Shapiro ledger: Lemma 6.15 free (104) and involution (105)  (ticket P-15c)

Proves the two non-on-the-nose orbit cases of the paper's Lemma 6.15 (the square case (103) is
already proved on the nose in `GQ2/SectionSix.lean`).  The `ĝ`-shift changes the canonical
transversal representatives (`Quotient.out`) by right-`N` corrections; the two raw cochains
(graph pullback vs. corestriction) therefore differ by a **coboundary**, not literally.

The engine:

* `smul_zmodTwo` — every `DistribMulAction _ (ZMod 2)` is trivial (`Aut(𝔽₂) = 1`), so a
  `Z¹(N, 𝔽₂)` cocycle is a genuine homomorphism `N → 𝔽₂` (`z1_mul`/`z1_one`/`z1_inv`).
* `H2ofFun_eq_of_sub_mem_B2` — if `φ − ψ ∈ B²` then `H2ofFun φ = H2ofFun ψ` (junk-total, so this
  is all that is needed: it forces `φ ∈ Z² ↔ ψ ∈ Z²` and equal classes when both hold).
* `lWord_mul` — the transversal 1-cochain is a cocycle: `ℓ_h(γη) = ℓ_h(γ)·ℓ_{γ̄⁻¹h}(η)`.
* `shiftCorr` / `lWord_shift` — the `.out` discrepancy `ℓ_{kḡ}(η) = c(k)⁻¹·(ĝ⁻¹ℓ_k(η)ĝ)·c(η̄⁻¹k)`.

For the **free** case, these combine (with a finsum reindex over `G/N` and the `ℓ`-cocycle
identity) to give `φ − ψ = δ¹Λ` for the explicit 1-cochain
`Λ(γ) = Σ_h α(ℓ_h(γ))·β(c(γ̄⁻¹h))` (`lemma_6_15_free_aux`, **proved, std-3**).

Paper: Lemma 6.15, eqs. (104)/(105), proof pp. 31–32 (the `(106)`/`(108)` bar-corestriction
identities).  No axioms (`Ax = ∅`).

## Status and remaining work (P-15c)

* **Free orbits (104), `lemma_6_15_free_aux` — done, std-3.**
* **Involution orbits (105) — routed, not yet formalized.**  The graph pullback of
  `invOrbitDatum` (a `⟨ḡ⟩`-orbit sum with orientation corrections `m^g_c` via the `ε`-sign of
  paper eq. (67)) equals `cor_{K₀/F} N^{Ev}_{K/K₀}(α)` where `N^{Ev} = evensNormFun` (the
  two-point graph cocycle (98)) and `U₀ = ⟨N, ĝ⟩` is index-2 over `N`.  Route (paper (107)–
  (109)): expand `evensNormFun`'s `if q.1 ∈ U` case-split via `evensAux`/`bS` (`GQ2/EvensKahn.lean`)
  against the `(G/N)/⟨ḡ⟩`-transversal `.out`; the first `κ⁰`-summand matches the oriented
  factor-set term of (107) and the second matches the orientation-reversal correction; the
  residual `.out`-transversal discrepancy is again a `δ¹`-coboundary (same `H2ofFun_eq_of_sub_mem_B2`
  engine).  This is a materially larger computation than the free case (case-split × orientation
  × index-2 corestriction) and is the outstanding half of this ticket.

## Splice architecture note

The `_aux` lemma here **cannot** yet be spliced into `GQ2/SectionSix.lean`'s
`lemma_6_15_free` (`:= ShapiroLedger.lemma_6_15_free_aux …`) because that would import
`ShapiroLedger` into `SectionSix`, and `ShapiroLedger` imports `SectionSix` (for `graphPullback`,
`RegRep`, the orbit data) — an import cycle.  This blocks **every** P-15 own-file sub-ticket's
splice, not just this one.  The clean fix is to extract the factor-set / orbit-data layer
(`FactorSet`, `graphPullback`, `RegRep`, `*OrbitDatum`) from `SectionSix` into a lower shared
file both `SectionSix` and the P-15 own-files import; that is a coordinated refactor of the hot
co-owned `SectionSix` and is deliberately **not** done mid-parallel-work here.  Until then the
`SectionSix` statement keeps its `sorry` (allowlist unchanged) and `lemma_6_15_free_aux` stands
as the proved, consumable result.
-/

open scoped Pointwise

namespace GQ2

open ContCoh Corestriction SectionSix

namespace ShapiroLedger

/-! ## `ZMod 2` actions are trivial (`Aut(𝔽₂) = 1`) -/

section Triv

variable {H : Type*} [Group H] [DistribMulAction H (ZMod 2)]

/-- Case split on `𝔽₂`. -/
theorem zmodTwo_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide

/-- Every `DistribMulAction` on `𝔽₂` is trivial: `ℤ/2` has no nontrivial additive
automorphism. -/
theorem smul_zmodTwo (h : H) (m : ZMod 2) : h • m = m := by
  have hinj : Function.Injective (fun n : ZMod 2 => h • n) := fun a b hab => by
    have := congrArg (fun x => h⁻¹ • x) hab
    simpa only [← mul_smul, inv_mul_cancel, one_smul] using this
  have h0 : h • (0 : ZMod 2) = 0 := smul_zero h
  have h1 : h • (1 : ZMod 2) = 1 := by
    rcases zmodTwo_cases (h • (1 : ZMod 2)) with hc | hc
    · exact absurd (hinj (hc.trans h0.symm)) (by decide)
    · exact hc
  rcases zmodTwo_cases m with rfl | rfl
  · exact h0
  · exact h1

end Triv

/-! ## `Z¹(N, 𝔽₂)` cocycles are homomorphisms -/

section Z1Hom

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G)

/-- A `Z¹(N, 𝔽₂)`-cocycle is additive (the action is trivial). -/
theorem z1_mul (α : Z1 N (ZMod 2)) (x y : N) : α.1 (x * y) = α.1 x + α.1 y := by
  rw [(mem_Z1_iff.mp α.2).2 x y, smul_zmodTwo]

/-- `α(1) = 0`. -/
theorem z1_one (α : Z1 N (ZMod 2)) : α.1 1 = 0 := by
  have h := z1_mul N α 1 1
  rw [mul_one] at h
  exact h.trans (CharTwo.add_self_eq_zero (α.1 1))

/-- `α(x⁻¹) = α(x)` in `𝔽₂`. -/
theorem z1_inv (α : Z1 N (ZMod 2)) (x : N) : α.1 x⁻¹ = α.1 x := by
  have h := z1_mul N α x x⁻¹
  rw [mul_inv_cancel, z1_one] at h
  have h2 : α.1 x = - α.1 x⁻¹ := add_eq_zero_iff_eq_neg.mp h.symm
  rw [CharTwo.neg_eq] at h2
  exact h2.symm

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
  · have hψ : ψ ∈ Z2 G (ZMod 2) := by
      have he : ψ = φ - (φ - ψ) := by abel
      rw [he]; exact sub_mem hφ (B2_le_Z2 h)
    rw [H2ofFun_of_mem hφ, H2ofFun_of_mem hψ]
    have hmem : (⟨φ, hφ⟩ : Z2 G (ZMod 2)) - ⟨ψ, hψ⟩
        ∈ (B2 G (ZMod 2)).addSubgroupOf (Z2 G (ZMod 2)) := by
      rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub]
      exact h
    rw [← sub_eq_zero, ← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).mpr hmem
  · have hψ : ψ ∉ Z2 G (ZMod 2) := by
      intro hψ; apply hφ
      have he : φ = ψ + (φ - ψ) := by abel
      rw [he]; exact add_mem hψ (B2_le_Z2 h)
    rw [H2ofFun, H2ofFun, dif_neg hφ, dif_neg hψ]

end Coboundary

/-! ## The transversal 1-cochain is a cocycle; the `ĝ`-shift correction -/

section Transversal

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The `G`-action on `G ⧸ N` is left multiplication by the image: `g • z = ḡ · z`. -/
theorem quot_smul_eq_mk_mul (g : G) (z : G ⧸ N) : g • z = (g : G ⧸ N) * z := by
  refine QuotientGroup.induction_on z fun z₀ => ?_
  rw [← QuotientGroup.mk_mul]
  rfl

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
  have h2 : ((k * (ghat : G ⧸ N)).out : G ⧸ N) = k * (ghat : G ⧸ N) := QuotientGroup.out_eq' _
  exact (QuotientGroup.eq (s := N)).mp (h1.trans h2.symm)

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

@[simp] theorem coe_lTrans (u : G ⧸ N) (γ : G) : (lTrans N u γ : G) = lWord N u γ := rfl

/-- `γ ↦ γ⁻¹ • h : G → G ⧸ N` is continuous (into the discrete quotient). -/
theorem continuous_inv_smul (hNo : IsOpen (N : Set G)) (h : G ⧸ N) :
    Continuous fun γ : G => γ⁻¹ • h := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  have he : (fun γ : G => γ⁻¹ • h) = (fun γ : G => ((γ : G ⧸ N))⁻¹ * h) := by
    funext γ; rw [quot_smul_eq_mk_mul]; rfl
  rw [he]
  exact (continuous_mul_right h).comp ((continuous_inv).comp QuotientGroup.continuous_mk)

/-- `γ ↦ lTrans N h γ : G → ↥N` is continuous. -/
theorem continuous_lTrans (hNo : IsOpen (N : Set G)) (h : G ⧸ N) :
    Continuous fun γ : G => lTrans N h γ := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  have hcont : Continuous fun γ : G => lWord N h γ := by
    simp only [lWord]
    exact (continuous_mul_left h.out⁻¹).mul
      ((continuous_of_discreteTopology (f := fun u : G ⧸ N => u.out)).comp
        (continuous_inv_smul N hNo h))
  exact hcont.subtype_mk _

/-- `freeLambda` is continuous. -/
theorem freeLambda_continuous (hNo : IsOpen (N : Set G)) (α β : Z1 N (ZMod 2)) (ghat : G) :
    Continuous (freeLambda N α β ghat) := by
  haveI := QuotientGroup.discreteTopology (N := N) hNo
  haveI : Fintype (G ⧸ N) := Fintype.ofFinite _
  have hα : Continuous α.1 := (mem_Z1_iff.mp α.2).1
  have hEq : freeLambda N α β ghat
      = fun γ => ∑ h : G ⧸ N, α.1 (lTrans N h γ) * freeCorr N β ghat (γ⁻¹ • h) := by
    funext γ
    show (∑ᶠ h : G ⧸ N, α.1 (lTrans N h γ) * freeCorr N β ghat (γ⁻¹ • h)) = _
    rw [finsum_eq_sum_of_fintype]
  rw [hEq]
  refine continuous_finset_sum Finset.univ (fun h _ => ?_)
  exact (hα.comp (continuous_lTrans N hNo h)).mul
    ((continuous_of_discreteTopology (f := freeCorr N β ghat)).comp
      (continuous_inv_smul N hNo h))

/-- The conjugate `ĝ⁻¹·ℓ_k(η)·ĝ` lands in `N` (`N` normal). -/
theorem conjN_mem (ghat : G) (k : G ⧸ N) (η : G) :
    ghat⁻¹ * lWord N k η * ghat ∈ N := by
  simpa using ‹N.Normal›.conj_mem _ (lWord_mem N k η) ghat⁻¹

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

/-- The free graph pullback, unfolded to an explicit sum over `G ⧸ N`. -/
theorem phi_free_eq (α β : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat)) (QuotientGroup.mk' N)
        (fun δ ↦ (shapiroFun N α.1 δ, shapiroFun N β.1 δ)) (γ, η)
      = ∑ᶠ h : G ⧸ N, α.1 (lTrans N h γ)
          * β.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (h * QuotientGroup.mk' N ghat)) η) := by
  show (∑ᶠ h : G ⧸ N, α.1 (lTrans N h γ)
      * β.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (h * QuotientGroup.mk' N ghat)) η)) + 0 = _
  rw [add_zero]

/-- The corestriction side, unfolded to an explicit sum over `G ⧸ N` (definitional). -/
theorem psi_free_eq (α β : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    cor2Fun N (fun p ↦ α.1 p.1 * β.1 ⟨ghat⁻¹ * (p.2 : G) * ghat,
        (by simpa using ‹N.Normal›.conj_mem _ p.2.2 ghat⁻¹ : ghat⁻¹ * (p.2 : G) * ghat ∈ N)⟩)
        (γ, η)
      = ∑ᶠ u : G ⧸ N, α.1 (lTrans N u γ)
          * β.1 ⟨ghat⁻¹ * lWord N (γ⁻¹ • u) η * ghat, conjN_mem N ghat (γ⁻¹ • u) η⟩ := rfl

/-- Reindexing over `G ⧸ N` by left translation. -/
theorem sum_reindex_smul [Fintype (G ⧸ N)] (γ : G) (F : G ⧸ N → ZMod 2) :
    ∑ h : G ⧸ N, F (γ • h) = ∑ h : G ⧸ N, F h :=
  Fintype.sum_equiv (Equiv.mulLeft (γ : G ⧸ N)) (fun h => F (γ • h)) F
    (fun h => by rw [quot_smul_eq_mk_mul]; rfl)

/-- **Lemma 6.15, free orbits (104)**: proved via the coboundary `δ¹Λ` with the explicit
`Λ = freeLambda`.  (P-14 statement; P-15c proof, `Ax = ∅`.) -/
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
    refine QuotientGroup.induction_on h fun h₀ => ?_
    rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    rfl
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
    rw [show γ⁻¹ • (γ • h) = h from by rw [← mul_smul, inv_mul_cancel, one_smul],
      show (γ * η)⁻¹ • (γ • h) = η⁻¹ • h from by rw [← mul_smul]; congr 1; group]
  rw [hreindex]
  -- `Λη + Λ(γη) + Λγ = Λγ + (Λ(γη) + Λη)`
  abel

end Free

end ShapiroLedger

end GQ2
