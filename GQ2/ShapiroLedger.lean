import GQ2.OrbitData
import GQ2.Corestriction
import GQ2.EvensKahn

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
* **Involution orbits (105) — foundations + Steps 1–2 done (std-3), reconciliation outstanding.**
  The graph pullback of `invOrbitDatum` (a `⟨ḡ⟩`-orbit sum with orientation corrections `m^g_c`
  via the `ε`-sign of paper eq. (67)) equals `cor_{K₀/F} N^{Ev}_{K/K₀}(α)` where
  `N^{Ev} = evensNormFun` (the two-point graph cocycle (98)) and `U₀ = ⟨N, ĝ⟩` is index-2 over `N`.
  **Landed here — foundations (§ "…foundations"):** `ghatQuot_sq` (`ḡ` is an involution of
  `G/N`), `map_U0_eq_zpowers` (`U₀ ↠ ⟨ḡ⟩`), `finite_quot_U0`, the key **index correspondence
  `invIndexEquiv : G/U₀ ≃ (G/N)/⟨ḡ⟩`** bijecting the orbit index sets, and **both sides in
  explicit form** — `phi_inv_eq` (LHS as the two paper-(107) sums, oriented term + orientation
  correction) and `psi_inv_eq` (RHS as an `evensNormFun` sum over `G/U₀`).
  **Landed here — Step 1 (reindex):** `psi_inv_reindex` moves the RHS sum from `G/U₀` onto the
  orbit set `O = (G/N)/⟨ḡ⟩` via `invIndexEquiv` (`finsum_comp_equiv`), lining it up with the
  `phi_inv_eq` sums.  **Landed here — Step 2 (Evens-norm expansion):** the **free-action fact**
  `orbit_free` (`ĝ ∉ N ⟹ z·ḡ ≠ z`, so every `⟨ḡ⟩`-orbit is a free 2-set `{z, z·ḡ}` — no
  fixed-point/diagonal term), and `evensAux_alphaOn_{mem,notMem}` / `bS_alphaOn_{mem,notMem}`
  reducing the `N^{Ev}` building blocks to explicit `α`-reads (`ĝ ∉ N`; `x·ĝ ∈ N ⟺ x ∉ N`), plus
  `alphaOn`(`_hom`/`_continuous`) and `subgroupOf_isOpen`.
  **Landed here — Step 3, γ-word machinery (all std-3):** `lWordU0_mem_N_iff` (the **membership
  correspondence** `ℓ^{U₀}_v(γ) ∈ N ⟺ γ̄`-aligned reps, using `orbit_free`); the `U₀→N` **word
  factorization** `nLift`/`uCorr`/`uCorr_mem`/`lWordU0_factor` (`ℓ^{U₀}_v(γ) = uCorr(v)⁻¹ ·
  (nLift-word) · uCorr(γ⁻¹•v)`, isolating the `.out^{U₀}` vs `.out^{G/N}` discrepancy into the
  `N`-corrections `uCorr`); `orbit_equiv` + `mem_zpowers_sq_one` + `zb_flipped` (the flipped
  orientation `zb = (γ̄⁻¹za)·ḡ`); and **both** α-decompositions of the `evensAux` γ-reading —
  `alpha_lWordU0_aligned` (`x ∈ N`: `α(x) = α(uCorr v) + α(ℓ^N_{mk v.out}(γ)) + α(uCorr(γ⁻¹•v))`)
  and `alpha_lWordU0_flipped` (`x ∉ N`: `α(x·ĝ) = α(uCorr v) + α(ℓ^N_{mk v.out}(γ)) + α(W)`,
  `W = ĝ·shiftCorr(γ⁻¹•za)·uCorr(γ⁻¹•v)·ĝ`), both reducing to the **same base word**
  `ℓ^N_{mk v.out}(γ)` plus `N`-corrections.  The top-level reduction is also verified: applying
  `H2ofFun_eq_of_sub_mem_B2` reduces the goal to `graphPullback(…) − cor2Fun(…) ∈ B²`.

  **REMAINING — the coboundary assembly (the uncracked core, banked 2026-07-04).**  Need the
  explicit `Λ : G → 𝔽₂` with `δ¹Λ = phi − psi` (then `H2ofFun_eq_of_sub_mem_B2`).  Two pieces:
  1. **`bS(y)` / η-word decomposition.**  The γ-word (`evensAux(x)`) is done above; `evensAux(y)`
     reuses those lemmas with `(v,γ) ↦ (γ⁻¹•v, η)`; but `bS(y)` reads `α` at `ĝ⁻¹yĝ` / `ĝ⁻¹y`
     (conjugation by `ĝ`), needing its own decomposition (structurally like the γ one but with a
     leading `ĝ⁻¹`).
  2. **The η-index / Shapiro-composition reconciliation (the hard part).**  `psi`'s η-words are
     indexed by `γ⁻¹•v` through the **`U₀`-transversal**; `phi`'s η-words (`phi_inv_eq`'s two
     sums) are indexed by `γ̄⁻¹·u.out·ḡ` / `orbOut(γ̄⁻¹u.out)` through the **`G/N`-transversal +
     orbit reps**.  Matching them is the corestriction/Shapiro-composition identity — the `G/N`
     transversal factoring as `G/U₀ × {1,ĝ}` — and is a distinct, harder layer than the γ-word
     transversal calculus above.  `Λ` is expected to be `Λ(γ) = ∑_{v : G/U₀}`
     (`evensAux`/`bS`-reading of `ℓ^{U₀}_v(γ)`) · (`α`-correction `uCorr`/`W`), mirroring the free
     case's `Λ(γ) = ∑_h α(ℓ_h γ)·Δ(γ⁻¹h)`, but its exact form requires the full per-term
     expansion (piece 1 + the reconciliation of piece 2) before `δ¹Λ = phi − psi` can be checked
     by the free case's reindex-over-`O` + char-2-cancellation route.

  Everything above the assembly is committed and std-3; only the coboundary (`Λ` + `δ¹Λ = phi −
  psi`, ~150 lines) remains.  A focused session should build piece 1, then attack piece 2.

## Splice architecture (resolved 2026-07-04)

The factor-set / orbit-data def-layer (`FactorSet`, `graphPullback`, `RegRep`, `*OrbitDatum`, …)
now lives in `GQ2/OrbitData.lean` (top-level `namespace GQ2`); this file imports that (not
`SectionSix`), so `SectionSix` can import `ShapiroLedger` and splice
`lemma_6_15_free := ShapiroLedger.lemma_6_15_free_aux N hNo α β ghat` with **no import cycle**
(`SectionSix → ShapiroLedger → OrbitData`, and `SectionSix → OrbitData`).  That splice is now
live — `SectionSix.lemma_6_15_free` is `sorry`-free.  See `docs/orbit-data-refactor.md`.  The
same OrbitData layer unblocks every other P-15 own-file's splice (each imports `OrbitData`, not
`SectionSix`).  `lemma_6_15_involution` awaits the Step-3 core above before its own splice.
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

theorem lWordT_mem (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (v : G ⧸ U) (γ : G) : lWordT U T v γ ∈ U := by
  have h1 : ((T (γ⁻¹ • v) : G) : G ⧸ U) = γ⁻¹ • v := hT _
  have h2 : ((γ⁻¹ * T v : G) : G ⧸ U) = γ⁻¹ • v := by
    conv_rhs => rw [← hT v]
    exact MulAction.Quotient.smul_mk U γ⁻¹ (T v)
  have h3 : (γ⁻¹ * T v)⁻¹ * T (γ⁻¹ • v) ∈ U :=
    (QuotientGroup.eq (s := U)).mp (h2.trans h1.symm)
  have h4 : (γ⁻¹ * T v)⁻¹ * T (γ⁻¹ • v) = lWordT U T v γ := by
    rw [lWordT]; group
  rwa [h4] at h3

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

theorem tCorr_mem (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v) (v : G ⧸ U) :
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
  have hset : (fun γ : G => γ⁻¹ • v) ⁻¹' {w}
      = (fun γ : G => (γ⁻¹ * (v.out : G))⁻¹ * (w.out : G)) ⁻¹' (U : Set G) := by
    ext γ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe]
    constructor
    · intro h
      refine (QuotientGroup.eq (s := U)).mp ?_
      have h2 : ((γ⁻¹ * (v.out : G) : G) : G ⧸ U) = γ⁻¹ • v := by
        conv_rhs => rw [← QuotientGroup.out_eq' v]
        exact MulAction.Quotient.smul_mk U γ⁻¹ v.out
      rw [h2, h, QuotientGroup.out_eq']
    · intro h
      have h2 : ((γ⁻¹ * (v.out : G) : G) : G ⧸ U) = ((w.out : G) : G ⧸ U) :=
        (QuotientGroup.eq (s := U)).mpr h
      have h3 : ((γ⁻¹ * (v.out : G) : G) : G ⧸ U) = γ⁻¹ • v := by
        conv_rhs => rw [← QuotientGroup.out_eq' v]
        exact MulAction.Quotient.smul_mk U γ⁻¹ v.out
      rw [← h3, h2, QuotientGroup.out_eq']
  rw [hset]
  exact ((continuous_mul_right _).comp ((continuous_inv).comp
    ((continuous_mul_right _).comp continuous_inv))).isOpen_preimage _ hUo

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
    exact ((continuous_mul_left _).mul
      (continuous_comp_inv_smul U hUo v (fun w => (w.out : G)))).comp
      (continuous_id)
  exact hw.subtype_mk _

/-- `twistLambda` is continuous. -/
theorem twistLambda_continuous [Finite (G ⧸ U)] (hUo : IsOpen (U : Set G))
    (T : G ⧸ U → G) (hT : ∀ v : G ⧸ U, (T v : G ⧸ U) = v)
    (ν : U × U → ZMod 2) (hνc : Continuous ν) :
    Continuous (twistLambda U T hT ν) := by
  haveI : Fintype (G ⧸ U) := Fintype.ofFinite _
  have hEq : twistLambda U T hT ν = fun γ => ∑ v : G ⧸ U,
      twistCorr ν (lTrans U v γ) (tCorrEl U T hT v) (tCorrEl U T hT (γ⁻¹ • v)) := by
    funext γ
    exact finsum_eq_sum_of_fintype _
  rw [hEq]
  refine continuous_finset_sum Finset.univ (fun v _ => ?_)
  have ha : Continuous fun γ : G => lTrans U v γ := continuous_lTrans' U hUo v
  have hd : Continuous fun γ : G => tCorrEl U T hT (γ⁻¹ • v) :=
    continuous_comp_inv_smul U hUo v _
  simp only [twistCorr]
  exact ((hνc.comp (continuous_const.prodMk (ha.mul hd))).add
    (hνc.comp (ha.prodMk hd))).add
    (hνc.comp (hd.prodMk hd.inv))

variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

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
              (tCorrEl U T hT (η⁻¹ • w))) (γ⁻¹ • v) := by
      intro v
      simp only
      congr 2
      rw [← mul_smul, mul_inv_rev]
    rw [Finset.sum_congr rfl (fun v _ => hcong v)]
    have := sum_reindex_smul' U γ (fun w => twistCorr ν (lTrans U w η) (tCorrEl U T hT w)
      (tCorrEl U T hT (η⁻¹ • w)))
    simpa using this
  rw [hreindex]
  abel

end Topological

end TransversalChange

/-! ## Lemma 6.15, involution orbits (105) — foundations

The involution case compares `graphPullback(invOrbitDatum_{N,ḡ})` with `cor_{U₀→G}` of the
two-point Evens cocycle `evensNormFun_{N≤U₀}` (paper (107)–(109)), where `U₀ = ⟨N, ĝ⟩` is the
index-2-over-`N` subgroup (fixed field `K₀ = K^{⟨ḡ⟩}`) and `ḡ = mk ĝ` is an involution of
`G/N`.  These are the setup lemmas: `ḡ` is an involution, `G/U₀` is finite, and the two
index sets `G/U₀` and `(G/N)/⟨ḡ⟩` correspond (`U₀` maps onto `⟨ḡ⟩` under `G ↠ G/N`). -/

section Involution

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable (N : Subgroup G) [N.Normal]

/-- `ḡ = mk ĝ ≠ 1` in `G/N` when `ĝ ∉ N`. -/
theorem ghatQuot_ne_one (ghat : G) (hg : ghat ∉ N) : QuotientGroup.mk' N ghat ≠ 1 := by
  rw [Ne, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hg

/-- **The involution acts freely on `G/N`**: `z·ḡ ≠ z` for every `z` (no fixed points), because
`z·ḡ = z ⟹ ḡ = 1 ⟹ ĝ ∈ N`, contradicting `ĝ ∉ N`.  Hence every `⟨ḡ⟩`-orbit in `G/N` has
exactly two elements `{z, z·ḡ}` — the structural fact behind the involution comparison (there is
no diagonal/fixed-point term in the orbit sum). -/
theorem orbit_free (ghat : G) (hg : ghat ∉ N) (z : G ⧸ N) :
    z * (QuotientGroup.mk' N ghat) ≠ z := fun h =>
  ghatQuot_ne_one N ghat hg (mul_left_cancel (h.trans (mul_one z).symm))

/-- `ḡ = mk ĝ` is an involution of `G/N` when `ĝ² ∈ N`. -/
theorem ghatQuot_sq (ghat : G) (hg2 : ghat * ghat ∈ N) :
    (QuotientGroup.mk' N ghat) * (QuotientGroup.mk' N ghat) = 1 := by
  rw [← map_mul, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact hg2

/-- The image of `U₀ = ⟨N, ĝ⟩` under `G ↠ G/N` is `⟨ḡ⟩` (`N` dies, `ĝ ↦ ḡ`). -/
theorem map_U0_eq_zpowers (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    U₀.map (QuotientGroup.mk' N) = Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
  rw [hU₀, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hN : N.map (QuotientGroup.mk' N) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hx
  rw [hN, bot_sup_eq]

/-- `G/U₀` is finite (`U₀ ⊇ N` has index dividing the finite `N.index`). -/
theorem finite_quot_U0 [Finite (G ⧸ N)] (ghat : G) (U₀ : Subgroup G)
    (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) : Finite (G ⧸ U₀) := by
  have hle : N ≤ U₀ := hU₀ ▸ le_sup_left
  have hdvd : U₀.index ∣ N.index := Subgroup.index_dvd_of_le hle
  have hN0 : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  haveI : U₀.FiniteIndex := ⟨fun h => hN0 (Nat.eq_zero_of_zero_dvd (h ▸ hdvd))⟩
  exact Subgroup.finite_quotient_of_finiteIndex

/-- **The index correspondence** `G/U₀ ≃ (G/N)/⟨ḡ⟩`: both are the coset space of the
index-2-over-`N` subgroup `U₀ = ⟨N, ĝ⟩` (whose image in `G/N` is `⟨ḡ⟩`).  This bijects the two
orbit index sets of the involution comparison. -/
def invIndexEquiv (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    (G ⧸ U₀) ≃ ((G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)) where
  toFun := Quotient.lift (fun g : G => (QuotientGroup.mk (QuotientGroup.mk g)))
    (fun a b hab => Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
      have hm : (QuotientGroup.mk' N a)⁻¹ * QuotientGroup.mk' N b
          ∈ U₀.map (QuotientGroup.mk' N) := by
        rw [← map_inv, ← map_mul]
        exact Subgroup.mem_map_of_mem _ (QuotientGroup.leftRel_apply.mp hab)
      rwa [map_U0_eq_zpowers N ghat U₀ hU₀] at hm)))
  invFun := Quotient.lift
    (Quotient.lift (fun g : G => (QuotientGroup.mk g : G ⧸ U₀))
      (fun a b hab => Quotient.sound (QuotientGroup.leftRel_apply.mpr
        ((hU₀ ▸ le_sup_left : N ≤ U₀) (QuotientGroup.leftRel_apply.mp hab)))))
    (Quotient.ind fun a => Quotient.ind fun b => fun hxy =>
      Quotient.sound (QuotientGroup.leftRel_apply.mpr (by
        have hxy' : (QuotientGroup.mk' N a)⁻¹ * QuotientGroup.mk' N b
            ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := QuotientGroup.leftRel_apply.mp hxy
        rw [← map_inv, ← map_mul, ← map_U0_eq_zpowers N ghat U₀ hU₀, Subgroup.mem_map] at hxy'
        obtain ⟨u, hu, hue⟩ := hxy'
        have hn : u⁻¹ * (a⁻¹ * b) ∈ N := QuotientGroup.eq.mp (by
          rw [← QuotientGroup.mk'_apply, ← QuotientGroup.mk'_apply]; exact hue)
        have hrw : a⁻¹ * b = u * (u⁻¹ * (a⁻¹ * b)) := by group
        rw [hrw]
        exact mul_mem hu ((hU₀ ▸ le_sup_left : N ≤ U₀) hn))))
  left_inv := Quotient.ind fun _ => rfl
  right_inv := Quotient.ind fun y => QuotientGroup.induction_on y fun _ => rfl

variable [Finite (G ⧸ N)]

/-- The `⟨ḡ⟩`-orbit canonical representative of a `G/N`-element `z`. -/
noncomputable def orbOut (ghat : G) (z : G ⧸ N) : G ⧸ N :=
  ((z : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat)).out)

open scoped Classical in
/-- The involution graph pullback, unfolded to the two explicit sums of paper eq. (107)
(the oriented factor-set term + the orientation-reversal correction). -/
theorem phi_inv_eq (α : Z1 N (ZMod 2)) (ghat : G) (γ η : G) :
    graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat)) (QuotientGroup.mk' N)
        (shapiroFun N α.1) (γ, η)
      = (∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
          α.1 (lTrans N u.out γ)
            * α.1 (lTrans N ((QuotientGroup.mk' N γ)⁻¹ * (u.out * QuotientGroup.mk' N ghat)) η))
        + ∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
            (if (QuotientGroup.mk' N γ)⁻¹ * u.out
                  = orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out) then 0 else 1)
              * (α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)) η)
                * α.1 (lTrans N (orbOut N ghat ((QuotientGroup.mk' N γ)⁻¹ * u.out)
                    * QuotientGroup.mk' N ghat) η)) := rfl

/-- The involution corestriction side, unfolded to an explicit sum over `G ⧸ U₀` (the
`evensNormFun` two-point cocycle at the `U₀`-transversal words).  The remaining assembly
reindexes this over `(G/N)/⟨ḡ⟩` via `invIndexEquiv`, expands `evensNormFun`'s `if _ ∈ N`
case-split (`evensAux`/`bS`, `GQ2/EvensKahn.lean`) into `α`-values, matches the two `phi_inv_eq`
sums + orientation, and discharges the two-transversal `.out` discrepancy as a `δ¹`-coboundary. -/
theorem psi_inv_eq (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (γ η : G) :
    cor2Fun U₀ (fun p ↦ evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩
        (fun u ↦ α.1 ⟨u.1.1, u.2⟩) (p.1, p.2)) (γ, η)
      = ∑ᶠ v : G ⧸ U₀, evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (fun u ↦ α.1 ⟨u.1.1, u.2⟩)
          (lTrans U₀ v γ, lTrans U₀ (γ⁻¹ • v) η) := rfl

/-- `ḡ = mk ĝ` has order exactly 2 in `G/N` (`ĝ ∉ N`, `ĝ² ∈ N`). -/
theorem orderOf_ghatQuot (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N) :
    orderOf (QuotientGroup.mk' N ghat) = 2 := by
  have hne : QuotientGroup.mk' N ghat ≠ 1 := by
    rw [QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]; exact hg
  have hsq : (QuotientGroup.mk' N ghat) ^ 2 = 1 := by
    rw [sq]; exact ghatQuot_sq N ghat hg2
  have hdvd : orderOf (QuotientGroup.mk' N ghat) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exact absurd (orderOf_eq_one_iff.mp h1) hne
  · exact h2

/-- `N` has index 2 in `U₀ = ⟨N, ĝ⟩`: the map `U₀ → G/N` has kernel `N.subgroupOf U₀` and
range `⟨ḡ⟩` (order 2), so `U₀/(N.subgroupOf U₀) ≅ ⟨ḡ⟩`. -/
theorem subgroupOf_index_two (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) :
    (N.subgroupOf U₀).index = 2 := by
  set f : U₀ →* G ⧸ N := (QuotientGroup.mk' N).comp U₀.subtype with hf
  have hker : f.ker = N.subgroupOf U₀ := by
    ext u
    simp only [MonoidHom.mem_ker, hf, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_subtype]
  have hrange : f.range = Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
    rw [hf, MonoidHom.range_comp, Subgroup.subtype_range, map_U0_eq_zpowers N ghat U₀ hU₀]
  have hcard : Nat.card (U₀ ⧸ N.subgroupOf U₀) = 2 := by
    rw [← hker]
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hrange, Nat.card_zpowers,
      orderOf_ghatQuot N ghat hg hg2]
  rw [Subgroup.index, hcard]

/-! ### Involution assembly — setup -/

/-- `N.subgroupOf U₀` is open in `U₀` (preimage of the open `N` under `U₀ ↪ G`). -/
theorem subgroupOf_isOpen (hNo : IsOpen (N : Set G)) (U₀ : Subgroup G) :
    IsOpen ((N.subgroupOf U₀ : Subgroup U₀) : Set U₀) := by
  rw [Subgroup.coe_subgroupOf]
  exact hNo.preimage continuous_subtype_val

/-- The restriction of `α` to `N.subgroupOf U₀` (reading `α` at the underlying `N`-element). -/
noncomputable def alphaOn (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) :
    (N.subgroupOf U₀) → ZMod 2 := fun u ↦ α.1 ⟨u.1.1, u.2⟩

/-- `alphaOn` is additive (inherited from `α`, a hom on `N`). -/
theorem alphaOn_hom (α : Z1 N (ZMod 2)) (U₀ : Subgroup G)
    (x y : N.subgroupOf U₀) : alphaOn N α U₀ (x * y) = alphaOn N α U₀ x + alphaOn N α U₀ y := by
  have h : (⟨(x * y).1.1, (x * y).2⟩ : N) = ⟨x.1.1, x.2⟩ * ⟨y.1.1, y.2⟩ := Subtype.ext rfl
  simp only [alphaOn, h, z1_mul N α]

/-- `alphaOn` is continuous. -/
theorem alphaOn_continuous (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) :
    Continuous (alphaOn N α U₀) := by
  have hα : Continuous α.1 := (mem_Z1_iff.mp α.2).1
  exact hα.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)

/-- **Step 1 (reindex).** The involution corestriction side, reindexed from a sum over `G/U₀` to
a sum over the orbit set `O = (G/N)/⟨ḡ⟩` via the bijection `invIndexEquiv`. -/
theorem psi_inv_reindex (α : Z1 N (ZMod 2)) (ghat : G)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (hgU : ghat ∈ U₀) (γ η : G) :
    cor2Fun U₀ (fun p ↦ evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩
        (alphaOn N α U₀) (p.1, p.2)) (γ, η)
      = ∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat),
          evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
            (lTrans U₀ ((invIndexEquiv N ghat U₀ hU₀).symm u) γ,
             lTrans U₀ (γ⁻¹ • ((invIndexEquiv N ghat U₀ hU₀).symm u)) η) := by
  show (∑ᶠ v : G ⧸ U₀, evensNormFun (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀)
      (lTrans U₀ v γ, lTrans U₀ (γ⁻¹ • v) η)) = _
  exact (finsum_comp_equiv (invIndexEquiv N ghat U₀ hU₀).symm).symm

/-! ### Step 2 — the Evens-norm building blocks as explicit `α`-values

`evensAux`/`bS` on `U₀` (relative to `N.subgroupOf U₀`, shift `ĝ`) read `α` at the underlying
`N`-element, using the index-2 side bookkeeping (`ĝ ∉ N`; `x·ĝ ∈ N ⟺ x ∉ N`). -/

theorem evensAux_alphaOn_mem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (x : U₀) (hx : (x : G) ∈ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) x = α.1 ⟨(x : G), hx⟩ :=
  evensAux_of_mem (alphaOn N α U₀) (Subgroup.mem_subgroupOf.mpr hx)

theorem evensAux_alphaOn_notMem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (x : U₀) (hx : (x : G) ∉ N) (hmem : (x : G) * ghat ∈ N) :
    evensAux (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) x = α.1 ⟨(x : G) * ghat, hmem⟩ :=
  evensAux_of_notMem hUi hs (alphaOn N α U₀) (fun h => hx (Subgroup.mem_subgroupOf.mp h))

theorem bS_alphaOn_mem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (y : U₀) (hy : (y : G) ∈ N) (hmem : ghat⁻¹ * (y : G) * ghat ∈ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) y = α.1 ⟨ghat⁻¹ * (y : G) * ghat, hmem⟩ :=
  bS_of_mem hUi hs (alphaOn N α U₀) (Subgroup.mem_subgroupOf.mpr hy)

theorem bS_alphaOn_notMem (α : Z1 N (ZMod 2)) (ghat : G) (U₀ : Subgroup G) (hgU : ghat ∈ U₀)
    (hUi : (N.subgroupOf U₀).index = 2) (hs : (⟨ghat, hgU⟩ : U₀) ∉ N.subgroupOf U₀)
    (y : U₀) (hy : (y : G) ∉ N) (hmem : ghat⁻¹ * (y : G) ∈ N) :
    bS (N.subgroupOf U₀) ⟨ghat, hgU⟩ (alphaOn N α U₀) y = α.1 ⟨ghat⁻¹ * (y : G), hmem⟩ :=
  bS_of_notMem hUi hs (alphaOn N α U₀) (fun h => hy (Subgroup.mem_subgroupOf.mp h))

/-! ### Step 3 — the transversal reconciliation

Both sides are now sums over `O = (G/N)/⟨ḡ⟩` (`phi_inv_eq`, `psi_inv_reindex`).  The pieces below
bridge the `U₀`-transversal words (`ℓ^{U₀}`, used by `psi`) and the `N`-transversal words (`ℓ^N`,
used by `phi`), and the orientation. -/

/-- **Membership correspondence**: `ℓ^{U₀}_v(γ) ∈ N` iff the `N`-images of the chosen `U₀`-reps of
`v` and `γ⁻¹•v` are `γ̄`-aligned.  (The `∉ N`/flipped case is the orientation reversal.) -/
theorem lWordU0_mem_N_iff (U₀ : Subgroup G) (v : G ⧸ U₀) (γ : G) :
    lWord U₀ v γ ∈ N ↔
      QuotientGroup.mk' N ((γ⁻¹ • v).out)
        = (QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N v.out := by
  rw [← QuotientGroup.eq_one_iff, lWord, ← QuotientGroup.mk'_apply, map_mul, map_mul, map_inv,
    QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, mul_assoc,
    inv_mul_eq_one]
  constructor
  · intro h; rw [h]; group
  · intro h; rw [h]; group

/-- The `G/N`-canonical lift of the `N`-image of the `U₀`-rep `v.out`. -/
noncomputable def nLift (U₀ : Subgroup G) (v : G ⧸ U₀) : G :=
  (QuotientGroup.mk' N (v.out : G)).out

/-- The `U₀`- vs `N`-transversal correction: `v.out = nLift v · uCorr v` with `uCorr v ∈ N`. -/
noncomputable def uCorr (U₀ : Subgroup G) (v : G ⧸ U₀) : G :=
  (nLift N U₀ v)⁻¹ * (v.out : G)

theorem uCorr_mem (U₀ : Subgroup G) (v : G ⧸ U₀) : uCorr N U₀ v ∈ N := by
  have h : (QuotientGroup.mk (nLift N U₀ v) : G ⧸ N) = QuotientGroup.mk (v.out : G) := by
    rw [nLift]; exact QuotientGroup.out_eq' _
  rw [uCorr, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv, h,
    inv_mul_cancel]

/-- **Word factorization** (`U₀` → `N`-canonical lifts): `ℓ^{U₀}_v(γ)` sandwiches the
`nLift`-word between two `N`-corrections `uCorr`.  This is the `U₀`-analog of `lWord_shift`. -/
theorem lWordU0_factor (U₀ : Subgroup G) (v : G ⧸ U₀) (γ : G) :
    lWord U₀ v γ = (uCorr N U₀ v)⁻¹
      * ((nLift N U₀ v)⁻¹ * γ * nLift N U₀ (γ⁻¹ • v)) * uCorr N U₀ (γ⁻¹ • v) := by
  simp only [uCorr, lWord]; group

/-- `uCorr` as an element of `↥N`. -/
noncomputable def uCorrEl (U₀ : Subgroup G) (v : G ⧸ U₀) : N := ⟨uCorr N U₀ v, uCorr_mem N U₀ v⟩

/-- In the **aligned** case the `nLift`-word is exactly the `N`-transversal word at `mk v.out`. -/
theorem nLiftWord_aligned (U₀ : Subgroup G) (v : G ⧸ U₀) (γ : G) (hx : lWord U₀ v γ ∈ N) :
    (nLift N U₀ v)⁻¹ * γ * nLift N U₀ (γ⁻¹ • v)
      = lWord N (QuotientGroup.mk' N (v.out : G)) γ := by
  have hzb : QuotientGroup.mk' N ((γ⁻¹ • v).out) = γ⁻¹ • QuotientGroup.mk' N (v.out : G) := by
    rw [(lWordU0_mem_N_iff N U₀ v γ).mp hx, quot_smul_eq_mk_mul, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv]
  rw [lWord, nLift, nLift, hzb]

/-- **Aligned-case α-decomposition** (`beta_lTrans_shift`-analog): when `ℓ^{U₀}_v(γ) ∈ N`, its
`α`-value is the base `N`-word value plus the two `uCorr` corrections (`α` a hom). -/
theorem alpha_lWordU0_aligned (α : Z1 N (ZMod 2)) (U₀ : Subgroup G) (v : G ⧸ U₀) (γ : G)
    (hx : lWord U₀ v γ ∈ N) :
    α.1 ⟨lWord U₀ v γ, hx⟩
      = α.1 (uCorrEl N U₀ v) + α.1 (lTrans N (QuotientGroup.mk' N (v.out : G)) γ)
        + α.1 (uCorrEl N U₀ (γ⁻¹ • v)) := by
  have hfac : (⟨lWord U₀ v γ, hx⟩ : N)
      = (uCorrEl N U₀ v)⁻¹ * lTrans N (QuotientGroup.mk' N (v.out : G)) γ
        * uCorrEl N U₀ (γ⁻¹ • v) := by
    apply Subtype.ext
    simp only [uCorrEl, lTrans, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [← nLiftWord_aligned N U₀ v γ hx, lWordU0_factor N U₀ v γ]
  rw [hfac, z1_mul N α, z1_mul N α, z1_inv N α]

/-- **Orbit equivariance**: the `⟨ḡ⟩`-orbit of `mk((γ⁻¹•v).out)` equals that of `γ̄⁻¹·mk(v.out)`
(both are `N`-images of `U₀`-lifts of `γ⁻¹•v`). -/
theorem orbit_equiv (ghat : G) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (v : G ⧸ U₀) (γ : G) :
    (QuotientGroup.mk (QuotientGroup.mk' N ((γ⁻¹ • v).out)) :
        (G ⧸ N) ⧸ Subgroup.zpowers (QuotientGroup.mk' N ghat))
      = QuotientGroup.mk ((QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (v.out : G)) := by
  rw [QuotientGroup.eq, ← map_U0_eq_zpowers N ghat U₀ hU₀, Subgroup.mem_map]
  refine ⟨(γ⁻¹ • v).out⁻¹ * (γ⁻¹ * (v.out : G)), ?_, ?_⟩
  · have h1 : ((( γ⁻¹ • v).out : G) : G ⧸ U₀) = γ⁻¹ • v := QuotientGroup.out_eq' _
    have h2 : ((γ⁻¹ * (v.out : G)) : G ⧸ U₀) = γ⁻¹ • v := by
      conv_rhs => rw [← QuotientGroup.out_eq' v]
      exact MulAction.Quotient.smul_mk U₀ γ⁻¹ v.out
    exact (QuotientGroup.eq (s := U₀)).mp (h1.trans h2.symm)
  · rw [map_mul, map_mul, map_inv, map_inv]

/-- In `⟨g⟩` with `g² = 1`, every element is `1` or `g`. -/
theorem mem_zpowers_sq_one {H : Type*} [Group H] {g t : H} (hg2 : g * g = 1)
    (ht : t ∈ Subgroup.zpowers g) : t = 1 ∨ t = g := by
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
  have hsq : g ^ (2 : ℤ) = 1 := by rw [show (2 : ℤ) = 1 + 1 by ring, zpow_add, zpow_one]; exact hg2
  rcases Int.even_or_odd n with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · left; rw [show m + m = 2 * m by ring, zpow_mul, hsq, one_zpow]
  · right; rw [zpow_add, zpow_mul, hsq, one_zpow, one_mul, zpow_one]

/-- **Flipped case**: when `ℓ^{U₀}_v(γ) ∉ N`, the `N`-image of `(γ⁻¹•v).out` is the *other* orbit
element `(γ̄⁻¹·mk v.out)·ḡ`. -/
theorem zb_flipped (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : ¬ (lWord U₀ v γ ∈ N)) :
    QuotientGroup.mk' N ((γ⁻¹ • v).out)
      = (QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (v.out : G) * QuotientGroup.mk' N ghat := by
  set za := (QuotientGroup.mk' N γ)⁻¹ * QuotientGroup.mk' N (v.out : G) with hza
  set zb := QuotientGroup.mk' N ((γ⁻¹ • v).out) with hzb
  have hmem : za⁻¹ * zb ∈ Subgroup.zpowers (QuotientGroup.mk' N ghat) := by
    rw [← QuotientGroup.eq]; exact (orbit_equiv N ghat U₀ hU₀ v γ).symm
  have hne : za⁻¹ * zb ≠ 1 := by
    intro h
    exact hx ((lWordU0_mem_N_iff N U₀ v γ).mpr (inv_mul_eq_one.mp h).symm)
  rcases mem_zpowers_sq_one (ghatQuot_sq N ghat hg2) hmem with h | h
  · exact absurd h hne
  · rw [← h]; group

/-- The `.out` shift: `(k·ḡ).out = k.out · ĝ · shiftCorr(k)` (rearranged `shiftCorr`). -/
theorem out_ghat_shift (ghat : G) (k : G ⧸ N) :
    (k * (ghat : G ⧸ N)).out = k.out * ghat * shiftCorr N ghat k := by
  rw [shiftCorr]; group

/-- **Flipped** analog of `nLiftWord_aligned`: the `nLift`-word is the base `N`-word followed by a
`ĝ`-shift correction (from `zb` being the reversed orbit rep). -/
theorem nLiftWord_flipped (ghat : G) (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat) (v : G ⧸ U₀) (γ : G)
    (hx : ¬ (lWord U₀ v γ ∈ N)) :
    (nLift N U₀ v)⁻¹ * γ * nLift N U₀ (γ⁻¹ • v)
      = lWord N (QuotientGroup.mk' N (v.out : G)) γ * ghat
        * shiftCorr N ghat (γ⁻¹ • QuotientGroup.mk' N (v.out : G)) := by
  have hzb : QuotientGroup.mk' N ((γ⁻¹ • v).out)
      = (γ⁻¹ • QuotientGroup.mk' N (v.out : G)) * (ghat : G ⧸ N) := by
    rw [zb_flipped N ghat hg hg2 U₀ hU₀ v γ hx, quot_smul_eq_mk_mul, QuotientGroup.mk'_apply,
      ← QuotientGroup.mk_inv, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
  rw [lWord, nLift, nLift, hzb, out_ghat_shift]; group

/-- **Flipped-case α-decomposition**: when `ℓ^{U₀}_v(γ) ∉ N`, the α-value of `ℓ^{U₀}_v(γ)·ĝ`
(the `evensAux` reading) is the base `N`-word value plus `uCorr` and a `ĝ`-shift correction `W`. -/
theorem alpha_lWordU0_flipped (α : Z1 N (ZMod 2)) (ghat : G) (hg : ghat ∉ N)
    (hg2 : ghat * ghat ∈ N) (U₀ : Subgroup G) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (v : G ⧸ U₀) (γ : G) (hx : ¬ (lWord U₀ v γ ∈ N)) (hmem : lWord U₀ v γ * ghat ∈ N)
    (hW : ghat * shiftCorr N ghat (γ⁻¹ • QuotientGroup.mk' N (v.out : G))
        * uCorr N U₀ (γ⁻¹ • v) * ghat ∈ N) :
    α.1 ⟨lWord U₀ v γ * ghat, hmem⟩
      = α.1 (uCorrEl N U₀ v) + α.1 (lTrans N (QuotientGroup.mk' N (v.out : G)) γ)
        + α.1 ⟨ghat * shiftCorr N ghat (γ⁻¹ • QuotientGroup.mk' N (v.out : G))
            * uCorr N U₀ (γ⁻¹ • v) * ghat, hW⟩ := by
  have hfac : (⟨lWord U₀ v γ * ghat, hmem⟩ : N)
      = (uCorrEl N U₀ v)⁻¹ * lTrans N (QuotientGroup.mk' N (v.out : G)) γ
        * ⟨ghat * shiftCorr N ghat (γ⁻¹ • QuotientGroup.mk' N (v.out : G))
            * uCorr N U₀ (γ⁻¹ • v) * ghat, hW⟩ := by
    apply Subtype.ext
    simp only [uCorrEl, lTrans, Subgroup.coe_mul, InvMemClass.coe_inv]
    rw [lWordU0_factor N U₀ v γ, nLiftWord_flipped N ghat hg hg2 U₀ hU₀ v γ hx]
    group
  rw [hfac, z1_mul N α, z1_mul N α, z1_inv N α]

end Involution

end ShapiroLedger

end GQ2
