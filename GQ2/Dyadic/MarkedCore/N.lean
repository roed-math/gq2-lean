/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.HandleMixInst
public import GQ2.FrattiniCriterion
public import GQ2.Reconstruction

@[expose] public section

/-!
# MC-N: the rank-four Smith–Witt stabilizer of the `N_α` core, and its lifting

**Ticket MC4** of the dyadic campaign (lane MC), implementing the MC1 design memo
`docs/dyadic/mc-design.md` §3 (the `N`-frame), §3.3–§3.4 (the stabilizer and its six Nielsen
families), §5 (the three lifting strata) and §6.2/§6.4 (the obligation and hypothesis shapes),
against the packet (`refs/dyadic-presentations-formalization-proof.tex` §7, Prop. 7.2, §14).
Everything is uniform in `α ≥ 2`; the `N`-frame is completely α-free (memo V1).

## Contents

* **§1 The general-`h` frame** — `NFrame α h`, the rank-`(4+2h)` abelianization frame
  `D_N^{ab} ≅ ℤ/2 ⊕ ℤ₂^{3+2h}` with the torsion coordinate at the **marked** generator `x̄₀`
  and no forced row (memo §3.1); the bridge `NFrame.toNDecomposition` to MC2's rank-four
  `NDecomposition`, and `demushkinQ_DN_nFrame : q = 2` at every `h`.
* **§2 Row extraction** — the ℚ₂ engine of `GQ2/Roe/MarkedMatching.lean:307–1112` /
  `prop_3_8_classification` ported to rank four: coordinate monomials, the χ-value on
  coordinates, and the **integral pinning of the `x̄₁`-row by the infinite-order unit
  `v = −(1+2^α)⁻¹`** (`nUnit_zpowZtwo_injective`) — the memo's decisive simplification over the
  `M`-side (no `B`-scaling).
* **§3 The Smith–Witt stabilizer** — the mod-2 cup Gram `nGram` (memo §3.2(iii)), the isometry
  condition `M̄·G_N·M̄ᵀ = G_N` (memo §2.3's convention, dualized to `H¹`), and
  **`nStabilizer_classification`**: every frame automorphism preserving the marked invariant
  triple is given by a *unique* parameter tuple `(τ, p, q, τ_σ, τ_{x₂}, g)` with
  `g ∈ GL₂(ℤ₂)` and the two mod-2 couplings — the closed form
  `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` of memo §3.3.
* **§4 The S1 lifts** — the exact core transvections `dnTauBEquiv` (family N1) and
  `dnTauCEquiv` (family N3), completing HM4's `dnTauDEquiv` (family N2) to the full elementary
  block; χ-preservation and the ν-frame and abelianized rows of each.
* **§5 The S2 lift (axiom B8)** — `nPsiEquiv`: the `u`-scaling of the `(σ, x₂)`-block built
  from **two nested applications of the existing axiom B8** through MC2's
  `peripheralTriple_scaling` transport (memo §5.2) — family N4, with its shears, and the
  sheared-clean version `nScaling_lift`.  No new axiom; B8 enters as the explicit argument
  `R : PeripheralCyclotomicAction` exactly as in MC2's `nOuter_scaling`.
* **§6 The S3 binder and the hypothesis `def`s** — `NMixHypothesis` (memo §8 Decision 2(B), a
  `def`, **never an axiom**), the Labute classification hypothesis `NLabHypothesis` with its
  image invariant `imChiN` (memo §6.4), and the **vocabulary finding**
  `nCoreMixHypothesis_not_of_mix`: HM5's schematic `NCoreMixHypothesis` is *unsatisfiable* for
  any genuinely mixing stratum set, because membership in `A(P,h)` forces the `x₁`-row to be
  rigid (`dnClearAuts_fixes_dnX1`).  The sound binder is therefore stated at the marked
  generators, not through `DnRealizes`.
* **§7 The composition theorem** — `nMarkedCorrection` (packet Prop. 7.2 at the `N`-core):
  given any `ν'` with unimodular `(ν'(σ̄), ν'(x̄₂))`, an automorphism `u` with
  `χ_N ∘ u = χ_N` and `ν' ∘ u = ν_N`, assembled from HM5's handle stratum
  (`NLiftSplit.handle` / `nHandleMixLift`), the exact `SL₂`-solve on the `(σ, x₂)`-plane, and
  the `NMixHypothesis` binder for the `x̄₁`-slot — memo §5.3's three strata, composed.
* **§8 The parametrized lift** — `nStabParam_lift`: every admissible stabilizer parameter tuple
  is realized by a continuous automorphism of `D_N`, via the six families (N1–N3 exact, N4
  through B8, N5/N6 through the binder); with `nStabilizer_classification` this is the
  memo §6.2 obligation `prop_MC_N_lift`.
* **§9 Stress pins** at `(α, h) = (2, 0)` and `(2, 1)`.

## Dedup notes (reserved-name rule)

MC3 (`M.lean`) works in parallel; every declaration here is `n`- or `dn`-prefixed.  Three
generic helpers are restated name-distinct because their originals live in **non-module**
files that a module file cannot import: the `conjP` algebra (`nConjP_mul` … — private in
`GQ2/AnabelianBridge/Construction.lean`), the index-2 quotient lemmas (`nQuotient_mul_comm` … —
`GQ2/AnabelianBridge/Construction.lean` §IndexTwo), and the closed-generation lemmas
(`nTopClosure_le_ker`/`nTopClosure_le_comap` — ibid. §PinnedGeneration).  The
`topAbelianization` profinite instances are re-registered **section-locally** exactly as in
`GQ2/SectionThree.lean` (see the caution there: a file-global instance perturbs `K ⧸ M`
resolution, and §5 works with such quotients).
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

/-! ## §0 Generic helpers (dedup restatements; see the module docstring)

`conjP` algebra: `conjP x g = g⁻¹xg` is multiplicative, inversive and power-compatible in its
first argument.  Originals are `private` in `GQ2/AnabelianBridge/Construction.lean` (non-module);
restated `n`-prefixed. -/

section ConjPAlgebra

variable {G : Type*} [Group G]

theorem nConjP_mul (x y c : G) : conjP x c * conjP y c = conjP (x * y) c := by
  simp [conjP, mul_assoc]

theorem nConjP_inv (x c : G) : (conjP x c)⁻¹ = conjP x⁻¹ c := by
  simp [conjP, mul_assoc]

theorem nConjP_pow (x c : G) (n : ℕ) : conjP x c ^ n = conjP (x ^ n) c := by
  induction n with
  | zero => simp [conjP]
  | succ k ih => rw [pow_succ, pow_succ, ih, nConjP_mul]

theorem nConjP_conjP (x c d : G) : conjP (conjP x c) d = conjP x (c * d) := by
  simp [conjP, mul_assoc]

theorem nConjP_one (x : G) : conjP x 1 = x := by simp [conjP]

end ConjPAlgebra

/-- A continuous hom into a Hausdorff group vanishing on a pinned generating family kills the
whole closed generated subgroup (dedup of `GQ2.topClosure_closure_le_ker`,
`GQ2/AnabelianBridge/Construction.lean:147`, non-module). -/
theorem nTopClosure_le_ker {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [T2Space H]
    (q : ContinuousMonoidHom G H) {S : Set G} (h : ∀ x ∈ S, q x = 1) :
    (Subgroup.closure S).topologicalClosure ≤ q.toMonoidHom.ker := by
  refine Subgroup.topologicalClosure_minimal _ ((Subgroup.closure_le _).mpr h) ?_
  have hker : (q.toMonoidHom.ker : Set G) = q ⁻¹' {1} := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
    rfl
  rw [hker]
  exact isClosed_singleton.preimage q.continuous_toFun

/-- A continuous hom sending a pinned generating family into a closed subgroup sends the whole
closed generated subgroup into it (dedup of `GQ2.topClosure_closure_le_comap`,
`GQ2/AnabelianBridge/Construction.lean:162`, non-module). -/
theorem nTopClosure_le_comap {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H]
    (f : ContinuousMonoidHom G H) {S : Set G} {M : Subgroup H}
    (hM : IsClosed (M : Set H)) (h : ∀ x ∈ S, f x ∈ M) :
    (Subgroup.closure S).topologicalClosure ≤ M.comap f.toMonoidHom := by
  refine Subgroup.topologicalClosure_minimal _
    ((Subgroup.closure_le _).mpr fun x hx => Subgroup.mem_comap.mpr (h x hx)) ?_
  exact hM.preimage f.continuous_toFun

/-! ## §1 The general-`h` `N`-frame  (memo §3.1, §4.2; deliverable 1)

`D_N^{ab} ≅ ℤ/2·x̄₀ ⊕ ℤ₂·x̄₁ ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₂ ⊕ ℤ₂^{2h}` — the torsion coordinate **is** the
marked generator `x̄₀`, there is **no forced row**, and the handle block contributes `2h` free
`ℤ₂`-coordinates (memo §4.2: handles are invisible to the relation vector).  The frame is
completely α-free; `α` appears only through the relator that presents the group.

As with MC2's `NDecomposition` (the `h = 0` case, `GQ2/Dyadic/MarkedCore/Cores.lean:1786`),
the existence theorem (`phiEquiv` route) is *not* in scope: consumers take the frame as a
hypothesis, exactly as `prop_3_8_classification` consumes `BDecomposition`. -/

/-- The coordinate model of the rank-`(4+2h)` `N`-frame: `ℤ/2 × ℤ₂³ × ℤ₂^{2h}`. -/
abbrev NFrameModel (h : ℕ) : Type :=
  Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]))

/-- The handle coordinate index of the `j`-th handle's first letter `u_j`. -/
def nHandleCoordU {h : ℕ} (j : Fin h) : Fin (2 * h) :=
  ⟨2 * (j : ℕ), by omega⟩

/-- The handle coordinate index of the `j`-th handle's second letter `v_j`. -/
def nHandleCoordV {h : ℕ} (j : Fin h) : Fin (2 * h) :=
  ⟨2 * (j : ℕ) + 1, by omega⟩

/-- **The general-`h` `N`-frame** (memo §3.1/§4.2, deliverable 1 of MC4): a continuous
coordinate isomorphism `D_N^{ab} ≅ ℤ/2 ⊕ ℤ₂^{3+2h}` in which the torsion coordinate is the
**marked** generator `x̄₀` (no forced row — the structural difference from `M`, memo V1), the
three remaining core letters occupy the `ℤ₂³`-block, and the `2h` handle letters the free tail.
The frame is α-free. -/
structure NFrame (α h : ℕ) where
  /-- The coordinate isomorphism. -/
  e : ContinuousMulEquiv (topAbelianization (DN α h : Type)) (NFrameModel h)
  /-- The torsion coordinate — the *marked* generator `x̄₀ ↦ (1, 0, 0, 0, 0)`. -/
  map_t : e (abMk (dnX0 α h)) = ofAdd (1, 0, 0, 0, 0)
  /-- `x̄₁ ↦ (0, 1, 0, 0, 0)`. -/
  map_B : e (abMk (dnX1 α h)) = ofAdd (0, 1, 0, 0, 0)
  /-- `σ̄ ↦ (0, 0, 1, 0, 0)`. -/
  map_C : e (abMk (dnSigma α h)) = ofAdd (0, 0, 1, 0, 0)
  /-- `x̄₂ ↦ (0, 0, 0, 1, 0)`. -/
  map_D : e (abMk (dnX2 α h)) = ofAdd (0, 0, 0, 1, 0)
  /-- `ū_j ↦` the `2j`-th handle coordinate. -/
  map_U : ∀ j : Fin h, e (abMk (dnGen α h (handleIdxU j)))
    = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordU j) 1)
  /-- `v̄_j ↦` the `(2j+1)`-st handle coordinate. -/
  map_V : ∀ j : Fin h, e (abMk (dnGen α h (handleIdxV j)))
    = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordV j) 1)

/-- The rank-four model is the `h = 0` frame model with the empty handle tail dropped —
the continuous isomorphism used by the `NDecomposition` bridge. -/
noncomputable def nFrameModelZero :
    ContinuousMulEquiv (NFrameModel 0) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2])) where
  toFun p := ofAdd (p.toAdd.1, p.toAdd.2.1, p.toAdd.2.2.1, p.toAdd.2.2.2.1)
  invFun q := ofAdd (q.toAdd.1, q.toAdd.2.1, q.toAdd.2.2.1, q.toAdd.2.2.2, 0)
  left_inv p := by
    refine Multiplicative.toAdd.injective ?_
    refine Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl ?_)))
    exact funext fun i => absurd i.2 (by omega)
  right_inv q := rfl
  map_mul' p q := rfl
  continuous_toFun := by
    refine continuous_ofAdd.comp ?_
    exact ((continuous_fst.comp continuous_toAdd).prodMk
      (((continuous_fst.comp continuous_snd).comp continuous_toAdd).prodMk
        (((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp
            continuous_toAdd).prodMk
          ((continuous_fst.comp (continuous_snd.comp
            (continuous_snd.comp continuous_snd))).comp continuous_toAdd))))
  continuous_invFun := by
    refine continuous_ofAdd.comp ?_
    exact ((continuous_fst.comp continuous_toAdd).prodMk
      (((continuous_fst.comp continuous_snd).comp continuous_toAdd).prodMk
        (((continuous_fst.comp (continuous_snd.comp continuous_snd)).comp
            continuous_toAdd).prodMk
          (((continuous_snd.comp (continuous_snd.comp continuous_snd)).comp
              continuous_toAdd).prodMk
            continuous_const))))

/-- **The `h = 0` bridge**: a rank-four `NFrame` *is* MC2's `NDecomposition`
(`GQ2/Dyadic/MarkedCore/Cores.lean:1786`), so the §3 stabilizer classification below applies
to any group carrying the general-`h` frame at `h = 0`. -/
noncomputable def NFrame.toNDecomposition {α : ℕ} (F : NFrame α 0) : NDecomposition α where
  e := F.e.trans nFrameModelZero
  map_t := by
    show nFrameModelZero (F.e (abMk (dnX0 α 0))) = _
    rw [F.map_t]; rfl
  map_B := by
    show nFrameModelZero (F.e (abMk (dnX1 α 0))) = _
    rw [F.map_B]; rfl
  map_C := by
    show nFrameModelZero (F.e (abMk (dnSigma α 0))) = _
    rw [F.map_C]; rfl
  map_D := by
    show nFrameModelZero (F.e (abMk (dnX2 α 0))) = _
    rw [F.map_D]; rfl

section FrameTorsion

private lemma nPadicInt_nsmul_eq_zero {n : ℕ} (hn : 0 < n) {b : ℤ_[2]} (h : n • b = 0) :
    b = 0 := by
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr hn.ne')
  · exact h1

/-- A finite-order element of the general-`h` model has zero `ℤ₂`-components (core and
handle) — the rank-`(4+2h)` extension of the private `finOrder_zmod2_prod4` of `Cores.lean`. -/
private lemma nFinOrder_model {h : ℕ} {a : ZMod 2} {b c d : ℤ_[2]} {f : Fin (2 * h) → ℤ_[2]}
    (hfin : IsOfFinOrder (ofAdd (a, b, c, d, f) : NFrameModel h)) :
    b = 0 ∧ c = 0 ∧ d = 0 ∧ f = 0 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hfin
  obtain ⟨n, hn, hpow⟩ := hfin
  rw [← ofAdd_nsmul, ← ofAdd_zero] at hpow
  have hz := Multiplicative.ofAdd.injective hpow
  have hb : n • b = 0 := congrArg (fun p => p.2.1) hz
  have hc : n • c = 0 := congrArg (fun p => p.2.2.1) hz
  have hd : n • d = 0 := congrArg (fun p => p.2.2.2.1) hz
  have hf : n • f = 0 := congrArg (fun p => p.2.2.2.2) hz
  refine ⟨nPadicInt_nsmul_eq_zero hn hb, nPadicInt_nsmul_eq_zero hn hc,
    nPadicInt_nsmul_eq_zero hn hd, funext fun i => ?_⟩
  have hfi : n • f i = 0 := by
    have hfi' := congrFun hf i
    rwa [Pi.smul_apply] at hfi'
  exact nPadicInt_nsmul_eq_zero hn hfi

/-- **Torsion of the general-`h` model**: the finite-order subtype of `ℤ/2 × ℤ₂^{3+2h}` is
`ℤ/2` — the `Cores.lean` `torsionEquivZMod2Four` at every handle count. -/
noncomputable def nTorsionEquivZMod2 (h : ℕ) :
    {z : NFrameModel h // IsOfFinOrder z} ≃ ZMod 2 where
  toFun z := z.1.toAdd.1
  invFun a := ⟨ofAdd (a, 0, 0, 0, 0), by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨2, by norm_num, ?_⟩
    rw [← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · show (2 : ℕ) • a = 0
      rw [two_nsmul]
      exact (by decide : ∀ b : ZMod 2, b + b = 0) a
    all_goals simp⟩
  left_inv := by
    rintro ⟨z, hz⟩
    apply Subtype.ext
    have hz' : IsOfFinOrder (ofAdd
        (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
          : NFrameModel h) := by
      rw [show (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
        = z.toAdd from rfl, ofAdd_toAdd]
      exact hz
    obtain ⟨hb, hc, hd, hf⟩ := nFinOrder_model hz'
    show (ofAdd (z.toAdd.1, (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2])) : NFrameModel h) = z
    conv_rhs => rw [← ofAdd_toAdd z]
    exact congrArg ofAdd
      (Prod.ext rfl (Prod.ext hb.symm (Prod.ext hc.symm (Prod.ext hd.symm hf.symm))))
  right_inv a := rfl

/-- The `q`-invariant of a group carrying a general-`h` `N`-frame model is `2` (the
`demushkinQ_of_frame` of `Cores.lean`, extended to every handle count). -/
private theorem nDemushkinQ_of_frame {h : ℕ} {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G]
    (e : ContinuousMulEquiv (topAbelianization G) (NFrameModel h)) : demushkinQ G = 2 := by
  rw [demushkinQ]
  have eq : {x : topAbelianization G // IsOfFinOrder x}
      ≃ {z : NFrameModel h // IsOfFinOrder z} :=
    Equiv.subtypeEquiv e.toMulEquiv.toEquiv (fun x => by
      show IsOfFinOrder x ↔ IsOfFinOrder (e.toMulEquiv x)
      rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
      exact ⟨fun ⟨n, hn, hp⟩ => ⟨n, hn, by rw [← map_pow, hp, map_one]⟩,
        fun ⟨n, hn, hp⟩ => ⟨n, hn, e.toMulEquiv.injective (by rw [map_pow, map_one]; exact hp)⟩⟩)
  rw [Nat.card_congr eq, Nat.card_congr (nTorsionEquivZMod2 h), Nat.card_zmod]

/-- **`demushkinQ D_N = 2` at every handle count** (memo §3.1/§4.2): the torsion is untouched
by the handles, so the `q`-invariant of the `N`-family is `2` uniformly in `(α, h)` — the
general-`h` extension of MC2's `demushkinQ_DN`. -/
theorem demushkinQ_DN_nFrame {α h : ℕ} (F : NFrame α h) : demushkinQ (DN α h : Type) = 2 :=
  nDemushkinQ_of_frame F.e

end FrameTorsion

/-! ## §2 The exact S1 core transvections  (memo §3.4 families N1/N3, §5.1; deliverable 3)

HM1 proves all three `N`-side core-word transvections exact (`nWord_tau_b`, `nWord_tau_c`,
`nWord_tau_d` — memo: "`N` is the easy case"), but HM4 promotes only `τ_c(k)` (= family N2,
`x₂ ↦ σ^k·x₂`, `tauDMark`/`dnTauDEquiv`) to the presented core.  Here the other two rows get
the same treatment:

* **family N1** `x₁ ↦ x₀^k·x₁` (`nWord_tau_b`) — the τ-shift of the stabilizer, `nTauBMark`;
* **family N3** `σ ↦ x₂^k·σ` (`nWord_tau_c`) — the lower elementary of the `(σ, x₂)`-block,
  `nTauCMark`, the row *unavailable* on the `M`-side (memo §6.4's residue).

With HM4's `dnTauDEquiv` these generate the full elementary block `SL₂(ℤ₂)` on the
`(σ̄, x̄₂)`-plane (elementary matrices generate `SL₂` over a local ring — HM3's
`mem_closure_planeElemSet_of_det_eq_one` is the frame-side statement).  All axiom-free. -/

section CoreTransvections

variable {G : Type*} [Group G] {h : ℕ}

/-- The core letter `0` is not the letter `1`. -/
theorem nCoreZero_ne_one : (0 : Fin (coreRank h)) ≠ 1 :=
  Fin.ne_of_val_ne (by rw [coreVal_zero, coreVal_one]; omega)

/-- The core letter `2` is not the letter `1`. -/
theorem nCoreTwo_ne_one : (2 : Fin (coreRank h)) ≠ 1 :=
  Fin.ne_of_val_ne (by rw [coreVal_two, coreVal_one]; omega)

/-- The core letter `3` is not the letter `1`. -/
theorem nCoreThree_ne_one : (3 : Fin (coreRank h)) ≠ 1 :=
  Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_one]; omega)

/-- The core letter `0` is not the letter `2`. -/
theorem nCoreZero_ne_two : (0 : Fin (coreRank h)) ≠ 2 :=
  Fin.ne_of_val_ne (by rw [coreVal_zero, coreVal_two]; omega)

/-- The core letter `1` is not the letter `2`. -/
theorem nCoreOne_ne_two : (1 : Fin (coreRank h)) ≠ 2 :=
  Fin.ne_of_val_ne (by rw [coreVal_one, coreVal_two]; omega)

/-- The core letter `3` is not the letter `2`. -/
theorem nCoreThree_ne_two : (3 : Fin (coreRank h)) ≠ 2 :=
  Fin.ne_of_val_ne (by rw [coreVal_three, coreVal_two]; omega)

/-- Handle letters are not the letter `1`. -/
theorem nHandleIdxU_ne_one (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 1 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_one]; omega)

theorem nHandleIdxV_ne_one (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 1 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_one]; omega)

/-- Handle letters are not the letter `2`. -/
theorem nHandleIdxU_ne_two (j : Fin h) : (handleIdxU j : Fin (coreRank h)) ≠ 2 :=
  handleIdxU_ne_of_val_lt j (by rw [coreVal_two]; omega)

theorem nHandleIdxV_ne_two (j : Fin h) : (handleIdxV j : Fin (coreRank h)) ≠ 2 :=
  handleIdxV_ne_of_val_lt j (by rw [coreVal_two]; omega)

/-- **Structure of a one-slot update of the `N_α` relator at the letter `1`** — the
`nRelWord_update_three` of HM4, moved to the `x₁`-slot. -/
theorem nRelWord_update_one (α : ℕ) (m : Fin (coreRank h) → G) (w : G) :
    nRelWord α (Function.update m 1 w)
      = nWord α (m 0) w (m 2) (m 3)
        * handleWord (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) := by
  have hU : (fun i => Function.update m 1 w (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i => Function.update_of_ne (nHandleIdxU_ne_one i) _ _
  have hV : (fun i => Function.update m 1 w (handleIdxV i)) = fun i => m (handleIdxV i) :=
    funext fun i => Function.update_of_ne (nHandleIdxV_ne_one i) _ _
  rw [nRelWord, Function.update_self, hU, hV,
    Function.update_of_ne nCoreZero_ne_one, Function.update_of_ne nCoreTwo_ne_one,
    Function.update_of_ne nCoreThree_ne_one]

/-- **Structure of a one-slot update of the `N_α` relator at the letter `2`**. -/
theorem nRelWord_update_two (α : ℕ) (m : Fin (coreRank h) → G) (w : G) :
    nRelWord α (Function.update m 2 w)
      = nWord α (m 0) (m 1) w (m 3)
        * handleWord (fun i => m (handleIdxU i)) (fun i => m (handleIdxV i)) := by
  have hU : (fun i => Function.update m 2 w (handleIdxU i)) = fun i => m (handleIdxU i) :=
    funext fun i => Function.update_of_ne (nHandleIdxU_ne_two i) _ _
  have hV : (fun i => Function.update m 2 w (handleIdxV i)) = fun i => m (handleIdxV i) :=
    funext fun i => Function.update_of_ne (nHandleIdxV_ne_two i) _ _
  rw [nRelWord, Function.update_self, hU, hV,
    Function.update_of_ne nCoreZero_ne_two, Function.update_of_ne nCoreOne_ne_two,
    Function.update_of_ne nCoreThree_ne_two]

end CoreTransvections

section NTauMark

variable {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] {h : ℕ}

/-- **Family N1 as a substitution on markings** (memo §3.4): `x₁ ↦ x₀^k·x₁`, exact for every
2-adic `k` by HM1's `nWord_tau_b`.  Frame action: the pure `τ`-shift `x̄₁ ↦ k·t + x̄₁`
(`t = x̄₀` is 2-torsion, so only `k mod 2` survives); the ν-frame action is trivial
(`ν(x̄₀) = 0` for every `ℤ₂`-character — `nChar_dnX0` below). -/
noncomputable def nTauBMark (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  Function.update m 1 (zpowZtwo hP (m 0) k * m 1)

/-- **Family N3 as a substitution on markings** (memo §3.4): `σ ↦ x₂^k·σ`, exact by HM1's
`nWord_tau_c` — the lower elementary transvection `σ̄ ↦ σ̄ + k·x̄₂` of the `(σ, x₂)`-block. -/
noncomputable def nTauCMark (hP : IsProP 2 P) (k : ℤ_[2]) (m : Fin (coreRank h) → P) :
    Fin (coreRank h) → P :=
  Function.update m 2 (zpowZtwo hP (m 3) k * m 2)

variable (hP : IsProP 2 P) (k l : ℤ_[2]) (m : Fin (coreRank h) → P)

@[simp] theorem nTauBMark_one : nTauBMark hP k m 1 = zpowZtwo hP (m 0) k * m 1 :=
  Function.update_self _ _ _

theorem nTauBMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ 1) : nTauBMark hP k m i = m i :=
  Function.update_of_ne hi _ _

@[simp] theorem nTauBMark_zero_slot : nTauBMark hP k m 0 = m 0 :=
  nTauBMark_of_ne _ _ _ nCoreZero_ne_one

@[simp] theorem nTauCMark_two : nTauCMark hP k m 2 = zpowZtwo hP (m 3) k * m 2 :=
  Function.update_self _ _ _

theorem nTauCMark_of_ne {i : Fin (coreRank h)} (hi : i ≠ 2) : nTauCMark hP k m i = m i :=
  Function.update_of_ne hi _ _

@[simp] theorem nTauCMark_three_slot : nTauCMark hP k m 3 = m 3 :=
  nTauCMark_of_ne _ _ _ nCoreThree_ne_two

/-- N1 is a one-parameter group of substitutions. -/
theorem nTauBMark_nTauBMark : nTauBMark hP k (nTauBMark hP l m) = nTauBMark hP (k + l) m := by
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [nTauBMark_one, nTauBMark_zero_slot, nTauBMark_one, nTauBMark_one,
      zpowZtwo_add, mul_assoc]
  rw [nTauBMark_of_ne _ _ _ hi, nTauBMark_of_ne _ _ _ hi, nTauBMark_of_ne _ _ _ hi]

theorem nTauCMark_nTauCMark : nTauCMark hP k (nTauCMark hP l m) = nTauCMark hP (k + l) m := by
  funext i
  by_cases hi : i = 2
  · subst hi
    rw [nTauCMark_two, nTauCMark_three_slot, nTauCMark_two, nTauCMark_two,
      zpowZtwo_add, mul_assoc]
  rw [nTauCMark_of_ne _ _ _ hi, nTauCMark_of_ne _ _ _ hi, nTauCMark_of_ne _ _ _ hi]

@[simp] theorem nTauBMark_zero : nTauBMark hP 0 m = m := by
  funext i
  by_cases hi : i = 1
  · subst hi
    rw [nTauBMark_one, zpowZtwo_zero_exp, one_mul]
  rw [nTauBMark_of_ne _ _ _ hi]

@[simp] theorem nTauCMark_zero : nTauCMark hP 0 m = m := by
  funext i
  by_cases hi : i = 2
  · subst hi
    rw [nTauCMark_two, zpowZtwo_zero_exp, one_mul]
  rw [nTauCMark_of_ne _ _ _ hi]

/-- The N1 substitution fixes the `N_α` relator (HM1's `nWord_tau_b` at the full relator). -/
theorem nRelWord_nTauBMark (α : ℕ) : nRelWord α (nTauBMark hP k m) = nRelWord α m := by
  rw [nTauBMark, nRelWord_update_one, nWord_tau_b hP, nRelWord]

/-- The N3 substitution fixes the `N_α` relator (HM1's `nWord_tau_c` at the full relator). -/
theorem nRelWord_nTauCMark (α : ℕ) : nRelWord α (nTauCMark hP k m) = nRelWord α m := by
  rw [nTauCMark, nRelWord_update_two, nWord_tau_c hP, nRelWord]

end NTauMark

section NTauMarkNaturality

variable {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [T2Space P] [TotallyDisconnectedSpace P] [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q] {h : ℕ}

variable (hP : IsProP 2 P) (hQ : IsProP 2 Q) (f : ContinuousMonoidHom P Q)

theorem map_nTauBMark (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (nTauBMark hP k m i) = nTauBMark hQ k (fun i => f (m i)) i := by
  by_cases hi : i = 1
  · subst hi
    rw [nTauBMark_one, nTauBMark_one, map_mul, map_zpowZtwo hP hQ]
  rw [nTauBMark_of_ne _ _ _ hi, nTauBMark_of_ne _ _ _ hi]

theorem map_nTauCMark (k : ℤ_[2]) (m : Fin (coreRank h) → P) (i : Fin (coreRank h)) :
    f (nTauCMark hP k m i) = nTauCMark hQ k (fun i => f (m i)) i := by
  by_cases hi : i = 2
  · subst hi
    rw [nTauCMark_two, nTauCMark_two, map_mul, map_zpowZtwo hP hQ]
  rw [nTauCMark_of_ne _ _ _ hi, nTauCMark_of_ne _ _ _ hi]

end NTauMarkNaturality

/-! ### The two families on the presented core `D_N` -/

section NTauEquiv

variable (α h : ℕ)

/-- Family N1 (`x₁ ↦ x₀^k·x₁`) as a continuous endomorphism of `D_N`. -/
noncomputable def dnTauBHom (k : ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (nTauBMark (isProP_DN α h) k (dnGen α h))
    (by rw [nRelWord_nTauBMark]; exact dn_relation α h)

/-- Family N3 (`σ ↦ x₂^k·σ`) as a continuous endomorphism of `D_N`. -/
noncomputable def dnTauCHom (k : ℤ_[2]) :
    ContinuousMonoidHom (DN α h : Type) (DN α h : Type) :=
  nLiftHom α h (isProP_DN α h) (nTauCMark (isProP_DN α h) k (dnGen α h))
    (by rw [nRelWord_nTauCMark]; exact dn_relation α h)

@[simp] theorem dnTauBHom_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauBHom α h k (dnGen α h i) = nTauBMark (isProP_DN α h) k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

@[simp] theorem dnTauCHom_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauCHom α h k (dnGen α h i) = nTauCMark (isProP_DN α h) k (dnGen α h) i :=
  nLiftHom_gen _ _ _ _ _ _

/-- **Family N1 as a continuous automorphism of `D_N`**, for every `k ∈ ℤ₂` — via HM4's
one-parameter assembly `dnParamEquiv` (the inverse is the member at `−k`). -/
noncomputable def dnTauBEquiv (k : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  dnParamEquiv α h (dnTauBHom α h) (nTauBMark (isProP_DN α h)) (dnTauBHom_gen α h)
    (fun k f m i => map_nTauBMark (isProP_DN α h) (isProP_DN α h) f k m i)
    (fun k l m => nTauBMark_nTauBMark _ k l m) (fun m => nTauBMark_zero _ m) k

/-- **Family N3 as a continuous automorphism of `D_N`**. -/
noncomputable def dnTauCEquiv (k : ℤ_[2]) :
    ContinuousMulEquiv (DN α h : Type) (DN α h : Type) :=
  dnParamEquiv α h (dnTauCHom α h) (nTauCMark (isProP_DN α h)) (dnTauCHom_gen α h)
    (fun k f m i => map_nTauCMark (isProP_DN α h) (isProP_DN α h) f k m i)
    (fun k l m => nTauCMark_nTauCMark _ k l m) (fun m => nTauCMark_zero _ m) k

@[simp] theorem dnTauBEquiv_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauBEquiv α h k (dnGen α h i) = nTauBMark (isProP_DN α h) k (dnGen α h) i :=
  dnTauBHom_gen α h k i

@[simp] theorem dnTauCEquiv_gen (k : ℤ_[2]) (i : Fin (coreRank h)) :
    dnTauCEquiv α h k (dnGen α h i) = nTauCMark (isProP_DN α h) k (dnGen α h) i :=
  dnTauCHom_gen α h k i

/-- The moved N1 row: `x₁ ↦ x₀^k·x₁`. -/
theorem dnTauBEquiv_dnX1 (k : ℤ_[2]) :
    dnTauBEquiv α h k (dnX1 α h) = zpowZtwo (isProP_DN α h) (dnX0 α h) k * dnX1 α h := by
  rw [dnX1, dnTauBEquiv_gen, nTauBMark_one]
  rfl

/-- The moved N3 row: `σ ↦ x₂^k·σ`. -/
theorem dnTauCEquiv_dnSigma (k : ℤ_[2]) :
    dnTauCEquiv α h k (dnSigma α h) = zpowZtwo (isProP_DN α h) (dnX2 α h) k * dnSigma α h := by
  rw [dnSigma, dnTauCEquiv_gen, nTauCMark_two]
  rfl

/-- N1 fixes every other marked generator. -/
theorem dnTauBEquiv_of_ne (k : ℤ_[2]) {i : Fin (coreRank h)} (hi : i ≠ 1) :
    dnTauBEquiv α h k (dnGen α h i) = dnGen α h i := by
  rw [dnTauBEquiv_gen, nTauBMark_of_ne _ _ _ hi]

/-- N3 fixes every other marked generator. -/
theorem dnTauCEquiv_of_ne (k : ℤ_[2]) {i : Fin (coreRank h)} (hi : i ≠ 2) :
    dnTauCEquiv α h k (dnGen α h i) = dnGen α h i := by
  rw [dnTauCEquiv_gen, nTauCMark_of_ne _ _ _ hi]

/-- **N1 preserves the canonical orientation**: `χ_N(x₀) = 1`, so the moved row is
χ-invisible. -/
theorem chiN_dnTauBEquiv (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnTauBEquiv α h k x) = chiN α h x := by
  refine dn_char_fixed (chiN α h) _ (fun i => ?_) x
  by_cases hi : i = 1
  · subst hi
    show chiN α h (dnTauBEquiv α h k (dnX1 α h)) = chiN α h (dnX1 α h)
    rw [dnTauBEquiv_dnX1, map_mul,
      map_zpowZtwo (isProP_DN α h) isProP_two_unitsPadicInt (chiN α h)]
    show zpowZtwo isProP_two_unitsPadicInt (chiN α h (dnX0 α h)) k * _ = _
    rw [chiN_dnX0, zpowZtwo_one_base, one_mul]
  · rw [dnTauBEquiv_of_ne α h k hi]

/-- **N3 preserves the canonical orientation**: `χ_N(x₂) = 1`. -/
theorem chiN_dnTauCEquiv (k : ℤ_[2]) (x : (DN α h : Type)) :
    chiN α h (dnTauCEquiv α h k x) = chiN α h x := by
  refine dn_char_fixed (chiN α h) _ (fun i => ?_) x
  by_cases hi : i = 2
  · subst hi
    show chiN α h (dnTauCEquiv α h k (dnSigma α h)) = chiN α h (dnSigma α h)
    rw [dnTauCEquiv_dnSigma, map_mul,
      map_zpowZtwo (isProP_DN α h) isProP_two_unitsPadicInt (chiN α h)]
    show zpowZtwo isProP_two_unitsPadicInt (chiN α h (dnX2 α h)) k * _ = _
    rw [chiN_dnX2, zpowZtwo_one_base, one_mul]
  · rw [dnTauCEquiv_of_ne α h k hi]

/-- **Every `ℤ₂`-character of `D_N` kills `x₀`** (memo §3.6's `ν(t) = 0` consistency, as a
theorem about *all* characters): the abelianized relation `x̄₀^{2+2^α} = 1` lands in the
torsion-free `ℤ₂`, so the `x₀`-value dies.  This is why family N1 is ν-frame-invisible and why
the `x₀`-slot never appears in the marked correction. -/
theorem nChar_dnX0 (f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2])) :
    f (dnX0 α h) = 1 := by
  have hrel : nRelWord α (fun i => f (dnGen α h i)) = 1 := by
    rw [← map_nRelWord, dn_relation, map_one]
  rw [nRelWord_comm] at hrel
  have htor : (2 + 2 ^ α) • toAdd (f (dnX0 α h)) = 0 := by
    have := congrArg toAdd hrel
    rwa [toAdd_pow, toAdd_one] at this
  rw [nsmul_eq_mul] at htor
  rcases mul_eq_zero.mp htor with hc | hc
  · exfalso
    have h2 : ((2 + 2 ^ α : ℕ) : ℤ_[2]) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.add_pos_left two_pos _).ne'
    exact h2 hc
  · rw [← ofAdd_toAdd (f (dnX0 α h)), hc, ofAdd_zero]

end NTauEquiv

/-! ## §3 Row extraction: the infinite-order pinning of the `x̄₁`-row  (memo §3.3)

The χ-condition pins the `x̄₁`-row *integrally* because `v = −(1+2^α)⁻¹` has infinite order —
the memo's decisive simplification versus `M` (where `−1` gives only a mod-2 pin).  The engine
is the `ℤ₂`-powering injectivity of `v`, proved through the exact level of `v² = (1+2^α)⁻²`
(depth `α+1`), by the same unit-coefficient factorization as `ZtwoPowering`'s
`zpowZtwo_injective_of_exact_level` — which is hard-coded to level 2 (`η − 1 = 4a`) and does
not apply to `v ≡ 3 (mod 4)`; the level-general clone below is the dedup restatement. -/

section UnitInjectivity

/-- **Exact-level iteration at an arbitrary level `s ≥ 2`** (dedup: level-2 original
`exists_unit_pow_two_pow_sub_one`, `GQ2/ZtwoPowering.lean:520`): if `η − 1 = 2^s·b` with
`b ∈ ℤ₂ˣ`, then `η^{2^k} − 1 = 2^{k+s}·(unit)` — one exact level per squaring. -/
theorem nExists_unit_pow_two_pow_sub_one (η b : ℤ_[2]ˣ) (s : ℕ) (hs : 2 ≤ s)
    (hη : ((η : ℤ_[2])) - 1 = 2 ^ s * b) (k : ℕ) :
    ∃ c : ℤ_[2]ˣ, ((η ^ 2 ^ k : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (k + s) * c := by
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 2 := ⟨s - 2, by omega⟩
  induction k with
  | zero =>
    exact ⟨b, by rw [pow_zero, pow_one, hη, zero_add]⟩
  | succ j ih =>
    obtain ⟨c, hc⟩ := ih
    have hval : ((η ^ 2 ^ (j + 1) : ℤ_[2]ˣ) : ℤ_[2]) = ((η ^ 2 ^ j : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 := by
      rw [← Units.val_pow_eq_pow_val, ← pow_mul, pow_succ]
    have hu : IsUnit ((c : ℤ_[2]) * (1 + 2 * ((2 : ℤ_[2]) ^ (j + t) * c))) :=
      c.isUnit.mul (isUnit_one_add_two_mul _)
    refine ⟨hu.unit, ?_⟩
    rw [hval, sub_eq_iff_eq_add.mp hc, IsUnit.unit_spec]
    ring

/-- `v² = (1+2^α)⁻²` in `ℤ₂ˣ` (the sign squares away). -/
theorem nUnit_sq (α : ℕ) : (nUnit α) ^ 2 = ((onePlusTwoPow α) ^ 2)⁻¹ := by
  rw [nUnit, ← inv_pow, neg_sq]

/-- **The exact level of `v²` is `α + 1`**: `v² − 1 = 2^{α+1}·(unit)` for `α ≥ 2`
(`(1+2^α)² = 1 + 2^{α+1}(1 + 2^{α−1})` and `1 + 2^{α−1}` is odd). -/
theorem nUnit_sq_sub_one {α : ℕ} (hα : 2 ≤ α) :
    ∃ b : ℤ_[2]ˣ, ((nUnit α ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1 = 2 ^ (α + 1) * b := by
  obtain ⟨a, rfl⟩ : ∃ a, α = a + 2 := ⟨α - 2, by omega⟩
  have hodd : IsUnit (1 + 2 * (2 : ℤ_[2]) ^ a) := isUnit_one_add_two_mul _
  have hw : ((onePlusTwoPow (a + 2) : ℤ_[2]ˣ) : ℤ_[2]) = 1 + 2 ^ (a + 2) :=
    onePlusTwoPow_val (by omega)
  refine ⟨-(((onePlusTwoPow (a + 2)) ^ 2)⁻¹ * hodd.unit), ?_⟩
  have hinv : ((nUnit (a + 2) ^ 2 : ℤ_[2]ˣ) : ℤ_[2])
      * (((onePlusTwoPow (a + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) = 1 := by
    rw [nUnit_sq]
    push_cast
    rw [← mul_pow, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_pow]
  have hsq : (((onePlusTwoPow (a + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2)
      = 1 + 2 ^ (a + 3) * (1 + 2 * 2 ^ a) := by
    rw [hw]
    ring
  -- η² − 1 = η²·(1 − w²) with w² = 1 + 2^{α+1}·odd
  have hkey : ((nUnit (a + 2) ^ 2 : ℤ_[2]ˣ) : ℤ_[2]) - 1
      = ((nUnit (a + 2) ^ 2 : ℤ_[2]ˣ) : ℤ_[2])
        * (1 - (((onePlusTwoPow (a + 2) : ℤ_[2]ˣ) : ℤ_[2]) ^ 2)) := by
    rw [mul_sub, mul_one, hinv]
  rw [hkey, hsq, nUnit_sq]
  push_cast
  rw [IsUnit.unit_spec]
  ring

/-- **`ℤ₂`-powering by the `N`-orientation unit is injective** (memo §3.3: "`v` has infinite
order, so the `x₁`-row is pinned *integrally*").  A nonzero kernel exponent factors as
`w·2^m` (`w ∈ ℤ₂ˣ`), forcing `v^{2^m} = 1`; at `m = 0` this contradicts `v(1+2^α) = −1`, and
at `m ≥ 1` it contradicts the exact level `α+1` of `v²`. -/
theorem nUnit_zpowZtwo_injective {α : ℕ} (hα : 2 ≤ α) :
    Function.Injective (zpowZtwo isProP_two_unitsPadicInt (nUnit α)) := by
  intro c₁ c₂ hc
  by_contra hne
  have hc0 : c₁ - c₂ ≠ 0 := sub_ne_zero.mpr hne
  have hker : zpowZtwo isProP_two_unitsPadicInt (nUnit α) (c₁ - c₂) = 1 := by
    have hadd := zpowZtwo_add isProP_two_unitsPadicInt (nUnit α) (c₁ - c₂) c₂
    rw [sub_add_cancel, hc] at hadd
    exact right_eq_mul.mp hadd
  set m := (c₁ - c₂).valuation with hm
  set w := PadicInt.unitCoeff hc0 with hwdef
  have hspec : c₁ - c₂ = (w : ℤ_[2]) * 2 ^ m := PadicInt.unitCoeff_spec hc0
  have hfactor : zpowZtwo isProP_two_unitsPadicInt ((nUnit α) ^ 2 ^ m) ((w : ℤ_[2]))
      = zpowZtwo isProP_two_unitsPadicInt (nUnit α) (c₁ - c₂) := by
    rw [← zpowZtwo_natCast isProP_two_unitsPadicInt (nUnit α) (2 ^ m), zpowZtwo_zpowZtwo]
    congr 1
    rw [hspec]
    push_cast
    ring
  have hbase : ((nUnit α) ^ 2 ^ m : ℤ_[2]ˣ) = 1 := by
    refine (zpowZtwo_bijective isProP_two_unitsPadicInt w).injective ?_
    show zpowZtwo _ ((nUnit α) ^ 2 ^ m) ((w : ℤ_[2])) = zpowZtwo _ 1 ((w : ℤ_[2]))
    rw [hfactor, hker, zpowZtwo_one_base]
  rcases Nat.eq_zero_or_pos m with hm0 | hmpos
  · -- `m = 0`: `v = 1`, contradicting `v·(1+2^α) = −1`
    rw [hm0, pow_zero, pow_one] at hbase
    have hval := nUnit_mul (α := α) (by omega)
    rw [hbase, Units.val_one, one_mul] at hval
    have h20 : (2 + 2 ^ α : ℤ_[2]) = 0 := by linear_combination hval
    have hnat : ((2 + 2 ^ α : ℕ) : ℤ_[2]) = 0 := by push_cast; linear_combination h20
    exact Nat.cast_ne_zero.mpr (Nat.add_pos_left two_pos _).ne' hnat
  · -- `m ≥ 1`: `(v²)^{2^{m−1}} = 1` against the exact level `α+1`
    obtain ⟨j, hj⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
    rw [hj] at hbase
    have hsq : ((nUnit α ^ 2) ^ 2 ^ j : ℤ_[2]ˣ) = 1 := by
      rw [← pow_mul, mul_comm 2 (2 ^ j), ← pow_succ]
      exact hbase
    obtain ⟨b, hb⟩ := nUnit_sq_sub_one hα
    obtain ⟨c, hcl⟩ := nExists_unit_pow_two_pow_sub_one (nUnit α ^ 2) b (α + 1)
      (by omega) hb j
    rw [hsq] at hcl
    have hzero : (2 : ℤ_[2]) ^ (j + (α + 1)) * (c : ℤ_[2]) = 0 := by
      rw [← hcl]
      simp
    exact mul_ne_zero (pow_ne_zero _ (by norm_num : (2 : ℤ_[2]) ≠ 0)) c.ne_zero hzero

end UnitInjectivity
