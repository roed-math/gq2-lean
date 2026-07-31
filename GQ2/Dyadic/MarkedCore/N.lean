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

/-! ## §4 The Smith–Witt stabilizer of the rank-four `N`-frame  (memo §3.2(iii), §3.3)

The classification is **unconditional `ℤ₂`/`𝔽₂` linear algebra**, uniform in `α ≥ 2` and completely
independent of the lifting question — memo §10's "the stabilizer classification … can and should
land first, unconditionally".  Coordinates are the frame's: `(t, x̄₁, σ̄, x̄₂)` with `t = x̄₀` the
2-torsion coordinate (memo §3.1).

Three clauses define the stabilizer (memo §3.3):

* **relation vector** `ρ_N = 2t`, i.e. `φ(t) = t`.  For an *automorphism* this is not a hypothesis
  at all — `nFrameModel_map_t` proves it, `t` being the unique element of order 2 — so it is built
  into the `t`-column of `NRows.col`;
* **orientation datum** `χ̄∘φ = χ̄`, where `χ̄(v) = v^{v_{x̄₁}}` with `v = nUnit α` of **infinite**
  order (§3): the `x̄₁`-row is therefore pinned *integrally*, `IsNStab.x1_coord`;
* **mod-2 cup Gram** `M̄·G_N·M̄ᵀ = G_N`, entrywise (memo §2.3's convention, dualized to `H¹`).

`nStabilizer_classification` shows the three clauses hold for exactly the parameter tuples
`(τ, p, q, τ_σ, τ_{x₂}, g)` of memo §3.3, and for a *unique* one; `nStabParam_tauSolve_unique`
then reads off the closed form `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` — under the two mod-2 couplings the
pair `(τ_σ, τ_{x₂})` is determined by `(p, q, g)`, so the `(σ, x₂)`-plane behaves exactly like a
handle with the torsion coordinate riding along. -/

section Stabilizer

/-- **Mod-2 reduction** `ℤ₂ ↠ 𝔽₂` — the coefficient reduction taking the frame to the `𝔽₂`-space
that carries the cup form (memo §3.2(iii)). -/
noncomputable def nRed : ℤ_[2] →+* ZMod 2 := PadicInt.toZMod

/-- `ℤ₂` is local with residue field `𝔽₂`: a 2-adic integer is a unit exactly when its mod-2
reduction is `1`.  This is what turns the cup-form entry `⟨σ*, x₂*⟩ = 1` into `g ∈ GL₂(ℤ₂)`. -/
theorem nIsUnit_iff_nRed {x : ℤ_[2]} : IsUnit x ↔ nRed x = 1 := by
  have hker : nRed x = 0 ↔ ¬ IsUnit x := by
    rw [nRed, ← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal,
      mem_nonunits_iff]
  have hzo : ∀ a : ZMod 2, a = 1 ↔ ¬ a = 0 := by decide
  rw [hzo, hker, not_not]

/-- The coordinate vector of the rank-four `N`-frame: `(t, x̄₁, σ̄, x̄₂)`, the additive model of
`NDecomposition` (memo §3.1). -/
abbrev NVec : Type := ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]

/-- The mod-2 reduction of a frame coordinate vector, as an `𝔽₂`-vector on the four slots. -/
noncomputable def nMod2 (v : NVec) : Fin 4 → ZMod 2 :=
  ![v.1, nRed v.2.1, nRed v.2.2.1, nRed v.2.2.2]

@[simp] theorem nMod2_zero (v : NVec) : nMod2 v 0 = v.1 := rfl
@[simp] theorem nMod2_one (v : NVec) : nMod2 v 1 = nRed v.2.1 := rfl
@[simp] theorem nMod2_two (v : NVec) : nMod2 v 2 = nRed v.2.2.1 := rfl
@[simp] theorem nMod2_three (v : NVec) : nMod2 v 3 = nRed v.2.2.2 := rfl

/-- **A frame endomorphism of the rank-four `N`-model in coordinates**: the images of the three
non-torsion basis vectors `x̄₁, σ̄, x̄₂`.  The image of `t` is *not* data — it is `t`
(`nFrameModel_map_t`). -/
@[ext]
structure NRows where
  /-- The image of `x̄₁`. -/
  x1 : NVec
  /-- The image of `σ̄`. -/
  sigma : NVec
  /-- The image of `x̄₂`. -/
  x2 : NVec

/-- The four columns of the frame endomorphism — the images of `t, x̄₁, σ̄, x̄₂` in that order. -/
noncomputable def NRows.col (R : NRows) : Fin 4 → NVec := ![(1, 0, 0, 0), R.x1, R.sigma, R.x2]

@[simp] theorem NRows.col_zero (R : NRows) : R.col 0 = ((1 : ZMod 2), 0, 0, 0) := rfl
@[simp] theorem NRows.col_one (R : NRows) : R.col 1 = R.x1 := rfl
@[simp] theorem NRows.col_two (R : NRows) : R.col 2 = R.sigma := rfl
@[simp] theorem NRows.col_three (R : NRows) : R.col 3 = R.x2 := rfl

/-- **The mod-2 matrix `M̄` of a frame endomorphism**: `R.mat i j` is the `i`-th coordinate of the
image of the `j`-th basis vector, so `R.mat i` is the `i`-th **row**. -/
noncomputable def NRows.mat (R : NRows) (i j : Fin 4) : ZMod 2 := nMod2 (R.col j) i

/-- **The mod-2 cup Gram of the `N`-core** (memo §3.2(iii)), in the dual basis of `(x₀,x₁,σ,x₂)`:
`x₀^{2+2^α}` has exponent `≡ 2 (mod 4)` so the diagonal Bockstein entry is `1`, and `[x₀,x₁]`,
`[σ,x₂]` contribute the two hyperbolic pairs.  α-independent for `α ≥ 2`. -/
def nGram : Fin 4 → Fin 4 → ZMod 2 :=
  ![![1, 1, 0, 0], ![1, 0, 0, 0], ![0, 0, 0, 1], ![0, 0, 1, 0]]

/-- The mod-2 cup pairing on `H¹(D_N; 𝔽₂)` in the dual basis, in closed form (the Gram matrix it
belongs to is `nGram` — `nCupForm_eq_gram`). -/
def nCupForm (u w : Fin 4 → ZMod 2) : ZMod 2 :=
  u 0 * w 0 + u 0 * w 1 + u 1 * w 0 + u 2 * w 3 + u 3 * w 2

/-- `nCupForm` **is** the bilinear form of the Gram matrix `nGram` — the closed form above is only
a computational convenience (it keeps the `𝔽₂` decision procedure of `nCup_iff_mod2` cheap). -/
theorem nCupForm_eq_gram (u w : Fin 4 → ZMod 2) :
    nCupForm u w = ∑ i, ∑ j, u i * nGram i j * w j := by
  simp [nCupForm, Fin.sum_univ_four, nGram]

/-- **The cup-isometry clause**: `M̄·G_N·M̄ᵀ = G_N`, entrywise (memo §2.3's convention, dualized to
`H¹` — the pullback of a covector along `φ̄` is `M̄ᵀ`, so the isometry condition is on the rows of
`M̄`). -/
def NRows.IsCupIsometry (R : NRows) : Prop := ∀ i j, nCupForm (R.mat i) (R.mat j) = nGram i j

/-- The canonical orientation read on the frame (memo §3.2(i)): `χ̄(v) = v^{v_{x̄₁}}` with
`v = nUnit α = −(1+2^α)⁻¹`, since `χ_N` is `1` on `x₀`, `σ` and `x₂`. -/
noncomputable def nChiVec (α : ℕ) (v : NVec) : ℤ_[2]ˣ :=
  zpowZtwo isProP_two_unitsPadicInt (nUnit α) v.2.1

/-- **The Smith–Witt stabilizer of the marked invariant triple** (memo §3.3), on the rows of a
rank-four `N`-frame endomorphism.  The relation-vector clause is the `t`-column of `NRows.col`
and is automatic for automorphisms (`nFrameModel_map_t`). -/
structure IsNStab (α : ℕ) (R : NRows) : Prop where
  /-- `χ̄(φ(x̄₁)) = χ̄(x̄₁) = v`. -/
  chi_x1 : nChiVec α R.x1 = nUnit α
  /-- `χ̄(φ(σ̄)) = χ̄(σ̄) = 1`. -/
  chi_sigma : nChiVec α R.sigma = 1
  /-- `χ̄(φ(x̄₂)) = χ̄(x̄₂) = 1`. -/
  chi_x2 : nChiVec α R.x2 = 1
  /-- `M̄·G_N·M̄ᵀ = G_N`. -/
  cup : R.IsCupIsometry

/-- **The `x̄₁`-row is pinned integrally** (memo §3.3, the decisive `N`-side simplification): the
χ-clause forces the three `x̄₁`-coordinates *exactly*, not merely mod 2, because
`v = −(1+2^α)⁻¹` has infinite order (`nUnit_zpowZtwo_injective`). -/
theorem IsNStab.x1_coord {α : ℕ} (hα : 2 ≤ α) {R : NRows} (hR : IsNStab α R) :
    R.x1.2.1 = 1 ∧ R.sigma.2.1 = 0 ∧ R.x2.2.1 = 0 := by
  refine ⟨nUnit_zpowZtwo_injective hα ?_, nUnit_zpowZtwo_injective hα ?_,
    nUnit_zpowZtwo_injective hα ?_⟩
  · rw [zpowZtwo_one_exp]; exact hR.chi_x1
  · rw [zpowZtwo_zero_exp]; exact hR.chi_sigma
  · rw [zpowZtwo_zero_exp]; exact hR.chi_x2

/-! ### The parameter tuple of memo §3.3 -/

/-- **The stabilizer parameter tuple** `(τ, p, q, τ_σ, τ_{x₂}, g)` of memo §3.3:

```
φ(t)   = t
φ(x̄₁) = τ·t + x̄₁ + p·σ̄ + q·x̄₂
φ(σ̄)  = τ_σ·t + g₁·σ̄ + h₁·x̄₂
φ(x̄₂) = τ_{x₂}·t + g₂·σ̄ + h₂·x̄₂
```

with `g = [[g₁, g₂], [h₁, h₂]]`. -/
@[ext]
structure NStabParam where
  /-- The `t`-shift of the `x̄₁`-row (family N1). -/
  tau : ZMod 2
  /-- The `σ̄`-component of `φ(x̄₁)` (family N5). -/
  p : ℤ_[2]
  /-- The `x̄₂`-component of `φ(x̄₁)` (family N6). -/
  q : ℤ_[2]
  /-- The `t`-component of `φ(σ̄)` — coupled to `(p, q, g)`. -/
  tauSigma : ZMod 2
  /-- The `t`-component of `φ(x̄₂)` — coupled to `(p, q, g)`. -/
  tauX2 : ZMod 2
  /-- The `(σ̄, x̄₂)`-block (families N2, N3, N4). -/
  g : Matrix (Fin 2) (Fin 2) ℤ_[2]

/-- The rows determined by a parameter tuple. -/
noncomputable def NStabParam.rows (P : NStabParam) : NRows where
  x1 := (P.tau, 1, P.p, P.q)
  sigma := (P.tauSigma, 0, P.g 0 0, P.g 1 0)
  x2 := (P.tauX2, 0, P.g 0 1, P.g 1 1)

/-- **Admissibility** (memo §3.3): the `(σ̄, x̄₂)`-block is invertible and the two mod-2 couplings
link `(p, q)` to the `t`-components `(τ_σ, τ_{x₂})`.  These are exactly the three non-vacuous
entries of `M̄·G_N·M̄ᵀ = G_N` (`nStabParam_rows_isCupIsometry`). -/
structure NStabParam.Admissible (P : NStabParam) : Prop where
  /-- `g ∈ GL₂(ℤ₂)` — the cup entry `⟨σ*, x₂*⟩ = 1`. -/
  det : IsUnit P.g.det
  /-- `p̄ = τ_{x₂}·ḡ₁ + τ_σ·ḡ₂` — the cup entry `⟨t*, σ*⟩ = 0`. -/
  couple_p : nRed P.p = P.tauX2 * nRed (P.g 0 0) + P.tauSigma * nRed (P.g 0 1)
  /-- `q̄ = τ_{x₂}·h̄₁ + τ_σ·h̄₂` — the cup entry `⟨t*, x₂*⟩ = 0`. -/
  couple_q : nRed P.q = P.tauX2 * nRed (P.g 1 0) + P.tauSigma * nRed (P.g 1 1)

@[simp] theorem NStabParam.rows_x1 (P : NStabParam) : P.rows.x1 = (P.tau, 1, P.p, P.q) := rfl
@[simp] theorem NStabParam.rows_sigma (P : NStabParam) :
    P.rows.sigma = (P.tauSigma, 0, P.g 0 0, P.g 1 0) := rfl
@[simp] theorem NStabParam.rows_x2 (P : NStabParam) :
    P.rows.x2 = (P.tauX2, 0, P.g 0 1, P.g 1 1) := rfl

/-- `g ∈ GL₂(ℤ₂)`, read on the residue field: `ℤ₂` is local, so `det g` is a unit exactly when
`det ḡ = ḡ₁h̄₂ + ḡ₂h̄₁ = 1` in `𝔽₂` (signs are invisible in characteristic 2). -/
theorem nIsUnit_det_iff (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) :
    IsUnit g.det ↔ nRed (g 0 0) * nRed (g 1 1) + nRed (g 0 1) * nRed (g 1 0) = 1 := by
  rw [nIsUnit_iff_nRed, Matrix.det_fin_two, map_sub, map_mul, map_mul, CharTwo.sub_eq_add]

/-! ### The `𝔽₂` decision procedure

The whole Witt half of memo §3.3 is a statement about **nine** `𝔽₂`-parameters, hence a finite
check: `nCup_iff_mod2` settles all sixteen entries of `M̄·G_N·M̄ᵀ = G_N` at once, by kernel
evaluation over the `2⁹` assignments.  Everything `ℤ₂`-valued (the integral `x̄₁`-pin, the unit
`det g`) is handled separately, outside the decidable core. -/

/-- The mod-2 matrix `M̄` of memo §3.3 in terms of its nine free `𝔽₂` entries — rows indexed by
`(t, x̄₁, σ̄, x̄₂)`, and the `t`- and `x̄₁`-rows already rigid. -/
def nMatOf (τ τσ τx p q g₁ g₂ h₁ h₂ : ZMod 2) : Fin 4 → Fin 4 → ZMod 2 :=
  ![![1, τ, τσ, τx], ![0, 1, 0, 0], ![0, p, g₁, g₂], ![0, q, h₁, h₂]]

/-- **The `𝔽₂`-content of the Smith–Witt conditions** (memo §3.3, the Witt/cup half): with the
`x̄₁`-row already pinned by the orientation datum, the isometry `M̄·G_N·M̄ᵀ = G_N` holds **exactly**
when `det ḡ = 1` and the two mod-2 couplings hold.  Kernel check over the `2⁹` assignments. -/
theorem nCup_iff_mod2 (τ τσ τx p q g₁ g₂ h₁ h₂ : ZMod 2) :
    (∀ i j, nCupForm (nMatOf τ τσ τx p q g₁ g₂ h₁ h₂ i) (nMatOf τ τσ τx p q g₁ g₂ h₁ h₂ j)
        = nGram i j)
      ↔ g₁ * h₂ + g₂ * h₁ = 1 ∧ p = τx * g₁ + τσ * g₂ ∧ q = τx * h₁ + τσ * h₂ := by
  revert τ τσ τx p q g₁ g₂ h₁ h₂
  decide

/-- The mod-2 matrix of a parameter tuple's rows is `nMatOf` at the reduced parameters — the `M̄`
of memo §3.3. -/
theorem NStabParam.mat_eq (P : NStabParam) :
    P.rows.mat = nMatOf P.tau P.tauSigma P.tauX2 (nRed P.p) (nRed P.q)
      (nRed (P.g 0 0)) (nRed (P.g 0 1)) (nRed (P.g 1 0)) (nRed (P.g 1 1)) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [NRows.mat, NStabParam.rows, nMatOf, nMod2, nRed]

/-- **Soundness of the parameter tuple**: an admissible tuple satisfies the cup-isometry clause —
its three fields are exactly the three non-vacuous entries of `M̄·G_N·M̄ᵀ = G_N`. -/
theorem NStabParam.rows_isCupIsometry {P : NStabParam} (hP : P.Admissible) :
    P.rows.IsCupIsometry := by
  rw [NRows.IsCupIsometry, P.mat_eq]
  exact (nCup_iff_mod2 _ _ _ _ _ _ _ _ _).mpr
    ⟨(nIsUnit_det_iff P.g).mp hP.det, hP.couple_p, hP.couple_q⟩

/-- Distinct parameter tuples give distinct rows — the uniqueness half of the classification. -/
theorem NStabParam.rows_injective : Function.Injective NStabParam.rows := by
  intro P Q hEq
  have h1 : P.rows.x1 = Q.rows.x1 := by rw [hEq]
  have h2 : P.rows.sigma = Q.rows.sigma := by rw [hEq]
  have h3 : P.rows.x2 = Q.rows.x2 := by rw [hEq]
  simp only [NStabParam.rows_x1, NStabParam.rows_sigma, NStabParam.rows_x2,
    Prod.mk.injEq] at h1 h2 h3
  refine NStabParam.ext h1.1 h1.2.2.1 h1.2.2.2 h2.1 h3.1 (Matrix.ext fun i k => ?_)
  fin_cases i <;> fin_cases k
  exacts [h2.2.2.1, h3.2.2.1, h2.2.2.2, h3.2.2.2]

/-- **The rank-four Smith–Witt classification** (memo §3.3; MC4 deliverable 1).  A frame
endomorphism of `D_N^{ab}` preserves the marked invariant triple — the relation vector `ρ_N = 2t`
(built into `NRows.col`, automatic by `nFrameModel_map_t`), the orientation datum `χ̄`, and the
mod-2 cup Gram `G_N` — **if and only if** it is given by a parameter tuple
`(τ, p, q, τ_σ, τ_{x₂}, g)` with `g ∈ GL₂(ℤ₂)` and the two mod-2 couplings; and the tuple is then
**unique**.  Unconditional, and uniform in `α ≥ 2`. -/
theorem nStabilizer_classification {α : ℕ} (hα : 2 ≤ α) {R : NRows} :
    IsNStab α R ↔ ∃! P : NStabParam, P.Admissible ∧ P.rows = R := by
  constructor
  · intro hR
    obtain ⟨h1, h2, h3⟩ := hR.x1_coord hα
    set P : NStabParam := ⟨R.x1.1, R.x1.2.2.1, R.x1.2.2.2, R.sigma.1, R.x2.1,
      !![R.sigma.2.2.1, R.x2.2.2.1; R.sigma.2.2.2, R.x2.2.2.2]⟩ with hPdef
    have hrows : P.rows = R := by
      refine NRows.ext ?_ ?_ ?_
      · rw [hPdef, NStabParam.rows_x1, ← h1]
      · rw [hPdef, NStabParam.rows_sigma, ← h2]; rfl
      · rw [hPdef, NStabParam.rows_x2, ← h3]; rfl
    have hcup : ∀ i j, nCupForm (P.rows.mat i) (P.rows.mat j) = nGram i j := by
      rw [hrows]; exact hR.cup
    rw [P.mat_eq] at hcup
    obtain ⟨hdet, hp, hq⟩ := (nCup_iff_mod2 _ _ _ _ _ _ _ _ _).mp hcup
    exact ⟨P, ⟨⟨(nIsUnit_det_iff P.g).mpr hdet, hp, hq⟩, hrows⟩,
      fun Q hQ => NStabParam.rows_injective (hQ.2.trans hrows.symm)⟩
  · rintro ⟨P, ⟨hP, rfl⟩, -⟩
    exact ⟨by rw [NStabParam.rows_x1, nChiVec, zpowZtwo_one_exp],
      by rw [NStabParam.rows_sigma, nChiVec, zpowZtwo_zero_exp],
      by rw [NStabParam.rows_x2, nChiVec, zpowZtwo_zero_exp],
      NStabParam.rows_isCupIsometry hP⟩

/-! ### The semidirect-product shape `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` (memo §3.3) -/

/-- The two `t`-components solved from `(p, q, g)`: over `𝔽₂` the coupling reads
`(p̄, q̄) = ḡ·(τ_{x₂}, τ_σ)ᵀ`, and `ḡ` is invertible with `ḡ⁻¹ = [[h̄₂, ḡ₂], [h̄₁, ḡ₁]]` (the
adjugate; in characteristic 2 the signs vanish and `det ḡ = 1`). -/
noncomputable def nTauSolve (p q : ℤ_[2]) (g : Matrix (Fin 2) (Fin 2) ℤ_[2]) : ZMod 2 × ZMod 2 :=
  (nRed (g 1 0) * nRed p + nRed (g 0 0) * nRed q,
    nRed (g 1 1) * nRed p + nRed (g 0 1) * nRed q)

/-- **The closed form `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)`** (memo §3.3): the free parameters are
`τ ∈ ℤ/2`, `p, q ∈ ℤ₂` and `g ∈ GL₂(ℤ₂)`; for each such choice there is **exactly one** pair
`(τ_σ, τ_{x₂})` of `t`-components making the tuple admissible, namely `nTauSolve p q g`.  So the
`(σ, x₂)`-plane behaves exactly like a handle, with the torsion coordinate riding along. -/
theorem nStabParam_tauSolve_unique (τ : ZMod 2) (p q : ℤ_[2]) {g : Matrix (Fin 2) (Fin 2) ℤ_[2]}
    (hg : IsUnit g.det) :
    ∃! st : ZMod 2 × ZMod 2, NStabParam.Admissible ⟨τ, p, q, st.1, st.2, g⟩ := by
  have hdet := (nIsUnit_det_iff g).mp hg
  have hkey : ∀ pb qb g₁ g₂ h₁ h₂ : ZMod 2, g₁ * h₂ + g₂ * h₁ = 1 →
      ∀ st : ZMod 2 × ZMod 2,
        (pb = st.2 * g₁ + st.1 * g₂ ∧ qb = st.2 * h₁ + st.1 * h₂)
          ↔ st = (h₁ * pb + g₁ * qb, h₂ * pb + g₂ * qb) := by decide
  refine ⟨nTauSolve p q g, ⟨hg, ?_, ?_⟩, fun st hst => ?_⟩
  · exact ((hkey _ _ _ _ _ _ hdet _).mpr rfl).1
  · exact ((hkey _ _ _ _ _ _ hdet _).mpr rfl).2
  · exact (hkey _ _ _ _ _ _ hdet st).mp ⟨hst.couple_p, hst.couple_q⟩

/-! ### The relation-vector clause is automatic -/

/-- **Every frame automorphism fixes the torsion generator** (memo §3.2(ii)): `t = x̄₀` is the
unique element of order 2 of `D_N^{ab}`, so the relation-vector clause `φ(ρ_N) = ρ_N` costs
nothing and is legitimately built into the `t`-column of `NRows.col`.  (The rank-three precedent
is `xi_fixes_t`, `GQ2/AnabelianBridge/Classification.lean:161`.) -/
theorem nFrameModel_map_t {h : ℕ} (φ : NFrameModel h ≃* NFrameModel h) :
    φ (ofAdd ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2]))) = ofAdd (1, 0, 0, 0, 0) := by
  set t : NFrameModel h := ofAdd (1, 0, 0, 0, 0) with ht
  have htsq : t ^ 2 = 1 := by
    rw [ht, ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · show (2 : ℕ) • (1 : ZMod 2) = 0
      decide
    all_goals simp
  have htne : t ≠ 1 := by
    intro hc
    have h0 : ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
        (0 : Fin (2 * h) → ℤ_[2])) = 0 :=
      Multiplicative.ofAdd.injective (by rw [← ht, hc, ← ofAdd_zero])
    have h1 : (1 : ZMod 2) = 0 := congrArg (fun z => z.1) h0
    exact absurd h1 (by decide)
  have hfinφ : IsOfFinOrder (φ t) := by
    rw [isOfFinOrder_iff_pow_eq_one]
    exact ⟨2, by norm_num, by rw [← map_pow, htsq, map_one]⟩
  have hfin' : IsOfFinOrder (ofAdd ((φ t).toAdd.1, (φ t).toAdd.2.1, (φ t).toAdd.2.2.1,
      (φ t).toAdd.2.2.2.1, (φ t).toAdd.2.2.2.2) : NFrameModel h) := by
    rw [show ((φ t).toAdd.1, (φ t).toAdd.2.1, (φ t).toAdd.2.2.1, (φ t).toAdd.2.2.2.1,
      (φ t).toAdd.2.2.2.2) = (φ t).toAdd from rfl, ofAdd_toAdd]
    exact hfinφ
  obtain ⟨hb, hc, hd, hf⟩ := nFinOrder_model hfin'
  have hφne : (φ t).toAdd.1 ≠ 0 := by
    intro h0
    refine htne (φ.injective ?_)
    rw [map_one]
    conv_lhs => rw [← ofAdd_toAdd (φ t)]
    rw [← ofAdd_zero]
    exact congrArg ofAdd (Prod.ext h0 (Prod.ext hb (Prod.ext hc (Prod.ext hd hf))))
  have hone : (φ t).toAdd.1 = 1 := by
    revert hφne
    generalize (φ t).toAdd.1 = a
    revert a
    decide
  refine Multiplicative.toAdd.injective ?_
  show (φ t).toAdd = ((1 : ZMod 2), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
    (0 : Fin (2 * h) → ℤ_[2]))
  exact Prod.ext hone (Prod.ext hb (Prod.ext hc (Prod.ext hd hf)))

/-! ### The `(σ, x₂)`-block: `GL₂(ℤ₂) = E₂(ℤ₂)·{diag(κ, 1)}` -/

/-- The `N4` frame move on the `(σ, x₂)`-plane (memo §3.4): the determinant `diag(κ, 1)`,
`σ̄ ↦ κσ̄`. -/
noncomputable def nPlaneDet (κ : ℤ_[2]ˣ) : Matrix (Fin 2) (Fin 2) ℤ_[2] := !![(κ : ℤ_[2]), 0; 0, 1]

@[simp] theorem nPlaneDet_det (κ : ℤ_[2]ˣ) : (nPlaneDet κ).det = (κ : ℤ_[2]) := by
  rw [nPlaneDet, Matrix.det_fin_two_of]; ring

theorem nPlaneDet_mul (κ κ' : ℤ_[2]ˣ) : nPlaneDet κ * nPlaneDet κ' = nPlaneDet (κ * κ') := by
  rw [nPlaneDet, nPlaneDet, nPlaneDet, Matrix.mul_fin_two]
  refine Matrix.ext fun i k => ?_
  fin_cases i <;> fin_cases k <;> simp

@[simp] theorem nPlaneDet_one : nPlaneDet 1 = 1 := by
  rw [nPlaneDet, Matrix.one_fin_two, Units.val_one]

/-- **`GL₂(ℤ₂) = E₂(ℤ₂)·{diag(κ, 1)}`** — memo §3.4's "N2/N3 generate `SL₂(ℤ₂)` on the block
(elementary matrices generate `SL₂` over a local ring); N4 supplies the determinant, so N2–N4 give
all of `GL₂(ℤ₂)`", as a theorem.  The `SL₂` factor is HM3's `mem_closure_planeElemSet_of_det_eq_one`
(the memo's "SL₂ part lifts by one-line commutator identities"); the determinant factor is the
single `S2` family. -/
theorem nGL_factor {g : Matrix (Fin 2) (Fin 2) ℤ_[2]} (hg : IsUnit g.det) :
    ∃ s : Matrix (Fin 2) (Fin 2) ℤ_[2],
      s ∈ Submonoid.closure planeElemSet ∧ g = s * nPlaneDet hg.unit := by
  have hspec : ((hg.unit : ℤ_[2]ˣ) : ℤ_[2]) = g.det := hg.unit_spec
  refine ⟨g * nPlaneDet hg.unit⁻¹, mem_closure_planeElemSet_of_det_eq_one ?_, ?_⟩
  · rw [Matrix.det_mul, nPlaneDet_det]
    calc g.det * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2])
        = ((hg.unit : ℤ_[2]ˣ) : ℤ_[2]) * ((hg.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) := by rw [hspec]
      _ = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  · rw [Matrix.mul_assoc, nPlaneDet_mul, inv_mul_cancel, nPlaneDet_one, Matrix.mul_one]

end Stabilizer

/-! ## §5 The lifting strata: binders, and a vocabulary finding  (memo §5.1–§5.3, §6.4, §8)

Memo §5 splits the lift into three strata.  Two are already theorems in this lane: **S1** (the
exact Nielsen lifts — §2's `dnTauBEquiv`/`dnTauCEquiv` and HM4's `dnTauDEquiv`) and the **handle**
stratum (HM5's `nHandleMixLift`).  The other two enter as `def`s — **never axioms** (memo §8, the
`BLabHypothesis` convention):

* `NScalingHypothesis` — memo §3.4's family N4, the unit scaling of the `(σ, x₂)`-block.  Memo
  §5.2's verdict is that this is discharged by the **existing** axiom B8: `Cores.lean`'s
  `nOuter_scaling` and `nInner_scaling` are already theorems, obtained from B8 through
  `peripheralTriple_scaling`, so no new axiom and no census bump.  What is *not* done here is the
  conjugator matching that assembles the two scaled triples into one automorphism.
* `NMixHypothesis` — memo §3.4's families N5/N6, memo §8 Decision 2(B)'s `NMixHypothesis`.

**Vocabulary finding (reported, not patched).**  HM4's schematic S3 binder
`NCoreMixHypothesis α h S3` cannot be used for these families: it asks for a realizing
automorphism *inside* `A(P,h)`, and no generator of `dnClearAuts` touches a slot of index `< 3`,
so every element of `A(P,h)` fixes `x₀`, `x₁` and `σ` on the nose (`dnClearAuts_fixes_core`).  A
genuinely `x̄₁`-mixing frame move is therefore **unrealizable** in `A(P,h)`, and
`NCoreMixHypothesis α h {frameEnd (nFrameMixX1 p)}` is *false* for every `p ≠ 0`
(`nCoreMixHypothesis_not_of_mix`).  The sound binder is stated at the marked generators, through
the ν-frame, without the `A(P,h)` clause — that is `NMixHypothesis` below.  HM4's `nLiftSplit_iff`
is unaffected: it is a statement *about* the two binders, and the handle field it discharges is
exactly the stratum that does live in `A(P,h)`. -/

section Strata

/-- **Index case analysis for a rank-`(4+2h)` core**: a letter is one of the four core letters or
one of the `2h` handle letters.  (MC5 wants this too.) -/
theorem nCoreIdx_cases {h : ℕ} (i : Fin (coreRank h)) :
    i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ (∃ j : Fin h, i = handleIdxU j) ∨
      ∃ j : Fin h, i = handleIdxV j := by
  have hlt : (i : ℕ) < 4 + 2 * h := i.isLt
  by_cases h0 : (i : ℕ) = 0
  · exact Or.inl (Fin.val_injective (by rw [h0, coreVal_zero]))
  by_cases h1 : (i : ℕ) = 1
  · exact Or.inr (Or.inl (Fin.val_injective (by rw [h1, coreVal_one])))
  by_cases h2 : (i : ℕ) = 2
  · exact Or.inr (Or.inr (Or.inl (Fin.val_injective (by rw [h2, coreVal_two]))))
  by_cases h3 : (i : ℕ) = 3
  · exact Or.inr (Or.inr (Or.inr (Or.inl (Fin.val_injective (by rw [h3, coreVal_three])))))
  have hj : ((i : ℕ) - 4) / 2 < h := by omega
  by_cases hpar : (i : ℕ) % 2 = 0
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨⟨((i : ℕ) - 4) / 2, hj⟩,
      Fin.val_injective ?_⟩))))
    rw [handleIdxU_val]
    show (i : ℕ) = 4 + 2 * (((i : ℕ) - 4) / 2)
    omega
  · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨⟨((i : ℕ) - 4) / 2, hj⟩,
      Fin.val_injective ?_⟩))))
    rw [handleIdxV_val]
    show (i : ℕ) = 5 + 2 * (((i : ℕ) - 4) / 2)
    omega

/-- **Every automorphism in `A(P,h)` fixes the three leading marked generators.**  No generator of
`dnClearAuts` touches a slot of index `< 3` — the two handle transvections move a handle letter,
`τ_c(k)` moves `x₂`, and HM2's `Φ_j` moves a handle letter and `x₂` — so `x₀`, `x₁` and `σ` are
rigid throughout the whole monoid.  This is the structural fact behind
`nCoreMixHypothesis_not_of_mix`. -/
theorem dnClearAuts_fixes_core (α h : ℕ) {i : Fin (coreRank h)} (hi : (i : ℕ) < 3)
    {F : Function.End (DN α h : Type)} (hF : F ∈ Submonoid.closure (dnClearAuts α h)) :
    F (dnGen α h i) = dnGen α h i := by
  have hne3 : i ≠ 3 := coreVal_lt_three_ne hi
  induction hF using Submonoid.closure_induction with
  | mem G hG =>
    simp only [dnClearAuts, Set.mem_union, Set.mem_iUnion, Set.mem_range] at hG
    rcases hG with ((⟨j, k, rfl⟩ | ⟨j, k, rfl⟩) | ⟨k, rfl⟩) | ⟨j, rfl⟩
    · show dnTauUEquiv α h j k (dnGen α h i) = dnGen α h i
      rw [dnTauUEquiv_gen,
        tauUMark_of_ne _ _ _ _ (handleIdxU_ne_of_val_lt j (by omega)).symm]
    · show dnTauVEquiv α h j k (dnGen α h i) = dnGen α h i
      rw [dnTauVEquiv_gen,
        tauVMark_of_ne _ _ _ _ (handleIdxV_ne_of_val_lt j (by omega)).symm]
    · show dnTauDEquiv α h k (dnGen α h i) = dnGen α h i
      rw [dnTauDEquiv_gen, tauDMark_of_ne _ _ _ hne3]
    · show dnMixEquiv α h j (dnGen α h i) = dnGen α h i
      rw [dnMixEquiv_gen]
      exact handleMixUpdate_of_ne j _ _ _ (handleIdxU_ne_of_val_lt j (by omega)).symm hne3
  | one => rfl
  | mul a b _ _ ha hb =>
    show a (b (dnGen α h i)) = dnGen α h i
    rw [show b (dnGen α h i) = dnGen α h i from hb]
    exact ha

/-- The ν-frame move of family **N5** (memo §3.4): `x̄₁ ↦ x̄₁ + p·σ̄`. -/
noncomputable def nFrameMixX1 {h : ℕ} (p : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2]) :
    Fin (coreRank h) → ℤ_[2] := Function.update m 1 (m 1 + p * m 2)

/-- **HM4's schematic S3 binder is unsatisfiable for a genuinely mixing stratum.**  A frame move
that shifts the `x̄₁`-row by a nonzero multiple of the `σ̄`-row cannot be realized by an
automorphism of `A(P,h)`: such an automorphism fixes `x₁` (`dnClearAuts_fixes_core`), while the
standard marking `ν_N` has `ν_N(σ̄) = 1`.  So `NCoreMixHypothesis` — which quantifies
`DnRealizes`, whose first clause is membership in `A(P,h)` — is **false** for every stratum set
containing such a move.  The sound binder is `NMixHypothesis`. -/
theorem nCoreMixHypothesis_not_of_mix (α h : ℕ) {p : ℤ_[2]} (hp : p ≠ 0)
    {S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (hmem : frameEnd (nFrameMixX1 p) ∈ S3) : ¬ NCoreMixHypothesis α h S3 := by
  intro hS
  obtain ⟨Ψ, hclear, hframe⟩ := hS _ hmem
  have hx1 : Ψ (dnGen α h 1) = dnGen α h 1 :=
    dnClearAuts_fixes_core α h (by rw [coreVal_one]; omega) hclear
  have hval := congrFun (hframe (nuN α h)) 1
  rw [nuFrame_apply, hx1, frameEnd_apply, nFrameMixX1, Function.update_self, nuFrame_apply,
    nuFrame_apply, show dnGen α h 1 = dnX1 α h from rfl, show dnGen α h 2 = dnSigma α h from rfl,
    nuN_dnX1, nuN_dnSigma, toAdd_ofAdd, toAdd_ofAdd, mul_one, zero_add] at hval
  exact hp hval.symm

/-- **The S3 core-mixing binder for `N`** (memo §3.4's family N5, memo §8 Decision 2(B)'s
`NMixHypothesis`) — a `def`, **never an axiom**.  For every `p ∈ ℤ₂` a χ-preserving continuous
automorphism of `D_N` whose ν-frame action is the pure transvection `x̄₁ ↦ x̄₁ + p·σ̄`: the group
move is `x₁ ↦ x₁σ^p` with its coupled `x₂ ↦ x₀^p·x₂`, and the coupled factor is ν-invisible,
every `ℤ₂`-character killing `x₀` (`nChar_dnX0`).

Stated at the **marked generators**, not through `DnRealizes` — see
`nCoreMixHypothesis_not_of_mix` for why HM4's schematic form cannot be used. -/
def NMixHypothesis (α h : ℕ) : Prop :=
  ∀ p : ℤ_[2], ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
    (∀ x, chiN α h (Ψ x) = chiN α h x)
      ∧ ∀ f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]),
        nuFrame f (fun i => Ψ (dnGen α h i)) = nFrameMixX1 p (nuFrame f (dnGen α h))

/-- **The S2 unit-scaling binder for `N`** (memo §3.4's family N4, memo §5.2) — a `def`, **never
an axiom**.  For every `γ ∈ ℤ₂ˣ` a χ-preserving continuous automorphism of `D_N` scaling the
`σ̄`-row of the ν-frame by `γ`.  The other rows are left completely unconstrained: memo §5.2 says
the scaling shifts them uncontrollably and that the shifts are absorbed afterwards by the S1
shears — which is exactly what `nMarkedCorrection` does.

Memo §5.2's verdict: this stratum is **discharged by the existing axiom B8** — `nOuter_scaling`
and `nInner_scaling` (`Cores.lean`) are already theorems obtained from `peripheralTriple_scaling`,
so no new axiom and no census bump.  What MC4 does not carry out is the conjugator matching (and
the Frattini surjectivity) that assembles the two scaled triples into a single automorphism; hence
the family is threaded here rather than constructed. -/
def NScalingHypothesis (α h : ℕ) : Prop :=
  ∀ γ : ℤ_[2]ˣ, ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
    (∀ x, chiN α h (Ψ x) = chiN α h x)
      ∧ ∀ f : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]),
        toAdd (f (Ψ (dnSigma α h))) = (γ : ℤ_[2]) * toAdd (f (dnSigma α h))

/-- **The `N_α` image invariant** (memo §6.4): `im χ_N = ⟨v⟩` with `v = −(1+2^α)⁻¹`, procyclic.
The decisive `M`/`N` separator (memo §3.2(i), V2): `im χ_M = ⟨−1⟩ × ⟨u⟩` is not procyclic,
`im χ_N` is. -/
noncomputable def imChiN (α : ℕ) : Subgroup ℤ_[2]ˣ :=
  (Subgroup.closure {(nUnit α : ℤ_[2]ˣ)}).topologicalClosure

/-- **N-Lab (hypothesis form — never an axiom)** (memo §6.4, §8 Decision 1(c)): Labute's
classification of Demushkin groups of even rank with `q = 2` (Labute 1967, Thm 8), specialised to
the `N_α` core — a pro-2 group with the `N_α` invariants (Demushkin, rank `4 + 2h`, `q = 2`, image
invariant `imChiN α`) is continuously isomorphic to `D_N`.

**Two recorded deviations from `BLabHypothesis`** (`GQ2/Roe/MarkedPro2.lean:141`).  (i) The
abstract-`G` form is forced, not chosen: MC5's other side is `G_K(2)`, not a presented group
(memo §6.4, risk R6) — this widens what the owner is asked to accept.  (ii) The orientation clause
is carried by the **image invariant** alone.  The repo's descent-characterized orientation
predicate (`IsLabuteOrientation`) is stated for the presented `D_R` and has no abstract-`G`
counterpart (the dualizing-module route is deferred, `GQ2/Orientation.lean`); the image invariant
is what Labute's even-rank `q = 2` classification keys on, and it is the M/N separator.  Dropping
the descent clause makes this binder *stronger* than the memo's sketch — flagged for G-Lab, not
silently resolved. -/
def NLabHypothesis (α h : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G] [DistribMulAction G (ZMod 2)]
    [ContinuousSMul G (ZMod 2)],
    IsDemushkin 2 G → demushkinRank 2 G = coreRank h → demushkinQ G = 2 →
      (∃ χ : G →* ℤ_[2]ˣ, Continuous χ ∧ MonoidHom.range χ = imChiN α) →
        Nonempty (ContinuousMulEquiv G (DN α h : Type))

end Strata

/-! ## §6 The composition theorem: the marked correction at the `N`-core  (packet Prop. 7.2)

Memo §5.3's three strata, composed.  Given any `Multiplicative ℤ₂`-character `ν'` of `D_N` whose
value at the pivot letter `σ` is a **unit** — packet §7's unimodularity clause `I = C`, which is
all the marked data pins — there is a continuous automorphism `u` of `D_N` with

```
χ_N ∘ u = χ_N        and        ν' ∘ u = ν_N.
```

Four moves, in the order forced by what each one disturbs:

1. **S2** (`NScalingHypothesis` at `γ = ν'(σ̄)⁻¹`) normalizes the pivot row to `1`; memo §5.2 says
   it shifts the other rows uncontrollably, and the binder accordingly promises nothing about them;
2. **the handle stratum** (HM5's `nHandleMixLift`, a *theorem*) clears the `2h` handle rows,
   keeping the pivot;
3. **S1** (HM4's exact `dnTauDEquiv`, family N2) clears the `x̄₂`-row against the pivot;
4. **S3** (`NMixHypothesis`, family N5) clears the `x̄₁`-row against the pivot.

The `x̄₀`-row needs no move at all: `nChar_dnX0` kills it for *every* `ℤ₂`-character, which is why
`ν_N(t) = 0` is a consistency check that passes rather than an equation to solve (memo §3.6). -/

section Composition

variable (α h : ℕ)

/-- **The marked correction at the `N`-core** (packet Prop. 7.2; MC4 deliverable 3).  Under the
two S2/S3 binders, every `ν'` with unimodular pivot admits a χ-preserving continuous automorphism
`u` of `D_N` transporting it to the standard marking `ν_N`.  The handle stratum is *not* a
hypothesis — HM5 proved it. -/
theorem nMarkedCorrection (hMix : NMixHypothesis α h) (hScal : NScalingHypothesis α h)
    (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hw : IsUnit (toAdd (nu' (dnSigma α h)))) :
    ∃ u : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (u x) = chiN α h x) ∧ ∀ x, nu' (u x) = nuN α h x := by
  classical
  -- Step 1 (S2): normalize the pivot row.
  obtain ⟨Ψs, hsChi, hsFrame⟩ := hScal hw.unit⁻¹
  set nu2 : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]) :=
    nu'.comp (autHom Ψs) with hnu2
  have hsig2 : toAdd (nu2 (dnSigma α h)) = 1 := by
    show toAdd (nu' (Ψs (dnSigma α h))) = 1
    rw [hsFrame nu']
    calc ((hw.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * toAdd (nu' (dnSigma α h))
        = ((hw.unit⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((hw.unit : ℤ_[2]ˣ) : ℤ_[2]) := by rw [hw.unit_spec]
      _ = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  -- Step 2 (handles): HM5's theorem.
  obtain ⟨Ψh, -, hhChi, hU, hV, hpiv⟩ :=
    nHandleMixLift α h nu2 (by rw [hsig2]; exact isUnit_one)
  set nu3 : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]) :=
    nu2.comp (autHom Ψh) with hnu3
  have hsig3 : toAdd (nu3 (dnSigma α h)) = 1 := by
    show toAdd (nu2 (Ψh (dnSigma α h))) = 1
    rw [hpiv]; exact hsig2
  have hU3 : ∀ j : Fin h, nu3 (dnGen α h (handleIdxU j)) = 1 := hU
  have hV3 : ∀ j : Fin h, nu3 (dnGen α h (handleIdxV j)) = 1 := hV
  -- Step 3 (S1, family N2): clear the `x̄₂`-row.
  set k : ℤ_[2] := -(toAdd (nu3 (dnX2 α h))) with hk
  set nu4 : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]) :=
    nu3.comp (autHom (dnTauDEquiv α h k)) with hnu4
  have hgen4 : ∀ i : Fin (coreRank h),
      nu4 (dnGen α h i) = nu3 (tauDMark (isProP_DN α h) k (dnGen α h) i) := fun i => by
    show nu3 (dnTauDEquiv α h k (dnGen α h i)) = _
    rw [dnTauDEquiv_gen]
  have hsig4 : toAdd (nu4 (dnSigma α h)) = 1 := by
    rw [show dnSigma α h = dnGen α h 2 from rfl, hgen4, tauDMark_two]; exact hsig3
  have hx24 : toAdd (nu4 (dnX2 α h)) = 0 := by
    rw [show dnX2 α h = dnGen α h 3 from rfl, hgen4, tauDMark_three, map_mul, toAdd_mul,
      toAdd_map_zpowZtwo (isProP_DN α h) nu3, show dnGen α h 2 = dnSigma α h from rfl, hsig3,
      show dnGen α h 3 = dnX2 α h from rfl, hk, mul_one, neg_add_cancel]
  have hU4 : ∀ j : Fin h, nu4 (dnGen α h (handleIdxU j)) = 1 := fun j => by
    rw [hgen4, tauDMark_of_ne _ _ _ (handleIdxU_ne_three j)]; exact hU3 j
  have hV4 : ∀ j : Fin h, nu4 (dnGen α h (handleIdxV j)) = 1 := fun j => by
    rw [hgen4, tauDMark_of_ne _ _ _ (handleIdxV_ne_three j)]; exact hV3 j
  -- Step 4 (S3, family N5): clear the `x̄₁`-row.
  set p : ℤ_[2] := -(toAdd (nu4 (dnX1 α h))) with hp
  obtain ⟨Ψ5, h5Chi, h5Frame⟩ := hMix p
  refine ⟨Ψ5.trans ((dnTauDEquiv α h k).trans (Ψh.trans Ψs)), fun x => ?_, ?_⟩
  · show chiN α h (Ψs (Ψh (dnTauDEquiv α h k (Ψ5 x)))) = chiN α h x
    rw [hsChi, hhChi, chiN_dnTauDEquiv, h5Chi]
  · -- generator-wise agreement, then `dn_hom_ext`
    have hgen : ∀ i : Fin (coreRank h), nu4 (Ψ5 (dnGen α h i)) = nuN α h (dnGen α h i) := by
      intro i
      have hrow := congrFun (h5Frame nu4) i
      rw [nuFrame_apply, nFrameMixX1] at hrow
      refine Multiplicative.toAdd.injective ?_
      rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
      · rw [hrow, Function.update_of_ne nCoreZero_ne_one, nuFrame_apply,
          show dnGen α h 0 = dnX0 α h from rfl, nChar_dnX0, nuN_dnX0, toAdd_one, toAdd_ofAdd]
      · rw [hrow, Function.update_self, nuFrame_apply, nuFrame_apply,
          show dnGen α h 1 = dnX1 α h from rfl, show dnGen α h 2 = dnSigma α h from rfl,
          hsig4, mul_one, hp, nuN_dnX1, toAdd_ofAdd, add_neg_cancel]
      · rw [hrow, Function.update_of_ne nCoreTwo_ne_one, nuFrame_apply,
          show dnGen α h 2 = dnSigma α h from rfl, hsig4, nuN_dnSigma, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne nCoreThree_ne_one, nuFrame_apply,
          show dnGen α h 3 = dnX2 α h from rfl, hx24, nuN_dnX2, toAdd_ofAdd]
      · rw [hrow, Function.update_of_ne (nHandleIdxU_ne_one j), nuFrame_apply, hU4 j,
          nuN_handleU, toAdd_one]
      · rw [hrow, Function.update_of_ne (nHandleIdxV_ne_one j), nuFrame_apply, hV4 j,
          nuN_handleV, toAdd_one]
    have hEq : nu4.comp (autHom Ψ5) = nuN α h := dn_hom_ext _ _ hgen
    intro x
    show nu' (Ψs (Ψh (dnTauDEquiv α h k (Ψ5 x)))) = nuN α h x
    exact DFunLike.congr_fun hEq x

/-- **The composition theorem in `NLiftSplit` clothing** (HM4's `nLiftSplit_iff`): MC5 supplies
only the two binder fields — the handle field is `nLiftSplit_handle`, a theorem — and gets the
marked correction.  The S12/S3 stratum sets are carried but unused, which is the point: what the
correction consumes is the *marked-generator* form of the two strata (`NScalingHypothesis`,
`NMixHypothesis`), not HM4's schematic `A(P,h)` form (`nCoreMixHypothesis_not_of_mix`). -/
theorem nMarkedCorrection_of_liftSplit
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : NLiftSplit α h S12 S3) (hMix : NMixHypothesis α h) (hScal : NScalingHypothesis α h)
    (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hw : IsUnit (toAdd (nu' (dnSigma α h)))) :
    ∃ u : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (u x) = chiN α h x) ∧ ∀ x, nu' (u x) = nuN α h x :=
  nMarkedCorrection α h hMix hScal nu' hw

/-- The hypothesis set of `nMarkedCorrection` is non-empty at every `(α, h)`: the standard marking
`ν_N` itself has a unit pivot, so the correction is not vacuously quantified. -/
theorem nMarkedCorrection_nuN (hMix : NMixHypothesis α h) (hScal : NScalingHypothesis α h) :
    ∃ u : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (u x) = chiN α h x) ∧ ∀ x, nuN α h (u x) = nuN α h x :=
  nMarkedCorrection α h hMix hScal (nuN α h) (isUnit_nuN_dnSigma α h)

end Composition
