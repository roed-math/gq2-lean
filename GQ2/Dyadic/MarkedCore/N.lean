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
