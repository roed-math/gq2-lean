import GQ2.BoundaryFrame
import GQ2.MaxProP

/-!
# B10: the tame quotient of `G_ℚ₂` — definition layer  (P-06 follow-up)

The paper's Prop. 3.2 needs, on the local side, the **classical description of the tame
quotient of a local absolute Galois group**: there is a closed normal pro-2 subgroup
`W_F ≤ G_{ℚ₂}` (wild inertia) with

  `G_{ℚ₂}/W_F ≅ T_tame = ⟨σ, τ ∣ τ^σ = τ²⟩_prof`.

This is a literature leaf on a par with B1/B4 — **NSW [1], Ch. VII §7.5, Theorem (7.5.3)
(Iwasawa)**: the Galois group of the maximal tamely ramified extension of a local field `k`
is the profinite group on two generators `σ, τ` with the single relation `στσ⁻¹ = τ^q`
(`q = #κ = 2` here); together with **(7.5.2)** (the split extension `1 → Ẑ^{(p′)}(1) → G_k →
Γ → 1`) and the standard fact that `G(k̄|k_tr) = W_F` is pro-`p` (ramification theory; Serre,
*Local Fields* [7], Ch. IV).  It was **not** in the step-1 census (which is otherwise
2-centric); it enters now as axiom **B10** (`GQ2.tameQuotient`, in
`GQ2/Foundations/Axioms.lean`) by explicit decision after the P-06 escalation — see
`docs/section3-extraction.md` §"escalations" and the board's P-06 bullet.

## Conventions

* `Ttame`, `tameSigma`, `tameTau` are the P-11 layer's (`GQ2/BoundaryFrame.lean`) — the
  presented profinite group on `σ = of 0`, `τ = of 1` with relator `tameWord = τ^σ·(τ²)⁻¹`,
  where `x ^ g = g⁻¹xg` (`conjP`) and the paper's `σ` is **geometric** Frobenius ("geometric
  Frobenius acts by squaring", Prop. 3.2's proof).  NSW's (7.5.3) is stated with arithmetic
  `σ` acting on the left (`στσ⁻¹ = τ^q`); the two presentations agree under `σ ↦ σ⁻¹`, which
  is an automorphism of the free profinite group carrying either relator to a conjugate of
  the other's inverse — same closed normal closure, same presented group.
* **Deviation (as in `LocalTameQuotient`, `GQ2/SectionThree.lean`):** Mathlib has no
  ramification theory, so the bundle does not *say* "wild inertia"; it asserts a closed
  normal pro-2 `W` with tame quotient `T_tame`.  By paper Lemma 3.3 (`O₂(G_{ℚ₂}) = W_F`)
  such a `W` is unique — but **maximality is not part of the axiom**: it is Lemma 3.3's
  *proved* content (pure profinite group theory of `T_tame`, from Lemma 3.1's finite
  analysis), and stays a theorem obligation (P-09; consumed by `prop_3_2_local`, which
  `extends` this bundle with the maximality field).

The `normal` field is an instance-binder so that the `equiv` field's quotient `AbsGalQ2 ⧸ W`
elaborates (same device as `LocalTameQuotient`).
-/

namespace GQ2

/-- The tame relation holds in `T_tame`: `τ^σ = τ²`  (paper §3 opening display; proved from
the presentation — no axiom). -/
theorem tame_relation : conjP tameTau tameSigma = tameTau ^ 2 := by
  have h := relator_quotientMk_eq_one {tameWord} rfl
  rw [tameWord] at h
  simp only [conjP] at h ⊢
  exact mul_inv_eq_one.mp h

/-- **B10 (tame quotient of `G_ℚ₂`), the bundle.**  A closed normal pro-2 subgroup
`W ≤ G_{ℚ₂}` (wild inertia, encoded intrinsically — see the module docstring) together with
a continuous isomorphism `G_{ℚ₂}/W ≅ T_tame`.

Citation: **NSW [1] (7.5.3) (Iwasawa)** with (7.5.2); Serre *Local Fields* [7] Ch. IV
(wild inertia is pro-`p`).  Paper: Prop. 3.2, local side ("the standard description of the
tame quotient in the geometric normalization").  The axiom `GQ2.tameQuotient` lives in
`GQ2/Foundations/Axioms.lean`. -/
structure TameQuotientData where
  /-- The wild subgroup `W_F ≤ G_{ℚ₂}`. -/
  W : Subgroup AbsGalQ2
  /-- `W_F` is normal. -/
  [normal : W.Normal]
  /-- `W_F` is closed. -/
  isClosed : IsClosed (W : Set AbsGalQ2)
  /-- `W_F` is pro-2. -/
  isProP : IsProP 2 W
  /-- The tame quotient: `G_{ℚ₂}/W_F ≅ T_tame`. -/
  equiv : ContinuousMulEquiv (AbsGalQ2 ⧸ W) Ttame

end GQ2
