/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.NpcFox
import GQ2.Dyadic.Word.Stokes
import GQ2.Dyadic.Word.Hessian

/-!
# Dyadic campaign, ticket WNP-c: Stokes, scalar, Hessian and phase certificates for the
corrected noncompact-`N` word

Closing file of the procyclic-`N` lane (packet Def. 9.1 items (5)–(6) for row 3 of the R5
selection freeze), on WNP-a's word, WNP-b's Fox certificate, the NC lane's second-jet theorem
and WW3/WW4's toolkits.

Placeholder docstring; the final one is written at the end of the ticket.
-/

namespace GQ2.Dyadic.Certificates.Npc

open GQ2.FoxH GQ2.Dyadic.Words.Npc

/-! ## §0. The row's binomial parity

The generic `𝔽₂` parity kit lives in `GQ2/Dyadic/Word/Stokes.lean` since ticket WWH.  What stays
here is the parity that is about *this* row and cannot follow into a `module` file: it reads off
the plain-import spelling-discipline lemmas `Words.Npc.two_add_two_pow` /
`Words.Npc.odd_one_add_two_pow`. -/

section Parity

/-- `C(2 + 2^α, 2)` is odd exactly on the branch condition `α ≥ 2`: with `2 + 2^α = 2m`,
`C(2m,2) = m(2m−1)` and `m = 1 + 2^{α−1}` is odd iff `α ≥ 2`.  This is where the freeze's
"`α ≥ 2` is a Hessian condition" lives on this row: WNP-b's first-order rows see only the
parity of `2 + 2^α` (`even_two_add_two_pow`, `α ≥ 1`). -/
theorem choose_two_add_two_pow_odd {α : ℕ} (hα : 2 ≤ α) : Odd ((2 + 2 ^ α).choose 2) := by
  have hm : 2 + 2 ^ α = 2 * (1 + 2 ^ (α - 1)) := two_add_two_pow α (by omega)
  set m := 1 + 2 ^ (α - 1) with hm_def
  have hchoose : (2 * m).choose 2 = m * (2 * m - 1) := by
    rw [Nat.choose_two_right, show 2 * m * (2 * m - 1) = m * (2 * m - 1) * 2 by ring,
      Nat.mul_div_cancel _ (by norm_num)]
  rw [hm, hchoose]
  have hm1 : 1 ≤ m := Nat.le_add_right 1 _
  exact (odd_one_add_two_pow hα).mul ⟨m - 1, by omega⟩

/-- `2·w = 0` in `𝔽₂` — the `abel_nf` residue on every assembled row. -/
theorem two_nsmul_zmod2 : ∀ w : ZMod 2, (2 : ℕ) • w = 0 := by decide

/-- `2·w = 0` in `𝔽₂`, `ℤ`-smul form (the shape `abel_nf` actually produces). -/
theorem two_zsmul_zmod2 : ∀ w : ZMod 2, (2 : ℤ) • w = 0 := by decide

/-- `(−1)·w = w` in `𝔽₂` — the other `abel_nf` residue. -/
theorem neg_one_zsmul_zmod2 : ∀ w : ZMod 2, (-1 : ℤ) • w = w := by decide

end Parity

/-! ## §1. Second-order toolkit: pure-base lifts and the one-sided commutator

Two lane-generic additions to WW3's `HeisLift` calculus, both forced by the η̂-alphabet and both
hoist candidates (they are stated for an arbitrary `PWord` alphabet and an arbitrary module):

* `heisPureBase` — the base embedding `C →* HeisLift A C`.  It is what keeps the η̂-atom
  **opaque**: a `σ`-letter carrying no primal/dual offset has *pure base* denotation, so
  `σ^{η̂}` denotes `⟨0,0,0,S^{E(η̂)}⟩` and is never expanded into a geometric sum.  WNP-b's
  `.etaA`-opacity design call, one degree up.
* `heisCommR_of_left_trivial` — the commutator law when only the **left** argument has trivial
  base.  WW3's `heisCommR_of_trivial` needs both; this word's two η̂-flavored commutators
  (`[x₀, A]` and `[D_{r,η}, x₁]`) pair an inert argument with an arbitrary one, exactly as at
  first order (WNP-b's `trivAct_commR_left`). -/

section HeisToolkit

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The pure-base embedding** `g ↦ ⟨0, 0, 0, g⟩` of `C` into the Heisenberg lift group. -/
noncomputable def heisPureBase : C →* HeisLift A C where
  toFun g := ⟨0, 0, 0, g⟩
  map_one' := rfl
  map_mul' g g' := by
    refine HeisLift.ext ?_ ?_ ?_ rfl
    · show (0 : A) = 0 + g • 0
      rw [smul_zero, add_zero]
    · show (0 : ElemDual A) = 0 + g • 0
      rw [smul_zero, add_zero]
    · show (0 : ZMod 2) = 0 + 0 + (0 : ElemDual A) (g • 0)
      rw [smul_zero, map_zero, add_zero, add_zero]

@[simp] theorem heisPureBase_a (g : C) : (heisPureBase (A := A) g).a = 0 := rfl

@[simp] theorem heisPureBase_l (g : C) : (heisPureBase (A := A) g).l = 0 := rfl

@[simp] theorem heisPureBase_z (g : C) : (heisPureBase (A := A) g).z = 0 := rfl

@[simp] theorem heisPureBase_g (g : C) : (heisPureBase (A := A) g).g = g := rfl

/-- `(k • λ)(a) = k • λ(a)` on the elementary dual (lane-local copy of WW3's private
`elemDual_nsmul_apply`; hoist candidate). -/
theorem elemDual_nsmul_apply (k : ℕ) (f : ElemDual A) (a : A) : (k • f) a = k • f a := by
  induction k with
  | zero => rfl
  | succ k ih => rw [succ_nsmul, succ_nsmul, ElemDual.add_apply, ih]

/-- A lift with zero first jet **and** zero central value is the pure-base lift of its base —
the recognition lemma that turns an offset-free letter into an opaque operator. -/
theorem heisPureBase_of_eq (p : HeisLift A C) (ha : p.a = 0) (hl : p.l = 0) (hz : p.z = 0) :
    p = heisPureBase p.g :=
  HeisLift.ext ha hl hz rfl

/-- Integer powers of a pure-base lift stay pure base — the η̂- and `2^r`-powers of an
offset-free `σ`. -/
theorem heisPureBase_zpow (g : C) (k : ℤ) :
    (heisPureBase (A := A) g) ^ k = heisPureBase (g ^ k) :=
  (map_zpow (heisPureBase (A := A)) g k).symm

/-- **The commutator law with a trivially-acting left argument**: `[p, r] = p⁻¹ · p^r`, so the
jet is `(r̄⁻¹ − 1)` applied to `p`'s jet — WNP-b's `commR_u_of_left_trivial` one degree up — and
the central value picks up, besides the symmetric mixed pairing `λ_r(a_p) + λ_p(a_r)`, the
**diagonal** term `λ_p((1 + r̄⁻¹)·a_p)` that the two-sided law does not have.

At `r̄` acting trivially the diagonal term dies and this degenerates to WW3's
`heisCommR_of_trivial`. -/
theorem heisCommR_of_left_trivial (p r : HeisLift A C) (hp : ∀ a : A, p.g • a = a) :
    commR p r = ⟨r.g⁻¹ • p.a - p.a, r.g⁻¹ • p.l - p.l,
      p.l p.a + p.l (r.g⁻¹ • p.a) + r.l p.a + p.l r.a, commR p.g r.g⟩ := by
  have hpi : ∀ a : A, p.g⁻¹ • a = a := fun a => inv_smul_eq_iff.mpr (hp a).symm
  have hconj := heisConjR_of_trivial p r hp
  have hcomm : commR p r = p⁻¹ * conjR p r := by
    rw [commR, conjR]
    group
  rw [hcomm, hconj]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show -(p.g⁻¹ • p.a) + p.g⁻¹ • (r.g⁻¹ • p.a) = _
    rw [hpi, hpi, sub_eq_neg_add]
  · show -(p.g⁻¹ • p.l) + p.g⁻¹ • (r.g⁻¹ • p.l) = r.g⁻¹ • p.l - p.l
    rw [smul_elemDual_of_trivial hpi, smul_elemDual_of_trivial hpi]
    abel
  · show p.z + p.l p.a + (p.z + r.l p.a + p.l r.a)
        + (-(p.g⁻¹ • p.l)) (p.g⁻¹ • (r.g⁻¹ • p.a))
      = p.l p.a + p.l (r.g⁻¹ • p.a) + r.l p.a + p.l r.a
    rw [smul_elemDual_of_trivial hpi, hpi, ElemDual.neg_apply, CharTwo.neg_eq]
    linear_combination CharTwo.add_self_eq_zero p.z
  · show p.g⁻¹ * conjR p.g r.g = commR p.g r.g
    rw [commR, conjR]
    group

end HeisToolkit

/-! ### The corrected cross operator in resolver form

`lcSmul S k r` is `L_c = A⁻¹ + B + B·A⁻¹` with `A = S^k`, `B = S^{2^r}`, acting on an
**arbitrary** `C`-module.  Two consumers, and that is the point of the generality: the primal
module `V` (where it is NC2's `lcOp`, by `lcSmul_eq_lcOp`) and the elementary dual
`ElemDual V` (where it is the operator the correction block applies to the *dual* jet).  The
`k`-slot carries the resolved η̂-value `E(η̂)` — the η̂-atom stays opaque, exactly as in
WNP-b's `.etaA` design. -/

section LcSmul

variable {C : Type*} [Group C] {M : Type*} [AddCommGroup M] [DistribMulAction C M]

/-- **The corrected cross operator** `L_c = A⁻¹ + B + B·A⁻¹` (`A = S^k`, `B = S^{2^r}`) as a
module map, on any `C`-module.  Draft eq:Ncross's `L_c = A⁻¹` is the first summand alone
(S3.2, errata item 5). -/
noncomputable def lcSmul (S : C) (k : ℤ) (r : ℕ) (v : M) : M :=
  (S ^ k)⁻¹ • v + S ^ ((2 : ℤ) ^ r) • v + (S ^ ((2 : ℤ) ^ r) * (S ^ k)⁻¹) • v

theorem lcSmul_def (S : C) (k : ℤ) (r : ℕ) (v : M) :
    lcSmul S k r v
      = (S ^ k)⁻¹ • v + S ^ ((2 : ℤ) ^ r) • v + (S ^ ((2 : ℤ) ^ r) * (S ^ k)⁻¹) • v := rfl

/-- `L_c` is additive — it is a sum of three module actions. -/
theorem lcSmul_add (S : C) (k : ℤ) (r : ℕ) (v w : M) :
    lcSmul S k r (v + w) = lcSmul S k r v + lcSmul S k r w := by
  simp only [lcSmul, smul_add]
  abel

@[simp] theorem lcSmul_zero (S : C) (k : ℤ) (r : ℕ) : lcSmul S k r (0 : M) = 0 := by
  simp only [lcSmul, smul_zero, add_zero]

/-- **`L_c` as an additive map** — the `V →+ V` datum the Hessian certificate's change of
variables consumes. -/
noncomputable def lcHom (S : C) (k : ℤ) (r : ℕ) : M →+ M where
  toFun := lcSmul S k r
  map_zero' := lcSmul_zero S k r
  map_add' := lcSmul_add S k r

@[simp] theorem lcHom_apply (S : C) (k : ℤ) (r : ℕ) (v : M) :
    lcHom S k r v = lcSmul S k r v := rfl

/-- **`L_c = 1 + (1 + A⁻¹)(1 + B)`** — the freeze's factored display, over a `2`-torsion
module.  The factorization is what makes the two degenerations below one-liners, and it is the
shape the per-module invertibility question is asked in. -/
theorem lcSmul_eq_one_add_factored (hM₂ : ∀ v : M, v + v = 0) (S : C) (k : ℤ) (r : ℕ) (v : M) :
    lcSmul S k r v
      = v + ((v + (S ^ k)⁻¹ • v) + S ^ ((2 : ℤ) ^ r) • (v + (S ^ k)⁻¹ • v)) := by
  have hneg : ∀ w : M, -w = w := fun w => neg_eq_of_add_eq_zero_left (hM₂ w)
  rw [lcSmul, smul_add, ← mul_smul]
  rw [show v + ((v + (S ^ k)⁻¹ • v) + (S ^ ((2 : ℤ) ^ r) • v
      + (S ^ ((2 : ℤ) ^ r) * (S ^ k)⁻¹) • v))
    = (v + v) + ((S ^ k)⁻¹ • v + (S ^ ((2 : ℤ) ^ r) • v
      + (S ^ ((2 : ℤ) ^ r) * (S ^ k)⁻¹) • v)) by abel, hM₂, zero_add]
  abel

/-- **`L_c` degenerates to the identity when `S` acts trivially** — the scalar/split module:
`A = B = 1`, so `L_c = 1 + 1 + 1 = 1`.  "The scalar module separates nothing" survives the
correction at second order, exactly as it does at first (`foxD_npc_split`). -/
theorem lcSmul_of_trivial (hM₂ : ∀ v : M, v + v = 0) {S : C} (hS : ∀ v : M, S • v = v)
    (k : ℤ) (r : ℕ) (v : M) : lcSmul S k r v = v := by
  have hz : ∀ (m : ℤ) (w : M), (S ^ m) • w = w := fun m w =>
    MulAction.mem_stabilizer_iff.mp (zpow_mem (MulAction.mem_stabilizer_iff.mpr (hS w)) m)
  have hinv : ∀ (m : ℤ) (w : M), (S ^ m)⁻¹ • w = w := fun m w =>
    inv_smul_eq_iff.mpr (hz m w).symm
  rw [lcSmul, mul_smul, hinv, hz, hM₂, zero_add]

end LcSmul

/-! ## §2. The second-order rows of the six factors

The standing setting is WN0-c's, transported to the noncompact alphabet: a marking `t` whose
wild letters and `τ` act trivially (the **unramified class** — the freeze's plus form lives on
the unramified/split side), with the resolver value `E ω₂ = e` displayed exactly.

**The σ-offset convention, and why it is forced.**  Every row below assumes `x .sigma = 0` and
`y .sigma = 0`: the `σ`-letter carries no primal and no dual offset.  This is *not* a
convenience.  On the compact row `σ` occurs only as a bare conjugator, so its offsets enter
linearly and the certificate can carry them; here `σ` occurs inside the profinite power
`A = σ^{η̂}` and the integer power `B = σ^{2^r}`, whose jets are the **geometric sums**
`(1 + S + ⋯ + S^{k−1})·x_σ`.  Carrying those would force the resolver value `E(η̂)` to be
expanded — precisely what WNP-b's `.etaA`-opacity forbids, and what WNP-a's "the word is not
`IsOmega2Only`" makes unavailable anyway.  Under the convention, `A` and `B` are pure-base
lifts (`heisF_aW`, `heisF_bW`) and appear only as the **operators** `A`, `B` on the coefficient
module — exactly as `.etaA` appears only as an operator in the first-order certificates. -/

section StokesRows

variable {h α r : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
  (y : Generator (2 + 2 * h) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The η̂-conjugator is an opaque operator** — the single place `E(η̂)` is evaluated in this
file (WNP-b's `evalFin_aW`, one degree up).  Under the σ-offset convention `A = σ^{η̂}` denotes
the pure-base lift of the resolved element `S^{E(η̂)}`; no geometric sum ever appears. -/
theorem heisF_aW (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (e : EtaData) :
    heisEvalZ ⇑t x y E E₂ (aW h e) = heisPureBase (t.σ ^ E e.toZhat) := by
  rw [aW, heisEvalZ_profPow, heisEvalZ_gen,
    show (⟨x .sigma, y .sigma, 0, t Generator.sigma⟩ : HeisLift A C) = heisPureBase t.σ from
      HeisLift.ext hxσ hyσ rfl rfl,
    heisPureBase_zpow]

/-- **The `2^r`-conjugator is an opaque operator** too: `B = σ^{2^r}` denotes the pure-base lift
of `S^{2^r}`, symbolically in `r`. -/
theorem heisF_bW (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    heisEvalZ ⇑t x y E E₂ (bW h r) = heisPureBase (t.σ ^ ((2 : ℤ) ^ r)) := by
  rw [bW, heisEvalZ_zpow, heisEvalZ_gen,
    show (⟨x .sigma, y .sigma, 0, t Generator.sigma⟩ : HeisLift A C) = heisPureBase t.σ from
      HeisLift.ext hxσ hyσ rfl rfl,
    heisPureBase_zpow]

/-- **Factor 1** — `x₀^{2+2^α}` is jet-zero central with value the diagonal `y₀(a₀)`: the
binomial `C(2+2^α,2)` is odd for `α ≥ 2` (`choose_two_add_two_pow_odd`) while the even exponent
kills both first-order jets.  The `q(c₀)`-production mechanism; unchanged from the compact
row. -/
theorem heisF_leadingPow (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hα : 2 ≤ α) :
    heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α))
      = ⟨0, 0, y (coreLetter h 0) (x (coreLetter h 0)),
          t (coreLetter h 0) ^ (2 + 2 ^ α : ℕ)⟩ := by
  have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  rw [heisEvalZ_zpow, heisEvalZ_gen,
    show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring, zpow_natCast,
    heisPow_of_trivial _ h0]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · exact even_nsmul_eq_zero hA₂ (even_two_add_two_pow (by omega)) _
  · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero (even_two_add_two_pow (by omega)) _
  · show (2 + 2 ^ α) • (0 : ZMod 2) + ((2 + 2 ^ α).choose 2) • _ = _
    rw [smul_zero, zero_add, nsmul_zmod2_odd (choose_two_add_two_pow_odd hα)]
  · rfl

/-- **Factor 2, the first second-order difference from the compact row** — the front block
`[x₀, A]`.

Where the compact word's `[x₀, x₁]` is jet-**zero** with the hyperbolic value `y₀(a₁)+y₁(a₀)`,
this commutator's conjugator *acts*: the block acquires the first jet `(A⁻¹ + 1)·a₀` — the
second-order shadow of WNP-b's new `x₀`-block `A⁻¹ + 1` — and the central value
`y₀(a₀) + y₀(A⁻¹a₀)` whose **diagonal** summand `y₀(a₀)` is what cancels the leading power's
in the assembly (the Stokes-level twin of NC5's `q(c₀)`-cancellation, i.e. of `hα`). -/
theorem heisF_commX0A (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (e : EtaData) :
    heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (aW h e))
      = ⟨(t.σ ^ E e.toZhat)⁻¹ • x (coreLetter h 0) - x (coreLetter h 0),
          (t.σ ^ E e.toZhat)⁻¹ • y (coreLetter h 0) - y (coreLetter h 0),
          y (coreLetter h 0) (x (coreLetter h 0))
            + y (coreLetter h 0) ((t.σ ^ E e.toZhat)⁻¹ • x (coreLetter h 0)),
          commR (t (coreLetter h 0)) (t.σ ^ E e.toZhat)⟩ := by
  have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  rw [heisEvalZ_comm, heisEvalZ_gen, heisF_aW t x y E E₂ hxσ hyσ e,
    heisCommR_of_left_trivial _ _ h0]
  refine HeisLift.ext rfl rfl ?_ rfl
  show y (coreLetter h 0) (x (coreLetter h 0))
      + y (coreLetter h 0) ((t.σ ^ E e.toZhat)⁻¹ • x (coreLetter h 0))
      + (0 : ElemDual A) (x (coreLetter h 0)) + y (coreLetter h 0) 0 = _
  rw [ElemDual.zero_apply, map_zero, add_zero, add_zero]

/-- The boundary conjugator `g = x₁σ^{2^r}` in the certificate's `prodList` spelling: its jet is
the `x₁`-letter's, because `B` is pure base. -/
theorem heisF_gConj (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    heisEvalZ ⇑t x y E E₂ (PWord.prodList [.gen (coreLetter h 1), bW h r])
      = ⟨x (coreLetter h 1), y (coreLetter h 1), 0,
          t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r)⟩ := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_one, mul_one, heisF_bW t x y E E₂ hxσ hyσ]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show x (coreLetter h 1) + t (coreLetter h 1) • (0 : A) = _
    rw [smul_zero, add_zero]
  · show y (coreLetter h 1) + t (coreLetter h 1) • (0 : ElemDual A) = _
    rw [smul_zero, add_zero]
  · show (0 : ZMod 2) + 0 + y (coreLetter h 1) (t (coreLetter h 1) • (0 : A)) = 0
    rw [smul_zero, map_zero, add_zero, add_zero]

/-- **Factor 3, the second second-order difference** — the boundary block `(x₂^g)⁻¹` with
`g = x₁σ^{2^r}`.  The twisting operator is `B⁻¹ = S^{−2^r}`, where the compact row has `S⁻¹`
(WNP-b's `foxD_invConjX2G`, one degree up); the `x₁`-letter of `g` contributes only through the
mixed pairing `y₁(a₂) + y₂(a₁)`, and the diagonal `y₂(a₂)` is the `β(u⁻¹)`-rule's Bockstein
term. -/
theorem heisF_invConjX2G (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) :
    heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2))
        (PWord.prodList [.gen (coreLetter h 1), bW h r])))
      = ⟨-((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)),
          -((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • y (coreLetter h 2)),
          y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1))
            + y (coreLetter h 2) (x (coreLetter h 2)),
          (conjR (t (coreLetter h 2)) (t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r)))⁻¹⟩ := by
  have h1 := mem_trivAct.mp (trivAct_coreLetter t hwild 1)
  have h2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  have hgtriv : ((t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r))⁻¹ • ·) =
      ((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • · : A → A) := by
    funext v
    rw [mul_inv_rev, mul_smul, inv_smul_eq_iff.mpr (h1 _).symm]
  rw [heisEvalZ_inv, heisEvalZ_conj, heisEvalZ_gen, heisF_gConj t x y E E₂ hxσ hyσ,
    heisConjR_of_trivial _ _ h2]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show -((conjR (t (coreLetter h 2)) (t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r)))⁻¹ •
      ((t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2))) = _
    rw [mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _)),
      congrFun hgtriv (x (coreLetter h 2))]
  · show -((conjR (t (coreLetter h 2)) (t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r)))⁻¹ •
      ((t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r))⁻¹ • y (coreLetter h 2))) = _
    rw [smul_elemDual_of_trivial
      (mem_trivAct.mp (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _)))]
    congr 1
    refine ElemDual.ext fun v => ?_
    rw [ElemDual.smul_apply, ElemDual.smul_apply, inv_inv, inv_inv, mul_smul,
      h1]
  · show (0 : ZMod 2) + y (coreLetter h 1) (x (coreLetter h 2))
        + y (coreLetter h 2) (x (coreLetter h 1))
        + ((t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r))⁻¹ • y (coreLetter h 2))
            ((t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)) = _
    rw [ElemDual.smul_apply, inv_inv, smul_inv_smul, zero_add]
  · rfl

/-- The `ω₂`-block's inner word `x₂τ` (in the certificate's `prodList` spelling). -/
theorem heisF_deltaInner (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = ⟨x (coreLetter h i) + x .tau, y (coreLetter h i) + y .tau,
          y (coreLetter h i) (x .tau), t (coreLetter h i) * t.τ⟩ := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisEvalZ_gen, heisEvalZ_gen, heisEvalZ_one, mul_one]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show x (coreLetter h i) + t (coreLetter h i) • x .tau = _
    rw [hi]
  · show y (coreLetter h i) + t (coreLetter h i) • y .tau = _
    rw [smul_elemDual_of_trivial hi]
  · show (0 : ZMod 2) + 0 + y (coreLetter h i) (t (coreLetter h i) • x .tau) = _
    rw [hi, zero_add, zero_add]
  · rfl

/-- **Factor 4** — `(x₂τ)^{ω₂}` at a resolver value `E ω₂ = e` (unramified class): the `e`-th
power of the inner word, by the trivial-base power law.  The `C(e,2)`-term is the resolver-class
sensitivity, dying exactly on `e ≡ 0, 1 (mod 4)` — ticket S1.T's "the lift level is 4, not 2".
Identical to the compact row's, letter for letter: the boundary block is where the two words
agree. -/
theorem heisF_omega2Block (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = ⟨e • (x (coreLetter h i) + x .tau), e • (y (coreLetter h i) + y .tau),
          e • y (coreLetter h i) (x .tau)
            + (e.choose 2) • ((y (coreLetter h i) + y .tau) (x (coreLetter h i) + x .tau)),
          (t (coreLetter h i) * t.τ) ^ e⟩ := by
  have hi := mem_trivAct.mp (trivAct_coreLetter t hwild i)
  have hbase : ∀ v : A, (t (coreLetter h i) * t.τ) • v = v := fun v => by
    rw [mul_smul, hτ, hi]
  rw [PWord.omega2Pow, heisEvalZ_profPow, heisF_deltaInner t x y E E₂ i hwild, hE,
    zpow_natCast, heisPow_of_trivial _ hbase]

/-- **The `δ₀`-letter at second order**: `δ₀ = (x₀τ)^{ω₂}x₀⁻¹` has jet
`(e·(a₀+a_τ) − a₀, e·(y₀+y_τ) − y₀)` at the resolver value `E ω₂ = e`, and its base acts
trivially.  At every **odd** `e` — every honest resolver — the jet collapses to the τ-letter's
alone (`heisJetA_deltaZeroW_odd`), which is what makes the correction block's row readable. -/
theorem heisF_deltaZeroW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    heisEvalZ ⇑t x y E E₂ (deltaZeroW h)
      = ⟨e • (x (coreLetter h 0) + x .tau) - x (coreLetter h 0),
          e • (y (coreLetter h 0) + y .tau) - y (coreLetter h 0),
          e • y (coreLetter h 0) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 0) + y .tau)
                (x (coreLetter h 0) + x .tau))
            + y (coreLetter h 0) (x (coreLetter h 0))
            + e • ((y (coreLetter h 0) + y .tau) (x (coreLetter h 0))),
          (t (coreLetter h 0) * t.τ) ^ e * (t (coreLetter h 0))⁻¹⟩ := by
  have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
  have hbase : ∀ v : A, ((t (coreLetter h 0) * t.τ) ^ e) • v = v := by
    intro v
    have hm : ∀ v : A, (t (coreLetter h 0) * t.τ) • v = v := fun v => by rw [mul_smul, hτ, h0]
    exact MulAction.mem_stabilizer_iff.mp
      (pow_mem (MulAction.mem_stabilizer_iff.mpr (hm v)) e)
  have h0i : ∀ v : A, (t (coreLetter h 0))⁻¹ • v = v := fun v =>
    inv_smul_eq_iff.mpr (h0 v).symm
  rw [deltaZeroW, prodList_pair, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one,
    heisF_omega2Block t x y E E₂ 0 hwild hτ hE, heisEvalZ_inv, heisEvalZ_gen]
  refine HeisLift.ext ?_ ?_ ?_ rfl
  · show e • (x (coreLetter h 0) + x .tau)
        + ((t (coreLetter h 0) * t.τ) ^ e) • (-((t (coreLetter h 0))⁻¹ • x (coreLetter h 0)))
      = _
    rw [smul_neg, hbase, h0i, sub_eq_add_neg]
  · show e • (y (coreLetter h 0) + y .tau)
        + ((t (coreLetter h 0) * t.τ) ^ e) • (-((t (coreLetter h 0))⁻¹ • y (coreLetter h 0)))
      = e • (y (coreLetter h 0) + y .tau) - y (coreLetter h 0)
    rw [smul_neg, smul_elemDual_of_trivial hbase, smul_elemDual_of_trivial h0i,
      sub_eq_add_neg]
  · show e • y (coreLetter h 0) (x .tau)
          + (e.choose 2) • ((y (coreLetter h 0) + y .tau) (x (coreLetter h 0) + x .tau))
        + (0 + y (coreLetter h 0) (x (coreLetter h 0)))
        + (e • (y (coreLetter h 0) + y .tau))
            (((t (coreLetter h 0) * t.τ) ^ e) • (-((t (coreLetter h 0))⁻¹ •
              x (coreLetter h 0))))
      = e • y (coreLetter h 0) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 0) + y .tau)
                (x (coreLetter h 0) + x .tau))
            + y (coreLetter h 0) (x (coreLetter h 0))
            + e • ((y (coreLetter h 0) + y .tau) (x (coreLetter h 0)))
    rw [smul_neg, hbase, h0i, elemDual_nsmul_apply, map_neg, CharTwo.neg_eq, zero_add]

/-- **The `δ₀`-jet at an odd resolver value** — the τ-letter's offset alone.  In characteristic
`2` an odd `e` acts as the identity, so `e·(a₀+a_τ) − a₀ = a_τ`: the `x₀`-offset cancels between
the `ω₂`-power and the trailing `x₀⁻¹`, which is the second-order form of the freeze's
"`δ₀` is a `τ`-letter in disguise". -/
theorem heisJetA_deltaZeroW_odd (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : Odd e) :
    (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a = x .tau := by
  have hneg : ∀ w : A, -w = w := fun w => neg_eq_of_add_eq_zero_left (hA₂ w)
  rw [heisF_deltaZeroW t x y E E₂ hwild hτ hE]
  show e • (x (coreLetter h 0) + x .tau) - x (coreLetter h 0) = _
  obtain ⟨m, rfl⟩ := he
  rw [add_nsmul, mul_nsmul', two_nsmul, hA₂, zero_add, one_nsmul, sub_eq_add_neg, hneg,
    show x (coreLetter h 0) + x .tau + x (coreLetter h 0)
      = (x (coreLetter h 0) + x (coreLetter h 0)) + x .tau by abel, hA₂, zero_add]

@[inherit_doc heisJetA_deltaZeroW_odd]
theorem heisJetL_deltaZeroW_odd
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : Odd e) :
    (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l = y .tau := by
  have hL₂ : ∀ f : ElemDual A, f + f = 0 := ElemDual.add_self_eq_zero
  have hneg : ∀ f : ElemDual A, -f = f := fun f => neg_eq_of_add_eq_zero_left (hL₂ f)
  rw [heisF_deltaZeroW t x y E E₂ hwild hτ hE]
  show e • (y (coreLetter h 0) + y .tau) - y (coreLetter h 0) = _
  obtain ⟨m, rfl⟩ := he
  rw [add_nsmul, mul_nsmul', two_nsmul, hL₂, zero_add, one_nsmul, sub_eq_add_neg, hneg,
    show y (coreLetter h 0) + y .tau + y (coreLetter h 0)
      = (y (coreLetter h 0) + y (coreLetter h 0)) + y .tau by abel, hL₂, zero_add]

/-- **The `D`-block's second-order jet is the corrected cross operator applied to `δ₀`'s**:

```
a(D_{r,η}) = L_c · a(δ₀),   λ(D_{r,η}) = L_c · λ(δ₀),   L_c = A⁻¹ + B + B·A⁻¹.
```

The same three conjugators of the compressed spelling `δ₀^A (δ₀ δ₀^A)^{B⁻¹}` that WNP-b sees at
first order (`foxD_dBlockW`), now on **both** jet coordinates — right conjugation applies the
inverse conjugator, so `A` contributes `A⁻¹` and `B⁻¹` contributes `B`, once for each `δ₀`-copy
of the second factor.  Nothing below `δ₀` is unfolded and `A`, `B` are never expanded. -/
theorem heisJet_dBlockW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).a
        = lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a ∧
      (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).l
        = lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l ∧
      ∀ v : A, (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).g • v = v := by
  set δ := heisEvalZ ⇑t x y E E₂ (deltaZeroW h) with hδ
  -- the `δ₀`-denotation and its base
  have hδg : ∀ v : A, δ.g • v = v := by
    rw [hδ, heisF_deltaZeroW t x y E E₂ hwild hτ hE]
    intro v
    have h0 := mem_trivAct.mp (trivAct_coreLetter t hwild 0)
    have hm : ∀ v : A, (t (coreLetter h 0) * t.τ) • v = v := fun v => by rw [mul_smul, hτ, h0]
    show ((t (coreLetter h 0) * t.τ) ^ e * (t (coreLetter h 0))⁻¹) • v = v
    rw [mul_smul, inv_smul_eq_iff.mpr (h0 v).symm]
    exact MulAction.mem_stabilizer_iff.mp
      (pow_mem (MulAction.mem_stabilizer_iff.mpr (hm v)) e)
  set A' := t.σ ^ E d.toZhat with hA'
  set B' := t.σ ^ ((2 : ℤ) ^ r) with hB'
  -- the first factor `δ₀^A`
  have hfst : heisEvalZ ⇑t x y E E₂ (.conj (deltaZeroW h) (aW h d))
      = ⟨A'⁻¹ • δ.a, A'⁻¹ • δ.l, δ.z, conjR δ.g A'⟩ := by
    rw [heisEvalZ_conj, heisF_aW t x y E E₂ hxσ hyσ d, ← hδ,
      heisConjR_of_trivial _ _ hδg]
    refine HeisLift.ext rfl rfl ?_ rfl
    show δ.z + (0 : ElemDual A) δ.a + δ.l 0 = δ.z
    rw [ElemDual.zero_apply, map_zero, add_zero, add_zero]
  have hfstg : ∀ v : A, (conjR δ.g A') • v = v := fun v =>
    mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr hδg) A') v
  -- the inner product `δ₀ · δ₀^A`
  have hinn : heisEvalZ ⇑t x y E E₂
      (PWord.prodList [deltaZeroW h, .conj (deltaZeroW h) (aW h d)])
      = δ * ⟨A'⁻¹ • δ.a, A'⁻¹ • δ.l, δ.z, conjR δ.g A'⟩ := by
    rw [prodList_pair, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one, hfst, ← hδ]
  -- the second factor `(δ₀ δ₀^A)^{B⁻¹}`
  have hsndc : heisEvalZ ⇑t x y E E₂ (.inv (bW h r)) = heisPureBase B'⁻¹ := by
    rw [heisEvalZ_inv, heisF_bW t x y E E₂ hxσ hyσ, ← map_inv]
  rw [dBlockW, prodList_pair, heisEvalZ_mul, heisEvalZ_mul, heisEvalZ_one, mul_one, hfst,
    heisEvalZ_conj, hinn, hsndc,
    heisConjR_of_trivial _ _ (by
      intro v
      show (δ.g * conjR δ.g A') • v = v
      rw [mul_smul, hfstg, hδg])]
  refine ⟨?_, ?_, ?_⟩
  · show A'⁻¹ • δ.a + conjR δ.g A' • ((heisPureBase (A := A) B'⁻¹).g⁻¹ • (δ.a + δ.g • (A'⁻¹ • δ.a)))
      = _
    rw [heisPureBase_g, inv_inv, hfstg, hδg, lcSmul, smul_add, ← mul_smul]
    abel
  · show A'⁻¹ • δ.l + conjR δ.g A' • ((heisPureBase (A := A) B'⁻¹).g⁻¹ • (δ.l + δ.g • (A'⁻¹ • δ.l)))
      = _
    rw [heisPureBase_g, inv_inv, smul_elemDual_of_trivial hfstg,
      smul_elemDual_of_trivial hδg, lcSmul, smul_add, ← mul_smul]
    abel
  · intro v
    show (conjR δ.g A' * conjR (δ * ⟨A'⁻¹ • δ.a, A'⁻¹ • δ.l, δ.z, conjR δ.g A'⟩).g B'⁻¹) • v = v
    rw [mul_smul, hfstg]
    refine mem_trivAct.mp (trivAct_conjR (mem_trivAct.mpr ?_) B'⁻¹) v
    intro w
    show (δ.g * conjR δ.g A') • w = w
    rw [mul_smul, hfstg, hδg]

/-- **Factor 5, the lane's headline row: the correction block `E_{r,η}` is jet-zero central with
value the `L_c`-twisted pairing**

```
β(E_{r,η}) = (L_c·λ(δ₀))(a₁) + y₁(L_c·a(δ₀)),        L_c = A⁻¹ + B + B·A⁻¹.
```

This is the exact point at which the two lanes' findings meet.  At **first** order this block is
identically zero (WNP-b's `foxD_eBlockW`: `L_c` is fully present in `D_{r,η}` and then annihilated
by the commutator with `x₁`); at **second** order the commutator no longer annihilates — it
*pairs* — and what it pairs is precisely `L_c` applied to the `δ₀`-jet.  Gate D is blind to the
S3.2 correction and the Stokes level is not: this row is where the blindness stops.  It is the
cup-level shadow of NC5's `b_q(c₁, L_c c₀)`. -/
theorem heisF_eBlockW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v)
    (hτ : ∀ v : A, t.τ • v = v) (hxσ : x .sigma = 0) (hyσ : y .sigma = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (d : EtaData) :
    heisEvalZ ⇑t x y E E₂ (eBlockW h r d)
      = ⟨0, 0,
          lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l
              (x (coreLetter h 1))
            + y (coreLetter h 1)
                (lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a),
          commR (heisEvalZ ⇑t x y E E₂ (dBlockW h r d)).g (t (coreLetter h 1))⟩ := by
  obtain ⟨ha, hl, hg⟩ := heisJet_dBlockW t x y E E₂ hwild hτ hxσ hyσ hE d (r := r)
  rw [eBlockW, heisEvalZ_comm, heisEvalZ_gen,
    heisCommR_of_trivial _ _ hg (mem_trivAct.mp (trivAct_coreLetter t hwild 1)), ha, hl]

/-- **Factor 6, membership** — the handle block is jet-zero at every handle count. -/
theorem heisF_handlesW_mem (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (handlesW h) ∈ heisJetZero A C := by
  rw [handlesW]
  refine (heisEvalZ_prodList_jetZero ⇑t x y E E₂ ?_).1
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
      (mem_trivAct.mp (trivAct_handleV t hwild j))]
  exact ⟨rfl, rfl⟩

/-- **Factor 6, value** — `H_h` contributes exactly the `h` identity-operator hyperbolic planes
`Σ_j (y_{u_j}(a_{v_j}) + y_{v_j}(a_{u_j}))`: no `S`-, `A`- or `B`-operator touches the handle
block, at any handle count.  The "⊕ h hyperbolic planes" half of the block structure, identical
to the compact row's. -/
theorem heisF_handlesW_z (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) :
    (heisEvalZ ⇑t x y E E₂ (handlesW h)).z
      = ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 + 2 * h))),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
      heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
        (mem_trivAct.mp (trivAct_handleV t hwild j))]
    exact ⟨rfl, rfl⟩
  rw [handlesW, (heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2, List.map_map,
    Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show (heisEvalZ ⇑t x y E E₂ (.comm (.gen (handleU j)) (.gen (handleV j)))).z = _
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (trivAct_handleU t hwild j))
      (mem_trivAct.mp (trivAct_handleV t hwild j))]

/-! ### The assembled row

Three of the six factors have **nonzero first jet** on this row (the compact row has one), so
the assembly carries genuine cross terms: the front block's operator `A⁻¹ + 1` sees the whole
boundary jet.  `npcBoundaryJet` names that offset. -/

/-- **The boundary block's total primal jet** `a(x₂^{-g}) + a((x₂τ)^{ω₂})` — the offset the front
block's operator `A⁻¹ + 1` is paired against in the assembled row. -/
noncomputable def npcBoundaryJet (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (r e : ℕ) : A :=
  -((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • x (coreLetter h 2)) + e • (x (coreLetter h 2) + x .tau)

/-- **The corrected noncompact-`N` second-order (Stokes) row, unramified class, exact in the
resolver.**

Block reading, in the order the factors occur:

* the **`x₀`-diagonal** `y₀(A⁻¹a₀)` — and it is a *twisted* diagonal, not `y₀(a₀)`: the leading
  power's diagonal `y₀(a₀)` cancels against the front commutator's, leaving only the
  `A⁻¹`-twisted one.  This is the Stokes-level twin of NC5's `q(c₀)`-cancellation, i.e. of the
  hypothesis `α ≥ 2`, and it is why the endpoint's diagonal is `Q₀` and not `q`;
* the **boundary block** on `(x₁, x₂, τ)` with the `e`- and `C(e,2)`-sensitivities displayed and
  the operator `B = S^{2^r}` where the compact row has `S`;
* the **front-block cross term** `y₀((A + 1)·bnd)` — the second-order shadow of WNP-b's new
  `x₀`-column `A⁻¹ + 1`, paired against the boundary jet;
* the **correction block** `L_c(λ_{δ₀})(a₁) + y₁(L_c a_{δ₀})` — invisible at first order, and
  the only place the S3.2 correction appears;
* the `h` **identity-operator hyperbolic planes**, untouched by any operator, as on every row of
  the campaign. -/
theorem heisZ_npc_unram (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hα : 2 ≤ α)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (npcW α r h d)).z
      = y (coreLetter h 0) ((t.σ ^ E d.toZhat)⁻¹ • x (coreLetter h 0))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1))
            + y (coreLetter h 2) (x (coreLetter h 2)))
        + (e • y (coreLetter h 2) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 2) + y .tau) (x (coreLetter h 2) + x .tau)))
        + y (coreLetter h 2)
            (t.σ ^ ((2 : ℤ) ^ r) • (e • (x (coreLetter h 2) + x .tau)))
        + (y (coreLetter h 0) ((t.σ ^ E d.toZhat) • npcBoundaryJet t x r e)
            + y (coreLetter h 0) (npcBoundaryJet t x r e))
        + (lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).l
              (x (coreLetter h 1))
            + y (coreLetter h 1)
                (lcSmul t.σ (E d.toZhat) r (heisEvalZ ⇑t x y E E₂ (deltaZeroW h)).a))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have e1 := heisF_leadingPow t x y E E₂ hA₂ hwild hα (α := α)
  have e2 := heisF_commX0A t x y E E₂ hwild hxσ hyσ d
  have e3 := heisF_invConjX2G t x y E E₂ hwild hxσ hyσ (r := r)
  have e4 := heisF_omega2Block t x y E E₂ 2 hwild hτ hE
  have e5 := heisF_eBlockW t x y E E₂ hwild hτ hxσ hyσ hE d (r := r)
  have h6mem := heisF_handlesW_mem t x y E E₂ hwild
  have h6z := heisF_handlesW_z t x y E E₂ hwild
  rw [npcW, heisEvalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set P1 := heisEvalZ ⇑t x y E E₂
    (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α)) with hP1
  set P2 := heisEvalZ ⇑t x y E E₂ (.comm (.gen (coreLetter h 0)) (aW h d)) with hP2
  set P3 := heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 2))
    (PWord.prodList [.gen (coreLetter h 1), bW h r]))) with hP3
  set P4 := heisEvalZ ⇑t x y E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau])) with hP4
  set P5 := heisEvalZ ⇑t x y E E₂ (eBlockW h r d) with hP5
  set P6 := heisEvalZ ⇑t x y E E₂ (handlesW h) with hP6
  have h1jz : P1 ∈ heisJetZero A C := by rw [e1]; exact ⟨rfl, rfl⟩
  have h5jz : P5 ∈ heisJetZero A C := by rw [e5]; exact ⟨rfl, rfl⟩
  have h2g : ∀ v : A, P2.g • v = v := by
    rw [e2]
    exact fun v => mem_trivAct.mp
      (trivAct_commR_left (trivAct_coreLetter t hwild 0) (t.σ ^ E d.toZhat)) v
  have h3g : ∀ v : A, P3.g • v = v := by
    rw [e3]
    exact fun v => mem_trivAct.mp
      (inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _)) v
  have h56a : (P5 * P6).a = 0 := by
    rw [HeisLift.mul_a, h5jz.1, h6mem.1, smul_zero, add_zero]
  have h56z : (P5 * P6).z = P5.z + P6.z := heisJetZero_mul_z h5jz
  have h456a : (P4 * (P5 * P6)).a = P4.a := by
    rw [HeisLift.mul_a, h56a, smul_zero, add_zero]
  have h456z : (P4 * (P5 * P6)).z = P4.z + (P5.z + P6.z) := by
    rw [heisMul_z_of_a_eq_zero _ _ h56a, h56z]
  have h3456a : (P3 * (P4 * (P5 * P6))).a = P3.a + P4.a := by
    rw [HeisLift.mul_a, h456a, h3g]
  have h3456z : (P3 * (P4 * (P5 * P6))).z = P3.z + (P4.z + (P5.z + P6.z)) + P3.l P4.a := by
    rw [HeisLift.mul_z, h456z, h456a, h3g]
  have h23456z : (P2 * (P3 * (P4 * (P5 * P6)))).z
      = P2.z + (P3.z + (P4.z + (P5.z + P6.z)) + P3.l P4.a) + P2.l (P3.a + P4.a) := by
    rw [HeisLift.mul_z, h3456z, h3456a, h2g]
  rw [heisJetZero_mul_z h1jz, h23456z, e1, e2, e3, e4, e5, hP6, h6z]
  dsimp only
  rw [npcBoundaryJet, ElemDual.neg_apply, ElemDual.smul_apply, inv_inv, CharTwo.neg_eq,
    ElemDual.sub_apply, ElemDual.smul_apply, inv_inv]
  simp only [ElemDual.add_apply, map_add, map_neg, CharTwo.neg_eq]
  abel_nf
  simp only [two_zsmul_zmod2, neg_one_zsmul_zmod2, zero_add]

/-- **The certificate form at the honest resolver class** `e ≡ 1 (mod 4)` — the class the genuine
`ω₂` inhabits on every finite `2`-group target.  The `C(e,2)`-block dies and every `e •`
disappears; in particular the `δ₀`-jet collapses to the `τ`-letter's offsets, so the correction
block reads

```
(L_c·y_τ)(a₁) + y₁(L_c·a_τ)
```

— the whole S3.2 correction, at second order, as a pairing of the `τ`-offsets through `L_c`. -/
theorem heisZ_npc_res_one (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hα : 2 ≤ α)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (npcW α r h d)).z
      = y (coreLetter h 0) ((t.σ ^ E d.toZhat)⁻¹ • x (coreLetter h 0))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1))
            + y (coreLetter h 2) (x (coreLetter h 2)))
        + y (coreLetter h 2) (x .tau)
        + y (coreLetter h 2) (t.σ ^ ((2 : ℤ) ^ r) • (x (coreLetter h 2) + x .tau))
        + (y (coreLetter h 0) ((t.σ ^ E d.toZhat) • npcBoundaryJet t x r 1)
            + y (coreLetter h 0) (npcBoundaryJet t x r 1))
        + (lcSmul t.σ (E d.toZhat) r (y .tau) (x (coreLetter h 1))
            + y (coreLetter h 1) (lcSmul t.σ (E d.toZhat) r (x .tau)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hodd := odd_of_mod_four_eq_one he
  have hone : e • (x (coreLetter h 2) + x .tau) = x (coreLetter h 2) + x .tau := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, add_nsmul, mul_nsmul', two_nsmul, hA₂, zero_add, one_nsmul]
  have hbnd : npcBoundaryJet t x r e = npcBoundaryJet t x r 1 := by
    rw [npcBoundaryJet, npcBoundaryJet, one_nsmul, hone]
  rw [heisZ_npc_unram t x y E E₂ hA₂ hwild hτ hxσ hyσ hα hE d,
    heisJetA_deltaZeroW_odd t x y E E₂ hA₂ hwild hτ hE hodd,
    heisJetL_deltaZeroW_odd t x y E E₂ hwild hτ hE hodd, hbnd,
    nsmul_zmod2_odd hodd, nsmul_zmod2_even (choose_two_even_of_mod_four he), hone]
  abel_nf

/-- **The scalar (split) collapse**: with `σ` also acting trivially, `A = B = 1` and `L_c`
degenerates to the **identity** (`lcSmul_of_trivial`), so the row is the compact row's scalar
reading plus one extra hyperbolic plane — the `(τ, x₁)` pairing contributed by the correction
block.  "The scalar module separates nothing" survives the correction in the strong sense that
the *operator* disappears; what does **not** disappear is the correction block's pairing, which
is exactly why the separating gate has to be a **twisted** module (§8). -/
theorem heisZ_npc_scalar (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hσ : ∀ v : A, t.σ • v = v) (hxσ : x .sigma = 0) (hyσ : y .sigma = 0) (hα : 2 ≤ α)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (d : EtaData) :
    (heisEvalZ ⇑t x y E E₂ (npcW α r h d)).z
      = y (coreLetter h 0) (x (coreLetter h 0))
        + (y (coreLetter h 1) (x (coreLetter h 2)) + y (coreLetter h 2) (x (coreLetter h 1)))
        + (y .tau (x (coreLetter h 1)) + y (coreLetter h 1) (x .tau))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hzp : ∀ (m : ℤ) (v : A), (t.σ ^ m) • v = v := fun m v =>
    MulAction.mem_stabilizer_iff.mp (zpow_mem (MulAction.mem_stabilizer_iff.mpr (hσ v)) m)
  have hzpi : ∀ (m : ℤ) (v : A), (t.σ ^ m)⁻¹ • v = v := fun m v =>
    inv_smul_eq_iff.mpr (hzp m v).symm
  have hL₂ : ∀ f : ElemDual A, f + f = 0 := ElemDual.add_self_eq_zero
  have hbnd : npcBoundaryJet t x r 1 = x .tau := by
    rw [npcBoundaryJet, one_nsmul, hzpi,
      show -x (coreLetter h 2) + (x (coreLetter h 2) + x .tau) = x .tau by abel]
  rw [heisZ_npc_res_one t x y E E₂ hA₂ hwild hτ hxσ hyσ hα hE he d, hzpi, hzp, hbnd,
    lcSmul_of_trivial hA₂ hσ, lcSmul_of_trivial hL₂ (fun f => smul_elemDual_of_trivial hσ f),
    hzp, map_add]
  abel_nf
  simp only [two_zsmul_zmod2, zero_add]

end StokesRows

/-! ## §3. The Hessian certificate: the corrected endpoint, literally

WW4's `npcShape_certificate` certifies the **shape** `Q₀(c₀) + b_q(c₁, L_c c₀)` with an abstract
invertible cross operator, and its docstring names the literal identification as WNP-c's, blocked
there by the module rule (`NpcJet` is a plain-import file).  This section performs it: the
abstract `Lc` is replaced by NC2's `lcOp`, the abstract `Q₀` by NC2's `npcQ0`, and the endpoint
polynomial is proved to be the **evaluated word** through WNP-b's bridge
`npc_cross_operators_npcW` (and NC6's `_handles_std` at general `h`).

Nothing here re-derives jet content: `npc_cross_operators` is cited, never re-proved. -/

section Hessian

open GQ2.QuadraticFp2 NpcJet

section LcOpHom

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **NC2's `lcOp` as an additive map** — the `V →+ V` datum WW4's change of variables
`(c₀, c₁) ↦ (L_c c₀, c₁)` consumes.  `lcOp` is a sum of three module actions, so additivity is
immediate; this is the only packaging step between the NC lane's operator and the certificate
interface. -/
noncomputable def lcOpHom (s : C) (η : ℤ_[2]) (r : ℕ) : V →+ V where
  toFun := lcOp s η r
  map_zero' := by simp only [lcOp, smul_zero, add_zero]
  map_add' v w := by
    simp only [lcOp, smul_add]
    abel

@[simp] theorem lcOpHom_apply (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) :
    lcOpHom s η r v = lcOp s η r v := rfl

/-- The same map as an endomorphism-monoid element, so that `IsUnit` is available (WNP-b's
`oneSubInvEnd` idiom). -/
noncomputable def lcOpEnd (s : C) (η : ℤ_[2]) (r : ℕ) : AddMonoid.End V := lcOpHom s η r

@[simp] theorem lcOpEnd_apply (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) :
    lcOpEnd s η r v = lcOp s η r v := rfl

/-- **`L_c` degenerates to the identity when the `B`-element is trivial** (`σ^{2^r} = 1` on the
module): `L_c = A⁻¹ + 1 + A⁻¹ = 1`.  Together with NC5's `lcOp_eq_draft_of_eq_one` (the `A = 1`
degeneration, where `L_c = A⁻¹ = 1` as well) this is the pair of *free* invertibility cases. -/
theorem lcOp_of_B_eq_one (hV2 : ∀ v : V, v + v = 0) (s : C) (η : ℤ_[2]) (r : ℕ)
    (hB : s ^ (2 ^ r) = 1) (v : V) : lcOp s η r v = v := by
  rw [lcOp, hB, one_smul, one_mul,
    show (s ^ᶻ etaHatZ η)⁻¹ • v + v + (s ^ᶻ etaHatZ η)⁻¹ • v
      = ((s ^ᶻ etaHatZ η)⁻¹ • v + (s ^ᶻ etaHatZ η)⁻¹ • v) + v by abel, hV2, zero_add]

/-! ### The per-module invertibility of `L_c` — the NC lane's standing residual

NC5's scope note: *"invertibility of `L_c` per module class genuinely varies with the module and
belongs with WNP-c's Fox/normal-form clauses; on a concrete battery module it is a `decide`."*
Here is the general criterion; the battery is §7. -/

/-- **The general per-module criterion**: on a finite module, `L_c` is invertible exactly when it
has trivial kernel.  This is the honest general statement — unlike the compact lane's
`isUnit_oneSubSInvEnd_iff` (and WNP-b's first-order `isUnit_oneSubInvEnd_iff`, whose right-hand
side is the *geometric* condition `V^c = 0`), the corrected `L_c = 1 + (1+A⁻¹)(1+B)` admits no
uniform fixed-point description: it is a sum of three group actions and which of them cancel
depends on the module.  The battery shows the dependence is real. -/
theorem isUnit_lcOpEnd_iff [Finite V] (s : C) (η : ℤ_[2]) (r : ℕ) :
    IsUnit (lcOpEnd (V := V) s η r) ↔ ∀ v : V, lcOp s η r v = 0 → v = 0 := by
  have hinj_of : (∀ v : V, lcOp s η r v = 0 → v = 0) →
      Function.Injective (lcOpEnd (V := V) s η r) := by
    intro hker a b hab
    have h0 : (lcOpEnd (V := V) s η r) (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker _ h0)
  constructor
  · intro hu v hv
    have hinj : Function.Injective (lcOpEnd (V := V) s η r) := injective_of_isUnit hu
    refine hinj ?_
    show lcOp s η r v = lcOp s η r 0
    rw [hv]
    exact ((lcOpHom s η r).map_zero (M := V)).symm
  · intro hker
    have hbij : Function.Bijective (lcOpEnd (V := V) s η r) :=
      Finite.injective_iff_bijective.mp (hinj_of hker)
    refine isUnit_iff_exists.mpr
      ⟨(AddEquiv.ofBijective (lcOpEnd (V := V) s η r) hbij).symm.toAddMonoidHom, ?_, ?_⟩
    · exact AddMonoidHom.ext fun v =>
        (AddEquiv.ofBijective (lcOpEnd (V := V) s η r) hbij).apply_symm_apply v
    · exact AddMonoidHom.ext fun v =>
        (AddEquiv.ofBijective (lcOpEnd (V := V) s η r) hbij).symm_apply_apply v

/-- **The two-sided inverse witness**, extracted from the kernel criterion: this is what
discharges `npcShape_certificate`'s `hML`/`hLM`, so a consumer only ever has to check
`ker L_c = 0` — on a battery module, one `decide`. -/
theorem exists_lcOp_inverse [Finite V] (s : C) (η : ℤ_[2]) (r : ℕ)
    (hker : ∀ v : V, lcOp s η r v = 0 → v = 0) :
    ∃ Mc : V →+ V, (∀ v, Mc (lcOpHom s η r v) = v) ∧ (∀ v, lcOpHom s η r (Mc v) = v) := by
  have hinj : Function.Injective (lcOpHom s η r : V →+ V) := by
    intro a b hab
    have h0 : (lcOpHom s η r : V →+ V) (a - b) = 0 := by rw [map_sub, hab, sub_self]
    exact sub_eq_zero.mp (hker _ h0)
  have hbij : Function.Bijective (lcOpHom s η r : V →+ V) :=
    Finite.injective_iff_bijective.mp hinj
  exact ⟨(AddEquiv.ofBijective (lcOpHom s η r : V →+ V) hbij).symm.toAddMonoidHom,
    fun v => (AddEquiv.ofBijective (lcOpHom s η r : V →+ V) hbij).symm_apply_apply v,
    fun v => (AddEquiv.ofBijective (lcOpHom s η r : V →+ V) hbij).apply_symm_apply v⟩

end LcOpHom

section Certificate

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  [Module (ZMod 2) V] [Fintype V] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The corrected noncompact-`N` Hessian certificate — the literal identification.**

WW4's `npcShape_certificate` with its two abstract parameters replaced by the NC lane's objects:
`Q₀ := npcQ0 dat s η` and `Lc := lcOp s η r`.  The change of variables is
`(c₀, c₁) ↦ (L_c c₀, c₁)` with the two-sided inverse witness supplied by the caller (in practice
by `exists_lcOp_inverse` from a one-line kernel `decide`, §7's battery), and the endpoint
polynomial is `fun (c₀,c₁) ↦ Q₀(c₀) + b_q(c₁, L_c c₀)` — the value of the frozen word, by
`npc_word_eq_certQ` below.

`hQ₀` (quadraticity of the twisted diagonal `Q₀(v) = f(v, A⁻¹v) + m_{A⁻¹}(v)`) is a certificate
**input**, exactly as in WW4's shape: it is a statement about the factor-set datum, not about the
word, and it is discharged concretely on the battery module (`pin_isQuadratic_npcQ0`). -/
noncomputable def npcHessianCertificate (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (s : C) (η : ℤ_[2]) (r : ℕ) (hQ₀ : IsQuadraticFp2 (npcQ0 dat s η))
    (Mc : V →+ V) (hML : ∀ v, Mc (lcOpHom s η r v) = v)
    (hLM : ∀ v, lcOpHom s η r (Mc v) = v) {d : ℕ} (hcard : Fintype.card V = 2 ^ d) :
    HessianCertificate dat (fun v ↦ npcQ0 dat s η (Mc v))
      (fun p : V × V ↦ npcQ0 dat s η p.1 + polar q p.2 (lcOp s η r p.1))
      (plusFormD (fun v ↦ npcQ0 dat s η (Mc v)) q)
      (AddMonoidHom.inl V V) (AddMonoidHom.inr V V) :=
  npcShape_certificate dat hdat hq hns (npcQ0 dat s η) hQ₀ (lcOpHom s η r) Mc hML hLM hcard

omit [Module (ZMod 2) V] in
/-- **The word-side equation, `h = 0`**: the evaluated class-two value of the frozen corrected
word, as a function of the Gate-E offsets, **is** the certificate's endpoint polynomial.

This is pure assembly: the content is NC5's `npc_cross_operators`, transported onto the
hash-pinned tree by WNP-b's `npc_cross_operators_npcW`, and all that is added here is the
`funext` turning the pointwise identity into the equality of functions the certificate interface
wants. -/
theorem npc_word_eq_certQ (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) :
    (fun p : V × V ↦ ((npcMarking dat hdat s u p.1 p.2).eval (npcW α r 0 e)).fib)
      = fun p : V × V ↦ npcQ0 dat s e.toPadic p.1
          + polar q p.2 (lcOp s e.toPadic r p.1) :=
  funext fun p => npc_cross_operators_npcW dat hdat hV2 s u hu hVu α hα r e p.1 p.2

/-- **The Gauss residue of the *word's* evaluated Hessian is the certificate's `G0`** — WW4's
`endpoint_gaussSum` consumed at the corrected word.  The compact lane's `nCompact_word_gaussSum`,
one freeze row over, with the identity CoV replaced by the `L_c` CoV. -/
theorem npc_word_gaussSum (hV2 : ∀ v : V, v + v = 0) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData)
    (hQ₀ : IsQuadraticFp2 (npcQ0 dat s e.toPadic)) (Mc : V →+ V)
    (hML : ∀ v, Mc (lcOpHom s e.toPadic r v) = v)
    (hLM : ∀ v, lcOpHom s e.toPadic r (Mc v) = v) {d : ℕ}
    (hcard : Fintype.card V = 2 ^ d) :
    gaussSum (fun p : V × V ↦ ((npcMarking dat hdat s u p.1 p.2).eval (npcW α r 0 e)).fib)
      = (npcHessianCertificate dat hdat hq hns s e.toPadic r hQ₀ Mc hML hLM
          hcard).affinePhase.G0 := by
  rw [npc_word_eq_certQ dat hdat hV2 s u hu hVu α hα r e]
  exact (npcHessianCertificate dat hdat hq hns s e.toPadic r hQ₀ Mc hML hLM
    hcard).endpoint_gaussSum

omit [Module (ZMod 2) V] in
/-- **The handle tail, general `h`**: NC6's `npc_cross_operators_handles_std` says the genus-`h`
word adds `Σ_{j<h} b_q(e_{3+2j}, e_{4+2j})` to the same core.  Stated here as the certificate
lane's consumption of it — the core is `npcHessianCertificate`'s endpoint at `(e 0, e 1)` and the
tail is a sum of hyperbolic planes, so the `h`-handle endpoint is `Q_core ⊕ (h hyperbolic
planes)`, exactly as on the compact row.  The route is NC6's, never a cast on `npcWordH`. -/
theorem npc_word_handles_eq_certQ (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]) (h : ℕ)
    (ev : ℕ → V) (he2 : ev 2 = 0) :
    ((npcMarkingH dat hdat (2 * h) s u ev).eval
        (npcWordH (2 * h) α r η (fun j ↦ ⟨(3 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩)
          (fun j ↦ ⟨(4 + 2 * j) % (2 * h + 3), Nat.mod_lt _ (by omega)⟩) h)).fib
      = (fun p : V × V ↦ npcQ0 dat s η p.1 + polar q p.2 (lcOp s η r p.1)) (ev 0, ev 1)
        + ∑ j ∈ Finset.range h, polar q (ev (3 + 2 * j)) (ev (4 + 2 * j)) :=
  npc_cross_operators_handles_std dat hdat hV2 s u hu hVu α hα r η h ev he2

end Certificate

end Hessian

/-! ## §4. The `L_c` battery: per-module invertibility, decided

NC6's concrete carrier — `C = ℤ/3` acting on `𝔽₂²` by the companion matrix of `x² + x + 1`,
with the anisotropic form `pinQ` and the factor set `pinDat` — is the battery module.  On it
every hypothesis of the NC headline is discharged by `decide`, and so is the question NC5 left
open.  The answer is a genuine dichotomy, and the parameter it turns on is the one the *jet*
identity never consumes:

* at **`r = 1`** (and every odd `r`) `L_c = A⁻¹ + B + B·A⁻¹ = g` is the group action itself —
  invertible (`isUnit_lcOpEnd_pin_one`);
* at **`r = 0`** `A = B = g` and `L_c = g² + g + 1 = 0` — the **zero** operator, by the minimal
  polynomial of the companion matrix.  So `L_c` is not merely non-invertible there, it is
  identically zero (`pin_lcOp_zero`), and the certificate's change of variables does not exist.

`r = 0` is exactly the excluded case: `r ≥ 1` is the *word row's* noncompact side condition,
which NC5 deliberately does not consume (`npc_cross_operators` holds for all `r : ℕ`).  This
battery is where that side condition becomes load-bearing again — it is what per-module
invertibility needs, and the honest statement is that invertibility is a property of the pair
(module, `r`), not of the operator alone. -/

section Battery

open GQ2.QuadraticFp2 NpcJet

/-- The `ZMod 2`-module structure on the battery carrier (local — WW3's non-exporting idiom;
NC6 declares the additive and finiteness instances, this is the one the phase interface adds). -/
local instance : Module (ZMod 2) PinV := inferInstanceAs (Module (ZMod 2) (ZMod 2 × ZMod 2))

/-- **`L_c` is the zero operator at `r = 0`** on the battery module: `A = B = g` there, and
`g² + g + 1 = 0` is the minimal polynomial of the order-3 companion matrix.  The corrected
operator degenerates completely — the draft's `L_c = A⁻¹ = g²` does not. -/
theorem pin_lcOp_zero (η : ℤ_[2]) (v : PinV) : lcOp pinG η 0 v = 0 := by
  rw [lcOp, pinA]
  revert v
  decide

/-- **`L_c` is invertible on the battery module at `r = 1`** — the kernel criterion discharged by
kernel `decide` through NC6's closed form `pin_lcOp` (`L_c = g`). -/
theorem isUnit_lcOpEnd_pin_one (η : ℤ_[2]) : IsUnit (lcOpEnd (V := PinV) pinG η 1) := by
  refine (isUnit_lcOpEnd_iff pinG η 1).mpr fun v hv => ?_
  rw [pin_lcOp] at hv
  revert v
  decide

/-- **`L_c` is *not* invertible on the battery module at `r = 0`** — the negative half of the
dichotomy, and the reason the word row carries `r ≥ 1`. -/
theorem not_isUnit_lcOpEnd_pin_zero (η : ℤ_[2]) : ¬ IsUnit (lcOpEnd (V := PinV) pinG η 0) := by
  intro hu
  have h := (isUnit_lcOpEnd_iff pinG η 0).mp hu ((1, 0) : PinV) (pin_lcOp_zero η _)
  exact absurd h (by decide)

/-- The two-sided inverse of `L_c` on the battery at `r = 1`, in the shape the certificate's
change of variables consumes. -/
theorem exists_lcOp_inverse_pin_one (η : ℤ_[2]) :
    ∃ Mc : PinV →+ PinV, (∀ v, Mc (lcOpHom pinG η 1 v) = v) ∧
      (∀ v, lcOpHom pinG η 1 (Mc v) = v) := by
  refine exists_lcOp_inverse pinG η 1 fun v hv => ?_
  rw [pin_lcOp] at hv
  revert v
  decide

/-! ### The battery's quadratic data

The three inputs `npcHessianCertificate` cannot derive from the word — quadraticity of the
twisted diagonal `Q₀`, quadraticity and nonsingularity of `q` — are decided here.  `Q₀` is the
one that matters: `Q₀(v) = f(v, A⁻¹v) + m_{A⁻¹}(v)` is a statement about the *factor set*, and
WW4's shape takes it as an input for exactly that reason. -/

/-- The battery form is quadratic. -/
theorem pin_isQuadratic_pinQ : IsQuadraticFp2 pinQ := by
  constructor <;> decide

/-- The battery form is nonsingular (it is anisotropic). -/
theorem pin_nonsingular_pinQ : Nonsingular pinQ := by
  show ∀ v : PinV, v ≠ 0 → ∃ w, polar pinQ v w ≠ 0
  decide

/-- **The twisted diagonal is quadratic on the battery** — `Q₀(v) = f(v, g⁻¹v)` there
(`pin_npcQ0`, the correction `m` being zero), decided over the four points.  This discharges the
one certificate input that is about the factor-set datum rather than the word. -/
theorem pin_isQuadratic_npcQ0 (η : ℤ_[2]) : IsQuadraticFp2 (npcQ0 pinDat pinG η) := by
  rw [show npcQ0 pinDat pinG η = fun v : PinV => pinF v (pinG⁻¹ • v) from funext (pin_npcQ0 η)]
  constructor <;> decide

/-- The battery module has `2²` points. -/
theorem pin_card : Fintype.card PinV = 2 ^ 2 := by decide

/-! ### The `(α, r, η) = (2, 1, 1)` instance, end to end

The frozen harness row (`N-noncompact-alpha2-r1-eta1_1-h0-v001`, digest `08b7742caf3a34f8…`,
`F5` counts `6/1568/120` over `(S₃, D₈, A₄)`) at the battery module: word value, Hessian
certificate, and the Gauss residue, with **every** hypothesis discharged. -/

/-- **The Hessian certificate of the corrected noncompact-`N` row, fully concrete.**  Every input
is discharged: `hq`/`hns` by `decide`, `hQ₀` by `decide`, the change of variables by the battery's
`L_c = g`.  This is packet Def. 9.1 item (6) for freeze row 3 at a module where nothing is
hypothetical. -/
noncomputable def pinNpcHessianCertificate (η : ℤ_[2]) :
    HessianCertificate pinDat
      (fun v ↦ npcQ0 pinDat pinG η ((exists_lcOp_inverse_pin_one η).choose v))
      (fun p : PinV × PinV ↦ npcQ0 pinDat pinG η p.1 + polar pinQ p.2 (lcOp pinG η 1 p.1))
      (plusFormD (fun v ↦ npcQ0 pinDat pinG η ((exists_lcOp_inverse_pin_one η).choose v)) pinQ)
      (AddMonoidHom.inl PinV PinV) (AddMonoidHom.inr PinV PinV) :=
  npcHessianCertificate pinDat pinHdat pin_isQuadratic_pinQ pin_nonsingular_pinQ pinG η 1
    (pin_isQuadratic_npcQ0 η) _ (exists_lcOp_inverse_pin_one η).choose_spec.1
    (exists_lcOp_inverse_pin_one η).choose_spec.2 pin_card

/-- **The pinned word lands on the pinned certificate's endpoint** — `npc_word_eq_certQ` at the
battery, `(α, r) = (2, 1)`.  Both sides are now concrete functions of `(c₀, c₁) ∈ 𝔽₂² × 𝔽₂²`. -/
theorem pin_npc_word_eq_certQ (e : EtaData) :
    (fun p : PinV × PinV ↦
        ((npcMarking pinDat pinHdat pinG pinG p.1 p.2).eval (npcW 2 1 0 e)).fib)
      = fun p : PinV × PinV ↦ npcQ0 pinDat pinG e.toPadic p.1
          + polar pinQ p.2 (lcOp pinG e.toPadic 1 p.1) :=
  npc_word_eq_certQ pinDat pinHdat pinV2 pinG pinG (pinOddOrder pinG) pinVu 2 le_rfl 1 e

/-- **The pinned Gauss residue**: the Gauss sum of the *word's* evaluated Hessian is the
certificate's `G0 = 2²`.  End of the chain — word ⟶ jet identity ⟶ change of variables ⟶ plus
form ⟶ Gauss residue — with no hypothesis left standing. -/
theorem pin_npc_word_gaussSum (η : ℤ_[2]) :
    (pinNpcHessianCertificate η).affinePhase.G0 = 2 ^ 2 :=
  one_mul _

end Battery

end GQ2.Dyadic.Certificates.Npc
