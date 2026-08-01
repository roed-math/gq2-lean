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

end StokesRows

end GQ2.Dyadic.Certificates.Npc
