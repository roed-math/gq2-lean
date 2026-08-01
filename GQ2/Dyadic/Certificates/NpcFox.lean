/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.Word.FoxCert
import GQ2.Dyadic.NpcJet.Handles

/-!
# Dyadic campaign, ticket WNP-b: the Fox certificate of the corrected noncompact-`N` word

Certificate layer of the procyclic-`N` lane, sitting on WNP-a's word
(`GQ2/Dyadic/Words/Npc.lean`), WW1's Fox evaluator (`GQ2/Dyadic/Word/Fox.lean`) and WW2's
atom-generic certificate grammar (`GQ2/Dyadic/Word/FoxCert.lean`).  Carries packet Def. 9.1
items (3)–(4) for row 3 of the R5 selection freeze — the corrected word

```
R_{N,α,r,η} = x₀^{2+2^α} [x₀,A] · x₂^{-g} (x₂τ)^{ω₂} · E_{r,η} · H_h,
A = σ^{η̂},  B = σ^{2^r},  g = x₁σ^{2^r},  E_{r,η} = [D_{r,η}, x₁],
D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹}
```

symbolically in **all** `r` and `η` (the operator data is a function of `r`; `η` lives in the
interpretation), plus the `(α,r,η) = (2,1,1)` and `(2,1,−1/5)` instances.

(Module docstring finalized at the end of the ticket — see the axiom-state section there.)
-/

namespace GQ2.Dyadic.Certificates.Npc

open GQ2.FoxH GQ2.Dyadic.Words.Npc

/-! ## §0. Micro-toolkit (duplicated from WN0-b's `N0Fox.lean`, dedup ledger in the module
docstring)

Per the WNP-a convention, this lane file does **not** import the compact lane's
`Certificates/N0Fox.lean`: the two files are independently owned, and the price is the
duplication — in this nested namespace — of the four mathlib-shaped micro-lemmas below plus the
tame-relator toolkit of §5.  All of them are WAH/WWH-style hoist candidates; the ledger is in
the module docstring. -/

/-- An even multiple of a `2`-torsion element vanishes. -/
theorem even_nsmul_eq_zero {V : Type*} [AddCommGroup V] (hV₂ : ∀ v : V, v + v = 0) {k : ℕ}
    (hk : Even k) (v : V) : k • v = 0 := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul]
  exact hV₂ _

/-- `p_α = 2 + 2^α` is even for `α ≥ 1` — read off WNP-a's spelling-discipline lemma
`Words.Npc.two_add_two_pow`.  Same device as the compact row: the displayed spelling `2 + 2^α`
is opaque, `2(1 + 2^{α−1})` displays the parity. -/
theorem even_two_add_two_pow {α : ℕ} (hα : 1 ≤ α) : Even (2 + 2 ^ α) :=
  ⟨1 + 2 ^ (α - 1), by rw [two_add_two_pow α hα]; ring⟩

/-- Over a `2`-torsion module every element is its own negative. -/
theorem neg_eq_self {V : Type*} [AddCommGroup V] (hV₂ : ∀ v : V, v + v = 0) (v : V) : -v = v :=
  neg_eq_of_add_eq_zero_left (hV₂ v)

/-- A unit of the endomorphism ring is injective. -/
theorem injective_of_isUnit {W : Type*} [AddCommGroup W] {f : AddMonoid.End W} (hf : IsUnit f) :
    Function.Injective f := by
  obtain ⟨u, rfl⟩ := hf
  intro x y hxy
  have h : ((↑u⁻¹ * ↑u : AddMonoid.End W)) x = ((↑u⁻¹ * ↑u : AddMonoid.End W)) y := by
    show (↑u⁻¹ : AddMonoid.End W) (((↑u : AddMonoid.End W)) x)
        = (↑u⁻¹ : AddMonoid.End W) (((↑u : AddMonoid.End W)) y)
    rw [hxy]
  rw [u.inv_mul] at h
  exact h

/-! ## §1. The η̂-operator alphabet

WW2's certificate grammar is atom-generic, and its design note names this lane as the intended
first consumer: *"lanes whose coefficients need atoms beyond `TameSym` (e.g. WNP's `A = σ^{η̂}`)
instantiate the same generic layer at their own alphabet."*  `NpcSym` is that alphabet: the
standard atoms, embedded whole through `.std`, plus one new atom family `etaA k` for the integer
powers `A^k` of the η̂-conjugator `A = σ^{η̂}`.

**Where the symbolic parameters live.**  `B = σ^{2^r}` needs no new atom — it is the standard
atom `.std (.gen .sigma (2^r))`, so the `r`-dependence sits in the certificate *data* (the ℤ
exponent).  The `η`-dependence sits in the *interpretation*: `NpcSym.toEnd` takes the
`A`-element as a parameter (exactly as `TameSym.toEnd` takes the projector `π`), so one piece of
formal data serves every `η` — and every resolver.  The certificates below instantiate it at
the resolver value `t.σ ^ E η̂`; the NC-seam bridge of §8 identifies that with the honest
profinite `σ ^ᶻ η̂` under the lift-level resolver discipline. -/

/-- The **η̂-operator alphabet** of the noncompact-`N` certificates: WW2's standard atoms
(embedded via `std`) extended by the integer powers of the η̂-conjugator `A = σ^{η̂}`. -/
inductive NpcSym (n : ℕ)
  /-- A standard atom of WW2's alphabet (`S`-powers, `S₂`-powers, the projector `P`). -/
  | std (s : TameSym n)
  /-- The action of the `k`-th power of the η̂-conjugator `A = σ^{η̂}`. -/
  | etaA (k : ℤ)
  deriving DecidableEq, Repr

namespace NpcSym

variable {n : ℕ} {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **The standard interpretation** of the η̂-alphabet: the embedded atoms through
`TameSym.toEnd` at the marking `t` and projector `π`, and `etaA k` as the action of `A ^ k`,
where the **`A`-element** `A : C` is a parameter of the interpretation — the η̂-conjugator's
value, supplied per consumer (resolver value `t.σ ^ E η̂` in the certificates below, honest
`t.σ ^ᶻ η̂` on the NC seam). -/
noncomputable def toEnd (t : Marking n C) (A : C) (π : AddMonoid.End V) :
    NpcSym n → AddMonoid.End V
  | .std s => TameSym.toEnd t π s
  | .etaA k => DistribMulAction.toAddMonoidEnd C V (A ^ k)

variable (t : Marking n C) (A : C) (π : AddMonoid.End V)

@[simp] theorem toEnd_std (s : TameSym n) : toEnd t A π (.std s) = TameSym.toEnd t π s := rfl

@[simp] theorem toEnd_etaA_apply (k : ℤ) (v : V) : toEnd t A π (.etaA k) v = (A ^ k) • v := rfl

/-- **The split/unramified interpretation**: the projector collapses to the identity. -/
noncomputable abbrev splitEnd (t : Marking n C) (A : C) : NpcSym n → AddMonoid.End V :=
  toEnd t A 1

/-- **The ramified interpretation**: the projector collapses to zero. -/
noncomputable abbrev ramifiedEnd (t : Marking n C) (A : C) : NpcSym n → AddMonoid.End V :=
  toEnd t A 0

/-- A trivially-acting `A`-element evaluates to the identity operator at every power — the
class-collapse lemma for the `etaA` atoms (the scalar module's reading: `A` is a power of `σ`,
so it acts trivially whenever `σ` does). -/
theorem toEnd_etaA_of_trivial (hA : ∀ v : V, A • v = v) (k : ℤ) : toEnd t A π (.etaA k) = 1 :=
  AddMonoidHom.ext fun v =>
    MulAction.mem_stabilizer_iff.mp
      ((MulAction.stabilizer C v).zpow_mem (MulAction.mem_stabilizer_iff.mpr (hA v)) k)

end NpcSym

/-! ## §2. The six factors of the corrected word, differentiated

The standing setting, as in the compact lane: a finite coefficient module `V` over a finite
marked group `C`, with the marking `t` of the noncompact-`N` alphabet `Generator (2 + 2h)`.
The class hypotheses are `hwild` (wild letters act trivially) plus one of `hτ` (unramified:
`τ` trivial) / `hτfpf, hTodd` (ramified: `τ` fixed-point-free, its `2`-primary part trivial);
`hTodd` alone is the **uniform** hypothesis under which the correction block dies. -/

section Rows

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- The `x₀`, `x₁`, `x₂` letters act trivially, from the uniform wild hypothesis. -/
theorem trivAct_coreLetter (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (i : Fin 3) : t (coreLetter h i) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
/-- The handle letters act trivially. -/
theorem trivAct_handleU (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleU j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
@[inherit_doc trivAct_handleU]
theorem trivAct_handleV (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (j : Fin h) : t (handleV j) ∈ trivAct C V :=
  mem_trivAct.mpr (hwild _)

omit [Finite C] [Finite V] in
/-- A commutator whose **left** argument acts trivially acts trivially, whatever the right
argument is: `[x,y] = x⁻¹ · x^y`, and the kernel of the permutation representation is normal.

The one-sided strengthening of `trivAct_commR` this word forces: the front block `[x₀, A]` and
the correction block `[D_{r,η}, x₁]` both pair a trivially-acting argument with an arbitrary
one (in the front block it is the *conjugator* `A = σ^{η̂}` that acts). -/
theorem trivAct_commR_left {x : C} (hx : x ∈ trivAct C V) (y : C) : commR x y ∈ trivAct C V := by
  have hxy : commR x y = x⁻¹ * conjR x y := by
    rw [commR, conjR]
    group
  rw [hxy]
  exact mul_mem (inv_mem hx) (trivAct_conjR hx y)

omit [Finite C] [Finite V] in
/-- **The resolved η̂-conjugator**: the finite denotation of `A = σ^{η̂}` is the resolver power
`S^{E(η̂)}`.  This is the *only* place the η̂-power is evaluated in this file, and it is the
resolver route — WNP-a's finding that the word is not `IsOmega2Only` rules the numeric-pin
route out, so every row below is stated exactly, for **every** resolver `E`, with the resolved
element appearing as an operator. -/
theorem evalFin_aW (e : EtaData) :
    PWord.evalFin ⇑t E E₂ (aW h e) = t.σ ^ E e.toZhat := by
  rw [aW, PWord.evalFin_profPow_of_ne _ _ _ _ (toZhat_ne_omega2 e), PWord.evalFin_gen,
    Marking.apply_sigma]

omit [Finite C] [Finite V] in
/-- The finite denotation of the boundary conjugator `g = x₁σ^{2^r}`. -/
theorem evalFin_gConj :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h 1), bW h r])
      = t (coreLetter h 1) * t.σ ^ ((2 : ℤ) ^ r) := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_one, mul_one, PWord.evalFin_gen, bW, PWord.evalFin_zpow,
    PWord.evalFin_gen, Marking.apply_sigma]

/-! ### The lift-level commutator rule for a trivially-acting left argument -/

omit [Finite C] [Finite V] in
/-- **The offset of `[p,q]` when the left base acts trivially**: `(q̄⁻¹ − 1)·p.u`, whatever `q`
is.  The lift-group computation behind both η̂-flavored commutators of this word — for the
front block `[x₀, A]` it *is* the row entry, with `q̄ = S^{E(η̂)}` the resolved conjugator. -/
theorem commR_u_of_left_trivial {p q : WordLift V C} (hp : ∀ v : V, p.g • v = v) :
    (commR p q).u = q.g⁻¹ • p.u - p.u := by
  have hp' : ∀ v : V, p.g⁻¹ • v = v := fun v => inv_smul_eq_iff.mpr (hp v).symm
  simp only [commR, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, mul_smul,
    hp, hp']
  abel

/-! ### The six factors, one at a time -/

/-- **Factor 1** — `D(x₀^{p_α}) = 0`: the leading power's first-order content is the parity of
`p_α = 2 + 2^α`, even as soon as `α ≥ 1`.  The branch condition `α ≥ 2` is a Hessian
(second-order) condition — NC5's `hα` is sharp there and invisible here, matching S3.1's
measurement. -/
theorem foxD_leadingPow (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hα : 1 ≤ α)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α)) = 0 := by
  rw [show ((2 : ℤ) + 2 ^ α) = ((2 + 2 ^ α : ℕ) : ℤ) by push_cast; ring,
    foxD_zpow_natCast, WordLift.sum_pow_smul_of_trivial (fun v => ?_)]
  · exact even_nsmul_eq_zero hV₂ (even_two_add_two_pow hα) _
  · exact mem_trivAct.mp (trivAct_coreLetter t hwild 0) v

/-- **Factor 2 — the first gate-D difference from the compact row.**
`D([x₀, A]) = (A⁻¹ − 1)·a(x₀)` with `A` read at the resolver, `Ā = S^{E(η̂)}`.

The compact row's `[x₀,x₁]` had both arguments of trivial lower value and contributed `0`; here
the second argument is a `σ`-power, which *acts*.  The two `A`-contributions cancel because
`x₀` dies (`commR_u_of_left_trivial` — `D(A)` never enters), and what survives is the operator
`A⁻¹ − 1` on the `x₀`-column: the Sage reference row's `A^{-1} + 1` in char-2 print. -/
theorem foxD_commX0A (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (e : EtaData)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.comm (.gen (coreLetter h 0)) (aW h e))
      = (t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0) := by
  rw [foxD_def, foxEval_comm,
    commR_u_of_left_trivial (fun v => mem_trivAct.mp (trivAct_coreLetter t hwild 0) v),
    foxEval_g, evalFin_aW t E E₂ e]
  rfl

/-- **Factor 3 — the second gate-D difference.**  `D(x₂^{-g}) = −B⁻¹·a(x₂)` with
`g = x₁σ^{2^r}`, `B = σ^{2^r}`: the boundary operator is `S^{−2^r}` where the compact row had
`S^{−1}`.

Note what does **not** happen: `g`'s `x₁`-factor contributes *nothing* to the `x₁`-column — the
two conjugation contributions of any conjugator cancel in pairs once the conjugated letter has
trivial lower value (`D(g)` is multiplied by `x̄₂ − 1 = 0`), and the surviving `ḡ⁻¹` acts as
`B⁻¹` because `x̄₁` acts trivially. -/
theorem foxD_invConjX2G (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (.inv (.conj (.gen (coreLetter h 2))
        (PWord.prodList [.gen (coreLetter h 1), bW h r])))
      = -((t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2)) := by
  have hx2 := mem_trivAct.mp (trivAct_coreLetter t hwild 2)
  have hconj : PWord.evalFin ⇑t E E₂ (.conj (.gen (coreLetter h 2))
      (PWord.prodList [.gen (coreLetter h 1), bW h r])) ∈ trivAct C V := by
    rw [PWord.evalFin_conj, PWord.evalFin_gen]
    exact trivAct_conjR (trivAct_coreLetter t hwild 2) _
  rw [foxD_inv, mem_trivAct.mp (inv_mem hconj), foxD_conj, evalFin_gConj t E E₂,
    PWord.evalFin_gen, foxD_gen]
  simp only [hx2, add_sub_cancel_right, mul_inv_rev, mul_smul,
    mem_trivAct.mp (inv_mem (trivAct_coreLetter t hwild 1))]

/-- The `ω₂`-block's inner word `x_i · τ` as a `prodList` (the certificate's spelling),
differentiated: `a(x_i) + a(τ)`.  Stated at a general core letter because the word carries two
such blocks — the boundary factor (`i = 2`) and the `δ₀`-letter's (`i = 0`). -/
theorem foxD_deltaInner (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = a (coreLetter h i) + a .tau := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_mul,
    PWord.evalFin_gen, PWord.evalFin_gen, foxD_gen, foxD_gen, foxD_one, smul_zero, add_zero,
    mem_trivAct.mp (trivAct_coreLetter t hwild i)]

omit [Finite C] [Finite V] in
/-- The evaluation of the inner word `x_iτ` acts as `τ` does. -/
theorem evalFin_deltaInner_smul (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (v : V) :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau]) • v
      = t.τ • v := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one,
    mul_smul, mem_trivAct.mp (trivAct_coreLetter t hwild i)]
  rfl

omit [Finite C] [Finite V] in
/-- The inner word's finite denotation, as a product. -/
theorem evalFin_deltaInner (i : Fin 3) :
    PWord.evalFin ⇑t E E₂ (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = t (coreLetter h i) * t.τ := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one]
  rfl

/-- **The `ω₂`-block on a split/unramified module (`P = 1`)** —
`D((x_iτ)^{ω₂}) = a(x_i) + a(τ)`, via WW1's engine lemma `WordLift.powOmega2_u_of_trivial`;
`powOmega2` is never unfolded. -/
theorem foxD_omega2Block_unram (i : Fin 3) (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = a (coreLetter h i) + a .tau := by
  rw [foxD_def, foxEval_omega2Pow,
    WordLift.powOmega2_u_of_trivial hV₂ _ (fun v => by
      rw [foxEval_g]
      exact (evalFin_deltaInner_smul t E E₂ i hwild v).trans (hτ v))]
  exact foxD_deltaInner t E E₂ i hwild a

/-- **The `ω₂`-block on a ramified module (`P = 0`)** — `D((x_iτ)^{ω₂}) = 0`, via
`WordLift.powOmega2_u_of_oddFixedPointFree`. -/
theorem foxD_omega2Block_ram (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau]))
      = 0 := by
  rw [foxD_def, foxEval_omega2Pow]
  refine WordLift.powOmega2_u_of_oddFixedPointFree _ (fun v hv => hτfpf v ?_) (fun v => ?_)
  · rw [foxEval_g] at hv
    exact ((evalFin_deltaInner_smul t E E₂ i hwild v).symm.trans hv)
  · rw [foxEval_g, evalFin_deltaInner]
    exact WordLift.powOmega2_smul_of_trivial_mul _ _
      (mem_trivAct.mp (trivAct_coreLetter t hwild i)) hTodd v

omit [Finite V] in
/-- The `ω₂`-block's finite denotation acts trivially under the **uniform** hypothesis `hTodd`
(the `2`-primary part of `τ` acts trivially) — no class split: on the unramified side `hTodd`
follows from `hτ`, on the ramified side it is the standing rule-1 consequence.  This is what
lets the correction block die uniformly. -/
theorem trivAct_evalFin_omega2Block (i : Fin 3)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    PWord.evalFin ⇑t E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V := by
  rw [PWord.evalFin_omega2Pow, evalFin_deltaInner]
  exact mem_trivAct.mpr fun v => WordLift.powOmega2_smul_of_trivial_mul _ _
    (mem_trivAct.mp (trivAct_coreLetter t hwild i)) hTodd v

omit [Finite V] in
/-- The `δ₀`-letter `δ₀ = (x₀τ)^{ω₂}x₀⁻¹` evaluates trivially, under the uniform `hTodd`. -/
theorem trivAct_evalFin_deltaZeroW
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    PWord.evalFin ⇑t E E₂ (deltaZeroW h) ∈ trivAct C V := by
  rw [deltaZeroW]
  refine trivAct_evalFin_prodList ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact trivAct_evalFin_omega2Block t E E₂ 0 hwild hTodd
  · rw [PWord.evalFin_inv, PWord.evalFin_gen]
    exact inv_mem (trivAct_coreLetter t hwild 0)

omit [Finite V] in
/-- The compressed `D`-block evaluates trivially: a product of conjugates of the
trivially-evaluating `δ₀` (by *arbitrary* conjugators — normality does all the work; the
η̂-power and the `B⁻¹`-power are never inspected). -/
theorem trivAct_evalFin_dBlockW
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (e : EtaData) :
    PWord.evalFin ⇑t E E₂ (dBlockW h r e) ∈ trivAct C V := by
  have hδ := trivAct_evalFin_deltaZeroW t E E₂ hwild hTodd
  rw [dBlockW]
  refine trivAct_evalFin_prodList ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [PWord.evalFin_conj]
    exact trivAct_conjR hδ _
  · rw [PWord.evalFin_conj]
    refine trivAct_conjR ?_ _
    refine trivAct_evalFin_prodList ?_
    intro w' hw'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
    rcases hw' with rfl | rfl
    · exact hδ
    · rw [PWord.evalFin_conj]
      exact trivAct_conjR hδ _

/-- **The `D`-block's first-order row is the corrected cross operator applied to `D(δ₀)`**:

```
D(D_{r,η}) = A⁻¹·D(δ₀) + (B·D(δ₀) + B·A⁻¹·D(δ₀)),        A = S^{E(η̂)},  B = S^{2^r}
```

— the operator `L_c = A⁻¹ + B + B·A⁻¹` of the S3.2 correction, appearing verbatim at first
order.  The three summands are the three conjugators of the compressed spelling
`δ₀^A (δ₀ δ₀^A)^{B⁻¹}`: right conjugation applies the inverse conjugator, so `A` contributes
`A⁻¹` and `B⁻¹` contributes `B` (once each for the two `δ₀`-copies of the second factor).
This is the first-order shadow of NC4's `npcDBlock_eval` (whose `V`-part is `L_c c₀`), and §8
identifies it with NC2's `lcOp` on the nose.  `D(A)` and `D(B)` never enter: both conjugated
words evaluate trivially. -/
theorem foxD_dBlockW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (dBlockW h r e)
      = (t.σ ^ E e.toZhat)⁻¹ • foxD ⇑t a E E₂ (deltaZeroW h)
        + (t.σ ^ ((2 : ℤ) ^ r) • foxD ⇑t a E E₂ (deltaZeroW h)
          + t.σ ^ ((2 : ℤ) ^ r) • (t.σ ^ E e.toZhat)⁻¹ • foxD ⇑t a E E₂ (deltaZeroW h)) := by
  have hδ := trivAct_evalFin_deltaZeroW t E E₂ hwild hTodd
  have hδs := mem_trivAct.mp hδ
  have hδA : PWord.evalFin ⇑t E E₂ (.conj (deltaZeroW h) (aW h e)) ∈ trivAct C V := by
    rw [PWord.evalFin_conj]
    exact trivAct_conjR hδ _
  -- the first factor: `D(δ₀^A) = A⁻¹·D(δ₀)`
  have hfst : foxD ⇑t a E E₂ (.conj (deltaZeroW h) (aW h e))
      = (t.σ ^ E e.toZhat)⁻¹ • foxD ⇑t a E E₂ (deltaZeroW h) := by
    rw [foxD_conj, evalFin_aW t E E₂ e, hδs, add_sub_cancel_right]
  -- the second factor: `D((δ₀ δ₀^A)^{B⁻¹}) = B·(D(δ₀) + A⁻¹·D(δ₀))`
  have hsnd : foxD ⇑t a E E₂
      (.conj (PWord.prodList [deltaZeroW h, .conj (deltaZeroW h) (aW h e)]) (.inv (bW h r)))
      = t.σ ^ ((2 : ℤ) ^ r) • (foxD ⇑t a E E₂ (deltaZeroW h)
          + (t.σ ^ E e.toZhat)⁻¹ • foxD ⇑t a E E₂ (deltaZeroW h)) := by
    have hpair : ∀ w ∈ [deltaZeroW h, .conj (deltaZeroW h) (aW h e)],
        PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hδ
      · exact hδA
    have hin : PWord.evalFin ⇑t E E₂
        (PWord.prodList [deltaZeroW h, .conj (deltaZeroW h) (aW h e)]) ∈ trivAct C V :=
      trivAct_evalFin_prodList hpair
    rw [foxD_conj, mem_trivAct.mp hin, add_sub_cancel_right, PWord.evalFin_inv, bW,
      PWord.evalFin_zpow, PWord.evalFin_gen, Marking.apply_sigma, inv_inv,
      foxD_prodList_of_trivial _ _ _ _ _ hpair]
    simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hfst]
  rw [dBlockW, foxD_prodList_of_trivial _ _ _ _ _ (by
    intro w hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact hδA
    · rw [PWord.evalFin_conj]
      refine trivAct_conjR (trivAct_evalFin_prodList ?_) _
      intro w' hw'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw'
      rcases hw' with rfl | rfl
      · exact hδ
      · exact hδA)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero, hfst, hsnd,
    smul_add]

/-- **HEADLINE: the correction block `E_{r,η}` is invisible at first order.**

Its Fox row is **zero** — at every marking whose wild letters act trivially and whose
`τ`-letter has trivially-acting `2`-primary part, i.e. **uniformly across the module classes**
(split, unramified and ramified alike), for all `α, r, h`, all `η`, all resolvers and all
offsets.

This is the first-order half of "the S3.2 correction is second-order-only": `D_{r,η}` itself
has a genuinely nonzero first-order row — `L_c·D(δ₀)`, by `foxD_dBlockW` — but the commutator
with `x₁` kills it, because *both* arguments evaluate trivially and the Fox row of such a
commutator dies whatever the offsets are (`foxD_comm_of_trivial`; the operator coefficients
`v̄⁻¹ − 1` and `ū − 1` vanish).  What survives of `L_c` at second order is exactly NC5's
`npc_cross_operators`; what survives at first order is nothing.  Consequently the corrected
word's gate-D row equals the uncorrected word's (`foxD_npcW_eq_uncorrected` below) — the Sage
reference-row docstring's *"the reference row is the same for the raw and the corrected word"*,
banked as a theorem. -/
theorem foxD_eBlockW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (eBlockW h r e) = 0 := by
  rw [eBlockW]
  exact foxD_comm_of_trivial _ _ _ _ (trivAct_evalFin_dBlockW t E E₂ hwild hTodd e)
    (trivAct_coreLetter t hwild 1)

/-- **Factor 6** — `D(H_h) = 0`: the handle block's Fox row is zero at every handle count
(hyperbolic stabilization has zero first jet), by the hoisted `foxD_comm_of_trivial` route —
no freshness of the handle letters is used, only the triviality of their action. -/
theorem foxD_handlesW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (a : Generator (2 + 2 * h) → V) : foxD ⇑t a E E₂ (handlesW h) = 0 := by
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 + 2 * h))),
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)
  rw [handlesW, foxD_prodList_of_trivial _ _ _ _ _ hmem]
  refine List.sum_eq_zero ?_
  intro y hy
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact foxD_comm_of_trivial _ _ _ _ (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)

omit [Finite V] in
/-- Every factor of the corrected noncompact-`N` word evaluates trivially, under the uniform
hypotheses `hwild` + `hTodd` — **no class split**, unlike the compact lane's factor lemma: the
`δ`-flavored factors are covered by `hTodd` alone, and the two η̂-flavored commutators by
one-sided normality (`trivAct_commR_left`), never by evaluating their conjugators. -/
theorem trivAct_npc_factors (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (e : EtaData) :
    ∀ w ∈ [(PWord.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α) : PWord (Generator (2 + 2 * h))),
        .comm (.gen (coreLetter h 0)) (aW h e),
        .inv (.conj (.gen (coreLetter h 2)) (PWord.prodList [.gen (coreLetter h 1), bW h r])),
        PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
        eBlockW h r e,
        handlesW h],
      PWord.evalFin ⇑t E E₂ w ∈ trivAct C V := by
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · rw [PWord.evalFin_zpow, PWord.evalFin_gen]
    exact zpow_mem (trivAct_coreLetter t hwild 0) _
  · rw [PWord.evalFin_comm, PWord.evalFin_gen]
    exact trivAct_commR_left (trivAct_coreLetter t hwild 0) _
  · rw [PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_gen]
    exact inv_mem (trivAct_conjR (trivAct_coreLetter t hwild 2) _)
  · exact trivAct_evalFin_omega2Block t E E₂ 2 hwild hTodd
  · rw [eBlockW, PWord.evalFin_comm, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_evalFin_dBlockW t E E₂ hwild hTodd e)
      (trivAct_coreLetter t hwild 1)
  · rw [handlesW]
    refine trivAct_evalFin_prodList ?_
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen]
    exact trivAct_commR (trivAct_handleU t hwild j) (trivAct_handleV t hwild j)

/-! ### The wild rows

The evaluated first-order row of `R_{N,α,r,η}`, per module class — the Lean twins of the Sage
reference row `fox_reference_row_noncompact`,

```
(σ, τ, x₀, x₁, x₂, handles) = (0, P, A⁻¹ + 1, 0, S^{−2^r} + P, 0, …, 0),
```

which **differs from the compact row** `(0, P, 0, 0, S⁻¹ + P, 0, …, 0)` in exactly the two
predicted places: the `x₀`-column gained the block `A⁻¹ − 1` (factor 2's conjugator now acts)
and the boundary operator is `S^{−2^r}` where the compact row had `S⁻¹` (the conjugator is
`g = x₁σ^{2^r}`, not `σ`).  The noncompact word therefore needs — and here gets — **its own
reference row**; the freeze records the same fact for the Sage side. -/

/-- **The noncompact-`N` wild row on an unramified simple module** (`P = 1`; packet
Def. 9.1(3), freeze row 3):

```
D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) + a(τ) + (1 − B⁻¹)·a(x₂),   A = S^{E(η̂)},  B = S^{2^r}.
```

Exactly three of the `2h + 5` columns are nonzero; the whole statement is symbolic in `r` (the
operator data) and in `η` (through the resolver value), and exact for every resolver. -/
theorem foxD_npc_unram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e)
      = ((t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0))
        + (a .tau + (a (coreLetter h 2) - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2))) := by
  have hTodd : ∀ v : V, powOmega2 t.τ • v = v := fun v =>
    mem_trivAct.mp (trivAct_powOmega2 (mem_trivAct.mpr hτ)) v
  rw [npcW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_npc_factors t E E₂ hwild hTodd e)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_leadingPow t E E₂ hV₂ hwild hα, foxD_commX0A t E E₂ hwild e,
    foxD_invConjX2G t E E₂ hwild, foxD_omega2Block_unram t E E₂ 2 hV₂ hwild hτ,
    foxD_eBlockW t E E₂ hwild hTodd e, foxD_handlesW t E E₂ hwild]
  abel

/-- **The noncompact-`N` wild row on a ramified simple module** (`P = 0`): the `τ`- and
`x₂`-halves of the `ω₂`-block die and

```
D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) − B⁻¹·a(x₂)
```

— unlike the compact row, a **two**-entry ramified row: the single unit entry `B⁻¹` on `x₂`
plus the leftover `x₀`-block, which is why the ramified normal form costs two operations
(`C_Fox = 2`). -/
theorem foxD_npc_ram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e)
      = ((t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0))
        - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2) := by
  rw [npcW, foxD_prodList_of_trivial _ _ _ _ _ (trivAct_npc_factors t E E₂ hwild hTodd e)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_leadingPow t E E₂ hV₂ hwild hα, foxD_commX0A t E E₂ hwild e,
    foxD_invConjX2G t E E₂ hwild, foxD_omega2Block_ram t E E₂ 2 hwild hτfpf hTodd,
    foxD_eBlockW t E E₂ hwild hTodd e, foxD_handlesW t E E₂ hwild]
  abel

/-- **The noncompact-`N` wild row on a split (scalar) module**: with `σ` acting trivially both
σ-power blocks die — `A` *is* a power of `σ` — and the row degenerates to the `τ`-pivot
`a(τ)`, exactly as the compact row does: both blocks vanish simultaneously only on the scalar
module, and "the scalar module separates nothing" survives the correction. -/
theorem foxD_npc_split (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hσ : ∀ v : V, t.σ • v = v) (hα : 1 ≤ α) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e) = a .tau := by
  have hσmem : t.σ ∈ trivAct C V := mem_trivAct.mpr hσ
  rw [foxD_npc_unram t E E₂ hV₂ hwild hτ hα e a,
    mem_trivAct.mp (inv_mem (zpow_mem hσmem (E e.toZhat))),
    mem_trivAct.mp (inv_mem (zpow_mem hσmem ((2 : ℤ) ^ r)))]
  abel

/-! ### Gate-D blindness: the raw and the corrected word have the same first-order row -/

/-- The **uncorrected** noncompact word — eq:Npc-word *without* its correction factor
`E_{r,η}`.  Local to this file and deliberately so: the frozen word is the corrected one, and
this five-factor product exists only to make gate-D blindness a theorem rather than a
docstring claim. -/
noncomputable def npcUncorrectedW (α r h : ℕ) (e : EtaData) : PWord (Generator (2 + 2 * h)) :=
  PWord.prodList
    [.zpow (.gen (coreLetter h 0)) (2 + 2 ^ α),
     .comm (.gen (coreLetter h 0)) (aW h e),
     .inv (.conj (.gen (coreLetter h 2)) (PWord.prodList [.gen (coreLetter h 1), bW h r])),
     PWord.omega2Pow (PWord.prodList [.gen (coreLetter h 2), .gen .tau]),
     handlesW h]

/-- **Gate D is blind to `E_{r,η}`**: the corrected and the uncorrected words have the *same*
Fox row — at every marking of both module classes (the uniform `hTodd` again), every resolver,
every `(α, r, η, h)` and every offset vector.  The Lean form of the Sage reference-row fact
*"the reference row is the same for the raw and the corrected word, and a test pins that"*
(`fox_reference_row_noncompact`), and the first-order member of the blindness family
`EPI_BLIND_TO_E` (tame, pro-2, first Fox order, gate G) — only the second jet separates, and
that is NC5's theorem. -/
theorem foxD_npcW_eq_uncorrected
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e) = foxD ⇑t a E E₂ (npcUncorrectedW α r h e) := by
  rw [npcW, npcUncorrectedW,
    foxD_prodList_of_trivial _ _ _ _ _ (trivAct_npc_factors t E E₂ hwild hTodd e),
    foxD_prodList_of_trivial _ _ _ _ _ (fun w hw =>
      trivAct_npc_factors t E E₂ hwild hTodd e w (by
        simp only [List.mem_cons] at hw ⊢
        tauto))]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [foxD_eBlockW t E E₂ hwild hTodd e]
  abel

/-! ### The zero columns — the `2h` handle columns in particular

A *column* of the evaluated row is its value on a single-slot offset vector `Pi.single g v`.
The wild row has at most three nonzero columns at every handle count, so the `2h` handle
columns — the whole `h`-dependence of the first jet — vanish identically (packet item (4)'s
handle clause, at **every** `h`). -/

omit [Finite C] [Finite V] in
theorem handleU_ne_coreLetter (j : Fin h) (i : Fin 3) : handleU j ≠ coreLetter h i := by
  simp only [handleU, coreLetter, ne_eq, Generator.wild.injEq, Fin.mk.injEq]
  have := i.isLt
  omega

omit [Finite C] [Finite V] in
theorem handleV_ne_coreLetter (j : Fin h) (i : Fin 3) : handleV j ≠ coreLetter h i := by
  simp only [handleV, coreLetter, ne_eq, Generator.wild.injEq, Fin.mk.injEq]
  have := i.isLt
  omega

omit [Finite C] [Finite V] in
theorem handleU_ne_tau (j : Fin h) : handleU j ≠ (Generator.tau : Generator (2 + 2 * h)) := by
  simp [handleU]

omit [Finite C] [Finite V] in
theorem handleV_ne_tau (j : Fin h) : handleV j ≠ (Generator.tau : Generator (2 + 2 * h)) := by
  simp [handleV]

/-- **Every column of the unramified wild row other than `τ`, `x₀`, `x₂` is zero** — the `σ`-
and `x₁`-columns and, the point, all `2h` handle columns. -/
theorem foxDHom_npc_unram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) {g : Generator (2 + 2 * h)} (hgτ : g ≠ .tau)
    (hg0 : g ≠ coreLetter h 0) (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_npc_unram t E E₂ hV₂ hwild hτ hα e,
    Pi.single_eq_of_ne (Ne.symm hgτ), Pi.single_eq_of_ne (Ne.symm hg0),
    Pi.single_eq_of_ne (Ne.symm hg2)]
  simp

/-- The `2h` handle columns of the unramified wild row are zero — the `u`-half. -/
theorem foxDHom_npc_handleU_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single (handleU j) v) = 0 :=
  foxDHom_npc_unram_column_eq_zero t E E₂ hV₂ hwild hτ hα e (handleU_ne_tau j)
    (handleU_ne_coreLetter j 0) (handleU_ne_coreLetter j 2) v

/-- The `2h` handle columns of the unramified wild row are zero — the `v`-half. -/
theorem foxDHom_npc_handleV_column (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single (handleV j) v) = 0 :=
  foxDHom_npc_unram_column_eq_zero t E E₂ hV₂ hwild hτ hα e (handleV_ne_tau j)
    (handleV_ne_coreLetter j 0) (handleV_ne_coreLetter j 2) v

/-- The same on the ramified class: everything but the `x₀`- and `x₂`-columns dies, handles
included. -/
theorem foxDHom_npc_ram_column_eq_zero (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) {g : Generator (2 + 2 * h)} (hg0 : g ≠ coreLetter h 0)
    (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single g v) = 0 := by
  rw [foxDHom_apply, foxD_npc_ram t E E₂ hV₂ hwild hτfpf hTodd hα e,
    Pi.single_eq_of_ne (Ne.symm hg0), Pi.single_eq_of_ne (Ne.symm hg2)]
  simp

end Rows

end GQ2.Dyadic.Certificates.Npc
