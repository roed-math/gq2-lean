/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Word.NpcBridge
import GQ2.Dyadic.Certificates.MpcStokes

/-!
# Dyadic campaign, ticket WMP-J: the procyclic-`M` jet theorem

The `npc_cross_operators` analogue for `mpcW`, and **WW4 gap item 5 discharged** on the
procyclic-`M` row.  WW6's `Word/NpcBridge.lean` closed the carrier half of that gap and named
what was left: "an `mpcW` **jet theorem** — the `npc_cross_operators` analogue for `mpcW` — and
it exists nowhere".  This file is that theorem, and the consequences WW6 listed.

## The headline

`mpc_cross_operators` — at general `(α ≥ 1, r, p, η, h)`, at every graph-type κ⁰-marking whose
`x₂`-slot is zero:

```
fib( val(R_lin^pc) · val(R̂^pc) · val(D₀²[D₀,D₁]) )  =  q(c₀) + b_q(c₀, c₁)
```

and at the frozen word (`evalFin_fib_mpcW`, `h = 0`, where `H_h = 1`) this is
`plusFormD q q (c₀, c₁)`.  Both are `evalFin` statements; `hessRelZ_mpcW` is the `hessRelZ`
form and `mpc_hess_eval` the honest profinite `Marking.eval` form.

## The three mechanisms, all consumed rather than re-derived

1. **The δ-letters are Heisenberg-slice elements** (§3).  `u_i = (x_iτ)^{ω₂}` is *central*:
   NC3's rules 1 and 2 meet at the mixed base `(c_i, u)` — the order bound is WW6's transported
   `orderOf_hessElt_dvd_two_mul`, the norm vanishing is NC3's `sum_pow_smul_orderOf_eq_zero`
   (from `hVu`), the `ω₂`-reduction is NC3's `zpowHat_omega2_eq_pow_of_dvd_two_mul` (from `hu`),
   and the value is WW6's transported `hessElt_pow_eq_hessSlice`.  Hence
   `δ_i ↦ ((c_i,1), z_i + q(c_i))`, and at the boundary slot `δ₂ ↦ 1`.
2. **The two copies coincide** (§6).  `Sh_M`'s replacements `x₀ ↦ δ₀`, `x₁ ↦ δ₁` change the
   value by a *central* factor only, `x₂ ↦ 1` leaves `Ĉ₀ = C₀` on the nose, and `E₂^pc` dies
   outright because `δ₂ = 1`.  §4's three laws (squares and commutators are blind to the
   centre) then give `val(R̂^pc) = val(R_lin^pc)` — so the pair is a **square**.
3. **The square is trivial** (§7).  `fib(L·L) = κ(L̄, L̄)`, and `κ` at a zero primal offset is
   `0`.  The offset *is* zero: that is WMP-d's row collapse
   `D(R_lin^pc)(a) = S₂^{−s}σ^{−n}a(x₂)` (`foxD_mpcLinW_x2`), read at `a(x₂) = 0`.

What survives is the plus block, whose value is `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` (§5) — a word
identity, not a finite-order interpolation, exactly as WMP-c recorded.

## Two findings about the API

**(i) The registers do not meet, and `mpcCopiesCancel` is not consumable here.**  WMP-c's
cancellation sits in the **Heisenberg** register (`heisEvalZ : PWord X → HeisLift A C`, fields
`.a/.l/.z`); `hessRelZ` sits in the **κ⁰ central extension**
(`WordCoh.CentExt (kappa0Cocycle dat hdat)`, field `.fib`).  A repo-wide survey finds **no
lemma anywhere connecting them**, and none can be produced by a carrier identification: the two
central rules are `(p*q).z = p.z + q.z + p.l (p.g • q.a)` and
`(p*q).fib = p.fib + q.fib + κ(p̄, q̄)`, which agree only for a cocycle of Heisenberg shape
(`GQ2/MixedBObs.lean`'s `kappaHeis`), whereas `kappa0Cocycle` is `dat.f`/`dat.m`-shaped.  So §6
is the κ⁰-register **analogue** of `mpcCopiesCancel`, proved independently.

The compensation is real: on this carrier P4's central clause is **not needed**.  WMP-c had to
carry `CentralReplication` as a module hypothesis (the shadow memo's own table shows it failing
on three of the four ramified simples); here the two values are *literally equal*, so §6 is
hypothesis-free and the ⚠ around P4 does not apply to this row's Hessian.

**(ii) `foxD` and the κ⁰ base are the same object, and nobody had said so.**  §1 supplies the
missing identification `WordLift V C ≃* SemiProd C V` and
`evalFin_hessMark_fst`, which says
`(evalFin (hessMark s u vv) E E₂ w).1 = foxD ⇑(lowerMark s u) (hessOffsets vv) E E₂ w`
— the reason WMP-d's Fox-level row is usable at second order at all.  Both sides are `evalFin`,
so **no resolver hypothesis is spent** on it.  This is a hoist candidate (`Word/Fox.lean` or
`Word/Hessian.lean`), and it is what every future "gate-D row consumed at gate E" argument needs.

## What `d₀` is pinned to

WW6 asked the successor to "pin `d₀` from the `TwistedClass2Domain` normalization rather than
take it abstract".  **`d₀ = q`** — equivalently `fun v ↦ dat.f v v`, by `f_diag`; the compact
rows' spelling after all (`mpc_hessRelZTarget`).  This is not an assumption: it is forced, and
the reason is charge-independence.  The δ-letters *do* carry the twisted normalization's charge
(`NpcJet.powCharge dat u c_i (orderOf u)`, memo §3.3's "some element of `𝔽₂` depending on `c₀`
alone"), but the only two laws the plus block uses — `hessSlice_sq` and `hessSlice_commR` — are
both independent of the slice charge, so the twist cancels out of the endpoint.  No
`TwistedClass2Domain` input is needed, and none is available to change the answer.

## Hypotheses, and what they are

`hV2` (characteristic 2), `hu : Odd (orderOf u)` (Gate-B rule T1 / NC5's rule 1), `hVu`
(`V^u = 0`, NC5's rule 2), `hv2` (the `x₂`-has-no-primal-letter convention — S4.5's rider (ii),
here load-bearing), `hα : 1 ≤ α` (Prop. 9.2's balance, WMP-b/c/d's own threshold — *not* the
compact rows' `2 ≤ α`), and `hη` (the `η̂`-display acts as an integer power of `σ`, WMP-d's
`ActsAsPow` datum, definitional at the `√−10` instance via `actsAsPow_etaOne`).  The `hessRelZ`
and profinite forms add WMP-c's `ResolverLifts`, which is the *only* thing separating `evalZ`
from `evalFin`.  ⚠ **No `ResolvedAt`** — WW6's resolver-immunity finding for this row holds.

## Scope, honestly

This file's frozen-word statements take `h = 0`, where `handlesW 0 = 1`; §7's
`evalFin_mpcW_factored` splits the handle tail off at general `h`.  **The general-`h` tail is now
evaluated downstream** (W50: `Instances/MpcJetGeneral.lean` supplies the `evalFin` twin of
WN0-c's `hess_handlesW_eval` and the predicted `∑_j b_q(e_{3+2j}, e_{4+2j})` — this paragraph's
forecast held exactly); nothing else changes.  `E₀₁^pc`'s second-order justification is untouched — freeze row 5's status (gate-F
measurement, cited not proved) stands, and nothing below weakens or strengthens it.  The S4.5
block-order rider stays a gate-D statement (`swapDifference_zero_of_no_primal_x2`); §6's
`evalFin_e2W_one` is its value-level face on this marking and claims nothing more.

## Axiom prints (recorded at commit time)

`#print axioms` gives **the standard three** (`propext`, `Classical.choice`, `Quot.sound`) or a
strict subset, for every one of the 46 declarations — measured on the built module.  Strict
subsets: `wlEquiv` (none), `hessOffsets`/`lowerMark`/`conjR_mul_central`/
`commR_mul_central_left`/`commR_mul_central_right` (`[propext]`), and
`coreIdx`/`coreIdx_zero`/`coreIdx_one`/`coreIdx_two`/`hessMark_eq_foxLift`
(`[propext, Quot.sound]`).  Headlines: `evalFin_hessMark_fst`, `evalFin_uW`, `evalFin_dW`,
`evalFin_plusW`, `evalFin_mpcHatW_eq_mpcLinW`, `base_fst_mpcLinW`, `fib_mpcLinW_mul_mpcHatW`,
`mpc_cross_operators`, `evalFin_fib_mpcW`, `hessRelZ_mpcW`, `mpc_hessRelZTarget`,
`mpc_hess_eval`, `sqrtNeg10_hessRelZ`, `sqrtNeg10_hessRelZTarget`, `sqrtNeg10_word_eq_certQ`.

No sorries, no new axioms, **no `decide` at all**, and none of the nine obligations is touched.

## Module rule

Plain-import, and forced: `Word/NpcBridge.lean` (WW6) is plain and
`Certificates/MpcStokes.lean` (WMP-d) is plain, so this leaf is plain.  It **is** registered in
`GQ2.lean` (the "not registered" note here was stale — W50 doc fix); per-module build:
`lake build GQ2.Dyadic.Certificates.MpcJet`.
-/

namespace GQ2.Dyadic.Certificates.MpcJet

open GQ2.FoxH GQ2.SectionSix GQ2.QuadraticFp2
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates.MProcyclic

/-- The wild-letter slot of a core letter, in the sibling lanes' `xIdx` spelling. -/
def coreIdx (h : ℕ) (i : Fin 3) : Fin (2 + 2 * h + 1) := ⟨(i : ℕ), by omega⟩

theorem coreIdx_zero (h : ℕ) : coreIdx h 0 = Certificates.x0Idx h := rfl

theorem coreIdx_one (h : ℕ) : coreIdx h 1 = Certificates.x1Idx h := rfl

theorem coreIdx_two (h : ℕ) : coreIdx h 2 = Certificates.x2Idx h := rfl

/-! ## §1. The register bridge `WordLift V C ≃* SemiProd C V` -/

section Register

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V] [Finite C] [Finite V]

/-- The Fox lane's lift group and the `Word/` layer's semidirect carrier are the same group. -/
def wlEquiv : WordLift V C ≃* SemiProd C V where
  toFun p := (p.u, p.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

omit [Finite C] [Finite V] in
@[simp] theorem wlEquiv_fst (p : WordLift V C) : (wlEquiv p).1 = p.u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem wlEquiv_snd (p : WordLift V C) : (wlEquiv p).2 = p.g := rfl

/-- The primal offsets of a graph-type marking, as a Fox offset vector. -/
def hessOffsets {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V) : Generator (2 + 2 * h) → V
  | .sigma => 0
  | .tau => 0
  | .wild i => vv i

omit [Finite C] [Finite V] in
@[simp] theorem hessOffsets_sigma {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V) :
    hessOffsets vv Generator.sigma = 0 := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessOffsets_wild {h : ℕ} (vv : Fin (2 + 2 * h + 1) → V)
    (i : Fin (2 + 2 * h + 1)) : hessOffsets vv (Generator.wild i) = vv i := rfl

/-- The lower marking of a graph-type marking: `σ ↦ s`, `τ ↦ u`, every wild letter trivial. -/
noncomputable def lowerMark {h : ℕ} (s u : C) : Marking (2 + 2 * h) C :=
  Marking.ofLetters s u (fun _ => 1)

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_sigma {h : ℕ} (s u : C) : (lowerMark (h := h) s u).σ = s := rfl

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_tau {h : ℕ} (s u : C) : (lowerMark (h := h) s u).τ = u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem coreMark_x {h : ℕ} (s u : C) (i : Fin (2 + 2 * h + 1)) :
    (lowerMark (h := h) s u).x i = 1 := rfl

omit [Finite C] [Finite V] in
/-- **The graph-type marking is the Fox lift of its two halves.** -/
theorem hessMark_eq_foxLift {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    Certificates.hessMark s u vv
      = fun g => wlEquiv (foxLift (⇑(lowerMark (h := h) s u)) (hessOffsets vv) g) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i => rfl

/-- **The primal coordinate of a graph-type evaluation is the Fox derivative.**  Both sides are
`evalFin`, so no resolver hypothesis is spent: the identification is pure naturality. -/
theorem evalFin_hessMark_fst {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord (Generator (2 + 2 * h))) :
    (PWord.evalFin (Certificates.hessMark s u vv) E E₂ w).1
      = foxD (⇑(lowerMark (h := h) s u)) (hessOffsets vv) E E₂ w := by
  rw [hessMark_eq_foxLift s u vv, foxD_def, foxEval_def]
  exact congrArg Prod.fst
    (PWord.map_evalFin (wlEquiv : WordLift V C ≃* SemiProd C V).toMonoidHom
      (foxLift (⇑(lowerMark (h := h) s u)) (hessOffsets vv)) E E₂ w).symm

end Register

/-! ## §2. The `ω₂`-power rule on the `Word/` carrier -/

section Omega

/-- `powOmega2` form of NC3's reduction rule 1 — one rewrite from `zpowHat_omega2`. -/
theorem powOmega2_eq_pow_of_dvd_two_mul {P : Type} [Group P] [TopologicalSpace P]
    [DiscreteTopology P] [Finite P] {y : P} {m : ℕ} (hm : Odd m) (hdvd : orderOf y ∣ 2 * m) :
    powOmega2 y = y ^ m := by
  rw [← zpowHat_omega2, zpowHat_omega2_eq_pow_of_dvd_two_mul hm hdvd]

end Omega

/-! ## §3. The δ-letters at the graph-type κ⁰-marking -/

section Letters

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

/-- The κ⁰-lift of a graph-type marking, the object every value below is read at. -/
noncomputable def hessLift {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    Generator (2 + 2 * h) → WordCoh.CentExt (kappa0Cocycle dat hdat) :=
  WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_sigma {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    hessLift dat hdat (h := h) s u vv Generator.sigma = hessLine dat hdat s := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_tau {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) :
    hessLift dat hdat (h := h) s u vv Generator.tau = hessLine dat hdat u := rfl

omit [Finite C] [Finite V] in
@[simp] theorem hessLift_wild {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (i : Fin (2 + 2 * h + 1)) :
    hessLift dat hdat (h := h) s u vv (Generator.wild i) = hessSlice dat hdat (vv i) 0 := rfl

omit [Finite C] [Finite V] in
theorem hessLift_coreLetter {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (i : Fin 3) :
    hessLift dat hdat (h := h) s u vv (coreLetter h i)
      = hessSlice dat hdat (vv (coreIdx h i)) 0 := rfl

omit [Finite C] [Finite V] in
/-- The value of `x_i τ`: a `hessElt` over the mixed base `(c_i, u)`. -/
theorem evalFin_coreLetter_mul_tau {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
        (PWord.prodList [.gen (coreLetter h i), .gen .tau])
      = NpcBridge.hessElt dat hdat (vv (coreIdx h i)) u 0 := by
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_gen, PWord.evalFin_gen, PWord.evalFin_one, mul_one,
    hessLift_coreLetter, hessLift_tau, NpcBridge.hessSlice_mul_hessLine]

/-- **The `u_i`-letter is central.**  `(x_iτ)^{ω₂}` at a graph-type marking is the central
inclusion of NC2's accumulated charge — NC3's rules 1 and 2 meeting, on the `Word/` carrier.

Nothing here is re-derived: the order bound is WW6's transported `orderOf_hessElt_dvd_two_mul`,
the norm vanishing is NC3's `sum_pow_smul_orderOf_eq_zero`, the `ω₂`-reduction is NC3's rule 1,
and the `y^m` value is WW6's transported `hessElt_pow_eq_hessSlice`. -/
theorem evalFin_uW {h : ℕ} (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (uW h i)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (NpcJet.powCharge dat u (vv (coreIdx h i)) (orderOf u)) := by
  have hN : ∑ j ∈ Finset.range (orderOf u), u ^ j • vv (coreIdx h i) = 0 :=
    sum_pow_smul_orderOf_eq_zero hVu _
  have hm : u ^ orderOf u = 1 := pow_orderOf_eq_one u
  rw [uW, PWord.omega2Pow, PWord.evalFin_profPow_omega2,
    evalFin_coreLetter_mul_tau dat hdat s u vv E E₂ i,
    powOmega2_eq_pow_of_dvd_two_mul hu
      (NpcBridge.orderOf_hessElt_dvd_two_mul dat hdat hm hN),
    NpcBridge.hessElt_pow_eq_hessSlice dat hdat hm hN]
  rfl

/-- **The δ-letter is a Heisenberg-slice element** at offset `c_i`, with a charge that no
downstream value depends on (both the square law and the commutator law are charge-free). -/
theorem evalFin_dW {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Fin 3) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (dW h i)
      = hessSlice dat hdat (vv (coreIdx h i))
          (NpcJet.powCharge dat u (vv (coreIdx h i)) (orderOf u)
            + q (vv (coreIdx h i))) := by
  rw [dW, PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul,
    PWord.evalFin_mul, PWord.evalFin_one, mul_one, PWord.evalFin_inv, PWord.evalFin_gen,
    evalFin_uW dat hdat s u hu hVu vv E E₂ i, hessLift_coreLetter,
    hessSlice_inv dat hdat hV2,
    show WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (NpcJet.powCharge dat u (vv (coreIdx h i)) (orderOf u))
      = hessSlice dat hdat 0 (NpcJet.powCharge dat u (vv (coreIdx h i)) (orderOf u)) from
      rfl,
    hessSlice_mul dat hdat, hdat.f_zero_left, add_zero, zero_add, zero_add]

end Letters


/-! ## §4. Central elements are invisible to squares and commutators

Three laws the `Word/` kit lacks (WW6 supplied six; these are three more of the same kind).
They are what makes the two copies of the procyclic-`M` word *literally equal* on the κ⁰
carrier — the κ⁰-register face of P4's central clause, which here is a theorem rather than
the module hypothesis `CentralReplication` that the Heisenberg register needs. -/

section Central

variable {G : Type*} [Group G]

/-- Conjugation is blind to a central right factor. -/
theorem conjR_mul_central (x y c : G) (hc : ∀ z : G, Commute c z) :
    conjR x (y * c) = conjR x y := by
  calc conjR x (y * c)
      = c⁻¹ * ((y⁻¹ * x * y) * c) := by show (y * c)⁻¹ * x * (y * c) = _; group
    _ = c⁻¹ * (c * (y⁻¹ * x * y)) := by rw [(hc (y⁻¹ * x * y)).eq]
    _ = conjR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

/-- The commutator is blind to a central factor in its left slot. -/
theorem commR_mul_central_left (x y c : G) (hc : ∀ z : G, Commute c z) :
    commR (x * c) y = commR x y := by
  calc commR (x * c) y
      = c⁻¹ * (x⁻¹ * y⁻¹ * x * (c * y)) := by show (x * c)⁻¹ * y⁻¹ * (x * c) * y = _; group
    _ = c⁻¹ * (x⁻¹ * y⁻¹ * x * (y * c)) := by rw [(hc y).eq]
    _ = c⁻¹ * ((x⁻¹ * y⁻¹ * x * y) * c) := by group
    _ = c⁻¹ * (c * (x⁻¹ * y⁻¹ * x * y)) := by rw [← (hc (x⁻¹ * y⁻¹ * x * y)).eq]
    _ = commR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

/-- The commutator is blind to a central factor in its right slot. -/
theorem commR_mul_central_right (x y d : G) (hd : ∀ z : G, Commute d z) :
    commR x (y * d) = commR x y := by
  have hswap : x⁻¹ * (d⁻¹ * y⁻¹) = d⁻¹ * (x⁻¹ * y⁻¹) := by
    rw [← mul_assoc, ← mul_assoc, ((hd x).inv_left.inv_right).eq]
  calc commR x (y * d)
      = d⁻¹ * ((x⁻¹ * y⁻¹ * x * y) * d) := by
        show x⁻¹ * (y * d)⁻¹ * x * (y * d) = _
        rw [mul_inv_rev, show x⁻¹ * (d⁻¹ * y⁻¹) * x * (y * d)
          = x⁻¹ * (d⁻¹ * y⁻¹) * (x * (y * d)) from by group, hswap]
        group
    _ = d⁻¹ * (d * (x⁻¹ * y⁻¹ * x * y)) := by rw [(hd (x⁻¹ * y⁻¹ * x * y)).eq]
    _ = commR x y := by rw [← mul_assoc, inv_mul_cancel, one_mul]; rfl

end Central

section CentralIncl

variable {L : Type} [Group L] {c : WordCoh.TwoCocycle L}

/-- The central inclusion really is central. -/
theorem incl_commute (z : ZMod 2) (p : WordCoh.CentExt c) :
    Commute (WordCoh.CentExt.incl c z) p := by
  refine WordCoh.CentExt.ext ?_ ?_
  · show (1 : L) * WordCoh.CentExt.base p = WordCoh.CentExt.base p * 1
    rw [one_mul, mul_one]
  · show z + WordCoh.CentExt.fib p + c.κ 1 (WordCoh.CentExt.base p)
      = WordCoh.CentExt.fib p + z + c.κ (WordCoh.CentExt.base p) 1
    rw [c.κ_one_left, c.κ_one_right, add_comm z (WordCoh.CentExt.fib p)]

/-- Squares are blind to a central `𝔽₂`-factor (characteristic two). -/
theorem sq_mul_incl (p : WordCoh.CentExt c) (z : ZMod 2) :
    (p * WordCoh.CentExt.incl c z) ^ 2 = p ^ 2 := by
  rw [sq, mul_assoc, ← mul_assoc (WordCoh.CentExt.incl c z) p, (incl_commute z p).eq,
    mul_assoc, ← mul_assoc, centExt_incl_mul_self, mul_one, sq]

end CentralIncl

/-! ## §5. The plus block, and the vanishing boundary δ-letter -/

section PlusBlock

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

omit [Finite C] [Finite V] in
include hdat in
/-- `q` vanishes at the origin — `f_diag` read against `f_zero_left`. -/
theorem q_zero : q (0 : V) = 0 := by
  rw [← hdat.f_diag, hdat.f_zero_left]

omit [Finite C] [Finite V] in
include hdat in
/-- NC2's accumulated charge vanishes at a zero offset. -/
theorem powCharge_zero_vec (cc : C) (k : ℕ) : NpcJet.powCharge dat cc (0 : V) k = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [show NpcJet.normSum cc j (0 : V) = 0 from
      Finset.sum_eq_zero fun i _ => smul_zero _,
    smul_zero, hdat.f_zero_left, factorSet_m_zero dat hdat, add_zero]

/-- **The boundary δ-letter dies exactly.**  `x₂` carries no primal letter at the gate-E
marking, so `δ₂` is the identity — which is why the whole `E₂^pc` block is invisible here
(the value-level face of S4.5's rider (ii)). -/
theorem evalFin_dW_two {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (hv2 : vv (Certificates.x2Idx h) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (dW h 2) = 1 := by
  rw [evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 2,
    show vv (coreIdx h 2) = 0 from hv2,
    powCharge_zero_vec dat hdat, q_zero dat hdat, add_zero]
  rfl

/-- **The plus block's value**: `D₀²[D₀,D₁]` is the central inclusion of the plus form
`Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)` — a word identity, charge-free in both slots (the square law
and the commutator law of the slice calculus are both independent of the δ-letters' charges). -/
theorem evalFin_plusW {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (vv : Fin (2 + 2 * h + 1) → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (plusW h)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q (vv (Certificates.x0Idx h))
            + polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h))) := by
  rw [plusW, MCompact.evalFin_prodList_pair, PWord.evalFin_zpow, PWord.evalFin_comm,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 0,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 1,
    zpow_natCast, NpcBridge.hessSlice_sq_of_npc dat hdat hV2,
    hessSlice_commR dat hdat hV2, NpcBridge.hessSlice_zero_eq_incl, centExt_incl_mul]
  rfl

end PlusBlock


/-! ## §6. The two copies coincide on the κ⁰ carrier

`Sh_M`'s shrink replaces `x₀ ↦ δ₀`, `x₁ ↦ δ₁`, `x₂ ↦ 1` and kills `E₂^pc`.  At the graph-type
κ⁰-marking each replacement changes the value by a **central** factor only (§3: a δ-letter is the
corresponding slice element with a different charge), and `E₂^pc` dies outright because the
boundary δ-letter does.  §4's three laws then say the squares and commutators the row is built
from cannot see the difference — so the hat copy's value **equals** the linear copy's.

⚠ This is the κ⁰-register analogue of WMP-c's `mpcCopiesCancel`, not a transport of it: that
statement sits in the Heisenberg register (`heisEvalZ`, fields `.a/.l/.z`) against a cocycle of
Heisenberg shape, and **no bridge to the κ⁰ extension exists**, nor can one be built by a carrier
identification — the two cocycles are of different shapes.  The compensation is that on this
carrier P4's central clause is not needed: WMP-c's `CentralReplication` hypothesis is here a
theorem, because the two values are literally equal rather than merely centrally equal. -/

section Copies

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

omit [Finite C] [Finite V] in
/-- Splitting a slice charge off as a central factor. -/
theorem hessSlice_add_charge (v : V) (z w : ZMod 2) :
    hessSlice dat hdat v (z + w)
      = hessSlice dat hdat v z * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) w := by
  rw [show WordCoh.CentExt.incl (kappa0Cocycle dat hdat) w = hessSlice dat hdat 0 w from rfl,
    hessSlice_mul dat hdat, hdat.f_zero_right, add_zero, add_zero]

omit [Finite C] [Finite V] in
/-- A slice element is its zero-charge twin times a central factor. -/
theorem hessSlice_eq_zero_mul_incl (v : V) (z : ZMod 2) :
    hessSlice dat hdat v z
      = hessSlice dat hdat v 0 * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z := by
  rw [← hessSlice_add_charge dat hdat, zero_add]

omit [Finite C] [Finite V] in
/-- A central factor slides to the right through any product. -/
theorem mul_incl_mul (x y : WordCoh.CentExt (kappa0Cocycle dat hdat)) (z : ZMod 2) :
    x * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z * y
      = x * y * WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z := by
  rw [mul_assoc, (incl_commute z y).eq, ← mul_assoc]

variable {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite C] [Finite V] in
/-- `Ĉ₀ = σ₂^s` and `C₀ = x₂σ₂^s` have the **same** value: the boundary letter is trivial. -/
theorem evalFin_c0HatW_eq_c0W (hv2 : vv (coreIdx h 2) = 0) (s' : ℕ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (c0HatW h s')
      = PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (c0W h s') := by
  rw [c0W, MCompact.evalFin_prodList_pair, PWord.evalFin_gen, hessLift_coreLetter, hv2,
    hessSlice_zero_zero, one_mul]
  rfl

/-- `Â = δ₀⁻¹Ĉ₀⁻ᵐ` differs from `A = x₀⁻¹C₀⁻ᵐ` by a central factor. -/
theorem evalFin_aHatW_eq (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0) (s' mm : ℕ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (aHatW h s' mm)
      = PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (aW h s' mm)
        * WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (NpcJet.powCharge dat u (vv (coreIdx h 0)) (orderOf u)
              + q (vv (coreIdx h 0))) := by
  rw [aHatW, aW, MCompact.evalFin_prodList_pair, MCompact.evalFin_prodList_pair,
    PWord.evalFin_inv, PWord.evalFin_inv, PWord.evalFin_zpow, PWord.evalFin_zpow,
    PWord.evalFin_gen, hessLift_coreLetter,
    evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 0,
    evalFin_c0HatW_eq_c0W dat hdat s u vv E E₂ hv2 s',
    hessSlice_inv dat hdat hV2, hessSlice_inv dat hdat hV2, zero_add,
    show NpcJet.powCharge dat u (vv (coreIdx h 0)) (orderOf u)
        + q (vv (coreIdx h 0)) + q (vv (coreIdx h 0))
      = q (vv (coreIdx h 0))
        + (NpcJet.powCharge dat u (vv (coreIdx h 0)) (orderOf u)
          + q (vv (coreIdx h 0))) from by abel,
    hessSlice_add_charge dat hdat, mul_incl_mul dat hdat]

/-- `B̂ = δ₁σ₂^p` differs from `B = x₁σ₂^p` by a central factor, in both emitted displays. -/
theorem evalFin_bHatW_eq (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) : ∀ pp : ℕ,
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (bHatW h pp)
      = PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (bW h pp)
        * WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (NpcJet.powCharge dat u (vv (coreIdx h 1)) (orderOf u) + q (vv (coreIdx h 1)))
  | 0 => by
      rw [show bHatW h 0 = dW h 1 from rfl, show bW h 0 = .gen (coreLetter h 1) from rfl,
        PWord.evalFin_gen, hessLift_coreLetter,
        evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 1,
        hessSlice_eq_zero_mul_incl dat hdat]
  | pp + 1 => by
      rw [show bHatW h (pp + 1) = PWord.prodList [dW h 1, sig2PowW h (pp + 1)] from rfl,
        show bW h (pp + 1)
          = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (pp + 1)] from rfl,
        MCompact.evalFin_prodList_pair, MCompact.evalFin_prodList_pair, PWord.evalFin_gen,
        hessLift_coreLetter, evalFin_dW dat hdat hV2 s u hu hVu vv E E₂ 1,
        hessSlice_eq_zero_mul_incl dat hdat, mul_incl_mul dat hdat]

/-- The orbit-norm base `z = δ₂δ₂^{σ₂^p}` dies, in both emitted displays. -/
theorem evalFin_zW_one (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0) : ∀ pp : ℕ,
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (zW h pp) = 1
  | 0 => by
      rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl, PWord.evalFin_zpow,
        evalFin_dW_two dat hdat hV2 s u hu hVu vv hv2 E E₂, one_zpow]
  | pp + 1 => by
      rw [show zW h (pp + 1)
          = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (pp + 1))] from rfl,
        MCompact.evalFin_prodList_pair, PWord.evalFin_conj,
        evalFin_dW_two dat hdat hV2 s u hu hVu vv hv2 E E₂, one_conjR, mul_one]

/-- **`E₂^pc` is invisible at the gate-E marking** — every letter in it is a `δ₂`, and `δ₂ = 1`
because `x₂` carries no primal letter.  The orbit-norm node needs no `orbitNorm_eq`: it is a
product of conjugates of the identity. -/
theorem evalFin_e2W_one (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0) (s' mm pp : ℕ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (e2W h s' mm pp) = 1 := by
  have hz : ∀ w ∈ Export.orbitNormFactors (zW h pp) (.zpow sigma2W (s' : ℤ)) mm,
      PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ w = 1 := by
    intro w hw
    rw [Export.orbitNormFactors, List.mem_map] at hw
    obtain ⟨j, -, rfl⟩ := hw
    rw [PWord.evalFin_conj, evalFin_zW_one dat hdat s u vv E E₂ hV2 hu hVu hv2 pp, one_conjR]
  have hprod : ∀ l : List (PWord (Generator (2 + 2 * h))),
      (∀ w ∈ l, PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ w = 1) →
      PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (PWord.prodList l) = 1 := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons a l ih =>
        intro hl
        rw [PWord.prodList_cons, PWord.evalFin_mul, hl a (by simp),
          ih (fun w hw => hl w (by simp [hw])), one_mul]
  rw [e2W, MCompact.evalFin_prodList_pair, PWord.evalFin_conj, PWord.evalFin_conj,
    evalFin_dW_two dat hdat hV2 s u hu hVu vv hv2 E E₂, one_conjR, one_mul, hprod _ hz,
    one_conjR]

/-- **The hat copy's value is the linear copy's**, at every `(α, r, p, η, h)` and every
graph-type marking with `x₂`-slot zero.  This is the κ⁰-register self-replication statement. -/
theorem evalFin_mpcHatW_eq_mpcLinW (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0)
    (α r pp : ℕ) (η : EtaDisplay) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcHatW α r pp η h)
      = PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcLinW α r pp η h) := by
  rw [mpcHatW, mpcLinW, hatFactors, linFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, PWord.evalFin_mul, PWord.evalFin_one,
    PWord.evalFin_zpow, PWord.evalFin_comm, mul_one]
  rw [evalFin_e2W_one dat hdat s u vv E E₂ hV2 hu hVu hv2, mul_one,
    evalFin_aHatW_eq dat hdat s u vv E E₂ hV2 hu hVu hv2,
    evalFin_bHatW_eq dat hdat s u vv E E₂ hV2 hu hVu,
    evalFin_c0HatW_eq_c0W dat hdat s u vv E E₂ hv2,
    zpow_natCast, zpow_natCast, sq_mul_incl, ← zpow_natCast, ← zpow_natCast,
    commR_mul_central_left _ _ _ (fun z => incl_commute _ z),
    commR_mul_central_right _ _ _ (fun z => incl_commute _ z)]

end Copies


/-! ## §7. The jet theorem, and WW4 gap item 5 on the procyclic-`M` row -/

section Factored

variable {G : Type*} [Group G] {h : ℕ} (μ : Generator (2 + 2 * h) → G) (E : Zhat → ℤ)
  (E₂ : ℤ_[2] → ℤ)

/-- `evalFin` of a `prodList` (the `evalFin` twin of `Words.Mpc.eval_prodListM`).

W51-HOIST dedup: this was a second copy of `GQ2.Dyadic.evalFin_prodList` (`Word/Fox.lean`),
specialised to `Generator (2 + 2 * h)` and repeating the same list induction.  The statement is
kept, because the three call sites below rewrite with it and depend on its eta-expanded
right-hand side; only the proof changes, and it is now the generic lemma. -/
theorem evalFin_prodListM :
    ∀ ws : List (PWord (Generator (2 + 2 * h))),
      PWord.evalFin μ E E₂ (PWord.prodList ws) = (ws.map (PWord.evalFin μ E E₂ ·)).prod :=
  evalFin_prodList μ E E₂

/-- The displayed factorization at the `evalFin` denotation — the twin of
`Words.Mpc.eval_mpcW_factored`, which is stated for `Marking.eval` only. -/
theorem evalFin_mpcW_factored (α r pp : ℕ) (η : EtaDisplay) :
    PWord.evalFin μ E E₂ (mpcW α r pp η h)
      = PWord.evalFin μ E E₂ (mpcLinW α r pp η h) * PWord.evalFin μ E E₂ (mpcHatW α r pp η h)
        * PWord.evalFin μ E E₂ (plusW h) * PWord.evalFin μ E E₂ (handlesW h) := by
  have htail : ((handleTailW h).map (PWord.evalFin μ E E₂ ·)).prod
      = PWord.evalFin μ E E₂ (handlesW h) := by
    match h with
    | 0 => simp [handleTailW, handlesW]
    | h + 1 => simp [handleTailW]
  rw [mpcW, mpcLinW, mpcHatW, plusW, evalFin_prodListM, evalFin_prodListM, evalFin_prodListM,
    evalFin_prodListM, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append, htail]

end Factored

section Jet

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

variable {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- The base coordinate of a κ⁰-evaluation is the plain evaluation (one `map_evalFin` line). -/
theorem base_evalFin_hessLift (w : PWord (Generator (2 + 2 * h))) :
    WordCoh.CentExt.base (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ w)
      = PWord.evalFin (Certificates.hessMark s u vv) E E₂ w :=
  PWord.map_evalFin (WordCoh.CentExt.proj (kappa0Cocycle dat hdat))
    (hessLift dat hdat (h := h) s u vv) E E₂ w

/-- **The linear copy carries no primal offset at the gate-E marking.**

This is WMP-d's row collapse `D(R_lin^pc)(a) = S₂^{−s}σ^{−n}a(x₂)` consumed through §1's
register bridge: the row is supported on the `x₂`-column alone, and the gate-E marking gives
`x₂` no primal letter.  Nothing about the row is re-derived here. -/
theorem base_fst_mpcLinW (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V) :
    (PWord.evalFin (Certificates.hessMark s u vv) E E₂ (mpcLinW α r pp η h)).1 = 0 := by
  rw [evalFin_hessMark_fst s u vv E E₂,
    foxD_mpcLinW_x2 (lowerMark (h := h) s u) E E₂ (hessOffsets vv) rfl
      (fun i w => by rw [coreMark_x]; exact one_smul _ _) hVu
      (fun w => by rw [coreMark_tau, powOmega2_eq_one_of_odd hu]; exact one_smul _ _)
      hα r pp hη hV2,
    show hessOffsets vv (coreLetter h 2) = 0 from hv2, smul_zero, smul_zero]

/-- **The two copies contribute nothing to the Hessian.**

`val(R̂^pc) = val(R_lin^pc)` (§6), so the pair is a *square*; and the square of an element whose
primal offset vanishes is central with fibre `κ` at a zero offset, which is `0`.  No
`CentralReplication` hypothesis is needed — the κ⁰-register replacement for P4's central clause
is §6's literal equality. -/
theorem fib_mpcLinW_mul_mpcHatW (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcLinW α r pp η h)
          * PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcHatW α r pp η h))
      = 0 := by
  have hb : (WordCoh.CentExt.base
      (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcLinW α r pp η h))).1 = 0 := by
    rw [base_evalFin_hessLift dat hdat s u vv E E₂]
    exact base_fst_mpcLinW s u vv E E₂ hV2 hu hVu hv2 hα r pp hη
  rw [evalFin_mpcHatW_eq_mpcLinW dat hdat s u vv E E₂ hV2 hu hVu hv2 α r pp η,
    WordCoh.CentExt.mul_fib, CharTwo.add_self_eq_zero, zero_add, kappa0Cocycle_κ, hb,
    smul_zero, hdat.f_zero_left, factorSet_m_zero dat hdat, add_zero]

/-- **The `mpcW` jet theorem** — the `npc_cross_operators` analogue for the frozen procyclic-`M`
word, at general `(α ≥ 1, r, p, η, h)`.

The evaluated Hessian of `R_lin^pc·R̂^pc·D₀²[D₀,D₁]` at the graph-type κ⁰-marking is the plus
form `Q₊(c₀,c₁) = q(c₀) + b_q(c₀,c₁)`: the two copies cancel (§6 + WMP-d's row collapse) and the
plus block survives (§5). -/
theorem mpc_cross_operators (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (coreIdx h 2) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcLinW α r pp η h)
            * PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcHatW α r pp η h)
          * PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (plusW h))
      = q (vv (coreIdx h 0)) + polar q (vv (coreIdx h 0)) (vv (coreIdx h 1)) := by
  rw [WordCoh.CentExt.mul_fib,
    fib_mpcLinW_mul_mpcHatW dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη, zero_add,
    evalFin_plusW dat hdat hV2 s u hu hVu vv E E₂, WordCoh.CentExt.incl_fib,
    WordCoh.CentExt.incl_base, (kappa0Cocycle dat hdat).κ_one_right, add_zero]
  rfl

/-- **The jet theorem at the frozen word**, `h = 0`: the evaluated Hessian of `mpcW` itself is
`plusFormD q q (c₀, c₁)` — the endpoint polynomial of `mpcHessianCertificate` with the diagonal
`d₀` **pinned to `q`**. -/
theorem evalFin_fib_mpcW (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := 0) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s u) E E₂ (η.toPWord (n := 2 + 2 * 0))) V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.evalFin (hessLift dat hdat (h := 0) s u ![c₀, c₁, 0]) E E₂ (mpcW α r pp η 0))
      = plusFormD q q (c₀, c₁) := by
  rw [evalFin_mpcW_factored, handlesW_zero, PWord.evalFin_one, mul_one,
    mpc_cross_operators dat hdat s u ![c₀, c₁, 0] E E₂ hV2 hu hVu rfl hα r pp hη,
    plusFormD_apply]
  rfl

end Jet


/-! ## §8. `hessRelZ`, WW4 gap item 5, and the `√−10` instance (merge gate 9) -/

section Target

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V] (s u : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The word-side Hessian equation for the procyclic-`M` row.**

The `hessRelZ` (resolver-driven) form of the jet theorem.  The single hypothesis separating the
two registers is WMP-c's own `ResolverLifts` — the standing "resolvers correct at the lift level"
discipline — and nothing else: unlike the procyclic-`N` row this row needs no `ResolvedAt`. -/
theorem hessRelZ_mpcW (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := 0) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s u) E E₂ (η.toPWord (n := 2 + 2 * 0))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mpcW α r pp η 0)
      = plusFormD q q (c₀, c₁) := by
  rw [hessRelZ, hessEvalZ, evalZ_eq_evalFin_of_resolverLifts hres]
  exact evalFin_fib_mpcW dat hdat s u E E₂ hV2 hu hVu c₀ c₁ hα r pp hη

/-- **WW4 gap item 5, DISCHARGED on the procyclic-`M` row** — WW6's `mpcHessRelZTarget`, at the
diagonal `d₀` **pinned to `q`**.

The pinning is a *consequence* of the jet computation, not an input: the plus block's two laws
(the slice square law and the slice commutator law) are both charge-free, so the δ-letters'
`TwistedClass2Domain` charges cancel and the surviving diagonal is `q = fun v ↦ dat.f v v`
(`f_diag`) — the compact rows' spelling after all. -/
theorem mpc_hessRelZTarget (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := 0) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s u) E E₂ (η.toPWord (n := 2 + 2 * 0))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    NpcBridge.mpcHessRelZTarget dat hdat q s u c₀ c₁ α r pp η E E₂ := by
  rw [NpcBridge.mpcHessRelZTarget_iff,
    hessRelZ_mpcW dat hdat s u E E₂ hV2 hu hVu c₀ c₁ hα r pp hη hres, plusFormD_apply]

/-- **The honest profinite reading.**  At an `ω₂`-only `η`-display the genuine `Marking.eval`
value has the same fibre — WW6's resolver-immunity (`mpc_eval_eq_hessRelZ`) consumed at the
jet theorem. -/
theorem mpc_hess_eval (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ} (hη2 : η.IsOmega2Only)
    (hη : ActsAsPow (lowerMark (h := 0) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s u) E E₂ (η.toPWord (n := 2 + 2 * 0))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((Marking.mk (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
          (kappa0Cocycle dat hdat))).eval (mpcW α r pp η 0))
      = plusFormD q q (c₀, c₁) := by
  rw [NpcBridge.mpc_eval_eq_hessRelZ dat hdat s u c₀ c₁ α r pp hη2 E E₂
      (fun x => by rw [zpowHat_omega2, hres x])]
  exact hessRelZ_mpcW dat hdat s u E E₂ hV2 hu hVu c₀ c₁ hα r pp hη hres

/-! ### Merge gate 9 — the `ℚ₂(√−10)` row at second order

`(α, r, p, η, h) = (2, 1, 1, .one, 0)`.  WMP-d closed the gate at the Fox level
(`sqrtNeg10ProductRowCert`'s last input); this is the second-order counterpart, with the
`η`-datum definitional rather than hypothetical (`actsAsPow_etaOne`). -/

/-- **The `√−10` jet value**: the gate-9 word's evaluated Hessian is the plus form. -/
theorem sqrtNeg10_hessRelZ (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mpcW 2 1 1 .one 0)
      = plusFormD q q (c₀, c₁) :=
  hessRelZ_mpcW dat hdat s u E E₂ hV2 hu hVu c₀ c₁ (by norm_num) 1 1
    (actsAsPow_etaOne (lowerMark (h := 0) s u) E E₂) hres

/-- **Merge gate 9's second-order row, discharged.** -/
theorem sqrtNeg10_hessRelZTarget (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (c₀ c₁ : V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    NpcBridge.mpcHessRelZTarget dat hdat q s u c₀ c₁ 2 1 1 .one E E₂ :=
  mpc_hessRelZTarget dat hdat s u E E₂ hV2 hu hVu c₀ c₁ (by norm_num) 1 1
    (actsAsPow_etaOne (lowerMark (h := 0) s u) E E₂) hres

/-- **The `√−10` word's evaluated Hessian, as a function of the offsets, IS the endpoint
polynomial** of `mpcHessianCertificate` at `d₀ = q` — the identity-CoV connection, functionally.
This is the shape `nCompact_word_eq_certQ` has on the compact-`N` row. -/
theorem sqrtNeg10_word_eq_certQ (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    (fun p : V × V => hessRelZ (Certificates.hessMark (h := 0) s u ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mpcW 2 1 1 .one 0))
      = plusFormD q q :=
  funext fun p => sqrtNeg10_hessRelZ dat hdat s u E E₂ hV2 hu hVu p.1 p.2 hres

end Target

end GQ2.Dyadic.Certificates.MpcJet
