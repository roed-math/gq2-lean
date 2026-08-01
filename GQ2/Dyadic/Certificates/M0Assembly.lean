/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Certificates.M0

/-!
# Dyadic campaign, ticket WM0-d: the compact-`M` Hessian assembly

The closing leaf of the compact-`M` lane.  WM0-c
(`GQ2/Dyadic/Certificates/M0.lean`) built the κ⁰ slice calculus for freeze row 4 and
documented one residual honestly: the single-equation Hessian assembly.  This file is
that residual, discharged.

```
R_{M,0} = A₀² [A₀,x₁] σ₂^{2m} · J₂ · E_m^rev · H_h,
A₀ = x₀⁻¹σ₂⁻ᵐ,  J₂ = x₂^{-σ}(x₂τ)^{ω₂},  E_m^rev = δ₁^{σ₂^{2m}}δ₁^{σ₂^m}δ₀^{σ₂^m}δ₀,  m = 2^{α−1}
```

## 1. The transport lemma

`commR_mul_right_of_commute`: `[a·L, b] = [a, b]` whenever `L` commutes with `a` and with
`b`.  This is the lemma WM0-c named.  Its **final form carries two side conditions, not
one**, and both are honest:

* `Commute L b` is what lets `L` slide out of the middle of `a⁻¹b⁻¹(aL)b`;
* `Commute L a` is consumed **only** through the derived `Commute L [a,b]`, which is what
  conjugates the surviving commutator back to itself.

Neither can be dropped: with `L` central in `b` alone one gets `[a·L, b] = L⁻¹[a,b]L`, and
that is not `[a,b]` in a group where the commutator is noncentral.  In the application both
hypotheses are one and the same fact — `hessM_line_comm`, WM0-c's gate-E commutation — so
the two-hypothesis form costs nothing at the call site.  The companion
`conjR_eq_self_of_commute` (`x^g = x` when `g` commutes with `x`) is the same mechanism for
the correction block's three conjugated `δ`-letters.

## 2. The charged `C`-line, and why the bookkeeping closes

The six factors are chained through one small subgroup: the **charged `C`-line**
`hessLineZ c z = ((0,c), z)`, which is `hessLine` with a central charge (and contains both
`hessLine c = hessLineZ c 0` and `WordCoh.CentExt.incl z = hessLineZ 1 z`).  Its product law
`hessLineZ_mul` is *diagonal* —

```
hessLineZ c z · hessLineZ d w = hessLineZ (c·d) (z + w)
```

— because a κ⁰-cocycle value `f(0, c•0) + m_c(0)` vanishes on it (`f_zero_left`,
`factorSet_m_zero`).  Every factor of `R_{M,0}` lands there, at both projector branches:

| factor | value | mechanism |
| --- | --- | --- |
| `A₀²` | `hessLineZ (g^{−m}g^{−m}) (q c₀)` | `hessSlice_sq` after `Commute.mul_pow` |
| `[A₀,x₁]` | `hessLineZ 1 (b_q(c₀,c₁))` | the transport lemma, then `hessSlice_commR` |
| `σ₂^{2m}` | `hessLineZ (g^{2m}) 0` | `hessM_sigma2Pow` |
| `J₂` | `hessLineZ (u^{ω₂}) 0` | `x₂` carries no primal letter, exactly as in the pilot |
| `E_m^rev` | `hessLineZ 1 0` (`P=1`) / `hessLineZ 1 (q c₁ + q c₀)` (`P=0`) | `hessDeltaCert_P{1,0}` |
| `H_h` | `hessLineZ 1 (Σⱼ b_q(dⱼ,eⱼ))` | the pilot's `hess_handlesW_eval` |

so the whole word is one `hessLineZ`, whose `C`-coordinate is
`g^{−m}g^{−m}·g^{2m}·u^{ω₂}` — the packet's power balance `−2·2^{α−1} + 2^α = 0` leaves the
boundary line alone — and whose fibre is the sum of the column.  The fibre is the answer;
the `C`-coordinate is never inspected, which is why the opaque atom `D(σ₂)` stays opaque
here as it does at Stokes level.

**WM0-c's paper arithmetic, confirmed.**  At `P = 0` the correction block contributes
`q(c₀) + q(c₁)`, so the core's `q(c₀) + b_q(c₀,c₁)` becomes
`q(c₀) + b_q(c₀,c₁) + q(c₀) + q(c₁) = q(c₁) + b_q(c₀,c₁)` in characteristic 2 — **the block
swap is what the correction block performs**, now a theorem
(`hessRelZ_mCompact_P0`) and not a paper computation.

## 3. The two assembly equations

At general handle count `h`, with the `Σⱼ b_q(dⱼ,eⱼ)` tail the pilot's equation carries:

```
hessRelZ_mCompact_P1 :  q(c₀) + b_q(c₀,c₁) + Σⱼ b_q(dⱼ,eⱼ)
hessRelZ_mCompact_P0 :  q(c₁) + b_q(c₀,c₁) + Σⱼ b_q(dⱼ,eⱼ)
```

landing at `h = 0` on WW4's two endpoints: `compactM_P1_certificate`'s `plusFormD q q`
(identity CoV — literally `compactN_certificate`, S4.1's finding (i)) and
`compactM_P0_certificate`'s `fun p ↦ q p.2 + b_q(p.1, p.2)` (the `(c₀,c₁)` block-swap CoV).
The Gauss residues follow through `HessianCertificate.endpoint_gaussSum`, and are **equal**
on the two branches — the block swap is an isometry.

The projector branch enters exactly where WM0-b and WM0-c put it: as a hypothesis on the
evaluated `ω₂`-block, per `δ`-letter.  At `P = 1` that hypothesis is *discharged* by WM0-c's
`hessDeltaBlock_P1` (at `u = 1` and the honest class `e ≡ 1 mod 4`), so
`hessRelZ_mCompact_P1_res` and everything downstream of it is hypothesis-free apart from the
resolver pin.  At `P = 0` it stays a hypothesis — it is the ramified reading, and nothing in
this lane discharges it.

⚠ **No unconditional profinite twin of the pilot's `sqrtNegTwo_hess_eval`.**  The pilot's
honest `Marking.eval` row needs no `ω₂`-representative pin because its boundary block dies on
the `C`-line at *every* exponent.  The compact-`M` row has a second `ω₂`-block — the
correction block — and that one is resolver-sensitive (this is the Hessian-level twin of
WM0-c's Stokes deviation, "the assembled row is stated at `e ≡ 1 (mod 4)`, not exact in
`e`").  So `mCompact_hess_eval_P1`/`_P0` carry the branch hypothesis at the resolved
exponent, and say so.

## 4. Scope

Assembly only.  Nothing here restates WM0-c's layer, touches the order-rejection material
(complete), or attempts the seventeenth-root pin (a `GQ2/QuadraticFp2.lean` API item per
WM0-c's size-wall note).  `GQ2/Dyadic/Certificates/M0.lean` is not edited.

## Implementation notes

Not `module`-style, and forced: `GQ2.Dyadic.Certificates.M0` is plain-import.  No new axioms;
kernel `decide` only (in fact none is needed).  The `deltaC` → `deltaCert` rename is WM0-b's
and is repeated here for the same reason (the peripheral `GQ2.deltaC` wins the resolution
race).  WM0-c's `mk` marking abbreviation is `private`, so the lifted marking is spelled out;
`rw` still fires through it, since `abbrev` is reducible.

## Axiom state (audited; `#print axioms` run in a scratch file, not committed)

Zero `sorryAx`, zero `native_decide`, no `GQ2.AbsGalQ2` B-axiom leaks.  All headlines —
`commR_mul_right_of_commute`, `hessLineZ_mul`, `hessM_a0W`, `hessM_leadingSquare`,
`hessM_leadingComm`, `hessM_j2W`, `hessM_eRevW_P1`, `hessM_eRevW_P0`, `hessM_handleTailW`,
`hessRelZ_mCompact_P1`, `hessRelZ_mCompact_P0`, `hessRelZ_mCompact_P1_res`,
`hessRelZ_mCompact_P1_plusForm`, `hessRelZ_mCompact_P0_swapForm`,
`mCompact_P1_word_gaussSum`, `mCompact_P0_word_gaussSum`, `mCompact_hess_eval_P1`,
`mCompact_hess_eval_P0`, `sqrtTwo_hessRelZ_P1`, `sqrtTwo_hessRelZ_P0`,
`sqrtFive_hessRelZ_P1`, `sqrtFive_hessRelZ_P0`, `sqrtTwo_hess_gaussSum`,
`sqrtFive_hess_gaussSum` — print exactly the standard three
`[propext, Classical.choice, Quot.sound]`.  The census stays at eleven.
-/

namespace GQ2.Dyadic.Certificates.MCompact

open GQ2.FoxH GQ2.Dyadic.Words.MCompact

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## 1. The transport lemma

WM0-c's named residual, in the form the assembly consumes it. -/

section Transport

variable {G : Type*} [Group G]

/-- **The transport lemma**: a factor `L` commuting with both entries of a commutator may be
dropped from the left entry, `[a·L, b] = [a, b]`.

The two hypotheses do different work.  `hLb` slides `L` out of the middle of
`L⁻¹a⁻¹b⁻¹(aL)b`; `hLa` is consumed **only** to conjugate the surviving `[a,b]` back to
itself (`Commute L a` and `Commute L b` together give `Commute L [a,b]`).  Without `hLa` the
honest conclusion is `[a·L, b] = L⁻¹[a,b]L`, which is strictly weaker.  Both hypotheses come
from one source at the call site — WM0-c's `hessM_line_comm`, the gate-E commutation — so
the two-hypothesis form is free in practice. -/
theorem commR_mul_right_of_commute {a b L : G} (hLa : Commute L a) (hLb : Commute L b) :
    commR (a * L) b = commR a b := by
  have hc : Commute L (commR a b) :=
    ((hLa.inv_right.mul_right hLb.inv_right).mul_right hLa).mul_right hLb
  calc commR (a * L) b = L⁻¹ * (a⁻¹ * b⁻¹ * (a * (L * b))) := by rw [commR]; group
    _ = L⁻¹ * (a⁻¹ * b⁻¹ * (a * (b * L))) := by rw [hLb.eq]
    _ = L⁻¹ * (commR a b * L) := by rw [commR]; group
    _ = L⁻¹ * (L * commR a b) := by rw [hc.eq]
    _ = commR a b := inv_mul_cancel_left _ _

/-- The conjugation twin of the transport lemma: a commuting conjugator does nothing.  This
is what dissolves the three `σ₂`-conjugations of the correction block at the `P = 0`
branch. -/
theorem conjR_eq_self_of_commute {x g : G} (hgx : Commute g x) : conjR x g = x := by
  rw [conjR, hgx.inv_left.eq, mul_assoc, inv_mul_cancel, mul_one]

end Transport

/-! ## 2. The charged `C`-line

`hessLineZ c z = ((0,c), z)`: the κ-free `C`-line of WW4's slice calculus, carrying a central
charge.  It contains `hessLine` (charge `0`) and `WordCoh.CentExt.incl` (base `1`), and its
product law is diagonal, which is the entire bookkeeping device of this file. -/

section ChargedLine

open GQ2.SectionSix

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The charged `C`-line** `((0,c), z)` of the κ⁰-extension. -/
def hessLineZ (c : C) (z : ZMod 2) : WordCoh.CentExt (kappa0Cocycle dat hdat) := ((0, c), z)

@[simp] theorem hessLineZ_fib (c : C) (z : ZMod 2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat) (hessLineZ dat hdat c z) = z := rfl

/-- The uncharged line is WW4's `hessLine`. -/
theorem hessLineZ_line (c : C) : hessLineZ dat hdat c 0 = hessLine dat hdat c := rfl

/-- The based line is the central inclusion. -/
theorem hessLineZ_incl (z : ZMod 2) :
    hessLineZ dat hdat 1 z = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z := rfl

theorem hessLineZ_one : hessLineZ dat hdat 1 0 = 1 := rfl

include hdat in
/-- **The diagonal product law.**  The κ⁰-correction of a product of charged `C`-line elements
is `f(0, c•0) + m_c(0) = 0` — `f_zero_left` and the derived `factorSet_m_zero` — so bases
multiply and charges add, with no cross term.  This is what makes the six-factor bookkeeping
of `R_{M,0}` a two-column sum. -/
theorem hessLineZ_mul (c d : C) (z w : ZMod 2) :
    hessLineZ dat hdat c z * hessLineZ dat hdat d w = hessLineZ dat hdat (c * d) (z + w) := by
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show (0 : V) + c • (0 : V) = 0
    rw [smul_zero, add_zero]
  · rfl
  · show z + w + (dat.f 0 (c • (0 : V)) + dat.m c 0) = z + w
    rw [smul_zero, hdat.f_zero_left, factorSet_m_zero dat hdat, add_zero, add_zero]

include hdat in
/-- A central charge times a line is the charged line — the normal form every factor is
rewritten into. -/
theorem incl_mul_hessLine (c : C) (z : ZMod 2) :
    WordCoh.CentExt.incl (kappa0Cocycle dat hdat) z * hessLine dat hdat c
      = hessLineZ dat hdat c z := by
  rw [← hessLineZ_incl, ← hessLineZ_line, hessLineZ_mul dat hdat, one_mul, add_zero]

end ChargedLine

/-! ## 3. The six factors

Each factor of `R_{M,0}` evaluated at the graph-type κ⁰-marking `hessMark`, in the charged
`C`-line normal form.  WM0-c's `mk` abbreviation is `private`, so the lifted marking is
spelled out. -/

section Factors

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  {h α : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- `m` is even for `α ≥ 2` — the one arithmetic fact the whole gate-E commutation rests on
(`m = 2^{α−1}`), in the `ℤ`-form `hessM_line_comm` consumes. -/
theorem even_mOf_int (hα : 2 ≤ α) : Even ((mOf α : ℤ)) := by
  obtain ⟨j, hj⟩ := even_mOf hα
  exact ⟨(j : ℤ), by rw [hj]; push_cast; ring⟩

/-- …and so is `−m`, the exponent inside `A₀`. -/
theorem even_neg_mOf (hα : 2 ≤ α) : Even (-(mOf α : ℤ)) := (even_mOf_int hα).neg

/-- `2m` is even, trivially — the exponent of the word's third factor. -/
theorem even_two_mul_mOf : Even (2 * (mOf α : ℤ)) := even_two_mul _

/-- **The Labute letter `A₀ = x₀⁻¹σ₂^{−m}`** on the κ⁰-slice: the inverted `x₀`-slice (with the
`q`-charge of inversion) times the `C`-line element `σ₂^{−m}`. -/
theorem hessM_a0W (hV2 : ∀ v : V, v + v = 0) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (a0W α h)
      = hessSlice dat hdat (vv (xIdx h 0)) (q (vv (xIdx h 0)))
        * hessLine dat hdat ((s ^ E omega2) ^ (-(mOf α : ℤ))) := by
  rw [a0W, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [PWord.evalZ_inv, PWord.evalZ_gen,
    show WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)
        (coreLetter h 0) = hessSlice dat hdat (vv (xIdx h 0)) 0 from rfl,
    hessSlice_inv dat hdat hV2, zero_add, hessM_sigma2Pow]

include hdat in
/-- The `σ₂`-half of `A₀` commutes with every slice: `hessM_line_comm` at the even exponent
`−m`.  This single fact supplies **both** hypotheses of the transport lemma. -/
theorem hessM_a0W_line_commute (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) (hα : 2 ≤ α)
    (w : V) (z : ZMod 2) :
    Commute (hessLine dat hdat ((s ^ E omega2) ^ (-(mOf α : ℤ)))) (hessSlice dat hdat w z) :=
  hessM_line_comm dat hdat s E hS₂ (even_neg_mOf hα) w z

/-- **Factor 1 — `A₀²`.**  `Commute.mul_pow` splits the square, WW4's charge-independent
`hessSlice_sq` turns the slice half into `ι(q c₀)`, and the two `C`-line halves merge.  No
`α`-parity is consumed beyond the evenness of `m` that the commutation already needed. -/
theorem hessM_leadingSquare (hV2 : ∀ v : V, v + v = 0)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) (hα : 2 ≤ α) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (.zpow (a0W α h) 2)
      = hessLineZ dat hdat
          ((s ^ E omega2) ^ (-(mOf α : ℤ)) * (s ^ E omega2) ^ (-(mOf α : ℤ)))
          (q (vv (xIdx h 0))) := by
  have hcomm := (hessM_a0W_line_commute dat hdat s E hS₂ hα
    (vv (xIdx h 0)) (q (vv (xIdx h 0)))).symm
  rw [PWord.evalZ_zpow, hessM_a0W dat hdat s u vv E E₂ hV2,
    show ((2 : ℤ)) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, hcomm.mul_pow, sq, sq,
    hessSlice_sq dat hdat hV2, hessLine_mul dat hdat, incl_mul_hessLine dat hdat]

/-- **Factor 2 — `[A₀, x₁]`.**  The transport lemma retires the `σ₂`-half of `A₀`, and WW4's
`hessSlice_commR` returns the hyperbolic cross `b_q(c₀,c₁)` as a central charge.  This is the
step WM0-c could not take: it is exactly `commR (a·L) b = commR a b`. -/
theorem hessM_leadingComm (hV2 : ∀ v : V, v + v = 0)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) (hα : 2 ≤ α) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (.comm (a0W α h) (.gen (coreLetter h 1)))
      = hessLineZ dat hdat 1 (polar q (vv (xIdx h 0)) (vv (xIdx h 1))) := by
  rw [PWord.evalZ_comm, hessM_a0W dat hdat s u vv E E₂ hV2, PWord.evalZ_gen,
    show WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)
        (coreLetter h 1) = hessSlice dat hdat (vv (xIdx h 1)) 0 from rfl,
    commR_mul_right_of_commute
      (hessM_a0W_line_commute dat hdat s E hS₂ hα (vv (xIdx h 0)) (q (vv (xIdx h 0))))
      (hessM_a0W_line_commute dat hdat s E hS₂ hα (vv (xIdx h 1)) 0),
    hessSlice_commR dat hdat hV2, hessLineZ_incl]

/-- **Factor 3 — `σ₂^{2m}`**, the balancing `C`-line power. -/
theorem hessM_sigma2Pow_line :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (.zpow sigma2W (2 * (mOf α : ℤ)))
      = hessLineZ dat hdat ((s ^ E omega2) ^ (2 * (mOf α : ℤ))) 0 := by
  rw [hessM_sigma2Pow, hessLineZ_line]

/-- **Factor 4 — the boundary block `J₂ = x₂^{-σ}(x₂τ)^{ω₂}`.**  With `x₂` carrying no primal
letter (the ratified boundary convention) the conjugated half is trivial and the `ω₂`-block
lives on the κ-free `C`-line — the pilot's mechanism, verbatim, and resolver-immune. -/
theorem hessM_j2W (hv2 : vv (xIdx h 2) = 0) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (j2W h)
      = hessLineZ dat hdat (u ^ E omega2) 0 := by
  have hx2 : WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)
      (coreLetter h 2) = 1 := by
    show hessSlice dat hdat (vv (xIdx h 2)) 0 = 1
    rw [hv2]
    rfl
  rw [j2W, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, hx2, one_conjR,
    inv_one, one_mul, PWord.omega2Pow, PWord.evalZ_profPow, PWord.prodList_cons,
    PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul, PWord.evalZ_mul,
    PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one, hx2, one_mul,
    show WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) Generator.tau
      = hessLineHom dat hdat u from rfl, ← map_zpow]
  rfl

/-- **Factor 5 at `P = 1` — the correction block is trivial.**  Every `δ`-letter is `1`
(`hessDeltaCert_P1`: `d_i = (1+P)c_i = 0`), so all four conjugated factors are, and the
compact-`M` word's Hessian row **is** the compact-`N` word's — S4.1's finding (i) at the
Hessian level. -/
theorem hessM_eRevW_P1
    (hδ : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
      (kappa0Cocycle dat hdat)) E E₂ (deltaCert h i) = 1) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (eRevW α h)
      = hessLineZ dat hdat 1 0 := by
  rw [show eRevW α h
      = PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))
          (PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))
            (PWord.mul (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))
              (PWord.mul (deltaCert h 0) PWord.one))) from rfl]
  simp only [PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_one, hδ, one_conjR, mul_one]
  rfl

/-- **Factor 5 at `P = 0` — the correction block contributes `q(c₀) + q(c₁)`.**  Every
`δ`-letter is its own slice letter (`hessDeltaCert_P0`: `d_i = (1+P)c_i = c_i`), the three
`σ₂`-conjugations dissolve because their conjugators commute with slices
(`conjR_eq_self_of_commute` at even exponents), and the four surviving factors pair off into
two squares.

**This is WM0-c's paper arithmetic, mechanized**: the block delivers exactly the charge that
turns `q(c₀) + b_q(c₀,c₁)` into `q(c₁) + b_q(c₀,c₁)`.  The block swap is what the correction
block performs. -/
theorem hessM_eRevW_P0 (hV2 : ∀ v : V, v + v = 0)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) (hα : 2 ≤ α)
    (hδ : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
      (kappa0Cocycle dat hdat)) E E₂ (deltaCert h i)
      = hessSlice dat hdat (vv (xIdx h i)) (q (vv (xIdx h i)))) :
    PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
        (eRevW α h)
      = hessLineZ dat hdat 1 (q (vv (xIdx h 1)) + q (vv (xIdx h 0))) := by
  have hev : ∀ (k : ℤ), Even k → ∀ i : Fin 3,
      PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat)) E E₂
          (.conj (deltaCert h i) (.zpow sigma2W k))
        = hessSlice dat hdat (vv (xIdx h i)) (q (vv (xIdx h i))) := by
    intro k hk i
    rw [PWord.evalZ_conj, hδ i, hessM_sigma2Pow,
      conjR_eq_self_of_commute (hessM_line_comm dat hdat s E hS₂ hk _ _)]
  rw [show eRevW α h
      = PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (2 * (mOf α : ℤ))))
          (PWord.mul (.conj (deltaCert h 1) (.zpow sigma2W (mOf α : ℤ)))
            (PWord.mul (.conj (deltaCert h 0) (.zpow sigma2W (mOf α : ℤ)))
              (PWord.mul (deltaCert h 0) PWord.one))) from rfl,
    PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_one,
    mul_one, hev _ even_two_mul_mOf 1, hev _ (even_mOf_int hα) 1,
    hev _ (even_mOf_int hα) 0, hδ 0,
    hessSlice_sq dat hdat hV2 (vv (xIdx h 0)), ← mul_assoc,
    hessSlice_sq dat hdat hV2 (vv (xIdx h 1)),
    ← hessLineZ_incl, ← hessLineZ_incl, hessLineZ_mul dat hdat, one_mul]

/-- The handle **tail** (empty at `h = 0`, per WM0-a deviation 1) has the handle block's
value at every `h` — the Hessian twin of WM0-c's `heisEvalZ_handleTailW`. -/
theorem hessEvalZ_handleTailW (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    (((handleTailW h).map (PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
        (kappa0Cocycle dat hdat)) E E₂)).prod)
      = PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat))
          E E₂ (handlesW h) := by
  cases h with
  | zero => rw [handleTailW, handlesW_eq]; rfl
  | succ n => rw [handleTailW]; simp only [List.map_cons, List.map_nil, List.prod_cons,
      List.prod_nil, mul_one]

/-- **Factor 6 — the `h` hyperbolic planes**, reusing the pilot's `hess_handlesW_eval` across
the `rfl`-bridge `handlesW_eq`. -/
theorem hessM_handleTailW (hV2 : ∀ v : V, v + v = 0) :
    (((handleTailW h).map (PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
        (kappa0Cocycle dat hdat)) E E₂)).prod)
      = hessLineZ dat hdat 1
          (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) := by
  rw [hessEvalZ_handleTailW dat hdat s u vv E E₂, handlesW_eq,
    Certificates.hess_handlesW_eval dat hdat hV2, hessLineZ_incl]

end Factors

/-! ## 4. The two assembly equations

The single-equation Hessian row of the compact-`M` word, at both projector branches and at
general handle count. -/

section Assembly

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The word-side Hessian equation at the `P = 1` (unramified) branch**, general `h`
(packet Def. 9.1(5) at freeze row 4):

```
q(c₀) + b_q(c₀, c₁) + Σⱼ b_q(dⱼ, eⱼ).
```

This is **literally the compact-`N` row** (`hessRelZ_nCompact`), which is the mathematical
content of S4.1's finding (i) and the reason `compactM_P1_certificate` *is*
`compactN_certificate`.  The projector enters as WM0-b/WM0-c state it: a hypothesis on the
evaluated `ω₂`-block, per `δ`-letter; `hessRelZ_mCompact_P1_res` discharges it.

The hypotheses are exactly WM0-c's: `hV2` (2-torsion), `hα : 2 ≤ α` (so `m = 2^{α−1}` is
even, which is what makes every `σ₂`-power commute with the slice and carry no `m`-charge),
`hS₂` (the σ₂-triviality discipline), `hv2` (the boundary letter carries no primal offset). -/
theorem hessRelZ_mCompact_P1 {h α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (xIdx h 2) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP1 : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
      (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau]))
      = hessSlice dat hdat (vv (xIdx h i)) 0) :
    hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂ (mCompactW α h)
      = q (vv (xIdx h 0)) + polar q (vv (xIdx h 0)) (vv (xIdx h 1))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [hessRelZ, hessEvalZ, mCompactW, PWord.evalZ_prodList, List.map_append, List.prod_append,
    hessM_handleTailW dat hdat s u vv E E₂ hV2]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hessM_leadingSquare dat hdat s u vv E E₂ hV2 hS₂ hα,
    hessM_leadingComm dat hdat s u vv E E₂ hV2 hS₂ hα,
    hessM_sigma2Pow_line dat hdat s u vv E E₂,
    hessM_j2W dat hdat s u vv E E₂ hv2,
    hessM_eRevW_P1 dat hdat s u vv E E₂
      (fun i => hessDeltaCert_P1 dat hdat s u vv E E₂ i (hP1 i)),
    hessLineZ_mul dat hdat, hessLineZ_mul dat hdat, hessLineZ_mul dat hdat,
    hessLineZ_mul dat hdat, hessLineZ_mul dat hdat, hessLineZ_fib]
  abel

/-- **The word-side Hessian equation at the `P = 0` (ramified) branch**, general `h`:

```
q(c₁) + b_q(c₀, c₁) + Σⱼ b_q(dⱼ, eⱼ).
```

The `(c₀,c₁)` **block swap** of freeze row 4, derived rather than posited: the core still
produces `q(c₀) + b_q(c₀,c₁)`, and the correction block adds `q(c₀) + q(c₁)`
(`hessM_eRevW_P0`), which in characteristic 2 swaps the diagonal slot.  The hypothesis `hP0`
— the `ω₂`-block of each `δ`-letter is trivial — is the ramified reading (WM0-b's
`hTodd`/`hτfpf` class); nothing in this lane discharges it, and it is not asserted here. -/
theorem hessRelZ_mCompact_P0 {h α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (xIdx h 2) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark s u vv)
      (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter h i), .gen .tau])) = 1) :
    hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂ (mCompactW α h)
      = q (vv (xIdx h 1)) + polar q (vv (xIdx h 0)) (vv (xIdx h 1))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [hessRelZ, hessEvalZ, mCompactW, PWord.evalZ_prodList, List.map_append, List.prod_append,
    hessM_handleTailW dat hdat s u vv E E₂ hV2]
  simp only [mFactors, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  rw [hessM_leadingSquare dat hdat s u vv E E₂ hV2 hS₂ hα,
    hessM_leadingComm dat hdat s u vv E E₂ hV2 hS₂ hα,
    hessM_sigma2Pow_line dat hdat s u vv E E₂,
    hessM_j2W dat hdat s u vv E E₂ hv2,
    hessM_eRevW_P0 dat hdat s u vv E E₂ hV2 hS₂ hα
      (fun i => hessDeltaCert_P0 dat hdat hV2 s u vv E E₂ i (hP0 i)),
    hessLineZ_mul dat hdat, hessLineZ_mul dat hdat, hessLineZ_mul dat hdat,
    hessLineZ_mul dat hdat, hessLineZ_mul dat hdat, hessLineZ_fib]
  have h2 : q (vv (xIdx h 0)) + q (vv (xIdx h 0)) = 0 := CharTwo.add_self_eq_zero _
  linear_combination h2

/-- **The `P = 1` branch with its projector hypothesis discharged**: at `u = 1` and the
honest resolver class `e ≡ 1 (mod 4)`, WM0-c's `hessDeltaBlock_P1` supplies `hP1`, so the row
holds outright.  This is the compact-`M` twin of the pilot's unconditional row, up to the
resolver pin the correction block genuinely costs. -/
theorem hessRelZ_mCompact_P1_res {h α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s : C)
    (vv : Fin (2 + 2 * h + 1) → V) (hv2 : vv (xIdx h 2) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat) E E₂ (mCompactW α h)
      = q (vv (xIdx h 0)) + polar q (vv (xIdx h 0)) (vv (xIdx h 1))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) :=
  hessRelZ_mCompact_P1 dat hdat hV2 hα s 1 vv hv2 E E₂ hS₂
    (hessDeltaBlock_P1 dat hdat hV2 s vv E E₂ hE he)

/-! ### The endpoint connection: WW4's two certificates consumed at the word -/

/-- **The `h = 0` `P = 1` row lands on `compactM_P1_certificate`'s endpoint polynomial**
`plusFormD q q` — the identity-CoV connection, on the nose.  The certificate is literally
`compactN_certificate`, and so is this equation. -/
theorem hessRelZ_mCompact_P1_plusForm {α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s : C)
    (c₀ c₁ : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s (1 : C) ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW α 0)
      = plusFormD q q (c₀, c₁) := by
  rw [hessRelZ_mCompact_P1_res (h := 0) dat hdat hV2 hα s ![c₀, c₁, 0] rfl E E₂ hS₂ hE he,
    Fin.sum_univ_zero, add_zero, plusFormD_apply]
  rfl

/-- **The `h = 0` `P = 0` row lands on `compactM_P0_certificate`'s endpoint polynomial**
`fun p ↦ q p.2 + b_q(p.1, p.2)` — the `(c₀,c₁)` block-swap CoV's `Q`-parameter, on the nose. -/
theorem hessRelZ_mCompact_P0_swapForm {α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α)
    (s u : C) (c₀ c₁ : V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark (h := 0) s u
        ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    hessRelZ (Certificates.hessMark s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW α 0)
      = q c₁ + polar q c₀ c₁ := by
  rw [hessRelZ_mCompact_P0 (h := 0) dat hdat hV2 hα s u ![c₀, c₁, 0] rfl E E₂ hS₂ hP0,
    Fin.sum_univ_zero, add_zero]
  rfl

/-- The `P = 1` word's evaluated Hessian, as a function of the offsets, **is** the endpoint
polynomial of `compactM_P1_certificate`. -/
theorem mCompact_P1_word_eq_certQ {α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s : C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (fun p : V × V => hessRelZ (Certificates.hessMark s (1 : C) ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW α 0))
      = plusFormD q q :=
  funext fun p => hessRelZ_mCompact_P1_plusForm dat hdat hV2 hα s p.1 p.2 E E₂ hS₂ hE he

/-- The `P = 0` word's evaluated Hessian, as a function of the offsets, **is** the endpoint
polynomial of `compactM_P0_certificate` — the block-swapped plus form. -/
theorem mCompact_P0_word_eq_certQ {α : ℕ} (hV2 : ∀ v : V, v + v = 0) (hα : 2 ≤ α) (s u : C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ (c₀ c₁ : V) (i : Fin 3), PWord.evalZ (WordCoh.lift
        (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    (fun p : V × V => hessRelZ (Certificates.hessMark s u ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW α 0))
      = fun p : V × V => q p.2 + polar q p.1 p.2 :=
  funext fun p =>
    hessRelZ_mCompact_P0_swapForm dat hdat hV2 hα s u p.1 p.2 E E₂ hS₂ (hP0 p.1 p.2)

/-- **The Gauss sum of the `P = 1` word's evaluated Hessian is the certificate's `G0`** —
WW4's `compactM_P1_certificate` consumed at the word, through
`HessianCertificate.endpoint_gaussSum`. -/
theorem mCompact_P1_word_gaussSum {α : ℕ} [Module (ZMod 2) V] [Fintype V]
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ} (hcard : Fintype.card V = 2 ^ d)
    (hα : 2 ≤ α) (s : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    gaussSum (fun p : V × V => hessRelZ (Certificates.hessMark s (1 : C) ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW α 0))
      = (compactM_P1_certificate dat hdat hq hns hcard).affinePhase.G0 := by
  rw [mCompact_P1_word_eq_certQ dat hdat Certificates.module_zmod2_two_torsion hα s E E₂ hS₂
    hE he]
  exact (compactM_P1_certificate dat hdat hq hns hcard).endpoint_gaussSum

/-- **The Gauss sum of the `P = 0` word's evaluated Hessian is the same `G0`** — the block
swap is an isometry, which is freeze row 4's "the two rows are one plus form in two coordinate
systems", now read off the *word* rather than off the endpoint. -/
theorem mCompact_P0_word_gaussSum {α : ℕ} [Module (ZMod 2) V] [Fintype V]
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q) {d : ℕ} (hcard : Fintype.card V = 2 ^ d)
    (hα : 2 ≤ α) (s u : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ (c₀ c₁ : V) (i : Fin 3), PWord.evalZ (WordCoh.lift
        (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    gaussSum (fun p : V × V => hessRelZ (Certificates.hessMark s u ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW α 0))
      = (compactM_P0_certificate dat hdat hq hns hcard).affinePhase.G0 := by
  rw [mCompact_P0_word_eq_certQ dat hdat Certificates.module_zmod2_two_torsion hα s u E E₂ hS₂
    hP0]
  exact (compactM_P0_certificate dat hdat hq hns hcard).endpoint_gaussSum

end Assembly

/-! ## 5. The honest profinite evaluations

Genuine `Marking.eval` (no resolver), through F2's `eval_eq_evalNat_exponent` bridge and
`isOmega2Only_mCompact`.

⚠ Unlike the pilot's `sqrtNegTwo_hess_eval`, these carry the branch hypothesis.  The compact-`N`
word has one `ω₂`-block and it dies on the `C`-line at every exponent; the compact-`M` word has
a second one — the correction block — and *that* one is resolver-sensitive.  This is the
Hessian-level twin of WM0-c's Stokes deviation ("the assembled row is stated at `e ≡ 1 (mod 4)`,
not exact in `e`"), and it is why the hypothesis is stated at the canonical resolved exponent
rather than hidden. -/

section ProfiniteEval

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- Finiteness of the κ⁰-extension's base, for the honest evaluation (local — the WW3
non-exporting idiom). -/
local instance [Finite V] [Finite C] : Finite (SemiProd C V) :=
  inferInstanceAs (Finite (V × C))

/-- **The compact-`M` graph-type marking**, as an honest F2 `Marking` into the κ⁰-extension. -/
noncomputable def mCompactHessMarking (s u : C) (c₀ c₁ : V) :
    Marking 2 (WordCoh.CentExt (kappa0Cocycle dat hdat)) :=
  ⟨WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)⟩

/-- **The honest `ω₂`-evaluation of the compact-`M` word at the `P = 1` branch** hits
`compactM_P1_certificate`'s endpoint. -/
theorem mCompact_hess_eval_P1 [Finite V] [Finite C] {α : ℕ} (hV2 : ∀ v : V, v + v = 0)
    (hα : 2 ≤ α) (s : C) (c₀ c₁ : V)
    (hS₂ : ∀ w : V, (s ^ (omega2Exp (Monoid.exponent
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ)) • w = w)
    (hP1 : ∀ i : Fin 3, PWord.evalNat (WordCoh.lift
        (Certificates.hessMark (h := 0) s (1 : C) ![c₀, c₁, 0]) (kappa0Cocycle dat hdat))
        (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))))
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau]))
      = hessSlice dat hdat (![c₀, c₁, 0] (xIdx 0 i)) 0) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((mCompactHessMarking dat hdat s 1 c₀ c₁).eval (mCompactW α 0))
      = plusFormD q q (c₀, c₁) := by
  rw [Marking.eval_def,
    show ⇑(mCompactHessMarking dat hdat s 1 c₀ c₁)
      = WordCoh.lift (Certificates.hessMark (h := 0) s 1 ![c₀, c₁, 0])
        (kappa0Cocycle dat hdat) from rfl,
    PWord.eval_eq_evalNat_exponent _ (isOmega2Only_mCompact α 0)]
  show hessRelZ (Certificates.hessMark (h := 0) s (1 : C) ![c₀, c₁, 0])
      (kappa0Cocycle dat hdat)
      (fun _ => (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ))
      (fun _ => (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ))
      (mCompactW α 0) = plusFormD q q (c₀, c₁)
  rw [hessRelZ_mCompact_P1 (h := 0) dat hdat hV2 hα s 1 ![c₀, c₁, 0] rfl _ _ hS₂ hP1,
    Fin.sum_univ_zero, add_zero, plusFormD_apply]
  rfl

/-- **The honest `ω₂`-evaluation at the `P = 0` branch** hits `compactM_P0_certificate`'s
endpoint — the block-swapped plus form. -/
theorem mCompact_hess_eval_P0 [Finite V] [Finite C] {α : ℕ} (hV2 : ∀ v : V, v + v = 0)
    (hα : 2 ≤ α) (s u : C) (c₀ c₁ : V)
    (hS₂ : ∀ w : V, (s ^ (omega2Exp (Monoid.exponent
      (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ)) • w = w)
    (hP0 : ∀ i : Fin 3, PWord.evalNat (WordCoh.lift
        (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat))
        (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))))
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((mCompactHessMarking dat hdat s u c₀ c₁).eval (mCompactW α 0))
      = q c₁ + polar q c₀ c₁ := by
  rw [Marking.eval_def,
    show ⇑(mCompactHessMarking dat hdat s u c₀ c₁)
      = WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
        (kappa0Cocycle dat hdat) from rfl,
    PWord.eval_eq_evalNat_exponent _ (isOmega2Only_mCompact α 0)]
  show hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)
      (fun _ => (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ))
      (fun _ => (omega2Exp (Monoid.exponent (WordCoh.CentExt (kappa0Cocycle dat hdat))) : ℤ))
      (mCompactW α 0) = q c₁ + polar q c₀ c₁
  rw [hessRelZ_mCompact_P0 (h := 0) dat hdat hV2 hα s u ![c₀, c₁, 0] rfl _ _ hS₂ hP0,
    Fin.sum_univ_zero, add_zero]
  rfl

end ProfiniteEval

/-! ## 6. The two displayed instances

`ℚ₂(√2)` is freeze row 4 at `α = 3` (`m = 4`, `q_K = 2`) and `ℚ₂(√5)` at `α = 2` (`m = 2`,
`q_K = 4`).  `q_K` never reaches the branch word (WM0-a's `astHash_q2_eq_q4`), so the two
instances differ only in `α` — and `α` has already been consumed, once, as the evenness of
`m`.  Both rows are therefore the same two endpoints, at both projector branches. -/

section Instances

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **`ℚ₂(√2)`, `P = 1`** (`α = 3`, `m = 4`): the endpoint `q(c₀) + b_q(c₀,c₁)`. -/
theorem sqrtTwo_hessRelZ_P1 (hV2 : ∀ v : V, v + v = 0) (s : C) (c₀ c₁ : V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s (1 : C) ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW 3 0)
      = plusFormD q q (c₀, c₁) :=
  hessRelZ_mCompact_P1_plusForm dat hdat hV2 (by norm_num) s c₀ c₁ E E₂ hS₂ hE he

/-- **`ℚ₂(√5)`, `P = 1`** (`α = 2`, `m = 2`): the same endpoint — the `q_K`-sensitivity of this
row lives in the tame relator, not in the branch word. -/
theorem sqrtFive_hessRelZ_P1 (hV2 : ∀ v : V, v + v = 0) (s : C) (c₀ c₁ : V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark s (1 : C) ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW 2 0)
      = plusFormD q q (c₀, c₁) :=
  hessRelZ_mCompact_P1_plusForm dat hdat hV2 (by norm_num) s c₀ c₁ E E₂ hS₂ hE he

/-- **`ℚ₂(√2)`, `P = 0`** (`α = 3`): the block-swapped endpoint `q(c₁) + b_q(c₀,c₁)`. -/
theorem sqrtTwo_hessRelZ_P0 (hV2 : ∀ v : V, v + v = 0) (s u : C) (c₀ c₁ : V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark (h := 0) s u
        ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    hessRelZ (Certificates.hessMark s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW 3 0)
      = q c₁ + polar q c₀ c₁ :=
  hessRelZ_mCompact_P0_swapForm dat hdat hV2 (by norm_num) s u c₀ c₁ E E₂ hS₂ hP0

/-- **`ℚ₂(√5)`, `P = 0`** (`α = 2`): the same block-swapped endpoint. -/
theorem sqrtFive_hessRelZ_P0 (hV2 : ∀ v : V, v + v = 0) (s u : C) (c₀ c₁ : V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w)
    (hP0 : ∀ i : Fin 3, PWord.evalZ (WordCoh.lift (Certificates.hessMark (h := 0) s u
        ![c₀, c₁, 0]) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.gen (Words.coreLetter 0 i), .gen .tau])) = 1) :
    hessRelZ (Certificates.hessMark s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mCompactW 2 0)
      = q c₁ + polar q c₀ c₁ :=
  hessRelZ_mCompact_P0_swapForm dat hdat hV2 (by norm_num) s u c₀ c₁ E E₂ hS₂ hP0

/-- **The `ℚ₂(√2)` Gauss residue at the word** (`α = 3`): `G0 = 2^d`, via
`compactM_P1_certificate`. -/
theorem sqrtTwo_hess_gaussSum [Module (ZMod 2) V] [Fintype V] (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) {d : ℕ} (hcard : Fintype.card V = 2 ^ d) (s : C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    gaussSum (fun p : V × V => hessRelZ (Certificates.hessMark s (1 : C) ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW 3 0))
      = 2 ^ d := by
  rw [mCompact_P1_word_gaussSum dat hdat hq hns hcard (by norm_num) s E E₂ hS₂ hE he]
  exact mCompact_P1_G0 dat hdat hq hns hcard

/-- **The `ℚ₂(√5)` Gauss residue at the word** (`α = 2`): the same `2^d`. -/
theorem sqrtFive_hess_gaussSum [Module (ZMod 2) V] [Fintype V] (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) {d : ℕ} (hcard : Fintype.card V = 2 ^ d) (s : C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (hS₂ : ∀ w : V, (s ^ E omega2) • w = w) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    gaussSum (fun p : V × V => hessRelZ (Certificates.hessMark s (1 : C) ![p.1, p.2, 0])
        (kappa0Cocycle dat hdat) E E₂ (mCompactW 2 0))
      = 2 ^ d := by
  rw [mCompact_P1_word_gaussSum dat hdat hq hns hcard (by norm_num) s E E₂ hS₂ hE he]
  exact mCompact_P1_G0 dat hdat hq hns hcard

end Instances

end GQ2.Dyadic.Certificates.MCompact
