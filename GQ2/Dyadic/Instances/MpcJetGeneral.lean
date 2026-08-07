/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Certificates.MpcJet
import GQ2.Dyadic.Certificates.N0

/-!
# The procyclic-`M` jet layer at every handle count

The `mpcW` twin of `GQ2/Dyadic/Instances/NpcJetGeneral.lean`.  Wave 37 generalized the
noncompact-`N` `hessRelZ` layer from `h = 0` to the frozen genus-`h` word and recorded that
"the `mpcW` analogue remains open".  This file closes it.

## What was actually missing

Less than the `npc` side needed, and the reason is worth stating precisely.  WMP-J's
`mpc_cross_operators` (`GQ2/Dyadic/Certificates/MpcJet.lean`) is **already** general in `h`:
the two copies' cancellation (§6, the `Sh_M` self-replication on the κ⁰ carrier) and WMP-d's
row collapse (`foxD_mpcLinW_x2`) are both stated at `Marking (2 + 2h)`, and the plus block's
value is index-generic.  What `h = 0` bought was only that `handlesW 0 = 1`, so that
`evalFin_mpcW_factored`'s fourth factor could be dropped without evaluating it.

So no substitution/transport layer is needed here — no `mpcCoreLift`, no `eval_mpcW_eq_core_mul_handles`.
The `npc` side needed one because its `h`-general statement was assembled from the *`h = 0`
core theorem* (`npc_cross_operators_word`) by transport; the `M` row's core theorem was already
`h`-general, so the whole content of this file is **the fourth factor**:

* `evalFin_handlesW` — the handle block at the graph-type κ⁰-marking, in the `evalFin`
  register.  The `evalZ` twin is WN0-c's `hess_handlesW_eval`; the `M` row lives on `evalFin`
  (`ResolverLifts` is spent once, at the very end, not per factor), so the lemma is re-proved
  rather than transported.  Both proofs are the same six rewrites over `hessSlice_commR`.
* `evalFin_fib_mpcW_handles` — the jet theorem at every `h`;
* `hessRelZ_mpcW_handles` / `mpcW_hessRelZTarget_handles` — WW4 gap item 5 at every `h`;
* `mpc_hess_eval_handles` — the honest profinite reading, still resolver-immune at every `h`.

## The headline

```
hessRelZ (hessMark s u v) κ⁰ E E₂ (mpcW α r p η h)
  = q (v x₀) + b_q(v x₀, v x₁) + Σ_j b_q(v x_{3+2j}, v x_{4+2j})
  = plusFormD q q (v x₀, v x₁) + Σ_j b_q(v x_{3+2j}, v x_{4+2j}),
```

on WMP-J's hypothesis surface verbatim — `hV2`, `hu : Odd (orderOf u)`, `hVu`, the Gate-E
normalization `v x₂ = 0`, `1 ≤ α` (**not** the compact rows' `2 ≤ α`), the `ActsAsPow`
`η`-datum, and `ResolverLifts`.  Note what is *absent*: no `ResolvedAt`.  WW6's
resolver-immunity finding for this row survives the handle tail intact, because the handle
block is `ω₂`-only (`isOmega2Only_handlesW`) — which is also why `mpc_hess_eval_handles` can
still read the value profinitely at *every* resolver pair.  Contrast the `npc` twin
`hessRelZ_npcW_handles`, which must carry a genuine `ResolvedAt` because `npcW` has an
`η̂`-exponent node.

## Deviations from the `npc` statements, and why

1. **Endpoint shape.**  `hessRelZ_npcW_handles` lands on `npcQ0 + b_q(c₁, L_c c₀) + Σ`; the `M`
   row lands on `plusFormD q q + Σ`.  That is the `Q₊` endpoint WMP-c predicted, with the
   diagonal `d₀` **pinned to `q`** — pinned by WMP-J, not re-derived here.
2. **`x₂` is consumed differently.**  On the `npc` row `v x₂ = 0` normalizes the transported
   Gate-E marking (`lift_hessMark_npcCoreLift`); on the `M` row it is load-bearing twice over —
   it kills `δ₂`, hence the whole `E₂^pc` block, and it is where WMP-d's row collapse is read.
   Same hypothesis, two different jobs.
3. **No handle-tail hypothesis appears.**  `handleTailW` (the `M` emitter's no-node-at-`h = 0`
   display) never enters a *hypothesis*; `evalFin_mpcW_factored` already discharged it.

## The `hτfpf` seam — hit, and paid for by the caller, not by this file

MpcStokes §6 / MpcFox §5 `include hτfpf hTodd` on every factor row, and `hτfpf` is **false** on
the unramified branch.  This layer does hit that seam, through
`base_fst_mpcLinW → foxD_mpcLinW_x2`.  It costs nothing *here*: at the graph-type κ⁰-marking
the lower marking is `lowerMark s u` (`σ ↦ s`, `τ ↦ u`, wild letters trivial), so `hτfpf`
instantiates to `hVu : ∀ v, u • v = v → v = 0` — which is NC5's rule 2 and already a standing
hypothesis of the whole jet layer — and `hTodd` instantiates to
`powOmega2 u = 1`, which is `hu : Odd (orderOf u)`.  WMP-J already navigated this at general
`h`; nothing is re-derived.  The recorded hoist recommendation (parameterize the factor rows by
the two δ-row facts instead of `hτfpf`/`hTodd`) still stands for the *unramified* consumers and
is **not** performed here — it is a ~660-line change to two files this ticket may not edit.

## Module rule and axiom state

Plain-import leaf, forced (`Certificates/MpcJet.lean` is plain).  Every declaration below
`#print axioms` at the standard three (`propext`, `Classical.choice`, `Quot.sound`) or a
strict subset.  No `sorry`, no `decide`, no `native_decide`, no `set_option`.
-/

namespace GQ2.Dyadic.Certificates.MpcJet

open GQ2.FoxH GQ2.SectionSix GQ2.QuadraticFp2
open GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates.MProcyclic

noncomputable section

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V]

/-! ## §1. The handle block on the κ⁰ carrier, in the `evalFin` register -/

omit [Finite C] [Finite V] in
/-- **The handle tail is central with the hyperbolic fibre.**

`H_h = ∏_j [x_{3+2j}, x_{4+2j}]` at the graph-type κ⁰-marking is the central inclusion of
`Σ_j b_q(d_j, e_j)`: each handle letter is a zero-charge Heisenberg slice element, and the
slice commutator law (`hessSlice_commR`) is charge-free.

This is WN0-c's `hess_handlesW_eval` in the **`evalFin`** register rather than `evalZ`.  The
procyclic-`M` lane spends `ResolverLifts` exactly once, at `hessRelZ_mpcW_handles`, so every
factor lemma has to live on `evalFin`; the two proofs are otherwise identical, and neither
needs a resolver hypothesis (the block has no profinite exponent). -/
theorem evalFin_handlesW (hV2 : ∀ v : V, v + v = 0) {h : ℕ} (s u : C)
    (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (handlesW h)
      = WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) := by
  rw [handlesW, evalFin_prodList, List.map_map]
  have hcong : (List.finRange h).map
        (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
          ∘ fun j => PWord.comm (.gen (handleU j)) (.gen (handleV j)))
      = (List.finRange h).map fun j =>
          WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))) := by
    refine List.map_congr_left fun j _ => ?_
    show PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂
        (.comm (.gen (handleU j)) (.gen (handleV j))) = _
    rw [PWord.evalFin_comm, PWord.evalFin_gen, PWord.evalFin_gen,
      show hessLift dat hdat (h := h) s u vv (handleU j)
        = hessSlice dat hdat (vv (Certificates.hIdxU j)) 0 from rfl,
      show hessLift dat hdat (h := h) s u vv (handleV j)
        = hessSlice dat hdat (vv (Certificates.hIdxV j)) 0 from rfl,
      hessSlice_commR dat hdat hV2]
  rw [hcong,
    show ((List.finRange h).map fun j => WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))))
      = ((List.finRange h).map fun j =>
          polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j))).map
            (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)) from List.map_map.symm,
    centExt_incl_list_prod, ← Fin.sum_univ_def]

/-! ## §2. The jet theorem at every handle count -/

variable {h : ℕ} (s u : C) (vv : Fin (2 + 2 * h + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The `mpcW` jet theorem at every handle count** — the `evalFin` headline.

The evaluated Hessian of the frozen procyclic-`M` word at the graph-type κ⁰-marking with
`x₂`-slot zero is the plus form plus the hyperbolic handle sum.  The first three factors are
WMP-J's `mpc_cross_operators`, already general in `h`; the fourth is §1. -/
theorem evalFin_fib_mpcW_handles (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (Certificates.x2Idx h) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.evalFin (hessLift dat hdat (h := h) s u vv) E E₂ (mpcW α r pp η h))
      = q (vv (Certificates.x0Idx h))
        + polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [evalFin_mpcW_factored, evalFin_handlesW dat hdat hV2 s u vv E E₂,
    WordCoh.CentExt.mul_fib,
    mpc_cross_operators dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη,
    WordCoh.CentExt.incl_fib, WordCoh.CentExt.incl_base,
    (kappa0Cocycle dat hdat).κ_one_right, add_zero]
  rfl

/-! ## §3. `hessRelZ` and WW4 gap item 5, at every handle count -/

/-- **The word-side Hessian equation for the procyclic-`M` row at every handle count.**

The `hessRelZ` (resolver-driven) form of §2.  The hypothesis surface is WMP-J's verbatim, with
`ResolverLifts` the only thing separating the two registers: **no `ResolvedAt`**, at any `h`. -/
theorem hessRelZ_mpcW_handles (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (Certificates.x2Idx h) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂ (mpcW α r pp η h)
      = q (vv (Certificates.x0Idx h))
        + polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [hessRelZ, hessEvalZ, evalZ_eq_evalFin_of_resolverLifts hres]
  exact evalFin_fib_mpcW_handles dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη

/-- The same equation with the `h = 0` endpoint written as the certificate's endpoint
polynomial: `plusFormD q q` shifted by the (offset-constant) hyperbolic handle sum.  This is
the shape `mpcHessianCertificate`'s `Q`-parameter has, so the handle tail reads as a pure
translation of the endpoint. -/
theorem hessRelZ_mpcW_handles_plusForm (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (Certificates.x2Idx h) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂ (mpcW α r pp η h)
      = plusFormD q q (vv (Certificates.x0Idx h), vv (Certificates.x1Idx h))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [hessRelZ_mpcW_handles dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη hres,
    plusFormD_apply]

/-- **WW4 gap item 5, discharged on the procyclic-`M` row at every handle count.**

`HessRelZTarget` holds on the frozen genus-`h` procyclic-`M` word, with the endpoint polynomial
`plusFormD q q` shifted by the hyperbolic handle sum — the `M`-row twin of
`npcW_hessRelZTarget_handles`.  The diagonal `d₀` is `q`, exactly as WMP-J pinned it at
`h = 0`: the handle tail is charge-free, so it cannot move the diagonal. -/
theorem mpcW_hessRelZTarget_handles (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (Certificates.x2Idx h) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    Certificates.MProcyclic.HessRelZTarget dat hdat
      (Certificates.hessMark s u vv) E E₂ (mpcW α r pp η h)
      (fun p => plusFormD q q p
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)))
      (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) :=
  hessRelZ_mpcW_handles_plusForm dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη hres

/-! ## §4. The honest profinite reading, still at every handle count -/

/-- **The `M` row is resolver-immune at every handle count.**

WW6's `mpc_eval_eq_hessRelZ` is pinned at `h = 0`; the handle block is `ω₂`-only
(`isOmega2Only_handlesW`) and `isOmega2Only_mpcW` is already general in `h`, so the profinite
value and the `hessRelZ` value coincide for **every** resolver pair at every `h`.  Stated here
rather than in `Word/NpcBridge.lean` because that file is another lane's committed work. -/
theorem mpc_eval_eq_hessRelZ_handles {η : EtaDisplay} (hη2 : η.IsOmega2Only) (α r pp : ℕ)
    (hE : ∀ x : WordCoh.CentExt (kappa0Cocycle dat hdat), x ^ᶻ omega2 = x ^ E omega2) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((Marking.mk (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat))).eval
          (mpcW α r pp η h))
      = hessRelZ (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat) E E₂
          (mpcW α r pp η h) := by
  rw [Marking.eval_def, hessRelZ, hessEvalZ]
  exact congrArg _ (PWord.eval_eq_evalZ _ E E₂ _
    (PWord.resolvedAt_of_isOmega2Only _ E E₂ hE _ (isOmega2Only_mpcW α r pp hη2 h)))

/-- **The honest profinite jet value at every handle count**: the genuine `Marking.eval` of the
frozen genus-`h` procyclic-`M` word has fibre `plusFormD q q (c₀, c₁) + Σ_j b_q(d_j, e_j)`. -/
theorem mpc_hess_eval_handles (hV2 : ∀ v : V, v + v = 0) (hu : Odd (orderOf u))
    (hVu : ∀ v : V, u • v = v → v = 0) (hv2 : vv (Certificates.x2Idx h) = 0)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ} (hη2 : η.IsOmega2Only)
    (hη : ActsAsPow (lowerMark (h := h) s u).σ nη
      (PWord.evalFin ⇑(lowerMark (h := h) s u) E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        ((Marking.mk (WordCoh.lift (Certificates.hessMark s u vv) (kappa0Cocycle dat hdat))).eval
          (mpcW α r pp η h))
      = plusFormD q q (vv (Certificates.x0Idx h), vv (Certificates.x1Idx h))
        + ∑ j, polar q (vv (Certificates.hIdxU j)) (vv (Certificates.hIdxV j)) := by
  rw [mpc_eval_eq_hessRelZ_handles dat hdat s u vv E E₂ hη2 α r pp
      (fun x => by rw [zpowHat_omega2, hres x]),
    hessRelZ_mpcW_handles_plusForm dat hdat s u vv E E₂ hV2 hu hVu hv2 hα r pp hη hres]

/-! ## §5. The `h = 0` regressions

The general statements restrict to WMP-J's own, on the nose: `handlesW 0 = 1` makes the handle
sum empty and `![c₀, c₁, 0]` is the Gate-E offset vector. -/

/-- **The `h = 0` regression of the jet theorem**: `evalFin_fib_mpcW`, recovered. -/
theorem evalFin_fib_mpcW_handles_zero (hV2 : ∀ v : V, v + v = 0) (s' u' : C)
    (hu : Odd (orderOf u')) (hVu : ∀ v : V, u' • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := 0) s' u').σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s' u') E E₂ (η.toPWord (n := 2 + 2 * 0))) V) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.evalFin (hessLift dat hdat (h := 0) s' u' ![c₀, c₁, 0]) E E₂ (mpcW α r pp η 0))
      = plusFormD q q (c₀, c₁) := by
  rw [evalFin_fib_mpcW_handles dat hdat (h := 0) s' u' ![c₀, c₁, 0] E E₂ hV2 hu hVu rfl hα r pp
      hη,
    Fin.sum_univ_zero, add_zero, plusFormD_apply]
  rfl

/-- **The `h = 0` regression of the word-side equation**: `hessRelZ_mpcW`, recovered. -/
theorem hessRelZ_mpcW_handles_zero (hV2 : ∀ v : V, v + v = 0) (s' u' : C)
    (hu : Odd (orderOf u')) (hVu : ∀ v : V, u' • v = v → v = 0) (c₀ c₁ : V)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hη : ActsAsPow (lowerMark (h := 0) s' u').σ nη
      (PWord.evalFin ⇑(lowerMark (h := 0) s' u') E E₂ (η.toPWord (n := 2 + 2 * 0))) V)
    (hres : ResolverLifts E (WordCoh.CentExt (kappa0Cocycle dat hdat))) :
    hessRelZ (Certificates.hessMark (h := 0) s' u' ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (mpcW α r pp η 0)
      = plusFormD q q (c₀, c₁) := by
  rw [hessRelZ_mpcW_handles_plusForm dat hdat (h := 0) s' u' ![c₀, c₁, 0] E E₂ hV2 hu hVu rfl
      hα r pp hη hres,
    Fin.sum_univ_zero, add_zero]
  rfl

end

end GQ2.Dyadic.Certificates.MpcJet
