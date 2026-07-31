/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.ClearWide
public import GQ2.Dyadic.MarkedCore.M

@[expose] public section

/-!
# MC1 §5.3's displayed pure `M5`, over `A⁺(P,h)`

**Ticket HM6g** of the dyadic campaign (lane MC): the composition HM6ef could not make, because
the two files it needed were on different branches.  `ClearWide.lean` (HM6ef) landed the `⟨M5⟩`
factor at the **`τ_c`-corrected** move `hm6FrameBDc k`

```
B̄ ↦ B̄ + k(Ā + C̄₀),      D̄ ↦ D̄ + k·Ā ,
```

and recorded in its §6 that reaching MC1's *displayed* pure `M5` — `B̄ ↦ B̄ + k·C̄₀`, every other
row fixed — needs one more shear, which it named `τ_a(−k) : B ↦ A^{−k}·B` and located in MC3's
`M.lean` (`mLambdaEquiv`, family **M1**).  Both files are now on `dyadic`, so the composite can
be made.

## What the composition actually needs

`τ_a` is **not** the shear that finishes the job, and no shear of that shape could be: the
residue `hm6FrameBDc` leaves sits on **two** rows, `k·Ā` on `B̄` *and* `k·Ā` on `D̄`, and a
`B`-slot substitution reaches only the first.  A `D`-slot substitution `D ↦ A^{−k}·D` would
reach the second, but it does not exist — the `M_α` relator's second half is `c^{2^α}[c, d]`, and
`[c, a^{−k}d] ≠ [c, d]` because `a` and `c` do not commute (this is the same obstruction that
`frameTauD`'s docstring records for `c`).

What finishes the job instead is an **arithmetic** fact about `D_M`, the exact `M`-side analogue
of MC4's `nChar_dnX0`.  On `D_N` the relator abelianizes to `(2 + 2^α)x̄₀ = 0`, so `ν(x₀) = 0` for
every `ℤ₂`-character and the `x̄₀`-residues are invisible.  On `D_M` it abelianizes to
`2Ā + 2^αC̄₀ = 0` — *not* `Ā = 0`, which is precisely why HM6ef's `hm6FrameBDc_of_zero` does not
apply — but it does pin the `Ā`-row:

```
Ā = −2^{α−1}·C̄₀        (`mChar_frameZero`, α ≥ 1).
```

So the leftovers are not invisible; they are **`C̄₀`-multiples**, and `C̄₀`-multiples on the `D̄`-row
are exactly what HM4's exact transvection `τ_c` writes.  One further `τ_c` therefore clears the
`D̄`-row, and the `B̄`-row's `k·Ā` merges into the `C̄₀`-coefficient:

```
hm6FrameBDc k ∘ frameTauD (k·2^{α−1})  =  ( B̄ ↦ B̄ + k(1 − 2^{α−1})·C̄₀ ) .
```

For `α ≥ 2` the coefficient `1 − 2^{α−1}` is **odd**, hence a unit, so reparametrizing sweeps the
whole family.  The composite is one `.trans` onto HM6ef's `dmRealizesWide_frameBDc`, it stays
inside `A⁺(P,h)` (both factors are already generators of it), and it needs no second widening.

## Where `M.lean` does enter

`mLambdaEquiv` is still consumed, and it turns out to say something clean: by the same pinning of
the `Ā`-row, **the ν-frame row of `M1` is itself a pure `M5` row**, at parameter `−k·2^{α−1}`
(`nuFrame_mLambdaEquiv_eq`).  That is exactly the `B_c = −k·2^{α−1}` entry MC3's Nielsen table
records for `mFamM1`, and it says that `τ_a` reaches only the parameter ideal `2^{α−1}ℤ₂` while
`dmPureM5` reaches all of `ℤ₂` — so adding `mLambdaEquiv` to the generating set would buy nothing
at the frame level, which is the reason no second widening is proposed here.
`hm6FrameBDc_mFrameLambda` records what the literal `τ_a` composite of HM6ef's §6 does give: the
displayed pure `M5` at parameter `k`, times one HM4 `τ_c` — the same `τ_c` the route below simply
applies first.

## Contents

* **§1** the `M`-side character relation `2Ā + 2^αC̄₀ = 0` and the pinned `Ā`-row;
* **§2** the frame identities — the `τ_c` finish, and what `τ_a` gives;
* **§3** `dmPureM5`, its `DmRealizesWide` row, and the reparametrization by the unit
  `1 − 2^{α−1}`;
* **§4** the payoff: `MCoreMixHypothesisWide` for the **whole** displayed `M5` stratum, and the
  χ-preserving marked-generator form (`mMixFamily_coreMix`), the `M` mirror of
  `nMixPairHypothesis_coreMix`;
* **§5** stress pins at `(α, h) = (2, 1)`;
* **§6** what stays binder-shaped on `M` after this file.
-/

open Multiplicative

namespace GQ2

namespace Dyadic

namespace MarkedCore

open scoped GQ2

/-! ## §1 The `M`-side character relation

MC4's `nChar_dnX0` reads the `N_α` relator through an arbitrary `ℤ₂`-character and gets
`ν(x₀) = 0` on the nose.  The `M_α` relator gives one equation less: `2Ā + 2^αC̄₀ = 0` determines
`Ā` in terms of `C̄₀` rather than killing it.  That is the whole `M`/`N` difference for this
file, and it is enough. -/

section CharRel

variable (α h : ℕ)

/-- **The abelianized `M_α` relation, read by an arbitrary `ℤ₂`-character**: `2Ā + 2^α·C̄₀ = 0`
on the ν-frame of the marked generators (memo §2.1's relation vector `ρ_M`).  Commutators and
handles die in `Multiplicative ℤ_[2]` (`mRelWord_comm`), so only the two powered letters
survive.  The `M`-side counterpart of MC4's `nChar_dnX0`. -/
theorem mChar_frameRel (f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    2 * nuFrame f (dmGen α h) 0 + 2 ^ α * nuFrame f (dmGen α h) 2 = 0 := by
  have hmap : mRelWord α (fun i => f (dmGen α h i)) = 1 := by
    rw [← map_mRelWord, dm_relation, map_one]
  rw [mRelWord_comm] at hmap
  have hadd := congrArg toAdd hmap
  rw [toAdd_mul, toAdd_pow, toAdd_pow, toAdd_one, nsmul_eq_mul, nsmul_eq_mul] at hadd
  simpa only [nuFrame_apply, Nat.cast_ofNat, Nat.cast_pow] using hadd

/-- **The `Ā`-row of the ν-frame is pinned by the `C̄₀`-row**: `Ā = −2^{α−1}·C̄₀`, for every
`ℤ₂`-character of `D_M` and every `α ≥ 1`.  `ℤ₂` is a domain, so the `2` in `2Ā + 2^αC̄₀ = 0`
cancels.  This is the exact hypothesis `hm6FrameBDc_of_zero` wanted and did not get: on `D_N`
the analogous row is `0` (`nChar_dnX0`), on `D_M` it is a `C̄₀`-multiple — which is *also* enough,
because `C̄₀`-multiples are what `τ_c` writes. -/
theorem mChar_frameZero (hα : 1 ≤ α) (f : ContinuousMonoidHom (DM α h : Type)
    (Multiplicative ℤ_[2])) :
    nuFrame f (dmGen α h) 0 = -(2 ^ (α - 1) * nuFrame f (dmGen α h) 2) := by
  obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
  have hrel := mChar_frameRel (j + 1) h f
  have h2 : (2 : ℤ_[2]) ≠ 0 := by norm_num
  have hfac : 2 * (nuFrame f (dmGen (j + 1) h) 0
      + 2 ^ j * nuFrame f (dmGen (j + 1) h) 2) = 0 := by
    rw [← hrel, pow_succ]
    ring
  rcases mul_eq_zero.mp hfac with hc | hc
  · exact absurd hc h2
  · rw [Nat.add_sub_cancel, eq_neg_iff_add_eq_zero]
    exact hc

end CharRel

/-! ## §2 The last shear, at the frame level

Two identities, both on an arbitrary frame vector `m` subject only to the pinning
`m 0 = −(e · m 2)` — `e = 2^{α−1}` at the ν-frames of `D_M`, and the general `e` keeps the
arithmetic visible.  The first is the route this file takes; the second records what HM6ef's
literal `τ_a` composite gives, and why it is neither necessary nor sufficient on its own. -/

section PureFrame

variable {h : ℕ}

private theorem cmOne_ne_three : (1 : Fin (coreRank h)) ≠ 3 :=
  coreVal_lt_three_ne (by rw [coreVal_one]; omega)

private theorem cmZero_ne_three : (0 : Fin (coreRank h)) ≠ 3 :=
  coreVal_lt_three_ne (by rw [coreVal_zero]; omega)

/-- **The displayed pure `M5` move, at the frame level.**  On a frame whose `Ā`-row is the
`C̄₀`-multiple `−e·C̄₀`, HM6ef's corrected twist `hm6FrameBDc k` followed by one more HM4
transvection `τ_c(k·e)` is the pure mixing move `B̄ ↦ B̄ + k(1 − e)·C̄₀`, every other row fixed —
MC1 §5.3's displayed `M5`, which is `nFrameMixX1` at the twisted parameter.

Both residues are consumed at once: the `τ_c` factor cancels `k·e·C̄₀` on the `D̄`-row against the
`k·Ā` the twist put there, and on the `B̄`-row the twist's own `k·Ā` merges into its `k·C̄₀`. -/
theorem hm6FrameBDc_frameTauD (k e : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2])
    (h0 : m 0 = -(e * m 2)) :
    hm6FrameBDc k (frameTauD (k * e) m) = nFrameMixX1 (k * (1 - e)) m := by
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [hm6FrameBDc, hm6UpdateBD_one, frameTauD_of_ne _ _ cmOne_ne_three,
      frameTauD_of_ne _ _ cmZero_ne_three, frameTauD_two, nFrameMixX1, Function.update_self, h0]
    ring
  by_cases h3 : i = 3
  · subst h3
    rw [hm6FrameBDc, hm6UpdateBD_three, frameTauD_three, frameTauD_of_ne _ _ cmZero_ne_three,
      nFrameMixX1, Function.update_of_ne (Ne.symm cmOne_ne_three), smul_eq_mul, h0]
    ring
  rw [hm6FrameBDc, hm6UpdateBD_of_ne _ _ _ h1 h3, frameTauD_of_ne _ _ h3, nFrameMixX1,
    Function.update_of_ne h1]

/-- **MC3's `τ_a` row is itself a pure `M5` row.**  Once the `Ā`-row is pinned, `Λ_k`'s frame
action `B̄ ↦ B̄ + k·Ā` *is* `B̄ ↦ B̄ − k·e·C̄₀`, i.e. `nFrameMixX1 (−k·e)`.  At `e = 2^{α−1}` this is
the `B_c = −k·2^{α−1}` entry MC3's Nielsen table records for `mFamM1`, and it shows `τ_a` reaches
only the parameter ideal `2^{α−1}ℤ₂`. -/
theorem mFrameLambda_eq_nFrameMixX1 (k e : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2])
    (h0 : m 0 = -(e * m 2)) : mFrameLambda k m = nFrameMixX1 (-(k * e)) m := by
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [mFrameLambda, Function.update_self, nFrameMixX1, Function.update_self, h0]
    ring
  rw [mFrameLambda, Function.update_of_ne h1, nFrameMixX1, Function.update_of_ne h1]

/-- **What HM6ef's literal `τ_a` composite gives.**  `hm6FrameBDc k ∘ τ_a(−k)` is the displayed
pure `M5` at parameter `k` — *times one HM4 `τ_c`*, namely `τ_c(−k·e)`.  So the `τ_a` shear is
neither sufficient (it clears the `B̄`-row residue and cannot touch the `D̄`-row one) nor
necessary (`hm6FrameBDc_frameTauD` clears both with the `τ_c` factor alone, and reaches every
parameter).  Recorded because HM6ef's §6 names this composite as its residual item. -/
theorem hm6FrameBDc_mFrameLambda (k e : ℤ_[2]) (m : Fin (coreRank h) → ℤ_[2])
    (h0 : m 0 = -(e * m 2)) :
    hm6FrameBDc k (mFrameLambda (-k) m) = nFrameMixX1 k (frameTauD (-(k * e)) m) := by
  funext i
  by_cases h1 : i = 1
  · subst h1
    rw [hm6FrameBDc, hm6UpdateBD_one, mFrameLambda, Function.update_self,
      Function.update_of_ne nCoreZero_ne_one, Function.update_of_ne (Ne.symm nCoreOne_ne_two),
      nFrameMixX1, Function.update_self, frameTauD_of_ne _ _ cmOne_ne_three, frameTauD_two, h0]
    ring
  by_cases h3 : i = 3
  · subst h3
    rw [hm6FrameBDc, hm6UpdateBD_three, mFrameLambda,
      Function.update_of_ne (Ne.symm cmOne_ne_three), Function.update_of_ne nCoreZero_ne_one,
      nFrameMixX1, Function.update_of_ne (Ne.symm cmOne_ne_three), frameTauD_three,
      smul_eq_mul, h0]
    ring
  rw [hm6FrameBDc, hm6UpdateBD_of_ne _ _ _ h1 h3, mFrameLambda, Function.update_of_ne h1,
    nFrameMixX1, Function.update_of_ne h1, frameTauD_of_ne _ _ h3]

end PureFrame

/-! ## §3 The composite, inside `A⁺(P,h)`

One `.trans` onto HM6ef's `dmRealizesWide_frameBDc`.  Both factors are already generators of the
widened monoid — `dmCoreMixEquiv` by §1 of `ClearWide.lean`, `dmTauDEquiv` because it was in the
*narrow* `A(P,h)` all along — so no second widening is proposed and none is needed. -/

section PureLift

variable (α h : ℕ)

/-- **MC1 §5.3's displayed family `M5`** at 2-adic parameter `k`: HM6's raw twist, HM4's
transvection `τ_c(−k)` (together, HM6ef's `dmPureMix`), and one further `τ_c(k·2^{α−1})` to clear
the `Ā`-residue the pinning turns into a `C̄₀`-residue. -/
noncomputable def dmPureM5 (α h : ℕ) (k : ℤ_[2]) :
    ContinuousMulEquiv (DM α h : Type) (DM α h : Type) :=
  (dmPureMix α h k).trans (dmTauDEquiv α h (k * 2 ^ (α - 1)))

/-- **The displayed pure `M5` row, realized inside `A⁺(P,h)`** — the `M` mirror of HM6ef's
`dnRealizesWide_frameMixX1`.  The parameter is twisted by `1 − 2^{α−1}`; §3's reparametrization
untwists it. -/
theorem dmRealizesWide_pureM5 (hα : 1 ≤ α) (k : ℤ_[2]) :
    DmRealizesWide α h (dmPureM5 α h k) (frameEnd (nFrameMixX1 (k * (1 - 2 ^ (α - 1))))) := by
  rw [dmPureM5]
  obtain ⟨hmem, hfr⟩ :=
    (dmRealizesWide_frameBDc α h k).trans α h (dmRealizesWide_tauD α h (k * 2 ^ (α - 1)))
  refine ⟨hmem, fun f => ?_⟩
  rw [hfr f, frameEnd_mul_apply, frameEnd_apply]
  exact hm6FrameBDc_frameTauD k _ _ (mChar_frameZero α h hα f)

/-- **`1 − 2^{α−1}` is a unit** for `α ≥ 2`: `2^{α−1}` is even (MC3's `mParityZ_mul_two_pow`, the
same evenness that keeps `Λ_k` off the Witt coupling), so the difference is odd.  This is what
makes the twisted parameter of `dmRealizesWide_pureM5` sweep all of `ℤ₂`. -/
theorem mIsUnit_one_sub_two_pow {α : ℕ} (hα : 2 ≤ α) : IsUnit ((1 : ℤ_[2]) - 2 ^ (α - 1)) := by
  refine mIsUnit_of_parity_one ?_
  have hev : mParityZ ((2 : ℤ_[2]) ^ (α - 1)) = 0 := by
    have h := mParityZ_mul_two_pow hα 1
    rwa [one_mul] at h
  rw [mParityZ_sub, mParityZ_one, hev, add_zero]

/-- **Every displayed pure `M5` move is realized inside `A⁺(P,h)`**, at `α ≥ 2` (the smallest
valid exponent, `Parameters.lean`'s `Valid`).  Reparametrization by the unit of
`mIsUnit_one_sub_two_pow`. -/
theorem exists_dmRealizesWide_frameMixX1 (hα : 2 ≤ α) (b : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      DmRealizesWide α h Ψ (frameEnd (nFrameMixX1 b)) := by
  set u := (mIsUnit_one_sub_two_pow hα).unit with hu
  have huval : ((u : ℤ_[2]ˣ) : ℤ_[2]) = 1 - 2 ^ (α - 1) := IsUnit.unit_spec _
  have hkey : b * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * (1 - 2 ^ (α - 1)) = b := by
    rw [← huval, mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, mul_one]
  exact ⟨_, hkey ▸ dmRealizesWide_pureM5 α h (by omega) (b * ((u⁻¹ : ℤ_[2]ˣ) : ℤ_[2]))⟩

end PureLift

/-! ## §4 The payoff

`MCoreMixHypothesisWide` for the **whole** displayed `M5` stratum — the same stratum set
`{frameEnd (nFrameMixX1 b) | b}` that `nCoreMixHypothesisWide_mixX1` lands on the `N` side, and
that `nCoreMixHypothesis_not_of_mix` refutes over the narrow `A(P,h)`. -/

section Payoff

variable (α h : ℕ)

/-- **MC1 §5.3's `⟨M5⟩` factor is a THEOREM over `A⁺(P,h)`, at the displayed move** — HM6ef's
`mCoreMixHypothesisWide_m5` upgraded from the `τ_c`-corrected twist `hm6FrameBDc k` to MC1's
displayed pure `M5`, on literally the `N`-side stratum set of `nCoreMixHypothesisWide_mixX1`.
No new axiom, no B8, no second widening; census unchanged. -/
theorem mCoreMixHypothesisWide_pureM5 (hα : 2 ≤ α) :
    MCoreMixHypothesisWide α h (Set.range fun b : ℤ_[2] => frameEnd (nFrameMixX1 b)) := by
  rintro F ⟨b, rfl⟩
  exact exists_dmRealizesWide_frameMixX1 α h hα b

/-- **The `M` mirror of `nMixPairHypothesis_coreMix`**: for every 2-adic `b`, a χ-preserving
continuous automorphism of `D_M` whose ν-frame action at the marked generators is the displayed
pure `M5` move `B̄ ↦ B̄ + b·C̄₀`.  Stated at the marked generators, with the χ clause supplied by
HM5's `chiM_of_mem_dmClearAutsWide` from the same membership certificate — exactly the shape
`NMixHypothesis` has on the `N` side.  (There is no `M`-side binder of this shape to discharge:
see §6.) -/
theorem mMixFamily_coreMix (hα : 2 ≤ α) (b : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (Ψ x) = chiM α h x)
        ∧ ∀ f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]),
          nuFrame f (fun i => Ψ (dmGen α h i)) = nFrameMixX1 b (nuFrame f (dmGen α h)) := by
  obtain ⟨Ψ, hmem, hfr⟩ := exists_dmRealizesWide_frameMixX1 α h hα b
  exact ⟨Ψ, chiM_of_mem_dmClearAutsWide α h hmem, fun f => by rw [hfr f, frameEnd_apply]⟩

/-- **MC3's family `M1`, read through the pinned `Ā`-row**: `Λ_k` is χ-preserving (MC3's
`chiM_mLambdaEquiv`) and its ν-frame action is the displayed pure `M5` move at parameter
`−k·2^{α−1}`.  So `τ_a` does land in the `M5` direction — but only inside the parameter ideal
`2^{α−1}ℤ₂`, whereas `mMixFamily_coreMix` reaches all of `ℤ₂` without leaving `A⁺(P,h)`.  This is
why HM6ef's residual item needs no second widening of the generating set. -/
theorem nuFrame_mLambdaEquiv_eq (hα : 1 ≤ α) (k : ℤ_[2])
    (f : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (fun i => mLambdaEquiv α h k (dmGen α h i))
      = nFrameMixX1 (-(k * 2 ^ (α - 1))) (nuFrame f (dmGen α h)) := by
  rw [nuFrame_mLambdaEquiv]
  exact mFrameLambda_eq_nFrameMixX1 k _ _ (mChar_frameZero α h hα f)

end Payoff

/-! ## §5 Stress pins at `(α, h) = (2, 1)`

`α = 2` is the smallest valid exponent and `h = 1` the smallest instance with a genuine handle,
matching the lane's pin idiom.  At `α = 2` the twist coefficient is `1 − 2 = −1`, so the pins
also show the reparametrization doing visible work. -/

section StressPin

/-- The rank-four core with one handle has six letters. -/
example : coreRank 1 = 6 := by decide

/-- The `α = 2` twist exponent is `2^{α−1} = 2` — a kernel `decide` on the `ℕ`-side arithmetic
that feeds the pins below. -/
example : (2 : ℕ) ^ (2 - 1) = 2 := by decide

/-- Pin: at `α = 2` the twist coefficient is the unit `−1`. -/
example : (1 : ℤ_[2]) - 2 ^ (2 - 1) = -1 := by norm_num

/-- **The whole displayed `M5` stratum is realized at `(2, 1)`** — the `M` mirror of HM6f's
`nCoreMixHypothesisWide_mixX1` pin, on the same stratum set. -/
example : MCoreMixHypothesisWide 2 1 (Set.range fun b : ℤ_[2] => frameEnd (nFrameMixX1 b)) :=
  mCoreMixHypothesisWide_pureM5 2 1 le_rfl

/-- And the χ-preserving marked-generator form, at the move `B̄ ↦ B̄ + C̄₀`. -/
example : ∃ Ψ : ContinuousMulEquiv (DM 2 1 : Type) (DM 2 1 : Type),
    (∀ x, chiM 2 1 (Ψ x) = chiM 2 1 x)
      ∧ ∀ f : ContinuousMonoidHom (DM 2 1 : Type) (Multiplicative ℤ_[2]),
        nuFrame f (fun i => Ψ (dmGen 2 1 i)) = nFrameMixX1 1 (nuFrame f (dmGen 2 1)) :=
  mMixFamily_coreMix 2 1 le_rfl 1

/-- Pin: at `(2, 1)` the `Ā`-row is `−2·C̄₀` for every `ℤ₂`-character. -/
example (f : ContinuousMonoidHom (DM 2 1 : Type) (Multiplicative ℤ_[2])) :
    nuFrame f (dmGen 2 1) 0 = -(2 * nuFrame f (dmGen 2 1) 2) := by
  simpa using mChar_frameZero 2 1 one_le_two f

end StressPin

/-! ## §6 What stays binder-shaped on `M`

HM6ef's §6 listed two residues.  The first — "the `M5` isolation's last shear" — is closed by
this file: `mCoreMixHypothesisWide_pureM5` lands MC1's *displayed* `M5` over `A⁺(P,h)` at every
2-adic parameter, and `mMixFamily_coreMix` states it at the marked generators with χ.  What
remains is:

* **`⟨M4, M6, M7⟩`** (memo §4.2, §4.3) — unchanged, and unchanged *in kind*: these directions are
  structurally obstructed rather than merely unbuilt (they are not symplectic, hence not reachable
  by any relator-preserving word automorphism), so no widening of the generating set produces
  them.  `MCoreMixHypothesisWide α h ⟨M4, M6, M7⟩` therefore stays a binder, with MC1 §8
  Decision 2(A)'s levelwise/graded-Lie price and its "unknown risk" label intact.
* **MC3's S2 unit-scaling binder** — family `M3` (`Σ_γ : C₀ ↦ C₀^γ`), which runs through the
  *existing* axiom B8 exactly as its `N`-side counterpart does.  Untouched here.

Two scoping notes, so that the boundary of this file is not mistaken for a mathematical one.

1. **`MMixHypothesis` is not discharged, not even partially.**  MC3's binder
   (`M.lean:1560`) is *marking-transport* shaped — "carry a cleared `ν'` to `ν_M`" — not
   family shaped, and the `M` lane has no `mMixHypothesis_of_pair` analogue of MC4's
   `nMixHypothesis_of_pair` to feed a family into it.  Consuming `mMixFamily_coreMix` there
   needs the *other* strata as well (the `M4` unit scaling of the `B̄`-row and the `M3` unit
   scaling of the `C̄₀`-row at least), so no corollary lands, and none is claimed.  Restating
   `MMixHypothesis` in the consumed family form would change MC3's contract, which is an owner
   call, not a worker one.
2. **`mCoreMixHypothesisWide_m5` is not superseded.**  HM6ef's statement is about the corrected
   twist `hm6FrameBDc k` at *general* `α ≥ 0`; this file's needs `α ≥ 2` for the unit, and `α ≥ 1`
   already for the pinning `Ā = −2^{α−1}C̄₀`.  Both stand.

The `N` lane still has no S3 residue at all. -/

end MarkedCore

end Dyadic

end GQ2
