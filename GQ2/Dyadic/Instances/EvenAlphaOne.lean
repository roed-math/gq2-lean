/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenUnramified

/-!
# W70-ALPHA1: the `α = 1` even cores, computed

Owner decision 2 of 2026-08-12 (`docs/dyadic/owner-items-2026-08-05.md`), with its caveat:
settle the direction before spending.  This file settles it by computing, and the computation
comes out against the recorded residual.

## The direction, decided by a single binomial coefficient

The committed even Gram (`GQ2.Dyadic.EvenModel.evenCupForm`) is proved at `2 ≤ α` and the only
step that consumes that hypothesis is the diagonal exponent rule: the head power `a ^ (2 + 2 ^ α)`
of the `N` relator contributes `diagCoeff (2 + 2 ^ α) · κ(a, a)` to the relator fibre, and
`diagCoeff` depends only on the exponent mod `4` (`diagCoeff_mod_four`).  At `α = 1` the head
exponent is `2 + 2 = 4` and `diagCoeff 4 = C(4,2) = 6 ≡ 0`, so the head diagonal entry does die,
exactly as the residual's docstring says.

What the residual's docstring then infers does **not** follow.  Killing the `(0,0)` entry of

`[[1,1,0,0], [1,0,0,0], [0,0,0,1], [0,0,1,0]]`   (the committed `α ≥ 2` Gram)

leaves

`[[0,1,0,0], [1,0,0,0], [0,0,0,1], [0,0,1,0]]`   (`evenAlphaOneNCupForm`, §3),

which is two hyperbolic blocks and one hyperbolic block per handle.  That matrix is its own
inverse and has determinant `1`: it is **nondegenerate**.  What it is, is *alternating*:
`evenAlphaOneNCupForm v v = 0` for every `v` (§3), where the committed form has
`evenCupForm v v = v 0`.  Alternating is not degenerate, and the two were conflated.

So the `α = 1` `N` core is Demushkin (§8), the recorded residual `EvenDemResidualAlphaOneN` is
**false** (§9), and the vanishing of every cup square is the mod-`2` shadow of `q ≠ 2` rather than
a failure of the Demushkin property.  This is the reading `Instances/EvenUnramified.lean`
proposed; it is now computed rather than proposed.

## The `M` row goes the same way for the opposite reason

At `α = 1` the `M` relator's second power is `c ^ (2 ^ 1) = c ²` and `diagCoeff 2 = 1`, so the
`M` row *gains* a diagonal entry at slot `2`:

`[[1,1,0,0], [1,0,0,0], [0,0,1,1], [0,0,1,0]]`   (`evenAlphaOneMCupForm`, §3),

two copies of the committed head block.  Determinant `1` again, so nondegenerate again, and the
`M` core is Demushkin at `α = 1` too (§8).  Here the form is **not** alternating:
`evenAlphaOneMCupForm v v = v 0 + v 2`.  So the two rows part company at `α = 1` after all, but
not over Demushkin-ness, only over whether the form is alternating.

## What is proved, and at which `h`

Everything below is proved for **every** handle count `h : ℕ`, uniformly, by the same route the
committed `2 ≤ α` package uses.  No case of `h` is checked separately and none is extrapolated
from.  The only `decide` calls in the file are `diagCoeff 4 = 0`, `diagCoeff 2 = 1`, and two
identities of `ZMod 2`; each is a statement about one fixed finite object, and none of them
ranges over `h` or over `α`.

The branch depth is a different matter and is stated as such: `α` is **fixed at `1`** in every
statement from §2 on.  Nothing here is claimed at any other `α`, and in particular nothing here
bears on `α = 0`, where the relator leaves the Frattini subgroup.

The `α ≥ 2` hypothesis of the even classification is therefore **not** forced by a Demushkin
failure at `α = 1` on either row.  §10 says precisely what it is forced by instead.

## Numbering

1. The two `α = 1` diagonal coefficients.
2. The two `α = 1` relator fibres.
3. The two `α = 1` Gram forms, and the alternating split.
4. `relZ` at `α = 1`.
5. The obstruction of a coordinate cup, and the cup detector.
6. Nondegeneracy: the two inverse Grams.
7. `#H² = 2` at `α = 1`.
8. `IsDemushkin` at `α = 1`, on both rows.
9. The verdict on the two recorded residuals.
10. What `α ≥ 2` means now.
11. The third stratum's surviving point.
12. Axiom pins.
-/

namespace GQ2.Dyadic.EvenAlphaOne

noncomputable section

open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.EvenModel ContCoh

/-- The coefficient action at the `N` core, as everywhere on this route. -/
local instance evenAlphaOneScalarDN (α h : ℕ) : DistribMulAction (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of the `N`-core coefficient action. -/
local instance evenAlphaOneContinuousDN (α h : ℕ) : ContinuousSMul (DN α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- The coefficient action at the `M` core. -/
local instance evenAlphaOneScalarDM (α h : ℕ) : DistribMulAction (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of the `M`-core coefficient action. -/
local instance evenAlphaOneContinuousDM (α h : ℕ) : ContinuousSMul (DM α h : Type) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-! ## §1 The two `α = 1` diagonal coefficients

The whole direction question is these two numbers.  `diagCoeff k = C(k,2) mod 2` is the fibre
contribution of a `k`-th power in a class-two central extension (`MarkedCore/Cores.lean:1212`). -/

/-- **The `N` head diagonal dies at `α = 1`.**  `C(4,2) = 6 ≡ 0 (mod 2)`.  This is the one
computation the residual's docstring got right, and it is the reason the committed
`diagCoeff_two_pow` route is unavailable: `2 + 2 ^ 1 = 4 ≡ 0 (mod 4)` rather than `≡ 2`. -/
theorem evenAlphaOne_diagCoeff_nHead : diagCoeff (2 + 2 ^ 1) = 0 := by decide

/-- **The `M` second diagonal appears at `α = 1`.**  `2 ^ 1 = 2` and `C(2,2) = 1`, where for
`2 ≤ α` the exponent `2 ^ α ≡ 0 (mod 4)` contributes nothing (`diagCoeff_two_pow`). -/
theorem evenAlphaOne_diagCoeff_mSecond : diagCoeff (2 ^ 1) = 1 := by decide

/-! ## §2 The two `α = 1` relator fibres

The committed fibre lemmas `nWord_centLift_fib` / `mWord_centLift_fib`
(`MarkedCore/Cores.lean:1408`, `:1389`) carry `2 ≤ α` only through §1.  These are the same
proofs with §1 substituted, so the two rows now have genuinely different fibres. -/

section Fib

variable {L : Type} [Group L] {c : DRCoh.TwoCocycle L}

/-- The two-factor base bookkeeping of `MarkedCore/Cores.lean`, which is private there. -/
private theorem evenAlphaOne_base_mul {p q : DRCoh.CentExt c} (hp : p.base = 1)
    (hq : q.base = 1) : (p * q).base = 1 := by
  rw [DRCoh.CentExt.mul_base, hp, hq, one_mul]

variable (hc : IsCupCocycle c)
include hc

/-- **The `α = 1` `N` core-word fibre.**  `x₀⁴[x₀,x₁][x₂,x₃]`: the head power contributes
`diagCoeff 4 · κ(a,a) = 0`, so only the two commutators survive.  Compare
`nWord_centLift_fib`, whose value carries the extra `κ(a,a)`. -/
theorem evenAlphaOne_nWord_fib (a b d e : L) :
    (nWord 1 (centLift c a) (centLift c b) (centLift c d) (centLift c e)).fib
      = (c.κ a b + c.κ b a) + (c.κ d e + c.κ e d) := by
  have hpow : ((centLift c a) ^ (2 + 2 ^ 1)).base = 1 := by
    rw [show 2 + 2 ^ 1 = 2 * 2 from rfl]
    exact hc.pow_even_base a 2
  rw [nWord, fib_mul_of_base_one (evenAlphaOne_base_mul hpow (hc.commP_base a b)),
    fib_mul_of_base_one hpow, centLift_pow_fib (hc.kappa_pow_left a), hc.commP_fib, hc.commP_fib,
    evenAlphaOne_diagCoeff_nHead, zero_mul, zero_add]

/-- **The `α = 1` `M` core-word fibre.**  `a²[a,b]c²[c,d]`: *both* powers are honest squares, so
there are two diagonal contributions where the committed `2 ≤ α` value has one. -/
theorem evenAlphaOne_mWord_fib (a b d e : L) :
    (mWord 1 (centLift c a) (centLift c b) (centLift c d) (centLift c e)).fib
      = c.κ a a + (c.κ a b + c.κ b a) + (c.κ d d + (c.κ d e + c.κ e d)) := by
  have hsq : ((centLift c a) ^ 2).base = 1 := hc.pow_even_base a 1
  have hpow : ((centLift c d) ^ (2 ^ 1)).base = 1 := by
    rw [show (2 : ℕ) ^ 1 = 2 * 1 from rfl]
    exact hc.pow_even_base d 1
  rw [mWord,
    fib_mul_of_base_one (evenAlphaOne_base_mul (evenAlphaOne_base_mul hsq (hc.commP_base a b))
      hpow),
    fib_mul_of_base_one (evenAlphaOne_base_mul hsq (hc.commP_base a b)),
    fib_mul_of_base_one hsq,
    centLift_pow_fib (hc.kappa_pow_left a), centLift_pow_fib (hc.kappa_pow_left d),
    hc.commP_fib, hc.commP_fib, diagCoeff_two, evenAlphaOne_diagCoeff_mSecond, one_mul, one_mul]
  ring

/-- **The full `α = 1` `N` relator fibre**, handles included. -/
theorem evenAlphaOne_nRelWord_fib {h : ℕ} (m : Fin (coreRank h) → L) :
    (nRelWord 1 fun i => centLift c (m i)).fib
      = (c.κ (m 0) (m 1) + c.κ (m 1) (m 0)) + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  have hbase : (nWord 1 (centLift c (m 0)) (centLift c (m 1)) (centLift c (m 2))
      (centLift c (m 3))).base = 1 := by
    have hpow : ((centLift c (m 0)) ^ (2 + 2 ^ 1)).base = 1 := by
      rw [show 2 + 2 ^ 1 = 2 * 2 from rfl]
      exact hc.pow_even_base (m 0) 2
    exact evenAlphaOne_base_mul (evenAlphaOne_base_mul hpow (hc.commP_base _ _))
      (hc.commP_base _ _)
  rw [nRelWord, fib_mul_of_base_one hbase, evenAlphaOne_nWord_fib hc,
    hc.handleWord_centLift_fib]

/-- **The full `α = 1` `M` relator fibre**, handles included. -/
theorem evenAlphaOne_mRelWord_fib {h : ℕ} (m : Fin (coreRank h) → L) :
    (mRelWord 1 fun i => centLift c (m i)).fib
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 2) + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2)))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  have hbase : (mWord 1 (centLift c (m 0)) (centLift c (m 1)) (centLift c (m 2))
      (centLift c (m 3))).base = 1 := by
    have hsq : ((centLift c (m 0)) ^ 2).base = 1 := hc.pow_even_base (m 0) 1
    have hpow : ((centLift c (m 2)) ^ (2 ^ 1)).base = 1 := by
      rw [show (2 : ℕ) ^ 1 = 2 * 1 from rfl]
      exact hc.pow_even_base (m 2) 1
    exact evenAlphaOne_base_mul
      (evenAlphaOne_base_mul (evenAlphaOne_base_mul hsq (hc.commP_base _ _)) hpow)
      (hc.commP_base _ _)
  rw [mRelWord, fib_mul_of_base_one hbase, evenAlphaOne_mWord_fib hc,
    hc.handleWord_centLift_fib]

end Fib

/-! ## §3 The two `α = 1` Gram forms

`evenCupForm` (`Instances/EvenModelH2.lean:76`) is the `2 ≤ α` value, shared by the two rows.  At
`α = 1` there are two forms, and neither is it. -/

/-- **The `α = 1` `N` Gram**: `evenCupForm` with the `(0,0)` entry removed.  Head block
`[[0,1],[1,0]]`, core block `[[0,1],[1,0]]`, one hyperbolic block per handle. -/
def evenAlphaOneNCupForm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) : ZMod 2 :=
  (v 0 * w 1 + v 1 * w 0) + (v 2 * w 3 + v 3 * w 2)
    + ∑ j, (v (handleIdxU j) * w (handleIdxV j) + v (handleIdxV j) * w (handleIdxU j))

/-- **The `α = 1` `M` Gram**: `evenCupForm` with a `(2,2)` entry added.  Head block `[[1,1],[1,0]]`
and core block `[[1,1],[1,0]]`, one hyperbolic block per handle. -/
def evenAlphaOneMCupForm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) : ZMod 2 :=
  v 0 * w 0 + (v 0 * w 1 + v 1 * w 0) + (v 2 * w 2 + (v 2 * w 3 + v 3 * w 2))
    + ∑ j, (v (handleIdxU j) * w (handleIdxV j) + v (handleIdxV j) * w (handleIdxU j))

private theorem evenAlphaOne_handle_swap {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) :
    (∑ j, (v (handleIdxU j) * w (handleIdxV j) + v (handleIdxV j) * w (handleIdxU j))) =
      ∑ j, (w (handleIdxU j) * v (handleIdxV j) + w (handleIdxV j) * v (handleIdxU j)) :=
  Finset.sum_congr rfl fun j _ => by ring

/-- The `α = 1` `N` Gram is symmetric, so one nondegeneracy argument serves both slots. -/
theorem evenAlphaOneNCupForm_comm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneNCupForm v w = evenAlphaOneNCupForm w v := by
  simp only [evenAlphaOneNCupForm]
  rw [evenAlphaOne_handle_swap]
  ring

/-- The `α = 1` `M` Gram is symmetric. -/
theorem evenAlphaOneMCupForm_comm {h : ℕ} (v w : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneMCupForm v w = evenAlphaOneMCupForm w v := by
  simp only [evenAlphaOneMCupForm]
  rw [evenAlphaOne_handle_swap]
  ring

private theorem evenAlphaOne_handle_self {h : ℕ} (v : Fin (coreRank h) → ZMod 2) :
    (∑ j, (v (handleIdxU j) * v (handleIdxV j) + v (handleIdxV j) * v (handleIdxU j))) = 0 :=
  Finset.sum_eq_zero fun j _ => by
    rw [mul_comm (v (handleIdxV j))]
    exact CharTwo.add_self_eq_zero _

/-- **THE `α = 1` `N` FORM IS ALTERNATING.**  Every cup square vanishes, where the committed
`2 ≤ α` form has `evenCupForm v v = v 0`.  This is the fact the recorded residual read as
degeneracy; §6 shows the form is nondegenerate all the same.  Over `𝔽₂` an alternating
nondegenerate form is exactly a sum of hyperbolic planes, which is what §3's matrix is. -/
theorem evenAlphaOneNCupForm_self {h : ℕ} (v : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneNCupForm v v = 0 := by
  simp only [evenAlphaOneNCupForm, evenAlphaOne_handle_self, add_zero]
  rw [mul_comm (v 1) (v 0), mul_comm (v 3) (v 2), CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, add_zero]

/-- **The `α = 1` `M` form is not alternating**: the cup square is `v 0 + v 2`, two diagonal
entries where the committed form has one.  The `M` row therefore keeps a nonzero cup square at
`α = 1`, which is why its `#H²` lower bound (§7) can still be run on a single class. -/
theorem evenAlphaOneMCupForm_self {h : ℕ} (v : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneMCupForm v v = v 0 + v 2 := by
  have hsq : ∀ x : ZMod 2, x * x = x := by decide
  simp only [evenAlphaOneMCupForm, evenAlphaOne_handle_self, add_zero]
  rw [mul_comm (v 1) (v 0), mul_comm (v 3) (v 2), CharTwo.add_self_eq_zero,
    CharTwo.add_self_eq_zero, add_zero, add_zero, hsq (v 0), hsq (v 2)]

/-! ## §4 `relZ` at `α = 1`

`relZ_nNatWord` / `relZ_mNatWord` (`MarkedCore/Certificate.lean:241`, `:235`) carry no `α`
hypothesis: they are the definitional bridge from the generic obstruction to §2's fibres.  Only
the `_cupGram` wrappers carry `2 ≤ α`, and these are their `α = 1` replacements. -/

section RelZ

variable {L : Type} [Group L] {c : DRCoh.TwoCocycle L} (hc : IsCupCocycle c)
include hc

/-- **The `α = 1` `N` relator obstruction against a cup cocycle.**  The replacement for
`relZ_nNatWord_cupGram`, which needs `2 ≤ α`. -/
theorem evenAlphaOne_relZ_nNatWord {h : ℕ} (m : Fin (coreRank h) → L) :
    WordCoh.relZ (nNatWord 1 h) m (WordCoh.ofDRCoh c)
      = (c.κ (m 0) (m 1) + c.κ (m 1) (m 0)) + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  rw [relZ_nNatWord]
  exact evenAlphaOne_nRelWord_fib hc m

/-- **The `α = 1` `M` relator obstruction against a cup cocycle.** -/
theorem evenAlphaOne_relZ_mNatWord {h : ℕ} (m : Fin (coreRank h) → L) :
    WordCoh.relZ (mNatWord 1 h) m (WordCoh.ofDRCoh c)
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 2) + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2)))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  rw [relZ_mNatWord]
  exact evenAlphaOne_mRelWord_fib hc m

end RelZ

/-! ## §5 The obstruction of a coordinate cup product, at `α = 1`

The committed `obsH2_DN_coordinateCup` / `obsH2_DM_coordinateCup`
(`Instances/EvenModelH2.lean:332`, `:368`) with §4 in place of the `2 ≤ α` Gram.  Everything else
in those proofs (the coordinate characters, the pair cocycle, the factoring) needs only
`1 ≤ α`, which `α = 1` satisfies. -/

private theorem evenAlphaOne_one_le : (1 : ℕ) ≤ 1 := le_rfl

/-- **The `α = 1` `N`-row obstruction is the `α = 1` `N` Gram.** -/
theorem evenAlphaOne_obsH2_DN (h : ℕ) (v w : Fin (coreRank h) → ZMod 2) :
    WordCoh.obsH2 (fun _ _ => rfl) (nNatWord 1 h) (dnGen 1 h)
        (markedRelator_DN 1 h evenAlphaOne_one_le)
        (H2mk (DN 1 h : Type) (ZMod 2) (dnCoordinateCupZTwo 1 h evenAlphaOne_one_le v w)) =
      evenAlphaOneNCupForm v w := by
  let rho : (DN 1 h : Type) →* EvenCupBase :=
    (dnCoordinateCharacter 1 h evenAlphaOne_one_le v).toMonoidHom.prod
      (dnCoordinateCharacter 1 h evenAlphaOne_one_le w).toMonoidHom
  have hfactor : ∀ g k : (DN 1 h : Type),
      (dnCoordinateCupZTwo 1 h evenAlphaOne_one_le v w).1 (g, k) =
        (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := fun _ _ => rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl) (nNatWord 1 h) (dnGen 1 h)
    (markedRelator_DN 1 h evenAlphaOne_one_le)
    (dnCoordinateCupZTwo 1 h evenAlphaOne_one_le v w) rho
    (WordCoh.ofDRCoh evenPairCupCocycle) hfactor]
  have hgen : ∀ (u : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)),
      Multiplicative.toAdd
        ((dnCoordinateCharacter 1 h evenAlphaOne_one_le u).toMonoidHom (dnGen 1 h i)) = u i := by
    intro u i
    change Multiplicative.toAdd
      (dnCoordinateCharacter 1 h evenAlphaOne_one_le u (dnGen 1 h i)) = u i
    rw [dnCoordinateCharacter_gen, toAdd_ofAdd]
  rw [evenAlphaOne_relZ_nNatWord evenPairCupCocycle_isCup fun i => rho (dnGen 1 h i)]
  simp only [evenAlphaOneNCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply, hgen]

/-- **The `α = 1` `M`-row obstruction is the `α = 1` `M` Gram.** -/
theorem evenAlphaOne_obsH2_DM (h : ℕ) (v w : Fin (coreRank h) → ZMod 2) :
    WordCoh.obsH2 (fun _ _ => rfl) (mNatWord 1 h) (dmGen 1 h)
        (markedRelator_DM 1 h evenAlphaOne_one_le)
        (H2mk (DM 1 h : Type) (ZMod 2) (dmCoordinateCupZTwo 1 h evenAlphaOne_one_le v w)) =
      evenAlphaOneMCupForm v w := by
  let rho : (DM 1 h : Type) →* EvenCupBase :=
    (dmCoordinateCharacter 1 h evenAlphaOne_one_le v).toMonoidHom.prod
      (dmCoordinateCharacter 1 h evenAlphaOne_one_le w).toMonoidHom
  have hfactor : ∀ g k : (DM 1 h : Type),
      (dmCoordinateCupZTwo 1 h evenAlphaOne_one_le v w).1 (g, k) =
        (WordCoh.ofDRCoh evenPairCupCocycle).κ (rho g) (rho k) := fun _ _ => rfl
  rw [WordCoh.obsH2_eq_of_factor (fun _ _ => rfl) (mNatWord 1 h) (dmGen 1 h)
    (markedRelator_DM 1 h evenAlphaOne_one_le)
    (dmCoordinateCupZTwo 1 h evenAlphaOne_one_le v w) rho
    (WordCoh.ofDRCoh evenPairCupCocycle) hfactor]
  have hgen : ∀ (u : Fin (coreRank h) → ZMod 2) (i : Fin (coreRank h)),
      Multiplicative.toAdd
        ((dmCoordinateCharacter 1 h evenAlphaOne_one_le u).toMonoidHom (dmGen 1 h i)) = u i := by
    intro u i
    change Multiplicative.toAdd
      (dmCoordinateCharacter 1 h evenAlphaOne_one_le u (dmGen 1 h i)) = u i
    rw [dmCoordinateCharacter_gen, toAdd_ofAdd]
  rw [evenAlphaOne_relZ_mNatWord evenPairCupCocycle_isCup fun i => rho (dmGen 1 h i)]
  simp only [evenAlphaOneMCupForm, rho, evenPairCupCocycle, MonoidHom.prod_apply, hgen]

/-- A nonzero `α = 1` `N` Gram value detects a nonzero cup class. -/
theorem evenAlphaOne_cup_ne_zero_DN (h : ℕ) {v w : Fin (coreRank h) → ZMod 2}
    (hgram : evenAlphaOneNCupForm v w ≠ 0) :
    trivialCupPairing 2 (DN 1 h : Type) (fun _ _ => rfl)
        (dnCoordinateHOne 1 h evenAlphaOne_one_le v)
        (dnCoordinateHOne 1 h evenAlphaOne_one_le w) ≠ 0 := by
  rw [dnCoordinateHOne_cup]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (nNatWord 1 h) (dnGen 1 h)
      (markedRelator_DN 1 h evenAlphaOne_one_le)) hzero
  rw [evenAlphaOne_obsH2_DN h, map_zero] at hobs
  exact hgram hobs

/-- A nonzero `α = 1` `M` Gram value detects a nonzero cup class. -/
theorem evenAlphaOne_cup_ne_zero_DM (h : ℕ) {v w : Fin (coreRank h) → ZMod 2}
    (hgram : evenAlphaOneMCupForm v w ≠ 0) :
    trivialCupPairing 2 (DM 1 h : Type) (fun _ _ => rfl)
        (dmCoordinateHOne 1 h evenAlphaOne_one_le v)
        (dmCoordinateHOne 1 h evenAlphaOne_one_le w) ≠ 0 := by
  rw [dmCoordinateHOne_cup]
  intro hzero
  have hobs := congrArg
    (WordCoh.obsH2 (fun _ _ => rfl) (mNatWord 1 h) (dmGen 1 h)
      (markedRelator_DM 1 h evenAlphaOne_one_le)) hzero
  rw [evenAlphaOne_obsH2_DM h, map_zero] at hobs
  exact hgram hobs

/-! ## §6 Nondegeneracy: the two inverse Grams

Both `α = 1` matrices are invertible over `𝔽₂`, and their inverses are as explicit as the
committed `evenDualMap`.  The `N` matrix is a sum of hyperbolic planes, hence **its own inverse**:
the dual vector of slot `i` is the basis vector of the partner slot, with no correction term.
The `M` matrix is two copies of the committed head block `[[1,1],[1,0]]`, so it takes the
committed correction term at slot `1` and a second one at slot `3`.

`evenPartner` and `evenDot` are the committed index involution and dot product
(`Instances/EvenModelDemushkin.lean:74`, `:157`); `evenDot_single` is reused verbatim. -/

private theorem evenAlphaOne_ne_of_val {h : ℕ} {i k : Fin (coreRank h)}
    (hne : (i : ℕ) ≠ (k : ℕ)) : i ≠ k := fun e => hne (congrArg Fin.val e)

private theorem evenAlphaOne_handleU_ne_one {h : ℕ} (j : Fin h) :
    handleIdxU j ≠ (1 : Fin (coreRank h)) :=
  evenAlphaOne_ne_of_val (by rw [handleIdxU_val, coreVal_one]; omega)

private theorem evenAlphaOne_handleV_ne_one {h : ℕ} (j : Fin h) :
    handleIdxV j ≠ (1 : Fin (coreRank h)) :=
  evenAlphaOne_ne_of_val (by rw [handleIdxV_val, coreVal_one]; omega)

private theorem evenAlphaOne_handleU_ne_three {h : ℕ} (j : Fin h) :
    handleIdxU j ≠ (3 : Fin (coreRank h)) :=
  evenAlphaOne_ne_of_val (by rw [handleIdxU_val, coreVal_three]; omega)

private theorem evenAlphaOne_handleV_ne_three {h : ℕ} (j : Fin h) :
    handleIdxV j ≠ (3 : Fin (coreRank h)) :=
  evenAlphaOne_ne_of_val (by rw [handleIdxV_val, coreVal_three]; omega)

/-- **The `α = 1` `N` inverse Gram**, as a plain map on coordinate vectors: the hyperbolic
involution `evenPartner`, with no correction term.  The `N` Gram at `α = 1` is its own inverse. -/
def evenAlphaOneNDual {h : ℕ} (u : Fin (coreRank h) → ZMod 2) : Fin (coreRank h) → ZMod 2 :=
  fun k => u (evenPartner k)

/-- **The `α = 1` `M` inverse Gram**: `evenPartner` with the head-block correction at slot `1`
and its twin at slot `3`, the two `(1,1)` entries of `[[1,1],[1,0]]⁻¹ = [[0,1],[1,1]]`. -/
def evenAlphaOneMDual {h : ℕ} (u : Fin (coreRank h) → ZMod 2) : Fin (coreRank h) → ZMod 2 :=
  fun k => u (evenPartner k) + (if k = 1 then u 1 else 0) + (if k = 3 then u 3 else 0)

/-- **The `N` inversion identity.**  Pairing against `evenAlphaOneNDual u` in the `α = 1` `N` Gram
returns the plain dot product with `u`: in matrix terms `G · G⁻¹ = 1`. -/
theorem evenAlphaOneNCupForm_dual {h : ℕ} (v u : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneNCupForm v (evenAlphaOneNDual u) = evenDot v u := by
  have hsum : (∑ j, (v (handleIdxU j) * evenAlphaOneNDual u (handleIdxV j) +
      v (handleIdxV j) * evenAlphaOneNDual u (handleIdxU j))) =
        ∑ j, (v (handleIdxU j) * u (handleIdxU j) + v (handleIdxV j) * u (handleIdxV j)) :=
    Finset.sum_congr rfl fun j _ => by
      simp only [evenAlphaOneNDual, evenPartner_handleU, evenPartner_handleV]
  simp only [evenAlphaOneNCupForm, evenDot]
  rw [hsum]
  simp only [evenAlphaOneNDual, evenPartner_zero, evenPartner_one, evenPartner_two,
    evenPartner_three]

/-- **The `M` inversion identity.** -/
theorem evenAlphaOneMCupForm_dual {h : ℕ} (v u : Fin (coreRank h) → ZMod 2) :
    evenAlphaOneMCupForm v (evenAlphaOneMDual u) = evenDot v u := by
  have h2 : ∀ z : ZMod 2, z + z = 0 := by decide
  have hne01 : (0 : Fin (coreRank h)) ≠ 1 :=
    evenAlphaOne_ne_of_val (by rw [coreVal_zero, coreVal_one]; omega)
  have hne03 : (0 : Fin (coreRank h)) ≠ 3 :=
    evenAlphaOne_ne_of_val (by rw [coreVal_zero, coreVal_three]; omega)
  have hne13 : (1 : Fin (coreRank h)) ≠ 3 :=
    evenAlphaOne_ne_of_val (by rw [coreVal_one, coreVal_three]; omega)
  have hne21 : (2 : Fin (coreRank h)) ≠ 1 :=
    evenAlphaOne_ne_of_val (by rw [coreVal_two, coreVal_one]; omega)
  have hne23 : (2 : Fin (coreRank h)) ≠ 3 :=
    evenAlphaOne_ne_of_val (by rw [coreVal_two, coreVal_three]; omega)
  have w0 : evenAlphaOneMDual u 0 = u 1 := by
    show u (evenPartner 0) + (if (0 : Fin (coreRank h)) = 1 then u 1 else 0)
      + (if (0 : Fin (coreRank h)) = 3 then u 3 else 0) = u 1
    rw [evenPartner_zero, if_neg hne01, if_neg hne03, add_zero, add_zero]
  have w1 : evenAlphaOneMDual u 1 = u 0 + u 1 := by
    show u (evenPartner 1) + (if (1 : Fin (coreRank h)) = 1 then u 1 else 0)
      + (if (1 : Fin (coreRank h)) = 3 then u 3 else 0) = u 0 + u 1
    rw [evenPartner_one, if_pos rfl, if_neg hne13, add_zero]
  have w2 : evenAlphaOneMDual u 2 = u 3 := by
    show u (evenPartner 2) + (if (2 : Fin (coreRank h)) = 1 then u 1 else 0)
      + (if (2 : Fin (coreRank h)) = 3 then u 3 else 0) = u 3
    rw [evenPartner_two, if_neg hne21, if_neg hne23, add_zero, add_zero]
  have w3 : evenAlphaOneMDual u 3 = u 2 + u 3 := by
    show u (evenPartner 3) + (if (3 : Fin (coreRank h)) = 1 then u 1 else 0)
      + (if (3 : Fin (coreRank h)) = 3 then u 3 else 0) = u 2 + u 3
    rw [evenPartner_three, if_neg (Ne.symm hne13), if_pos rfl, add_zero]
  have hsum : (∑ j, (v (handleIdxU j) * evenAlphaOneMDual u (handleIdxV j) +
      v (handleIdxV j) * evenAlphaOneMDual u (handleIdxU j))) =
        ∑ j, (v (handleIdxU j) * u (handleIdxU j) + v (handleIdxV j) * u (handleIdxV j)) :=
    Finset.sum_congr rfl fun j _ => by
      simp only [evenAlphaOneMDual, evenPartner_handleU, evenPartner_handleV,
        if_neg (evenAlphaOne_handleU_ne_one j), if_neg (evenAlphaOne_handleV_ne_one j),
        if_neg (evenAlphaOne_handleU_ne_three j), if_neg (evenAlphaOne_handleV_ne_three j),
        add_zero]
  simp only [evenAlphaOneMCupForm, evenDot, w0, w1, w2, w3, hsum]
  linear_combination (h2 (v 0 * u 1)) + (h2 (v 2 * u 3))

/-- **The `N` dual vector of a slot**: pairing extracts that coordinate.  This is the
nondegeneracy certificate. -/
theorem evenAlphaOneNCupForm_dualVector {h : ℕ} (v : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) :
    evenAlphaOneNCupForm v (evenAlphaOneNDual (Pi.single i 1)) = v i := by
  rw [evenAlphaOneNCupForm_dual, evenDot_single]

/-- The `N` dual vector, in the left slot, by symmetry. -/
theorem evenAlphaOneNCupForm_dualVector_left {h : ℕ} (w : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) :
    evenAlphaOneNCupForm (evenAlphaOneNDual (Pi.single i 1)) w = w i := by
  rw [evenAlphaOneNCupForm_comm, evenAlphaOneNCupForm_dualVector]

/-- **The `M` dual vector of a slot.** -/
theorem evenAlphaOneMCupForm_dualVector {h : ℕ} (v : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) :
    evenAlphaOneMCupForm v (evenAlphaOneMDual (Pi.single i 1)) = v i := by
  rw [evenAlphaOneMCupForm_dual, evenDot_single]

/-- The `M` dual vector, in the left slot. -/
theorem evenAlphaOneMCupForm_dualVector_left {h : ℕ} (w : Fin (coreRank h) → ZMod 2)
    (i : Fin (coreRank h)) :
    evenAlphaOneMCupForm (evenAlphaOneMDual (Pi.single i 1)) w = w i := by
  rw [evenAlphaOneMCupForm_comm, evenAlphaOneMCupForm_dualVector]

/-! ## §7 `#H² = 2` at `α = 1`

`WordCoh.finite_H2` and `WordCoh.card_H2_le_two` carry no `α` hypothesis beyond the marked-relator
bundle, which exists from `1 ≤ α`.  Only the lower bound needs a Gram value, and on the `N` row it
can no longer be a cup *square*: §3 says every square vanishes.  A cup of two *different* classes
does the job, and §6 supplies one uniformly. -/

/-- **`#H²(D_N 1 h) = 2`.**  The lower bound is the cup of `e₀` with its `N` dual vector, which is
`1` by §6.  The committed `α ≥ 2` proof uses the cup square of `e₀`, which is unavailable here:
this is the one place where the alternating form changes the argument rather than the result. -/
theorem evenAlphaOne_card_H2_DN (h : ℕ) :
    Nat.card (H2 (DN 1 h : Type) (ZMod 2)) = 2 := by
  letI : Finite (H2 (DN 1 h : Type) (ZMod 2)) :=
    WordCoh.finite_H2 (fun _ _ => rfl) (nNatWord 1 h) (dnGen 1 h)
      (markedRelator_DN 1 h evenAlphaOne_one_le) (presentedBy_DN 1 h) (isProP_DN 1 h)
  have hle : Nat.card (H2 (DN 1 h : Type) (ZMod 2)) ≤ 2 :=
    WordCoh.card_H2_le_two (fun _ _ => rfl) (nNatWord 1 h) (dnGen 1 h)
      (markedRelator_DN 1 h evenAlphaOne_one_le) (presentedBy_DN 1 h) (isProP_DN 1 h)
  letI : Nontrivial (H2 (DN 1 h : Type) (ZMod 2)) :=
    ⟨trivialCupPairing 2 (DN 1 h : Type) (fun _ _ => rfl)
        (dnCoordinateHOne 1 h evenAlphaOne_one_le (Pi.single 0 1))
        (dnCoordinateHOne 1 h evenAlphaOne_one_le
          (evenAlphaOneNDual (Pi.single (0 : Fin (coreRank h)) 1))), 0,
      evenAlphaOne_cup_ne_zero_DN h (by
        rw [evenAlphaOneNCupForm_dualVector, Pi.single_eq_same]
        exact one_ne_zero)⟩
  have hgt : 1 < Nat.card (H2 (DN 1 h : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-- **`#H²(D_M 1 h) = 2`.**  The `M` form is not alternating, so the committed cup-square witness
would still work; the dual vector is used anyway so that the two rows read the same. -/
theorem evenAlphaOne_card_H2_DM (h : ℕ) :
    Nat.card (H2 (DM 1 h : Type) (ZMod 2)) = 2 := by
  letI : Finite (H2 (DM 1 h : Type) (ZMod 2)) :=
    WordCoh.finite_H2 (fun _ _ => rfl) (mNatWord 1 h) (dmGen 1 h)
      (markedRelator_DM 1 h evenAlphaOne_one_le) (presentedBy_DM 1 h) (isProP_DM 1 h)
  have hle : Nat.card (H2 (DM 1 h : Type) (ZMod 2)) ≤ 2 :=
    WordCoh.card_H2_le_two (fun _ _ => rfl) (mNatWord 1 h) (dmGen 1 h)
      (markedRelator_DM 1 h evenAlphaOne_one_le) (presentedBy_DM 1 h) (isProP_DM 1 h)
  letI : Nontrivial (H2 (DM 1 h : Type) (ZMod 2)) :=
    ⟨trivialCupPairing 2 (DM 1 h : Type) (fun _ _ => rfl)
        (dmCoordinateHOne 1 h evenAlphaOne_one_le (Pi.single 0 1))
        (dmCoordinateHOne 1 h evenAlphaOne_one_le
          (evenAlphaOneMDual (Pi.single (0 : Fin (coreRank h)) 1))), 0,
      evenAlphaOne_cup_ne_zero_DM h (by
        rw [evenAlphaOneMCupForm_dualVector, Pi.single_eq_same]
        exact one_ne_zero)⟩
  have hgt : 1 < Nat.card (H2 (DM 1 h : Type) (ZMod 2)) :=
    Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  omega

/-! ## §8 `IsDemushkin` at `α = 1`, on both rows

The committed `isDemushkin_DN` / `isDemushkin_DM` (`Instances/EvenModelDemushkin.lean:309`, `:336`)
with §7 in place of `card_H2_*` and §6 in place of the `evenDualVector` nondegeneracy.  Every other
field (`smul_trivial`, `isProP`, `finiteH1`, and the `H¹` coordinate bijection) is `α`-free or
needs only `1 ≤ α`. -/

/-- **THE `α = 1` `N` CORE IS DEMUSHKIN**, for every handle count `h`.  This contradicts the
recorded residual `EvenDemResidualAlphaOneN`; see §9. -/
theorem evenAlphaOne_isDemushkin_DN (h : ℕ) : IsDemushkin 2 (DN 1 h : Type) :=
  { smul_trivial := fun _ _ => rfl
    isProP := isProP_DN 1 h
    finiteH1 := finite_H1_DN 1 h evenAlphaOne_one_le
    cardH2 := evenAlphaOne_card_H2_DN h
    nondegen_left := by
      intro x hx
      obtain ⟨v, rfl⟩ := (dnCoordinateHOne_bijective 1 h evenAlphaOne_one_le).surjective x
      have hv : v ≠ 0 := (dnCoordinateHOne_ne_zero_iff 1 h evenAlphaOne_one_le v).mp hx
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      refine ⟨dnCoordinateHOne 1 h evenAlphaOne_one_le (evenAlphaOneNDual (Pi.single i 1)), ?_⟩
      refine evenAlphaOne_cup_ne_zero_DN h ?_
      rw [evenAlphaOneNCupForm_dualVector]
      exact hi
    nondegen_right := by
      intro y hy
      obtain ⟨w, rfl⟩ := (dnCoordinateHOne_bijective 1 h evenAlphaOne_one_le).surjective y
      have hw : w ≠ 0 := (dnCoordinateHOne_ne_zero_iff 1 h evenAlphaOne_one_le w).mp hy
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
      refine ⟨dnCoordinateHOne 1 h evenAlphaOne_one_le (evenAlphaOneNDual (Pi.single i 1)), ?_⟩
      refine evenAlphaOne_cup_ne_zero_DN h ?_
      rw [evenAlphaOneNCupForm_dualVector_left]
      exact hi }

/-- **THE `α = 1` `M` CORE IS DEMUSHKIN**, for every handle count `h`.  This is the recorded
residual `EvenDemResidualAlphaOneM`, proved as recorded; see §9. -/
theorem evenAlphaOne_isDemushkin_DM (h : ℕ) : IsDemushkin 2 (DM 1 h : Type) :=
  { smul_trivial := fun _ _ => rfl
    isProP := isProP_DM 1 h
    finiteH1 := finite_H1_DM 1 h evenAlphaOne_one_le
    cardH2 := evenAlphaOne_card_H2_DM h
    nondegen_left := by
      intro x hx
      obtain ⟨v, rfl⟩ := (dmCoordinateHOne_bijective 1 h evenAlphaOne_one_le).surjective x
      have hv : v ≠ 0 := (dmCoordinateHOne_ne_zero_iff 1 h evenAlphaOne_one_le v).mp hx
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
      refine ⟨dmCoordinateHOne 1 h evenAlphaOne_one_le (evenAlphaOneMDual (Pi.single i 1)), ?_⟩
      refine evenAlphaOne_cup_ne_zero_DM h ?_
      rw [evenAlphaOneMCupForm_dualVector]
      exact hi
    nondegen_right := by
      intro y hy
      obtain ⟨w, rfl⟩ := (dmCoordinateHOne_bijective 1 h evenAlphaOne_one_le).surjective y
      have hw : w ≠ 0 := (dmCoordinateHOne_ne_zero_iff 1 h evenAlphaOne_one_le w).mp hy
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hw
      refine ⟨dmCoordinateHOne 1 h evenAlphaOne_one_le (evenAlphaOneMDual (Pi.single i 1)), ?_⟩
      refine evenAlphaOne_cup_ne_zero_DM h ?_
      rw [evenAlphaOneMCupForm_dualVector_left]
      exact hi }

/-- The `α = 1` `N` model obligation of the even forward route, in the shape the assembly
consumes.  The rank half is the committed `demushkinRank_DN` at `1 ≤ α`, which was never in
doubt. -/
theorem evenAlphaOne_nModelDemushkin (h : ℕ) : EvenForward.NModelDemushkin 1 h :=
  ⟨evenAlphaOne_isDemushkin_DN h, demushkinRank_DN 1 h evenAlphaOne_one_le⟩

/-- The `α = 1` `M` model obligation. -/
theorem evenAlphaOne_mModelDemushkin (h : ℕ) : EvenForward.MModelDemushkin 1 h :=
  ⟨evenAlphaOne_isDemushkin_DM h, demushkinRank_DM 1 h evenAlphaOne_one_le⟩

/-! ## §9 The verdict on the two recorded residuals -/

/-- **The recorded residual R1 is FALSE.**  `EvenDemResidualAlphaOneN` asserts that the `α = 1`
`N` core is not Demushkin at any handle count; §8 proves it is Demushkin at every handle count, so
the `Prop` fails already at `h = 0`.  It should be deleted, not proved. -/
theorem evenAlphaOne_residualN_false : ¬ EvenDemushkin.EvenDemResidualAlphaOneN :=
  fun hres => hres 0 (evenAlphaOne_isDemushkin_DN 0)

/-- **The recorded residual R2 is TRUE**, and is exactly §8's `M` row. -/
theorem evenAlphaOne_residualM : EvenDemushkin.EvenDemResidualAlphaOneM :=
  evenAlphaOne_isDemushkin_DM

/-! ## §10 What the `α ≥ 2` hypothesis means now

Three separate things were being carried by one hypothesis, and only the third survives as a
statement about the cores.

1. **The Frattini threshold `1 ≤ α`** is genuine and untouched: at `α = 0` the `N` head exponent
   `2 + 2 ^ 0 = 3` is odd, the relator leaves the Frattini subgroup, and the marked-relator bundle
   that every `H¹` statement runs on does not exist
   (`EvenDemushkin.evenDem_nHeadExponent_even_iff`).  Nothing here touches `α = 0`; the third
   recorded residual `EvenDemResidualAlphaZeroNRank` stands unchanged.
2. **The Gram threshold `2 ≤ α` is a threshold for one *matrix*, not for Demushkin-ness.**  It is
   exactly the range on which the two rows share the single form `evenCupForm`.  At `α = 1` there
   are two forms instead of one, both nondegenerate, and both rows are Demushkin.  So `2 ≤ α` in
   the committed `isDemushkin_DN` / `isDemushkin_DM` is a **convenience of uniformity**: it buys
   one proof for two rows, and §8 pays for the `α = 1` rows separately.
3. **What `α = 1` really costs is the frame layer, not the Demushkin layer.**  `NFrame 1 h` is
   empty and `Nonempty (NFrame α h) ↔ 2 ≤ α` is a committed theorem
   (`EvenDemushkin.evenDem_nFrame_nonempty_iff`).  Read against §8 this is now a statement about
   `q` rather than about Demushkin-ness: the `N` frame layer represents the torsion `ℤ/2`, the
   `α = 1` `N` core is a Demushkin group whose cup form is alternating, and an alternating form is
   the mod-`2` signature of `q ≢ 2`.  The frame is empty because the invariant it would record is
   not `2`, not because there is no invariant.

Section §3's alternating theorem is the sharp form of point 3, and is the only part of it this
file proves.  The identification of the invariant as `q = 4` is **not** proved here: `demushkinQ`
is a torsion count on the abelianization, and computing it at `α = 1` is a separate step that this
file does not take.  What is proved is that the Demushkin property holds, which is what the two
residuals were about.

The `α ≥ 2` hypothesis on the even *classification* is therefore not forced by a failure at
`α = 1` on either row.  Whether the classification extends to `α = 1` is a question about the
frame and stage layers above the model, and stays open. -/

/-! ## §11 The third stratum's surviving point

Wave 69 (`Instances/EvenUnramified.lean`) showed the presented cores meet the third stratum of the
range identity, the principal-unit images `evenRangePrin α`, in exactly one point:
`imChiN 0 = imChiN 1 = evenRangePrin 2`, with `ℚ₂(i)` the model field.  That point sits at branch
depth `a = 1` on the `N` row, which is exactly the core this file computes.

The connection is the following, and it is worth stating precisely because it is easy to overstate.
The surviving point is a point of the *range* stratification, and the core sitting over it is
`DN 1 h`.  Before this file, that core's Demushkin-ness was unasserted in both directions, so the
one surviving point had no candidate answer that was known to be a Demushkin group at all.  It now
does: §8.  That removes the obstruction; it does **not** by itself prove the classification there,
which needs the frame and stage inputs that §10.3 says are missing at `α = 1`. -/

/-- **The third stratum's surviving point carries a Demushkin core.**  The wave-69 point
`imChiN 1 = evenRangePrin 2` is the branch depth `α = 1` of the `N` row, and the core there is
Demushkin at every handle count.  Stated as the conjunction so that the two halves are read
together and neither is quoted alone. -/
theorem evenAlphaOne_survivingPoint_isDemushkin :
    imChiN 1 = EvenCyclotomicRange.evenRangePrin 2 ∧
      ∀ h : ℕ, IsDemushkin 2 (DN 1 h : Type) :=
  ⟨EvenUnram.evenUnram_imChiN_one_eq_prin_two, evenAlphaOne_isDemushkin_DN⟩

/-! ## §12 Axiom pins

Every declaration is expected std-3 (`propext`, `Classical.choice`, `Quot.sound`), matching the
`2 ≤ α` analogues they replace.  The pins are listed beside those analogues in the report: §6
against `card_H2_DN` / `card_H2_DM`, §8 against `isDemushkin_DN` / `isDemushkin_DM`. -/

#print axioms evenAlphaOne_diagCoeff_nHead
#print axioms evenAlphaOne_diagCoeff_mSecond
#print axioms evenAlphaOne_nRelWord_fib
#print axioms evenAlphaOne_mRelWord_fib
#print axioms evenAlphaOneNCupForm_self
#print axioms evenAlphaOneMCupForm_self
#print axioms evenAlphaOne_obsH2_DN
#print axioms evenAlphaOne_obsH2_DM
#print axioms evenAlphaOneNCupForm_dualVector
#print axioms evenAlphaOneMCupForm_dualVector
#print axioms evenAlphaOne_card_H2_DN
#print axioms evenAlphaOne_card_H2_DM
#print axioms evenAlphaOne_isDemushkin_DN
#print axioms evenAlphaOne_isDemushkin_DM
#print axioms evenAlphaOne_nModelDemushkin
#print axioms evenAlphaOne_mModelDemushkin
#print axioms evenAlphaOne_residualN_false
#print axioms evenAlphaOne_residualM
#print axioms evenAlphaOne_survivingPoint_isDemushkin

end

end GQ2.Dyadic.EvenAlphaOne
