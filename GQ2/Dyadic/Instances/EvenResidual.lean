/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.EvenAlphaTwo
import GQ2.Dyadic.Instances.EvenSlotZero
import GQ2.Dyadic.Instances.StageAbstractionEvenClimbFinal

/-!
# W57-RESIDUAL: `EvenClimbResidualSupply` is exactly the raw defect supply, so `Hfam` closes it

## Headline

**The even route's residual supply is PROVED, at every branch depth `α ≥ 2`, on both branches,
modulo `Hfam` alone.**  Precisely, on either even branch and at every `α ≥ 2`,

```
  EvenClimbResidualSupply (α-1)  ↔  EvenKernelRawDefectSupply
```

(`evenResidual_residualSupply_iff_rawDefect_{N,M}`), the right-hand side being exactly what the
derivation family produces (`evenKernel_rawDefectSupply_of_family`).  So the wave-51 chain's
last two named inputs collapse to one: `Hup` is not merely refuted, it is *unnecessary*, and
`Hfam` alone delivers the supply (`evenResidual_residualSupplyN`, `…M`).

## Why the wave-56 refutation cannot reach here, quantitatively

Wave 56 refuted `Hup`, the *span equality* `evenRawShiftSpan = evenBracketSpan`, at every `α`.
That refutation is exactly one bit wide, and this file identifies the bit.

Let `χ̄` be the depth-`(α-1)` character shadow `Q_{k+1} →* (ℤ/2^(k+α))ˣ`
(`evenSharpDeepChiLevel`, well defined by `evenSharpDeepDefined`).  Then:

* **§2** every bracket of the literal shift word dies under `χ̄`, because the target is
  commutative, so only the diagonal square survives:

  `χ̄ (evenRawDbarWord base c) = χ̄ (c 0) ^ 2`   (`evenResidual_shadow_dbarWord`).

  This *is* wave 56's `evenSlotZero_digit`, read off in one line: a correction with trivial
  shift word has `χ̄ (c 0) ^ 2 = 1`, which on `λ_{k-1}` forces the coordinate-`0` class deep.
  So `χ̄` is precisely the functional that separates the raw span from the bracket span.

* **§3** the stage defect is *always* on the trivial side of that functional:

  `χ̄ (stageDefect W G k T.generators) = 1`   (`evenResidual_shadow_defect_{n,m}`),

  for one reason and one only: **every exponent sum of an even relator is even**
  (`2` and `2^α` for `M_α`, `2 + 2^α` for `N_α`), the coordinates carrying them have table
  value `1`, and `Z_k` has exponent two, so the canonical lifts' ambiguity squares away.  This
  needs neither the depth bound nor the range identity.

* **§4** on the trivial side the two spans agree.  A raw shift whose shadow is trivial has
  deep coordinate `0`; the *off-zero* flips, which wave 55 proved outright
  (`evenFlip_flipOffZero_{M,N}`), make every other coordinate deep too; and the sharp central
  class of `evenDigit_sharp_zLayer_{M,N}` turns "deep" into "neutral" at no cost.  The one
  flip that is false, the one at coordinate `0`, is never invoked, because the shadow already
  did its work.

* **§5** finally, every depth-`(α-1)` *admissible* correction has all coordinates deep
  automatically, by the tuple's own exact rows: its coordinate `i` is a neutral coordinate
  times a central class (`evenResidual_admissible_mul_zLayer_neutral`).  So the residual
  `(shift of Wc)⁻¹ · (defect)⁻¹` lies in the bracket span exactly when the inverse defect
  does, with no dependence on the choice of `Wc` at all.

The one-digit margin that killed the flip is therefore real, and the defect never spends it.

## Proved versus measured versus refuted

* **PROVED** (§5, §6): the equivalence above and, from it, `Hfam ⟹ EvenClimbResidualSupply`
  on both branches at every `α ≥ 2`, and the `α = 2` endpoints carrying `Hfam` alone.
* **PROVED** (§2, §3): the two structural identities, both unconditional.
* **MEASURED** (certificates below): that the gap `evenRawShiftSpan / evenBracketSpan` really
  is one bit and really is cut out by `χ̄`, and that honestly sampled stage defects sit in the
  bracket span.  None of this is used by the Lean proofs; it is a check of them.
* **REFUTED**: nothing new.  Wave 56's refutation of `Hup` stands and is *reproved* here as a
  corollary of §2 (`evenResidual_slotZero_deep`).

## Certificates

`scripts/w57_residual/residual_model.g` rebuilds the wave-56 model - the honest even relator
group of rank `4 + 2h` with `MarkedCore.mWord`/`nWord` verbatim, its level-`k` two-quotient by
the `p`-quotient algorithm, and the cyclotomic character into `(ℤ/2^(k+α))ˣ` - and adds the
two functionals of this file: `Λ` (sharp at `k+α-2`) on `λ_{k-1}` and `Ω` (sharp at `k+α-1`)
on `Z_k`.  In all twelve cases run (both branches, `α ∈ {2,3,4,5}`, `k ∈ {3,4}`, `h ∈ {0,1}`)
it certifies `Ω(R_0(p)) = Λ(p)` and `Ω(R_i(p)) = 0` for `i ≠ 0`, hence
`χ(evenRawDbarWord c) = χ(c 0)²`; that `dim R - dim B = 1` and `B = R ∩ ker Ω` exactly; and
that the sharp central class exists.  It then samples honest stage tuples - generating markings
of `G/λ_k` killing the relator and satisfying the row condition, stratified by the depth at
which they perturb the standard marking, so the sample is not confined to deep perturbations -
and finds **1201 of 1201 with `Ω(defect) = 0`, all lying in `B`**.  As a by-product every
sampled defect also lies in `R`, which is evidence for `Hfam` but is not used.  Output in
`scripts/w57_residual/results/w57_residual_model.txt`.

## Numbering

1. two digit lemmas: sharp digits cancel, and the depth bound is representative-independent;
2. the character shadow of the literal shift word, and the wave-56 refutation as a corollary;
3. the shadow of the stage defect is trivial: the even relators have even exponent sums;
4. deep coordinates are neutral up to a central class; the off-zero repair; the span
   comparison on the trivial side of the shadow;
5. the headline: the residual supply is the raw defect supply, generically and per branch;
6. `Hfam` alone: the branch supplies and the `α = 2` endpoints;
7. axiom pins.
-/

namespace GQ2.Dyadic.EvenResidual

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 Two digit lemmas

Both are restatements of `private` lemmas of `StageAbstractionEvenDigit.lean`, which this file
cannot reach; the proofs are theirs. -/

section Digits

/-- **Two sharp digits at level `n` cancel to a trivial digit at `n + 1`.**  The digit group of
the modification space is elementary of order two.  (`evenDigit_deep_cancel`, restated: it is
`private` there.) -/
theorem evenResidual_deep_cancel {n : ℕ} (hn : 1 ≤ n) {u w : ℤ_[2]}
    (hu : (2 : ℤ_[2]) ^ n ∣ u - 1) (hu' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ u - 1)
    (hw : (2 : ℤ_[2]) ^ n ∣ w - 1) (hw' : ¬ (2 : ℤ_[2]) ^ (n + 1) ∣ w - 1) :
    (2 : ℤ_[2]) ^ (n + 1) ∣ u * w - 1 := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hw
  have ha2 : ¬ (2 : ℤ_[2]) ∣ a := by
    rintro ⟨e, rfl⟩
    exact hu' ⟨e, by rw [ha, pow_succ]; ring⟩
  have hb2 : ¬ (2 : ℤ_[2]) ∣ b := by
    rintro ⟨e, rfl⟩
    exact hw' ⟨e, by rw [hb, pow_succ]; ring⟩
  have hab : (2 : ℤ_[2]) ∣ a + b := by
    rw [show (2 : ℤ_[2]) = 2 ^ 1 by ring, two_pow_dvd_iff] at ha2 hb2 ⊢
    rw [map_add]
    revert ha2 hb2
    generalize PadicInt.toZModPow 1 a = x
    generalize PadicInt.toZModPow 1 b = y
    revert x y
    decide
  obtain ⟨e, he⟩ := hab
  refine ⟨e + 2 ^ (n - 1) * (a * b), ?_⟩
  have hu2 : u = 1 + 2 ^ n * a := by linear_combination ha
  have hw2 : w = 1 + 2 ^ n * b := by linear_combination hb
  have hpow : (2 : ℤ_[2]) ^ n * 2 ^ n = 2 ^ (n + 1) * 2 ^ (n - 1) := by
    rw [← pow_add, ← pow_add]
    congr 1
    omega
  rw [hu2, hw2]
  linear_combination (2 : ℤ_[2]) ^ n * he + (a * b) * hpow

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α k : ℕ}

/-- **Representative independence of the committed depth bound.**  Any ambient representative
of a depth-`k-1` class carries `k - 1 + (α - 1)` character digits.  (`evenDigit_rep_dvd`,
restated: it is `private` there.) -/
theorem evenResidual_rep_dvd (hα : 1 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    {q : levelQuot G (k + 1)} (hq : q ∈ lambdaImage G (k - 1) (k + 1))
    {g : G} (hg : q = levelMk G (k + 1) g) :
    (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  obtain ⟨u, hu, hurep⟩ := hq
  have hrel : u⁻¹ * g ∈ twoCentralSeries G (k + 1) :=
    QuotientGroup.eq.mp (hurep.trans hg)
  have hsplit : chi g = chi u * chi (u⁻¹ * g) := by
    rw [← map_mul]
    congr 1
    group
  have h1 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    evenSharp_mem_ker_iff.mp (evenSharp_map_le_deep hα hbound (k - 1) (by omega) ⟨u, hu, rfl⟩)
  have h2 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi (u⁻¹ * g) : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans (evenSharp_mem_ker_iff.mp
      (evenSharp_map_le_deep hα hbound (k + 1) (by omega) ⟨u⁻¹ * g, hrel, rfl⟩))
  rw [hsplit, Units.val_mul]
  exact dvd_mul_sub_one h1 h2

end Digits

/-! ## §2 The character shadow of the literal shift word

The whole file turns on one identity: the depth-`(α-1)` shadow of the even shift word sees
only the diagonal square.  Every other letter of `evenRawCoreDbarWord`, and every letter of
`evenRawHandleDbarWord`, is a commutator, and the shadow's target is commutative. -/

section Shadow

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α k h : ℕ}

/-- **The depth-`(α-1)` character shadow at level `k+1`**, `Q_{k+1} →* (ℤ/2^(k+α))ˣ`.  Its
well-definedness is exactly `evenSharpDeepDefined`, whose exponent count the even lane's own
depth bound makes an equality. -/
def evenResidualShadow (chi : ContinuousMonoidHom G ℤ_[2]ˣ) {α k : ℕ} (hα : 1 ≤ α)
    (hk : 1 ≤ k) (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) :
    levelQuot G (k + 1) →* (ZMod (2 ^ (k + 1 + (α - 1))))ˣ :=
  evenSharpDeepChiLevel chi (k + 1) (α - 1) (evenSharpDeepDefined hα hk hbound)

variable (hα : 1 ≤ α) (hk : 1 ≤ k) (hbound : ∀ g : G, EvenSharpPmOne α (chi g))

@[simp] theorem evenResidualShadow_levelMk (g : G) :
    evenResidualShadow chi hα hk hbound (levelMk G (k + 1) g) =
      Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom (chi g) := rfl

/-- The shadow of a central class squares away: `Z_k` has exponent two. -/
theorem evenResidualShadow_zLayer_sq {z : levelQuot G (k + 1)} (hz : z ∈ zLayer G k) :
    evenResidualShadow chi hα hk hbound z ^ 2 = 1 := by
  rw [← map_pow, zLayer_sq G hz, map_one]

/-- The shadow kills every bracket, the target being commutative. -/
theorem evenResidualShadow_commP (x y : levelQuot G (k + 1)) :
    evenResidualShadow chi hα hk hbound (commP x y) = 1 :=
  map_commP_eq_one _ x y

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The handle block is a product of brackets, so the shadow kills it. -/
theorem evenResidualShadow_handle
    (base c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenResidualShadow chi hα hk hbound (evenRawHandleDbarWord base c) = 1 := by
  rw [evenRawHandleDbarWord, map_list_prod]
  refine List.prod_eq_one ?_
  intro x hx
  obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hy
  rw [map_mul, evenResidualShadow_commP, evenResidualShadow_commP, one_mul]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The core block reduces to the diagonal square. -/
theorem evenResidualShadow_core
    (base c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenResidualShadow chi hα hk hbound (evenRawCoreDbarWord base c) =
      evenResidualShadow chi hα hk hbound (c 0) ^ 2 := by
  rw [evenRawCoreDbarWord]
  simp only [map_mul, map_pow, evenResidualShadow_commP, mul_one]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The identity the whole file turns on.**  The shadow of the literal even shift word is the
square of the shadow of its coordinate-`0` letter; every other letter is a bracket. -/
theorem evenResidual_shadow_dbarWord
    (base c : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1)) :
    evenResidualShadow chi hα hk hbound (evenRawDbarWord base c) =
      evenResidualShadow chi hα hk hbound (c 0) ^ 2 := by
  rw [evenRawDbarWord, map_mul, evenResidualShadow_core, evenResidualShadow_handle, mul_one]

end Shadow

/-! ## §3 The shadow of the stage defect is trivial

The reason is arithmetic and has nothing to do with the character's image: the two even
relators have exponent sums `2, 2^α` and `2 + 2^α`, all even, at coordinates whose table value
is `1`, and the canonical lifts' ambiguity lies in `Z_k`, of exponent two.  So the defect can
never be sharp at `k + α - 1`, which by §2 is exactly the digit separating the raw span from
the bracket span. -/

section Defect

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α k h : ℕ}
variable (hα : 1 ≤ α) (hk : 1 ≤ k) (hbound : ∀ g : G, EvenSharpPmOne α (chi g))

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The canonical lift's shadow, squared, is the table value squared.**  A stage tuple's row
provides an exact `chi`-fibre representative, and the canonical lift differs from it by a
central class, whose shadow squares to `1`. -/
theorem evenResidual_shadow_canonLift_sq {n : ℕ} {W : StageWord n} {v : Fin n → ℤ_[2]ˣ}
    (T : Tuple W v G chi k) (i : Fin n) :
    evenResidualShadow chi hα hk hbound (canonLift G k (T.generators i)) ^ 2 =
      Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom (v i) ^ 2 := by
  obtain ⟨x, hxchi, hx⟩ := T.rows i
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul (G := G) (k := k)
    (x := canonLift G k (T.generators i)) (y := levelMk G (k + 1) x)
    (by rw [levelProj_canonLift, levelProj_levelMk, hx])
  rw [hzeq, map_mul, mul_pow, evenResidualShadow_zLayer_sq hα hk hbound hz, one_mul,
    evenResidualShadow_levelMk, hxchi]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `N` defect has trivial shadow.**  `nRelWord` abelianises to `m 0 ^ (2 + 2^α)`, the
exponent is even, and `vN α 0 = 1`. -/
theorem evenResidual_shadow_defect_n (hα₁ : 1 ≤ α)
    (T : Tuple (nStageWord α h hα₁) (vN α) G chi k) :
    evenResidualShadow chi hα hk hbound
      (stageDefect (nStageWord α h hα₁) G k T.generators) = 1 := by
  have hdef : stageDefect (nStageWord α h hα₁) G k T.generators =
      MarkedCore.nRelWord α (fun i ↦ canonLift G k (T.generators i)) := rfl
  have hexp : 2 + 2 ^ α = 2 * (1 + 2 ^ (α - 1)) := by
    have : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by
      rw [← pow_succ']; congr 1; omega
    omega
  rw [hdef, map_nRelWord, nRelWord_comm, hexp, pow_mul,
    evenResidual_shadow_canonLift_sq hα hk hbound T 0, vN_zero]
  simp

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The `M` defect has trivial shadow.**  `mRelWord` abelianises to `m 0 ^ 2 * m 2 ^ (2^α)`,
both exponents are even, and `vM α 0 = vM α 2 = 1`. -/
theorem evenResidual_shadow_defect_m (hα₁ : 1 ≤ α)
    (T : Tuple (mStageWord α h hα₁) (vM α) G chi k) :
    evenResidualShadow chi hα hk hbound
      (stageDefect (mStageWord α h hα₁) G k T.generators) = 1 := by
  have hdef : stageDefect (mStageWord α h hα₁) G k T.generators =
      MarkedCore.mRelWord α (fun i ↦ canonLift G k (T.generators i)) := rfl
  have hexp : (2 : ℕ) ^ α = 2 * 2 ^ (α - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hdef, map_mRelWord, mRelWord_comm, hexp, pow_mul,
    evenResidual_shadow_canonLift_sq hα hk hbound T 0,
    evenResidual_shadow_canonLift_sq hα hk hbound T 2, vM_zero, vM_two]
  simp

end Defect

/-! ## §4 Deep coordinates, the off-zero repair, and the span comparison

`EvenResidualDeep` is the wave-55/56 predicate: a class with an ambient representative reaching
`k + (α - 1)` character digits, one digit short of the neutrality the bracket span demands.
The sharp central class of `evenDigit_sharp_zLayer_{M,N}` closes that last digit for free, so
"deep" and "neutral up to a central class" are the same thing (§4.1).  The off-zero flips of
wave 55 make every coordinate but `0` deep (§4.2), and §2 makes coordinate `0` deep whenever
the shadow is trivial - which §3 says it always is at a defect. -/

section Deep

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α k h : ℕ}

/-- **A deep class**: some ambient representative reaches `k + (α - 1)` character digits.  This
is the predicate the flips of `StageAbstractionEvenFlip.lean` and the refutation of
`EvenSlotZero.lean` are both stated against. -/
def EvenResidualDeep (chi : ContinuousMonoidHom G ℤ_[2]ˣ) (α k : ℕ)
    (q : levelQuot G (k + 1)) : Prop :=
  ∃ g : G, q = levelMk G (k + 1) g ∧
    (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1

/-- A neutral coordinate is deep. -/
theorem evenResidual_deep_of_neutral {q : levelQuot G (k + 1)}
    (hq : q ∈ evenBracketNeutralSubgroup (α - 1) G chi k) : EvenResidualDeep chi α k q := by
  obtain ⟨-, g, hg, hgchi⟩ := hq
  exact ⟨g, hg, (pow_dvd_pow (2 : ℤ_[2]) (by omega)).trans
    (evenSharp_mem_ker_iff.mp (MonoidHom.mem_ker.mpr hgchi))⟩

/-- The product of two deep classes is deep. -/
theorem evenResidual_deep_mul {q q' : levelQuot G (k + 1)}
    (hq : EvenResidualDeep chi α k q) (hq' : EvenResidualDeep chi α k q') :
    EvenResidualDeep chi α k (q * q') := by
  obtain ⟨g, hg, hgd⟩ := hq
  obtain ⟨g', hg', hg'd⟩ := hq'
  refine ⟨g * g', by rw [hg, hg', map_mul], ?_⟩
  rw [map_mul, Units.val_mul]
  exact dvd_mul_sub_one hgd hg'd

/-! ### §4.1 Deep is neutral, up to a central class -/

/-- **The sharp central class closes the last digit.**  A deep class of depth `k-1` becomes a
*neutral* coordinate after multiplication by a class of `Z_k`: either it is already neutral, or
the sharp central class of `evenDigit_sharp_zLayer_{M,N}` cancels its remaining digit. -/
theorem evenResidual_neutral_of_deep (hα : 2 ≤ α)
    (hz : ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    {q : levelQuot G (k + 1)} (hq : q ∈ lambdaImage G (k - 1) (k + 1))
    (hdeep : EvenResidualDeep chi α k q) :
    ∃ z ∈ zLayer G k, q * z ∈ evenBracketNeutralSubgroup (α - 1) G chi k := by
  obtain ⟨g, hg, hgd⟩ := hdeep
  by_cases hfull : (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [mul_one]
    exact ⟨hq, g, hg, MonoidHom.mem_ker.mp (evenSharp_mem_ker_iff.mpr hfull)⟩
  · obtain ⟨w₀, hw₀mem, hw₀dvd, hw₀sharp⟩ := hz
    have hz₀ : levelMk G (k + 1) w₀ ∈ zLayer G k := ⟨w₀, hw₀mem, rfl⟩
    refine ⟨levelMk G (k + 1) w₀, hz₀, ?_, g * w₀, by rw [hg, map_mul], ?_⟩
    · exact Subgroup.mul_mem _ hq (lambdaImage_le_of_le (by omega) hz₀)
    · refine MonoidHom.mem_ker.mp (evenSharp_mem_ker_iff.mpr ?_)
      rw [map_mul, Units.val_mul]
      have hEq : k + 1 + (α - 1) = k + (α - 1) + 1 := by omega
      rw [hEq] at hfull hw₀sharp ⊢
      exact evenResidual_deep_cancel (by omega) hgd hfull hw₀dvd hw₀sharp

variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

/-- **A correction all of whose coordinates are deep has a neutral correction with the same
literal shift word.**  The correcting central factors move no letter of the word at all
(`evenDigit_dbarWord_eq_one_of_zLayer`). -/
theorem evenResidual_exists_neutral_of_forall_deep (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hz : ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (V : EvenRawDepthCorrection G h k)
    (hV : ∀ j, EvenResidualDeep chi α k (V.correction j)) :
    ∃ N : EvenSharpNeutralCorrection (α - 1) G chi h k,
      evenRawDbarWord base N.correction = evenRawDbarWord base V.correction := by
  classical
  choose z hz₀ hn using fun j ↦
    evenResidual_neutral_of_deep hα hz (V.depth j) (hV j)
  have hzd : ∀ j, z j ∈ lambdaImage G (k - 1) (k + 1) := fun j ↦
    lambdaImage_le_of_le (by omega) (hz₀ j)
  refine ⟨{ correction := fun j ↦ V.correction j * z j
            depth := fun j ↦ (hn j).1
            neutral := fun j ↦ (hn j).2 }, ?_⟩
  show evenRawDbarWord base (fun j ↦ V.correction j * z j) = _
  rw [evenRawDbarWord_mul h k hk base V.depth hzd,
    evenDigit_dbarWord_eq_one_of_zLayer base z hz₀, mul_one]

/-! ### §4.2 The off-zero repair

The clone of the `private` first repair pass of `StageAbstractionEvenDigit.lean` §4, with the
flip at coordinate `0` deleted from the hypotheses and the deepness of coordinate `0` carried
through the induction instead.  That deletion is the point: the coordinate-`0` flip is exactly
what wave 56 refuted, and nothing here asks for it. -/

/-- **The off-zero repair pass.**  Given the flips away from `0` and a correction whose
coordinate `0` is already deep, every coordinate in a finite set can be made deep without
moving the literal shift word - and coordinate `0` stays deep, because a flip at `i₀ ≠ 0`
multiplies coordinate `0` by a deep class. -/
theorem evenResidual_midRepair (hα : 2 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hFl : ∀ i₀ : Fin (MarkedCore.coreRank h), i₀ ≠ 0 →
      ∃ F : EvenRawDepthCorrection G h k,
        evenRawDbarWord base F.correction = 1 ∧
        (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
          ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
        (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
          EvenResidualDeep chi α k (F.correction j)))
    (V : EvenRawDepthCorrection G h k) (hV0 : EvenResidualDeep chi α k (V.correction 0))
    (S : Finset (Fin (MarkedCore.coreRank h))) :
    ∃ C : EvenRawDepthCorrection G h k,
      evenRawDbarWord base C.correction = evenRawDbarWord base V.correction ∧
      EvenResidualDeep chi α k (C.correction 0) ∧
      ∀ j ∈ S, EvenResidualDeep chi α k (C.correction j) := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨V, rfl, hV0, fun j hj ↦ absurd hj (by simp)⟩
  | @insert i₀ S hi₀S ih =>
    obtain ⟨C, hCword, hC0, hCS⟩ := ih
    by_cases hδ : EvenResidualDeep chi α k (C.correction i₀)
    · refine ⟨C, hCword, hC0, fun j hj ↦ ?_⟩
      rcases Finset.mem_insert.mp hj with rfl | hjS
      · exact hδ
      · exact hCS j hjS
    · have hi₀ : i₀ ≠ 0 := by rintro rfl; exact hδ hC0
      obtain ⟨F, hFword, ⟨gd, hgd, hgdsharp⟩, hFoff⟩ := hFl i₀ hi₀
      have hCF : (C * F).correction = fun i ↦ C.correction i * F.correction i := rfl
      refine ⟨C * F, ?_, ?_, ?_⟩
      · rw [hCF, evenRawDbarWord_mul h k hk base C.depth F.depth, hFword, mul_one, hCword]
      · exact evenResidual_deep_mul hC0 (hFoff 0 (Ne.symm hi₀))
      · intro j hj
        rcases Finset.mem_insert.mp hj with rfl | hjS
        · obtain ⟨u, hu, hurep⟩ := C.depth j
          have husharp :
              ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            fun hdvd ↦ hδ ⟨u, hurep.symm, hdvd⟩
          have hubase :
              (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi u : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            evenResidual_rep_dvd (by omega) hbound hk (C.depth j) hurep.symm
          have hgdbase :
              (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi gd : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
            evenResidual_rep_dvd (by omega) hbound hk (F.depth j) hgd
          refine ⟨u * gd, ?_, ?_⟩
          · rw [hCF]
            show C.correction j * F.correction j = _
            rw [map_mul, hgd, ← hurep]
          · rw [map_mul, Units.val_mul]
            have hEq : k + (α - 1) = k - 1 + (α - 1) + 1 := by omega
            rw [hEq] at husharp hgdsharp ⊢
            exact evenResidual_deep_cancel (by omega) hubase husharp hgdbase hgdsharp
        · exact evenResidual_deep_mul (hCS j hjS) (hFoff j (fun hEq ↦ hi₀S (hEq ▸ hjS)))

/-- **The repair, assembled.**  A raw depth correction whose coordinate `0` is deep has a
*neutral* correction with the same literal shift word - and hence its shift lies in the bracket
span.  Only the off-zero flips are consumed. -/
theorem evenResidual_mem_bracketSpan_of_deep_zero (hα : 2 ≤ α)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g)) (hk : 3 ≤ k)
    (hz : ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hFl : ∀ i₀ : Fin (MarkedCore.coreRank h), i₀ ≠ 0 →
      ∃ F : EvenRawDepthCorrection G h k,
        evenRawDbarWord base F.correction = 1 ∧
        (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
          ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
        (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
          EvenResidualDeep chi α k (F.correction j)))
    (V : EvenRawDepthCorrection G h k) (hV0 : EvenResidualDeep chi α k (V.correction 0)) :
    evenRawDbarWord base V.correction ∈ evenBracketSpan (α - 1) chi base := by
  classical
  obtain ⟨C, hCword, hC0, hCall⟩ :=
    evenResidual_midRepair hα hbound hk base hFl V hV0 Finset.univ
  obtain ⟨N, hN⟩ := evenResidual_exists_neutral_of_forall_deep hα hk hz base C
    (fun j ↦ hCall j (Finset.mem_univ j))
  rw [← hCword, ← hN, ← evenSharpNeutralShiftHom_apply (s := α - 1) base hk N,
    ← evenSharpNeutralShiftHom_range_eq_bracketSpan (s := α - 1) (chi := chi) base hk]
  exact ⟨_, ⟨N, rfl⟩, rfl⟩

/-! ### §4.3 Coordinate `0` from the shadow

This is §2 read backwards, and it *is* the wave-56 refutation: a raw shift with trivial shadow
has deep coordinate `0`.  Taking the shift to be `1` recovers `evenSlotZero_digit`. -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **Trivial shadow forces a deep coordinate `0`.**  The coordinate has depth `k-1`, so its
character level is at least `k + α - 2`; §2 turns the trivial shadow of the shift word into
`χ(g)² ≡ 1 (mod 2^(k+α))`; and the two-adic step of `EvenSlotZero.lean` §1 gains the last
digit. -/
theorem evenResidual_deep_zero_of_shadow (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g))
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (V : EvenRawDepthCorrection G h k)
    (hsh : evenResidualShadow chi (by omega : 1 ≤ α) (by omega : 1 ≤ k) hbound
      (evenRawDbarWord base V.correction) = 1) :
    EvenResidualDeep chi α k (V.correction 0) := by
  obtain ⟨g, hg⟩ := levelMk_surjective G (k + 1) (V.correction 0)
  refine ⟨g, hg.symm, ?_⟩
  have h1 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 :=
    evenResidual_rep_dvd (by omega) hbound hk (V.depth 0) hg.symm
  have hsq : Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom (chi g) ^ 2 = 1 := by
    rw [evenResidual_shadow_dbarWord (by omega) (by omega) hbound base V.correction, ← hg,
      evenResidualShadow_levelMk] at hsh
    exact hsh
  have h2 : (2 : ℤ_[2]) ^ (k - 1 + (α - 1) + 2) ∣
      ((chi g : ℤ_[2]ˣ) : ℤ_[2]) * ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
    have hker : chi g ^ 2 ∈ (Units.map (PadicInt.toZModPow (k + 1 + (α - 1))).toMonoidHom).ker :=
      MonoidHom.mem_ker.mpr (by rw [map_pow]; exact hsq)
    have := evenSharp_mem_ker_iff.mp hker
    rw [Units.val_pow_eq_pow_val, sq] at this
    rwa [show k - 1 + (α - 1) + 2 = k + 1 + (α - 1) by omega]
  have hstep := evenSlotZero_step (j := k - 1 + (α - 1)) (by omega) h1 h2
  rwa [show k - 1 + (α - 1) + 1 = k + (α - 1) by omega] at hstep

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **Wave 56's refutation, recovered.**  A correction with literally trivial shift word has a
deep coordinate `0`: this is `evenSlotZero_digit`, obtained here as the case `shift = 1` of the
shadow identity. -/
theorem evenResidual_slotZero_deep (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g))
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (V : EvenRawDepthCorrection G h k) (hV : evenRawDbarWord base V.correction = 1) :
    EvenResidualDeep chi α k (V.correction 0) :=
  evenResidual_deep_zero_of_shadow hα hk hbound base V (by rw [hV, map_one])

/-- **The span comparison on the trivial side of the shadow.**  A raw shift with trivial shadow
lies in the bracket span.  This is the exact residue of `Hup` that survives wave 56: the two
spans agree on `ker` of the shadow, and differ only off it. -/
theorem evenResidual_mem_bracketSpan_of_shadow (hα : 2 ≤ α) (hk : 3 ≤ k)
    (hbound : ∀ g : G, EvenSharpPmOne α (chi g))
    (hz : ∃ w ∈ twoCentralSeries G k,
      (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1 ∧
        ¬ (2 : ℤ_[2]) ^ (k + 1 + (α - 1)) ∣ ((chi w : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    (base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1))
    (hFl : ∀ i₀ : Fin (MarkedCore.coreRank h), i₀ ≠ 0 →
      ∃ F : EvenRawDepthCorrection G h k,
        evenRawDbarWord base F.correction = 1 ∧
        (∃ g : G, F.correction i₀ = levelMk G (k + 1) g ∧
          ¬ (2 : ℤ_[2]) ^ (k + (α - 1)) ∣ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) - 1) ∧
        (∀ j : Fin (MarkedCore.coreRank h), j ≠ i₀ →
          EvenResidualDeep chi α k (F.correction j)))
    {z : levelQuot G (k + 1)} (hzmem : z ∈ evenRawShiftSpan base hk)
    (hsh : evenResidualShadow chi (by omega : 1 ≤ α) (by omega : 1 ≤ k) hbound z = 1) :
    z ∈ evenBracketSpan (α - 1) chi base := by
  obtain ⟨-, ⟨V, rfl⟩, rfl⟩ := hzmem
  exact evenResidual_mem_bracketSpan_of_deep_zero hα hbound hk hz base hFl V
    (evenResidual_deep_zero_of_shadow hα hk hbound base V hsh)

end Deep

/-! ## §5 The headline: the residual supply is the raw defect supply

Two halves.  §5.1: every depth-`(α-1)` admissible correction has all coordinates deep, indeed
neutral up to a central class, *by the tuple's own exact rows* - no character bound, no flip,
no sharp class.  So its literal shift lies in the bracket span, and the residual differs from
the inverse defect by an element of that span, which is why the choice of correction is
immaterial.  §5.2: the equivalence. -/

section Headline

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {α k h : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-! ### §5.1 Admissible corrections are neutral up to the central layer -/

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **Every coordinate of a depth-`s` admissible correction is a neutral coordinate times a
central class.**  The row condition says the modified row matches the table value to
`k + 1 + s` digits, and the tuple's own row provides an *exact* fibre representative; the
canonical lift differs from it by a class of `Z_k`, and that class is the correcting factor. -/
theorem evenResidual_admissible_mul_zLayer_neutral {s : ℕ} {T : Tuple W v G chi k}
    (Wc : DeepSharpAdmissibleCorrection s T) (i : Fin (MarkedCore.coreRank h)) :
    ∃ z ∈ zLayer G k,
      Wc.correction i * z ∈ evenBracketNeutralSubgroup s G chi k := by
  obtain ⟨x, hxchi, hx⟩ := T.rows i
  obtain ⟨g', hmod, hcong⟩ := Wc.rows i
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul (G := G) (k := k)
    (x := canonLift G k (T.generators i)) (y := levelMk G (k + 1) x)
    (by rw [levelProj_canonLift, levelProj_levelMk, hx])
  refine ⟨z, hz, Subgroup.mul_mem _ (Wc.depth i) (lambdaImage_le_of_le (by omega) hz),
    x⁻¹ * g', ?_, ?_⟩
  · have hcomm : z * levelMk G (k + 1) x * Wc.correction i =
        levelMk G (k + 1) x * (Wc.correction i * z) := by
      rw [mul_assoc, (zLayer_commute hz (levelMk G (k + 1) x * Wc.correction i)).eq, mul_assoc]
    simp only [stageModified] at hmod
    rw [hzeq, hcomm] at hmod
    rw [map_mul, map_inv, ← hmod]
    group
  · rw [map_mul, map_inv, hxchi, map_mul, map_inv, hcong, inv_mul_cancel]

/-- **The literal shift of an admissible correction lies in the bracket span.**  Unconditional:
the only inputs are the tuple's exact rows and the fact that central classes move no letter of
the shift word. -/
theorem evenResidual_admissible_shift_mem_bracketSpan {s : ℕ} (hk : 3 ≤ k)
    {T : Tuple W v G chi k} (Wc : DeepSharpAdmissibleCorrection s T) :
    evenRawDbarWord (fun i ↦ canonLift G k (T.generators i)) Wc.correction ∈
      evenBracketSpan s chi (fun i ↦ canonLift G k (T.generators i)) := by
  classical
  choose z hz hn using fun i ↦ evenResidual_admissible_mul_zLayer_neutral Wc i
  have hzd : ∀ j, z j ∈ lambdaImage G (k - 1) (k + 1) := fun j ↦
    lambdaImage_le_of_le (by omega) (hz j)
  set base : Fin (MarkedCore.coreRank h) → levelQuot G (k + 1) :=
    fun i ↦ canonLift G k (T.generators i) with hbase
  set N : EvenSharpNeutralCorrection s G chi h k :=
    { correction := fun j ↦ Wc.correction j * z j
      depth := fun j ↦ (hn j).1
      neutral := fun j ↦ (hn j).2 } with hNdef
  have hword : evenRawDbarWord base N.correction = evenRawDbarWord base Wc.correction := by
    show evenRawDbarWord base (fun j ↦ Wc.correction j * z j) = _
    rw [evenRawDbarWord_mul h k hk base Wc.depth hzd,
      evenDigit_dbarWord_eq_one_of_zLayer base z hz, mul_one]
  rw [← hword, ← evenSharpNeutralShiftHom_apply (s := s) base hk N,
    ← evenSharpNeutralShiftHom_range_eq_bracketSpan (s := s) (chi := chi) base hk]
  exact ⟨_, ⟨N, rfl⟩, rfl⟩

/-! ### §5.2 The equivalence, generically -/

/-- **The residual is reachable exactly when the inverse defect lies in the bracket span.**  The
choice of admissible correction is immaterial, by §5.1. -/
theorem evenResidual_reachable_iff_defect_mem {s : ℕ} (hk : 3 ≤ k) {T : Tuple W v G chi k}
    (Wc : DeepSharpAdmissibleCorrection s T) :
    EvenSharpNeutralResidualReachable Wc ↔
      (stageDefect W G k T.generators)⁻¹ ∈
        evenBracketSpan s chi (fun i ↦ canonLift G k (T.generators i)) := by
  rw [evenSharpNeutralResidualReachable_iff_mem_bracketSpan hk Wc,
    evenSharpNeutralResidualElement]
  have hWc := evenResidual_admissible_shift_mem_bracketSpan hk Wc
  constructor
  · intro hmem
    have := Subgroup.mul_mem _ hWc hmem
    rwa [mul_inv_cancel_left] at this
  · intro hmem
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hWc) hmem

/-- **The residual supply implies the raw defect supply**, on any word datum: the bracket span
sits inside the raw span. -/
theorem evenResidual_rawDefectSupply_of_residualSupply {s : ℕ}
    (H : EvenClimbResidualSupply s W v G chi) : EvenKernelRawDefectSupply W v G chi := by
  intro k hk T
  obtain ⟨Wc⟩ := evenSharpDeepAdmissible_nonempty s T
  have hmem := (evenResidual_reachable_iff_defect_mem hk Wc).mp (H k hk T Wc)
  exact evenRawTo_bracketSpan_le_rawShiftSpan _ hk hmem

/-! ### §5.3 The equivalence on the two even branches

Every input of §4 is discharged from the range identity: the `±1` bound is
`evenSlotZero_bound_{M,N}`, the sharp central class is `evenDigit_sharp_zLayer_{M,N}`, and the
off-zero flips are wave 55's `evenFlip_flipOffZero_{M,N}`, which are unconditional theorems.
So on either branch the residual supply carries **nothing** beyond the raw defect supply. -/

variable {α : ℕ}

/-- **`N` branch: the raw defect supply gives the residual supply.** -/
theorem evenResidual_residualSupply_of_rawDefect_N (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α)
    (Hraw : EvenKernelRawDefectSupply (nStageWord α h hα₁) (vN α) G chi) :
    EvenClimbResidualSupply (α - 1) (nStageWord α h hα₁) (vN α) G chi := by
  intro k hk T Wc
  have hbound := evenSlotZero_bound_N hα hrange
  rw [evenResidual_reachable_iff_defect_mem hk Wc]
  refine evenResidual_mem_bracketSpan_of_shadow hα hk hbound
    (evenDigit_sharp_zLayer_N hα hrange hk) _
    (fun i₀ hi₀ ↦ evenFlip_flipOffZero_N hα hk T i₀ hi₀) (Hraw k hk T) ?_
  rw [map_inv, evenResidual_shadow_defect_n (by omega) (by omega) hbound hα₁ T, inv_one]

/-- **`M` branch: the raw defect supply gives the residual supply.** -/
theorem evenResidual_residualSupply_of_rawDefect_M (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α)
    (Hraw : EvenKernelRawDefectSupply (mStageWord α h hα₁) (vM α) G chi) :
    EvenClimbResidualSupply (α - 1) (mStageWord α h hα₁) (vM α) G chi := by
  intro k hk T Wc
  have hbound := evenSlotZero_bound_M hα hrange
  rw [evenResidual_reachable_iff_defect_mem hk Wc]
  refine evenResidual_mem_bracketSpan_of_shadow hα hk hbound
    (evenDigit_sharp_zLayer_M hα hrange hk) _
    (fun i₀ hi₀ ↦ evenFlip_flipOffZero_M hα hk T i₀ hi₀) (Hraw k hk T) ?_
  rw [map_inv, evenResidual_shadow_defect_m (by omega) (by omega) hbound hα₁ T, inv_one]

/-- **The headline on the `N` branch**: the residual supply *is* the raw defect supply. -/
theorem evenResidual_residualSupply_iff_rawDefect_N (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiN α) :
    EvenClimbResidualSupply (α - 1) (nStageWord α h hα₁) (vN α) G chi ↔
      EvenKernelRawDefectSupply (nStageWord α h hα₁) (vN α) G chi :=
  ⟨evenResidual_rawDefectSupply_of_residualSupply,
    evenResidual_residualSupply_of_rawDefect_N hα hα₁ hrange⟩

/-- **The headline on the `M` branch.** -/
theorem evenResidual_residualSupply_iff_rawDefect_M (hα : 2 ≤ α) (hα₁ : 1 ≤ α)
    (hrange : MonoidHom.range chi.toMonoidHom = imChiM α) :
    EvenClimbResidualSupply (α - 1) (mStageWord α h hα₁) (vM α) G chi ↔
      EvenKernelRawDefectSupply (mStageWord α h hα₁) (vM α) G chi :=
  ⟨evenResidual_rawDefectSupply_of_residualSupply,
    evenResidual_residualSupply_of_rawDefect_M hα hα₁ hrange⟩

end Headline

/-! ## §6 `Hfam` alone

`StageAbstractionEvenClimbFinal.lean` §1 already discharges the derivation criterion, so the
family is the only input its residual supply carried besides `Hup`.  Dropping `Hup` and keeping
the range identity - which those statements' consumers hold anyway - gives the even route's
supply from `Hfam` alone.  §6.2 restates the two `α = 2` endpoints in that form; they are the
wave-56 re-cut endpoints with their single remaining hypothesis discharged. -/

section Family

open ContCoh
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.EvenPerK
open GQ2.Dyadic.EvenAlphaTwo

/-- The coefficient action at `G_K(2)`, as everywhere on this route. -/
local instance evenResidualScalar {K : IntermediateField ℚ_[2] ℚ̄₂} [CompactSpace (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

/-- Continuity of that action. -/
local instance evenResidualContinuousScalar {K : IntermediateField ℚ_[2] ℚ̄₂}
    [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
variable [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-! ### §6.1 The branch supplies -/

/-- **The `N` branch residual supply from `Hfam` alone.**  This is
`evenClimbFinal_residualSupplyN` with `Hup` deleted; the range identity, which that statement's
consumers already carry, replaces it. -/
theorem evenResidual_residualSupplyN {α h : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN α)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenClimbResidualSupply (α - 1) (nStageWord α h (Nat.le_of_succ_le hα)) (vN α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) := by
  refine evenResidual_residualSupply_of_rawDefect_N hα _ hrange
    (evenKernel_rawDefectSupply_of_family ?_)
  intro k hk T
  obtain ⟨F, Hrel⟩ := Hfam k hk T
  exact ⟨F, evenDeriv_derivKerCriterion (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient hk F evenKernel_vN_sub_one_dvd_four
    (evenKernel_vN_diagonal_add_one_dvd_four hα), Hrel⟩

/-- **The `M` branch residual supply from `Hfam` alone.** -/
theorem evenResidual_residualSupplyM {α h : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    EvenClimbResidualSupply (α - 1) (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) := by
  refine evenResidual_residualSupply_of_rawDefect_M hα _ hrange
    (evenKernel_rawDefectSupply_of_family ?_)
  intro k hk T
  obtain ⟨F, Hrel⟩ := Hfam k hk T
  exact ⟨F, evenDeriv_derivKerCriterion (LSquare.maxProTwoGalK_isTopologicallyFinGen K)
    isProP_maxProPQuotient hk F (evenKernel_vM_sub_one_dvd_four hα)
    evenKernel_vM_diagonal_add_one_dvd_four, Hrel⟩

/-! ### §6.2 The endpoints -/

/-- **The `N` forward-generator package from `Hfam` alone**, at every `α ≥ 2`. -/
theorem evenResidual_forwardGeneratorDataN_of_family {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha)
    (base : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha)) (vN alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord alpha h (Nat.le_of_succ_le halpha))
        (vN alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (NForwardGeneratorData alpha h (chiCycKTwo (K := K))) :=
  evenAlphaTwo_forwardGeneratorDataN_of_residual halpha hrange base
    (evenResidual_residualSupplyN K halpha hrange Hfam)

/-- **The `M` forward-generator package from `Hfam` alone.** -/
theorem evenResidual_forwardGeneratorDataM_of_family {alpha h : ℕ} (halpha : 2 ≤ alpha)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha)
    (base : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha)) (vM alpha)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord alpha h (Nat.le_of_succ_le halpha))
        (vM alpha) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (MForwardGeneratorData alpha h (chiCycKTwo (K := K))) :=
  evenAlphaTwo_forwardGeneratorDataM_of_residual halpha hrange base
    (evenResidual_residualSupplyM K halpha hrange Hfam)

/-- **The `N` endpoint on the `α = 2` stratum, carrying `Hfam` alone.**  Wave 56's re-cut
endpoint `evenAlphaTwo_orientedEquivN_two_of_residual` with its single remaining hypothesis
discharged. -/
theorem evenResidual_orientedEquivN_two_of_family {R : LocalReciprocity} (B : MarkedRecip R K)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (nStageWord 2 h one_le_two) (vN 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (OrientedContinuousMulEquiv (chiN 2 h) (chiCycKTwo (K := K))) :=
  evenAlphaTwo_orientedEquivN_two_of_residual B hkappa hrange h hev
    (evenResidual_residualSupplyN K (le_refl 2) hrange Hfam)

/-- **The `M` endpoint on the `α = 2` stratum, carrying `Hfam` alone.** -/
theorem evenResidual_orientedEquivM_two_of_family {R : LocalReciprocity} (B : MarkedRecip R K)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : ∀ (k : ℕ), 3 ≤ k → ∀ T : Tuple (mStageWord 2 h one_le_two) (vM 2)
        (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) k,
      ∃ F : EvenKernelDerivationFamily T, EvenKernelRelatorKill F) :
    Nonempty (OrientedContinuousMulEquiv (chiM 2 h) (chiCycKTwo (K := K))) :=
  evenAlphaTwo_orientedEquivM_two_of_residual B hkappa hrange h hev
    (evenResidual_residualSupplyM K (le_refl 2) hrange Hfam)

end Family

end

end GQ2.Dyadic.EvenResidual

/-! ## §7 Axiom pins

Every public declaration of this file, printed.  §1-§5 are arithmetic-free and print std-3,
`[propext, Classical.choice, Quot.sound]`.  §6.1 acquires exactly one census axiom,
`absGalQ2_isTopologicallyFinitelyGenerated`, from `maxProTwoGalK_isTopologicallyFinGen` - the
same single axiom `evenClimbFinal_residualSupply{N,M}` acquires at the same station.  §6.2's two
`α = 2` endpoints print exactly the pins of the committed
`evenAlphaTwo_orientedEquiv{N,M}_two_of_residual` they restate, namely std-3 plus
`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
`absGalQ2_isTopologicallyFinitelyGenerated` and `absGalQ2_localEulerCharacteristic`.  **This
lane introduces no axiom that its inputs did not already consume.** -/

section AxiomPins

open GQ2.Dyadic.EvenResidual

-- §1 the two digit lemmas
#print axioms evenResidual_deep_cancel
#print axioms evenResidual_rep_dvd

-- §2 the character shadow of the shift word
#print axioms evenResidualShadow
#print axioms evenResidualShadow_levelMk
#print axioms evenResidualShadow_zLayer_sq
#print axioms evenResidualShadow_commP
#print axioms evenResidualShadow_handle
#print axioms evenResidualShadow_core
#print axioms evenResidual_shadow_dbarWord

-- §3 the shadow of the stage defect
#print axioms evenResidual_shadow_canonLift_sq
#print axioms evenResidual_shadow_defect_n
#print axioms evenResidual_shadow_defect_m

-- §4 deep coordinates, the off-zero repair, and the span comparison
#print axioms EvenResidualDeep
#print axioms evenResidual_deep_of_neutral
#print axioms evenResidual_deep_mul
#print axioms evenResidual_neutral_of_deep
#print axioms evenResidual_exists_neutral_of_forall_deep
#print axioms evenResidual_midRepair
#print axioms evenResidual_mem_bracketSpan_of_deep_zero
#print axioms evenResidual_deep_zero_of_shadow
#print axioms evenResidual_slotZero_deep
#print axioms evenResidual_mem_bracketSpan_of_shadow

-- §5 the headline
#print axioms evenResidual_admissible_mul_zLayer_neutral
#print axioms evenResidual_admissible_shift_mem_bracketSpan
#print axioms evenResidual_reachable_iff_defect_mem
#print axioms evenResidual_rawDefectSupply_of_residualSupply
#print axioms evenResidual_residualSupply_of_rawDefect_N
#print axioms evenResidual_residualSupply_of_rawDefect_M
#print axioms evenResidual_residualSupply_iff_rawDefect_N
#print axioms evenResidual_residualSupply_iff_rawDefect_M

-- §6 `Hfam` alone
#print axioms evenResidual_residualSupplyN
#print axioms evenResidual_residualSupplyM
#print axioms evenResidual_forwardGeneratorDataN_of_family
#print axioms evenResidual_forwardGeneratorDataM_of_family
#print axioms evenResidual_orientedEquivN_two_of_family
#print axioms evenResidual_orientedEquivM_two_of_family

end AxiomPins
