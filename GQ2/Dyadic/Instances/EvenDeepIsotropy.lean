/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenFrameDeep

/-!
# W54-BOCK: the depth class is isotropic, and the `M` frame becomes unconditional

## The gap this file closes

W53-KAPPA (`GQ2/Dyadic/Instances/StageAbstractionEvenFrameDeep.lean`) re-cut the `M`-row frame
onto the deep seam and reduced the whole `M` branch to a single equation.  Its frame theorem
`evenFrameDeep_mFrame_of_range` builds the `M`-row cup-adapted frame for every `α ≥ 2` from the
range identity, the ramified-`i` binder, and **one** further input: `frattiniFrameCup μ μ = 0`,
the isotropy of the depth class `μ = evenDeepClass α`, packaged per field as
`EvenDeepMIsotropicSupply`.  That input was shown to be *unavoidable*
(`evenFrameDeep_isotropic_of_frame`, an iff at `evenFrameDeep_mFrame_iff_isotropic`), and it was
discharged only on the `α = 2` stratum (`evenFrameDeep_isotropic_two`).  For `α ≥ 3` its
docstring recorded the intended route in two halves: `μ` lifts to a `ℤ/4`-valued character of
`G_K(2)`, and `x ∪ x` vanishes on a mod-2 class that lifts to `ℤ/4`.  Neither half was in the
tree.

**Both halves are proved here.**  `EvenDeepMIsotropicSupply K` is a theorem for every field and
every `α ≥ 2` (`evenDeepMIsotropicSupply_holds`); the `M`-row frame, the `M` level-three stage
base and the even `M` endpoint follow with that input gone.

## The mechanism: one congruence replaces the procyclic argument

The recorded justification for the lift was that `imChiM α / {±1}` is procyclic, so the depth
digit, being a surjection onto `ℤ/2`, extends to `ℤ/4`.  That argument needs a topological
generator and an isomorphism `1 + 2^αℤ₂ ≅ ℤ₂`.  §2 replaces it by a one-line congruence.

Write `u^2 - 1 = 2^(α+1) x` for `u ≡ ±1 (mod 2^α)`; the depth digit is the parity of `x`
(`evenDeepDigit_eq_zero_iff_two_dvd`).  Multiplying two such units gives
`x_{uw} = x_u + x_w + 2^(α+1) x_u x_w`, and for `α ≥ 1` the coefficient `2^(α+1)` is already
divisible by `4`.  So the cofactor **read modulo four** is additive on the nose:
`evenDeepDigitFour α`, defined as `x mod 4` through a locally constant test on the
mod-`2^(α+3)` reduction of `u^2`, is a homomorphism on the units `≡ ±1 (mod 2^α)`
(`evenDeepDigitFour_mul`), and its reduction is the depth digit
(`evenDeepDigit_eq_redFour`).  No logarithm, no procyclic generator, no filtration: exactly the
shape of argument W53-KAPPA used for the digit itself, one modulus deeper.

§1 supplies the classical half, at the generality the campaign's cup form actually needs.  For a
topological group `G` acting (necessarily trivially) on `𝔽₂`, a continuous `1`-cocycle `z` whose
values are the mod-2 reductions of a continuous homomorphism `F : G → ℤ/4` has
`[z] ∪ [z] = 0` (`trivialCup_self_eq_zero_of_liftFour`).  The witnessing `1`-cochain is the
*upper* binary digit of `F`: the carry identity
`carry b - carry (a + b) + carry a = red a · red b` on `ℤ/4` (`carryFour_add`, sixteen cases by
`decide`) is literally the coboundary equation for the cup cocycle `(g,h) ↦ z g · z h`.
This is `Sq^1 = β` in degree one, written out.

## What is proved, and what is carried

* §1 `trivialCup_self_eq_zero_of_liftFour`: group-generic, no field, std-3.
* §2 the mod-four digit, its homomorphism law, its continuity, and (§2.2) the identification
  `μ = ω` at `α = 2` (`evenDeepDigit_two_eq_omega`), the mod-16 case check the W53 docstring
  recorded as prose only: `u^2 ≡ 1 (mod 16)` exactly when `u ≡ ±1 (mod 8)`.  All std-3.
* §3 `frattiniFrameCup_self_eq_zero_of_liftFour`: the same vanishing at the transported field
  cup form, through the committed degree-two inflation comparison
  `inf2_trivialCupPairing_maxProPMk_galK`.  It costs exactly `tateDualityAt` (B6), which is the
  cost of `cupFormK` itself; **no further census axiom**.
* §4 `evenDeep_isotropic`, `evenDeepMIsotropicSupply_holds`: the discharge.  Nothing is
  carried.
* §5 the unconditional corollaries.  `evenDeepIsotropy_mFrame` is the `M`-row cup-adapted frame
  for every `α ≥ 2` with no isotropy hypothesis; `evenDeepIsotropy_mFrame_off_refutedSeam` is
  that frame at `α ≥ 3` paired with the refutation of the seam the committed layer consumed;
  `evenDeepIsotropy_mStageBase` is the level-three base; and
  `evenDeepIsotropy_orientedEquivM` is the even `M` endpoint.  The endpoint also loses the
  ramified-`i` binder: `evenDeep_kappa_ne_zero_of_neg` derives `κ ≠ 0` from the sign datum
  `hneg`, since a group element with cyclotomic value `-1` has mod-four parity `1`.  So the `M`
  endpoint now carries exactly `Hfam` and `Hup`, plus the marked-reciprocity bundle, the sign
  datum and the degree parity that the committed statement already carried.

Nothing committed is restated or modified; every declaration below is new.

## The alternative route, not taken

The equivalent Hilbert-symbol statement is `(-1, u_μ)_K = 1`, because `frattiniFrameCup_kappa`
turns `μ ∪ μ` into `κ ∪ μ` and `κ` is the class of `-1`.  It is true for a reason worth
recording, though it is not proved here.  Under the branch identification the cyclotomic image
is `{u ≡ ±1 (mod 2^α)}`, so `K(ζ_{2^α})` is quadratic over `K` and equals `K(i)`; and the kernel
of `μ` is `{u ≡ ±1 (mod 2^(α+1))}`, whose fixed field is the real subfield `K(λ)`,
`λ = ζ_{2^(α+1)} + ζ_{2^(α+1)}^{-1}`, with `λ^2 = d = 2 + ζ_{2^α} + ζ_{2^α}^{-1}`.  Since
the nontrivial element of `Gal(K(i)/K)` is `-1` in the image and so inverts `ζ_{2^α}`, one has
`d = (1 + ζ_{2^α})(1 + ζ_{2^α}^{-1}) = N_{K(i)/K}(1 + ζ_{2^α})`, so `d` is a norm and the symbol
is trivial.  Formalising that route needs the Kummer identification of `μ` with `[d]`, a
cyclotomic-unit computation, and the norm criterion (census axiom **B11a**); the Bockstein route
above needs none of the three, and its isotropy statement is strictly cheaper in census terms.

## Numbering

1. the Bockstein vanishing, group-generic;
2. the mod-four depth digit, its homomorphism law, its continuity, and `μ = ω` at depth two;
3. the vanishing at the field cup form;
4. the discharge of `EvenDeepMIsotropicSupply`;
5. the unconditional corollaries: frame, bypass, stage base, endpoint, and `μ = ω` at `α = 2`;
6. axiom pins.
-/

namespace GQ2.Dyadic.EvenDeepIsotropy

noncomputable section

open GQ2 ContCoh
open GQ2.Roe.Labute
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.StageGeneric
open GQ2.Dyadic.EvenForward
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.EvenCyclotomicRange
open GQ2.Dyadic.LSquare
open GQ2.Dyadic.LSquare.FrattiniFrameSupply
open GQ2.Dyadic.EvenFrameDeep

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The Bockstein vanishing

The classical fact the tree lacked: a mod-2 degree-one class that lifts to `ℤ/4` is isotropic
for the cup product.  It is stated here at exactly the generality the campaign's cup form needs,
namely the trivial-action mod-2 pairing `trivialCupPairing` of `Demushkin.lean`, and for an
arbitrary topological group; no field, no pro-`p` hypothesis, no finiteness.

The proof is the degree-one case of `Sq^1 = β`, written out on cochains.  Let `F : G → ℤ/4` be
a continuous homomorphism reducing to the cocycle `z`.  Split `F` into its two binary digits:
the lower one is `z`, and the upper one, `carryFour ∘ F`, is a continuous `1`-cochain whose
coboundary is the cup cocycle, because addition in `ℤ/4` carries into the second binary place
exactly when both lower digits are `1`.  That is `carryFour_add`, sixteen cases by `decide`. -/

section Bockstein

variable {G : Type*} [Group G] [TopologicalSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- **The lower binary digit** of a residue mod four, that is the reduction `ℤ/4 → ℤ/2`.  It is
spelled through `ZMod.val` rather than through `ZMod.castHom` so that the carry identity below is
a `decide`; the two agree (`redFour_eq_castHom`). -/
def redFour (a : ZMod 4) : ZMod 2 := ((a.val : ℕ) : ZMod 2)

/-- **The upper binary digit** of a residue mod four.  This is not a homomorphism, and its
failure to be one is exactly the cup cocycle: that is the content of `carryFour_add`. -/
def carryFour (a : ZMod 4) : ZMod 2 := ((a.val / 2 : ℕ) : ZMod 2)

/-- The lower digit is the ring-theoretic reduction. -/
theorem redFour_eq_castHom (a : ZMod 4) :
    redFour a = ZMod.castHom (by norm_num) (ZMod 2) a := by
  rw [redFour, ZMod.castHom_apply, ZMod.natCast_val]

/-- **The carry identity on `ℤ/4`**: the coboundary of the upper digit is the square of the
lower one.  Adding two residues carries into the second binary place exactly when both lower
digits are `1`, which is the whole of the Bockstein computation. -/
theorem carryFour_add (a b : ZMod 4) :
    carryFour b - carryFour (a + b) + carryFour a = redFour a * redFour b := by
  revert a b
  decide

/-- **The Bockstein vanishing**: a mod-2 degree-one class whose cocycle is the reduction of a
continuous `ℤ/4`-valued homomorphism has vanishing self-cup.

The hypotheses are unbundled on purpose: `F` is a bare continuous function together with its
multiplicativity and its reduction law, so a consumer who has a `ℤ/4` character in any packaging
can feed it without first building a `ContinuousMonoidHom`.  Nothing is assumed of `G` beyond a
topology, and the coefficient action is trivial for free at `ZMod 2`. -/
theorem trivialCup_self_eq_zero_of_liftFour
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (z : Z1 G (ZMod 2)) (F : G → ZMod 4) (hFc : Continuous F)
    (hFmul : ∀ g h : G, F (g * h) = F g + F h)
    (hFred : ∀ g : G, z.1 g = redFour (F g)) :
    H1mk G (ZMod 2) z ⌣[htriv] H1mk G (ZMod 2) z = 0 := by
  rw [trivialCupPairing, cup11_mk_mk]
  refine (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
  refine AddSubgroup.mem_map.mpr ⟨fun g => carryFour (F g), ?_, ?_⟩
  · exact Continuous.comp' (continuous_of_discreteTopology (f := carryFour)) hFc
  · funext p
    show p.1 • carryFour (F p.2) - carryFour (F (p.1 * p.2)) + carryFour (F p.1)
      = z.1 p.1 * (p.1 • z.1 p.2)
    rw [htriv, htriv, hFmul, hFred, hFred]
    exact carryFour_add (F p.1) (F p.2)

end Bockstein

/-! ## §2 The mod-four depth digit

The `ℤ/4` lift of `evenDeepDigit α`.  The recorded route obtained it from procyclicity of
`imChiM α / {±1}`; the route here is a congruence.  For `u ≡ ±1 (mod 2^α)` write
`u^2 - 1 = 2^(α+1) x` (`evenDeep_sq_sub_one`).  Multiplication gives
`x_{uw} = x_u + x_w + 2^(α+1) x_u x_w`, and `4 ∣ 2^(α+1)` as soon as `α ≥ 1`, so `x mod 4` is
already additive.  W53-KAPPA's proof that `x mod 2` is additive is the same computation one
modulus coarser, which is the sense in which the lift is free.

As in W53-KAPPA the definition is factored through the reduction of `u^2`, here modulo
`2^(α+3)` and so one digit further out, so that continuity is a one-liner.  Reading `x mod 4` off
that residue is the only arithmetic step with any content: `evenDeepFour_scale` divides by
`2^(α+1)` inside `ZMod (2^(α+3))` and `evenDeepFour_cast` identifies the result with
`toZModPow 2 x`. -/

section DigitFour

private theorem evenDeepFour_natMod (α m : ℕ) :
    2 ^ (α + 1) * m % 2 ^ (α + 3) / 2 ^ (α + 1) = m % 4 := by
  rw [show (2 : ℕ) ^ (α + 3) = 2 ^ (α + 1) * 4 from by ring, Nat.mul_mod_mul_left,
    Nat.mul_div_cancel_left _ (by positivity)]

private theorem evenDeepFour_dvd (α : ℕ) : (4 : ℕ) ∣ 2 ^ (α + 3) :=
  Dvd.intro (2 ^ (α + 1)) (by ring)

private theorem evenDeepFour_scale (α : ℕ) (c : ZMod (2 ^ (α + 3))) :
    ((((2 : ZMod (2 ^ (α + 3))) ^ (α + 1) * c).val / 2 ^ (α + 1) : ℕ) : ZMod 4)
      = ZMod.castHom (evenDeepFour_dvd α) (ZMod 4) c := by
  have hval : ((2 : ZMod (2 ^ (α + 3))) ^ (α + 1)) = ((2 ^ (α + 1) : ℕ) : ZMod (2 ^ (α + 3))) := by
    push_cast
    ring
  have hv : ((2 : ZMod (2 ^ (α + 3))) ^ (α + 1)).val = 2 ^ (α + 1) := by
    rw [hval, ZMod.val_natCast_of_lt (Nat.pow_lt_pow_right (by omega) (by omega))]
  rw [ZMod.val_mul, hv, evenDeepFour_natMod, ZMod.natCast_mod, ZMod.castHom_apply,
    ZMod.natCast_val]

private theorem evenDeepFour_cast (α : ℕ) (x : ℤ_[2]) :
    ZMod.castHom (evenDeepFour_dvd α) (ZMod 4) (PadicInt.toZModPow (α + 3) x)
      = PadicInt.toZModPow 2 x := by
  have h := PadicInt.zmod_cast_comp_toZModPow (p := 2) 2 (α + 3) (by omega)
  have h2 := congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ 2) => f x) h
  simp only [RingHom.comp_apply] at h2
  rw [← h2, ZMod.castHom_apply, ZMod.castHom_apply]

/-- The mod-four cofactor, read off a residue: divide by `2^(α+1)` in the integers, which is
exact on the residues that actually occur.  Factoring the definition through this function is
what makes §2.1 a one-liner. -/
def evenDeepFourOfSq (α : ℕ) (w : ZMod (2 ^ (α + 3))) : ZMod 4 :=
  (((w - 1).val / 2 ^ (α + 1) : ℕ) : ZMod 4)

/-- **The mod-four depth-`α` digit of a two-adic unit**: the residue of `(u^2 - 1)/2^(α+1)`
modulo four, spelled as a test on the mod-`2^(α+3)` reduction of `u^2`.  Its reduction mod two
is `evenDeepDigit α`, and on the units `≡ ±1 (mod 2^α)` it is a homomorphism, so it is the
`ℤ/4` lift the Bockstein vanishing asks for. -/
def evenDeepDigitFour (α : ℕ) (u : ℤ_[2]ˣ) : ZMod 4 :=
  evenDeepFourOfSq α (PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2))

/-- **The defining identity**: whenever `u^2 - 1 = 2^(α+1) x` the mod-four digit is `x` read
modulo four.  Everything below is this identity plus ring-hom formalities. -/
theorem evenDeepDigitFour_eq {α : ℕ} {u : ℤ_[2]ˣ} {x : ℤ_[2]}
    (hx : ((u : ℤ_[2]) ^ 2 - 1) = 2 ^ (α + 1) * x) :
    evenDeepDigitFour α u = PadicInt.toZModPow 2 x := by
  have hstep : PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2) - 1
      = (2 : ZMod (2 ^ (α + 3))) ^ (α + 1) * PadicInt.toZModPow (α + 3) x := by
    have h1 : PadicInt.toZModPow (α + 3) ((u : ℤ_[2]) ^ 2 - 1)
        = PadicInt.toZModPow (α + 3) (2 ^ (α + 1) * x) := by rw [hx]
    rw [map_sub, map_one] at h1
    rw [h1, map_mul, map_pow, map_ofNat]
  rw [evenDeepDigitFour, evenDeepFourOfSq, hstep, evenDeepFour_scale, evenDeepFour_cast]

/-- **The homomorphism law of the mod-four digit**, on the units `≡ ±1 (mod 2^α)`.  The cross
term of `x_{uw} = x_u + x_w + 2^(α+1) x_u x_w` dies modulo four because `α ≥ 1`, which is the
one place the extra digit is bought.  Compare `evenDeepDigit_mul`, the same computation modulo
two, where the cross term dies for the weaker reason `α ≥ 0`. -/
theorem evenDeepDigitFour_mul {α : ℕ} (hα : 1 ≤ α) {a b : ℤ_[2]ˣ}
    (ha : EvenSharpPmOne α a) (hb : EvenSharpPmOne α b) :
    evenDeepDigitFour α (a * b) = evenDeepDigitFour α a + evenDeepDigitFour α b := by
  obtain ⟨x, hx⟩ := evenDeep_sq_sub_one hα ha
  obtain ⟨y, hy⟩ := evenDeep_sq_sub_one hα hb
  have hxy : (((a * b : ℤ_[2]ˣ) : ℤ_[2]) ^ 2 - 1) =
      2 ^ (α + 1) * (x + y + 2 ^ (α + 1) * (x * y)) := by
    push_cast
    linear_combination ((b : ℤ_[2]) ^ 2) * hx + (1 + 2 ^ (α + 1) * x) * hy
  have h0 : (2 : ZMod 4) ^ (α + 1) = 0 := by
    obtain ⟨β, rfl⟩ : ∃ β, α = β + 1 := ⟨α - 1, by omega⟩
    rw [show β + 1 + 1 = 2 + β from by omega, pow_add,
      show ((2 : ZMod 4) ^ 2) = 0 from by decide, zero_mul]
  rw [evenDeepDigitFour_eq hx, evenDeepDigitFour_eq hy, evenDeepDigitFour_eq hxy,
    map_add, map_add, map_mul, map_pow, map_ofNat, h0, zero_mul, add_zero]

/-- **The lift condition**: reducing the mod-four digit gives the depth digit.  Both sides are
readings of the same cofactor, one modulo four and one modulo two. -/
theorem evenDeepDigit_eq_redFour {α : ℕ} (hα : 1 ≤ α) {u : ℤ_[2]ˣ}
    (hu : EvenSharpPmOne α u) :
    evenDeepDigit α u = redFour (evenDeepDigitFour α u) := by
  obtain ⟨x, hx⟩ := evenDeep_sq_sub_one hα hu
  have hlow : redFour (PadicInt.toZModPow 2 x) = PadicInt.toZModPow 1 x := by
    rw [redFour_eq_castHom]
    have h := PadicInt.zmod_cast_comp_toZModPow (p := 2) 1 2 (by norm_num)
    have h2 := congrArg (fun f : ℤ_[2] →+* ZMod (2 ^ 1) => f x) h
    simp only [RingHom.comp_apply] at h2
    rw [← h2, ZMod.castHom_apply, ZMod.castHom_apply]
  have hdvd : (2 : ℤ_[2]) ∣ x ↔ PadicInt.toZModPow 1 x = 0 := by
    rw [show (0 : ZMod (2 ^ 1)) = PadicInt.toZModPow 1 (0 : ℤ_[2]) from (map_zero _).symm,
      GQ2.toZModPow_eq_iff_two_pow_dvd, pow_one, sub_zero]
  rw [evenDeepDigitFour_eq hx, hlow]
  by_cases hd : evenDeepDigit α u = 0
  · rw [hd, hdvd.mp ((evenDeepDigit_eq_zero_iff_two_dvd hx).mp hd)]
  · rw [evenDeepDigit_eq_one_of_ne_zero hd]
    have hne : PadicInt.toZModPow 1 x ≠ 0 := fun hc ↦
      hd ((evenDeepDigit_eq_zero_iff_two_dvd hx).mpr (hdvd.mpr hc))
    rcases ZMod.eq_zero_or_eq_one (PadicInt.toZModPow 1 x) with h' | h'
    · exact absurd h' hne
    · rw [h']

end DigitFour

/-! ### §2.1 Continuity

Verbatim the shape of `evenDeepDigitChar`'s continuity proof: the digit is a function of the
mod-`2^(α+3)` reduction of the square of the character value, and those reductions have open
fibres. -/

section DigitFourChar

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

omit [IsTopologicalGroup G] in
/-- **Continuity of the mod-four digit** along a continuous character: it factors through the
mod-`2^(α+3)` reduction of the square of the character value, which is locally constant. -/
theorem continuous_evenDeepDigitFour (α : ℕ) (chi : ContinuousMonoidHom G ℤ_[2]ˣ) :
    Continuous (fun g : G ↦ evenDeepDigitFour α (chi g)) := by
  refine IsLocallyConstant.continuous fun s ↦ ?_
  have hfact : (fun g : G ↦ evenDeepDigitFour α (chi g)) ⁻¹' s =
      (fun g : G ↦ ((chi g : ℤ_[2]ˣ) : ℤ_[2]) ^ 2) ⁻¹'
        (PadicInt.toZModPow (p := 2) (α + 3) ⁻¹'
          {c : ZMod (2 ^ (α + 3)) | evenDeepFourOfSq α c ∈ s}) := rfl
  show IsOpen ((fun g : G ↦ evenDeepDigitFour α (chi g)) ⁻¹' s)
  rw [hfact]
  exact (isOpen_preimage_toZModPow (α + 3) _).preimage
    ((continuous_pow 2).comp (Units.continuous_val.comp chi.continuous_toFun))

end DigitFourChar

/-! ### §2.2 The identification with `ω` at depth two

The W53-KAPPA docstring states in prose that the depth class at `α = 2` *is* the `ω` class,
"since both digits vanish exactly when `u^2 ≡ 1 (mod 16)`", and records that nothing there needs
it.  It is proved here: on `(ZMod 16)ˣ` the squares are `1` exactly at `±1, ±7`, which is
`u ≡ ±1 (mod 8)`, which is `ω = 0`.  Eight cases by `decide`; the class-level statement
`evenDeepClass_two_eq_omegaClass` is in §5.  This is what makes the input of W53-KAPPA the
depth-`α` generalisation of `mEvenFrameCup_omega_self` rather than an analogy. -/

/-- **At depth two the digit is Serre's `ω`.**  The mod-16 case check W53-KAPPA recorded in
prose: a two-adic unit has `u^2 ≡ 1 (mod 16)` exactly when `u ≡ ±1 (mod 8)`, so both digits
vanish on the same units, and being `𝔽₂`-valued they are equal. -/
theorem evenDeepDigit_two_eq_omega (u : ℤ_[2]ˣ) :
    evenDeepDigit 2 u = Multiplicative.toAdd (unitsModEightOmega
      (Units.map (PadicInt.toZModPow 3).toMonoidHom u)) := by
  have key : ∀ w : (ZMod 16)ˣ,
      evenDeepDigitOfSq 2 ((w : ZMod 16) ^ 2)
        = Multiplicative.toAdd (unitsModEightOmega
            (Units.map (ZMod.castHom (by norm_num : (8 : ℕ) ∣ 16) (ZMod 8)).toMonoidHom w)) := by
    decide
  have hcast : Units.map (PadicInt.toZModPow 3).toMonoidHom u
      = Units.map (ZMod.castHom (by norm_num : (8 : ℕ) ∣ 16) (ZMod 8)).toMonoidHom
          (Units.map (PadicInt.toZModPow 4).toMonoidHom u) := by
    refine Units.ext ?_
    rw [Units.coe_map, Units.coe_map, Units.coe_map]
    show PadicInt.toZModPow 3 ((u : ℤ_[2])) =
      ZMod.castHom (by norm_num : (8 : ℕ) ∣ 16) (ZMod 8) (PadicInt.toZModPow 4 (u : ℤ_[2]))
    rw [ZMod.castHom_apply]
    exact (PadicInt.cast_toZModPow 3 4 (by norm_num) _).symm
  have hsq : PadicInt.toZModPow (2 + 2) ((u : ℤ_[2]) ^ 2)
      = ((Units.map (PadicInt.toZModPow 4).toMonoidHom u : (ZMod 16)ˣ) : ZMod 16) ^ 2 := by
    rw [Units.coe_map, ← map_pow]
    rfl
  rw [evenDeepDigit, hsq, key, hcast]

/-! ## §3 The Bockstein vanishing at the field cup form

§1 lands in `H²(G_K(2), 𝔽₂)`; the campaign's form is `frattiniFrameCup`, the field cup form
`FieldData.cupFormK` transported along degree-one inflation.  The bridge is committed:
`inf2_trivialCupPairing_maxProPMk_galK` says degree-two inflation carries the quotient-side cup
to the field-side one, so a vanishing upstairs is a vanishing downstairs, and `invGalK` of `0`
is `0`.  The statement therefore costs exactly what `cupFormK` costs, `tateDualityAt`, and no
more: in particular it does **not** go through `cupFormK_kappa`, so it does not consume the
norm criterion. -/

section FieldBockstein

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance evenDeepIsotropyScalar : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance evenDeepIsotropyContinuousScalar :
    ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

omit [T2Space (GalK K)] in
/-- **The field-level Bockstein vanishing**: the degree-one class of a mod-2 character of
`G_K(2)` that lifts to `ℤ/4` is isotropic for the transported field cup form.

Note what this does *not* use: the Labute identity `frattiniFrameCup_kappa`, and with it the
norm criterion.  The only census axiom consumed is the one already inside `cupFormK`. -/
theorem frattiniFrameCup_self_eq_zero_of_liftFour
    (c : ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) (Multiplicative (ZMod 2)))
    (F : maxProPQuotient 2 (GalK K) → ZMod 4) (hFc : Continuous F)
    (hFmul : ∀ g h : maxProPQuotient 2 (GalK K), F (g * h) = F g + F h)
    (hFred : ∀ g : maxProPQuotient 2 (GalK K),
      Multiplicative.toAdd (c g) = redFour (F g)) :
    frattiniFrameCup (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c) = 0 := by
  have hz : trivialCupPairing 2 (maxProPQuotient 2 (GalK K)) Count.smul_zmod2
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c)
      (SqCyclotomicFrattiniFrame.characterClass (K := K) c) = 0 :=
    trivialCup_self_eq_zero_of_liftFour Count.smul_zmod2 (Count.homEquivZ1 c) F hFc hFmul hFred
  have hgal : trivialCupPairing 2 (GalK K) (htriv_galK K)
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      = 0 := by
    rw [← inf2_trivialCupPairing_maxProPMk_galK, hz, map_zero]
  unfold frattiniFrameCup FieldData.cupFormK
  rw [show (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
        ⌣[FieldData.smul_zmodTwo_galK K]
      (h1MaxProTwoEquivGalK (K := K) (SqCyclotomicFrattiniFrame.characterClass (K := K) c))
      = 0 from hgal, map_zero]

/-! ## §4 The discharge

§2 and §3 meet.  The depth class is `characterClass` of `evenDeepDigitChar`; its `ℤ/4` lift is
`evenDeepDigitFour ∘ chiCycKTwo`, a homomorphism because the range identity puts every character
value in `{u ≡ ±1 (mod 2^α)}` (`evenDeep_bound_of_range`), continuous by §2.1, and reducing to
the digit by §2.  So the isotropy holds outright, and the per-field supply
`EvenDeepMIsotropicSupply` of W53-KAPPA §7 is a theorem. -/

omit [T2Space (GalK K)] in
/-- **The depth class is isotropic**, for every `α ≥ 2` and every field with the branch
identification.  This is the lemma W53-KAPPA reduced its `M` branch to. -/
theorem evenDeep_isotropic {α : ℕ} (hα : 2 ≤ α)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    frattiniFrameCup (evenDeepClass α (Nat.le_of_succ_le hα) hrange)
      (evenDeepClass α (Nat.le_of_succ_le hα) hrange) = 0 := by
  have hbound := evenDeep_bound_of_range (Nat.le_of_succ_le hα) hrange
  unfold evenDeepClass
  refine frattiniFrameCup_self_eq_zero_of_liftFour _
    (fun g ↦ evenDeepDigitFour α (chiCycKTwo (K := K) g))
    (continuous_evenDeepDigitFour α (chiCycKTwo (K := K))) (fun g h ↦ ?_) (fun g ↦ ?_)
  · rw [map_mul, evenDeepDigitFour_mul (by omega) (hbound g) (hbound h)]
  · rw [evenDeepDigitChar_apply, toAdd_ofAdd]
    exact evenDeepDigit_eq_redFour (by omega) (hbound g)

/-- **The per-field isotropy supply is a theorem.**  `EvenDeepMIsotropicSupply` was the last
new datum of the `M` frame re-cut; it is carried by nobody after this line. -/
theorem evenDeepMIsotropicSupply_holds : EvenDeepMIsotropicSupply K :=
  fun _ hα hrange ↦ evenDeep_isotropic hα hrange

/-! ## §5 The unconditional corollaries

The shapes W53-KAPPA left conditional, with the isotropy gone: the frame, the bypass statement,
the level-three stage base, and the endpoint.  The endpoint sheds one more binder: the
ramified-`i` datum `κ ≠ 0` is not independent of the `M`-branch sign datum, because an element
with cyclotomic value `-1` already has mod-four parity `1` (`evenDegreeM_parity_negOne`), so
`evenDeep_kappa_ne_zero_of_neg` derives it.  What the even `M` endpoint carries after this file
is `Hfam` and `Hup` and nothing else new.  §5 closes with the `α = 2` class identification, the
one item of this file that no later consumer needs but that pins the layer's provenance. -/

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The ramified-`i` binder is implied by the `M`-branch sign datum.**  If `-1` is a
cyclotomic value then some group element has mod-four parity `1`, so the mod-four class is
nonzero.  This removes `hkappa` from the endpoint's input list. -/
theorem evenDeep_kappa_ne_zero_of_neg
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom) :
    cyclotomicModFourClassKTwo (K := K) ≠ 0 := by
  obtain ⟨g, hg⟩ := hneg
  intro h0
  have h1 : frattiniFrameEval (cyclotomicModFourClassKTwo (K := K)) g = 0 := by
    rw [h0]
    exact frattiniFrameEval_zero g
  rw [frattiniFrameEval_modFour, show chiCycKTwo (K := K) g = -1 from hg,
    evenDegreeM_parity_negOne] at h1
  exact one_ne_zero h1

/-- **The `M`-row cup-adapted Frattini frame, unconditionally in the isotropy**, for every
`α ≥ 2`: `evenFrameDeep_mFrame_of_range` with its last hypothesis discharged. -/
theorem evenDeepIsotropy_mFrame {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    ∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
      F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) :=
  evenFrameDeep_mFrame_of_range hα hdeg hkappa hrange (evenDeep_isotropic hα hrange)

/-- **The `M` level-three stage base, unconditionally in the isotropy**:
`evenFrameDeep_mStageBase` with its last hypothesis discharged.  This is the shape that
discharges `Hbase` of the committed endpoint. -/
theorem evenDeepIsotropy_mStageBase {α h : ℕ} (hα : 2 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (hkappa : cyclotomicModFourClassKTwo (K := K) ≠ 0)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    Nonempty (Tuple (mStageWord α h (Nat.le_of_succ_le hα)) (vM α)
      (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)) 3) :=
  evenFrameDeep_mStageBase hα hdeg hkappa hrange (evenDeep_isotropic hα hrange)

/-- **The bypass, unconditionally.**  At `α ≥ 3` the level-two lift instance that the committed
frame layer consumes is false (`evenPerK_not_mLevelTwoLift_of_range`), and the `M`-row
cup-adapted frame exists all the same, with nothing carried but the range identity and the sign
datum.  This is the sharp form of what the wave bought: the re-cut route is not merely available
where the committed one is, it is available where the committed one is refuted. -/
theorem evenDeepIsotropy_mFrame_off_refutedSeam {α h : ℕ} (hα3 : 3 ≤ α)
    (hdeg : Module.finrank ℚ_[2] K = 2 * h + 2)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM α) :
    ¬ EvenPerK.EvenPerKLevelTwoLift (vM (h := h) α) (maxProPQuotient 2 (GalK K))
        (chiCycKTwo (K := K)) ∧
      ∃ F : Frame (vM (h := h) α) (maxProPQuotient 2 (GalK K)) (chiCycKTwo (K := K)),
        F.IsCupAdapted (evenFrameGram h) (evenFramePairing (K := K)) :=
  evenFrameDeep_mFrame_off_refutedSeam hα3 hdeg (evenDeep_kappa_ne_zero_of_neg hneg) hrange
    (evenDeep_isotropic (Nat.le_of_succ_le hα3) hrange)

omit [FiniteDimensional ℚ_[2] K] [T2Space (GalK K)] in
/-- **The depth class at `α = 2` is the `ω` class.**  Both are the degree-one class of a
character of `G_K(2)`, and §2.2 identifies the two characters value by value.  With this, the
input of W53-KAPPA is literally the depth-`α` generalisation of `mEvenFrameCup_omega_self`, and
its `α = 2` discharge `evenFrameDeep_isotropic_two` is that theorem transported. -/
theorem evenDeepClass_two_eq_omegaClass
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM 2) :
    evenDeepClass 2 one_le_two hrange = cyclotomicModEightOmegaClassKTwo (K := K) := by
  unfold evenDeepClass SqCyclotomicFrattiniFrame.characterClass
    cyclotomicModEightOmegaClassKTwo
  congr 1
  apply Subtype.ext
  funext g
  exact evenDeepDigit_two_eq_omega (chiCycKTwo (K := K) g)

/-- **The even `M` endpoint**, with the isotropy discharged and the ramified-`i` binder derived.

Against the committed `evenPerK_orientedEquivM` this trades `Hbase` for nothing and keeps
`Hfam`, `Hup`; against `evenFrameDeep_orientedEquivM` it drops both `Hiso` and `hkappa`.  The
inputs that remain are the marked-reciprocity bundle, the sign datum, the even-degree parity,
and the two per-field supplies `Hfam` and `Hup`. -/
theorem evenDeepIsotropy_orientedEquivM {R : LocalReciprocity} (B : MarkedRecip R K)
    (hneg : (-1 : ℤ_[2]ˣ) ∈ MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom)
    (h : ℕ) (hev : Module.finrank ℚ_[2] K = 2 + 2 * h)
    (Hfam : EvenPerK.EvenPerKMFamilySupply h K) (Hup : EvenPerK.EvenPerKMRawToBracket h K) :
    ∃ alpha : ℕ, 2 ≤ alpha ∧
      Nonempty (OrientedContinuousMulEquiv (chiM alpha h) (chiCycKTwo (K := K))) :=
  evenFrameDeep_orientedEquivM B hneg (evenDeep_kappa_ne_zero_of_neg hneg) h hev
    evenDeepMIsotropicSupply_holds Hfam Hup

end FieldBockstein

end

end GQ2.Dyadic.EvenDeepIsotropy

/-! ## §6 Axiom pins

Every public declaration of this file, printed, the two local coefficient-action instances
included.  §§1 and 2 are group-generic cohomology and two-adic arithmetic and print at std-3
(`propext`, `Classical.choice`, `Quot.sound`); `evenDeepFourOfSq` prints a proper subset of it.

§§3 and 4 reach the field layer through `cupFormK` and print std-3 plus **B6**
`tateDualityAt` only.  That is the whole cost of the new input: in particular the norm criterion
**B11a** `hilbertSymbol_normCriterion_finiteDyadic` does *not* appear, which is the census
statement of the remark in the header that the Bockstein route is the cheaper of the two.

§5's four corollaries print exactly the committed prints of the theorems they instantiate,
namely std-3 plus B6, B7 (`absGalQ2_localEulerCharacteristic`), B11a and
`absGalQ2_isTopologicallyFinitelyGenerated`: the frame scaffolding and the transgression
realisation, unchanged.  `evenDeep_kappa_ne_zero_of_neg` and `evenDeepClass_two_eq_omegaClass`
are std-3.  No axiom of this file is new. -/

section AxiomPins

open GQ2.Dyadic.EvenDeepIsotropy

#print axioms redFour
#print axioms carryFour
#print axioms redFour_eq_castHom
#print axioms carryFour_add
#print axioms trivialCup_self_eq_zero_of_liftFour
#print axioms evenDeepFourOfSq
#print axioms evenDeepDigitFour
#print axioms evenDeepDigitFour_eq
#print axioms evenDeepDigitFour_mul
#print axioms evenDeepDigit_eq_redFour
#print axioms continuous_evenDeepDigitFour
#print axioms evenDeepIsotropyScalar
#print axioms evenDeepIsotropyContinuousScalar
#print axioms frattiniFrameCup_self_eq_zero_of_liftFour
#print axioms evenDeep_isotropic
#print axioms evenDeep_kappa_ne_zero_of_neg
#print axioms evenDeepMIsotropicSupply_holds
#print axioms evenDeepIsotropy_mFrame
#print axioms evenDeepIsotropy_mStageBase
#print axioms evenDeepIsotropy_mFrame_off_refutedSeam
#print axioms evenDeepDigit_two_eq_omega
#print axioms evenDeepClass_two_eq_omegaClass
#print axioms evenDeepIsotropy_orientedEquivM

end AxiomPins
