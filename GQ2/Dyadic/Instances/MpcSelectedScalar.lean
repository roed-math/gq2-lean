/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.MpcPairings

/-!
# The procyclic-`M` scalar residue at the selection seam

`MpcPairings` discharges `MProcyclicExact.ScalarActionImageStokes` for each of the three
`EtaDisplay` constructors separately: `.one` unconditionally, `.lit k` under `Odd k`, and
`.hat num den` under the `2`-adic unit hypothesis `η = 1 + 2z`.  The campaign seam does not
present a constructor: `SemanticSelectionView` carries an abstract `MpcDisplayFor eta`, a
*structure* with fields `display`, `wf` and `represents`, so a case split there has to discharge
all three side conditions from `wf` and `represents` alone.  This file does that, and hence
removes the scalar residue from the seam-level supply theorems.

⚠ **The obstruction recorded on `MProcyclicExact.scalarActionImageStokes_ofNpc` is real but
avoidable.**  That docstring says `MpcDisplayFor` has no analogue of
`NpcDisplayFor.exists_toPadic_eq_one_add_two_mul` because reading `toPadic` back off
`represents` would need injectivity of `etaHatZ`, which is not in the tree.  True, and it stays
true — but the `.hat` case never needed `represents` at all.  A `.hat` display's
well-formedness field *is* the statement that both entries are odd (`wfB`), and `num/den` with
both entries odd is a `2`-adic unit on the nose.  So the hypothesis comes off `wf`, not off
`represents`, and no injectivity is involved.

The `.lit` case is the one that does use `represents`, and there the argument is the
`etaHatZ_ne_omega2` argument one prime down: evaluate the displayed exponent on a group of order
`2`.  Rule T2's companion says `η̂` acts as `x · x^{padicOmega2Exp(η−1, 2)}`, and the second
factor is trivial because `η − 1` is even; the display acts as `x^k`; so `x^k = x` on an element
of order `2` and `k` is odd.

## What this file adds

* `Words.Mpc.EtaDisplay.exists_toPadic_eq_one_add_two_mul_of_wf` — the `.hat` unit hypothesis
  from well-formedness;
* `Words.Mpc.EtaDisplay.odd_of_lit_representsUnit` — the `.lit` oddness from representation;
* `MProcyclicExact.scalarActionImageStokes_of_display` — the scalar residue for **every**
  `MpcDisplayFor`, the analogue of `displayFixedPointFree_of_representsUnit` one residue over;
* `MProcyclicExact.uniformPushedHsimp_of_ramified_display` — the procyclic-`M` uniform pushed
  residue on the single remaining ramified input, at an arbitrary selected display.
-/

namespace GQ2.Dyadic

noncomputable section

open GQ2 GQ2.Dyadic.Words.Mpc

namespace Words.Mpc.EtaDisplay

/-- **A well-formed `.hat` display denotes a `2`-adic unit, hence is `1 + 2z`.**

`wfB` on the `.hat` constructor is exactly "both entries odd", and an odd integer is a `2`-adic
unit, so `η = num · den⁻¹` has residue `1` in `ZMod 2` and `η − 1` lies in the maximal ideal.
This is the `Mpc` analogue of `NpcDisplayFor.exists_toPadic_eq_one_add_two_mul`, obtained from
the certificate's well-formedness rather than from its representation claim. -/
theorem exists_toPadic_eq_one_add_two_mul_of_wf {num den : ℤ}
    (hwf : (EtaDisplay.hat num den).wfB = true) :
    ∃ z : ℤ_[2], (EtaData.mk num den).toPadic = 1 + 2 * z := by
  simp only [EtaDisplay.wfB, Bool.and_eq_true, bne_iff_ne, ne_eq] at hwf
  obtain ⟨hnum, hden⟩ := hwf
  have hdennorm : ‖((den : ℤ) : ℤ_[2])‖ = 1 := by
    rcases lt_or_eq_of_le (PadicInt.norm_le_one (((den : ℤ) : ℤ_[2]))) with hlt | heq
    · exact absurd ((PadicInt.norm_int_lt_one_iff_dvd den).mp hlt) (by omega)
    · exact heq
  have hnumZ : (PadicInt.toZMod ((num : ℤ) : ℤ_[2]) : ZMod 2) = 1 := by
    have hcast : PadicInt.toZMod ((num : ℤ) : ℤ_[2]) = ((num : ℤ) : ZMod 2) := map_intCast _ _
    have hne : ((num : ℤ) : ZMod 2) ≠ 0 := fun h ↦ by
      rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at h
      omega
    rw [hcast]
    revert hne
    generalize ((num : ℤ) : ZMod 2) = a
    revert a
    decide
  have hinvZ : (PadicInt.toZMod (PadicInt.inv ((den : ℤ) : ℤ_[2])) : ZMod 2) = 1 := by
    have hmul := congrArg (PadicInt.toZMod (p := 2)) (PadicInt.mul_inv hdennorm)
    rw [map_mul, map_one] at hmul
    revert hmul
    generalize (PadicInt.toZMod (((den : ℤ) : ℤ_[2])) : ZMod 2) = b
    generalize (PadicInt.toZMod (PadicInt.inv ((den : ℤ) : ℤ_[2])) : ZMod 2) = c
    revert b c
    decide
  have hone : PadicInt.toZMod ((EtaData.mk num den).toPadic) = 1 := by
    rw [EtaData.toPadic, map_mul, hnumZ, hinvZ, mul_one]
  have hker : ((EtaData.mk num den).toPadic - 1)
      ∈ RingHom.ker (PadicInt.toZMod : ℤ_[2] →+* ZMod 2) := by
    rw [RingHom.mem_ker, map_sub, hone, map_one, sub_self]
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton] at hker
  obtain ⟨z, hz⟩ := hker
  refine ⟨z, ?_⟩
  push_cast at hz
  rwa [sub_eq_iff_eq_add'] at hz

section LitDisplay

local instance : TopologicalSpace (Multiplicative (ZMod 2)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 2)) := ⟨rfl⟩

/-- **A literal display that represents a field unit carries an odd exponent.**

`etaHatZ_ne_omega2` separates `η̂` from `ω₂` by their action on a group of order `3`; the same
device one prime down separates `Zhat.ofInt k` from `η̂` unless `k` is odd.  On an element `x` of
order `2` the display acts as `x^k`, while `η̂` acts as `x · x^{padicOmega2Exp(η−1, 2)}` and the
second factor is trivial because `η − 1` is even for a unit `η`
(`NProcyclicUnram.even_padicOmega2Exp_of_oneUnit`).  So `x^k = x`, i.e. `2 ∣ k − 1`.

⚠ The oddness is genuinely needed downstream: `MProcyclicNormal.oddDisplayJet_lit` reads the
scalar row's `(a_σ, x₂)` plane off `|k|`, and at an even `k` that plane degenerates. -/
theorem odd_of_lit_representsUnit {k : ℤ} {eta : ℤ_[2]ˣ}
    (hd : (EtaDisplay.lit k).RepresentsUnit eta) : Odd k := by
  have hzh : Zhat.ofInt k = etaHatZ (eta : ℤ_[2]) := hd
  set x : Multiplicative (ZMod 2) := Multiplicative.ofAdd (1 : ZMod 2) with hxdef
  have hx2 : x ^ 2 = 1 := by decide
  have hxne : x ≠ 1 := by decide
  have hord : orderOf x = 2 := by
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_two _ (orderOf_dvd_of_pow_eq_one hx2)
      with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxne
    · exact h
  obtain ⟨w, hw⟩ := exists_padicUnit_eq_one_add_two_mul eta
  obtain ⟨c, hc⟩ := NProcyclicUnram.even_padicOmega2Exp_of_oneUnit w hw (orderOf x)
  have hev : x ^ᶻ etaHatZ (eta : ℤ_[2]) = x := by
    rw [zpowHat_etaHatZ, hc, ← two_mul, pow_mul, hx2, one_pow, mul_one]
  have hkey : x ^ (k : ℤ) = x := by rw [← zpowHat_ofInt, hzh, hev]
  have hsub : x ^ (k - 1 : ℤ) = 1 := by
    rw [zpow_sub, hkey, zpow_one, mul_inv_cancel]
  have hdvd : ((orderOf x : ℕ) : ℤ) ∣ (k - 1) := orderOf_dvd_iff_zpow_eq_one.mpr hsub
  rw [hord] at hdvd
  rw [Int.odd_iff]
  omega

end LitDisplay

end Words.Mpc.EtaDisplay

namespace MProcyclicExact

/-- **The scalar sub-branch of the procyclic-`M` unramified obligation, for every selected
display.**

The three constructors close by three different routes, and none of them is an extra hypothesis:

* `.one` — jet `1`, unconditionally (`scalarActionImageStokes_one`);
* `.lit k` — jet `|k|`, odd because the display represents a field unit;
* `.hat num den` — jet `1 + padicOmega2Exp(η − 1, N)`, odd because the display is well formed.

This is `displayFixedPointFree_of_representsUnit` one residue over: with it and
`unramifiedNormalPairingIsCompact`, the only second-order input the procyclic-`M` row still
needs at the seam is the ramified one.

`2 ≤ α` is not a restriction at the seam either: `FieldBranchSelection.valid` supplies exactly
`2 ≤ α ∧ 1 ≤ r` on the `Mpc` branch. -/
theorem scalarActionImageStokes_of_display {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ}
    (hα : 2 ≤ alpha) (hqe : Even q) (d : MpcDisplayFor eta) :
    ScalarActionImageStokes alpha r pp h q d.display := by
  obtain ⟨disp, hwf, hrep⟩ := d
  cases disp with
  | one => exact scalarActionImageStokes_one hα hqe
  | lit k =>
      exact scalarActionImageStokes_lit hα hqe
        (Words.Mpc.EtaDisplay.odd_of_lit_representsUnit hrep)
  | hat num den =>
      obtain ⟨z, hz⟩ := Words.Mpc.EtaDisplay.exists_toPadic_eq_one_add_two_mul_of_wf hwf
      exact scalarActionImageStokes_hat z hα hqe hz

/-- **The procyclic-`M` uniform pushed residue at an arbitrary selected display, on the single
ramified input.**

Of the three second-order residues `uniformPushedHsimp_of_pairings` names, two are now theorems
for every display the seam can present: the generic unramified pairing unconditionally
(`unramifiedNormalPairingIsCompact`) and the scalar sub-branch from the display package
(`scalarActionImageStokes_of_display`).  The arithmetic residue was already free through
`MpcDisplayFor.represents`.  So `hsep` is the whole remaining cost of the row.

This is the shape `CertificateSupplyFamilyRN.SemanticSelectedHsimpRN.of_Mpc_actionImage` and
`SelectedHsimp.of_Mpc_actionImage` consume: both currently bind `hpair`, `hsc` and `hsep`, and
both can drop the first two by routing through this theorem. -/
theorem uniformPushedHsimp_of_ramified_display {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ}
    (hα : 2 ≤ alpha) (hqe : Even q) (d : MpcDisplayFor eta)
    (hsep : RamifiedNormalPairingSeparates alpha r pp h q d.display) :
    UniformPushedHsimp alpha r pp h q d.display :=
  uniformPushedHsimp_of_pairings (by omega) hqe d.represents unramifiedNormalPairingIsCompact
    (scalarActionImageStokes_of_display hα hqe d) hsep

end MProcyclicExact

end

end GQ2.Dyadic

/-! ## Axiom audit -/

section AxiomAudit

#print axioms
  GQ2.Dyadic.Words.Mpc.EtaDisplay.exists_toPadic_eq_one_add_two_mul_of_wf
#print axioms GQ2.Dyadic.Words.Mpc.EtaDisplay.odd_of_lit_representsUnit
#print axioms GQ2.Dyadic.MProcyclicExact.scalarActionImageStokes_of_display
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_ramified_display

end AxiomAudit
