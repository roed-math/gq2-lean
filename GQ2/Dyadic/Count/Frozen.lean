/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Presentation
import GQ2.Dyadic.Words.L
import GQ2.Dyadic.Words.Npc
import GQ2.Dyadic.Words.M0
import GQ2.Dyadic.Words.Mpc
import GQ2.Dyadic.Certificates.M0
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.Certificates.MpcStokes
import GQ2.Dyadic.Certificates.Npc

/-!
# The five frozen branch families, presented and resolved at their intrinsic words
(tickets CB-TR, CB-FR)

`Count/Presentation.lean` proves `Count.isAdmissibleMarkedPresentation_gammaR`, which is generic
in the branch word `R` and carries **no hypotheses**.  The five frozen rows of the count lane are
therefore specializations of it and nothing more — which is the whole point of the CB-TR redesign:
with the relators read at each finite discrete target, there is no per-branch reconciliation left
to do.  This file records the five, plus the `ω₂`-only status that decides which of them
`Count.resolvesAt_gammaFam` covers on the word side.

It is a **leaf**: `Count/Presentation.lean` deliberately does not import the four `Words.*`
modules the other four rows need (measured delta: `148 → 216` `GQ2` modules, driven by the
`Roe.Labute` span stack behind `Words.Mpc`), because that file is the count lane's interface and
CB-4 consumes it.  Everything here is a corollary, so it pays the import cost instead.

## Contents (CB-FR)

* **§1/§2** (CB-TR) the five hypothesis-free presentation instances and the `ω₂`-only inventory.
* **§3** `ResolvesAt` for the three remaining `ω₂`-only certificate families — `mCompactFam`,
  `lSqFam`, `mpcFam` — at the target-chosen resolver `omega2Exp N`; **§3.1** both pins per row
  (`e = 3` at exponent dividing `6`, `e = 1` at every `2`-group).
* **§4** the `IsStokesEndpoint` twins at `e = 1`.  Audit result: every one of the five generic
  endpoint theorems is already generic in `e` under `Odd e` alone, so **no branch's frozen Stokes
  payload is pinned at an unusable `e`** — the `e = 1` forms are corollaries, not re-pins.
* **§5** the procyclic-`N` row.  Its `η̂`-node is a `.profPow` at `etaHatZ η`, not a `z2pow`, so
  what it needs is a *second value of the `ℤ̂`-resolver*: `zpowHat_etaHatZ_zpow` supplies it, and
  `resolvedAt_npcW` walks the word.  **§5.3** is the sharp negative — `ω₂` kills pro-odd elements
  while `η̂` fixes them, so no *constant* resolver survives odd torsion, and at exponent level `6`
  this row has no honest `e` at all.  **§5.4** records that the same node occurs in the
  procyclic-`M` row's `.hat` display.
* **§6** discharges the count lane's standing `orderOf x ∣ 6` from the lower group: the `6` is
  `2` (lift level, `WordLift.orderOf_dvd_two_mul`) times `3` (the tame head's `τ`-order).

## Axiom posture

`sorry`-free, no new axiom, no `decide`; every declaration prints the standard three, except
`not_isOmega2Only_hatDisplay`, which prints the strict subset `[propext]`.
-/

namespace GQ2.Dyadic

namespace Count

open GQ2 GQ2.Dyadic

/-! ## §1 The five instances

The presentation instance is generic in `R` and hypothesis-free, so each frozen branch's instance
is a *specialization and nothing more* — which is the point: with the relators read at the target
there is no per-branch reconciliation left to do.  The five below are the count lane's five rows,
each at its own **intrinsic** branch word, hence at the genuine `Γ_R` of that branch.

⚠ Read against `Count/Resolve.lean`'s `isAdmissible_gammaR_*`, which are the same five statements
at `resolvedRelator e R` — the word with its `ω₂`-nodes replaced by `e`.  Those are presentations
of a **different group** (CB-RES §7/§8 prove `Γ_{resolveWord e R} ≠ Γ_R` by exhibiting an element
nontrivial in one and trivial in the other), and that is exactly why they were the wrong object to
compute at. -/

section Frozen

/-- **Compact `N`** (the `√−2`, `√−1` rows). -/
theorem isAdmissible_gammaR_nCompactW (α h q : ℕ) :
    IsAdmissibleMarkedPresentation
      ((GammaR (2 + 2 * h) q (Words.nCompactW α h)) : Type)
      (gammaGen (2 + 2 * h) q (Words.nCompactW α h))
      (gammaFam (2 + 2 * h) q (Words.nCompactW α h)) (wildAlphabet (2 + 2 * h)) :=
  isAdmissibleMarkedPresentation_gammaR _ _ _

/-- **Procyclic `N`.** -/
theorem isAdmissible_gammaR_npcW (α r h q : ℕ) (d : EtaData) :
    IsAdmissibleMarkedPresentation
      ((GammaR (2 + 2 * h) q (Words.Npc.npcW α r h d)) : Type)
      (gammaGen (2 + 2 * h) q (Words.Npc.npcW α r h d))
      (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d)) (wildAlphabet (2 + 2 * h)) :=
  isAdmissibleMarkedPresentation_gammaR _ _ _

/-- **Compact `M`** (the `√2`, `√5` rows). -/
theorem isAdmissible_gammaR_mCompactW (α h q : ℕ) :
    IsAdmissibleMarkedPresentation
      ((GammaR (2 + 2 * h) q (Words.MCompact.mCompactW α h)) : Type)
      (gammaGen (2 + 2 * h) q (Words.MCompact.mCompactW α h))
      (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h)) (wildAlphabet (2 + 2 * h)) :=
  isAdmissibleMarkedPresentation_gammaR _ _ _

/-- **Procyclic `M`** (the `√−10`, `√10` rows). -/
theorem isAdmissible_gammaR_mpcW (α r pp h q : ℕ) (η : Words.Mpc.EtaDisplay) :
    IsAdmissibleMarkedPresentation
      ((GammaR (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h)) : Type)
      (gammaGen (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h))
      (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h)) (wildAlphabet (2 + 2 * h)) :=
  isAdmissibleMarkedPresentation_gammaR _ _ _

/-- **`L_sq`.** -/
theorem isAdmissible_gammaR_lSqW (h q : ℕ) :
    IsAdmissibleMarkedPresentation
      ((GammaR (2 * h + 1) q (Words.LSq.lSqW h)) : Type)
      (gammaGen (2 * h + 1) q (Words.LSq.lSqW h))
      (gammaFam (2 * h + 1) q (Words.LSq.lSqW h)) (wildAlphabet (2 * h + 1)) :=
  isAdmissibleMarkedPresentation_gammaR _ _ _

/-! ### The `ω₂`-only status of the five, i.e. which rows `resolvesAt_gammaFam` covers

`Count.resolvesAt_heisToFree` needs the branch word to be `ω₂`-only.  Four of the five rows are;
the procyclic-`N` word is **not** (`Words.Npc.not_isOmega2Only_npcW`), because its `η̂`-twist is a
genuine `ℤ₂`-exponent.  Nothing about the presentation changes there — the instance above is
unconditional — but the target-resolution of its *word-lane* family needs a `ℤ₂`-resolver at the
target as well as the `ω₂` one, which is the count lane's remaining word-side item. -/

theorem isOmega2Only_gammaFam_nCompactW (α h q : ℕ) :
    ∀ k, (gammaFam (2 + 2 * h) q (Words.nCompactW α h) k).IsOmega2Only :=
  isOmega2Only_gammaFam _ _ (Words.isOmega2Only_nCompact α h)

theorem isOmega2Only_gammaFam_mCompactW (α h q : ℕ) :
    ∀ k, (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k).IsOmega2Only :=
  isOmega2Only_gammaFam _ _ (Words.MCompact.isOmega2Only_mCompact α h)

theorem isOmega2Only_gammaFam_mpcW (α r pp h q : ℕ) {η : Words.Mpc.EtaDisplay}
    (hη : η.IsOmega2Only) :
    ∀ k, (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h) k).IsOmega2Only :=
  isOmega2Only_gammaFam _ _ (Words.Mpc.isOmega2Only_mpcW α r pp hη h)

theorem isOmega2Only_gammaFam_lSqW (h q : ℕ) :
    ∀ k, (gammaFam (2 * h + 1) q (Words.LSq.lSqW h) k).IsOmega2Only :=
  isOmega2Only_gammaFam _ _ (Words.LSq.isOmega2Only_lSq h)

end Frozen

/-! ## §3 `ResolvesAt` for the certificate families of the four `ω₂`-only rows

`Count/Presentation.lean` §7.5 does the compact-`N` row; the other three `ω₂`-only rows are the
same two steps, because all five `Certificates.*Fam` are **literally** `heisToFree` applied to
`gammaFam` at a constant resolver:

* `*Fam_eq_gammaFam` — the frozen family *is* the `heisToFree` image of the intrinsic family, on
  the nose (both entries by `rfl`, the tame one because `Certificates.tameRelW` is `gammaFam`'s
  first entry by definition);
* `resolvesAt_gammaFam` at `omega2Exp N` — the target-chosen resolver, on an `ω₂`-only word.

⚠ The procyclic-`N` row is **not** here: `Words.Npc.npcW` is not `ω₂`-only, and §5 treats it
separately (and differently — the constant resolver is genuinely constrained there). -/

section TargetResolution

variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]

/-- The frozen compact-`M` family **is** the `heisToFree` image of the intrinsic family. -/
theorem mCompactFam_eq_gammaFam (α h q e : ℕ) :
    Certificates.MCompact.mCompactFam α h q e
      = fun k => heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
        (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h) k) := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

/-- **The compact-`M` family resolves the relators of `Γ_R` at the intrinsic branch word**, at
every target killed by `N`, when the resolver is `omega2Exp N`. -/
theorem resolvesAt_mCompactFam {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N) (α h q : ℕ) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h))
      (Certificates.MCompact.mCompactFam α h q (omega2Exp N)) Q := by
  rw [mCompactFam_eq_gammaFam]
  exact resolvesAt_gammaFam hN hord _ _ (Words.MCompact.isOmega2Only_mCompact α h)

/-- The frozen `L_sq` family **is** the `heisToFree` image of the intrinsic family. -/
theorem lSqFam_eq_gammaFam (h q e : ℕ) :
    Certificates.LSqStokes.lSqFam h q e
      = fun k => heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
        (gammaFam (2 * h + 1) q (Words.LSq.lSqW h) k) := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

/-- **The `L_sq` family resolves the relators of `Γ_R` at the intrinsic branch word.** -/
theorem resolvesAt_lSqFam {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N) (h q : ℕ) :
    ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q (omega2Exp N)) Q := by
  rw [lSqFam_eq_gammaFam]
  exact resolvesAt_gammaFam hN hord _ _ (Words.LSq.isOmega2Only_lSq h)

/-- The frozen procyclic-`M` family **is** the `heisToFree` image of the intrinsic family. -/
theorem mpcFam_eq_gammaFam (α r pp h q e : ℕ) (η : Words.Mpc.EtaDisplay) :
    Certificates.MProcyclic.mpcFam α r pp h q e η
      = fun k => heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
        (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h) k) := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

/-- **The procyclic-`M` family resolves the relators of `Γ_R` at the intrinsic branch word**, for
every `ω₂`-only `η̂`-display.  (`Words.Mpc.EtaDisplay.IsOmega2Only` is the display-level condition
that the `η̂`-slot is spelled by `ω₂`-powers; the `.one` display of the frozen `√±10` pins
satisfies it, and that is the difference from the procyclic-`N` row of §5.) -/
theorem resolvesAt_mpcFam {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (α r pp h q : ℕ) {η : Words.Mpc.EtaDisplay} (hη : η.IsOmega2Only) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h))
      (Certificates.MProcyclic.mpcFam α r pp h q (omega2Exp N) η) Q := by
  rw [mpcFam_eq_gammaFam]
  exact resolvesAt_gammaFam hN hord _ _ (Words.Mpc.isOmega2Only_mpcW α r pp hη h)

/-! ### §3.1 The two pins, per row

`Count/Presentation.lean` §7.5 pins the compact-`N` row twice — at `omega2Exp 6 = 3` and at
`omega2Exp (2 ^ a) = 1` — and flags that **which one the count lane may use is decided by the
counting target, not by the branch**.  The same two pins for the other three `ω₂`-only rows are
below, so that the choice is available uniformly and no row has to be re-derived when the target
is settled.

Read `Count/Resolve.lean` §7 alongside: its refutations of the *global* statement at the frozen
`e = 3` land in `ℤ/8` and `ℤ/4`, i.e. at `2`-groups, which is exactly the regime where
`omega2Exp = 1 ≠ 3`.  Nothing here contradicts them — these are statements at one target. -/

/-- Compact `M` at `e = 3`: honest at every target of exponent dividing `6`. -/
theorem resolvesAt_mCompactFam_three (hord : ∀ x : Q, orderOf x ∣ 6) (α h q : ℕ) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h))
      (Certificates.MCompact.mCompactFam α h q 3) Q := by
  have h := resolvesAt_mCompactFam (N := 6) (by norm_num) hord α h q
  rwa [omega2Exp_six] at h

/-- **Compact `M` at `e = 1`: honest at every `2`-group target.** -/
theorem resolvesAt_mCompactFam_one {a : ℕ} (ha : a ≠ 0) (hord : ∀ x : Q, orderOf x ∣ 2 ^ a)
    (α h q : ℕ) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.MCompact.mCompactW α h))
      (Certificates.MCompact.mCompactFam α h q 1) Q := by
  have h := resolvesAt_mCompactFam (N := 2 ^ a) (Nat.two_pow_pos a).ne' hord α h q
  rwa [omega2Exp_two_pow ha] at h

/-- `L_sq` at `e = 3`. -/
theorem resolvesAt_lSqFam_three (hord : ∀ x : Q, orderOf x ∣ 6) (h q : ℕ) :
    ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q 3) Q := by
  have hr := resolvesAt_lSqFam (N := 6) (by norm_num) hord h q
  rwa [omega2Exp_six] at hr

/-- **`L_sq` at `e = 1`.**  This is the row whose frozen Stokes pin already sits at `e = 1`
(`Certificates.LSqStokes.qFour_isStokesEndpoint` is `IsStokesEndpoint (lSqFam 0 4 1)`), so for
`L_sq` the resolver pin and the Stokes pin already agree at the `2`-group value. -/
theorem resolvesAt_lSqFam_one {a : ℕ} (ha : a ≠ 0) (hord : ∀ x : Q, orderOf x ∣ 2 ^ a) (h q : ℕ) :
    ResolvesAt (gammaFam (2 * h + 1) q (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q 1) Q := by
  have hr := resolvesAt_lSqFam (N := 2 ^ a) (Nat.two_pow_pos a).ne' hord h q
  rwa [omega2Exp_two_pow ha] at hr

/-- Procyclic `M` at `e = 3`. -/
theorem resolvesAt_mpcFam_three (hord : ∀ x : Q, orderOf x ∣ 6) (α r pp h q : ℕ)
    {η : Words.Mpc.EtaDisplay} (hη : η.IsOmega2Only) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h))
      (Certificates.MProcyclic.mpcFam α r pp h q 3 η) Q := by
  have hr := resolvesAt_mpcFam (N := 6) (by norm_num) hord α r pp h q hη
  rwa [omega2Exp_six] at hr

/-- **Procyclic `M` at `e = 1`.** -/
theorem resolvesAt_mpcFam_one {a : ℕ} (ha : a ≠ 0) (hord : ∀ x : Q, orderOf x ∣ 2 ^ a)
    (α r pp h q : ℕ) {η : Words.Mpc.EtaDisplay} (hη : η.IsOmega2Only) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Mpc.mpcW α r pp η h))
      (Certificates.MProcyclic.mpcFam α r pp h q 1 η) Q := by
  have hr := resolvesAt_mpcFam (N := 2 ^ a) (Nat.two_pow_pos a).ne' hord α r pp h q hη
  rwa [omega2Exp_two_pow ha] at hr

end TargetResolution

/-! ## §4 The Stokes payload at the `e = 1` pin

⚠ **Audit item.**  A branch's `hres`, `hd` and `hend` must all be read at *one* `e`: `hZcardN`
and `tcocycle_cardN` take `ResolvesAt W w Q`, `StokesDuality c w V` and `IsStokesEndpoint w` at
the same family `w`.  Eight of the campaign's nine frozen Stokes pins sit at `e = 3`
(`sqrtNegTwo_`, `sqrtTwo_`, `sqrtFive_`, `sqrtNeg10_`, `sqrt10_`, `npcPin_`, `qTwo_`), and one at
`e = 1` (`qFour_isStokesEndpoint`, `lSqFam 0 4 1`).  So if the counting target is a `2`-group,
where §3.1's `e = 1` pins are the honest ones, the `e = 3` Stokes pins are stated at a family the
resolver cannot use.

That is **not** a defect in the Stokes lane: every one of the five generic endpoint theorems is
already generic in `e` under `Odd e` alone, and `1` is odd.  So the `e = 1` twins below are
*corollaries of the frozen generic theorems*, obtained by supplying `Odd 1` in place of `Odd 3` —
nothing is re-proved and no frozen declaration is re-pinned.  They are recorded here so that the
count lane can take a matched `(hres, hend)` pair at either pin without touching a `Certificates`
file. -/

section StokesAtOne

open GQ2.Dyadic.Certificates

/-- Compact `N` at `e = 1` — the `e = 1` twin of `sqrtNegTwo_isStokesEndpoint`. -/
theorem nCompact_isStokesEndpoint_one {α h q : ℕ} (hα : 1 ≤ α) (hq : Even q) :
    IsStokesEndpoint (nCompactFam α h q 1) :=
  nCompact_isStokesEndpoint hα hq odd_one

/-- Compact `M` at `e = 1` — the twin of `sqrtTwo_`/`sqrtFive_isStokesEndpoint`. -/
theorem mCompact_isStokesEndpoint_one {α h q : ℕ} (hq : Even q) :
    IsStokesEndpoint (MCompact.mCompactFam α h q 1) :=
  MCompact.mCompact_isStokesEndpoint hq odd_one

/-- `L_sq` at `e = 1` — this one the campaign already froze, at `lSqFam 0 4 1`. -/
theorem lSq_isStokesEndpoint_one {h q : ℕ} (hq : Even q) :
    IsStokesEndpoint (LSqStokes.lSqFam h q 1) :=
  LSqStokes.lSq_isStokesEndpoint hq odd_one

/-- Procyclic `M` at `e = 1` — the twin of `sqrtNeg10_`/`sqrt10_isStokesEndpoint`. -/
theorem mpc_isStokesEndpoint_one {α r pp h q : ℕ} {η : Words.Mpc.EtaDisplay} (hα : 1 ≤ α)
    (hq : Even q) : IsStokesEndpoint (MProcyclic.mpcFam α r pp h q 1 η) :=
  MProcyclic.mpc_isStokesEndpoint hα hq odd_one

/-- Procyclic `N` at `e = 1` — the twin of `npcPin_isStokesEndpoint`.  The Stokes payload of this
row is available at `e = 1` exactly as the other four are; §5 is about the *resolver*, which is
where this row genuinely differs. -/
theorem npc_isStokesEndpoint_one {α r h q : ℕ} (hα : 1 ≤ α) (hq : Even q) (d : EtaData) :
    IsStokesEndpoint (Npc.npcFam α r h q 1 d) :=
  Npc.npc_isStokesEndpoint hα hq odd_one d

end StokesAtOne

/-! ## §5 The procyclic-`N` row: the second resolver

`Words.Npc.not_isOmega2Only_npcW` puts this row outside §3's route.  The obstruction is a single
node — the conjugator `A = σ^{η̂}` of `Words.Npc.aW`, a `.profPow` at `d.toZhat = etaHatZ η`,
which `Words.Npc.etaHatZ_ne_omega2` separates from `ω₂` for **every** `η`.  There is no `z2pow`
node anywhere in `npcW`; the `ℤ₂`-exponent enters `ℤ̂` through the splitting
`padicOmega2 : ℤ₂ ↪ ℤ̂`, so what the row needs is a **second value of the `ℤ̂`-resolver `E`**, not
a value of `E₂`.  Otherwise CB-TR's principle applies verbatim: at a target of exponent level `N`,

* `E ω₂ = omega2Exp N` (`GQ2.zpowHat_omega2_zpow`), and
* `E η̂ = 1 + padicOmega2Exp (η − 1) N` (`zpowHat_etaHatZ_zpow` below),

both functions of the target alone.  §5.1 records the walk, §5.2 the consequence for the
**frozen** family, and §5.3 the sharp negative: `Certificates.Npc.npcFam` resolves the two nodes
with the *same constant* `e`, so it is honest only where those two levels coincide. -/

section Procyclic

open GQ2.Dyadic.Certificates Words.Npc

/-! ### §5.1 The `η̂`-resolver at a level, and the walk over `npcW` -/

variable {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **The `ℤ₂`-exponent resolver at a level** — the `padicOmega2` analogue of
`GQ2.zpowHat_omega2_zpow`: on a target killed by `N`, `x ^ᶻ (z·ω₂)` is the honest integer power
`x ^ padicOmega2Exp z N`, an exponent depending on the target and not on `x`. -/
theorem zpowHat_padicOmega2_zpow {N : ℕ} (hN : N ≠ 0) {x : P} (hx : orderOf x ∣ N) (z : ℤ_[2]) :
    x ^ᶻ padicOmega2 z = x ^ padicOmega2Exp z N := by
  rw [zpowHat_padicOmega2]
  exact (pow_eq_pow_iff_modEq.mpr (padicOmega2Exp_modEq hx hN z)).symm

/-- **The `η̂`-resolver at a level**: `x ^ᶻ η̂ = x ^ (1 + padicOmega2Exp (η − 1) N)`.  This is the
procyclic-`N` row's second resolver value, and it is what CB-TR's target-dependent principle
produces at an `η̂`-node. -/
theorem zpowHat_etaHatZ_zpow {N : ℕ} (hN : N ≠ 0) {x : P} (hx : orderOf x ∣ N) (η : ℤ_[2]) :
    x ^ᶻ etaHatZ η = x ^ (1 + padicOmega2Exp (η - 1) N) := by
  rw [etaHatZ, zpowHat_mul, zpowHat_ofInt, zpow_one, zpowHat_padicOmega2_zpow hN hx,
    pow_add, pow_one]

section Walk

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- `PWord.prodList` of resolved words is resolved — the `ResolvedAt` twin of
`Words.isOmega2Only_prodList`. -/
theorem resolvedAt_prodList (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    ∀ {l : List (PWord X)}, (∀ w ∈ l, PWord.ResolvedAt μ E E₂ w) →
      PWord.ResolvedAt μ E E₂ (PWord.prodList l)
  | [], _ => trivial
  | w :: _ws, hw =>
      ⟨hw w (List.mem_cons_self ..),
       resolvedAt_prodList μ E E₂ fun u hu => hw u (List.mem_cons_of_mem _ hu)⟩

variable {h : ℕ} {d : EtaData} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
  (μ : Generator (2 + 2 * h) → G)
  (hω : ∀ x : G, x ^ᶻ omega2 = x ^ E omega2)
  (hη : ∀ x : G, x ^ᶻ d.toZhat = x ^ E d.toZhat)

include hη in
/-- The conjugator `A = σ^{η̂}` is resolved exactly when `E` is correct at `η̂`. -/
theorem resolvedAt_aW : PWord.ResolvedAt μ E E₂ (aW h d) := ⟨trivial, hη _⟩

include hω in
/-- `δ₀` is `ω₂`-only, so `E ω₂` alone resolves it. -/
theorem resolvedAt_deltaZeroW : PWord.ResolvedAt μ E E₂ (deltaZeroW h) := by
  refine resolvedAt_prodList μ E E₂ ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨resolvedAt_prodList μ E E₂ (by intro u hu; fin_cases hu <;> exact trivial), hω _⟩
  · exact trivial

include hω hη in
/-- The compressed `D`-block: `δ₀`-copies at `ω₂`, conjugators at `η̂` and at a `ℤ`-power. -/
theorem resolvedAt_dBlockW (r : ℕ) : PWord.ResolvedAt μ E E₂ (dBlockW h r d) := by
  have hδ : PWord.ResolvedAt μ E E₂ (deltaZeroW h) := resolvedAt_deltaZeroW μ hω
  have hA : PWord.ResolvedAt μ E E₂ (aW h d) := resolvedAt_aW μ hη
  refine resolvedAt_prodList μ E E₂ ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · exact ⟨hδ, hA⟩
  · exact ⟨resolvedAt_prodList μ E E₂ (by
      intro u hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hδ
      · exact ⟨hδ, hA⟩), trivial⟩

include hω hη in
/-- **The procyclic-`N` word is resolved by a resolver correct at `ω₂` and at `η̂`.**

This is the row's whole word-side content: `npcW`'s six factors use exactly two profinite
exponents, and no `ℤ₂`-exponent node at all, so two values of `E` suffice.  Compare
`Count/Resolve.lean`'s `not_resolvedAt_npcW`, which is the *same word at the free profinite
marking*, where no pair of values works — the difference is entirely that `P` here is finite. -/
theorem resolvedAt_npcW (α r : ℕ) : PWord.ResolvedAt μ E E₂ (npcW α r h d) := by
  refine resolvedAt_prodList μ E E₂ ?_
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact trivial
  · exact ⟨trivial, resolvedAt_aW μ hη⟩
  · exact ⟨trivial, resolvedAt_prodList μ E E₂ (by intro u hu; fin_cases hu <;> exact trivial)⟩
  · exact ⟨resolvedAt_prodList μ E E₂ (by intro u hu; fin_cases hu <;> exact trivial), hω _⟩
  · exact ⟨resolvedAt_dBlockW μ hω hη r, trivial⟩
  · exact PWord.resolvedAt_of_isOmega2Only μ E E₂ hω _ (Words.isOmega2Only_handlesW h)

end Walk

/-! ### §5.2 The frozen family, and the constraint the constant resolver imposes

`Certificates.Npc.npcFam α r h q e d` resolves **both** profinite exponents by the *same* constant
`e`.  So where §3's rows needed one arithmetic identity (`omega2Exp N = e`), this row needs two,
and they are identities about different things: `e` has to be simultaneously the `ω₂`-level and
the `η̂`-level of the target. -/

variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]

/-- The frozen procyclic-`N` family **is** the `heisToFree` image of the intrinsic family. -/
theorem npcFam_eq_gammaFam (α r h q e : ℕ) (d : EtaData) :
    Npc.npcFam α r h q e d
      = fun k => heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
        (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d) k) := by
  funext k
  match k with
  | 0 => rfl
  | 1 => rfl

/-- **`ResolvedAt` at every marking gives `ResolvesAt`** — the general bridge behind
`Count.resolvesAt_heisToFree`, with the `ω₂`-only hypothesis replaced by the resolution itself.
This is what lets a row outside the `ω₂`-only fragment still reach `ResolvesAt`. -/
theorem resolvesAt_of_resolvedAt {ι ρ : Type*} {W : ρ → PWord ι} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    (hres : ∀ (f : ι → Q) (k : ρ), PWord.ResolvedAt f E E₂ (W k)) :
    ResolvesAt W (fun k => heisToFree E E₂ (W k)) Q := by
  intro f k
  rw [← evalZ_eq_lift_heisToFree f E E₂ (W k)]
  exact (PWord.eval_eq_evalZ f E E₂ (W k) (hres f k)).symm

/-- **The procyclic-`N` family resolves the relators of `Γ_R` at the intrinsic branch word**, at
any target killed by `N`, provided the frozen constant `e` is *both* resolver levels of that
target: the `ω₂`-level `omega2Exp N` and the `η̂`-level `1 + padicOmega2Exp (η − 1) N`.

The second hypothesis is the whole difference from `Count.resolvesAt_nCompactFam`, and it is not
vacuous: §5.3 exhibits targets where the two levels provably disagree. -/
theorem resolvesAt_npcFam {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (α r h q : ℕ) (d : EtaData) {e : ℕ} (hω : omega2Exp N = e)
    (hη : 1 + padicOmega2Exp (d.toPadic - 1) N = e) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d))
      (Npc.npcFam α r h q e d) Q := by
  rw [npcFam_eq_gammaFam]
  refine resolvesAt_of_resolvedAt ?_
  have hωx : ∀ x : Q, x ^ᶻ omega2 = x ^ ((e : ℤ)) := by
    intro x
    rw [PWord.zpowHat_omega2_zpow hN (hord x), hω]
  have hηx : ∀ x : Q, x ^ᶻ d.toZhat = x ^ ((e : ℤ)) := by
    intro x
    rw [EtaData.toZhat, zpowHat_etaHatZ_zpow hN (hord x), hη, zpow_natCast]
  intro f k
  match k with
  | 0 => exact PWord.resolvedAt_of_isOmega2Only f _ _ hωx _ (isOmega2Only_tameRelW _ q)
  | 1 => exact resolvedAt_npcW f hωx hηx α r

/-- **The procyclic-`N` row at the `e = 1` pin, on a `2`-group target.**

`omega2Exp (2 ^ a) = 1` supplies the `ω₂` level; the `η̂` level is `1` exactly when
`padicOmega2Exp (η − 1) (2 ^ a) = 0`, i.e. when `η ≡ 1 (mod 2^a)`.  That congruence is a genuine
condition on the branch datum at `a ≥ 2` — see `resolvesAt_npcFam_one_of_exponent_two` for the
case where it is automatic. -/
theorem resolvesAt_npcFam_one {a : ℕ} (ha : a ≠ 0) (hord : ∀ x : Q, orderOf x ∣ 2 ^ a)
    (α r h q : ℕ) (d : EtaData) (hd : padicOmega2Exp (d.toPadic - 1) (2 ^ a) = 0) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d))
      (Npc.npcFam α r h q 1 d) Q :=
  resolvesAt_npcFam (Nat.two_pow_pos a).ne' hord α r h q d (omega2Exp_two_pow ha) (by rw [hd])

/-- **At an exponent-`2` target the `e = 1` pin is unconditional**, for every `2`-adic unit `η`
that is a `1`-unit: `v₂(2) = 1`, so `Fox`'s `padicOmega2Exp_eta_eq_zero` kills the `η̂` level
whatever `η` is.  This is the elementary-abelian case, i.e. the `A`-coordinate of the count
lane's split target read on its own. -/
theorem resolvesAt_npcFam_one_of_exponent_two (hord : ∀ x : Q, orderOf x ∣ 2)
    (α r h q : ℕ) (d : EtaData) (z : ℤ_[2]) (hz : d.toPadic = 1 + 2 * z) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d))
      (Npc.npcFam α r h q 1 d) Q := by
  have hfac : (2 : ℕ).factorization 2 = 1 := Nat.Prime.factorization_self Nat.prime_two
  refine resolvesAt_npcFam (N := 2) two_ne_zero hord α r h q d ?_ ?_
  · simp [omega2Exp, hfac]
  · rw [padicOmega2Exp_eta_eq_zero z hz (le_of_eq hfac)]

/-! ### §5.3 The sharp negative: no constant resolver survives odd torsion

CB-RES's impossibility is global — no integer resolves `ω₂` in the *free profinite group*.  The
procyclic-`N` row has a second, strictly local obstruction of the same flavour, and it is what
makes this row genuinely different from the other four rather than merely longer:

`ω₂` **kills** pro-odd elements (Gate B rule T1) while `η̂` **fixes** them (rule T2).  So at any
target carrying a nontrivial element of odd order the two exponents are separated — this is
`Words.Npc.etaHatZ_ne_omega2`'s argument, read as a statement about resolvers — and a family that
spends a *single* constant on both cannot be honest there, at any value of the constant. -/

/-- **No constant resolves both `ω₂` and `η̂` at an element of odd order `> 1`.**

Hence `Certificates.Npc.npcFam α r h q e d` — which resolves both nodes at the same `e` — cannot
resolve `Words.Npc.npcW` at any target with nontrivial odd torsion, for **any** `e`.  Contrast
the other four rows, where every target admits the honest constant `omega2Exp N`. -/
theorem not_constant_resolver_of_odd {x : P} (hodd : Odd (orderOf x)) (hx : x ≠ 1) (η : ℤ_[2])
    (k : ℤ) : ¬ (x ^ᶻ omega2 = x ^ k ∧ x ^ᶻ etaHatZ η = x ^ k) := by
  rintro ⟨h1, h2⟩
  rw [← zpowHat_padicOmega2_one, zpowHat_padicOmega2_eq_one_of_odd hodd] at h1
  rw [zpowHat_etaHatZ_of_odd hodd] at h2
  exact hx (h2.trans h1.symm)

/-- **The `e = 3` pin is unavailable to the procyclic-`N` row.**  At exponent level `6` the `ω₂`
level is `3` (`Count.omega2Exp_six`) while the `η̂` level is `1` for every `1`-unit `η`, because
`v₂(6) = 1`.  So `resolvesAt_npcFam`'s two hypotheses are contradictory at `N = 6`: the row that
the campaign froze at `e = 3` alongside the other four has no `e` at all there.

This is the precise sense in which the procyclic-`N` row's resolver pin is *not* a free choice
between `3` and `1`: on a target of exponent `6` it is neither. -/
theorem npc_levels_ne_at_six {η : ℤ_[2]} (z : ℤ_[2]) (hη : η = 1 + 2 * z) :
    omega2Exp 6 ≠ 1 + padicOmega2Exp (η - 1) 6 := by
  have hfac : (6 : ℕ).factorization 2 = 1 := by
    rw [show (6 : ℕ) = 2 ^ 1 * 3 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  rw [omega2Exp_six, padicOmega2Exp_eta_eq_zero z hη (le_of_eq hfac)]
  norm_num

/-! ### §5.4 ⚠ The `η̂`-obstruction is not confined to the procyclic-`N` row

`Words.Mpc.EtaDisplay` has three constructors and `IsOmega2Only` is `False` on exactly one of
them, `.hat num den` — whose denoted exponent is, on the nose, the *same* `η̂` node as
`Words.Npc.aW`'s.  So §3's `resolvesAt_mpcFam` excludes the `.hat` display for the same reason
§3 excludes the procyclic-`N` row, and §5's two-level treatment is what that display needs.

**This does not block the count lane today**: the campaign's frozen procyclic-`M` Stokes pins
(`Certificates.MProcyclic.sqrtNeg10_isStokesEndpoint`, `sqrt10_isStokesEndpoint`) both use the
`.one` display, on which `IsOmega2Only` is `trivial`, so `resolvesAt_mpcFam` covers them.  But the
`.hat` display is a certified word of the row (`Words/Mpc.lean`'s `etahat display` ast-hash pin),
and for it the row is **not** covered — closing that is a `ResolvedAt` walk over `mpcW`, the
mpc-side twin of §5.1's walk over `npcW`. -/

/-- The `.hat` display denotes the very same `η̂` exponent as the procyclic-`N` conjugator. -/
theorem mpc_hatDisplay_zhat (num den : ℤ) :
    (Words.Mpc.EtaDisplay.hat num den).zhat = EtaData.toZhat ⟨num, den⟩ := rfl

/-- Hence it is never `ω₂`, at any `num`, `den` — so `§3`'s route is unavailable there, and
`not_constant_resolver_of_odd` applies to it verbatim. -/
theorem mpc_hatDisplay_ne_omega2 (num den : ℤ) :
    (Words.Mpc.EtaDisplay.hat num den).zhat ≠ omega2 :=
  Words.Npc.toZhat_ne_omega2 _

/-- And `IsOmega2Only` is definitionally `False` there — the exclusion `resolvesAt_mpcFam`'s `hη`
performs, made explicit. -/
theorem not_isOmega2Only_hatDisplay (num den : ℤ) :
    ¬ (Words.Mpc.EtaDisplay.hat num den).IsOmega2Only := id

/-- **The procyclic-`N` row has no constant pin at exponent level `6`** — the two hypotheses of
`resolvesAt_npcFam` are jointly unsatisfiable there, at every `e`.

This is the actionable form of §5.3 for the count lane, because `6` is the level the count lane
has actually committed to (`Count/Presentation.lean`'s two standing `orderOf x ∣ 6` hypotheses).
At that level the other four rows take `e = omega2Exp 6 = 3`; this row takes nothing.  Its
options are exactly two: move the row to a `2`-group target and use `resolvesAt_npcFam_one`, or
give `Certificates.Npc.npcFam` a *two-valued* resolver — `resolvesAt_of_resolvedAt` together with
`resolvedAt_npcW` already supports the latter, at the honest pair
`(omega2Exp N, 1 + padicOmega2Exp (η − 1) N)`. -/
theorem no_constant_pin_npcFam_at_six {η : ℤ_[2]} (z : ℤ_[2]) (hη : η = 1 + 2 * z) (e : ℕ) :
    ¬ (omega2Exp 6 = e ∧ 1 + padicOmega2Exp (η - 1) 6 = e) := by
  rintro ⟨h1, h2⟩
  exact npc_levels_ne_at_six z hη (h1.trans h2.symm)

end Procyclic

/-! ## §6 Discharging the count lane's standing exponent hypothesis

`Count/Presentation.lean`'s `sqrtNegTwo_*_gammaR_nCompact` carry `orderOf x ∣ 6` at the split
target as an **undischarged hypothesis**, and every `resolvesAt_*` above consumes exactly that
shape.  The lift-level lemma discharges it from a statement about the *lower* group alone:
`Additive ↥D.T` is `2`-torsion (`Count.radT_add_self`), so
`GQ2.Dyadic.WordLift.orderOf_dvd_two_mul` gives `orderOf x ∣ 2 · N` for any `N` killing
`Bg ⧸ D.M`.

⚠ The `6` is therefore **`2 · 3`, not a `2`-power**: the factor `2` is the lift level and the
factor `3` is the lower group's.  `Bg ⧸ D.M` is not a `2`-group in the campaign's frame — it
surjects onto the finite tame head, whose `τ`-image has odd order
(`GQ2.Dyadic.TameQ.odd_order`) — so CB-TR's alternative "if `C` is a `2`-group the target is one
too" is *not* the case the count lane is in, and `e = 3` is the honest pin for the four
`ω₂`-only rows.  Which is precisely why §5.3 bites: at that same target the procyclic-`N` row has
no constant pin at all. -/

section LiftLevel

open GQ2.FoxH GQ2.SectionEight GQ2.SectionEight.AffineTLift

variable {Bg : Type} [Group Bg] [Finite Bg]

/-- **The count lane's `hord`, from the lower group.**  Over the `2`-torsion coefficient module
`Additive ↥D.T`, every element of the split target is killed by `2 · N` as soon as the lower
group is killed by `N`. -/
theorem orderOf_wordLift_radT_dvd (D : RadicalCoverData Bg) {N : ℕ}
    (hbase : ∀ g : Bg ⧸ D.M, orderOf g ∣ N) (x : WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :
    orderOf x ∣ 2 * N :=
  WordLift.orderOf_dvd_two_mul (radT_add_self D) hbase x

/-- **`orderOf x ∣ 6` at the split target, from `orderOf g ∣ 3` at the lower group** — the exact
hypothesis `Count/Presentation.lean`'s pilot theorems leave open, reduced to the tame head's
`τ`-order.  This is the `e = 3` regime of `resolvesAt_nCompactFam_three`. -/
theorem orderOf_wordLift_radT_dvd_six (D : RadicalCoverData Bg)
    (hbase : ∀ g : Bg ⧸ D.M, orderOf g ∣ 3) (x : WordLift (Additive ↥D.T) (Bg ⧸ D.M)) :
    orderOf x ∣ 6 := by simpa using orderOf_wordLift_radT_dvd D hbase x

/-- The `V`-side twin, over `DD.Vmod = M/T`. -/
theorem orderOf_wordLift_vmod_dvd {D : RadicalCoverData Bg} (DD : DescData D)
    {E : Type} [Group E] [DistribMulAction E DD.Vmod] {N : ℕ}
    (hbase : ∀ g : E, orderOf g ∣ N) (x : WordLift DD.Vmod E) :
    orderOf x ∣ 2 * N :=
  WordLift.orderOf_dvd_two_mul (vmod_add_self DD) hbase x

end LiftLevel

/-! ## §7 The two-valued resolver, and the procyclic-`N` row without side conditions

§5.3 leaves the procyclic-`N` row with two options and shows the first one — "move the row to a
`2`-group target" — is unavailable to the count lane, because §6 shows the counting target is
`2 · 3`-torsion and not a `2`-group.  This section takes the second: **give the row a resolver
with two values**, one per profinite exponent node of `npcW`.

The point is that `Certificates.Npc.npcFam`'s `E = fun _ ↦ e` is the only thing that was ever
constrained.  `npcW` has exactly two `ℤ̂`-exponents, `ω₂` and `η̂`, and *no* `ℤ₂`-exponent node at
all; §5.1's `resolvedAt_npcW` already asks for nothing but a resolver correct at those two.  So
the honest object is `E = npcResolver N d`, and with it §5.2's two arithmetic hypotheses **both
disappear**: `resolvesAt_npcFamOf` carries exactly `hN` and `hord`, the same two hypotheses
`Count.resolvesAt_gammaFam` carries for the four `ω₂`-only rows, and no more.  In particular
there is no `2`-group restriction and no `η ≡ 1 (mod 2^a)` congruence.

§5.3's two negatives are untouched and still bound what may be claimed: they are statements about
*constant* resolvers, and `npcResolver N d` is not constant — `npcResolver_ne_const` records that
this is exactly how the row escapes them, at the very targets where `not_constant_resolver_of_odd`
bites. -/

section TwoValued

open GQ2.Dyadic.Certificates Words.Npc

/-! ### §7.1 The resolver

Two values, and the `ℤ̂`-elements they sit at are distinct for every `η`
(`Words.Npc.toZhat_ne_omega2`), so the definition by cases is well posed and both projections are
`rfl`-level. -/

/-- **The procyclic-`N` row's `ℤ̂`-resolver at level `N`** — CB-FR's two values, assembled:
`omega2Exp N` at `ω₂` and `1 + padicOmega2Exp (η − 1) N` at `η̂`.  Both are functions of the target
level `N` and the branch datum alone, which is CB-TR's target-dependence principle applied twice
rather than once.

The value away from the two nodes is irrelevant — `npcW` has no other profinite exponent — and is
taken to be the `η̂` one so that the definition needs a single decision. -/
noncomputable def npcResolver (N : ℕ) (d : EtaData) (γ : Zhat) : ℤ :=
  @ite _ (γ = omega2) (Classical.propDecidable _) (omega2Exp N : ℤ)
    ((1 + padicOmega2Exp (d.toPadic - 1) N : ℕ) : ℤ)

@[simp] theorem npcResolver_omega2 (N : ℕ) (d : EtaData) :
    npcResolver N d omega2 = (omega2Exp N : ℤ) := if_pos rfl

@[simp] theorem npcResolver_toZhat (N : ℕ) (d : EtaData) :
    npcResolver N d d.toZhat = ((1 + padicOmega2Exp (d.toPadic - 1) N : ℕ) : ℤ) :=
  if_neg (Words.Npc.toZhat_ne_omega2 d)

/-! ### §7.2 The family at a general resolver, and the resolution with no side condition -/

variable {Q : Type} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q] [Finite Q]

/-- **The procyclic-`N` family at an arbitrary resolver pair.**  `Certificates.Npc.npcFam` is the
constant instance (`npcFamOf_const`, by `rfl`), so this is a generalization of the frozen family
and not a competitor to it: everything below specializes back. -/
noncomputable def npcFamOf (α r h q : ℕ) (d : EtaData) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  fun k => heisToFree E E₂ (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d) k)

@[simp] theorem npcFamOf_zero (α r h q : ℕ) (d : EtaData) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    npcFamOf α r h q d E E₂ 0 = heisToFree E E₂ (tameRelW (2 + 2 * h) q) := rfl

@[simp] theorem npcFamOf_one (α r h q : ℕ) (d : EtaData) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    npcFamOf α r h q d E E₂ 1 = heisToFree E E₂ (Words.Npc.npcW α r h d) := rfl

/-- The frozen family is the constant instance. -/
theorem npcFamOf_const (α r h q e : ℕ) (d : EtaData) :
    npcFamOf α r h q d (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) = Npc.npcFam α r h q e d :=
  (npcFam_eq_gammaFam α r h q e d).symm

/-- **The procyclic-`N` row resolves at every target killed by `N`, with no side condition.**

This is the row's ticket into the count lane, and the exact analogue of
`Count.resolvesAt_gammaFam` for a word that is not `ω₂`-only: same two hypotheses (`N ≠ 0` and
`hord`), same shape of conclusion, nothing extra.  Compare `resolvesAt_npcFam`, which needs `e` to
be simultaneously both levels of the target — a demand §5.3 shows is unsatisfiable at the count
lane's own level `6`. -/
theorem resolvesAt_npcFamOf {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : Q, orderOf x ∣ N)
    (α r h q : ℕ) (d : EtaData) (E₂ : ℤ_[2] → ℤ) :
    ResolvesAt (gammaFam (2 + 2 * h) q (Words.Npc.npcW α r h d))
      (npcFamOf α r h q d (npcResolver N d) E₂) Q := by
  refine resolvesAt_of_resolvedAt ?_
  have hωx : ∀ x : Q, x ^ᶻ omega2 = x ^ npcResolver N d omega2 := by
    intro x
    rw [npcResolver_omega2, PWord.zpowHat_omega2_zpow hN (hord x), zpow_natCast]
  have hηx : ∀ x : Q, x ^ᶻ d.toZhat = x ^ npcResolver N d d.toZhat := by
    intro x
    rw [npcResolver_toZhat, EtaData.toZhat, zpowHat_etaHatZ_zpow hN (hord x), zpow_natCast]
  intro f k
  match k with
  | 0 => exact PWord.resolvedAt_of_isOmega2Only f _ _ hωx _ (isOmega2Only_tameRelW _ q)
  | 1 => exact resolvedAt_npcW f hωx hηx α r

end TwoValued

end Count

end GQ2.Dyadic
