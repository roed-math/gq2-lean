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
# The five frozen branch families, presented at their intrinsic words (ticket CB-TR)

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

## Axiom posture

`sorry`-free, no new axiom, no `decide`; every declaration prints the standard three.
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

end Procyclic

end Count

end GQ2.Dyadic
