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

end TargetResolution

end Count

end GQ2.Dyadic
