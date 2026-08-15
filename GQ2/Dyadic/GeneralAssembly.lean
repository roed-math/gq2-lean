/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Main

/-!
# The general-degree assembly statement  (dyadic campaign, lane W75-STATE)

`GQ2/Dyadic/Main.lean` states the campaign's final theorem
(`ramifiedI_candidate_equiv_galK`) over the **frozen quadratic table**: five rows, all at
`n = 2`, all at handle count `h = 0`, all at `α ≥ 2`.  The campaign's actual goal is the
`n`-free statement.  This module states that goal, so that the distance between the committed
tree and the goal is a checkable Lean object rather than prose.

## What is and is not claimed here

**Nothing in this module proves the general theorem.**  The general theorem is *stated*, and
its obligations are *named record fields*.  The one thing that is proved outright is the
assembly step: that the obligations, once supplied, compose to the conclusion
(`genAsm_candidate_equiv_galK`).  That is exactly the status of `Main.lean` §6's
`candidate_equiv_galK_of_frozenRow_certificates` at the quadratic slot, lifted off `n = 2`.

The honest reading of every `structure` below: a field is an obligation the campaign owes, or
a selector that places `K` on the family member.  §2 separates the two, following
`docs/dyadic/w74-critical-path.md` §3's preliminary, which is the reason the separation exists:

> "Close every record at every ramified-`i` `K`" is not achievable, and should not be a goal.
> The records are not all obligations; some of them *select* `K`.

## The shape

The general branch datum is **not** new: `SelectedPresentation`
(`GQ2/Dyadic/SelectedWords.lean`) is already the R5 constructor table at free `(α, r, ε, η, h)`,
with `degree` and `word` at that degree.  §1 adds the missing third column, the presented
pro-`2` core, and the degree-parity coherence: `2*h+1` on the `L` row through `D_sq`, `2+2*h`
on the four even rows through `D_N`/`D_M`.  §2 is the selector/obligation split, §3 the
statement, §4 the reconciliation against `Main.lean`'s five records.

## Sources

`docs/dyadic/w74-critical-path.md` (the anatomy of the quadratic path: the records, the
obligations-versus-selectors split, the eight-item closing list, the `KTwoN` finding);
`GQ2/Dyadic/Main.lean` §§3-7; `GQ2/Dyadic/Instances/KSupply.lean` §§4-6;
`GQ2/Dyadic/Instances/Cores.lean` (the general-`(α, h)` core presentations and word
certificates).
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 The general branch datum: the third column of the constructor table

`SelectedPresentation` supplies the degree and the word at every `(α, r, ε, η, h)`.  What it
does not supply is the presented pro-`2` core that the certificate interface pairs the word
with.  `genAsmCore` is that column, read off the core-presentation layer
(`GQ2/Dyadic/Instances/Cores.lean`, `GQ2/Dyadic/Instances/NpcCore.lean`): the procyclic rows
share the compact rows' cores, and the `L` row's is the square-commutator core `D_sq`. -/

section Column

/-- **The presented pro-`2` core of a selected presentation.**  `L` takes the
square-commutator core `D_sq h` (`lCorePresentation h : CorePresentation (2*h+1) (lSqW h)
(DSq h)`); the two `N` rows take `D_N α h` (`nCorePresentation`, `npcCorePresentationUnit`);
the two `M` rows take `D_M α h` (`mCorePresentation`, `mpcCorePresentation` — both branches
present the *same* core, the dictionaries differ). -/
noncomputable def genAsmCore : SelectedPresentation → ProfiniteGrp
  | .L h => SqCore.DSq h
  | .N0 alpha h => DN alpha h
  | .Npc alpha _ h _ => DN alpha h
  | .M0 alpha h => DM alpha h
  | .Mpc alpha _ _ _ h => DM alpha h

/-- Every core in the table is pro-`2` (MC2's `isProP_DN`/`isProP_DM`, SqCore's
`isProP_DSq`). -/
noncomputable def genAsmCoreIsProP :
    (S : SelectedPresentation) → IsProP 2 ((genAsmCore S : ProfiniteGrp) : Type)
  | .L h => SqCore.isProP_DSq h
  | .N0 alpha h => isProP_DN alpha h
  | .Npc alpha _ h _ => isProP_DN alpha h
  | .M0 alpha h => isProP_DM alpha h
  | .Mpc alpha _ _ _ h => isProP_DM alpha h

/-- The handle count of a selected presentation (the `h` stored in every constructor: it is
what controls the generator alphabet). -/
def genAsmHandles : SelectedPresentation → ℕ
  | .L h => h
  | .N0 _ h => h
  | .Npc _ _ h _ => h
  | .M0 _ h => h
  | .Mpc _ _ _ _ h => h

/-- `true` exactly on the four even rows (`Parameters.lean`'s `BranchData.isEven`, read on the
displayed table). -/
def genAsmIsEven : SelectedPresentation → Bool
  | .L _ => false
  | _ => true

/-- **Degree parity, `L` side**: the odd row's degree is `1 + 2h`, `h` the handle count, and
its core is the square-commutator core `D_sq h` at that same `h`. -/
theorem genAsm_degree_odd :
    (S : SelectedPresentation) → genAsmIsEven S = false →
      S.degree = 1 + 2 * genAsmHandles S
  | .L h, _ => by simp [SelectedPresentation.degree, genAsmHandles, Nat.add_comm]

/-- **Degree parity, even side**: every non-`L` row's degree is `2 + 2h`, and its core is
`D_N`/`D_M` at that same `h`. -/
theorem genAsm_degree_even :
    (S : SelectedPresentation) → genAsmIsEven S = true →
      S.degree = 2 + 2 * genAsmHandles S
  | .N0 _ _, _ => rfl
  | .Npc _ _ _ _, _ => rfl
  | .M0 _ _, _ => rfl
  | .Mpc _ _ _ _ _, _ => rfl

/-- The degree of a selected presentation is odd on the `L` row and even on the other four:
this is `Parameters.lean`'s `Compatible` predicate, read on the displayed table. -/
theorem genAsm_degree_parity (S : SelectedPresentation) :
    if genAsmIsEven S then Even S.degree else Odd S.degree := by
  cases S with
  | L h => simp [genAsmIsEven, SelectedPresentation.degree]
  | N0 _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | Npc _ _ h _ => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | M0 _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩
  | Mpc _ _ _ _ h => simpa [genAsmIsEven, SelectedPresentation.degree] using ⟨1 + h, by ring⟩

end Column

end GQ2.Dyadic
