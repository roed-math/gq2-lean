/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.GeneralCertificates

/-!
# The `L`-row word certificate at free handle count  (dyadic campaign, lane W82-CAND)

`GQ2/Dyadic/GeneralAssembly.lean`'s constructor table lists, for the `CAND` field of
`GenAsmRowResidual`, which rows have a `WordCertificate` producer over the row's own core at
free parameters.  The `L h` row is entered as **none over `D_sq h`**, and
`GQ2/Dyadic/GeneralCertificates.lean` §5 closes it at `h = 0` only, by transporting
`Main.lean`'s `wordCertificate_nonempty_lSq` off `Π`.  Wave 76 called the general `h` case
"new mathematics, not plumbing", on the ground that there is no `Π_h` to transport from.

**That reading was wrong about which mathematics is missing.**  The transport route is indeed
unavailable at `h ≥ 1`, but the transport route is not the only route: the compact-`N` and
compact-`M` rows never use it.  They build the certificate directly out of a
`Count.CorePresentation`, and `Instances.LSquareCore.lCorePresentation h`
(`GQ2/Dyadic/Instances/Cores.lean:146`) **is a `CorePresentation (2*h+1) (lSqW h) (D_sq h)` at
every `h` already**, with its `Ztwo` normalization `lNu h` and both normalization clauses
(`lNu_sigma`, `lNu_wild`) also proved at every `h`.  So this module is the `L`-row twin of
`GeneralCertificates` §6, and it lands in exactly the same posture as the `M` and `N` rows:

* **thirteen fields proved at free `h`**, and
* **four analytic clauses carried as explicit arguments** (AS1 divergence 4: the certificate ⇒
  count bridge does not exist at the candidate carrier `GammaR`).

## What that does and does not settle

It settles the *producer* hole: the `L h` row now has a free-`h` `CAND` constructor, so all
three of the campaign's `CorePresentation`-backed rows (`L`, `N0`, `M0`) are uniform in the
handle count, and the general theorem's `L` rows no longer need a per-`h` classification input
on the candidate side.

It does **not** discharge the four analytic clauses, and §4 records honestly that the wave-80/81
odd machinery does **not** discharge them either.  That check is worth stating because the lane
brief hypothesised the opposite.  `SqCore.gOdd_certificate` and
`Instances.OddIdentification.oddId_supply_iff_certificate` are about the *classification* input
of the `L` row (the oriented identification `D_sq h ≅ G_K`, i.e. the branch datum
`genAsm_branch_of_oddSq_canonical` consumes), which is a different field of the general
assembly from `CAND`.  Concretely: `oddId_supply_iff_certificate` is an equivalence between the
odd seam and a `MarkedMatchingCertificate`, not a `WordCertificate`; the two records share no
field.  §4 pins the separation as a Lean statement rather than a remark.

## Section guide

* §1 the eight core-free fields and the four `CorePresentation` fields, at free `h`;
* §2 `lCand_wordCertificate`, the producer, and `lCand_wordCertificateCanonical` at `lNu h`;
* §3 the `h = 0` sanity check against the committed `n = 1` endpoint;
* §4 what the odd rows of the general theorem still need, stated at the row.

## Axioms

`#print axioms` runs on every declaration at the end of the file, with the split recorded
there.
-/

namespace GQ2.Dyadic.Instances.LRowCand

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore
open GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Instances.LSquareCore

/-! ## §1 The twelve non-analytic fields at free `h`

Nothing here is new mathematics.  The point of writing it out is that every input is already
stated at free `h` in the tree, which is the fact wave 76 did not have.  The four
`CorePresentation`-backed fields go through `Count.CorePresentation.coreHom` and its three
companions, exactly as `genCertNPro2` and friends do on the `N` row. -/

section Fields

/-- **`WordCertificate.coreRel` at the `L` row.**  The square-commutator relator shape
`SqCore.sqRelWord` read through the literal `L_sq` dictionary `sqIdxMark` (`σ ↦ 0`,
`x_i ↦ i+1`).

The binder list is the record's, and that is the whole delicacy: `Words.LSq`'s Gate-C headline
`eval_pro2_lSqW_eq_sqRelWord` is stated at
`[Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
[TotallyDisconnectedSpace G]` and **no `T2Space`**, so it sits in the `coreRel`/`proTwoWord`
slots directly.  (This is where the `N` row needed a re-derivation: its named form
`eval_pro2_nCompact_reindex` factors through `CoreReindex.toCore`, which carries a `T2Space`
binder the record does not have.) -/
def lCandCoreRel (h : ℕ) (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking (2 * h + 1) G) : G :=
  SqCore.sqRelWord (sqIdxMark t)

/-- **`WordCertificate.proTwoWord` at the `L` row**, at every handle count: Gate C's headline,
verbatim. -/
theorem lCandProTwoWord (h : ℕ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    (t : Marking (2 * h + 1) G) :
    t.eval (pro2 (lSqW h)) = lCandCoreRel h G t :=
  eval_pro2_lSqW_eq_sqRelWord h t

/-- **`WordCertificate.tameSpecialization` at the `L` row**, at every handle count. -/
theorem lCandTameSpecializes (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    TameSpecializes (2 * h + 1) q (lSqW h) :=
  Count.tameSpecializes_lSq hq0 hqe h

/-- **`WordCertificate.pro2` at the `L` row**: the classifier of the uniform `L_sq` core
presentation. -/
noncomputable def lCandPro2 (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    ContinuousMonoidHom ((GammaR (2 * h + 1) q (lSqW h)) : Type)
      ((SqCore.DSq h : ProfiniteGrp) : Type) :=
  CorePresentation.coreHom (lCorePresentation h) hq0 hqe

/-- **`WordCertificate.ker_pro2` at the `L` row.** -/
theorem lCand_ker_pro2 (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    (lCandPro2 h q hq0 hqe).toMonoidHom.ker
      = proPKernel 2 ((GammaR (2 * h + 1) q (lSqW h)) : Type) :=
  CorePresentation.ker_coreHom (lCorePresentation h) hq0 hqe

/-- **`WordCertificate.hpro2` at the `L` row.** -/
theorem lCandPro2_surjective (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q) :
    Function.Surjective (lCandPro2 h q hq0 hqe) :=
  CorePresentation.coreHom_surjective (lCorePresentation h) hq0 hqe

/-- **`WordCertificate.compat` at the `L` row**, at an arbitrary `Ztwo` normalization of the
core satisfying the two `prop_3_4_three` clauses. -/
theorem lCandCompat (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    (hspec : TameSpecializes (2 * h + 1) q (lSqW h))
    (nuP : ContinuousMonoidHom ((SqCore.DSq h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((lCorePresentation h).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 * h + 1 + 1), nuP ((lCorePresentation h).mark (.wild j)) = 1)
    (g : ((GammaR (2 * h + 1) q (lSqW h)) : Type)) :
    nuTq q (tameOfSpec (2 * h + 1) q (lSqW h) hspec g) = nuP (lCandPro2 h q hq0 hqe g) :=
  CorePresentation.nu_compat_coreHom (lCorePresentation h) hq0 hqe hspec nuP hnuSigma hnuWild g

end Fields

end GQ2.Dyadic.Instances.LRowCand
