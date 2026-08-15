/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.GeneralCertificates
import GQ2.Dyadic.SqCore.GradedOddClose

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
on the candidate side.  The producer is also **std-3** where the committed `h = 0` closure is
not (§6): the transport route drags in three campaign axioms that the core-presentation route
does not touch.

It does **not** discharge the four analytic clauses, and §4 records that the wave-80/81
odd machinery does **not** discharge them either.  That check is worth stating because the lane
brief hypothesised the opposite.  `SqCore.gOdd_certificate` and
`Instances.OddIdentification.oddId_supply_iff_certificate` are about the *classification* input
of the `L` row (the oriented identification `D_sq h ≅ G_K`, i.e. the branch datum
`genAsm_branch_of_oddSq_canonical` consumes), which is a different field of the general
assembly from `CAND`.  Concretely: `oddId_supply_iff_certificate` is an equivalence between the
odd seam and a `MarkedMatchingCertificate`, not a `WordCertificate`; the two records share no
field.  §4 pins the separation as a Lean statement rather than a remark.

## Section guide

* §1 the seven row-specific non-analytic fields at free `h` (the other six are generic and are
  filled inline in §2);
* §2 `lCand_wordCertificate`, the producer, and `lCand_wordCertificateCanonical` at `lNu h`;
* §3 the `h = 0` sanity check against the committed `n = 1` endpoint;
* §4 the feed into `GenAsmRowResidual.cand`, and the separation from the odd machinery;
* §5 the odd row from the seam alone, and the total remaining list.

## Axioms

`#print axioms` runs on every declaration in §6, with the split recorded there.
-/

namespace GQ2.Dyadic.Instances.LRowCand

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open TameSpec MarkedCore
open GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.LSq
open GQ2.Dyadic.Instances.LSquareCore

/-! ## §1 The seven row-specific non-analytic fields at free `h`

Thirteen of the record's seventeen fields are proved by this module.  Six of the thirteen
(`tfg`, `smulZmod2`, `contSMulZmod2`, `htriv`, `htame`, `hwild`) are generic in `(n, q, R)` and
are filled inline in §2 from `Count`; the seven stated here are the row-specific ones.

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

/-! ## §2 The producer

The `L`-row twin of `MCompactCore.mWordCertificate` and `genCertNWordCertificate`: thirteen
fields proved, the four analytic clauses as explicit arguments at exactly the record's types, so
the elaborator is the acceptance check.

Two differences from the `M` template, both checked here rather than assumed:

* **no `1 ≤ α`**, and indeed no `α` at all: the `L` row carries no `α`, and none of
  `lCorePresentation`, `eval_pro2_lSqW_eq_sqRelWord`, `tameSpecializes_lSq` or `hwild_lSq` has a
  threshold hypothesis.  The only arithmetic binders are `q ≠ 0` and `Even q`.
* **the `coreRel`/`proTwoWord` pair is a one-liner** rather than a re-derivation, for the binder
  reason recorded on `lCandCoreRel`. -/

section Producer

/-- **The `L`-row word certificate at free handle count.**  This is the producer the general
constructor table's `L h` row was missing: `GQ2/Dyadic/GeneralAssembly.lean`'s table entry
"`L h` | none over `D_sq h`" and item 1 of `docs/dyadic/w75-state-note.md` §6 at every `h`,
not only `h = 0`.

Thirteen fields are proved; the four arguments are AS1's analytic clauses.  ⚠ The four are
**not** discharged here and are not discharged anywhere at this tree for a general row: the
certificate ⇒ count bridge does not exist at the candidate carrier `GammaR` (AS1 divergence 4).
At `h = 0` they *are* available, by a route that does not generalize (see §3). -/
noncomputable def lCand_wordCertificate (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 * h + 1)}
    (nuP : ContinuousMonoidHom ((SqCore.DSq h : ProfiniteGrp) : Type) Ztwo)
    (hnuSigma : nuP ((lCorePresentation h).mark .sigma) = ztwoOne)
    (hnuWild : ∀ j : Fin (2 * h + 1 + 1), nuP ((lCorePresentation h).mark (.wild j)) = 1)
    (exactLifting : ExactLiftingSemantics (GammaR (2 * h + 1) q (lSqW h))
      (2 * h + 1) q (SqCore.DSq h) nuP SN)
    (stokes : StokesDualityCertificate (GammaR (2 * h + 1) q (lSqW h)) (2 * h + 1) q
      (SqCore.DSq h) nuP SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 * h + 1) q (lSqW h)) (2 * h + 1) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 * h + 1) q (lSqW h))
      (2 * h + 1) q (SqCore.DSq h) nuP SN
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCandTameSpecializes h q hq0 hqe))
      (lCandPro2 h q hq0 hqe)
      (lCandCompat h q hq0 hqe (lCandTameSpecializes h q hq0 hqe) nuP hnuSigma hnuWild)
      (scalarActionZmodTwo _)) :
    WordCertificate (2 * h + 1) q (lSqW h) (SqCore.DSq h) (SqCore.isProP_DSq h) nuP SN where
  tameSpecialization := lCandTameSpecializes h q hq0 hqe
  coreRel := lCandCoreRel h
  proTwoWord := fun G _ _ _ _ _ t => lCandProTwoWord h G t
  pro2 := lCandPro2 h q hq0 hqe
  ker_pro2 := lCand_ker_pro2 h q hq0 hqe
  hpro2 := lCandPro2_surjective h q hq0 hqe
  compat := lCandCompat h q hq0 hqe (lCandTameSpecializes h q hq0 hqe) nuP hnuSigma hnuWild
  tfg := Count.gammaR_topologicallyFinitelyGenerated _ _ _
  smulZmod2 := scalarActionZmodTwo _
  contSMulZmod2 := scalarActionZmodTwo_continuousSMul _
  htriv := scalarActionZmodTwo_triv _
  exactLifting := exactLifting
  stokes := stokes
  scalar := scalar
  determinant := determinant
  htame := Count.htame_of_tameSpecializes _
  hwild := Count.hwild_lSq _

/-- **The producer at the canonical marking.**  `lNu h` is the core's own unramified `Ztwo`
coordinate, and its two normalization clauses are already theorems at free `h`
(`LSquareCore.lNu_sigma`, `LSquareCore.lNu_wild`), so all three marking binders vanish: the `L h`
row's `CAND` producer takes free `(h, q)`, the two `q`-conditions, and AS1's four analytic
clauses, and nothing else.

This is the exact shape of `genCertNWordCertificateCanonical` on the `N0` row. -/
noncomputable def lCand_wordCertificateCanonical (h q : ℕ) (hq0 : q ≠ 0) (hqe : Even q)
    {SN : SourceNumerics (2 * h + 1)}
    (exactLifting : ExactLiftingSemantics (GammaR (2 * h + 1) q (lSqW h))
      (2 * h + 1) q (SqCore.DSq h) (lNu h) SN)
    (stokes : StokesDualityCertificate (GammaR (2 * h + 1) q (lSqW h)) (2 * h + 1) q
      (SqCore.DSq h) (lNu h) SN (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 * h + 1) q (lSqW h)) (2 * h + 1) SN
      (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 * h + 1) q (lSqW h))
      (2 * h + 1) q (SqCore.DSq h) (lNu h) SN
      (tameOfSpec (2 * h + 1) q (lSqW h) (lCandTameSpecializes h q hq0 hqe))
      (lCandPro2 h q hq0 hqe)
      (lCandCompat h q hq0 hqe (lCandTameSpecializes h q hq0 hqe) (lNu h) (lNu_sigma h)
        (lNu_wild h))
      (scalarActionZmodTwo _)) :
    WordCertificate (2 * h + 1) q (lSqW h) (SqCore.DSq h) (SqCore.isProP_DSq h) (lNu h) SN :=
  lCand_wordCertificate h q hq0 hqe (lNu h) (lNu_sigma h) (lNu_wild h)
    exactLifting stokes scalar determinant

/-- The canonical `L`-row marking is onto, the twin of `genCertNNuZtwo_surjective` on the `N`
row.  (`KSupply` and `genAsm_candidate_equiv_galK_of_supply` both take a surjectivity binder on
the row's `ν`; this is what fills it at the `L` row.) -/
theorem lCandNu_surjective (h : ℕ) : Function.Surjective (lNu h) :=
  Instances.NuWitness.surjective_of_ztwoOne_mem_range _ ⟨_, lNu_sigma h⟩

/-- The producer sits over the general constructor table's `L h` row: same degree, … -/
theorem lCand_row_degree (h : ℕ) : (SelectedPresentation.L h).degree = 2 * h + 1 := rfl

/-- … same word, … -/
theorem lCand_row_word (h : ℕ) : (SelectedPresentation.L h).word = lSqW h := rfl

/-- … and same core. -/
theorem lCand_row_core (h : ℕ) : genAsmCore (.L h) = SqCore.DSq h := rfl

/-- …and the row's `IsProP` witness is the one the producer uses. -/
theorem lCand_row_isProP (h : ℕ) : genAsmCoreIsProP (.L h) = SqCore.isProP_DSq h := rfl

end Producer

/-! ## §3 The `h = 0` sanity check

The producer must not have drifted off the committed `n = 1` endpoint.  Three checks, all of
which the elaborator performs:

1. the **word-layer fields recover verbatim**: `lCandCoreRel 0` and `lCandProTwoWord 0` are the
   committed `QTwo.coreRelLSq` and `QTwo.proTwoWord_lSq` on the nose (both sides are
   `SqCore.sqRelWord ∘ sqIdxMark` and Gate C's headline at `h = 0`);
2. the producer's **output type at `h = 0` is the type the committed `L 0` closure inhabits**,
   so `genCert_wordCertificate_nonempty_L_zero` typechecks against it directly;
3. the row pins of §2 hold at `h = 0` by the same `rfl`s.

⚠ **What the check does not say, and this is a finding worth carrying.**  The committed `h = 0`
closure lives at the marking `genCertLNu = ν₂ ∘ genCertLEquiv`, i.e. at the *transported* `Π`
marking, and `GeneralCertificates` §5's own docstring records that this is **not** claimed to be
the canonical `lNu 0` and that no comparison is available at this tree.  So check 2 is at
`genCertLNu`, not at `lNu 0`: the unconditional `h = 0` certificate and the canonical-marking
producer `lCand_wordCertificateCanonical` are at *different* markings, and the composite
"unconditional certificate at `lNu 0`" is **not** available even at `h = 0`.  That matters
downstream, because the branch datum the odd route builds
(`genAsm_branch_of_oddSq_canonical`) is at `lNu h`; see §4. -/

section ZeroCheck

/-- **Check 1a**: the `coreRel` field recovers the committed `n = 1` one verbatim. -/
theorem lCand_zero_coreRel : lCandCoreRel 0 = QTwo.coreRelLSq := rfl

/-- **Check 1b**: and so does `proTwoWord` (both are Gate C's headline at `h = 0`). -/
theorem lCand_zero_proTwoWord (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking 1 G) :
    lCandProTwoWord 0 G t = QTwo.proTwoWord_lSq G t := rfl

/-- **Check 2**: the producer's target type at `h = 0` is exactly the type of the committed
`L 0` closure, so the committed theorem typechecks against it with no massaging.  (This is the
`h = 0` regression the lane owes: it fails the moment the degree, the word, the core or the
`IsProP` witness drifts.) -/
theorem lCand_zero_nonempty :
    Nonempty (WordCertificate (2 * 0 + 1) 2 (lSqW 0) (SqCore.DSq 0) (SqCore.isProP_DSq 0)
      genCertLNu (standardNumerics (2 * 0 + 1))) :=
  genCert_wordCertificate_nonempty_L_zero

end ZeroCheck

/-! ## §4 Feeding `GenAsmRowResidual.cand`, and what the odd rows now need in total

`GenAsmRowResidual.cand` is stated at the branch datum's own marking `G.nuP`, so a producer at
the canonical `lNu h` reaches it only if the branch datum is *known* to be at `lNu h`.  The
odd route's producer `genAsm_branch_of_oddSq_canonical` does build the datum at `lNu h`, but it
states `∃ G : GenAsmBranch K B, G.pres = .L h`, and the existential drops the marking.  So the
first thing §4 does is rebuild the same datum as a **definition** rather than an existential
(`lCandBranch`), which is a pure repackaging of `genAsm_branch_of_oddSq` with the two canonical
marking binders discharged exactly as the committed theorem discharges them.

With that, the `L h` row's `CAND` field is supplied at every `h` by the four analytic clauses,
and `lCandRowResidual` assembles the whole residual record.

### What the odd rows of the general theorem need, in total, after this lane

Reading `oddId_candidate_equiv_galK_of_supply` and `genAsm_candidate_equiv_galK` against what
is now producible:

1. **the selector**, an oriented equivalence `D_sq h ≃ G_K(2)` with the two `ν` normalizations,
   i.e. wave 81's seam `SqMarkedForwardSupply B h`.  Discharged at `h = 0`
   (`oddId_markedSupply_degreeOne`), open at `h ≥ 1`;
2. **the three ASK clauses** at the carrier `G_K` (`exactLifting`, `stokes`, `determinant`),
   which are row-independent and are `KSupply`'s business, not this lane's;
3. **the four CAND analytic clauses** at the candidate carrier `GammaR (2h+1) q (lSqW h)`:
   what is left of `cand` after this module.

⚠ Item 3 is the honest residue, and the lane brief's hypothesis that the wave-80/81 odd
machinery would discharge it is **refuted by inspection of the statements**: `gOdd_certificate`
and `oddId_supply_iff_certificate` produce a `MarkedCoreCertificateKTwoSq` / a
`SqMarkedForwardSupply`, which are inputs to item 1, and neither record shares a single field
with `WordCertificate`.  The odd supply is consumed by the *selector*, not by the certificate's
recursion.  §4's `lCandRowResidual` makes the separation checkable: item 1 enters through
`lCandBranch`'s arguments and item 3 enters through `lCandRowResidual`'s, and no argument of
either is derivable from the other. -/

section Row

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The `L`-row branch datum as a definition.**  Field-for-field the datum
`genAsm_branch_of_oddSq_canonical` builds, but returned rather than existentially quantified, so
that `nuP` is *definitionally* `lNu h` and the canonical producer of §2 reaches the `cand`
field.

Nothing here is new: `hnuP` is `genAsm_lNu_surjective` and the `ztwoIota` clause is
`LSquare.ztwoIota_lNu`, exactly the two the committed canonical theorem discharges. -/
noncomputable def lCandBranch (h : ℕ) (c : ℤ_[2])
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.L h).degree)
    (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K)))
    (hMix : SqCore.SqHandleMixFixesCore h c)
    (hsigma : nuUrKTwo B (e.1 (SqCore.dsqSigma h)) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (e.1 (SqCore.dsqX0 h)) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    GenAsmBranch K B where
  pres := .L h
  hdeg := hdeg
  nuP := lNu h
  hnuP := genAsm_lNu_surjective h
  realization := MarkedCoreRealization.ofCertificateSq (lNu h) (LSquare.ztwoIota_lNu h)
    (marked_matching_certificate_KTwoSq_of_fixesCore B h c e.1 e.2 hMix hsigma hx0).some

variable (h : ℕ) (c : ℤ_[2]) (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.L h).degree)
  (e : OrientedContinuousMulEquiv (SqCore.chiSq h) (chiCycKTwo (K := K)))
  (hMix : SqCore.SqHandleMixFixesCore h c)
  (hsigma : nuUrKTwo B (e.1 (SqCore.dsqSigma h)) = Multiplicative.ofAdd (1 : ℤ_[2]))
  (hx0 : nuUrKTwo B (e.1 (SqCore.dsqX0 h)) = Multiplicative.ofAdd (0 : ℤ_[2]))

/-- The datum sits on the `L h` row, which is what the existential form records. -/
theorem lCandBranch_pres : (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).pres = .L h := rfl

/-- …and, unlike the existential form, it remembers the marking. -/
theorem lCandBranch_nuP : (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).nuP = lNu h := rfl

include c hdeg e hMix hsigma hx0 in
/-- The existential form is recovered, so nothing is lost by working with the definition. -/
theorem lCandBranch_exists : ∃ G : GenAsmBranch K B, G.pres = .L h :=
  ⟨lCandBranch h c hdeg e hMix hsigma hx0, rfl⟩

/-- **The `CAND` field at the `L h` row, at free `h`.**  Stated at the branch datum's own
projections, so the elaborator is the acceptance check: this term has *exactly* the type of
`GenAsmRowResidual.cand` over `lCandBranch`, at the field's tame modulus `q_K` and the standard
numerics.

The `q`-side binders are discharged from the filtration (`qOf_ne_zero`, `even_qOf`), so the four
analytic clauses are the only inputs. -/
noncomputable def lCandCand
    (exactLifting : ExactLiftingSemantics (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)))
    (stokes : StokesDualityCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (scalar : ScalarHilbertCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (determinant : AffineDeterminantCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1))
      (tameOfSpec (2 * h + 1) (qOf K FF) (lSqW h)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (lCandPro2 h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
      (lCandCompat h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)) (lNu h)
        (lNu_sigma h) (lNu_wild h))
      (scalarActionZmodTwo _)) :
    WordCertificate (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).degree (qOf K FF)
      (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).word
      (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).core
      (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).coreIsProP
      (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).nuP
      (standardNumerics (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).degree) :=
  lCand_wordCertificateCanonical h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
    exactLifting stokes scalar determinant

/-- **The whole residual record at the `L h` row.**  Three `ASK` clauses at the arithmetic
carrier `G_K` and four `CAND` clauses at the candidate carrier `Γ_R`; no classification input,
no per-`h` transport, no handle-count binder.

This is the object the lane owes: after it, the odd rows of the general theorem need exactly
the selector (item 1 of the section header) and these seven analytic clauses. -/
noncomputable def lCandRowResidual (T : OrientedTameQuotientK B FF)
    (askExactLifting : ExactLiftingSemantics (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)))
    (askStokes : StokesDualityCertificate (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) (smulZmod2GalK K))
    (askDeterminant : AffineDeterminantCertificate (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) T.tameFK
      (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).pro2
      (fun g => T.compatF_K (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).pro2 (lNu h)
        (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)).realization.nu_compat g)
      (smulZmod2GalK K))
    (candExactLifting : ExactLiftingSemantics (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)))
    (candStokes : StokesDualityCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (candScalar : ScalarHilbertCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (candDeterminant : AffineDeterminantCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1))
      (tameOfSpec (2 * h + 1) (qOf K FF) (lSqW h)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (lCandPro2 h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
      (lCandCompat h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)) (lNu h)
        (lNu_sigma h) (lNu_wild h))
      (scalarActionZmodTwo _)) :
    GenAsmRowResidual (lCandBranch h c hdeg e hMix hsigma hx0 (B := B)) T where
  exactLifting := askExactLifting
  stokes := askStokes
  determinant := askDeterminant
  cand := lCandCand h c hdeg e hMix hsigma hx0 (FF := FF)
    candExactLifting candStokes candScalar candDeterminant

end Row

/-! ## §5 The odd row from the seam alone

§4's `lCandBranch` still carries the handle-mix binder `hMix` and the correction exponent `c`.
Wave 80 removed both at every `h`: `SqCore.gOdd_pivotFix h : SqHandleMixFixesCore h sqPivotExp`
is a theorem free in `h`, which is exactly what `oddId_genAsmBranch_L_of_supply` uses.  So the
branch datum is a function of the seam `SqMarkedForwardSupply B h` and the degree pin alone,
and, unlike the committed existential form, the definition below remembers that its marking is
`lNu h`, which is what lets §2's canonical producer reach the `cand` field.

`lCand_oddRow_of_supply` is then the lane's headline, and it is the honest statement of what the
odd rows of the general theorem need in total: the seam, the row-independent field inputs, three
`ASK` clauses at `G_K`, and four `CAND` clauses at `Γ_R`.  Nothing else, at any handle count. -/

section Seam

variable {Rec : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- **The `L h` branch datum from the seam**, as a definition.  The marking-forgetting
existential of `oddId_genAsmBranch_L_of_supply`, made into a term. -/
noncomputable def lCandBranchOfSupply (h : ℕ)
    (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.L h).degree)
    (H : LSquare.SqMarkedForwardSupply B h) : GenAsmBranch K B :=
  lCandBranch h SqCore.sqPivotExp hdeg ⟨H.choose, H.choose_spec.1⟩ (SqCore.gOdd_pivotFix h)
    H.choose_spec.2.1 H.choose_spec.2.2

variable (h : ℕ) (hdeg : Module.finrank ℚ_[2] K = (SelectedPresentation.L h).degree)
  (H : LSquare.SqMarkedForwardSupply B h)

/-- It sits on the `L h` row… -/
theorem lCandBranchOfSupply_pres : (lCandBranchOfSupply h hdeg H).pres = .L h := rfl

/-- …at the canonical marking, which is the fact the existential form loses. -/
theorem lCandBranchOfSupply_nuP : (lCandBranchOfSupply h hdeg H).nuP = lNu h := rfl

/-- **The lane's headline.**  At every odd degree and every handle count, the general theorem's
conclusion on the `L h` row follows from

* the wave-81 seam `H : SqMarkedForwardSupply B h` (the selector, open at `h ≥ 1`),
* the row-independent field inputs `F`,
* three `ASK` clauses at the arithmetic carrier `G_K`, and
* four `CAND` clauses at the candidate carrier `Γ_R (2h+1) q_K (lSqW h)`.

Before this lane the list had a fifth candidate-side item, a `WordCertificate` over `D_sq h`
with no producer at `h ≥ 1`, and `oddId_candidate_equiv_galK_of_supply`'s docstring names it
("the CAND `WordCertificate` over `D_sq h`, which has no producer at free `h` in this tree").
That sentence is what this module retires. -/
theorem lCand_oddRow_of_supply (T : OrientedTameQuotientK B FF)
    (F : GenAsmFieldInputs K B FF (lCandBranchOfSupply h hdeg H).degree)
    (hT : F.T = T)
    (askExactLifting : ExactLiftingSemantics (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)))
    (askStokes : StokesDualityCertificate (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) (smulZmod2GalK K))
    (askDeterminant : AffineDeterminantCertificate (galKProfinite K) (2 * h + 1) (qOf K FF)
      (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) T.tameFK
      (lCandBranchOfSupply h hdeg H).pro2
      (fun g => T.compatF_K (lCandBranchOfSupply h hdeg H).pro2 (lNu h)
        (lCandBranchOfSupply h hdeg H).realization.nu_compat g)
      (smulZmod2GalK K))
    (candExactLifting : ExactLiftingSemantics (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)))
    (candStokes : StokesDualityCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (candScalar : ScalarHilbertCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h)) (2 * h + 1)
      (standardNumerics (2 * h + 1)) (scalarActionZmodTwo _))
    (candDeterminant : AffineDeterminantCertificate (GammaR (2 * h + 1) (qOf K FF) (lSqW h))
      (2 * h + 1) (qOf K FF) (SqCore.DSq h) (lNu h) (standardNumerics (2 * h + 1))
      (tameOfSpec (2 * h + 1) (qOf K FF) (lSqW h)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)))
      (lCandPro2 h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF))
      (lCandCompat h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)
        (lCandTameSpecializes h (qOf K FF) (qOf_ne_zero K FF) (even_qOf K FF)) (lNu h)
        (lNu_sigma h) (lNu_wild h))
      (scalarActionZmodTwo _)) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (2 * h + 1) (qOf K FF) (lSqW h) : ProfiniteGrp) : Type) (GalK K)) :=
  genAsm_candidate_equiv_galK (lCandBranchOfSupply h hdeg H) F
    (hT ▸ lCandRowResidual h SqCore.sqPivotExp hdeg ⟨H.choose, H.choose_spec.1⟩
      (SqCore.gOdd_pivotFix h) H.choose_spec.2.1 H.choose_spec.2.2 T
      askExactLifting askStokes askDeterminant
      candExactLifting candStokes candScalar candDeterminant)

end Seam

/-! ## §6 Axiom pins

One pin per declaration, **27** in all, in declaration order.  Measured against the mirror at
`a45bc557`:

* **25 of the 27 print at most the std-3 set** `propext, Classical.choice, Quot.sound`, and
  `lCand_row_degree` prints none at all.  That includes the producer `lCand_wordCertificate`,
  the canonical form, the whole `GenAsmRowResidual` feed of §4, and the branch datum of §5:
  building the `L`-row certificate out of the core presentation, and placing `K` on the row,
  introduce **no campaign axiom**.  This matches `GeneralAssembly` §5's reading of its own
  branch-datum layer.
* **`lCand_oddRow_of_supply` adds three**: `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` and
  `Foundations.absGalQ2_localEulerCharacteristic`, exactly
  `genAsm_candidate_equiv_galK`'s pin, inherited and nothing more.
* ⚠ **`lCand_zero_nonempty` adds three others**, namely `dyadicOrientation`, `localReciprocity`
  and `peripheralCyclotomicAction`, and they come from the *committed* `h = 0` closure, not from
  this module: `genCert_wordCertificate_nonempty_L_zero` transports off `Π` through
  `genAsm_nonempty_equiv_L_core_piBd`, which is where those three enter.  So the free-`h`
  producer is **strictly narrower in axioms than the `h = 0` route it generalizes**, which is a
  second reason (beyond the marking mismatch of §3) not to read the committed `h = 0` closure
  as the `h = 0` case of this one.

The reading a consumer should take is the one `GeneralAssembly` asks for: **the candidate side
is axiom-free**, and the campaign axioms enter only at the identification with `G_K`. -/

section AxiomPins

#print axioms lCandCoreRel
#print axioms lCandProTwoWord
#print axioms lCandTameSpecializes
#print axioms lCandPro2
#print axioms lCand_ker_pro2
#print axioms lCandPro2_surjective
#print axioms lCandCompat
#print axioms lCand_wordCertificate
#print axioms lCand_wordCertificateCanonical
#print axioms lCandNu_surjective
#print axioms lCand_row_degree
#print axioms lCand_row_word
#print axioms lCand_row_core
#print axioms lCand_row_isProP
#print axioms lCand_zero_coreRel
#print axioms lCand_zero_proTwoWord
#print axioms lCand_zero_nonempty
#print axioms lCandBranch
#print axioms lCandBranch_pres
#print axioms lCandBranch_nuP
#print axioms lCandBranch_exists
#print axioms lCandCand
#print axioms lCandRowResidual
#print axioms lCandBranchOfSupply
#print axioms lCandBranchOfSupply_pres
#print axioms lCandBranchOfSupply_nuP
#print axioms lCand_oddRow_of_supply

end AxiomPins

end GQ2.Dyadic.Instances.LRowCand
