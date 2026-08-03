/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Instances.GammaLDualityBoundary
import GQ2.Dyadic.Instances.QTwo

/-!
# Audited routes to a field realization of `GammaL`

`GammaLFieldRealization h q` asks for an equivalence from the full profinite presentation
`gamma h q` to an open subgroup of `G_Q2` of index `2h+1`.  This file audits the available
classification routes and separates two meanings of "noncircular": not assuming the desired
carrier equivalence, and being upstream of the unresolved analytic L residue.

There are two distinct results.

* At `(h,q) = (0,2)`, the existing independently proved Q2 presentation theorem gives an actual
  realization, with open subgroup `top`.  This construction is genuinely upstream of the
  general analytic residue.  The standard-three theorem
  `gammaL_zero_two_isLocalDualizingGroup_of_equiv` isolates transport of the truth-side B6
  predicate; `gammaL_tateDualityG_zero_two` then invokes the existing B6 axiom explicitly.
* In general, `gammaLFieldRealization_of_reconstruction` applies the existing two-source
  reconstruction theorem to an L `WordCertificate` and an arithmetic `DyadicLocalInput`.  These
  inputs contain source-side counting and boundary data, but no equivalence between `GammaL` and
  the arithmetic source; `candidate_equiv_absoluteGalois` constructs that equivalence by the
  finite-quotient reconstruction theorem.

This distinction matters.  A theorem taking
`ContinuousMulEquiv (gamma h q : Type) (GalK K)` as an input would merely repackage the desired
carrier presentation and would be circular as an upstream construction.  The reduction below
does not take such an input.  Its arithmetic record has an equivalence only from its own abstract
`SourceDataN` carrier to `GalK K`, while the comparison with the candidate source is the output of
reconstruction.  Thus the general constructor is **carrier-noncircular**.

It is not, however, an upstream route for closing the current analytic L residue.  A legacy
`WordCertificate` directly contains `ExactLiftingSemantics`, `StokesDualityCertificate`,
`ScalarHilbertCertificate`, and `AffineDeterminantCertificate`; the regression
`wordCertificate_lSq_exactLifting` makes the first dependency explicit.  The known corrected
family L producer `wordCertificateRN_of_familyFieldSelection_resolvedL` obtains its exact-lifting
field from `ResolvedPushedHsimp`.  Consequently the general result below is a useful final
assembly interface once the analytic certificate exists, not a replacement proof of that
certificate or of the unresolved GammaL duality input.

The audit also rules out a shorter current route through `IsDemushkin`: that structure records
only scalar mod-2 cohomology of a pro-2 group, whereas `TateDualityG` quantifies over every finite
exponent-two module for the full profinite group.  The maximal-pro-2 APIs currently identify
`H¹` only for trivial pro-2 coefficients and inject `H²` only for trivial `ZMod 2`; a finite
module can still have a nontrivial odd-order tame action, so those results cannot populate the
bundle.  Moreover, an equivalence of maximal pro-2 quotients alone does not determine the tame
extension.  The repository deliberately has no general odd-rank `SqLabHypothesis`, and an
arbitrary natural `q` need not be a residue cardinality.  `DyadicLocalInput.params_qK` keeps that
necessary arithmetic restriction explicit.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## The genuine degree-one construction -/

/-- The canonical top-subgroup equivalence, isolated so the base-case realization contains no
choice of a field model. -/
def continuousMulEquivTop (G : Type) [Group G] [TopologicalSpace G] :
    G ≃ₜ* ↥(⊤ : Subgroup G) where
  toFun g := ⟨g, trivial⟩
  invFun g := g.1
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _
  continuous_invFun := continuous_subtype_val

/-- **Actual construction at the base L row.**  The independently established Q2 presentation
`GammaL(0,2) ≃ G_Q2` realizes the source as the open subgroup `top`, of index one.

This is not a general classification argument: it deliberately exposes the only `(h,q)` for
which the repository already has an unconditional full carrier equivalence. -/
noncomputable def gammaLFieldRealization_zero_two : GammaLFieldRealization 0 2 where
  subgroup := ⊤
  isOpen_subgroup := isOpen_univ
  equiv := QTwo.candidateGroup_lSq_equiv_absGalQ2_via_sourcesN.some.trans
    (continuousMulEquivTop AbsGalQ2)
  index_eq := Subgroup.index_top

theorem nonempty_gammaLFieldRealization_zero_two :
    Nonempty (GammaLFieldRealization 0 2) :=
  ⟨gammaLFieldRealization_zero_two⟩

/-! ## The full Tate boundary at the base L row -/

/-- A supplied topological equivalence `GammaL(0,2) ≃ G_Q2` makes the base L source a local
dualizing group at two.

The implication itself is standard-three: it transports only the truth-side predicate and does
not invoke B6.  Keeping the equivalence explicit separates this formal transport from the
arithmetic axiom footprint of the repository's unconditional Q2 presentation theorem. -/
theorem gammaL_zero_two_isLocalDualizingGroup_of_equiv
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    (e : (gamma 0 2 : Type) ≃ₜ* AbsGalQ2) :
    IsLocalDualizingGroup (gamma 0 2 : Type) 2 :=
  isLocalDualizingGroup_two_of_equiv e (isLocalDualizingGroup_absGalQ2 2)

/-- **Unconditional truth-side boundary at `(h,q) = (0,2)`.**

The independently proved Q2 presentation supplies the equivalence consumed by the preceding
standard-three transport theorem.  This corollary therefore inherits exactly the existing
arithmetic dependencies of `candidateGroup_lSq_equiv_absGalQ2_via_sourcesN`; it adds no B6
application of its own. -/
theorem gammaL_zero_two_isLocalDualizingGroup
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)] :
    IsLocalDualizingGroup (gamma 0 2 : Type) 2 :=
  gammaL_zero_two_isLocalDualizingGroup_of_equiv
    QTwo.candidateGroup_lSq_equiv_absGalQ2_via_sourcesN.some

/-- **Full Tate duality at the base L row.**  This is the existing B6 axiom applied after the
unconditional truth-side reduction above.  The final constructor adds B6 and no new arithmetic
axiom; the total theorem still inherits the Q2 presentation's pre-existing B6/B7 footprint.

For general `(h,q)`, no corresponding upstream theorem is currently available.  The maximal
pro-2 APIs compare only trivial scalar `H¹` and inject scalar `H²`; they do not cover finite
modules with nontrivial tame (possibly odd-order) action, as required by `TateDualityG`. -/
noncomputable def gammaL_tateDualityG_zero_two
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    [ContinuousSMul (gamma 0 2 : Type) (MuN 2)] :
    TateDualityG (gamma 0 2 : Type) 2 :=
  tateDualityG_two_of_equiv
    QTwo.candidateGroup_lSq_equiv_absGalQ2_via_sourcesN.some
    (isLocalDualizingGroup_absGalQ2 2)

/-- Regression in the proposition-valued shape used by downstream constructors. -/
theorem nonempty_gammaL_tateDualityG_zero_two
    [DistribMulAction (gamma 0 2 : Type) (MuN 2)]
    [ContinuousSMul (gamma 0 2 : Type) (MuN 2)] :
    Nonempty (TateDualityG (gamma 0 2 : Type) 2) :=
  ⟨gammaL_tateDualityG_zero_two⟩

/-! ## A carrier-noncircular, but analytically downstream, general reduction -/

/-- Audit regression: a legacy L `WordCertificate` already assumes the exact-lifting semantics
needed by source reconstruction.  It also stores Stokes, scalar Hilbert, and affine determinant
certificates in adjacent fields.  In the known corrected-family L supply, the corresponding
exact-lifting payload is constructed from `ResolvedPushedHsimp`.

This theorem prevents the general realization constructor below from being mistaken for an
upstream proof of the outstanding analytic residue. -/
theorem wordCertificate_lSq_exactLifting
    {h q : ℕ}
    {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics (2 * h + 1)}
    (W : WordCertificate (2 * h + 1) q (Words.LSq.lSqW h) P hP nuP SN) :
    ExactLiftingSemantics
      (GammaR (2 * h + 1) q (Words.LSq.lSqW h)) (2 * h + 1) q P nuP SN :=
  W.exactLifting

/-- **Carrier-noncircular reconstruction interface for a general odd L row.**

The word certificate constructs the candidate `SourceDataN`; the local input supplies a second
source whose carrier is `G_K`.  Neither argument contains an equivalence from the candidate to
`G_K`.  The equivalence used in the returned realization is produced by
`candidate_equiv_absoluteGalois`, hence by equality of finite-quotient counts and profinite
reconstruction.

This is nevertheless analytically downstream: `W` already contains exact lifting, Stokes
duality, scalar Hilbert, and affine determinant certificates.  In particular, this constructor
cannot be used to prove the `ResolvedPushedHsimp`-dependent exact-lifting result used by the known
general L certificate supply.  It is an assembly theorem conditional on that certificate payload,
not a route around it.

The remaining inputs say exactly that the selected arithmetic field has degree `2h+1`, that the
tame parameter satisfies the reconstruction hypotheses, and that the common pro-2 orientation
is onto.  In particular, `L.params_qK` already asserts that `q` is the residue cardinality of the
chosen arithmetic packet.
-/
noncomputable def gammaLFieldRealization_of_reconstruction
    {h q : ℕ}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {Rec : LocalReciprocity}
    {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics (2 * h + 1)}
    (W : WordCertificate (2 * h + 1) q (Words.LSq.lSqW h) P hP nuP SN)
    (L : DyadicLocalInput K Rec (2 * h + 1) q P hP nuP SN)
    (hdegree : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hq2 : 2 ≤ q) (hqe : Even q) (hnuP : Function.Surjective nuP) :
    GammaLFieldRealization h q where
  subgroup := GalKsub K
  isOpen_subgroup := isOpen_fixingSubgroup K
  equiv := (candidate_equiv_absoluteGalois W L hq2 hqe hnuP).some
  index_eq := (IntermediateField.finrank_eq_fixingSubgroup_index K).symm.trans hdegree

/-- Regression in the exact truth-side shape consumed by `GammaLDualityBoundary`: reconstruction
data supplies a nonempty `GammaLFieldRealization`, without a carrier-equivalence hypothesis but
still conditional on the analytic payload already present in `W`. -/
theorem nonempty_gammaLFieldRealization_of_reconstruction
    {h q : ℕ}
    {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
    {Rec : LocalReciprocity}
    {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics (2 * h + 1)}
    (W : WordCertificate (2 * h + 1) q (Words.LSq.lSqW h) P hP nuP SN)
    (L : DyadicLocalInput K Rec (2 * h + 1) q P hP nuP SN)
    (hdegree : Module.finrank ℚ_[2] K = 2 * h + 1)
    (hq2 : 2 ≤ q) (hqe : Even q) (hnuP : Function.Surjective nuP) :
    Nonempty (GammaLFieldRealization h q) :=
  ⟨gammaLFieldRealization_of_reconstruction W L hdegree hq2 hqe hnuP⟩

end

end GQ2.Dyadic.LSquare
