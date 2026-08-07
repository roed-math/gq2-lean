/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.KSupply
import GQ2.Dyadic.MarkedMaxProTwo
import GQ2.Dyadic.MarkedCore.Certificate
import GQ2.Dyadic.MarkedCore.CompactCoV
import GQ2.Dyadic.SelectedEta
import GQ2.Dyadic.SqCore.Certificate

/-!
# The sound interface around the missing general Labute classification

This file joins four already-proved layers without asserting the missing classification theorem:

* the canonical cyclotomic and unramified characters on `G_K(2)`;
* the existing, explicitly conditional `MLabHypothesis` and `NLabHypothesis` interfaces;
* the three marked-core certificate types; and
* the R5-selected word constructors for all five arithmetic rows.

The abstract classification adapters below continue to take `MLabHypothesis` or
`NLabHypothesis` as visibly named arguments.  There is deliberately no new umbrella
"classification hypothesis", and no provisional odd-rank `SqLabHypothesis`: the repository has
not yet fixed an abstract characterization of the canonical orientation on a general profinite
group, and the rank-three `BLabHypothesis` does not supply the general odd-rank theorem.

The last section factors the core-independent map
`G_K -> G_K(2) -> P` and its kernel/marking proofs.  Thus a future Labute theorem only has to
produce a marked-core certificate; it will not have to duplicate the maximal-pro-2 plumbing.
-/

namespace GQ2.Dyadic

open GQ2
open MarkedCore SqCore

noncomputable section

/-! ## Direct `G_K(2)` marked-core certificates -/

section DirectCertificates

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-- The `M` certificate read directly at the two canonical characters on `G_K(2)`. -/
abbrev MarkedCoreCertificateKTwoM (B : MarkedRecip Rec K) (alpha h : ℕ)
    (halpha : 1 ≤ alpha) :=
  MarkedCoreCertificateM alpha h halpha (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom

/-- The `N` certificate read directly at the two canonical characters on `G_K(2)`. -/
abbrev MarkedCoreCertificateKTwoN (B : MarkedRecip Rec K) (alpha h : ℕ) :=
  MarkedCoreCertificateN alpha h (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom

/-- The odd `L` certificate read directly at the two canonical characters on `G_K(2)`. -/
abbrev MarkedCoreCertificateKTwoSq (B : MarkedRecip Rec K) (h : ℕ) :=
  MarkedCoreCertificateSq h (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom

/-- Direct-`G_K(2)` production for an `N` marked-core certificate.  In contrast with the older
`marked_matching_certificate_KN`, this needs no homomorphism to the full abelianization. -/
theorem marked_matching_certificate_KTwoN (B : MarkedRecip Rec K) (alpha h : ℕ)
    (f : ContinuousMulEquiv (DN alpha h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiN alpha h x)
    (hpair : IsUnit (Multiplicative.toAdd (nuUrKTwo B (f (dnSigma alpha h)))) ∨
      IsUnit (Multiplicative.toAdd (nuUrKTwo B (f (dnX2 alpha h))))) :
    Nonempty (MarkedCoreCertificateKTwoN B alpha h) :=
  marked_matching_certificate_N alpha h (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun) hpair

/-- Preferred compact direct-`G_K(2)` constructor for the `N` core.  An oriented abstract
equivalence, a rank-four frame, and the genuine arithmetic level fact `r = 0` suffice: the level
clause produces a unit value on `ker χ`, the compact frame converts that to primitive
`(σ, x₂)` data, and the exact `SL₂(ℤ₂)` correction finishes without a scaling hypothesis. -/
theorem marked_matching_certificate_KTwoN_of_level_zero (B : MarkedRecip Rec K) (alpha : ℕ)
    (halpha : 2 ≤ alpha) (D : NDecomposition alpha) (hr : B.r = 0)
    (f : ContinuousMulEquiv (DN alpha 0 : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiN alpha 0 x) :
    Nonempty (MarkedCoreCertificateKTwoN B alpha 0) := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  let q : maxProPQuotient 2 (GalK K) := maxProPMk 2 (GalK K) g
  let x : (DN alpha 0 : Type) := f.symm q
  apply marked_matching_certificate_N_of_chiKer halpha D
    (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun)
  refine ⟨x, ?_, ?_⟩
  · rw [← horient x]
    change chiCycKTwo (K := K) (f (f.symm q)) = 1
    rw [f.apply_symm_apply]
    change chiCycKTwo (K := K) (maxProPMk 2 (GalK K) g) = 1
    rw [chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK]
    exact hgchi
  · change IsUnit (Multiplicative.toAdd (nuUrKTwo B (f (f.symm q))))
    rw [f.apply_symm_apply]
    change IsUnit (Multiplicative.toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g)))
    rw [nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
    exact isUnit_one

/-- Direct-`G_K(2)` production for an `M` marked-core certificate. -/
theorem marked_matching_certificate_KTwoM (B : MarkedRecip Rec K) (alpha h : ℕ)
    (halpha : 1 ≤ alpha)
    (f : ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiM alpha h x)
    (hMix : MMixHypothesis alpha h halpha)
    (hpivot : IsUnit (Multiplicative.toAdd (nuUrKTwo B (f (dmC alpha h))))) :
    Nonempty (MarkedCoreCertificateKTwoM B alpha h halpha) :=
  marked_matching_certificate_M alpha h halpha (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun) hMix hpivot

/-- Preferred compact direct-`G_K(2)` constructor for the `M` core.  The genuine arithmetic
level fact `r = 0` supplies a unit value on `ker χ`; the rank-four frame turns it into the
`C̄₀` pivot; canonical B8 transport supplies M3 unit scaling; exact handle/M2/M5 corrections
clear every other row.  Thus the compact level-zero constructor has no residual marked-core
hypothesis. -/
theorem marked_matching_certificate_KTwoM_of_level_zero (B : MarkedRecip Rec K) (alpha : ℕ)
    (halpha : 2 ≤ alpha) (D : MDecomposition alpha) (hr : B.r = 0)
    (f : ContinuousMulEquiv (DM alpha 0 : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiM alpha 0 x) :
    Nonempty (MarkedCoreCertificateKTwoM B alpha 0 (by omega)) := by
  obtain ⟨gbar, hgchi, hgnu⟩ := B.nu_ker_chi_ge 1
  obtain ⟨g, rfl⟩ := surjective_toAbK K gbar
  let q : maxProPQuotient 2 (GalK K) := maxProPMk 2 (GalK K) g
  let x : (DM alpha 0 : Type) := f.symm q
  apply marked_matching_certificate_M_of_chiKer halpha (by omega) D
    (chiCycKTwo (K := K)).toMonoidHom (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun)
  refine ⟨x, ?_, ?_⟩
  · rw [← horient x]
    change chiCycKTwo (K := K) (f (f.symm q)) = 1
    rw [f.apply_symm_apply]
    change chiCycKTwo (K := K) (maxProPMk 2 (GalK K) g) = 1
    rw [chiCycKTwo_maxProPMk, ← chiCycKAb_toAbK]
    exact hgchi
  · change IsUnit (Multiplicative.toAdd (nuUrKTwo B (f (f.symm q))))
    rw [f.apply_symm_apply]
    change IsUnit (Multiplicative.toAdd (nuUrKTwo B (maxProPMk 2 (GalK K) g)))
    rw [nuUrKTwo_maxProPMk, hgnu, hr, pow_zero, one_mul]
    exact isUnit_one

/-- Direct-`G_K(2)` production for an odd `L` marked-core certificate.  This is a certificate
adapter, not a general odd-rank classification theorem: the abstract equivalence and both
marked-correction strata remain explicit inputs. -/
theorem marked_matching_certificate_KTwoSq (B : MarkedRecip Rec K) (h : ℕ) (c : ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x)
    (hMix : SqHandleMixHypothesis h c) (hShear : SqCoreShearHypothesis h c)
    (hpivot : nuUrKTwo B (f (sqMixPivotElem h c)) = Multiplicative.ofAdd (1 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_sq h c (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun) hMix hShear hpivot

/-- The preferred one-binder direct `L` producer: a handle correction that fixes the two core
rows removes the separate shear hypothesis. -/
theorem marked_matching_certificate_KTwoSq_of_fixesCore (B : MarkedRecip Rec K)
    (h : ℕ) (c : ℤ_[2])
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (horient : ∀ x, chiCycKTwo (K := K) (f x) = chiSq h x)
    (hMix : SqHandleMixFixesCore h c)
    (hsigma : nuUrKTwo B (f (dsqSigma h)) = Multiplicative.ofAdd (1 : ℤ_[2]))
    (hx0 : nuUrKTwo B (f (dsqX0 h)) = Multiplicative.ofAdd (0 : ℤ_[2])) :
    Nonempty (MarkedCoreCertificateKTwoSq B h) :=
  marked_matching_certificate_sq_of_fixesCore h c (chiCycKTwo (K := K)).toMonoidHom
    (nuUrKTwo B).toMonoidHom f horient
    ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun) hMix hsigma hx0

end DirectCertificates

/-! ## Exact adapters for the existing even-rank Labute hypotheses -/

section AbstractClassification

variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2)]

omit [FiniteDimensional ℚ_[2] K] in
/-- Apply the existing `NLabHypothesis` to `G_K(2)` and reverse its equivalence into the
source-to-arithmetic direction used by marked-core certificate production.  Every genuinely
unproved input remains visible in the statement.  As on the `M` side, the abstract predicate
identifying the canonical orientation, its proof for the descended cyclotomic character, and the
exact image equality are kept separate; image equality alone is intentionally not treated as
orientation canonicity — `GQ2/Dyadic/Instances/EvenNLabWitness.lean` shows that treating it so
collapses the two even rows. -/
theorem abstractEquiv_KTwoN (alpha h : ℕ)
    (nIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (hLab : NLabHypothesis alpha h nIsCanonical)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hcanonical : nIsCanonical (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)).toMonoidHom)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiN alpha) :
    Nonempty (ContinuousMulEquiv (DN alpha h : Type) (maxProPQuotient 2 (GalK K))) := by
  obtain ⟨e⟩ := hLab (maxProPQuotient 2 (GalK K)) hD hrank hq
    ⟨(chiCycKTwo (K := K)).toMonoidHom, (chiCycKTwo (K := K)).continuous_toFun,
      hcanonical, hrange⟩
  exact ⟨e.symm⟩

omit [FiniteDimensional ℚ_[2] K] in
/-- The corresponding `M` adapter.  The abstract predicate identifying the canonical
orientation, its proof for the descended cyclotomic character, and the exact image equality are
kept separate; image equality alone is intentionally not treated as orientation canonicity. -/
theorem abstractEquiv_KTwoM (alpha h : ℕ)
    (mIsCanonical : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G],
      (G →* ℤ_[2]ˣ) → Prop)
    (hLab : MLabHypothesis alpha h mIsCanonical)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hcanonical : mIsCanonical (maxProPQuotient 2 (GalK K))
      (chiCycKTwo (K := K)).toMonoidHom)
    (hrange : MonoidHom.range (chiCycKTwo (K := K)).toMonoidHom = imChiM alpha) :
    Nonempty (ContinuousMulEquiv (DM alpha h : Type) (maxProPQuotient 2 (GalK K))) := by
  obtain ⟨e⟩ := hLab (maxProPQuotient 2 (GalK K)) hD hrank hq
    ⟨(chiCycKTwo (K := K)).toMonoidHom, (chiCycKTwo (K := K)).continuous_toFun,
      hcanonical, hrange⟩
  exact ⟨e.symm⟩

end AbstractClassification

/-! ## One actual-certificate type for all five selected branches -/

section BranchIndex

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The marked-core certificate belonging to a valid arithmetic branch.  Compact and
procyclic rows of the same Labute family deliberately have the same core certificate; their
different `r`, `epsilon`, and `eta` data enter through the selected word and later
`WordCertificate` construction. -/
def BranchData.CoreCertificate (B : BranchData) (hB : B.Valid) (h : ℕ)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) : Type :=
  match B with
  | .L => MarkedCoreCertificateSq h chiG nuG
  | .N0 alpha => MarkedCoreCertificateN alpha h chiG nuG
  | .Npc alpha _ _ => MarkedCoreCertificateN alpha h chiG nuG
  | .M0 alpha => MarkedCoreCertificateM alpha h (le_trans (by omega) hB) chiG nuG
  | .Mpc alpha _ _ _ => MarkedCoreCertificateM alpha h (le_trans (by omega) hB.1) chiG nuG

/-- A branch that has genuinely reached the marked-core layer, paired with the honest display
data selecting the improved R5 word.  This record does not claim that every field produces such
a value: existence is exactly the remaining branch-selection, Labute-classification, and
marked-correction work. -/
structure SelectedBranchRealization (B : BranchData) (hB : B.Valid) (h : ℕ)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  /-- A compatible concrete display for the exact selected word. -/
  display : B.DisplayFor
  /-- The actual marked-core certificate, not a classification hypothesis. -/
  core : B.CoreCertificate hB h chiG nuG

namespace SelectedBranchRealization

variable {B : BranchData} {hB : B.Valid} {h : ℕ}
  {chiG : G →* ℤ_[2]ˣ} {nuG : G →* Multiplicative ℤ_[2]}

/-- The exact improved presentation selected by a realized branch. -/
def presentation (R : SelectedBranchRealization B hB h chiG nuG) : SelectedPresentation :=
  SelectedPresentation.ofBranch h B R.display

/-- The exact R5 word selected by a realized branch. -/
noncomputable def word (R : SelectedBranchRealization B hB h chiG nuG) :
    PWord (Generator R.presentation.degree) :=
  R.presentation.word

@[simp] theorem presentation_L
    (R : SelectedBranchRealization .L (by trivial) h chiG nuG) :
    R.presentation = .L h := rfl

@[simp] theorem presentation_N0 {alpha : ℕ} {hvalid : (BranchData.N0 alpha).Valid}
    (R : SelectedBranchRealization (.N0 alpha) hvalid h chiG nuG) :
    R.presentation = .N0 alpha h := rfl

@[simp] theorem presentation_Npc {alpha r : ℕ} {eta : ℤ_[2]ˣ}
    {hvalid : (BranchData.Npc alpha r eta).Valid}
    (R : SelectedBranchRealization (.Npc alpha r eta) hvalid h chiG nuG) :
    R.presentation = .Npc alpha r h R.display.data := rfl

@[simp] theorem presentation_M0 {alpha : ℕ} {hvalid : (BranchData.M0 alpha).Valid}
    (R : SelectedBranchRealization (.M0 alpha) hvalid h chiG nuG) :
    R.presentation = .M0 alpha h := rfl

@[simp] theorem presentation_Mpc {alpha r : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    {hvalid : (BranchData.Mpc alpha r epsilon eta).Valid}
    (R : SelectedBranchRealization (.Mpc alpha r epsilon eta) hvalid h chiG nuG) :
    R.presentation = .Mpc alpha r epsilon R.display.display h := rfl

end SelectedBranchRealization

end BranchIndex

/-! ## Core-independent maximal-pro-2 realization and `KSupply` assembly -/

section Realization

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

/-- A standard pro-2 core, already corrected so that its `Ztwo` marking agrees with the
canonical unramified character on `G_K(2)`. -/
structure MarkedCoreRealization (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo) where
  /-- The corrected marked-core equivalence. -/
  equiv : ContinuousMulEquiv (P : Type) (maxProPQuotient 2 (GalK K))
  /-- Full `Ztwo`-valued marking compatibility, before precomposition with `maxProPMk`. -/
  nu_equiv : ∀ x, ztwoIota (nuP x) = nuUrKTwo B (equiv x)

namespace MarkedCoreRealization

variable {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-- The canonical source map `G_K -> P` associated to a corrected core realization. -/
def pro2 (M : MarkedCoreRealization (K := K) (B := B) P nuP) :
    ContinuousMonoidHom (GalK K) P :=
  ⟨M.equiv.symm.toMulEquiv.toMonoidHom.comp (maxProPMk 2 (GalK K)).toMonoidHom,
    M.equiv.symm.continuous_toFun.comp (maxProPMk 2 (GalK K)).continuous_toFun⟩

/-- `pro2` is onto because both the maximal-pro-2 projection and the corrected equivalence are
onto. -/
theorem pro2_surjective (M : MarkedCoreRealization (K := K) (B := B) P nuP) :
    Function.Surjective M.pro2 := by
  intro y
  obtain ⟨g, hg⟩ := quotientMk_surjective _ (M.equiv y)
  exact ⟨g, by
    show M.equiv.symm (maxProPMk 2 (GalK K) g) = y
    rw [show maxProPMk 2 (GalK K) g = M.equiv y from hg]
    exact M.equiv.symm_apply_apply y⟩

/-- The corrected equivalence introduces no extra kernel. -/
theorem ker_pro2 (M : MarkedCoreRealization (K := K) (B := B) P nuP) :
    M.pro2.toMonoidHom.ker = proPKernel 2 (GalK K) := by
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    have hg' : M.equiv.symm (maxProPMk 2 (GalK K) g) = 1 := hg
    have h1 : maxProPMk 2 (GalK K) g = 1 := by
      have h0 := congrArg M.equiv hg'
      rwa [M.equiv.apply_symm_apply, map_one] at h0
    exact (ker_maxProPMk (GalK K)).le (MonoidHom.mem_ker.mpr h1)
  · intro hg
    show M.equiv.symm (maxProPMk 2 (GalK K) g) = 1
    have h1 : maxProPMk 2 (GalK K) g = 1 :=
      MonoidHom.mem_ker.mp ((ker_maxProPMk (GalK K)).ge hg)
    rw [h1, map_one]

/-- The source map computes the original unramified character of `G_K`. -/
theorem nu_compat (M : MarkedCoreRealization (K := K) (B := B) P nuP) (g : GalK K) :
    ztwoIota (nuP (M.pro2 g)) = B.nu_ur (toAbK K g) := by
  rw [M.nu_equiv]
  change nuUrKTwo B (M.equiv (M.equiv.symm (maxProPMk 2 (GalK K) g))) = _
  rw [M.equiv.apply_symm_apply, nuUrKTwo_maxProPMk]

/-! The three adapters below are the only family-specific part of the generic realization.
Each takes the already-existing bridge from the core's `Ztwo` coordinate to its standard
`Multiplicative ℤ_[2]` marking; no classification or marked-correction statement is assumed here,
because the input is an actual `MarkedCoreCertificate*`. -/

/-- Turn an actual `N` marked-core certificate into the common realization. -/
def ofCertificateN {alpha h : ℕ}
    (nuP : ContinuousMonoidHom (DN alpha h) Ztwo)
    (hnuP : ∀ x, ztwoIota (nuP x) = nuN alpha h x)
    (C : MarkedCoreCertificateKTwoN B alpha h) :
    MarkedCoreRealization (K := K) (B := B) (DN alpha h) nuP where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => (hnuP x).trans (C.correction_nu x).symm

/-- Turn an actual `M` marked-core certificate into the common realization. -/
def ofCertificateM {alpha h : ℕ} {halpha : 1 ≤ alpha}
    (nuP : ContinuousMonoidHom (DM alpha h) Ztwo)
    (hnuP : ∀ x, ztwoIota (nuP x) = nuM alpha h halpha x)
    (C : MarkedCoreCertificateKTwoM B alpha h halpha) :
    MarkedCoreRealization (K := K) (B := B) (DM alpha h) nuP where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => (hnuP x).trans (C.correction_nu x).symm

/-- Turn an actual odd-`L` marked-core certificate into the common realization. -/
def ofCertificateSq {h : ℕ}
    (nuP : ContinuousMonoidHom (DSq h) Ztwo)
    (hnuP : ∀ x, ztwoIota (nuP x) = nuSq h x)
    (C : MarkedCoreCertificateKTwoSq B h) :
    MarkedCoreRealization (K := K) (B := B) (DSq h) nuP where
  equiv := C.correction.trans C.abstractEquiv
  nu_equiv := fun x => (hnuP x).trans (C.correction_nu x).symm

end MarkedCoreRealization

namespace KSupply

variable {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- Assemble a `KSupply` from a corrected marked-core realization.  The four pro-2 fields are
proved once here; the three analytic certificate blocks remain the explicit, independently
auditable inputs they already are in `KSupply`. -/
def ofMarkedCoreRealization
    (hdeg : Module.finrank ℚ_[2] K = n) (hhom : SN.homScalar = 2 ^ (n + 2))
    (M : MarkedCoreRealization (K := K) (B := B) P nuP)
    (exactLifting : ExactLiftingSemantics (galKProfinite K) n (qOf K FF) P nuP SN)
    (stokes : StokesDualityCertificate (galKProfinite K) n (qOf K FF) P nuP SN
      (smulZmod2GalK K))
    (determinant : AffineDeterminantCertificate (galKProfinite K) n (qOf K FF) P nuP SN
      T.tameFK M.pro2 (fun g => T.compatF_K M.pro2 nuP M.nu_compat g)
      (smulZmod2GalK K)) :
    KSupply T n P hP nuP SN where
  hdeg := hdeg
  hhom := hhom
  pro2 := M.pro2
  hpro2 := M.pro2_surjective
  ker_pro2 := M.ker_pro2
  nu_compat := M.nu_compat
  exactLifting := exactLifting
  stokes := stokes
  determinant := determinant

end KSupply

end Realization

end


end GQ2.Dyadic
