/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
import GQ2.Dyadic.SourceTransportRN

/-!
# Replacing the boundary of a corrected source

Exact lifting, Stokes duality, scalar counts, and finite generation depend on the source
carrier and its pro-2 slot, but not on a chosen tame/pro-2 boundary pair.  The affine
determinant is the unique corrected-source clause which sees that pair.

`SourceAnalyticCoreRN` packages the boundary-independent clauses, and
`SourceAnalyticBoundaryRN` packages a boundary and its determinant.  Their `toSource`
constructor is the exact decomposition of `SourceDataRN`.  When an entire source is already
known over the same marked pro-2 slot, `BoundaryReplacementRN` and
`SourceDataRN.replaceBoundary` reuse its analytic core.

Combined with `SourceDataRN.transport`, the latter route reduces a mobile-pivot model to:

1. an abstract equivalence from its candidate group to an analytic core over the same marked
   pro-2 slot;
2. an exact adapted boundary pair; and
3. the affine determinant for that pair.

No equality with a canonical `tameOfSpec` map is required.  The decomposition also makes the
remaining caveat explicit: if the mobile marking is not marking-equivalent to a landed source,
its boundary-independent analytic core must still be constructed.
-/

namespace GQ2.Dyadic.Instances.SourceBoundaryReplacementRN

noncomputable section

open GQ2 GQ2.Dyadic
open GQ2.Dyadic.Instances.FieldFamilyFlexibleModelAssembly
open GQ2.Dyadic.Instances.FieldFamilyFlexibleAssembly
open GQ2.Dyadic.Instances.FieldFamilyGeneralAssemblyExact

/-! ## Exact decomposition of a corrected source -/

/-- The boundary-independent corrected analytic clauses on a fixed marked pro-2 slot. -/
structure SourceAnalyticCoreRN
    (n q : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n) where
  Γ : ProfiniteGrp
  smulZmod2 : DistribMulAction ↥Γ (ZMod 2)
  contSMulZmod2 : letI := smulZmod2; ContinuousSMul ↥Γ (ZMod 2)
  htriv : letI := smulZmod2; ∀ (γ : ↥Γ) (m : ZMod 2), γ • m = m
  tfg : ∃ s : Finset (Γ : Type),
    (Subgroup.closure (s : Set (Γ : Type))).topologicalClosure = ⊤
  exactLifting : ExactLiftingSemanticsRN Γ n q P nuP SN
  stokes : StokesDualityCertificate Γ n q P nuP SN smulZmod2
  scalar : ScalarHilbertCertificate Γ n SN smulZmod2

/-- The boundary pair and determinant over a fixed corrected analytic core. -/
structure SourceAnalyticBoundaryRN
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (A : SourceAnalyticCoreRN n q P hP nuP SN) where
  tame : ContinuousMonoidHom A.Γ (Tq q)
  pro2 : ContinuousMonoidHom A.Γ P
  compat : ∀ g : A.Γ, nuTq q (tame g) = nuP (pro2 g)
  surj : Function.Surjective
    (fun g : A.Γ => (⟨(tame g, pro2 g), compat g⟩ : ↥(boundarySubgroupQ q nuP)))
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 A.Γ
  determinant : AffineDeterminantCertificate A.Γ n q P nuP SN
    tame pro2 compat A.smulZmod2

/-- Assemble a corrected source from its exact analytic-core/boundary decomposition. -/
noncomputable def SourceAnalyticCoreRN.toSource
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (A : SourceAnalyticCoreRN n q P hP nuP SN) (D : SourceAnalyticBoundaryRN A) :
    SourceDataRN n q P hP nuP SN where
  Γ := A.Γ
  tame := D.tame
  pro2 := D.pro2
  compat := D.compat
  surj := D.surj
  ker_pro2 := D.ker_pro2
  smulZmod2 := A.smulZmod2
  contSMulZmod2 := A.contSMulZmod2
  htriv := A.htriv
  tfg := A.tfg
  exactLifting := A.exactLifting
  stokes := A.stokes
  scalar := A.scalar
  determinant := D.determinant

/-- Forget a corrected source to its boundary-independent analytic core. -/
noncomputable def SourceDataRN.toAnalyticCore
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S : SourceDataRN n q P hP nuP SN) :
    SourceAnalyticCoreRN n q P hP nuP SN where
  Γ := S.Γ
  smulZmod2 := S.smulZmod2
  contSMulZmod2 := S.contSMulZmod2
  htriv := S.htriv
  tfg := S.tfg
  exactLifting := S.exactLifting
  stokes := S.stokes
  scalar := S.scalar

/-! ## Boundary replacement on an existing source -/

/-- The boundary-dependent fields needed to retarget a corrected source. -/
structure BoundaryReplacementRN
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S : SourceDataRN n q P hP nuP SN) where
  tame : ContinuousMonoidHom S.Γ (Tq q)
  pro2 : ContinuousMonoidHom S.Γ P
  compat : ∀ g : S.Γ, nuTq q (tame g) = nuP (pro2 g)
  surj : Function.Surjective
    (fun g : S.Γ => (⟨(tame g, pro2 g), compat g⟩ : ↥(boundarySubgroupQ q nuP)))
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 S.Γ
  determinant : AffineDeterminantCertificate S.Γ n q P nuP SN
    tame pro2 compat S.smulZmod2

namespace BoundaryReplacementRN

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
  {S : SourceDataRN n q P hP nuP SN}

/-- The replacement boundary map. -/
noncomputable def b (B : BoundaryReplacementRN S) :
    ContinuousMonoidHom S.Γ ↥(boundarySubgroupQ q nuP) :=
  sourceBoundaryMapK B.tame B.pro2 B.compat

@[simp] theorem b_apply_coe (B : BoundaryReplacementRN S) (g : S.Γ) :
    (B.b g : Tq q × P) = (B.tame g, B.pro2 g) := rfl

end BoundaryReplacementRN

/-- A replacement boundary is a boundary over the forgotten analytic core. -/
noncomputable def BoundaryReplacementRN.toAnalyticBoundary
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    {S : SourceDataRN n q P hP nuP SN} (B : BoundaryReplacementRN S) :
    SourceAnalyticBoundaryRN (SourceDataRN.toAnalyticCore S) where
  tame := B.tame
  pro2 := B.pro2
  compat := B.compat
  surj := B.surj
  ker_pro2 := B.ker_pro2
  determinant := B.determinant

/-- Replace the boundary-dependent fields of a corrected source. -/
noncomputable def SourceDataRN.replaceBoundary
    {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S : SourceDataRN n q P hP nuP SN) (B : BoundaryReplacementRN S) :
    SourceDataRN n q P hP nuP SN :=
  SourceAnalyticCoreRN.toSource (SourceDataRN.toAnalyticCore S)
    (BoundaryReplacementRN.toAnalyticBoundary B)

namespace SourceDataRN

variable {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- A surjective pro-2 marking makes the tame leg of every corrected source surjective. -/
theorem tame_surjective_of_nuP
    (S : SourceDataRN n q P hP nuP SN) (hnuP : Function.Surjective nuP) :
    Function.Surjective S.tame := by
  intro t
  obtain ⟨p, hp⟩ := hnuP (nuTq q t)
  have htp : nuTq q t = nuP p := hp.symm
  obtain ⟨g, hg⟩ := S.surj ⟨(t, p), htp⟩
  exact ⟨g, congrArg (fun x : ↥(boundarySubgroupQ q nuP) => x.val.1) hg⟩

@[simp] theorem replaceBoundary_Gamma
    (S : SourceDataRN n q P hP nuP SN) (B : BoundaryReplacementRN S) :
    (SourceDataRN.replaceBoundary S B).Γ = S.Γ := rfl

end SourceDataRN

/-! ## Handoff to the flexible model assembler -/

namespace FlexibleModelSourceRN

variable {n q : ℕ} {R : PWord (Generator n)} {P : ProfiniteGrp}
  {hP : IsProP 2 P} {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- An analytic core and adapted boundary directly supply a flexible source model. -/
noncomputable def ofAnalyticBoundary
    (A : SourceAnalyticCoreRN n q P hP nuP SN) (D : SourceAnalyticBoundaryRN A)
    (e : ContinuousMulEquiv ((GammaR n q R) : Type) (A.Γ : Type))
    (hnuP : Function.Surjective nuP)
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN n q R P hP nuP SN where
  source := A.toSource D
  equivCandidate := e
  tame_surjective := SourceDataRN.tame_surjective_of_nuP (A.toSource D) hnuP
  wild_isProP := hwild

/-- Transport all boundary-independent clauses of a word certificate across an arbitrary
candidate-group equivalence. -/
noncomputable def transportedWordSourceRN
    {R₀ R₁ : PWord (Generator n)}
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (hq2 : 2 ≤ q) (hqe : Even q)
    (e : ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type)) :
    SourceDataRN n q P hP nuP SN :=
  (W.toSourceRN hq2 hqe).transport e
    (scalarActionZmodTwo (GammaR n q R₁))
    (scalarActionZmodTwo_continuousSMul (GammaR n q R₁))
    (scalarActionZmodTwo_triv (GammaR n q R₁))

/-- A boundary replacement on an existing analytic source supplies a flexible source model. -/
noncomputable def ofBoundaryReplacement
    (S : SourceDataRN n q P hP nuP SN) (B : BoundaryReplacementRN S)
    (e : ContinuousMulEquiv ((GammaR n q R) : Type) (S.Γ : Type))
    (hnuP : Function.Surjective nuP)
    (hwild : IsProP 2 B.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN n q R P hP nuP SN :=
  ofAnalyticBoundary (SourceDataRN.toAnalyticCore S)
    (BoundaryReplacementRN.toAnalyticBoundary B) e hnuP hwild

/-- Start with a word certificate, transport its boundary-independent clauses across an
arbitrary candidate-group equivalence, and install an adapted boundary.  Unlike
`WordCertificateRN.transportWordEquiv`, this constructor requires no tame-compatibility
equation. -/
noncomputable def ofWordEquivBoundaryReplacement
    {R₀ R₁ : PWord (Generator n)}
    (W : WordCertificateRN n q R₀ P hP nuP SN)
    (hq2 : 2 ≤ q) (hqe : Even q)
    (e : ContinuousMulEquiv ((GammaR n q R₁) : Type) ((GammaR n q R₀) : Type))
    (B : BoundaryReplacementRN (transportedWordSourceRN W hq2 hqe e))
    (hnuP : Function.Surjective nuP)
    (hwild : IsProP 2 B.tame.toMonoidHom.ker) :
    FlexibleModelSourceRN n q R₁ P hP nuP SN := by
  let S := transportedWordSourceRN W hq2 hqe e
  exact ofBoundaryReplacement S B (ContinuousMulEquiv.refl _) hnuP hwild

end FlexibleModelSourceRN

/-! ## Direct field-family consumer -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable {Rec : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {B : MarkedRecip Rec K} {FF : DyadicUnitFiltration K}

omit [CompactSpace (GalK K)] [T2Space (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- End-to-end general-K assembly from an arbitrary word equivalence and an adapted boundary.
No equality between the adapted tame map and `tameOfSpec` is assumed. -/
theorem genAsmFlexible_candidate_equiv_galKRN_compatible_ofBoundaryReplacement
    (G : GenAsmFlexibleBranch K B)
    (F : GenAsmCompatibleFieldInputs B FF G.degree)
    {R₀ : PWord (Generator G.degree)}
    (W : WordCertificateRN G.degree (qOf K FF) R₀ G.core
      G.coreIsProP G.nuP (standardNumerics G.degree))
    (e : ContinuousMulEquiv
      ((GammaR G.degree (qOf K FF) G.word) : Type)
      ((GammaR G.degree (qOf K FF) R₀) : Type))
    (D : BoundaryReplacementRN
      (FlexibleModelSourceRN.transportedWordSourceRN W
        (two_le_qOf K FF) (even_qOf K FF) e))
    (hwild : IsProP 2 D.tame.toMonoidHom.ker) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup G.degree (qOf K FF) G.word : ProfiniteGrp) : Type) (GalK K)) :=
  genAsmFlexible_candidate_equiv_galKRN_compatible_ofModelSource G F
    (FlexibleModelSourceRN.ofWordEquivBoundaryReplacement W
      (two_le_qOf K FF) (even_qOf K FF) e D G.hnuP hwild)

#print axioms BoundaryReplacementRN
#print axioms BoundaryReplacementRN.b
#print axioms SourceAnalyticCoreRN
#print axioms SourceAnalyticBoundaryRN
#print axioms SourceAnalyticCoreRN.toSource
#print axioms SourceDataRN.toAnalyticCore
#print axioms BoundaryReplacementRN.toAnalyticBoundary
#print axioms SourceDataRN.replaceBoundary
#print axioms SourceDataRN.tame_surjective_of_nuP
#print axioms FlexibleModelSourceRN.ofAnalyticBoundary
#print axioms FlexibleModelSourceRN.ofBoundaryReplacement
#print axioms FlexibleModelSourceRN.transportedWordSourceRN
#print axioms FlexibleModelSourceRN.ofWordEquivBoundaryReplacement
#print axioms genAsmFlexible_candidate_equiv_galKRN_compatible_ofBoundaryReplacement

end

end GQ2.Dyadic.Instances.SourceBoundaryReplacementRN
