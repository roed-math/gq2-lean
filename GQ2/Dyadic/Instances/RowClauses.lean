/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.CanonicalRecords
import GQ2.Dyadic.Instances.AskCounting
import GQ2.Dyadic.Instances.EvenMRamifiedPairing

/-!
# The analytic clauses at a tied row's candidate carrier  (dyadic campaign, lane W84-CLAUSES)

W83-RECORDS reduced each of the four tied quadratic rows to "the four analytic clauses at the
row's candidate carrier `Γ_R = GammaR n q_K word`, plus two `ASK` blocks at `G_K`".  This module
takes the cheapest row, `M0 2 0` at `ℚ₂(√5)`, and asks what those six things actually cost.

Nothing here is asserted that is not proved; every reduction names the residue it stops at.
-/

namespace GQ2.Dyadic.Instances.RowClauses

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances

/-! ## §1 The frozen (136) coefficient, at an arbitrary carrier

`Instances.AskCounting` measured the gap between the frozen and corrected R-stage coefficients
and drew the equivalence `ExactLiftingSemantics ↔ askCStageVanishing` **at `G_K` only**, because
its corrected input was `correctedRStageSemantics_galK`.  Nothing in that argument is arithmetic:
the two coefficients `zR = #R² · #D_R` and `zRN = #R^{n+1} · #D_R` are frame invariants, and both
of `askC_zRN_eq_zR_of_card_one` and `askC_zRN_ne_zR` are already carrier-free.

So the same equivalence holds at **any** carrier that has the corrected bundle, with the
corrected bundle as an explicit hypothesis in place of the `G_K` theorem.  That is what §1
proves.  `askCStageVanishing` is already stated at a free `Γ : ProfiniteGrp`, so no new `Prop`
is introduced here. -/

section Coefficient

variable {Γ : ProfiniteGrp} {n q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-- **The frozen bundle from the corrected one plus the vanishing, at any carrier.**  The
carrier-free form of `askC_exactLiftingSemantics_galK`: that proof used `G_K` only through
`correctedRStageSemantics_galK`, whose conclusion is the third conjunct of
`ExactLiftingSemanticsRN`, and the first two conjuncts of the two bundles are literally the
same. -/
theorem rowCl_exactLifting_of_stageVanishing
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hvan : askCStageVanishing Γ q P nuP) :
    ExactLiftingSemantics Γ n q P nuP (standardNumerics n) := by
  refine ⟨hRN.1, hRN.2.1, ?_⟩
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F
  have hcorr := hRN.2.2 hE2 hRK hR2 b F
  rcases lt_or_ge 1 (Nat.card ↥Blk.frattiniK) with hR | hR
  · rw [hvan hE2 hRK hR2 b F hR, mul_zero] at hcorr ⊢
    exact hcorr
  · have h1 : Nat.card ↥Blk.frattiniK = 1 := le_antisymm hR Nat.card_pos
    rw [← askC_zRN_eq_zR_of_card_one (n := n) (blockFrameImpl T Blk hE2) h1]
    exact hcorr

/-- **The vanishing from the frozen bundle, at any carrier, at `2 ≤ n`.**  The carrier-free form
of `askC_stageVanishing_of_exactLifting`.  Both bundles evaluate the same left-hand side
`#D_R · e_Γ(B)`, so their right-hand sides agree; at `2 ≤ n` with `1 < #R` the coefficients are
distinct naturals and `ℤ` is a domain. -/
theorem rowCl_stageVanishing_of_exactLifting (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hfroz : ExactLiftingSemantics Γ n q P nuP (standardNumerics n)) :
    askCStageVanishing Γ q P nuP := by
  intro H E _ _ _ _ _ _ _ _ Y _ _ _ _ T Blk hE2 hRK hR2 b F hR
  have hfr := hfroz.2.2 hE2 hRK hR2 b F
  have hcorr := hRN.2.2 hE2 hRK hR2 b F
  have hcoeff : ((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ) ≠ 0 := by
    rw [sub_ne_zero]
    exact fun hc => askC_zRN_ne_zR (blockFrameImpl T Blk hE2) hn hR
      (Nat.cast_injective (R := ℤ) hc.symm)
  have hzero : (((blockFrameImpl T Blk hE2).zR : ℤ)
      - (zRN (blockFrameImpl T Blk hE2) (standardNumerics n) : ℤ))
      * ∑ᶠ l : (blockFrameImpl T Blk hE2).DR,
          (2 * (mBK (blockFrameImpl T Blk hE2) b F l : ℤ)
            - exactImageCountK b F (blockFrameImpl T Blk hE2).TB) = 0 := by
    rw [sub_mul, ← hfr, ← hcorr, sub_self]
  rcases mul_eq_zero.mp hzero with hc | hs
  · exact absurd hc hcoeff
  · exact hs

/-- **The equivalence at any carrier with the corrected bundle, at `2 ≤ n`.**  Wave 81's
`askC_exactLifting_iff_stageVanishing` with `G_K` replaced by an arbitrary `Γ` and its corrected
theorem replaced by a hypothesis. -/
theorem rowCl_exactLifting_iff_stageVanishing (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n)) :
    ExactLiftingSemantics Γ n q P nuP (standardNumerics n)
      ↔ askCStageVanishing Γ q P nuP :=
  ⟨rowCl_stageVanishing_of_exactLifting hn hRN, rowCl_exactLifting_of_stageVanishing hRN⟩

/-- **What carrying the frozen bundle costs, at any carrier.**  Carrier-free form of
`askC_exactImageCount_eq_zero_of_exactLifting`: on every frame with a nontrivial Frattini block
the boundary-framed exact image count of the target vanishes. -/
theorem rowCl_exactImageCount_eq_zero_of_exactLifting (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hfroz : ExactLiftingSemantics Γ n q P nuP (standardNumerics n))
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hR : 1 < Nat.card ↥Blk.frattiniK) :
    exactImageCountK b F T = 0 := by
  have hvan := rowCl_stageVanishing_of_exactLifting hn hRN hfroz hE2 hRK hR2 b F hR
  have hcorr := hRN.2.2 hE2 hRK hR2 b F
  rw [hvan, mul_zero] at hcorr
  letI : Nonempty (blockFrameImpl T Blk hE2).DR := ⟨(blockFrameImpl T Blk hE2).zeroDR⟩
  have hd : (Nat.card (blockFrameImpl T Blk hE2).DR : ℤ) ≠ 0 :=
    Int.natCast_ne_zero.mpr Nat.card_pos.ne'
  rcases mul_eq_zero.mp hcorr with hc | hx
  · exact absurd hc hd
  · exact Nat.cast_eq_zero.mp hx

/-- **The refutation handle, at any topologically finitely generated carrier.**  Carrier-free
form of `askC_isEmpty_boundaryLifts_of_exactLifting`.  Contrapositively: *one* boundary-framed
surjection of `Γ` onto a marked target with `1 < #R` refutes the frozen bundle at `Γ`, and hence
(by §1) `askCStageVanishing Γ q P νP`.  Wave 81 could not use this at `G_K` because the frame is
branch data the arithmetic side does not own; at a candidate carrier the frame data are exactly
what the branch lanes build. -/
theorem rowCl_isEmpty_boundaryLifts_of_exactLifting (hn : 2 ≤ n)
    (hRN : ExactLiftingSemanticsRN Γ n q P nuP (standardNumerics n))
    (hfroz : ExactLiftingSemantics Γ n q P nuP (standardNumerics n))
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP)) (F : BoundaryFrameK q P H E)
    (hR : 1 < Nat.card ↥Blk.frattiniK) :
    IsEmpty (BoundaryLiftsK b F T) := by
  haveI : Finite (BoundaryLiftsK b F T) := finite_boundaryLiftsK b F T hfg
  have hzero : Nat.card (BoundaryLiftsK b F T) = 0 :=
    rowCl_exactImageCount_eq_zero_of_exactLifting hn hRN hfroz hE2 hRK hR2 b F hR
  rcases Nat.card_eq_zero.mp hzero with he | hi
  · exact he
  · exact absurd hi (not_infinite_iff_finite.mpr inferInstance)

end Coefficient

/-! ## §2 The compact-`M` candidate carrier

Two facts the row records had not been read against.

* `MCompact.exactLiftingRN_unconditional` (`Instances/EvenMRamifiedPairing.lean`) proves the
  **corrected** bundle at `GammaR (2+2h) q (mCompactW α h)` from `2 ≤ α`, `q ≠ 0`, `Even q` and
  nothing else: no `Hsimp`, no `StageSep`, no `StageZ`.  Both frozen `M0` rows of the tied table
  are at `α ≥ 2` (`M0 3 0` at `ℚ₂(√2)`, `M0 2 0` at `ℚ₂(√5)`), so it applies at both.
* `MCompact.uniformPushedHsimp` is unconditional at `2 ≤ α` as well, which is what makes the
  scalar clause below free rather than `Hsimp`-conditional.

Feeding the first to §1 turns the row's frozen `exactLifting` clause into the *same* residual
`Prop` that wave 81 isolated on the arithmetic side, with no side condition at all, and carries
the refutation handle to the candidate carrier where the frames are branch data. -/

section MCandidate

open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact GQ2.CardH2GammaA
open GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Count.PilotN GQ2.SectionEight.CentralObstruction FoxH ContCoh

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

variable {α h q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}

/-- The corrected bundle at the compact-`M` candidate, respelled at the row table's degree
`2 + 2h` (`MCompact.exactLiftingRN_unconditional` states it at `2h + 2`).  **Unconditional**
at `2 ≤ α`. -/
theorem rowCl_mCand_exactLiftingRN (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h)) :=
  exactLiftingRN_standard_congr (by omega) (exactLiftingRN_unconditional hα hq0 hqe nuP)

/-- **The `M0` row's `exactLifting` clause, measured.**  At the candidate carrier the frozen
bundle is *equivalent* to `askCStageVanishing` at that carrier, with no analytic side condition.
So the first of W83-RECORDS' "four analytic clauses" is not a clause's worth of analysis at all:
it is exactly the coefficient `Prop` that the row's `ASK` block at `G_K` also reduces to
(`askC_exactLifting_iff_stageVanishing`).  **The two sides of the row record carry one statement
between them, at two carriers.** -/
theorem rowCl_mCand_exactLifting_iff (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    ExactLiftingSemantics (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q P nuP
        (standardNumerics (2 + 2 * h))
      ↔ askCStageVanishing (GammaR (2 + 2 * h) q (mCompactW α h)) q P nuP :=
  rowCl_exactLifting_iff_stageVanishing (by omega)
    (rowCl_mCand_exactLiftingRN hα hq0 hqe nuP)

/-- The candidate carrier is topologically finitely generated: it is an admissible marked
presentation on finitely many generators. -/
theorem rowCl_mCand_tfg (α h q : ℕ) :
    ∃ s : Finset ((gamma α h q : Type)),
      (Subgroup.closure (s : Set ((gamma α h q : Type)))).topologicalClosure = ⊤ :=
  tfg_of_isAdmissibleMarkedPresentation
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h))

/-- **The refutation handle at the `M0` candidate.**  If the row's `exactLifting` clause holds,
then `Γ_R` admits *no* boundary-framed surjection onto any marked target with a nontrivial
Frattini block.  Contrapositively, exhibiting one such surjection refutes the clause, and by
`rowCl_mCand_exactLifting_iff` refutes `askCStageVanishing` at the candidate carrier.  Unlike the
`G_K` form of this statement (`askC_isEmpty_boundaryLifts_of_exactLifting`), whose frames wave 81
could not build, the frames here are candidate-side data. -/
theorem rowCl_mCand_isEmpty_boundaryLifts (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    (hfroz : ExactLiftingSemantics (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h)))
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (b : ContinuousMonoidHom ((GammaR (2 + 2 * h) q (mCompactW α h) : Type))
      ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (hR : 1 < Nat.card ↥Blk.frattiniK) :
    IsEmpty (BoundaryLiftsK b F T) :=
  rowCl_isEmpty_boundaryLifts_of_exactLifting (by omega)
    (rowCl_mCand_exactLiftingRN hα hq0 hqe nuP) hfroz (rowCl_mCand_tfg α h q)
    hE2 hRK hR2 b F hR

/-! ### The `scalar` clause

`ScalarHilbertCertificate` is `#Hom_c(Γ, 𝔽₂) = SN.homScalar` together with `#H²(Γ, 𝔽₂) = 2`.  The
second conjunct is `MCompact.cardH2_of_uniformPushed`.  The first is the generic scalar count
`Count.homCard_field_goal` fed the handle-uniform datum surjection `MCompact.datumRho`; this is
the compact-`M` twin of `LSquare.homCard_of_uniformPushed`, which the `L` row has had since
`GammaLAnalyticLeaves`, and **it had never been stated at the `M` candidate** (no `MCompact`
file mentions `homCard`).  With `MCompact.uniformPushedHsimp` both conjuncts are unconditional
at `2 ≤ α`. -/

/-- Transport only the numerical degree of a scalar certificate, keeping its carrier fixed.
Twin of `MCompact.exactLifting_standard_congr`. -/
theorem rowCl_scalar_standard_congr {Gam : ProfiniteGrp} {n m : ℕ}
    (smul : DistribMulAction ↥Gam (ZMod 2)) (hn : n = m) :
    ScalarHilbertCertificate Gam n (standardNumerics n) smul →
      ScalarHilbertCertificate Gam m (standardNumerics m) smul := by
  subst m
  exact id

/-- **The scalar character count at the compact-`M` candidate**, from the uniform pushed
residue.  `Count.homCard_field_goal` at `MCompact.datumRho`, with the uniform Heisenberg
resolver supplying `ResolvesAt` and `IsStokesEndpoint`. -/
theorem rowCl_mCand_homCard_of_uniformPushed (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α)
    (hq0 : q ≠ 0) (hqe : Even q) :
    Nat.card (ContinuousMonoidHom ((gamma α h q : Type)) (Multiplicative (ZMod 2)))
      = (standardNumerics (2 * h + 2)).homScalar := by
  letI : TopologicalSpace Base := ⊥
  letI : DiscreteTopology Base := ⟨rfl⟩
  letI : DiscreteTopology (Base ⧸ datum.M) := discreteTopology_quotient datum
  letI := scalarActionZmodTwo (Base ⧸ datum.M)
  set rho := datumRho α h q hα hq0 hqe with hrho
  have hb := resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := Base ⧸ datum.M) (A := ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)
    (α := α) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (mCompactFam α h q (omega2Exp (4 * Monoid.exponent (Base ⧸ datum.M))))
      (WordLift (ZMod 2) (Base ⧸ datum.M)) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) (Base ⧸ datum.M))
        (HeisLift (ZMod 2) (Base ⧸ datum.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact homCard_field_goal rho (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres
    (isWildTwo_of_gammaGen rho (datumRho_surjective α h q hα hq0 hqe) (fun _ => rfl))
    (degree h)
    (hsimp (Base ⧸ datum.M) rho (ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0))
    hb.2

/-- **The `M0` row's `scalar` clause is a theorem, unconditionally at `2 ≤ α`.**  So the second
of W83-RECORDS' four analytic clauses costs nothing at all at either frozen `M0` row. -/
theorem rowCl_mCand_scalar (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q) :
    ScalarHilbertCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h)
      (standardNumerics (2 + 2 * h)) (scalarActionZmodTwo _) :=
  rowCl_scalar_standard_congr _ (by omega)
    ⟨rowCl_mCand_homCard_of_uniformPushed (uniformPushedHsimp hα hqe) (by omega) hq0 hqe,
     cardH2_of_uniformPushed (uniformPushedHsimp hα hqe) (by omega) hq0 hqe⟩

end MCandidate

end GQ2.Dyadic.Instances.RowClauses
