/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus 5
-/
import GQ2.Dyadic.Instances.RowClauses
import GQ2.Dyadic.Instances.MpcRamifiedRow
import GQ2.Dyadic.Instances.MpcSelectedScalar

/-!
# The blocks the record still carries  (dyadic campaign, lane W85-BLOCKS)

W84-CLAUSES measured the `ℚ₂(√5)` row down to four things: two open analytic clauses at the
candidate carrier (`stokes`, `determinant`), one coefficient `Prop` (`askCStageVanishing`)
carried once at each of the row's two carriers, and, on the `Mpc` row only, a missing
unconditional corrected bundle.  This module works those four blocks.

Sections are added as the lane lands them; the axiom pins at the end carry the honest split.
-/

namespace GQ2.Dyadic.Instances.RecordBlocks

open GQ2 GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Instances

/-! ## §1 The `Mpc` corrected bundle (ticket T4)

W84-CLAUSES §2 narrowed "the residue is uniform across the four rows" to **three**: the two `M0`
rows and the `N0` row get the identical treatment, and `Mpc 2 1 false 1 0` (`ℚ₂(√10)`) does not,
because `MProcyclicExact` has no `exactLiftingRN_unconditional` and its corrected bundle still
carries an `Hsimp`-family hypothesis.

That gap is now closable, and the reason is a file the note did not consult.
`MpcPairings.lean:72` records `MProcyclicExact.RamifiedNormalPairingSeparates` as **not** proved
there, with a precise obstruction (on the ramified reading neither commutator base is trivial,
so `heisCommR_of_trivial_right` does not apply and a fully general commutator law is needed).
That obstruction was subsequently removed: `MpcRamifiedRow.lean:988` proves
`MProcyclicExact.ramifiedNormalPairingSeparates` at `1 ≤ α` for **every** display, and
`MpcSelectedScalar.lean:206` reduces `UniformPushedHsimp` to exactly that one input.  Composing
the two is the whole ticket.

⚠ **"Unconditional" is not the same word here as on the `M` side.**  `MCompact` quantifies over
`(α, h, q)` and nothing else, so its bundle is unconditional in the literal sense.  The `Mpc`
carrier is indexed by a *display* of the field unit `η`, and the reduction needs that display to
be well formed and to represent `η`.  Both are fields of `MpcDisplayFor η`, which is what the
field seam presents, so the honest statement is **unconditional given the display package**, and
that is how §1 states it.  `1 ≤ r` is likewise carried, and it is not free: it is supplied at the
seam by `FieldBranchSelection.valid`, which gives `2 ≤ α ∧ 1 ≤ r` on the `Mpc` branch. -/

section MpcBundle

open GQ2.Dyadic.MProcyclicExact GQ2.Dyadic.Words.Mpc

/-- **The procyclic-`M` uniform pushed residue, for every display package.**  The `Mpc` twin of
`MCompact.uniformPushedHsimp`.  Three second-order inputs feed
`uniformPushedHsimp_of_pairings`; two were already theorems for every display the seam can
present, and the third is `MpcRamifiedRow`'s separation, which needs only `1 ≤ α`. -/
theorem recBl_mpc_uniformPushedHsimp {alpha r pp h q : ℕ} {eta : ℤ_[2]ˣ}
    (hα : 2 ≤ alpha) (hqe : Even q) (d : MpcDisplayFor eta) :
    UniformPushedHsimp alpha r pp h q d.display :=
  uniformPushedHsimp_of_ramified_display hα hqe d (ramifiedNormalPairingSeparates (by omega))

/-- **Corrected exact lifting at the procyclic-`M` presentation, for every display package.**
The `Mpc` twin of `MCompact.exactLiftingRN_unconditional`, and the theorem whose absence made
W84-CLAUSES narrow its uniformity claim from four rows to three.  With it the `Mpc` row joins
the other three: its `exactLifting` clause is `askCStageVanishing` at its own candidate carrier
and nothing else. -/
theorem recBl_mpc_exactLiftingRN {alpha r h q : ℕ} {epsilon : Bool} {eta : ℤ_[2]ˣ}
    (d : MpcDisplayFor eta) (hα : 2 ≤ alpha) (hr : 1 ≤ r) (hqe : Even q)
    {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo) :
    ExactLiftingSemanticsRN (gamma alpha r (p epsilon r) h q eta) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) :=
  exactLiftingRN_of_uniformPushed d (recBl_mpc_uniformPushedHsimp hα hqe d) (by omega) hr hqe nuP

end MpcBundle

/-! ## §2 The coefficient frame (ticket T1)

W84-CLAUSES §3 named this the sharpest item: `rowCl_mCand_isEmpty_boundaryLifts` says that if the
row's frozen `exactLifting` clause holds then `BoundaryLiftsK b F T` is **empty** for every
boundary-framed marked target with `1 < #Φ(K)`, so one frame with a nonempty `BoundaryLiftsK`
refutes the clause, and with it `askCStageVanishing` at the candidate carrier.  The note's
recommended starting point was `MCompact.datumRho`, "a handle-uniform surjection onto a
nontrivial finite 2-group".

**That starting point does not work, and the reason generalises.**  A frame needs a
`SectionSeven.MinimalBlock`, whose `nontrivial_action` field demands a `y` and a `p ∈ P` with
`y p y⁻¹ p⁻¹ ∉ S`: the chief factor `P/S` must be a *nontrivial* `Y`-module.  §2 proves that no
**nilpotent** `Y` admits one, for any marked kernel `L`.  Finite 2-groups are nilpotent, so the
whole "surject onto a nontrivial finite 2-group" strategy is dead, and `datumRho` in particular
is dead twice over: its target `Base ⧸ datum.M` has exponent 2 (`datumQuot_sq`), hence is
abelian.

So the refutation handle is real but its input is not a 2-group quotient: **any refuting frame
must have a target `Y` that is not nilpotent**, i.e. one whose odd part acts nontrivially on a
2-group chief factor.  The smallest shape that can work is `Y` with `L_Y = Q₈`, `S = Z(Q₈)`,
`P = Q₈`, `K = Q₈` and `H = Y/Q₈` of order 3, where `Φ(K) = Z(Q₈)` has order 2; nothing in the
`M`-row's resolver package produces a surjection of the candidate group onto such a `Y` with the
boundary equation satisfied, and this lane did not build one.

This is a **narrowing, not a discharge**: `askCStageVanishing` at the candidate carrier is still
open, and the honest statement of what changed is that the cheap route to refuting it is closed
and the owner call still rests on W81-ASK's recommendation to restate the records against
`ExactLiftingSemanticsRN` (which `rowCl_rn_both_carriers_sqrtFive` already supports at both
carriers). -/

section CoefficientFrame

open GQ2.SectionSeven

variable {Y : Type} [Group Y] [Finite Y]

/-- The centraliser of `S` "one layer up": the elements whose class in `Y ⧸ S` is central.  It is
the largest subgroup on which the `Y`-action mod `S` is trivial, and it is what lets §2 conclude
from a *generator-wise* triviality statement to the whole of `P`, with no decomposition of the
join `S ⊔ X` into a product. -/
private def centralMod (S : Subgroup Y) [S.Normal] : Subgroup Y :=
  (Subgroup.center (Y ⧸ S)).comap (QuotientGroup.mk' S)

omit [Finite Y] in
private theorem mem_centralMod {S : Subgroup Y} [S.Normal] {p : Y} :
    p ∈ centralMod S ↔ ∀ y : Y, y * p * y⁻¹ * p⁻¹ ∈ S := by
  constructor
  · intro hp y
    have hz : (QuotientGroup.mk y : Y ⧸ S) * QuotientGroup.mk p
        = QuotientGroup.mk p * QuotientGroup.mk y :=
      Subgroup.mem_center_iff.mp hp _
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at hz
    have h3 := (‹S.Normal›).conj_mem _
      (S.inv_mem ((‹S.Normal›).conj_mem _ hz y)) p
    have heq : p * (y * ((y * p)⁻¹ * (p * y)) * y⁻¹)⁻¹ * p⁻¹ = y * p * y⁻¹ * p⁻¹ := by group
    rwa [heq] at h3
  · intro hp
    rw [centralMod, Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro z
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective z
    show (QuotientGroup.mk y : Y ⧸ S) * QuotientGroup.mk p
      = QuotientGroup.mk p * QuotientGroup.mk y
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have h := (‹S.Normal›).conj_mem _ (hp y⁻¹) p⁻¹
    have heq : p⁻¹ * (y⁻¹ * p * y⁻¹⁻¹ * p⁻¹) * p⁻¹⁻¹ = (y * p)⁻¹ * (p * y) := by group
    rwa [heq] at h

omit [Finite Y] in
private theorem le_centralMod_self (S : Subgroup Y) [S.Normal] : S ≤ centralMod S := fun s hs =>
  mem_centralMod.mpr fun y => S.mul_mem ((‹S.Normal›).conj_mem _ hs y) (S.inv_mem hs)

/-- The `Y`-lower central series of a normal subgroup: `P₀ = P`, `Pₙ₊₁ = ⁅Y, Pₙ⁆`.  Mathlib's
`Subgroup.lowerCentralSeries P` is the lower central series of `P` **as a group in its own
right** (`⁅Pₙ, P⁆`), which is not the same thing and does not see the `Y`-action; the whole point
here is that the outer group acts. -/
private def yLower (P : Subgroup Y) : ℕ → Subgroup Y
  | 0 => P
  | n + 1 => ⁅(⊤ : Subgroup Y), yLower P n⁆

omit [Finite Y] in
private theorem yLower_normal {P : Subgroup Y} (hP : P.Normal) : ∀ n, (yLower P n).Normal
  | 0 => hP
  | n + 1 => @Subgroup.commutator_normal _ _ ⊤ (yLower P n) inferInstance (yLower_normal hP n)

omit [Finite Y] in
private theorem yLower_le {P : Subgroup Y} (hP : P.Normal) : ∀ n, yLower P n ≤ P
  | 0 => le_rfl
  | n + 1 => le_trans (@Subgroup.commutator_le_right _ _ ⊤ _ (yLower_normal hP n)) (yLower_le hP n)

omit [Finite Y] in
private theorem yLower_le_lcs (P : Subgroup Y) :
    ∀ n, yLower P n ≤ Subgroup.lowerCentralSeries (⊤ : Subgroup Y) n
  | 0 => le_top
  | n + 1 => by
      rw [Subgroup.lowerCentralSeries_succ, Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl (yLower_le_lcs P n)

omit [Finite Y] in
/-- **No nilpotent group carries a §7 minimal block.**

The block asks for a chief factor `P/S` of `Y` inside the marked kernel on which `Y` acts
nontrivially.  In a nilpotent group there is no such factor: the `Y`-lower central series of `P`
reaches `⊥`, and at every step the chief dichotomy forces `S ⊔ ⁅Y, …⁆ = P`, because the only
alternative makes the whole of `P` central mod `S` and so contradicts `nontrivial_action`.  At
the last step `S ⊔ ⊥ = P` reads `S = P`, against `S < P`.

This is what closes the cheap route to ticket T1: every finite 2-group is nilpotent, so no
surjection of the candidate carrier onto a finite 2-group can carry a refuting frame, whatever
`H`, `E`, `b` and `F` are chosen alongside it. -/
theorem recBl_minimalBlock_isEmpty_of_nilpotent [Group.IsNilpotent Y] (L : Subgroup Y) :
    IsEmpty (MinimalBlock L) := by
  refine ⟨fun B => ?_⟩
  haveI hSn : B.S.Normal := B.hS
  haveI hPn : B.P.Normal := B.hP
  -- If the whole of `P` is central mod `S`, the block's `nontrivial_action` fails.
  have hcentral : ¬ B.P ≤ centralMod B.S := by
    intro hle
    obtain ⟨y, p, hp, hnot⟩ := B.nontrivial_action
    exact hnot (mem_centralMod.mp (hle hp) y)
  -- The chief dichotomy propagates `S ⊔ yLower P n = P` down the whole series.
  have key : ∀ n, B.S ⊔ yLower B.P n = B.P := by
    intro n
    induction n with
    | zero => exact sup_eq_right.mpr B.hSP.le
    | succ n ih =>
        haveI := yLower_normal hPn n
        haveI := yLower_normal hPn (n + 1)
        have hle : B.S ⊔ yLower B.P (n + 1) ≤ B.P :=
          sup_le (le_trans B.hSP.le le_rfl) (yLower_le hPn (n + 1))
        rcases B.chief _ (Subgroup.sup_normal _ _) le_sup_left hle with hS | hP
        · exfalso
          refine hcentral ?_
          rw [← ih]
          refine sup_le (le_centralMod_self B.S) fun x hx => mem_centralMod.mpr fun y => ?_
          have : y * x * y⁻¹ * x⁻¹ ∈ yLower B.P (n + 1) :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top y) hx
          exact hS ▸ (le_sup_right.trans_eq hS) this
        · exact hP
  -- Nilpotency drives the series to `⊥`, so the last instance of `key` says `S = P`.
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp ‹Group.IsNilpotent Y›
  have hbot : yLower B.P n = ⊥ := le_bot_iff.mp (hn ▸ yLower_le_lcs B.P n)
  have := key n
  rw [hbot, sup_bot_eq] at this
  exact absurd this B.hSP.ne

/-- **No finite `p`-group carries a §7 minimal block.**  Finite `p`-groups are nilpotent. -/
theorem recBl_minimalBlock_isEmpty_of_isPGroup {p : ℕ} [Fact (Nat.Prime p)] (hY : IsPGroup p Y)
    (L : Subgroup Y) : IsEmpty (MinimalBlock L) :=
  haveI := hY.isNilpotent
  recBl_minimalBlock_isEmpty_of_nilpotent L

omit [Finite Y] in
/-- **No exponent-2 group carries a §7 minimal block.**  Exponent 2 forces commutativity, and a
commutative group is nilpotent of class at most one.  This is the form that applies to
`Base ⧸ datum.M`, the target of every `datumRho`. -/
theorem recBl_minimalBlock_isEmpty_of_sq (h2 : ∀ y : Y, y * y = 1) (L : Subgroup Y) :
    IsEmpty (MinimalBlock L) := by
  have hinv : ∀ y : Y, y⁻¹ = y := fun y => inv_eq_of_mul_eq_one_right (h2 y)
  have hcomm : ∀ a b : Y, a * b = b * a := by
    intro a b
    calc a * b = (a * b)⁻¹ := (hinv _).symm
      _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
      _ = b * a := by rw [hinv, hinv]
  haveI : Group.IsNilpotent Y := by
    refine ⟨⟨1, ?_⟩⟩
    rw [Subgroup.upperCentralSeries_one]
    exact eq_top_iff.2 fun y _ => Subgroup.mem_center_iff.mpr fun g => hcomm g y
  exact recBl_minimalBlock_isEmpty_of_nilpotent L

end CoefficientFrame

/-! ## §3 The Stokes conjuncts at the compact-`M` candidate (ticket T2)

W84-CLAUSES did not attempt this clause and said why: the `L` row's four conjuncts are a file's
worth of plumbing over the generic count suppliers, and "that is a lane, not a section".  It is
also, on inspection, entirely mechanical: `GammaLAnalyticLeaves` never uses anything about the
`L` word except that it has a uniform Heisenberg resolver, a Stokes endpoint, an admissible
marked presentation, a degree identity, and a surjective datum map.  The compact-`M` row has all
five (`Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis`,
`isAdmissibleMarkedPresentation_gammaR`, `MCompact.degree`, `MCompact.datumRho_surjective`), and
`MCompact.uniformPushedHsimp` is unconditional at `2 ≤ α`.  So §3 is the `L` file transposed, and
the four conjuncts become theorems at the `M` candidate with the same hypotheses the row already
carries.

Three things are genuinely different from the `L` transcription and are worth naming:

* the degree is **even**, `2h + 2` rather than `2h + 1`, so `MCompact.degree` feeds the count
  suppliers `n = 2 * h + 2`, and the record spells the same number `2 + 2 * h`.  Those are not
  definitionally equal as `Nat` and `SourceNumerics` is indexed by `n`, so §3 carries the
  transport `recBl_stokes_standard_congr` (the Stokes twin of `rowCl_scalar_standard_congr`,
  which did not exist);
* `MCompact.cardH2_of_uniformPushed` carries `1 ≤ α` and `q ≠ 0`, which the `L` twin does not,
  so the `hpartial` conjunct and everything downstream of it carry them too;
* `MCompact.datumRho` needs `1 ≤ α` as well.

Nothing here needs Tate duality or a local Euler characteristic: the alternative producer
`KAnalytic.stokesDualityCertificate_of_localDualityG` takes both, and neither is available at an
abstract candidate carrier (`GammaLDualityBoundary` records that using them there would be
circular). -/

section MStokes

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact GQ2.Dyadic.MCompact
open GQ2.Dyadic.Certificates GQ2.CardH2GammaA TameSpec

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

variable {α h q : ℕ}

/-- **Degree transport for a Stokes certificate.**  The Stokes twin of
`rowCl_scalar_standard_congr`: the `M` count lane produces `2 * h + 2` and the row records spell
`2 + 2 * h`, and `SourceNumerics` is indexed by the degree, so the two elaborate to different
types.  There was no such lemma in the tree. -/
theorem recBl_stokes_standard_congr {Gam : ProfiniteGrp} {n m : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {smul : DistribMulAction ↥Gam (ZMod 2)} (hnm : n = m)
    (S : StokesDualityCertificate Gam n q P nuP (standardNumerics n) smul) :
    StokesDualityCertificate Gam m q P nuP (standardNumerics m) smul := by
  subst hnm; exact S

/-- **Conjunct 1 at the compact-`M` candidate**: the `T`-cocycle count at every recursion frame.
Transcription of `LSquare.tcocycle_of_uniformPushed`. -/
theorem recBl_mCand_tcocycle (hsimp : UniformPushedHsimp α h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (TCocycle (En.radData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      (standardNumerics (2 * h + 2)).tMult
          (Nat.card (Additive ↥(En.radData l hl).T)) *
        Nat.card (fixedPts (RF.YB ⧸ (En.radData l hl).M)
          (ElemDual (Additive ↥(En.radData l hl).T))) := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI : TopologicalSpace (Additive ↥D.T) := ⊥
  haveI : DiscreteTopology (Additive ↥D.T) := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) (Additive ↥D.T) :=
    DistribMulAction.compHom _ rho.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) (Additive ↥D.T) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × Additive ↥D.T => p.1 • p.2) =
          (fun p : (RF.YB ⧸ D.M) × Additive ↥D.T => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × Additive ↥D.T => (rho p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D) (α := α) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.tcocycle_cardN rho (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres
    (radT_add_self D)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    (rhoPrimeK_surjective RF b F D rfl ρ) (MCompact.degree h)
    (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D)) hb.2

/-- **Conjunct 2 at the compact-`M` candidate**: the `(T^∨)^C` separation clause, via the
word-side marking route.  Transcription of `LSquare.hsep_of_uniformPushed`. -/
theorem recBl_mCand_hsep (hsimp : UniformPushedHsimp α h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC)
    (c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    (hvan : letI := scalarActionZmodTwo ((gamma α h q : Type))
      ∀ chi : ↥(TCharC (En.radData l hl)),
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c = 0) :
    TLiftable (descSigma_spec En l hl Dsc) c := by
  let D := En.radData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  letI := scalarActionZmodTwo (RF.YB ⧸ D.M)
  have hb := Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := RF.YB ⧸ D.M) (A := Additive ↥D.T) (radT_add_self D) (α := α) (h := h) (q := q) hqe
  have hres2 : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (ZMod 2) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (ZMod 2) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresT : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent (RF.YB ⧸ D.M))))
      (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M)) := by
    let incl : ContinuousMonoidHom
        (WordLift (Additive ↥D.T) (RF.YB ⧸ D.M))
        (HeisLift (Additive ↥D.T) (RF.YB ⧸ D.M)) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  exact Count.hsep_field_goal_marking b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (scalarActionZmodTwo _) (scalarActionZmodTwo_triv _)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) (fun _ => rfl)
    (isWildTwo_of_gammaGen rho (rhoPrimeK_surjective RF b F D rfl ρ) (fun _ => rfl))
    hres2 hresT (hsimp (RF.YB ⧸ D.M) rho (Additive ↥D.T) (radT_add_self D))
    hb.2 c hvan

/-- Right separation for the descent module at the compact-`M` candidate: the fork feeding
conjunct 3.  Transcription of `LSquare.hrsep_of_uniformPushed`. -/
theorem recBl_mCand_hrsep (hsimp : UniformPushedHsimp α h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (ρ : BoundaryLiftsK b F RF.TC) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    letI : TopologicalSpace (En.descData l hl).Vmod := ⊥
    haveI : DiscreteTopology (En.descData l hl).Vmod := ⟨rfl⟩
    letI : DistribMulAction ((gamma α h q : Type)) (En.descData l hl).Vmod :=
      DistribMulAction.compHom (En.descData l hl).Vmod
        (rho0 (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ))
    letI : TopologicalSpace (ElemDual (En.descData l hl).Vmod) := ⊥
    haveI : DiscreteTopology (ElemDual (En.descData l hl).Vmod) := ⟨rfl⟩
    IsRightSeparating ((gamma α h q : Type)) (En.descData l hl).Vmod := by
  let D := En.radData l hl
  let DD := En.descData l hl
  let rho := rhoPrimeK RF b F D rfl ρ
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction ((gamma α h q : Type)) DD.Vmod :=
    DistribMulAction.compHom DD.Vmod (rho0 DD rho)
  letI : TopologicalSpace (ElemDual DD.Vmod) := ⊥
  haveI : DiscreteTopology (ElemDual DD.Vmod) := ⟨rfl⟩
  letI : TopologicalSpace DD.C0 := ⊥
  haveI : DiscreteTopology DD.C0 := ⟨rfl⟩
  letI := scalarActionZmodTwo DD.C0
  let theta := Count.rho0Continuous DD rho
  have hcompat : ∀ (g : ((gamma α h q : Type))) (a : DD.Vmod), g • a = theta g • a :=
    fun _ _ => rfl
  haveI : ContinuousSMul ((gamma α h q : Type)) (ElemDual DD.Vmod) := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × ElemDual DD.Vmod => p.1 • p.2) =
          (fun p : DD.C0 × ElemDual DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × ElemDual DD.Vmod => (theta p.1, p.2)) := by
      funext p
      exact elemDual_compat theta hcompat p.1 p.2
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hb := Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := DD.C0) (A := DD.Vmod) (Vmod_exp2 DD) (α := α) (h := h) (q := q) hqe
  have hresS : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ZMod 2) DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisScal, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisScal_injective
  have hresP : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift DD.Vmod DD.C0) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hresD : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0)))
      (WordLift (ElemDual DD.Vmod) DD.C0) := by
    let incl : ContinuousMonoidHom
        (WordLift (ElemDual DD.Vmod) DD.C0) (HeisLift DD.Vmod DD.C0) :=
      ⟨Count.heisDual, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisDual_injective
  have hsurj : Function.Surjective theta :=
    LSquare.rho0Continuous_surjective DD rho (rhoPrimeK_surjective RF b F D rfl ρ)
  have hwild := isWildTwo_of_gammaGen theta hsurj (fun _ => rfl)
  have hd := hsimp DD.C0 theta DD.Vmod (Vmod_exp2 DD)
  have hsd : IsSelfDualN (2 * h + 2)
      (fun g => theta (gammaGen (2 + 2 * h) q (mCompactW α h) g))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent DD.C0))) DD.Vmod :=
    Count.isSelfDualN_of_stokesDuality (MCompact.degree h) hd
      (lower_rel theta (fun _ => rfl)
        (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hresP) hb.2
  exact Count.isRightSeparating_of_selfDualN theta hcompat (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hwild
    hresS hresP hresD hb.1 hsd hb.2 (Vmod_exp2 DD)

/-- **Conjunct 3 at the compact-`M` candidate**: the nonzero-character obstruction.
Transcription of `LSquare.hpartial_of_uniformPushed`; `1 ≤ α` and `q ≠ 0` enter here, through
`MCompact.cardH2_of_uniformPushed`. -/
theorem recBl_mCand_hpartial (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α) (hq0 : q ≠ 0)
    (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR) (Dsc : Descent (En.radData l hl))
    (ρ : BoundaryLiftsK b F RF.TC) (chi : ↥(TCharC (En.radData l hl)))
    (hchi : chi ≠ 0) :
    letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∃ c : VCocycle (En.descData l hl) (rhoPrimeK RF b F (En.radData l hl) rfl ρ),
      betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi c ≠
        betaChi (descSections En l hl Dsc) (descSigma_spec En l hl Dsc) chi
          (0 : VCocycle (En.descData l hl)
            (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) :=
  Count.hpartial_field_goal b F En l hl Dsc ρ (scalarActionZmodTwo _)
    (scalarActionZmodTwo_triv _) (cardH2_of_uniformPushed hsimp hα hq0 hqe)
    (recBl_mCand_hrsep hsimp hqe b F En l hl ρ) chi hchi

/-- **Conjunct 4 at the compact-`M` candidate**: the simple nontrivial `V`-cocycle count.
Transcription of `LSquare.hZcard_of_uniformPushed`.  This one is also what the determinant
bridge needs for its finiteness step, so §4 consumes it too. -/
theorem recBl_mCand_hZcard (hsimp : UniformPushedHsimp α h q) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    {Y : Type} [Group Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} {RF : RecursionFrame T Blk}
    (b : ContinuousMonoidHom ((gamma α h q : Type)) ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E) (En : RF.Enrichment) (l : RF.DR)
    (hl : l ≠ RF.zeroDR)
    (hsimple : ∀ W : AddSubgroup En.Vmod,
      (∀ g : RF.YC, ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hVne : ∃ v : En.Vmod, v ≠ 0)
    (hnt : ∃ (g : RF.YC) (v : En.Vmod), g • v ≠ v)
    (ρ : BoundaryLiftsK b F RF.TC) :
    Nat.card (VCocycle (En.descData l hl)
        (rhoPrimeK RF b F (En.radData l hl) rfl ρ)) =
      Nat.card En.Vmod *
        (standardNumerics (2 * h + 2)).h1Mult (Nat.card En.Vmod) := by
  let D := En.radData l hl
  let DD := En.descData l hl
  letI : TopologicalSpace DD.Vmod := ⊥
  haveI : DiscreteTopology DD.Vmod := ⟨rfl⟩
  letI : DistribMulAction RF.YC DD.Vmod :=
    (inferInstance : DistribMulAction RF.YC En.Vmod)
  letI : DistribMulAction ((gamma α h q : Type)) DD.Vmod :=
    DistribMulAction.compHom _ ρ.1.1.toMonoidHom
  haveI : ContinuousSMul ((gamma α h q : Type)) DD.Vmod := by
    constructor
    have hfac :
        (fun p : ((gamma α h q : Type)) × DD.Vmod => p.1 • p.2) =
          (fun p : RF.YC × DD.Vmod => p.1 • p.2) ∘
            (fun p : ((gamma α h q : Type)) × DD.Vmod => (ρ.1.1 p.1, p.2)) := by
      funext p; rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.1.1.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI := scalarActionZmodTwo RF.YC
  have hb := Count.resolvesAt_and_endpoint_mCompactFam_uniformHeis
    (C := RF.YC) (A := DD.Vmod) (Vmod_exp2 DD) (α := α) (h := h) (q := q) hqe
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mCompactW α h))
      (MCompact.mCompactFam α h q (omega2Exp (4 * Monoid.exponent RF.YC)))
      (WordLift DD.Vmod RF.YC) := by
    let incl : ContinuousMonoidHom (WordLift DD.Vmod RF.YC) (HeisLift DD.Vmod RF.YC) :=
      ⟨Count.heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl Count.heisPrim_injective
  have hsimple' : IsSimpleModTwo RF.YC DD.Vmod := by
    obtain ⟨v, hv⟩ := hVne
    exact ⟨nontrivial_of_ne v 0 hv, hsimple⟩
  exact Count.hZcardN ρ.1.1
    (fun g v => congrArg (fun c : RF.YC => c • v)
      (rho0_descData_rhoPrimeK b F En l hl ρ g))
    (fun _ _ => rfl) (fun _ => rfl)
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mCompactW α h)) hres
    (Vmod_exp2 DD) (isWildTwo_of_gammaGen ρ.1.1 ρ.1.2 (fun _ => rfl)) ρ.1.2
    (MCompact.degree h) (hsimp RF.YC ρ.1.1 DD.Vmod (Vmod_exp2 DD)) hb.2 hsimple' hnt

/-- **The Stokes certificate at the compact-`M` candidate, from the uniform residue.**  The `M`
twin of `LSquare.stokesDualityCertificate_of_uniformPushed`, at the count lane's degree
spelling. -/
theorem recBl_mCand_stokes_of_uniformPushed (hsimp : UniformPushedHsimp α h q) (hα : 1 ≤ α)
    (hq0 : q ≠ 0) (hqe : Even q) {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2))
      (scalarActionZmodTwo ((gamma α h q : Type))) :=
  ⟨fun b F En l hl ρ => recBl_mCand_tcocycle hsimp hqe b F En l hl ρ,
   fun b F En l hl Dsc ρ c hvan => recBl_mCand_hsep hsimp hqe b F En l hl Dsc ρ c hvan,
   fun b F En l hl Dsc ρ chi hchi =>
    recBl_mCand_hpartial hsimp hα hq0 hqe b F En l hl Dsc ρ chi hchi,
   fun b F En l hl hsimple hVne hnt ρ =>
    recBl_mCand_hZcard hsimp hqe b F En l hl hsimple hVne hnt ρ⟩

/-- **The `M0` row's `stokes` clause is a theorem, unconditionally at `2 ≤ α`**, at the degree
spelling the row records use.  This is the clause W84-CLAUSES left open, and it closes with no
new hypothesis: `MCompact.uniformPushedHsimp` is already unconditional at `2 ≤ α`.

[W86-HOUSE, as of `f0de6ad5`: read "unconditionally at `2 ≤ α`" as this module's shorthand for
"no hypothesis beyond the row's standing three".  The statement below binds `2 ≤ α`, `q ≠ 0`
AND `Even q`, and so does `MCompact.uniformPushedHsimp` (`Even q`).  Nothing is owed at either
frozen `M0` row, where all three are available, and §5's docstring spells the three out
correctly; the shorthand is only a hazard for a reader who greps this line alone.] -/
theorem recBl_mCand_stokes (hα : 2 ≤ α) (hq0 : q ≠ 0) (hqe : Even q)
    {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo} :
    StokesDualityCertificate (GammaR (2 + 2 * h) q (mCompactW α h)) (2 + 2 * h) q P nuP
      (standardNumerics (2 + 2 * h))
      (scalarActionZmodTwo ((GammaR (2 + 2 * h) q (mCompactW α h) : Type))) :=
  recBl_stokes_standard_congr (by omega)
    (recBl_mCand_stokes_of_uniformPushed (uniformPushedHsimp hα hqe) (by omega) hq0 hqe)

end MStokes

/-! ## §4 The candidate determinant (ticket T3)

`SqrtNeg2.lean:893`'s docstring says the two Gauss-`Z` clauses "have no candidate-side supplier
in the repository", and W84-CLAUSES repeated it.  That was accurate for every carrier except the
`L` row, where `LSquare.affineDeterminantCertificate_of_wordPhaseSupply` reduces the whole
certificate to a **word-phase supply** carrying no duality input at all.  §4 puts the same
reduction at the compact-`M` candidate.

**The trap, stated.**  There is a second route, and it must not be taken.  The `G_K`-side clone
`affineDeterminant_galK` discharges both clauses internally through
`gaussZResidueDK_{unramified,ramified}`, each of which takes `D : TateDualityG ↥U 2` and, on the
ramified branch, a `RamifiedCertificate` indexed by the field.  `TateDualityG` is produced only
by `FieldData.tateDualityGalK`, which is gated on `IsLocalDualizingGroup` and so on an open
finite-index embedding into the absolute Galois group.  A word group has no such embedding
without the presentation theorem this campaign is trying to prove, so routing the candidate
determinant through it is circular; `GammaLDualityBoundary`'s docstring says exactly this.  The
word-phase bridge `gaussZResidueK_of_wordPhase` takes **no** duality, and that is the route §4
uses.

**What §4 lands and what it does not.**  It lands the reduction: the `M0` row's `determinant`
clause follows from `recBlWordPhaseSupply`, a statement purely about the Gauss sum of a
word-phase model, given the finiteness that §3's `recBl_mCand_hZcard` now supplies.  It does
**not** land the supply.  The `L` producers `wordPhaseResidueK_unramified_lSq` and
`wordPhaseResidueK_ramified_lSq` run through `lSqWallHandlePhase_gaussSum_standardUnram` and
`…Ram`, which exist only at odd degree `2h + 1`; the compact-`M` word offers only the unsigned
magnitude (`Certificates.MCompact.mCompact_gauss_pow`), and the even-degree sign pins do not
exist.  So the row's residual moves from "the whole determinant certificate, with no supplier
anywhere" to "two even-degree wall-handle phase computations", which is a strictly smaller and
purely combinatorial object.

Two things named in the refined brief are confirmed by construction: the duality-carrying
determinant clone is not reused (no declaration in this module takes a `TateDualityG` or a
`LocalEulerChar`, and neither occurs anywhere in this module outside this paragraph), and
the two `n = 2` numerics facts really are absent -- `Recursion/Numerics.lean` has a `NEqOne`
section and no `NEqTwo`, and no `standardNumerics_two_*` exists in the tree.  §4 routes around
them rather than building them: `gaussUnram` and `gaussRam` are carried symbolically as
`(standardNumerics (2 * h + 2)).gauss…` and never evaluated, so no even-degree sign collapse is
needed at this layer.  It will be needed by whoever builds the supply. -/

section MDeterminant

open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh FoxH
open GQ2.Dyadic.Words GQ2.Dyadic.Words.MCompact GQ2.Dyadic.MCompact
open GQ2.Dyadic.Certificates GQ2.QuadraticFp2

variable {α h q : ℕ}

set_option linter.unusedVariables false in
/-- **The compact-`M` word-phase supply**: the `M` twin of
`LSquare.DeterminantWordPhaseSupply`.  Binder for binder the two clauses of
`AffineDeterminantCertificate`, with the already-summed `GaussZResidueK` conclusion replaced by
a word-phase model whose Gauss sum has the required value.  Stated as a conjunction rather than
a structure because both clauses are `Prop`. -/
def recBlWordPhaseSupply {P : ProfiniteGrp} (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma α h q) P)
    (compat : ∀ g : (gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g)) : Prop :=
  (letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hunram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v = v),
      LSquare.WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 2)).gaussUnram m))
  ∧ (letI := scalarActionZmodTwo ((gamma α h q : Type))
    ∀ {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
      [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
      {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
      (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
      [Blk.frattiniK.Normal] [(Blk.S.subgroupOf Blk.P).Normal] [Blk.K.Normal]
      (hE2 : ∀ e : E, e ^ 2 = 1) (hq0 : q ≠ 0) (hqe : Even q)
      (F : BoundaryFrameK q P H E)
      (hsimple : ∀ W : AddSubgroup (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod,
        (∀ g : (SectionNine.blockFrame T Blk hE2).YC, ∀ w ∈ W, g • w ∈ W) →
          W = ⊥ ∨ W = ⊤)
      (hVne : ∃ v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod, v ≠ 0)
      (hnt : ∃ (g : (SectionNine.blockFrame T Blk hE2).YC)
        (v : (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod), g • v ≠ v)
      (m : ℕ) (hm : 1 ≤ m)
      (hcard : Nat.card (blockEnrichmentDK T Blk hE2 hq0 hqe F).Vmod = 2 ^ (2 * m))
      (l : (SectionNine.blockFrame T Blk hE2).DR)
      (hl : l ≠ (SectionNine.blockFrame T Blk hE2).zeroDR)
      (hram :
        letI := blockPS_commGroup Blk
        letI := SectionNine.headAct T Blk
        ∃ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha (tqTau q) • v ≠ v),
      LSquare.WordPhaseResidueK (sourceBoundaryMapK tame pro2 compat) F
        (blockEnrichmentDK T Blk hE2 hq0 hqe F) l hl
        (scalarActionZmodTwo_triv _)
        ((standardNumerics (2 * h + 2)).gaussRam m))

/-- **The determinant certificate at the compact-`M` candidate, from a word-phase supply.**  The
`M` twin of `LSquare.affineDeterminantCertificate_of_wordPhaseSupply`.  §3's
`recBl_mCand_hZcard` supplies the finiteness of the cocycle group (the `L` proof calls
`hZcard_of_uniformPushed`, which had no `M` counterpart until §3); simplicity and nontriviality
kill the fixed vectors through the generic `hfix_of_simple_nt`; the phase is the only input left.
`2 ≤ α` enters through `MCompact.uniformPushedHsimp`. -/
theorem recBl_mCand_determinant_of_wordPhaseSupply (hα : 2 ≤ α) {P : ProfiniteGrp}
    (nuP : ContinuousMonoidHom P Ztwo)
    (tame : ContinuousMonoidHom (gamma α h q) (Tq q))
    (pro2 : ContinuousMonoidHom (gamma α h q) P)
    (compat : ∀ g : (gamma α h q : Type), nuTq q (tame g) = nuP (pro2 g))
    (S : recBlWordPhaseSupply nuP tame pro2 compat) :
    AffineDeterminantCertificate (gamma α h q) (2 * h + 2) q P nuP
      (standardNumerics (2 * h + 2)) tame pro2 compat
      (scalarActionZmodTwo ((gamma α h q : Type))) := by
  letI := scalarActionZmodTwo ((gamma α h q : Type))
  haveI := scalarActionZmodTwo_continuousSMul ((gamma α h q : Type))
  constructor
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [recBl_mCand_hZcard (uniformPushedHsimp hα hqe) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.1 T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hunram
  · exact fun T Blk _ _ _ hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram ↦ by
      let En := blockEnrichmentDK T Blk hE2 hq0 hqe F
      apply LSquare.gaussZResidueK_of_wordPhase
        (sourceBoundaryMapK tame pro2 compat) F En l hl (scalarActionZmodTwo_triv _)
      · intro rho
        apply (Nat.card_ne_zero.mp ?_).2
        rw [recBl_mCand_hZcard (uniformPushedHsimp hα hqe) hqe
          (sourceBoundaryMapK tame pro2 compat) F En l hl hsimple hVne hnt rho]
        exact Nat.mul_ne_zero Nat.card_pos.ne' (Nat.pow_pos Nat.card_pos).ne'
      · intro rho v hfixed
        apply hfix_of_simple_nt (hsimple := hsimple) (hnt := hnt) ?_ v hfixed
        intro c0
        obtain ⟨g, hg⟩ := rho.1.2 c0
        exact ⟨g, (rho0_descData_rhoPrimeK
          (sourceBoundaryMapK tame pro2 compat) F En l hl rho g).trans hg⟩
      · exact S.2 T Blk hE2 hq0 hqe F hsimple hVne hnt m hm hcard l hl hram

/-- Degree transport for a determinant certificate, the twin of `recBl_stokes_standard_congr`. -/
theorem recBl_determinant_standard_congr {Gam : ProfiniteGrp} {n m : ℕ} {P : ProfiniteGrp}
    {nuP : ContinuousMonoidHom P Ztwo} {tame : ContinuousMonoidHom Gam (Tq q)}
    {pro2 : ContinuousMonoidHom Gam P}
    {compat : ∀ g : (Gam : Type), nuTq q (tame g) = nuP (pro2 g)}
    {smul : DistribMulAction ↥Gam (ZMod 2)} (hnm : n = m)
    (S : AffineDeterminantCertificate Gam n q P nuP (standardNumerics n) tame pro2 compat smul) :
    AffineDeterminantCertificate Gam m q P nuP (standardNumerics m) tame pro2 compat smul := by
  subst hnm; exact S

end MDeterminant

/-! ## §5 The row, restated

`rowCl_candidate_equiv_galK_sqrtFive` carried four binders after W84-CLAUSES: the `stokes` and
`determinant` certificates at the candidate carrier, and `askCStageVanishing` at each of the
row's two carriers.  §3 discharges the first outright.  §4 replaces the second by the word-phase
supply.  The two coefficient `Prop`s are untouched, and §2 says why the cheap way to refute them
does not exist.

| W83-RECORDS obligation | after W84-CLAUSES | after this lane |
| --- | --- | --- |
| `cand` `exactLifting` at `Γ_R` | `askCStageVanishing` at `Γ_R` | unchanged (§2 narrows the refutation route) |
| `cand` `scalar` at `Γ_R` | discharged | discharged |
| `cand` `stokes` at `Γ_R` | **open** | **discharged**, `recBl_mCand_stokes`, no new hypothesis |
| `cand` `determinant` at `Γ_R` | **open**, no supplier anywhere | `recBlWordPhaseSupply`, two even-degree phase computations |
| `ASK` `exactLifting` at `G_K` | `askCStageVanishing` at `G_K` | unchanged |
| `ASK` `stokes` at `G_K` | discharged | discharged |

So the row's residue is now **one word-phase supply and two instances of one coefficient
`Prop`**, and the coefficient `Prop` is the same statement at both carriers, which is the finding
W84-CLAUSES built its module around. -/

section SqrtFiveRow

open GQ2.Dyadic.Instances.CanonicalRecords GQ2.Dyadic.FieldBranchId GQ2.Dyadic.Fields
open GQ2.Dyadic.FieldSqrtFive GQ2.Dyadic.Instances.MCompactCore
open GQ2.Dyadic.MCompact GQ2.Dyadic.Words.MCompact TameSpec MarkedCore

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] {R : LocalReciprocity}

/-- **The acceptance statement, with every binder this lane discharged removed.**  Compare
`rowCl_candidate_equiv_galK_sqrtFive`, whose binder list is `candStokes`, `candDeterminant`,
`hvanCand`, `hvanK`.  The `stokes` certificate is gone entirely (§3 proves it at `2 ≤ α` with
nothing but `Even q` and `q ≠ 0`, both already available at the row), and the determinant
certificate is replaced by the word-phase supply of §4.  What is left is that supply and the two
coefficient `Prop`s. -/
theorem recBl_candidate_equiv_galK_sqrtFive [T2Space (GalK KSqrtFive)]
    (B : MarkedRecip R KSqrtFive) {FF : DyadicUnitFiltration KSqrtFive}
    (F : GenAsmFieldInputs KSqrtFive B FF (SelectedPresentation.M0 2 0).degree)
    (Sdet : recBlWordPhaseSupply (α := 2) (h := 0) (q := qOf KSqrtFive FF)
      (fieldId_mNuZtwo 2 0 (by omega))
      (tameOfSpec (2 + 2 * 0) (qOf KSqrtFive FF) (mCompactW 2 0)
        (mTameSpecializes 2 0 (qOf KSqrtFive FF) (qOf_ne_zero KSqrtFive FF)
          (even_qOf KSqrtFive FF)))
      (mPro2 2 0 (qOf KSqrtFive FF) (by omega) (qOf_ne_zero KSqrtFive FF)
        (even_qOf KSqrtFive FF))
      (mCompat 2 0 (qOf KSqrtFive FF) (by omega) (qOf_ne_zero KSqrtFive FF)
        (even_qOf KSqrtFive FF)
        (mTameSpecializes 2 0 (qOf KSqrtFive FF) (qOf_ne_zero KSqrtFive FF)
          (even_qOf KSqrtFive FF))
        (fieldId_mNuZtwo 2 0 (by omega)) (canRec_mNuZtwo_sigma 2 0 (by omega))
        (canRec_mNuZtwo_wild 2 0 (by omega))))
    (hvanCand : askCStageVanishing (GammaR (2 + 2 * 0) (qOf KSqrtFive FF) (mCompactW 2 0))
      (qOf KSqrtFive FF) (DM 2 0) (fieldId_mNuZtwo 2 0 (by omega)))
    (hvanK : askCStageVanishing (galKProfinite KSqrtFive) (qOf KSqrtFive FF)
      (genAsmCore (.M0 2 0)) (fieldId_mNuZtwo 2 0 (by omega))) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup (SelectedPresentation.M0 2 0).degree (qOf KSqrtFive FF)
        (SelectedPresentation.M0 2 0).word : ProfiniteGrp) : Type) (GalK KSqrtFive)) :=
  RowClauses.rowCl_candidate_equiv_galK_sqrtFive B F
    (recBl_mCand_stokes (le_refl 2) (qOf_ne_zero KSqrtFive FF) (even_qOf KSqrtFive FF))
    (recBl_determinant_standard_congr (by omega)
      (recBl_mCand_determinant_of_wordPhaseSupply (le_refl 2) _ _ _ _ Sdet))
    hvanCand hvanK

end SqrtFiveRow



/-! ## Axiom audit

**The honest split, read off the pins below.**

* **Twenty-three of the twenty-four declarations are std-3**: `propext`, `Classical.choice`,
  `Quot.sound` and nothing else.  That covers every one of this lane's own results: the `Mpc`
  bundle, the nilpotency obstruction and its two corollaries, all five Stokes leaves, the packed
  Stokes certificate at both degree spellings, the determinant bridge, and the two degree
  transports.
* **One declaration carries campaign axioms**: `recBl_candidate_equiv_galK_sqrtFive`, which pins
  std-3 together with `{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
  absGalQ2_localEulerCharacteristic, hilbertSymbol_normCriterion_finiteDyadic,
  peripheralCyclotomicAction, relativeStiefelWhitney_dyadic}`.  That is **term for term** the set
  already on `rowCl_candidate_equiv_galK_sqrtFive`, so discharging the row's `stokes` clause and
  reducing its `determinant` clause **adds no axiom to the row's record**.  The six come in
  through the general theorem and the row's arithmetic inputs, not through anything here.

**Elaboration cost.**  Nothing in this module raises `maxHeartbeats`.  That is worth recording,
because the `L` originals do: `GammaLAnalyticLeaves` carries `1200000` on the `tcocycle` and
`hZcard` leaves and `1600000` on `hrsep` and `hpartial`, and
`GammaLDeterminantBridge.affineDeterminantCertificate_of_wordPhaseSupply` carries `1200000`.
The compact-`M` transcriptions of all five elaborate inside the default budget.  The one option
this module does set is `linter.unusedVariables`, on `recBlWordPhaseSupply`, for the same reason
the `L` structure sets it: `hm`, `hcard` and `hVne` are binders of
`AffineDeterminantCertificate` that the word-phase conclusion does not mention, and they are kept
so the supply is binder-for-binder the certificate. -/

section AxiomPins

#print axioms centralMod
#print axioms mem_centralMod
#print axioms le_centralMod_self
#print axioms yLower
#print axioms yLower_normal
#print axioms yLower_le
#print axioms yLower_le_lcs
#print axioms recBlWordPhaseSupply
#print axioms recBl_mpc_uniformPushedHsimp
#print axioms recBl_mpc_exactLiftingRN
#print axioms recBl_minimalBlock_isEmpty_of_nilpotent
#print axioms recBl_minimalBlock_isEmpty_of_isPGroup
#print axioms recBl_minimalBlock_isEmpty_of_sq
#print axioms recBl_stokes_standard_congr
#print axioms recBl_mCand_tcocycle
#print axioms recBl_mCand_hsep
#print axioms recBl_mCand_hrsep
#print axioms recBl_mCand_hpartial
#print axioms recBl_mCand_hZcard
#print axioms recBl_mCand_stokes_of_uniformPushed
#print axioms recBl_mCand_stokes
#print axioms recBl_mCand_determinant_of_wordPhaseSupply
#print axioms recBl_determinant_standard_congr
#print axioms recBl_candidate_equiv_galK_sqrtFive

end AxiomPins

end GQ2.Dyadic.Instances.RecordBlocks
