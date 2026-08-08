/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.StageAbstractionEvenBracketSpan
import GQ2.Dyadic.Instances.StageAbstractionEvenStageClimb
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteStageFunctionals

/-!
# W51-EV3F2 §D: the even kernel-adapted supply

Ticket **EV-3f** of `docs/dyadic/ev4b-stage-abstraction.md` §4, the derivation-family station.
The even clone of `GQ2/Dyadic/Instances/GammaLSylowPreimageFieldLabuteKernelAdaptedSupply.lean`,
whose purpose is to discharge the one gap `StageAbstractionEvenStageClimb.lean` §1 leaves open,
`EvenClimbResidualSupply`, through the seam that
`StageAbstractionEvenBracketSpan.lean` §6 supplies.

## The predicted divergence, and its resolution

The orchestrator flagged a risk: in the L template the *twisted* index `2` plays **three**
roles at once, and if those roles separate in even degree the port cannot proceed by renaming.
The three roles are

1. the index carrying the **diagonal (square-bearing) row** of the literal shift word;
2. the index **omitted from the tail atom set** of the augmented span;
3. the unique index whose **character value is not `≡ 1 (mod 4)`**, which is exactly the
   hypothesis the tail dichotomy (`stageDeriv_tail_{mem,not_mem}_derivKer_of_{even,odd}`)
   consumes at every *other* index.

In even degree roles 1 and 2 visibly separate: the seam note §3 puts the square on coordinate
`0`, while §3(d) omits coordinate `1` from the tail set.  So the risk was real.

**It does not bite, and §1 proves why.**  The even diagonal row is not
`p² · [p, base t]` for a single letter `t` but `p² · [p, base 0 · base 1]`, with a *product*
partner (seam note §3, `evenRawCoreDbarWord_zero_row`).  What
`stageDeriv_diagonal_row_mem_derivKer` actually requires of that partner is
`χ(partner) ≡ −1 (mod 4)`, and here `χ(base 0 · base 1) = v 0 · v 1 = v 1`, because `v 0 = 1`
on both even branches.  So the product partner *transports role 1 from coordinate `0` back to
coordinate `1`*, where roles 2 and 3 already live, and the L coincidence is restored verbatim
at the even twisted index `1`.  The extra bracket that cost §B one central transposition pays
for itself here.

Roles 2 and 3 then agree on both branches for a reason that is not a coincidence:
`nUnit α ≡ −1 (mod 4)` and `mUnit α ≡ 1 (mod 4)` for `α ≥ 2`, so the unique non-`1`-mod-`4`
row value is `vN α 1 = nUnit α` on the `N` branch and `vM α 1 = -1` on the `M` branch, and in
both cases it sits at index `1`.

## Numbering

1. the mod-`4` alignment of the two even value tables (the finding above);
2. the even coordinate derivation family;
3. the two inputs this station still needs, as named `Prop`s;
4. the derivation criterion and the discharge of `EvenClimbResidualSupply`.
-/

namespace GQ2.Dyadic.StageGeneric

noncomputable section

open GQ2
open GQ2.Roe.Labute
open GQ2.Dyadic.EvenRowSupply
open GQ2.Dyadic.MarkedCore
open GQ2.Dyadic.LSquare (IsChiShadowDeriv)

/-! ## §1 The mod-`4` alignment of the even value tables

Everything the derivation calculus asks of a value table is here, and all of it is about the
residue mod `4`.  The two facts that drive it are the defining equations of the even
orientation units, `nUnit_mul` and `mUnit_mul`, which are committed. -/

section Alignment

/-- `v = −(1 + 2^α)⁻¹` is `≡ −1 (mod 4)` once `α ≥ 2`, because `v + 1 = −v · 2^α`. -/
theorem evenKernel_nUnit_add_one_dvd_four {α : ℕ} (hα : 2 ≤ α) :
    (2 : ℤ_[2]) ^ 2 ∣ ((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  refine ⟨-((nUnit α : ℤ_[2]ˣ) : ℤ_[2]) * 2 ^ (α - 2), ?_⟩
  have hmul := nUnit_mul (α := α) (by omega : 1 ≤ α)
  have hpow : (2 : ℤ_[2]) ^ α = 2 ^ 2 * 2 ^ (α - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow] at hmul
  linear_combination hmul

/-- `u = (1 − 2^α)⁻¹` is `≡ 1 (mod 4)` once `α ≥ 2`, because `u − 1 = u · 2^α`. -/
theorem evenKernel_mUnit_sub_one_dvd_four {α : ℕ} (hα : 2 ≤ α) :
    (2 : ℤ_[2]) ^ 2 ∣ ((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  refine ⟨((mUnit α : ℤ_[2]ˣ) : ℤ_[2]) * 2 ^ (α - 2), ?_⟩
  have hmul := mUnit_mul (α := α) (by omega : 1 ≤ α)
  have hpow : (2 : ℤ_[2]) ^ α = 2 ^ 2 * 2 ^ (α - 2) := by
    rw [← pow_add]; congr 1; omega
  rw [hpow] at hmul
  linear_combination hmul

/-- **Role 3 on the `N` branch**: every row value away from the twisted index `1` is
`≡ 1 (mod 4)`.  On this branch they are all literally `1`. -/
theorem evenKernel_vN_sub_one_dvd_four {α h : ℕ} (i : Fin (MarkedCore.coreRank h))
    (hi : i ≠ 1) : (2 : ℤ_[2]) ^ 2 ∣ ((vN α i : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  refine evenIndex_cases
    (P := fun i ↦ i ≠ 1 → (2 : ℤ_[2]) ^ 2 ∣ ((vN α i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    ?_ ?_ ?_ ?_ ?_ ?_ i hi
  · exact fun _ ↦ by rw [vN_zero]; simp
  · exact fun h1 ↦ absurd rfl h1
  · exact fun _ ↦ by rw [vN_two]; simp
  · exact fun _ ↦ by rw [vN_three]; simp
  · exact fun j _ ↦ by rw [vN_handleU]; simp
  · exact fun j _ ↦ by rw [vN_handleV]; simp

/-- **Role 3 on the `M` branch**: away from index `1` the values are `1` except at index `3`,
where `mUnit α ≡ 1 (mod 4)` by `evenKernel_mUnit_sub_one_dvd_four`.  This is the only place
`α ≥ 2` is consumed on the `M` side. -/
theorem evenKernel_vM_sub_one_dvd_four {α h : ℕ} (hα : 2 ≤ α)
    (i : Fin (MarkedCore.coreRank h)) (hi : i ≠ 1) :
    (2 : ℤ_[2]) ^ 2 ∣ ((vM α i : ℤ_[2]ˣ) : ℤ_[2]) - 1 := by
  refine evenIndex_cases
    (P := fun i ↦ i ≠ 1 → (2 : ℤ_[2]) ^ 2 ∣ ((vM α i : ℤ_[2]ˣ) : ℤ_[2]) - 1)
    ?_ ?_ ?_ ?_ ?_ ?_ i hi
  · exact fun _ ↦ by rw [vM_zero]; simp
  · exact fun h1 ↦ absurd rfl h1
  · exact fun _ ↦ by rw [vM_two]; simp
  · exact fun _ ↦ by rw [vM_three]; exact evenKernel_mUnit_sub_one_dvd_four hα
  · exact fun j _ ↦ by rw [vM_handleU]; simp
  · exact fun j _ ↦ by rw [vM_handleV]; simp

/-- **Roles 1 and 2 reunited, `N` branch.**  The diagonal row's *product* partner has character
value `v 0 · v 1 = nUnit α`, which is `≡ −1 (mod 4)`: exactly the hypothesis of
`stageDeriv_diagonal_row_mem_derivKer`, and located at the twisted index `1`. -/
theorem evenKernel_vN_diagonal_add_one_dvd_four {α h : ℕ} (hα : 2 ≤ α) :
    (2 : ℤ_[2]) ^ 2 ∣
      ((vN α (0 : Fin (MarkedCore.coreRank h)) *
        vN α (1 : Fin (MarkedCore.coreRank h)) : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  rw [vN_zero, vN_one, one_mul]
  exact evenKernel_nUnit_add_one_dvd_four hα

/-- **Roles 1 and 2 reunited, `M` branch.**  Here `v 0 · v 1 = -1` on the nose. -/
theorem evenKernel_vM_diagonal_add_one_dvd_four {α h : ℕ} :
    (2 : ℤ_[2]) ^ 2 ∣
      ((vM α (0 : Fin (MarkedCore.coreRank h)) *
        vM α (1 : Fin (MarkedCore.coreRank h)) : ℤ_[2]ˣ) : ℤ_[2]) + 1 := by
  rw [vM_zero, vM_one, one_mul]
  simp

end Alignment

/-! ## §2 The even coordinate derivation family

The clone of `SqStageCoordinateDerivationFamily` (L template, line 92), with two changes forced
by §1 and by the seam note.

* The index set of the derivations is `i₀ ≠ 1`, not `i₀ ≠ 2`: it must be the **tail-atom**
  index set (`evenRawTailAtomSet` omits `1`), and §1 shows that is also the set on which the
  mod-`4` hypothesis holds.
* The family is stated generically in the word datum `W` and the value table `v`, so the `N`
  and `M` branches share it; §1 supplies the branch-specific arithmetic.

`WL`, `IsChiShadowDeriv` and `derivKer` are the committed crossed-derivation calculus, reused
unchanged: every lemma of `GammaLSylowPreimageFieldLabuteStageFunctionals.lean` that this
station consumes is already stated for an arbitrary group, character and functional. -/

section Family

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **A coordinate derivation family for an even stage.**  A choice of exact ambient lift per
row, together with one `χ`-twisted derivation per non-twisted coordinate whose parity pattern
on those lifts is the Kronecker delta. -/
structure EvenKernelDerivationFamily (T : Tuple W v G chi k) where
  /-- One ambient lift per row. -/
  lifts : Fin (MarkedCore.coreRank h) → G
  /-- Each lift hits its table value exactly. -/
  lifts_chi : ∀ i, chi (lifts i) = v i
  /-- Each lift reduces to the marking at level `k`. -/
  lifts_level : ∀ i, levelMk G k (lifts i) = T.generators i
  /-- One functional per non-twisted coordinate. -/
  deriv : ∀ i₀ : Fin (MarkedCore.coreRank h), i₀ ≠ 1 → ContinuousMonoidHom G (WL (k + 1))
  /-- Each functional is a `χ`-shadow derivation. -/
  deriv_base : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
    IsChiShadowDeriv chi (deriv i₀ hi₀)
  /-- Diagonal parity: the functional is odd on its own lift. -/
  deriv_diag : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
    ¬ (2 : ZMod (2 ^ (k + 1))) ∣ ((deriv i₀ hi₀) (lifts i₀)).u
  /-- Off-diagonal parity: it is even on every other non-twisted lift. -/
  deriv_off : ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1)
    (j : Fin (MarkedCore.coreRank h)), j ≠ 1 → j ≠ i₀ →
    (2 : ZMod (2 ^ (k + 1))) ∣ ((deriv i₀ hi₀) (lifts j)).u

end Family

/-! ## §3 The two remaining station boundaries, and the reduction

What is left between §2 and `EvenClimbResidualSupply` splits cleanly into exactly two
boundaries, and §3 proves that those two compose to the goal.  Each is stated as a `Prop` so
the composition is machine-checked now and each can be discharged independently later.

* `EvenKernelDerivKerCriterion` : the even clone of the L crux
  `stageResidual_mem_rawShiftSpan_of_forall_derivKer`: a central element killed by every
  functional of the family lies in the raw shift span.  Its L proof is the augmented-span
  decomposition `residual = shift · tail`, the squarefree normal form on the tail atoms, and
  the diagonal/off-diagonal contradiction.  §1 supplies the mod-`4` hypotheses that
  contradiction consumes, at exactly the indices the even tail atom set uses.
* `EvenKernelRawToBracketSupply` : the raw-to-neutral upgrade, the even clone of the L
  `VariableStageOne` crux `stageResidual_nonempty_actualDefectSupply_of_kernelAdaptedKill`.
  The raw span imposes no character condition on its corrections; the bracket span of §B
  restricts them to the neutral subgroup, and closing that difference is a separate station.

The relator kill is *not* a third boundary: it is folded into
`EvenKernelRelatorKill` below, whose discharge is immediate from the committed
`isLabuteOrientationDatum{M,N}_iff`, since those theorems say precisely that `vN α` and
`vM α` are Labute orientation data, which is the hypothesis the word-lift kill consumes. -/

section Boundaries

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable {chi : ContinuousMonoidHom G ℤ_[2]ˣ} {h k s : ℕ}
variable {W : StageWord (MarkedCore.coreRank h)} {v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ}

/-- **Boundary one.**  The functionals of the family cut out the raw shift span inside the
central layer.  This is the `⟸` half; the `⟹` half is the span kill, which §1 unlocks. -/
def EvenKernelDerivKerCriterion {T : Tuple W v G chi k}
    (F : EvenKernelDerivationFamily T) (hk : 3 ≤ k) : Prop :=
  ∀ z ∈ zLayer G k,
    (∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
      z ∈ derivKer (F.deriv i₀ hi₀) k) →
    z ∈ evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk

/-- The relator kill: every functional of the family annihilates the current defect.  In the L
template this is unconditional, by the word-lift identity for the orientation datum. -/
def EvenKernelRelatorKill {T : Tuple W v G chi k}
    (F : EvenKernelDerivationFamily T) : Prop :=
  ∀ (i₀ : Fin (MarkedCore.coreRank h)) (hi₀ : i₀ ≠ 1),
    stageDefect W G k T.generators ∈ derivKer (F.deriv i₀ hi₀) k

/-- **The raw defect supply**: the inverse defect lies in the raw shift span at every level. -/
def EvenKernelRawDefectSupply (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (T : Tuple W v G chi k),
    (stageDefect W G k T.generators)⁻¹ ∈
      evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk

/-- **Boundary two.**  Raw shift span membership upgrades to bracket span membership. -/
def EvenKernelRawToBracketSupply (s : ℕ) (W : StageWord (MarkedCore.coreRank h))
    (v : Fin (MarkedCore.coreRank h) → ℤ_[2]ˣ) (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (chi : ContinuousMonoidHom G ℤ_[2]ˣ) : Prop :=
  ∀ (k : ℕ) (hk : 3 ≤ k) (T : Tuple W v G chi k) (z : levelQuot G (k + 1)),
    z ∈ evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk →
      z ∈ evenBracketSpan s chi (fun i ↦ canonLift G k (T.generators i))

/-- **The derivation criterion delivers the raw defect**, the even clone of
`sqRawDefectReachable_of_coordinateDerivationFamily`.  The defect is central because the
marking kills the relator, and the relator kill puts it in every functional's kernel, so the
criterion drops its inverse straight into the span. -/
theorem evenKernel_rawDefect_of_family {T : Tuple W v G chi k} (hk : 3 ≤ k)
    (F : EvenKernelDerivationFamily T)
    (Hcrit : EvenKernelDerivKerCriterion F hk) (Hrel : EvenKernelRelatorKill F) :
    (stageDefect W G k T.generators)⁻¹ ∈
      evenRawShiftSpan (fun i ↦ canonLift G k (T.generators i)) hk :=
  Hcrit _ (Subgroup.inv_mem _ (stageDefect_mem_zLayer W k T.relation))
    (fun i₀ hi₀ ↦ Subgroup.inv_mem _ (Hrel i₀ hi₀))

/-- **The reduction.**  The two boundaries compose to the gap
`StageAbstractionEvenStageClimb.lean` §1 left open.  The residual differs from the inverse
defect by the literal shift of the reference correction, which is itself in the raw span, so
raw membership of the inverse defect propagates to the residual, and boundary two carries it
into the bracket span, where §B §6 reads it as neutral reachability. -/
theorem evenKernel_residualSupply_of_supplies
    (Hraw : EvenKernelRawDefectSupply W v G chi)
    (Hup : EvenKernelRawToBracketSupply s W v G chi) :
    EvenClimbResidualSupply s W v G chi := by
  intro k hk T Wc
  rw [evenSharpNeutralResidualReachable_iff_mem_bracketSpan hk Wc]
  refine Hup k hk T _ ?_
  rw [evenSharpNeutralResidualElement]
  refine Subgroup.mul_mem _ (Subgroup.inv_mem _ ?_) (Hraw k hk T)
  exact evenRawDepthShift_mem_shiftSpan _ hk ⟨Wc.correction, Wc.depth⟩

/-- The family route packaged as the raw defect supply, uniformly in the level. -/
theorem evenKernel_rawDefectSupply_of_family
    (Hfam : ∀ (k : ℕ) (hk : 3 ≤ k) (T : Tuple W v G chi k),
      ∃ F : EvenKernelDerivationFamily T,
        EvenKernelDerivKerCriterion F hk ∧ EvenKernelRelatorKill F) :
    EvenKernelRawDefectSupply W v G chi := by
  intro k hk T
  obtain ⟨F, Hcrit, Hrel⟩ := Hfam k hk T
  exact evenKernel_rawDefect_of_family hk F Hcrit Hrel

end Boundaries

end

end GQ2.Dyadic.StageGeneric

/-! ## §4 Axiom pins

Every public declaration of this file, printed.  All are expected at std-3,
`[propext, Classical.choice, Quot.sound]`.  The L template's `KernelAdaptedSupply.lean` prints
`absGalQ2_isTopologicallyFinitelyGenerated` on five of its eleven pins and three further
census axioms on `nonempty_orientedEquiv_oddDegree_of_family_of_digitRepair`, because that
file also closes the classification; this station stops at the span criterion, so it stays at
std-3. -/

section AxiomPins

open GQ2.Dyadic.StageGeneric

-- §1 the mod-4 alignment
#print axioms evenKernel_nUnit_add_one_dvd_four
#print axioms evenKernel_mUnit_sub_one_dvd_four
#print axioms evenKernel_vN_sub_one_dvd_four
#print axioms evenKernel_vM_sub_one_dvd_four
#print axioms evenKernel_vN_diagonal_add_one_dvd_four
#print axioms evenKernel_vM_diagonal_add_one_dvd_four

-- §2 the derivation family
#print axioms EvenKernelDerivationFamily

-- §3 the boundaries and the reduction
#print axioms EvenKernelDerivKerCriterion
#print axioms EvenKernelRelatorKill
#print axioms EvenKernelRawDefectSupply
#print axioms EvenKernelRawToBracketSupply
#print axioms evenKernel_rawDefect_of_family
#print axioms evenKernel_residualSupply_of_supplies
#print axioms evenKernel_rawDefectSupply_of_family

end AxiomPins
