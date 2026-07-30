/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.SqCore.Cores
import GQ2.Roe.MarkedPro2
import GQ2.Roe.Labute.Assembly

/-!
# `marked_square_core_rank3`: the rank-three marked core of the `L_sq` family

**Ticket SQ3** of the dyadic campaign (lane SQ), implementing the SQ1 design memo
`docs/dyadic/sq-design.md` §4.2.  This file discharges the obligation the owner commissioned at
gate R2 — the rank-3 marked-core / orientation theorem that the campaign page prices at
`C_mark = 3` (S2.4 §2.4, §7.3, §9.2(4)).

## Why this is an interface file and not a 3000-line development

`GQ2/Dyadic/SqCore/Cores.lean` proves `sqWord_eq_drWord` by `rfl` and `dsq_zero : DSq 0 = DR`:
the `L_sq` rank-3 pro-2 core **is** the frozen Roe core `D_R`, letter for letter (memo V1).
Every rank-3 datum the certificate needs is therefore already a sorry-free theorem of the frozen
ℚ₂ development, and this file *cites* it:

| datum | value | frozen source (under `GQ2/Roe/`) |
|---|---|---|
| Demushkin type | `IsDemushkin 2`, rank `3`, `q = 2` | `DRDemushkin.lean` |
| orientation | Hensel root of `Z³+2Z²+1`; `X ≡ 5, S ≡ 13, Y ≡ 7 (16)` | `OrientationRoot.lean` |
| `im χ` | `ℤ₂ˣ` (Labute `f = 2`) | `ChiR.lean` (`chiR_surjective`) |
| frame | `ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀`, `t = x̄₁ − 2x̄₀`, `x̄₁`-row forced | `DRAbelianization.lean` |
| cup Gram | `[[0,1,0],[1,0,0],[0,0,1]]`, `det = 1` over `𝔽₂` | `DRDemushkin.lean` |
| unramified marking | full `ℤ₂`-valued, `ν(σ) = 1`, `ν(x_i) = 0` | `MarkedPro2.lean` (`nuDR`) |
| Labute classification | `GQ2.Roe.Labute.bLab`, **a theorem** | `Labute/Assembly.lean` |
| matching correction | `markedPro2_R` | `MarkedPro2.lean` |

`BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:141`) is *deliberately specialized to `D_R`* — i.e.
to this very core — and `bLab` proves it sorry-free at std-3, so the anticipated single biggest
cost driver of the lane is zero (memo V3, §2).  There is likewise **no matching-engine port**:
`GQ2/Roe/MarkedMatching.lean`'s masters → span → `evalMatrix` → solve → contract pipeline was
already run for this core (memo V4, §3.1).

## Statements on `D_R`, not on `DSq 0` (memo risk R3)

`dsq_zero` is an `Eq` of `ProfiniteGrp`, so transport along it is a `cast`.  Every rank-3 fact
below is therefore stated **directly about the frozen `DR` names**, and the single `cast` of the
lane lives in `dsqEquivDR` (`Cores.lean` §4), which is the only sanctioned consumer-facing form.
The one statement that mentions `DSq 0` is `gammaRPro2EquivDSqZero`, which is built *from*
`dsqEquivDR` rather than from a fresh transport.

## Contents

* **§1 The frame.**  `SqDecomposition` — the rank-3 abelianization frame in the
  `BDecomposition`/`MDecomposition` house style — with existence `sq_decomposition` and the
  forced row `sq_decomposition_forcedRow`, both discharged field-for-field from
  `br_decomposition` / `br_decomposition_Y`.
* **§2 The four marked-data coordinates**, restated in SQ vocabulary: the Demushkin triple, the
  orientation (existence, the torsion character `χ(t) = −1`, and surjectivity), all nine cup-Gram
  entries, and the full `ℤ₂` unramified marking.
* **§3 The certificate.**  `MarkedSqCoreRank3` and the headline theorem
  **`marked_square_core_rank3`**, in S2.4 §2.4's statement shape with the certificate unbundled
  so that it can be stated before MC5's `MarkedCoreCertificate` exists.
* **§4 The `n = 1` word identification.**  `L_sq` at `n = 1` is Roe's own candidate `Γ_R` as a
  *whole word*, not merely at the core (memo §1.2, §7.5): `gammaRPro2EquivDSqZero` exhibits
  `Γ_R(2) ≅ D_sq(0)`, and the frozen `main_presentation_literal_roe_unconditional` is the
  corresponding hypothesis-free rank-3 word theorem.  **This is a WL-lane discovery**, reported
  in memo §7.5 and not designed against here.
* **§5 Stress tests** pinning the cited data and the axiom content.

## Axiom hygiene — B8 is consumed here, deliberately (memo Q2, risk R4)

Measured with `#print axioms`:

```text
marked_square_core_rank3    : [propext, Classical.choice, GQ2.dyadicOrientation,
                               GQ2.peripheralCyclotomicAction, Quot.sound]
MarkedSqCoreRank3           : [propext, Classical.choice, GQ2.dyadicOrientation, Quot.sound]
SqDecomposition             : [propext, Classical.choice, Quot.sound]   -- std-3
sq_decomposition            : [propext, Classical.choice, Quot.sound]   -- std-3
sq_decomposition_forcedRow  : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_isDemushkin          : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_demushkinRank        : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_demushkinQ           : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_orientation          : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_chi_torsion          : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_cupGram              : [propext, Classical.choice, Quot.sound]   -- std-3
sqCore_nu                   : [propext, Classical.choice, Quot.sound]   -- std-3
gammaRPro2EquivDSqZero      : [propext, Classical.choice, Quot.sound]   -- std-3
```

Two refinements of the memo's §5.3 table, both measured here.  (i) The *structure*
`MarkedSqCoreRank3` already carries B3c — it reaches it through `chiD0G`/`D0`, whose orientation
calibration is a B3c consumer — but **not** B8; B8 is contributed by the discharge alone, through
`markedPro2_R`.  So the certificate's *statement* and its *proof* have different footprints, and
a downstream consumer that only mentions the type inherits B3c only.  (ii) All twelve data and
frame declarations are std-3, so §1–§2 and §4 are consumable with no census axiom at all.

`dyadicOrientation` is **B3c** and `peripheralCyclotomicAction` is **B8**
(`GQ2/Foundations/Axioms.lean:165`, `:259`); both are pre-existing census entries, so the census
stays at **11** and no `G-AX` gate is touched.  B8 enters through `prop_3_8_lift`
(`GQ2/AnabelianBridge/Construction.lean:1089`) inside `markedPro2_R`.

MC2 deliberately *threaded* B8 as an explicit `PeripheralCyclotomicAction` hypothesis rather
than consuming the axiom.  Here we **consume** it, per the memo's §3.4 recommendation and the
owner's Q2 ruling: at rank three over `ℚ₂`, B8 is the relevant published ℚ₂ input and is already
in the census, whereas cloning `exists_matching_iso`/`markedPro2_R` with a
`PeripheralCyclotomicAction` binder would reprove ≈200 lines of *frozen* code to remove an axiom
that is genuinely a ℚ₂ fact at this rank.  MC2's threading exists for the **general-`K`**
rank-four analogues, which is a different obligation.  Note that the h-generic layer of
`Cores.lean` is untouched by this: `chiSq`, `nuSq`, `dsq_zero` and `dsqEquivDR` all print at
std-3, so MC5 can consume them without inheriting B3c/B8.

The prints above are verified out of band, in the repo's usual way — `GQ2/AxiomLedger.lean`
walks the elaborated environment and `scripts/check_axioms.sh` certifies the census — rather
than by committing `#print axioms` commands, which no file under `GQ2/` does.

## Scope: what this file does NOT own

`HandleMixLift`, packet Lemma 6.3 and any degree-`n` handle stabilization (MC5 / MC-HM); the
degree-`n` and general-`K` reach of the certificate (`hData` + `hMix`, memo §4.3, both MC5's);
`MLabHypothesis`/`NLabHypothesis` and gate G-Lab, to whose docket the SQ lane adds **nothing**
(memo §2); the `L_sq` *word* certificate — Fox/Stokes/scalar/quadratic (WL lane).  No file
outside `GQ2/Dyadic/SqCore/` is edited (plan §3 A6: the ℚ₂/Roe development is frozen).
-/

open Multiplicative

namespace GQ2

open Roe Roe.Labute SectionThree

namespace Dyadic

namespace SqCore

/-! ## §1 The rank-three abelianization frame

Abelianizing the core kills both commutators and leaves the relation vector
`ρ_sq = −4x̄₀ + 2x̄₁` (`sqWord_comm`; frozen `drWord_comm`).  Smith normal form over `ℤ₂` gives
`(2,0,0)` in the basis `(t, σ̄, x̄₀)` with `t := x̄₁ − 2x̄₀`, so

```text
L_sq := D_sq^{ab} ≅ ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀ ,        x̄₁ = t + 2x̄₀   (forced row)
```

This is S2.4's prediction R6 reproduced verbatim (memo §1.8).  Note the structural contrast with
the collector's `BDecomposition` frame: there the forced row carries `−2` in the `S̄` slot, while
here it carries `+2` in the `x̄₀` slot and the **marked letter `σ̄` is a free coordinate untouched
by the relation** — so the SQ lane's frame is `NDecomposition`-like (no forced row on a marked
letter) rather than `MDecomposition`-like. -/

/-- **The rank-3 frame of the `L_sq` core** (memo §1.3): `ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀` with torsion
generator `t = x̄₁ − 2x̄₀`; the `x̄₁`-row is forced.

Stated against the frozen `D_R` (memo risk R3(ii)) and discharged verbatim from
`br_decomposition` (`GQ2/Roe/DRAbelianization.lean:462`) — the fields are in bijection with
`BRDecomposition`'s, which is what `sq_decomposition` exhibits. -/
structure SqDecomposition where
  /-- The coordinate isomorphism `L_sq ≅ ℤ/2 ⊕ ℤ₂ ⊕ ℤ₂`. -/
  e : ContinuousMulEquiv (topAbelianization (DR : Type))
        (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
  /-- The torsion coordinate: `t = x̄₁ · x̄₀⁻² ↦ (1,0,0)`. -/
  map_t : e (abMk (drY * (drX ^ 2)⁻¹)) = ofAdd (1, 0, 0)
  /-- The marked letter is a *free* coordinate: `σ̄ ↦ (0,1,0)`. -/
  map_sigma : e (abMk drS) = ofAdd (0, 1, 0)
  /-- `x̄₀ ↦ (0,0,1)`. -/
  map_x0 : e (abMk drX) = ofAdd (0, 0, 1)

/-- **The `L_sq` rank-3 frame exists** — transported field-for-field from the frozen
`br_decomposition`. -/
theorem sq_decomposition : Nonempty SqDecomposition :=
  br_decomposition.elim fun B => ⟨⟨B.e, B.map_t, B.map_s, B.map_x⟩⟩

/-- **The forced row** `x̄₁ ↦ (1, 0, 2)` (i.e. `x̄₁ = t + 2x̄₀`), from `br_decomposition_Y`.
This is S2.4 R6's prediction verbatim. -/
theorem sq_decomposition_forcedRow (B : SqDecomposition) :
    B.e (abMk drY) = ofAdd (1, 0, 2) :=
  br_decomposition_Y ⟨B.e, B.map_t, B.map_sigma, B.map_x0⟩

/-! ## §2 The four marked-data coordinates, restated in SQ vocabulary

These are the antecedents `bLab` consumes plus the two invariants that identify the Labute type
`(p, rank, q, im χ) = (2, 3, 2, ℤ₂ˣ)` — the odd-rank `q = 2`, `f = 2` type. -/

/-- **Demushkin (i)**: the `L_sq` rank-3 core is a Demushkin pro-2 group. -/
theorem sqCore_isDemushkin : IsDemushkin 2 (DR : Type) := isDemushkin_DR

/-- **Demushkin (ii)**: its Demushkin rank is `3` — the memo's `n + 2` at `n = 1`. -/
theorem sqCore_demushkinRank : demushkinRank 2 (DR : Type) = 3 := demushkinRank_DR

/-- **Demushkin (iii)**: its `q`-invariant is `2` (torsion `ℤ/2` in the abelianization, i.e.
`t² = 1` in the frame of §1). -/
theorem sqCore_demushkinQ : demushkinQ (DR : Type) = 2 := demushkinQ_DR

/-- **The orientation exists, and is surjective** (memo §1.4): the canonical `χ_sq = chiR`, with
values `(σ, x₀, x₁) ↦ (S, X, Y)` where `X` is the unique root of `Z³ + 2Z² + 1` in `ℤ₂`, is a
continuous Labute orientation onto the *whole* unit group — the Labute image invariant `f = 2`.

This is the exact antecedent shape `BLabHypothesis` requires. -/
theorem sqCore_orientation : ∃ χ : (DR : Type) →* ℤ_[2]ˣ,
    Continuous χ ∧ IsLabuteOrientation χ ∧ Function.Surjective χ :=
  ⟨chiR.toMonoidHom, chiR.continuous_toFun, isLabuteOrientation_chiR, chiR_surjective⟩

/-- **The orientation on the frame's torsion generator**: `χ(t) = Y·X⁻² = −1` (the note's
equation `(tR)`).  Together with `χ(σ̄) = S` and `χ(x̄₀) = X`, both in `1 + 4ℤ₂` and `≡ 13, 5
(16)`, this is the `C_mark = 3` content: the χ-trivial subspace of the `L_sq` frame is a rank-1
free `ℤ₂`-module *transverse* to `σ̄`, **not** `⟨σ̄⟩` (memo V6, risk R1 — reported to MC5). -/
theorem sqCore_chi_torsion : chiR drY * (chiR drX)⁻¹ ^ 2 = -1 := chiR_torsion

/-- **The mod-2 cup Gram matrix**, all nine entries: in the dual basis `(σ*, x₀*, x₁*)` of
`H¹(D_sq, 𝔽₂) ≅ 𝔽₂³`,

```text
G_sq = [[0,1,0],[1,0,0],[0,0,1]]        det = 1 over 𝔽₂
```

i.e. `⟨x₁,x₁⟩ = 1`, `⟨σ,x₀⟩ = ⟨x₀,σ⟩ = 1`, all six others `0` — S2.4 §1.1 PROBE F verbatim.
Form class `⟨1⟩ ⊥ (one hyperbolic plane)`, the anisotropic direction being `x₁*`; this is S2.4's
`⟨1⟩ ⊥ (h+1 hyperbolic planes)` at `h = 0`, with `x₀ ↔ x₁` transposed relative to the collector.

The reading rule (the reusable MC2 asset): the square `x₁²` contributes the diagonal Bockstein
because `diagCoeff 2 = 1`, and `x₀⁻³`/`x₀^σ` contribute `0` on the diagonal because `diagCoeff`
is `mod 4`-periodic with `diagCoeff 4 = 0`; the off-diagonals come from the two
conjugations/commutators.  Both triangles are listed because graded commutativity of `cup11` is
not formalized.  **Not** to be reformulated through `QuadraticForm`/Arf: at `p = 2` the diagonal
is the Bockstein, which is additive, so this is the Gram matrix of a symmetric bilinear form. -/
theorem sqCore_cupGram :
    drSStar ⌣[drSmul_trivial] drSStar = 0 ∧
    drSStar ⌣[drSmul_trivial] drXStar ≠ 0 ∧
    drSStar ⌣[drSmul_trivial] drYStar = 0 ∧
    drXStar ⌣[drSmul_trivial] drSStar ≠ 0 ∧
    drXStar ⌣[drSmul_trivial] drXStar = 0 ∧
    drXStar ⌣[drSmul_trivial] drYStar = 0 ∧
    drYStar ⌣[drSmul_trivial] drSStar = 0 ∧
    drYStar ⌣[drSmul_trivial] drXStar = 0 ∧
    drYStar ⌣[drSmul_trivial] drYStar ≠ 0 :=
  ⟨drCup_ss, drCup_sx, drCup_sy, drCup_xs, drCup_xx, drCup_xy, drCup_ys, drCup_yx, drCup_yy⟩

/-- **The full `ℤ₂`-valued unramified marking** (memo §1.5): packet normalisation `ν(σ) = 1`,
`ν(x₀) = ν(x₁) = 0`, and surjective.  This is merge gate 6 ("mod-2 is not enough") met at rank
three: the target `Ztwo` is continuously isomorphic to `Multiplicative ℤ_[2]`.  There is **no
forced row** — the abelianized relation involves only wild letters, so `ν(t) = 0` is free. -/
theorem sqCore_nu : nuDR drS = ztwoOne ∧ nuDR drX = 1 ∧ nuDR drY = 1 ∧
    Function.Surjective nuDR :=
  ⟨nuDR_drS, nuDR_drX, nuDR_drY, nuDR_surjective⟩

/-! ## §3 The certificate, and the headline theorem -/

/-- **The `C_mark = 3` marked-core certificate at rank three** — packet `def:core-certificate`
(`proof.tex:711`) instantiated at `K = ℚ₂`, `P = C_sq`, in S2.4 §2.4's statement shape.  Three
clauses:

1. the abstract Demushkin identification `D_sq ≅ D₀` (Labute; supplied by `bLab`);
2. the transported canonical orientation of `D₀` **is** a Labute orientation of `D_sq`, i.e. the
   cyclotomic-orientation clause;
3. the marking-corrected identification of `G_{ℚ₂}(2)` with `D_sq`, matching the **full
   `ℤ₂`-valued** unramified character — with the `Ztwo ≅ Multiplicative ℤ₂` normalisation `ι`
   quantified explicitly and pinned on the generator, exactly as `markedPro2_R` delivers it.

The bundle is stated so as to be field-wise a superset of `mc-design.md` §6.3's five fields; the
`correction` there is already absorbed into `markedEquiv`, which is how `markedPro2_R` supplies
it.  If MC5's `MarkedCoreCertificate` wants the correction split out, `exists_matching_iso`
(`GQ2/Roe/MarkedMatching.lean:1112`) provides it separately.  Reshaping to MC5's exact field list
is ticket SQ4 (memo risk R5). -/
structure MarkedSqCoreRank3 [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (R : LocalReciprocity) where
  /-- Clause 1: the abstract Demushkin isomorphism `D_sq ≅ D₀`. -/
  abstractEquiv : ContinuousMulEquiv (DR : Type) (D0 : Type)
  /-- Clause 2: the transported orientation *is* the canonical Labute orientation. -/
  orientation :
    IsLabuteOrientation (chiD0G.toMonoidHom.comp abstractEquiv.toMulEquiv.toMonoidHom)
  /-- The `Ztwo ≅ Multiplicative ℤ₂` normalisation of the two `ν`-targets. -/
  iota : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2])
  /-- `ι` is pinned on the generator, so the marking is matched on the nose. -/
  iota_one : iota ztwoOne = ofAdd ((1 : ℤ) : ℤ_[2])
  /-- Clause 3: the marking-corrected identification with `G_{ℚ₂}(2)`. -/
  markedEquiv : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)
  /-- …matching the full `ℤ₂`-valued unramified character, read through arbitrary lifts. -/
  marked_nu : ∀ g : AbsGalQ2,
    R.nu_ur (toAb g) = iota (nuDR (markedEquiv (maxProPMk 2 AbsGalQ2 g)))

/-- **`marked_square_core_rank3`** — the obligation commissioned at gate R2, **DISCHARGED**.

The rank-3 marked core of the owner-selected `L_sq` family exists over `ℚ₂`: the `C_mark = 3`
certificate of `MarkedSqCoreRank3` is inhabited, unconditionally.

The proof is four lines because the core *is* `D_R` (`sqWord_eq_drWord`, by `rfl`): `bLab` — a
sorry-free, axiom-free **theorem** of the L-campaign, and one whose `BLabHypothesis` is
deliberately specialized to this very core — supplies clause 1 from the §2 antecedents;
`isLabuteOrientation_comp_iso` supplies clause 2 by orientation functoriality across the B-Lab
isomorphism; and `markedPro2_R` supplies clause 3, the marking correction.

Axioms: std-3 + `dyadicOrientation` (B3c) + `peripheralCyclotomicAction` (B8), both pre-existing
census entries, so the census stays at 11.  See the module docstring for the B8 ruling. -/
theorem marked_square_core_rank3 [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] (R : LocalReciprocity) :
    Nonempty (MarkedSqCoreRank3 R) := by
  obtain ⟨f⟩ : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type)) :=
    bLab isDemushkin_DR demushkinRank_DR demushkinQ_DR
      ⟨chiR.toMonoidHom, chiR.continuous_toFun, isLabuteOrientation_chiR, chiR_surjective⟩
  obtain ⟨ι, hι, e, he⟩ := markedPro2_R R bLab
  exact ⟨⟨f, isLabuteOrientation_comp_iso f, ι, hι, e, he⟩⟩

/-! ## §4 The `n = 1` word identification

The identification of memo §1.2 extends past the core to the **whole word**: `GQ2/Roe/Words.lean`
presents

```text
Γ_R = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}]⟩
```

which is the `L_sq` full relator `R^sq_{L,1}` (`L.py:1238`) plus the tame relation
`τ^σ = τ^{q_K}` at `q_K = 2`.  So **`L_sq` at `n = 1` is Roe's own candidate `Γ_R`**, and its
terminal theorem `main_presentation_literal_roe_unconditional` (`GQ2/Roe/Main.lean:563`,
`Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)`) is a *hypothesis-free* rank-3 word theorem.

Recorded here at the pro-2 level, which is the level this lane owns: `maxPro2Bridge`
(`GQ2/Roe/MaxPro2Bridge.lean:426`, the `Γ_R` half of the note's Lemma 3.1) matches the marked
generators `σ ↦ s`, `τ ↦ 1`, `x₀ ↦ x`, `x₁ ↦ y`, so composing it with `dsqEquivDR.symm` lands in
the SQ lane's own object.

**This is a WL-lane finding** (memo §7.5): the WL rank-3 word-certificate base has a frozen
precedent in `GQ2/Roe/{WildRow,FoxBasic,Stokes,Hessian,Gauss,Tame}.lean`, assembled at
`GQ2/Roe/Main.lean:563`.  It is reported, not designed against — the WL tickets should be
re-priced before dispatch (memo owner question Q4). -/

section WordRankThree

-- The two instances `MarkedPro2.lean`'s `NuComposite` section installs locally for the same
-- purpose; `local` does not export, so they are restated rather than imported.
local instance : T2Space (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

local instance : TotallyDisconnectedSpace (FreeProfiniteGroup (Fin 4) ⧸ NR) :=
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  inferInstance

/-- **`Γ_R(2) ≅ D_sq(0)`**: the maximal pro-2 quotient of the degree-1 `L_sq` word is the SQ
lane's own presented core at `h = 0`.  The `n = 1` word identification of memo §1.2, at the
pro-2 level. -/
noncomputable def gammaRPro2EquivDSqZero :
    ContinuousMulEquiv (maxProPQuotient 2 (FreeProfiniteGroup (Fin 4) ⧸ NR)) (DSq 0 : Type) :=
  maxPro2Bridge.trans dsqEquivDR.symm

end WordRankThree

/-! ## §5 Stress tests

Repo idiom (`GQ2/Roe/DRPresentation.lean` `section StressTests`): the cited facts restated in
their raw frozen form, so that a rename or a change of statement upstream fails *here* rather
than silently changing what the certificate means.  These also pin the axiom content recorded in
the module docstring — every one of them is std-3. -/

section StressTests

/-- Stress: the word identification is definitional, at the presented-core generators. -/
example : sqWord (dsqSigma 0) (dsqX0 0) (dsqX1 0) = drWord (dsqSigma 0) (dsqX0 0) (dsqX1 0) :=
  rfl

/-- Stress: the relator of the degree-1 core is the frozen `drRelator`. -/
example : sqRelator 0 = drRelator := sqRelator_zero

/-- Stress: the presented core at `h = 0` **is** `D_R`, as `ProfiniteGrp`s. -/
example : DSq 0 = DR := dsq_zero

/-- Stress: the `bLab` antecedents are exactly the §2 data, in `BLabHypothesis`'s order. -/
example : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type)) :=
  bLab sqCore_isDemushkin sqCore_demushkinRank sqCore_demushkinQ sqCore_orientation

/-- Stress: `BLabHypothesis` is a theorem, not a hypothesis — the L-campaign result the owner
ordered in place of an axiom. -/
example : BLabHypothesis := bLab

/-- Stress: the anisotropic direction of the Gram form is `x₁*` (the diagonal `1`), and the
hyperbolic plane is `⟨σ*, x₀*⟩`. -/
example : drYStar ⌣[drSmul_trivial] drYStar ≠ 0 ∧ drSStar ⌣[drSmul_trivial] drXStar ≠ 0 :=
  ⟨sqCore_cupGram.2.2.2.2.2.2.2.2, sqCore_cupGram.2.1⟩

/-- Stress: the marked letter `σ` carries the *deep* orientation value, so the S2.4 blanket
"`χ(σ) = 1` for type `L`" cannot be applied to `L_sq` (memo V5, risk R1). -/
example (h : ℕ) : chiSq h (dsqSigma h) = SvalUnit := chiSq_sigma h

/-- Stress: the unramified marking is `ℤ₂`-valued and surjective at every `h`, on the nose. -/
example (h : ℕ) : nuSq h (dsqSigma h) = ofAdd (1 : ℤ_[2]) := nuSq_sigma h

end StressTests

end SqCore

end Dyadic

end GQ2
