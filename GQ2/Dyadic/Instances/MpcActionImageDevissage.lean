/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.NpcActionImageDevissage
import GQ2.Dyadic.Instances.MpcExact
import GQ2.Dyadic.Word.FoxProd

/-!
# Action-image devissage for the corrected procyclic-`M` row

The row-independent half of the argument is `RowActionImage`, built in
`NpcActionImageDevissage`.  This file supplies the procyclic-`M` inputs and the pushed residue
layer, exactly as its procyclic-`N` twin does.

The one structural difference is the resolver.  The `M` row's family is *display-dependent*: the
`ω₂`-only displays `.one` and `.lit k` use the constant resolver `omega2Exp N`, while a genuine
`.hat num den` display uses the two-valued `npcResolver N ⟨num, den⟩` shared with the `N` row.
`MProcyclicExact.resolvedFamily` already records that case split, and `levelResolver` below
discharges the `LevelResolver` interface one display at a time.  Nothing in the devissage sees
the split: the action-map transport theorem compares two Stokes complexes with *different* words,
so a per-display resolver is no obstacle at all.

What is left over is the same as for the `N` row, and is the honest state of both procyclic rows:
`SimpleActionImageStokes` — Stokes duality at the canonical action-image marking of a *simple*
elementary coefficient — is still an interface, not a theorem, and it splits along the
`tau`-dichotomy into an unramified obligation on a procyclic target
(`finiteActionImage_unramified_closure_sigma`) and a ramified obligation.
-/

namespace GQ2.Dyadic.MProcyclicExact

noncomputable section

open GQ2 GQ2.SectionEight GQ2.FoxH
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.Count GQ2.Dyadic.RowActionImage

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The whole word's ramified Fox row

`MpcStokes` §6 computes the **linear copy's** row (`foxD_mpcLinW_x2`, one entry in the
`x₂`-column) and `MpcFox` §5 shows the **hat copy's** row vanishes (`foxD_mpcHatW_ram`).  Neither
reaches `mpcW` itself, because

```
mpcW α r p η h = prodList (linFactors ++ hatFactors ++ [δ₀², [δ₀,δ₁]] ++ handleTailW h)
```

is a `prodList` over a four-block **append**, and `prodList` does not split syntactically over
`++` — the reason `Words/Mpc.lean` states its own factorization `eval_mpcW_factored` at the
*value* level only.  `Word/FoxProd.lean`'s `foxD_prodList_append` is the Fox-level law, and here
it costs nothing at all: the three trailing blocks each have **zero** row, so every prefix weight
the product rule produces is applied to `0` and no `S₂`-power is ever consulted.

The two new block rows are the easy ones.  The plus block `δ₀²[δ₀,δ₁]` is a square of a
trivially-acting value (hence `2·(−a(x₀)) = 0` in characteristic two) times a commutator of two
such (hence `0` by `foxD_comm_of_trivial`); the handle tail is empty at `h = 0` and the single
handle block otherwise, whose row is WN0-a's `foxD_handlesW`.
-/

section FullRow

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The handle tail's Fox row vanishes**, at every handle count: the `Mpc` row is on the
no-node-at-`h = 0` handle shape, so the tail is the empty list at `h = 0` and the single block
`H_h` otherwise. -/
theorem foxD_prodList_handleTailW
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) :
    foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = 0 := by
  cases h with
  | zero => rfl
  | succ n =>
      rw [show handleTailW (n + 1) = [handlesW (n + 1)] from rfl, PWord.prodList_cons,
        PWord.prodList_nil, foxD_mul, foxD_one, smul_zero, add_zero]
      exact foxD_handlesW t E E₂ hwild a

/-- **The plus block has zero Fox row** in characteristic two at the ramified reading.  Both
δ-letters evaluate into `trivAct` (`trivAct_dW_ram`), so the square contributes the doubled row
`2·D(δ₀)` and the commutator contributes nothing. -/
theorem foxD_plusW (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (plusW h) = 0 := by
  have ht0 : PWord.evalFin ⇑t E E₂ (dW h 0) ∈ trivAct C V := trivAct_dW_ram t E E₂ hwild hTodd 0
  have ht1 : PWord.evalFin ⇑t E E₂ (dW h 1) ∈ trivAct C V := trivAct_dW_ram t E E₂ hwild hTodd 1
  have hsq : foxD ⇑t a E E₂ (PWord.zpow (dW h 0) ((2 : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast, WordLift.sum_pow_smul_of_trivial (mem_trivAct.mp ht0), two_nsmul,
      hV₂]
  have hcm : foxD ⇑t a E E₂ (PWord.comm (dW h 0) (dW h 1)) = 0 :=
    foxD_comm_of_trivial _ _ _ _ ht0 ht1
  rw [plusW, MCompact.foxD_prodList_pair, hsq, hcm, smul_zero, add_zero]

/-- **The whole word's Fox row is the linear copy's**, at σ-free offsets on a ramified
elementary coefficient: the hat copy, the plus block and the handle tail all die, so no prefix
weight survives. -/
theorem foxD_mpcW_eq_mpcLinW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay)
    (hσ : a Generator.sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h) = foxD ⇑t a E E₂ (mpcLinW α r pp η h) := by
  have hhat : foxD ⇑t a E E₂ (PWord.prodList (hatFactors α r pp η h)) = 0 :=
    foxD_mpcHatW_ram t E E₂ a hσ hwild hτfpf hTodd hα r pp η hV₂
  have hplus : foxD ⇑t a E E₂
      (PWord.prodList [PWord.zpow (dW h 0) ((2 : ℕ) : ℤ), PWord.comm (dW h 0) (dW h 1)]) = 0 :=
    foxD_plusW t E E₂ a hwild hTodd hV₂
  have htail : foxD ⇑t a E E₂ (PWord.prodList (handleTailW h)) = 0 :=
    foxD_prodList_handleTailW t E E₂ a hwild
  rw [mpcW, mpcLinW, foxD_prodList_append, foxD_prodList_append, foxD_prodList_append, hhat,
    hplus, htail, smul_zero, smul_zero, smul_zero, add_zero, add_zero, add_zero]

/-- **The procyclic-`M` word's ramified Fox row is a single entry**, at every `(α ≥ 1, r, p, η,
h)`:

```
D(R_{M,pc})(a) = S₂^{−s}·σ^{−n}·a(x₂)
```

at σ-free offsets on a ramified elementary coefficient.  This is the **compact shape** — the
row is supported on `x₂` alone, with an invertible operator in front, exactly like
`MCompact.mCompactWildRow` read at `P ↦ 0` — and **not** the two-entry procyclic-`N` shape. -/
theorem foxD_mpcW_x2 {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) {η : EtaDisplay} {nη : ℤ}
    (hσ : a Generator.sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    (hη : ActsAsPow t.σ nη (PWord.evalFin ⇑t E E₂ (η.toPWord (n := 2 + 2 * h))) V)
    (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcW α r pp η h)
      = ((powOmega2 t.σ) ^ (-(s r : ℤ))) • ((t.σ ^ (-nη)) • a (coreLetter h 2)) := by
  rw [foxD_mpcW_eq_mpcLinW t E E₂ a hα r pp η hσ hwild hτfpf hTodd hV₂,
    foxD_mpcLinW_x2 t E E₂ a hσ hwild hτfpf hTodd hα r pp hη hV₂]

end FullRow

/-! ## The row's level-indexed resolver -/

/-- The corrected procyclic-`M` row supplies a level-indexed resolver, one display at a time:
`resolvesAt_mpcFam` for the two `ω₂`-only displays and `resolvesAt_mpcFamOf_hat` for a genuine
`η̂`-display, with `resolvedFamily_isStokesEndpoint` as the common endpoint half. -/
theorem levelResolver {alpha r pp h q : ℕ} (d : EtaDisplay) (hα : 1 ≤ alpha) (hqe : Even q) :
    LevelResolver (2 + 2 * h) q (mpcW alpha r pp d h) (resolvedFamily alpha r pp h q d) where
  resolves := fun _ _ _ _ _ _ hN hord ↦ by
    cases d with
    | one => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | lit k => exact resolvesAt_mpcFam hN hord alpha r pp h q trivial
    | hat num den => exact resolvesAt_mpcFamOf_hat hN hord alpha r pp h q num den (fun _ ↦ 0)
  endpoint := fun _ hN hv ↦ resolvedFamily_isStokesEndpoint hN hv hα hqe d

/-! ## The pushed residues -/

/-- The source-facing residue for the corrected procyclic-`M` row: markings pushed forward from
the candidate group only, and the three induced word-cohomology bijections in place of the six
`StokesDuality` clauses. -/
def PushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C) (N : ℕ),
    N ≠ 0 → N.factorization 2 ≠ 0 →
    ∀ (hr : ∀ k, FreeGroup.lift
        (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
        (resolvedFamily alpha r pp h q d N k) = 1)
      (hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N))
      (V : Type) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V →
        StokesCohomologyBijections
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
          (resolvedFamily alpha r pp h q d N) V hr hend

/-- The coefficient-independent residue at the uniform level `4 * Monoid.exponent C`, in the
shape produced by action-image devissage. -/
def UniformPushedHsimp (alpha r pp h q : ℕ) (d : EtaDisplay) : Prop :=
  ∀ (C : Type) [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      (∀ a : A, a + a = 0) →
        StokesDuality
          (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
          (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) A

/-- The historical all-markings residue implies the pushed cohomological one. -/
theorem pushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) : PushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho N hN hv hr hend V _ _ _ hV₂ hsimple
  set t : Marking (2 + 2 * h) C :=
    ⟨fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g)⟩ with ht
  exact (stokesDuality_iff_cohomologyBijections ⇑t (resolvedFamily alpha r pp h q d N) V hr
    hend).mp (hsimp C t N hN hv hr V hV₂ hsimple)

/-! ## The pushed replacements for the two chain entry points -/

/-- The devissage step of the pushed residue, once relator death at the pushed marking is in
hand. -/
private theorem stokesDuality_of_pushed_of_relators {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hr : ∀ k, FreeGroup.lift
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N k) = 1)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A := by
  have hend : IsStokesEndpoint (resolvedFamily alpha r pp h q d N) :=
    resolvedFamily_isStokesEndpoint hN hv hα hqe d
  exact stokesDuality_of_simple _ (resolvedFamily alpha r pp h q d N) hr hend
    (fun V _ _ _ hV₂ hsimple ↦
      (stokesDuality_iff_cohomologyBijections _ (resolvedFamily alpha r pp h q d N) V hr
        hend).mpr (hsimp C rho N hN hv hr hend V hV₂ hsimple)) A hA₂

/-- `MProcyclicExact.stokesDuality` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed_of_relators hsimp hα hqe rho hN hv
    (fun k ↦ lower_rel (A := ZMod 2) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- `MProcyclicExact.stokesDuality_T` with its `Hsimp` binder weakened to `PushedHsimp`. -/
theorem stokesDuality_T_of_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) := by
  have hb := resolvesAt_and_endpoint_resolvedFamily heisLevel_ne_zero heisLevel_even
    (Q := WordLift (ZMod 2) (Bg ⧸ D.M)) orderOf_dvd_heisLevel_scal
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hqe d
  exact stokesDuality_of_pushed hsimp hα hqe rho heisLevel_ne_zero heisLevel_even hb.1
    (Additive ↥D.T) (radT_add_self D)

/-! ## The uniform residue, and the action-image route to it -/

/-- The pushed residue supplies the uniform one. -/
theorem uniformPushedHsimp_of_pushedHsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : PushedHsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  letI : TopologicalSpace (WordLift A C) := ⊥
  letI : DiscreteTopology (WordLift A C) := ⟨rfl⟩
  have hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) (WordLift A C) := by
    refine (levelResolver d hα hqe).resolves (WordLift A C) (4 * Monoid.exponent C)
      (fourMulExponent_ne_zero_and_even C).1 ?_
    intro x
    refine (WordLift.orderOf_dvd_two_mul hA₂
      (fun g : C ↦ Monoid.order_dvd_exponent g) x).trans ?_
    exact mul_dvd_mul_right (by norm_num) (Monoid.exponent C)
  exact stokesDuality_of_pushed_of_relators hsimp hα hqe rho
    (fourMulExponent_ne_zero_and_even C).1 (fourMulExponent_ne_zero_and_even C).2
    (fun k ↦ lower_rel (A := A) rho (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h)) hres k) A hA₂

/-- Both weakenings composed. -/
theorem uniformPushedHsimp_of_hsimp {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_pushedHsimp (pushedHsimp_of_hsimp hsimp) hα hqe

/-- **The action-image route for the corrected procyclic-`M` row, at every admissible level.**
The only remaining input is the simple-module branch at the canonical action image. -/
theorem stokesDuality_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) {N : ℕ} (hN : N ≠ 0)
    (hord : ∀ x : HeisLift A C, orderOf x ∣ N) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  pushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂ hN hord

/-- The uniform residue from the action image. -/
theorem uniformPushedHsimp_of_actionImage {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hα : 1 ≤ alpha) (hqe : Even q)
    (hsimp : SimpleActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d := by
  intro C _ _ _ _ rho A _ _ _ hA₂
  exact uniformPushedStokesDuality_of_actionImage (levelResolver d hα hqe) hsimp rho A hA₂

/-- The residue split along the `tau`-dichotomy, at the corrected procyclic-`M` word. -/
theorem uniformPushedHsimp_of_branches {alpha r pp h q : ℕ} {d : EtaDisplay} (hα : 1 ≤ alpha)
    (hqe : Even q)
    (hunram : UnramifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d))
    (hram : RamifiedActionImageStokes (2 + 2 * h) q (mpcW alpha r pp d h)
      (resolvedFamily alpha r pp h q d)) :
    UniformPushedHsimp alpha r pp h q d :=
  uniformPushedHsimp_of_actionImage hα hqe (simpleActionImageStokes_of_branches hunram hram)

/-! ## Regression: the historical entry points factor through the pushed ones -/

/-- `MProcyclicExact.stokesDuality`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    [DistribMulAction C (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) C)
    {N : ℕ} (hN : N ≠ 0) (hv : N.factorization 2 ≠ 0)
    (hres : ResolvesAt (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h))
      (resolvedFamily alpha r pp h q d N) (WordLift (ZMod 2) C))
    (A : Type) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d N) A :=
  stokesDuality_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho hN hv hres A hA₂

/-- `MProcyclicExact.stokesDuality_T`, re-derived through `PushedHsimp`. -/
theorem stokesDuality_T_via_pushed {alpha r pp h q : ℕ} {d : EtaDisplay}
    (hsimp : Hsimp alpha r pp h q d) (hα : 1 ≤ alpha) (hqe : Even q)
    {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    {D : RadicalCoverData Bg} [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
    [TopologicalSpace (WordLift (ZMod 2) (Bg ⧸ D.M))]
    [DiscreteTopology (WordLift (ZMod 2) (Bg ⧸ D.M))]
    (rho : ContinuousMonoidHom ((displayedGamma alpha r pp h q d : Type)) (Bg ⧸ D.M)) :
    StokesDuality
      (fun g ↦ rho (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) g))
      (resolvedFamily alpha r pp h q d (heisLevel D)) (Additive ↥D.T) :=
  stokesDuality_T_of_pushed (pushedHsimp_of_hsimp hsimp) hα hqe rho

end

/-! ## Axiom footprint -/

#print axioms GQ2.Dyadic.MProcyclicExact.foxD_prodList_handleTailW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_plusW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_eq_mpcLinW
#print axioms GQ2.Dyadic.MProcyclicExact.foxD_mpcW_x2
#print axioms GQ2.Dyadic.MProcyclicExact.levelResolver
#print axioms GQ2.Dyadic.MProcyclicExact.pushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_hsimp
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_actionImage
#print axioms GQ2.Dyadic.MProcyclicExact.uniformPushedHsimp_of_branches
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_via_pushed
#print axioms GQ2.Dyadic.MProcyclicExact.stokesDuality_T_via_pushed

end GQ2.Dyadic.MProcyclicExact
