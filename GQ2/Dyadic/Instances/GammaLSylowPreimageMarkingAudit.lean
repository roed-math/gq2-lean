/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageRealizationBypass
import GQ2.Dyadic.Instances.KExactLiftingGalK

/-!
# P5 — the marking audit: exactly which handle rows the L-row pro-2 block consumes

**The load-bearing audit of `SqNuClearHypothesis`.**  The χ-free clearing binder
(`GQ2/Dyadic/SqCore/ChiFreeClearing.lean`) is the last hypothesis on the L-row realization
bypass (`markedCoreRealization_of_supply`).  It exists for one reason only: to make a
transported arithmetic marking's **handle** rows match `lNu`'s, which are zero.  This file
settles, field by field, what actually needs them.

## The verdict

| datum | reads `nuP`? | reads `nuP`'s handle rows? |
|---|---|---|
| `MarkedCoreRealization.equiv` | no | no |
| `MarkedCoreRealization.nu_equiv` | at **every** `x` | yes |
| `pro2` | no (`retarget_pro2 : rfl`) | no |
| `pro2_surjective` | no (a property of `pro2`) | no |
| `ker_pro2` | no (a property of `pro2`) | no |
| `nu_compat` | at every `g`, and **equivalently** to `nu_equiv` | yes |
| `KExactSupplyRN.exactLifting` | generic in `nuP` (`exactLiftingSemanticsRN_galK`) | no |
| `KExactSupplyRN` as a whole | only through `nu_compat` | **no** — §2 builds it for free |

So the three *structural* exports are marking-blind, and `KExactSupplyRN` is satisfiable, with
no clearing hypothesis at all, over a marking whose handle rows are whatever the arithmetic
hands back (`kExactSupplyRN_transport`, §2).  The binder is therefore **not** needed by the
pro-2 block.

But it is not removable either, and §1 says why sharply: `nu_compat` at the *marking* `nuP` is
**equivalent** to `nu_equiv` at `nuP` (`nu_equiv_of_nu_compat`), because `maxProPMk` is onto.
There is no slack anywhere inside the block: whichever marking the block is taken over, that
marking is pinned at every point of the core by the arithmetic.  The pin to `lNu h`
specifically comes from *outside* the block — from the candidate side, where
`LSquare.lCanonicalCompat` (via `Instances.LSquareCore.lNu_wild`) forces the shared marking to
kill **every** wild and handle generator, because those letters die in `Γ_L`'s tame quotient.
Consequence, made literal in §1: any realization at `lNu h` carries every handle letter into
`ker ν_ur` (`handleU_unramified_of_realization`).

## The corrected interface (§3)

The realization at `lNu h` is *equivalent* to a strictly arithmetic statement, with no
group-theoretic clearing anywhere:

  `SqFullNuForwardSupply B h ↔ Nonempty (MarkedCoreRealization (DSq h) (lNu h))`

(`sqFullNuForwardSupply_iff_realization`) — "some equivalence of the core with `G_K(2)` carries
**all** of `ν_sq`", the full-row upgrade of `SqNuForwardSupply`'s two rows.  The clearing binder
is exactly the two-rows-to-all-rows bridge (`sqFullNuForwardSupply_of_clear`), and it is
consumed only at *transported* markings (§4, `SqNuClearAtTransport`), never at the arbitrary
markings `SqNuClearHypothesis` quantifies over.  The implication chain, each step strict:

  `SqNuSeed` ⇒ `SqNuMoveAt` ⇒ `SqNuClearHypothesis` ⇒ `SqNuClearAtTransport`
    ⇒ (over `SqNuForwardSupply`) `SqFullNuForwardSupply` ⇔ the pro-2 block.

The two banked machine searches bear on the **first** item of that chain only — the four-slot
Eichler substitution, with `v_j` fixed literally by `sqEichlerSub_handleV` and only
`β₁/β₀/β₂/ρ` free.  Nothing in them bears on the last two, which quantify over *all* continuous
automorphisms and over *one* arithmetic equivalence respectively.  §6 records the chain as
stress pins so that a later reshaping cannot silently confuse the targets.

Two further findings, from re-running the banked scripts, say the searched obstruction should
not be believed even about that first item:

* the class-4 report is produced by a **linear** solver — it fixes a layer of the lower
  exponent-2 central series, computes each move's effect separately, and asks whether the
  defect lies in the span of those effects.  Two weight-`2` corrections cross at weight `4`,
  exactly the reported layer, and that cross term is outside the model.  Adding the *exact*
  pairwise effects to the same solver lifts the layer-4 span from `150/175` to `159/175` and
  carries the seed **through** class 4 with an explicit witness: the obstruction is an artifact
  of the linearization.  (At class 3 the same solver already reports candidate-dependent
  obstructions, which an invariant cannot be.)
* the ansatz is narrower than the move it is chasing.  `SqNuMoveAt` fixes the `v`-**rows**, not
  the `v`-letters, so the `v_j`-slot may move as long as its correction is `ν`-invisible.
  `GQ2/Dyadic/SqCore/NuSeedWide.lean` releases it (`SqNuSeedW`, `sqNuMoveAt_of_seedW`), with
  the four-slot family embedded at `ρ_v = 1`.

So no refutation of `SqNuClearHypothesis` is available from the banked data, and the productive
next step is the widened search with a cross-term-aware solver — or, better, the arithmetic
full-row supply of §3, which sidesteps `Aut(D_sq)` altogether.

## Axiom hygiene

No `sorry`, no new axiom, no `native_decide`.  Every declaration prints **std-3**
(`propext`, `Classical.choice`, `Quot.sound`) except `kExactSupplyRN_transport`, which carries
exactly `exactLiftingSemanticsRN_galK`'s three existing census members (`tateDualityAt`,
`absGalQ2_isTopologicallyFinitelyGenerated`, `absGalQ2_localEulerCharacteristic`) — no new
axiom is introduced anywhere.  Census unchanged at **11**.
-/

namespace GQ2.Dyadic.LSquare.MarkingAudit

open GQ2 GQ2.Dyadic SqCore MarkedCore Multiplicative

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

noncomputable section

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-! ## §1 Field dependence: what each export of the block reads

`MarkedCoreRealization` has two fields.  `pro2`, `pro2_surjective` and `ker_pro2` are built
from `equiv` alone, so they are literally invariant under retargeting the marking; `nu_compat`
is, by contrast, *equivalent* to the whole of `nu_equiv`. -/

section Dependence

variable {B : MarkedRecip R K} {P : ProfiniteGrp}

/-- **Retargeting**: a realization's equivalence supports a realization at *any* marking it
happens to match.  Only the second field changes. -/
def retarget {nuP nuP' : ContinuousMonoidHom P Ztwo}
    (M : MarkedCoreRealization (K := K) (B := B) P nuP)
    (hnu : ∀ x, ztwoIota (nuP' x) = nuUrKTwo B (M.equiv x)) :
    MarkedCoreRealization (K := K) (B := B) P nuP' where
  equiv := M.equiv
  nu_equiv := hnu

/-- The retargeted realization has the **same** source map: `pro2` never reads the marking. -/
@[simp] theorem retarget_pro2 {nuP nuP' : ContinuousMonoidHom P Ztwo}
    (M : MarkedCoreRealization (K := K) (B := B) P nuP)
    (hnu : ∀ x, ztwoIota (nuP' x) = nuUrKTwo B (M.equiv x)) :
    (retarget M hnu).pro2 = M.pro2 := rfl

/-- The retargeted realization has the same equivalence, by construction. -/
@[simp] theorem retarget_equiv {nuP nuP' : ContinuousMonoidHom P Ztwo}
    (M : MarkedCoreRealization (K := K) (B := B) P nuP)
    (hnu : ∀ x, ztwoIota (nuP' x) = nuUrKTwo B (M.equiv x)) :
    (retarget M hnu).equiv = M.equiv := rfl

/-- **Marking-blindness of the structural exports**: two realizations of the same core with the
same equivalence but *different* markings have the same `pro2`, hence the same surjectivity and
the same kernel. -/
theorem pro2_congr {nuP nuP' : ContinuousMonoidHom P Ztwo}
    (M : MarkedCoreRealization (K := K) (B := B) P nuP)
    (M' : MarkedCoreRealization (K := K) (B := B) P nuP')
    (he : M.equiv = M'.equiv) : M.pro2 = M'.pro2 := by
  refine DFunLike.ext _ _ fun g => ?_
  show M.equiv.symm (maxProPMk 2 (GalK K) g) = M'.equiv.symm (maxProPMk 2 (GalK K) g)
  rw [he]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **No slack in the block**: the fourth export determines the second.  If a marking is
`ν_ur`-compatible along the source map of an equivalence, then it is `ν_ur`-compatible at
*every* point of the core — because `maxProPMk` is onto.  So the block cannot be satisfied by a
marking that is "right on the core rows and free on the handle rows": the arithmetic pins every
row of whichever marking the block is taken over. -/
theorem nu_equiv_of_nu_compat {nuP : ContinuousMonoidHom P Ztwo}
    (e : ContinuousMulEquiv (P : Type) (maxProPQuotient 2 (GalK K)))
    (hc : ∀ g : GalK K,
      ztwoIota (nuP (e.symm (maxProPMk 2 (GalK K) g))) = B.nu_ur (toAbK K g)) :
    ∀ x : P, ztwoIota (nuP x) = nuUrKTwo B (e x) := by
  intro x
  obtain ⟨g, hg⟩ := quotientMk_surjective _ (e x)
  have hgx : maxProPMk 2 (GalK K) g = e x := hg
  have hx : e.symm (maxProPMk 2 (GalK K) g) = x := by
    rw [hgx, e.symm_apply_apply]
  calc ztwoIota (nuP x) = ztwoIota (nuP (e.symm (maxProPMk 2 (GalK K) g))) := by rw [hx]
    _ = B.nu_ur (toAbK K g) := hc g
    _ = nuUrKTwo B (maxProPMk 2 (GalK K) g) := (nuUrKTwo_maxProPMk B g).symm
    _ = nuUrKTwo B (e x) := by rw [hgx]

/-- **The block *is* the realization.**  Given the corrected equivalence, the four exported
pro-2 data at a marking are exactly a `MarkedCoreRealization` at that marking: `nu_compat`
converts back to `nu_equiv`.  This is the precise sense in which the marking cannot be
weakened inside the block. -/
def ofNuCompat {nuP : ContinuousMonoidHom P Ztwo}
    (e : ContinuousMulEquiv (P : Type) (maxProPQuotient 2 (GalK K)))
    (hc : ∀ g : GalK K,
      ztwoIota (nuP (e.symm (maxProPMk 2 (GalK K) g))) = B.nu_ur (toAbK K g)) :
    MarkedCoreRealization (K := K) (B := B) P nuP where
  equiv := e
  nu_equiv := nu_equiv_of_nu_compat e hc

end Dependence

/-! ## §2 The pro-2 block over a general marking, unconditionally

The transported marking is a marking: no clearing, no supply, no row hypotheses at all.  Its
handle rows are whatever `ν_ur` says they are, and the block is built over it for free.  This
answers the audit's headline question — `KExactSupplyRN` **is** satisfiable with arbitrary
handle rows. -/

section Transport

variable {B : MarkedRecip R K} {h : ℕ}

/-- The `Ztwo`-coordinate of the core transported through an arbitrary `K`-side equivalence.
This is `transportedNuUr` read through the seam `ι`, i.e. in the coordinate
`MarkedCoreRealization` wants. -/
def transportZ (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    ContinuousMonoidHom (DSq h : Type) Ztwo where
  toFun := fun x => ztwoIota.symm (nuUrKTwo B (f x))
  map_one' := by rw [map_one, map_one, map_one]
  map_mul' := fun x y => by rw [map_mul, map_mul, map_mul]
  continuous_toFun :=
    ztwoIota.symm.continuous_toFun.comp
      ((nuUrKTwo B).continuous_toFun.comp f.continuous_toFun)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
@[simp] theorem transportZ_apply (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (x : (DSq h : Type)) : transportZ B f x = ztwoIota.symm (nuUrKTwo B (f x)) := rfl

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The seam sends the transported marking back to the arithmetic one. -/
@[simp] theorem ztwoIota_transportZ (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (x : (DSq h : Type)) : ztwoIota (transportZ B f x) = nuUrKTwo B (f x) :=
  ztwoIota.apply_symm_apply _

/-- **The unconditional block.**  Every equivalence of the `L_sq` core with `G_K(2)` is already
a marked-core realization — over its own transported marking.  No clearing hypothesis, no row
hypothesis, no certificate. -/
def markedCoreRealizationTransport (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    MarkedCoreRealization (K := K) (B := B) (DSq h) (transportZ B f) where
  equiv := f
  nu_equiv := ztwoIota_transportZ B f

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The transported marking carries the two P3-selected core rows as soon as the χ-free supply
does — but its handle rows are unconstrained, and nothing above needed them. -/
theorem transportZ_sigma_of_supply (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)))
    (hsigma : nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2])) :
    ztwoIota (transportZ B f (dsqSigma h)) = ofAdd (1 : ℤ_[2]) := by
  rw [ztwoIota_transportZ, hsigma]

/-- **The audit's headline, existential form**: the L-row pro-2 block is satisfiable at *some*
marking of `D_sq(h)` — for every arithmetic equivalence and with no hypothesis whatever.  The
marking's handle rows are exactly the unramified rows of the handle letters. -/
theorem exists_markedCoreRealization_of_equiv (B : MarkedRecip R K)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    ∃ nuP : ContinuousMonoidHom (DSq h : Type) Ztwo,
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h) nuP) ∧
        ∀ x, ztwoIota (nuP x) = nuUrKTwo B (f x) :=
  ⟨transportZ B f, ⟨markedCoreRealizationTransport B f⟩, ztwoIota_transportZ B f⟩

variable {FF : DyadicUnitFiltration K}

/-- **`KExactSupplyRN` with arbitrary handle rows.**  The corrected arithmetic supply at the
L-row slot, over the transported marking, from an arithmetic equivalence and the degree pin
alone.  This is the literal answer to "does some consumer of the block need the handle rows
zero?": the block does not. -/
def kExactSupplyRN_transport {T : OrientedTameQuotientK B FF} {n : ℕ}
    (hdeg : Module.finrank ℚ_[2] K = n)
    (f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K))) :
    KExactSupplyRN T n (DSq h) (SqCore.isProP_DSq h) (transportZ B f) :=
  kExactSupplyRN_of_markedCore (T := T) hdeg
    (markedCoreRealizationTransport B f).pro2
    (markedCoreRealizationTransport B f).pro2_surjective
    (markedCoreRealizationTransport B f).ker_pro2
    (markedCoreRealizationTransport B f).nu_compat

end Transport

/-! ## §3 What genuinely pins `lNu h`, and the corrected interface

Outside the block, the candidate side (`LSquare.lCanonicalCompat`, through
`Instances.LSquareCore.lNu_wild`) forces the *shared* marking to kill every wild and handle
generator, because those letters die in `Γ_L`'s tame quotient.  So `lNu h` is the marking, and
the realization at `lNu h` is equivalent to an arithmetic full-row supply. -/

section Interface

variable {B : MarkedRecip R K} {h : ℕ}

/-- **The full-row χ-free supply**: *some* equivalence of the `L_sq` core with `G_K(2)` carries
the *whole* standard marking, not merely its two selected rows.  This is the corrected residual
of the L-row: an arithmetic statement about one equivalence, with no automorphism group in
sight. -/
def SqFullNuForwardSupply (B : MarkedRecip R K) (h : ℕ) : Prop :=
  ∃ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
    ∀ x, nuUrKTwo B (f x) = nuSq h x

/-- The full-row supply gives the L-row realization **with no clearing binder**. -/
theorem markedCoreRealization_of_fullSupply (H : SqFullNuForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) := by
  obtain ⟨f, hf⟩ := H
  exact ⟨⟨f, fun x => by rw [ztwoIota_lNu h x, hf x]⟩⟩

/-- The converse: the realization *produces* the full-row supply. -/
theorem sqFullNuForwardSupply_of_realization
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h)) :
    SqFullNuForwardSupply B h :=
  ⟨M.equiv, fun x => by rw [← M.nu_equiv x, ztwoIota_lNu h x]⟩

/-- **The corrected interface, exactly**: the L-row pro-2 block at the frozen marking is the
full-row arithmetic supply, no more and no less. -/
theorem sqFullNuForwardSupply_iff_realization :
    SqFullNuForwardSupply B h ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
        (Instances.LSquareCore.lNu h)) :=
  ⟨markedCoreRealization_of_fullSupply, fun ⟨M⟩ => sqFullNuForwardSupply_of_realization M⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The full-row supply refines the χ-free two-row supply. -/
theorem sqNuForwardSupply_of_full (H : SqFullNuForwardSupply B h) : SqNuForwardSupply B h := by
  obtain ⟨f, hf⟩ := H
  exact ⟨f, by rw [hf, nuSq_sigma], by rw [hf, nuSq_x0]⟩

/-- **The handle rows are load-bearing, sharply.**  A realization at `lNu h` forces every `u_j`
letter of the corrected basis into the kernel of the unramified character. -/
theorem handleU_unramified_of_realization
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (j : Fin h) : nuUrKTwo B (M.equiv (sqGen h (sqHandleIdxU j))) = 1 := by
  rw [← M.nu_equiv, ztwoIota_lNu, nuSq_handleU]

/-- The same for the `v_j` letters. -/
theorem handleV_unramified_of_realization
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h))
    (j : Fin h) : nuUrKTwo B (M.equiv (sqGen h (sqHandleIdxV j))) = 1 := by
  rw [← M.nu_equiv, ztwoIota_lNu, nuSq_handleV]

/-- And for the `x₁` letter, the third row that `SqNuForwardSupply` does not name. -/
theorem x1_unramified_of_realization
    (M : MarkedCoreRealization (K := K) (B := B) (DSq h) (Instances.LSquareCore.lNu h)) :
    nuUrKTwo B (M.equiv (dsqX1 h)) = ofAdd (0 : ℤ_[2]) := by
  rw [← M.nu_equiv, ztwoIota_lNu, nuSq_x1]

end Interface

/-! ## §4 The binder actually consumed

`markedCoreRealization_of_nuSupply` applies `SqNuClearHypothesis` at one marking only: the
transported one.  So the consumed binder is the following weakening, which quantifies over
arithmetic equivalences rather than over all continuous markings of the abstract core. -/

section ConsumedBinder

variable {B : MarkedRecip R K} {h : ℕ}

/-- **The consumed binder**: clearing, but only at markings that arise by transport from an
arithmetic equivalence with the two selected rows. -/
def SqNuClearAtTransport (B : MarkedRecip R K) (h : ℕ) : Prop :=
  ∀ f : ContinuousMulEquiv (DSq h : Type) (maxProPQuotient 2 (GalK K)),
    nuUrKTwo B (f (dsqSigma h)) = ofAdd (1 : ℤ_[2]) →
    nuUrKTwo B (f (dsqX0 h)) = ofAdd (0 : ℤ_[2]) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        ∀ x, nuUrKTwo B (f (Ψ x)) = nuSq h x

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The abstract clearing hypothesis implies the consumed one. -/
theorem sqNuClearAtTransport_of_clear (hclear : SqNuClearHypothesis h) :
    SqNuClearAtTransport B h := fun f hsigma hx0 =>
  hclear (transportedNuUr B f) hsigma hx0

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The consumed binder plus the two-row supply gives the full-row supply — hence, by §3, the
whole L-row pro-2 block. -/
theorem sqFullNuForwardSupply_of_transportClear (hclear : SqNuClearAtTransport B h)
    (H : SqNuForwardSupply B h) : SqFullNuForwardSupply B h := by
  obtain ⟨f, hsigma, hx0⟩ := H
  obtain ⟨Ψ, hΨ⟩ := hclear f hsigma hx0
  exact ⟨Ψ.trans f, hΨ⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The two-rows-to-all-rows bridge, named**: this is the entire job of the χ-free clearing
hypothesis on the L row. -/
theorem sqFullNuForwardSupply_of_clear (hclear : SqNuClearHypothesis h)
    (H : SqNuForwardSupply B h) : SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_transportClear (sqNuClearAtTransport_of_clear hclear) H

/-- The bypass, rerouted through the corrected interface: the binder is consumed only here. -/
theorem markedCoreRealization_of_transportClear (hclear : SqNuClearAtTransport B h)
    (H : SqNuForwardSupply B h) :
    Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
      (Instances.LSquareCore.lNu h)) :=
  markedCoreRealization_of_fullSupply (sqFullNuForwardSupply_of_transportClear hclear H)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- At `h = 0` the consumed binder is a theorem, as the abstract one already was. -/
theorem sqNuClearAtTransport_zero : SqNuClearAtTransport B 0 :=
  sqNuClearAtTransport_of_clear sqNuClearHypothesis_zero

end ConsumedBinder

/-! ## §5 The clearing target is a pure handle-row statement

`nu_eq_nuSq_of_core` says the two selected core rows plus the forced `x₁`-row determine
everything but the handles.  So `SqNuClearHypothesis` is *equivalent* to asking only that some
automorphism clear the handle rows while preserving the two core rows — which is precisely the
statement the seed search targets, and precisely the statement whose failure would be needed to
refute the binder. -/

section HandleReduction

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **Handle-row form of the clearing target.**  Nothing but the `2h` handle rows is ever at
issue. -/
theorem sqNuClearHypothesis_of_handles {h : ℕ}
    (H : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
          nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
            nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧
            (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1) ∧
            (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1)) :
    SqNuClearHypothesis h := by
  intro nu' hsigma hx0
  obtain ⟨Ψ, hs, hx, hU, hV⟩ := H nu' hsigma hx0
  exact ⟨Ψ, fun x => nu_eq_nuSq_of_core (nu'.comp (autHom Ψ)) hs hx hU hV x⟩

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- The converse: the clearing target delivers the handle-row form. -/
theorem handles_of_sqNuClearHypothesis {h : ℕ} (hclear : SqNuClearHypothesis h)
    (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]))
    (hsigma : nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]))
    (hx0 : nu' (dsqX0 h) = ofAdd (0 : ℤ_[2])) :
    ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
      nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
        nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧
        (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1) ∧
        (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1) := by
  obtain ⟨Ψ, hΨ⟩ := hclear nu' hsigma hx0
  refine ⟨Ψ, ?_, ?_, fun j => ?_, fun j => ?_⟩
  · rw [hΨ (dsqSigma h), nuSq_sigma]
  · rw [hΨ (dsqX0 h), nuSq_x0]
  · rw [hΨ, nuSq_handleU]
  · rw [hΨ, nuSq_handleV]

end HandleReduction

end

/-! ## §6 Stress pins

The chain the two machine searches sit at the top of, written out so a later reshaping cannot
confuse the targets: the searched object is the **seed**, three strict weakenings above the
statement the campaign needs. -/

section StressTests

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- Rung 1→2: the searched seed gives the move. -/
example {h : ℕ} {j : Fin h} {k : ℤ_[2]} (S : SqNuSeed h j k) : SqNuMoveAt h j k :=
  sqNuMoveAt_of_seed S

/-- Rung 2→3: the move family gives the clearing hypothesis. -/
example {h : ℕ} (H : ∀ (j : Fin h) (k : ℤ_[2]), SqNuMoveAt h j k) : SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_moves H

/-- Rung 3→4: the clearing hypothesis gives the binder actually consumed. -/
example {B : MarkedRecip R K} {h : ℕ} (hclear : SqNuClearHypothesis h) :
    SqNuClearAtTransport B h :=
  sqNuClearAtTransport_of_clear hclear

/-- Rung 4→5: over the two-row supply, the consumed binder gives the full-row supply. -/
example {B : MarkedRecip R K} {h : ℕ} (hclear : SqNuClearAtTransport B h)
    (H : SqNuForwardSupply B h) : SqFullNuForwardSupply B h :=
  sqFullNuForwardSupply_of_transportClear hclear H

/-- Rung 5 is the endpoint: the full-row supply *is* the L-row pro-2 block. -/
example {B : MarkedRecip R K} {h : ℕ} :
    SqFullNuForwardSupply B h ↔
      Nonempty (MarkedCoreRealization (K := K) (B := B) (DSq h)
        (Instances.LSquareCore.lNu h)) :=
  sqFullNuForwardSupply_iff_realization

/-- The block over a general marking, at one handle: no binder at all. -/
noncomputable example {B : MarkedRecip R K}
    (f : ContinuousMulEquiv (DSq 1 : Type) (maxProPQuotient 2 (GalK K))) :
    MarkedCoreRealization (K := K) (B := B) (DSq 1) (transportZ B f) :=
  markedCoreRealizationTransport B f

/-- At `h = 0` the corrected interface needs only the two-row supply. -/
example {B : MarkedRecip R K} (H : SqNuForwardSupply B 0) : SqFullNuForwardSupply B 0 :=
  sqFullNuForwardSupply_of_clear sqNuClearHypothesis_zero H

/-- The handle-row reduction: the target is exactly the `2h` handle rows. -/
example {h : ℕ}
    (H : ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
      nu' (dsqSigma h) = ofAdd (1 : ℤ_[2]) → nu' (dsqX0 h) = ofAdd (0 : ℤ_[2]) →
        ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
          nu' (Ψ (dsqSigma h)) = ofAdd (1 : ℤ_[2]) ∧
            nu' (Ψ (dsqX0 h)) = ofAdd (0 : ℤ_[2]) ∧
            (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1) ∧
            (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1)) :
    SqNuClearHypothesis h :=
  sqNuClearHypothesis_of_handles H

end StressTests

/-! ## §7 Axiom pins

Committed prints: every declaration of this file is **std-3**.  Census unchanged at **11**. -/

section AxiomPins

#print axioms retarget
#print axioms retarget_pro2
#print axioms pro2_congr
#print axioms nu_equiv_of_nu_compat
#print axioms ofNuCompat
#print axioms transportZ
#print axioms ztwoIota_transportZ
#print axioms markedCoreRealizationTransport
#print axioms exists_markedCoreRealization_of_equiv
#print axioms kExactSupplyRN_transport
#print axioms markedCoreRealization_of_fullSupply
#print axioms sqFullNuForwardSupply_of_realization
#print axioms sqFullNuForwardSupply_iff_realization
#print axioms sqNuForwardSupply_of_full
#print axioms handleU_unramified_of_realization
#print axioms handleV_unramified_of_realization
#print axioms x1_unramified_of_realization
#print axioms sqNuClearAtTransport_of_clear
#print axioms sqFullNuForwardSupply_of_transportClear
#print axioms sqFullNuForwardSupply_of_clear
#print axioms markedCoreRealization_of_transportClear
#print axioms sqNuClearAtTransport_zero
#print axioms sqNuClearHypothesis_of_handles
#print axioms handles_of_sqNuClearHypothesis

end AxiomPins

end GQ2.Dyadic.LSquare.MarkingAudit
