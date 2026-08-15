/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Count.Scalar

/-!
# The `G_K`-side supply package  (dyadic campaign, ticket ASK)

The arithmetic half of packet Thm. 1.1.  AS1 built the assembly
(`GQ2/Dyadic/CertificateMain.lean`) but had to **carry** the `G_K` source as an opaque field
`DyadicLocalInput.source`, because the `K`-side of SD1 memo §3.3's supply map did not exist.
This file builds as much of it as the campaign's landed mathematics supports, and makes the
remainder countable: `KSupply` below is a `SourceDataN` at `Γ = G_K` **minus the leaves ASK can
prove**, and `KSupply.toSourceN` / `KSupply.toLocalInput` close the loop into AS1's records.

## What is proved here, and what is carried

**Inventory truth-synced as of `23041e0f`** by AB-0 of
`docs/dyadic/followup/analytic-bridges-plan.md` §6, lane W83-HOUSE.  It replaces the wave-77
inventory and the pointer annotations waves 79 and 82 stacked on top of it; those annotations
are gone because their content is folded in below.  **Nothing about the record changed**: the
same eleven fields are carried today as on the day the file was written.  What changed is the
tree around it, so the inventory keeps two words apart that the wave-77 form ran together.
**Carried** means "a structure field of `KSupply`", a fact about this file.  **Owed** means "no
theorem anywhere produces it at `G_K`", a fact about the tree.  Converting a carried field into
a call is a *statement* change, hence an owner item and not a housekeeping one, which is why a
leaf can be carried and not owed for many waves at a stretch.

Twenty-one `SourceDataN` fields.  **Ten are discharged here; eleven are carried, of which two
are owed, eight have a landed `G_K` supplier, and one has a supplier at a corrected
coefficient.**

| field | status |
|---|---|
| `Γ` | **proved**: `galKProfinite K`, `G_K` as a bundled `ProfiniteGrp` (§1) |
| `tame` | **proved**: B10-K's `OrientedTameQuotientK.tameFK` |
| `compat` | **proved**: B10-K's `compatF_K` at the record's `(pro2, νP)` |
| `surj` | **proved**: F3's `boundary_jointly_surjective_of_maxProP` |
| `smulZmod2`, `contSMulZmod2` | **proved**: the ambient subgroup action (§2) |
| `htriv` | **proved**: `Count.smul_zmod2` (any action on `𝔽₂` is trivial) |
| `tfg` | **proved**: FG1's `absGalK_isTopologicallyFinitelyGenerated` (B1, Route D) |
| `homCard` | **proved**: §3's `card_hom_zmodTwo_galK`, new here; B6 + B7 |
| `cardH2` | **proved**: FD1's `card_H2_zmodTwo`; B6 |
| `pro2`, `ker_pro2` | carried, **owed** |
| `liftsOver_card`, `lem86` | carried, supplier landed |
| `tcocycle_card`, `hsep`, `hpartial`, `hZcard` | carried, supplier landed |
| `gaussZ_unramified`, `gaussZ_ramified` | carried, supplier landed |
| `stageR136` | carried, **one coefficient short** |

The eleven carried leaves, by supplier:

* `pro2`, `ker_pro2`: the marked-core certificate composite, owed by AS2 to AS5 per branch.
  **The only two leaves with no `G_K` producer**, unchanged since wave 77.
* `liftsOver_card`, `lem86`: `liftsOver_card_galK` and `lem86_galK_of_noDescent`
  (`Instances/KExactLiftingGalK.lean`), the latter from `D.NoDescent` and surjectivity alone.
* `tcocycle_card`, `hsep`, `hpartial`, `hZcard`: all four from
  `stokesDualityCertificate_galK` (`Instances/KAnalytic.lean`), out of the degree pin alone,
  over the `Γ`-generic `Count/LocalDuality.lean` layer.
* `gaussZ_unramified`, `gaussZ_ramified`: `affineDeterminant_galK`
  (`Dyadic/GaussZ/FinalDK.lean`), from the packet's own `ramifiedData`.
* `stageR136`: `correctedRStageSemantics_galK` (`Instances/KAnalytic.lean`) proves equation
  (136) at `zRN = SN.tMult #R · #D_R`, while the *frozen* clause §4 carries pins
  `zR = #R²·#D_R`.  This is the one genuine gap, and it is one coefficient wide.

The three carried clause bundles are **AS1's own `Prop`s**, verbatim, at the carrier
`galKProfinite K`.  That is deliberate: AS1 stated them "at an abstract carrier `Γ` so that both
sides of the comparison can use one vocabulary", and this file is the second consumer.  The
fourth clause bundle, `ScalarHilbertCertificate`, is **not** a field: §3 proves it
(`scalarHilbert_galK`), which is the only place in the two-sided architecture where a
`SourceDataN` clause is discharged at `G_K` by arithmetic rather than assumed.

The one coefficient is worth stating exactly, because it is the whole of what the analytic
side still costs.  `ExactLiftingSemanticsRN` (`CertificateMain.lean`) differs from the frozen
`ExactLiftingSemantics` in its third conjunct alone; the first two are the same text.  So
`exactLiftingSemanticsRN_galK` is a theorem at **every** degree, and W81-ASK's
`askC_exactLifting_iff_stageVanishing` shows that at `2 ≤ n` the frozen field is equivalent to
the single `Prop` `askCStageVanishing` (`Instances/AskCounting.lean`).  Every live row sits at
`n = 2`.

⚠ And that `Prop` is not obviously *wanted*: `askC_isEmpty_boundaryLifts_of_exactLifting`
derives from the frozen field, at `2 ≤ n`, that `G_K` admits no boundary-framed surjection onto
any marked target with a nontrivial Frattini block, and the recursion exists to count exactly
those.  Deciding between proving it and restating the row records against
`ExactLiftingSemanticsRN` is a statement question and is the standing owner item.

## Where B6 and B7 enter — this file is the point of entry

SD-R3's headline finding was that `closedRecursionK_of_source` prints std-3 where its `ℚ₂` model
needs B6 + B7: the two-sided refactor removed those axioms from the *spine*, structurally, and
they were predicted to re-enter through the supply package.  They do, here, at the following
instance-pinned declarations plus their consumers:

* `card_H2_zmodTwo_galK` — B6 alone (FD1's invariant map `H²(G_K, 𝔽₂) ≃+ 𝔽₂`);
* `exists_trivialCupPairing_ne_zero_galK` — B6 alone (FD1's nondegenerate cup form), stated on
  the pinned `GalK` side of the instance firewall;
* `card_hom_zmodTwo_galK` — B6 **and** B7 (`#H¹ = #H⁰ · #H² · 2^{n·v₂(#V)}` at `V = 𝔽₂`, with
  B7 arriving through LG2a's *derived* `absGalK_localEulerCharacteristic`, not as an axiom of
  its own — AX2 is closed).

Everything else in the file is std-3 or std-3 ∪ {B1}: the boundary layer (`tame`/`compat`/`surj`)
is parametrized over the AX4 *bundle* `OrientedTameQuotientK`, never over the axiom
`orientedTameQuotientAt`, so B10-K does not appear; `tfg_galK` carries B1 because FG1 derives the
general statement from the `ℚ₂` axiom.  Per-declaration prints are in the ticket report.

## Scope: SD-R3's five-item cut, verified

The board removed `prop_8_9_of_inputs` / `prop_8_9_of` / `prop_8_9_of_source` / `prop_8_9` and
`rhoPrime_surjective` from this ticket's budget.  Both halves check out, for **two different
reasons** (see the ticket report):

* the four `prop_8_9*` capstones are the `ℚ₂`-*hybrid* shape — source-side by hypotheses,
  `G_ℚ₂`-side by the `_local` pack — which the two-sided restatement dissolves;
  `GQ2/Dyadic/Recursion/Prop89Close.lean`'s `closedRecursionK_of_source` is the one-sided generic
  producer SD3 applies twice, and it takes its `G_K` leaves from the *record*, i.e. from here;
* `rhoPrime_surjective` is not structurally unnecessary — it is **already cloned**, as
  `GQ2.Dyadic.rhoPrimeK_surjective` (`GQ2/Dyadic/Recursion/Bridge.lean:159`), by SD-R3 itself.

## What this file does **not** do

No `sorry`, no new axiom, and none of the nine obligations as an axiom.  The eleven carried
leaves are hypothesis binders (structure fields), which is the campaign's permitted interim
state.  It does not *call* the eight suppliers the table names, because replacing a field by a
call changes the record's statement; that is the assembly-wiring owner item, and a housekeeping
lane may not do it.

**The wave-77 form of this paragraph is retracted, as of `23041e0f`.**  It said the `K`-clones
of the `ℚ₂` `*Local` counting pack and the LG5 ⇒ `GaussZResidueK` bridge were "still owed".
Neither is, and in both cases the resolution was not the clone the sentence expected:

* the **determinant** bridge landed at ticket CB-DET as `GQ2/Dyadic/GaussZ/FinalDK.lean`, whose
  `gaussZResidueDK_unramified` / `_ramified` twins and headline `affineDeterminant_galK` produce
  this file's `determinant` field type on the nose (its §8 `Acceptance` block contains the
  `example` that says so).  `affineDeterminant_galK`'s remaining arguments are `params_n` /
  `params_qK`, `hdeg` (this file's own pin), `hgu` / `hgr` (`rfl` at `standardNumerics n`),
  `htame` (`T.tameFK_surjective`) and `ramifiedData` (already an AS1 constructor argument), so
  what is left is wiring.  The genuinely unowned Gauss-`Z` item is the **candidate** side,
  `SqrtNeg2.PilotDet`;
* the **counting pack** was answered by generalization rather than cloning, exactly as §6 item 3
  below predicted: the four `Phase140/Local.lean` residues have carrier-generic twins over
  `TateDualityG Γ 2` plus `LocalEulerChar Γ d` in `Count/LocalDuality.lean`, and both inputs
  exist at `G_K`.  `stokesDualityCertificate_galK` assembles all four `stokes` clauses from the
  degree pin; `liftsOver_card_galK` and `lem86_galK_of_noDescent` cover
  `MStageCount.liftsOver_card_local` and `SectionEight.lemma_8_6_local`; `RStage/Local.lean`'s
  stage (136) has `correctedRStageSemantics_galK`.

So this file does still not consume LG5's `local_gauss_K`, and for the original reason (the
(83)-evaluation rung is not what `FinalDK.lean` proves), but the conclusion the old paragraph
drew from that, that the determinant leaf is unowned at `K`, is false.

## Import discipline

Plain-import (SD1 memo §5): `GQ2.Dyadic.CertificateMain` is plain-import, and the module rule is
one-directional, so this file must be too.  `GQ2.Dyadic.Count.Scalar` (CB-2) is imported for
three carrier-generic bricks — `Count.smul_zmod2`, `Count.card_hom_eq_card_Z1`, `Count.lem86N` —
which are stated over an abstract `Γ` and are as much the arithmetic side's as the candidate
side's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionEight
open SectionSeven AffineTLift CentralObstruction ContCoh FoxH

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ## §1 `G_K` as a bundled profinite group

`SourceDataN.Γ` is a `ProfiniteGrp` (the R31a carrier decision), so the supply package's first
job is to produce one.  `G_K = ↥(GalKsub K)` is an *open* subgroup of `G_ℚ₂`, hence closed,
hence compact; total disconnectedness is inherited by any subspace. -/

section Carrier

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- `G_K ≤ G_ℚ₂` is closed (an open subgroup of a topological group is closed). -/
theorem isClosed_galKsub : IsClosed ((GalKsub K : Subgroup AbsGalQ2) : Set AbsGalQ2) :=
  Subgroup.isClosed_of_isOpen _ (isOpen_fixingSubgroup K)

/-- `G_K` is compact — a closed subspace of the compact `G_ℚ₂`.  Registered as an instance:
every profinite statement about `G_K` in this file (and in the `SourceDataN` it produces) needs
it, and it fires only under the `[CompactSpace AbsGalQ2]` binder the whole two-sided layer
already carries. -/
instance compactSpace_galK : CompactSpace (GalK K) :=
  isCompact_iff_compactSpace.mp (isClosed_galKsub K).isCompact

/-- **`G_K` as a bundled profinite group** — the `SourceDataN.Γ` slot of the arithmetic side.
Its carrier is `GalK K` on the nose, which is what makes `DyadicLocalInput.source_carrier`
the identity (§5). -/
noncomputable def galKProfinite : ProfiniteGrp :=
  ProfiniteGrp.of (GalK K)

/-- The carrier of `galKProfinite K` **is** `G_K` — `rfl`.  Recorded because every statement
below silently uses it. -/
theorem galKProfinite_carrier : ((galKProfinite K : ProfiniteGrp) : Type) = GalK K := rfl

end Carrier

/-! ## §2 The scalar action

The `ZMod 2`-action of `G_K` is the ambient one restricted along `G_K ≤ G_ℚ₂`
(`GQ2/SectionSix.lean`), and it is trivial — as it is for *any* group, by CB-2's
`Count.smul_zmod2`.  These three fields of `SourceDataN` therefore need no arithmetic. -/

section Scalars

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- The `𝔽₂`-scalar action of `G_K`, restricted from `G_ℚ₂`.  A **reducible** name for the
ambient instance, not a new one: the clause `Prop`s of AS1 take the action as an explicit
argument, so it needs a name, but registering a second instance would create a diamond with the
one every `H*(G_K, 𝔽₂)` statement in `FieldData` already uses. -/
noncomputable abbrev smulZmod2GalK : DistribMulAction (GalK K) (ZMod 2) := inferInstance

noncomputable abbrev contSMulZmod2GalK : ContinuousSMul (GalK K) (ZMod 2) := inferInstance

omit [FiniteDimensional ℚ_[2] K] in
/-- **The action is trivial** — the `htriv` field.  Generic (`Count.smul_zmod2`): a group action
on `ZMod 2` fixes `0` and, being injective, fixes `1`. -/
theorem htriv_galK (γ : GalK K) (m : ZMod 2) : γ • m = m := Count.smul_zmod2 γ m

end Scalars

/-! ## §3 The scalar block at `G_K` — the clause ASK discharges

`ScalarHilbertCertificate` is `#Hom_c(Γ, 𝔽₂) = SN.homScalar` together with `#H²(Γ, 𝔽₂) = 2`.
On the candidate side CB-2 closed the first and left the second one structural theorem short
(`GQ2/Dyadic/Count/Scalar.lean` §8).  On the **arithmetic** side both close, and this is the
whole of the file's new mathematics.

The `H²` clause is FD1's `card_H2_zmodTwo` (B6's invariant map at `K`).  The `Hom` clause is new:
characters are `1`-cocycles for the (trivial) action, trivial action kills the coboundaries, and
`H¹(G_K, 𝔽₂)` has order `2^{n+2}` by FD1 — i.e. by B7 at `K`, which LG2a *derived* from the
`ℚ₂` axiom through Shapiro (AX2 closed, census unchanged). -/

section ScalarBlock

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **`#H²(G_K, 𝔽₂) = 2`** — FD1's theorem, B6.  Stated at the plain `GalK K` spelling: the
bundled carrier `↥(galKProfinite K)` is `GalK K` by `rfl` (§1), and stating it at the bundle
would force every consumer to re-synthesize the scalar action through the `ProfiniteGrp`
projection. -/
theorem card_H2_zmodTwo_galK : Nat.card (H2 (GalK K) (ZMod 2)) = 2 :=
  FieldData.card_H2_zmodTwo K

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The field-side mod-2 cup product is nondegenerate, in the pinned `GalK` spelling.**

This is the cup-product companion to `card_H2_zmodTwo_galK`.  Keeping the use of
`FieldData.invGalK` on this side of the `GalKsub` instance firewall prevents later imports from
re-synthesizing the definitionally equal `ZMod 2` and subgroup structures along a different
instance path. -/
theorem exists_trivialCupPairing_ne_zero_galK
    (x : H1 (GalK K) (ZMod 2)) (hx : x ≠ 0) :
    ∃ y : H1 (GalK K) (ZMod 2),
      trivialCupPairing 2 (GalK K) (htriv_galK K) x y ≠ 0 := by
  have hnondeg := FieldData.nondegFp2_cupFormK K
  by_contra hnone
  push Not at hnone
  apply hx
  apply hnondeg x
  intro y
  show FieldData.invGalK K
      (trivialCupPairing 2 (GalK K) (htriv_galK K) x y) = 0
  rw [hnone y]
  exact map_zero (FieldData.invGalK K)

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **`#Hom_c(G_K, 𝔽₂) = 2^{n+2}`** — the `SourceDataN.homCard` value at the arithmetic source.

Three steps, no new cohomology: CB-2's `Count.card_hom_eq_card_Z1` identifies continuous
characters with continuous `1`-cocycles (the action being trivial, the cocycle law *is* the
homomorphism law); `ContCoh.H1equivZ1OfTrivial` identifies `Z¹` with `H¹` (trivial action ⇒ no
coboundaries); and FD1's `card_H1_zmodTwo` evaluates `#H¹(G_K, 𝔽₂) = 2^{[K:ℚ₂]+2}` off the local
Euler characteristic at `K`.

This is the `ℚ₂` `lemma_8_2_local`'s job (`GQ2/SectionEight/ScalarCount.lean:337`) done by a
completely different route: the `ℚ₂` proof counts characters of the *presentation* `Π` and is
hard-coded at `Fin 3` and `8`; the Euler-characteristic route is degree-generic and needs no
presentation of `G_K` at all — which is essential, since the whole campaign exists to *prove*
that `Γ_{R_K}` presents `G_K`. -/
theorem card_hom_zmodTwo_galK :
    Nat.card (ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2)))
      = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
  rw [Count.card_hom_eq_card_Z1,
    ← Nat.card_congr (H1equivZ1OfTrivial (G := GalK K) (M := ZMod 2) (htriv_galK K)).toEquiv]
  -- `GalK K` and `↥K.fixingSubgroup` are the *same* type through two instance paths
  -- (`MarkedRecipBundle`'s R6 trap), so this last step is `exact`, not `rw`.
  exact FieldData.card_H1_zmodTwo K

/-- **AS1's `ScalarHilbertCertificate` at the arithmetic source** — the ledger §5.2 field 5,
proved rather than assumed.  The two hypotheses pin the abstract slot to `K`: `hdeg` says the
slot's degree is `[K : ℚ₂]`, `hhom` says the shared numerics are the packet's at that degree
(both are `rfl` at `SN = standardNumerics n` and `n = [K : ℚ₂]`). -/
theorem scalarHilbert_galK {n : ℕ} {SN : SourceNumerics n}
    (hdeg : Module.finrank ℚ_[2] K = n) (hhom : SN.homScalar = 2 ^ (n + 2)) :
    ScalarHilbertCertificate (galKProfinite K) n SN (smulZmod2GalK K) := by
  refine ⟨?_, card_H2_zmodTwo_galK K⟩
  show Nat.card (ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2))) = SN.homScalar
  rw [card_hom_zmodTwo_galK K, hhom, hdeg]

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **Topological finite generation of `G_K`** at the `galKProfinite` spelling — FG1's theorem
(B1 through Route D, never a `K`-level axiom). -/
theorem tfg_galK : ∃ s : Finset (GalK K),
    (Subgroup.closure (s : Set (GalK K))).topologicalClosure = ⊤ :=
  absGalK_isTopologicallyFinitelyGenerated K

/-- **The `lem86` reduction at `G_K`** (CB-2's `Count.lem86N`, instantiated).  Not a clause
value: it converts the record's half-torsor field into the single per-source residue `hvar`,
the existence of a nonzero variation class.  At `G_ℚ₂` that residue is
`RadicalEdgeLocal.exists_good_twist` (`GQ2/RadicalEdge/Local.lean`, `private`; its public entry
point is `half_torsor_local`, which is what `lemma_8_6_local` actually calls).

**As of `23041e0f` (AB-0) the `K` residue is owned**, and this reduction is kept as the
reduction it always was rather than as a statement about what is missing.
`Count.exists_nonzero_varCoc_of_tateDualityG` (`Instances/KExactLiftingVar.lean`) is the
carrier-generic twin of `exists_good_twist`, and `lem86_galK_of_noDescent`
(`Instances/KExactLiftingGalK.lean`) is the resulting half-torsor count at `G_K`: it takes
`D.NoDescent` and a surjective `ρ` and nothing else, so the `hvar` binder below is discharged
there.  W81-ASK restated it at the row shape as `askC_halfTorsor_galK`
(`Instances/AskCounting.lean`), measured at std-3 plus B6 plus B1 and **no B7**, the
half-torsor clause being degree-free.  The wave-77 form of this docstring said the residue was
unowned at `K`, and inferred from that the reason `ExactLiftingSemantics` is carried whole in
§4 rather than split; the inference is retracted with the premise. -/
theorem lem86_galK {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
    (D : RadicalCoverData Bg) (ρ : ContinuousMonoidHom (GalK K) (Bg ⧸ D.M))
    (S : TComplement D) (u : TCocycle D ρ)
    (hvar : H2mk (GalK K) (ZMod 2)
      ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S Count.smul_zmod2 u⟩ ≠ 0) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) :=
  Count.lem86N (tfg_galK K) (card_H2_zmodTwo_galK K) D ρ S u hvar

end ScalarBlock

/-! ## §4 The supply record

`KSupply` is `SourceDataN` at `Γ = G_K` minus §1–§3.  Its four data fields are the marked-core
certificate's output (the pro-`2` coordinate of eq. (27)); its three clause fields are AS1's own
`Prop`s at this carrier.  `q` is not a parameter: it is `qOf K FF = 2^{f_K}`, read off B13's unit
filtration, which is what makes `2 ≤ q` and `Even q` automatic (§5). -/

section Supply

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}

/-- **The `G_K`-side supply package** (SD1 memo §3.3's supply map, as a record).

The pro-`2` block is data because it is the *marked-core certificate's* output and that
certificate is per-branch: `pro2` is the composite of `G_K ↠ G_K(2)` with
`MarkedCoreCertificateK{M,N,Sq}.abstractEquiv⁻¹`, which AS2–AS5 build.  `nu_compat` is stated in
AX3's vocabulary (`ι ∘ νP ∘ pro2 = ν_ur^K` on `G_K^{ab}`) because that is the form B10-K's
`compatF_K` consumes; the record's own `compat` field is then *derived*, not assumed.

The three clause fields are the ledger §5.2 vocabulary at the arithmetic carrier.  Field 5
(`scalar`) is absent by design — §3 proves it. -/
structure KSupply (T : OrientedTameQuotientK B FF) (n : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 P)
    (nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  /-- The degree pin: the abstract slot's `n` is `[K : ℚ₂]`. -/
  hdeg : Module.finrank ℚ_[2] K = n
  /-- The numerics pin: the shared `SN` is the packet's at that degree, in the one place the
  scalar clause needs it. -/
  hhom : SN.homScalar = 2 ^ (n + 2)
  /-- **The pro-`2` coordinate of eq. (27)** — the marked-core certificate's output. -/
  pro2 : ContinuousMonoidHom (GalK K) P
  /-- `pro2` is onto the standard core. -/
  hpro2 : Function.Surjective pro2
  /-- `pro2` is *the* maximal pro-`2` quotient map of `G_K`. -/
  ker_pro2 : pro2.toMonoidHom.ker = proPKernel 2 (GalK K)
  /-- **ν-compatibility in AX3's vocabulary**: the pro-`2` unramified coordinate computes the
  marked reciprocity character.  This is the `sourceR` density clause at `K`, and it is what
  B10-K's `compatF_K` turns into the record's `compat`. -/
  nu_compat : ∀ g : GalK K, ztwoIota (nuP (pro2 g)) = B.nu_ur (toAbK K g)
  /-- **Ledger field 3** at `G_K`: `#LiftsOver`, the half-torsor count, the (136) stage. -/
  exactLifting : ExactLiftingSemantics (galKProfinite K) n (qOf K FF) P nuP SN
  /-- **Ledger field 4** at `G_K`: the `T`-cocycle count, separation, nondegeneracy, `#Z¹(V)`. -/
  stokes : StokesDualityCertificate (galKProfinite K) n (qOf K FF) P nuP SN (smulZmod2GalK K)
  /-- **Ledger field 6** at `G_K`: the Gauss-`Z` residue at both heads. -/
  determinant : AffineDeterminantCertificate (galKProfinite K) n (qOf K FF) P nuP SN
    T.tameFK pro2 (fun g => T.compatF_K pro2 nuP nu_compat g) (smulZmod2GalK K)

namespace KSupply

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- **The arithmetic source.**  Ten of `SourceDataN`'s twenty-one fields are proved here, eleven
are projected off the `KSupply`; the field-by-field table is in the module docstring.  (AB-0,
as of `23041e0f`: this line read "nine projected", which never matched the record; the eleven
projected are `pro2`, `ker_pro2`, the three `exactLifting` conjuncts, the four `stokes`
conjuncts and the two `determinant` conjuncts.)

Two of the ten deserve naming.  `surj` is *the same theorem the candidate side uses*: F3's
`boundary_jointly_surjective_of_maxProP`, at `(tameF_K, pro2)`, legitimate because `ker_pro2` pins
`pro2` as the maximal pro-`2` quotient map — so eq. (27) at `K` costs one line and no arithmetic,
exactly as `WordCertificate.toSource` reports on its side.  `compat` is B10-K's `compatF_K`, i.e.
the tame-reciprocity identity `ι ∘ ν_t ∘ tameF_K = ν_ur^K` matched against the supply's
`nu_compat`; note it is *derived* from the AX3/AX4 orientation clauses rather than assumed, which
is what merge gate 6 (full `ℤ₂`-valued marking) requires. -/
noncomputable def toSourceN (KS : KSupply T n P hP nuP SN) :
    SourceDataN n (qOf K FF) P hP nuP SN where
  Γ := galKProfinite K
  tame := T.tameFK
  pro2 := KS.pro2
  compat := fun g => T.compatF_K KS.pro2 nuP KS.nu_compat g
  surj := boundary_jointly_surjective_of_maxProP (qOf_ne_zero K FF) (even_qOf K FF) nuP
    T.tameFK KS.pro2 T.tameFK_surjective KS.hpro2 KS.ker_pro2
    (fun g => T.compatF_K KS.pro2 nuP KS.nu_compat g)
  ker_pro2 := KS.ker_pro2
  smulZmod2 := smulZmod2GalK K
  contSMulZmod2 := contSMulZmod2GalK K
  htriv := htriv_galK K
  tfg := tfg_galK K
  homCard := (scalarHilbert_galK K KS.hdeg KS.hhom).1
  cardH2 := (scalarHilbert_galK K KS.hdeg KS.hhom).2
  liftsOver_card := KS.exactLifting.1
  lem86 := KS.exactLifting.2.1
  stageR136 := KS.exactLifting.2.2
  tcocycle_card := KS.stokes.1
  hsep := KS.stokes.2.1
  hpartial := KS.stokes.2.2.1
  hZcard := KS.stokes.2.2.2
  gaussZ_unramified := KS.determinant.1
  gaussZ_ramified := KS.determinant.2

/-- The source's carrier **is** `G_K` — `rfl`.  This is what `DyadicLocalInput.source_carrier`
becomes: the identity, not a transport.  (AS1 had to carry `source_carrier` as data precisely
because the source was opaque.) -/
theorem toSourceN_carrier (KS : KSupply T n P hP nuP SN) :
    ((KS.toSourceN.Γ : ProfiniteGrp) : Type) = GalK K := rfl

/-- The tame coordinate is surjective — §10's instantiation-side condition 1
(`DyadicLocalInput.htame`), free from B10-K's bundle. -/
theorem toSourceN_htame (KS : KSupply T n P hP nuP SN) :
    Function.Surjective KS.toSourceN.tame :=
  T.tameFK_surjective

/-- The wild part is pro-`2` — §10's instantiation-side condition 2 (`DyadicLocalInput.hwild`):
`ker tameF_K = W_K` (B10-K's `ker_tameFK`) and `W_K` is pro-`2` by the bundle's own clause. -/
theorem toSourceN_hwild (KS : KSupply T n P hP nuP SN) :
    IsProP 2 KS.toSourceN.tame.toMonoidHom.ker :=
  T.ker_tameFK ▸ T.isProP

end KSupply

end Supply

/-! ## §5 Into AS1's record

`DyadicLocalInput` is packet §12's arithmetic bundle plus the carried source.  With §4 in hand the
source and its three side conditions are supplied by the package, so the constructor's remaining
arguments are exactly packet §12's standard local inputs — which is what the ledger says
`DyadicLocalInput` *is*.

`params` is threaded rather than built: `FieldParameters` is F1's `(n, f, q_K)` record and its
`f_dvd_n` clause is field arithmetic that no lane has attached to a `DyadicUnitFiltration`.  The
two pins `params_n`/`params_qK` are therefore hypotheses of the constructor; at a concrete
instance (AS2–AS5) they are `rfl`. -/

section IntoAS1

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
  {R : LocalReciprocity} {B : MarkedRecip R K} {FF : DyadicUnitFiltration K}
  {T : OrientedTameQuotientK B FF} {n : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 P}
  {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}

/-- **The standard local inputs at `K`, assembled** — ASK's output plugged into AS1's record.

The `duality` field is `FieldData.tateDualityGalK K`, i.e. B6 at `G_K`; it is the only field this
constructor fills from an axiom rather than from an argument, and it is filled rather than taken
because a `DyadicLocalInput` whose `duality` disagreed with the one `card_H2_zmodTwo_galK` used
would be incoherent. -/
noncomputable def toLocalInput (KS : KSupply T n P hP nuP SN) (params : FieldParameters)
    (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho)) :
    DyadicLocalInput K R n (qOf K FF) P hP nuP SN where
  params := params
  params_n := params_n
  params_qK := params_qK
  recip := B
  filtration := FF
  tameQuot := T
  duality := FieldData.tateDualityGalK K
  ramified := ramified
  ramifiedData := ramifiedData
  source := KS.toSourceN
  source_carrier := ContinuousMulEquiv.refl (GalK K)
  htame := KS.toSourceN_htame
  hwild := KS.toSourceN_hwild

omit [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] in
/-- **The two `q`-side hypotheses of the main theorem are automatic at `K`.**  `2 ≤ q_K` and
`Even q_K` hold because `q_K = 2^{f}` with `f ≥ 1` (B13's residue degree); AS1 flagged this and
it is discharged here, so AS2–AS5 never supply them by hand. -/
theorem qOf_hyps (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    (FF : DyadicUnitFiltration K) : 2 ≤ qOf K FF ∧ Even (qOf K FF) :=
  ⟨two_le_qOf K FF, even_qOf K FF⟩

/-- **Packet Thm. 1.1 at a supplied `K`** — the ticket's acceptance criterion, and the reason
`toLocalInput` exists.  A word certificate over the *same* slot plus a `KSupply` gives
`Γ_{R_K} ≅ G_K`; the two `q`-side hypotheses of AS1's theorem are discharged from B13's residue
degree, so the only hypothesis left over the two packages is `νP`'s surjectivity, which is
automatic at every standard core (the marking sends `σ ↦ 1`).

Nothing new is proved here: this is `candidate_equiv_absoluteGalois` with its second argument
built rather than assumed.  That *is* the deliverable — before this file the arithmetic argument
had no producer at all. -/
theorem candidate_equiv_galK_of_supply {R : PWord (Generator n)}
    (W : WordCertificate n (qOf K FF) R P hP nuP SN) (KS : KSupply T n P hP nuP SN)
    (params : FieldParameters) (params_n : params.n = n) (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : ∀ {D : Type} [Group D] [TopologicalSpace D] [DiscreteTopology D] [Finite D]
      (V : Type) [AddCommGroup V] [DistribMulAction D V]
      (c : ContinuousMonoidHom (Tq params.qK) D)
      (rho : ContinuousMonoidHom ↥(GalKsub K) D),
      (∃ v : V, c (tqTau params.qK) • v ≠ v) →
        Nonempty (RamifiedCertificate params (GalKsub K) V c rho))
    (hnuP : Function.Surjective nuP) :
    Nonempty (ContinuousMulEquiv ((candidateGroup n (qOf K FF) R : Type)) (GalK K)) :=
  candidate_equiv_absoluteGalois W
    (toLocalInput KS params params_n params_qK ramified ramifiedData)
    (two_le_qOf K FF) (even_qOf K FF) hnuP

end IntoAS1

/-! ## §6 What is still owed, and by whom

**Handover truth-synced as of `23041e0f`** by AB-0 of
`docs/dyadic/followup/analytic-bridges-plan.md` §6, lane W83-HOUSE.  The wave-77 list this
replaces grouped the eleven carried leaves by "the `ℚ₂` object whose `K`-clone would discharge
them"; that framing is itself the thing that went stale, because three of its four items were
answered by a `Γ`-generic layer instead of a clone.  The current handover has **one** item.

1. **`pro2` / `hpro2` / `ker_pro2` / `nu_compat`** (4 data fields) — the marked-core certificate
   composite `G_K ↠ G_K(2) ≅ D_P`.  *Owed by:* AS2–AS5, per branch, via
   `marked_matching_certificate_KM` / `_KN` / `_KSq`.  Not new mathematics: AS1 identified the
   composite; nobody has written it down.  This is the only item on the list that is still
   owed, and it is unchanged since wave 77.

2. **`exactLifting`**: *discharged as a theorem, still carried as a field.*
   `liftsOver_card_galK` and `lem86_galK_of_noDescent` (`Instances/KExactLiftingGalK.lean`) are
   the two counts the wave-77 list called "the natural first targets", and
   `correctedRStageSemantics_galK` (`Instances/KAnalytic.lean`) is stage (136).  Together they
   give `exactLiftingSemanticsRN_galK` at **every** degree.  The frozen bundle this file's §4
   field asks for differs in the (136) coefficient alone, `zR = #R²·#D_R` against the `G_K`
   count `#R^{n+1}·#D_R`, and W81-ASK proved the two equivalent at `2 ≤ n` to the single
   `Prop` `askCStageVanishing` (`Instances/AskCounting.lean`).  Every live row is at `n = 2`.

3. **`stokes`**: *discharged, and the wave-77 prediction was right.*  That item said the right
   shape was "a `Γ`-generic `prop_5_16` over a `TateDualityG Γ 2` bundle plus an Euler-character
   hypothesis, not a `K`-clone".  That is what `Count/LocalDuality.lean` is, and
   `stokesDualityCertificate_galK` (`Instances/KAnalytic.lean`) assembles all four clauses at
   `G_K` from the degree pin alone.  The four `Phase140/Local.lean` residues were never cloned.

4. **`determinant`**: *discharged; the plumbing is the residue.*  `affineDeterminant_galK`
   (`Dyadic/GaussZ/FinalDK.lean`, ticket CB-DET) produces the field's type.  SD1 memo §9's flag
   was honoured: the `K` chain is stated at `|V| * SN.h1Mult |V|`, not at the `ℚ₂` chain's
   `#Z¹ = |V|²`.  What remains is the call.

So the analytic handover is now: one owed data composite (item 1), one statement question
(whether `askCStageVanishing` is wanted, or the row records should be restated against
`ExactLiftingSemanticsRN`, see the module docstring), and three wirings.  Items 2 to 4 are
kept on the list rather than deleted because each is still a *field* here, and a reader who
sees only the record must not conclude from that that the mathematics is missing.

None of these is one of the nine campaign obligations, and none of them may become an axiom.

**A note on how to keep this list true.**  Every stale sentence AB-0 removed from this file had
the same shape: a claim that a `K`-side theorem does not exist, written when it did not, read
years of waves later when it did.  `scripts/scoreboard.sh` re-derives the state of each named
supplier by elaborating it, so a lane that suspects this section has drifted should run that
rather than re-read this. -/

end GQ2.Dyadic
