/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.MarkedCore.Variance
public import GQ2.Dyadic.MarkedCore.CoreMixM
public import GQ2.Dyadic.Word.WordCoh
public import GQ2.Dyadic.SqCore.Cores
public import GQ2.Dyadic.MarkedRecipBundle

@[expose] public section

/-!
# MC5 — `MarkedCoreCertificate` and the marked-matching reduction (packet §7)

**Ticket MC5** of the dyadic campaign (lane MC; the convergence ticket).  Packet authorities:
Def. 7.1 (`def:core-certificate`, proof.tex:711) and Prop. 7.2 (`prop:marked-reduction`,
proof.tex:731); ledger §5.1; MC1 memo (`docs/dyadic/mc-design.md`) §5.3/§6.3; the accumulated
rulings of MC3, MC4, MC-VAR, HM4–HM6g and MC-OB (board log 2026-07-30/31).

## What this file is

The packet's Def. 7.1 certificate has three items: (1) an abstract Demushkin isomorphism
`f : D_P ≃ D_K` supplied by Labute's classification, (2) a proof that the intrinsic orientation
satisfies `χ_K ∘ f = χ_P`, and (3) a marking-correcting automorphism `u ∈ Aut(D_P)` with
`χ_P ∘ u = χ_P` and `ν_K ∘ f ∘ u = ν_P`.  Prop. 7.2 reduces the *construction of `u`* to the
per-core lifting statement — which is exactly what MC3/MC4 + the HM lane landed
(`nMarkedCorrection`, `prop_MC_M_correction`).  This file:

* instantiates MC-OB's generic word-cohomology layer at the marked cores (§1 — the
  `relZ_ofDRCoh` line the MC-OB log assigns to MC5);
* ports the surviving pieces of the `MarkedMatching` engine to the 4-frame (§2);
* proves the marked-matching reductions for both cores (§3), with the N-side S3 stratum a
  **theorem** (`nMixHypothesis_coreMix`, HM6ef) and the M-side residual binders threaded;
* defines `MarkedCoreCertificate{M,N}` per ledger §5.1 and produces them (§4);
* supplies the `K`-facing instantiation layer through AX3's `MarkedRecip` bundle (§5);
* performs the SQ1-R1 redo: the §6.4 handle-mixing analysis in the `L_sq` frame (§6).

## The abstract marked pro-2 slot (design ruling)

Ledger §5.1 writes the certificate against `(K : DyadicField)` with fields `K.chi`, `K.nu`,
`K.maxProTwo` — none of which exist in this repository.  Following SD1's ratified Q4 pattern
("abstract marked pro-2 slot `(P, IsProP 2, nuP)` — SD never waits on MC5"), the certificate
here is parametrized by an abstract topological group `G` together with two *plain* monoid
homs `chiG : G →* ℤ₂ˣ`, `nuG : G →* Multiplicative ℤ₂`.  The certificate's fields are
pointwise equalities, so no continuity is stored; the *production* theorems take the
continuity of the transported marking as an explicit hypothesis (discharged by the bundle's
`continuous_nu_ur` at the `K`-instantiation).  AS1 instantiates `G` at the pro-2 quotient of
`G_K` and discharges the slot; nothing here waits on that.

## Prop. 7.2's hypothesis surface, per core (the accumulated binder state)

The three lifting strata (MC1 §5):

* **S1** (elementary Nielsen): theorems — MC3/MC4's exact families, consumed inside the
  correction theorems.
* **Handle stratum**: a THEOREM (HM4/HM5's `mLiftSplit_handle` / `nLiftSplit_handle`,
  consumed through `nMarkedCorrection` / `prop_MC_M_correction`).
* **S2** (unit scalings): the binders `NScalingHypothesis` / `MMixHypothesis`'s scaling face —
  kept as binders per MC4's deliberate deviation (B8 route cited, not executed; discharging
  them is a separate small ticket and would introduce the census-neutral B8 print, which this
  file must not do).
* **S3** (core mixing): **N-side a THEOREM** (`nMixHypothesis_coreMix`, via HM6ef's widened
  `A⁺(P,h)`); **M-side** the marking-transport binder `MMixHypothesis` (NOT restated in family
  form — owner call pending per the HM6g ruling; `mMixFamily_coreMix` is consumed as-is where
  a family-shaped M5 row is wanted, see the §7 pins).

Net binder inventory for the N-core: `NScalingHypothesis` **alone**.  For the M-core:
`MMixHypothesis` (which subsumes the M-side S2/S3 residual `⟨M4,M6,M7⟩` +
`MLabHypothesis`-adjacent content in transport shape) **plus** the pivot-unit datum below.

## The compact-`M` change-of-variables gap (errata item 3 — explicit datum)

Where Prop. 7.2 transports `ν_K` to the `M`-core, the correction machinery needs
`ν'(C̄₀) ∈ ℤ₂ˣ` (HM memo §6.4 residue 2, HM6g's "one-line F4/MC5 data check").  Whether the
transported marking satisfies it is decided by the **compact-`M` marked change of variables,
which is MISSING from the vendored sources** (MC1 §7.2, owner Q4, errata item 3): the draft
displays only the procyclic substitution, which degenerates at `r = 0`.  Per the standing
rule this file does **not** invent the substitution: the unit row is threaded as the explicit
hypothesis `hpivot : IsUnit (toAdd (nu' (dmC α h)))` everywhere the M-side reduction needs
it, the standard marking discharges it (`isUnit_nuM_dmC` — the non-vacuity pin), and the
`K`-side discharge is F4/packet-author territory.

On the N-side the packet's marked-data clause (`I = C`) pins the *pair*
`(ν'(σ̄), ν'(x̄₂))` unimodular (MC1 §5.3), not the pivot itself; §2's plane solve
(`nPivot_normalize`, the 4-frame descendant of `exists_correction`'s mod-2 step) converts
pair-unimodularity into a unit pivot by the exact family N3.  The N-side reduction therefore
takes the disjunction `IsUnit ν'(σ̄) ∨ IsUnit ν'(x̄₂)` as its marked-data hypothesis.

## The matching-engine port (MC1 §6.2's mandate, resolved against the landed state)

`GQ2/Roe/MarkedMatching.lean:307–1112`'s pipeline, piece by piece:

* **masters** — ported (§2.1): `mMasterMark`/`nMasterMark` realize *every* derivation
  coordinate tuple `c : Fin (coreRank h) → ℤ₂` as a `WordLift ℤ₂ ℤ₂ˣ`-valued marking killing
  the relator (α-uniform; the 4-frame `masterRel`).  The `ContinuousMonoidHom` packaging of
  the rank-three `masterH` is one `mLiftHom` line for any consumer, but it needs
  `IsProP 2 (WordLift ℤ₂ ℤ₂ˣ)`, which lives only in the **plain-import**
  `GQ2/Roe/MarkedMatching.lean` (`isProP_two_wordLift`) — a module-side copy would be a
  ~90-line topology re-derivation with no in-file consumer, so the masters land at the
  algebra level and the packaging note travels here instead.
* **mod-2 span** — ported (§2.2): `exists_isUnit_nu_dmGen`/`_dnGen`: a *surjective*
  `ℤ₂`-character of a presented core has a unit value at some marked generator (the
  span/Nakayama content, run through `dm_hom_ext` against the parity quotient instead of an
  explicit span computation).
* **`evalMatrix` invertibility** — NOT ported, deliberately: its rank-three role (pinning
  the transported orientation and the `(u,b)`-solve) is carried at rank four by MC3/MC4's
  parameter classifications (`mStabilizer_classification`'s `∃!`, `nStabilizer_classification`'s
  iff with `NStabParam.Admissible.det`) — a 4-frame `evalMatrix` would duplicate content that
  no consumer reads.  Recorded as a deviation, not a gap.
* **solve** — ported (§2.3): `nPivot_normalize`, the `(σ̄, x̄₂)`-plane mod-2 solve.
* **contract** — ported (§2.4): `chiM_matching`/`chiN_matching`, the closed-form-uniqueness
  contraction (MC2's `isLabuteOrientationDatum?_unique` + `d?_hom_ext`, letters split by
  MC4's `nCoreIdx_cases`) turning a Labute-datum witness for a transported character into
  the certificate's orientation equality.

## MC-VAR discipline

This file works exclusively with *marked-generator character values* (`nu' (dmGen α h i)`,
`nuFrame`) — the `H¹` side.  No matrix is moved between `M.lean`'s row layout and `N.lean`'s
column layout; the one matrix-valued object consumed (`NStabParam.nuAction` through
`nStabParam_lift_of_scaling`) is `N.lean`'s own, with its `nCoreMat P.g.transpose` correct as
written (MC-VAR verdict).  Cup data enters only through `Variance.lean`'s dictionary names.

## The SQ1-R1 redo (§6) — headline

For the collector/`L_tw` frame S2.4 §6.4 clears the handle plane against the pivot `σ̄`,
using `χ(σ) = 1`.  **For `L_sq` that premise is FALSE** (`χ_sq(σ) = S`, the Hensel value,
`S ≡ 13 (16)` — SQ1 V5/R1): `σ̄` is not χ-trivial and cannot serve as the clearing pivot.
§6 identifies the corrected reachable block: the χ-trivial core direction is the rank-1
module spanned by `w = σ·x₀^{−c}` where `S = X^c` (`c ∈ ℤ₂ˣ` — both depth-2, so the exponent
is a unit), the clearing pivot functional is `ν'(w̄) = ν'(σ̄) − c·ν'(x̄₀)`, and the standard
marking gives `ν_sq(w̄) = 1` **exactly** (the L_sq unit row, the analogue of HM6g's M-side
data check).  The exponent datum `S = X^c` is carried by the record `SqMixPivot`; its
existence is a statement about the procyclic group `1 + 4ℤ₂` (`S` lies in the closed subgroup
generated by `X` since both have depth exactly 2) whose `zpowZtwo`-surjectivity half is not
in the repository — it is recorded as the SQ4 supply obligation, with the mod-16 congruence
`S ≡ X³ (16)` landed here as the c ≡ 3 (4) evidence pin.  The *word-level* realization of
the clearing moves additionally needs a change of variables exhibiting a genuine hyperbolic
pair for `⟨σ̄, x̄₀⟩` (the `L_sq` core carries no literal `[y,z]` factor on that plane — the
shared-commutator-letters caveat of errata item 1), which is why the `L_sq` handle stratum
stays binder-shaped (`SqHandleMixHypothesis`) rather than inheriting `HandleMixLift`.

## Axiom hygiene

Every declaration in this file prints std-3 (`propext`, `Classical.choice`, `Quot.sound`).
No B8 (the S2 stratum stays a binder), no B3c (nothing here touches `dyadicOrientation`; the
SqCore *values* consumed — `chiSq`/`nuSq`/`SvalUnit`/`rootXUnit` — are the std-3 h-generic
definitions, not the B3c/B8-printing rank-3 discharge), no B5/B5-K (the `MarkedRecip` layer
is bundle-parametrized; the axiom `markedRecipAt` is never named).  Census unchanged at 11.
-/

open Multiplicative

namespace GQ2

open FoxH

namespace Dyadic

namespace MarkedCore

/-! ## §1 The MC-OB instantiation: the marked cores in the generic word-cohomology layer

MC-OB's log (2026-07-31, item (ii)): *"the MC2 instantiation goes the other way via
`relZ_ofDRCoh` (the `?RelWord_centLift_fib` fibres ARE this file's `relZ`; one-line anonymous
constructor at the MarkedCore layer — that line belongs to MC5)."*  The layer rule (`Word/`
never imports `MarkedCore/`) puts these lines here: `mRelWord`/`nRelWord` are function-shaped
words with naturality lemmas, so each is a `NatWord` by an anonymous constructor, and MC2's
cup-Gram fibre computations are literally the generic `relZ` against a translated cocycle. -/

section NatWords

/-- **The `M_α` relator as a natural word** — the MC-OB anonymous constructor pairing MC2's
word shape with its naturality lemma. -/
def mNatWord (α h : ℕ) : WordCoh.NatWord (Fin (coreRank h)) where
  ev := fun μ => mRelWord α μ
  nat := fun f μ => map_mRelWord f α μ

/-- **The `N_α` relator as a natural word.** -/
def nNatWord (α h : ℕ) : WordCoh.NatWord (Fin (coreRank h)) where
  ev := fun μ => nRelWord α μ
  nat := fun f μ => map_nRelWord f α μ

/-- **The `L_sq` relator as a natural word** (SqCore's word shape, for the SQ4/WL seam). -/
def sqNatWord (h : ℕ) : WordCoh.NatWord (Fin (SqCore.sqRank h)) where
  ev := fun μ => SqCore.sqRelWord μ
  nat := fun f μ => SqCore.map_sqRelWord f μ

@[simp] theorem mNatWord_ev {α h : ℕ} {G : Type} [Group G] (μ : Fin (coreRank h) → G) :
    (mNatWord α h).ev μ = mRelWord α μ := rfl

@[simp] theorem nNatWord_ev {α h : ℕ} {G : Type} [Group G] (μ : Fin (coreRank h) → G) :
    (nNatWord α h).ev μ = nRelWord α μ := rfl

@[simp] theorem sqNatWord_ev {h : ℕ} {G : Type} [Group G] (μ : Fin (SqCore.sqRank h) → G) :
    (sqNatWord h).ev μ = SqCore.sqRelWord μ := rfl

variable {L : Type} [Group L]

/-- **The MC-OB instantiation line, `M`-side**: the generic relator obstruction of the `M_α`
word against a translated `DRCoh` cocycle IS the fibre MC2's `IsCupCocycle` layer computes.
Definitional — `WordCoh.lift` is `centLift` and the two `CentExt`s agree on the nose. -/
theorem relZ_mNatWord (α h : ℕ) (c : DRCoh.TwoCocycle L) (m : Fin (coreRank h) → L) :
    WordCoh.relZ (mNatWord α h) m (WordCoh.ofDRCoh c)
      = (mRelWord α fun i => centLift c (m i)).fib :=
  WordCoh.relZ_ofDRCoh (mNatWord α h) m c

/-- The `N`-side instantiation line. -/
theorem relZ_nNatWord (α h : ℕ) (c : DRCoh.TwoCocycle L) (m : Fin (coreRank h) → L) :
    WordCoh.relZ (nNatWord α h) m (WordCoh.ofDRCoh c)
      = (nRelWord α fun i => centLift c (m i)).fib :=
  WordCoh.relZ_ofDRCoh (nNatWord α h) m c

/-- **The generic `relZ` of the `M_α` relator is the cup Gram value** — MC2's
`mRelWord_centLift_fib` re-read through the MC-OB layer: the diagonal Bockstein at slot `0`,
the two core hyperbolic pairs, and one hyperbolic pair per handle. -/
theorem relZ_mNatWord_cupGram {c : DRCoh.TwoCocycle L} (hc : IsCupCocycle c) {α h : ℕ}
    (hα : 2 ≤ α) (m : Fin (coreRank h) → L) :
    WordCoh.relZ (mNatWord α h) m (WordCoh.ofDRCoh c)
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  rw [relZ_mNatWord]
  exact hc.mRelWord_centLift_fib hα m

/-- The `N`-side cup Gram value through the MC-OB layer — the same matrix in its own basis. -/
theorem relZ_nNatWord_cupGram {c : DRCoh.TwoCocycle L} (hc : IsCupCocycle c) {α h : ℕ}
    (hα : 2 ≤ α) (m : Fin (coreRank h) → L) :
    WordCoh.relZ (nNatWord α h) m (WordCoh.ofDRCoh c)
      = c.κ (m 0) (m 0) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + (c.κ (m 2) (m 3) + c.κ (m 3) (m 2))
        + ∑ j, (c.κ (m (handleIdxU j)) (m (handleIdxV j))
            + c.κ (m (handleIdxV j)) (m (handleIdxU j))) := by
  rw [relZ_nNatWord]
  exact hc.nRelWord_centLift_fib hα m

end NatWords

section Bundles

/-- Every element of `Multiplicative (ZMod 2)` has square one (ℕ-power form). -/
theorem sq_eq_one_multZMod2' (g : Multiplicative (ZMod 2)) : g ^ (2 : ℕ) = 1 := by
  revert g; decide

/-- **The `M_α` relator is a marked relator for `D_M`** in MC-OB's vocabulary: it lies in the
Frattini subgroup (the abelian collapse `a²c^{2^α}` has even exponents once `α ≥ 1`) and it
holds at the presentation's marking.  This is the entry ticket to `obsH2`/`card_H2_le_two`
for the marked cores — the rank-`(4+2h)` Demushkin `#H² ≤ 2` half — for any consumer that
supplies the (trivial) `ZMod 2` action instances. -/
theorem markedRelator_DM (α h : ℕ) (hα : 1 ≤ α) :
    WordCoh.MarkedRelator (DM α h : Type) (mNatWord α h) (dmGen α h) := by
  refine ⟨fun ν => ?_, dm_relation α h⟩
  show mRelWord α ν = 1
  rw [mRelWord_comm]
  obtain ⟨k, hk⟩ : ∃ k, 2 ^ α = 2 * k := ⟨2 ^ (α - 1), by
    obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring⟩
  rw [hk, pow_mul, sq_eq_one_multZMod2', sq_eq_one_multZMod2', one_pow, one_mul]

/-- The `N`-side marked-relator bundle. -/
theorem markedRelator_DN (α h : ℕ) (hα : 1 ≤ α) :
    WordCoh.MarkedRelator (DN α h : Type) (nNatWord α h) (dnGen α h) := by
  refine ⟨fun ν => ?_, dn_relation α h⟩
  show nRelWord α ν = 1
  rw [nRelWord_comm]
  obtain ⟨k, hk⟩ : ∃ k, 2 + 2 ^ α = 2 * k := ⟨1 + 2 ^ (α - 1), by
    obtain ⟨j, rfl⟩ : ∃ j, α = j + 1 := ⟨α - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ]; ring⟩
  rw [hk, pow_mul, sq_eq_one_multZMod2', one_pow]

/-- **`D_M` is presented by the `M_α` natural word** — the universal-property bundle MC-OB's
`obsH2_injective` consumes, discharged by MC2's `mLiftHom`/`mLiftHom_gen`/`dm_hom_ext`. -/
noncomputable def presentedBy_DM (α h : ℕ) :
    WordCoh.PresentedBy (DM α h : Type) (mNatWord α h) (dmGen α h) where
  liftHom := fun hP ν hν => mLiftHom α h hP ν hν
  liftHom_mark := fun hP ν hν k => mLiftHom_gen α h hP ν hν k
  hom_ext := fun φ ψ hgen => dm_hom_ext φ ψ hgen

/-- The `N`-side presentation bundle. -/
noncomputable def presentedBy_DN (α h : ℕ) :
    WordCoh.PresentedBy (DN α h : Type) (nNatWord α h) (dnGen α h) where
  liftHom := fun hP ν hν => nLiftHom α h hP ν hν
  liftHom_mark := fun hP ν hν k => nLiftHom_gen α h hP ν hν k
  hom_ext := fun φ ψ hgen => dn_hom_ext φ ψ hgen

end Bundles

/-! ## §2 The 4-frame matching-engine port

The pieces of `GQ2/Roe/MarkedMatching.lean:307–1112` that survive to rank `4 + 2h`, in the
form the §3 reductions consume.  See the module docstring for the piece-by-piece disposition
(including why the `evalMatrix` block is deliberately *not* duplicated). -/

section Masters

/-- **The `M`-master marking** at a derivation coordinate tuple `c` — the 4-frame analogue of
`masterH`'s value table: slot `i` carries the pair `⟨c i, χ_M(gen i)⟩` in `WordLift ℤ₂ ℤ₂ˣ`,
with the canonical closed-form orientation values on the four core letters and `1` on every
handle letter. -/
noncomputable def mMasterMark (α : ℕ) {h : ℕ} (c : Fin (coreRank h) → ℤ_[2]) :
    Fin (coreRank h) → WordLift ℤ_[2] ℤ_[2]ˣ :=
  fun i => ⟨c i, coreMark 1 (-1) 1 (mUnit α) i⟩

/-- The `N`-master marking. -/
noncomputable def nMasterMark (α : ℕ) {h : ℕ} (c : Fin (coreRank h) → ℤ_[2]) :
    Fin (coreRank h) → WordLift ℤ_[2] ℤ_[2]ˣ :=
  fun i => ⟨c i, coreMark 1 (nUnit α) 1 1 i⟩

/-- **The 4-frame `masterRel`, `M`-side** (α-uniform): the `M_α` relator dies at the master
marking for **every** coordinate tuple — the derivation space of the presented core at the
canonical orientation is full.  This is what makes the rank-three master family portable:
the core block is MC2's closed-form datum theorem and the handle block is the handle lemma. -/
theorem mRelWord_mMasterMark {α : ℕ} (hα : 1 ≤ α) {h : ℕ} (c : Fin (coreRank h) → ℤ_[2]) :
    mRelWord α (mMasterMark α c) = 1 := by
  have h0 : mMasterMark α c 0 = ⟨c 0, 1⟩ := by
    show (⟨c 0, coreMark 1 (-1) 1 (mUnit α) 0⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_zero]
  have h1 : mMasterMark α c 1 = ⟨c 1, -1⟩ := by
    show (⟨c 1, coreMark 1 (-1) 1 (mUnit α) 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_one]
  have h2 : mMasterMark α c 2 = ⟨c 2, 1⟩ := by
    show (⟨c 2, coreMark 1 (-1) 1 (mUnit α) 2⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_two]
  have h3 : mMasterMark α c 3 = ⟨c 3, mUnit α⟩ := by
    show (⟨c 3, coreMark 1 (-1) 1 (mUnit α) 3⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_three]
  have hU : ∀ j : Fin h, mMasterMark α c (handleIdxU j) = ⟨c (handleIdxU j), 1⟩ := fun j => by
    show (⟨c (handleIdxU j), coreMark 1 (-1) 1 (mUnit α) (handleIdxU j)⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_handleU]
  have hV : ∀ j : Fin h, mMasterMark α c (handleIdxV j) = ⟨c (handleIdxV j), 1⟩ := fun j => by
    show (⟨c (handleIdxV j), coreMark 1 (-1) 1 (mUnit α) (handleIdxV j)⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_handleV]
  rw [mRelWord, h0, h1, h2, h3,
    show (fun j => mMasterMark α c (handleIdxU j)) = fun j => (⟨c (handleIdxU j), 1⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) from funext hU,
    show (fun j => mMasterMark α c (handleIdxV j)) = fun j => (⟨c (handleIdxV j), 1⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) from funext hV,
    isLabuteOrientationDatumM_mUnit hα (c 0) (c 1) (c 2) (c 3),
    handleWord_wordLift_one, one_mul]

/-- **The 4-frame `masterRel`, `N`-side.** -/
theorem nRelWord_nMasterMark {α : ℕ} (hα : 1 ≤ α) {h : ℕ} (c : Fin (coreRank h) → ℤ_[2]) :
    nRelWord α (nMasterMark α c) = 1 := by
  have h0 : nMasterMark α c 0 = ⟨c 0, 1⟩ := by
    show (⟨c 0, coreMark 1 (nUnit α) 1 1 0⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_zero]
  have h1 : nMasterMark α c 1 = ⟨c 1, nUnit α⟩ := by
    show (⟨c 1, coreMark 1 (nUnit α) 1 1 1⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_one]
  have h2 : nMasterMark α c 2 = ⟨c 2, 1⟩ := by
    show (⟨c 2, coreMark 1 (nUnit α) 1 1 2⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_two]
  have h3 : nMasterMark α c 3 = ⟨c 3, 1⟩ := by
    show (⟨c 3, coreMark 1 (nUnit α) 1 1 3⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_three]
  have hU : ∀ j : Fin h, nMasterMark α c (handleIdxU j) = ⟨c (handleIdxU j), 1⟩ := fun j => by
    show (⟨c (handleIdxU j), coreMark 1 (nUnit α) 1 1 (handleIdxU j)⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_handleU]
  have hV : ∀ j : Fin h, nMasterMark α c (handleIdxV j) = ⟨c (handleIdxV j), 1⟩ := fun j => by
    show (⟨c (handleIdxV j), coreMark 1 (nUnit α) 1 1 (handleIdxV j)⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) = _
    rw [coreMark_handleV]
  rw [nRelWord, h0, h1, h2, h3,
    show (fun j => nMasterMark α c (handleIdxU j)) = fun j => (⟨c (handleIdxU j), 1⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) from funext hU,
    show (fun j => nMasterMark α c (handleIdxV j)) = fun j => (⟨c (handleIdxV j), 1⟩ :
      WordLift ℤ_[2] ℤ_[2]ˣ) from funext hV,
    isLabuteOrientationDatumN_nUnit hα (c 0) (c 1) (c 2) (c 3),
    handleWord_wordLift_one, one_mul]

end Masters

section Span

variable (α h : ℕ)

/-- The sign character of the `ν`-target — MC3's `mSign` read multiplicatively, the mod-2
reduction the span argument runs through.  (`ℤ₂ˣ` is used as the discrete-free stand-in for
`ZMod 2`: the repo carries no global topology on `ZMod n`, and `mSign`'s continuity is
already a theorem.) -/
noncomputable def nuSignHom : ContinuousMonoidHom (Multiplicative ℤ_[2]) ℤ_[2]ˣ where
  toFun := fun x => mSign (toAdd x)
  map_one' := by rw [toAdd_one, mSign_zero]
  map_mul' := fun x y => by rw [toAdd_mul, mSign_add]
  continuous_toFun := mSign_continuous.comp continuous_toAdd

@[simp] theorem nuSignHom_apply (x : Multiplicative ℤ_[2]) :
    nuSignHom x = mSign (toAdd x) := rfl

/-- The sign of `1` is `−1` — what makes `nuSignHom` separate units from non-units. -/
theorem mSign_one : mSign (1 : ℤ_[2]) = -1 := by
  rw [mSign, map_one]
  rw [show ((1 : ZMod (2 ^ 1))).val = 1 from rfl, pow_one]

/-- **The mod-2 span/Nakayama port, `M`-side**: a surjective `ℤ₂`-character of `D_M` has a
2-adic **unit** value at some marked generator.  (Rank-three shape: the mod-2 reduction of a
topologically generating family spans, so not every coordinate can vanish mod 2 — here run
through `dm_hom_ext` against the trivial hom instead of an explicit span computation.) -/
theorem exists_isUnit_nu_dmGen (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hsurj : Function.Surjective nu') :
    ∃ i : Fin (coreRank h), IsUnit (toAdd (nu' (dmGen α h i))) := by
  by_contra hall
  push Not at hall
  have hcomp : nuSignHom.comp nu' = 1 := by
    refine dm_hom_ext _ _ fun i => ?_
    show mSign (toAdd (nu' (dmGen α h i))) = 1
    have hpar : mParityZ (toAdd (nu' (dmGen α h i))) = 0 := by
      by_contra hne
      refine hall i (mIsUnit_of_parity_one ?_)
      revert hne
      generalize mParityZ (toAdd (nu' (dmGen α h i))) = z
      revert z; decide
    obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff _).mp hpar
    rw [hy, mSign_two_mul]
  obtain ⟨d, hd⟩ := hsurj (ofAdd 1)
  have h1 : mSign (toAdd (nu' d)) = 1 := DFunLike.congr_fun hcomp d
  rw [hd, toAdd_ofAdd, mSign_one] at h1
  have hval : ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2]) := congrArg Units.val h1
  rw [Units.val_neg, Units.val_one] at hval
  norm_num at hval

/-- The `N`-side span/Nakayama port. -/
theorem exists_isUnit_nu_dnGen (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hsurj : Function.Surjective nu') :
    ∃ i : Fin (coreRank h), IsUnit (toAdd (nu' (dnGen α h i))) := by
  by_contra hall
  push Not at hall
  have hcomp : nuSignHom.comp nu' = 1 := by
    refine dn_hom_ext _ _ fun i => ?_
    show mSign (toAdd (nu' (dnGen α h i))) = 1
    have hpar : mParityZ (toAdd (nu' (dnGen α h i))) = 0 := by
      by_contra hne
      refine hall i (mIsUnit_of_parity_one ?_)
      revert hne
      generalize mParityZ (toAdd (nu' (dnGen α h i))) = z
      revert z; decide
    obtain ⟨y, hy⟩ := (mParityZ_eq_zero_iff _).mp hpar
    rw [hy, mSign_two_mul]
  obtain ⟨d, hd⟩ := hsurj (ofAdd 1)
  have h1 : mSign (toAdd (nu' d)) = 1 := DFunLike.congr_fun hcomp d
  rw [hd, toAdd_ofAdd, mSign_one] at h1
  have hval : ((-1 : ℤ_[2]ˣ) : ℤ_[2]) = ((1 : ℤ_[2]ˣ) : ℤ_[2]) := congrArg Units.val h1
  rw [Units.val_neg, Units.val_one] at hval
  norm_num at hval

end Span

section Solve

variable (α h : ℕ)

/-- **The plane solve** (the 4-frame descendant of `exists_correction`'s mod-2 step): from
the packet's marked-data clause — MC1 §5.3's reading, the *pair* `(ν'(σ̄), ν'(x̄₂))` is
unimodular — produce a χ-preserving exact automorphism after which the **pivot** `σ̄` carries
a unit.  The move is family N3 (`dnTauCEquiv`, axiom-free): if `ν'(σ̄)` is even and `ν'(x̄₂)`
odd, then `σ ↦ x₂·σ` makes the pivot value `ν'(x̄₂) + ν'(σ̄)`, which is odd. -/
theorem nPivot_normalize (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hpair : IsUnit (toAdd (nu' (dnSigma α h))) ∨ IsUnit (toAdd (nu' (dnX2 α h)))) :
    ∃ Ψ : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (Ψ x) = chiN α h x) ∧ IsUnit (toAdd (nu' (Ψ (dnSigma α h)))) := by
  by_cases hσ : IsUnit (toAdd (nu' (dnSigma α h)))
  · exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, hσ⟩
  rcases hpair with hσ' | hx2
  · exact absurd hσ' hσ
  refine ⟨dnTauCEquiv α h 1, chiN_dnTauCEquiv α h 1, ?_⟩
  rw [dnTauCEquiv_dnSigma, map_mul, toAdd_mul,
    toAdd_map_zpowZtwo (isProP_DN α h) nu', one_mul]
  rw [nIsUnit_iff_nRed] at hσ hx2 ⊢
  rw [map_add, hx2]
  have h0 : nRed (toAdd (nu' (dnSigma α h))) = 0 := by
    revert hσ
    generalize nRed (toAdd (nu' (dnSigma α h))) = z
    revert z; decide
  rw [h0, add_zero]

end Solve

section Contract

/-- **The contraction, `M`-side** (packet Def. 7.1 item 2, reduced): a continuous character
of `D_M` whose core values form a Labute orientation datum and which kills the handle letters
IS the canonical orientation `χ_M` — MC2's closed-form uniqueness contracted along the
rank-`(4+2h)` letter split (`nCoreIdx_cases`) through `dm_hom_ext`.  The datum witness for a
*transported* `χ_K ∘ f` is the certificate's orientation input; this theorem is what turns it
into the pointwise equality the certificate stores. -/
theorem chiM_matching {α h : ℕ} (hα : 1 ≤ α)
    (χ' : ContinuousMonoidHom (DM α h : Type) ℤ_[2]ˣ)
    (hdatum : IsLabuteOrientationDatumM α (χ' (dmA α h)) (χ' (dmB α h)) (χ' (dmC α h))
      (χ' (dmD α h)))
    (hU : ∀ j : Fin h, χ' (dmGen α h (handleIdxU j)) = 1)
    (hV : ∀ j : Fin h, χ' (dmGen α h (handleIdxV j)) = 1) :
    ∀ x, χ' x = chiM α h x := by
  obtain ⟨h0, h1, h2, h3⟩ := isLabuteOrientationDatumM_unique hα hdatum
  have hext : χ' = chiM α h := by
    refine dm_hom_ext _ _ fun i => ?_
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show dmGen α h 0 = dmA α h from rfl, h0, chiM_dmA]
    · rw [show dmGen α h 1 = dmB α h from rfl, h1, chiM_dmB]
    · rw [show dmGen α h 2 = dmC α h from rfl, h2, chiM_dmC]
    · rw [show dmGen α h 3 = dmD α h from rfl, h3, chiM_dmD]
    · rw [hU j, chiM_handleU]
    · rw [hV j, chiM_handleV]
  exact fun x => DFunLike.congr_fun hext x

/-- **The contraction, `N`-side.** -/
theorem chiN_matching {α h : ℕ} (hα : 1 ≤ α)
    (χ' : ContinuousMonoidHom (DN α h : Type) ℤ_[2]ˣ)
    (hdatum : IsLabuteOrientationDatumN α (χ' (dnX0 α h)) (χ' (dnX1 α h)) (χ' (dnSigma α h))
      (χ' (dnX2 α h)))
    (hU : ∀ j : Fin h, χ' (dnGen α h (handleIdxU j)) = 1)
    (hV : ∀ j : Fin h, χ' (dnGen α h (handleIdxV j)) = 1) :
    ∀ x, χ' x = chiN α h x := by
  obtain ⟨h0, h1, h2, h3⟩ := isLabuteOrientationDatumN_unique hα hdatum
  have hext : χ' = chiN α h := by
    refine dn_hom_ext _ _ fun i => ?_
    rcases nCoreIdx_cases i with rfl | rfl | rfl | rfl | ⟨j, rfl⟩ | ⟨j, rfl⟩
    · rw [show dnGen α h 0 = dnX0 α h from rfl, h0, chiN_dnX0]
    · rw [show dnGen α h 1 = dnX1 α h from rfl, h1, chiN_dnX1]
    · rw [show dnGen α h 2 = dnSigma α h from rfl, h2, chiN_dnSigma]
    · rw [show dnGen α h 3 = dnX2 α h from rfl, h3, chiN_dnX2]
    · rw [hU j, chiN_handleU]
    · rw [hV j, chiN_handleV]
  exact fun x => DFunLike.congr_fun hext x

end Contract

/-! ## §3 The marked-matching reductions (packet Prop. 7.2, item 3)

The per-core correction `u ∈ Aut(D_P)` with `χ_P ∘ u = χ_P` and `ν' ∘ u = ν_P`, from the
marked-data hypotheses and the surviving binders.  The `N`-side consumes **one** binder
(`NScalingHypothesis` — S2 through B8, cited not executed); its S3 stratum is HM6ef's
theorem.  The `M`-side consumes `MMixHypothesis` plus the compact-`M` pivot datum
(errata item 3 — see the module docstring). -/

section Reductions

variable (α h : ℕ)

/-- **The marked-matching reduction at the `N`-core** (packet Prop. 7.2): under the S2
scaling binder alone, every transported marking with unimodular `(σ̄, x̄₂)`-pair admits a
χ-preserving correction `u` with `ν' ∘ u = ν_N`.  Composition: the §2 plane solve, then
MC4's `nMarkedCorrection` with its S3 hypothesis discharged by `nMixHypothesis_coreMix`. -/
theorem nMarkedMatching (hScal : NScalingHypothesis α h)
    (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hpair : IsUnit (toAdd (nu' (dnSigma α h))) ∨ IsUnit (toAdd (nu' (dnX2 α h)))) :
    ∃ u : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (u x) = chiN α h x) ∧ ∀ x, nu' (u x) = nuN α h x := by
  obtain ⟨Ψ₀, hΨ₀chi, hpiv⟩ := nPivot_normalize α h nu' hpair
  obtain ⟨u, huchi, hunu⟩ := nMarkedCorrection α h (nMixHypothesis_coreMix α h) hScal
    (nu'.comp (autHom Ψ₀)) hpiv
  refine ⟨u.trans Ψ₀, fun x => ?_, fun x => hunu x⟩
  show chiN α h (Ψ₀ (u x)) = chiN α h x
  rw [hΨ₀chi, huchi]

/-- **The marked-matching reduction at the `M`-core**: under the transport binder
`MMixHypothesis` and the compact-`M` pivot datum `IsUnit (ν'(C̄₀))` — threaded explicitly
because the compact-`M` marked change of variables is missing from the vendored sources
(errata item 3) — every transported marking admits a χ-preserving correction with
`ν' ∘ u = ν_M` **on all of `D_M`** (MC3's generator-wise conclusion upgraded through
`dm_hom_ext`). -/
theorem mMarkedMatching {α h : ℕ} (hα : 1 ≤ α) (hMix : MMixHypothesis α h hα)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hpivot : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ u : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (u x) = chiM α h x) ∧ ∀ x, nu' (u x) = nuM α h hα x := by
  obtain ⟨Ψ, hchi, hgen⟩ := prop_MC_M_correction hα hMix nu' hpivot
  refine ⟨Ψ, hchi, fun x => ?_⟩
  have hext : nu'.comp (autHom Ψ) = nuM α h hα :=
    dm_hom_ext _ _ fun i => hgen i
  exact DFunLike.congr_fun hext x

/-- **The `M`-side pivot row is satisfiable** — HM6g's "one-line F4/MC5 data check", landed:
the standard marking meets the threaded compact-`M` datum (`isUnit_nuM_dmC`), so the
reduction's hypothesis set is non-empty at every `(α, h)` and the question is genuinely
about the *transported* `ν' = ν_K ∘ f`, i.e. about the missing change of variables. -/
theorem mMarkedMatching_nuM {α h : ℕ} (hα : 1 ≤ α) (hMix : MMixHypothesis α h hα) :
    ∃ u : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (u x) = chiM α h x) ∧ ∀ x, nuM α h hα (u x) = nuM α h hα x :=
  mMarkedMatching hα hMix (nuM α h hα) (isUnit_nuM_dmC α h hα)

/-- The `N`-side reduction in `NLiftSplit` clothing (HM4's split API): the record's handle
field is a theorem, so carrying the record adds no assumption — it exists so downstream code
can consume the reduction in the shape the split advertises (`nLiftSplit_iff` supplies two of
three fields). -/
theorem nMarkedMatching_of_liftSplit {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : NLiftSplit α h S12 S3) (hScal : NScalingHypothesis α h)
    (nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]))
    (hpair : IsUnit (toAdd (nu' (dnSigma α h))) ∨ IsUnit (toAdd (nu' (dnX2 α h)))) :
    ∃ u : ContinuousMulEquiv (DN α h : Type) (DN α h : Type),
      (∀ x, chiN α h (u x) = chiN α h x) ∧ ∀ x, nu' (u x) = nuN α h x :=
  nMarkedMatching α h hScal nu' hpair

/-- The `M`-side reduction in `MLiftSplit` clothing. -/
theorem mMarkedMatching_of_liftSplit {α h : ℕ} (hα : 1 ≤ α)
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : MLiftSplit α h S12 S3) (hMix : MMixHypothesis α h hα)
    (nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]))
    (hpivot : IsUnit (toAdd (nu' (dmC α h)))) :
    ∃ u : ContinuousMulEquiv (DM α h : Type) (DM α h : Type),
      (∀ x, chiM α h (u x) = chiM α h x) ∧ ∀ x, nu' (u x) = nuM α h hα x :=
  mMarkedMatching hα hMix nu' hpivot

end Reductions

/-! ## §4 `MarkedCoreCertificate` (packet Def. 7.1 / ledger §5.1)

The five ledger fields (`abstractEquiv`, `orientation`, `correction`, `correction_chi`,
`correction_nu`), stated against the abstract marked pro-2 slot `(G, chiG, nuG)` — see the
module docstring for the design ruling.  The characters are *plain* monoid homs: the
certificate stores pointwise equalities, and continuity lives in the production theorems'
hypotheses. -/

section Certificate

/-- **The marked-core certificate for the `M_α` family** (packet Def. 7.1, ledger §5.1). -/
structure MarkedCoreCertificateM (α h : ℕ) (hα : 1 ≤ α) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  /-- Item 1: the abstract Demushkin isomorphism (Labute's classification —
  `MLabHypothesis`'s output at the `G_K(2)` slot). -/
  abstractEquiv : ContinuousMulEquiv (DM α h : Type) G
  /-- Item 2: the intrinsic orientation matches the canonical one through the isomorphism. -/
  orientation : ∀ x, chiG (abstractEquiv x) = chiM α h x
  /-- Item 3a: the marking-correcting automorphism. -/
  correction : ContinuousMulEquiv (DM α h : Type) (DM α h : Type)
  /-- Item 3b: the correction preserves the canonical orientation. -/
  correction_chi : ∀ x, chiM α h (correction x) = chiM α h x
  /-- Item 3c: the corrected isomorphism matches the unramified markings. -/
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) = nuM α h hα x

/-- **The marked-core certificate for the `N_α` family.** -/
structure MarkedCoreCertificateN (α h : ℕ) {G : Type} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G]
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2]) where
  /-- Item 1: the abstract Demushkin isomorphism. -/
  abstractEquiv : ContinuousMulEquiv (DN α h : Type) G
  /-- Item 2: the orientation matching. -/
  orientation : ∀ x, chiG (abstractEquiv x) = chiN α h x
  /-- Item 3a: the marking-correcting automorphism. -/
  correction : ContinuousMulEquiv (DN α h : Type) (DN α h : Type)
  /-- Item 3b: χ-preservation of the correction. -/
  correction_chi : ∀ x, chiN α h (correction x) = chiN α h x
  /-- Item 3c: the marking matching. -/
  correction_nu : ∀ x, nuG (abstractEquiv (correction x)) = nuN α h x

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **Certificate production, `N`-side** (packet Prop. 7.2 assembled): from the hypothesized
abstract isomorphism (item 1), the orientation-matching datum (item 2), the continuity of the
transported marking, the marked-data pair-unimodularity, and the single surviving binder
`NScalingHypothesis`, the full certificate exists. -/
theorem marked_matching_certificate_N (α h : ℕ)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN α h : Type) G)
    (horient : ∀ x, chiG (f x) = chiN α h x)
    (hcont : Continuous fun x : (DN α h : Type) => nuG (f x))
    (hScal : NScalingHypothesis α h)
    (hpair : IsUnit (toAdd (nuG (f (dnSigma α h)))) ∨ IsUnit (toAdd (nuG (f (dnX2 α h))))) :
    Nonempty (MarkedCoreCertificateN α h chiG nuG) := by
  set nu' : ContinuousMonoidHom (DN α h : Type) (Multiplicative ℤ_[2]) :=
    { toFun := fun x => nuG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hcont } with hnu'
  obtain ⟨u, huchi, hunu⟩ := nMarkedMatching α h hScal nu' hpair
  exact ⟨⟨f, horient, u, huchi, fun x => hunu x⟩⟩

/-- **Certificate production, `M`-side**: as for `N`, with the `MMixHypothesis` binder and
the compact-`M` pivot datum (errata item 3) in place of the pair clause. -/
theorem marked_matching_certificate_M (α h : ℕ) (hα : 1 ≤ α)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α h : Type) G)
    (horient : ∀ x, chiG (f x) = chiM α h x)
    (hcont : Continuous fun x : (DM α h : Type) => nuG (f x))
    (hMix : MMixHypothesis α h hα)
    (hpivot : IsUnit (toAdd (nuG (f (dmC α h))))) :
    Nonempty (MarkedCoreCertificateM α h hα chiG nuG) := by
  set nu' : ContinuousMonoidHom (DM α h : Type) (Multiplicative ℤ_[2]) :=
    { toFun := fun x => nuG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hcont } with hnu'
  obtain ⟨u, huchi, hunu⟩ := mMarkedMatching hα hMix nu' hpivot
  exact ⟨⟨f, horient, u, huchi, fun x => hunu x⟩⟩

/-- Certificate production, `N`-side, with the orientation supplied in **datum form** (the
shape a `K`-side cohomological argument produces) and contracted by §2.4's port. -/
theorem marked_matching_certificate_N_of_datum (α h : ℕ) (hα : 1 ≤ α)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN α h : Type) G)
    (hχcont : Continuous fun x : (DN α h : Type) => chiG (f x))
    (hdatum : IsLabuteOrientationDatumN α (chiG (f (dnX0 α h))) (chiG (f (dnX1 α h)))
      (chiG (f (dnSigma α h))) (chiG (f (dnX2 α h))))
    (hU : ∀ j : Fin h, chiG (f (dnGen α h (handleIdxU j))) = 1)
    (hV : ∀ j : Fin h, chiG (f (dnGen α h (handleIdxV j))) = 1)
    (hcont : Continuous fun x : (DN α h : Type) => nuG (f x))
    (hScal : NScalingHypothesis α h)
    (hpair : IsUnit (toAdd (nuG (f (dnSigma α h)))) ∨ IsUnit (toAdd (nuG (f (dnX2 α h))))) :
    Nonempty (MarkedCoreCertificateN α h chiG nuG) := by
  set χ' : ContinuousMonoidHom (DN α h : Type) ℤ_[2]ˣ :=
    { toFun := fun x => chiG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hχcont } with hχ'
  have horient : ∀ x, chiG (f x) = chiN α h x :=
    chiN_matching hα χ' hdatum hU hV
  exact marked_matching_certificate_N α h chiG nuG f horient hcont hScal hpair

/-- Certificate production, `M`-side, orientation in datum form. -/
theorem marked_matching_certificate_M_of_datum (α h : ℕ) (hα : 1 ≤ α)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α h : Type) G)
    (hχcont : Continuous fun x : (DM α h : Type) => chiG (f x))
    (hdatum : IsLabuteOrientationDatumM α (chiG (f (dmA α h))) (chiG (f (dmB α h)))
      (chiG (f (dmC α h))) (chiG (f (dmD α h))))
    (hU : ∀ j : Fin h, chiG (f (dmGen α h (handleIdxU j))) = 1)
    (hV : ∀ j : Fin h, chiG (f (dmGen α h (handleIdxV j))) = 1)
    (hcont : Continuous fun x : (DM α h : Type) => nuG (f x))
    (hMix : MMixHypothesis α h hα)
    (hpivot : IsUnit (toAdd (nuG (f (dmC α h))))) :
    Nonempty (MarkedCoreCertificateM α h hα chiG nuG) := by
  set χ' : ContinuousMonoidHom (DM α h : Type) ℤ_[2]ˣ :=
    { toFun := fun x => chiG (f x)
      map_one' := by rw [map_one, map_one]
      map_mul' := fun x y => by rw [map_mul, map_mul]
      continuous_toFun := hχcont } with hχ'
  have horient : ∀ x, chiG (f x) = chiM α h x :=
    chiM_matching hα χ' hdatum hU hV
  exact marked_matching_certificate_M α h hα chiG nuG f horient hcont hMix hpivot

/-- Certificate production consuming the `NLiftSplit` record (HM4's split API; the record's
stratum sets are carried but the handle field is the theorem, so only `hScal` is real). -/
theorem marked_matching_certificate_N_of_liftSplit (α h : ℕ)
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : NLiftSplit α h S12 S3)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DN α h : Type) G)
    (horient : ∀ x, chiG (f x) = chiN α h x)
    (hcont : Continuous fun x : (DN α h : Type) => nuG (f x))
    (hScal : NScalingHypothesis α h)
    (hpair : IsUnit (toAdd (nuG (f (dnSigma α h)))) ∨ IsUnit (toAdd (nuG (f (dnX2 α h))))) :
    Nonempty (MarkedCoreCertificateN α h chiG nuG) :=
  marked_matching_certificate_N α h chiG nuG f horient hcont hScal hpair

/-- Certificate production consuming the `MLiftSplit` record. -/
theorem marked_matching_certificate_M_of_liftSplit (α h : ℕ) (hα : 1 ≤ α)
    {S12 S3 : Set (Function.End (Fin (coreRank h) → ℤ_[2]))}
    (_hs : MLiftSplit α h S12 S3)
    (chiG : G →* ℤ_[2]ˣ) (nuG : G →* Multiplicative ℤ_[2])
    (f : ContinuousMulEquiv (DM α h : Type) G)
    (horient : ∀ x, chiG (f x) = chiM α h x)
    (hcont : Continuous fun x : (DM α h : Type) => nuG (f x))
    (hMix : MMixHypothesis α h hα)
    (hpivot : IsUnit (toAdd (nuG (f (dmC α h))))) :
    Nonempty (MarkedCoreCertificateM α h hα chiG nuG) :=
  marked_matching_certificate_M α h hα chiG nuG f horient hcont hMix hpivot

end Certificate

/-! ## §5 The `K`-facing instantiation layer (AX3's `MarkedRecip` bundle)

The `K`-side characters live on `GalKab K` (the bundle's `ν_ur^K` and the cyclotomic
`chiCycKAb K`), while the certificate's slot `G` is the pro-2 quotient of `G_K` that AS1
will supply.  Following `markedPro2_R`'s pattern, the layer here does not construct that
quotient: it reads the two characters through an *abelianization slot* `π : G →* GalKab K`
(for the intended instantiation, the composite of `toAbK` with the pro-2 projection's
section data — AS1's `sourceR`-transport recipe), so that the whole layer stays
bundle-parametrized and axiom-free.  `markedRecipAt` is never named. -/

section KLayer

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K]

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- **The `K`-instantiated `N`-certificate**: the abstract certificate at the bundle's
marked characters, read through the abelianization slot `π`. -/
abbrev MarkedCoreCertificateKN (B : MarkedRecip R K) (α h : ℕ) (π : G →* GalKab K) :=
  MarkedCoreCertificateN α h ((chiCycKAb K).comp π) (B.nu_ur.comp π)

/-- **The `K`-instantiated `M`-certificate.** -/
abbrev MarkedCoreCertificateKM (B : MarkedRecip R K) (α h : ℕ) (hα : 1 ≤ α)
    (π : G →* GalKab K) :=
  MarkedCoreCertificateM α h hα ((chiCycKAb K).comp π) (B.nu_ur.comp π)

/-- **The `K`-side production, `N`-family** (packet Prop. 7.2 at `K`): the bundle's
`continuous_nu_ur` discharges the marking-continuity hypothesis, so the inputs are the
abstract isomorphism, the continuity of the slot, the orientation matching, the marked-data
pair clause, and the S2 binder. -/
theorem marked_matching_certificate_KN (B : MarkedRecip R K) (α h : ℕ)
    (π : G →* GalKab K) (hπ : Continuous π)
    (f : ContinuousMulEquiv (DN α h : Type) G)
    (horient : ∀ x, chiCycKAb K (π (f x)) = chiN α h x)
    (hScal : NScalingHypothesis α h)
    (hpair : IsUnit (toAdd (B.nu_ur (π (f (dnSigma α h)))))
      ∨ IsUnit (toAdd (B.nu_ur (π (f (dnX2 α h)))))) :
    Nonempty (MarkedCoreCertificateKN B α h π) :=
  marked_matching_certificate_N α h ((chiCycKAb K).comp π) (B.nu_ur.comp π) f horient
    (B.continuous_nu_ur.comp (hπ.comp f.continuous_toFun)) hScal hpair

/-- **The `K`-side production, `M`-family**, with the compact-`M` pivot datum threaded
explicitly (errata item 3: the vendored sources do not determine `ν_ur^K(f(C₀))`'s
unit-ness at `r = 0` — the packet author's change of variables is the missing input). -/
theorem marked_matching_certificate_KM (B : MarkedRecip R K) (α h : ℕ) (hα : 1 ≤ α)
    (π : G →* GalKab K) (hπ : Continuous π)
    (f : ContinuousMulEquiv (DM α h : Type) G)
    (horient : ∀ x, chiCycKAb K (π (f x)) = chiM α h x)
    (hMix : MMixHypothesis α h hα)
    (hpivot : IsUnit (toAdd (B.nu_ur (π (f (dmC α h)))))) :
    Nonempty (MarkedCoreCertificateKM B α h hα π) :=
  marked_matching_certificate_M α h hα ((chiCycKAb K).comp π) (B.nu_ur.comp π) f horient
    (B.continuous_nu_ur.comp (hπ.comp f.continuous_toFun)) hMix hpivot

end KLayer

/-! ## §6 The SQ1-R1 redo: handle mixing in the `L_sq` frame

S2.4 §6.4's clearing analysis (reproduced by the HM memo §2 and consumed by HM4/HM5) reads:
clear the handle plane against the pivot `σ̄`, whose `ν'`-value is a unit because `ν'` is
surjective on `ker χ ⊇ ⟨σ̄⟩ ⊕ P_han` — using `χ(σ) = 1`.  SQ1 V5/R1: **that premise is false
for `L_sq`** (`χ_sq(σ) = S`, the Hensel value, infinite order), so the reachable-block
identification must be redone in the `L_sq` frame.  HM5's deferral note assigns the redo
here.

### The corrected identification

On the `L_sq` frame `ℤ/2·t ⊕ ℤ₂σ̄ ⊕ ℤ₂x̄₀ ⊕ P_han` the χ-trivial subspace is
`(ker χ̄ ∩ ⟨σ̄, x̄₀⟩) ⊕ P_han` with `χ̄(t) = −1` excluded, and the core intersection is the
**rank-1** module spanned by `w̄ = σ̄ − c·x̄₀` for any exponent `c` with `X^c = S` — such a
`c` is necessarily a **unit** because `v₂(S−1) = v₂(X−1) = 2` exactly
(`OrientationRoot.lean`'s `Sval_sub_one_eq`/`rootX_sub_one_eq`).  Consequences:

* the clearing moves for handle `j` are Eichler unipotents pairing `⟨w̄⟩` with
  `⟨ū_j, v̄_j⟩` — χ-admissible because `χ̄(w̄) = 1` (`chiSq_sqMixPivotElem`), where the
  collector's `σ̄`-moves are χ-obstructed (`chiSq_sigma_ne_one`);
* the pivot functional is `ν'(w̄) = ν'(σ̄) − c·ν'(x̄₀)`, and at the standard marking
  `ν_sq(w̄) = 1` **exactly** (`nuSq_sqMixPivotElem` — the `L_sq` unit row, the analogue of
  the M-side `ν'(C̄₀)` data check);
* the mod-2 class of `w̄` is `σ̄ + x̄₀` (both coefficients odd), which is isotropic for the
  `L_sq` cup Gram (`⟨σ,x₀⟩`-hyperbolic ⊥ `⟨x₁⟩`-diagonal), so the Eichler moves exist at the
  symplectic level — the frame-level analysis closes.

### What stays open, and where it lives

1. **The exponent datum.**  `S = X^c` holds for some `c ∈ ℤ₂ˣ` because `S` lies in the
   procyclic `1 + 4ℤ₂` topologically generated by `X` (both depth exactly 2); the
   `zpowZtwo`-surjectivity of powering on `1 + 4ℤ₂` is not in the repository, so the datum
   is carried by the record `SqMixPivot` and its production is an **SQ4 supply obligation**.
   The congruence pin `S ≡ X³ (16)` (`sval_congr_rootX_cubed`) is the landed evidence:
   any solution has `c ≡ 3 (4)`, a unit.
2. **The word-level realization.**  `HandleMixLift`'s construction (HM §6.1) twists along
   curves built from a *literal* core commutator `[y,z]` disjoint-lettered from the prefix;
   the `L_sq` core `(x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]` has **no** such factor on the `⟨σ̄,x̄₀⟩`-plane
   (its commutator letters are shared — errata item 1's note), so the handle stratum of the
   `L_sq` family does **not** inherit `mLiftSplit_handle`'s proof and needs a change of
   variables first.  It is therefore bound as `SqHandleMixHypothesis` — a `def`, never an
   axiom — stated in the corrected (pivot-`w`) form that this section identifies; SQ4/WL-b
   consume it and the change-of-variables ticket discharges it. -/

section SqRedo

open SqCore Roe

/-- **The `L_sq` mixing-pivot datum** (SQ1-R1): an exponent `c` with `X^c = S` in `ℤ₂ˣ`.
Existence is the procyclic statement `S ∈ ⟨X⟩-closure ⊆ 1 + 4ℤ₂` — an SQ4 supply obligation
(see the §6 preamble); the unit-ness of any solution is forced by the depth computation and
is carried as a field so consumers need not re-derive it. -/
structure SqMixPivot : Prop where
  /-- Some unit exponent `c` realizes `S = X^c`. -/
  exists_exponent : ∃ c : ℤ_[2], IsUnit c ∧
    zpowZtwo isProP_two_unitsPadicInt rootXUnit c = SvalUnit

/-- **The corrected clearing pivot** of the `L_sq` frame at exponent `c`: the word
`w = σ · x₀^{−c}` whose frame class spans the χ-trivial core direction. -/
noncomputable def sqMixPivotElem (h : ℕ) (c : ℤ_[2]) : (DSq h : Type) :=
  dsqSigma h * (zpowZtwo (isProP_DSq h) (dsqX0 h) c)⁻¹

/-- **The old pivot is χ-obstructed** — the SQ1-R1 refutation pin, in Lean: `χ_sq(σ) = S ≠ 1`
(`S ≡ 13 (16)`), so no clearing move built on the `σ̄`-pivot is χ-preserving for `L_sq`.
This is the Lean form of "S2.4 §1.1's `χ(σ) = 1` for type `L` is FALSE for `L_sq`". -/
theorem chiSq_sigma_ne_one (h : ℕ) : chiSq h (dsqSigma h) ≠ 1 := by
  rw [chiSq_sigma]
  intro hS
  have hval : (SvalUnit : ℤ_[2]) = 1 := by rw [hS, Units.val_one]
  have h13 : PadicInt.toZModPow 4 Sval = 13 := Sval_toZModPow_four
  rw [show (SvalUnit : ℤ_[2]) = Sval from rfl] at hval
  rw [hval, map_one] at h13
  exact absurd h13 (by decide)

/-- **The corrected pivot is χ-trivial**: `χ_sq(w) = S · X^{−c} = 1` at any exponent datum
(the unit-ness of `c` is not consumed here — χ-triviality is what the relation alone buys).
This is the row that licenses the Eichler clearing moves in the `L_sq` frame. -/
theorem chiSq_sqMixPivotElem (h : ℕ) {c : ℤ_[2]}
    (hrel : zpowZtwo isProP_two_unitsPadicInt rootXUnit c = SvalUnit) :
    chiSq h (sqMixPivotElem h c) = 1 := by
  rw [sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) isProP_two_unitsPadicInt (chiSq h) (dsqX0 h) c,
    chiSq_x0, chiSq_sigma, hrel, mul_inv_cancel]

/-- **The `L_sq` unit row** (the analogue of HM6g's M-side `ν'(C̄₀)` data check): the
standard marking evaluates the corrected pivot to `1` **exactly** —
`ν_sq(w) = ν_sq(σ) − c·ν_sq(x₀) = 1 − c·0 = 1`. -/
theorem nuSq_sqMixPivotElem (h : ℕ) (c : ℤ_[2]) :
    nuSq h (sqMixPivotElem h c) = ofAdd (1 : ℤ_[2]) := by
  rw [sqMixPivotElem, map_mul, map_inv,
    map_zpowZtwo (isProP_DSq h) PropOneOne.isProP_two_multPadicInt (nuSq h) (dsqX0 h) c,
    nuSq_sigma, nuSq_x0]
  refine Multiplicative.toAdd.injective ?_
  rw [toAdd_mul, toAdd_inv]
  have hz : zpowZtwo PropOneOne.isProP_two_multPadicInt (ofAdd (0 : ℤ_[2])) c
      = ofAdd (0 : ℤ_[2]) := by
    refine Multiplicative.toAdd.injective ?_
    rw [show (ofAdd (0 : ℤ_[2])) = (1 : Multiplicative ℤ_[2]) from rfl]
    simp
  rw [hz]
  simp

/-- The corrected pivot's `ν`-value is a unit — the form the clearing recipe consumes. -/
theorem isUnit_nuSq_sqMixPivotElem (h : ℕ) (c : ℤ_[2]) :
    IsUnit (toAdd (nuSq h (sqMixPivotElem h c))) := by
  rw [nuSq_sqMixPivotElem, toAdd_ofAdd]
  exact isUnit_one

/-- **The `c ≡ 3 (4)` evidence pin**: `S ≡ X³ (mod 16)` — the mod-16 shadow of the exponent
datum (`X ≡ 5`, `5³ = 125 ≡ 13 ≡ S`), pinning the SQ4 obligation's answer at the first
nontrivial level of the depth filtration. -/
theorem sval_congr_rootX_cubed :
    PadicInt.toZModPow 4 Sval = PadicInt.toZModPow 4 (rootX ^ 3) := by
  rw [Sval_toZModPow_four, map_pow, rootX_toZModPow_four]
  decide

/-- **The `L_sq` handle-mixing binder** (a `def`, never an axiom), in the **corrected**
pivot-`w` form this section identifies: for every marking `ν'` whose value at the corrected
pivot is a unit, a χ-preserving continuous automorphism of `DSq h` clears the handle plane
and fixes the pivot row.  This is the statement `SQ4`'s certificate consumes and the
change-of-variables follow-up (errata item 1) discharges; it deliberately does *not* quantify
through `HandleMixLift`'s `A(P,h)` monoid, whose generators do not exist for the `L_sq`
word without the change of variables. -/
def SqHandleMixHypothesis (h : ℕ) (c : ℤ_[2]) : Prop :=
  ∀ nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]),
    IsUnit (toAdd (nu' (sqMixPivotElem h c))) →
      ∃ Ψ : ContinuousMulEquiv (DSq h : Type) (DSq h : Type),
        (∀ x, chiSq h (Ψ x) = chiSq h x)
          ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxU j))) = 1)
          ∧ (∀ j : Fin h, nu' (Ψ (sqGen h (sqHandleIdxV j))) = 1)
          ∧ nu' (Ψ (sqMixPivotElem h c)) = nu' (sqMixPivotElem h c)

/-- At `h = 0` the `L_sq` binder is a theorem — there is nothing to clear, so the identity
works.  The non-vacuity floor of the corrected statement. -/
theorem sqHandleMixHypothesis_zero (c : ℤ_[2]) : SqHandleMixHypothesis 0 c := by
  intro nu' _
  exact ⟨ContinuousMulEquiv.refl _, fun _ => rfl, fun j => absurd j.2 (by omega),
    fun j => absurd j.2 (by omega), rfl⟩

/-- The standard marking meets the corrected binder's hypothesis at every `(h, c)` — the
`L_sq` mirror of `mHandleMixLift_nuM`'s non-vacuity: the binder is never vacuously
quantified. -/
theorem sqHandleMix_hypothesis_nonvacuous (h : ℕ) (c : ℤ_[2]) :
    IsUnit (toAdd (nuSq h (sqMixPivotElem h c))) :=
  isUnit_nuSq_sqMixPivotElem h c

end SqRedo

/-! ## §7 Stress pins

`(α, h) = (2, 0)` and `(2, 1)` per the lane idiom.  Every pin instantiates a §1–§6 statement
at concrete numerals so a later reshaping cannot silently become vacuous. -/

section StressTests

open SqCore

/-- The `N`-side reduction at `(2, 1)`, written out: one binder, one marked-data clause. -/
example (hScal : NScalingHypothesis 2 1)
    (nu' : ContinuousMonoidHom (DN 2 1 : Type) (Multiplicative ℤ_[2]))
    (hpair : IsUnit (toAdd (nu' (dnSigma 2 1))) ∨ IsUnit (toAdd (nu' (dnX2 2 1)))) :
    ∃ u : ContinuousMulEquiv (DN 2 1 : Type) (DN 2 1 : Type),
      (∀ x, chiN 2 1 (u x) = chiN 2 1 x) ∧ ∀ x, nu' (u x) = nuN 2 1 x :=
  nMarkedMatching 2 1 hScal nu' hpair

/-- The `N`-side reduction is inhabited by the standard marking (pivot already a unit). -/
example (hScal : NScalingHypothesis 2 1) :
    ∃ u : ContinuousMulEquiv (DN 2 1 : Type) (DN 2 1 : Type),
      (∀ x, chiN 2 1 (u x) = chiN 2 1 x) ∧ ∀ x, nuN 2 1 (u x) = nuN 2 1 x :=
  nMarkedMatching 2 1 hScal (nuN 2 1) (Or.inl (isUnit_nuN_dnSigma 2 1))

/-- The `M`-side pivot row at `(2, 1)` — HM6g's data check at the standard marking. -/
example (hMix : MMixHypothesis 2 1 one_le_two) :
    ∃ u : ContinuousMulEquiv (DM 2 1 : Type) (DM 2 1 : Type),
      (∀ x, chiM 2 1 (u x) = chiM 2 1 x)
        ∧ ∀ x, nuM 2 1 one_le_two (u x) = nuM 2 1 one_le_two x :=
  mMarkedMatching_nuM one_le_two hMix

/-- The masters cover every derivation tuple at `(2, 1)` — the 4-frame `masterRel` pin. -/
example (c : Fin (coreRank 1) → ℤ_[2]) : mRelWord 2 (mMasterMark 2 c) = 1 :=
  mRelWord_mMasterMark one_le_two c

example (c : Fin (coreRank 1) → ℤ_[2]) : nRelWord 2 (nMasterMark 2 c) = 1 :=
  nRelWord_nMasterMark one_le_two c

/-- The plane solve moves an `x̄₂`-unit into the pivot at `(2, 0)`. -/
example (nu' : ContinuousMonoidHom (DN 2 0 : Type) (Multiplicative ℤ_[2]))
    (hx2 : IsUnit (toAdd (nu' (dnX2 2 0)))) :
    ∃ Ψ : ContinuousMulEquiv (DN 2 0 : Type) (DN 2 0 : Type),
      (∀ x, chiN 2 0 (Ψ x) = chiN 2 0 x) ∧ IsUnit (toAdd (nu' (Ψ (dnSigma 2 0)))) :=
  nPivot_normalize 2 0 nu' (Or.inr hx2)

/-- The `L_sq` unit row at one handle: the corrected pivot evaluates to exactly `1`. -/
example (c : ℤ_[2]) : nuSq 1 (sqMixPivotElem 1 c) = ofAdd (1 : ℤ_[2]) :=
  nuSq_sqMixPivotElem 1 c

/-- The SQ1-R1 refutation at one handle: the collector's pivot premise fails for `L_sq`. -/
example : chiSq 1 (dsqSigma 1) ≠ 1 := chiSq_sigma_ne_one 1

/-- **HM6g's family-shaped `M5` row, consumed as-is** (no restatement of `MMixHypothesis` —
the family-form owner call stays pending): the displayed pure `M5` move at `b = 1`,
χ-preserving, at `(2, 1)`. -/
example : ∃ Ψ : ContinuousMulEquiv (DM 2 1 : Type) (DM 2 1 : Type),
    (∀ x, chiM 2 1 (Ψ x) = chiM 2 1 x)
      ∧ ∀ f : ContinuousMonoidHom (DM 2 1 : Type) (Multiplicative ℤ_[2]),
        nuFrame f (fun i => Ψ (dmGen 2 1 i)) = nFrameMixX1 1 (nuFrame f (dmGen 2 1)) :=
  mMixFamily_coreMix 2 1 le_rfl 1

/-- **MC4's parametrized lift with S3 discharged**, consumed through the MC-VAR-correct
`NStabParam.nuAction` (its `nCoreMat P.g.transpose` is right as written — the H¹ layout):
the identity parameter tuple at `(2, 1)`, conditional on the plane-scaling binder alone. -/
example (hScal : NPlaneScalingHypothesis 2 1) :
    ∃ Ψ : ContinuousMulEquiv (DN 2 1 : Type) (DN 2 1 : Type),
      (∀ x, chiN 2 1 (Ψ x) = chiN 2 1 x)
        ∧ ∀ f : ContinuousMonoidHom (DN 2 1 : Type) (Multiplicative ℤ_[2]),
          nuFrame f (fun i => Ψ (dnGen 2 1 i))
            = NStabParam.nuAction ⟨0, 0, 0, 0, 0, 1⟩ (nuFrame f (dnGen 2 1)) :=
  nStabParam_lift_of_scaling 2 1 hScal
    ⟨by rw [Matrix.det_one]; exact isUnit_one, by simp, by simp⟩

end StressTests

end MarkedCore

end Dyadic

end GQ2
