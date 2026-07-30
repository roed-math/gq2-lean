/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Reciprocity
public import GQ2.Dyadic.Branches

@[expose] public section

/-!
# Dyadic campaign, layer AX3: marked local reciprocity over a finite dyadic `K`

The **statement** file for the AX3 interface `MarkedRecip` (`docs/dyadic/ax3-proposal.md`, the
memo this file implements clause for clause): the reciprocity map `rec_K` and the full
`ℤ₂`-valued geometric unramified coordinate `ν_ur^K` for a finite extension `K/ℚ₂` inside `ℚ̄₂`,
together with the marked cyclotomic quotient datum `(C, I, λ, γ)` of the draft's eqs. 2.1–2.3.

**This file is deliberately axiom-free.**  The axiom `GQ2.markedRecipAt` — memo §2.3 — lands
separately, in `GQ2/Foundations/Axioms.lean`, in the orchestrator's census-flip commit (memo §6,
checklist item 3).  Everything below is either a definition or a theorem over an *arbitrary*
`MarkedRecip R K`, exactly the B5 discipline of `GQ2/Reciprocity.lean` (`#print axioms` on any
declaration here is the standard three).  Consumers bind the structure, so they keep compiling
unchanged across the flip.

## Layout

* **§1 K-side vocabulary** — `GalK`, `GalKab`, `chiCycK`/`chiCycKAb`, `inclAbK`, `normUnitsK`,
  and the compatibility `chiCycKAb = chiCycAb ∘ inclAbK` (memo §1.1: `χ_K` is the *literal
  restriction* of Mathlib's cyclotomic character, so this layer adds no content).
* **§2 the abstract marked pair** — `MarkedPair`, carrying only `(χ, ν, r)` and the two
  `ν(ker χ) = 2^r ℤ₂` clauses; the whole `(C, I, λ, γ)` derivation of memo §1.5 lives here, so
  it can be exercised by a synthetic pair (§6) as well as by a bundle.
* **§3 the bundle** — `MarkedRecip` (memo §2.2, twelve fields) and its derived layer (memo §2.4):
  `surjective_nu_ur`, `toMarkedPair`, the `(r, ε, η)` extraction API, and the `K(i)` field
  bridge in both directions of use (memo §1.6, owner answer Q4).
* **§4 the `ℚ₂` compatibility regression** — memo §3, at `K = ⊥`: `norm_compat` *is* B5's
  reciprocity clause there, and the marked level is forced to `r = 0` (type `L`).
* **§5 the five quadratic test vectors** — memo §5, as hypothesis-shaped lemmas.
* **§6 the synthetic `r = 2` marked pair** — memo §7 R2, the mandated λ-sign regression, and the
  non-vacuity witness (memo §7 R8) for §2's clause set.
* **§7 the norm-matching adapter** — `HasEqualNormValueGroups` in the tower shape that
  `GQ2/Dyadic/LocalGauss/VanishCloseK.lean`'s `InvolutionFieldPackage` consumes.

## Conventions (inherited verbatim from B5; the #1 human-review target)

`rec` is **arithmetic** and `ν_ur` is **geometric** (`ν(rec π) = −1` for a uniformizer `π`), and
`ν_ur`'s target is the *profinite* `Multiplicative ℤ₂` — never `ℤ`, which would make the clause
set inconsistent (`GQ2/Reciprocity.lean`'s soundness note; memo §7 R5).  A uniformizer is spelled
spectrally, "maximal norm `< 1`" (the B13 idiom), and a unit by `‖u‖ = 1` (the B11b idiom); no
valuation `v_K` exists in the repository.  Unramifiedness of `K(i)/K` is spelled by the isolated
convention `def HasEqualNormValueGroups` (moved here from `GQ2/Foundations/Interfaces.lean`; see
its docstring), which asserts nothing.

## Sources

Packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex` §8 (Prop. 8.1, Cor. 8.2),
§12 (the `MarkedRecip` row), §7 (Prop. 7.2), §3 (Prop. 3.4, Thm. 3.5); draft
`docs/dyadic/refs/dyadic-presentations.tex` §2 (eqs. 2.1–2.3 and the Warning), §7, §10.2.
Classical inputs behind the *axiom* (not behind anything in this file): NSW (7.1.1)/(7.1.5) at
base `K`; Serre, *Local Fields*, Ch. XI §3 (norm functoriality) and Ch. XIII §4 Prop. 13
(units/uniformizers); NSW Ch. I §5 and Ch. VII §7.1 (class-formation functoriality).  Those
citations are owner-approved as *sources*; the exact display numbers have **not** been verified
against the PDFs, so the house "verified against the cited PDFs" line is deliberately absent
here and in the axiom docstring (memo §8 Q7).

## Module-system note

`module`-style, and its import closure is `GQ2.Reciprocity` (B5's statement vocabulary) plus
`GQ2.Dyadic.Branches` (F4's data-level marked datum, itself only Mathlib + `GQ2.Dyadic.Parameters`
+ `GQ2.Words`).  Neither reaches `GQ2/Foundations/Axioms.lean`, so `Axioms.lean` can `public
import` this file at the flip without a cycle, and the §8/§9 proof stack is untouched (plan §3
A5, memo §7 R9).
-/

open scoped Classical

namespace GQ2

/-- **Equal norm value groups for `k(δa)/k` — the project's unramifiedness criterion.**  Every
nonzero `z = x + y·δa` (`x, y ∈ k`) has the same norm as some nonzero element of the base `k`,
i.e. `k(δa)` and `k` have equal norm value groups.  For a quadratic extension of complete
discretely valued fields this says `e(k(δa)/k) = 1`, the standard unramifiedness criterion
(Serre, *Local Fields*, Ch. I §4); the definition is named by what it literally asserts because
the equivalence with a bona-fide ramification-theoretic notion is *not* proved here (no Mathlib
ramification theory applies at these types yet — `IsNonarchimedeanLocalField` has no
extension/ramification layer as of 2026-07-24).  This is **not** a Mathlib unramifiedness notion
and is asserted by nothing (it is a `def`, not an axiom); it is the convention the §6 ledger
consumes, named and isolated per adversarial review rec 2 so a human reviewer can see exactly
where the project departs from a directly citable statement.  Named
`IsUnramifiedQuadraticSpectral` before 2026-07-24 (deprecated alias in
`GQ2/Foundations/Interfaces.lean`, next to the negative stress test
`not_hasEqualNormValueGroups_sqrt_two` and the B11b consumer, which are unchanged).

*Located here, rather than with those consumers, since 2026-07-29* (AX3 ticket, memo §7 R7 /
owner answer Q3): the `ki_unramified` clause of `MarkedRecip` below needs the convention, and
`GQ2/Foundations/Interfaces.lean` sits *above* `GQ2/Foundations/Axioms.lean`, which must import
this file at the AX3 census flip.  Moving the `def` breaks that cycle; the name, statement and
namespace are unchanged, so every call site is byte-identical. -/
def HasEqualNormValueGroups
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    (δa : AlgebraicClosure ℚ_[2]) : Prop :=
  ∀ z : AlgebraicClosure ℚ_[2], z ≠ 0 →
    (∃ x y : ↥k, z = (x : AlgebraicClosure ℚ_[2]) + (y : AlgebraicClosure ℚ_[2]) * δa) →
    ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : AlgebraicClosure ℚ_[2])‖

end GQ2

namespace GQ2.Dyadic

noncomputable section

/-! ## §1 The `K`-side vocabulary

Memo §1.1: on the `ℚ₂` side the cyclotomic character is `GQ2.chiCyc` (Mathlib's
`cyclotomicCharacter … 2`), and `χ_K` is its literal restriction to `G_K`, because `μ_{2^∞}` and
its Galois action do not depend on the subgroup.  So this whole section is plumbing: it adds no
mathematical content, and every declaration is a restriction or a `QuotientGroup.lift` of a B5
object.

Memo §7 R6 (the instance-path trap): `K.fixingSubgroup` elaborates by default into
`Subgroup Gal(ℚ̄₂/ℚ₂)`, whose `Group` instance is `AlgEquiv.aut`, while `chiCyc`/`commClosure`
live on `AbsGalQ2 = Field.absoluteGaloisGroup ℚ₂`.  The two types are definitionally equal with
*different registered instances*, so the ambient is pinned **once**, in `GalKsub`, and every
declaration below goes through it — the `restrictHom` precedent of `GQ2/Reciprocity.lean`. -/

section Vocabulary

variable (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))

/-- `G_K = Gal(ℚ̄₂/K)` as a subgroup of `AbsGalQ2`.  The type ascription is the R6 instance pin:
it forces the `Field.absoluteGaloisGroup` instance path, the one `chiCyc` and `commClosure` use. -/
abbrev GalKsub : Subgroup AbsGalQ2 := K.fixingSubgroup

/-- `G_K = Gal(ℚ̄₂/K)`, the repo's `K`-side vocabulary (B6/B9/B11a). -/
abbrev GalK : Type := ↥(GalKsub K)

/-- The closed commutator subgroup of `G_K` — the subgroup Mathlib's `TopologicalAbelianization`
quotients by, so `GalKab K` below *is* Mathlib's topological abelianization of `G_K`
(the `commClosure` device of `GQ2/Reciprocity.lean`, verbatim at `K`). -/
abbrev commClosureK : Subgroup (GalK K) := (commutator (GalK K)).topologicalClosure

/-- `G_K^{ab}`, the topological abelianization of `G_K`.  This is Mathlib's
`TopologicalAbelianization`, not a rival construction — the same `abbrev` that unfolds
`AbsGalQ2ab`. -/
abbrev GalKab : Type := TopologicalAbelianization (GalK K)

/-- The abelianization projection `G_K ↠ G_K^{ab}`. -/
def toAbK : GalK K →* GalKab K := QuotientGroup.mk' (commClosureK K)

lemma continuous_toAbK : Continuous (toAbK K) := continuous_quotient_mk'

lemma surjective_toAbK : Function.Surjective (toAbK K) :=
  QuotientGroup.mk'_surjective _

/-- The 2-adic cyclotomic character restricted to `G_K` (memo §1.1). -/
def chiCycK : GalK K →* ℤ_[2]ˣ := chiCyc.comp (GalKsub K).subtype

@[simp] lemma chiCycK_apply (g : GalK K) : chiCycK K g = chiCyc (g : AbsGalQ2) := rfl

lemma continuous_chiCycK : Continuous (chiCycK K) :=
  continuous_chiCyc.comp continuous_subtype_val

/-- `χ_K` kills the closed commutator subgroup (its target `ℤ₂ˣ` is Hausdorff abelian), verbatim
the `commClosure_le_ker_chiCyc` argument at `K`. -/
lemma commClosureK_le_ker_chiCycK : commClosureK K ≤ (chiCycK K).ker := by
  apply Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker (chiCycK K))
  rw [MonoidHom.coe_ker]
  exact isClosed_singleton.preimage (continuous_chiCycK K)

/-- The cyclotomic character as a map out of `G_K^{ab}`. -/
def chiCycKAb : GalKab K →* ℤ_[2]ˣ :=
  QuotientGroup.lift (commClosureK K) (chiCycK K)
    (fun _ hx => MonoidHom.mem_ker.mp (commClosureK_le_ker_chiCycK K hx))

/-- **Stress test (`chiCycKAb`):** it factors `χ_K` through the abelianization. -/
@[simp] lemma chiCycKAb_toAbK (g : GalK K) : chiCycKAb K (toAbK K g) = chiCycK K g := rfl

/-- The inclusion `G_K ↪ G_{ℚ₂}` followed by abelianization, `G_K →* G_{ℚ₂}^{ab}`. -/
def inclHomK : GalK K →* AbsGalQ2ab := toAb.comp (GalKsub K).subtype

@[simp] lemma inclHomK_apply (g : GalK K) : inclHomK K g = toAb (g : AbsGalQ2) := rfl

lemma continuous_inclHomK : Continuous (inclHomK K) :=
  continuous_quotient_mk'.comp continuous_subtype_val

/-- `G_K → G_{ℚ₂}^{ab}` kills the closed commutator subgroup of `G_K`: its kernel is the
*preimage* of the closed subgroup `commClosure`, hence closed. -/
lemma commClosureK_le_ker_inclHomK : commClosureK K ≤ (inclHomK K).ker := by
  apply Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker (inclHomK K))
  have hset : ((inclHomK K).ker : Set (GalK K))
      = Subtype.val ⁻¹' ((commClosure : Subgroup AbsGalQ2) : Set AbsGalQ2) := by
    ext g
    simp only [Set.mem_preimage, SetLike.mem_coe, MonoidHom.mem_ker, inclHomK_apply, toAb,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  rw [hset]
  exact (Subgroup.isClosed_topologicalClosure _).preimage continuous_subtype_val

/-- The abelianized inclusion `G_K^{ab} →* G_{ℚ₂}^{ab}`, the map `rec_K` is pinned against in
the bundle's norm-functoriality clause. -/
def inclAbK : GalKab K →* AbsGalQ2ab :=
  QuotientGroup.lift (commClosureK K) (inclHomK K)
    (fun _ hx => MonoidHom.mem_ker.mp (commClosureK_le_ker_inclHomK K hx))

@[simp] lemma inclAbK_toAbK (g : GalK K) : inclAbK K (toAbK K g) = toAb (g : AbsGalQ2) := rfl

lemma continuous_inclAbK : Continuous (inclAbK K) :=
  continuous_quot_lift _ (continuous_inclHomK K)

/-- **The `χ_K` compatibility (memo §1.1, and what makes the §4 regression run):** the `K`-side
cyclotomic character on `G_K^{ab}` is the `ℚ₂`-side one composed with the abelianized inclusion.
Both sides are, by construction, `chiCyc` on a lift. -/
theorem chiCycKAb_eq_comp : chiCycKAb K = chiCycAb.comp (inclAbK K) := by
  refine MonoidHom.ext fun g => ?_
  obtain ⟨h, rfl⟩ := surjective_toAbK K g
  rfl

@[simp] theorem chiCycAb_inclAbK (g : GalKab K) : chiCycAb (inclAbK K g) = chiCycKAb K g :=
  (congrArg (fun f => f g) (chiCycKAb_eq_comp K)).symm

/-- The norm on units, `(↥K)ˣ →* ℚ₂ˣ` (the map whose image is `GQ2.normSubgroup K`). -/
def normUnitsK [FiniteDimensional ℚ_[2] K] : (↥K)ˣ →* ℚ_[2]ˣ :=
  Units.map (Algebra.norm ℚ_[2] (S := K))

@[simp] lemma normUnitsK_val [FiniteDimensional ℚ_[2] K] (x : (↥K)ˣ) :
    ((normUnitsK K x : ℚ_[2]ˣ) : ℚ_[2]) = Algebra.norm ℚ_[2] ((x : ↥K)) := rfl

end Vocabulary

end

end GQ2.Dyadic
