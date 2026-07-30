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

/-! ## §2 The abstract marked pair, and the `(C, I, λ, γ)` derivation

Memo §1.5: the only genuinely new finiteness fact in the marked block is the draft's eq. 2.1
`A = ν(ker χ) = 2^r ℤ₂`; *everything* else — `λ` well-defined, `I = ker λ`, surjectivity of `λ`,
the Frobenius coset `γ` with `λ(γ) = 1` — is formal.  This section isolates that formal content
on an abstract commutative group carrying only `(χ, ν, r)` and the two `2^r ℤ₂` clauses, for three
reasons:

* the bundle's own derived layer (§3) is then two lines per item;
* the synthetic level-`2` regression of memo §7 R2 (§6 below) can exercise the *same* code — a
  `MarkedRecip` cannot be hand-built (its `recip` is a genuine local-CFT object), but a marked
  pair with prescribed `(χ, ν)` can, which is exactly what R2 asks for;
* the clause set gets a non-vacuity witness (memo §7 R8): `mockMarkedPair` constructs one
  outright, so the two `nu_ker_chi_*` clauses cannot be silently unsatisfiable.

`ν` surjectivity is a *field* here rather than a derivation: over a bundle it comes from the
uniformizer clause (`MarkedRecip.surjective_nu_ur`), which an abstract pair has no access to.
Memo §1.5's derivation of `λ`-surjectivity from `ν`-surjectivity is `surjective_lambda` below. -/

section MarkedPairSection

/-- **The abstract marked pair** `(χ, ν, r)` of draft eq. 2.1: a cyclotomic coordinate
`χ : A →* ℤ₂ˣ`, a surjective unramified coordinate `ν : A ↠ ℤ₂` (written multiplicatively — the
profinite target of memo §7 R5), and the marked level `r` with `ν(ker χ) = 2^r ℤ₂` stated as its
two inclusions.

This is the *derived-layer* interface, **not** the axiom's: it carries no reciprocity map and no
field, so it is satisfiable by hand (§6) and adds no strength.  `MarkedRecip.toMarkedPair`
produces the arithmetic one. -/
structure MarkedPair (A : Type*) [CommGroup A] where
  /-- The cyclotomic coordinate `χ : A →* ℤ₂ˣ` (over a bundle: `chiCycKAb K`). -/
  chi : A →* ℤ_[2]ˣ
  /-- The unramified coordinate `ν : A →* Multiplicative ℤ₂` (over a bundle: `nu_ur`). -/
  nu : A →* Multiplicative ℤ_[2]
  /-- `ν` is surjective (over a bundle: derived from the uniformizer clause). -/
  surjective_nu : Function.Surjective nu
  /-- The marked level `r`: `ν(ker χ) = 2^r ℤ₂` (draft eq. 2.1's `A`). -/
  r : ℕ
  /-- `ν(ker χ) ⊆ 2^r ℤ₂` — the direction that makes `λ` well defined. -/
  nu_ker_chi_le : ∀ g : A, chi g = 1 → ∃ y : ℤ_[2], (nu g).toAdd = 2 ^ r * y
  /-- `ν(ker χ) ⊇ 2^r ℤ₂` — exactness of the level, the direction that gives `I = ker λ`. -/
  nu_ker_chi_ge : ∀ y : ℤ_[2], ∃ g : A, chi g = 1 ∧ (nu g).toAdd = 2 ^ r * y

namespace MarkedPair

variable {A : Type*} [CommGroup A] (P : MarkedPair A)

/-! ### The `2^r ℤ₂` ideal, in `toZModPow` form

Both `nu_ker_chi_*` clauses are stated with an explicit factorization `2^r · y`; the `λ`
machinery wants the equivalent `PadicInt.toZModPow r` form.  These two lemmas are the (unique)
translation, and they are where `ZMod (2 ^ r)` meets `ℤ₂`. -/

/-- `2^n · y` dies mod `2^n`. -/
theorem toZModPow_two_pow_mul (n : ℕ) (y : ℤ_[2]) :
    PadicInt.toZModPow n ((2 : ℤ_[2]) ^ n * y) = 0 := by
  rw [map_mul, map_pow, map_ofNat]
  have h : ((2 : ZMod (2 ^ n))) ^ n = 0 := by
    rw [show ((2 : ZMod (2 ^ n))) = ((2 : ℕ) : ZMod (2 ^ n)) by push_cast; ring, ← Nat.cast_pow,
      ZMod.natCast_self]
  rw [h, zero_mul]

/-- Conversely, an element killed mod `2^n` is `2^n` times something. -/
theorem exists_eq_two_pow_mul {n : ℕ} {z : ℤ_[2]} (hz : PadicInt.toZModPow n z = 0) :
    ∃ y : ℤ_[2], z = 2 ^ n * y := by
  have hmem : z ∈ Ideal.span {((2 : ℕ) : ℤ_[2]) ^ n} := by
    rw [← PadicInt.ker_toZModPow n]
    exact hz
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.1 hmem
  exact ⟨y, by rw [← hy, mul_comm]; norm_num⟩

/-- Every 2-adic integer is an ordinary integer modulo `2^n`.  (Used for `ν`-surjectivity over a
bundle and for `λ`-surjectivity here.) -/
theorem exists_intCast_congr (n : ℕ) (z : ℤ_[2]) :
    ∃ (m : ℤ) (y : ℤ_[2]), z - (m : ℤ_[2]) = 2 ^ n * y := by
  refine ⟨((PadicInt.toZModPow n z).cast : ℤ), ?_⟩
  refine exists_eq_two_pow_mul ?_
  rw [map_sub, map_intCast, ZMod.intCast_zmod_cast, sub_self]

/-! ### `C`, `λ` and the quotient `C/I ≅ ℤ/2^r` -/

/-- The cyclotomic image `C = χ(A)` of draft eq. 2.1.  Over a bundle this is
`(chiCycKAb K).range` — the instantiation F4's `unramified_of_even` docstring names. -/
abbrev C : Subgroup ℤ_[2]ˣ := P.chi.range

/-- `ν` reduced mod `2^r`, as a hom on all of `A`.  `λ` is its descent along `χ`. -/
def nuMod : A →* Multiplicative (ZMod (2 ^ P.r)) :=
  (AddMonoidHom.toMultiplicative (PadicInt.toZModPow P.r).toAddMonoidHom).comp P.nu

@[simp] theorem toAdd_nuMod (g : A) :
    (P.nuMod g).toAdd = PadicInt.toZModPow P.r (P.nu g).toAdd := rfl

theorem surjective_nuMod : Function.Surjective P.nuMod := fun z => by
  obtain ⟨g, hg⟩ := P.surjective_nu (Multiplicative.ofAdd (((z.toAdd.cast : ℤ) : ℤ_[2])))
  refine ⟨g, Multiplicative.toAdd.injective ?_⟩
  rw [toAdd_nuMod, hg]
  show PadicInt.toZModPow P.r (((z.toAdd.cast : ℤ) : ℤ_[2])) = z.toAdd
  rw [map_intCast, ZMod.intCast_zmod_cast]

/-- **`λ` is well defined** (memo §1.5, first bullet): `χ g = χ g'` forces
`ν g ≡ ν g' (mod 2^r)`, i.e. `ker χ ≤ ker (ν mod 2^r)`. -/
theorem ker_chi_le_ker_nuMod : P.chi.ker ≤ P.nuMod.ker := by
  intro g hg
  obtain ⟨y, hy⟩ := P.nu_ker_chi_le g (MonoidHom.mem_ker.1 hg)
  refine MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_)
  rw [toAdd_nuMod, hy, toZModPow_two_pow_mul]
  rfl

/-- `A/ker χ ≅ C`, the first isomorphism theorem for `χ`. -/
def quotEquivC : A ⧸ P.chi.ker ≃* ↥P.C := QuotientGroup.quotientKerEquivRange P.chi

@[simp] theorem quotEquivC_mk (g : A) :
    P.quotEquivC (QuotientGroup.mk g) = ⟨P.chi g, ⟨g, rfl⟩⟩ := rfl

/-- `ν mod 2^r` descended to `A/ker χ` — the intermediate step in the construction of `λ`, and
the place `ker_chi_le_ker_nuMod` (well-definedness) is spent. -/
def lambdaQuot : A ⧸ P.chi.ker →* Multiplicative (ZMod (2 ^ P.r)) :=
  QuotientGroup.lift P.chi.ker P.nuMod fun _ hg =>
    MonoidHom.mem_ker.1 (P.ker_chi_le_ker_nuMod hg)

@[simp] theorem lambdaQuot_mk (g : A) : P.lambdaQuot (QuotientGroup.mk g) = P.nuMod g := rfl

/-- **The marked quotient `λ : C ↠ ℤ/2^r`** of draft eq. 2.2, written multiplicatively as draft
§10.2 does: `λ(χ g) = ν(g) mod 2^r`.  Constructed as the descent of `ν mod 2^r` along
`A ↠ A/ker χ ≅ C`, so `map_mul` is free. -/
def lambda : ↥P.C →* Multiplicative (ZMod (2 ^ P.r)) :=
  P.lambdaQuot.comp P.quotEquivC.symm.toMonoidHom

/-- The additive spelling of `λ` (memo §7 R3: every branch equation is additive). -/
def lambdaAdd (c : ↥P.C) : ZMod (2 ^ P.r) := (P.lambda c).toAdd

/-- **The defining property of `λ`** (memo §4.2 `lambdaOf_spec`): on the `χ`-image of `g`, `λ` is
`ν g` reduced mod `2^r`.  Its `∀ g`-shape *is* the well-definedness statement. -/
theorem lambda_chi (g : A) : P.lambda ⟨P.chi g, ⟨g, rfl⟩⟩ = P.nuMod g := by
  show P.lambdaQuot (P.quotEquivC.symm ⟨P.chi g, ⟨g, rfl⟩⟩) = P.nuMod g
  rw [P.quotEquivC.symm_apply_eq.2 (P.quotEquivC_mk g).symm, lambdaQuot_mk]

theorem lambdaAdd_eq (c : ↥P.C) (g : A) (hg : P.chi g = (c : ℤ_[2]ˣ)) :
    P.lambdaAdd c = PadicInt.toZModPow P.r (P.nu g).toAdd := by
  have hc : (⟨P.chi g, ⟨g, rfl⟩⟩ : ↥P.C) = c := Subtype.ext hg
  rw [lambdaAdd, ← hc, lambda_chi, toAdd_nuMod]

@[simp] theorem lambdaAdd_mul (c c' : ↥P.C) :
    P.lambdaAdd (c * c') = P.lambdaAdd c + P.lambdaAdd c' := by
  simp [lambdaAdd]

@[simp] theorem lambdaAdd_one : P.lambdaAdd 1 = 0 := by simp [lambdaAdd]

@[simp] theorem lambdaAdd_inv (c : ↥P.C) : P.lambdaAdd c⁻¹ = -P.lambdaAdd c := by
  simp [lambdaAdd]

/-- **`λ` is surjective** (memo §1.5, third bullet), from surjectivity of `ν`. -/
theorem surjective_lambda : Function.Surjective P.lambda := fun z => by
  obtain ⟨g, hg⟩ := P.surjective_nuMod z
  exact ⟨⟨P.chi g, ⟨g, rfl⟩⟩, by rw [lambda_chi, hg]⟩

theorem surjective_lambdaAdd : Function.Surjective P.lambdaAdd := fun z => by
  obtain ⟨c, hc⟩ := P.surjective_lambda (Multiplicative.ofAdd z)
  exact ⟨c, by rw [lambdaAdd, hc]; rfl⟩

/-- **F4's abstract datum** (`GQ2/Dyadic/Branches.lean`, draft §10.2): the marked pair's
`(r, λ)` is a `CyclotomicFrobeniusDatum` on `C`.  This is the bridge memo §4.2 asks for; F4's
`inertiaImage`/`gammaCoset` then agree with `I`/`γ` by `mem_I_iff` and `mk_eq_gammaCoset_iff`
below. -/
def datum : CyclotomicFrobeniusDatum ↥P.C where
  r := P.r
  lambda := P.lambda
  lambda_surjective := P.surjective_lambda

@[simp] theorem datum_r : P.datum.r = P.r := rfl

@[simp] theorem datum_lambdaAdd (c : ↥P.C) : P.datum.lambdaAdd c = P.lambdaAdd c := rfl

/-! ### `I`, and `I = ker λ` -/

/-- The inertia image `I = χ(ker ν)` of draft eq. 2.1.  Memo §1.5's last bullet records why the
name is honest (`ker ν ⊇ inertia` with pro-odd quotient, and `χ` kills pro-odd images inside the
pro-2 group `ℤ₂ˣ`); that identification is *not* a Lean obligation and is not claimed here. -/
abbrev I : Subgroup ℤ_[2]ˣ := P.nu.ker.map P.chi

/-- **`I = ker λ`** (memo §1.5, second bullet) — the theorem that lets F4 use "`I`" and "`ker λ`"
interchangeably.  `⊆` is immediate; `⊇` is where clause `nu_ker_chi_ge` (exactness of the level)
is spent: an element of `ker λ` is `χ g` with `ν g ∈ 2^r ℤ₂ = ν(ker χ)`, and correcting `g` by the
`ker χ`-element of the same `ν`-value lands in `ker ν`. -/
theorem mem_I_iff (c : ↥P.C) : (c : ℤ_[2]ˣ) ∈ P.I ↔ P.lambdaAdd c = 0 := by
  constructor
  · rintro ⟨g, hg, hgc⟩
    rw [P.lambdaAdd_eq c g hgc, MonoidHom.mem_ker.1 hg]
    show PadicInt.toZModPow P.r (0 : ℤ_[2]) = 0
    exact map_zero _
  · intro hc
    obtain ⟨g, hg⟩ := c.2
    obtain ⟨y, hy⟩ := exists_eq_two_pow_mul (P.lambdaAdd_eq c g hg ▸ hc)
    obtain ⟨h, hh1, hh2⟩ := P.nu_ker_chi_ge y
    refine ⟨g * h⁻¹, MonoidHom.mem_ker.2 (Multiplicative.toAdd.injective ?_), ?_⟩
    · rw [map_mul, map_inv]
      show (P.nu g).toAdd + (-(P.nu h).toAdd) = (1 : Multiplicative ℤ_[2]).toAdd
      rw [hy, hh2, add_neg_cancel]
      rfl
    · rw [map_mul, map_inv, MonoidHom.mem_ker.1 hh1, inv_one, mul_one, hg]

/-- `I = ker λ` in F4's `inertiaImage` spelling. -/
theorem mem_inertiaImage_iff (c : ↥P.C) :
    c ∈ P.datum.inertiaImage ↔ (c : ℤ_[2]ˣ) ∈ P.I :=
  (P.datum.mem_inertiaImage_iff).trans (P.mem_I_iff c).symm

/-! ### `γ`, the Frobenius coset -/

/-- **A geometric Frobenius lift exists** (memo §1.5, fourth bullet): some `g` has `ν g = 1`. -/
theorem exists_frobenius : ∃ g : A, (P.nu g).toAdd = 1 := by
  obtain ⟨g, hg⟩ := P.surjective_nu (Multiplicative.ofAdd (1 : ℤ_[2]))
  exact ⟨g, by rw [hg]; rfl⟩

/-- **`γ` is well defined, with `λ(γ) = 1`** (draft eq. 2.3): the `χ`-image of any `ν`-value-`1`
element represents F4's `gammaCoset`, and two such differ by `I`.  ⚠ The `1` is the *additive*
one of `ℤ/2^r`; it is `λ(γ) = 1`, not `γ ∈ I`. -/
theorem mk_eq_gammaCoset_of_nu_eq_one {g : A} (hg : (P.nu g).toAdd = 1) :
    (QuotientGroup.mk ⟨P.chi g, ⟨g, rfl⟩⟩ : ↥P.C ⧸ P.datum.inertiaImage) = P.datum.gammaCoset := by
  refine P.datum.mk_eq_gammaCoset_iff.2 ?_
  rw [datum_lambdaAdd, P.lambdaAdd_eq _ g rfl, hg]
  exact map_one _

theorem exists_gamma_rep :
    ∃ (g : A) (hc : P.chi g ∈ P.C), (P.nu g).toAdd = 1 ∧
      (QuotientGroup.mk ⟨P.chi g, hc⟩ : ↥P.C ⧸ P.datum.inertiaImage) = P.datum.gammaCoset := by
  obtain ⟨g, hg⟩ := P.exists_frobenius
  exact ⟨g, ⟨g, rfl⟩, hg, P.mk_eq_gammaCoset_of_nu_eq_one hg⟩

/-! ### The `(r, ε, η)` extraction API (memo §4.2)

Value spelling, recorded once (memo §4.2, and the risk R2 this section's regression guards):
`λ(unit-part(N_{K/ℚ₂} x)) = + v_K(x) mod 2^r`, because `χ(rec x) = unit-part(N x)⁻¹` and
`ν(rec x) = −v_K(x)` — the two inversions cancel. -/

/-- **`λ` at a `C`-member** — memo §4.2's `lambdaOf`, the form instances call. -/
def lambdaAt (c : ℤ_[2]ˣ) (hc : c ∈ P.C) : ZMod (2 ^ P.r) := P.lambdaAdd ⟨c, hc⟩

theorem lambdaAt_spec (c : ℤ_[2]ˣ) (hc : c ∈ P.C) (g : A) (hg : P.chi g = c) :
    P.lambdaAt c hc = PadicInt.toZModPow P.r (P.nu g).toAdd :=
  P.lambdaAdd_eq ⟨c, hc⟩ g hg

theorem lambdaAt_eq_zero_iff_mem_I (c : ℤ_[2]ˣ) (hc : c ∈ P.C) :
    P.lambdaAt c hc = 0 ↔ c ∈ P.I :=
  (P.mem_I_iff ⟨c, hc⟩).symm

/-- `λ(−1)` is two-torsion, so it is `ε·2^{r−1}` for a **unique Boolean** `ε` when `r ≥ 1` — F1's
`epsVal` design decision (`ε : Bool`) as a theorem.  At `r = 0` the statement is meaningless
(`ℕ`-subtraction truncates and `ZMod 1` is trivial), which is memo §7 R4. -/
theorem exists_eps (hr : 1 ≤ P.r) (h₁ : (-1 : ℤ_[2]ˣ) ∈ P.C) :
    ∃ ε : Bool, P.lambdaAt (-1) h₁ = ((epsVal ε * 2 ^ (P.r - 1) : ℕ) : ZMod (2 ^ P.r)) := by
  haveI : NeZero (2 ^ P.r) := ⟨by positivity⟩
  have hsq : ((⟨-1, h₁⟩ : ↥P.C) * ⟨-1, h₁⟩) = 1 := by
    refine Subtype.ext ?_
    show (-1 : ℤ_[2]ˣ) * (-1 : ℤ_[2]ˣ) = 1
    simp
  have h2 : (2 : ℕ) • P.lambdaAt (-1) h₁ = 0 := by
    have h := P.lambdaAdd_mul ⟨-1, h₁⟩ ⟨-1, h₁⟩
    rw [hsq, lambdaAdd_one, ← two_nsmul] at h
    exact h.symm
  have hval : ((2 * (P.lambdaAt (-1) h₁).val : ℕ) : ZMod (2 ^ P.r)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, two_mul, ← two_nsmul]
    exact h2
  have hdvd : (2 : ℕ) ^ P.r ∣ 2 * (P.lambdaAt (-1) h₁).val :=
    (ZMod.natCast_eq_zero_iff _ _).1 hval
  rcases eq_zero_or_eq_two_pow_pred hr hdvd (ZMod.val_lt _) with h | h
  · refine ⟨false, ?_⟩
    rw [← ZMod.natCast_zmod_val (P.lambdaAt (-1) h₁), h]
    simp [epsVal]
  · refine ⟨true, ?_⟩
    rw [← ZMod.natCast_zmod_val (P.lambdaAt (-1) h₁), h]
    simp [epsVal]

/-- The sign parameter `ε ∈ Bool` of packet §8, extracted from `λ(−1) = ε·2^{r−1}` (`r ≥ 1`). -/
def epsilonOf (hr : 1 ≤ P.r) (h₁ : (-1 : ℤ_[2]ˣ) ∈ P.C) : Bool :=
  (P.exists_eps hr h₁).choose

theorem epsilonOf_spec (hr : 1 ≤ P.r) (h₁ : (-1 : ℤ_[2]ˣ) ∈ P.C) :
    P.lambdaAt (-1) h₁
      = ((epsVal (P.epsilonOf hr h₁) * 2 ^ (P.r - 1) : ℕ) : ZMod (2 ^ P.r)) :=
  (P.exists_eps hr h₁).choose_spec

/-- **`η` for the `M_α` rows** (packet §8): `η = λ(u)` with `u = (1 − 2^α)⁻¹ ∈ 1 + 4ℤ₂`.  The
`α`-pinning travels as a hypothesis in the house style (B5's `chiCyc_recip_neg3`, F4's
`toZModPow_three_eq_five_of_uM_two`), so a caller cannot feed the wrong unit. -/
def etaM (α : ℕ) (_hα : 2 ≤ α) (u : ℤ_[2]ˣ) (_hu : (u : ℤ_[2]) * (1 - 2 ^ α) = 1)
    (hmem : u ∈ P.C) : ZMod (2 ^ P.r) := P.lambdaAt u hmem

/-- **`η` for the `N_α` procyclic rows** (draft §2, type-`N` paragraph): `η = λ(v)` with
`v = −(1 + 2^α)⁻¹`. -/
def etaN (α : ℕ) (_hα : 2 ≤ α) (v : ℤ_[2]ˣ) (_hv : (v : ℤ_[2]) * (-(1 + 2 ^ α)) = 1)
    (hmem : v ∈ P.C) : ZMod (2 ^ P.r) := P.lambdaAt v hmem

theorem etaM_spec (α : ℕ) (hα : 2 ≤ α) (u : ℤ_[2]ˣ) (hu : (u : ℤ_[2]) * (1 - 2 ^ α) = 1)
    (hmem : u ∈ P.C) (g : A) (hg : P.chi g = u) :
    P.etaM α hα u hu hmem = PadicInt.toZModPow P.r (P.nu g).toAdd :=
  P.lambdaAt_spec u hmem g hg

theorem etaN_spec (α : ℕ) (hα : 2 ≤ α) (v : ℤ_[2]ˣ) (hv : (v : ℤ_[2]) * (-(1 + 2 ^ α)) = 1)
    (hmem : v ∈ P.C) (g : A) (hg : P.chi g = v) :
    P.etaN α hα v hv hmem = PadicInt.toZModPow P.r (P.nu g).toAdd :=
  P.lambdaAt_spec v hmem g hg

/-- The `η`-adapter bridge to F1/F4: `η : ℤ₂ˣ` represents `λ(u)` exactly when its `mod 2^r`
reduction is `λ(u)` (`IsEtaFor` of `GQ2/Dyadic/Branches.lean`). -/
theorem isEtaFor_datum_iff (u : ℤ_[2]ˣ) (hmem : u ∈ P.C) (η : ℤ_[2]ˣ) :
    IsEtaFor P.datum ⟨u, hmem⟩ η ↔ P.lambdaAt u hmem = PadicInt.toZModPow P.r (η : ℤ_[2]) := by
  rw [isEtaFor_iff]
  rfl

end MarkedPair

end MarkedPairSection

/-! ## §3 The bundle

Memo §2.2 verbatim: twelve fields.  The finite-layer norm-residue clause `(a_K)`
(`Gal(L/K) ≅ Kˣ/N(Lˣ)`) is **omitted** — no dyadic-campaign lane consumes it (memo §1.3, owner
answer Q2); `ν_ur` surjectivity, `C`, `I`, `λ` and `γ` are **not** fields, being derived in §2 and
below (memo §1.4, §1.5).  The `R : LocalReciprocity` parameter is B5, exactly as B10′'s
`OrientedTameQuotient (R : LocalReciprocity)`; B5 is *extended, not replaced* (memo §6, owner
answer Q6), so nothing about `localReciprocity` changes. -/

/-- **Marked local reciprocity for a finite dyadic `K` (the packet's `MarkedRecip`).**
The arithmetic reciprocity map `rec_K` and the geometric full `ℤ₂`-valued unramified
coordinate `ν_ur^K`, pinned against the ℚ₂ bundle `R` by norm functoriality, together with the
marked cyclotomic quotient datum `(r, A = 2^r ℤ₂)` of draft eq. 2.1 and the `K(i)`
fixed-field bridge (packet Prop. 8.1's input).  `C`, `I`, `λ`, `γ` are *derived* from these
fields (see `MarkedRecip.toMarkedPair` and §2), not carried.  Conventions inherited verbatim
from B5 (`GQ2/Reciprocity.lean` module docstring): `rec` arithmetic, `ν` geometric
(`ν(rec π) = −1` for a uniformizer `π`), `ν`-target the profinite `Multiplicative ℤ₂`
(soundness: a discrete target would be inconsistent).

The axiom `GQ2.markedRecipAt : ∀ K, MarkedRecip localReciprocity K` is **not** declared in this
file; it lands in `GQ2/Foundations/Axioms.lean` at the census flip (memo §2.3, §6).  Everything
here and below is bundle-parametrized, hence axiom-free. -/
structure MarkedRecip (R : LocalReciprocity)
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K] where
  /-- The arithmetic local reciprocity map `rec_K : Kˣ →* G_K^{ab}`. -/
  recip : (↥K)ˣ →* GalKab K
  /-- `rec_K` is continuous. -/
  continuous_recip : Continuous recip
  /-- `rec_K` has dense image (`G_K^{ab}` is the profinite completion of `Kˣ`). -/
  denseRange_recip : DenseRange recip
  /-- The full unramified coordinate `ν_ur^K : G_K^{ab} →* Multiplicative ℤ₂` (target
  profinite — B5 soundness note). -/
  nu_ur : GalKab K →* Multiplicative ℤ_[2]
  /-- `ν_ur^K` is continuous. -/
  continuous_nu_ur : Continuous nu_ur
  /-- **(c1) Norm functoriality against the ℚ₂ bundle**: `incl_* ∘ rec_K = rec ∘ N_{K/ℚ₂}`.
  [Serre LF Ch. XI §3; NSW class-formation functoriality — this is the inclusion↔norm
  diagram, *not* the transfer↔field-inclusion diagram.] -/
  norm_compat : ∀ x : (↥K)ˣ, inclAbK K (recip x) = R.recip (normUnitsK K x)
  /-- **(b_K) units.** `ν_ur^K(rec_K u) = 1` for every unit (`‖u‖ = 1`, the B11b idiom).
  [Serre LF Ch. XIII §4, Prop. 13: reciprocity maps units into (onto) inertia.] -/
  nu_ur_recip_unit : ∀ u : (↥K)ˣ, ‖((u : ↥K) : AlgebraicClosure ℚ_[2])‖ = 1 →
      nu_ur (recip u) = 1
  /-- **(b_K) uniformizers.** `ν_ur^K(rec_K π) = ofAdd (−1)` for `π` of maximal norm `< 1`
  (the B13 uniformizer idiom): `rec_K π` is arithmetic Frobenius mod inertia; geometric
  coordinate `−1`.  [Serre LF XIII §4 Prop. 13 corollary; B10′ orientation pattern.] -/
  nu_ur_recip_uniformizer : ∀ π : (↥K)ˣ,
      ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖ < 1 →
      (∀ z : ↥K, z ≠ 0 → ‖(z : AlgebraicClosure ℚ_[2])‖ < 1 →
        ‖(z : AlgebraicClosure ℚ_[2])‖ ≤ ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖) →
      nu_ur (recip π) = Multiplicative.ofAdd ((-1 : ℤ) : ℤ_[2])
  /-- The marked level `r`: `ν_ur^K(ker χ_K) = 2^r ℤ₂` (draft eq. 2.1's `A`).  Finiteness of
  `r` = finiteness of the unramified part of `K(μ_{2^∞})/K`. -/
  r : ℕ
  /-- `A ⊆ 2^r ℤ₂` (λ well-definedness direction). -/
  nu_ker_chi_le : ∀ g : GalKab K, chiCycKAb K g = 1 →
      ∃ y : ℤ_[2], (nu_ur g).toAdd = 2 ^ r * y
  /-- `A ⊇ 2^r ℤ₂` (exactness of the level; `I = ker λ` direction). -/
  nu_ker_chi_ge : ∀ y : ℤ_[2], ∃ g : GalKab K,
      chiCycKAb K g = 1 ∧ (nu_ur g).toAdd = 2 ^ r * y
  /-- **The `K(i)` fixed-field bridge** (packet Prop. 8.1's input, one direction): if the
  inertia image `I = χ(ker ν)` lies in `1 + 4ℤ₂` (trivial action on `μ₄`), then `K(i)/K` is
  unramified in the repo's equal-norm-value-groups convention.  [Composite: Galois
  correspondence for the inertia fixed field + the `e = 1` criterion; the convention is the
  isolated `def` `HasEqualNormValueGroups`, B11b precedent.] -/
  ki_unramified : (∀ g : GalKab K, nu_ur g = 1 →
        (PadicInt.toZModPow 2 ((chiCycKAb K g : ℤ_[2]ˣ) : ℤ_[2])) = 1) →
      ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi

namespace MarkedRecip

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])}
  [FiniteDimensional ℚ_[2] K] (B : MarkedRecip R K)

/-! ### `ν_ur` surjectivity (memo §1.5, third bullet)

B5 carries surjectivity of `ν_ur` as a *field*; here it is a theorem, and the uniformizer is the
input.  Two independent routes, both in the memo:

* `surjective_nu_ur_of_uniformizer` — the uniformizer clause plus `nu_ker_chi_ge`.  Because it
  *needs* a `π` meeting the spectral spec, it is simultaneously the guard of memo §7 R8: a
  vacuously-stated uniformizer clause fails to produce surjectivity, so the bundle cannot
  silently lose its Frobenius pin.
* `surjective_nu_ur_of_level_zero` — at `r = 0` (`ν(ker χ) = ℤ₂`, the type-`L` case)
  `nu_ker_chi_ge` alone suffices.

The uniformizer is threaded as a hypothesis rather than taken from `dyadicUnitFiltration K`: that
interface lives in `GQ2/Foundations/Interfaces.lean`, *above* the axiom file this one must sit
below (memo §7 R9).  Every consumer that has a filtration in scope discharges it in one line. -/

/-- `ν_ur` hits every `2^r`-multiple, straight from `nu_ker_chi_ge`. -/
theorem exists_nu_ur_eq_two_pow_mul (y : ℤ_[2]) :
    ∃ g : GalKab K, (B.nu_ur g).toAdd = 2 ^ B.r * y :=
  (B.nu_ker_chi_ge y).imp fun _ h => h.2

/-- **`ν_ur` is surjective**, given a uniformizer.  Any `z : ℤ₂` is `2^r·y + m` for an ordinary
integer `m` (`MarkedPair.exists_intCast_congr`); the `2^r·y` part comes from `nu_ker_chi_ge` and
the `m` part from `rec_K(π)^{−m}`, whose `ν`-value is `ofAdd m` by the geometric normalization. -/
theorem surjective_nu_ur_of_uniformizer (π : (↥K)ˣ)
    (hπ : ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖ < 1)
    (hmax : ∀ z : ↥K, z ≠ 0 → ‖(z : AlgebraicClosure ℚ_[2])‖ < 1 →
      ‖(z : AlgebraicClosure ℚ_[2])‖ ≤ ‖((π : ↥K) : AlgebraicClosure ℚ_[2])‖) :
    Function.Surjective B.nu_ur := by
  intro w
  obtain ⟨m, y, hmy⟩ := MarkedPair.exists_intCast_congr B.r w.toAdd
  obtain ⟨g, hg⟩ := B.exists_nu_ur_eq_two_pow_mul y
  refine ⟨g * B.recip (π ^ (-m)), Multiplicative.toAdd.injective ?_⟩
  have hπval : (B.nu_ur (B.recip (π ^ (-m)))).toAdd = ((-m : ℤ) : ℤ_[2]) * (-1 : ℤ_[2]) := by
    rw [map_zpow, map_zpow, B.nu_ur_recip_uniformizer π hπ hmax]
    show ((-m : ℤ) • ((-1 : ℤ) : ℤ_[2])) = _
    rw [zsmul_eq_mul]
    norm_num
  show (B.nu_ur (g * B.recip (π ^ (-m)))).toAdd = w.toAdd
  rw [map_mul]
  show (B.nu_ur g).toAdd + (B.nu_ur (B.recip (π ^ (-m)))).toAdd = w.toAdd
  rw [hg, hπval]
  have : w.toAdd - (m : ℤ_[2]) = 2 ^ B.r * y := hmy
  push_cast
  linear_combination -this

/-- At level `r = 0` surjectivity of `ν_ur` needs no uniformizer. -/
theorem surjective_nu_ur_of_level_zero (hr : B.r = 0) : Function.Surjective B.nu_ur := by
  intro w
  obtain ⟨g, hg⟩ := B.exists_nu_ur_eq_two_pow_mul w.toAdd
  exact ⟨g, Multiplicative.toAdd.injective (by rw [hg, hr]; ring)⟩

/-! ### The derived marked pair, and the `(C, I, λ, γ)` block -/

/-- **The bundle's marked pair** `(χ_K, ν_ur^K, r)` — the object §2's whole derivation applies to.
`hsurj` is `surjective_nu_ur_of_uniformizer` (or `_of_level_zero`) at the call site. -/
def toMarkedPair (hsurj : Function.Surjective B.nu_ur) : MarkedPair (GalKab K) where
  chi := chiCycKAb K
  nu := B.nu_ur
  surjective_nu := hsurj
  r := B.r
  nu_ker_chi_le := B.nu_ker_chi_le
  nu_ker_chi_ge := B.nu_ker_chi_ge

@[simp] theorem toMarkedPair_r (hsurj : Function.Surjective B.nu_ur) :
    (B.toMarkedPair hsurj).r = B.r := rfl

@[simp] theorem toMarkedPair_chi (hsurj : Function.Surjective B.nu_ur) :
    (B.toMarkedPair hsurj).chi = chiCycKAb K := rfl

@[simp] theorem toMarkedPair_nu (hsurj : Function.Surjective B.nu_ur) :
    (B.toMarkedPair hsurj).nu = B.nu_ur := rfl

/-- **`C = χ(G_K^{ab}) = χ(D_K)`** (memo §1.4): a definition, not a clause.  This is exactly the
instantiation `C := (chiCycKAb K).range` that F4's `unramified_of_even` docstring names. -/
abbrev CK : Subgroup ℤ_[2]ˣ := (chiCycKAb K).range

/-- **`I = χ(ker ν_ur)`**, draft eq. 2.1's inertia image. -/
abbrev IK : Subgroup ℤ_[2]ˣ := B.nu_ur.ker.map (chiCycKAb K)

theorem toMarkedPair_C (hsurj : Function.Surjective B.nu_ur) :
    (B.toMarkedPair hsurj).C = CK (K := K) := rfl

theorem toMarkedPair_I (hsurj : Function.Surjective B.nu_ur) :
    (B.toMarkedPair hsurj).I = B.IK := rfl

/-! ### The `K(i)` field bridge, in both directions of use (memo §1.6, owner answer Q4)

Only the data ⇒ field direction is asserted.  Owner answer Q4 fixes the *field-language*
spelling for the final theorem's standing hypothesis, so the shape AS5 needs is the
contrapositive `not_forall_mem_IK_...` below: an instance discharges "K(i)/K is ramified" by an
explicit norm-value mismatch in the `not_hasEqualNormValueGroups_sqrt_two` pattern
(`GQ2/Foundations/Interfaces.lean`), and this lemma turns that into the marked-data fact
`¬ (I ≤ 1 + 4ℤ₂)` that the branch rows consume. -/

/-- **The bridge in `I`-language** (memo §1.6): if every element of the inertia image `I` is
`≡ 1 (mod 4)` then `K(i)/K` is unramified.  The clause is stated on `ker ν`; this is the same
statement transported through `I = χ(ker ν)`, which is the form F4's `bridge` binder takes. -/
theorem hasEqualNormValueGroups_of_mem_IK
    (h : ∀ c ∈ B.IK, PadicInt.toZModPow 2 ((c : ℤ_[2]ˣ) : ℤ_[2]) = 1)
    (δi : AlgebraicClosure ℚ_[2]) (hδi : δi ^ 2 = -1) : HasEqualNormValueGroups K δi :=
  B.ki_unramified (fun g hg => h _ ⟨g, MonoidHom.mem_ker.2 hg, rfl⟩) δi hδi

/-- **The contrapositive AS5 uses** (owner answer Q4): a field-language ramification witness for
`K(i)/K` forces some element of the inertia image to move `μ₄`, i.e. `¬ (I ≤ 1 + 4ℤ₂)`. -/
theorem exists_mem_IK_of_not_hasEqualNormValueGroups
    (δi : AlgebraicClosure ℚ_[2]) (hδi : δi ^ 2 = -1)
    (hram : ¬ HasEqualNormValueGroups K δi) :
    ∃ c ∈ B.IK, PadicInt.toZModPow 2 ((c : ℤ_[2]ˣ) : ℤ_[2]) ≠ 1 := by
  by_contra hcon
  refine hram (B.hasEqualNormValueGroups_of_mem_IK (fun c hc => ?_) δi hδi)
  by_contra hne
  exact hcon ⟨c, hc, hne⟩

/-- The bridge in the shape F4's `MarkedSplitting.unramified_of_even` binder wants: `chi` the
inclusion `C ↪ ℤ₂ˣ`, `Unramified` the field-side conclusion, and the premise quantified over
`ker λ = I` (the identification is `MarkedPair.mem_inertiaImage_iff`). -/
theorem bridge_of_inertiaImage (hsurj : Function.Surjective B.nu_ur) :
    (∀ c ∈ (B.toMarkedPair hsurj).datum.inertiaImage,
        PadicInt.toZModPow 2 ((((CK (K := K)).subtype c : ℤ_[2]ˣ)) : ℤ_[2]) = 1) →
      ∀ δi : AlgebraicClosure ℚ_[2], δi ^ 2 = -1 → HasEqualNormValueGroups K δi := by
  intro h
  refine B.hasEqualNormValueGroups_of_mem_IK fun c hc => ?_
  obtain ⟨g, hg, rfl⟩ := hc
  exact h ⟨chiCycKAb K g, ⟨g, rfl⟩⟩
    (((B.toMarkedPair hsurj).mem_inertiaImage_iff _).2 ⟨g, hg, rfl⟩)

end MarkedRecip

end

end GQ2.Dyadic
