/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Foundations.Axioms
public import GQ2.HilbertSymbol
public import GQ2.HilbertSymbolDyadicClose
public import GQ2.KummerSurjectivity
public import GQ2.UnramifiedQuadraticNorms
public import GQ2.UnitFiltration
public import GQ2.UnitFiltrationCounts
public import GQ2.EvensKahnDerived
public import GQ2.Dyadic.MarkedRecipBundle

@[expose] public section

/-!
# Discharged and derived interfaces over the literature axioms

Companion to `GQ2/Foundations/Axioms.lean` — the census file, which since 2026-07-27 contains
the nine `axiom` declarations and nothing else.  This file hosts the *derived* layer that
shares the axioms' public interface:

* the formerly-axiom interfaces discharged by in-repository proofs, under their original
  names — `HilbertSymbol.hilbertSymbol_dyadic` (B7′), `unramifiedQuadratic_units_are_norms`
  (B11b), `kummerClassK_surjective` (B12), `dyadicUnitFiltration` (B13);
* `evensKahn_dyadic` — the pre-2026-07-24 B9 axiom, re-derived byte-identically from the
  current B9 leaf `relativeStiefelWhitney_dyadic` together with B11a;
* `tateDuality` — the `k = ℚ₂` member of the B6 axiom `tateDualityAt`;
* the `HasEqualNormValueGroups` convention `def`, its negative stress test, and the combined
  `dyadicNormCriterion`.

Every name is unchanged from when these declarations lived in `Axioms.lean`, so consumers
needed no migration; importers of the old combined file now import this one (a strict API
superset, since `GQ2.Foundations.Axioms` is a `public import` above).  The split exists for
auditability: the *proofs* collected here are what pulled the proof layer into the axiom
file's transitive imports, and after the split the axiom file's import closure is its
statement vocabulary only.  Census history and citations remain with the axioms and in
`docs/literature-axioms.md`.
-/

open GQ2.ContCoh

namespace GQ2.HilbertSymbol

/-! ## B7′ — the dyadic Hilbert-symbol formula

`hilbertSymbol`, `ε`, `ω`, `unit2`, `unitCoe`, `signOf` and their unconditional theory live in
`GQ2/HilbertSymbol.lean`. -/

/-- **The dyadic Hilbert symbol formula, formerly interface B7′.**
Writing `a = 2^α u`, `b = 2^β v` with `u, v ∈ ℤ₂ˣ`, the Hilbert symbol over `ℚ₂` is
`(a, b)₂ = (-1)^{ε(u) ε(v) + α ω(v) + β ω(u)}`.

Citation: **Serre, *A Course in Arithmetic* [CiA], Ch. III §1.2, Theorem 1** (the `p = 2`
case), with `ε, ω` the residue characters of Ch. II §3.3.  This is exactly the paper's
Lemma 3.5 formula for the cup product on `H¹(ℚ₂, μ₂)`.  Convention: `signOf` sends the
`𝔽₂`-valued exponent to `{±1} = ℤˣ`; every element of `ℚ₂ˣ` has the form `2^α u` (`α ∈ ℤ`,
`u ∈ ℤ₂ˣ`), so this determines the symbol on all of `ℚ₂ˣ × ℚ₂ˣ`.

The theorem delegates to `hilbertSymbol_dyadic'` in `GQ2/HilbertSymbolDyadicClose.lean`, whose
proof uses 2-adic Hensel lifting, the norm-form identity `(a,b) = (a,−ab)`, and finite mod-8
computations. -/
theorem hilbertSymbol_dyadic (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u) :=
  hilbertSymbol_dyadic' α β u v

/-- Faithfulness check on B7′: the axiom reproduces the canonical value `(-1, -1)₂ = -1` — the
one nontrivial diagonal entry, which anchors the paper's initial cup form `α² + βγ + γβ`.
(Depends on `hilbertSymbol_dyadic`, so this is an `example`, not part of the unconditional
API.) -/
example : hilbertSymbol (unitCoe (-1)) (unitCoe (-1)) = -1 := by
  have h := hilbertSymbol_dyadic 0 0 (-1) (-1)
  rw [zpow_zero, one_mul] at h
  rw [h, ε_neg_one, ω_neg_one]
  decide

end GQ2.HilbertSymbol

namespace GQ2

/-! ## B6 at the base field — the `G = G_ℚ₂` member of the axiom `tateDualityAt` -/

/-- **B6 at the base field `ℚ₂`** — the `G = G_ℚ₂` member of `tateDualityAt`, using
`isLocalDualizingGroup_absGalQ2`. -/
noncomputable def tateDuality (n : ℕ) [NeZero n] : TateDuality n :=
  tateDualityAt AbsGalQ2 n (isLocalDualizingGroup_absGalQ2 n)

/-! ## The B11 convention layer and the discharged B11b

The full B11 conventions and citations are with the B11a axiom in
`GQ2/Foundations/Axioms.lean`; this section holds the pieces that are not axioms. -/

/- The convention `def GQ2.HasEqualNormValueGroups` itself now lives in
`GQ2/Dyadic/MarkedRecipBundle.lean` (moved 2026-07-29, AX3 memo §7 R7 / owner answer Q3: the AX3
`ki_unramified` clause needs it, and `Axioms.lean` — which this file imports — must import the
bundle file at the census flip).  Name, statement, namespace and docstring are unchanged, so the
alias and the two consumers below are byte-identical to before the move. -/

@[deprecated HasEqualNormValueGroups (since := "2026-07-24")]
alias IsUnramifiedQuadraticSpectral := HasEqualNormValueGroups

/-- **Negative stress test for `HasEqualNormValueGroups`** (adversarial-review plan U1): the
*ramified* quadratic extension `ℚ₂(√2)/ℚ₂` **fails** the criterion, so the predicate is not
vacuously satisfied — it genuinely detects `e = 1`.  Take the base `k = ⊥` (every element is the
image of a `2`-adic scalar) and `δa` any square root of `2` in `ℚ̄₂`.  The witness `z = δa`
(`= ↑0 + ↑1·δa`) has `‖δa‖² = ‖δa²‖ = ‖(2 : ℚ̄₂)‖ = ‖(2 : ℚ₂)‖`, while every nonzero `w ∈ ⊥` is
`algebraMap c` for some `c ∈ ℚ₂` with `‖w‖ = ‖c‖` in the discrete value group `{2ⁿ : n ∈ ℤ}`.
A match `‖δa‖ = ‖w‖` would give `‖(2 : ℚ₂)‖ = ‖c²‖`, i.e. `v₂(2) = v₂(c²)`, i.e. `1 = 2·v₂(c)`
in `ℤ` — impossible.  Contrast `unramifiedQuadratic_units_are_norms`, whose conclusion the
criterion supplies precisely in the unramified case it does hold. -/
lemma not_hasEqualNormValueGroups_sqrt_two (δa : AlgebraicClosure ℚ_[2])
    (hδa : δa ^ 2 = (2 : AlgebraicClosure ℚ_[2])) :
    ¬ HasEqualNormValueGroups ⊥ δa := by
  intro h
  have h2q : (2 : ℚ_[2]) ≠ 0 := two_ne_zero
  have hδa0 : δa ≠ 0 := by
    intro h0
    rw [h0, zero_pow two_ne_zero] at hδa
    exact two_ne_zero hδa.symm
  obtain ⟨w, hw0, hnorm⟩ := h δa hδa0 ⟨0, 1, by simp⟩
  obtain ⟨c, hc⟩ := IntermediateField.mem_bot.1 w.2
  have hwne0 : (w : AlgebraicClosure ℚ_[2]) ≠ 0 := by simpa using hw0
  have hc0 : c ≠ 0 := fun h0 => hwne0 (by rw [← hc, h0, map_zero])
  -- `‖δa‖² = ‖2‖`, transported from the algebraic closure down to the `2`-adic base.
  have hδanorm : ‖δa‖ ^ 2 = ‖(2 : ℚ_[2])‖ := by
    rw [← norm_pow, hδa, ← map_ofNat (algebraMap ℚ_[2] (AlgebraicClosure ℚ_[2])) 2,
      norm_algebraMap' (𝕜' := AlgebraicClosure ℚ_[2])]
  have hcnorm : ‖(w : AlgebraicClosure ℚ_[2])‖ = ‖c‖ := by
    rw [← hc, norm_algebraMap' (𝕜' := AlgebraicClosure ℚ_[2])]
  -- Squaring the (hypothetical) equal norm collapses to `‖2‖ = ‖c²‖` inside `ℚ₂`.
  have key : ‖(2 : ℚ_[2])‖ = ‖c ^ 2‖ := by rw [← hδanorm, hnorm, hcnorm, norm_pow]
  rw [Padic.norm_eq_zpow_neg_valuation h2q,
    Padic.norm_eq_zpow_neg_valuation (pow_ne_zero 2 hc0),
    zpow_right_inj₀ (by norm_num) (by norm_num)] at key
  have hv2 : (2 : ℚ_[2]).valuation = 1 := by exact_mod_cast Padic.valuation_p (p := 2)
  have hvp : (c ^ 2).valuation = 2 * c.valuation := by exact_mod_cast Padic.valuation_pow c 2
  omega

/-! ## B9, derived form (the pre-flip axiom, now a theorem over B9 + B11a) -/

/-- **Formerly the B9 axiom — since 2026-07-24 a derived theorem** (the B9-A flip; the statement
is byte-identical to the pre-flip axiom, zero consumer churn — the B7′/B11b/B12/B13 pattern).
Eq. (111) at the paper's Lemma 6.16 diagonalizations `Tr_{L/k}⟨a⟩ ≃ ⟨2u, 2dn/u⟩`,
`Tr_{L/k}⟨1⟩ ≃ ⟨2, 2d⟩`, with `w₁⟨x,y⟩ = [x]+[y]` and `w₂⟨x,y⟩ = [x] ⌣ [y]`:

* degree 1: `[2u] + [2dn/u] = [2] + [2d] + cor[a]`;
* degree 2: `[2u] ⌣ [2dn/u] = [2] ⌣ [2d] + ([2] + [2d]) ⌣ cor[a] + N^{Ev}[a]`.

Proof: `evensKahn_dyadic_of_rsw` (`GQ2/EvensKahnDerived.lean`) applied to the B9 axiom
`relativeStiefelWhitney_dyadic` and to B11a (the `hnorm` input of the Delzant well-definedness
layer); the T2 trace-form diagonalizations and the proved `swOne`/`swTwo` invariance do the
rewriting.  `#print axioms`: `relativeStiefelWhitney_dyadic` and
`hilbertSymbol_normCriterion_finiteDyadic` (+ the standard three).  Full setting and citations:
the B9 axiom's docstring in `GQ2/Foundations/Axioms.lean` and `docs/literature-axioms.md` §B9. -/
theorem evensKahn_dyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (u n d : (↥k)ˣ) (v : ↥k)
    (hn : (n : ↥k) = (u : ↥k) ^ 2 - (d : ↥k) * v ^ 2)
    (δ β : AlgebraicClosure ℚ_[2])
    (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hβ : β ^ 2 = ((u : ↥k) : AlgebraicClosure ℚ_[2]) + (v : AlgebraicClosure ℚ_[2]) * δ)
    (hβ0 : β ≠ 0)
    (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup).index = 2)
    (s : k.fixingSubgroup)
    (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
        k.fixingSubgroup) → ZMod 2)
    (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
        ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hα : ∀ g h, α (g * h) = α g + α h)
    (hαc : Continuous α) :
    (kummerClassK k (twoUnit k * u) + kummerClassK k (twoUnit k * d * n * u⁻¹)
      = kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d)
        + corH1 htriv hUo hidx hs α hα hαc)
    ∧ (kummerClassK k (twoUnit k * u) ⌣[htriv] kummerClassK k (twoUnit k * d * n * u⁻¹)
      = kummerClassK k (twoUnit k) ⌣[htriv] kummerClassK k (twoUnit k * d)
        + (kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d)) ⌣[htriv]
            corH1 htriv hUo hidx hs α hα hαc
        + evensNormH2 htriv hUo hidx hs α hα hαc) :=
  evensKahn_dyadic_of_rsw relativeStiefelWhitney_dyadic k u n d v hn δ β hδ hβ hβ0 hidx s hs
    htriv hUo α hαdef hα hαc (hilbertSymbol_normCriterion_finiteDyadic k htriv)

/-- **Unramified unit-norm surjectivity, formerly interface B11b.**  If
`k(√a)/k` is unramified (the `HasEqualNormValueGroups` convention on a chosen root `δa`,
`δa² = a`), then every unit of `k` (`‖u‖ = 1`) is a norm from `k(√a)` — i.e. `u = x² − a y²` is
solvable in `k`.

Citation: Serre, *Local Fields* [7], Ch. V §2 (norms of unramified
extensions are the units times the norms of uniformizers).  Paper: §6.3 (unramified-norm input to
the local calculation).

The proof in `GQ2/UnramifiedQuadraticNorms.lean` completes the square using the involution
`σδ = −δ`, then constructs a depth-by-depth norm-form approximation
`wₙ₊₁ = wₙ(1 + πⁿ⁺¹z₀)` against the dyadic unit filtration.  Exact trace coverage
`z ↦ z + σz` supplies each increment. -/
theorem unramifiedQuadratic_units_are_norms
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (a : (↥k)ˣ) (δa : AlgebraicClosure ℚ_[2])
    (hδa : δa ^ 2 = ((a : ↥k) : AlgebraicClosure ℚ_[2]))
    (hunram : HasEqualNormValueGroups k δa) :
    ∀ u : (↥k)ˣ, ‖((u : ↥k) : AlgebraicClosure ℚ_[2])‖ = 1 →
      ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 :=
  UnramifiedQuadraticNorms.unramifiedQuadratic_units_are_norms' k a δa hδa hunram

/-- **The combined dyadic norm criterion.**  This theorem pairs the classical B11a leaf with the
proved unramified-unit theorem.  The equal-norm-value-groups convention remains isolated in
`HasEqualNormValueGroups` (named `IsUnramifiedQuadraticSpectral` before 2026-07-24), which is a
definition rather than an axiom. -/
theorem dyadicNormCriterion
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    (∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0
        ↔ ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2)
    ∧ ∀ (a : (↥k)ˣ) (δa : AlgebraicClosure ℚ_[2]),
        δa ^ 2 = ((a : ↥k) : AlgebraicClosure ℚ_[2]) →
        (∀ z : AlgebraicClosure ℚ_[2], z ≠ 0 →
          (∃ x y : ↥k, z = (x : AlgebraicClosure ℚ_[2]) + (y : AlgebraicClosure ℚ_[2]) * δa) →
          ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : AlgebraicClosure ℚ_[2])‖) →
        ∀ u : (↥k)ˣ, ‖((u : ↥k) : AlgebraicClosure ℚ_[2])‖ = 1 →
          ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2 :=
  ⟨hilbertSymbol_normCriterion_finiteDyadic k htriv,
   fun a δa hδa hunram u hu =>
     unramifiedQuadratic_units_are_norms k a δa hδa hunram u hu⟩

/-! ## In-repository Kummer and unit-filtration interfaces

Lemma 6.17 uses local Kummer surjectivity and the graded structure of the dyadic unit filtration.
Both interfaces are constructed below from in-repository proofs.  The surrounding
`DeepKummerData` assembly is developed in `GQ2/LocalKummer.lean`; its remaining inputs include
coprime averaging, the Hensel square criterion, graded duality, Lemma 6.10, and Lemma 6.11.
-/

/-- **Local Kummer theory, surjective half, formerly interface B12.**

For a finite extension `k/ℚ₂`, the Kummer class map descends to an isomorphism
`k^×/(k^×)² ≅ H¹(G_k, ℤ/2)` (continuous cochain cohomology; `μ₂ ≅ ℤ/2`, canonical in
char 0).  This theorem exposes only surjectivity; injectivity is proved separately by
`Kummer.kummerClass_eq_zero_iff` (`[a] = 0 ↔ IsSquare a`) via Mathlib's infinite Galois
correspondence.

Citation: **NSW [1], Ch. VI §2 — Theorem (6.2.1) (Hilbert's Satz 90)
and the Kummer-sequence isomorphism `H¹(G_K, μ_n) ≅ K^×/K^{×n}` displayed immediately after it
(electronic ed. p. 344), dual form Theorem (6.2.2)**; at `n = 2`.  Secondary: Serre, *Local
Fields* [7], Ch. XIV §2 (p. 206).  Both verified verbatim against the cited PDFs; the audit
copies are not vendored in this repository.

The proof in `GQ2/KummerSurjectivity.lean` combines completing the square with the
Krull–Galois correspondence from `GQ2/KummerKrullBridge.lean`, where an open index-two subgroup
produces the required quadratic subextension.

Paper: §6.3 (Lemma 6.17, "By Hochschild–Serre and Kummer theory").
`docs/literature-axioms.md` B12. -/
theorem kummerClassK_surjective (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    Function.Surjective (kummerClassK k) :=
  KummerSurjectivity.kummerClassK_surjective' k

/-- **The dyadic unit filtration interface, formerly B13.**

Every finite extension `k/ℚ₂` carries a `DyadicUnitFiltration` (`GQ2/UnitFiltration.lean`):
a uniformizer `π` (an element of maximal spectral norm `< 1` — discreteness of the value
group), the normalization `‖2‖ = ‖π‖^e` (`e = v_k(2) ≥ 1`), a residue degree `f ≥ 1`, and
the graded counts of the unit filtration `U^{(i)} = 1 + 𝔭_k^i`:
`#(U^{(0)}/U^{(1)}) = 2^f − 1` and `#(U^{(i)}/U^{(i+1)}) = 2^f` for `i ≥ 1`.

Citation: **Serre, *Local Fields* [7], Ch. IV §2, Proposition 6** (verified verbatim against
the cited source, pp. 66–67; the audit copy is not vendored): "(a) `U_L/U_L^{(1)} = L̄^*`;
(b) for `i ≥ 1`, the group
`U^{(i)}/U^{(i+1)}` is canonically isomorphic to `𝔭_L^i/𝔭_L^{i+1}`, which is itself
isomorphic (non-canonically) to the additive group of the residue field `L̄`" — read through
`#L̄ = 2^f`, `#L̄^× = 2^f − 1`.  Uniformizer existence: Serre LF Ch. I–II (discrete
valuations, complete fields; standard).

Deviations (flagged, review-packet §3): stated in spectral-norm vocabulary (no valuation
ring/residue field is constructed — the graded pieces enter through their cardinalities, the
form the multiplicity count consumes); the proposal's (F2) inertia-twist clause
(`θ_g = (g•π)/π` acting on `gr_j` by `θ_g^j`) is derivable from the exact `ℚ̄₂`-algebra action
and the `he` normalization, so it is deliberately not stored as a field.

Paper: §6.3, eq. (93) (the display's own bracket "[7, Ch. XIV §§2–3]" is coarse — the
filtration is Ch. IV §2).  `docs/literature-axioms.md` B13.

The definition delegates to `dyadicUnitFiltration'` in `GQ2/UnitFiltrationCounts.lean`, built on
`GQ2/UnitFiltrationTop.lean`; `Classical.choice` selects witnesses from the proved existence
lemmas.  The uniformizer comes from compactness of the
unit ball + an `O/2O` pigeonhole (no spectral-norm value formula); the residue field `O/𝔪` is the
finite quotient of the valuation subring; and the graded counts are the explicit isomorphisms
`U^{(0)}/U^{(1)} ≅ (O/𝔪)ˣ` and `U^{(i)}/U^{(i+1)} ≅ (O/𝔪)⁺`. -/
noncomputable def dyadicUnitFiltration (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    DyadicUnitFiltration k :=
  dyadicUnitFiltration' k

end GQ2
