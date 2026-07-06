import GQ2.Statement
import GQ2.ProfinitePresentation
import GQ2.Cohomology
import GQ2.HilbertSymbol
import GQ2.Reciprocity
import GQ2.TateDuality
import GQ2.EvensKahn
import GQ2.MaxProP
import GQ2.DyadicPresentation
import GQ2.PeripheralAction
import GQ2.Orientation
import GQ2.TameQuotient
import GQ2.UnitFiltration

/-!
# The axioms: classical literature inputs of Theorem 1.2  (ticket T-19)

**Every `axiom` of the GQ2 library lives in this file** (enforced by
`scripts/check_axioms.sh`).  Each one is a **classical, published** result that the paper's
proof of Theorem 1.2 rests on — the intended leaves once the paper's own §§3–9 argument is
granted.  The paper's own intermediate propositions (Prop. 1.1, Prop. 3.2, Thm. 4.2,
Lemma 10.1, …) are **not** here — they are the paper's contribution and live as sorried nodes
near `main_surjection_count`.

**How to read this for review.**  Each `axiom` below is a result that already
exists in the literature; the docstring gives the precise statement, the citation, and the
paper cross-reference.  The B-labels follow `docs/literature-axioms.md` (which also records the
dependency structure, paper App. D).  Current census — thirteen axioms (B11 split into B11a/B11b
by P-23, 2026-07-04), faithfully stated against
current Mathlib plus this repo's `ContCoh` cohomology:

* **B1** `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` — `G_ℚ₂` top. f.g.
* **B2** `Foundations.cyclotomicCharacter_two_surjective` — 2-adic cyclotomic surjectivity
  **(available; no current consumer — see its docstring)**.
* **B3c** `dyadicOrientation` — the canonical orientation character in cyclotomic-interface
  form: a B4 isomorphism normalized so the descended cyclotomic character takes Labute's
  Thm 4(2) values `(−1, 1, (−3)⁻¹)` on `A, S, Y` (defs + route decision in
  `GQ2/Orientation.lean`).  **Composite interface** — subsumes a marked B4 (see its docstring).
* **B4** `Foundations.absGalQ2_maxProTwo_presentation` — `G_ℚ₂(2) ≅ D₀`, the rank-3 dyadic
  Demushkin presentation (defs in `GQ2/DyadicPresentation.lean`).
* **B5** `localReciprocity` — the local-reciprocity bundle (defs in `GQ2/Reciprocity.lean`).
* **B6** `tateDualityAt` — local Tate duality, per-`n` bundle, at every finite `k/ℚ₂`
  (base-generalized 2026-07-06; the `ℚ₂` member is the `def tateDuality`; defs in
  `GQ2/TateDuality.lean`).
* **B7** `Foundations.absGalQ2_localEulerCharacteristic` — local Euler characteristic
  (cohomology from `GQ2/Cohomology.lean`).
* **B7′** `HilbertSymbol.hilbertSymbol_dyadic` — the dyadic Hilbert-symbol formula
  (defs in `GQ2/HilbertSymbol.lean`).
* **B8** `peripheralCyclotomicAction` — the cyclotomic action on the peripheral generators of
  `Δ = maxPro2(F₂)` (Lemma 3.6; defs + deviation note in `GQ2/PeripheralAction.lean`).
  **Composite** — Stix + cyclotomic surjectivity (see its docstring).
* **B9** `evensKahn_dyadic` — the Evens/Kahn eq. (111), degrees ≤ 2, at the paper's
  diagonalizations, over an arbitrary **finite dyadic base** `k` (defs in `GQ2/EvensKahn.lean`;
  base-generalized from `k = ℚ₂` by explicit census decision, resolving the P-15 escalation —
  the literature theorems are base-general and the paper applies (111) over general `k` in
  Lemma 6.16).
* **B10** `tameQuotient` — the tame quotient of `G_ℚ₂` (Iwasawa, NSW (7.5.3)), **oriented
  form B10′** (strengthened in place 2026-07-06, P-25 escalation, user-approved): a closed
  normal pro-2 `W` with `G_ℚ₂/W ≅ T_tame`, plus two reciprocity-orientation clauses (units ↦
  `ker ν_t`; `rec(2)` ↦ `ztwoOne⁻¹`; Neukirch ANT V (6.2), V (1.2)) (defs + convention/deviation
  notes in `GQ2/TameQuotient.lean`; added post-kickoff by explicit census decision, resolving
  the P-06 escalation — Prop. 3.2's local side; the orientation discharges Prop. 3.14's
  `compatF`).
* **B11a** `hilbertSymbol_normCriterion_finiteDyadic` + **B11b**
  `unramifiedQuadratic_units_are_norms` — the Hilbert-symbol norm criterion over finite dyadic
  bases (`[a]∪[b] = 0 ⟺ b` is a norm from `k(√a)`) and unramified unit-norm surjectivity.  Split
  from the single pre-P-23 `axiom dyadicNormCriterion` (census 12→13, adversarial review rec 2,
  user-approved 2026-07-04); `dyadicNormCriterion` survives as a same-name **theorem** over the
  two leaves (zero consumer churn) and the spectral-norm unramifiedness convention is isolated as
  the `def IsUnramifiedQuadraticSpectral` (not an axiom).  Same amendment decision as B9's
  base-generalization; consumed by Lemma 6.16's ledger and 6.17's (94)-orthogonality.

**Citation-faithfulness classification** (adversarial review 2026-07-04,
`docs/adversarial-axioms-review.md`; full table in `docs/review-packet.md` §2).  The leaves fall
in four tiers by how directly the Lean statement matches a single published theorem: **direct
classical theorem** (B1, B6, B7, B7′), **classical theorem + encoding choices** (B4, B5,
B9, B10 — since the B10′ orientation), **composite/project interface** (B3c, B8, B11a, B11b — each pairs a cited theorem with
encoding/convention inputs, flagged in its own docstring), and **available/unused** (B2).  The distinction keeps a
reviewer from mistaking a "nearby true theorem" for "this exact Lean interface appears verbatim
in the cited literature".

**B3's remaining pieces are deliberately not axioms**: the *definition* `IsDemushkin` and the
invariants (`demushkinRank`, `demushkinQ`) are done (`GQ2/Demushkin.lean`, T-09/T-10), and the
abstract rank-3 `q = 2` classification statement (B3b) is carried by **B4** at the field level
— stating it abstractly would require Labute's dualizing characterization of the canonical
character (route (i) of T-11, deliberately deferred; see `docs/tickets.md` T-10/T-11).

Consumers derive consequences by importing this file; the derived stress tests live next to
their definitions (`GQ2/EulerCharacteristic.lean` for B7) or are parametrized over the bundle
and axiom-free (`GQ2/Reciprocity.lean` for B5).  B7′'s faithfulness check (the canonical value
`(-1,-1)₂ = -1`) is an anonymous `example`, kept below next to its axiom.

References (paper's bibliography):
[1] Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer 2015.  (NSW)
[2] Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132.
[3] Serre, *Structure de certains pro-p-groupes*, Sém. Bourbaki 252 (1962–64).
[4] Ribes–Zalesskiĭ, *Profinite Groups*, 2nd ed., Springer 2010.  (RZ)
[7] Serre, *Local Fields*, GTM 67, Springer 1979.
[CiA] Serre, *A Course in Arithmetic*, GTM 7, Springer 1973.
-/

open GQ2.ContCoh

namespace GQ2.Foundations

open scoped Classical

/-! ## B1, B2 — leaves stateable against bare Mathlib -/

/-- **[Classical — B1.]** The absolute Galois group of a `p`-adic local field is *topologically
finitely generated* (by `[K : ℚ_p] + 3` elements when `μ_p ⊆ K`).  For `K = ℚ₂` this is the
input `hfgG` that `main_presentation` feeds to `reconstruction`.

Citation: NSW [1], Ch. VII §7.5, Theorem (7.5.14) (Jannsen–Wingberg) — `G_k` has `N+3`
generators (`N=[k:ℚ_p]`) with the tame + one wild relation, so is topologically finitely
generated; also (7.5.11). Original: Jannsen–Wingberg, Invent. Math. 70 (1982/83), 71–98.
(Verified against the NSW PDF in `references/`.)

This is a genuine, faithful Lean statement: it is exactly the topological-finite-generation
predicate used throughout `Reconstruction.lean`. -/
axiom absGalQ2_isTopologicallyFinitelyGenerated :
    ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤

/-- **[Classical — B2; available, currently unused.]** The `2`-adic cyclotomic character
`Gal(ℚ̄/ℚ) → ℤ₂ˣ` is surjective, equivalently `Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`.  This is the
surjectivity behind the paper's Lemma 3.6 (cyclotomic powering of the three peripheral inertia
classes of `π₁(ℙ¹∖{0,1,∞})`).  Stated here against Mathlib's `cyclotomicCharacter 2` on an
algebraic closure of `ℚ`.

**Ledger status** (adversarial review 2026-07-04, `docs/adversarial-axioms-review.md` §4): **no
Lean declaration currently consumes this axiom.**  Lemma 3.6 enters the formalization through
**B8** (`peripheralCyclotomicAction`), which bundles its own cyclotomic-surjectivity need (see
B8's note), and P-08 closed with B2 unused.  B2 is retained as B8's citation companion and the
global route to eliminate B8's surjectivity dependency — it is **not** on the critical path of
any current proof.  Verified by `grep` and `GQ2/AxiomLedger.lean` (zero consumers, 2026-07-04).

Citation: `Gal(ℚ(ζ_n)/ℚ) ≅ (ℤ/nℤ)ˣ` via `a ↦ (ζ ↦ ζ^a)` (Washington, *Introduction to
Cyclotomic Fields*, 2nd ed., GTM 83, Ch. 2, Theorem 2.5, verified), whence the inverse limit
`Gal(ℚ(μ_{2^∞})/ℚ) ≅ ℤ₂ˣ`. -/
axiom cyclotomicCharacter_two_surjective :
    Function.Surjective
      (cyclotomicCharacter (L := AlgebraicClosure ℚ) 2)

/-! ## B4 — the rank-3 dyadic Demushkin presentation

The presented group `D₀ = ⟨A, S, Y | A²S⁴[S,Y]⟩` (the relator `d0Relator`) and its finite-marking
stress test live in `GQ2/DyadicPresentation.lean`; the maximal pro-2 quotient `maxProPQuotient 2`
and its universal property live in `GQ2/MaxProP.lean`. -/

/-- **[Classical — B4.]** The maximal pro-2 quotient `G_ℚ₂(2) = maxProPQuotient 2 G_ℚ₂` of the
absolute Galois group is the rank-3 dyadic Demushkin group `D₀ = ⟨A, S, Y | A²S⁴[S,Y] = 1⟩`:
there is a continuous isomorphism `G_ℚ₂(2) ≅ D₀`.

Citation: **NSW [1], Ch. VII §7.5, Theorem (7.5.11)(ii)** — if `μ_p ⊆ k` then `G_k(p)` is a
Demushkin group of rank `[k:ℚ_p]+2`; for `k = ℚ₂` (`p=2`, `N=1`, `μ_2 = {±1} ⊆ ℚ₂`) this is
rank `1+2 = 3`.  The explicit relation `A²S⁴[S,Y]` is **Labute [2], Theorem 8** at `d = 1` (the
paper's `D₀`); also Serre [3].  Paper: Lemma 3.4 → Prop. 1.1.  `docs/literature-axioms.md` B4.

The `CompactSpace`/`TotallyDisconnectedSpace` instance hypotheses on `AbsGalQ2` mirror
`main_presentation` (Mathlib's `Field.absoluteGaloisGroup` does not yet carry them; open PR). -/
axiom absGalQ2_maxProTwo_presentation
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty (ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0)

/-! ## B7 — the local Euler–Poincaré characteristic

Statement conventions, citation discussion, and the derived stress tests
(`finite_H1`, `card_H1`, …) are in `GQ2/EulerCharacteristic.lean`, which imports this file. -/

/-- **[Classical — B7 (local Euler–Poincaré characteristic).]**  For every finite discrete
`G_ℚ₂`-module `M`, the continuous cohomology groups `Hⁱ(G_ℚ₂, M)` are finite for `i = 0, 1, 2`,
and

  `#H¹(G_ℚ₂, M) = #H⁰(G_ℚ₂, M) · #H²(G_ℚ₂, M) · 2 ^ v₂(#M)`.

Equivalently `χ := #H⁰ · #H² / #H¹ = ‖#M‖_{ℚ₂} = 2 ^ (−v₂(#M))`.

Citation: **NSW [1], Ch. VII §7.3, Theorem (7.3.1) (Tate)** (`χ(k, A) = ‖#A‖_k`); Serre,
*Galois Cohomology*, Ch. II §5.7 Theorem 5; Milne, *ADT* Thm I.2.8.  Paper: §9.2, eq. (145).
See `GQ2/EulerCharacteristic.lean` for conventions and for the (retained-for-faithfulness)
redundancy of the `H⁰`-finiteness clause. -/
axiom absGalQ2_localEulerCharacteristic (M : Type*) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M] :
    Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
      Nat.card (H1 AbsGalQ2 M)
        = Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) * 2 ^ padicValNat 2 (Nat.card M)

end GQ2.Foundations

namespace GQ2.HilbertSymbol

/-! ## B7′ — the dyadic Hilbert-symbol formula

`hilbertSymbol`, `ε`, `ω`, `unit2`, `unitCoe`, `signOf` and their unconditional theory live in
`GQ2/HilbertSymbol.lean`. -/

/-- **B7′ (dyadic Hilbert symbol), `[Classical.]`.**  Writing `a = 2^α u`, `b = 2^β v` with
`u, v ∈ ℤ₂ˣ`, the Hilbert symbol over `ℚ₂` is
`(a, b)₂ = (-1)^{ε(u) ε(v) + α ω(v) + β ω(u)}`.

Citation: **Serre, *A Course in Arithmetic* [CiA], Ch. III §1.2, Theorem 1** (the `p = 2`
case), with `ε, ω` the residue characters of Ch. II §3.3.  This is exactly the paper's
Lemma 3.5 formula for the cup product on `H¹(ℚ₂, μ₂)`.  Convention: `signOf` sends the
`𝔽₂`-valued exponent to `{±1} = ℤˣ`; every element of `ℚ₂ˣ` has the form `2^α u` (`α ∈ ℤ`,
`u ∈ ℤ₂ˣ`), so this determines the symbol on all of `ℚ₂ˣ × ℚ₂ˣ`. -/
axiom hilbertSymbol_dyadic (α β : ℤ) (u v : ℤ_[2]ˣ) :
    hilbertSymbol (unit2 ^ α * unitCoe u) (unit2 ^ β * unitCoe v)
      = signOf (ε u * ε v + (α : ZMod 2) * ω v + (β : ZMod 2) * ω u)

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

/-! ## B3c — the canonical dyadic orientation (cyclotomic interface)

The bundle `DyadicOrientation` — a B4 isomorphism together with the descended cyclotomic
character, normalized to Labute's Theorem 4(2) values on the marked generators — and the
route-(ii) decision with its flagged deviations are in `GQ2/Orientation.lean`; its stress
tests are bundle-parametrized and axiom-free. -/

/-- **The B3c axiom** (composite interface — Labute [2], Théorème 4, case (2): `q = 2`,
`n = 3` odd, `f = 2`).
There is a B4 isomorphism `ψ : G_{ℚ₂}(2) ≅ D₀` and a continuous descent `χ₂` of the cyclotomic
character through `G_{ℚ₂} ↠ G_{ℚ₂}(2)`, surjective (image invariant `{±1} × U₂⁽²⁾ = ℤ₂ˣ`),
with values `(χ(A), χ(S), χ(Y)) = (−1, 1, (−3)⁻¹)` — the paper's `χ_D`-row of eq. (13)
(Lemmas 3.4/3.5).

**Composite classification** (adversarial review 2026-07-04,
`docs/adversarial-axioms-review.md` §3): this is **not** a bare Labute citation.  It bundles
(a) Labute's orientation/classification values, (b) the local-Galois fact that the Demushkin
dualizing character equals the cyclotomic character (through *this* quotient map — Labute Thm 4
does not by itself assert `chiCyc`-compatibility), and (c) the choice of a **normalized** B4
isomorphism realizing (a)+(b) on the marked generators.  Consequently **B3c subsumes a marked
version of B4**: a downstream declaration whose `#print axioms` shows `dyadicOrientation` need
not *also* list B4 in its **Ax** column unless B4 is consumed independently (the review-packet
classification table, `docs/review-packet.md` §2, records this).

Deviation (route (ii), flagged in `GQ2/Orientation.lean`): the *abstract* dualizing
characterization of the canonical character (Labute Prop. 6) is not formalized; the bundle
asserts exactly the interface the paper consumes. -/
axiom dyadicOrientation [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    DyadicOrientation

/-! ## B5 — the local reciprocity bundle

The bundle structure `LocalReciprocity` (with the convention table and the soundness note on
the profinite target of `ν_ur`) is defined in `GQ2/Reciprocity.lean`; its stress tests are
parametrized over an arbitrary bundle and are therefore axiom-free. -/

/-- **The B5 axiom.** Local class field theory for `ℚ₂` provides the reciprocity bundle.

Citation: NSW [1] (7.1.1)/(7.1.5); Serre *Local Fields* [7] Ch. XI–XIII.  Paper: Lemma 3.5,
eq. (13); Prop. 1.1. -/
axiom localReciprocity : LocalReciprocity

/-! ## B6 — local Tate duality (per-`n` bundle, at every finite `k/ℚ₂`)

The dual module `MuDual n M = Hom(M, μₙ)` (conjugation action), the evaluation cup pairing,
the group-parametric bundle `TateDualityG G n` (with `TateDuality n` = the `G_ℚ₂` member), and
the gate `IsLocalDualizingGroup` — with the encoding decisions and flagged deviations (per-`n`
form, `ℤ/n`-valued Pontryagin duals, single currying, unnormalized `inv`) — are defined in
`GQ2/TateDuality.lean`; its stress tests are parametrized over an arbitrary bundle and are
therefore axiom-free.  **Base-generalized 2026-07-06** (census-neutral, B9/B11 pattern;
P-15f7 consumer at `G_K`; `docs/p15f7-axiom-proposal.md`). -/

/-- **The B6 axiom (base-generalized to all finite `k/ℚ₂`).** Local Tate duality at any local
Galois group `G` over `ℚ₂` (`G_ℚ₂` or a finite-index subgroup `G_K`, `K/ℚ₂` finite — the
`IsLocalDualizingGroup` hypothesis): an invariant map `inv : H²(G, μₙ) ≃+ ℤ/n` making the
evaluation cup pairings `Hⁱ(G, Hom(M, μₙ)) × H^{2−i}(G, M) → H²(G, μₙ) ≅ ℤ/n` perfect for every
finite discrete `n`-torsion `G`-module `M`, in the three degree pairs `(0,2)`, `(1,1)`, `(2,0)`.

Base-generalized 2026-07-06 (census-neutral, the B9/B11 pattern): NSW (7.2.6) already states Tate
duality for arbitrary `p`-adic `k`, so the old `ℚ₂`-only form under-used its citation.  The base
member `k = ℚ₂` is the in-repo `def GQ2.tateDuality` below (identity embedding), so every existing
`G_ℚ₂` consumer is unchanged and `#print axioms` traces show `tateDualityAt`.

Citation: **NSW [1], Ch. VII §7.2, Theorem (7.2.6)** (local Tate duality, for any `p`-adic `k`);
Serre, *Galois Cohomology* II §5.2, Theorem 2; Milne, *ADT* I.2.3.  Induced mod-2 Hilbert-pairing
nondegeneracy (the P-15f7 consumer at `G_K`): FV Ch. IV §5 Prop (5.1)(6)/Cor./Thm (5.2), O'Meara
ITQF 63:13.  Paper: §§5–8 (the `𝔽₂` dimension counts), §6.3 (P-15f7);
`docs/literature-axioms.md` B6, `docs/p15f7-axiom-proposal.md`. -/
axiom tateDualityAt (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (n : ℕ) [NeZero n] [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
    (hloc : IsLocalDualizingGroup G n) : TateDualityG G n

/-- **B6 at the base field `ℚ₂`** — the `G = G_ℚ₂` member of `tateDualityAt` (identity embedding,
`isLocalDualizingGroup_absGalQ2`).  An in-repo `def`, not an axiom (census unchanged): every
existing consumer of `GQ2.tateDuality`/`GQ2.TateDuality` is byte-for-byte unaffected. -/
noncomputable def tateDuality (n : ℕ) [NeZero n] : TateDuality n :=
  tateDualityAt AbsGalQ2 n (isLocalDualizingGroup_absGalQ2 n)

/-! ## B8 — the cyclotomic action on peripheral generators (Lemma 3.6)

The concrete group `Δ = maxPro2(FreeProfinite (Fin 2))`, its peripheral generators `P, T, C`, and
the bundle `PeripheralCyclotomicAction` — with the flagged faithfulness deviation (the literal
statement is about the outer action on an étale/anabelian `π₁`, absent from Mathlib) and the pinning
of the exponent embedding `ι` — are defined in `GQ2/PeripheralAction.lean`. -/

/-- **[Composite — B8.]** Local cyclotomic action on the peripheral inertia generators of
`Δ = π₁^{pro-2}(ℙ¹ ∖ {0,1,∞})`: for every `u ∈ ℤ₂ˣ` there is a continuous automorphism `φ_u` of `Δ`
sending each peripheral generator to a cyclotomic conjugate, `φ_u(P) = c_P⁻¹ · P^u · c_P` (and
likewise `T`, `C`), the `u`-th power via ẑ-exponentiation.  This is Lemma 3.6's group-theoretic
conclusion; see `GQ2/PeripheralAction.lean` for the deviation from the literal `π₁` statement.

**This is a composite leaf, not Stix alone** (adversarial review 2026-07-04,
`docs/adversarial-axioms-review.md` §1).  Stix supports that the decomposition group acts on
cuspidal inertia *through the cyclotomic character*; producing an automorphism for **every**
`u ∈ ℤ₂ˣ` — the `aut : ℤ_[2]ˣ → ContinuousMulEquiv Δ Δ` field, quantified over all units —
additionally needs a **cyclotomic-surjectivity** input (a decomposition-group element realizing
each `u`).  That input is available in the census two ways: globally from **B2**
(`cyclotomicCharacter_two_surjective`), and locally from **B5**'s `χ_cyc(rec u) = u⁻¹` with
dense reciprocity image (the machinery P-07 already exercises — `units_gen`/`markedHom_bijective`).
The alternative of *weakening* B8 to quantify only over `u` in the cyclotomic image — deferring
the surjectivity choice to each call site — was considered and **declined** (the downstream
rewrite churn outweighs the ledger gain); B8 keeps the all-units form and this note carries the
dependency.

Citation: **Stix [8], §3.3 + Definition 37** (cuspidal inertia acts through the cyclotomic
character — the paper's exact citation) **+ cyclotomic surjectivity (B2 globally / B5 locally)**;
classical origin Deligne, MSRI 16 (1989).  Paper: Lemma 3.6.  `docs/literature-axioms.md` B8. -/
axiom peripheralCyclotomicAction : PeripheralCyclotomicAction

/-! ## B9 — the Evens/Kahn formula (paper eq. (111)), degrees ≤ 2

The ingredients — degree-1 corestriction `corH1Z`, the index-two Evens norm `evensNormH2Z`
(the paper's two-point graph cocycle (98), Lemma 6.13), and the subgroup Kummer cocycle
`kummerZ1On` — are all *defined* (with full well-formedness proofs) in `GQ2/EvensKahn.lean`;
Stiefel–Whitney classes of the rank-2 transfer forms enter through the paper's fixed
diagonalizations `Tr_{L/k}⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr_{L/k}⟨1⟩ ≃ ⟨2, 2d⟩` (Lemma 6.16), with
`w₁⟨x,y⟩ = [x]+[y]` and `w₂⟨x,y⟩ = [x]∪[y]` in Kummer classes.  The axiom asserts the
degree-1 and degree-2 components of (111) for these representatives.  **Deviations (flagged;
see `GQ2/EvensKahn.lean`)**: truncation to degrees ≤ 2; concrete diagonal representatives
(Delzant well-definedness absorbed into the scoping); the degree-1 component is equivalent to
the classical `cor[a] = [N_{L/k}a]` compatibility. -/

/-- **The B9 axiom** (Kahn Théorème 2 at rank 1, expanded by Evens Theorem 1 / Kozlowski
Thm 1.1 for index 2; paper eq. (111), degrees ≤ 2, at the Lemma 6.16 diagonalizations), over an
arbitrary **finite dyadic base** `k`.

Setting: `k/ℚ₂` finite (an `IntermediateField` of the fixed `ℚ̄₂`, so all classes live over the
subtype group `G_k = k.fixingSubgroup ≤ G_ℚ₂`), `L = k(δ)` with `δ² = d ∈ kˣ`, `G_L = N =` the
stabilizer of `δ` within `G_k` (assumed of index 2 — i.e. `d` is a non-square in `k`), `s ∉ N`,
and `a = u + vδ ∈ Lˣ` with norm `n = u² − dv² ∈ kˣ` and a square root `β = √a ∈ k̄ˣ`.  With
`[x] = kummerClassK k x` the base-general Kummer classes (canonical roots, `GQ2/EvensKahn.lean`),
`∪ = trivialCupPairing`, `cor = corH1` and `N^{Ev} = evensNormH2` (the unbundled T-18 forms; the
Kummer 1-cocycle `α(g) = κ_β(g)` of `a` over `N` enters via its defining equation `hαdef`, with
its hom/continuity side-proofs quantified), the two components of (111) read:

* degree 1: `[2u] + [2dn/u] = [2] + [2d] + cor[a]`;
* degree 2: `[2u] ∪ [2dn/u] = [2] ∪ [2d] + ([2] + [2d]) ∪ cor[a] + N^{Ev}[a]`.

**Base-generality (census amendment, 2026-07-03, user-approved; resolves the P-15 escalation)**:
the cited theorems hold over any field of characteristic `≠ 2` (Kahn Th. 2 requires no local
hypothesis; the dyadic scoping here is a *restriction*), and the paper invokes (111) over the
general base `k` of Lemma 6.16 — the former `k = ℚ₂` scoping was the deviation.  The `k = ℚ₂`
case is the bottom-field instance.

Citation: Kahn, Invent. Math. 78 (1984), Théorème 2 (with Théorème 1); Kozlowski, Proc. AMS
91 (1984), Thm 1.1; Evens, Trans. AMS 108 (1963), Thm 1.  Paper: §6, eq. (111),
Lemmas 6.13/6.16.  `docs/literature-axioms.md` B9. -/
axiom evensKahn_dyadic
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
    ∧ (trivialCupPairing 2 k.fixingSubgroup htriv
          (kummerClassK k (twoUnit k * u)) (kummerClassK k (twoUnit k * d * n * u⁻¹))
      = trivialCupPairing 2 k.fixingSubgroup htriv
          (kummerClassK k (twoUnit k)) (kummerClassK k (twoUnit k * d))
        + trivialCupPairing 2 k.fixingSubgroup htriv
            (kummerClassK k (twoUnit k) + kummerClassK k (twoUnit k * d))
            (corH1 htriv hUo hidx hs α hα hαc)
        + evensNormH2 htriv hUo hidx hs α hα hαc)

/-! ## B10 — the tame quotient of `G_ℚ₂` (Iwasawa)

The bundle `TameQuotientData` (closed normal pro-2 `W` + `G_ℚ₂/W ≅ T_tame`), the NSW
convention notes (arithmetic-vs-geometric Frobenius, `σ ↦ σ⁻¹`), and the flagged deviation
(no ramification theory: `W` is characterized, not constructed; its **maximality** — paper
Lemma 3.3 — is deliberately *not* asserted here, it stays a theorem obligation of P-09) are
in `GQ2/TameQuotient.lean`.  Added by explicit census decision (P-06 escalation): the step-1
census was 2-centric and did not cover the prime-to-2 tame structure. -/

/-- **[Classical — B10 (oriented form, B10′).]**  The tame quotient of `G_ℚ₂`, *oriented
against local reciprocity*: a closed normal pro-2 subgroup `W ≤ G_ℚ₂` (wild inertia) with
`G_ℚ₂/W ≅ T_tame = ⟨σ, τ ∣ τ^σ = τ²⟩_prof`, whose unramified coordinate `ν_t` matches B5's
reciprocity normalization — `ν_t(tameF(rec u)) = 1` for units `u` and
`ν_t(tameF(rec 2)) = ztwoOne⁻¹` (arithmetic Frobenius, geometric coordinate).

Citation, existence: **NSW [1], Ch. VII §7.5, Theorem (7.5.3) (Iwasawa)** — `G(k_tr|k)` is the
profinite group on `σ, τ` with the single relation `στσ⁻¹ = τ^q` (`q = 2`); with
**(7.5.2)** (split extension `1 → Ẑ^{(p′)}(1) → G(k_tr|k) → Γ → 1`) and `G(k̄|k_tr)`
pro-`p` (Serre, *Local Fields* [7], Ch. IV).  Citation, orientation clauses:
**Neukirch, *Algebraic Number Theory* (Grundlehren 322), Chap. V, Theorem (6.2)** (norm residue symbol maps
`U_K^{(n)}` onto the upper-numbering ramification groups; `n = 0`: units ↦ inertia, so prime
elements ↦ Frobenius lifts) with **Chap. V, (1.2)** / NSW [1] (7.1.2)(i) (units are norms in
unramified extensions).  (All verified against the PDFs in `references/`; the
Frobenius-direction convention `σ = geometric` and the clause encoding are documented at
`OrientedTameQuotient` in `GQ2/TameQuotient.lean`.)

History: added census 10→11 as the unoriented `TameQuotientData` (P-06 escalation);
**strengthened in place to the oriented form (census unchanged) 2026-07-06** (P-25 escalation,
user-approved) — the orientation discharges `tame_reciprocity` (`docs/p25-tame-reciprocity-plan.md`),
whose derivation from B5's `norm_reciprocity` alone is blocked by the absence of local
ramification theory for `Field.absoluteGaloisGroup` in Mathlib.  Paper: Prop. 3.2 local side +
Prop. 3.14 / Cor. 3.12 (the "same natural unramified character").
`docs/literature-axioms.md` B10. -/
axiom tameQuotient : OrientedTameQuotient localReciprocity

/-! ## B11 — the dyadic norm criterion over finite bases (split into named leaves, P-23)

Added by the same explicit census decision as B9's base-generalization (2026-07-03,
user-approved; resolves the P-15 escalation): §6.3's local ledger — Lemma 6.16's step-2
arithmetic and Lemma 6.17's (94)-orthogonality — runs over arbitrary finite dyadic bases.

**P-23 split (2026-07-04, user-approved census change 12→13; adversarial review rec 2).**  The
old single `axiom dyadicNormCriterion` bundled two classical facts with one project convention.
It is now factored into the two classical leaves below plus one isolated, plainly-labelled
convention `def`, and re-derived as a **same-name `theorem`** — so every downstream `.1`/`.2`
projection is byte-for-byte unchanged (zero consumer churn):

* `hilbertSymbol_normCriterion_finiteDyadic` — the symbol/norm criterion (classical).
* `unramifiedQuadratic_units_are_norms` — units of an unramified quadratic extension are norms
  (classical).
* `IsUnramifiedQuadraticSpectral` — **not an axiom**: the repo's spectral-norm *working
  definition* of "`k(δa)/k` is unramified" (equal norm value groups on `ℚ̄₂`).  Isolated here as
  the review's "riskiest piece": it is a project convention, not a Mathlib unramifiedness notion,
  and is deliberately a `def` (asserting nothing) rather than a bridge axiom.

Encoding conventions carried over from the pre-split axiom: the "`b` is a norm from `k(√a)`"
condition is the **norm form** `b = x² − a y²` (elementary, no relative field-extension
plumbing); unramifiedness by **equal norm value groups** through the spectral norm on `ℚ̄₂` (the
`GQ2/SectionSix.lean` `IsDeepUnit`/`lemma_6_16` convention).

Note for reviewers: the Steinberg relation `[x]∪[1−x] = 0` and `[2]∪[−1] = 0` used in
Lemma 6.16's proof are *consequences* of the criterion clause (norm representations
`1 − x = 1² − x·1²` and `−1 = 1² − 2·1²`), so they are deliberately not separate clauses.

Citation: Serre, *Local Fields* [7], Ch. XIV §2 (the symbol–norm criterion; over `ℚ_p` also
CiA [CiA] Ch. III §1.1 Prop. 1) and Ch. V §2 (norms of unramified extensions are the units
times the norms of uniformizers).  *(Citation display numbers pending PDF verification —
flagged for P-20.)*  Paper: §6.3, displays (93)/(94) and Lemma 6.16's proof. -/

/-- **[Project convention — isolated spectral-norm bridge, P-23.]**  The repo's working
definition of "`k(δa)/k` is unramified", encoded via the spectral norm on `ℚ̄₂`: every nonzero
`z = x + y·δa` (`x, y ∈ k`) has the same norm as some nonzero element of the base `k` — i.e.
`k(δa)` and `k` have equal norm value groups.  This is **not** a Mathlib unramifiedness notion
and is asserted by nothing (it is a `def`, not an axiom); it is the convention the §6 ledger
consumes, named and isolated per adversarial review rec 2 so a human reviewer can see exactly
where the project departs from a directly citable statement. -/
def IsUnramifiedQuadraticSpectral
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    (δa : AlgebraicClosure ℚ_[2]) : Prop :=
  ∀ z : AlgebraicClosure ℚ_[2], z ≠ 0 →
    (∃ x y : ↥k, z = (x : AlgebraicClosure ℚ_[2]) + (y : AlgebraicClosure ℚ_[2]) * δa) →
    ∃ w : ↥k, w ≠ 0 ∧ ‖z‖ = ‖(w : AlgebraicClosure ℚ_[2])‖

/-- **[Classical — B11a.]**  The dyadic Hilbert-symbol **norm criterion** over a finite base
`k/ℚ₂`, in Kummer-cup form: for `a, b ∈ kˣ`, `[a] ∪ [b] = 0` in `H²(G_k, 𝔽₂)` iff `b` is a norm
from `k(√a)` — iff `b = x² − a y²` has a solution in `k` (for `a` a square the norm form is
universal, so no non-square hypothesis is needed).

Citation: Serre, *Local Fields* [7], Ch. XIV §2 (over `ℚ_p` also CiA Ch. III §1.1 Prop. 1). -/
axiom hilbertSymbol_normCriterion_finiteDyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    ∀ a b : (↥k)ˣ,
      trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k b) = 0
        ↔ ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2

/-- **[Classical — B11b.]**  **Unramified unit-norm surjectivity**: if `k(√a)/k` is unramified
(the `IsUnramifiedQuadraticSpectral` convention on a chosen root `δa`, `δa² = a`), then every
unit of `k` (`‖u‖ = 1`) is a norm from `k(√a)` — i.e. `u = x² − a y²` is solvable in `k`.

Citation: Serre, *Local Fields* [7], Ch. V §2 (norms of unramified extensions are the units times
the norms of uniformizers). -/
axiom unramifiedQuadratic_units_are_norms
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (a : (↥k)ˣ) (δa : AlgebraicClosure ℚ_[2])
    (hδa : δa ^ 2 = ((a : ↥k) : AlgebraicClosure ℚ_[2]))
    (hunram : IsUnramifiedQuadraticSpectral k δa) :
    ∀ u : (↥k)ˣ, ‖((u : ↥k) : AlgebraicClosure ℚ_[2])‖ = 1 →
      ∃ x y : ↥k, (u : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2

/-- **B11 (re-derived, P-23).**  The pre-split `dyadicNormCriterion` interface, now a
**theorem** with a byte-for-byte unchanged statement so every downstream consumer's `.1`/`.2`
projection is untouched.  It rests on exactly the two classical leaves
`hilbertSymbol_normCriterion_finiteDyadic` + `unramifiedQuadratic_units_are_norms` (plus the
isolated `IsUnramifiedQuadraticSpectral` convention, which is a `def`, not an axiom). -/
theorem dyadicNormCriterion
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    (∀ a b : (↥k)ˣ,
      trivialCupPairing 2 k.fixingSubgroup htriv (kummerClassK k a) (kummerClassK k b) = 0
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

/-! ## B12/B13 — the deep-half Kummer-count leaves  (P-15f1)

Added by explicit census decision (**P-15f1 instantiation**, user-approved 2026-07-06,
census 13 → 15; proposal and precise-citation record: `docs/p15f1-axiom-proposal.md`).
Lemma 6.17's dimension clause is reduced (P-15f1 Layers 1–2b, all std-3, in
`GQ2/LocalKummer.lean`) to constructing one `DeepKummerData` instance; its literature
content is exactly **local Kummer theory** (B12) and the **unit-filtration graded structure**
(B13).  Everything else in the instance is *proved*, not assumed: `H^{1,2}(H_V, V) = 0` via
coprime averaging (Brown [5] III (10.2)), the square-class graded computation, the Hensel top
(`sq_of_near_one`, P-15e), `−1 ∈ U^{(e)}`, the graded duality, Lemma 6.10, and — separately,
as paper content — Lemma 6.11 projectivity for the deep-count multiplicativity. -/

/-- **The B12 axiom (local Kummer theory, surjective half).**

For a finite extension `k/ℚ₂`, the Kummer class map descends to an isomorphism
`k^×/(k^×)² ≅ H¹(G_k, ℤ/2)` (continuous cochain cohomology; `μ₂ ≅ ℤ/2`, canonical in
char 0).  **Only surjectivity is assumed** — injectivity is proved
(`Kummer.kummerClass_eq_zero_iff`: `[a] = 0 ↔ IsSquare a`, via Mathlib's infinite Galois
correspondence), so this leaf is strictly weaker than the literature statement.

Citation: **NSW [1], Ch. VI §2 — Theorem (6.2.1) (Hilbert's Satz 90) and the Kummer-sequence
isomorphism `H¹(G_K, μ_n) ≅ K^×/K^{×n}` displayed immediately after it (electronic ed.
p. 344), dual form Theorem (6.2.2)**; at `n = 2`.  Secondary: Serre, *Local Fields* [7],
Ch. XIV §2 (p. 206) — "the map `a ↦ χ_a` defines an isomorphism of `K*/K*ⁿ` onto the group
of those characters of `G` having order dividing `n`" (construction from Ch. X §3).  Both
verified verbatim against the `references/` PDFs.

Deviations (flagged, review-packet §3): surjectivity-only; the `IntermediateField`-subtype
flavor with canonical roots (`sqrtCl`) is B9's `kummerClassK` input shape (root-independence
is T-13's `kummerCocycleFun_root_indep`, proved).  Discharge note: provable-with-effort via
completing the square + the Krull–Galois correspondence; the leaf can later become a theorem
without consumer churn (B11 precedent).

Paper: §6.3 (Lemma 6.17, "By Hochschild–Serre and Kummer theory").
`docs/literature-axioms.md` B12. -/
axiom kummerClassK_surjective (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    Function.Surjective (kummerClassK k)

/-- **The B13 axiom (dyadic unit filtration).**

Every finite extension `k/ℚ₂` carries a `DyadicUnitFiltration` (`GQ2/UnitFiltration.lean`):
a uniformizer `π` (an element of maximal spectral norm `< 1` — discreteness of the value
group), the normalization `‖2‖ = ‖π‖^e` (`e = v_k(2) ≥ 1`), a residue degree `f ≥ 1`, and
the graded counts of the unit filtration `U^{(i)} = 1 + 𝔭_k^i`:
`#(U^{(0)}/U^{(1)}) = 2^f − 1` and `#(U^{(i)}/U^{(i+1)}) = 2^f` for `i ≥ 1`.

Citation: **Serre, *Local Fields* [7], Ch. IV §2, Proposition 6** (verified verbatim against
the `references/` scan, pp. 66–67): "(a) `U_L/U_L^{(1)} = L̄^*`; (b) for `i ≥ 1`, the group
`U^{(i)}/U^{(i+1)}` is canonically isomorphic to `𝔭_L^i/𝔭_L^{i+1}`, which is itself
isomorphic (non-canonically) to the additive group of the residue field `L̄`" — read through
`#L̄ = 2^f`, `#L̄^× = 2^f − 1`.  Uniformizer existence: Serre LF Ch. I–II (discrete
valuations, complete fields; standard).

Deviations (flagged, review-packet §3): stated in spectral-norm vocabulary (no valuation
ring/residue field is constructed — the graded pieces enter through their cardinalities, the
form the multiplicity count consumes); the proposal's (F2) inertia-twist clause
(`θ_g = (g•π)/π` acting on `gr_j` by `θ_g^j`) was found **derivable** during statement design
(exact `ℚ̄₂`-algebra + the `he` normalization) and is deliberately NOT a field — it will be
proved in-repo (`docs/p15f1-axiom-proposal.md`, B13 entry note).

Paper: §6.3, eq. (93) (the display's own bracket "[7, Ch. XIV §§2–3]" is coarse — the
filtration is Ch. IV §2).  `docs/literature-axioms.md` B13. -/
axiom dyadicUnitFiltration (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] :
    DyadicUnitFiltration k

end GQ2
