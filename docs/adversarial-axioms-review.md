# Adversarial review: `GQ2/Foundations/Axioms.lean`

Date: 2026-07-04.  Scope: review of the literature axioms in
`GQ2/Foundations/Axioms.lean`, with emphasis on whether the Lean statements match the cited
results.  Existing files were not edited.

This is a historical review snapshot, not a current status report. Its two operational findings
were resolved after the review: unused B2 was deleted, and the repository now has zero `sorry` with
`scripts/check_axioms.sh` passing. The discussion of encoded/composite interfaces—especially B8,
B10′, and the dyadic norm inputs—remains relevant. Current names, statements, and citations are in
[`literature-axioms.md`](literature-axioms.md); the live trust base is generated in
[`../atlas-audit.md`](../atlas-audit.md).

## Executive findings

### 1. B8 silently absorbs cyclotomic surjectivity

`peripheralCyclotomicAction` is stated for every `u : ℤ_[2]ˣ`:

```lean
aut : ℤ_[2]ˣ → ContinuousMulEquiv Delta Delta
hP : ∀ u, aut u deltaP = conjP (deltaP ^ᶻ ι u) (cP u)
...
```

The Stix citation supports the statement that the decomposition group acts on cusp inertia
through the cyclotomic character.  It does not, by itself, produce an automorphism for every
2-adic unit; that requires a surjectivity input for the relevant cyclotomic character.  The
project had B2, but B8 was axiomatized as a standalone bundle and the development board already
showed that B2 was unused.

Risk: the B8 axiom is stronger than its displayed citation.  It is probably true after adding
the cyclotomic surjectivity input, but the ledger should say so explicitly, or B8 should be
weakened to quantify over the cyclotomic image.

Relevant code:
- `GQ2/PeripheralAction.lean`, `PeripheralCyclotomicAction`
- `GQ2/Foundations/Axioms.lean`, B8
- `docs/orchestration/tickets.md`, historical P-08 row

### 2. B11 is the least citation-faithful axiom

`dyadicNormCriterion` combines two classical facts over every finite dyadic base:

1. Kummer-cup vanishing iff the norm-form equation `b = x² - a y²` has a solution.
2. If the chosen quadratic extension is unramified, encoded as equality of value groups via
   the spectral norm on `ℚ̄₂`, then every unit is represented by that norm form.

The underlying mathematics is standard, but the Lean axiom is not just Serre's norm criterion.
It bakes in:

- the repo's concrete `k.fixingSubgroup` continuous cohomology,
- `kummerClassK`,
- `trivialCupPairing`,
- the additive zero in `H²(G_k, 𝔽₂)`,
- and the repo-specific "unramified = equal spectral-norm value groups" proxy.

The docstring itself says the citation display numbers are pending PDF verification.  That is
not good enough for a foundation axiom that now feeds §6.

Risk: moderate.  I do not see an obvious false clause, but this is a composite theorem with
several translation layers.  It should either be split into smaller axioms or documented with
an explicit proof bridge from Serre's Hilbert symbol/norm theorem to this exact Lean statement.

Relevant code: `GQ2/Foundations/Axioms.lean:367`.

### 3. B3c is a deliberate strengthening of B4 and should be treated as the real Demushkin axiom

`dyadicOrientation` packages not merely Labute's orientation values, but the existence of a
B4 isomorphism normalized so that the descended cyclotomic character has specified values on
the selected generators:

```lean
equiv : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0
chiTwo_factors : ∀ g, chiTwo (maxProPMk 2 AbsGalQ2 g) = chiCyc g
surjective_chiTwo : Function.Surjective chiTwo
chi_A, chi_S, chi_Y
```

This is probably the interface the paper uses, and the deviation is documented.  But it means
B3c subsumes a marked version of B4 plus compatibility with the local cyclotomic character.
Labute's Theorem 4 is about the canonical character after a classified presentation; it does
not by itself assert compatibility with Mathlib's `chiCyc` through this particular quotient map.
That compatibility is local Galois theory plus the identification of the canonical orientation
with the cyclotomic character.

Risk: acceptable if documented as a composite axiom, not as a bare Labute citation.

Relevant code:
- `GQ2/Orientation.lean:66`
- `GQ2/Foundations/Axioms.lean:201`

### 4. B2 is true but no longer looks like a minimal leaf

B2 states global surjectivity:

```lean
Function.Surjective (cyclotomicCharacter (L := AlgebraicClosure ℚ) 2)
```

Washington's finite cyclotomic theorem supports this statement.  The issue is ledger hygiene:
the paper's local uses are now apparently covered by B3c/B5/B8, and P-08 says B2 was not needed.
If B2 remains in the foundation census, the docs should say it is currently unused or remove it
from the minimal list.

Risk: low for soundness, medium for audit clarity.

Relevant code: `GQ2/Foundations/Axioms.lean:102`.

### 5. The axiom guard failed in the reviewed snapshot

Running `scripts/check_axioms.sh` reports:

```text
FAIL: sorry outside the allowlist:
GQ2/WF72.lean:239:    sorry
```

`GQ2/WF72.lean` is not imported by `GQ2.lean`, so this is not necessarily in the built library.
But it meant the advertised hygiene check was not green in that worktree. `WF72.lean` is not part
of the completed library and the present repository-wide guard passes.

Risk: process/tooling, not mathematics.  Fix either by importing/tracking the file deliberately,
removing it, or updating the docs to say it is scratch/untracked.

## Axiom-by-axiom notes

### B1: topological finite generation of `G_ℚ₂`

Lean statement:

```lean
∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤
```

This matches the finite-generation consequence of NSW VII (7.5.14), and is exactly the
predicate consumed by reconstruction.  No issue found.

### B4: `G_ℚ₂(2) ≅ D0`

The high-level theorem is supported by NSW VII (7.5.11) plus the explicit odd-degree dyadic
relation in Labute/Serre.  I checked the NSW text around (7.5.11): for `μ_p ⊆ k`, `G_k(p)` is a
Demushkin group of rank `N + 2`; for `k = ℚ₂`, this is rank 3.  NSW also records the special
`p = 2`, `p^s = 2`, odd `N` relation, giving the three-generator relation for `ℚ₂`.

The repo's `D0` is the maximal pro-2 quotient of the full profinite one-relator presentation,
not literally a free pro-2 presentation.  That looks mathematically equivalent to the intended
pro-2 presentation, and the file documents why the full profinite presentation alone would be
too large.

### B5: local reciprocity bundle

The direction and normalizations are plausible:

- `recip : ℚ₂ˣ →* G_ℚ₂^ab` with dense image,
- finite abelian norm kernels,
- `ν_ur ∘ rec = -v₂`,
- `χ_cyc(rec(u)) = u⁻¹` on units and `χ_cyc(rec(2)) = 1`.

These match the paper's Lemma 3.5 conventions.  The target `Multiplicative ℤ₂` for `ν_ur` is a
good correction; a discrete `ℤ` target would be wrong for a continuous map out of a compact
group.

No blocking issue found.

### B6: local Tate duality

The per-`n` formulation is a faithful specialization of NSW VII (7.2.6), modulo the documented
choices:

- finite `n`-torsion modules only,
- duals encoded as `Hom(-, ZMod n)`,
- one currying direction,
- unnormalized invariant map.

This is stronger than just cardinality duality but within the standard theorem.  No issue found.

### B7: Euler characteristic

The formula

```lean
#H¹ = #H⁰ * #H² * 2 ^ padicValNat 2 (#M)
```

matches `χ = #H⁰ #H² / #H¹ = ‖#M‖₂ = 2^{-v₂(#M)}` for `ℚ₂`.  Since `char(ℚ₂)=0`, NSW's
"order prime to char" restriction is vacuous for finite modules.  No issue found.

### B7': dyadic Hilbert symbol

The formula agrees with Serre's standard dyadic Hilbert-symbol formula, and the local stress
test `(-1,-1)₂ = -1` checks the most important sign convention for the paper's initial form.
I could not text-extract the local copy of *A Course in Arithmetic* with `pdftotext`, so this
specific check was against project docs plus known formula, not a fresh line-local PDF quote.

### B9: Evens/Kahn formula

The Kahn PDF does contain the advertised formula
`w(T(q)) = N'(w(q)) · w(T(1))^r`.  The Lean axiom is a specialized, degree ≤ 2, diagonalized
version of the paper's equation (111).  That is a documented deviation.

The main review concern is not falsehood but complexity: the axiom is no longer a single
published theorem.  It is Kahn plus the paper's trace-form diagonalizations plus this repo's
Kummer/corestriction/Evens-normalization choices.  Keep the deviation table prominent.

### B10: tame quotient

NSW VII (7.5.3) states the tame quotient presentation with relation `σ τ σ⁻¹ = τ^q`.  The repo
uses the paper's geometric convention `τ^σ = τ²` with `x^g = g⁻¹ x g`.  The convention note
explaining `σ ↦ σ⁻¹` is important and should stay.  No issue found.

## Recommended next fixes

### 1. Resolve B8's hidden surjectivity dependency

Best resolution: make the dependency explicit instead of letting the Stix citation carry more
weight than it should.

Possible routes:

- Keep `PeripheralCyclotomicAction` as currently stated, but document B8 as **Stix plus
  cyclotomic surjectivity**.  In that case, the axiom ledger should say B8 depends on the
  cyclotomic-surjectivity input, or the B2 content should be folded into B8's citation story.
- Weaken B8 so it only quantifies over `u` lying in the image of the relevant cyclotomic
  character.  Downstream lemmas that need arbitrary `u : ℤ_[2]ˣ` would then explicitly invoke
  B2, B3c, or B5 to choose a preimage.
- If the downstream proofs only need a smaller collection of powers, introduce a smaller
  interface for exactly those powers.

Preference: weaken B8 to the cyclotomic-image form if the downstream rewrite is manageable.  If
that churn is too large, keep the current bundle but update the ledger so B8 is no longer cited as
"Stix alone".

### 2. Split or proof-bridge B11

B11 should not remain one large "Serre says this" axiom.  Split it into smaller named leaves, or
add a dedicated bridge document proving that the exact Lean statement follows from standard local
field facts.

Suggested split:

- `hilbertSymbol_normCriterion_finiteDyadic`:
  `[a] ∪ [b] = 0 ↔ b = x² - a y²`.
- `unramifiedQuadratic_units_are_norms`:
  an unramified quadratic extension has all base-field units in its norm image.
- Optional bridge:
  the repo's spectral-norm equal-value-group condition implies the extension is unramified, or is
  otherwise exactly the unramifiedness condition consumed by §6.

That last bridge is the riskiest piece.  If it is only a project convention, isolate it and say so
plainly.  This would make the actual classical facts much easier for a human reviewer to check.

### 3. Reclassify B3c as a composite interface

Do not present B3c as only "Labute Theorem 4".  It should be documented as:

```text
Labute classification/orientation values
+ local fact that the Demushkin dualizing character equals the cyclotomic character
+ choice of a normalized B4 isomorphism.
```

Possible cleanup:

- Rename or describe the leaf as `dyadicOrientationInterface`.
- Say explicitly that it subsumes a marked version of B4 plus extra cyclotomic compatibility.
- Where downstream declarations consume B3c, avoid also listing B4 unless B4 is independently
  used.

### 4. Decide B2's role

Either remove B2 from the minimal axiom list if no declaration consumes it, or keep it with an
honest label such as "available but currently unused / intended for B8 elimination".

The reviewed state was confusing: B2 was presented as a theorem the proof rested on, while the
development history said it was unnecessary. B2 was subsequently removed from the census.

### 5. Fix the axiom-hygiene failure

In the reviewed worktree, `scripts/check_axioms.sh` failed because `GQ2/WF72.lean` contained a
non-allowlisted `sorry`.

Reasonable outcomes:

- If `WF72.lean` is scratch, move it out of `GQ2/` or document a deliberately ignored scratch area.
- If it is real project work, import it from `GQ2.lean` and add it to the proof/sorry ledger.
- If it is obsolete, delete it after checking that no active Claude Code workflow depends on it.

Short-term, treat the guard failure as real.  A failing axiom guard undermines the audit story even
if the main build is unaffected.

### 6. Add a composite-axiom classification table

For review clarity, classify the leaves by how directly they match a published statement:

- Direct classical theorem: B1, B6, B7, B7', B10.
- Classical theorem plus encoding choices: B4, B5, B9.
- Composite/project interface: B3c, B8, B11.
- Unused or auxiliary: B2, if it remains unused.

This distinction would prevent a reviewer from mistaking "nearby true theorem" for "this exact Lean
interface appears verbatim in the cited literature."
