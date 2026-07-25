# L-campaign scoping: discharging `BLabHypothesis` by a Lean proof (ticket L0)

**Date**: 2026-07-25 · **Author**: Fable (L0 scoping worker) · **Status**: for owner review —
no L-ticket dispatches before sign-off (board `roe-tickets.md` §L-campaign).

**Charter.** The owner has declined the B-Lab literature axiom (plan §3 Route L step 4; R14
cancelled). The fat-tail clause of `roe-verification-plan.md` §3 is live: the campaign must
*prove* the statement it wanted to assume. This memo scopes that proof: the exact minimal
theorem, the recommended route tensioned against the sources, the asset map, a phased ticket
decomposition in house style, effort estimates, risks, the first de-risking spike, and
smaller-than-B-Lab middle-path options for the owner.

---

## 1. The exact minimal theorem

**Deliverable statement — verbatim the existing interface** (`GQ2/Roe/MarkedPro2.lean`,
`section Draft`):

```lean
theorem bLab : BLabHypothesis
-- where
def BLabHypothesis : Prop :=
  IsDemushkin 2 (DR : Type) →
    demushkinRank 2 (DR : Type) = 3 →
      demushkinQ (DR : Type) = 2 →
        (∃ χ : (DR : Type) →* ℤ_[2]ˣ,
          Continuous χ ∧ IsLabuteOrientation χ ∧ Function.Surjective χ) →
          Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type))
```

Consumers (R15 `markedPro2_R`, R32 capstone) stay hypothesis-parametrized until `bLab` lands,
then are discharged by a one-line application — exactly the interface-stability discipline the
R14 memo prescribed for the axiom flip, now applied to a theorem. **No statement changes
anywhere.**

**D_R-specialized, not abstract-G — recommendation: keep the draft's choice.** The R7 design
memo (§R14, design choice 1) already argued this for the axiom; for a *proof* the case is
stronger still:

* `IsLabuteOrientation` is defined through D_R's presentation (`CrossedDerivation.lean`); an
  abstract-G statement needs either bundled presentation data (then it quantifies over
  presented pro-2 groups *with this same relator* — no more general in practice) or the
  abstract dualizing-module characterization, i.e. the deferred route (i) of
  `GQ2/Orientation.lean` — a separate multi-week development that **no consumer needs**.
* The honest mathematical content of the instance is: *the concrete relators
  `r₂ = (x^s)⁻¹x⁻³y²[y,y^s]` and `r₀ = A²S⁴[S,Y]` present isomorphic pro-2 groups.* Both
  groups are already constructed and presented in-tree (`DRPresentation.lean`,
  `DyadicPresentation.lean`); a proof may freely use both presentations and the pinned
  orientation values. Abstracting G would forbid exactly the assets that make the proof
  tractable.
* The four antecedents are all **landed theorems** (R11: `chiR`, `isLabuteOrientation_chiR`,
  `chiR_surjective`; R12/R13b: `isDemushkin_DR`, `demushkinRank_DR`, `demushkinQ_DR` — H²
  half in re-dispatched R13b). Inside the proof they serve as conveniences, not gates: via
  `isLabuteOrientationDatum_solution` the χ-hypothesis pins `(S, X, Y)` to the Hensel root
  `X ≡ 5 (mod 16)`, `S = −X³/(X²+X+1)`, `Y = −X²` — the concrete data the low-stage analysis
  consumes.

**Is the honest instance much smaller than the general odd-rank/q=2 case? Verdict: yes,
substantially — with one irreducible core.** What specialization removes:

1. No abstract Demushkin structure theory: both groups arrive presented, so the general
   "every Demushkin group is one-relator" step (relation-module rank 1 from dim H² = 1) is
   not needed.
2. No case analysis over `(n, q, Im χ)`: a single target normal form; no other families, no
   completeness ("every invariant tuple occurs"), no distinctness ("different tuples give
   non-isomorphic groups" — B-Lab never asserted it and no consumer uses it).
3. No Théorème 4 intrinsic content: the orientation enters as the **descent
   characterization**, which is a *definition* in-tree (`IsLabuteOrientationDatum`), with its
   D_R-instance solved and unique (`CrossedDerivation.lean`, sorry-free; R10/R11).
4. Rank 3 kills the symplectic induction over hyperbolic pairs `[x₄,x₅]⋯[x_{n−1},x_n]` in the
   general odd-rank proof: one distinguished generator + one hyperbolic pair, no recursion
   over rank.

What specialization does **not** remove: the per-level lifting induction over the full pro-2
tower ("successive approximation"). The R2 spike proved this is irreducible: no finite-word
identification exists in either direction, marked or unmarked (norm/rationality obstruction on
χ-values: word-values on the D_R side lie in the cubic field ℚ(X) with norms ±4^ℤ while `η`
has norm −1/27; D₀-side word-values are rational while `X` is cubic-irrational), and the
forced congruence data grows without bound (spike §2.5: exponent sums ~2^(k−3) at depth k).
Any honest proof constructs a genuine limit. The whole design question is *which* limit
construction is cheapest in this codebase — §2.

---

## 2. Recommended route: levelwise two-sided lifting ("Route L2", König + Hopfian)

### 2.1 The skeleton

Let `λₖ(G)` be the (closed) lower 2-central series, `λ₁ = G`, `λₖ₊₁ = cl(λₖ²[λₖ, G])`. For a
topologically f.g. pro-2 group each `λₖ` is open, each `G/λₖ` a finite 2-group, and the tower
is a neighborhood basis of 1 (§2.4, Tier F). Define for each k the finite sets

```
S⁰ₖ = { m : Fin 3 → D_R/λₖ(D_R) | d0Word m = 1 ∧ triple generates }   (D₀-relator triples)
Sᴿₖ = { m : Fin 3 → D₀/λₖ(D₀)  | drWord m = 1 ∧ triple generates }   (r₂-relator triples)
```

(`drWord`/`d0Word` are the in-tree word shapes; a triple killing the relator = a hom out of
the presented group, by `drLiftHom`/`d0LiftHom`; generation mod λₖ = surjectivity.) Then:

1. **Levelwise nonemptiness** (the mathematical core): `∀ k, S⁰ₖ ≠ ∅` and `∀ k, Sᴿₖ ≠ ∅`,
   by induction on k — base cases by explicit witnesses (§2.3), inductive step by the **stage
   lemma** (§2.2).
2. **Compactness assembly**: the restriction maps `S⁰ₖ₊₁ → S⁰ₖ` exist (relator-kill and
   surjectivity both project); an inverse system of nonempty finite sets has a nonempty limit.
   The in-tree König machinery does exactly this: `GQ2/Reconstruction.lean` —
   `konigFunctor` (line 185), `nonempty_sections_of_finite_cofiltered_system` (mathlib),
   and the Cantor-intersection realization inside `exists_contSurj_of_card_le` (line 213)
   which turns a compatible family of finite-level surjections into a
   `ContSurj S R`. The card-≤ hypothesis of that lemma enters **only** through
   levelwise nonemptiness (`contSurj_quotient_nonempty_finite`, line 119), so an
   `exists_contSurj_of_levelwise_nonempty` variant is a small refactor reusing the proof
   verbatim. (Levelwise sets over the λ-tower suffice for all open normal U: the tower is a
   neighborhood basis, so any `D_R/U` is a further quotient of some `D_R/λₖ`.)
   Result: continuous epis `φ : D₀ ↠ D_R` and `ψ : D_R ↠ D₀`.
3. **Endgame**: `ψ ∘ φ : D₀ ↠ D₀` is a surjective endo of a topologically f.g. profinite
   group, hence injective (`profinite_hopfian`, Reconstruction.lean:76, proven); so `φ` is
   injective, so bijective, so `continuousMulEquivOfBijective` (line 44) yields
   `ContinuousMulEquiv D_R D₀` (up to symm). This is byte-for-byte the endgame of the proven
   `reconstruction_of_equinum` (line 319). F.g. hypotheses: `dr_topGen`
   (`DRAbelianization.lean:132`) and `topGen_d0` (`DyadicNielsen.lean:47`).

No Aut(F₃-pro-2) API, no noncommutative infinite products (absent from mathlib — inventory
§9), no sequential convergence, no new continuous-cohomology exact sequences. Every
convergence-flavored step is either in-tree or a mathlib König lemma.

### 2.2 The stage lemma — the irreducible core, stated honestly

Fix the D₀ → D_R direction (the other is symmetric with the roles of the relators swapped).
Write `Qₖ = D_R/λₖ`, `Zₖ = λₖ/λₖ₊₁` (finite elementary abelian, central in `Qₖ₊₁`).

* **Defect is well-defined.** Given `T ∈ S⁰ₖ`, lift each coordinate arbitrarily to `Qₖ₊₁`;
  the defect `δ(T) := d0Word(lift) ∈ Zₖ` is independent of the lifts: for central `z` with
  `z² = 1`, `(az₁)² = a²`, `(sz₂)⁴ = s⁴`, `[sz₂, yz₃] = [s,y]` — all relator exponent sums
  are even and commutators absorb central factors. (Same computation for `r₂`:
  exponent sums `(0, −4, 2)`.) This is the q = 2 pathology: **first-order corrections cannot
  move the defect**, so lifting is genuinely a second-order problem — this is where the
  classification's actual content lives, and why the induction cannot be a soft argument.
* **`T` lifts to `S⁰ₖ₊₁` iff `δ(T) = 0`** (generation mod λₖ₊₁ is free: the triple covers
  `Qₖ₊₁/Φ(Qₖ₊₁)` since `Zₖ ⊆ λ₂(Qₖ₊₁) = Φ`; Burnside-basis argument, in-tree patterns
  `FrattiniNongen.lean` / R11's index-2 argument).
* **Second-order modification calculus.** Changing `T` itself by `w = (w₁,w₂,w₃)`,
  `wᵢ ∈ λₖ₋₁/λₖ₊₁-range` (which preserves membership in `S⁰ₖ`), shifts the defect by,
  modulo `λₖ₊₁` (k ≥ 3; signs/order to be fixed by the calculus ticket):

  ```
  δ(T·w) · δ(T)⁻¹  ≡  w₁²·[w₁, a] · [w₂, y]^ε · [s, w₃]^ε'
  ```

  — the `S⁴` factor is *inert* (its contribution `(w₂²[w₂,s])²` dies in `λₖ₊₁`), squares and
  brackets pair the correction against the triple's own coordinates. Meanwhile `Zₖ` is
  *spanned* by `{v², [v,a], [v,s], [v,y] : v ∈ λₖ₋₁}` (definition of the series + generation
  by the triple). So the reachable shifts form a proper-looking subspace: three free
  parameters against four spanning families, with `v²` and `[v,a]` only jointly reachable.
* **The stage lemma** is then: *for k ≥ k₀, the defect of some element of S⁰ₖ (reachable by
  modification from any given one) is zero* — equivalently, the actual defects lie in the
  reachable shift subspace. This is **not generic** (it must fail for the f = 3 relator
  `A²S⁸[S,Y]`, which has the same rank, q, and low quotients but is a different group —
  spike §2.6 control: counts differ first at order 16), so it must consume the pinned
  orientation data: the induction invariant `P` carries a χ-compatibility congruence
  (`χ_R`- vs `χ₀`-values matching mod 2^{m(k)}; the spike's §2.5 dlog table is its numeric
  shadow), and the f = 2 hypothesis (`Function.Surjective χ`, i.e. `v₂(X−1) = 2`) enters at
  the finitely many low stages where the secondary invariant is decided (orders 8–32),
  which the base cases handle concretely.

**Hardest seam, named**: the *uniform-in-k* proof of the stage lemma for k ≥ k₀ — not the
convergence (König kills that), not the filtration topology (standard), but the per-level
quadratic linear algebra: showing the constrained defect always lands in the reachable
subspace. The sources prove exactly this in relator-normalization language (initial forms in
the graded algebra of the free pro-2 group); our hom-lifting transcription must be re-derived,
not cited. Risk analysis and the spike that de-risks it: §5, §6. The known-safe fallback if
the uniform step resists elementary treatment is to formalize the graded structure it needs
(free restricted-Lie-algebra fragments — the Zassenhaus route the R-campaign deliberately
avoided); that is the fat tail, priced in §5.

### 2.3 Base cases

The induction starts at explicit small k (expected k₀ ≈ 4–5, i.e. |Qₖ| ≤ 2^10). Nonemptiness
needs **one witness per level and direction**, not enumeration: a concrete triple with a
`decide`-checked relator kill and Frattini-covering check in a finite 2-group presented as
`F₃/(relator, λₖ-generators)`. Witnesses come from the spike's p-quotient computation (§6);
the house pattern is the D₄/ZMod-8 stress tests of `DRPresentation.lean` and the
`CardH2GammaA` decide style. If kernel-`decide` budgets bite at 2^9–2^10, fall back to
structured verification (the witness's relator value traced through the λ-quotient
presentation) — flagged as an L3 risk, not a blocker; `native_decide` only with owner consent
(house axiom rules).

### 2.4 New generic infrastructure (Tier F): the λ-tower

For topologically f.g. pro-2 G (stated for `IsProP 2`, instantiated at D_R and D₀):
closed lower 2-central series; `λₖ` open (f.g. + finite elementary quotients at each step);
`G/λₖ` finite 2-group; `⋂ λₖ = 1` and neighborhood-basis (every open normal U contains some
λₖ — via: finite 2-groups are nilpotent with λ-series reaching 1); `Zₖ` central elementary
abelian; functoriality (any continuous hom maps λₖ into λₖ — verbal); `G ≅ lim G/λₖ`
(against mathlib's `ProfiniteGrp` limits or the in-tree quotient machinery). Mathlib has
essentially none of this (inventory §6: `lowerCentralSeries` for abstract groups only; no
p-central series, no Zassenhaus, no pro-p Frattini); it is standard, self-contained, and
reusable — the only sizable *generic* development in the campaign.

### 2.5 Alternatives considered and rejected

* **Finite-word Nielsen (Route N revival)** — impossible; the R2 spike's obstruction is a
  theorem covering both directions, marked or unmarked.
* **ℤ₂-exponent word iso** (adjoin `x^μ` letters) — spike §3: the χ-obstruction vanishes but
  certificates stop being free-group identities and "the Labute successive approximation
  gives no reason for a finite ledger to exist at any finite alphabet". With B-Lab declined
  this is Route L2 with worse ergonomics, not a shortcut.
* **Counting route via `reconstruction`** (prove `#ContSurj(D_R,H) = #ContSurj(D₀,H)` for all
  finite H, apply Reconstruction.lean:367) — the identity `#{r₂-triples} = #{r₀-triples}` in
  every finite 2-group is spike-verified to order 128 but has no known uniform proof except
  through the classification itself; as a target it is strictly stronger than levelwise
  nonemptiness. Rejected as primary; noted as a sanity harness (R5-style) for the L-spike.
* **Deriving BLab from the campaign's own endgame** (`main_surjection_count_R` +
  `reconstruction` would give Γ_R ≅ G_ℚ₂, hence D_R ≅ G_ℚ₂(2) ≅ D₀) — **circular**: the
  exact-image induction's source interface consumes the marked pro-2 boundary
  (`markedPro2_R`), which consumes `BLabHypothesis` (reduction note §7, input 1). Recorded so
  nobody re-proposes it.
* **One-sided epi + five-term/cup argument** (spike Step 1's "optional keeper": any epi
  between these two groups is an iso) — mathematically correct and halves the lifting work,
  but needs generic inflation–restriction–transgression exactness for `ContCoh` with cup
  functoriality, which is **not** in-tree (`Transgression.lean` is §6-specific;
  p15i resolved a different gap) and not in mathlib (inventory §3: continuous cohomology has
  H⁰ only). Two-sided lifting + `profinite_hopfian` avoids all of it. Keep as a documented
  plan-B inside L4 if one direction's stage lemma turns out much harder than the other's.
* **Abstract dualizing-module route** (`GQ2/Orientation.lean` route (i)) — unnecessary: the
  descent characterization is the hypothesis's own vocabulary and its D_R-instance is landed.

### 2.6 Tensioning against the sources (literature survey)

The proof-structure survey (WebSearch/WebFetch pass, this ticket) against: Labute,
*Classification of Demushkin groups*, Canad. J. Math. 19 (1967) 106–132 (Théorème 4:
canonical orientation, q=2 image classification, case (2) values `(−1, 1, (1−2^f)⁻¹)` —
page-verified in `docs/literature-axioms.md` §B3; Théorème 8, §5: for q=2 and d = [K:ℚ_p] odd
the group of the maximal 2-extension has the normal form `x₁²x₂^{2^f}[x₂,x₃]⋯`, at d = 1
exactly `D₀` — page-verified ibid.); Serre, Bourbaki 252 (1962/63); NSW *Cohomology of
Number Fields* ch. III §9; Serre, *Galois Cohomology* I §4.5.

Key questions the survey answers for L1's design: (i) the exact inductive invariant Labute's
Théorème 8 proof carries through the filtration (his §3–4 normalization), and which filtration
(lower 2-central vs Zassenhaus) — our λ-series choice must be checked against it; (ii)
whether NSW III §9 proves the q=2 odd case in the book or cites Serre/Labute (determines
whether a second modern-source cross-check of the stage lemma exists); (iii) the cleanest
statement of the "correction converges" step, to transcribe into the hom-lifting form.

#### 2.6a Survey results (patched 2026-07-25; original literature lane died mid-extraction,
completed by the R26b worker on orchestrator instruction — fetched sources listed at end)

**(i) Filtration: CONFIRMED, our λ-series is the sources' filtration verbatim.**
Serre, Bourbaki 252 §6 (p. 149, page-verified): "La démonstration utilise de façon
essentielle une certaine filtration (F_i) du pro-p-groupe libre F", defined `F₁ = F`,
`F_{i+1} = (F_i)^q (F, F_i)` — and §7 (p. 151, the `q = p = 2` case): "La filtration (F_i)
de F est la même que ci-dessus: F₁ = F, F_{i+1} = (F_i)² (F, F_i), et la méthode de Lazard
s'applique encore."  This is exactly §2.1's `λₖ₊₁ = cl(λₖ²[λₖ,G])`.  **No Zassenhaus**: the
p-Zassenhaus filtration `G_{(n)}` appearing in the modern Massey literature (e.g. Mináč–Tan,
arXiv:1307.6624, Lemma 3.8) is that subject's tool, not the classification proof's.  Serre's
Remarque (b) (p. 151): at `q = 2^f, f ≥ 2`, `gr(F)` is "n'est plus tout à fait une algèbre de
Lie libre" over `ℤ/qℤ[π]`, "toutefois, on peut montrer que le lemme 6.3 reste vrai, et c'est
l'essentiel" — i.e. the surjectivity survives without the full graded-Lie apparatus, which
*softens* the §5 HIGH-scenario pricing (the restricted-Lie fallback is a last resort, not the
default second step).  The *refined* inductive invariant of **Labute's** Théorème 8 proof
(the χ-bookkeeping beyond Serre's sketch) could not be page-verified: Labute 1967 is
paywalled (Cambridge Core, CJM 19, doi:10.4153/CJM-1967-007-8) — extraction stays on LS
step 2 (library access).

**(ii) NSW III §9: statement home; in-book proof status UNVERIFIED.**  Pál–Quick (below)
cite "NSW §3.9, p. 232" as the general reference *alongside* the original papers; Mináč–Tan
(Example 7.3) cite **[NSW, Propositions 3.9.12–3.9.13]** for the cup-product values on the
classified normal form — pinning the numbering neighborhood of the classification package.
Whether NSW contains a self-contained proof of the q=2 odd case (vs citing Serre/Labute)
could not be page-verified (the free NSW2e PDF at Heidelberg resisted text extraction);
LS step 2 must check the book directly.  Design consequence unchanged either way: the proof
sources for the stage lemma are Serre 252 §7 + Labute 1967.

**(iii) The "correction converges" step: page-verified, Serre 252 §6–§7 (pp. 149–151).**
q ≠ 2 skeleton (§6): with `r ≡ r₀(x) mod F_h` (h ≥ 3), set `x_i' = x_i c_i`, `c_i ∈ F_{h−1}`;
then `r₀(x) = r₀(x')·d(c)` with defect image `d̄(c̄) ∈ gr_h(F)` depending only on
`c̄ ∈ (gr_{h−1}F)ⁿ`, a **homomorphism** with explicit formula (Lemme 6.3)
`d̄(c̄₁,…,c̄ₙ) = π·c̄₁ + [c̄₁,y₂] + [y₁,c̄₂] + ⋯ + [y_{n−1},c̄ₙ]`, **surjective for h ≥ 2**;
given `r = r₀(x)·u`, `u ∈ F_h`, choose `c` with `d(c) ≡ u⁻¹ mod F_{h+1}`, iterate, "on passe
à la limite (c'est possible puisque les corrections successives c tendent vers 1)".
q = 2 repair (§7): `d̄` is **not** surjective — "gr_h(F) est engendré par l'image de d̄ et
par les classes des éléments x₂^{2^h}, …, xₙ^{2^h}" — whence `r = r₀·x₂^{μ₂}⋯xₙ^{μₙ}` with
`μ_i ∈ 4ℤ₂`; then `r = x₁²·r′` where `r′` is a Demushkin relation in `x₂,…,xₙ` **of invariant
q = 0 or ≥ 4**, normalized by Théorème 5.1 on one fewer generator.  This two-step shape
(normalize the `x₁²`-part; delegate the hyperbolic block to the q ≥ 4 argument) is a
candidate decomposition for L4's stage lemma, and the cokernel description (`2^h`-power
classes) is the source-side mirror of §2.2's "three free parameters against four spanning
families".  Distinctness (§7 end): `χ(x₁) = −1, χ(x₃) = 1+k, χ(x_i) = 1` else, so
`Im χ = {±1} × C_k` separates distinct `k` — the ground truth for the f = 3 control relator
(`k = 8` vs `k = 4` non-isomorphic).  **Transcription caveat stands** (risk 2): Serre
normalizes the relator by generator changes (Aut(F)-side); Route L2 lifts hom-triples — the
shift formula of §2.2 is the transport of `d̄` along the presentation and must be re-derived,
now against a page-verified explicit target.

**B-Lab anchors, page-verified in Serre 252**: Corollaire 4.4 (p. 148): q=2, d odd ⟹
`x₁²x₂⁴(x₂,x₃)⋯(x_{d+1},x_{d+2}) = 1`, "En particulier, pour K = ℚ₂ … trois éléments
x, y, z liés par la relation x²y⁴(y,z) = 1" — the D₀ relator; its proof (p. 153): dualizing
module = 2-primary roots of unity, "χ : G → U₂ est surjectif. Ceci entraîne k = 4" — i.e.
**χ-surjectivity ⟹ f = 2**, the exact hypothesis shape `BLabHypothesis` consumes.
Théorème 3.2 (p. 147): q=2, n odd classification with uniqueness at fixed k.  Convention
flag for L1: Serre's commutator is `(x,y) = xyx⁻¹y⁻¹` (Remarque a, p. 147) vs the repo's
`commP x y = x⁻¹y⁻¹xy` — statements must fix conventions explicitly.

**Modern recap (statements only): Pál–Quick, "A₃-formality for pro-2 Demushkin groups",
arXiv:2607.01028, §3.3** (fetched): every pro-2 Demushkin group is one of four types —
I (Demushkin): d even, `x₁^{2^f}[x₁,x₂][x₃,x₄]⋯[x_{d−1},x_d]`, f ∈ {2,…}∪{∞};
II (Serre): d ≥ 3 odd, `x₁²x₂^{2^f}[x₂,x₃]⋯[x_{d−1},x_d]`;
III (Labute): d even, `x₁^{2+2^f}[x₁,x₂]⋯`;
IV (Labute): d ≥ 4 even, `x₁²[x₁,x₂]x₃^{2^f}[x₃,x₄]⋯`, f finite.
The campaign target is **Type II at d = 3, f = 2**: `x₁²x₂⁴[x₂,x₃]` — `D₀` on the nose;
their Example 3.5 confirms 2-adic fields land in Types I/II.  No proof-method content there
(they cite the originals).  Bar-On–Nikolov (arXiv:2309.04007, fetched pp. 1–8) corroborates
the invariant system (`q`; Serre's second invariant `Im χ ≤ ℤ₂ˣ` at q = 2).

**Sources fetched this pass**: Serre, Sém. Bourbaki 252 (1962/63), pp. 145–155, via numdam
(`numdam.org/article/SB_1962-1964__8__145_0.pdf`, full text read); Pál–Quick
arXiv:2607.01028 (HTML, §3.3 + Example 3.5 + bibliography); Mináč–Tan arXiv:1307.6624
(pp. 8–18); Bar-On–Nikolov arXiv:2309.04007 (pp. 1–8); NSW2e page
(`mathi.uni-heidelberg.de/~schmidt/NSW2e/`, PDF text extraction failed).  Not obtained:
Labute 1967 (paywalled), NSW III §9 page images — both on LS step 2's checklist.

---

## 3. Asset map

### In-tree (all sorry-free unless noted)

| Asset | Where | Role in L |
|---|---|---|
| `IsLabuteOrientationDatum/_iff/_solution/_unique`, `isLabuteOrientation_ext`, `isLabuteOrientationDatum_of_root` | `GQ2/Roe/CrossedDerivation.lean` | The full descent side of Théorème 4 at r₂: pins `(S,X,Y)` to the Hensel root. Consumed by the χ-bookkeeping of the invariant `P`. |
| `rootX(_spec/_unique)`, `Sval`, `Yval`, mod-16 congruences, exact-level facts | `GQ2/Roe/OrientationRoot.lean` (R10) | Concrete orientation numerics for low stages and `P`. |
| `chiR`, `isLabuteOrientation_chiR`, `chiR_surjective` | `GQ2/Roe/ChiR.lean` (R11) | Discharges BLab's χ-antecedent; χ_R-side of `P`. |
| `isDemushkin_DR`, `demushkinRank_DR`, `demushkinQ_DR`, 9 Gram entries, `card_H1/H2_DR` | `GQ2/Roe/DRDemushkin.lean` (R12/R13b, in flight) | Low-stage data; the cup–Bockstein matrix `[[0,1,0],[1,0,0],[0,0,1]]` is the k=2 shadow of the stage analysis. |
| `drWord/drLiftHom/DR` + stress tests; `d0Relator/D0/d0LiftHom` | `GQ2/Roe/DRPresentation.lean`; `GQ2/DyadicPresentation.lean`, `SectionThree.lean:444` | Presentations; triples-⟺-homs. |
| `dr_topGen`, `dr_hom_ext`; `topGen_d0` | `GQ2/Roe/DRAbelianization.lean:132,151`; `GQ2/DyadicNielsen.lean:47` | F.g. hypotheses for Hopfian/König; density arguments. |
| `profinite_hopfian`, `ContSurj`, `finite_continuousMonoidHom`, `konigFunctor`, `contSurj_quotient_nonempty_finite`, `exists_contSurj_of_card_le`, `continuousMulEquivOfBijective`, `reconstruction_of_equinum` | `GQ2/Reconstruction.lean:76,37,56,185,119,213,44,319` | The entire assembly layer; refactor target for `_of_levelwise_nonempty`. |
| ZMod-2 central-extension calculus: `TwoCocycle`, `CentExt`, obstruction maps `drRelZ/obs/obsH2_DR` | `GQ2/WordCoh2.lean`, `GQ2/Roe/DRWordCoh.lean` (R13b in flight) | One-step lifting calculus (elementary-abelian kernels factor into 𝔽₂-lines); the defect function's natural home. |
| `frattiniLike` + nongeneration | `GQ2/FrattiniCriterion.lean`, `GQ2/FrattiniNongen.lean` | Generation-for-free in the induction. |
| `maxProPQuotient/IsProP` API; `topAbelianization`; `zpowZtwo`/`ZtwoPowering` | `GQ2/MaxProP.lean` etc. | Ambient pro-2 vocabulary; ℤ₂-powering for χ-congruences. |
| R2 spike numerics & methods | `docs/orchestration/roe-r2-spike.md` | Witness triples mod 2^k, dlog congruence table, Hom-count harness (O(|G|²) trick), obstruction precondition. |

### Mathlib (from the L0 inventory subagent; local checkout)

* **EXISTS / usable**: `ProfiniteGrp` category with `P ≅ lim P/U` over `OpenNormalSubgroup`
  (`Topology/Algebra/Category/ProfiniteGrp/Limits.lean`); `nonempty_sections_of_finite_cofiltered_system`
  (`CategoryTheory/CofilteredSystem.lean`, already imported by Reconstruction.lean);
  `CompleteSpace` via `complete_of_compact`; `hensels_lemma` (`NumberTheory/Padics/Hensel`);
  `PadicInt.toZModPow`/`lift`; `ZMod.orderOf_five` + `isCyclic_units_two_pow_iff`
  (`RingTheory/ZMod/UnitsCyclic`) for the `{±1}×(1+4ℤ₂)` split at finite level;
  `ContinuousMulEquiv` API (`Topology/Algebra/ContinuousMonoidHom:311`); discrete
  `groupCohomology` H¹/H²/inf-res as a *template* only.
* **ABSENT (project-owned)**: Demushkin anything; cohomological dimension/duality; continuous
  cohomology beyond H⁰ (Hill–Yang file is H⁰-only); free/presented pro-p groups (in-tree
  already); lower p-central/Zassenhaus/Jennings/restricted Lie; pro-p Frattini/rank theory;
  noncommutative `Multipliable` (irrelevant under Route L2); `Procyclic`.

Verdict: mathlib contributes ambient topology and two convenient arithmetic files; every
Demushkin-specific layer is (and stays) project-owned. No mathlib bump needed.

---

## 4. Phased ticket decomposition (house style: skeleton-first, recon-first, disjoint files)

New files live under `GQ2/Roe/Labute/` — disjoint from every in-flight worker (R13b owns
`DRWordCoh/DRH2/DRDemushkin`, R15 owns `MarkedPro2` fills, R30/R32 own `SourceData/Main`).
The single existing-file edit (Reconstruction.lean refactor) is quarantined in its own
serialized ticket per the R30 pattern. Models: fable = design/hard seams, opus =
well-specified construction.

| id | title | model | files owned | depends on | est. lines |
|---|---|---|---|---|---|
| **LS** | **Off-Lean de-risking spike** (§6): paper-level stage lemma + p-quotient computational validation; deliverable `docs/orchestration/labute-spike.md` | fable | spike memo only | — | 0 (memo) |
| L1 | Design memo + compiling sorry-skeletons, statements final: λ-tower API, levelwise sets + defect, stage lemma (invariant `P` fixed per LS), base-case interfaces, assembly statement; `labute-l1-design.md` | fable | `GQ2/Roe/Labute/{TwoCentralTower,Levelwise,StageLemma,Assembly}.lean` (skeletons), memo | LS | 400–700 |
| L2 | λ-tower fills (generic pro-2: openness, basis, `Zₖ` structure, functoriality, `G ≅ lim G/λₖ`) | opus | `TwoCentralTower.lean` | L1 | 500–900 |
| L3 | Base cases: witness triples + relator/generation checks through k₀, both directions (witnesses from LS) | opus | `Levelwise.lean` | L1 (LS numerics) | 300–700 |
| L4 | Stage lemma: defect calculus (shift formula) + reachability under `P` for k ≥ k₀; split L4a (calculus, opus-able) / L4b (reachability, fable) if L1 so decides | fable | `StageLemma.lean` | L1, L2 | 800–2,000 |
| L5 | Assembly: `exists_contSurj_of_levelwise_nonempty` refactor (serialized existing-file edit, regression gate: `reconstruction`/`reconstruction_of_equinum` byte-identical consumers), two epis, Hopfian endgame, `theorem bLab : BLabHypothesis`, stress tests | opus | `Assembly.lean`, `GQ2/Reconstruction.lean` (refactor only) | L2, L3, L4 | 400–700 |
| L6 | Gates/docs: `docs/literature-axioms.md` B3 addendum ("B-Lab discharged as theorem", census unchanged), board/README notes, `lean_verify bLab` = std-3 certificate, blueprint chunk hook | opus | docs | L5 | 100–250 |

**Dependency edges into the R-board** (unchanged from the board's L-campaign header):
R15 consumes `BLabHypothesis` as a hypothesis — no L dependency; after L5, the orchestrator
adds the one-line discharge at the R32 assembly (R32 is the only row whose final shape waits
on L; it stays hypothesis-parametrized until then). Nothing else blocks on L; L blocks on
nothing in-flight (L1 can start the moment the owner signs off — LS is dispatchable today).
G2 (final census sign-off) requires L6.

---

## 5. Effort estimate

Calibration anchors: the §5 dévissage clone ran ≈ 2.3k lines / 2 dispatches; the original
tower averaged ≈ 11k lines/swarm-day on established patterns; genuinely novel seams (R9's
454-line χ-calculus with heavy `linear_combination`) run 3–5× slower per line; the
verification plan priced the *abstract* classification fat tail at 3–6 weeks.

| Scenario | Lean lines | dispatches | swarm-days | when |
|---|---|---|---|---|
| **LOW** | ≈ 2.0k | 6–7 | 1.5–2 | LS validates a clean invariant `P`; stage lemma reachability is elementary linear algebra over the definitional generation of `Zₖ`; base k₀ ≤ 4. |
| **LIKELY** | ≈ 2.5–5.5k | 8–12 | 2.5–4 | Stage lemma needs careful but elementary graded bookkeeping (one L4 split, one redispatch); base cases need structured witnesses at 2^9–2^10. |
| **HIGH** | ≈ 6–10k | 15–20 | 8–15 | Uniform step demands genuine graded-Lie structure of the free pro-2 group (Zassenhaus/initial-form development ~2–4k extra lines, Labute's Lie-algebra companion paper territory) or the invariant `P` needs several redesign cycles. This is the original fat tail; LS exists to detect it for the price of a spike. |

The LIKELY case is a moderate campaign — bigger than a b-series axiom flip, well under the
original fat-tail pricing, because §1's instance reductions are real and §2's assembly is
already in-tree.

---

## 6. Risks and the first de-risking spike (LS — dispatch first, off-Lean, R2-style)

**Risks, ranked.**

1. **Stage-lemma uniformity** (the HIGH scenario above). Detected by LS; mitigated by the
   middle-path options (§7) and the graded-structure fallback.
2. **Formulation drift**: the sources normalize relators under Aut(F); our hom-lifting
   transcription is equivalent but must be re-derived — the invariant `P` (χ-congruence
   bookkeeping at q = 2, secondary level f) is the subtle part. Mitigated by LS steps 2–3 and
   L1's verbatim-quote tensioning (house `/develop` discipline).
3. **λ-tower topology fiddliness** (closures of verbal subgroups; openness needs f.g.).
   Standard but new; quarantined in L2 with stress tests.
4. **Base-case kernel budgets** at |Q| = 2^9–2^10 (witness-checking, not enumeration, keeps
   this small; `native_decide` only with owner consent).
5. **Coordination**: all new files in `GQ2/Roe/Labute/`; the single Reconstruction.lean edit
   is serialized (L5) with a byte-identical-consumers regression gate; no contact with R13b/
   R15/R30/R32 files.
6. **Axiom hygiene** (§8): the campaign must not silently import B3c-derived D₀ facts; L6's
   `lean_verify` gate enforces std-3.

**The spike (LS), concretely.** Off-Lean, Sage/GAP (ANUPQ p-quotient), timeboxed like R2,
deliverable `docs/orchestration/labute-spike.md`:

1. Compute the λ-towers: 2-quotients of `⟨s,x,y | r₂⟩` and `⟨A,S,Y | r₀⟩` to depth k ≈ 7–9
   (p-quotient algorithm; orders through ~2^15). Record `dim Zₖ` both sides (equal? — a free
   consistency check), and per-level witness triples for L3 (both directions), verified by
   the R2 Hom-count harness.
2. Write the stage lemma on paper against the sources, starting from the Serre 252 §6–§7
   skeleton page-verified in §2.6a: obtain Labute 1967 (paywalled — library access) and
   extract his refined inductive step (Théorème 8 proof; plus the NSW III §9 proof-status
   check — both per §2.6a's unobtained-sources checklist) with verbatim quotes; transcribe
   to the hom-lifting form; fix the invariant `P` (exact χ-congruence modulus m(k), any
   extra normal-form clauses) and the exact shift formula with signs.
3. **Test the induction computationally**: at each computed level, enumerate (or sample) the
   defect classes of `S⁰ₖ`-elements and the reachable-shift subspace; verify empirically that
   constrained defects are reachable, that `P` propagates, and that the f = 3 control relator
   fails at exactly the predicted level. If the empirical margin is thin or the reachable
   space misses defects at some k, the uniform lemma as drafted is wrong — redesign before
   any Lean is written.
4. Verdict: GREEN (invariant + step validated ⇒ dispatch L1) / AMBER (step needs graded-Lie
   input ⇒ re-scope L4 toward the HIGH scenario, present §7 options to owner) / RED
   (formulation unfixable in hom-language ⇒ fall back to Route A relator-normalization
   scoping — not expected; the two languages are equivalent).

---

## 7. Middle-path options (owner decision points — flagged, not decided)

If the owner wants a smaller axiom rather than a full proof after seeing LS:

* **O1 — axiomatize only the uniform stage step** (k ≥ k₀, both directions): a single
  ∀k statement, strictly weaker than B-Lab, with the base cases, tower, and assembly all
  proven. Kills the L4 tail; the axiom is exactly "Labute's inductive step", citable to a
  specific displayed step of the source.
* **O2 — axiomatize levelwise nonemptiness** (`∀ k, S⁰ₖ ≠ ∅ ∧ Sᴿₖ ≠ ∅`): purely
  finite-2-group content, machine-checked instance-wise to order 128 already (spike §2.6) and
  further by LS; unusually falsifiable for a literature axiom. Everything else proven.
* **O3 — timebox L4**: run the full campaign with an owner-set stall limit on L4; on stall,
  drop to O1 with the partial proof kept.

Each option keeps `BLabHypothesis` as the interface and the census discussion honest (the
axiom would be new and needs the same G-gate as B-Lab did; O2 is the least classification-
shaped of the three).

---

## 8. Axiom-interaction map (required by the charter)

* The L campaign depends on **zero** of the nine census axioms. It lives entirely on the
  presented-group side (`DR`, `D0`, free pro-2 machinery, ℤ₂-arithmetic).
* **B3c cannot help and must not be touched**: `dyadicOrientation` speaks about
  `G_ℚ₂(2) ≅ D₀` and the cyclotomic character — it relates the *Galois* group to D₀ and says
  nothing about D_R. Any D₀-side fact imported into L must come from the presentation
  (`DyadicPresentation`, `SectionThree`, `DyadicNielsen`) — these are proven, not
  axiomatized; L1's skeleton imports will be audited for this (no `Foundations/Axioms`
  transitive dependencies; `lean_verify bLab` must report std-3 exactly).
* `prop_3_8_*`/`prop_1_1` (D₀-side automorphism lifting, marked normalization) are R15's
  business, downstream of `bLab`; L does not touch them.
* The would-be B-Lab ledger section in `docs/literature-axioms.md` §B3 becomes an addendum
  recording the discharge (L6); `check_axioms.sh` expected-set is **unchanged** throughout.

---

## 9. Definition of done (L-campaign)

`theorem bLab : BLabHypothesis` sorry-free, std-3 axioms; all `GQ2/Roe/Labute/*` green with
stress tests; Reconstruction.lean refactor regression-gated; R32 capstone discharged of the
hypothesis (one-line, at R32); ledger/board/docs updated (L6); LS + L1 memos archived as the
design record.
