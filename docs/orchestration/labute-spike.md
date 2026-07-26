# LS — Labute-discharge spike: report

**Date**: 2026-07-25 · **Worker**: Fable (LS) · **Ticket**: LS of `labute-plan.md` §4/§6.
**Deliverable of**: the off-Lean de-risking spike gating the whole L-campaign.

## 0. VERDICT: GREEN

The invariant, the inductive step, and the shift formulas are validated — by complete
finite censuses at the low levels, by sampled tests to depth k = 6 (towers computed to
k = 8), by two f = 3 controls that fail at exactly the predicted level with the predicted
mechanism, and by page-verification of every load-bearing claim in Serre, Bourbaki 252.
L1 can freeze statements (§4 below).

**One-paragraph justification.** The naive local stage lemma (plan §2.2's draft: any
relator-killing generating triple's defect is reachable by one-level modifications) is
**false** — machine-falsified at k = 4 — exactly because of Serre's q = 2 pathology
(coker d̄ = 2 at every level, machine-measured). The repair is sharper than the plan's
tail-augmented fallback: within the strict levelwise sets, defect-reachability is exactly
governed by a **χ-congruence invariant** `P(T) : χ̂∘T ≡ (χ-targets) mod 2^k` (modulus
m(k) = k). This dichotomy was verified *exhaustively* at k = 3 and k = 4 (256/256
trajectory classes classified, perfect separation both directions), and on every sample at
k = 5, 6. With P, a guided greedy lift runs stall-free to k = 6 in both directions,
producing small reproducible witness words (L3's test vectors), and the two fresh χ-digits
are always adjustable inside ker d̄ (empirically uniform 1/4 fibers). Both f = 3 controls
have S⁰₄ = ∅ **proved by exhaustion**, because the f-mismatch caps the χ-depth at 2 < 3 =
m(3); this is the classification's distinctness mechanism operating levelwise, and it
shows P is necessary, not decorative. The uniform-in-k inputs the Lean proof needs reduce
to one graded spanning statement page-verified in Serre §7 and machine-verified to k = 6
(plus elementary 2-adic functional calculus); a no-basis-theorem proof route for it is
drafted in §2.5. **Biggest residual risk** (named, priced): the uniform-in-k Lean proof of
that spanning statement — if the drafted elementary reduction snags, options O1/O2 of plan
§7 apply to a much smaller, machine-corroborated statement.

Summary data: k-depth 6 tested / 8 computed; tooling Sage 10.7 + libgap `PQuotient`
(collector 4096); dim Z_k identical for D_R, D₀ and the f = 3 control at every k ≤ 8;
formula checks 24/24; census 6→2→64-of-256→(sampled) both directions; controls dead at
k = 4 by exhaustion; witness words ≤ 196 letters at k = 6.

---

## 1. Step 1 — λ-towers (lower exponent-2 central series)

`λ₁ = G, λ_{k+1} = λ_k²[λ_k, G]`; `Q_k = G/λ_k`, `Z_k = λ_k/λ_{k+1}`. GAP's
`PQuotient`/`PCentralSeries` implement exactly this series (checked against the
definition; the class-c quotient is `Q_{c+1}`).

| k | dim Z_k | log₂ |Q_{k+1}| |
|---|---:|---:|
| 1 | 3 | 3 |
| 2 | 5 | 8 |
| 3 | 10 | 18 |
| 4 | 20 | 38 |
| 5 | 44 | 82 |
| 6 | 94 | 176 |
| 7 | 214 | 390 |
| 8 | 484 | 874 |

**Identical for all three groups** `D_R = ⟨s,x,y | r₂⟩`, `D₀ = ⟨A,S,Y | r₀⟩`, and the
control `D' = ⟨A,S,Y | A²S⁸[S,Y]⟩`, at every level k ≤ 8.

Readings: (i) the D_R ≅ D₀ consistency check passes at all 8 levels; (ii) the dims are
**f-blind** (the control matches too), so no dimension count can carry the
classification's content — the discrimination lives at triple level, as designed;
(iii) the plan's "orders through ~2^15" guess was far too small: layers grow ≈ ×2.2 per
level and the tooling handles 2^874 pc-groups without strain. Base-case budget news is
excellent: k₀ = 3 (below), so L3's `decide`-work lives in `Q₃` of order **2^8 = 256**.

---

## 2. Step 2 — the stage lemma on paper

Conventions (repo): `g^h = h⁻¹gh`, `[g,h] = g⁻¹h⁻¹gh` (Serre's `(x,y) = xyx⁻¹y⁻¹` is the
opposite; all displayed formulas below are in repo convention).
`r₀ = A²S⁴[S,Y]` (exponent sums (2,4,0)); `r₂ = (x^s)⁻¹x⁻³y²[y,y^s]` (sums (0,−4,2)).

### 2.1 Transported defect calculus (validity threshold k ≥ 3)

For `T ∈ S⁰_k` (kills the source relator in `Q_k`, generates), lift to `Q_{k+1}`; the
defect `δ(T) ∈ Z_k` is lift-independent (all relator exponent sums even; commutators
absorb central factors — plan §2.2, re-derived and machine-confirmed). Modifications
`T ↦ T·w`, `w ∈ (λ_{k-1})³`, stay in `S⁰_k` (generation: Frattini; relator: shift lands in
λ_k) and shift the defect by the **defect homomorphism** d̄_k. The group-identity lemmas
underlying all of this need exactly `k ≥ 3`:
`[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2} ⊆ λ_{k+1}`, `[λ_{k-1}, λ₂] ⊆ λ_{k+1}`, `v ↦ v²` is
𝔽₂-linear `Z_{k-1} → Z_k`, `[v,g]` depends only on `(v mod λ_k, g mod λ₂)`, and
`w² , [v,g]` are central of order ≤ 2 mod `λ_{k+1}`. At k = 2 several of these fail
(squaring not additive, λ₁-moves change the Frattini class): **k = 2 is base-case
territory, not calculus territory** — this is why the broken first draft of the spike's
lookahead (which searched "level-2 kernels") produced garbage; see §3.5.

### 2.2 The shift formulas (signs resolved, machine-verified)

In additive notation for `Z_k` (elementary abelian — hence **every sign is trivial**,
resolving plan §2.2's "unresolved signs": the content is *which factors appear*, and the
derivation fixes the multiplicative order, immaterial after centrality):

* r₀-side, triple `(a,s,y)` (images of `(A,S,Y)`), modification `(w₁,w₂,w₃)`:

  `d̄_k(w₁,w₂,w₃) = w₁² + [w₁,a] + [w₂,y] + [w₃,s]`

  The `S⁴` factor is **inert** (its whole contribution `(w₂²[w₂,s])²` dies in λ_{k+1});
  the `A²` factor gives the π-diagonal `w₁² + [w₁,a]`; `[S,Y]` gives the two cross terms.

* r₂-side, triple `(s,x,y)`, modification `(u,v,w)`:

  `d̄_k(u,v,w) = w² + [w,y] + [u,x] + [v,s]`

  Here `y` is the distinguished (squared) generator; the x-block `(x^s)⁻¹x⁻³` is π-inert
  (`v^{-4}` dies since `v⁴ ∈ λ_{k+1}`) but contributes the cross terms `[u,x]` (s-slot
  correction against x, via `x^s`) and `[v,s]`; the factor `[y, y^s]` is **fully inert**
  (its first-order terms cancel in pairs — both slots are y-letters).

Machine verification: 24/24 random-modification checks (12 per side, levels 3–4), and
every census/witness computation below uses *empirical* columns
`r(T·w)·r(T)⁻¹` — independent of the formulas — so the formulas were re-confirmed
implicitly thousands of times. These formulas are the transported, q = 2, repo-convention
analogue of Serre's Lemme 6.3 display (which is stated for the q ≠ 2 normal form); the
q = 2 self-pairing term `[w₁,a]` replaces his `[c̄₁,y₂]`. **They are a derivation, not a
citation** (risk 2 of plan §6 discharged by re-derivation + machine check).

### 2.3 The span theorem (the graded input, isolated)

**Statement (free form).** In the free pro-2 group F on x₁,x₂,x₃ with the λ-filtration,
for the d̄ of either relator shape and every k ≥ 3:

  `gr_k(F) = Im d̄_k + ⟨ classes of g₂^{2^{k-1}}, g₃^{2^{k-1}} ⟩`

where g₂,g₃ are the two non-π'd generators (for r₀: S,Y; for r₂: s,x), and moreover the
π'd generator's power `g₁^{2^{k-1}}` already lies in `Im d̄_k` (via
`d̄(π^{k-2}g₁,0,0) = g₁^{2^{k-1}} + [π^{k-2}g₁, g₁]` and `ad(π^m g)(g) = (ad g)^{2^m}(g)
= 0`).

**Descent.** `gr_k(F) ↠ Z_k(D)` (λ is verbal, so `λ_k(D) = im λ_k(F)`), the map carries
d̄-image to d̄-image and tails to tails; hence the span statement holds verbatim in
`Z_k(D_R)` and `Z_k(D₀)` at any generating triple. **The Lean statement only ever needs
the free version.**

**Source.** Serre 252 §7 (p. 151), for the mod-F₃-normalized relator: d̄ "n'est pas
surjective"; all one can say is that gr_h(F) is generated by Im d̄ together with the
classes of the elements written there as `x₂^{2^h}, …, x_n^{2^h}`. **Transcription
caveat (caught here, empirically confirmed):** as printed the powers are off by one —
`x^{2^h} ∈ F_{h+1}`, so its class is one level too deep; the level-h tails are
`x_i^{2^{h-1}}`. Cross-checks: Serre's own μ_i ∈ 4ℤ₂ (p. 152) requires the first
absorbable digit at h = 3 to be 4 = 2^{3-1}; and the machine rank data (below) completes
`rank d̄ + 2` with the `2^{k-1}`-powers, while `2^k`-powers are the zero class.

**Machine verification.** In free F₃ (dims 3, 6, 14, 32, 80, 196) at k = 3,4,5 and in
both group towers at k = 3,4,5,6, for both relators: `rank d̄_k = dim Z_k − 2` and adding
the two adapted tail columns gives full rank — SPAN = YES in all 20 table rows; the π'd
generator's power is in Im d̄ in every row.

| tower, relator | k=3 | k=4 | k=5 | k=6 |
|---|---|---|---|---|
| F₃, r₀-d̄ (tails S,Y) | 12+2=14 ✓ | 30+2=32 ✓ | 78+2=80 ✓ | — |
| F₃, r₂-d̄ (tails s,x) | 12+2=14 ✓ | 30+2=32 ✓ | 78+2=80 ✓ | — |
| D_R, r₀-d̄ | 8+2=10 ✓ | 18+2=20 ✓ | 42+2=44 ✓ | 92+2=94 ✓ |
| D₀, r₂-d̄ | 8+2=10 ✓ | 18+2=20 ✓ | 42+2=44 ✓ | 92+2=94 ✓ |

(An early run with the r₂-tails wrongly taken as (x,y) gave rank dim−1 — the relator-
adapted tail pair is forced, a detail L1 must carry into the statements.)

### 2.4 The invariant P, the modulus m(k), the base k₀, and the stage lemma

Fix the direction (D₀-relator triples in the D_R-tower; the other direction is the mirror
with targets swapped as below). Let `χ̂_k : Q_k → (ℤ/2^{k+1})ˣ` be the level-k shadow of
χ_R (well-defined: `χ(λ_k) ⊆ λ_k(ℤ₂ˣ) = 1 + 2^{k+1}ℤ₂` for k ≥ 2 — exact, elementary).
χ-targets: `(A,S,Y) ↦ (−1, 1, η)` with `η = (1−4)⁻¹ = −1/3`; reverse direction
`(s,x,y) ↦ (S, X, Y)`, X the Hensel root ≡ 5 (16) of `Z³+2Z²+1`, `S = −X³/(X²+X+1)`,
`Y = −X²`. Numerics mod 2^9: `X = 437, S = 253, Y = 7, η = 341` (and mod 16: 5, 13, —, 5).

**Levelwise sets (FINAL FORM for L1 — freeze this):**

```
S^P_k = { T : Fin 3 → Q_k | relatorWord T = 1 ∧ T generates
                            ∧ χ̂_k(T_i) ≡ target_i mod 2^k  (i = 1,2,3) }
```

**Stage lemma** (uniform, k ≥ k₀ = 3): for `T ∈ S^P_k`:
* **SL1 (reachability)**: `δ_k(T) ∈ Im d̄_k(T)`;
* **SL2 (digit adjustment)**: the map `ker d̄_k → (ℤ/2)²` sending a modification to the
  pair of fresh χ-digits of the corrected triple is onto;
* hence some corrected lift lies in `S^P_{k+1}`, so `S^P_{k+1} ≠ ∅`.

Restrictions `S^P_{k+1} → S^P_k` exist (all three clauses weaken); König then gives the
continuous epi with `χ ∘ φ = χ-targets` **exactly** — the limit is orientation-
compatible for free, a bonus for R15's marked interface.

**m(k) = k, and P is necessary as well as sufficient.** Empirically (exhaustive at
k = 3, 4; sampled k = 5, 6): within the strict sets, `δ_k(T)` reachable **⟺** χ̂-depth
≥ k. Membership alone forces depth ≥ k−1 (all 256 classes at k = 4 had depth ≥ 3). The
192/256 P-violating classes at k = 4 were *all* unreachable: no P-free lemma exists.

**Base case k₀ = 3**: `S^P_3 ≠ ∅` by explicit witness in `Q₃` (order 2^8): direction 1
`(y, s·x, x)` (mod-8 χ-values (7,1,5) = targets), direction 2 `(S·Y, Y, A)`. All 168
mod-2 seeds enumerated: 6 kill the relator mod λ₃ (this is Serre's (7.1)-condition, cup
form data), exactly 2 satisfy P, and exactly those 2 have reachable δ₃ — per-seed table
in §3.1.

**Relation to plan §2.2's draft and to the orchestrator's tail-augmented directive.** The
draft's vacuous-P local lemma is false (§3.5). The Serre-faithful repair — carry a
deformation tail `r·g₂^{μ₂}g₃^{μ₃}`, absorb coker components into forced μ-digits — was
implemented and validated too (never stalls; digit streams in §3.3; the controls absorb
exactly the predicted wrong digit at k = 3). The census then showed the two designs
coincide: **the χ-clause is the tail-augmentation, collapsed** — P pins the μ-digits to
0, so the strict sets with the χ-clause carry the whole induction and no relator family,
no phase-2 renormalization (Serre p. 152's `r = x₁²r′` + Théorème 5.1 on one fewer
generator), and no χ-surjectivity anchor *inside the induction* are needed in Lean. The
f = 2 input enters only through the numeric targets (η mod 8 = 5); the p. 153 anchor
("χ surjectif ⟹ k = 4") remains the *interpretation* of why the hypothesis pins these
targets — it is consumed where the plan already consumes it, in the landed
`isLabuteOrientationDatum_solution` / `chiR` layer, not in L4. The tail-augmented design
survives in this memo as the documented fallback (§3.3) and maps to plan §7's O1/O2.

### 2.5 Proof routes for the uniform-in-k inputs (drafted; where the risk sits)

The Lean proof needs three uniform-in-k lemmas beyond the (routine) calculus of §2.1–2.2.

**(a) The span theorem (§2.3) — the irreducible graded input; THE residual risk.**
Serre's proof is "la méthode de Lazard" (embed gr F in the graded of the free associative
algebra); at q = 2 he explicitly warns gr F is *not* an algebra over ℤ/2[π] but asserts
(Remarque b, p. 151, for q = 2^f; §7 for q = 2) that the needed statement survives.
Formalizing Lazard's embedding is the HIGH scenario. The spike's de-risking discovery is
that **spanning needs no basis theorem**: `Z_k = π(Z_{k-1}) + [Z_{k-1}, gens]` is
*definitional* (verbal subgroup), so it suffices to reduce each atom `πv` and `[v,g]`
into `Im d̄ + tails` by a well-founded structural induction using only: the three
d̄-columns; the diagonal trick `[v,g₁] ≡ πv mod Im`; char-2 Jacobi; `ad(πu) = (ad u)²`
(so `[πu, z] = [[z,u],u]`); `π(u+v) = πu + πv + [u,v]` with `[u,v]` dying for degree
reasons (k ≥ 3); `[z,z] = 0`; and `π^m(g_i)`-base-atoms = the tails resp. the diagonal
trick. Worked instance: `π[x₂,x₃] ≡ [[x₂,x₃],x₁]` (diagonal) `= [[x₂,x₁],x₃] +
[[x₃,x₁],x₂]` (Jacobi) — two d̄-columns. The only atoms requiring recursion are
`π[u,g]`-classes (handled by diagonal-then-Jacobi with measure (degree, π-height,
left-depth)) and nested brackets `[u, [g,g']]` (Jacobi-rotate outward, recurse on u).
All listed identities are group-commutator facts about λ-layers (Hall–Witt calculus),
formalizable without any free-Lie development. Estimated as the "careful but elementary
graded bookkeeping" of the plan's LIKELY scenario. **If the reduction snags** (a
non-terminating case or a q = 2 identity failure), fallbacks in order: (1) O1-style axiom
of exactly the free span statement (a single ∀k sentence about F₃, machine-corroborated
here to k = 6 in quotients and k = 5 in F itself; falsifiable; far smaller than B-Lab);
(2) the Lazard development (HIGH scenario, 2–4k lines).

**(b) SL1 from span + functional calculus.** Given span, `Z_k/Im d̄_k` is (at most) the
2-dim tail space. Two functionals separate it, both elementary: (i) `χ̂` — with
`v₂(η^{2^{k-1}} − 1) = k + 1` exactly (from `v₂(η−1) = 2`, elementary 2-adic), the
η-slot tail has nonzero χ̂-shadow at the right depth, while `χ̂(δ_k(T)) = χ̂(T₁)²χ̂(T₂)⁴`
is pinned by the P-congruence; (ii) the abelianized shadow (`D_R^{ab} = ℤ₂²×ℤ/2`,
landed) — the S-slot tail has nonzero image in `gr_k(ab)` and the ab-shadow of the
defect is pinned by the relator-kill one level up. The bookkeeping is a small triangular
2×2 computation per level, uniform in k via the exact valuations. (The empirical
dichotomy says this cannot leak: it was exact at 256/256 classes.)

**(c) SL2 (digit adjustment).** Candidate explicit kernel elements: the two-slot
combinations that cancel their own d̄-image while carrying χ̂-value `1 + 2^k(unit)` in
one slot (e.g. corrections built from `g₂^{2^{k-2}}`-type words paired against
compensating brackets; the empirical fibers over the four digit pairs were *exactly*
32/32/32/32 at k = 4 — the map is not merely onto but balanced, so random search found
digit-fixes in ≤ 7 tries at every level ≤ 6). If explicit elements get ugly at some
level, SL2 also follows from a dimension count over the span theorem (ker d̄ is huge:
`3·m_{k-1} − m_k + 2`). Low risk.

### 2.6 Paper-quote ledger (page-verified this spike, numdam scan of Bourbaki 252)

All French fragments ≤ a line, cited for identification; the memo's statements above are
transcriptions, not quotations.

* p. 148, Cor. 4.4: q = 2, d odd normal form; "x²y⁴(y, z) = 1" for K = ℚ₂ — the D₀
  relator. ✓ (matches `DyadicPresentation`).
* p. 148, Th. 5.1: q ≠ 2 normalization `r = x₁^q(x₁,x₂)⋯(x_{n-1},x_n)`; the q = 2,
  n odd analogue announced ("un résultat analogue, qui précise le théorème 3.2"). ✓
* p. 149, §6: the filtration `F₁ = F, F_{i+1} = (F_i)^q(F,F_i)` — our λ-series verbatim
  at q = 2 (no Zassenhaus). ✓  Lazard picture: gr F ⊂ gr A; for p ≠ 2 free Lie over
  ℤ/qℤ[π], π = image of q-th power, degree +1. gr₂-basis `πy_i, [y_k,y_l]`. ✓
* p. 150, Lemme 6.1: Demushkin-ness of r ⟺ (a_i) coprime mod q + alternating (b_kl)
  invertible mod q (cup form = mod-p reduction). Lemme 6.2: mod-F₃ normalization. ✓
* p. 150, Lemme 6.3: the defect homomorphism, displayed formula
  `d̄(c̄) = π·c̄₁ + [c̄₁,y₂] + [y₁,c̄₂] + ⋯ + [y_{n-1},c̄_n]`, surjective for h ≥ 2;
  proof by explicitness ("suffisamment explicite … sans trop de mal"). ✓
* p. 151, iteration: choose c with `d(c) ≡ u⁻¹ mod F_{h+1}`, iterate, pass to the limit
  ("les corrections successives c tendent vers 1"). ✓
* p. 151, Remarque a: q = 0 case via descending central series. Remarque b: q = 2^f,
  f ≥ 2: gr F not quite free Lie over ℤ/q[π], "toutefois … le lemme 6.3 reste vrai, et
  c'est l'essentiel". ✓
* p. 151, §7 (q = p = 2): same filtration, "la méthode de Lazard s'applique encore";
  squaring no longer equals multiplication by π; (7.1) `r ≡ x₁²(x₂,x₃)⋯ mod F₃` for n
  odd; d̄ "n'est pas surjective"; gr_h generated by Im d̄ + generator-power classes
  [printed exponent `2^h`; correct level-h power is `2^{h-1}` — §2.3 erratum note]. ✓
* p. 152: `r = r₀·x₂^{μ₂}⋯x_n^{μ_n}`, μ_i ∈ 4ℤ₂; rewrite `r = x₁²·r′`, r′ Demushkin in
  x₂,…,x_n with invariant q "nul ou ≥ 4"; apply Th. 5.1 on one fewer generator;
  distinctness via χ: `χ(x₁) = −1, χ(x₃) = 1+k, χ(x_i) = 1` else, `Im χ = {±1}×C_k`. ✓
  (Note χ(x₃) — the Y-slot — carries the η-like value: matches our target placement.)
* p. 153: dualizing module of the local group = p-primary roots of unity; for p = 2, d
  odd: "χ : G → U₂ est surjectif. Ceci entraîne k = 4" — the f = 2 anchor. ✓
* p. 153–154, §9: cd = 2; open subgroups Demushkin; 9.3 uniqueness of χ; q recoverable
  from Im χ; the H¹-surjectivity characterization of χ, "que l'on utilise pour
  déterminer explicitement χ lorsque la relation r … est connue" — the source anchor for
  the repo's descent characterization (`IsLabuteOrientationDatum`, R10/R11). ✓
* Pál–Quick arXiv:2607.01028 §3.3 (HTML, re-fetched): four types; Type II d ≥ 3 odd
  `x₁²x₂^{2^f}[x₂,x₃]⋯`; at d = 3, f = 2 exactly `x₁²x₂⁴[x₂,x₃]`; classification cited
  to Demushkin/Serre/Labute (no independent proof). Example 3.5: 2-adic fields → I/II. ✓
* NSW III §9: in-book proof status **still unverified** (two fetches reached only a
  bibliographic landing page; the PDF resisted extraction as before). Consequence nil:
  the stage-lemma source is Serre §6–7 (fully page-verified above) + this spike's
  machine verification. Labute 1967: **paywalled, not attempted** (per charter); its
  refined χ-bookkeeping is exactly what the census has now pinned empirically (m(k) = k),
  so the campaign no longer depends on obtaining it.

### 2.7 Design deltas vs plan §2.1–2.2 (for L1)

1. Levelwise sets acquire the **χ-clause** (final form in §2.4); the plan's `S⁰_k` keeps
   only base-case and bookkeeping roles. König/assembly (§2.1 items 2–3) unchanged, with
   the marked-ness bonus noted in §2.4.
2. The stage lemma splits **SL1/SL2**; the "reachable-shift subspace" language of §2.2 is
   replaced by `Im d̄_k + P`-reachability; the draft shift formula's ε, ε′ are settled
   (§2.2 here) — signs are vacuous in Z_k, and the r₂-side formula differs from the
   draft's guess (the draft paired `[w₂,y]·[s,w₃]` on the r₀ side only; the r₂ side is
   `w² + [w,y] + [u,x] + [v,s]` with tails on (s,x), not (x,y)).
3. New named lemma: the **span theorem** (free version + descent), §2.3 — this is L4's
   real load-bearing wall, replacing the vaguer "per-level quadratic linear algebra".
   The quadratic/lookahead phenomenon (trajectory-dependence of the defect's
   coker-component) is real — measured — but the P-design routes around it: no
   second-order calculus in Lean.
4. k₀ = 3 (better than the plan's 4–5 guess); all base data in `Q₃`, order 256.
5. χ̂_k needs a small new API layer: level shadows of `chiR` with the modulus lemma
   `χ(λ_k) ⊆ 1 + 2^{k+1}ℤ₂` (elementary; the spike's GAP-checked-hom construction is the
   computational template, and it caught a wrong-modulus attempt immediately).

---

## 3. Step 3 — computational validation

### 3.1 Complete censuses (exhaustive; the completeness arguments are part of the result)

Completeness: (i) mod-λ₃ relator-kill and level-3 reachability depend only on the mod-2
seed (λ₂-lifts shift δ₃ exactly by Im d̄₃) — so 168 seed tests are exhaustive at k = 3;
(ii) `S⁰₄`-elements = (good seed) × (solution of the level-3 system) modulo
λ₃-freedom that changes neither δ₄'s class mod Im d̄₄ nor the matrix (Frattini-only
dependence, machine-checked) — so (good seeds) × 2^(ker-dim) covers k = 4 exhaustively.

**k = 3 (both directions, per-seed, exhaustive).** 6/168 seeds kill the relator mod λ₃;
χ̂-min-depth ≥ 3 ⟺ δ₃ reachable — exactly 2 seeds each direction:

* r₀-in-D_R: good `(y, sx, x)` (depths 3,5,5) and `(y, sx, s)` (3,5,3); the four bad
  seeds all have an x-or-sx-slot at depth exactly 2.
* r₂-in-D₀: good `(SY, Y, A)`-class seeds (depths 3,5,3); bads at min-depth 2.

**k = 4 (exhaustive, 256 trajectory classes per direction).** 64/256 reachable; per good
seed exactly 32/128; the χ-dichotomy is perfect:

| direction | depth ≥ 4, reachable | depth = 3, unreachable | anomalies |
|---|---:|---:|---:|
| r₀-in-D_R | 64/64 | 192/192 | 0 |
| r₂-in-D₀ | 64/64 | 192/192 | 0 |

**k = 5, 6 (sampled).** Census k = 5: 14/60 resp. 16/60 reachable (≈ the predicted 1/4 =
two fresh digits); class-7 deep run with χ recorded: k = 5: {(4,False): 9, (5,True): 1}
and {(4,False): 6, (5,True): 4}; k = 6: {(6,True): 1} and {(5,False): 3, (6,True): 1}.
Small samples at k = 6, but zero dichotomy violations anywhere, and the P-guided witness
runs (§3.4) add stall-free SL1/SL2 instances at every level 3…5 → 6 in both directions.

### 3.2 Controls (f = 3), the sharpest single result

`S⁰₄ = ∅` **proved by exhaustion at k = 3** for *both* placements: r₀-in-D′ (0/6 seeds
reachable) and r′-in-D_R (0/6). Mechanism, exposed per-seed: the η-slot χ-depth is
**capped at 2** for every seed (η = 5 mod 8 vs η′ = (1−8)⁻¹ = −1/7 ≡ 1 mod 8), so the
m(3)-filter can never be satisfied. The strict tower for the wrong pair survives to k = 3
(cup-form data is f-blind, matching the R2 spike's "counts first diverge at order 16"
group-order shadow) and dies exactly at k = 4. This confirms both that the stage lemma
genuinely consumes f = 2 through the numeric targets, and that the predicted failure
level was correct.

### 3.3 Tail-augmented (Serre-faithful) fallback — validated too

With strict-solve preference (absorbed digits are *forced*): good pair r₀-in-D_R absorbed
**no** digits through k = 5 on its trajectory (μ = (0,0)); r₂-in-D₀ absorbed
trajectory-dependent x-digits (μ_x = 8 then +16) — deformed relator still of content
v₂ = 2, consistent with f = 2. Controls: r₀-in-D′ forced μ_S = 4 at k = 3 (deforming
S⁴ → S⁸ = the target's own relator); r′-in-D_R forced μ_S = 4 then 8 (8+12 = 20 = 4·unit:
back to f = 2 content). The augmented process never stalled anywhere (= span theorem in
action). This design would work but is strictly heavier in Lean (relator family + a
phase-2 renormalization à la Serre p. 152); kept as fallback and as the O1/O2 shape.

### 3.4 P-guided witnesses (L3 test vectors)

The P-guided greedy (solve d̄w = δ, then adjust the two fresh χ-digits inside ker d̄)
ran **stall-free to k = 6 in both directions** — every solve succeeded on the first try
(SL1 instance) and every digit-fix was found in ≤ 7 random kernel tries (SL2 instance;
kernel dims 7/12/18). Witness words (free words in the target's generators; verification
transcript = relator depth, generation, χ-depths, all asserted):

* r₀-in-D_R, level 3: `(y, s·x, x)`.
* r₀-in-D_R, level 4: `t₁ = y·s·x⁻¹·s·x·s⁻¹y⁻¹sy·x⁻¹y⁻¹xy`, `t₂ = s·x·[s,y]`,
  `t₃ = x·[s,y]` (repo convention `[s,y] = s⁻¹y⁻¹sy`; χ-depths (6,5,5)).
* r₂-in-D₀, level 3: `(S·Y, Y, A)`; level 4: `t₁ = S·Y·(…12 letters…)`, `t₂` length 7,
  `t₃` length 11 (χ-depths (4,5,6)).
* levels 5–6: word lengths (49,26,11) → (195,178,123) resp. (48,25,35) → (196,145,165);
  full words + per-level transcripts in the scratch file `witness_words.txt` (see §5 —
  regenerate with one command; the words are deterministic given the pinned seeds).

For L3 as scoped (base case k₀ = 3): only the level-3 witnesses are *load-bearing*, in a
group of order 256; deeper witnesses are stress-test vectors.

### 3.5 Honest coverage + what went wrong on the way (recorded per charter)

* The naive strict greedy (no P) stalled at k = 4 (r₀-in-D_R) / k = 5 (r₂-in-D₀):
  first machine falsification of the draft local lemma. Both stalls are now understood:
  those trajectories had drifted to χ-depth-k-violating elements (the k = 4 census
  contains them among the 192).
* A first "lookahead" implementation reported fake strict witnesses for the *controls*:
  it searched "kernels" of the level-2 system, where the calculus is invalid (§2.1), and
  it never checked generation — the escape hatch was a mod-2 seed change to a degenerate
  (rank-15 instead of 18) matrix. Diagnosed via deterministic ground-truth replication;
  superseded by the census (which asserts generation and never touches level 2).
  Lesson encoded in the design: **k = 2 is outside the calculus; generation is a clause,
  not an afterthought.**
* Coverage statement: exhaustive k = 3, 4 both directions and both controls; sampled
  k = 5 (60+60 census + 20 deep + 2 witness), k = 6 (5 deep + 2 witness); span table
  exhaustive per level (a rank computation) k ≤ 6 groups / k ≤ 5 free; dims k ≤ 8.
  Nothing tested ever violated the dichotomy or the span statement.

---

## 4. L1 handoff — statements to freeze

1. **λ-tower API** (L2, unchanged from plan §2.4) + one new lemma family: the χ-shadows
   `χ̂_k` with `χ(λ_k) ⊆ 1 + 2^{k+1}ℤ₂` (k ≥ 2), naturality in k, and evaluation on the
   pinned targets. Numeric anchors to bake into statements: targets mod 2^9 =
   (−1, 1, 341) on (A,S,Y)-side, (253, 437, 7) on (s,x,y)-side; control discriminator
   η′ ≡ 1 ≠ 5 ≡ η mod 8.
2. **Levelwise sets** `S^P_k` exactly as §2.4 (three clauses; generation via the landed
   Frattini machinery; the χ-clause at modulus 2^k).
3. **Defect + d̄** by the §2.2 formulas (their Lean proof is the §2.1 calculus; state at
   k ≥ 3 only). d̄'s dependence on T through T̄ mod Frattini (machine-checked) is worth
   its own lemma — it is what makes the census-style base-case checks small.
4. **Span theorem**, free version + descent corollary (§2.3), with the relator-adapted
   tail pairs. Proof by the §2.5(a) reduction; if it stalls, O1 = axiomatize exactly this
   (owner gate), O2 = axiomatize levelwise nonemptiness (§7 of the plan; now
   machine-corroborated to k = 6 and, via dims, k = 8).
5. **Stage lemma = SL1 + SL2** (§2.4), k ≥ 3, both directions (mirror targets).

   **⚠ CORRECTION 2026-07-26 (L4c) — §2.5(b)'s two-functional separation plan is REFUTED,
   not merely incomplete.** Write `V = Z_k`, `W = Im d̄`. Both proposed functionals fail
   to descend to `V/W`, because **both are surjective on `W`**:
   - *ab-shadow*: `D₀^ab = ℤ₂³/(2A+4S)`, image of `λ_j` is `2^{j-1}G^ab`, so `V`'s shadow
     is `(ℤ/2)²` in `(c_S, c_Y)`. But `ab(d̄(w)) = 2·ab(w₀)` (commutators die) and
     `2·ab(λ_{k-1}) = ab(λ_k)`, so **`ab(W) = ab(V)`** — the `w₀`-diagonal alone saturates
     the entire abelian shadow.
   - *χ̂-depth*: `χ_R` is abelian-valued, so it factors through `G^ab`. On `V`, since the
     S-target is 1 and `v₂(η^{2^{k-1}} − 1) = k+1` **exactly**, the depth digit is
     precisely `c_Y`. So **`f_χ` IS the Y-coordinate of the ab-shadow** — not a second
     functional at all. *That is the coupling, made explicit.*

   Consequence: the tails have independent shadows `(1,0)`, `(0,1)`, yet `W` already
   surjects onto the shadow, so modulo `W` the tails are visible only through their
   `ker(ab)` components. **Any correct separation must live on `ker(ab|_V)` — the purely
   commutator part of the layer — where χ gives literally nothing.** A successor should
   not hunt for a second χ-type or abelian functional; there isn't one. SL1 needs a
   genuinely different ingredient.
6. **Base case** k₀ = 3: the §3.4 level-3 witnesses, `decide`-checked in Q₃ (order 256);
   χ-clause check mod 8. (Budget: trivial; the plan's 2^9–2^10 worry dissolves.)
7. **Assembly** (L5): unchanged (`exists_contSurj_of_levelwise_nonempty` refactor +
   Hopfian endgame); note the limit epi is automatically χ-intertwining (§2.4), which
   R15 may consume.
8. Suggested split: L4a = calculus + d̄ + SL2 (opus-able); L4b = span theorem + SL1
   (fable). The census scripts' numbers (this memo) are the regression targets for L1's
   stress lemmas.

---

## 5. Reproduction

Scratch (session-bound): `…/scratchpad/labute-spike/` — `towers.py` (dims, any class),
`harness.py` (Tower infra, naive greedy, formula checks), `harness2.py` (span tables,
forced-digit augmented greedy, matrix-invariance), `census.py` (exhaustive censuses, χ
machinery via GAP-checked hom, controls), `deep.py` (class-7 run), `witness.py`
(P-guided witnesses + `witness_words.txt`). All RNG-seeded; Sage 10.7, libgap
`PQuotient(G, 2, class, 4096)`. Runtimes: class 6 ≈ 40 s/tower; class 7 ≈ 4 min/tower;
class 8 dims ≈ 15 min/tower; censuses ≈ 1–2 min each. Every number quoted in this memo
is reproduced by those scripts from the two presentations and the pinned χ-targets; the
key numbers (dims, ranks, census counts, seed tables, digit streams, witness words to
k = 4) are all *in* the memo, per charter. Serre 252 read from the numdam scan
(pp. 145–155); fetched copy in the session's tool-results cache.

**Board effects** (for the orchestrator, not executed by LS): G1-style gate satisfied —
auto-run clause fires: dispatch L1 with §4 as the statement freeze; L4b carries the
named residual risk and the O1/O2 fallbacks; L3's scope shrinks to k₀ = 3 witnesses +
stress vectors; Labute-1967 library access drops from blocker to nice-to-have.
