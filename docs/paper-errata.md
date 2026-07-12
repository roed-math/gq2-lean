# Manuscript errata and formalization findings

**Date**: 2026-07-09 · **Amended**: 2026-07-09 — second-formalization completion findings (new
entries 2.11/3.5, strengthened 1.3/2.2/2.3) and the census update 15 → 9 · **Status of the
formalization**: complete — the library is sorry-free;
`main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)` is proved modulo the
9-axiom census of source-verified literature inputs (`docs/literature-axioms.md`,
`atlas-audit.md`).

## 0. Purpose and method

This document collects every place where formalizing the manuscript exposed an error, a gap, an
implicit load-bearing hypothesis, or a fragile phrasing — in the paper's text or in attempted
mechanical readings of it.  It has two audiences:

1. **The rewrite.**  §1 lists corrections the text needs; §2 lists hypotheses the rewrite should
   make prominent (each verified *load-bearing*, several with explicit counterexamples showing
   sharpness); §3 lists passages that are correct as written but were demonstrably misread by
   careful mechanical extraction and deserve a clarifying remark.
2. **The process record.**  §4 documents transcription hazards (relevant to Appendix B's machine
   block and to any external verification code); §5 records what the formalization *confirmed*,
   which is as much a part of the story as what it corrected.

**How things were caught.**  Three mechanisms, noted per entry:

- **Failed proof → counterexample**: a statement transcribed into Lean resisted proof, and the
  obstruction was crystallized into an explicit counterexample or a surviving cohomological
  obstruction.
- **Sharpness witness**: a hypothesis was tested for removability and a literature or small-group
  counterexample shows it cannot be dropped.
- **Independent cross-validation**: a second, independent formalization of the same manuscript (a
  GPT-5.5-Pro-driven pipeline; snapshots in `GPT_formalization/q2_v428_active/` — the
  39-axiom intermediate state — and `GPT_Fable_formalization/` — its completion, sorry-free
  with 7 axioms) hit the same corners.  Where both projects independently converged on the same
  reading or the same fix, that is strong evidence about the text.  Entries 2.11 and 3.5, and
  the strengthenings of 1.3/2.2/2.3, come from the completion's adversarial soundness sweep
  (2026-07-05 → 09).

**Anchors.**  Paper references use the manuscript's labels and display numbers; line numbers
(`l.NNNN`) refer to the formalized revision, the snapshot at
`GPT_formalization/q2_v428_active/reference/q2_manuscript.tex` (5543 lines).  Lean witnesses are
declarations in `GQ2/` unless said otherwise.

**Summary counts**: 3 corrections to the text (§1) · 11 load-bearing implicit hypotheses (§2) ·
5 fragility remarks (§3) · 4 transcription-control notes (§4).

---

## 1. Corrections to the text (errata proper)

### 1.1 Display (134) omits the cup term `γ ⌣ a`  [§8]

- **Where**: display (134) (the total scalar phase `Δ_{χ,κ}` of the edge-killing shear).
- **Finding**: carrying out the shear as an instance of Lemma 6.22 produces the total phase
  `Δ = δ + Θ⁰_q̄(a) + (γ ⌣ a)`; display (134) as printed omits the `γ ⌣ a` cup term.
- **Impact**: none on the results — Prop 8.9 existentially quantifies the phase family
  `(μ, G⁰, D_T, phase)`, so the count-level content is unchanged; but the display itself is
  incomplete as an identity.
- **How caught**: failed proof — proving (134) verbatim from the (proved) `lemma_6_22` leaves the
  cup term; recorded 2026-07-05 (P-16d4).
- **Witness**: `GQ2/AffineTLift.lean` (`prop_8_8_target`), `SectionSix.lemma_6_22`;
  `docs/section8-extraction.md` §"P-16d statement corrections", item 5(b).
- **Fix for the rewrite**: add the `γ ⌣ a` term to (134) (or remark that the phase is taken
  modulo the cup contribution, which the existential formulation absorbs).

### 1.2 Lemma 2.5 (`lem:reconstruction`, l.371): "the same number" must mean *cardinality* — the ℕ-valued reading is false  [§2]

- **Where**: `lem:reconstruction` — "Let $P$ be a topologically finitely generated profinite
  group and let $Q$ be **any** profinite group.  If $|\Sur(P,H)|=|\Sur(Q,H)|$ for every finite
  group $H$, then $P\cong Q$." — and the proof's first step, "Since $P$ is finitely generated,
  $\Sur(P,H)$ **and hence** $\Sur(Q,H)$ are finite" (l.383).
- **Finding**: the lemma is correct exactly when `|·|` is read as genuine cardinality (equality =
  a bijection).  Under the other natural formal reading — counts valued in ℕ with infinite sets
  read as `0` (Lean's `Nat.card`; equally, any convention that assigns non-f.g. groups a
  "count") — the one-sided statement is **false**: `P = 1` and `Q = (ℤ/2)^ℕ` have equal
  ℕ-counts for every finite `H` (both `0` except at `H = 1`) but are not isomorphic.  The proof's
  "hence" is precisely the transport of finiteness across the assumed bijection, i.e. it *uses*
  the cardinality reading.
- **How caught**: failed proof + counterexample in our formalization (the ℕ-count form needed `Q`
  topologically finitely generated as a second hypothesis); independently, the GPT formalization
  chose `Cardinal.mk` equality for the same reason.  Both projects then proved the lemma in its
  faithful one-sided form.
- **Witness**: `GQ2/Reconstruction.lean` — `reconstruction` (ℕ-count form, two-sided f.g., with
  the counterexample in the docstring) and `reconstruction_of_equinum` (the faithful one-sided
  form); GPT `Profinite/Reconstruction.lean` `profinite_reconstruction_of_surj_counts`
  (`Cardinal.mk`, one-sided).
- **Fix for the rewrite**: keep the statement; add one sentence: *"Here $|\cdot|$ denotes
  cardinality: the hypothesis is that the two sets are equinumerous.  (If the counts are instead
  read in ℕ with some convention for infinite sets, the one-sided statement fails —
  $P=1$, $Q=(\mathbf{Z}/2)^{\mathbf{N}}$ — and $Q$ must also be assumed finitely generated.)"*

### 1.3 The zero-count displays need `V ≠ 0`  [§6, displays at l.2736–2737, l.2772, l.3354–3355]

- **Where**: the displays `#\{q=0\} = 2^{d-1} ∓ 2^{d/2-1}` (unramified/ramified) and
  `\#Q^{-1}(0)=2^{d-1}+(-1)^{\Arf(Q)}2^{d/2-1}`.
- **Finding**: at `d = 0` (the zero module) the left side is `1` and the right side is not
  (`1 ± 1/2` as real numbers; `0` or `2` under truncated integer conventions) — the displayed
  formula is false for `V = 0`, though every use in the paper has `V` a nontrivial (simple)
  module, where `d = \dim V` is even and `≥ 2` by nonsingularity.
- **How caught**: independent cross-validation — the GPT project's transcription of these
  displays as axioms over *all* finite `V` is refuted inside their own repository (their
  `Quadratic/DicksonCount.lean`, `dickson_count_false_at_zero`).  Our formalization carries the
  guard throughout (`hVne : V ≠ 0`; the dimension in the form `card V = 2^{2m}, 1 ≤ m`).
- **Fix for the rewrite**: attach "for `V ≠ 0`" (equivalently `d ≥ 1`; in the nonsingular case
  `d = 2m ≥ 2`) to the displays, so they are correct as free-standing statements.
- **Update (2026-07-09)**: the second formalization's completion applied exactly this fix — the
  refutable axiom pair was deleted and re-homed as `[Nontrivial V]`-guarded theorems.

---

## 2. Implicit or standing hypotheses verified load-bearing

These are places where the paper is **correct**, but a hypothesis is stated once (in a standing
convention, an earlier lemma, or surrounding prose) and then silently consumed.  In each case the
formalization (i) initially dropped the hypothesis when reading the statement in isolation,
(ii) discovered the resulting statement is unprovable — in most cases **false**, with an explicit
counterexample — and (iii) restored the paper's hypothesis.  The rewrite should make each one
locally visible at the point of use.

### 2.1 Lemma 6.21 is *relative to the fixed equivariant class* `κ⁰_q` — the hypothesis cannot be dropped

- **Paper text**: "Let `q` be a nonsingular `C`-invariant quadratic form on `V`, *and assume that
  a zero-section-normalized equivariant class `κ⁰_q ∈ H²(V⋊C, 𝔽₂)` restricting to `q` on `V` has
  been fixed*."
- **Finding**: extracting only the conclusion (the splitting criterion) yields a statement
  asserting the splitting for *every* `(B, ξ)`.  That is not provable by the paper's mechanism —
  and the obstruction is intrinsic: the coherence defect of any pointwise repair is again exactly
  the class `[B_q^♭ f] = o(q,ρ) ∈ H²(C, V^∨)` (the obstruction to lifting the `C`-action to the
  `q`-extraspecial cover), which the fixed `κ⁰_q` is what trivializes.  The `m`-family of the
  equivariant factor set *is* the coherent automorphism family `α_c` of the paper's proof.
- **Witness**: `docs/orchestration/p15i-transgression-gap.md` (full analysis; resolution
  user-approved 2026-07-04); `GQ2/Transgression.lean` (`splitting_of_global_cocycle`,
  sorry-free), `SectionSix.lemma_6_21` (amended form, proved).
- **For the rewrite**: keep the hypothesis displayed in the lemma (not in the preamble); consider
  a one-line remark that it is genuinely necessary (the equivariance obstruction survives without
  it).

### 2.2 Existence of `κ⁰_q` is Lemma 6.3's content, and its hypotheses are sharp (Griess) — recommend adding the citation

- **Paper structure**: Lemma 6.1 proves the equivalence "(59)+(60) ⟺ lifted action" and *assumes*
  the lift; the existence result is Lemma 6.3, for **simple self-dual tame** `V`.
- **Finding**: the unqualified existence statement (arbitrary finite `𝔽₂[C]`-module) is **false**:
  a `κ⁰`-datum is a splitting of `1 → V^∨ → Aut(E_f) → O(q) → 1` pulled back along `ρ`, and this
  sequence is non-split for `C = O(q)` at large extraspecial `E_f` — R. L. Griess,
  *Pacific J. Math.* **48** (1973).  The paper's hypotheses on Lemma 6.3 are exactly what rescue
  existence.
- **How caught**: failed proof at the over-general transcription; sharpness witness from the
  literature.  (The manuscript does not currently cite Griess anywhere.)
- **Witness**: `docs/section9-extraction.md` deviation 4 and §P-17e; `SectionNine.kappa0_exists`
  (amended with `hsimple`/`htame`, proved).
- **For the rewrite**: at Lemma 6.3, add a remark with the Griess citation: the simplicity/tameness
  hypotheses are not conveniences — the lifting problem is genuinely obstructed in general.
- **Convergence (2026-07-09)**: the second formalization's citability audit independently hit the
  same obstruction one layer down (`lem:extraspecialconnecting` l.2102–2131, `lem:basedetclass`
  l.2286–2360): its lane graded the high-even-dimensional *split base-model* claim "suspect …
  treat as false" against Griess (non-split for `n ≥ 3`) before resolving it by proof — exactly
  the confusion a Griess citation at the base-model/`κ⁰` layer would preempt.

### 2.3 Prop 7.4 consumes §7's standing framed-target hypothesis, and it is sharp at `H¹`

- **Finding**: step 2 of Prop 7.4 (`q_λ|_{T₀} = 0`) needs `H¹(H_V, V^∨) = 0` for the head-action
  image `H_V`.  This holds for **tame** heads (odd inertia via `s⁻¹ts = t²` in the ramified case;
  odd-cyclic image in the unramified case) but is **false for general finite heads** — sharp
  already at `H¹`, e.g. `L₃(2)`-type action images.  A transcription of Prop 7.4 without the
  framed-target head data is unprovable.
- **Witness**: `docs/section67-extraction.md` §"P-15 amendments" (soundness amendment #3);
  `GQ2/SectionSeven.lean` `prop_7_4` (amended, proved).
- **For the rewrite**: restate the standing assumption (tame head `π : Y ↠ H`, `H` a quotient of
  `T_tame`) in Prop 7.4's own hypothesis list.
- **Second witness (2026-07-09)**: the second formalization independently tripped on the same
  proposition (`prop:simpleheaddet`) at the level of `C` itself: its residual demanded a
  nontrivial odd *normal* subgroup of `C`, which can fail to exist (an `SL₂(3)`-shaped `C` —
  wild `Q₈` inside the action kernel, tame `C₃` on top; the 3-Sylows are not normal), whereas
  the manuscript's argument (l.3749–3760) works at the acting quotient `H_V = C̄`, which is
  metacyclic with normal odd inertia.  Recommendation sharpened: phrase step 2 as explicitly
  *passing to the acting image `H_V`* before invoking odd-inertia normality.

### 2.4 "Tame module" in §5 must be *defined* to include σ₂-triviality — it is an input, not a consequence

- **Paper text**: Lemma 5.13 is stated for a "nontrivial simple **tame** `𝔽₂[C]`-module"; the
  wild-core half of tameness (`x₀, x₁` act trivially) is secured by Lemma 5.12 from the pro-2-core
  admissibility clause.
- **Finding**: the proofs (the `h₀`-shadow collapse, Lemma 5.3(i), and the pairing computation of
  5.13/5.14) additionally need **σ's 2-primary part `σ₂` to act trivially** on `V`.  This is
  *not* implied by simplicity plus the wild-core clause: in `C = S₃ ≅ GL₂(𝔽₂)` an involution acts
  nontrivially on the 2-dimensional simple module.  Arithmetically the clause is the tameness of
  σ (Frobenius; its 2-part lies in wild inertia) — a genuine input.  Separately, the split-case
  normal form needs `V^S = 0` (invertibility of `1 + S⁻¹`), a refinement of "σ acts nontrivially".
- **Witness**: `docs/orchestration/p13-normal-form-hypothesis-gap.md` (§7, with the counterexample
  and the applied fix); `GQ2/FoxHeisenberg.lean` (`lemma_5_13_*`, `prop_5_15`, all proved with the
  full tameness hypotheses).
- **For the rewrite**: give "tame `𝔽₂[C]`-module" a one-line displayed definition — *the full wild
  inertia (the images of `x₀`, `x₁`, **and** `σ₂`) acts trivially* — and cite it from 5.13/5.15;
  note that Lemma 5.12 supplies only the `x₀, x₁` half.

### 2.5 The exponent-2 constraint on the decoration group `E` is load-bearing — repeat it inside Def 4.1

- **Paper text**: the §4 setup (l.1164) fixes "an **elementary abelian 2-group** `E`"; Def 4.1
  (`def:framed`, l.1174) then says only "θ_Y : Y → E is a homomorphism".
- **Finding**: the constraint is consumed twice in the proof of Theorem 4.2 — Lemma 7.3
  (`lem:decorationblock`: "every homomorphism to an *elementary abelian 2-group* vanishes on `K`")
  and the terminal case (decorations kill the odd complement).  A transcription of Def 4.1 taken
  standalone, with `E` an arbitrary finite abelian group, produces a Theorem 4.2 statement whose
  proof does not go through (and §10 only ever uses `E = 0`).
- **How caught**: failed proof — our Def 4.1 transcription had generalized `E`; the induction
  forced the exponent-2 hypothesis back in (P-17a, 2026-07-06).
- **Witness**: `docs/section9-extraction.md` deviation 1; `SectionNine.thm_4_2` (with
  `hE2 : ∀ e : E, e^2 = 1`, proved).
- **For the rewrite**: repeat "`E` elementary abelian of exponent 2 (as fixed above)" inside
  Def 4.1, so the definition is self-contained.

### 2.6 (139)/(140) hold under §7.4/§6.1 *standing data*, not for arbitrary central covers

- **Finding**: Prop 8.9's closed system quantified over a bare "scalar central cover of `B`" is
  false — there are covers for which (139) fails.  The paper proves (139)/(140) under its
  standing data: the square form of `p_λ` restricted to `M_B` (polar radical ⊇ `T_B`, vanishing
  on `T_B` — Prop 7.4's output) and a *fixed* equivariant base class `κ⁰_{q̄_λ}` for the descended
  module `V ≅ M_B/T_B` (the Lemma 6.1/6.21 datum of entry 2.1).
- **Witness**: `docs/section8-extraction.md` §"P-16d statement corrections", item 3;
  `GQ2/SectionEight.lean` (`RecursionFrame.Enrichment`), `prop_8_9` (proved at the enrichment).
- **For the rewrite**: list the standing data in Prop 8.9's hypothesis line (or a displayed
  "Setting" block opening §8.3), rather than leaving it distributed across §§6–7.

### 2.7 The reciprocity orientation of the tame data is load-bearing for the ramified sign — and it must be pinned to *the* reciprocity map

- **Finding**: the ±-sign in the ramified local computation (Prop 6.18's Gauss-sign comparison,
  hence Theorem 4.2) depends on the tame quotient's normalization against local reciprocity: two
  clauses — *units land in the `ν_t`-kernel* (units ↦ inertia, Serre *Local Fields* XIII §4,
  Prop. 13 and its corollary; Neukirch ANT V (6.2) is only for `n > 0`)
  and *`rec(2)` has geometric σ-coordinate `1`* (units are unramified norms, Neukirch V (1.2) /
  NSW (7.1.2)(i)).  Formalizing Theorem 4.2 over abstract boundary data forced these clauses to
  be carried as an explicit hypothesis (`TameUnitOrientation`); the concrete boundary of §3
  satisfies them.  A subtlety worth recording: the clauses are correct only *relative to the fixed
  reciprocity isomorphism* — quantifying them over all class-formation isomorphisms is false
  (Frobenius-coordinate twists).
- **How caught**: failed proof at the ramified local twin (the sign is otherwise undetermined);
  escalation P-25, user-approved 2026-07-06 (axiom B10 strengthened in place to the oriented
  B10′).
- **Witness**: `docs/literature-axioms.md` §B10 (oriented form B10′);
  `GQ2/TameTwoQuotient.lean` (`TameUnitOrientation`), `GQ2/TameOrientationWitness.lean`
  (discharged at the concrete boundary); `SectionNine.thm_4_2` (carries the orientation
  hypothesis).
- **For the rewrite**: state the orientation normalization as an explicit standing convention in
  §3 (with `lem:standardorientation` / `prop:compatiblemarking`), and point to it from the
  ramified sign computation in §6 — one sentence in each place suffices.

### 2.8 Lemma 10.1: continuity of the induced frame comes from compactness

- **Finding**: the frame `α_f` induced by a lift `f` is continuous because the tame coordinate is
  a *topological quotient map* — a continuous surjection from a compact source onto the Hausdorff
  `T_tame` is closed, hence a quotient map.  Without compactness of the source the descended
  homomorphism need not be continuous; the lemma's statement should carry the (always satisfied)
  compactness explicitly.
- **Witness**: `docs/section10-extraction.md` deviation 10; `SectionTen.lemma_10_1` (proved).
- **For the rewrite**: one clause in the proof ("since Γ is compact and `T_tame` Hausdorff, the
  tame coordinate is a quotient map, so the induced frame is continuous").

### 2.9 §7's "marked normal 2-subgroup" is essential to Lemma 7.1 — keep it visible at the block choice

- **Finding**: Lemma 7.1's head clause (`R ≤ K ∩ S`) is **false** without the standing hypothesis
  that the marked kernel is a 2-group: `Y = S₃`, `L = P = K = A₃`, `S = ⊥` satisfies every other
  clause of the block, but `Φ(A₃) = A₃ ≰ K ∩ S`.
- **How caught**: failed proof (the transcription of the block had dropped the standing
  hypothesis; the attempted proof of the head clause produced the counterexample).
- **Witness**: `GQ2/SectionSeven.lean` `MinimalBlock.h2L` (field docstring records the
  counterexample); `lemma_7_1_head` (proved).
- **For the rewrite**: repeat "recall `L_Y` is a finite 2-group" at the §7 opening where the block
  `S < P ≤ L_Y`, `K` is chosen.

### 2.10 §§6.16–6.18 genuinely need the general-dyadic-base classical inputs — make the citations match

- **Finding**: Lemma 6.16's arithmetic runs over a general finite dyadic base `k = K₀` (a tame
  extension of `ℚ₂`), not just `ℚ₂`.  A reduction of the Evens–Kahn input to base `ℚ₂` is **not
  available**: restriction reaches only a 3-dimensional subspace of `k^×/(k^×)²`, and the
  corestriction route is equivalent to cor–inv compatibility, itself a general-base CFT input.
  Step 2 of 6.16 additionally consumes two general-base facts: the dyadic symbol–norm criterion
  (Serre, *Local Fields* XIV §2 Prop. 7(iii), V §2 Prop. 3) and unramified unit-norm surjectivity.
  The formalization's axiom census was amended accordingly (B9 base-generalized; B11a/B11b added;
  user-approved 2026-07-03).
- **Witness**: `docs/section67-extraction.md` §"P-15 amendments" (escalation 6.16);
  `docs/literature-axioms.md` B9/B11a/B11b entries; `GQ2/HilbertLedger.lean`, `GQ2/DimClose.lean`.
- **For the rewrite**: cite Evens–Kahn (Evens; Kahn; Kozlowski) in their general-base forms at
  6.16, and name the two auxiliary norm facts where they are used.

### 2.11 `prop:defduality` is scoped to the ρ-structured setting — make the marking-compatibility explicit

- **Where**: `prop:defduality` (l.1917–1972), with its inputs `lem:simpletame` (l.1799) and
  `lem:simplenormalforms` (l.1812).
- **Finding**: the duality/normal-form package is asserted for markings *compatible with the
  fixed boundary frame* (the ρ-structured setting §5 operates in).  Quantifying its
  row-surjectivity clauses over arbitrary markings `q` produces a false statement: the second
  formalization had to weaken exactly this way, conditioning the clauses on frame-compatible
  markings, recording "manuscript defduality is for the ρ-structured setting;
  unconditional-∀q was a false-axiom hazard".  Our formalization carries the same scoping
  through its standing boundary-compatibility hypotheses (cf. entry 2.4's tameness clauses — an
  adjacent but distinct scoping point).
- **How caught**: independent cross-validation (the completion's soundness sweep, 2026-07-09).
- **For the rewrite**: state the frame-compatibility scope in `prop:defduality`'s own hypothesis
  line rather than inheriting it silently from the section's running setup.

---

## 3. Fragile passages — correct as written, demonstrably misread (add remarks)

The first four items concern §7–§9's induction interfaces.  Evidence that they are fragile is
empirical: the independent GPT formalization's 2026-07-01 manuscript-verification pass found its
own machine-generated §7 interface had mis-transcribed **all four**, in each case *strengthening*
the text into a false statement (its PROGRESS.md "SOUNDNESS FINDINGS"); our formalization,
proving rather than axiomatizing, was forced onto the correct readings from the start.  The
convergence of both projects on the same four corners is a strong signal these deserve explicit
remarks in the rewrite.  That project's completion (2026-07-05 → 09) then found and repaired
**fourteen further falsifiable residual statements** — two outright inconsistent — with every
repair again converging on a manuscript-true form; its findings that bear on the manuscript
itself are entries 2.11 and 3.5 and the strengthenings of 2.2/2.3.

### 3.1 `R = Φ(K) = 1` is a legal, terminating branch (l.4429/4437, l.4542)

The text says it plainly ("when `R ≠ 1`"; "If `R = 1`, then `B = Y` and the induction closes at
this [elementary] stage") — but a reader tracking only the `R ≠ 1` machinery can assume
`|Φ(K)| > 1` unconditionally, which is false (elementary minimal `K`, e.g. `Y = V ⋊ H`, `K = V`).
Our Theorem 4.2 proof carries the case split explicitly (`Blk.R = ⊥` → the M-stage lane).
*Recommendation*: display the `R = 1` / `R ≠ 1` dichotomy as a numbered case list at the top of
the inductive step, rather than in running prose.

### 3.2 "Minimal subject to `KS = P`" means ⊆-minimal, not least (l.3623)

The least normal subgroup with `KS = P` need not exist (two incomparable normal complements over
a diagonal lower); every use in the paper needs only ⊆-minimality (applications are to normal
subgroups **contained in** `K`), and existence then follows by finite descent.
*Recommendation*: say "minimal under inclusion (such `K` exist by finiteness; we fix one)".

### 3.3 The chosen chief factor is the *first* non-scalar one, and firstness is used (l.3622)

"All chief factors below `S` are scalar" is load-bearing for `lem:collapse` (the `[S,Ñ] = 1`
coprime step); for an arbitrary non-scalar chief factor the collapse fails.  In our block this is
the `scalar_below` datum, obtained by taking `S` inclusion-maximal among normal scalar stacks.
*Recommendation*: make "first" part of the displayed choice ("choose `S` maximal with all chief
factors below it scalar, then `P` minimal above"), not a property recalled mid-proof.

### 3.4 `𝒳_R = 0` is legal in the `R ≠ 1` branch (`prop:finalfourier`)

`prop:finalfourier` needs only `R ≠ 1`; the character set `𝒳_R` may be empty, in which case the
recursion degenerates to `e_Γ(Y) = z_R · e_Γ(B)` and no minimal-block invariant is available.
Our closed-system step case-splits on `∃ λ ≠ 0` explicitly and returns the degenerate count
otherwise.  *Recommendation*: one sentence at `prop:finalfourier` noting the `𝒳_R = 0` case and
what the recursion becomes there.

### 3.5 `prop:localzero` / `prop:candidatezero` (l.3349–3403, l.2731–2775): the Gauss sign belongs to the *fixed* class `κ⁰_q`, not to an arbitrary bundle

Both zero-count propositions compute at the canonical zero-section-normalized equivariant class
`κ⁰_q` (the Lemma 6.1/6.3 datum; cf. entry 2.1), and the normalization is load-bearing for the
**sign**: pinned bundles form a torsor under an `H¹(C,V)`-gauge, and a gauge shift by a class
`[A] ≠ 0` flips the descended Gauss line by a computable per-lift phase.  Reading the
propositions as asserting one bundle-independent sign is therefore an over-reading.  Both
formalizations converged on the same discipline — evaluate at one definite pinned bundle: ours
fixes the 6.22-normalized `κ⁰_{q̄_λ}` throughout §§8–9; the second formalization first asserted
a bundle-uniform sign, found it "exceeds `prop:localzero` (manuscript computes only at canonical
`κ_q⁰`)" under the gauge action, and repaired to a chosen-witness form.  *Recommendation*: one
sentence at `prop:localzero`/`prop:candidatezero` noting that the sign is attached to the fixed
`κ⁰_q` — which is exactly why §6 fixes the normalization once and §§8–9 reuse it.

---

## 4. Transcription control (process notes; relevant to Appendix B)

None of these are errors in the paper — they are hazards discovered when transcribing it, recorded
because Appendix B advertises a machine block for external verification and the same hazards will
face any independent transcriber.

### 4.1 The `h₀` haplography — and how the formalization caught it

The repo's transcription of eq. (3)'s auxiliary word `h₀` dropped the bare `d₀` factor
(`… dg·d0²·hc` for the paper's `… dg·d0·d0²·hc` — a classic haplography next to `d₀²`).  The bug
was **caught by the paper's own Prop 5.8**: for the corrupted word the mod-2 Fox exponent vector
of the wild relator is `(0, 0, e+1, e+1)` (proved), while the paper asserts `(0, 1, 0, 0)` — and
the Stokes corrections then fail to cancel, with a concrete finite counterexample.  Restoring the
paper's word, the formalization *verified* Prop 5.8's computation exactly, including the
parenthetical "the two occurrences of `d₀` cancel" — via the (provable) observation that every
valid `ω₂`-representative is odd.  Full record: `docs/erratum-h0-transcription.md`.
**Note for Appendix B**: external verification code transcribed from the same source should be
checked for the same haplography (`dg*d0*d0^2`, not `dg*d0^2`).

### 4.2 Display (132): the `|B¹(V)|` factor belongs inside `μ`

An intermediate transcription moved the coboundary factor out of the multiplicity `μ`; display
(132) as printed keeps it inside, and the printed form is the correct one (the un-quotiented
`red_T`-enumeration carries the residual factor).  Recorded as Bug 1 in
`docs/orchestration/p16d6c-handoff.md`; the proved count matches the paper.

### 4.3 Display (137): the stratum sum ranges over `J` surjecting onto `C` only

The unrestricted sum over proper strata overcounts (strata missing `C` have empty `Z`-slices but
nonzero `m_{Γ,λ}`).  The paper's (137) is stated with the surjectivity restriction; a transcriber
who drops it gets a false identity.  (`docs/section8-extraction.md`, P-16d correction 2.)

### 4.4 "Normalized factor set" includes the 2-cocycle identity

Lemma 6.1's factor-set data (59)–(61) includes associativity of the twisted product (the additive
2-cocycle identity for `f`).  A field list that drops it makes the graph pullback fail to be a
cocycle.  (`docs/section67-extraction.md`, P-15 amendment 1.)

---

## 5. What the formalization confirmed (selected)

For balance, the headline confirmations — the manuscript's load-bearing computations survived
full verification:

- **The wild-relator ledger of §5 is exactly right** (after the transcription fix of §4.1): the
  ε-exponent computation of Prop 5.8, the `h₀`-shadow collapse (Lemma 5.2/5.3), the wild Fox row
  (Lemma 5.5), and the Hessian pairing (Lemma 5.14) are all proved as stated.
- **The §7 block theory is exactly right** once the standing hypotheses are carried (entries
  2.3/2.9): Lemmas 7.1–7.4 and the `R = Φ(K)` structure are proved, including the fourth-power
  argument of `lem:collapse` reproduced verbatim in Lean.
- **The closed recursion of §§8–9 is provable as displayed** — (136)–(142), the M-stage partition,
  the terminal correspondence, and the master induction of Theorem 4.2 are all proved; notably the
  **terminal case needs no classical input at all** (`terminal_count_eq` has an empty axiom trace:
  Schur–Zassenhaus and the marked-quotient correspondence are proved outright).
- **Lemma 2.5's only classical input is discharged**: Hopficity of finitely generated profinite
  groups (Ribes–Zalesskiĭ 2.5.2) is proved from scratch, so the reconstruction lemma is
  formalized with no axioms.
- **The four §7 corners of §3 were navigated identically by two independent formalizations** —
  the strongest available evidence that the corrected readings are the intended mathematics.
- **The final trust base is small, shrinking, and fully source-verified**: at completion the
  theorem rested on the 15-axiom census, each a named classical result checked verbatim against
  its cited source (`docs/literature-axioms.md`, `atlas-audit.md`); post-completion work has
  since removed six of them (B7′, B11b, B12, B13 **proved** in-tree; the unused B2 and B4
  **deleted**), bringing the census to **9** — with every remaining census axiom in the
  capstone's closure (census = trust base).  Notably, no Demushkin-classification axiom
  survives: the marked-Labute presentation input the parallel formalization assumes is, in this
  tree, off the proof path entirely.

---

## Appendix: index by manuscript anchor

| Anchor | Entry | Type |
|---|---|---|
| Lemma 2.5 `lem:reconstruction` (l.371) | 1.2 | erratum (precision) |
| eq. (3) `h₀` / Appendix B block | 4.1 | transcription warning |
| Lemma 5.13 / Prop 5.15 ("tame module") | 2.4 | implicit hypothesis |
| `prop:defduality` (l.1917–1972) | 2.11 | implicit hypothesis (ρ-structured scope) |
| Prop 5.8 | 4.1, §5 | confirmed |
| Lemma 6.1 (factor sets) | 4.4 | transcription warning |
| Lemma 6.3 (κ⁰ existence) | 2.2 | sharpness (add Griess citation) |
| Lemma 6.16–6.18 (deep units) | 2.10 | citation scope |
| Prop 6.9 / Arf displays (l.2736, l.2772, l.3354) | 1.3 | erratum (edge case) |
| `prop:localzero` / `prop:candidatezero` | 3.5 | fragility remark (κ⁰-pinned sign) |
| Lemma 6.21 (transgression) | 2.1 | implicit hypothesis |
| §4 setup + Def 4.1 `def:framed` (l.1164/1174) | 2.5 | implicit hypothesis |
| Thm 4.2 `thm:fixedframe` (l.1205) | 2.5, 2.7 | implicit hypotheses |
| Lemma 7.1 | 2.9 | implicit hypothesis (S₃) |
| Prop 7.4 `prop:simpleheaddet` | 2.3 | implicit hypothesis (sharp at H¹; acting-quotient scope) |
| Prop 8.9 / (139)–(140) | 2.6 | implicit standing data |
| display (132) | 4.2 | transcription warning |
| display (134) | 1.1 | erratum (missing term) |
| display (137) | 4.3 | transcription warning |
| `thm:closedrecursion` (l.4427ff) | 3.1–3.3 | fragility remarks |
| `prop:finalfourier` | 3.4 | fragility remark |
| Lemma 10.1 | 2.8 | implicit hypothesis (topology) |
