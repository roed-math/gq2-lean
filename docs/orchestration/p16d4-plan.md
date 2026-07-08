# P-16d4 execution plan — Lemma 8.7 (affine T-lifting) + Prop 8.8/(135), target side

**F-half design (Fable, 2026-07-05); O-half = this work order.**  Claim the P-16d4 board
row (◐) before starting.  Deps: P-16d1 ☑ only.  Axiom budget **∅** (std-3 throughout —
see the P-13f firewall, §7 below).  Paper: pp. 40–43 ((130)–(135) and the (140)-proof
paragraph); the pdf is `paper/A_Profinite_Presentation_for_G__Q_2.pdf`.

## 0. Role in the d-graph

d4 builds the **zero-edge engines** consumed by d6's `phase140` derivation and d5's
witness: when the radical edge of `p_λ` vanishes (the `∃ N`-branch of (140)), the paper

1. identifies `B/T ≅ V ⋊ C` via Lemma 6.21 (**proved**, needs the κ⁰_q datum = the
   `Enrichment` fields from P-16d1),
2. classifies `M`-lifts over a lower map `ρ : Γ ↠ C` by their `V`-coordinates with a
   constant multiplicity (Lemma 8.7, (131)/(132)), and
3. normalizes the per-χ constrained sums into shifted base Gauss sums (Prop 8.8, (135))
   so that `lemma_8_5` ((126), **proved**) applies.

d4 delivers 1, 2, and the **target-side half** of 3.  The Γ-side pullback of (135) (which
consumes cor. 5.17 / props 5.15–5.16 = P-13f material) is **out of scope** — it belongs to
d6, whose deps include P-13f.

## 1. Binding design decisions (F-half; deviations to ledger)

- **D1 — cocycle level, not class level.**  Paper 8.7 counts cohomology classes with
  multiplicity `μ = |B¹(V)|·|Z¹(T)|`.  We stay at cocycle level: `M`-lifts over `ρ` fibre
  over crossed `V`-cocycles with fibre `|Z¹(T)|`; the `|B¹|`-factor is absorbed into the
  cocycle count (`|Z¹(V)|`-sized `W` in the 8.5-application; d6 reconciles with the
  5.15/5.16 numerics).  No quotient-set defs, no class-well-definedness lemmas.
  Add a deviation-ledger entry (`docs/section8-extraction.md`, P-16d corrections list)
  in the same spirit as "liftability encodes obstruction-vanishing".
- **D2 — 8.8 is target-side only.**  The Lean Prop 8.8 is a **finite `C`-level cochain
  identity** (the edge-killing shear, an instance of `lemma_6_22` at
  `(E.qbar l h, E.dat l h)`), producing the total scalar phase `Δ`.  Do NOT state the
  Γ-level (135): its proof needs 5.17 (P-13f).  The paper itself notes "Δ_{χ,κ} is
  defined on the finite target C; no comparison map between the two source H¹-spaces is
  involved" — this cut is paper-faithful.
- **D3 — the Lean `Δ`-scalar is the 6.22 output.**  `lemma_6_22` shears
  `κ⁰ + Γ_γ + inf δ` to `κ⁰ + Γ_{γ+B♭a} + inf(δ + Θ⁰_q(a) + γ⌣a)`.  With `B♭a = γ`
  (edge-killing) define `DeltaScalar := δ + thetaPhase dat a + gammaCupA γ a`.  The
  paper display (134) has **no cup term** — do not chase display equality: `prop_8_9`
  **existentially quantifies** the phase family `(μ, G⁰, D_T, phase)`, so d5/d6 are free
  to build the covers from the Lean-`Δ`.  Record the difference as a ledger note
  ("(134) as displayed vs the 6.22-normalized scalar; count-level content unaffected
  because the family is ∃-bound").
- **D4 — the splitting `σ` is data-with-spec** in the 8.7 engines
  (`(σ : YC →* Q) (hσ : ∀ cc, piQbar (σ cc) = cc)`); its **existence** is the separate
  6.21-application `descended_splitting`.  House pattern (`a_χ` in `lemma_8_5`,
  `lam` in `prop_7_4`).
- **D5 — boundary-framing rides free over `ρ`.**  Both boundary components of a `B`-lift
  factor through the `C`-stage: `TB.piY = TC.piY ∘ piBC` (proved inline as `hheadBC` in
  `partition137_of`, SectionEight.lean:1736 — export it) and `TB.thetaY = TC.thetaY ∘
  piBC` (same `MonoidHom.cancel_right RF.piB_surj` proof from `TB_theta`/`TC_theta`/
  `piBC_comp`).  Hence any continuous hom over a boundary-framed `ρ` is itself
  boundary-framed — the `IsBoundaryLift` clause in `zBC`'s pairs is redundant given the
  over-`ρ` clause, and **no `θ|_T = 1` hypotheses are needed anywhere**.  This kills the
  main threat to the torsor counts.
- **D6 — file layout.**  New own file `GQ2/AffineTLift.lean`, `namespace GQ2 /
  namespace SectionEight`, imports `GQ2.FrameEnrichment`, `GQ2.CentralObstruction`,
  `GQ2.SectionSix` (cycle-safe: SectionSix imports nothing ≥ §8; it is sorried/allowlisted
  but the consumed `lemma_6_21`/`lemma_6_22` are proved std-3).  Small derived-lemma
  exports go into `SectionEight.lean`'s `RecursionFrame` namespace (see §2.0).
  `SectionEight.lean` then imports `GQ2.AffineTLift`?  **No** — keep the import direction
  `AffineTLift → (FrameEnrichment, CentralObstruction, SectionSix)` and let **d6** add
  `import GQ2.AffineTLift` to SectionEight when splicing `phase140`; d4 itself only edits
  SectionEight for §2.0 (avoids rebuilding SectionEight's slow proofs during d4
  iteration).  Exception: if a §2.0 lemma is needed inside AffineTLift, prove it there
  against the frame fields instead (the `RecursionFrame` context is available via
  `import GQ2.FrameEnrichment`?  **No** — `RecursionFrame` lives in SectionEight.lean.
  See §2.0 note: the two 8.7-engine files must NOT reference `RecursionFrame`; they work
  over the **`RadicalCoverData` + quotient-stage vocabulary**, exactly like P-16a/P-16b.
  d6 instantiates at `E.radData l h`.)

**Consequence of D6 (read twice):** every AffineTLift statement is phrased over
`(D : RadicalCoverData Bg)` (+ a descent datum `N`, + the κ⁰-side data as explicit
hypotheses matching `Enrichment`'s fields), NOT over `RF`/`En`.  d1's
`Enrichment.radData` + `radData_noDescent_iff` + `ker_piBC`/`piBC_surj` make the d6
instantiation mechanical.  This is the same lower-file discipline that made P-16a/b
spliceable (`docs/p16-ticket-split.md`, "circular-import trap").

## 2. Deliverables

### 2.0 SectionEight.lean, `RecursionFrame` namespace (small, low-conflict)

```lean
theorem headBC : RF.TC.piY.comp RF.piBC = RF.TB.piY            -- export of hheadBC
theorem thetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY     -- same cancel_right proof
theorem isBoundaryLift_of_over (f : ContinuousMonoidHom Γ RF.YB)
    (ρ : BoundaryLifts b F RF.TC) (hover : ∀ γ, RF.piBC (f γ) = ρ.1.1 γ) :
    IsBoundaryLift b F RF.TB f                                  -- D5, two lines from the above
```
(Also dedupe: rewrite `partition137_of`'s inline `hheadBC` to use the export.)

### 2.1 The descended cover  (AffineTLift.lean)

Context: `(D : RadicalCoverData Bg)` and a **descent datum**
`(N : Subgroup D.C.cover) (hN : N.Normal) (hNT : N.map D.C.p = D.T) (hNz : D.C.z ∉ N)`.
Let `Q := Bg ⧸ D.T` (needs `D.hT` as a `letI`-instance; the T-projection `piT :=
QuotientGroup.mk' D.T`).

* `sectN : ↥D.T → ↥N` — the inverse of the bijection `p|_N : N ≅ T`
  (injective: `N ⊓ ⟨z⟩ = ⊥` from `hNz` + `eq_one_or_z_of_mem_ker`; surjective: `hNT`).
* `descCover : CentralCover Q` — carrier `D.C.cover ⧸ N`, map = lift of `piT ∘ D.C.p`
  (kills `N` by `hNT`), `z' := mk z`.  `ker = zpowers z'`: `x̄ ∈ ker ⟺ p x ∈ T ⟺
  x ∈ N·⟨z⟩` (cardinality: `|p⁻¹T| = 2|T| = |N⟨z⟩|`, or elementwise via `sectN`);
  `z' ≠ 1` from `hNz`; centrality descends along `mk`-surjectivity.

### 2.2 `descended_splitting`  (the 6.21-application; the "κ⁰_q datum" consumer)

Extra data (the `Enrichment`-shaped hypotheses; d6 feeds `E.…` in):
`(Vmod) [AddCommGroup Vmod] [Finite Vmod]`, a group `C0` with `[Group C0] [Finite C0]`
`[DistribMulAction C0 Vmod]`, `(piC0 : Bg →* C0)` with `ker piC0 = D.M`
(+ surjectivity), `descend : ↥D.M →* Multiplicative Vmod` with `descend_surj`,
`descend_ker` (kernel = T), `descend_conj`, form data `(qbar, hquad, hns)` with
`hqbar : ∀ m hm, D.q ⟨m, hm⟩ = qbar (descend ⟨m, hm⟩).toAdd`, and `(dat, hdat)`.

Steps:
1. `piQbar : Q →* C0` := `QuotientGroup.lift` of `piC0` (kills `T ≤ M`); surjective.
2. `iV : Multiplicative Vmod →* Q` := `piT ∘ (section of descend)` made a hom via
   `QuotientGroup.lift` on `↥D.M ⧸ ker descend`-mechanics, or directly: the composite
   `Multiplicative Vmod ≃* ↥D.M ⧸ (T-in-M) →* Q` (use `descend_surj`/`descend_ker` to
   build the `MulEquiv` via `QuotientGroup.quotientKerEquivOfSurjective`-style; then
   `range iV = ker piQbar` from `ker piC0 = D.M`).
3. `iV_conj : ∀ (x : Q) (v : Vmod), x * iV (.ofAdd v) * x⁻¹ = iV (.ofAdd (piQbar x • v))`
   — lift `x` to `Bg` (`piT` surjective), apply `descend_conj`, push down.
4. The cover 2-cocycle: choose a normalized set-section `s₀ : Q → descCover.cover`
   (`s₀ 1 = 1`; `Function.surjInv` + patch at 1) and set
   `ξ (a, b) := zsign-exponent of s₀ a * s₀ b * (s₀ (a*b))⁻¹ ∈ ⟨z'⟩` (the `zsign`
   calculus of `CentralObstruction` is the template; the element lies in `ker`, and
   `eq_one_or_z_of_mem_ker` gives the `𝔽₂`-value).  Cocycle identity: standard central-
   extension computation (`z'` central; four-term rearrangement — `group` after
   `hp4`-style power expansions is NOT needed here, everything is degree ≤ 2).
5. `hξq : ξ (iV (.ofAdd v), iV (.ofAdd v)) = qbar v`: `s₀ (iV …)` is SOME cover-lift `x`
   of a `piT`-preimage `m ∈ D.M` of `iV …`; `x * x = z^{(D.q ⟨p x, _⟩).val}` by `D.hq`,
   which descends to `(s₀ …)² = z'^{qbar v}` by `hqbar` (any lift squares the same:
   `(z'^k · w)² = w²` since `z'` is central of order 2); with `s₀ 1 = 1` the
   `ξ`-diagonal is exactly that exponent.
6. Apply `SectionSix.lemma_6_21` with `B := Q, p := piQbar, i := iV, q := qbar` and the
   datum `(dat, hdat)`:  **conclusion** `∃ σ : C0 →* Q, ∀ cc, piQbar (σ cc) = cc`.

```lean
theorem descended_splitting … : ∃ σ : C0 →* Q, ∀ cc, piQbar … (σ cc) = cc
```
(No topology: 6.21 is finite-group; continuity of `σ`-composites is free downstream since
everything is finite discrete.)

### 2.3 V-coordinates  (the (131)-vocabulary)

With `σ`-data `(σ, hσ)` and a continuous `ρ : Γ → C0` (Γ topological group):

* `VCoc ρ := {c : Γ → Vmod // Continuous c ∧ ∀ γ δ, c (γ*δ) = c γ + ρ γ • c δ}`
  (`letI : TopologicalSpace Vmod := ⊥` + `DiscreteTopology` — the P-16b `Additive`
  lesson: provide the instances explicitly, do not hope for synthesis).
* `graphEquiv : {h : ContinuousMonoidHom Γ Q // ∀ γ, piQbar (h γ) = ρ γ} ≃ VCoc ρ` —
  forward `c γ := (the Vmod-value with iV (.ofAdd (c γ)) = h γ * (σ (ρ γ))⁻¹)`
  (the difference lies in `ker piQbar = range iV`; extract via the `MulEquiv` from 2.2.2);
  backward `h_c γ := iV (.ofAdd (c γ)) * σ (ρ γ)` — hom-check is exactly the crossed
  condition via `iV_conj` + `hσ`; continuity free (finite discrete targets).
  Round-trips: `Subtype.ext` + `funext` + `iV`-injectivity.

### 2.4 Lemma 8.7, count form  (torsor + invariance + fibration)

All over `(D, N-datum, σ-data, ρ)` with `MOver ρ := {f : ContinuousMonoidHom Γ Bg //
∀ γ, piC0 (f γ) = ρ γ}` and `Central f := ∃ g : ContinuousMonoidHom Γ D.C.cover,
∀ γ, D.C.p (g γ) = f γ` (the `MLifts.Central` shape).

**Reuse note:** `MOver ρ ≃ MLifts D ρ'` where `ρ' := (the `Bg ⧸ D.M ≃* C0`
iso).symm-composite` (iso from `ker piC0 = D.M` + surjectivity).  If the P-16a
`TCocycle`/`twist` layer plugs in cleanly through this bridge, USE it (define
`TCoc := TCocycle D ρ'`); if the `Quotient.out`-based crossed condition fights the
transport, define the crossed `T`-cocycles freshly over `ρ` (conjugation through `σ`:
`u (γδ) = u γ * ⟨σ(ρ γ)-conj of u δ⟩` — well-defined because `M` is abelian, so
`T`-conjugation factors through `Bg/M`).  Either way the counting API is:

* **(a) torsor** `tFibre_equiv` : for `f₀ ∈ MOver ρ`, the `piT`-fibre
  `{f : MOver ρ // ∀ γ, piT (f γ) = piT (f₀ γ)} ≃ TCoc` — freeness: pointwise
  cancellation; transitivity: `u γ := f γ * (f₀ γ)⁻¹ ∈ T` (values in `T` since the
  `piT`-reductions agree), crossed condition from hom-ness (the `lemma_8_3
  liftChar`/`liftDiff` pattern one level up).
* **(b) zero-edge Central-invariance** `central_twist_iff` : for the `T`-twist
  `u·f`, `Central (u·f) ↔ Central f`.  **Direct route (preferred, no ob-calculus):**
  given a cover-lift `g` of `f`, set `g' γ := (sectN (u γ) : D.C.cover) * g γ`.
  Hom-check: `sectN`-uniqueness in `N` over `T` + `N` normal (`hN`) — the conjugate
  `(g γ)·(sectN (u δ))·(g γ)⁻¹` lies in `N` and projects to `(f γ)(u δ)(f γ)⁻¹`, hence
  EQUALS `sectN` of that conjugate; the crossed identity for `u` then gives
  multiplicativity of `g'`.  Continuity: finite discrete.  Symmetry: apply to `u⁻¹`
  (`TCoc` inverses / `twist` involution).  Fallback route: P-16a `ob_twist` + the
  `N`-complement (`sectN` linearizes: `TComplement` with `edge ≡ 0` — `edge_spec` with
  this complement makes `varCoc u` exact) + `central_iff_ob_eq_zero`; only if the direct
  route stalls.
* **(c) fibration corollary** `lemma_8_7_count` :
  ```lean
  Nat.card {f : MOver ρ // Central f}
    = Nat.card TCoc * Nat.card {c : VCoc ρ // ∃ f : MOver ρ,
        (∀ γ, piT (f γ) = h_c c γ) ∧ Central f}
  ```
  via `Equiv.sigmaFiberEquiv` over the map `f ↦ graphEquiv ⟨piT∘f, …⟩`, per-fibre (a)
  + all-or-nothing (b) (`Nat.card_sigma`, then `Finset.sum_ite`-style split — the
  `stageR136_of` h1-pattern verbatim).  Finiteness side conditions: thread
  `[CompactSpace Γ] [TotallyDisconnectedSpace Γ]` + `hfg` and use
  `finite_continuousMonoidHom`/`Subtype.finite` (the `lemma_8_3`/P-16b pattern).
  The multiplicity `μ` of (132) is `Nat.card TCoc` here (D1); its numeric value
  (`|Z¹(T)|`, 5.15/5.16) is d5/d6 material — do NOT compute it.

### 2.5 `exists_polar_inverse`  (the `a_{χ,κ}` supplier, (133)-prep)

Finite linear algebra, no paper subtlety: for `q̄` with `hquad` + `hns` on finite `Vmod`,
the polar map `B♭ : Vmod →ₗ (Vmod →ₗ 𝔽₂)` is bijective (injective by `hns` +
`polar_self`-alternation; bijective by `Nat.card` — `Module.Finite` dual counting; if the
dual-card lemma fights, state surjectivity onto the finitely-many functionals directly).
Deliverable: `∀ φ : Vmod →ₗ[ZMod 2] ZMod 2, ∃! a, ∀ v, polar q̄ a v = φ v` — this is what
d5 uses to define `a_{χ,κ}` from `γ_χ + γ_κ`.  (Cf. `lemma_8_5`'s `a`-data-with-spec: d4
produces the data, 8.5 consumes the spec.)

### 2.6 Prop 8.8, target side  (the edge-killing shear; (133)/(134)-Lean)

An **instantiation lemma** of the proved `lemma_6_22` at `(qbar, dat)`: given a crossed
`γtot`-edge family (`γ : C0 → Vmod →+ ZMod 2`), scalar `δ : C0 × C0 → ZMod 2`, and an
edge-killing shear `a : C0 → Vmod` (crossed 1-cocycle, `ha`) with
`hkill : ∀ c v, polar qbar (a c) v + γ c v = 0`   (from 2.5 applied per `c`; mind
𝔽₂-signs), conclude — directly from `lemma_6_22` + `hkill` — the sheared class is
`κ⁰ + inf (DeltaScalar)` up to the explicit coboundary `w`:

```lean
noncomputable def DeltaScalar (dat …) (γ …) (δ …) (a …) : C0 × C0 → ZMod 2 :=
  fun cd => δ cd + thetaPhase dat a cd + gammaCupA γ a cd

theorem prop_8_8_target … :
    ∃ w : Vmod × C0 → ZMod 2, ∀ p q',
      (kappa0 dat (shear a p) (shear a q') + gammaEdge γ (shear a p) (shear a q')
          + inflScalar δ (shear a p) (shear a q'))
        = (kappa0 dat p q' + inflScalar (DeltaScalar dat γ δ a) p q')
          + (w (p.1 + p.2 • q'.1, p.2 * q'.2) + w p + w q')
```
Proof: `lemma_6_22` gives the identity with edge `γ + B♭a`; `hkill` makes that family
the zero `AddMonoidHom` (careful: `AddMonoidHom.ext` + `𝔽₂` `a + a = 0` to turn
`γ c + polar-hom = 0-hom`), and `gammaEdge 0 = 0` collapses the edge term.  Notes:
`gammaEdge`'s zero needs `map_zero`-of-the-zero-hom, pointwise.  The χ-side (`χ_* e`
term of (134)) does NOT appear here — at the count level `χ_* e` enters through d5's
cover construction, not through this cochain identity; record this routing in the
docstring.

### 2.7 (Optional, d5-prep — do only if time permits)

`centralCoverOfCocycle : (δ : C0 × C0 → ZMod 2) → (normalized 2-cocycle hyps) →
CentralCover C0` — the twisted product `𝔽₂ ×_δ C0` (multiplication
`(s,c)(t,d) := (s + t + δ(c,d), cd)`); the P-15i `Transgression.Twisted` construction is
the template (private instances Zero/Add/…, letI-assembled `Group`).  d5 needs it for
`phase ζ := centralCoverOfCocycle (DeltaScalar …)`.  If skipped, note it on d5's row.

## 3. What d6 will do with these (context, not scope)

Per `ρ`: `zBC`-fibre ≃ `{f : MOver ρ // Central f}` (D5 kills the boundary clause) →
2.4(c) → `lemma_8_5` on `W := VCoc ρ` with the liftability constraint packaged as an
obstruction-module datum (the `stageR136_of` pattern at the `T`-stage) → 2.6 + 5.17
(P-13f) converts the χ-sums to `DeltaScalar`-cover liftability → `nPhase`.  If 2.4(c)'s
statement shape makes any of this awkward, adjust 2.4(c) — it is the API boundary, the
rest is fixed.

## 4. Suggested order & effort

2.0 (½h) → 2.1 (1–2h) → 2.5 (1h, independent — good warm-up) → 2.2 (2–3h, the 6.21 splice
is the heart) → 2.3 (1–2h) → 2.4 (3–4h, the torsor is P-16a-patterned) → 2.6 (1–2h,
mostly plumbing `lemma_6_22`) → 2.7 (optional).  2.5/2.6 are independent of 2.1–2.4 —
reorder freely if blocked.

## 5. Lean gotchas (banked from P-16a/b/d, directly relevant)

- `Quotient`/quotient-group: `Quotient.out (c⁻¹ : Bg ⧸ D.M)`-style ascriptions; prefer
  `QuotientGroup.mk'`/`lift` over raw `Quotient` API; `QuotientGroup.eq`,
  `eq_one_iff`, `mk_one` are the workhorses.
- Instances: `letI : TopologicalSpace Vmod := ⊥` + `letI : DiscreteTopology Vmod` before
  any `Continuous c`-talk (P-16b `Additive` lesson); keep the minimal-context-helper
  discipline — do NOT put `[CompactSpace Γ]` on statements that don't count anything.
- Continuity of maps out of discrete groups: pin the outer function —
  `(continuous_of_discreteTopology (f := fun … => …)).comp h`.
- Data through `set`, not `have` (opacity kills `rfl`-defeqs — the 8.2-local lesson);
  `Equiv` fields as named private lemmas (abstraction timeouts — the P-05/8.2 lesson).
- Never `rw` a `range = J`-type equation inside hypotheses mentioning dependent types
  (motive failure — the 8.3 lesson); rewrite fresh goal-memberships instead.
- `MonoidHom.mem_ker` is an iff with no `_`; `Subgroup.mem_map_of_mem piB hk`;
  `sup_eq_left.mpr`; `Multiplicative.ofAdd/.toAdd` dot-notation works.
- 𝔽₂: `CharTwo.add_self_eq_zero`, `sign`-calculus in SectionEight, `by decide` for
  `(1 : ZMod 2).val = 1`-style facts; `linear_combination (norm := (ring_nf;
  simp [CharTwo.two_eq_zero]))` closed 6.22 — same endgame likely works in 2.6.
- Lines ≤ 100 chars; `fun x ↦ …` in new mathlib-style code is fine but the §8 files use
  `fun x => …` — match the file.

## 6. Acceptance criteria

1. `lake build` green; `bash scripts/check_axioms.sh` green (census 13, allowlist
   UNCHANGED — `AffineTLift.lean` must be sorry-free at close; stage WIP sorries only
   locally, never commit-ready with them).
2. `#print axioms` (lean_verify) = std-3 for EVERY new theorem (`descended_splitting`,
   `graphEquiv`-lemmas, `tFibre_equiv`, `central_twist_iff`, `lemma_8_7_count`,
   `exists_polar_inverse`, `prop_8_8_target`).  Ax column stays ∅.
3. Ledger entries in `docs/section8-extraction.md` (P-16d corrections list): D1
   (cocycle-level 8.7) and D3 (6.22-normalized Δ vs display (134)).
4. Board: P-16d4 row → ☑ with summary; note on P-16d5's row what 2.7 delivered or
   deferred; note on P-16d6's row if 2.4(c)'s API shape changed from this plan.
5. No edits to: `RecursionInputs`, `ClosedRecursion`, `prop_8_9`, `lemma_8_6_*`,
   anything in `GQ2/CentralObstruction.lean`/`GQ2/RadicalEdgeData.lean` (P-16a frozen
   layer) beyond consuming them.  §2.0's SectionEight additions + the `hheadBC` dedupe
   are the only SectionEight edits.

## 7. Firewalls

- **P-13f firewall:** do not use `prop_5_15`, `prop_5_16*`, `corollary 5.17`-material,
  `prop_5_10`, or anything from `GQ2/LocalLiftingDuality.lean` beyond what P-16a/b
  already consume.  If a step seems to need them, the d4/d6 cut is being crossed — stop
  and re-scope (that step belongs to d6).
- **Axiom firewall:** no B6/B7 (no `tateDuality`, no `absGalQ2_localEulerCharacteristic`).
  d4 is a finite-group + generic-Γ ticket.
- **Parallel agents:** P-13f, P-15f, P-25(+) may be active; root-build reds in files you
  don't own are not your concern; your targets must build 0-error standalone
  (`lake build GQ2.AffineTLift` + `lake build GQ2.SectionEight`).  Do not commit.
