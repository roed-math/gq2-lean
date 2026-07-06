# P-16d6c handoff — the (140) Prop-8.8 core

*Self-contained scoping/handoff (Opus, 2026-07-06).  P-16d6c is decomposed into **c1/c2/c3**; this
doc pins each sub-ticket's exact interface obligation against the already-proved engine
`phase140_of_nonsingular`.  Companion files: `GQ2/PhaseLIndep.lean` (c3-μ, DONE).*

## 0. The deliverable and what is already done

`phase140_of_nonsingular` (`GQ2/RecursionSplice.lean:418`, std-3, **proved**) is the (140) engine.
It reduces `RecursionInputs.phase140` to a fixed list of concrete inputs; the abstract layer, the
Gauss-correspondence, and `polarInverseL`/`enrichment_card_Vmod` are all done
(`docs/p16d6-concrete-spec.md` §2).  **P-16d6c must supply the residual concrete inputs**, all with
`W := En.Vmod`, `Q := En.qbar l h`, `D := En.radData l h` (`hD := rfl`):

| input | shape | sub-ticket | status |
|---|---|---|---|
| `Lin : En.Vmod →ₗ[ZMod 2] Efp`, `hLin` (surj), `κ : BoundaryLifts → Efp`, `ε : BoundaryLifts → ZMod 2` | C-descent data | **c1** | open |
| `hM` — the (135)/Prop 8.8 count | `∀ ρ, #{central-liftable T-reductions} = #{x : V // Lin x = κ ρ ∧ Q x = ε ρ}` | **c1** | open |
| `hphase` — character↔phase reindex | `Σ_χ Σ_ρ sign(χ(κ ρ)+ε ρ+Q(polarInverseL … χ)) = Σ_ζ (2·nPhase(phase ζ) − e_Γ(C))` | **c2** | open |
| `phase : DT → CentralCover RF.YC` witness | `phaseFamily (DeltaScalar (En.dat l h) γ_ζ δ_ζ a_ζ) …` | **c2** | open |
| `μ` `l`-independence | `#TCocycle(radData l h)` constant in `l` | **c3** | ✅ DONE |
| `G0` `l`-independence | `gaussSum(qbar l h)` constant in `l` | **c3** | route decided: §6.2 pinning (§c3) |
| `hμ` (ρ-independence, per `l`) | `∀ ρ, #TCocycle(radData l h)(…) = μ` | P-16d6b | ✅ DONE (torsor reduction) |

`DT := Module.Dual (ZMod 2) En.Vmod` (`= V^∨`), so `hDT`/`hG0` are `rfl`, `0 < #DT` is free.

---

## ⚠ VERIFICATION PASS (Fable, 2026-07-06): two engine-spec bugs — read before starting c1

The Opus plan below is architecturally confirmed (the c1a/c1b/c1c layering and the paper mapping
are right), but checking the **satisfiability** of the engine spec it targets found two bugs.

### Bug 1 — `hM`/`μ` are miscalibrated by `|B¹_{Γ,ρ}(V)| = #V` (blocker for c1c)

For `b̄ ∈ V`, conjugating a central `M`-lift `f` of `ρ'` by any `m ∈ M_B` lifting `b̄` gives
another central `M`-lift of `ρ'` (mod-`M` unchanged since `m ∈ M_B`; centrality survives by
conjugating the cover lift), and `redT (m f m⁻¹) = (δb̄) · redT f` — the crossed-coboundary
translate.  So `Set.range (redT on central lifts)` is stable under the **free** translation action
of `B¹_{Γ,ρ}(V)` (free because `δb̄ = 0 ⟹ b̄ ∈ V^C = 0`: `V` is the nontrivial simple head and
boundary lifts are surjective).  Hence **`hM`'s LHS is a positive multiple of `#B¹ = #V` whenever
nonzero** (`#B¹ = #V/#H⁰ = #V`).  But `hM`'s RHS is `≤ #W = #V` (`hWV`), with equality impossible
(`hLin` surjective + `q̄` nonsingular ⟹ proper constraint set).  So `hM` as stated forces
LHS `= 0` for **every** `ρ`, i.e. `phase140_of_gaussCorrespondence`/`_of_nonsingular` are usable
only when `zBC = 0` — vacuous in the intended regime.

Magnitude cross-check: paper (132) has multiplicity `μ = |B¹(V)|·|Z¹(T)|`; the engine's `μ` is
pinned by `hμ` to `#Z¹(T)` alone (`central_card_eq_reductions_mul_tcocycle` extracts only the
`T`-torsor).  The missing `|B¹(V)| = #V` is exactly the discrepancy.  Independent check via the
P-16d6b all-lifts torsor + 5.16 numerics: `#(redT image over ALL lifts) = #Z¹(Γ,M_B)/#Z¹(T)
= 2^{2m}/2^{2t+r} = 2^{2d−r}` — the central sub-count is `~2^{2d−r−1}`, vs RHS `~2^{d−r−1}`:
off by `2^d`.

**The repair (c1s — small, shape-preserving, co-owned `RecursionSplice.lean`) — ✅ LANDED
(Fable, 2026-07-07): both `phase140_of_*` repaired, std-3, build green, algebra re-verified in
situ (`phase140_ofPhaseData` untouched — μ-generic, applied at `#W·μ`):**
* `hM` becomes `… = Nat.card W * Nat.card {x : W // Lin x = κ ρ ∧ Q x = ε ρ}`;
* the conclusions of `phase140_of_gaussCorrespondence` and `phase140_of_nonsingular` change their
  `μ`-slot to `(Nat.card W * μ)` — algebra check: `zBC = μ·Σ LHS = μ·#W·Σ N_V` and
  `2#DT·Σ N_V = #W·e + G0·Σ_ζ` compose to
  `2·#DT·zBC = (#W·μ)·((#M_B/#T_B)·e + G0·Σ_ζ …)` — same shape, `μ ↦ #W·μ`;
* `ClosedRecursion.eq140` / `prop_8_9` need **no change** (`μ` is existential); the final witness
  becomes `μ := #V · #Z¹(T_B)` — the paper's (132) value.
* `zBC_eq_mu_mul_reductionCount` and `hμ` (P-16d6b) are **correct as stated** — do not touch.

The mathematically true per-`ρ` statement c1c will prove:
`#(redT image over central lifts of ρ') = #B¹_{Γ,ρ}(V) · N(κρ, ερ)` with `#B¹ = #V = #W`.

### Bug 2 — spec §1's `DT := (En.Vmod)^∨` is the wrong index (doc-level)

The paper's phase index is `D = (T^∨)^C` (dim `r`) — (140)'s prefactor is `2^{r+1} = 2·#D` — and
`Δ_{χ,κ}` is indexed by `χ ∈ D`.  So the instantiation must take
`DT := fixedPts C (ElemDual T_B-model)` (the same object as P-16d6b's `μ`-value and 5.16 clause 1:
`#H²_{Γ,ρ}(T) = #(T^∨)^C = 2^r`) and `Efp ≅ D^∨` (dim `r`), NOT `V^∨` (dim `d`).  The engine is
agnostic (`DT` a parameter); only `docs/p16d6-concrete-spec.md` §1 is wrong.  `hDT` stays
rfl-adjacent through finite double-duality.

### Hidden obligations surfaced by the paper check

1. **cor 5.17's adjoint identity** `⟨∂b, χ⟩_Γ = ⟨b, ρ*γ_χ⟩_Γ` — the first line of the paper's
   (135) proof — was **explicitly deferred by P-13g** ("needs connecting-map infrastructure in both
   theories").  It is part of c1b's deliverable (or c1c must route around it cocycle-level).
2. **`∂`-surjectivity** onto the `H²(T)`-model (dim `r`) — needed for the source-side (126)
   application (`L` surjective kills nontrivial characters); comes from an LES fragment of
   `0→T→M→V→0` + 5.16 numerics (c1b).
3. **Source-Gauss = target-Gauss**: `G(Q⁰_{Γ,ρ}) = gaussSum q̄`, `ρ`-free — the paper writes
   `G(Q⁰)` once, silently.  **Γ-side content**: `Q⁰_{Γ,ρ}` lives on `H¹_{Γ,ρ}(V)`, so no
   frame-level `En` field can carry it (an earlier "fold into one `En` amendment" idea here was
   wrong on that count).  Routes: pin both sides to the same structural constant (target via the
   §6.2 pinning as in c3; source via a `prop_6_9`-style dual pinch on `(H¹, Q⁰_{Γ,ρ})` — polar
   nonsingularity is 5.16 cl.-4 cup-perfectness ✓, the tame/free structure on `H¹` is the open
   design item), or a direct source↔target Arf transport (cor-5.17 parity).  (c1c, F-design)
4. **The per-`(χ,ρ)` exponent identity** `ι_Γ(ρ*Δ_{χ,κ}) = χ(κρ) + ερ + q̄(a_χ)` — the Γ-level
   (135) in count-ready form.  This is the **shared keystone of c1c and c2**: c1c consumes it for
   `hM` (via (126) on both sides), c2 for `hphase` (then (141)/(142) are counting).
   `κρ ∈ E = D^∨` is canonical: `κρ(χ) := ι_Γ(ρ*(χ_* e))` (linear in `χ` since pushforward along
   characters is additive); `ερ := ι_Γ(ρ*δ_κ)`; `Lin` is pinned by matching the `q̄(a_χ)` term.

## c1 — C-descent data `Lin`/`κ`/`ε` + the Prop 8.8 count `hM`  ⭐⭐⭐ (the largest piece)

**The deep group-theory↔quadratic bridge** — paper Lemma 8.7 + Prop 8.8, pulled onto `V` directly.
Own file (e.g. `GQ2/Prop88Count.lean`).  *This section is paper-grounded (Opus 2026-07-06, read
of paper pp. 38–43: Lemmas 8.4/8.5/8.7, Prop 8.8, displays (125)–(135)); count shapes corrected by
the Fable verification pass above (2026-07-06) — where the two conflict, the verification pass
wins.*

### Where `hM` sits in the engine

The (140) engine already reduces to `hM` cleanly:
`zBC_eq_mu_mul_reductionCount` gives `zBC = μ · Σ_ρ #(red_T image over central lifts of ρ')`;
`lemma_8_5_aggregated` (✓, `RecursionSplice.lean:280`) evaluates `Σ_ρ #{x∈W : Lx=κρ, Qx=ερ}` via
the Gauss sum (paper Lemma 8.5 / display (126)); `hphase` (c2) matches the character sum.  **`hM` is
the one bridge between them:**
`#(red_T image over {central M-lifts of ρ'}) = #{x : V // Lin x = κ ρ ∧ q̄(x) = ε ρ}` — i.e. the
group-theoretic count of achievable central `T`-reductions equals the constrained-quadratic count
`N(κρ, ερ)` of Lemma 8.5.  Note `W := En.Vmod = V` (so `|W| = |V|` via `enrichment_card_Vmod`),
`Q := En.qbar l h = q̄_λ`.

### What `Efp`/`Lin`/`κ`/`ε` are (paper (130), (133)–(135))

* `Efp = E`, the finite `𝔽₂`-obstruction space with `Lin = L : V ↠ E` the **surjective linear part**
  of Lemma 8.5's constraint; `a_χ = polarInverseL` (already wired) is its `B_q̄(a_χ, ·) = χ(L·)`
  supplier.  Concretely `E`/`L` come from the **descended central class** `κ = κ⁰ + Γ_{γκ} + inf δ_κ`
  (130): `κ⁰` = the fixed base determinant class on `V` (`En.dat`), `Γ_{γκ}` (with `γ_κ ∈ Z¹(C,V^∨)`)
  is the linear part → `L`, and `δ_κ ∈ Z²(C,𝔽₂)` the scalar part → `ε`.
* `κ ρ ∈ E`, `ε ρ ∈ 𝔽₂` are the per-`ρ` residues of that class pulled back along `ρ : Γ ↠ C`
  (`ρ*`), read through the completed square (135):
  `Q_{κ,Γ,ρ}(b) + ⟨∂b + ρ*e, χ⟩ = Q⁰(b + ρ*a_{χ,κ}) + ι(ρ*Δ_{χ,κ})`.

### The proof chain (Lemma 8.7 + Prop 8.8)

1. **V-coordinate ↔ `red_T` (Lemma 8.7 setup).**  `descended_splitting` (✓,
   `AffineTLift.lean:503`) gives `σ : C ↪ B/T` with `B/T ≅ V ⋊ C`.  A `red_T`-value of an `M`-lift
   over `ρ'` decomposes through `σ` into (its `V`-part = a **crossed 1-cochain** `Γ → V`, its
   `C`-part = `ρ`).  So `red_T`-image over lifts of `ρ'` ≅ the crossed `V`-cochains that are cocycles.
2. **Actual-lift ⟺ `∂c = ρ*e` (Lemma 8.7 (131)).**  The `V`-coordinate `c ∈ H¹_{Γ,ρ}(V)` comes from
   a genuine `M`-lift iff `∂_{Γ,ρ}(c) = ρ*e` in `H²_{Γ,ρ}(T)`, where `e ∈ H²(C,T)` is the extension
   class of `B → V⋊C` pulled back along the zero section.
3. **Central ⟺ scalar condition; completed square (Prop 8.8 (135)).**  In the edge-zero regime,
   `central` (scalar pushout vanishes) is the quadratic condition on the `V`-coordinate; the
   completed-square identity (135) — Γ-level, pulled back from `prop_8_8_target` (✓) along cor. 5.17
   — collapses the count of central-liftable `V`-classes to `N(κρ,ερ) = #{x∈V : Lx=κρ, q̄x=ερ}`, the
   `|B¹(V)|` cocycle-spread being absorbed into the direct-`V` parameterization.

### ⚠ The real work: a crossed-cohomology `V`/`T` layer (new machinery)

Steps 1–2 need objects the repo has **deliberately not built** (`section8-extraction.md` dev. #4:
"no quotient-set / class objects introduced"): `H¹_{Γ,ρ}(V)`, `H²_{Γ,ρ}(T)`, the connecting map
`∂_{Γ,ρ} : H¹(V) → H²(T)` of the module extension `0→T→M→V→0`, the class `e`, and `ρ*`.  This is a
**multi-session architectural build** — the honest bulk of c1.  Sub-decomposition:

* **c1s** [**F**, ⭐, gate for c1c only] — **✅ DONE (Fable, 2026-07-07; board row P-16d6c1s)** —
  the Bug-1 spec repair in co-owned `RecursionSplice.lean`
  (`hM` `#W`-factor + `μ ↦ #W·μ` in the two `phase140_of_*` conclusions) and the Bug-2 doc fix.
  Small, but it changes the reducer contract d6e consumes — re-verify the algebra in situ.
  Coordinate: nobody else touches those two theorems (d6a = stageR136, d6d = half139), but it IS a
  co-owned file — flag on the board before/at commit.
* **c1a** [**O**, ⭐⭐] — the crossed `V`-cochain layer over `ρ` (a `VCocycle` mirroring `TCocycle`)
  + the bijection {continuous homs `Γ → B/T` over `ρ'`} ≅ `Z¹_{Γ,ρ}(V)` via `descended_splitting`'s
  `σ`, + the **`B¹`-translation facts** (conjugation by `m ∈ M_B` acts on `red_T` values by
  crossed coboundaries, freely when `V^C = 0` — the mathematical core of Bug 1, so landing it
  validates the repair).  Well-specified: mirror the `TCocycle` API; `V⋊C` structure from `σ`.
* **c1b** [**F**, ⭐⭐⭐] — the connecting `∂_{Γ,ρ}` for `0→T→M→V→0` **at cocycle level**, the class
  `e` (extension class of `B → V⋊C` along the zero section), Lemma 8.7 (131)
  `actual-lift ⟺ ∂c = ρ*e`, **the P-13g-deferred cor-5.17 adjoint** `⟨∂b,χ⟩ = ⟨b,ρ*γ_χ⟩`, and
  `∂`-surjectivity (LES fragment + 5.16 numerics).  New subsystem; statement-design-sensitive
  (crossed `H²(T)`-encodings, cocycle-vs-class choices).
* **c1c** [**F**-design → **O**-close, ⭐⭐⭐] — the `central` ⟺ scalar-quadratic characterization,
  the Γ-level (135) keystone (obligation 4 above), the Gauss transport (obligation 3), and the
  **repaired** `hM` close: `LHS(ρ) = #B¹ · N(κρ, ερ)`.  Pins `Efp = D^∨`, `Lin`,
  `κρ(χ) = ι_Γ(ρ*(χ_*e))`, `ερ = ι_Γ(ρ*δ_κ)` concretely.  Couples to c2 through the keystone.

Tools ready: `lemma_8_5_aggregated` ✓, `descended_splitting` ✓, `lemma_8_7_count` /
`central_card_eq_reductions_mul_tcocycle` ✓, `central_twist_iff` ✓, `prop_8_8_target` ✓,
`exists_polar_inverse`/`polarInverseL` ✓, `lemma_6_21`/`6_22` ✓.  Missing = the crossed-cohomology
`V`/`T` layer (c1a/c1b) — that is the gate, and it is a real new subsystem, not a splice.

> **Recommendation:** do **not** stub `Lin`/`κ`/`ε` speculatively (they are pinned only by the c1c
> proof).  Order: c1s (unblocks c1c's target statement) and c1a (independent) first — c1a is the
> concrete entry point and is Opus-ready; then c1b (Fable); then c1c.  Each its own leaf.

## c2 — `hphase` + the `phase`/`DeltaScalar` witness  ⭐⭐⭐ (one coupled build)

Own file (e.g. `GQ2/PhaseReindex.lean`).  `hphase` and the witness `phase` are **one build** — the
`Δ = DeltaScalar (En.dat l h) γ_ζ δ_ζ a_ζ` used to define `phase = phaseFamily (Δ …)` must be the
same `Δ` whose signed sum `hphase` evaluates.

* `DeltaScalar`/`phaseFamily`/`centralCoverOfCocycle` interfaces: `GQ2/AffineTLift.lean:528/841/769`.
* `prop_8_8_target` (`:534`, ✓) is the **edge-killing shear**: given `γ`/`δ`/`a` with the kill
  condition `∀ c v, polar q (a c) v + γ c v = 0`, it collapses the determinant class to
  `κ⁰ + inflΔ` up to an explicit coboundary `w`.  The per-character `γ_ζ`/`δ_ζ`/`a_ζ` are that shear
  (with `a_ζ = polarInverseL …` the canonical polar-inverse shift, already wired in the engine).
* The residual work is: (i) the **`DeltaScalar` 2-cocycle normalization** proofs (`hcoc`/`hl`/`hr`)
  that `phaseFamily`/`centralCoverOfCocycle` require; (ii) the **sign-sum ↔ `2·nPhase − e`**
  identity that is `hphase`.
* **Post-verification notes (Fable 2026-07-06):** the index is `ζ ∈ DT = (T^∨)^C` (Bug 2 — NOT
  `V^∨`), so the `Δ`-family is `χ ∈ D`-indexed exactly as in (133)/(134).  The per-`(χ,ρ)` exponent
  identity (obligation 4, the c1c keystone) is what converts `hphase`'s LHS signs into
  `ι_Γ(ρ*Δ_χ)`; after that, (141) `s_Γ(ζ) = 2·n_{Γ,0}(ζ) − e_Γ(C)` is an unobstructed/obstructed
  count split (mechanical, O).  Model: **F**-design for the reindex + witness coupling, **O** for
  the normalization proofs and the (141)-count.  Depends on c1c's keystone — do not start the
  `hphase` half before it; the `hcoc`/`hl`/`hr` normalization half is independent and O-ready.

## c3 — `G0`/`μ` `l`-independence

* **μ: ✅ DONE** — `GQ2/PhaseLIndep.lean`, `tcocycle_card_l_indep` (std-3):
  `#TCocycle(En.radData l h)(rhoPrime … l …)` is independent of `l`, because `radData`'s `M`/`T`
  layers are `RF.MB`/`RF.TBsub` for every `l` and `rhoPrime` factors through `piBCiso` (which sees
  the datum only via the proof-irrelevant `D.M = RF.MB`).  Combine with P-16d6b's ρ-independence to
  pin `μ` at a reference `l₀` and transport to the current `l` for `hμ (l h)`.
* **G0: ✅ ROUTE DECIDED (2026-07-06) — §6.2 pinning via P-15b; NO `En` amendment.**
  `G0 := gaussSum (En.qbar l h)` must be constant in `l`; `Enrichment` carries no cross-`l` field,
  but none is needed: P-15b's Gauss-sign pair pins the Gauss data of **any** nonsingular
  `C`-invariant quadratic form on `V` to a λ-free structural value (analysis credit: parallel-agent
  note on the c3 board row; verified against the signatures by the c-agent).
  - **Unramified**: `prop_6_9_unramified` (`SectionSix.lean:306`) has NO data hypotheses beyond the
    tame structure (`c`/`hc`/`hfaith`/`hsimple`/`hV`/`hunram`) — apply twice (`qbar l h`,
    `qbar l' h'`, both qualify via `En.hquad`/`hns`/`hinv`), equal `zeroCount`s, equal Gauss sums
    via `gaussSum_eq` (`g = 2·zeroCount − #V`, P-15a).
  - **Ramified**: `lemma_6_8` (`SectionSix.lean:240`) — its **first conjunct pins `arf q = s`
    directly** (no detour through `qDouble`) — apply twice + the P-15a `arf`↔`gaussSum` bridges
    (`gaussSum_eq_pow`, `arf_eq_zero_iff_gaussSum_pos`).  Its data hypotheses
    (`s`/`r`/`a`/`hs1`/`Wt`/`e`/`he` + the P-15b-flagged `hVU`/`hrank` gap) are λ-free — they
    thread **hypothesis-side to d6e's residue list** (the c3-μ/d6b/d6a idiom).
  - Deciding arguments (from the board-row analysis, accepted): the §9 recursion needs the Gauss
    **value** anyway (determinism), so §6.2 must be wired regardless — an `En` field would
    duplicate it AND have to be constructed at every stage of P-17i's `blockEnrichment` induction.
  - **Fallback** (only if the hypothesis-threading proves heavier than expected at d6e): the
    amendment `hGaussConst : ∀ l h l' h', gaussSum (qbar l h) = gaussSum (qbar l' h')` (or an
    `arf`-pin), owner sign-off required (`Enrichment` is co-owned `SectionEight.lean`).
  - NB the amendment could never have served c1c's source-side obligation anyway (`Q⁰_{Γ,ρ}` is
    Γ-side, on `H¹` — see obligation 3 above); the earlier "one amendment for both" kinship note
    is superseded.

---

## Recommended order (within P-16d6c)

1. **c3** μ-half ✅ (done).  **c3** G0-half — route decided (§6.2 pinning, no amendment): two
   `prop_6_9_unramified`/`lemma_6_8` applications + the P-15a bridges; O-ready now, structural
   hyps thread to d6e.
2. **c1** (`Lin`/`κ`/`ε` + `hM`) — the largest; unblocks the `hfib` half.
3. **c2** (`hphase` + `phase`/`Δ`) — one coupled build on top of `prop_8_8_target`.
4. Feed all into `RecursionInputs.phase140 := fun l h _hN => phase140_of_nonsingular …`
   (spec §2 has the exact application) — this final wiring is the **P-16d6e** assembly's job.

## Build / gate

* Each sub-ticket = its own leaf off the co-owned `RecursionSplice.lean`/`SectionEight.lean`.
* `GQ2/PhaseLIndep.lean` is sorry-free, std-3 — **not** on the `SORRY_ALLOWLIST`.
* `#print axioms GQ2.SectionEight.tcocycle_card_l_indep` = `{propext, Classical.choice, Quot.sound}`.
