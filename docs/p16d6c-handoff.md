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
| `G0` `l`-independence | `gaussSum(qbar l h)` constant in `l` | **c3** | ⚠ needs amendment (§c3) |
| `hμ` (ρ-independence, per `l`) | `∀ ρ, #TCocycle(radData l h)(…) = μ` | P-16d6b | ✅ DONE (torsor reduction) |

`DT := Module.Dual (ZMod 2) En.Vmod` (`= V^∨`), so `hDT`/`hG0` are `rfl`, `0 < #DT` is free.

---

## c1 — C-descent data `Lin`/`κ`/`ε` + the Prop 8.8 count `hM`  ⭐⭐⭐ (the largest piece)

**The deep group-theory↔quadratic bridge** — paper Lemma 8.7 + Prop 8.8, pulled onto `V` directly.
Own file (e.g. `GQ2/Prop88Count.lean`).  *This section is now paper-grounded (Opus 2026-07-06, read
of paper pp. 38–43: Lemmas 8.4/8.5/8.7, Prop 8.8, displays (125)–(135)).*

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

* **c1a** — the crossed `V`-cochain layer over `ρ` (`Z¹_{Γ,ρ}(V)`, `B¹`, `H¹`) + the `red_T` ≅
  `V`-cocycle bijection via `descended_splitting` (the "thin step" of dev. #4, but it needs the
  `V⋊C` crossed structure spelled out).
* **c1b** — the connecting `∂_{Γ,ρ}` for `0→T→M→V→0` and the class `e`; Lemma 8.7 (131)
  characterization `actual-lift ⟺ ∂c = ρ*e`, and the raw-lift multiplicity (132) `|B¹(V)|·|Z¹(T)|`
  (the latter reconciles with the already-proved `central_card_eq_reductions_mul_tcocycle` /
  `lemma_8_7_count`).
* **c1c** — the `central` ⟺ scalar-quadratic characterization + the Γ-level completed square (135)
  from `prop_8_8_target`, giving `hM = N(κρ,ερ)`.  Defines `Efp`/`Lin`/`κ`/`ε` concretely (they are
  determined by this proof, per (130)).

Tools ready: `lemma_8_5_aggregated` ✓, `descended_splitting` ✓, `lemma_8_7_count` /
`central_card_eq_reductions_mul_tcocycle` ✓, `central_twist_iff` ✓, `prop_8_8_target` ✓,
`exists_polar_inverse`/`polarInverseL` ✓, `lemma_6_21`/`6_22` ✓.  Missing = the crossed-cohomology
`V`/`T` layer (c1a/c1b) — that is the gate, and it is a real new subsystem, not a splice.

> **Recommendation:** do **not** stub `Lin`/`κ`/`ε` speculatively (they are pinned only by the c1c
> proof).  Build c1a → c1b → c1c in order; each is its own leaf.  c1a (the `red_T` ≅ crossed-`V`
> bijection) is the concrete entry point.

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

## c3 — `G0`/`μ` `l`-independence

* **μ: ✅ DONE** — `GQ2/PhaseLIndep.lean`, `tcocycle_card_l_indep` (std-3):
  `#TCocycle(En.radData l h)(rhoPrime … l …)` is independent of `l`, because `radData`'s `M`/`T`
  layers are `RF.MB`/`RF.TBsub` for every `l` and `rhoPrime` factors through `piBCiso` (which sees
  the datum only via the proof-irrelevant `D.M = RF.MB`).  Combine with P-16d6b's ρ-independence to
  pin `μ` at a reference `l₀` and transport to the current `l` for `hμ (l h)`.
* **G0: ⚠ NOT derivable from the current `Enrichment`.**  `G0 := gaussSum (En.qbar l h)` must be
  constant in `l`, but the `qbar l h` are genuinely different forms per `l`, and `Enrichment`
  carries **no field** relating them across `l` (no shared-Arf / shared-gaussSum datum — checked:
  fields are `q`/`hq`/`hrad`/`hTzero`/`Vmod`/`descend*`/`qbar`/`hqbar`/`hquad`/`hns`/`hinv`/`dat`/`hdat`,
  none cross-`l`).  Mathematically the `q̄_λ` are Arf-equivalent (paper §7.4: the same nondegenerate
  deformation form), but that is exactly what `Enrichment` abstracts away.
  **Action (owner sign-off — `Enrichment` is co-owned `SectionEight.lean`):** add a field
  `hGaussConst : ∀ l h l' h', gaussSum (qbar l h) = gaussSum (qbar l' h')` (or the stronger
  `arf (qbar l h) = arf (qbar l' h')`, from which `gaussSum` equality follows via `gaussSum_eq_pow`).
  Then G0 `l`-independence is that field.  Do **not** edit `Enrichment` unilaterally; coordinate at
  the P-16d6e assembly / with the frame owner.

---

## Recommended order (within P-16d6c)

1. **c3-μ** ✅ (done).  **c3-G0** — get the `Enrichment.hGaussConst` amendment approved (quick, but
   gated on owner).
2. **c1** (`Lin`/`κ`/`ε` + `hM`) — the largest; unblocks the `hfib` half.
3. **c2** (`hphase` + `phase`/`Δ`) — one coupled build on top of `prop_8_8_target`.
4. Feed all into `RecursionInputs.phase140 := fun l h _hN => phase140_of_nonsingular …`
   (spec §2 has the exact application) — this final wiring is the **P-16d6e** assembly's job.

## Build / gate

* Each sub-ticket = its own leaf off the co-owned `RecursionSplice.lean`/`SectionEight.lean`.
* `GQ2/PhaseLIndep.lean` is sorry-free, std-3 — **not** on the `SORRY_ALLOWLIST`.
* `#print axioms GQ2.SectionEight.tcocycle_card_l_indep` = `{propext, Classical.choice, Quot.sound}`.
