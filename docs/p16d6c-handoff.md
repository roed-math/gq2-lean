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

**The deep group-theory↔quadratic bridge.**  Own file (e.g. `GQ2/Prop88Count.lean`).

* `Efp`/`Lin`/`κ`/`ε` are **not free** — they are whatever makes `hM` hold, from the concrete
  `scalarCover`/`piBC` C-stage structure.  `Efp` is the C-stage image space (the target of the
  descent-to-`C` obstruction map); `Lin` is that descent map on `V = M_B/T_B`; `κ ρ`/`ε ρ` are the
  per-`ρ` constraints (`κ` = the C-image linear residue, `ε` = the scalar-square residue).
* `hM` says: a central `M`-lift's `T`-reduction is achievable ⟺ its coordinate `x ∈ V` solves
  `Lin x = κ ρ ∧ Q x = ε ρ`.  The `Q x = ε ρ` half is the scalar-cover **square** relation
  (`En.q`/`En.hq`, `hqbar`); the `Lin x = κ ρ` half is the **C-image / boundary** constraint.
* Tools (all ✓): `En.q`/`En.hq`/`En.hqbar` (square form), `lemma_6_21`/`lemma_6_22`
  (`GQ2/SectionSix.lean:964/1011`), `prop_8_8_target` (`GQ2/AffineTLift.lean:534`),
  `central_card_eq_reductions_mul_tcocycle` (already relates `#{central lifts}` to the `T`-reduction
  image and `#Z¹(T)`).
* **Consumes** P-16d6b's `hμ` shape and this ticket's `hM` count together (they multiply in
  `zBC_eq_mu_mul_reductionCount`).

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
