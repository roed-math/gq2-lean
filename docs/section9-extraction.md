# §9 extraction + induction design — ticket P-17 (F-half = P-17a)

Companion to [`GQ2/SectionNine.lean`](../GQ2/SectionNine.lean).  Maps the §9 nodes (paper
pp. 44–47: Lemmas 9.1–9.4, displays (143)–(153), the Theorem 4.2 endgame) to Lean, records
the deviations, and carries the work order for the O-half sub-tickets P-17b–P-17i.
Paper: `paper/A_Profinite_Presentation_for_G__Q_2.pdf`.

## Statement inventory

| Paper node | Lean name | Status | Ticket |
|---|---|---|---|
| Lemma 9.1 (coprime subdirect) | `GQ2.FiniteGroup.coprime_fiber_product` | **proved** (Goursat) | — |
| Lemma 9.2 core (SZ splitting) | `GQ2.FiniteGroup.oddOrder_twoQuotient_split` | **proved** (Schur–Zassenhaus) | — |
| §9.1 terminal case | `SectionNine.terminal_count_eq` | ☑ **proved** (std-3) | **P-17b** |
| Lemma **6.3** (κ⁰ existence; consumed at 9.3) | `SectionNine.kappa0_exists` (**amended** +`hsimple`+`htame`, deviation 4) | sorried (statement now true; assembly core proved) | **P-17e** |
| §7↦§8 concrete frame | `SectionNine.blockFrame` | sorried def | **P-17c** |
| §7.4↦§8 concrete enrichment | `SectionNine.blockEnrichment` | sorried def | **P-17d** |
| §9.2 `M`-stage partition | `SectionNine.mStage_partition` | sorried | **P-17f** |
| Lemma 9.4 bounds ((145)/(148)/(153)) | per work order below | not yet stated | **P-17g** |
| §9.3 recursion bookkeeping | `SectionNine.count_eq_of_closedRecursion` | sorried | **P-17h** |
| **Theorem 4.2** | `GQ2.thm_4_2` (+`thm_4_2_stratum`) | sorried, **relocated+amended** | **P-17i** |
| Lemma 9.3 (obstruction dual) | *not separately stated* | — | absorbed in P-16d2's `(W,o,e)` datum |

Lemma 9.3's content — the `R`-obstruction dual is `(R^∨)^C`, scalar pushouts exhaust it —
is exactly the obstruction-module datum `(W, o, e, hmB, hobs, hfib)` that P-16d2 supplies to
`stageR136_of`; it is proof-internal to `prop_8_9` (the P-14 precedent) and gets no §9
statement.  Likewise (146)/(147)/(149)/(151)/(152) are `prop_8_9`'s (137)/(138)/(139)/
(140)/(142), already frozen.

## Deviations (review-flagged)

1. **`thm_4_2` amended with `(hE2 : ∀ e : E, e ^ 2 = 1)` and relocated** from
   `GQ2/BoundaryFrame.lean` to `GQ2/SectionNine.lean` (P-17a, 2026-07-06).
   *Why the amendment*: the induction descends the θ-decoration through the block via
   `lemma_7_3`, whose paper statement is "every homomorphism **to an elementary abelian
   2-group** vanishes on `K`" (p. 37) — the exponent-2 hypothesis is the paper's own; and
   the terminal case's "every boundary decoration kills the odd group `Ñ`" (p. 45) equally
   needs the decoration target to be a 2-group.  Def 4.1's Lean form had left `E` an
   arbitrary finite `CommGroup`, which is *broader than the paper uses*: §10 applies
   Theorem 4.2 **only at `E = 0`** (p. 48), so the amendment restores the paper's operative
   generality and is downstream-harmless (P-18 discharges `hE2` trivially).
   *Why the relocation*: the proof needs §§5–9 machinery which imports `BoundaryFrame`
   (P-08/P-10 moved-out pattern).  `BoundaryFrame.lean` is now sorry-free and off the
   allowlist; `SectionNine.lean` takes its slot.
2. **The `M`-multiplicity is a hypothesis** (`mStage_partition`'s `mult`/`hmult`), not a
   computed `2^{2·dim M}`: the identity is source-generic; the numerics
   (`|Z¹_{Γ,ρ}(M)| = 2^{2 dim M}`, props 5.15/5.16) are discharged per source at P-17i.
   Same house pattern as P-16d3's `hlem86`/`hMcount`.
3. **The solver's IH-atoms**: `count_eq_of_closedRecursion` takes agreement of `e(T_B)`,
   `e(T_C)`, the (138) pullback-stratum counts (`hpull`, per scalar cover and stratum), and
   the phase-cover liftable counts (`hphase`, per `ζ`).  `hphase` is *derived* at P-17i from
   `lemma_8_3` at the phase covers + strata-IH ((153)); it is an atom here so the solver
   stays pure arithmetic.
4. **`kappa0_exists` amended with `(hsimple : FoxH.IsSimpleModTwo C V)` and
   `(htame : ActsThroughTame C V)`** (P-17e F-review, Fable 2026-07-06).  The P-17a form
   (arbitrary finite module) was *stronger than the paper's* and **false**: a datum is a
   splitting of `1 → V^∨ → Aut(E_f) → O(q) → 1` pulled back along `ρ`, non-split for
   `C = O(q)` at large extraspecial `E_f` (Griess, Pacific J. Math. 48 (1973)).  The paper's
   existence result is **Lemma 6.3** (simple self-dual *tame* `V`), whose hypotheses the
   amendment restores; both are dischargeable at the sole consumer P-17d (see its work
   order).  Full analysis: `docs/p17e-kappa0-scoping.md`.

## Asset inventory (all proved unless noted)

`coprime_fiber_product`, `oddOrder_twoQuotient_split` (FiniteGroupLemmas);
`tame_two_nilpotent` (P-17b2), **`lemma_9_2_core`/`sz_odd_complement`/`head_two_nilpotent`**
(P-17b1 — the Lemma 9.2 bundle + SZ complement + frame 2-nilpotency, all SectionNine, std-3);
`prop_3_10_gammaA` (marked `Γ_A(2) ≅ Π`, std-3), `prop_3_10_local_marked`
(`(Π,ν₂) ≅ (G_ℚ₂(2), ν_ur)`, B3c+B8), `BoundaryMaps` bundle incl. `pro2F` (P-25);
`exists_minimalBlock`, `lemma_7_1_head`, `lemma_7_1_dual`, `lemma_7_2`, **`lemma_7_3`**
(θ kills `K`, takes `hE : ∀ e, e ^ 2 = 1`), `prop_7_4`, `frattiniLike_normal`,
`frattiniLike_le` (SectionSeven); `blockAction`/`blockPerm` (BlockModule);
`sq_mem_frattiniLike`, `comm_mem_frattiniLike`, `eq_top_of_map_frattini_quotient_top`
(FrattiniNongen); `Enrichment`/`radData`/`mForm_of_qbar` (P-16d1);
`descended_splitting`/`lemma_8_7_count`/`prop_8_8_target`/`exists_polar_inverse`/
`centralCoverOfCocycle`/`phaseFamily` (P-16d4/d5, AffineTLift);
`LiftsOver`/`CentralOver`/`liftsOver_equiv`/`centralOver_equiv`/`half139_of`/`piBCiso`
(P-16d3, RadicalEdgeBridge); `partition137_of`/`stageR136_of`/`lemma_8_3`/`lemma_8_4`/
`lemma_8_5` + `prop_8_9` (statement; proof = P-16c/d2/d6, in flight);
`prop_5_15`/`prop_5_16_bundle` (the `Z¹`/`H²` numerics); `lemma_8_2_gammaA`/`_local`
(`#Hom(Γ,𝔽₂) = 8`); `symm_cocycle_is_coboundary` (Transgression, for P-17e);
`finite_continuousMonoidHom`/`finite_boundaryLifts`; `GammaA` t.f.g. (P-03); axiom B1
(`absGalQ2_isTopologicallyFinitelyGenerated`, **first consumed at P-17i**).

## Work order

### P-17b — terminal case — DECOMPOSED → P-17b1–b3

**Foundation landed (Opus 2026-07-06, std-3, in `SectionNine.lean`)**:
`scalarStack_centralized_of_coprime` (`IsScalarStack L` + `Coprime(#N,#L)` ⟹ `⁅N,L⁆ = ⊥`),
`coprime_card_of_odd_pTwo`, `isScalarStack.normal`.  A naive full dive was blocked: **no
result yet that a finite quotient of `Ttame` is 2-nilpotent** (needed for `Ñ` odd) — **now
resolved by P-17b2's `tame_two_nilpotent` (☑ 2026-07-06)**.  Split:

* **P-17b2 (gating foundation) — ☑ DONE (Opus 2026-07-06, std-3, `SectionNine.lean`)** — tame
  2-nilpotency: `H = ⟨s,t | tˢ=t²⟩` finite ⟹ `O²(H)` odd.  `t` odd (`Tame.tame_odd_order` ✓),
  `⟨t⟩ ◁ H` (`Tame.zpowers_normal_of_tame` ✓), `H/⟨t⟩` cyclic (image of `s`) ⟹ `H` metacyclic
  ⟹ 2-nilpotent.  Landed as **`tame_two_nilpotent`** (`∃ N, ∃ _ : N.Normal, Odd (card N) ∧
  IsPGroup 2 (H ⧸ N)` — the exact `oddOrder_twoQuotient_split` interface) plus two reusable
  abstract lemmas: **`exists_normal_odd_pow_mem_of_cyclic`** (odd part `Q₀ = ⟨g^{2ᵃ}⟩` of a
  finite cyclic group, membership-form 2-quotient — via `orderOf_pow'` + `ordProj/ordCompl`)
  and **`exists_normal_odd_twoQuotient_of_cyclic_quotient`** (odd-normal `C` + cyclic `H/C` ⟹
  2-nilpotent; `N := comap (mk' C) Q₀`, `card N = card C·card Q₀` via `index_comap_of_surjective`,
  the 2-quotient by lifting the membership form).  Note: the honest `O²(H)` is not constructed
  as a named characteristic subgroup — the existential `N` is forced `= O²(H)` (odd + 2-group
  quotient pins it), which is all P-17b1 needs.  Whole library green (8670), gate census 15.
* **P-17b1 (Lemma 9.2 structure) — ☑ DONE (Opus 2026-07-06, std-3, `SectionNine.lean`)** —
  `lemma_9_2_core`: `Ñ := ` odd complement of `L_Y` in `P = π_Y⁻¹(O²H)`.  **Deviation from the
  sketch**: SZ here is *not* `oddOrder_twoQuotient_split` (that splits an *odd* normal with
  2-quotient) — for `P` the normal subgroup `L_Y` is the *2-group* with *odd* quotient, so the
  general Mathlib SZ `Subgroup.exists_right_complement'_of_coprime` is used (in `↥P`, then
  transported to `Y`; helper `sz_odd_complement`).  Normality of `Ñ ◁ Y` is proved via the
  characterization **`Ñ` = the odd-order elements of `P`** (from `⁅Ñ,L_Y⁆=⊥`
  (`scalarStack_centralized_of_coprime` ✓) + coprime orders ⟹ `P = L_Y × Ñ` internally;
  conjugation preserves both `P` and order), avoiding any complement-uniqueness/conjugacy
  theory.  Output bundle `⟨Ñ, Ñ.Normal, Odd, IsPGroup 2 (Y/Ñ), Ñ⊓L_Y=⊥, ⁅Ñ,L_Y⁆=⊥, π_Y(Ñ)=M,
  Ñ⊔L_Y=P⟩` — the pieces P-17b3 feeds to `coprime_fiber_product` for `Y ≅ H ×_{H₂} (Y/Ñ)`.  The
  `M = O²H` hypothesis is discharged from the frame by **`head_two_nilpotent`** (`gen_ttame_quotient`
  ✓ + `tame_relation` ✓ + `tame_two_nilpotent` ✓).
* **P-17b3 (correspondence + assembly)** — deps b1.  Below (was the whole of P-17b):

### P-17b3 — the correspondence (⭐⭐⭐, O; Ax: **∅** — B3c/B8 turned out unneeded)

**☑ DONE (Opus 2026-07-06, std-3, sorry-free, `SectionNine.lean`)** — `terminal_count_eq` proved;
library green 8671, gate census 15; `#print axioms terminal_count_eq` = `[propext,
Classical.choice, Quot.sound]` exactly.  Landed: **(A) `boundaryLifts_equiv_qlifts`** (the (144)
bijection `BoundaryLifts b F T ≃ QLifts`, source-generic; `qliftHom` reconstruction via
`L92.fibreMulEquiv` + a 2nd `coprime_fiber_product` for surjectivity), **(B)
`qlifts_equiv_commonLifts`** (source-independence `QLifts Γ b ≃ CommonLifts` on `Π`, via
`compPro2Equiv`/`pro2Iso` = `maxProPHomEquiv` transported), **`ker_pro2A`** (from
`prop_3_10_gammaA` + `topGen_gammaA`), plus the `L92` support (`fibreMulEquiv`, `thetaBarQ`,
`mkCH`, `discreteTopology_Q`).  **The `head_factors_through_nuT`/`Zhat.zpowHat` route in
[`docs/p17b3-plan.md`](p17b3-plan.md) was AVOIDED** — source-independence instead rides
`b`-surjectivity onto `∂bd` (+ `compat*`, `nuT`/`nuTwo`-surjectivity), so the H-condition becomes
the source-free `∀ x∈∂bd, λ(g̃ x.2) = κ(F.α x.1)`.  **Deviations**: general Mathlib SZ
(`exists_right_complement'_of_coprime`), **not** `oddOrder_twoQuotient_split` (wrong side);
**B3c/B8 confirmed unneeded** (std-3 axiom trace); `terminal_count_eq` gains
`[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]`; `SectionNine` imports
`GQ2.SectionThreeMarked`.

Prove `terminal_count_eq`.  Route (paper §9.1 + p. 45 top):
1. `IsScalarStack T.LY` ⟹ every chief factor of `L_Y` is `Y`-central.  With
   `H₂ :=` the maximal 2-quotient of `H` and `N := ker (H → H₂)` (odd), Lemma 9.2:
   `N`'s preimage `P ≤ Y` splits as `L_Y × Ñ` (`oddOrder_twoQuotient_split` + the
   commutator-chain argument that `Ñ` centralizes `L_Y` — the paper's coprime-action
   collapse, cf. `lemma_7_2`'s proof for the same technique); `Ñ ◁ Y` unique, and
   `Y ≅ H ×_{H₂} Q` with `Q := Y/Ñ` a 2-group (143).
2. Boundary data descend: `θ` kills `Ñ` (odd source, exponent-2 target — `hE2`), the head
   splits through the pullback.
3. The (144) correspondence: boundary-framed `f : Γ → Y` with the fixed frame ↔ continuous
   `g : Π → Q` with `q ∘ g = α₂` and `θ̄ ∘ g = ψ̄` — via each source's marked maximal
   pro-2 quotient (`BoundaryMaps.pro2F`, `prop_3_10_gammaA`/`prop_3_10_local_marked`) and
   `coprime_fiber_product` for the surjectivity transfer (Lemma 9.1).  Exact-image subsets
   correspond likewise, so the two counts are *literally* counts of the same `Π`-set.
   No finiteness/B1 needed — produce a bijection, conclude `Nat.card`-equality.

### P-17c — `blockFrame` (⭐⭐⭐, O; Ax ∅)

Fill the def + prove its spec lemmas (state them in `SectionNine.lean` as you go; they are
P-17g's inputs):
* `YB := Y ⧸ Blk.R` (`frattiniLike_normal`), `piB := QuotientGroup.mk'`,
  `ker_piB : … = Blk.R` (`QuotientGroup.ker_mk'`).
* `TB : MarkedTarget H E YB`: head `piY` descends (`R ≤ K ≤ L_Y = ker piY` via
  `lemma_7_1_head`/`hKP`/`hPL`); decoration `thetaY` descends by **`lemma_7_3`** + `hE2`
  (θ kills `K ⊇ R`); `LY := L_Y.map piB` with `ker_piY` transported.  Same at
  `YC := Y ⧸ Blk.K` for `TC`.  `piBC := QuotientGroup.map id` with `piBC_comp`.
* `MB_eq`/`TBsub_eq`: definitional choices `MB := Blk.K.map piB` etc.
* `DR :=` the subtype `{R' : Subgroup Y // R'.Normal ∧ R' ≤ Blk.R ∧ R'.relIndex Blk.R ≤ 2}`
  itself, `zeroDR := ⟨Blk.R, …⟩` (`relIndex_self = 1 ≤ 2`), `card_DR := rfl`.
* `scalarCover l h`: cover `Y ⧸ l.val` (normal ✓), `p :=` the connecting quotient map,
  `z :=` the class of any `r₀ ∈ R \ l.val` (nonempty since `l ≠ zeroDR` forces
  `l.val < R`… derive `relIndex = 2` from `≤ 2` + `≠ R`); `z_sq`: `r₀² ∈ l.val` because
  `R/R'` has order 2; `central`: `[Y, R] ≤ R'`?  **Careful**: centrality of `z` in
  `Y/R'` needs `[Y, R] ≤ R'` — for `Y`-normal `R'` of index 2 in the `Y`-central-in-`K`…
  `R` is central in `K` (`lemma_7_2`) but `Y`-conjugation on `R/R'` is an action of
  `Y/K = C` on `ℤ/2` — trivial since `Aut(ℤ/2) = 1` **given the action fixes** … an
  action on a 2-element group fixing `1` is trivial ⟹ `[Y,R] ≤ R'` ✓ (prove via: for
  `y r`, `y r y⁻¹ r⁻¹ ∈ R` and its `R/R'`-class is `(y·r̄)·r̄⁻¹ = r̄·r̄⁻¹ = 1̄`).
  `ker_eq = zpowers z`: index-2 kernel `R/R'` = `{1, z}`.

### P-17d — `blockEnrichment` (⭐⭐⭐, O; Ax ∅; deps P-17c, P-17e)

Per `l = ⟨R', …⟩ ≠ zeroDR`, let `lam : ↥Blk.R → ZMod 2` be the `R ↠ R/R' ≅ 𝔽₂` character
(`hlam_hom` ✓; `hlam_conj` = the centrality computation above; `hlam_ne` from `R' ≠ R`).
* `q l h := mForm_of_qbar`'s witness (P-16d1) at `prop_7_4`'s output `(qbar, hspec)`;
  transport `↥(K.map piB) → ↥MB` along `MB_eq := rfl`-style defeq.
* `hq` (cover square relation): for `x = (y mod R')` with `piB`-image in `MB`, reduce to
  `lam (y²) = q(…)` — the `mForm_of_qbar` value clause + `z^{lam(r)} = (r mod R')` for
  `r ∈ R` (the `R/R' ≅ ⟨z⟩` dictionary).
* `hrad`/`hTzero`: `mForm_of_qbar` clauses (b)/(c), transported.
* `Vmod := Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P)` with the `BlockModule.blockAction`
  descended to `YC = Y/K` (`K` acts trivially: `[K,P] ≤ [P,P] ≤ S` since `V` abelian);
  `descend :=` the `K/R ↠ P/S`-composite (`k ↦ mk ⟨k, hKP hk⟩`), kernel `T_B`
  (`= (K∩S)R/R`, `lemma_7_1_head` folds `R`), surjective (`gen : K ⊔ S = P` +
  `mul_normal` decomposition — the `prop_7_4` `hdec` pattern).
* `qbar l h := prop_7_4`'s `qbar`; `hqbar` = its spec; `hinv` = its invariance clause
  descended to `YC`.
* **`hquad`** (new derivation): polar biadditivity of `q̄_λ`.  Route: at the `M`-level,
  `polar q_λ (x, y) = lam [x̃, ỹ]`-type commutator pairing — from `hq` + the
  `CentralObstruction.mul_comm_z` extraspecial ledger at the concrete cover, commutator
  biadditivity on the elementary abelian `M`;  descend along `descend_surj`.
* **`hns`** (new derivation): the polar radical of `q̄_λ` is a `C`-submodule of the simple
  `V` (invariance ⟹ radical stable); if radical `= V` then `q̄_λ` is additive
  (`polar ≡ 0` + `IsQuadraticFp2`) and `C`-invariant, so its kernel-pullback gives a
  `Y`-normal index-≤2 subgroup of `K` above `R` — `lemma_7_1_dual` kills it unless
  `q̄_λ = 0`, and `q̄_λ ≠ 0` is `prop_7_4`'s nonzero clause.  Hence radical `= ⊥` = 
  nonsingular.  (This is the paper's own endgame in Prop 7.4, p. 38.)
* `dat/hdat := kappa0_exists` (P-17e) at `(qbar, hquad, hns, hinv)` **+ the two amended
  hypotheses (deviation 4)**: `hsimple` from `Blk.chief` + `nontrivial_action` (Y-normal
  chiefness → `C`-stable `AddSubgroup` dictionary; `C`-stable = `Y`-invariant since the
  action is induced conjugation), and `htame` with `H :=` the frame head — `K` kills by
  `[K,P] ≤ S` (the `Vmod` descent above), the rest of `L_Y` kills by the proved
  `FoxH.lemma_5_12`, so the action descends along `Y/K ↠ Y/L_Y ≅ H`; generators/relation
  from `gen_ttame_quotient` ✓ + `tame_relation` ✓ (the `head_two_nilpotent` pattern).

### P-17e — `kappa0_exists` (⭐⭐⭐; Ax ∅) — **escalation RESOLVED, statement amended**

Now **Lemma 6.3** (paper p. 26), not 6.1: the general form was false (deviation 4; Griess
counterexample) — Lemma 6.1 only proves the "(59)+(60) ⟺ lifted action" equivalence and
*assumes* the lift.  Statement amended with `hsimple`/`htame` (F-review, Fable 2026-07-06);
design + staged proof plan in `docs/p17e-kappa0-scoping.md`.  **Proved already (std-3)**: the
assembly core `isEquivariantFactorSet_of_invariant` / `_of_biadditive_invariant` /
`IsEquivariantFactorSet.add` / `.comap` / `.comapHom` / `kappa0_exists_of_split`.
**Sub-tickets**: **P-17e1 ✅ DONE** (odd/unramified case — `kappa0_exists_of_odd` +
`exists_biadditive_refinement`, std-3: average a bilinear refinement over the odd `H`, `m = 0`,
no embedding/Maschke/SZ needed); P-17e2 square/free orbit-datum equivariance ((75)/(76) via the
biadditive entry point); P-17e3 the involution datum (Lemma 6.2, nonzero `m`); P-17e4 the
ramified split embedding (**Lemma 6.11** projectivity — the long pole); P-17e5 the invariant
normal form on `𝔽₂[H]^N` + final assembly closing `kappa0_exists`.
`symm_cocycle_is_coboundary` remains available but is no longer the route — the paper's
(60)-coherence comes from the explicit orbit data, not per-`c` correction patching.

### P-17f — `mStage_partition` (⭐⭐, O; Ax ∅ in-file)

The `LiftsOver`-total fibration: `Σ_ρ #LiftsOver(ρ) = mult · e(T_C)` (`hmult` +
`sigmaFiberEquiv`, the P-16d3 `half139_of` pattern), then stratify the total by exact
image (the `partition137_of` Step-2/3 machinery: `cmhCodRestrict`/`cmhInclude`
corestriction, `C`-onto strata ↔ `BoundaryLifts` of `TB.stratum J`, `C`-missing strata
empty on the left/excluded on the right, head-missing strata die by `hhead` ↔ the
`exactImageCountOn` dite-0 branch).  Watch the two banked gotchas: never `rw` a
`range = J` equation inside dependent hypotheses; `set` the stratification `Finset`.

### P-17g — Lemma 9.4 bounds (⭐⭐, O; Ax ∅; deps P-17c)

State + prove in `SectionNine.lean` (shapes final-ized against `blockFrame`'s actual
fields; semantic content fixed here):
* `card_LB_mul : Nat.card ↥(blockFrame T Blk hE2).TB.LY * Nat.card ↥Blk.R
    = Nat.card ↥T.LY` and `card_LB_lt` when `Blk.R ≠ ⊥` (Lagrange on `L_Y ↠ L_Y/R`).
* `card_LC_lt : Nat.card ↥(blockFrame …).TC.LY < Nat.card ↥T.LY` (`K ≠ ⊥` from
  `nontrivial_action`).
* (148): for any `CentralCover (blockFrame …).YB`-instance `Cov`, any stratum `J'` of
  `Cov.pullTarget TB` with `J := J'.map Cov.p` satisfying `J ≠ ⊤`, `J ↠ C`:
  `Nat.card ↥((Cov.pullTarget TB).stratum J' hJ').LY < Nat.card ↥T.LY` — via
  `|J' ∩ p⁻¹(L_B)| ≤ 2·|J ∩ L_B|` (double cover) and (145)'s
  `|J ∩ L_B| ≤ |L_B|/2` (the index-2 step: `J ∩ M < M` since `J ≠ ⊤` +
  `J·M = B`… follow the paper's (145) exact sequence `1 → J∩M → J∩L_B → L_C → 1`).
* (153): for any `CentralCover (blockFrame …).YC`-instance and any stratum:
  kernel card `≤ 2·|L_C| < |L_Y|`, using `4 ≤ Nat.card ↥Blk.K` (from `dim V ≥ 2`:
  `nontrivial_action` forces a non-fixed vector, and a 1-dim `𝔽₂`-module has trivial
  `GL` — formalize as `4 ≤ |V|` via: `V ≃ K/(K∩S)`-card + if `|V| = 2` the action is
  trivial, contradiction).
All bounds are **cover-generic** (independent of which `CentralCover` — kernels are
`p⁻¹`-doubles), which is what lets P-17i apply them to `prop_8_9`'s ∃-bound phase family.

### P-17h — `count_eq_of_closedRecursion` (⭐⭐, O; Ax ∅)

Pure arithmetic per the docstring: from (138)+`hpull`: `8·mJ₁ = Σ₁ = Σ₂ = 8·mJ₂` ⟹
`mJ` agree (ℕ-cancel 8; the finsums over `{J' | J'.map p = J}` agree pointwise by `hpull`,
support finite via `Finite (Subgroup cover)`); `mJOn` agree (dite both branches);
(139): `2z₁ = |MB|²·e₁(TC) = … = 2z₂` ⟹ `zBC` agree; (140): `2·#DT·z₁ = μ(…)` with RHS
agreeing via `hTC`+`hphase` ⟹ cancel `2·#DT ≠ 0` (ℤ, `mul_left_cancel₀`); the (139)/(140)
case split (`Classical.em` on the descent-∃) is target-side, identical for both sources;
(137): `mB = zBC − Σ mJOn` (ℤ) agree; `mB(zeroDR) = e(TB)` (`dif_pos`) agree by `hTB`;
(136): `(#DR : ℤ)·e(T) = zR·Σᶠ l, (2 mB l − e(TB))` — RHS agree termwise ⟹ cancel
`(#DR : ℤ) ≠ 0` (`Fintype` + `zeroDR` inhabitant).

### P-17i — the master induction (⭐⭐⭐, O; Ax: B1 + everything transitively; deps ALL + P-16 closed)

Prove `thm_4_2` in `SectionNine.lean`:
```
induction n := Nat.card ↥T.LY using Nat.strong_induction_on generalizing Y T …
by_cases hstack : SectionSeven.IsScalarStack T.LY
· exact terminal_count_eq …                                        -- P-17b
· obtain ⟨Blk⟩ := SectionSeven.exists_minimalBlock T.normal T.isPGroup_two hstack
  by_cases hR : Blk.R = ⊥
  · -- M-stage lane: mStage_partition at (blockFrame …) for BOTH sources;
    -- mult := 2^{2 dim M} discharged by prop_5_15 / prop_5_16_bundle;
    -- ⊤-stratum = e(TB) ≈ e(T) [R = ⊥ ⟹ piB iso; add the transport lemma or
    -- special-case the frame], proper C-onto strata < |L_Y| by (145) ⟹ IH;
    -- solve the two partition identities for e(T).
  · -- R-stage lane: En := blockEnrichment …;
    -- ⟨μ, G0, DT, _, phase, hA, hF⟩ := prop_8_9 B (blockFrame …) En F;
    -- count_eq_of_closedRecursion with atoms from IH:
    --   hTB/hTC: card_LB_lt (hR) / card_LC_lt;
    --   hpull: per (l,h,J'): exactImageCountOn unfolds to a stratum count of the
    --     pullTarget — dite-split; surviving branch = IH at the (148) bound;
    --   hphase: expand nPhase via lemma_8_3 at (phase ζ) over TC (side conditions:
    --     hfg [Γ_A: P-03; G_ℚ₂: axiom B1], hscalar [lemma_8_2_*]), strata agree by
    --     IH at the (153) bound, cancel 8.
```
Discharge `hDT ≠ 0`… **note**: `prop_8_9`'s ∃ gives `Fintype DT` but not `Nonempty`;
if the witness could be empty, (140) fails to pin `zBC` — but d6's witness has
`DT = (T^∨)^C ∋ 0`.  **Action for P-16d6** (coordinate): strengthen `prop_8_9`'s
existential with `Nat.card DT ≠ 0` (or return `0 < Nat.card DT`) — a benign statement
touch-up while it is still sorried; otherwise P-17i must re-derive nonemptiness, which is
impossible for an abstract witness.  FLAGGED on the P-16d6 row.

## Sub-ticket DAG

```
P-17a ☑ (this design + skeleton)
  ├─► P-17b2 ☑ (tame 2-nilpotency) ─► P-17b1 ☑ (Lemma 9.2) ─► P-17b3 ☑ (correspondence ⟹ terminal_count_eq)
  ├─► P-17e ◐ (κ⁰ restated = Lemma 6.3 + assembly core proved; decomposed ↓)
  │     ├─► P-17e1 ✅ (odd/unramified case — bilinear averaging, DONE)
  │     ├─► P-17e2 ✅ (square/free orbit data, m=0 — DONE)
  │     ├─► P-17e3 (involution datum, Lemma 6.2, m≠0)                          [startable]
  │     ├─► P-17e4 (ramified split embedding, Lemma 6.11) ◐ — assembly + trace +
  │     │     counting criterion all PROVED; residual sorry = the counting bound
  │     │     card_fixedPoints_pow_le_of_ramified (#V^P ^ |P| ≤ #V, ramified simple
  │     │     faithful; F2-rational plan in RegularSummand.lean + P-17e4 board row)
  │     └─► P-17e5 (invariant normal form + assembly) ◄─ e1,e2,e3,e4 ⟹ closes kappa0_exists
  ├─► P-17f ☑ (M-stage partition)
  ├─► P-17h ☑ (solver)
  ├─► P-17c ☑ (blockFrame) ─► P-17d (enrichment; also needs P-17e) ── discharges hsimple/htame
  │                        └► P-17g ☑ (bounds)
  └─► P-17i (master) ◄─ b,c,d,e,f,g,h + P-16c/P-16d2/P-16d6 (prop_8_9 proof)
```
P-17e3/e4 are startable **now**, in parallel (P-17e1, P-17e2 ✅ done; e5 after them).  P-17i is the sink and also
waits for the §8 closure (P-16c + P-16d2 + P-16d6).

## Axiom bookkeeping

The P-17 parent row's budget gains **B1** (the `hfg` discharge for `G_ℚ₂` at P-17i — the
first actual consumption of `absGalQ2_isTopologicallyFinitelyGenerated`) and **B3c**
(via `prop_3_10_local_marked` in the terminal case).  No census change — both are existing
axioms; the row's Ax column is updated accordingly (flagged for P-20-style review).
