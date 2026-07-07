# P-15f2c — Shapiro coordinates + scalar deepness: design + landed record (Opus, 2026-07-08)

## ⟨2026-07-07 update⟩ f2b landed → f2d unblocked; deepness transport landed

**State change since the original design.**  P-15f2b's `OrbitDecomp.lean` is now **sorry-free and
complete** — the orbit-decomposition capstone `isEquivariantFactorSet_orbitSumDatum`
(`OrbitDecomp.lean:1036`) delivers clause (2), and `RegularIsometry.regular_isometric_embedding_orbit`
(`RegularIsometry.lean:165`) packages the full f2b interface with `datW` **definitionally** the
orbit sum `sumDatum (orbitIndexSet Q_W) orbitDatum` — the exact shape
`OrbitVanish.Q0loc_vanish_of_datum_decomp` consumes.  (The P-15f2b *ticket text* saying "PAUSED at
foundation" is **stale**.)  So the f2d assembly of `lemma_6_17_vanish` is unblocked.

**Free-orbit conjugation-stability caveat: RESOLVED (banked).**  `AdmissibleCount.conjAct_deepClasses`
(`AdmissibleCount.lean:128`, std-3) is exactly the free-orbit stability — `conjAct ρ g` carries a
deep class to a deep class (`conjAct ρ g [κ_β] = [κ_{g•β}]` via `kcf_conj`, `g•A` again deep by
`norm_galois`).  It is now an f2d *consumer*, not new f2c work.

**LANDED (2026-07-07, `ShapiroDeepness.lean`, all std-3 exactly) — the f2d infrastructure bricks:**
* **`deepPart_mapCoeff1`** (§DeepTransport) — deepness transports along any continuous equivariant
  coefficient map `f : W₁ →+ W₂`: `x ∈ deepPart ρ ⟹ mapCoeff1 f x ∈ deepPart ρ` (every scalar
  restriction of the pushed class is a scalar restriction of `x` at the pre-composed functional,
  `ShapiroExtend.phiRes_mapCoeff1`, hence deep).  Carries `X₊` across the Lemma-6.14 embedding `ι`.
* **`FactorSet.reindexHom`** + **`graphPullback_reindexHom`** + **`Q0loc_reindexHom`** (§Reindex,
  §ReindexQ0loc) — the **C ↔ `AbsGalQ2 ⧸ ker ρ` bridge**.  f2b's orbit datum lives over `G ⧸ N`
  while the ambient `Q0loc`/Lemma-6.14 transport is over `C`; reindexing the datum's acting group
  along `φ : C' → C` (only `m` sees the group; `f` unchanged) gives, when the `C'`-action is the
  `φ`-pullback of the `C`-action, `graphPullback (dat.reindexHom φ) ρ' = graphPullback dat (φ∘ρ')`
  and hence `Q0loc (dat.reindexHom φ) ρ' = Q0loc dat (φ∘ρ')`.  With `φ = e : C → AbsGalQ2 ⧸ ker ρ`
  and `e ∘ ρ = mk' (ker ρ)` this rewrites the C-level datum as the `mk'`-level orbit map so the
  banked `lemma_6_15_*` (stated at `mk' N`) and `Q0loc_vanish_of_datum_decomp` fire.

**The f2d assembly path** (`lemma_6_17_vanish`, `SectionSix.lean:882`, still `sorry`; consumed at
`DeepPart.lean:1448`):
```
Q0loc D dat ρ x                                            -- arbitrary equivariant dat for q
  = Q0loc D (ι∗datW) ρ x        via Q0loc_datum_indep_of_core  [needs DI-core, f2a]
  = Q0loc D datW ρ (ι∗x)        via RepIndependence.lemma_6_14 [banked]
  = 0                           via Q0loc_vanish_of_datum_decomp with datW = sumDatum orbitDatum
                                    [needs per-orbit hcoh + hvanish]
```
`ι∗x = mapCoeff1 ι x` is deep by `deepPart_mapCoeff1` (LANDED); `e : C ≃* AbsGalQ2 ⧸ ker ρ` from ρ
onto; `hvanish` from the landed cores (`hvanish_cup`/`hvanish_evensNorm`) + the block-coordinate
deepness (`mem_deepPart_iff` on `ι∗x`) + `conjAct_deepClasses` (free) / `lemma_6_16` (involution).

**Remaining gaps** (refined):
1. **The Shapiro coordinate read** (the substantive "Shapiro coordinates" content, ⭐ the core):
   `hcoh` needs the W-cocycle `(out (ι∗x)).1`'s block-`j` coordinate to be *cohomologous to*
   `shapiroFun N α_j` for a **scalar** `α_j : Z1 (ker ρ) 𝔽₂`, so that `lemma_6_15_square/free/involution`
   (`SectionSix.lean:664/690/706` — stated at `shapiroFun N α.1`, acting map `mk' N`) applies.
   Two sub-pieces: **(a)** Shapiro coordinate extraction (block ≅ `shapiroFun α_j`, `H¹(G,Coind) ≅
   H¹(N,𝔽₂)` — **not banked**), **(b)** `graphPullback` respects cohomologous inputs (partly banked:
   `DeepPart.graphPullback_add_sub_mem_B2`, `RepIndependence.graphPullback_sub_mem_B2`), plus the
   `mk' N` ↔ `ρ = e∘mk'` reindex.
2. **DI-core** (datum-independence heart, `Q0loc_datum_indep_of_core`'s `hcore`) — a genuine
   cohomological gap (`H¹(C, V∨)` obstruction, increment B); **f2a territory**, not f2c.
3. **The involution `lemma_6_16` field-data** construction (`k`, `L`, `δ`, `u`, `v` from `deepPart`'s
   deep-unit witness) — the deep §6.3 Kummer residue.  ⟨2026-07-07⟩ **SPLIT → P-15f2c2a
   (abstract Kummer package) ∥ P-15f2c2b (spine)**; tower dictionary **CORRECTED** (see
   §"Remaining — the involution field-data construction" below — the previous
   "`k` = fixed field of `ker ρ`" line was misassigned).

The original design (`hcoh`/`hvanish` reduction, deepness extraction) is below, still accurate.

---


Produces the two per-orbit hypotheses of `OrbitVanish.Q0loc_vanish_of_datum_decomp`
(`OrbitVanish.lean:294`) for the deep half `x ∈ deepPart ρ`, at the regular module after the
Lemma-6.14 transport.  Boundary with **P-15f2b** (`OrbitDecomp.lean`, the other agent): they
own the orbit **decomposition** (`sumDatum`, `orbitDatum`, the `blockProj`/`blockBas`
coordinates, `isEqFS_orbitDatum`); f2c owns the per-orbit **cohomology matching** (`hcoh`) and
**scalar deepness** (`hvanish`).

## The reducer contract (what f2c+f2d must feed)

```
hcoh    : ∀ o ∈ s, H2ofFun AbsGalQ2 (graphPullback (datf o) ρ (out x)) = H2ofFun AbsGalQ2 (cor2Fun (U o) (inner o))
hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0
```

## `hcoh` — direct `lemma_6_15_*` (f2b structures the pullbacks as its inputs)

P-15f2b's `datf o = (orbitDatum).comap (blockProj)` is a **definitional** comap, so
`graphPullback (datf o) ρ (out x)` is *syntactically* `graphPullback (orbitDatum) (mk' N)
(shapiroFun N α)` at the block coordinate `α` (OrbitDecomp header, lines 22–26).  Hence `hcoh`
per orbit is the banked lemma applied at that coordinate:
* **square**: `SectionSix.lemma_6_15_square N hNo α` — `inner o = fun p ↦ α.1 p.1 * α.1 p.2`, `U o = N`.
* **free**: `lemma_6_15_free N hNo α β ghat` — `inner o = fun p ↦ α.1 p.1 * (ḡβ).1 p.2`, `U o = N`.
* **involution**: `lemma_6_15_involution N hNo α ghat …` — `inner o = evensNormFun (N.subgroupOf U₀) ĝ α`, `U o = U₀`.
Instantiation needs f2b's coordinate reads (`out(ι∗x)`'s block `j` = `shapiroFun N α_j`) → **f2d**.

## `hvanish` — scalar deepness  ⭐ the f2c content

`x ∈ deepPart ρ` ⟹ every scalar restriction is a **deep Kummer class**:
`LocalKummer.mem_deepPart_iff` — `x ∈ deepPart ρ ↔ ∀ φ, phiRes ρ x φ ∈ deepClasses (ker ρ)`.
Each block coordinate `α_j` satisfies `H1mk (ker ρ) α_j = phiRes ρ x φ_j` (the `j`-th
coordinate functional), hence `∈ deepClasses (ker ρ)`.  With `ker ρ = k.fixingSubgroup`
(`k = fixed field of the open finite-index `ker ρ``; the Galois-correspondence field bridge,
supplied at f2d as `hker`), the deepness feeds:

### LANDED (`GQ2/ShapiroDeepness.lean`, std-3 + B11a)

* **`H2ofFun_eq_zero_of_H2mk`** — the shared `H2mk = 0 ⟹ H2ofFun = 0` tail.
* **`hvanish_cup`** (square + free): for `a, b : Z1 k.fixingSubgroup` with `H1mk a, H1mk b ∈
  deepClasses k.fixingSubgroup`, `H2ofFun k.fixingSubgroup (cup11Fun mul a.1 b.1) = 0`.  Via
  `cup_deepClasses` (eq.-(94) orthogonality; `trivialCupPairing = cup11 = H2mk⟨cup11Fun⟩`) +
  `B²`-extraction.  With `htriv`, `cup11Fun mul a.1 b.1 = fun p ↦ a.1 p.1 * b.1 p.2` = the
  reducer's `inner o` (square at `a = b`; free at `a = α, b = ḡβ`).
* **`hvanish_evensNorm`** (involution cochain bridge): `evensNormH2 … = 0 ⟹
  H2ofFun G (evensNormFun U s α) = 0` (since `evensNormH2 = H2mk⟨evensNormFun⟩`).  f2d composes
  `SectionSix.lemma_6_16` (whose conclusion IS `evensNormH2 … = 0`) with this bridge.
* **`hvanish_involution`** (P-15f2c2b, LANDED 2026-07-08 — the assembly core; `#print axioms` =
  std-3 + {B9, B11a, B11b}, sorry-free): the involution-orbit `hvanish` assembled as
  `hvanish_evensNorm ∘ SectionSix.lemma_6_16`.  Takes the concrete Kummer field data — the tower
  `k ≤ L` (`hindex`, `hunram`), the √-generator `(d, δ, hδ, hδL, hLδ)`, coordinates `(u, v, hAuv)`,
  the deep witness `(A, β, hdeep, hβ, hβ0)`, side-conditions `(s, hs, htriv, hUo, hα, hαc)` — as
  hypotheses (the c2a ∃-package + the `mem_deepPart_iff` deep witness, discharged by the plumbing
  step / f2d), and concludes `H2ofFun ↥(k.fixingSubgroup) (evensNormFun ((L.fs).subgroupOf (k.fs))
  s (kummerCocycleFun β ∘ ·)) = 0` — the reducer's involution `hvanish` in `k.fixingSubgroup`
  vocabulary (f2d bridges `k.fixingSubgroup = U₀` via the InfiniteGalois transport
  `fixingSubgroup (fixedField U₀) = U₀`).  Proof is the one-liner
  `hvanish_evensNorm htriv hUo hindex hs _ hα hαc (lemma_6_16 …)`: `lemma_6_16`'s conclusion is
  literally the `evensNormH2 … = 0` that `hvanish_evensNorm` consumes, over the SAME ambient
  `↥(k.fixingSubgroup)` — no dependent rewrite, no `sorry`.
* **`hvanish_involution_of_deepClass`** (P-15f2c2b, LANDED 2026-07-08 — the witness-plumbing step
  in `L`-vocabulary; `#print axioms` = std-3 + {B9, B11a, B11b}, sorry-free): from a deep class
  `ξ ∈ deepClasses (L.fixingSubgroup)` + the c2a package (threaded as the hypothesis
  `hc2a : ∀ A, IsDeepUnit L.fixingSubgroup A → ∃ d δ u v, …`), produces the involution `hvanish` for
  the class's own square root `β`.  Does steps (2)–(5): unpacks `deepClasses` → `(A, β, hdeep, hβ,
  hβ0)` (the cochain `IS` `kummerCocycleFun β` by definition — step 4 free); derives the
  side-conditions `hα` (additivity via `kummerCocycleFun_hom_on` on `L.fixingSubgroup`, which fixes
  `A`; the `subgroupOf` coercion closes by `push_cast; rfl`) and `hαc` (continuity via
  `kummerCocycleFun_continuous β ∘ Subtype.val ∘ Subtype.val`); applies `hc2a` + `hvanish_involution`.
  **Remaining c2b** = only the `ker ρ = L.fixingSubgroup` transport (`L := fixedField (ker ρ)`,
  `InfiniteGalois.fixingSubgroup_fixedField` — the `ResidueLift.splitField`/`kerGal` pattern) to feed
  `mem_deepPart_iff`'s deep class into this lemma; cleanest at **f2d** (ResidueLift is importable
  there — avoids duplicating `kerGal`).  The c2a package proof is **P-15f2c2a**; `hunram` is **c2c**.

### Remaining — the involution field-data construction (SPLIT 2026-07-07 → c2a ∥ c2b; c2c deferred)

`lemma_6_16` needs the block's concrete Kummer presentation: the fields `k ≤ L`, the generator
`(d, δ, hδ, hδL)` with `L = k(δ)`, `δ² = d`, and the deep unit's coordinates `(A, β, u, v,
hAuv)` with `A = u + vδ`.  Constructing this data from `deepPart`'s existential + f2b's
coordinate is "concrete construction by the consumer" (the lemma_6_16 amendment note).

⚠ **Tower dictionary (CORRECTED 2026-07-07** — the previous revision of this paragraph had it
misassigned): matching the reducer's involution `hvanish` (`H2ofFun ↥U₀ (evensNormFun
(N.subgroupOf U₀) ĝ α) = 0`) against `lemma_6_16`'s conclusion (`evensNormH2` over
`↥(k.fixingSubgroup)` with index-2 `(L.fixingSubgroup).subgroupOf (k.fixingSubgroup)`) forces
`k.fixingSubgroup = U₀` and `L.fixingSubgroup = N = ker ρ`, i.e.:

* **`k = fixedField U₀`** (the *lower* field) and **`L = fixedField (ker ρ)`** (the *upper*);
  `Gal(L/k) = U₀/N = ⟨ĝ⟩`, quadratic from `[U₀ : N] = 2`;
* the deep unit `A_j` lives in `L` (`IsDeepUnit`'s `N`-fixedness conjunct + `fixedField`);
  `β = √A_j` generates a *further*, unnamed extension — `L ≠ k(√A_j)`;
* the witness transport `IsDeepUnit (ker ρ) A → IsDeepUnit L.fixingSubgroup A` is an
  **equality** rewrite: `ker ρ` open ⟹ closed ⟹ `fixingSubgroup (fixedField (ker ρ)) = ker ρ`
  (InfiniteGalois closed-subgroup correspondence; the DeepDualityK `kerToFixing`/`hker`
  pattern) — no monotonicity helper.  Likewise `U₀ ⊇ ker ρ` open ⟹ `k.fixingSubgroup = U₀`.

**Split** (principle: `lemma_6_16`'s signature is landed and frozen, so bricks statable purely
against it parallelize with zero f2b coupling; `hunram` is not yet statable — see c2c):

* **P-15f2c2a — abstract Kummer presentation package**: ✅ **LANDED 2026-07-07 (Fable),
  `GQ2/QuadraticAdjoin.lean` (340 ln), all declarations proved, std-3 exactly, registered,
  tree green (8719).**  Exports **`exists_kummer_presentation`**:
  `(hkL : k ≤ L) (hdeg : finrank ↥k ↥(extendScalars hkL) = 2) (hAL : A ∈ L)`
  `(hA1 : ‖A − 1‖ < ‖2‖) ⟹ ∃ d δ u v, δ² = ↑d ∧ δ ∈ L ∧ hLδ ∧ A = ↑u + ↑v·δ` — hypothesis
  shapes match `lemma_6_16` on the nose.  **Interface refinements vs the spec above**: the
  deepness input is the *norm inequality*, not `IsDeepUnit` (c2b converts via banked
  `norm_sub_one_lt_of_isDeepUnit`; `A ∈ L` comes from `N`-fixedness + `fixedField`) — so the
  `hc2a` threading needs this 2-line conversion; the index-2 → degree-2 bridge stays c2b's.
  **Routes (simpler than planned — no `powerBasis`, no `liftNormal`, no minpoly
  identification)**: (i) `fixingSubgroup_adjoin_simple` (the mathlib gap, proved *generally*
  over any `F`, `E`): `fixingSubgroup F⟮δ⟯ = stabilizer δ` via the Galois connection
  `le_iff_le` at `zpowers σ`; `subgroupOf` packaging transports along `fixingSubgroupEquiv`
  (underlying-function `rfl`) + `mem_extendScalars` (`Iff.rfl`); (ii) conjugation from
  `InfiniteGalois.fixedField_fixingSubgroup` at `⊥` + `fixingSubgroup_bot` (`fixedField ⊤ =
  ⊥`; `IsGalois ↥k ℚ̄₂` auto by `tower_top_intermediateField`) — some σ moves δ, and
  `(σδ)² = σ(δ²) = d = δ²` forces `σδ = −δ`; (iii) complete-the-square in **discriminant
  form** `δ := 2θ + a`, `d := a² − 4b` (no division); (iv) coordinates by
  `Algebra.adjoin_singleton_eq_range_aeval` + `modByMonic` reduction
  (`natDegree_modByMonic_lt`) — needs no `δ ∉ k`; (v) unit coordinate by `norm_galois` at
  `AlgEquiv.restrictScalars` + `IsUltrametricDist.norm_add_le_max`, uniform in `v` (the
  `v = 0` sub-case needs no split).  Gotchas banked in the board row.
* **P-15f2c2b — spine: dictionary + assembly** (`ShapiroDeepness.lean`).  Step-0 f2b
  involution-coordinate read (`ĝ`, `hs`); pin the tower above + **decide the `hunram` route →
  scope c2c**; witness plumbing (`mem_deepPart_iff`, `A ∈ L`, the two equality transports,
  `hkL`, the fixing-index-2 → degree-2 bridge for c2a's interface); mechanical side-conditions
  (`hα`/`hαc` banked: `kummerCocycleFun_mul` `GQ2/Kummer.lean:179`, continuity `:148`; `hUo`
  from open `ker ρ`); the `α_j = kummerCocycleFun β` **cochain-level** match (`heq` is
  class-level — confirm the `H2mk`/`H2ofFun` layer absorbs a `B¹` discrepancy, else the
  `graphPullback_…_mem_B2` machinery); assemble `lemma_6_16` ∘ `hvanish_evensNorm` with c2a's
  package + `hunram` sorried for an early end-to-end typecheck, discharge as they land.
* **c2c — `hunram` (Step-0 RESOLVED 2026-07-08 by c2b — SPAWNABLE; `L/k` is ALWAYS unramified,
  NO statement amendment).**  The involution block coordinate gives `ρ(ĝ)` **order 2** in `C`
  (`hg : ĝ ∉ N ⟹ ρ(ĝ) ≠ 1`; `hg2 : ĝ² ∈ N ⟹ ρ(ĝ)² = 1`).  `C = c(Ttame)` is a *tame* quotient,
  so its inertia is the image `⟨c tameTau⟩` of tame inertia, which has **odd** order —
  `Tame.tame_odd_order` (`GQ2/Tame.lean:42`) applied to `tame_relation`'s `σ⁻¹τσ = τ²`
  (`orderOf (c tameSigma) ≠ 0` since `C` is finite).  An order-2 element cannot lie in an
  odd-order subgroup, so `ρ(ĝ) ∉ inertia`, whence `L/k = K / K^{⟨ĝ⟩}` (`L = fixedField (ker ρ)`,
  `k = fixedField U₀`) is **unramified** and `hunram : ∀ x ∈ L, x ≠ 0, ∃ y ∈ k, ‖x‖ = ‖y‖`
  (equal value groups `‖L^×‖ = ‖k^×‖`) HOLDS.  So **c2c is a genuine proof obligation (TRUE),
  not an amendment**: derive `hunram` from `ρ(ĝ) ∉ inertia` in the repo's spectral-norm
  vocabulary (the residue-field-free bridge — the c2c content; likely via B13 unit-filtration /
  the norm-value-group argument).  c2b threads `hunram` as an input (sorried until c2c) and
  assembles; the involution vanish route is SOUND for **every** involution orbit — no ramified
  exception, no upstream-hypothesis leak into the frozen `lemma_6_17_vanish` signature.

## Free-orbit deepness caveat

`hvanish_cup` for the free orbit needs `H1mk (ḡβ) ∈ deepClasses` — the **conjugate** `ḡβ` of a
deep class.  `deepClasses` is conjugation-stable (a deep unit's Galois conjugate is deep;
`IsDeepUnit` is preserved under the `G`-action since `‖·‖` is Galois-invariant) — a small lemma
to add at f2d/here if not banked.

## Work order

1. ✅ LANDED — `hvanish_cup`, `hvanish_evensNorm`, `H2ofFun_eq_zero_of_H2mk` (the `hvanish`
   cores, `GQ2/ShapiroDeepness.lean`).
2. (f2d, coordinate plumbing) `hcoh` via `lemma_6_15_*` at f2b's block reads; the deepness
   `H1mk α_j ∈ deepClasses` via `mem_deepPart_iff`; the `ker ρ = k.fixingSubgroup` bridge.
3. (deep residue — SPLIT 2026-07-07) **P-15f2c2a** (abstract Kummer presentation package) ∥
   **P-15f2c2b** (spine + assembly); **c2c** (`hunram`) deferred pending c2b's Step-0 route
   decision.  See §"Remaining — the involution field-data construction".
