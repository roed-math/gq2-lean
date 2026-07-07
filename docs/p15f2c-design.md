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
   deep-unit witness) — the deep §6.3 Kummer residue (unchanged from the original design).

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

### Remaining (the involution field-data construction — the deep §6.3 residue)

`lemma_6_16` needs the block's concrete Kummer presentation: the fields `k ≤ L`, the generator
`(d, δ, hδ, hδL)` with `L = k(δ)`, `δ² = d`, and the deep unit's coordinates `(A, β, u, v,
hAuv)` with `A = u + vδ`.  For the involution orbit, `L = K(√A_j)` where `A_j` is the deep unit
of the block scalar coordinate `α_j` (from `deepPart`'s witness), `k = K = fixed field of ker ρ`,
and `U₀/N` is the index-2 `⟨ĝ⟩`-extension.  Constructing this data from `deepPart`'s existential
+ f2b's coordinate is "concrete construction by the consumer" (the lemma_6_16 amendment note) —
the genuine deep remaining piece.  ⚠ needs the `AbsGalQ2 = Kummer.GaloisGroup ℚ_[2]` and
`ker ρ = k.fixingSubgroup` bridges (the DeepDualityK `kerToFixing`/`hker` pattern).

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
3. (deep residue) the involution `lemma_6_16` field-data construction (`k`, `L`, `δ`, `u`, `v`)
   from `deepPart`'s deep-unit witness — the last §6.3 Kummer piece.
