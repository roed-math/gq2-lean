# P-15f2 handoff — closing `lemma_6_17_vanish` (`Q⁰_loc|X₊ = 0`)

*Self-contained continuation guide (Opus, 2026-07-07). Read this before touching the f2 family.*

## 0. Orientation / TL;DR

**Goal**: discharge the `sorry` in `SectionSix.lemma_6_17_vanish` — the base connecting map
`Q⁰_loc` vanishes on the deep half `X₊ = deepPart ρ`. This is one of the two remaining §6.3
Kummer cores (the other, `lemma_6_17_dim`, is a separate lane — P-15f1/f5–f8, its chain now built).

**Route** (Lemma 6.14 + §6.2 orbit decomposition + §6.3 deepness, the paper's proof):
```
Q⁰_loc dat ρ x
  =[f2a: datum-independence]   Q⁰_loc (datW_C.comap ι) ρ x
  =[Lemma 6.14: RepIndependence.lemma_6_14]  Q⁰_loc datW_C ρ (ι∗x)
  =[f2d wiring: reindex + orbit reducer]     0
```
where `ι : V →+ W` is f2b's isometric embedding into the regular module `W = Fin K → RegRep N`
(`N = ker ρ`), `datW_C` its orbit-sum datum reindexed to `C`, and the final `0` is
`Q0loc_vanish_of_datum_decomp` fed per-orbit `hcoh` (f2c1) and `hvanish` (landed cores + f2c2).

**State**: f2b is **fully landed**; the f2d transport/reindex/deepness **infrastructure is landed**;
the two `hvanish` cores are landed. The genuinely open mathematics is **three tickets**:
- **P-15f2a** — DI-core (datum-independence heart), ⭐⭐⭐, cross-lane.
- **P-15f2c1** — the Shapiro H¹ coordinate read (`hcoh`), ⭐⭐⭐, the keystone.
- **P-15f2c2** — the involution deep-unit Kummer presentation (`hvanish` field-data), ⭐⭐.

then **P-15f2d** = thin composition. f2c1 and f2c2 are parallelizable (no shared dependency).

**Do not** edit `GQ2/Foundations/Axioms.lean` (frozen). Keep every landed file sorry-free and
std-3 (`{propext, Classical.choice, Quot.sound}`) unless a B-axiom is explicitly in the ticket's
`Ax` budget; gate with `lake build` + `scripts/check_axioms.sh` (or `lean_verify` per decl).

---

## 1. The target

`GQ2/SectionSix.lean:882` (statement frozen — co-owned with P-15f1/f8; **do not** edit the
signature, use the §6.18ram statement-move pattern to exit SectionSix):

```lean
theorem lemma_6_17_vanish (D : TateDuality 2) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat) :
    ∀ x ∈ deepPart (V := V) ρ, Q0loc D dat ρ x = 0 := by sorry
```

Ambient section vars (`SectionSix.lean:130–139`): `{C : Type} [Group C] [TopologicalSpace C]
[DiscreteTopology C] [Finite C]`, `{V : Type} [AddCommGroup V] [TopologicalSpace V]
[DiscreteTopology V] [Finite V] [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V]
[DistribMulAction C V]`.

**Consumer**: `GQ2/DeepPart.lean:1448` (`prop_6_18_ramified`). It currently inherits the `sorryAx`
through this lemma; closing it clears the ramified determinant theorem.

`Q0loc` (`SectionSix.lean:145`) is definitionally
`fun x ↦ iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1))`.

---

## 2. The ticket tree (`docs/tickets.md`)

| Ticket | Piece | Status |
|---|---|---|
| P-15f2 | umbrella (`lemma_6_17_vanish`) | ◐ |
| **P-15f2a** | DI-core (datum-independence, Lemma 6.1/6.4) | ☐ OPEN ⭐⭐⭐ |
| **P-15f2b** | isometric regular embedding + §6.2 orbit decomposition | ☑ **LANDED** |
| P-15f2c | Shapiro coordinates + scalar deepness (COORDINATOR) | ◐ cores+infra landed |
| **P-15f2c1** | Shapiro H¹ coordinate read (`hcoh`) | ☐ OPEN ⭐⭐⭐ (keystone) |
| **P-15f2c2** | involution deep-unit Kummer presentation (`hvanish`) | ☐ OPEN ⭐⭐ |
| **P-15f2d** | final assembly + SectionSix splice | ☐ OPEN (thin — infra landed) |

---

## 3. What is BANKED (with exact names + files)

Everything below is landed, sorry-free. Signatures abbreviated; read the file for full binders.

**f2b — the embedding + orbit decomposition** (`GQ2/RegularIsometry.lean`, `GQ2/OrbitDecomp.lean`):

- `RegularIsometry.regular_isometric_embedding_orbit` (`RegularIsometry.lean:165`) — the full f2b
  interface. Given `e : C ≃* G ⧸ N`, `cT`, `hgen`, and the module hyps, produces
  ```
  ∃ (K : ℕ) (ι : V →+ (Fin K → RegRep N)) (r : (Fin K → RegRep N) →+ V),
    IsEquivariantFactorSet (fun F => q (r F))
      (sumDatum (orbitIndexSet N (fun F => q (r F))) (orbitDatum N)) ∧    -- datW = orbit sum
    (∀ v, q (r (ι v)) = q v) ∧                                            -- isometry
    (∀ (a : C) (v : V), ι (a • v) = e a • ι v) ∧                          -- e-equivariance
    (∀ v, r (ι v) = v)                                                    -- retraction
  ```
  `datW` is **definitionally** the orbit sum — the `Q0loc_vanish_of_datum_decomp` shape. Needs
  `[Fintype (G ⧸ N)]`.
- `OrbitDecomp.isEquivariantFactorSet_orbitSumDatum` (`OrbitDecomp.lean:1036`) — the capstone the
  above wraps. `IsEquivariantFactorSet Q (sumDatum (orbitIndexSet N Q) (orbitDatum N))`.
- `OrbitDecomp.orbitDatum` (`:779`) — `OrbitIx K Γ = Fin K ⊕ (Fin K × Γ) ⊕ (Fin K × Fin K × Γ)`
  → `FactorSet (G⧸N) (Fin K → RegRep N)`; each summand is a **definitional `FactorSet.comap`** of a
  literal `squareOrbitDatum`/`invOrbitDatum`/`freeOrbitDatum` along `blockProj`/`blockProj₂`.
- `OrbitDecomp.isEqFS_orbitDatum` (`:832`), `sum_orbitIndexSet` (`:807`), `orbitIndexSet` (`:802`).

**Lemma 6.14 transport** (`GQ2/RepIndependence.lean:157`) — `RepIndependence.lemma_6_14`:
```
Q0loc D (datW.comap i) ρ x = Q0loc D datW ρ (mapCoeff1 i hic hicompat x)
```
with `datW : FactorSet C W`, `i : V →+ W`, `hic : Continuous i`,
`hicompat/hiC : ∀ g/c, i (g•v) = g•i v` / `i (c•v) = c•i v`, `hdatW : IsEquivariantFactorSet q datW`,
`hρW : ∀ g w, g•w = ρ g•w`. **C-level** (fixed acting group). `mapCoeff1 i x = ι∗x`.

**The orbit reducer** (`GQ2/OrbitVanish.lean:294`) — `Q0loc_vanish_of_datum_decomp`:
```
(hdat_eq : dat = sumDatum s datf)
(hdatf : ∀ o ∈ s, IsEquivariantFactorSet (qf o) (datf o))
(U : ι → Subgroup AbsGalQ2) (hfin/hopen) (inner) (hZ2)
(hcoh : ∀ o ∈ s, H2ofFun AbsGalQ2 (graphPullback (datf o) ρ (out x)) = H2ofFun (cor2Fun (U o) (inner o)))
(hvanish : ∀ o ∈ s, H2ofFun ↥(U o) (inner o) = 0)
⊢ Q0loc D dat ρ x = 0
```
**No `deepPart` hypothesis** — deepness enters only through `hvanish`.

**Lemma 6.15** (`GQ2/SectionSix.lean:664/690/706`) — `lemma_6_15_{square,free,involution}`. Shape
(square): `H2ofFun G (graphPullback (squareOrbitDatum N) (QuotientGroup.mk' N) (shapiroFun N α.1))
= H2ofFun G (cor2Fun N (fun p ↦ α.1 p.1 * α.1 p.2))` for `α : Z1 N (ZMod 2)`. **Note the acting map
is `mk' N`, and the cochain is `shapiroFun N α.1`** — this is what f2c1 must produce.

**Lemma 6.16** (`GQ2/SectionSix.lean:752`) — `lemma_6_16` (deep-unit Evens norm, Ax B9/B11a). Takes
the concrete Kummer field data `(k, L, hkL, hindex, hunram, d, δ, hδ, hδL, hLδ, A, β, hdeep, hβ,
hβ0, u, v, hAuv, s, hs, htriv, hUo, hα, …)` and concludes `evensNormH2 … = 0`. **f2c2 builds the
field data.**

**Deepness extraction** (`GQ2/LocalKummer.lean`): `mem_deepPart_iff` (`:305`):
`x ∈ deepPart ρ ↔ ∀ φ, phiRes ρ x φ ∈ deepClasses (ρ.toMonoidHom.ker)`; `cup_deepClasses` (`:374`,
the eq.-(94) orthogonality, Ax B11a); `deepClass_eq_kummerClassK` (`:335`).

**Free-orbit conjugation-stability** (`GQ2/AdmissibleCount.lean:128`) — `conjAct_deepClasses`:
`conjAct ρ g` carries a deep class to a deep class (`= [κ_{g•β}]` via `kcf_conj`, `g•A` deep by
`norm_galois`). The free orbit's `hvanish` needs the conjugate `ḡβ` deep — this supplies it.

---

## 4. What was LANDED THIS SESSION — the f2d infrastructure (`GQ2/ShapiroDeepness.lean`, all std-3)

- **`hvanish_cup`** — square + free `hvanish`: `H1mk a, H1mk b ∈ deepClasses k.fixingSubgroup ⟹
  H2ofFun (cup11Fun mul a.1 b.1) = 0` (via `cup_deepClasses` + B²-extraction). **Ax: B11a.**
- **`hvanish_evensNorm`** — involution `hvanish` bridge: `evensNormH2 … = 0 ⟹ H2ofFun (evensNormFun
  U s α) = 0`. std-3 (B9/B11a enter when `lemma_6_16` supplies the `evensNormH2 = 0`).
- **`H2ofFun_eq_zero_of_H2mk`** — shared tail (`H2mk = 0 ⟹ H2ofFun = 0`).
- **`deepPart_mapCoeff1`** (§DeepTransport) — deepness transports along any continuous equivariant
  `f : W₁ →+ W₂`: `x ∈ deepPart ρ ⟹ mapCoeff1 f x ∈ deepPart ρ` (via `ShapiroExtend.phiRes_mapCoeff1`
  + `mem_deepPart_iff`). **Carries `x ∈ deepPart ρ` to `ι∗x ∈ deepPart ρ` at the SAME `ρ`** (no
  acting-group bridge needed if you keep the reducer at `C`; see §5-f2d).
- **`FactorSet.reindexHom`** (§Reindex) — reindex a datum's acting group along `φ : C' → C`
  (`f` unchanged, `m` pre-composes `φ`).
- **`graphPullback_reindexHom`** — `graphPullback (dat.reindexHom φ) ρ' b = graphPullback dat (φ∘ρ') b`
  when `∀ c' v, c' • v = φ c' • v` (the `C'`-action is the `φ`-pullback). **The C ↔ `G⧸N` linchpin.**
- **`Q0loc_reindexHom`** (§ReindexQ0loc) — same lifted to `Q0loc`:
  `Q0loc (dat.reindexHom φ) ρ' x = Q0loc dat (φ.comp ρ') x`.

`FactorSet.reindexHom` is declared `_root_.GQ2.FactorSet.reindexHom` (dot-notation on `FactorSet`).

---

## 5. What is OPEN — per ticket, with interface + gotchas

### P-15f2a — DI-core (datum-independence)

**Interface (banked, parametric)**: `OrbitVanish.Q0loc_datum_indep_of_core` (`:414`):
```
(hcore : graphPullback (diffDatum dat1 dat2) ρ (out x) ∈ B2 AbsGalQ2 (ZMod 2))
⊢ Q0loc D dat1 ρ x = Q0loc D dat2 ρ x
```
The task is to **discharge `hcore`** for two equivariant factor sets of the same `q` (unconditional
datum-independence). `diffDatum` is an equivariant factor set for the **zero form**
(`isEquivariantFactorSet_diffDatum`, banked). Increment A is banked: `exists_refinement_of_zero_form`
(`:438`) gives a quadratic refinement `Δφ` with polar `Δdat.f`. **Increment B (open)**: correct `Δφ`
against the `C`-equivariance defect `Δm` — the genuine `H¹(C, V∨)` obstruction — to build the
coboundary `Λ(g) = Δφ(b g)`. See `docs/p15f2-option1-scoping.md`. **Cross-lane** (not f2c).

### P-15f2c1 — the Shapiro H¹ coordinate read (`hcoh`), the keystone

**Deliverable**: for each orbit `o`, produce
`hcoh o : H2ofFun AbsGalQ2 (graphPullback (orbitDatum o … reindexed) ρ (out (ι∗x)))
= H2ofFun (cor2Fun (U o) (inner o))`, matching `lemma_6_15_{square,free,involution}`.

**The chain per orbit** (square shown):
1. `orbitDatum (Sum.inl j) = squareBlockDatum N j = (squareOrbitDatum N).comap (blockProj N j)`
   (definitional). So `graphPullback (squareBlockDatum N j) (mk'N) b
   = graphPullback (squareOrbitDatum N) (mk'N) (blockProj N j ∘ b)` — need `graphPullback_comap`
   functoriality (check `KappaNormalForm.datum_comap` / add a `graphPullback_comap` if absent).
2. **THE CORE (not banked)**: `blockProj N j ∘ (out (ι∗x))` is cohomologous to `shapiroFun N α_j`
   for a **scalar** `α_j : Z1 N (ZMod 2)`. This is Shapiro's H¹ iso `H¹(G, Coind_N 𝔽₂) ≅ H¹(N, 𝔽₂)`:
   define `α_j := (n ↦ (block-j of out(ι∗x))(n)(base coset))` restricted to `N`, then exhibit the
   explicit coboundary `b − shapiroFun N α_j = δ¹Λ` (transversal-based Λ, mirroring the `invLift`/
   `invLambda` constructions already in `ShapiroLedger.lean`). `graphPullback` respects the
   coboundary via `DeepPart.graphPullback_add_sub_mem_B2` (`:823`) + `H2ofFun_eq_of_sub_mem_B2`.
3. Then `lemma_6_15_square N hNo α_j` fires. The `mk'N` acting map in `lemma_6_15` is bridged to the
   reducer's `ρ` by `graphPullback_reindexHom` (with `φ = e`, `e∘ρ = mk'N`; landed).
4. **`α_j` IS the deep coordinate**: `H1mk N α_j = phiRes ρ (ι∗x) φ_j` for the block-`j` coordinate
   functional `φ_j : W →+ 𝔽₂` — this identification is what makes f2c1 also feed `hvanish` (see f2c2
   / cores). So f2c1 should return `(α_j, hcoh o, H1mk α_j = phiRes ρ (ι∗x) φ_j)`.

**Why it's the keystone**: all three orbits' `hcoh` route through the same Shapiro read (step 2).
**Gotcha**: `lemma_6_11`'s `ι` (`RegularSummand.lean:2050`) gives only the coinduced *module*
structure (`ι(h•v) n x = ι v n (h⁻¹x)`), NOT `shapiroFun`-shaped *cocycles* — step 2 genuinely needs
the cohomology-level iso, built from scratch. Repo has `shapiroFun` (`Corestriction.lean:71`) +
forward props only; no H¹-level Shapiro machinery. May split (general iso vs. per-orbit
instantiation) if large. **Ax: ∅ (std-3).** Touches shared `Corestriction`/`ShapiroLedger` — coordinate.

### P-15f2c2 — the involution deep-unit Kummer presentation (`hvanish`)

**Deliverable**: the involution `hvanish o : H2ofFun ↥(U₀) (inner o) = 0`, where `inner o =
evensNormFun (N.subgroupOf U₀) ĝ α` (from `lemma_6_15_involution`). Route: build the concrete Kummer
field data `lemma_6_16` consumes, apply it (gives `evensNormH2 … = 0`), then `hvanish_evensNorm`
(landed) closes.

**The field data** (from `deepPart ρ`'s deep-unit witness at the involution block coordinate, via
`mem_deepPart_iff` + `deepClass_eq_kummerClassK`): `k ≤ L` (index-2, `L = K(√A_j)`), a Kummer
generator `(d : kˣ, δ, hδ : δ² = d, hδL : δ ∈ L, hLδ : fixingSubgroup relation)`, and coordinates
`(u : kˣ, v : k, hAuv : A = u + vδ)` for the deep unit `A ∈ L`. This is standard char-≠2 Kummer
theory ("write `L = k(√d)`, `A = u + v√d`"). **Self-contained**, no Shapiro dependency.

**mathlib support** (searched): `IntermediateField.adjoin.powerBasis`,
`IntermediateField.powerBasisAux` (degree-2 power basis for `A = u + vδ`),
`Algebra.IsQuadraticExtension.finrank_eq_two`. **Gap**: the √-adjoin generator (complete-the-square:
degree-2 minpoly `X² − aX + b` → `δ = δ₀ − a/2`, `δ² = a²/4 − b ∈ k`) is **not** a mathlib lemma —
build it. **Bridges needed**: `AbsGalQ2 = Kummer.GaloisGroup ℚ_[2]` and `ker ρ = k.fixingSubgroup`
(the `DeepDualityK.kerToFixing` / `hker` pointwise-membership pattern — see `GQ2/DeepDualityK.lean`).
**Ax: ∅ construction** (enables B9/B11a via `lemma_6_16`).

### P-15f2d — final assembly + SectionSix splice (thin)

Compose the C-level chain (recommended — avoids a `deepPart`-at-`mk'N` bridge):
```lean
-- e : C ≃* AbsGalQ2 ⧸ ker ρ  from  ρ surjective (hc + hfac + B.tameF onto);
--   e := (QuotientGroup.quotientKerEquivOfSurjective ρ hρsurj).symm ;  e ∘ ρ = mk' (ker ρ).
-- letI : DistribMulAction C W := e-pullback of the canonical G⧸N action on W = Fin K → RegRep N.
-- datW_C := (sumDatum (orbitIndexSet N (q∘r)) (orbitDatum N)).reindexHom e : FactorSet C W
obtain ⟨K, ι, r, hEqfs, hIso, hιe, hri⟩ := regular_isometric_embedding_orbit e cT hgen q hq hinv …
-- 1. datum-independence (f2a): dat  ~  datW_C.comap ι   (both equiv for q, via isometry q∘r∘ι = q)
-- 2. lemma_6_14 : Q0loc (datW_C.comap ι) ρ x = Q0loc datW_C ρ (ι∗x)
-- 3. Q0loc_vanish_of_datum_decomp at (C, ρ, W, dat := datW_C):
--      hdat_eq  via  reindexHom_sumDatum  (reindexHom distributes over sumDatum — small OPEN brick)
--      hdatf    via  isEquivariantFactorSet_reindexHom  (small OPEN brick) + isEqFS_orbitDatum
--      hcoh o   via  f2c1  (graphPullback_reindexHom turns e∘ρ into mk'N, then lemma_6_15_*)
--      hvanish  via  hvanish_cup (sq/free) + f2c2⇒hvanish_evensNorm (inv);
--               block deepness from  deepPart_mapCoeff1 ρ  (ι∗x ∈ deepPart ρ)  +  mem_deepPart_iff
```
**Remaining f2d wiring bricks** (small, mechanical — none open mathematics):
- `reindexHom_sumDatum` : `(sumDatum s d).reindexHom φ = sumDatum s (fun o => (d o).reindexHom φ)`.
- `isEquivariantFactorSet_reindexHom` : equivariance preserved under `reindexHom` + `φ`-pullback action.
- the e-pullback `DistribMulAction C W` instance (+ `hφ : c • w = e c • w`) and
  `e.comp ρ = mk' (ker ρ)` as `ContinuousMonoidHom`s.
- `datW_C.comap ι` equivariant for `q` (via `datum_comap` + isometry `q∘r∘ι = q`).
- **SectionSix splice**: `lemma_6_17_vanish` statement is co-owned/frozen; exit via the §6.18ram
  statement-move (statement upstream, proof downstream) — coordinate with P-15f1/f8; the machinery
  lives in `DeepPart`/`LocalKummer`, so move the statement out of SectionSix or reroute the
  `prop_6_18_ramified` citation.

---

## 6. Gotchas discovered

- **The `hvanish` reducer takes no `deepPart` hyp** — deepness threads only through `hvanish`. Get
  `ι∗x ∈ deepPart ρ` from `deepPart_mapCoeff1` at the **actual `ρ`** (C-level), then `mem_deepPart_iff`
  gives each block coordinate deep. Keeping the reducer at `C` (not `G⧸N`) avoids a
  `deepPart ρ = deepPart (mk' (ker ρ))` bridge (they're equal as predicates but the `H1 ↥ker`-type
  subgroup — `ρ.ker` vs `(mk' N).ker` — is not defeq; `QuotientGroup.ker_mk'` is a `theorem`).
- **`lemma_6_15` acts via `mk' N`, the reducer via `ρ`** — bridged by `graphPullback_reindexHom`
  with `φ = e`, `e ∘ ρ = mk' N`. This is exactly why the reindex bricks exist.
- **`lemma_6_11`'s `ι` is only a coinduced *module* map**, not `shapiroFun`-shaped on cocycles —
  f2c1's step 2 is unavoidable (Shapiro's H¹ iso, not banked).
- **`FactorSet C V` needs `[Group C]`** (from `OrbitData.lean:28`'s section vars), so `reindexHom`'s
  target group must be a `Group`.
- **Instance diamond on `W`**: `W = Fin K → RegRep N` carries the canonical `G⧸N` action; the C-view
  is a `letI` e-pullback. Beat rw-mismatches by stating bricks pointwise / defeq-filling (the
  `ShapiroExtend`-`RegMod`-synonym idiom in `docs/p15f-handoff.md §5` is the reference pattern if the
  global trivial `DistribMulAction AbsGalQ2 (ZMod 2)` interferes).
- **`ρ` is surjective** (needed for `e`): `ρ = c ∘ B.tameF`, `hc : Surjective c`, and `B.tameF` onto
  `Ttame` (check `BoundaryMaps`; `SectionThree.gen_ttame_quotient` is the generation input). The
  §6.3 `hc` amendment travels with the frozen signatures (flag for P-20).

---

## 7. File map

| File | Role |
|---|---|
| `GQ2/SectionSix.lean` | `lemma_6_17_vanish` (`:882`), `lemma_6_15_*` (`:664/690/706`), `lemma_6_16` (`:752`), `Q0loc` (`:145`), `deepPart` (`:836`), `IsDeepUnit` (`:734`) |
| `GQ2/OrbitVanish.lean` | `Q0loc_vanish_of_datum_decomp` (`:294`), `Q0loc_datum_indep_of_core` (`:414`), `sumDatum` (`:253`), `diffDatum`/`exists_refinement_of_zero_form` (f2a substrate) |
| `GQ2/OrbitDecomp.lean` | f2b decomposition: `orbitDatum` (`:779`), `isEquivariantFactorSet_orbitSumDatum` (`:1036`), `orbitIndexSet`/`isEqFS_orbitDatum`, `blockProj` (`:324`) |
| `GQ2/RegularIsometry.lean` | f2b embedding: `regular_isometric_embedding_orbit` (`:165`), `regular_isometric_embedding` (`:63`), `reBlock`/`reSummand` reindex |
| `GQ2/RepIndependence.lean` | Lemma 6.14 `lemma_6_14` (`:157`) |
| `GQ2/ShapiroDeepness.lean` | **the landed f2d infra + hvanish cores** (this session) |
| `GQ2/OrbitData.lean` | `FactorSet` (`:34`), `graphPullback` (`:72`), `kappa0`, `FactorSet.comap` (`:78`), `RegRep`/`*OrbitDatum` |
| `GQ2/LocalKummer.lean` | `mem_deepPart_iff` (`:305`), `deepClasses` (`:295`), `cup_deepClasses` (`:374`), `deepClass_eq_kummerClassK` (`:335`), `phiRes` (`:216`) |
| `GQ2/AdmissibleCount.lean` | `conjAct_deepClasses` (`:128`), `kcf_conj` (`:85`) |
| `GQ2/ShapiroExtend.lean` | `phiRes_mapCoeff1` (`:244`), `mapCoeff1_H1mk` (`:235`) |
| `GQ2/Corestriction.lean` | `shapiroFun` (`:71`), `cor2Fun` (`:81`), `cor1Fun` (`:76`) — f2c1's Shapiro primitives |
| `GQ2/EvensKahn.lean` | `evensNormFun` (`:281`) — involution inner cochain |
| `GQ2/DeepPart.lean` | `graphPullback_add_sub_mem_B2` (`:823`), consumer `prop_6_18_ramified` (`:1448`) |
| `GQ2/DeepDualityK.lean` | `kerToFixing`/`hker` pattern (f2c2's `ker ρ = k.fixingSubgroup` bridge) |
| `docs/p15f2c-design.md` | the ⟨2026-07-07⟩ design record (f2c1/f2c2 detail) |
| `docs/p15f2-option1-scoping.md` | f2a DI-core scoping |
| `docs/p15f2b-foundation-notes.md` | f2b scoping |

---

## 8. Suggested work order

1. **f2c1** (keystone) and **f2c2** (self-contained) in parallel — they share no dependency.
   f2c1 is the biggest risk (Shapiro's H¹ iso from scratch); scope it first, split if large.
2. **f2a** (DI-core increment B) — cross-lane, independent; can run concurrently.
3. **f2d** — once f2a + f2c1 + f2c2 land: build the small wiring bricks (§5-f2d), compose, and do
   the SectionSix statement-move splice (coordinate with P-15f1/f8). ~100–200 ln.

The critical path is `max(f2a, f2c1, f2c2)` then f2d. The f2d infra being pre-landed means the
capstone is genuinely thin.
