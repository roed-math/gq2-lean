# P-15f2c2c handoff — the analytic `hunram` (unramified ⟹ equal value groups)

**Purpose.**  Everything a fresh session needs to work any of **P-15f2c2c1–c2c4** (the c2c
split).  Self-contained: does not rely on chat history or session task state.  Written
2026-07-08 (Fable).  All line numbers are approximate — grep the named declaration.
Companion docs: `docs/p15f2c2c-scoping.md` (the design of record — read §half-(B) first),
`docs/p15f2c-design.md` (the c2 lane), `docs/p15f2-handoff.md` (the f2 lane).

---

## 0. TL;DR

* **Deliverable**: discharge the analytic **`hunram`** hypothesis — equal norm value groups
  `‖L^×‖ = ‖k^×‖` for the involution tower — which c2b threads into
  `ShapiroDeepness.hvanish_involution` / `hvanish_involution_of_deepClass` and
  `SectionSix.lemma_6_16` / `HilbertLedger.cup_unramified_unit` consume.  It has been an
  **unproved hypothesis threaded through the entire §6.3 Kummer ledger**; c2c is the ticket
  that finally produces it.
* **DONE — half (A)** (commit `6e0ea24`, std-3, sorry-free, `lake build` green 8650):
  `GQ2/UnramifiedNorm.lean` — `norm_eq_zpow` (B13 discreteness ⟹ every nonzero field norm is
  a `π`-power), **`hunram_of_uniformizer_norm_eq`** (`‖π_L‖ = ‖π_k‖ ⟹ hunram`, in
  `lemma_6_16`'s verbatim shape), `uniformizer_norm_eq_of_e_eq` + `hunram_of_e_eq` (the
  `e_L = e_k` entry point).  Registered in `GQ2.lean`.
* **REMAINING — half (B)**: `‖π_L‖ = ‖π_k‖` from the tame datum.  **USER DECISION
  (2026-07-08): NO new axiom** — derive from the existing budget.  The derivation is pinned
  (§2) and **split for orchestration** (commit `d1a5540`) into
  **c2c1 (coset-norm kit) ∥ c2c2 (CFT index) ∥ c2c3 (`nuT`-factoring) → c2c4 (assembly)** —
  the first three are mutually independent and startable now, each in its own NEW file.
* **The keystone discovery**: B5's `norm_reciprocity` (`GQ2/Reciprocity.lean:216`) is the
  **full finite-level norm-group correspondence** — for every finite *abelian* Galois
  `F/ℚ₂`, `ℚ₂ˣ → Gal(F/ℚ₂)` (= `restrictAb F hab ∘ recip`) is surjective with kernel exactly
  `normSubgroup F = (Units.map (Algebra.norm ℚ₂)).range`.  This is what makes the ramified
  case refutable without new axioms.
* Final axiom trace of the assembled `hunram`: **std-3 + {B5, B10′, B13}** (all existing;
  census unchanged).  Two coordination flags live on the c2c4 row (§5).

---

## 1. The two `hunram`s (do not conflate)

| form | statement | where |
|---|---|---|
| group-level | `c tameTau = 1` | `prop_6_9_unramified`, `SectionSix.lean:306` |
| **analytic (c2c)** | `∀ x : ℚ̄₂, x ≠ 0 → x ∈ L → ∃ y, y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖` | `lemma_6_16` (`SectionSix.lean:755`), `hvanish_involution` (`ShapiroDeepness.lean:187`) |

The repo has **no valuation ring / residue field / ramification theory** (B13's deliberate
convention) and **`inertia` is nowhere defined** — the only Galois↔norm bridges are
`norm_galois` (`HilbertLedger.lean:312`), the B5/B10′ clauses, and the f8 `ResidueLift`
toolkit.  The related-but-distinct `IsResidueTrivial` lives at `DeepDuality.lean:1165`;
`IsUnramifiedQuadraticSpectral` (a `def`, asserts nothing) at `Foundations/Axioms.lean:480`.

Setting (fixed by c2b, `docs/p15f2c-design.md`): `L = fixedField (ker ρ)` — use
`ResidueLift.splitField` (`ResidueLift.lean:284`, with `fixingSubgroup_splitField:289`,
`splitField_finiteDimensional:294`) — `k = fixedField U₀`, `Gal(L/k) = ⟨ĝ⟩` order 2 (c2b's
`hindex`/`s`/`hs`); `ρ = c ∘ B.tameF` (**`hfac`**, frozen `lemma_6_17_vanish` signature,
`SectionSix.lean:882–885`); `C = ⟨s₀, t⟩` with `s₀ := c tameSigma`, `t := c tameTau`,
`s₀⁻¹ t s₀ = t²` (`tame_relation`, `TameQuotient.lean:49`), `r := ord t` **odd**
(`Tame.tame_odd_order`, `Tame.lean:42`).

## 2. The half-(B) derivation (design of record — scoping doc §half-(B))

1. **`m := e_{L/k} ∣ 2`** *(axiom-free)*: for `x ∈ L^×`, `x·(ĝ•x) ∈ k` — fixed by
   `k.fixingSubgroup` since `L.fixingSubgroup` is **index-2 hence normal** in it and `ĝ²` falls
   back in; membership via `fixedField_fixingSubgroup` — and `‖x·ĝx‖ = ‖x‖²` (`norm_galois`).
   So `‖x‖² ∈ ‖k^×‖`; at `x = π_L`, zpow-injectivity gives `m ∣ 2`.
2. **`e_L = e(L/F₀)·e_{F₀}`, `e(L/F₀) ∣ r`** *(axiom-free)*: `F₀ := L^{⟨t⟩}` and the
   `⟨t⟩`-coset norm `∏_{γ ∈ ⟨t⟩} γ•x ∈ F₀` with `‖·‖ = ‖x‖^r`.
3. **`e_{F₀} = [U : U∩N(F₀ˣ)] = #(unit-image in Gal(F₀/ℚ₂))`** *(B5(a))*: `Gal(F₀/ℚ₂)` is a
   quotient of the **cyclic** `C/⟨t⟩`, hence abelian ⟹ `norm_reciprocity` applies;
   `[ℚ₂ˣ:N] = #Gal = finrank`; `v₂(N(F₀ˣ)) = (n₀/e₀)ℤ` via `Algebra.norm_eq_prod_automorphisms`
   + `norm_galois` (lift automorphisms along `AlgEquiv.restrictNormalHom_surjective`) +
   `norm_eq_zpow`; factor the index through `v₂ : ℚ₂ˣ ↠ ℤ`.
4. **The unit-image is odd** *(B10′)*: the composite `AbsGalQ2 → Gal(F₀/ℚ₂) ↠ (2-part Q)`
   kills `ker B.tameF` and `τ` (`hfac`), i.e. is `φ ∘ B.tameF` with `φ : Ttame → Q` continuous,
   `φ(tameTau) = 1`.  **Factoring lemma (c2c3)**: such `φ` factors through
   `nuT : Ttame → Ztwo` (`BoundaryFrame.lean:187`; `nuT_tameSigma = ztwoOne:194`,
   `nuT_tameTau = 1:199`).  Then B10′'s `nuT_recip_unit` (`TameQuotient.lean:94`) kills the
   unit-image in `Q`.  ⚠ subtle point: `ker nuT ⊋ closure⟨τ⟩` (`nuT` targets the **2-part**
   `Ztwo`, so the odd σ-directions also die) — this is exactly why the factoring lemma is
   through-`nuT`, NOT "units land in the τ-closure" (which is unavailable and false to hope
   for).  The 2-group target absorbs the odd directions.
5. **Assembly**: `e_L = e(L/F₀)·e₀ ∣ r·e₀` odd; `e_L = m·e_k`; `m ∣ 2` ⟹ `m = 1` ⟹
   `‖π_L‖ = ‖π_k‖` ⟹ half (A)'s `hunram_of_uniformizer_norm_eq`. ∎

## 3. The subtickets (board rows P-15f2c2c1–c2c4, commit `d1a5540`)

Each gets a **NEW file** — write-disjoint from each other and from the live f2 agents
(`ShapiroRead/QuadraticAdjoin/ShapiroDeepness/VanishClose` are taken).

### c2c1 — `GQ2/GaloisCosetNorm.lean` [O, axiom-free, startable now]
`cosetNorm H K x := ∏_{c : K ⧸ H.subgroupOf K} ((Quotient.out c : ↥K) : _) • x` for
`H ≤ K ≤ Kummer.GaloisGroup ℚ_[2]`, `Finite (K ⧸ H.subgroupOf K)`:
(i) each factor well-defined for `x ∈ fixedField H` (`g•x` depends only on `gH`);
(ii) `∈ fixedField K` (left mult permutes cosets; commutative reordering of the finite
product — `Finset.prod_bij`/`Equiv.prod_comp` idiom); (iii) `‖·‖ = ‖x‖ ^ Nat.card (K ⧸ …)`
(`norm_galois` factorwise).  Then the relative-`e` kit over B13-data-as-hypotheses (half-A
idiom): `relE` extraction (unique `m ≥ 1` with `‖π_F‖ = ‖π_L‖^m`, from `norm_eq_zpow` +
`‖π‖ ∈ (0,1)` zpow-injectivity), tower multiplicativity (`e_L = relE·e_F` from
`‖2‖ = ‖π‖^e` both sides), and **`relE ∣ n` whenever `∀ x ∈ L^×, ‖x‖^n ∈ ‖F^×‖`**.
c2c4 instantiates twice: (c2b's `hindex`-pair ⟹ `m ∣ 2`) and (the `⟨t⟩`-preimage pair ⟹
`e(L/F₀) ∣ r`).

### c2c2 — `GQ2/UnitNormIndex.lean` [F+O, std-3 + B5, startable now, ρ-FREE]
For `F : IntermediateField ℚ_[2] ℚ̄₂`, `[FiniteDimensional]`, `[IsGalois ℚ_[2] F]`,
`hab : ∀ σ τ : F ≃ₐ[ℚ_[2]] F, σ*τ = τ*σ`, `FF : DyadicUnitFiltration F`:
**`Nat.card ((restrictAb F hab ∘ localReciprocity.recip)-image of unitEmbed-units) = FF.e`.**
Pins: `normSubgroup` (`Reciprocity.lean:134`), `restrictAb:167`, `unitEmbed:183`, `v2:128`,
`toAb:92`.  Steps: `[ℚ₂ˣ:N] = #Gal` (`Subgroup.index_ker` + surjectivity + range = ⊤);
`#Gal = finrank` (`IsGalois.card_aut_eq_finrank`); `n/e ∈ ℤ` (full-Galois coset norm or
directly `‖Norm π_F‖ = ‖π_F‖^n = ‖2‖^{n/e}` uniqueness); `v₂(N(Fˣ)) = (n/e)ℤ` (⊇ at `π_F`);
`U := ker v₂ = unitEmbed.range` (a `v₂ = 0` element has `‖·‖ = 1` and `PadicInt` is literally
`{x // ‖x‖ ≤ 1}`); the SES index factorization `[ℚ₂ˣ:N] = [ℤ : v₂(N)]·[U : U∩N]` (2nd iso +
index multiplicativity — hand-roll ~30 ln if `Subgroup.relindex` calculus resists);
`[U : U∩N] = #(unit-image)` (B5(a) kernel + 1st iso on `U`).
⚠ risk = mathlib `Units.map`/index API wrangling; the mathematics is pinned.

### c2c3 — `GQ2/TameTwoQuotient.lean` [F] — ☑ **CLOSED 2026-07-08**

**(i)+(ii)+(iii-def)** landed `b43be7a` (std-3 exactly; (ii) via the kernel-inclusion route
`ker_nuT_le_proPKernel` — `maxProPMk = ρ'∘nuT` by the `Zhat`-power hom + `monoidHom_eq_of_topGen`,
no `T₂ ≅ Ztwo` iso; consumer shape `map_eq_one_of_nuT_eq_one_finite`).  **(iii) witness
discharge** landed in the NEW leaf `GQ2/TameOrientationWitness.lean` (registered):
`tameUnitOrientation_tameFHom` (std-3 + {B5, B10′} exactly — the §7 predicted trace) and
`tameUnitOrientation_witness` (`B := boundaryMapsWitness` shape; + the witness's B3c/B8).
Leaf placement: keeps `TameTwoQuotient` light for c2c4 and dodges the
`maxProPMk_tameTau`/`ker_nuT_le_proPKernel` name collision between the `GQ2` and
`GQ2.SectionThree` scopes.  Original spec follows for reference.
(i) *τ-death*: any `φ : Ttame →* Q`, `Q` finite 2-group ⟹ `φ tameTau = 1`
(`tame_odd_order` on the pushed `tame_relation`: `orderOf (φ tameSigma) ≠ 0` in finite `Q`;
odd ∧ 2-power order ⟹ trivial).  **Pure finite group theory, no topology.**
(ii) *the factoring*: continuous `φ : Ttame → Q` (finite discrete 2-group) factors through
`nuT`.  Route of record: `T₂ := maxProPQuotient 2 Ttame`; T-05 `proPKernel_le_ker` factors
`φ` through `T₂`; identify `T₂ ≅ Ztwo` compatibly with `nuT` — `nuT` descends to
`T₂ → Ztwo` (`Ztwo` pro-2); the inverse `Ztwo → T₂` from the `Zhat` generator-classifier
(cf. `nuT`'s own construction via `presentationLift` + `maxProPMk`, `BoundaryFrame.lean:187`)
killing the pro-2 kernel; roundtrips = id on the topological generator
(`monoidHom_eq_of_topGen` pattern, `BoundaryMapsWitness.lean:190`-adjacent).
FALLBACK: the direct procyclic-closure argument — the image of `(nuT, φ) : Ttame → Ztwo × Q`
is the closure of one generator, and a procyclic subgroup of `ℤ₂ × Q` surjecting onto `ℤ₂`
meets `1 × Q` trivially (the `Q`-coordinate is determined by the `ℤ₂`-coordinate mod `2^c`).
(iii) `def TameUnitOrientation (R : LocalReciprocity)
(tameF : ContinuousMonoidHom AbsGalQ2 Ttame) : Prop := ∀ (u : ℤ_[2]ˣ) (g : AbsGalQ2),
toAb g = R.recip (unitEmbed u) → nuT (tameF g) = 1` — the B10′ clause shape
(`TameQuotient.lean:92–96`) — **+ the witness discharge**: `boundaryMapsWitness.tameF`
satisfies it (unpack the witness's `tameF` against `tameQuotient.nuT_recip_unit`; read
`GQ2/BoundaryMapsWitness.lean`'s construction — the witness is built from the axiom bundle,
so the clause should transfer nearly verbatim).
⚠ (ii) is the one genuinely new profinite plumbing in the whole plan — budget accordingly.

### c2c4 — `GQ2/UnramifiedBridge.lean` [F+O, capstone, gated on c2c1–c2c3]
Tower setup: `⟨t⟩ ◁ C` (conj-by-`s₀` maps `⟨t⟩` into itself via the relation; finite ⟹ onto),
`C/⟨t⟩` cyclic (`hc : Surjective c` ⟹ `C = ⟨s₀, t⟩`: images of a topological generating set
of `Ttame` generate the finite discrete `C`); `F₀ := fixedField (kerGal-style preimage of
⟨t⟩)` (mirror `ResidueLift.kerGal:252`/`splitField:284` — the `toAbs` two-views bridge
`:248` handles the `AbsGalQ2` vs `Kummer.GaloisGroup` instance split); `IsGalois ℚ_[2] F₀`
(the fixing subgroup is normal — if mathlib's InfiniteGalois lacks the
normal-closed-subgroup ⟹ `IsGalois`-fixedField instance, this is the main plumbing risk —
scout `DimAssembly`/`DimClose`/f8 for a precedent); `Gal(F₀/ℚ₂)` abelian
(`AlgEquiv.restrictNormalHom` is surjective and kills the fixing subgroup ⟹ `Gal(F₀/ℚ₂)` is
a quotient of the cyclic `C/⟨t⟩` — this also supplies c2c2's `hab`).  Unit-image odd: the
2-part quotient `Gal(F₀/ℚ₂) ↠ Q` pulled back to `AbsGalQ2` factors as `φ ∘ B.tameF`
(`hfac`), `φ(tameTau) = 1` (τ ↦ t ∈ ⟨t⟩ dies) ⟹ c2c3(ii)+(iii) kill the unit-image in `Q`
⟹ image ⊆ odd part ⟹ **c2c2 gives `e_{F₀}` odd**.  Then the `e`-chain (c2c1, §2 steps
1–2–5) ⟹ `m = 1` ⟹ half (A) ⟹ **`hunram` verbatim in `hvanish_involution`'s shape**
(`ShapiroDeepness.lean:187–188`: `∀ x : AlgebraicClosure ℚ_[2], x ≠ 0 → x ∈ L → ∃ y, y ≠ 0 ∧
y ∈ k ∧ ‖x‖ = ‖y‖`).  Consumes: c2b's `(k, L, hkL, hindex, s, hs)` + frozen-signature
`(ρ, c, hc, B, hfac)` + `TameUnitOrientation localReciprocity B.tameF` + c2b's
`L.fixingSubgroup = kerGal ρ` identification.  **Build the sorried skeleton early** against
c2c1–c2c3's pinned signatures (e-lane idiom) — it validates the c2b interface before the
lanes land.

## 4. Interface pin table (verified 2026-07-08)

| need | pinned name | where |
|---|---|---|
| target `hunram` shape | hypothesis of `hvanish_involution` / `_of_deepClass` | `ShapiroDeepness.lean:187, 228` |
| downstream consumers | `lemma_6_16` (`:755`), `cup_unramified_unit` (`:293`) | `SectionSix.lean`, `HilbertLedger.lean` |
| **B5(a) norm-group correspondence** | `LocalReciprocity.norm_reciprocity` | `Reciprocity.lean:216–220` |
| B5 helpers | `normSubgroup:134`, `restrictHom:144`, `restrictAb:167`, `unitEmbed:183`, `uniformizer:190`, `v2:128`, `toAb:92` | `Reciprocity.lean` |
| B10′ orientation | `OrientedTameQuotient.nuT_recip_unit` | `TameQuotient.lean:92–96`; axiom `tameQuotient`, `Foundations/Axioms.lean:437` |
| `nuT` + generator values | `nuT:187`, `nuT_tameSigma:194`, `nuT_tameTau:199` | `BoundaryFrame.lean` |
| `B.tameF` clauses | `tameF:402`, `tameF_surjective:407`, `wild_isProP:409`, `wild_isMax:412`, `compatF:406` | `BoundaryFrame.lean` (structure `BoundaryMaps:383`) |
| frozen 6.17 data (`ρ = c ∘ B.tameF` etc.) | `lemma_6_17_vanish` hypotheses | `SectionSix.lean:882–893` |
| tame relation / odd inertia order | `tame_relation` (`TameQuotient.lean:49`), `Tame.tame_odd_order` (`Tame.lean:42`) | — |
| splitting-field plumbing | `toAbs:248`, `kerGal:252`, `splitField:284`, `fixingSubgroup_splitField:289`, `splitField_finiteDimensional:294`, `hker_splitField:300` | `ResidueLift.lean` |
| B13 bundle + fields | `DyadicUnitFiltration` (`UnitFiltration.lean:153`; `π`/`hπ_mem`/`hπ_ne`/`hπ_lt`/`hπ_max`/`e`/`he_pos`/`he`/`f`/…); axiom `dyadicUnitFiltration`, `Axioms.lean:599` | — |
| half (A) outputs | `norm_eq_zpow:41`, `hunram_of_uniformizer_norm_eq:64`, `uniformizer_norm_eq_of_e_eq:77`, `hunram_of_e_eq:86` | `UnramifiedNorm.lean` |
| value-group atoms | `exists_nat_val` (`DeepCount.lean:791`), `norm_step_down` (`:152`) | — |
| Galois norm-invariance | `norm_galois` | `HilbertLedger.lean:312` |
| Teichmüller/Hensel kit (if needed) | `exists_nthRoot_near:46`, `exists_rootOfUnity_near:90`, `galois_smul_smul_comm_of_rootOfUnity:141` | `ResidueLift.lean` |
| mathlib | `Algebra.norm_eq_prod_automorphisms`, `AlgEquiv.restrictNormalHom_surjective`, `IsGalois.card_aut_eq_finrank`, `Subgroup.index_ker`, `pow_left_inj₀` | — |

## 5. Coordination flags (live on the c2c4 board row)

1. **Orientation-hypothesis amendment**: B10′'s clause is about the *axiom bundle's* tame
   coordinate; an arbitrary `B : BoundaryMaps` carries no reciprocity clause (`wild_isMax`
   pins only the kernel).  So the moved `lemma_6_17_vanish` gains ONE hypothesis
   (`TameUnitOrientation localReciprocity B.tameF`), discharged at `boundaryMapsWitness` —
   same pattern as the `hc`/`hV2` amendments (flag for P-20; cross-flag the c2b/f2d owner).
2. **Docstring budget deviation**: `lemma_6_17_vanish`'s docstring predicts "Ax: B6, B7′,
   B9"; the trace will gain B5/B10′/B13 (existing axioms — census unchanged).  P-20 note.

## 6. Gotchas & incidents (learned this session)

* **Shared tree, whole-file board rewrites**: an uncommitted `docs/tickets.md` row was
  clobbered by a concurrent board rewrite, and a concurrent commit swept the
  `import GQ2.UnramifiedNorm` line into `GQ2.lean` *before the file itself was committed*
  (HEAD transiently unbuildable from fresh checkout).  **Commit each green increment
  immediately; stage ONLY your files; print the staged set before committing.**
* Name traps hit in half (A): `le_or_lt` doesn't exist at the needed generality — use
  `le_or_gt`; the nonneg-real pow-injectivity is **`pow_left_inj₀`** (needs `n ≠ 0`, supply
  `Nat.one_le_iff_ne_zero.mp FF.he_pos`).  Line-width lint: count **codepoints**, not bytes
  (`‖`, `π`, `ℚ̄₂` inflate bytes; the 100-char rule is codepoints).
* `Kummer.GaloisGroup ℚ_[2]` vs `AbsGalQ2` are the same type with different registered
  `Group` instances — closure proofs cross by `exact`/term-mode only (the
  `ResidueLift.toAbs` device; same instance-split family as GA/GammaA).
* The filtration-as-hypothesis idiom (half A): state lemmas over
  `(F : DyadicUnitFiltration k)` arguments so statements stay axiom-free; B13 enters only at
  call sites via `dyadicUnitFiltration k`.
* `‖(y : ℚ̄₂)‖` for `y : ℚ₂`: bridge via `norm_algebraMap'` (pattern at `DeepCount.lean:118`).

## 7. Verify / gate

```
lake build GQ2.GaloisCosetNorm    # (resp. UnitNormIndex / TameTwoQuotient / UnramifiedBridge)
lake build GQ2                    # full tree before commit if you touched GQ2.lean
```
Then `lean_verify` / `#print axioms` on each new declaration.  Expected traces —
c2c1: **std-3 exactly**; c2c2: std-3 + `localReciprocity`; c2c3(i)(ii): std-3,
(iii): std-3 + `tameQuotient` (+ `localReciprocity` via the bundle parameter);
c2c4: std-3 + {`localReciprocity`, `tameQuotient`, `dyadicUnitFiltration`}.
**Any other axiom or `sorryAx` in a final artifact is a red flag** — in particular nothing
here may touch B6/B7 (those belong to other lanes) and **no new `axiom` may be added**
(user decision of record).  Register each new file in `GQ2.lean` in the same commit that
creates it.  New files are not on any `SORRY_ALLOWLIST` — keep them sorry-free at commit
time (c2c4's early skeleton stays uncommitted, or coordinate an allowlist entry if it must
land sorried).

## 8. Pointers

* Design of record: `docs/p15f2c2c-scoping.md` (§half-(B) = the 5-step route; §bricks table).
* Board rows: `docs/tickets.md` P-15f2c2c (umbrella, ◐) + P-15f2c2c1–c2c4.
* Landed: `GQ2/UnramifiedNorm.lean` (half A, commit `6e0ea24`); split commit `d1a5540`.
* Consumers: `GQ2/ShapiroDeepness.lean` (c2b), then f2d (`docs/p15f2-handoff.md`).
* Precedent for the Galois↔spectral bridge style: `GQ2/ResidueLift.lean` (f8's
  residue-trivial tame lift — the whole file is a worked example of this ticket's genre).
