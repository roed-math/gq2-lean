# P-16d6e4a — the (83)-evaluation seam: F-design + reduction record (Opus, 2026-07-08)

Discharges `GaussZResidue b F En l h G0` (the `phase140_from_residues` `hGaussZ` input) per
source, i.e. `∀ ρ, ∑ᶠ c : VCocycle …, sign(QZero … c) = #V · G0`.  Authoritative for
P-16d6e4a; the board row defers here.  Builds on `docs/p16d6e4-gauss-design.md` (layer (I),
LANDED) — which reduced the residue to `∑ᶠ x : Z¹⧸B¹, sign(Q̄⁰ x) = G0`.

## 0. The pivotal simplification (survey, 2026-07-08): the LOCAL source needs NO (83)

The e4 design (§3) proposed evaluating `Q̄⁰` on `H¹` by explicit cocycle coordinates.  The
survey found this is **already done for the local source**, better: the base determinant
form's Gauss sum on `H¹(G_ℚ₂, V)` is computed **directly** by §6.2/§6.3, both **sorry-free**:

* **`GQ2.UnramifiedModel.prop_6_18_unramified`** (`UnramifiedModel.lean:538`, sorry-free,
  std-3 + B7, B6 via the `D` param):
  `Nat.card {x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0} = 2^{2m−1} − 2^{m−1}`
  (hyp `hunram : ∀ v, c tameTau • v = v`).
* **`GQ2.DeepPart.prop_6_18_ramified`** (`DeepPart.lean:1428`, **sorry-free** — the two
  Lemma 6.17 sorries were closed):
  `Nat.card {x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0} = 2^{2m−1} + 2^{m−1}`
  (hyp `hram : ∃ v, c tameTau • v ≠ v`).

With `gaussSum_eq` (`GaussCount.lean:138`: `gaussSum q = 2·(zeroCount q) − #V`) and
`#H¹ = #V = 2^{2m}`:
`∑_{H¹} sign(Q0loc) = gaussSum(Q0loc) = 2·(2^{2m−1} ∓ 2^{m−1}) − 2^{2m} = ∓2^m`.

So **`G0 = −2^m` (unramified) / `+2^m` (ramified)** for the local source, matching the e4
design §0.  The `Q0loc` structure layer (`isQuadraticFp2_Q0loc`/`nonsingular_Q0loc`/
`polar_Q0loc`, `DeepPart.lean:916–1108`) and `D.inv.injective` are all landed.

**Consequence for scope**: P-16d6e4a's local half is a *transport* (my `QZero`/`VCocycle`
world ↔ the paper's `Q0loc`/`H1` world) composed with `prop_6_18` — no new deep math.  The
candidate half genuinely still needs (83)-for-Γ_A (no `prop_6_18`-analog exists over `Γ_A`).

## 1. The local-source transport reduction (O-work, ~300 ln)

Target: `GaussZResidue B.bF F En l h G0` where `Γ = AbsGalQ2`, `DD = En.descData l h`,
`ρ' = rhoPrime …ρ : AbsGalQ2 →* YC`, `V = En.Vmod`, `dat = En.dat l h`, `q̄ = En.qbar l h`.

```
GaussZResidue (local)
  ⟸ layer (I) gaussZ_reduction        [LANDED]  reduces to ∑_{Z¹⧸B¹} sign(QZeroBar) = G0
  ⟸ (A) VCocycle DD ρ' ≃+ Z1 AbsGalQ2 V      [SHARED — e3 is building it, see §3]
  ⟸ (B) vCobRange ↦ B1 under (A)             ⟹ (Z¹⧸B¹)_mine ≃ H1 AbsGalQ2 V
  ⟸ (C) iotaB φ = iotaF D (H2ofFun φ)  on Z2 ⟹ QZeroBar x = Q0loc D dat ρ' (Φ x)
  ⟸ (D) ∑_{H1} sign(Q0loc) = 2·zeroCount − #H1   [gaussSum_eq]
  ⟸ (E) prop_6_18_{unramified,ramified}          [LANDED, sorry-free]
```

### Sub-lemma (A) — the `VCocycle ≃+ Z1` bridge  ⚠ SHARED with e3

`VCocycle DD ρ'.crossed` (`c(γδ) = c γ + rho0 γ • c δ`) IS the `Z1` cocycle law
(`mem_Z1_iff`: `φ(gh) = φ g + g • φ h`) once the `V`-action factors through `ρ'`
(`hρ : g • v = ρ' g • v`).  Topology setup: `letI : TopologicalSpace En.Vmod := ⊥`
(finite ⟹ discrete), action `DistribMulAction AbsGalQ2 V := compHom … (rho0-as-hom)`,
continuity of `c` as a map to discrete `V` via the `iV`-invFun trick (`VCocycle.cont` gives
continuity through `iV∘ofAdd`, injective ⟹ invert — same exercise as
`graphPullback_mem_Z2_of_cocycle`).  **`GQ2/Phase140Local.lean:234,275` (the e3 prototype)
is building exactly this** for its `card_Z1_eq`/`hZcard` use.  **Recommendation**: land the
bridge ONCE as `vcocycleEquivZ1 : VCocycle DD ρ' ≃+ Z1 AbsGalQ2 V` in a shared file
(`VCocycle.lean` or a new common leaf), consumed by both e3 (hZcard) and e4a (this) — do NOT
duplicate.  Coordinate before writing.

### Sub-lemma (B) — `vCobRange ↦ B1`

Under (A), `vCob DD ρ' v = (γ ↦ rho0 γ • v − v)` maps to `dZero v = (γ ↦ γ•v − v) ∈ B1`
(same formula via `hρ`).  So `(A)` sends `vCobRange = range vCobHom` onto `B1 AbsGalQ2 V`,
inducing `Φ : (VCocycle ⧸ vCobRange) ≃+ (Z1 ⧸ B1) = H1 AbsGalQ2 V`
(`QuotientAddGroup.quotientEquiv…` / `QuotientAddGroup.congr` at the range-equality).

### Sub-lemma (C) — `iotaB = iotaF ∘ H2ofFun` on `Z²`  ⚠ mine (self-contained)

**LANDED (Opus, 2026-07-08)**: `GQ2/IotaBridge.lean` — `iotaB_eq_iotaF_of_injective (D) (hinj : Function.Injective (iotaF D)) {φ} (hφ : φ ∈ Z2 …) : iotaB φ = iotaF D (H2ofFun φ)` (std-3, green): both sides `= 0 ⟺ φ ∈ B²` (via `iotaB_eq_zero_iff`, `map_eq_zero_iff … hinj`, `H2mk_eq_zero_iff`), `ZMod 2` ⟹ equal.  **Remaining**: `iotaF_injective` (= `mapCoeff2_injective` — the degree-2 analog of `DeepPart.mapCoeff1_injective` — composed with `D.inv.injective` + `muTwoOfF2_injective`); a ~40-line cohomology-infra proof best homed in `Cohomology.lean`/`DeepPart.lean`, NOT the e4a leaf.

For `φ ∈ Z2 AbsGalQ2 (ZMod 2)`: `iotaB φ = iotaF D (H2ofFun φ)`.
Proof: `H2ofFun φ = H2mk ⟨φ,·⟩`; both sides are `0 ⟺ φ ∈ B2` — LHS by `iotaB`'s def; RHS
because `H2mk⟨φ⟩ = 0 ⟺ φ ∈ B2` (`H2mk_eq_zero_iff`) and **`iotaF D` is injective** (so
`iotaF(H2mk⟨φ⟩) = 0 ⟺ H2mk⟨φ⟩ = 0`); a `ZMod 2` element is 0-or-1, so agreeing-on-0 ⟹ equal.
`iotaF D` injective: `iotaF D = D.inv.toAddMonoidHom.comp (mapCoeff2 muTwoOfF2 …)`,
`D.inv.injective` (AddEquiv, `DeepPart.lean:1104` uses it) ∘ `mapCoeff2 muTwoOfF2` injective
(the μ₂≅𝔽₂ coeff-iso; establish via `mapCoeff2` functoriality or the `#H² = 2 = #ZMod 2`
equal-card argument — the ingredients are in `DeepPart.lean:1082–1108`/`Cohomology.lean:429`).
Then `QZero DD ρ' c = iotaB(graphPullback dat ρ' c) = iotaF(H2ofFun(graphPullback dat ρ' c))`
and `Q0loc D dat ρ' [c] = iotaF(H2ofFun(graphPullback dat ρ' (out[c])))`; by Lemma 6.4
(`RepIndependence.lemma_6_14`/rep-independence) the `out` representative is immaterial, so
`QZeroBar (mk c) = Q0loc D dat ρ' (Φ (mk c))`.  (`graphPullback` is always a `Z2` —
`graphPullback_mem_Z2_of_cocycle` — so the `φ ∈ Z2` side-condition is free.)

### Sub-lemmas (D)/(E) — the Gauss value  ⚠ mine (self-contained, output side)

`∑ᶠ x : H1, sign(Q0loc D dat ρ' x) = ∑ x, sign(Q0loc x)` (finsum→Finset, `H1` finite)
`= 2·(Nat.card {x // Q0loc x = 0}) − #H1` (`gaussSum_eq` + `zeroCount = Nat.card{=0}` + the
sign split) `= 2·(2^{2m−1} ∓ 2^{m−1}) − 2^{2m} = ∓2^m` (prop_6_18 + `hcard`).  Package as
`sum_sign_Q0loc_eq_pinned` (both cases).

### Hypothesis supply (at e7, from `En`/the block — the interface)

`prop_6_18` needs, over `AbsGalQ2` at `C := YC`, `V := En.Vmod`:
* `c : ContinuousMonoidHom Ttame YC`, `hc` surjective, `hfac : ∀ g, ρ' g = c (B.tameF g)` —
  the **tame factorization** of the lower map (the block's `C` receives the boundary through
  the tame quotient; this is the c3-G0 tame package `c`/`hc`, threaded at e7).  ⚠ the single
  genuinely structural input beyond the form data.
* form data `q := En.qbar l h`, `hq := En.hquad`, `hns := En.hns`, `hinv := En.hinv`,
  `dat := En.dat l h`, `hdat := En.hdat` — all `En` fields ✓.
* `hfaith`/`hsimple` (the `prop_8_9` ledger hyps ✓), `hV := hVne` ✓.
* `m`, `hm : 1 ≤ m`, `hcard : #V = 2^{2m}` — the block's even-dimension fact (c3-G0 threads
  `#V = 2^{2m}`; `hm` from `hVne`).
* **un/ram split**: `hunram : ∀ v, c tameTau • v = v` vs `hram : ∃ v, c tameTau • v ≠ v` —
  decides `G0 = ∓2^m`.  Source-INDEPENDENT (the marking `c` is frame-level), so BOTH sources
  land in the same case and share `G0`, as `prop_8_9` requires.  At e7: `by_cases` on
  `∀ v, c tameTau • v = v`.

## 2. The candidate source (`Γ_A`) — the genuine remaining seam

`QZeroBar` over `Γ_A` lives on `H¹(Γ_A, En.Vmod)`; there is **no `prop_6_18`-analog** over
`Γ_A`.  Two routes:
* **(83)-for-Γ_A** (the paper's actual candidate derivation): `Q⁰_{Γ_A} ≅ q̄` (unramified) /
  `q_U` (ramified) as forms, via the §6.3–6.5 finite-word ledger through `WordCohBridge` +
  P-16c4 technology; then `gaussSum = gaussSum(q̄)` from `prop_6_9_unramified`/`lemma_6_8`
  (`SectionSix.lean:303/240`, both landed).  This is the P-12 seam; overlaps P-16d6e5's
  degree-2 word bridge — sequence AFTER it.
* **equal-Gauss shortcut**: `prop_8_9` shares ONE `G0` across sources; if the candidate base
  form is shown to have the SAME Gauss sum as the local one (Cor 6.19(iv) — both `∓2^m`),
  `hGaussZA` follows from the local value.  But proving the candidate's Gauss sum still needs
  a form-identification (83)-for-Γ_A or a direct `H¹(Γ_A)`-Kummer computation — no free lunch.
* **Fallback (legitimate)**: leave `hGaussZA` on the `prop_8_9` ledger and close P-16 modulo
  it, exactly as §6.2 deferred Prop 6.5.  Then `hGaussZF` (local) is discharged, `hGaussZA`
  (candidate) remains a single named hypothesis.

## 3. Coordination + status

* **(A) `VCocycle ≃+ Z1`** is shared with **e3** (`Phase140Local.lean`, in flight).  Must be
  landed once in a common file; do not duplicate.  This is the gating item for the local
  O-close.
* **(C)/(D)/(E)** are self-contained and mine; (C)'s `iotaB_eq_iotaF` is reusable well beyond
  e4a (it bridges the ENTIRE `iotaB`/master-count layer to the `iotaF`/§6 layer).
* The **candidate** is genuinely coupled to e5/e6's Γ_A word machinery; expect it to remain a
  ledger hypothesis at first P-16 close.

**Recommended order**: (i) coordinate/land (A) as `vcocycleEquivZ1` in a shared file; (ii)
land (C) `iotaB_eq_iotaF` + (D)/(E) `sum_sign_Q0loc_eq_pinned` (self-contained); (iii) assemble
the local `hGaussZF` discharge with the (hfac tame-factorization + form + un/ram) supply;
(iv) candidate via (83)-for-Γ_A after e5, else ledger fallback.
