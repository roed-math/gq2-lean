# LG-K recon survey — field-generic deep-unit package (2026-07-28)

Read-only survey of the repo at master `d0714a7`, taken at campaign setup. Seed material for
ticket LG1 (design memo). File:line anchors verified at survey time.

## 1. The ℚ₂ determinant/deep-part chain

**Entry points** (both in the `2^{2m−1} ± 2^{m−1}` zero-count form, `#V = 2^{2m}`):

| Decl | File:line | Statement |
|---|---|---|
| `GQ2.DetRamified.prop_6_18_ramified` | `GQ2/DetRamified.lean:53` | `#{x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0} = 2^(2m−1) + 2^(m−1)` (positive sign) |
| `GQ2.UnramifiedModel.prop_6_18_unramified` | `GQ2/UnramifiedModel.lean:585` | same, `− 2^(m−1)` (negative sign), hypothesis `hunram : ∀ v, c tameTau • v = v` |

**Join point** — `GQ2.DeepPart.card_Q0loc_zero_eq_of_dim_of_vanish`
(`GQ2/DeepPart/Q0locLayer.lean:547`): takes `hdim : #X₊² = #H¹` and
`hvanish : Q⁰_loc|X₊ = 0`, returns the count via the Lagrangian-Arf package + Euler collapse.
Axioms B6, B7.

**Dimension clause** (`#X₊² = #H¹`), the square-class-filtration → Hom-count lane:

```
ResidueLift.lemma_6_17_dim_final            GQ2/ResidueLift.lean:333
  └ DimClose.lemma_6_17_dim_of_residueLift  GQ2/DimClose.lean:55
     └ DimAssembly.lemma_6_17_dim_of_hduality        GQ2/DimAssembly.lean:249
        └ DimAssembly.lemma_6_17_dim_of_hext_hduality GQ2/DimAssembly.lean:199
           └ AdmissibleCount.card_deepPart_sq_of_duality GQ2/AdmissibleCount.lean:466
```
Three deferred inputs to `card_deepPart_sq_of_duality`:
- `hinf : LocalKummer.InflationVanishes ρ` — def `GQ2/LocalKummer.lean:304`; discharged
  `inflationVanishes_ramifiedTame` (:587) ← `inflationVanishes_of_oddNormal` (:493, coprime
  averaging over odd normal `I = ⟨cτ⟩`).
- `hext : LocalKummer.FamiliesExtend ρ` — def `GQ2/LocalKummer.lean:898`; discharged
  `Shapiro.familiesExtend_of_package` (`GQ2/Shapiro/Extend.lean:271`).
- `hduality : #Hom_C(V^∨, Deep) = #Hom_C(V^∨, H¹(N)/Deep)` — `DeepCount.hduality_of_data`
  (`GQ2/DeepCount/Finale.lean:46`) ← abstract engine `GQ2.card_equivHoms_deep_eq_quot`
  (`GQ2/DeepDuality.lean:874`).

The `hduality` inputs are the **square-class filtration** layer:
- pairing `pairingK` (`GQ2/DeepDualityK.lean:145`), nondegeneracy `pairingK_nondeg` (:159),
  built off `tateDualityK` (:84) via `ker_isLocalDualizingGroup` (:70);
- isotropy `deepClassesSubgroup_le_pairPerp_pairingK` (:567) ← `pairingK_deep_deep` (:514);
- `hsharp` = `midClassesSubgroup_le_pairPerp_pairingK` (:554) ← `pairingK_mid_deep` (:534),
  plus `DeepCount.card_quot_deep_le_card_mid_ker` (`GQ2/DeepCount/Transport.lean:301`) ←
  `card_quot_deep_le_card_mid` (`GQ2/DeepCount/Bounds.lean:517`);
- filtration arithmetic: `GQ2/DeepCount/Filtration.lean` (`grSq_injective/_surjective`
  :361/:385, `kummerDepth_even_collapse` :415, `classGrMap_injective` :499,
  `card_classGr_odd/_even` :554/:574), `Bounds.lean` (`exists_kummerDepth_ne_zero` :69,
  `kummerDepth_zero_collapse` :223, `card_quot_kummerDepth_one_le_two` :338);
- the `U^{(i)}` filtration itself: `GQ2.depthUnits` / `normUnits` / `DyadicUnitFiltration`
  (`GQ2/UnitFiltration.lean:48,63,134`), discharged (no axiom) by `dyadicUnitFiltration'`
  (`GQ2/UnitFiltrationCounts.lean:390`) — **field-generic for every finite `k/ℚ₂`**.

**Vanishing clause** (`Q⁰_loc|X₊ = 0`), the graph-obstruction lane:
```
VanishClose.lemma_6_17_vanish_final          GQ2/VanishClose.lean:205
  └ OrbitVanish.Q0loc_vanish_of_datum_decomp GQ2/OrbitVanish.lean:298
     ├ hcoh   : SectionSix.lemma_6_15_{square,free,involution}
     └ hvanish: InvolutionSplice.hvanish_cup_ker            GQ2/InvolutionSplice.lean:544
                ShapiroDeepness.hvanish_cup / _evensNorm / _involution
                                       GQ2/Shapiro/Deepness.lean:55 / :71 / :190
```
Field-side inputs: eq. (94) orthogonality in `GQ2/HilbertLedger.lean` (deep⟂deep :829,
mid⟂deep :907), and the deep Evens norm `SectionSix.lemma_6_16` (`GQ2/SectionSix.lean:767`) via
`EvensKahn.evensNormH2` (`GQ2/EvensKahn.lean:332`) and `EvensKahnDerived.evensKahn_dyadic_of_rsw`
(`GQ2/EvensKahnDerived.lean:91`).

**Q⁰_loc itself**: `SectionSix.Q0loc` (`GQ2/SectionSix.lean:157`) =
`iotaF D ∘ H2ofFun ∘ graphPullback dat ρ`, with `kappa0`/`graphPullback` in
`GQ2/OrbitData.lean:74,80`. Quadratic structure in `GQ2/DeepPart/Q0locLayer.lean`:
`graphPullback_add_sub_mem_B2` (:44), `Q0loc_add` (:96), `polar_Q0loc` (:141),
`isQuadraticFp2_Q0loc` (:156), `nonsingular_Q0loc` (:306), `deepPartSubgroup` (:430). Euler
collapse `#H¹ = #V`: `card_H1_eq_card_of_H0_H2_trivial` (`GQ2/DeepPart/MuTwoPolarDual.lean:34`),
assembled at `card_H1_eq_card_of_simple` (:317).

**Gauss-sign side** (Q⁰_A, not Q⁰_loc): `SectionSix.prop_6_9_unramified`
(`GQ2/SectionSix.lean:328`) / `prop_6_9_ramified` (:381).

## 2. ℚ₂-specific vs. already-generic

**Occurrence census** (`AbsGalQ2` hits / `ℚ_[2]|ℚ̄₂` hits / lines):

| Already field-generic (0 × `AbsGalQ2`) | ℚ₂-typed (needs re-basing) |
|---|---|
| `DeepPart/QuadraticFp2.lean` 0/0/359 · `DeepPart/HermitianCount.lean` 0/0/669 · `GaussSigns.lean` 0/0/768 · `GaussSignsRamified.lean` 0/0/285 · `UnitFiltration.lean` 0/26/159 · `UnitFiltrationCounts.lean` 0/70/414 · `DeepCount/Filtration.lean` 0/99/600 · `DeepCount/Bounds.lean` 0/45/642 · `HilbertLedger.lean` 0/109/929 | `Q0locLayer.lean` 117/13/626 · `LocalKummer.lean` 149/16/1001 · `DeepDualityK.lean` 93/43/580 · `VanishClose.lean` 77/0/425 · `DeepCount/Transport.lean` 75/29/373 · `AdmissibleCount.lean` 68/15/516 · `UnramifiedModel.lean` 60/0/673 · `DeepDuality.lean` 54/37/1395 · `MuTwoPolarDual.lean` 42/11/337 · `ResidueLift.lean` 26/39/365 · `DimAssembly.lean` 16/0/279 · `DeepCount/Finale.lean` 13/6/122 · `DimClose.lean` 8/3/105 |

The generic files are parametrized by `k : IntermediateField ℚ_[2] ℚ̄₂` with
`[FiniteDimensional ℚ_[2] k]`, ramification index `e`, residue degree `f` — **no `n = 1`, no
fixed `e_L`, no `U_3`/`1+8ℤ₂` anywhere**. `SectionSix.IsDeepUnit` (`GQ2/SectionSix.lean:742`)
encodes `U_{e+1}` π-freely as `‖A−1‖ < ‖2‖` over an arbitrary `N`; `IsMidUnit`
(`GQ2/DeepDuality.lean:1004`) is `U_e` as `‖A−1‖ ≤ ‖2‖`. Neither hard-codes a depth.

**Per packet deep-unit-package item (packet Def. 6.11):**
- **(a) projective inflation–restriction** — mechanically ℚ₂-typed only. `InflationVanishes`
  quantifies `b : Z1 AbsGalQ2 V`; the *proof* (`inflationVanishes_of_oddNormal`) is coprime
  averaging and base-free. Companion `FamiliesExtend` + `familiesExtend_of_package` likewise.
  **Effort: retyping, no new mathematics.**
- **(b) Hilbert orthogonality on the square-class filtration** — **already field-generic**
  (`HilbertLedger.lean`, `DeepCount/{Filtration,Bounds}.lean`). Only the `ker ρ`-side splices
  `pairingK_deep_deep` / `pairingK_mid_deep` carry `AbsGalQ2`, and they already take
  `(k, hker : x ∈ ker ρ ↔ x ∈ k.fixingSubgroup)` as a parameter.
- **(c) `X₊ = Hom_H(V^∨, U_{e_L+1})`, dim `n·dim V/2`** — `SectionSix.deepPart` (:844) already
  documents itself as `Hom_{H_V}(V^∨, U_{e+1})`. The Hom-count engine
  `card_equivHoms_deep_eq_quot` is **fully abstract**. What is `n = 1`: the Euler collapse
  delivers `#H¹ = #V`; for degree `n` the B7-analogue gives `#H¹ = (#V)^n`, hence exactly
  `n·dim V/2`. **This is the single arithmetic place `n` enters the dimension clause.**
- **(d) vanishing of the normalized graph obstruction on `X₊`** — `Q0loc` is typed at
  `H1 AbsGalQ2 V` with `D : TateDuality 2` (= `TateDualityG AbsGalQ2 2`). The Shapiro-Evens
  producers `hvanish_cup` / `hvanish_evensNorm` / `hvanish_involution`
  (`Shapiro/Deepness.lean:55/71/190`) are stated over an abstract `G` / a pair
  `k L : IntermediateField`, and `lemma_6_16` (deep Evens norm) is **already** stated for
  arbitrary finite dyadic `k ≤ L`. So (d) is: retype the shell, reuse producers verbatim.

**Genuinely `n = 1` / `q = 2` mathematics** (not just retyping):
1. `absGalQ2_localEulerCharacteristic` (B7) is stated only at `G_{ℚ₂}`.
2. `Ttame = ⟨σ, τ ∣ τ^σ = τ²⟩` (`GQ2/TameQuotient.lean:21,35`) hard-codes `q = 2`. Consumed by
   `prop_6_18_ramified`'s `c : ContinuousMonoidHom Ttame C`, by
   `inflationVanishes_ramifiedTame`, and by `powOmega2`/`tameSigma`/`tameTau` throughout §6.2.
3. `B10 tameQuotient : OrientedTameQuotient localReciprocity` and `B5 localReciprocity` are
   ℚ₂-only bundles.

## 3. The unramified sign side

The Hermitian-line computation lives in **`GQ2/DeepPart/HermitianCount.lean`** (669 lines,
zero Galois content — pure finite-field counting over `D` with `Fintype.card D = 2^(2m)`):
- `hermitian_form_eq_trace_form` (:477) = Lemma 6.7: every nonsingular `q` on `𝔽_{2^{2m}}`
  invariant under the norm-one circle is `x ↦ Tr(c·x^{2^m+1})` with `c^{2^m} ≠ c`;
- supporting: `card_frobFixed` (:184), `exists_trace_rep` (:206), `exists_add_pow_eq` (:240),
  `subring_eq_top_of_normOne_le` (:330), `card_filter_eq_of_mem_range` (:452);
- headline count `1 + (2^m+1)(2^{m−1}−1) = 2^{2m−1} − 2^{m−1}` (docstring :13–21).

Consumed at `UnramifiedModel.prop_6_18_unramified` (:585). The Q⁰_A twin is
`SectionSix.prop_6_9_unramified` (:328) ← `GaussSigns.prop_6_9_unramified_of_cyclic` (:451) ←
`_of_abelian` (:410) ← `_of_free` (:389); sign-level wrappers
`FoxH.GaussSigns.QZeroR_zeroCount_unramified` (`Roe/Gauss.lean:175`) and
`QZeroR_finsum_sign_unramified` (:208).

**What is hard-coded:** the sign is the *literal* `−` everywhere; there is no `n` argument and
no `(−1)^n` anywhere in the repo. The parity-carrying mechanism exists and is generic:
`GaussSigns.arf_eq_of_free_norm_one` (`GQ2/GaussSigns.lean:613`) and `arf_eq_of_free` (:682)
prove `arf q = (s : ZMod 2)` for `#V = 2^(2·m'·s)` under a free norm-one action, with
`not_dvd_sub_one_of_odd`/`not_dvd_add_one_of_even` (:546/:565) and the `gen_*` twins
(:647/:663) as the parity pinch. **That `s`-slot is exactly where `n` goes.** Also:
`UnramifiedModel.c_cyclic` (:69) collapses the unramified `C` to cyclic — `f = 1`-flavoured,
re-derive for general residue degree.

## 4. Axioms consumed

`prop_6_18_ramified` declares std-3 + {B6, B7, B9, B11a} (`GQ2/DetRamified.lean:27–30`);
consumers additionally supply B5/B10 for the `(R, horient)` reciprocity datum.

| Tag | Name | One line | Base-general? |
|---|---|---|---|
| B6 | `tateDualityAt` (:197) | Tate duality bundle `TateDualityG G 2` at any `G` with `IsLocalDualizingGroup G n` | **Yes** — `G_K` covered |
| B7 | `absGalQ2_localEulerCharacteristic` (:117) | `#H¹ = #H⁰·#H²·2^{v₂(#M)}` + finiteness, at `G_{ℚ₂}` only | **No** — the `n`-dependence of `dim X₊` lives here |
| B9 | `relativeStiefelWhitney_dyadic` (:266) | Kahn's relative SW identity (deg ≤ 2), arbitrary finite dyadic base | **Yes** |
| B11a | `hilbertSymbol_normCriterion_finiteDyadic` (:368) | cup-vanishing ⟺ norm equation, arbitrary finite dyadic `k` | **Yes** |
| B5 | `localReciprocity` (:171) | LCFT bundle for ℚ₂ | **No** |
| B10 | `tameQuotient` (:325) | oriented tame quotient `G_{ℚ₂}/W ≅ ⟨σ,τ ∣ τ^σ = τ²⟩` | **No** (`q = 2` baked in) |

**Discharged, no longer axioms:** B13 (unit filtration) → `dyadicUnitFiltration'`
(`GQ2/UnitFiltrationCounts.lean:390`), field-generic; B12 → `Shapiro.finite_H1_open`
(`GQ2/Shapiro/Finiteness.lean:262`), which **already transports B7-finiteness from `G_{ℚ₂}` to
any open finite-index subgroup — the precedent for deriving general-K Euler characteristic
instead of axiomatizing it**; B11b likewise in-repo.

**Not touched by this chain:** B1, B3c, B8.

## 5. Q0locLayer's "local source type"

**Literally `G_{ℚ₂}`, not an abstract Tate-duality source.** Variable block
(`GQ2/DeepPart/Q0locLayer.lean:36–38`) fixes `AbsGalQ2` (the concrete
`Field.absoluteGaloisGroup ℚ_[2]`, `GQ2/Statement.lean:40`); `TateDuality n` is the
`AbsGalQ2`-abbreviation (`GQ2/TateDuality.lean:237`). The abstraction target already exists:
`structure TateDualityG (G : Type) …` (`GQ2/TateDuality.lean:208`) and
`def IsLocalDualizingGroup G n` (:244) — `∃ ι : G →* AbsGalQ2, IsOpenEmbedding ι ∧
ι.range.FiniteIndex ∧ (compatible μₙ-action)`; `DeepDualityK.ker_isLocalDualizingGroup` (:70)
and `tateDualityK` (:84) already instantiate it at `ker ρ`. LG-K re-basing = replace `AbsGalQ2`
by an `IsLocalDualizingGroup`-parametrized `G` (or `K.fixingSubgroup`) through the 13 ℚ₂-typed
files above.

## Scoping summary

- **Free (no work):** ~4,400 lines already field-generic; B9/B11a base-general; B6
  group-parametric; B13/B12 discharged generically.
- **Mechanical retyping** (`AbsGalQ2` → local dualizing `G` / `K.fixingSubgroup`): ~6,700 lines
  across the 13 files in §2.
- **Genuine new mathematics:** (i) general-K Euler characteristic — TRY-DERIVE-FIRST from
  ℚ₂-B7 by Shapiro/induced modules (the `finite_H1_open` precedent), else axiom extension;
  (ii) general tame quotient `τ^σ = τ^{q_K}` + the B10/B5 orientation bundle over `K` (axiom
  extension); (iii) thread `(−1)^n` through the unramified sign using the existing parity
  engines.
