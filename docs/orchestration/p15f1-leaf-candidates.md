# P-15f1 — precise leaf candidates and references

**Date**: 2026-07-05 (Opus).  **For**: the census/scope decision on instantiating
`GQ2.LocalKummer.DeepKummerData` (the last open piece of `lemma_6_17_dim`).

Bibliography keys are the **paper's own** (`paper/…pdf`):
* **[1]** J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  Springer Grundlehren **323**, 2015.
* **[5]** K. S. Brown, *Cohomology of Groups*, Springer GTM **87**, 1982.
* **[7]** J.-P. Serre, *Local Fields*, Springer GTM **67**, 1979.

---

## 0. Refined picture (after reading the paper's proofs of (78)–(80) and Lemma 6.17)

The `DeepKummerData` fields do **not** all have the same difficulty.  Reading the paper closely
(pp. 25, 33–34) splits them three ways:

| Field(s) | Mathematical content | Difficulty | Needs a leaf? |
|---|---|---|---|
| `card_fam` (total) | `#Hom_{H_V}(V^∨,M_K) = #H¹(ℚ₂,V) = #V` | **BANKED** (`card_H1_eq_card_of_simple`, B7 Euler) | **no** |
| `hinf`, `hext` | `H¹, H²(H_V, V) = 0` | tractable in-repo (see §1) | **no** |
| `hpair`, `hmid`, `card_deepFam` | the deep half is exactly half: `#deepPart = 2^m` | the real content (see §2) | see §3 |

So the honest remaining mathematics is a single statement — **`#deepPart = 2^m`** (`#V = 2^{2m}`)
— and the machinery below exists to prove *that*.  (The Layer-1 graded `(e,d)` scaffold is more
general than strictly needed now that `#H¹ = #V` is banked; it will be trimmed at instantiation.)

---

## 1. `hinf` / `hext` — PROVABLE in-repo, NO leaf proposed

**Claim.** `H¹(H_V, V) = 0` and `H²(H_V, V) = 0`, where `H_V = im ρ` is the faithful tame image.

**Paper's proof** (proof of (78), p. 25, lines "Assume that V is ramified…"; and p. 33 for the
same vanishing):
* *Unramified case*: `H_V` is cyclic of **odd** order ⟹ `𝔽₂[H_V]` semisimple ⟹ **Maschke**
  kills positive-degree cohomology.
* *Ramified case*: let `I ◁ H_V` be the odd tame-inertia subgroup.  `(V)^I = 0` (V simple,
  inertia acts nontrivially); `|I|` odd ⟹ `H^j(I, V) = 0` for `j > 0` (coprime-order
  averaging).  The **Hochschild–Serre** sequence for `1 → I → H_V → H_V/I → 1` then has every
  `E₂^{p,q} = H^p(H_V/I, H^q(I,V)) = 0`, so `H^n(H_V, V) = 0` for all `n`.

**Reference**: [5] Brown, Ch. VII (Hochschild–Serre / coprime averaging); Maschke is standard.

**Formalization note**: these are `InflationVanishes`/`FamiliesExtend` in `LocalKummer.lean`,
phrased ambiently (a cocycle on `G_ℚ₂` vanishing on `ker ρ` is a coboundary; every admissible
family is hit).  The one friction is that the repo cohomology is the bespoke `ContCoh`, not
Mathlib `groupCohomology`, so Hochschild–Serre is not off-the-shelf.  **But `hinf` in particular
is provable directly, no spectral sequence**: a continuous cocycle `b : G_ℚ₂ → V` vanishing on
`N = ker ρ` descends to `b̄ : H_V → V`, and `H¹(H_V,V)=0` (coprime/Maschke, or the HS collapse)
gives `b̄ = coboundary`.  `hext` needs the surjectivity direction (`H²`), a bit more.  **Estimated
tractable; scoped as ordinary proof work, not a leaf.**

---

## 2. The half-count `#deepPart = 2^m` — the real content

`#deepPart = #Hom_{H_V}(V^∨, U_{e+1})` and the total `#Hom_{H_V}(V^∨, M_K) = #V = 2^{2m}`.  The
claim `#deepPart² = #V` is that `U_{e+1}` carries exactly **half** the `V^∨`-isotypic content of
`M_K`.  It rests on two independent inputs:

* **(2a) Multiplicativity of `#Hom_{H_V}(V^∨, −)` across `0 → U_{e+1} → M_K → M_K/U_{e+1} → 0`**
  — i.e. `Ext¹_{𝔽₂[H_V]}(V^∨, U_{e+1}) = 0`.  The `≤` direction is free (left-exactness of
  `Hom`); the `≥` direction is **exactly** projectivity of `V^∨`.  Here the coprime argument of §1
  does **not** help: `(V ⊗ U_{e+1})^I ≠ 0` at the deep contributing depths, so `H¹(H_V, V⊗U_{e+1})`
  need not vanish — projectivity is genuinely required.  **This is Lemma 6.11 (the mountain).**
* **(2b) The self-duality halving `#Hom(V^∨,U_{e+1}) = #Hom(V^∨, M_K/U_{e+1})`** — from `V ≅ V^∨`
  (invariant form `q`) + Hilbert duality `U_i^⊥ = U_{2e−i+1}` (eq. (94)) pairing depth `j` with
  depth `2e−j` and the unpaired middle `j=e` carrying no ramified `V` (Lemma 6.10).  This is the
  `hpair`/`hmid` content, resting on **L2/L3** below.

---

## 3. The proposed leaves (with exact statements, signatures, references)

### L1 — Kummer identification `H¹(G_K, 𝔽₂) ≅ K^×/K^{×2}`

**Statement.** For `K` a finite extension of `ℚ₂` (char 0, so `μ₂ = {±1} ⊂ K`), the class map
`kummerClass : Kˣ → H¹(G_K, ℤ/2)` induces an isomorphism `K^×/(K^×)² ≅ H¹(G_K, ℤ/2)`.

**Lean shape** (only the *surjectivity* is open):
```
theorem kummerClass_surjective (K …) : Function.Surjective (kummerClass (K := K))
```
**Reference**: [1] NSW, Ch. VI (Kummer theory); the `μ₂`-case of `H¹(G_K, μ_n) ≅ K^×/(K^×)^n`.
Also Serre, *Galois Cohomology* II §1.2.

**Provability**: injectivity is **already proved** — `Kummer.kummerClass_eq_zero_iff`
(`[a]=0 ⟺ IsSquare a`, via `InfiniteGalois.mem_range_algebraMap_iff_fixed`).  Surjectivity is
likely **provable without a leaf** by a cardinality pinch: `#(K^×/K^{×2}) = 2^{[K:ℚ₂]+2}` and
`#H¹(G_K,ℤ/2) = 2^{[K:ℚ₂]+2}` (local Euler characteristic, the `G_K`-analogue of B7) coincide, so
injective + equal-finite ⟹ bijective.  **Recommendation: attempt the proof; leaf only if the
`G_K`-Euler-characteristic input proves out of reach in the repo framework.**

### L2 — the (93) dyadic square-class filtration

**Statement (eq. (93))**: for `K/ℚ₂` tame with `e = v_K(2)`, the `Gal(K/ℚ₂)`-module
`M_K = K^×/K^{×2}` has a filtration by the unit-image submodules `U_i = im(1 + 𝔭_K^i)` with graded
pieces
```
gr_i M_K ≅ k_K   (1 ≤ i < 2e, i odd),      gr_i M_K = 0   (1 ≤ i < 2e, i even),
```
(`k_K` = residue field as inertia-twisted module), boundary layers `ℤ/2` at `i ∈ {0, 2e}`, and
`U_{2e+1} ⊆ (K^×)²`.

**Reference**: [7] Serre, *Local Fields*, **Ch. XIV §§2–3** (the paper's own citation for
(93)/(94)); the unit filtration `U_i = 1 + 𝔭^i` is Serre LF Ch. IV–V.

**Provability**: standard but genuinely nontrivial to formalize (dyadic square classes; `U_{2e+1}
⊆ squares` is Hensel — the repo already has the analogue `sq_of_near_one` from P-15e).  **A
defensible leaf** (literature-standard, [7]-cited), or a real formalization project.

### L3 — the (94) Hilbert orthogonality `U_i^⊥ = U_{2e−i+1}`, `−1 ∈ U_e`

**Statement**: under the Hilbert-symbol pairing on `M_K`, `U_i^⊥ = U_{2e−i+1}` and `−1 ∈ U_e`.

**Reference**: [7] Serre, *Local Fields*, **Ch. XIV §§2–3**.

**Consumer**: **P-15f2** (the free-orbit (94) vanishing), *not* f1 directly — but f1's `hpair`
(self-duality halving) uses the depth-pairing `j ↔ 2e−j` that (94) encodes.  Bundle with L2.

### 6.11 — projectivity of `V`, `V^∨` over `𝔽₂[H_V]` (the mountain)

**Statement (Lemma 6.11)**: if `V` is ramified, `V` and `V^∨` are projective `𝔽₂[H_V]`-modules.
**Consequence used**: `Ext¹_{𝔽₂[H_V]}(V^∨, −) = 0` ⟹ `Hom_{H_V}(V^∨, −)` exact ⟹ the
multiplicativity (2a).

**Reference**: **Higman's criterion** — [5] Brown, Ch. VI (relative projectivity /
`𝔽₂[H]`-projective ⟺ `𝔽₂[P]`-projective, `P` a Sylow-2); or Serre, *Linear Representations*, §14.
**Clifford theory** (the weight-orbit freeness over `P`) — Curtis–Reiner, *Methods of
Representation Theory* I, §11.  Mathlib has **neither**.

**Provability**: this is the paper's own content, not a citation — proving it means building
Higman + a Clifford weight-orbit argument in the repo.  **Either a large formalization, or (if
sped) a single leaf `V^∨` projective ⟹ `Ext¹(V^∨,−)=0`, capturing 6.11's consequence.**  The
latter would be the *one* place the project leafs paper-proved (not literature-cited) content.

---

## 4. Recommendation

The principled reading, matching the project's hygiene (leaf [7]/[1]-citable facts; prove the
paper's own content):

1. **`hinf`/`hext`**: prove (Brown Ch VII coprime + HS) — **no leaf**.
2. **L1**: attempt the cardinality-pinch proof (injectivity banked) — **leaf only if it stalls**.
3. **L2** (± L3 for f2): **leaf** — literature-standard, [7 Ch XIV]-cited, heavy to formalize.
4. **6.11**: the genuine fork.  Principled = **prove** (Higman+Clifford, multi-session).  Fast =
   **one leaf** for `Ext¹(V^∨,−)=0`.

Net if we leaf L2(+L3) only and prove the rest: **census 13 → 14** (one literature leaf), with
6.11 as a scoped in-repo formalization.  If we also leaf 6.11's consequence: **13 → 15**.
