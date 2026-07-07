# P-15f2 option-1 scoping: closing `lemma_6_17_vanish` via orbit decomposition

**Date**: 2026-07-07 (Opus).  **Goal**: remove the `lemma_6_17_vanish` sorry
(`Q⁰_loc∣X₊ = 0`) by building the §6.2 orbit decomposition on top of the banked
`KappaNormalForm` scaffolding — the user-selected "option 1".

This doc records the **critical path** and, crucially, a prerequisite discovered during scoping —
**general `Q⁰_loc` datum-independence** (Lemma 6.1/6.4) — with its own reduction (landed) and a
subtlety analysis so the next session does not repeat the derivation.

## Architecture (paper §6.3, p. 34)

`lemma_6_17_vanish` gives an arbitrary equivariant factor set `dat` for the invariant nonsingular
`q` on the simple `𝔽₂[C]`-module `V`.  The paper's route:

1. **Regular embedding** (`lemma_6_11`, ✓ std-3 in `RegularSummand`): `V ↪ W = 𝔽₂[C]^N` as a
   `C`-equivariant split summand (`ι`, `r`, `r∘ι = id`).
2. **Transport** (`lemma_6_14`, ✓ in `RepIndependence`): `Q⁰_loc (datW.comap ι) ρ x = Q⁰_loc datW ρ (ι_*x)`
   for a datum `datW` on `W`.
3. **Orbit-sum datum on `W`**: `datW = sumDatum (orbit datums ext-by-0)` (`squareOrbitDatum` /
   `freeOrbitDatum` / `invOrbitDatum` from `OrbitData`, equivariance for the involution case banked
   in `InvolutionDatum.isEquivariantFactorSet_invOrbitDatum`).  Then `Q⁰_loc datW ρ (ι_*x)` is the
   orbit sum (via `graphPullback_sumDatum` + `Q0loc_vanish_of_datum_decomp`, both ✓ landed).
4. **Per-orbit corestriction** (`lemma_6_15` (103)/(104)/(105), ✓ banked in `ShapiroLedger`): each
   `graphPullback (orbit datum) ρ (Shapiro α_r)` is a `cor2Fun` of a scalar cup / Evens norm.
5. **Deep vanishing** (`cup_deepClasses` (94) / `lemma_6_16`, ✓ banked): for a deep class every
   scalar coordinate `α_r ∈ U_{e+1}(K)`, so each `inner` vanishes in the subgroup's `H²`.

The cohomological assembly of 3–5 is **already built** (P-15f2 increments 1–4,
`GQ2/OrbitVanish.lean`): `Q0loc_vanish_of_datum_decomp` consumes `datW = sumDatum s datf`,
per-orbit banked 6.15 `hcoh`, and per-orbit `hvanish`.

## The critical-path prerequisites (what is NOT yet built)

| # | Prerequisite | Status |
|---|---|---|
| **P0** | **`Q⁰_loc` datum-independence** (swap the given `dat` for `datW.comap ι`) | ⚠ **reduced to DI-core**, landed 2026-07-07 (below); DI-core itself open |
| P1 | **Isometric** regular embedding: `ι` with `Q_W ∘ ι = q` (`Q_W` = orbit-sum form) — upgrades `lemma_6_11`'s split embedding to an isometry | open |
| P2 | Orbit decomposition `datW = sumDatum (orbit datums)` at the datum level | ~trivial once `datW` is *defined* as the sum; the content is P1 (isometry) + P3 |
| P3 | **Shapiro-coordinate identification**: `(Quotient.out (ι_*x))` block coords = `shapiroFun (ker ρ) α_r` for scalar Kummer coordinates `α_r` | open |
| P4 | Per-orbit `hcoh`/`hvanish` matching to banked 6.15/6.16/(94) | small, on banked lemmas |

**Banked scaffolding** (`KappaNormalForm`, P-17e5, std-3): `PermW`, `permBas`,
`permBas_support_decomp`, `quadratic_eq_double_sum` (the monomial expansion
`Q F = ∑_{p,p'} F_p F_{p'} f₀(p,p')`), `exists_biadditive_refinement'`, `datum_add`/`datum_comap`/
`datum_of_split`, `exists_datum_of_invariant_quadratic`.  ⚠ It took a **non-orbit-decomposed**
"single β-refinement" route (for `kappa0_exists`), so it does not hand P2 the orbit-sum datum
directly — but P1/P3 sit on exactly this machinery.

## P0 — `Q⁰_loc` datum-independence (the discovered prerequisite)

Because `lemma_6_17_vanish` quantifies over **arbitrary** `dat`, step 2 cannot apply unless the given
`dat` equals `datW.comap ι` (impossible in general — `dat` is gauge-free) **or** `Q⁰_loc` is
independent of the datum for a fixed form.  Only a *special isometry case* is banked
(`UnramifiedModel.graphPullback_comap_smul_sub_mem_B2`).

**Reduction landed 2026-07-07** (`GQ2/OrbitVanish.lean`, `section DatumIndependence`, all std-3):
- `diffDatum dat1 dat2` — the pointwise 𝔽₂-sum (= char-2 difference).
- `graphPullback_diffDatum` — `graphPullback` is 𝔽₂-linear along it.
- `isEquivariantFactorSet_diffDatum` — the difference of two equivariant factor sets for the same
  `q` is an equivariant factor set for the **zero form**.
- `Q0loc_datum_indep_of_core` — datum-independence, **parametric on DI-core**.

**DI-core** (the isolated remaining input): *the graph pullback of a zero-form equivariant factor
set is a `2`-coboundary* (`∈ B²`).  Equivalently: the class `[κ⁰]` of a zero-form factor set on
`V ⋊ C` is trivial, so its `(b,ρ)`-pullback splits over `G_ℚ₂`.

### DI-core analysis (where the obstruction actually sits)

Candidate coboundary `Λ(g) := Δφ(b g)` for a quadratic refinement `Δφ : V → 𝔽₂` of the difference
datum.  With `polar Δφ = Δf` and the cocycle identity for `b`, a direct computation gives
`δ¹Λ(g,h) = Δf(b g, ρg·b h) + [Δφ(b h) + Δφ(ρg·b h)]`, which matches
`graphPullback (Δdat) ρ b (g,h) = Δf(b g, ρg·b h) + Δm(ρg)(b h)` **iff**
`Δφ(v) + Δφ(c·v) = Δm c v`.  That compatibility is **consistent** with the factor-set identities
(checked: `m_quad`, `m_mul`, `m_one` all follow from `polar Δφ = Δf`).

**The V-part is free.** `dat1.f` and `dat2.f` are factor sets with the **same diagonal** `q` and the
**same polar** `polar q`.  Over 𝔽₂, `H²(V; 𝔽₂)` (for a vector space `V`) is classified by the
diagonal quadratic form (`[f] ↦ (v ↦ f(v,v))` is a bijection onto quadratic forms), so `dat1.f` and
`dat2.f` are **cohomologous**: `Δf = dat1.f + dat2.f = δ_sym ψ₀` is a symmetric coboundary, and a
polar-refinement `Δφ` (with `polar Δφ = Δf`) **exists**.  (Earlier draft wrongly feared a cup-product
obstruction here — it cancels because the two data share the polar.)

**The residual obstruction is the C-equivariance.** The refinements form a torsor under additive
`L : V → 𝔽₂` (`Hom(V, 𝔽₂)`); matching the defect `Δφ(v) + Δφ(c·v) = Δm c v` requires an `L` with
`L(v) + L(c·v) = Δm c v − [ψ₀(v) + ψ₀(c·v)]`, solvable iff a class in `H¹(C, Hom(V, 𝔽₂))` vanishes.
That is the genuine Lemma-6.1/6.4 content (the `V ⋊ C` extension of a zero-form factor set splits).

So DI-core reduces to: **(i)** construct a quadratic refinement `Δφ` of `Δf` (𝔽₂-splitting of a
symmetric zero-diagonal cocycle — a `Module`-level lemma; `exists_biadditive_refinement'` gives the
biadditive analog and is a template), **(ii)** correct it by an additive `L` killing the
C-equivariance defect (`H¹(C, V*)` vanishing — leverage the odd-inertia / involution structure of
`C`), **(iii)** set `Λ(g) = Δφ(b g)` and verify `δ¹Λ = graphPullback Δdat` by the char-2 identity
above.

**(iii) LANDED 2026-07-07 (Opus): `OrbitVanish.graphPullback_mem_B2_of_refinement`** (std-3) — given
any `Δφ` with the polar identity `hQ` (Q) and the equivariance-defect identity `hE` (E), the graph
pullback IS the coboundary `δ¹(Δφ∘b)`, so `∈ B²`; capstone `Q0loc_datum_indep_of_refinement` chains
it through `Q0loc_datum_indep_of_core` to full `Q⁰_loc` datum-independence.  **The sole remaining f2a
input is the EXISTENCE of `Δφ` satisfying both (Q) and (E)** — equivalently, a `V`-only section
`σ(v,c) = Δφ(v)` splitting the zero-form central `2`-cocycle `κ⁰` on `V ⋊ C`.

**⚠ Refined finding (superseded below)**: (ii) does need C-structure — the combined `Δφ` exists iff a
class in `H¹(C, V*)` vanishes, false for general `C`.  But the alarm "(a2) hard / not ∅-axiom" was
**overcautious**; see the resolution.

### ★ RESOLVED PLAN (Fable 2026-07-07): full (a1)+(a2) proof verified on paper — ∅ axioms, banked patterns

**(a1), C-independent** (`exists_refinement_of_zero_form`, needs `hV2`): `Δf` is **symmetric**
(`f_polar` with `polar 0 = 0`) with **zero diagonal** (`f_diag`), so the central extension
`E = V ×_Δf 𝔽₂` — twisted addition `(v,a)+(w,b) = (v+w, a+b+Δf v w)`; associativity = `f_cocycle`
(orientation checked), commutativity = symmetry, `(e)+(e) = (2v, Δf v v) = 0` = `hV2` + zero
diagonal — is an **elementary abelian 2-group**, i.e. a `ZMod 2`-vector space (`zmodModule` +
`Fact (Nat.Prime 2)`, the in-repo `exists_biadditive_refinement'` pattern).  The linear projection
`E ↠ V` has a **linear section** (`LinearMap.exists_rightInverse_of_surjective` over the field
`ZMod 2`); its second coordinate is `Δφ₀` with (Q) on the nose.  [`Transgression.splitting_of_global_cocycle`
probed 2026-07-07: it is the §6.4 multiplicative group-section splitting (needs `hns`), NOT reusable
here.]  ~150–200 ln incl. the instance boilerplate.

**(a2), by the banked f1 averaging pattern** (`inflationVanishes_of_oddNormal`'s idiom; producers
`tameInertia_normal`/`odd_orderOf_tameInertia`/`fixedByNormal_eq_bot` banked): define the defect
`D c v := Δφ₀(c•v) + Δφ₀ v + Δm c v`.  Then (checked):
- `D c` is **additive in `v`** — (Q) twice + `m_quad` (the `Δf(cv,cw)+Δf(v,w)` terms cancel in pairs);
- `c ↦ D c` is a **right 1-cocycle**: `D (c*d) v = D c (d•v) + D d v` — `m_mul` + `mul_smul`;
- **Step A** (kill on `I`, only `|I|` odd needed): `L₀ v := Σ_{i∈I} D i v` satisfies
  `L₀(j•v) + L₀ v = D j v` for `j ∈ I` — expand `D i (j•v) = D (i*j) v + D j v`, reindex `i ↦ i*j`
  (`Equiv.mulRight` on `↥I`), `|I|·x = x` in `𝔽₂`.  Set `Δφ₁ = Δφ₀ + L₀` ((Q) preserved: `L₀` additive);
  its defect `D'` vanishes on `I`.
- **Step B** (kill everywhere, needs `I ◁ C` + `V^I = 0`): for `c ∈ C`, `i ∈ I`:
  `D' (c*i) = D' c (i•·)` (defect cocycle + `D' i = 0`) and `c*i = i'*c` with `i' = c i c⁻¹ ∈ I`
  gives `D' (i'*c) = D' c` — so `D' c (i•v) = D' c v` (`D' c` is `I`-invariant).  Then
  `D' c v = |I|·D' c v = Σ_{i∈I} D' c (i•v) = D' c (Σ_{i∈I} i•v) = D' c 0 = 0`, since
  `S v := Σ_{i∈I} i•v` is `I`-fixed (`mulLeft` reindex) hence `0` by `V^I = 0`.
  **No `H¹(C,V*)` general theory; no 2-torsion of `V` used in (a2)** (values in `𝔽₂`).

**(a3) capstone** `Q0loc_datum_indep`: (a1)+(a2) at `diffDatum dat1 dat2` (zero-form by the landed
`isEquivariantFactorSet_diffDatum`) feed the landed `Q0loc_datum_indep_of_refinement`.  **Parametric
signature** `(I : Subgroup C) (hIn : I.Normal) (hodd : Odd (Nat.card ↥I)) (hVI : ∀ v, (∀ i ∈ I, i•v = v) → v = 0)`
+ `hV2` — the f1 pattern; tame instantiation (`I = zpowers (c tameTau)`) stays with f2d.

So **f2a remains ∅-axiom as originally scoped** (the increment-1 alarm is retracted); est. total
~350–450 ln over increments A=(a1), B=(a2), C=(a3).

**Option-2 amendment (fix the canonical datum in 6.17) EVALUATED AND REJECTED (Fable 2026-07-07)**:
downstream consumers receive datums **existentially** (`kappa0_exists` / Lemma 6.3 produce
"`∃ dat, IsEquivariantFactorSet q dat`"), so fixing the datum inside 6.17/6.18 would only **relocate**
the independence requirement to the 6.18/6.19 → §8 consumer boundary (the Gauss-count statements
depend on the datum), not remove it — with frozen-signature churn across co-owned statements on top.
The paper proves 6.4 (independence) anyway, and (a2)'s collapse to the banked averaging pattern
removes the cost rationale.  Proceed with option 1 / f2a as scoped.

## Recommended order

1. **P0 / DI-core** — general datum-independence (Lemma 6.1/6.4).  Self-contained; the interface is
   already fixed by `Q0loc_datum_indep_of_core`.
2. **P1** — isometric regular embedding (on `KappaNormalForm`'s `PermW` + `exists_biadditive_refinement'`).
3. **P3** — Shapiro-coordinate identification (on `permBas_support_decomp` + `shapiroFun`).
4. **P2/P4** — assemble via the landed `Q0loc_vanish_of_datum_decomp`.

Each of P0/P1/P3 is a substantial, mostly-independent lemma; option 1 is a multi-session build.  The
**alternative** (reroute the vanishing through `KappaNormalForm`'s single β-datum, bypassing orbit
decomposition — still needs P0) remains on the table and may be shorter; weigh before P1.
