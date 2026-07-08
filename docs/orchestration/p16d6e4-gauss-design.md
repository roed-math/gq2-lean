# P-16d6e4 — the source-Gauss transport `hGaussZ`: F-design record (Fable 5, 2026-07-08)

The design for the residue
`hGaussZ : ∀ ρ, ∑ᶠ c : VCocycle DD ρ', sign (QZero DD ρ' c) = #V · G0`
(consumed by `phase140_from_residues`, both sources, shared `G0`).  Authoritative; the
P-16d6e4 board row defers here.

## 0. The finding that reshapes the ticket (paper pp. 40–41 reread)

The (140) factor is `G(Q⁰)` for `Q⁰` **the base determinant form on `H¹_{Γ,ρ}(V)`** — NOT
`gaussSum q̄` on `V`.  Its value comes from the §6.2 evaluation **(83)**: `Q⁰ ≅ q̄`
(inertia trivial in `C₀`) or `Q⁰ ≅ q̄_U = qDouble q̄ (U•·)`, `U = S^{ω₂}` (ramified) — and
the repo formalized §6.2 **in the evaluated shape** (`SectionSix.lean` GaussSign header:
"Deriving (83) from the relator ledger is Prop 6.5 = the P-12 seam").  Consequences:

* The e1-ledger hypothesis `hG0indep : gaussSum (En.qbar l h) const` is **wrong-shaped** in
  the ramified case (`G0 ≠ gaussSum q̄` there) — replace it (§4 below).
* The pinned values are **concrete** (both landed, std-3):
  - unramified (`c tameTau = 1`): `prop_6_9_unramified` gives
    `zeroCount q̄ = 2^{2m−1} − 2^{m−1}`, i.e. `gaussSum q̄ = 2·zc − 2^{2m} = −2^m`;
  - ramified: `lemma_6_8` clause 4 gives `arf (qDouble q̄ (U•·)) = 0` on the SAME space `V`
    (`qDouble q U x = q x + polar q x (U x)`, `QuadraticFp2.lean:81`), i.e. Gauss sum `+2^m`.

  **`G0 = −2^m` unramified, `+2^m` ramified** — frame-level (the tame marking
  `c : Ttame → C₀` is source-free), hence shared between the sources as required.
* The irreducible depth is the **(83)-evaluation per source** — identifying the descended
  form `Q̄⁰` on `H¹_{Γ,ρ}(V)` with the pinned shape.  This is the P-12 seam surfacing in
  the (140) lane; it CANNOT be absorbed into e4 silently → split ticket **P-16d6e4a** (§5).

Dead ends checked so far: pinning `Arf(Q̄⁰)` via the §6.2 orbit machinery fails (`H¹` is
not a `C`-module); `zeroCount(Q⁰)` as a lift-count through the `κ⁰`-extension
`Ẽ(q̄) ↠ V⋊C` is the Gauss count itself (the obstruction is quadratic in `c`, so no
half-torsor affinity); redefining the shared datum to dodge the sign fails (source-equality
of the `H¹`-Gauss IS the content).

## 1. The three-layer decomposition

```
hGaussZ  =  (I) Z¹ → H¹ reduction   [generic, PROVE NOW — the e4 O-close]
          ⊗ (II) the H¹-evaluation (83) per source   [P-16d6e4a — the deep seam]
          ⊗ (III) the pinning of the evaluated form   [LANDED: prop_6_9_unramified / lemma_6_8]
```

## 2. Layer (I): the generic `Z¹ → H¹` reduction (fully specified O-work)

New leaf `GQ2/GaussZReduction.lean` (imports `GQ2.KeystoneDelta`; work at the
`DescData`/`VCocycle` layer of the master count).

1. **`graphPullback_shift_mem_B2`** (generic Γ): for `c : VCocycle DD ρ`, `v : DD.Vmod`,
   `graphPullback DD.dat ρ' (c + vCob DD ρ v).c − graphPullback DD.dat ρ' c.c
     ∈ B2 Γ (ZMod 2)`.
   Adapt `RepIndependence.graphPullback_sub_mem_B2` (`RepIndependence.lean:88`) — its
   cochain identity (`dOne ψ` with `ψ g = f(w₀, b g) + f(b g, ρg•w₀) + m(ρg, w₀)`, the
   `(w₀,1)`-conjugation phase, proved by the P-15d `linear_combination` over
   `f_cocycle`/`f_polar`/`m_quad`/`m_mul`) is pure factor-set algebra; only the
   `AbsGalQ2`-bound continuity needs the `invFun`-through-`iV`-and-`ρ` factorization
   (same exercise as `graphPullback_mem_Z2_of_cocycle`, P-16d6e2).  Sign note: the paper's
   `vCob v = ρ'(γ)•v − v` matches RepIndependence's `δ⁰w₀`.
2. **`iotaB_add_mem_B2`** : `β ∈ B2 → iotaB (φ + β) = iotaB φ` — 3 lines from `iotaB`'s
   defining `if φ ∈ B2` (B2 is an `AddSubgroup`); **no `hH2` needed** (unlike `iotaB_add`).
3. **`QZero_add_vCob`** : `QZero DD ρ (c + vCob DD ρ v) = QZero DD ρ c` — (1)+(2) plus the
   pointwise function identity `graphPullback (c+∂v) = graphPullback c + shift`.
4. **`vCobHom : DD.Vmod →+ VCocycle DD ρ`** (from `vCob_add`, c1a) with
   `#(vCobHom.range) = #V`: `vCob_injective` (c1a, `VCocycle.lean:169`) at
   `hfix : ∀ v, (∀ γ, rho0 DD ρ γ • v = v) → v = 0`, discharged from
   {`hsimple`, `hfaith`, `Nontrivial RF.YC`, surjectivity of `γ ↦ rho0 …` (from the
   `ContSurj` in `BoundaryLifts` through `rho0_descData_rhoPrime`)}:
   `V^{C₀}` is a `C₀`-submodule; `= ⊤` ⟹ trivial action ⟹ (`hfaith`) `C₀`
   subsingleton, contradicting `Nontrivial`; so `= ⊥` by `hsimple`.
   ⚠ ledger impact: `Nontrivial RF.YC` is a NEW hypothesis (see §4).
5. **`QZeroBar`** on `VCocycle DD ρ ⧸ vCobHom.range` (well-defined by (3);
   `QuotientAddGroup.lift`-free — define via `Quotient.lift` on the raw quotient or just
   work with fiberwise sums) and the **orbit-sum**:
   `∑ᶠ c, sign (QZero c) = #V * ∑ᶠ x : quotient, sign (QZeroBar x)` —
   `Fintype.sum_fiberwise` over `QuotientAddGroup.mk`, constant on cosets by (3), fibre
   card `#V` by (4) (coset ≃ range ≃ V).  Finiteness: `finite_vcocycle` (c1b) from `hfg`.
6. Cheap corollary for e4a's consumers: `#(quotient) = #V` from `hZcard`
   (`#Z¹ = #V²`) and (4).

Result shape: `hGaussZ ⟺ ∑ᶠ x : H¹-model, sign (QZeroBar x) = G0` — a Gauss sum on a
`#V`-sized space.

## 3. Layer (II) = P-16d6e4a: the (83)-evaluation (the honest new seam)

Per source, produce an explicit `𝔽₂`-isomorphism `e : (VCocycle DD ρ ⧸ B¹) ≃+ V` (or any
`#V`-space) with `QZeroBar = (pinned form) ∘ e`, where the pinned form is `q̄` (unramified)
/ `qDouble q̄ (U•·)` (ramified).  Routes:

* **Local (`G_ℚ₂`)**: explicit cocycle coordinates.  `Z¹` splits along the wild/tame
  filtration (the wild part contributes `Hom`-coordinates since `V` is tame); evaluate
  `ι_Γ ∘ graphPullback` on the coordinates via the landed invariant-map machinery
  (`LocalLiftingDuality`, B6).  The unramified case kills the `H¹_ur`-part
  (`V^F = V^{C₀} = 0`).
* **Candidate (`Γ_A`)**: the §6.3–6.5 finite-word ledger (the original home of (83)) —
  word-level evaluation of the pulled-back class on the two relators, through the
  `WordCohBridge` and P-16c4's ledger technology.  This overlaps P-16d6e5's degree-2
  bridge; sequence AFTER it.
* **Fallback** (legitimate, matches the repo's own (83)-precedent): keep the two
  evaluations as the `prop_8_9` ledger hypotheses `hGaussZA`/`hGaussZF` (§4) and close
  P-16 modulo them, with P-16d6e4a remaining open — exactly how §6.2 itself deferred
  Prop 6.5.

## 4. Ledger reshape (Prop89Close.lean — do at the e4 O-close)

* **DROP** `hG0indep` (wrong-shaped in the ramified case, and subsumed).
* **ADD** `(G0 : ℤ)` + per-source
  `hGaussZA : ∀ l h ρ, ∑ᶠ c : VCocycle …(B.bA)…, sign (QZero …) = #V · G0` and
  `hGaussZF : (same at B.bF)` — the exact `phase140_from_residues`-input shape (already
  (l,ρ)-uniform, so no separate l-independence hypothesis).
  Dischargers (recorded): layer (I) + P-16d6e4a + the landed pinning; expected value
  `G0 = if c tameTau = 1 then −2^m else 2^m`.
* **ADD** `Nontrivial RF.YC` (for §2 item 4; discharged at P-17h — the §7 block has a
  nontrivial simple head, so `C = Y/K ≠ 1`).
* e3/e6 rows: **remove `hGaussZ` from their scopes** (it is not per-source-provable with
  current machinery; it is e4/e4a's).

## 5. Work order

1. ✅ **DONE (Opus, 2026-07-08)** — Layer (I) in `GQ2/GaussZReduction.lean` (all std-3) + the §4
   ledger reshape in `GQ2/Prop89Close.lean` + the `GaussZResidue` abbreviation in
   `GQ2/Phase140Assembly.lean`; tree 8711, `check_axioms` exit 0.
2. ✅ **DONE** — `hGaussZ` is now the `GaussZResidue` ledger hypothesis; e7 threads
   `hGaussZA`/`hGaussZF` into `phase140_from_residues` (they are NOT e3/e6 residues — the board
   e3/e6 rows are annotated accordingly).
3. (F→O, **P-16d6e4a**) the two (83)-evaluations `∑_{Z¹⧸B¹} sign(Q̄⁰) = G0`, local first
   (candidate waits on e5's degree-2 bridge).  This is the only remaining P-16d6e4 content.

## 6. Landed name map (for e4a / e7)

`GQ2.SectionEight.AffineTLift` (in `GaussZReduction.lean`):
* `gaussZ_reduction σ hσ hfg htriv hfix : ∑ᶠ c, sign (QZero DD ρ c)
  = #V * ∑ᶠ x : (VCocycle DD ρ ⧸ vCobRange DD ρ), sign (QZeroBar DD ρ htriv x)`
* `QZeroBar DD ρ htriv : (VCocycle DD ρ ⧸ vCobRange DD ρ) → ZMod 2` — the descended form
  e4a evaluates; `QZeroBar_mk` reduces it on representatives.
* `card_quotient_vCobRange hfix hZcard : #(VCocycle DD ρ ⧸ vCobRange DD ρ) = #V`.
* `hfix_of_simple hsurj hsimple hfaith : hfix` (discharges the freeness at e7).

`GQ2.SectionEight` (in `Phase140Assembly.lean`):
* `GaussZResidue b F En l h G0 : Prop` — the exact `phase140_from_residues` `hGaussZ` shape;
  e4a proves it from `gaussZ_reduction` + the (83)-evaluation, per source.
