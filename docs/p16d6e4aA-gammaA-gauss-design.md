# P-16d6e4a-A — the (83)-for-Γ_A seam: F-survey + route design (Fable, 2026-07-08 session 4)

The candidate-source Gauss discharge: `hGaussZA`, i.e. for every boundary lift `ρ` of `Γ_A`,

    ∑ᶠ c : Z¹_{Γ_A,ρ'}(V), sign(Q⁰ c) = #V · G0        (G0 = −2^m unram / +2^m ram)

— `GaussZResidue B.bA F En l h G0` verbatim.  This is the ONLY remaining leaf of the P-16
tree (all parents closed "modulo P-16d6e4a"); `prop_8_9` itself is proved with `hGaussZA` a
named ledger hypothesis, so this lane discharges the hypothesis for the ThmFourTwo/P-17i
consumer.  Status quo ante: the sanctioned deferral (e4a design §2).

## 0. What is already generic (survey, verified in-repo)

The ENTIRE local composition except the pinned value is source-generic and lands for `Γ_A`
unchanged (all verified against the sources this session):

* `QZero DD ρ' c := iotaB (graphPullback DD.dat ρ'₀ c.c)` (`VLiftCount.lean:589`) — generic Γ.
* `iotaB` = the **continuous-coboundary indicator** `if φ ∈ B2 Γ 𝔽₂ then 0 else 1`
  (`PhaseObstruction.lean:51`) — generic; additive on cocycles given `#H²(Γ,𝔽₂) = 2`
  (`iotaB_add`), and `#H²(Γ_A,𝔽₂) = 2` is LANDED (`CardH2GammaA.card_H2_gammaA`).
* `gaussZ_reduction` (`GaussZReduction.lean`) — generic Γ, now takes `[Finite Z¹]`
  (σ-free; supply `hZcard_gammaA`'s count exactly as `GaussZFinal` does with
  `hZcard_local`).  `hfix_of_simple` — generic.
* The `Z¹⧸B¹ ≅ H¹(Γ, V)` bridge `toZ1`/`ofZ1`/`h1OfVQuot` (`GaussZLocal.lean` §Bridge) —
  **generic Γ** (checked: the section is `{Γ : Type} [Group Γ] [TopologicalSpace Γ]`).
* `#(Z¹⧸B¹) = #V` via `card_quotient_vCobRange` + `hZcard_gammaA` ✓.

**Non-generic remainder** (the true seam): the VALUE
`∑_{x : Z¹_{Γ_A}⧸B¹} sign(Q̄⁰ x) = G0` — locally this was `prop_6_18_{un,}ramified` through
Tate duality (`Q0loc`); over `Γ_A` there is no duality and no `Q0loc`.  Equivalently
(`iotaB` unfolds): compute

    zeroCount = #{x : Z¹⧸B¹ | graphPullback (En.dat l h) ρ'₀ (out x) ∈ B²(Γ_A, 𝔽₂)}
             = 2^{2m−1} ∓ 2^{m−1}.

## 1. The two candidate routes

### Route W (word-relator evaluation — the presentation-native route)

`Γ_A`'s finite presentation has ONE defining relation (the `GammaA`/`main_presentation`
layer).  For a one-relator (pro-2) group, `H²(Γ_A, 𝔽₂) ≅ 𝔽₂` is detected by the
**relator value**: a normalized 2-cocycle `φ` is a coboundary iff the `WordCoh2.CentExt φ`
central extension splits iff the e5-marking correction kills the relator lift
(`card_H2_gammaA_le_two`'s injection, `WordCoh2.lean:1545`; the e5 `Marking.push`/
`corrMark`/`Marking.descend` calculus; c4's obs/varCoc embedding `H²(Γ_A,𝔽₂) ↪ 𝔽₂`).

So `Q̄⁰(x)` = the relator-evaluation of `graphPullback (En.dat l h) ρ'₀ c` after
gauge-normalizing the generator marks — an EXPLICIT `𝔽₂`-valued function of the generator
values `c(g₁), c(g₂), c(g₃) ∈ V` (`z1Equiv`/e6-bridge coordinates, `Phase140GammaA`
Stage-0 blocks).  `graphPullback`'s relator evaluation = a finite sum of
`(En.dat l h)`-factor-set values along the relator word — **quadratic** in the `c(gᵢ)`
(the factor set is bi-affine in the graph coordinates).

Then the paper's (83)-shape: this quadratic on `Z¹⧸B¹ ≅ V` is `q̄` (unramified — the tame
generator acts trivially, collapsing two of the three coordinates) or `qDouble q̄ (U•·)`
(ramified — same space, the `U`-twisted double).  Finale: `gaussSum` is pinned by Arf
(`gaussSum_eq_of_arf_eq`, `PhaseGaussLIndep` ✓) with `arf(q̄) = 1` / `arf(qDouble) = 0`
(`prop_6_9_unramified` / `lemma_6_8` cl. 4, both landed and source-free) — no new counting.

Risks: (i) the gauge-normalization ("after correcting marks") must be shown to change the
relator value by a `B¹`-shift-absorbable amount — this is exactly the e5 `corrMark`
calculus, banked but fiddly; (ii) the relator-word expansion of `graphPullback` is long but
mechanical; (iii) matching the resulting explicit quadratic against `q̄`/`qDouble` needs the
concrete `En.dat`-normalizations (`IsEquivariantFactorSet` clauses).

### Route K (the paper's §6.3–6.5 Kummer word ledger)

The e4a design doc (§2) records the paper's own candidate derivation as going through the
§6.3–6.5 finite-word ledger (`WordCohBridge` + P-16c4 technology): identify
`(H¹(Γ_A,V), Q̄⁰)` with the pinned quadratic space via the deep-part/Shapiro coordinates
(`ShapiroLedger`/`RadicalEdgeGammaA` banked lanes).  More paper-faithful, but the repo's
§6.3–6.5 ledger is `AbsGalQ2`-side (Kummer theory!) — its `Γ_A`-mirror would be new.
**Recommendation: Route W** — everything it needs is `Γ_A`-native and already banked
(e5 markings, c2/c4 word-H², e6 coordinates); Route K would first have to re-derive
Route W's word tools anyway.

⚠ STANDING WATCH-ITEM (inherited from e4/c1c): **re-read paper pp. 33 ((83)), 40–41
((126)–(128)) before freezing the exact un/ram form-identification** — the `q` vs `q_U`
dichotomy shape and the `U`-twist convention must come from the paper, not be guessed.

## 2. Brick decomposition (Route W)

* **A-1 (coordinates)**: `Z¹_{Γ_A,ρ'}(V) ⧸ B¹ ≅ V`-model in generator coordinates —
  extract from e6's `hZcard_gammaA` Stage-0 (the `VCocycle ≃ Z¹_cont(GA,V)` bridge +
  `z1Equiv` + `prop_5_15` cl. 2) as REUSABLE declarations (the `GaussZLocal.toZ1` pattern;
  e6 inlined them).  Deliverable: an explicit bijection `h1CoordGammaA : Z¹⧸B¹ ≃ V-model`.
* **A-2 (relator evaluation of `iotaB`)**: for a normalized continuous 2-cocycle `φ` on
  `Γ_A`, `iotaB φ = relatorValue φ` — package `card_H2_gammaA_le_two`'s injection as a
  COMPUTATION RULE (the `WordCoh2.CentExt` splitting ⟺ marking-corrected relator death;
  e5's `mlift_of_relatorFree_marking` is the Γ_A-side precedent, `Phase140GammaA:644`).
* **A-3 (the quadratic)**: expand `graphPullback (En.dat l h) ρ'₀ c` along the relator in
  the A-1 coordinates → the explicit `𝔽₂`-quadratic `Q̂(v)`; prove `Q̄⁰ ∘ h1CoordGammaA⁻¹ = Q̂`
  (the gauge-normalization step; `graphPullback_shift_mem_B2` absorbs the `out`-choices as
  in `QZeroBar_eq_Q0loc`).
* **A-4 (form identification + count)**: `Q̂ = q̄` (unram: `hunram : ∀ v, c tameTau • v = v`
  collapses the twist) / `Q̂ = qDouble q̄ (U•·)`-congruent (ram); conclude via
  `gaussSum_eq_of_arf_eq` + the landed Arf pins; assemble
  `gaussZResidue_gammaA_{unramified,ramified}` mirroring `GaussZFinal` verbatim
  (its per-lift `hpack` shape, the σ-free finiteness from `hZcard_gammaA`, the dual-key
  `letI` idiom — gotchas banked on the e4a row).

Est. total ~1200–2500 ln; A-2 is the F-heavy brick (the only genuinely new device);
A-1/A-3 are mechanical against banked tech; A-4 mirrors `GaussZFinal`.

## 3. Interface pins (verified this session)

| decl | where | note |
|---|---|---|
| `QZero` | `VLiftCount.lean:589` | `iotaB ∘ graphPullback`, generic Γ |
| `iotaB`, `iotaB_eq_zero_iff` | `PhaseObstruction.lean:51` | B²-indicator |
| `gaussZ_reduction [Finite Z¹]` | `GaussZReduction.lean:237` | σ-free (this session) |
| `toZ1`/`ofZ1`/`h1OfVQuot`(+inj/surj) | `GaussZLocal.lean` §Bridge | generic Γ ✓ |
| `hZcard_gammaA` | `Phase140GammaA.lean:60` | needs `hsimple`/`hVne`/`hnt` |
| `card_H2_gammaA` | `CardH2GammaA.lean:214` | `#H²(Γ_A,𝔽₂) = 2` |
| `card_H2_gammaA_le_two` | `WordCoh2.lean:1545` | the ↪𝔽₂ device (A-2 source) |
| `mlift_of_relatorFree_marking` | `Phase140GammaA.lean:644` | e5-marking Γ_A precedent |
| `gaussSum_eq_of_arf_eq` | `PhaseGaussLIndep.lean:56` | Arf ⟹ Gauss |
| `arf_qbar_eq_one_of_unramified` | `PhaseGaussLIndep.lean:79` | unram Arf pin |
| `lemma_6_8` cl. 4 / `prop_6_9_unramified` | `SectionSix.lean:240/303` | ram/unram pins |
| `GaussZFinal.gaussZResidue_local_*` | `GQ2/GaussZFinal.lean` | the shape to mirror |

## 4. Gates

New leaf(s) off `Phase140GammaA`/`GaussZReduction`/`WordCoh2`; expected axioms:
A-1/A-2/A-3 std-3; A-4 std-3 (the Arf pins are proved).  NO new axioms.  The final
`gaussZResidue_gammaA_*` join the ThmFourTwo supply next to `gaussZResidue_local_*`.
