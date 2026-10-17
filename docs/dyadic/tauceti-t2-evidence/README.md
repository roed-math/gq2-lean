# T2 recon evidence (dyadic Tau Ceti discharge: B5-K, B10-K)

Scratch Lean files written by the T2 recon of the dyadic campaign, kept as starting points for
the tickets A1-K, B5-K and B10-K. The memo [`../tauceti-discharge-recon.md`](../tauceti-discharge-recon.md)
explains every file. These are **prototypes, not library code**. They sit outside every
`lean_lib`, so nothing builds them. They are not module-imported by anything, and they cannot
import each other, so each file is self-contained and repeats the pieces it needs from the files
before it. Each ticket must redo the work in its own `GQ2/TauCeti/<id>.lean` under the board
protocol: module style, no top-level `open TauCeti`, statements stated once, no duplicate public
names. All of them use the namespace `GQ2.TauCetiBridge`, so check the names before landing them.

Status at Tau Ceti `706344c35`, Mathlib `cfc55fc58` and Lean `v4.35.0`, re-checked when written:

- every file elaborates with `tools.sh chk <file>` from the worktree root (this is `lake env lean`
  with the lakefile's options and the Tau Ceti cache environment);
- no file contains `sorry`;
- every `#print axioms` in them prints exactly `propext, Classical.choice, Quot.sound`.

| file | lines | elaboration | contents |
|---|---|---|---|
| `bridge/bridge.lean` | 250 | ~20 s | **A1-K, light imports.** It covers four things. (1) The norm ↔ valuation bridge: `vle_iff_of_isEquiv`, which is generic and comes from Tau Ceti's uniqueness of the extended valuation; `normValuation`; `isEquiv_normValuation`; `vle_iff_norm_le`; `valuation_le_iff_norm_le`; `valuation_eq_iff_norm_eq`. (2) Normalized valuations: units (`normalizedValuation_eq_one_of_norm_eq_one`), gq2's spectral uniformizers (`normalizedValuation_eq_ofAdd_one_of_norm`) and `v_K(2) ≠ 0` (`normalizedValuation_two_ne_one`). (3) **Q3**: `osub_eq_integer`, the residue map `osubToResidue`, and `natCard_residueField_eq_two_pow : Nat.card 𝓀[↥K] = 2 ^ FF.f`. (4) Topologies: `isValuativeTopology_subtype` and `localTopology_eq`, which says Tau Ceti's topology on `↥K` equals the subspace topology. |
| `recipK/b5k.lean` | 441 | ~10 s | **B5-K except `ki_unramified`, under the heavy B5 imports.** It restates the bridge and adds `galKEquiv`, `abEquivK`, `recipK`, `continuous_recipK`, `denseRange_recipK`, `nuUrK` (with continuity and `nuUrK_recipK : ν(rec x) = −v_K(x)`), the unit and uniformizer clauses, and `inclAbK_recipK` (norm functoriality from `artinMap_norm`). For **Q1** it proves the generic `exists_level` (in a compact group, `ν(ker χ)` is a closed subgroup of `ℤ₂`, hence an ideal, hence `2^r ℤ₂` once nonzero), the witness `rec_K(2)` (`chiCycKAb_recipK_two`, `nuUrK_recipK_two_ne_zero`) and `exists_levelK`. `markedRecipOfKi` is the full bundle with `ki_unramified` taken as a hypothesis. |
| `kiunram/ki.lean` | 626 | ~35 s | **Q2 and all of B5-K.** It is a copy of `b5k.lean` plus five steps. (1) `nuUrK_toAbK_of_mem_inertia` shows inertia lies in `ker ν_ur`. (2) `fixes_of_chiCyc_mod_four` shows that `χ ≡ 1 (mod 4)` fixes `δi`. (3) `isUnramified_layerE` shows that inertia fixes `E = K(δi) ⊆ ↥Kˢᵉᵖ`, so `IsUnramified ↥K ↥E`. (4) `normValuationE`, `isEquiv_normValuationE` and `hasEqualNormValueGroups_of_isUnramified` give the bridge at `↥E` and then equal norm value groups. (5) `kiClause` combines them. **`markedRecipAt_tauceti K : MarkedRecip localReciprocity_tauceti K`** is complete. |
| `tameK/b10k.lean` | 495 | ~13 s | **B10-K, under the B10 imports.** It copies the bridge, Q3, `abEquivK` and `recipK`. The generic part works for any local field `L` with `hq : #𝓀[L] = q`: `iwasawaGeometricEquivTq : IwasawaGroupGeometric L ≃ₜ* Tq q` (B10's `Ttame` construction with `q` as a parameter) and `nuTq_iwasawaGeometricToTq` (the sign). At `↥K` it adds `phiK`, `wildK` (normal, closed, pro-2), `tameEquivK FF : GalK K ⧸ W ≃ₜ* Tq (qOf K FF)` and the single orientation lemma `nuTq_tameEquivK_mk`. `orientedTameQuotientOfRecip B hB FF : OrientedTameQuotientK B FF` works for any `B` with `B.recip = recipK K`. |
| `full/b5k_b10k.lean` | 963 | ~25 s | **Both inputs in one file**: `markedRecipAt_tauceti K` and `orientedTameQuotientAt_tauceti K FF : OrientedTameQuotientK (markedRecipAt_tauceti K) FF`. A comment records that the cast to the census-axiom type `MarkedRecip GQ2.localReciprocity K` fails outside `GQ2/Foundations/TauCetiInstance.lean`, because `localReciprocity` is not exposed there (memo finding 4). |
| `smokeK-check-output.txt` | 404 | n/a | The verbatim `#check` output of `GQ2/TauCeti/SmokeK.lean` (section `Signatures`), quoted in the memo. |

To run one (the Tau Ceti modules are already unpacked in this worktree; `tools.sh` is the T1 session
tooling described in `../tauceti-t1-bump-notes.md`, not part of the repository):

```bash
/tmp/claude-1006/-scratch-claudeM-gq2-tauceti/7313d86f-f71b-4b07-b403-b7c281f9491b/scratchpad/dyadic/tools.sh chk docs/dyadic/tauceti-t2-evidence/full/b5k_b10k.lean
```

or, to see the `#print axioms` lines:

```bash
export LAKE_CONFIG=$PWD/.lake/tauceti-lake-cache.toml LAKE_CACHE_DIR=/scratch/claudeM/gq2-tauceti/.lake/cache
lake env lean -DautoImplicit=false docs/dyadic/tauceti-t2-evidence/full/b5k_b10k.lean
```
