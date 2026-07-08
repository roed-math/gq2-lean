# P-16d6e4aA-P4d/P4e handoff — the Γ_A twins at `blockEnrichmentD`, and the obtain

**Context**: read `docs/p16d6e4aA-p4-tame-package.md` first (the P4 refutation + head-inflation
reshape).  P4b (`GQ2/BlockHeadDat.lean`) and P4c (`GQ2/GaussZFinalD.lean`) are LANDED: the
head-inflated enrichment `blockEnrichmentD` (dat := `(blockDatHV).reindexHom blockProjF`,
`_dat_eq` = rfl) and the two hpack-free LOCAL twins `gaussZResidueD_local_{unramified,ramified}`
(axiom footprints = the baseline twins', no sorryAx).  P4d = the Γ_A twins; P4e = the obtain.
⚠ Do NOT edit `GQ2/GaussZFinalGammaA.lean` (P3's agent owns its one remaining sorry) — new leaf
(`GQ2/GaussZGammaAD.lean`, say), importing GaussZFinalGammaA + BlockHeadDat + GaussZFinalD.

## P4d targets

```
theorem gaussZResidueD_gammaA_unramified … (hunram : letI := blockPS_commGroup Blk; letI := headAct T Blk
    ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v = v) :
    GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h (-(2 ^ m : ℤ))
theorem gaussZResidueD_gammaA_ramified   … (hram : … ∃ v, F.alpha tameTau • v ≠ v) :
    GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h (2 ^ m : ℤ)
```
Hypothesis shapes exactly as P4c's local twins (hsimple/hVne/hnt at `EnD`, m/hm/hcard, the
head-level dichotomy under `headAct` — same letI-in-binder idiom).

## Shape of the proof (mirror `gaussZResidue_gammaA_unramified`, GaussZFinalGammaA:2106-2136)

**Front half — verbatim** (dat-free, action-level): `intro ρ`; `ρM := RF.rhoPrime B.bA F
(EnD.radData l h) rfl ρ`; `finite_vcocycle_gammaA B.bA F EnD l h ρ hsimple hVne hnt`;
`hsurjρ'` from `ρ.1.2` + `rho0_descData_rhoPrime`; `hfix := hfix_of_simple_nt`;
`gaussZ_reduction htriv_gammaA hfix` reduces to `∑ᶠ x, sign (QZeroBar (EnD.descData l h) ρM
htriv_gammaA x) = ∓2^m` — **the seam**.

**The seam — the A-4.5d/e assembly replayed at `HVq`** (this is the substantive work; every
cell is banked):

1. **Per-ρ HV data** (as in P4c): `ρHV := ⟨(blockProjF T Blk).comp ρ.1.1.toMonoidHom, …⟩`,
   `cF := ⟨(QuotientGroup.mk' (headActKer T Blk)).comp F.alpha.toMonoidHom, …⟩`,
   `hfacHV g := congrArg (⇑(mk' _)) (boundaryLift_head_gammaA T Blk hE2 B F ρ g)`.
   Slot values: `ρHV(σ-class) = cF tameSigma`, `ρHV(τ-class) = cF tameTau`,
   **`ρHV(x₀-class) = cF 1 = 1`, `ρHV(x₁-class) = 1`** (via `hfacHV` + `tameA_sigma/tau/x0/x1`)
   — the `hx0cc/hx1cc` of the peels, now rfl-level, NO hpack.
2. **Space side** (A-1/A-4.1, dat-free — apply at `DD := EnD.descData l h` verbatim):
   `h1CoordGammaA` + `x0Section_bijective_{split,ramified}` + the `secC := ofZ1 ∘ ofZ1w`
   section cocycles at `x0Supported`, `markC θ`-admissibility (`markC_admissible`),
   `map_tameRel`/`map_wildRel` for the mapped markings.  The A-4.5d letI-pack applies; note
   its gotchas (board row A-4.5d): GA-native `(fun x m => rfl)` for the keystone's htriv-binder
   (do NOT pass the GammaA-coerced `htriv_gammaA`); do NOT letI-shadow the global
   `DescData.actVmod`; `letI DistribMulAction GA (ZMod 2)` not haveI.
3. **Value side — the ONE new transport**: A-3's keystone `QZero_eq_relZPair_kappa0` (applied
   at `dat := (EnD.descData l h).dat`, generic ✓) gives the relator values in
   `CentExt (kappa0Cocycle ((blockDatHV …).reindexHom ⇑(blockProjF T Blk)) hdat)`.  Prove
   `kappa0Cocycle (dat.reindexHom ⇑π) hdat' = fun p => kappa0Cocycle dat hdat (sdMap π p.1, sdMap π p.2)`
   -shaped pointwise (the κ⁰-formula: `f` sees only V-arguments, `m` composes with `π` —
   the same 3-line computation as `graphPullback_reindexHom`), where `sdMap π : Sd C' V → Sd C V`
   is the C-coordinate map (a `MonoidHom` since the actions agree along `π` — mirror
   `graphSdHom`'s construction); then move through `relZPair` by the A-3 kernel-level
   `LevelFactor`/`relZPair_comap` machinery (GaussZRelatorGammaA — the same device that
   transported `(univMarking.map mk'_U).map φU`; remember the DEFEQ-but-rw-blind marking
   identification closes with explicit `rfl`).  Result: the relator values at the
   **`HVq`-marking** with slots `(v-parts, cF-values)`, wild slots `(v, 1)` exactly.
4. **Peels at `C := HVq`** (generic, banked): `relZPair_kappa0_fst_eq_zero` (A-4.2, tame value
   0), `liftMark_kappa0_wildValue_fib_split` (A-4.3c, `q(v)`) /
   `liftMark_kappa0_wildValue_fib_ramified` (A-4.4b, the Wall double) at
   `dat := blockDatHV`, `hdat := blockDatHV_spec`.  Hypothesis packs at HV:
   `hτodd` (odd order of `cF tameTau` — image of tame inertia, cf. `odd_orderOf_tameInertia`'s
   device), split `htau` from `hunram` (rfl through `hvAct_mk`), `hU`/`hVS` via the A-4.5c
   SplitPack lemmas at `hgen :=` the `hv_gen`-generation (their `C = ⟨s,t⟩, t trivial` shape),
   ram `htauf` via `tau_fixed_eq_zero_of_gen`, `hqg0` from `hv_inv`, `hV₂` from
   `exp_two_of_simple_of_card`-analog or `blockPS_exp2` directly.
5. **Counts at `HVq`**: `hfaith := hvAct_faithful` is TRUE — split: `prop_6_9_unramified`
   applies DIRECTLY (+ `zeroCount`→`finsum_sign_eq_neg` via the A-4.5a bricks; the A-4.5b/f
   actionizations are unnecessary on this route); ram: **the P3 interface**
   (`zeroCount_qDouble_ramified_of_faithful`-shaped at `HVq`) — P3's isotypic-pack derivation
   is stated at abstract faithful `(C, V)`, so it discharges this route identically.  Until P3
   lands, the ram twin carries that ONE sorry — put the new leaf on `SORRY_ALLOWLIST` and
   coordinate the interface NAME with P3's agent (do not fork the statement).
6. Reindex the sum over `Z¹⧸B¹` through `h1CoordGammaA ∘ x0Section` exactly as A-4.5d
   (`hcoordψ` collapses by ONE defeq-show + `toZ1_ofZ1`/`toZ1wHom_ofZ1w`; count =
   `finsum_eq_of_bijective`).

## P4c gotchas that WILL recur (banked list, board row P4)

Pin `continuous_of_discreteTopology (f := …)`; shadow the global
`QuotientGroup.instTopologicalSpace` at raw `Y ⧸ Blk.K` with the frame-valued cover-letIs;
re-key letIs for the `(HVq, EnD.Vmod/descData.Vmod)` and `(YC, raw-Additive)` instance cells;
NEVER hand-write a mixed-spelling `H1`/finsum type (convert the pinned value to the
`Z¹⧸B¹`-side with `rw [← hpinned]` so only full-defeq unification crosses spellings);
qualify `SectionEight.sign`; route `ρ.1.1 γ • v`-at-descData-`v` through a C0-typed
restatement of `blockProjF_compat`.

## P4e (after P4d) — the hypothesis-free obtain

```
theorem gaussZ_obtain_blockD [CompactSpace AbsGalQ2] … (hsimple hVne hnt) :
    ∃ G0 : ℤ, (∀ l h, GaussZResidue B.bA F (blockEnrichmentD T Blk hE2 F) l h G0)
            ∧ (∀ l h, GaussZResidue B.bF F (blockEnrichmentD T Blk hE2 F) l h G0) := by
  obtain ⟨m, hm, hcard⟩ := exists_one_le_card_eq_two_pow_of_nonsingular …  -- A-4.6b, from En.hns + hVne
  by_cases hd : letI := blockPS_commGroup Blk; letI := headAct T Blk
      ∀ v : Additive (↥Blk.P ⧸ Blk.S.subgroupOf Blk.P), F.alpha tameTau • v = v
  · exact ⟨-(2 ^ m), fun l h => gaussZResidueD_gammaA_unramified … hd,
                     fun l h => gaussZResidueD_local_unramified … hd⟩
  · push_neg at hd
    exact ⟨(2 ^ m), ram twins at hd⟩
```
The ramified local twin additionally takes `(R := localReciprocity)`,
`(horient := TameOrientationWitness.tameFHom_tameUnitOrientation)` — both global witnesses,
sanctioned census.  P5 then swaps `En := blockEnrichmentD` throughout the ThmFourTwo R-lane
(`prop_8_9` is En-generic; `blockHsimple`/`blockHnt` transfer — `Vmod`/`actV` fields are
kept verbatim by the record-update) and closes the G0-obtain sorry with
`gaussZ_obtain_blockD`.
