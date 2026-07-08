# P-16d6e4aA-P4 — the c3-G0 package derivation: REFUTATION + the head-inflation reshape

**Status: RESHAPE VERDICT (Fable, 2026-07-08).**  The frozen `TamePackage{Unram,Ram}` /
`hpack` shape (`ρ.1.1 = c ∘ tameA` with `c : Ttame → RF.YC`) is **not block-derivable — it is
unsatisfiable at a positive-measure class of frames** (§1).  The paper never claims it: §6 runs
over the *faithful tame image* `H_V` (p. 25, "the uniqueness assertion is deliberately made over
the faithful image H_V"), and every lower map enters §9.3 only through the inflated base class
κ⁰.  The correct Lean shape is the **head-inflation reshape** (§2): make the enrichment's
`dat` *definitionally* a `FactorSet.reindexHom` pullback of a faithful-head-level datum, after
which the tame factorization of every boundary lift is **free at the head** — it is literally the
first component of the boundary equation — and every package field dissolves.  §3 gives the
component-by-component reuse map (almost everything is banked), §4 the P5 impact, §5 effort.

This supersedes the A-4.6a `TamePackageUnram/Ram` + `gaussZ_obtain_of_tamePackage*` route as the
endgame (those theorems stay landed and true — they are just not witnessable per block; do NOT
build P5 on them).

---

## 1. Refutation: why `hpack` cannot be derived (and is false with lifts present)

Fix the R-lane context: `RF := blockFrameImpl T Blk hE2`, `C := RF.YC = Y ⧸ Blk.K`,
`L_C := L_Y/K = RF.TC.LY`, and a boundary lift `ρ : BoundaryLifts B.bA F RF.TC`
(`BoundaryFrame.lean:350`: a continuous **epi** `Γ_A ↠ Y/K` with the boundary equation).

The boundary equation (`IsBoundaryLift`, `BoundaryFrame.lean:343`) pins, for every `γ`:

```
(TC.piY (ρ.1.1 γ), TC.thetaY (ρ.1.1 γ)) = F.frameMap (B.bA γ)
                                        = (F.alpha (B.tameA γ), F.psiBar (B.pro2A γ))
```

(second equality: `frameMap (t,p) = (α t, ψ̄ p)` at `BoundaryFrame.lean:293` +
`bA_apply_coe`, both `rfl`).  Consequences:

* **Head component**: `TC.piY ∘ ρ.1.1 = F.alpha ∘ B.tameA` — the head-composite of *every*
  boundary lift is the *same* tame-factored map.  (This is the engine of §2.)
* **θ component at a wild generator**: `TC.thetaY (ρ.1.1 x₀) = F.psiBar piX0` (using
  `B.pro2A_x0 : pro2A x₀ = piX0`, `tameA_x0 : tameA x₀ = 1`).

Now suppose a package witness existed, i.e. for every `ρ` some `c : Ttame → RF.YC` with
`ρ.1.1 = c ∘ B.tameA`.  Then `ρ.1.1 x₀ = c (tameA x₀) = c 1 = 1`, hence
`TC.thetaY (ρ.1.1 x₀) = 1`, hence **`F.psiBar piX0 = 1`**.  But `thm_4_2` quantifies over *all*
frames `F`, and `piX0` is a free-generator image in `PiBd` (nonzero in the Frattini quotient), so
frames with `ψ̄(piX0) ≠ 1` exist for any decoration group `E` with `#E ≥ 2`.  At such a frame the
package is constructible only if `BoundaryLifts B.bA F RF.TC` is *empty* — and emptiness is not
block-derivable either (a lift may exist sending the `x₀`-class to a θ-detected element of
`L_C`; the wild image is only constrained to lie in `L_C` with the pinned θ-value).  The same
argument runs verbatim on the local side with `tameF`/`pro2F` and `W_F = ker tameF`
(`ρ(W_F) ≤ L_C` by the head equation + `wild_isMax`-side facts, with θ pinned by `ψ̄ ∘ pro2F`).

Even at ψ̄-clean frames the factorization does not follow: `ρ(wild) ≤ L_C ∩ ker θ_C` is a
normal 2-subgroup which no block hypothesis kills — this is the **same** structural point as the
e6/e7 amendment that removed `hfaith` from the residue interfaces ("a central 2-part of `Y`
outside `K` centralizes `V`", ThmFourTwo.lean:269-273).  `hfaith` at `RF.YC` is likewise
**false** whenever `K < L_Y`: `L_C ≠ 1` acts trivially on the simple module (normal 2-subgroup
on a simple `𝔽₂`-module has nonzero, hence full, fixed space) — so the local twins' `hfaith`
field is unwitnessable too, independently of the factorization problem.

**What IS true, uniformly and for free** (the paper's actual content):

1. `ρ(wild)` acts trivially on `Vmod` — indeed all of `L_C` does; the `Y/K`-action factors
   through the head `H` (**banked**: `SectionNine.blockHtame`, BlockEnrichment.lean:222, via
   `FoxH.lemma_5_12`; the `ActsThroughTame` witness is `π := lift of T.piY through K = TC.piY`,
   generators `α σ, α τ`).
2. The Γ-action on `Vmod` through *any* boundary lift is the **fixed** tame action
   `α ∘ (tame coordinate of b)` — pinned by the head equation.  Hence the un/ramified
   **dichotomy is ρ-uniform and source-uniform**: it is the intrinsic disjunction
   "`α(tameTau)` acts trivially on `V` or not" (well-defined on the head since `L_C` acts
   trivially), decidable by `by_cases` at the consumer — *not* a package field.

## 2. The reshape: head-inflated `dat` (paper Lemma 6.3, taken seriously)

The only ρ-sensitivity of the base form beyond the action is the correction cochain:
`QZero DD ρM cc = iotaB (graphPullback DD.dat ρ.1.1 cc.c)` (VLiftCount.lean:589), and
`graphPullback` consumes `dat` through `f` (V-arguments only) and `m` at `ρ.1.1 γ`-slots.
The landed `kappa0_exists` proof (SectionNine.lean:1352, **proved**, P-17e5) already *ends* with
`IsEquivariantFactorSet.comapHom hdat π hπcompat` — i.e. the constructed datum has
`m = m_H ∘ π`, inflated through the head — but the existential statement forgets it, and
`blockKappa0 = (kappa0_exists …)` enters `blockEnrichment.dat` via `.choose`, making the
inflation property unrecoverable.  Fix (no co-owned edits):

**New leaf** (`GQ2/BlockHeadDat.lean`, say), all pieces public in BlockEnrichment/KappaNormalForm:

1. Rebuild the head-action data concretely: `e : Y/L_Y ≃* H` (descend `T.piY`), the `H`-action
   on `V` (`blockActLY` transported along `e.symm`), `πC := TC.piY : Y/K →* H` with
   `∀ c v, c • v = πC c • v` (the `blockHtame` construction, inlined as *data*).
2. The **faithful head quotient**: `Kact := {h : H | ∀ v, h • v = v}` (subgroup, normal),
   `HV := H ⧸ Kact`, descended action (the literal A-4.5b device —
   `zeroCount_unramified_of_action`'s `K`-construction, GaussZFinalGammaA.lean:1149, public and
   generic in `C`), `hfaithHV` **by construction**, `projF := mk' Kact ∘ πC : Y/K →* HV`,
   `cF := mk' Kact ∘ (e-side α) : Ttame → HV` continuous (discrete target) and surjective.
3. `datHV l h := (kappa0_exists_tame …).choose` at `HV` (KappaNormalForm.lean:1097,
   **sorry-free**): `hgen` = images of `α σ, α τ` generate (`gen_ttame_quotient` + closure-map),
   `hrel` = image of `tame_relation`, `q := En.qbar l h` (V-side unchanged), invariance/
   simplicity transported along the surjections (the `kappa0_exists` proof's own transport
   steps, replayed).
4. **`blockEnrichmentD F := { blockEnrichment T Blk hE2 F with dat := fun l h => (datHV l h).reindexHom projF, hdat := … }`**
   (record-update: every other field — `Vmod`, action, `q`, `qbar`, descents — identical).
   `hdat` = `IsEquivariantFactorSet.comapHom (datHV-spec) projF (compat)` re-expressed at
   `reindexHom` (they produce the *same* `FactorSet`: `⟨f, m ∘ projF⟩` — `rfl`-level).
   Side fact for consumers, `rfl`: `(blockEnrichmentD F).dat l h = (datHV l h).reindexHom projF`.

**Why this dissolves the packages.**  For any boundary lift `ρ` (either source):

```
QZero cc = iotaB (graphPullback ((datHV l h).reindexHom projF) ρ.1.1 cc.c)
         = iotaB (graphPullback (datHV l h) (projF ∘ ρ.1.1) cc.c)     -- graphPullback_reindexHom
```

(ShapiroDeepness.lean:127; hφ = the action compat from steps 1–2), and
`projF ∘ ρ.1.1 = cF ∘ (tame coordinate of b)` — **the boundary equation's first component**,
composed with `mk' Kact`.  So the evaluation runs at `C := HV` with the *fixed* surjection
`cF`, where: tame factorization is `rfl`-level, `hfaith` is true by construction, the wild
slots are literally `1` (`projF (ρ x₀) = cF 1 = 1`), and the dichotomy is `by_cases` at
`cF tameTau`.  The local side uses the same transport through `Q0loc_reindexHom`
(ShapiroDeepness.lean:151).

## 3. Reuse map (what is banked vs. new)

**Local twins** (`gaussZResidueD_local_{unram,ram}` at `blockEnrichmentD`) — *mechanical*:
replay `GaussZFinal.lean:56/132` (~70 lines each) with (i) the `letI` AbsGalQ2-action installed
along `projF ∘ ρ.1.1` instead of `ρ.1.1`, (ii) one `Q0loc_reindexHom` rewrite inserted in the
calc, (iii) `sum_sign_Q0loc_{unramified,ramified}` applied at `C := HV`, `c := cF`,
`hfac := congrArg (mk' Kact) ∘ (boundary-eq .1)`, `hfaith := hfaithHV`, `dat := datHV l h`.
The workers are generic in `(C, dat)` — **no P-15 chain re-proving**.  `hZcard_local`,
`gaussZ_reduction`, `QZeroBar_eq_Q0loc`, `h1OfVQuot` — all dat-free or dat-generic, reused
verbatim.  Ramified keeps `horient` at `R := localReciprocity` (B10′ witness at the consumer,
as in A-4.6a).

**Γ_A twins** (`gaussZResidueD_gammaA_{unram,ram}`) — *the A-4.5d/e assembly replayed once*
(new leaf; GaussZFinalGammaA untouched to avoid colliding with P3's surgical edit):

* Space side **verbatim** (dat-free): `finite_vcocycle_gammaA`, `h1CoordGammaA` (A-1),
  `x0Section_bijective_{split,ramified}` (A-4.1), `hfix_of_simple_nt`, the `secC` section
  cocycles, `markC θ`-admissibility, `map_tameRel`/`map_wildRel`.
* Value side: A-3 keystone `QZero_eq_relZPair_kappa0` at `dat := reindexHom …` (dat-generic),
  **plus one new transport**: `kappa0Cocycle ((datHV).reindexHom projF)` agrees pointwise with
  `kappa0Cocycle datHV ∘ (Sd-projection along projF)` (κ⁰-formula: `f` sees only V-arguments,
  `m` composes — the same 3-line computation as `graphPullback_reindexHom`), moved through
  `relZPair` by the A-3 `relZPair_comap`/`LevelFactor` machinery.  After the transport the
  marking slots are `(v-parts, cF-values)` with **wild slots `(v, 1)` on the nose** — the
  banked peels `relZPair_kappa0_fst_eq_zero` (A-4.2), `liftMark_kappa0_wildValue_fib_split`
  (A-4.3c), `liftMark_kappa0_wildValue_fib_ramified` (A-4.4b) apply at `C := HV` with
  `hx0cc/hx1cc := rfl`-level, `hτodd` via the odd tame-inertia order at `cF`, `htau/hU/hVS/htauf`
  via the A-4.5c/e pack lemmas at `hgen := generation of HV`.
* Counts at `HV`: `hfaith` is TRUE there, so `prop_6_9_unramified` applies *directly* — the
  A-4.5b/f actionizations become unnecessary on this route (they remain correct; the faithful
  quotient is now taken once, in the enrichment).  The ramified count is **the same P3
  interface** (`zeroCount_qDouble_ramified_of_faithful`-shaped, at `HV`): P3's isotypic-pack
  derivation discharges old and new routes alike — no scope change to P3.

**The G0-obtain** (replaces A-4.6a's package obtain): with `hsimple/hVne/hnt` (already derived
in the ThmFourTwo lane) and `m/hm/hcard` free via A-4.6b
(`exists_one_le_card_eq_two_pow_of_nonsingular` at `En.hns` + `hVne`),

```
theorem gaussZ_obtain_blockD … :
    ∃ G0 : ℤ, (∀ l h, GaussZResidue B.bA F (blockEnrichmentD …) l h G0)
            ∧ (∀ l h, GaussZResidue B.bF F (blockEnrichmentD …) l h G0) :=
  by by_cases hd : ∀ v, cF tameTau • v = v
     · exact ⟨-(2^m), unram twins⟩
     · exact ⟨ (2^m), ram twins⟩      -- push-neg gives the ∃-witness form
```

**no package hypothesis at all** — the entire c3-G0 layer reduces to the enrichment swap.

## 4. P5 impact (the ThmFourTwo swap)

P5 changes `En := SectionNine.blockEnrichment T Blk hE2 F` to `blockEnrichmentD` **throughout
the R-lane block** of ThmFourTwo (the obtain + the `prop_8_9` call — `prop_8_9` is
En-generic; `blockHsimple`/`blockHnt` are `Vmod`-level and `blockEnrichmentD` shares `Vmod` and
the action *fields verbatim* via record-update, so they transport unchanged), then closes the
sorry with `gaussZ_obtain_blockD`.  Nothing else in ThmFourTwo moves.  `horient` enters as the
B10′ witness (`TameOrientationWitness.tameFHom_tameUnitOrientation`) as already planned.

## 5. Effort and sequencing

| Piece | Content | Est. |
|---|---|---|
| P4b (substrate) | `BlockHeadDat.lean`: head-action data, `HV`, `datHV`, `blockEnrichmentD`, `dat_eq`, the κ-transport lemmas (`kappa0Cocycle`-reindex, both `graphPullback` transports are banked) | ~300–400 ln, 1 session |
| P4c (local) | the two local twins replayed at `blockEnrichmentD` | ~200 ln, ½ session |
| P4d (Γ_A) | the A-4.5d/e assembly replayed at `HV` (all cells banked; one new `relZPair`-transport) | ~500–700 ln, 1–2 sessions |
| P4e (obtain) | `gaussZ_obtain_blockD` (`by_cases` + A-4.6b) | ~80 ln, with P4c/d |
| P5 | unchanged in scope, now hypothesis-free | as ticketed |

The ramified-count sorry (P3's interface) is the **only** mathematics remaining on the whole
chain, unchanged in shape.  Axiom budget: unchanged (std-3 + the sanctioned B-census; no new
axioms; `kappa0_exists_tame` is sorry-free).

## 6. Verification trail (Lean-level anchors)

* `frameMap` head/θ split: BoundaryFrame.lean:293-296; `bA_apply_coe`/`bF_apply_coe` :437/:440.
* `tameA_x0/x1 = 1`, `pro2A_x0 = piX0`: BoundaryFrame.lean:392-397.
* `BoundaryLifts`/`IsBoundaryLift`: BoundaryFrame.lean:343-353.
* `L_C` acts trivially / action through `H`: `blockLY_smul_eqY`, `blockActLY`, `blockHtame`
  (BlockEnrichment.lean:180-273; `π = lift T.piY through K` — same map as `TC.piY` in
  `blockFrameImpl`, BlockFrameImpl.lean:72).
* `QZero = iotaB ∘ graphPullback dat ρ.1.1`: VLiftCount.lean:589 + `rho0_descData_rhoPrime`
  (Phase140Assembly.lean:107).
* `FactorSet.reindexHom` + `graphPullback_reindexHom` + `Q0loc_reindexHom`:
  ShapiroDeepness.lean:117/:127/:151.
* `IsEquivariantFactorSet.comapHom` (= inflation, Lemma 6.3's step): SectionNine.lean:1137;
  `kappa0_exists` proved via it :1352-1375; `kappa0_exists_tame` sorry-free
  (KappaNormalForm.lean:1097; file has 0 sorries).
* A-4.5b actionization cells (public, generic in `C`): GaussZFinalGammaA.lean:1149/:1220/:1258.
* Paper: §6.1 p. 25 (faithful image H_V; "after inflation … remains part of the target-side
  affine data"), Prop 6.5/(82)–(83) p. 25-26, Prop 6.9 p. 28, §9.3 pp. 45-47 ("G(Q⁰) is the
  common base Gauss sum supplied by propositions 6.9 and 6.18").
