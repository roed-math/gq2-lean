# P-16d6e5 design — the Γ_A (136) residues  (F-design 2026-07-07, Fable → Opus execution)

**Deliverable**: `GQ2/RStageGammaA.lean` (new leaf; imports `GQ2.RStageLocal`,
`GQ2.WordCohBridge`, `GQ2.HalfTorsorGammaA`-adjacent) ending in

```
stageR136_gammaA_of_hcard  (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2) …
  : the (136) identity for blockFrameImpl at b := B.bA        -- mirror of stageR136_local
```

with `hcard_A` threaded as a hypothesis (supplied by **P-16d6e6**'s `card_H2_gammaA_eq_two`;
add the hypothesis-free `stageR136_gammaA` one-liner when e6 lands — this decouples e5 from e6).
Mirror `stageR136_local_of_hsep`/`stageR136_local` (`RStageLocal.lean:581/603`) verbatim with
`Γ := GammaA`, `hfg := gammaA_topologicallyFinitelyGenerated` (P-03 ✓, so `hfg` can even be
discharged here — unlike the local B1 reservation).

## 0. Two design simplifications vs the ticket row (verified against source)

The row scoped two "named §5-lane gaps".  **Both dissolve**:

* **Gap (i) — the (2,0)-perfectness — is already formalized content.**  `prop_5_8_right`
  (`FoxHeisenberg.lean`, PROVED) states `mixedB t x (d0 lam) = lam ((d1Fun t x).1 + (d1Fun t x).2)`.
  So the trace functional `Φ(lam) : (v₁,v₂) ↦ lam (v₁ + v₂)` kills `im (d1 t)` **exactly when**
  `d0 lam = 0`, i.e. `lam ∈ H0w = fixedPts` (`H0w_eq_fixedPts`, needs `t.Generates`).  `Φ` is
  trivially injective (`Φ(lam)[⟨v,0⟩] = lam v`), and `#H0w(R^∨) = #H2w(R)` from `IsSelfDual`
  clause 1 (`#H2w(A) = #fixedPts C (ElemDual A)`) + `card_addHom_zmod2`.  Injective +
  equinumerous finite ⟹ **`Φ` is a bijection onto `H2w(R)^∨`** — the separation, with NO new
  pairing content.
* **Gap (ii) — the twisted degree-2 continuous bridge — is eliminated.**  Do NOT extend
  `WordCoh2` to twisted coefficients and do NOT touch `H²(Γ_A, R)`.  `obs_zero_iff_lifts`
  (`RStageObstructionBuild`, PROVED, Γ-generic) already converts `obs g = 0` into **concrete
  continuous lifts through every scalar cover `Y/l ↠ Y/R`**.  The rest is a marking-level
  lifting argument at finite groups (§3), using only P-04/P-05 technology (`markC_admissible`,
  `NA_le_ker`, `quotientLift`) + the word-complex linear algebra of §0(i).

## 1. `hZcount_A` — mirror `hZcount_local` with the word bridge  (1 session)

`hZcount_local` (`RStageLocal.lean:149`) = [`RCocycle ≃ Z1 AbsGalQ2 (Additive ↥Blk.R)`-bridge,
built inline at lines ~205] + `card_Z1_eq` (prop_5_16 building block) + the
`fixedPts ↔ RCharSub` bridge + `blockRChar_card`.  The Γ_A version replaces ONLY the middle
count:

```
#Z1 GammaA R_ρ  =  #Z1w (markC ρ) R          -- z1Equiv (WordCohBridge:430, PROVED):
                                              --   Z1 GA A ≃+ Z1w (markC q), over
                                              --   (hq : Surjective q) (hA₂) (hcompat)
                =  #R² · #fixedPts C (R^∨)    -- IsSelfDual clause 2 via prop_5_15 (markC ρ):
                                              --   invoke as HalfTorsorGammaA:63-66 does —
                                              --   FoxH.prop_5_15 (markC ρ) adm.2.1 adm.2.2.1
                                              --     adm.1 hA₂ adm.2.2.2
                =  #R² · #D_R                 -- the fixedPts↔RCharSub bridge (mirror
                                              --   RStageLocal's) + blockRChar_card ✓
```

Notes for the executor:
* `ρ : GammaA → C := (piBC-composite of g₀'s lower map)` — same shape as `RStageLocal`'s;
  the `RCocycle ≃ Z1` bridge construction at `RStageLocal.lean:205` is Γ-generic in structure;
  transplant with `AbsGalQ2 → GammaA` (the file stated it inline at AbsGalQ2 — copy, don't
  import-generalize, to avoid touching the landed local file).
* The GA-action instances: `DistribMulAction.compHom … ρ.toMonoidHom` + `hcompat := fun _ _ =>
  rfl` + `ContinuousSMul` via the discrete-factorization — copy the `HalfTorsorGammaA:24-45`
  `letI` block verbatim.
* The admissibility bundle `adm : (markC ρ).Admissible` = `markC_admissible hρ_surj`
  (`WordCohBridge:89`); surjectivity of `ρ` from the boundary lift's surjectivity (the
  `rhoPrime_surjective`/`BoundaryLifts ⊆ ContSurj` pattern, `Half139Local`).
* `hA₂ : ∀ a : Additive ↥Blk.R, a + a = 0` from `hR2` (lemma_7_2 clause, threaded like the
  local file's `hR2`).
* `htriv_A (γ : GammaA) (m : ZMod 2) : γ • m = m := rfl`-pattern (mirror `htriv_local`,
  `RStageLocal.lean:282`).

## 2. `hsep_hom_A` — the marking-level route  (the main work, ~2–3 sessions)

Target statement (mirror `hsep_hom_local`, `RStageLocal.lean:307`, with the `hcard_A` variable):

```
theorem hsep_hom_gammaA (hE2 …) (hRK) (hR2) (hcard_A : Nat.card (H2 GammaA (ZMod 2)) = 2)
    (b := B.bA …) (F) :
    ∀ g : BoundaryLifts b F (blockFrameImpl T Blk hE2).TB,
      obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2) htriv_A hcard_A g.1.1 = 0 →
      ∃ φ : ContinuousMonoidHom GammaA Y, ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ
```

(`obs`'s `htriv`/`hcard` arguments are Props — proof-irrelevant, so the variable `hcard_A` is
interchangeable with e6's eventual theorem.)

### The lemma DAG

**L1 (general-extension relator correction) — the heaviest piece.**  For a finite group `Y'`
with abelian normal `R' ◁ Y'`, a 4-tuple `ŷ : Fin 4 → Y'`, and corrections `r⃗ : Fin 4 → R'`:
the tame/wild relator values of `(rᵢ·ŷᵢ)` and of `ŷ` (both computed by `Words.lean`'s finite
reading — `Marking.tameRelator`/wild analog on the `Marking Y'` given by the tuples) differ by
exactly the `d1Fun` rows:

```
tameValue (r⃗·ŷ) = (d1Fun-tame-row of r⃗) * tameValue ŷ        -- in Y', the factor in R'
wildValue (r⃗·ŷ) = (d1Fun-wild-row of r⃗) * wildValue ŷ
```

where the action in `d1Fun` is conjugation by the `ŷᵢ` (which, at the intended instance,
factors through `C = Y/K` — matching `d1Fun (markC ρ)`'s action; state L1 with the action
"conj by ŷᵢ" and add a small transport to the `markC ρ` action via
`RStageLocal.conj_eq_of_mk_eq_K`).  Prove by the same word-expansion as FoxH's
`mixedB_tameRow`/`mixedB_wildRow` (the split `WordLift` structure is never used in those
computations' first-order bookkeeping; the `ω₂`-power correction `(r·y)^{ω₂} = P(r)·y^{ω₂}`
with `P` the norm idempotent is Appendix A (157) — mirror FoxH's power lemma).  **Risk: the
wild row is long**; budget accordingly and consider mirroring `mixedB_wildRow`'s proof
skeleton line-by-line.

**L2 (`d1Fun` naturality).**  For a `C`-equivariant `f : A →+ A'`:
`d1Fun t (f ∘ r⃗) = (f × f) (d1Fun t r⃗)`.  Trivial induction over the closed-form rows.

**L3 (the trace-span package)** — all quick, from §0(i):
* `Phi (lam : H0w (R^∨)) : H2w (markC ρ) R →+ ZMod 2`, `[v] ↦ lam (v.1 + v.2)` — well-defined
  by `prop_5_8_right` + `lam ∈ ker d0`;
* `Phi_injective` (evaluate at `[⟨v, 0⟩]`);
* `Phi_bijective` from `IsSelfDual.1` (via `prop_5_15 (markC ρ) …`) + `H0w_eq_fixedPts` +
  `card_addHom_zmod2` + `Finite.injective_iff_bijective`-style counting;
* `trace_kills_im_trivial` : for the TRIVIAL module `𝔽₂`, `(v.1+v.2) = 0` on `im (d1 t)` —
  `prop_5_8_right` at `A := ZMod 2` with `lam := id` (`d0 id = 0` since the action is trivial);
* **`sep_word`** (the separation): `v : R × R` with
  `∀ d ∈ fixedPts C (R^∨), (d v.1, d v.2) ∈ ((d1 t).range.map (d × d)-image sense)` — phrase as
  `(d ∘ ·) ∘ v ∈ (d1 (𝔽₂-triv)).range` via L2 — implies `v ∈ (d1 t).range`.
  Proof: for each `lam ∈ H0w(R^∨)` (= invariant by `H0w_eq_fixedPts`), `lam(v.1+v.2) =`
  sum-of-coords of the pushed element `∈ im d1(𝔽₂)` `= 0` by `trace_kills_im_trivial`; so
  every `Phi(lam)` kills `[v]`; by `Phi_bijective` every functional kills `[v]`; a finite
  elem-2 group with all functionals vanishing is `0` (`exists_addHom_ne_zero`-complement,
  already used in `bijective_cup`'s proof — reuse), so `[v] = 0`.

**L4 (per-cover data extraction).**  From `obs g = 0`:
`obs_zero_iff_lifts (blockFrameImpl …) (blockRObstructionData …) htriv_A hcard_A g.1.1 d hd`
gives, for each `d ≠ 0` (i.e. each `l = ker d ∈ DR∖{zeroDR}` via `blockToDR`), a continuous
`g_l : GammaA → (scalarCover l h).cover = Y ⧸ l.1` with `p ∘ g_l = g.1.1`.  Fix once a set-lift
`ŷ : Fin 4 → Y` of `g`'s marking (`g.1.1`'s images of the four `gammaGen` generators; lift
along `mk' Blk.R` by `Quotient.out`-choice).  For each `l`: `g_l`'s generator images and
`red_l ∘ ŷ` both lift `g`'s marking mod `l` ⟹ differ by `r̄⃗ : Fin 4 → R/l`; `g_l` is a hom ⟹
its relator values are `1` ⟹ by **L1 at `Y' := Y ⧸ l.1`** (kernel `R/l ≅ 𝔽₂` via `d`; trivial
action by `d`-invariance) + L2: `(d v₁, d v₂) ∈ im d1(𝔽₂-triv)` where `v := relator values of
ŷ ∈ R × R` (they lie in `R = ker (mk' Blk.R)` since `g`'s marking kills the relators in `B` —
`g.1.1` is a HOM, so its marking satisfies TameRel/WildRel in `B`).
  * Careful: `d` ranges over `RCharSub Blk ∖ {0}` = the invariant characters; the
    correspondence `d ↔ l = RCharKer d` is `blockToDR` (`BlockRStage`, ✓ incl.
    `blockToDR_coe`); `d = 0` needs no data (the `sep_word` hypothesis at `d = 0` is trivial:
    `(0,0) = d1(0)`).

**L5 (correct + descend).**  `sep_word` (L3) applied to L4's data: `v ∈ im (d1 (markC ρ_g))`
(action-transport per L1's note) ⟹ corrections `r⃗ : Fin 4 → R` with the corrected tuple
`x̂ᵢ := rᵢ⁻¹·ŷᵢ`-orientation killing both relators (sign bookkeeping per L1's exact form).  Then:
* `J := Subgroup.closure (range x̂)`; the `Marking ↥J` given by the corrected tuple:
  `Generates` ✓ (closure = ⊤ by construction), `TameRel`/`WildRel` ✓ (values are `1`),
  `Pro2Core`: `normalClosure {x̂₂, x̂₃}` in `J` maps onto the `B`-side wild closure
  (2-group, from `(markC g-surj).Admissible.2.2.2` — `markC_admissible`, `WordCohBridge:89`)
  with kernel ≤ `R ∩ J` (2-group, `hR2`); finite extension of 2-group by 2-group is 2-group
  (`Subgroup.card_eq_card_quotient_mul_card_subgroup`-count or `IsPGroup` extension — small
  lemma, may already exist near `MaxProP`).
* `f : F₄ → ↥J` continuous via `FreeProfiniteGroup.homEquiv .symm` on the corrected tuple;
  `(univMarking.map f).Admissible` ⟹ `NA_le_ker` (`GammaA.lean:232`) ⟹
  `quotientLift NA f …` ⟹ `φ' : GammaA → ↥J`; `φ := (J.subtype-comp) φ'`.
* `π_B ∘ φ = g.1.1`: two continuous homs `GammaA → Y/R` agreeing on the four topological
  generators (`π(x̂ᵢ) = π(ŷᵢ) = g(genᵢ)` since corrections ∈ `R`) — close by the
  `monoidHom_eq_of_topGen` pattern (`BoundaryMapsWitness:190`).

### Assembly

`stageR136_gammaA_of_hcard := blockStageR136 T Blk hE2 htriv_A hcard_A
  gammaA_topologicallyFinitelyGenerated B.bA F hsep_hom_gammaA hZcount_gammaA` — mirror
`stageR136_local_of_hsep`'s term (`RStageLocal.lean:596`).

## 3. Interface pin table (verified 2026-07-07)

| need | pinned name | where |
|---|---|---|
| word complex `H2w = (A×A) ⧸ (d1 t).range`, `H0w = ker d0`, `Z1w = ker d1` | `FoxH.H2w/H0w/Z1w` | `FoxHeisenberg.lean:485-508` |
| trace adjointness | `prop_5_8_right` (+`_left`) | `FoxHeisenberg.lean` (PROVED) |
| `#H2w = #fixedPts(R^∨)`, `#Z1w = #R²·#fixedPts`, (1,1)-pairing | `IsSelfDual` clauses via `FoxH.prop_5_15 (markC ρ) adm…` | `FoxHeisenberg.lean:1653`, invocation pattern `HalfTorsorGammaA.lean:63-66` |
| `H0w = fixedPts` (needs `Generates`) | `H0w_eq_fixedPts` | `Devissage.lean` (per its §39 note) |
| degree-1 bridge | `z1Equiv : Z1 GA A ≃+ Z1w (markC q)` | `WordCohBridge.lean:430` |
| pushed marking + admissibility | `markC`, `markC_admissible` | `WordCohBridge.lean:87-89` |
| `#Hom(A,𝔽₂) = #A` | `card_addHom_zmod2` | `GaussCount.lean` |
| functional separation on elem-2 | `exists_addHom_ne_zero` | (as used by `bijective_cup`, `LocalLiftingDuality`) |
| obs → per-cover lifts (Γ-generic) | `obs_zero_iff_lifts` | `RStageObstructionBuild.lean:358` |
| character ↔ cover index | `blockToDR`, `blockToDR_coe`, `RCharKer_*` | `BlockRStage.lean` |
| descent to `Γ_A` | `NA_le_ker` (`GammaA.lean:232`), `quotientLift`, `FreeProfiniteGroup.homEquiv` | P-04/P-05 |
| `Admissible` fields | `Generates ∧ TameRel ∧ WildRel ∧ Pro2Core` (`Pro2Core = IsPGroup 2 (normalClosure {x₀,x₁})`) | `Words.lean:117-120` |
| topological-generator agreement | `monoidHom_eq_of_topGen` pattern | `BoundaryMapsWitness.lean:190` |
| C-action on R, `R` abelian, conj-descent | `rCommGroup`, `conj_eq_of_mk_eq_K`, `conjC_smul_of_mk` | `RStageLocal.lean:46-123` (reuse via import) |
| local mirror (statement shapes) | `hZcount_local:149`, `htriv_local:282`, `hsep_hom_local:307`, `stageR136_local_of_hsep:581` | `RStageLocal.lean` |

## 4. Execution order (Opus)

1. **File skeleton** + `htriv_A` + the action/`letI` block + `hZcount_gammaA` (§1) — lands a
   verifiable increment; `lake build`, `lean_verify` (expect std-3, no B — the word side is
   axiom-free; `prop_5_15` is std-3).
2. **L2, L3** (small, independent of L1) — the trace-span package; verify `Phi_bijective`.
3. **L1 tame row**, then **L1 wild row** (the long one) — mirror `mixedB_*Row` proofs.
4. **L4 + L5 + `hsep_hom_gammaA`** assembly.
5. `stageR136_gammaA_of_hcard`; board + allowlist hygiene (new file stays sorry-free
   throughout — build increments in a scratch section if needed).

Risks: (a) L1-wild length — if it stalls, land everything else + `hsep_hom_gammaA` reduced to
the single L1-wild statement (hypothesis-threaded), and split a micro-ticket; (b) the
`Marking`-vs-tuple plumbing in L1 (Words' relator evaluation is on `Marking Y'` records —
define the corrected marking record directly); (c) orientation/sign conventions in L1 (`rᵢŷᵢ`
vs `ŷᵢrᵢ`; pick the one matching `d1Fun`'s rows — check against `d1_tame`'s closed form,
`FoxHeisenberg.lean:513`).

## 5. Status

F-design COMPLETE (this doc).  No `Enrichment`/`BoundaryMaps` amendments, no new axioms, no
`WordCoh2` extension needed.  e5 is **O-ready**; only e6's `hcard_A` is consumed, and only at
the final one-liner (decoupled via `stageR136_gammaA_of_hcard`).
