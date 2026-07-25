# R20 recon — the §5/§6 word-level parameter boundary for r_R

**Ticket:** R20 (read-only recon, P3). **Read from:** `~/claude/gq2-lean` (main checkout,
frozen Γ_A tower). **Writes:** this file only. **Consumers:** R21–R27 fill prompts, R26
assembly, R30/R31 interface refactor.

**One-line verdict.** The wild word couples the §5/§6 layer through exactly **one definitional
spine** — `Marking.wildValue` (Words.lean:121 relation / Basic.lean:48 element) and the objects
built from it (`d1Fun → d1 → Z1w/H1w/H2w`, and `mixedB`). Everything above that spine
(`IsSelfDual(W)`, the χ-maps, the LES, the cone dévissage, `prop_5_15`) is **generic in
`t : Marking C` and forwards `hw : t.WildRel` without ever unfolding the aux-word
factorisation**; everything at the spine's leaves (the evaluated Fox rows, the Heisenberg
central coordinates, the Stokes endpoint, the trivial-module Gram) **unfolds the specific
Γ_A word and needs fresh r_R proofs**. §6 (`SectionSix.lean`) and the deep-duality / ramified /
tame-representation packs are already abstract in `(q, U, dat, ρ)` and carry **zero** wild-word
coupling — reuse verbatim.

---

## 0. The coupling mechanism and the classification scheme

### 0.1 What "the word" is, in Lean

`Marking` (Words.lean:66) is the bare quadruple `(σ, τ, x₀, x₁)`; it is word-agnostic and
**shared** with Γ_R. The Γ_A relators are two derived predicates:

| decl | file:line | statement | Γ_R status |
|---|---|---|---|
| `Marking.TameRel` | Words.lean:118 | `τ^σ = τ²` | **unchanged** (r_R keeps the tame relation) — shared |
| `Marking.WildRel` | Words.lean:121 | `h₀·u₁⁻¹·(x₁^σ)·c₀ = 1` | **new** `WildRelR` (r_R word) |
| `Marking.Generates`,`Pro2Core` | Words.lean:124,128 | closure=⊤ / pro-2 core | **unchanged** — shared |
| `Marking.wildValue` | Basic.lean:48 | the element `h₀·u₁⁻¹·(x₁^σ)·c₀` | **new** `wildValueR` |
| aux words `sigma2,u,u0,u1,d0,z0,c0,g0,dg,hc,h0` | Words.lean:90–113 | the factor ledger of `wildValue` | **replaced** by r_R's factors (`x₀^σ`, `(x₀⁻³τ)^ω₂`, `x₁²`, `[x₁,x₁^σ₂]`) |

`sigma2 = σ^ω₂` (Words.lean:90) is generic (both presentations have `σ`) — it is **not** a
word-coupling marker, and `TameSimple.sigma2_pairing_operator_injective` reuses verbatim.

### 0.2 The definitional spine (the only place the word enters the complex)

```
Marking.wildValue  (Basic.lean:48)          -- the fixed Γ_A relator element
   │  used by
d1Fun (Basic.lean:334) = (tameValue.u, wildValue.u)   -- wild half = wildValue.u
   │        d1Fun_comp_d0 (Basic.lean:385) needs hw:WildRel  ⇒ wildValue = 1 ⇒ d¹∘d⁰ = 0
d1 (Basic.lean:378) → Z1w/B1w/H1w/H2w (Basic.lean:404–430)
mixedB (Heisenberg.lean:312) = tameValue.z + wildValue.z     -- the degree-1 pairing
```

**Key fact (verified):** `d1Fun`, `Z1w`, `H1w`, `H2w`, `mixedB` take `t : Marking C` as an
argument but **hard-reference the single fixed def `Marking.wildValue`** — there is *no*
relator-word parameter anywhere. Consequently `IsSelfDual t A` (Traced.lean:542),
`IsSelfDualW t A` (SelfDual.lean:37), all `chi*`/`delta*` maps, and `prop_5_15` are computed
from `t` **through** `wildValue`. Plugging a Γ_R marking into these still evaluates the **Γ_A**
word. This is the crux for Q2/Q6 (§2.2, §2.6 below).

### 0.3 Classification buckets used in this report

The task's A/B/C, refined with a **reuse-mode** tag that is the actual parameter boundary:

- **(A)** word-generic — no `wildValue`/`WildRel`/aux/complex-object in statement or proof.
  *Reuse verbatim.*
- **(B·fwd)** statement carries `hw : t.WildRel` and/or a spine object (`Z1w t`, `H2w t`,
  `mixedB t`, `chi* t`, `IsSelfDual(W) t`, `d1 t`), but the **proof only forwards `hw`** / uses
  `d¹∘d⁰=0` + functoriality + LES + finite linear algebra — **never unfolds the aux words**.
  *Re-instantiate over the r_R complex: NO new mathematics — either a mechanical clone or (better)
  one generalisation that parameterises the spine over the relator word (§2.6).*
- **(B·word)** the **statement itself** encodes the specific word or its evaluated closed form
  (`wildValue.u/.z`, `wildValueExp`, an aux word, the Γ_A Jacobian/Gram value). *NEW r_R proof —
  the genuine seams.*
- **(C)** statement generic in the module `A`, but the **proof unfolds the specific word**
  (via `liftMarking_wildValue_u`, `heisMarking_wildValue_z`, `prop_5_8`, aux-word closed forms).
  *NEW r_R proof.*

`B·fwd` is the plan's "re-instantiate / reuse verbatim / wired through" bucket; `B·word`+`C` are
the plan's "new, small — the four seams".

---

## 1. Per-file classification

### 1.1 Files that are entirely (A) — reuse verbatim, zero wild-word coupling

Grep-verified: **no** `liftMarking`/`heisMarking`/`mixedB`/`wildValue`/`WildRel`/aux-word tokens.

| file | content | note |
|---|---|---|
| `GQ2/DeepDuality.lean` (1395 ln) | abstract pairing-perp duality, `pairPerp`/`perpEquivDualQuot`/`card_equivHoms_deep`, Kummer mid/deep classes, `polarSelfDual` | (A) all decls |
| `GQ2/DeepDualityK.lean` (580 ln) | local Tate-duality-K, `pairingK`, conj-action | (A) all decls |
| `GQ2/RamifiedPack/Basic.lean`, `RamifiedPack/Descent.lean` | ramified isotypic rep theory (`actEnd`, `AdjoinRoot`, `frobEquiv`, `card_fixed_powOmega2`) — the split/ramified module inputs | (A) all decls; feeds `lemma_5_13_ramified`'s hypotheses generically |
| `GQ2/TameSimple.lean` (385 ln) | tame group theory + the ramified pairing operator | (A) all decls; **`sigma2_pairing_operator_injective`:303** = `1+U+U⁻¹` invertibility reused as-is by R24 |
| `GQ2/SectionSix.lean` (1056 ln) | §6 Gauss/determinant apparatus | (A) all decls — abstract in `(D:TateDuality, dat:FactorSet, ρ, q:V→ZMod 2, U:V≃+V)`; see §1.9 |
| `GQ2/Devissage.lean` (65 ln) | import/doc hub | no public decls |

`RamifiedPack.lean`, `Devissage.lean` are import shells (no classifiable decls).

### 1.2 `GQ2/FoxHeisenberg/Basic.lean` — the spine root + generic WordLift API

- **(A)** the whole `WordLift A C` group + functorial API and the `ω₂` calculus:
  `pow_u`:159, `powOmega2_u_of_trivial`:172, `powOmega2_u_of_oddFixedPointFree`:235,
  `powOmega2_u_zero`:202, `sum_pow_smul_eq_zero`:208, `norm_eq_zero_of_fixedPointFree`:223,
  `powOmega2_smul_of_trivial_mul`:250, `inv/mul/conjP/commP_*_trivial`:265–306, `map`:121,
  `baseEmbed`:134, `conj_baseEmbed`:143, `equivProd`:109. Also `ElemDual` + its action/eval
  (453–513), `d0`:326, `d1Fun_tame`:437, `H0w`:404, `B1w`:411. **These are exactly the
  `WordLift`/`ω₂` primitives the R21/R24 rows are assembled from — reuse verbatim.**
- **(B·word)** `Marking.wildValue`:48 (the word); `Marking.wildValue_eq_one_iff`:52;
  `Marking.map_wildValue`:65 (its naturality). → r_R needs `wildValueR`, `WildRelR_iff`,
  `map_wildValueR` (owned by R1 in `Roe/Words.lean` + a Roe `Basic`).
- **(B·fwd)** `d1Fun`:334, `d1`:378 (wild half = `wildValue.u`); `d1Fun_add`:345 (functorial);
  `d1Fun_comp_d0`:385 (proof uses `hw:WildRel ⇒ wildValue=1`, otherwise generic); `Z1w`:407,
  `H1w`:415, `H2w`:427 (+ their `AddCommGroup` instances), `h1wMk`:422. → r_R needs
  `d1Fun_R`/`d1_R`/`Z1w_R`/`H1w_R`/`H2w_R` built on `wildValueR.u` (proofs port verbatim).

### 1.3 `GQ2/FoxHeisenberg/WildRow.lean` (423 ln) — **R21 seam** (⟦prop:jacobian⟧, eq:jacobian)

Whole file is the evaluated Fox rows of the Γ_A aux words. **All decls (B·word) or (C)** — each
computes `(liftMarking t x).<auxword>.u` (or `.g_smul`) for a **Γ_A** aux word. Enumerated:

| decl | line | proves | generic ingredient reused |
|---|---|---|---|
| `liftMarking_u0_u`, `liftMarking_u1_u` | 41,54 | `D(uᵢ)=x₂+x₁ / x₃+x₁` (split) | `WordLift.powOmega2_u_of_trivial`:172 |
| `liftMarking_u0/u1_g_ramified`, `_u_ramified` | 76–111 | ramified `uᵢ` collapse | `powOmega2_u_of_oddFixedPointFree`:235 |
| `liftMarking_d0_u`, `_c0_u`, `_h0_u` | 123,267,230 | `D(d₀),D(c₀),D(h₀)` | `commP_u_of_trivial`:291, `conjP_u_of_*`:277,286 |
| `liftMarking_{g0,u0,u1,d0,z0,h0}_g_smul` | 175–206 | base-slice triviality of aux words | `WordLift.mul/inv/conjP_g_trivial` |
| `liftMarking_sigma2_g`, `_conjP_x1_sigma_u` | 144,163 | `σ₂`-slice, `D(x₁^σ)=S⁻¹x₃` | `conjP_g_trivial`, `pow_u` |
| **`liftMarking_wildValue_u`** | **277** | **split wild row `= x₁+(1+S⁻¹)x₃`** | assembly; **r_R: `L_w=Pb+(P+S⁻¹)c`** |
| `liftMarking_{d0,c0,h0}_*_ramified` | 306–354 | ramified aux offsets | as above |
| **`liftMarking_wildValue_u_ramified`** | **397** | **ramified wild row `= S⁻¹·x₃`** | **r_R: `L_w=S⁻¹c`** |

**R21 mirror rule:** replace the six Γ_A aux-word lemmas (`u0,u1,d0,z0,c0,h0`) by r_R's four
factors (`x₀^σ`, `(x₀⁻³τ)^ω₂`, `x₁²`, `[x₁,x₁^σ₂]`); the generic column comes from the same
`WordLift` API cited above. Expect **≪ 423 ln** (no `h₀` class-two word; `D(x₁²)=0`,
`D([x₁,x₁^σ₂])=0`). Paper proof: tex:508–538.

### 1.4 `GQ2/FoxHeisenberg/HessianRow.lean` (~800 ln) — **R22 + R24 seams**

Two roles. **(a) heisMarking central-coordinate ledger** for the Γ_A aux words (56–330) — all
**(B·word)**; **(b) the normal-form and pairing lemmas** (582–~800) — **(C)**.

(a) The per-aux-word coordinate lemmas (all `heisMarking_<aux>_<coord>` for `<aux> ∈
{h0,d0,c0,u1,g0,z0,dg,hc,sigma2}`, `<coord> ∈ {a,l,z,g_smul,g_eq}`): lines 47–193, plus
`heisMarking_h0_z`:205, `powOmega2_secHom_z`:274, `heisMarking_c0_z`:279, `heisMarking_u1_z`:299,
`heisMarking_conjP_x1_sigma_z`:310, `heisMarking_u1_a`:322, `heisMarking_h0_z_ramified`:403,
`heisMarking_c0_z_ramified`:493. **Generic ingredients (reuse):** `HeisLift.mul_z_of_trivial`
(Heisenberg.lean:226), `commP_z_of_trivial`:278, `conjP_z_of_slice`:271, `conjP_a/l_of_slice`,
`inv_a/l/z`, `secHom`. **(A) helpers within:** `surjective_smul_sub_of_fixedPointFree`:378,
`elemDual_fixedPointFree_of_fixedPointFree`:387, `powOmega2_secHom_a`:319.

| assembled decl | line | proves | Γ_R (R24) |
|---|---|---|---|
| **`heisMarking_wildValue_z`** | **331** | split Hessian wild summand `= λ(c)` | `x₁²` diagonal via `mul_z_of_trivial`; commutator via `commP_z_of_trivial` |
| **`heisMarking_wildValue_z_ramified`** | **535** | ramified `= λ((1+U+U⁻¹)c)` | ditto; operator invertibility = `sigma2_pairing_operator_injective`:TameSimple:303 |

(b) normal-form / split-case machinery: `wild_acts_trivially`:582 **(A)** (Pro2Core⇒x₀,x₁ act
trivially — about generators, not the relator); `d1Fun_tame_split`:594 **(A)** (tame row, `S⁻¹x₁`);
`b1w_split_shape`:605 **(A)** (`B¹`=d⁰ range); `heisMarking_tameValue_z_eq_zero`:619 **(A)**
(tame value in base slice). Word-coupled leaves:

| decl | line | class | proves (⟦lem:normalforms⟧/⟦prop:hessian⟧) |
|---|---|---|---|
| `lemma_5_13_split` | 647 | (C) | `Z¹={(a,0,c,0)}`, `B¹` shape — uses `liftMarking_wildValue_u` |
| `lemma_5_13_ramified` | 696 | (C) | unique x₀-rep — uses `liftMarking_wildValue_u_ramified` |
| `lemma_5_13_pairing_split` | 752 | (C) | pairing `=λ(c)` — uses `heisMarking_wildValue_z` |
| `lemma_5_13_pairing_ramified` | 775 | (C) | pairing `=λ((1+U+U⁻¹)c)` — uses `_z_ramified` |

R22 = the two `lemma_5_13_*` normal forms; R24 = the two `heisMarking_wildValue_z*` +
two `lemma_5_13_pairing_*`. Paper: tex:541–574 (normal forms), tex:634–674 (Hessian).

### 1.5 `GQ2/FoxHeisenberg/Traced.lean` (~700 ln) — **R23 seam** (⟦lem:stokes⟧) + generic Stokes

- **(A) generic Stokes/bridge/section infrastructure** (reuse verbatim): `traceD0/D2`:39,44,
  `markVec`:64, `freeMarking`:67, `lgHom`:145, `heisMarking_eq_map`:151, `liftMarking_eq_map`:159,
  `bridge_tame`:168, `stokesEval_tame_l`:173, `lift_markVec_tameValue`:179, `d0_eq_markVec`:188,
  `mixedB_tameRow`:196, `secHom/secWL/secWA`:233,242,370 + injectivity, `orderOf_dvd_exponent_heis*`:
  252–275, `stokesEval_tame_a`:393, `mixedB_tameRow_right`:415, `lemma_5_6`:474, `fixedPts`:533,
  `IsSelfDual`(def):542, `IsSimpleModTwo`:562, `lemma_5_12`:576, `classTwoCore/Identity*`:654–687.
- **(B·word)** the explicit-exponent word: `wildValueExp`:75 (body hard-codes the Γ_A ledger),
  `expMod2_wildValueExp`:97 (**the Stokes endpoint `(0,e,0,e+1)→(0,1,0,0)`**), `wildValueExp_map`:114,
  `wildValueExp_eq_wildValue`:122, `_of_dvd`:133, `bridge_wild`:217. → r_R: `wildValueExpR`
  (R1) + `expMod2_wildValueExpR` (**R23**, ~20 ln, must also land `(0,1,0,0)`).
- **(C)** the wild chain-map rows (generic statement, proof runs `wildValueExp`/`WildRel`):
  `lift_markVec_wildValueExp_eq_one`:286, `stokesEval_wild_l`:301, `mixedB_wildRow`:319,
  `prop_5_8_left`:349, `stokesEval_wild_a`:399, `mixedB_wildRow_right`:431, `prop_5_8_right`:452.
  → r_R: `mixedB_wildRow(_right)_R`, `prop_5_8_left/right_R` (**R23**).

**Note (Q4):** `IsSelfDual` **def** lives here (Traced:542) but is a spine object (§0.2) — its
r_R analogue `IsSelfDual_R` belongs with the R-complex, not R23.

### 1.6 `GQ2/FoxHeisenberg/Heisenberg.lean` (~545 ln) — mostly generic HeisLift API

- **(A)** the entire `HeisLift A C` group + API (the R24 engine): `zc/zcHom`:111–134,
  `conj_gen(_r)`:150,165, `commP_z_fiber`:181, `mul/inv/conjP_*_trivial`:204–290 incl.
  **`mul_z_of_trivial`:226, `commP_z_of_trivial`:278, `commP_a_of_trivial`:290,
  `conjP_z_of_slice`:271**; `heisMarking`(def):306; the Stokes core `stokesEval`:325,
  `expMod2`:330, `stokesEval_g/zero`:334,342, `freeExp`:382, `epsWord`:403, `stokesRhs(R)`:415,493,
  `stokesEval_eq_rhs(R)`:426,504, **`lemma_5_7_left`:445, `lemma_5_7_right`:523** (generic finite
  Stokes over an arbitrary free word — reused as-is by R23/R24), `conjPa/conjQlam`:363,463,
  `fgTame`:535, `expMod2_fgTame`:540.
- **(B·word)** **`mixedB`:312** = `tameValue.z + wildValue.z` — unfolds `wildValue` (§0.2). This is
  the pairing; r_R needs `mixedB_R = tameValue.z + wildValueR.z`.

### 1.7 `GQ2/MixedBilinear.lean` (419 ln) — **R25 seam** (⟦lem:trivial⟧ Gram) + generic bilinearity

- **(A)** Stokes bilinearity/independence (reuse): `stokesEval_{a,l}_indep`:31,41,
  `stokesEval_{a,l}_{zero_dual,zero_prim}`:51,56, `stokesEval_{a,l}_add`:61,74,
  `stokesEval_z_add_{left,right}`:87,100, `mixedB_add_{left,right}`:113,122 (bilinearity of
  `mixedB` — proof is generic), `conjP_z_of_alzero`:163, `heisLift_pow_{l,a}_z_zero`:362,372,
  `stokesEval_tame_z_trivial(_cocycle)`:136,153.
- **(B·word)/(C)** the trivial-module wild `.z` peel and the Γ_A Gram closed form:
  `heisMarking_x1sig_z_trivial`:177, `heisMarking_c0_z_cocycle`:197, `heisMarking_h0_z_cocycle`:220,
  **`heisMarking_wildValue_z_cocycle`:295** (`= y₂(x₂)+y₃(x₀)−y₀(x₃)+u₁.z`),
  **`mixedB_cocycle`:350** (the Γ_A Gram — the R25 target), `heisMarking_u1_z_of_{y3,x3}_zero`:387,405
  (the ω₂ scalar `u₁.z` confined to the (3,3) slot). → r_R (**R25**): `mixedB_cocycle_R` with the
  **cleaner** Gram `⟨(a,c,d),(a',c',d')⟩ = ac'+ca'+dd'` (paper eq:scalarform, tex:583; diagonal
  (3,3) `dd'`, no opaque ω₂ scalar).

### 1.8 `GQ2/MixedBObs.lean` (162 ln) — obstruction bridge

- **(A)** generic constructions: `kappaHeis`:39, `PhiHeis`:54, `mBaseMarking`:62,
  `mBaseMarking_eq_liftMarking`:69, `map_liftMark_mBase`:73.
- **(C)** `mixedB_eq_relZPair`:79 — uses `mixedB` + `Marking.map_wildValue`; r_R needs `mixedB_R`
  naturality.
- **(B·fwd via presentation objects)** `obs_inflation`:110 — proof is generic obstruction theory,
  but statement references `gammaGen`/`univMarking`/`NA` (Γ_A presentation objects; P0 clones R1/R3).

### 1.9 `GQ2/SectionSix.lean` (1056 ln) — §6 apparatus, all (A) (abstract in `(q,U)`)

Verified abstract: `Q0loc`:157, `graphPullback_mem_Z2`:166, `onePlusU`:212, **`lemma_6_6`:222**
(Wall doubling), **`lemma_6_8`:268**, **`prop_6_9_unramified`:328 / `prop_6_9_ramified`:381**,
the two-point/dihedral fixtures 425–575, `lemma_6_13_*`, `SemiProd`, `lemma_6_15_*`:672–714,
`lemma_6_16`:760, `deepPart`:844, `lemma_6_21`:922, `gammaEdge/inflScalar/shear/thetaPhase/
gammaCupA`:941–956, `lemma_6_22`:970. **None** reference `Marking`/`wildValue`. The word enters
§6 only at the **"Fox–Heisenberg design seam"** (docstring tex-anchor, SectionSix:203–205:
"Deriving (83) from the relator ledger is Prop 6.5") — i.e. `Q⁰_A = q` (split) / `qDouble q U`
(ramified). That derivation is **not** in SectionSix; it is the **R27** obligation feeding the
R24 Hessian into the abstract `qDouble`. `qDouble` itself is `GaussZ/FinalGammaA/Counts.lean`
(also abstract in `q,U`), **not** SectionSix:212 (that line is `onePlusU`) — the plan's
"qDouble SectionSix.lean:212" citation is imprecise; correct it in the R27 prompt.

### 1.10 `GQ2/TrivialSelfDual.lean` (263 ln) — **R25 base case** (⟦lem:trivial⟧)

- **(A)** `d0_of_trivial`:68, `elemDual_smul_trivial`:76, `card_fixedPts_elemDual_trivial`:83,
  `B1w_trivial_eq_bot`:165 (all use only the tame coboundary / dual module theory).
- **(C)** proof unfolds the split wild row / Γ_A Gram: `d1Fun_of_trivial`:45 & `d1_of_trivial`:61
  (use `liftMarking_wildValue_u`; for r_R still `(b,b)` — S=T=P=1 collapses both rows),
  `card_range_d1_trivial`:96, `card_H2w_trivial`:112, `card_Z1w_trivial`:124, `mem_Z1w_trivial_iff`:157,
  **`trivialSelfDual`:176** (the Gram perfection — uses `mixedB_cocycle`+`heisMarking_u1_z_of_*`).
  → r_R (**R25**): reprove `d1Fun_of_trivial_R`, the three card clauses, `trivialSelfDual_R` with
  `mixedB_cocycle_R`. (Card-clause proofs are mechanical once `d1_of_trivial_R=(b,b)` is known.)

### 1.11 `GQ2/DualityAssembly.lean` (585 ln) — the simple-case assembly (mix of A/B·fwd/C)

- **(A)** `card_fixedPts_elemDual_eq_one_of_nontrivial`:112 (dual module theory),
  `tau_split_or_ramified`:147 (TameRel + `wild_acts_trivially` — no wild relator),
  `elemDual_smul_trivial_of`:445.
- **(B·fwd)** generic given the normal form / complex: `card_H1w_of_normalForm`:42,
  `card_H0w_eq_one_of_nontrivial`:75, `card_H2w_and_Z1w_of_nontrivial_simple`:92,
  `x0mem_of_Z1wShape`:327, `normalForm_of_shapes`:334, `clause3_of_normalForm`:232 (takes
  normal-form + nondegeneracy as hypotheses; proof uses `mixedB_congr` — thin), **`prop_5_15`:574**
  (assembly: `prop_5_15_of_simple ∘ selfDual_of_simple`).
- **(C)** proof unfolds the word (via `liftMarking_wildValue_u(_ramified)`, `prop_5_8`,
  `lemma_5_13_*`): `mixedB_left_congr`:205, `mixedB_right_congr`:216, `split_shapes_of_wild`:298,
  `x0Supported_mem_Z1w_ramified`:454, `selfDual_of_split`:364, `selfDual_of_trivial_action`:417,
  `selfDual_of_ramified`:476, `selfDual_of_split_case`:539, `selfDual_of_simple`:553.
  → r_R (**R26** assembles; R22/R23/R24/R25 supply the C-leaves).

### 1.12 `GQ2/DevissageInduction.lean` (207 ln) — the dévissage induction (B·fwd)

- **(A)** the `CardDrops` lattice helpers 87–149: `stableSubAction_subtype_equivariant`:87,
  `stableQuotAction_mk'_equivariant`:95, `subtype_range_eq_mk'_ker`:106, `two_torsion_sub/quot`:111,116,
  `card_lt_of_ne_top`:131, `card_quot_lt_of_ne_bot`:140.
- **(B·fwd)** **`prop_5_15_of_simple`:158** — strong induction on `Nat.card A`; proof forwards
  `hw` to `trivialSelfDual t ht hw`, `hsimp`, `lemma_5_11 t ht hw hgen`. **Generic scaffold** — the
  only Γ_R coupling is the `hw : t.WildRel` hypothesis type and the `Z1w t`/`H2w t` objects.

### 1.13 `GQ2/Devissage/*.lean` — the LES + cone dévissage tower (all B·fwd)

Every decl takes `(t : Marking C) (ht : t.TameRel) (hw : t.WildRel)` and references the spine
objects (`H0w/H1w/H2w/Z1w t`, `chi* t`, `delta* t`, `mixedB t`); **proofs forward `hw` and use
only `d¹∘d⁰=0`, functoriality, the LES, and finite linear algebra** — none unfold the aux words.
(One functoriality touch: `Naturality.lean:55–56` uses `Marking.map_wildValue` + `WordLift.map_u`
— generic naturality, r_R needs `map_wildValueR`.)

| file | decls | class |
|---|---|---|
| `ElemDualPack.lean` | `dualMap`/`elemDual_extend`/`dual_ses_exact` etc. (35–175) | **(A)** — pure dual-module linear algebra, reuse verbatim |
| `SelfDual.lean` | `IsSelfDualW`(def):37, `isSelfDualW_iff`:49, `chi_bij_of_selfdualW`:73, `four_lemma_inj`:140 | (B·fwd) |
| `GeneratesBridge.lean` | `H0w_eq_fixedPts`:36, `isSelfDual_iff_W`:68, **`lemma_5_11`:90** | (B·fwd); `four_lemma_inj`,`H0w_eq_fixedPts` proofs generic |
| `Chi1.lean` | `chi1(Aux/T/TAux)`:36–111, `chi1T_flip`:145, `pairing_clause_iff`:155, `chi1_bij_of_inj`:205, `chi1(T)_square`:240,254 | (B·fwd) |
| `EvalPairings.lean` | `H{0,1,2}w_two_torsion`:39–52 (A), `mixedB_zero_{left,right}`:60,64, `chi{0,2,0T,2T}`:70–163, `chi0/2_(inj/surj)*`:199–240, `chi*_square`:262–286 | (A)+(B·fwd) |
| `LESCore.lean` | `pi_/prod_*`:43–73 (A), `snake*`/`delta0/1(raw)`:93–260 | (B·fwd) |
| `LESExact.lean` | `H{0,1,2}w_exact_*`:41–274 | (B·fwd) |
| `LESMaster.lean` | `delta{0,1}D`:46,54, `delta_square_core{1,2}`:65,104, `square_delta*`:145–192, `selfdualW_two_of_three(_mid/quot/sub)`:212–556 | (B·fwd) |
| `Naturality.lean` | `d0_natural`:39 (A), `d1_natural`:47, `d1_ker_map`:71, `Z1wMap/H2wMap/H0wMap/H1wMap`:78–108, `card_Z1w_eq_sq_mul_card_H2w`:133, `B1w_le_Z1w`:158, `card_H1w_eq`:165 | (A)+(B·fwd) |

---

## 2. Answers to the specific questions

### Q1 — `prop_5_15` / `prop_5_16` hypotheses + downstream consumers

**`prop_5_15`** (DualityAssembly.lean:574, namespace `GQ2.FoxH`):
```
theorem prop_5_15 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (hgen : t.Generates)
    (hA₂ : ∀ a : A, a + a = 0) (hcore : t.Pro2Core) : IsSelfDual t A
```
Returns `IsSelfDual t A` (Traced.lean:542) = the 3-clause conjunction ⟨`#H²w = #(A∨)^C`,
`#Z¹w = #A²·#(A∨)^C`, ∃ perfect pairing `P` descending `mixedB t`⟩. Proof = `prop_5_15_of_simple`
∘ `selfDual_of_simple`. **All six hypotheses are wired through by consumers as
`(markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2`**, where `adm := markC_admissible θ hθs`
(so `adm.2.1=TameRel`, `adm.2.2.1=WildRel`, `adm.1=Generates`, `adm.2.2.2=Pro2Core`).

**`prop_5_16`** (LocalLiftingDuality.lean:544, proved from `prop_5_16_bundle`:496, **NOT in a
target file**): takes `(ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : surjective) (A, two compatible
actions, hA₂, hpair)`; returns the display-(57) numerics + the three cup bijections of
`H*(AbsGalQ2, A)`. **It is the Galois/Tate side (uses axioms B6, B7) — word-generic, contains no
`Marking`/`WildRel`. Reused verbatim for Γ_R; no `prop_5_16_R` is needed.** The two are bridged by
`cor_5_17_card` (LocalLiftingDuality.lean:571), which **does** carry `hw : t.WildRel` and calls
`prop_5_15 t ht hw hgen hA₂ hcore` — so `cor_5_17_card` needs a thin `_R` variant.

**Consumers of `prop_5_15`** (each passes the `adm` projections above; all take the whole
statement, differing only in which clause `.1 / .2.1 / .2.2` they read):

| consumer | file:line | clause used | passes |
|---|---|---|---|
| `RecursionFrame.liftsOver_card_gammaA_of_nonempty` | MStageCountGammaA.lean:523 | `.2.1` (Z¹ count) | `(markC θ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2` |
| (same file, second use) | MStageCountGammaA.lean:393 | `.2.1` | same |
| `hZcount_gammaA` / RStage Z¹ count | RStage/GammaA.lean:226, 1105 | `.2.1` | same |
| Phase140 GammaA Z¹ count | Phase140/GammaA/Foundation.lean:98, 180 | `.2.1` | same |
| Phase140 Hsep separation | Phase140/GammaA/Hsep.lean:70, 494 | `.2.2` (pairing) | `markC (RF.rhoPrime …)` variant |
| `half*` half-torsor | HalfTorsorGammaA.lean:71 | `.2.2` | same shape |
| RadicalEdge pairing | RadicalEdge/GammaA.lean (docstring 16) | `.2.2` | — |
| `cor_5_17_card` | LocalLiftingDuality.lean:590 | `.1,.2.1` | `t ht hw hgen hA₂ hcore` (abstract `t`) |
| GaussZ FinalGammaA | GaussZ/GammaAD.lean:410,701 (via `markC_admissible`) | — | `markC_admissible` |

**Chain into the §8 supply layer:** `prop_5_15` → `liftsOver_card_gammaA(_of_nonempty)`
(MStageCountGammaA.lean:488,603) → `Prop89Close.liftsOver_card_gammaA` use (Prop89Close.lean:177)
→ `lemma_8_6_gammaA` (SectionEight/Partition.lean:291, half-torsor) → `main_surjection_count'`
(SectionTenSources.lean). **All of these consume `prop_5_15` + `markC_admissible` only; both must
gain `_R` variants (R31).** The docstring at MStageCountGammaA.lean:485 confirms the Z¹-torsor
bridge is **source-generic once a base lift exists** — the r_R wrapper is thin.

### Q2 — is `mixedB` parameterised by the word, and does the generic dévissage accept `mixedB_R`?

`mixedB` (Heisenberg.lean:312) is **`(heisMarking t x y).tameValue.z + (heisMarking t x
y).wildValue.z`** — it **unfolds `Marking.wildValue`**; it is **not** parameterised by the relator.
For r_R you must define `mixedB_R := tameValue.z + wildValueR.z`.

**The generic dévissage does NOT accept a `mixedB_R` as a drop-in.** `selfdualW_two_of_three`
(LESMaster.lean:556), `lemma_5_11` (GeneratesBridge.lean:90), `isSelfDualW_iff` (SelfDual.lean:49)
are polymorphic in `t : Marking C` but are **stated over the fixed spine objects** `IsSelfDualW t`
/ `Z1w t` / `H2w t` / `mixedB t`, each a fixed def routed through the single `Marking.wildValue`.
There is **no `mixedB` (or complex) parameter** to substitute. Therefore Γ_R reuse requires **one
of**:

- **(i) clone** the spine + dévissage (`d1Fun/Z1w/H1w/H2w/mixedB`, `IsSelfDual(W)`, `chi*`,
  `delta*`, the LES, `selfdualW_two_of_three`, `lemma_5_11`, `prop_5_15_of_simple`) with
  `wildValue→wildValueR`; proofs port verbatim (they never unfold the aux words) — but this is a
  ~3 k-line clone of `Devissage/`;
- **(ii) generalise** (preferred, §2.6): lift the spine defs to take the relator word (or its
  natural differential) as a parameter, prove the dévissage once, instantiate for Γ_A
  (byte-identical capstone) and Γ_R.

So: **`mixedB` unfolds the word; `selfdualW_two_of_three`/`lemma_5_11` treat it as a fixed
constant of `t`, not a parameter — the "reuse verbatim" in the plan means "no new mathematics",
not "the same Lean decl applies unchanged".** This is the single load-bearing flag for R26/R30.

### Q3 — `markC_admissible`

`markC_admissible` (**WordCohBridge.lean:91**, not a target file):
```
theorem markC_admissible (hq : Function.Surjective q) : (markC q).Admissible
```
with `markC q := Marking.push q` (WordCohBridge.lean:89). `Admissible = Generates ∧ TameRel ∧
WildRel ∧ Pro2Core` (Words.lean:132). It certifies the **push-forward marking of a surjection
`q`** satisfies the Γ_A presentation's four conditions — the wild clause is the Γ_A `WildRel`. It
is the *other* candidate-specific input the MStageCountGammaA:485 docstring names (besides
`prop_5_15`): consumers write `adm := markC_admissible θ hθs` then feed `adm.2.1/.2.2.1/.1/.2.2.2`
to `prop_5_15`. **Γ_R needs `markC_admissible_R : (markC_R q).AdmissibleR`** (a P0/P1-level fact —
r_R holds in every quotient; owned by R1/R3/R6, consumed by R31), whose `AdmissibleR` swaps
`WildRel→WildRelR`. **(B·word by statement; proof-generic given the presentation clones.)**

### Q4 — WildRow / HessianRow lemma roles (R21/R22/R24 mirror map)

See §1.3 (WildRow) and §1.4 (HessianRow) tables. Summary of the generic-API vs word-unfolding split:

- **Reused generic API (do not re-prove):** `WordLift.{pow_u, powOmega2_u_of_trivial,
  powOmega2_u_of_oddFixedPointFree, commP_u_of_trivial, conjP_u_of_*, mul/inv/conjP/commP_g_trivial}`
  (Basic.lean:159–306); `HeisLift.{mul_z_of_trivial, commP_z_of_trivial, commP_a_of_trivial,
  conjP_z_of_slice, conjP_a/l_of_slice, inv_a/l/z}` (Heisenberg.lean:220–290);
  `lemma_5_7_left/right` (Heisenberg.lean:445,523); `sigma2_pairing_operator_injective`
  (TameSimple.lean:303); `d1Fun_tame(_split)` (Basic.lean:437 / HessianRow.lean:594);
  `b1w_split_shape` (HessianRow.lean:605).
- **Word-specific unfolding (re-prove for r_R's 4 factors):** the `liftMarking_<aux>_*` rows
  (WildRow, R21), the `heisMarking_<aux>_<coord>` ledger (HessianRow 47–535, R24), and the two
  `wildValue`-assembled rows (`liftMarking_wildValue_u(_ramified)` R21; `heisMarking_wildValue_z
  (_ramified)` R24). r_R's rows (paper tex:496–538): tame row **unchanged**
  `L_t=S⁻¹(1+T)a+(S⁻¹+1+T)b`; wild row **`L_w=Pb+(P+S⁻¹)c`** (split `P=1`: `b+(1+S⁻¹)c`;
  ramified `P=0`: `S⁻¹c`) — "the Γ_A matrix with the two wild columns interchanged"
  (paper tex:504–505). Normal form `(0,0,0,d)` (R22, tex:541).

### Q5 — trivial-module layer + `mixedB_cocycle`; what must be re-proven

`mixedB_cocycle` (MixedBilinear.lean:350) is the **Γ_A** Gram closed form
`mixedB t x y = y₂(x₂)+y₃(x₀)−y₀(x₃)+u₁.z`, with the opaque ω₂ scalar `u₁.z` confined to the (3,3)
slot (`heisMarking_u1_z_of_{x3,y3}_zero`). `trivialSelfDual` (TrivialSelfDual.lean:176) descends it
to `H¹w=Z¹w` (since `B¹w=⊥`) and proves two-sided nondegeneracy by the unit-determinant Gram.

**For r_R (R25) you must re-prove exactly:** `d1Fun_of_trivial_R : d1Fun_R = (b,b)` (paper
eq:scalarform, tex:579 — S=T=P=1 collapses both rows to `b`; *note it is still the diagonal
`(x1,x1)` shape*, so `card_range_d1_trivial_R`/`card_H2w_trivial_R`/`card_Z1w_trivial_R`/
`mem_Z1w_trivial_iff_R` are mechanical), `heisMarking_wildValueR_z_cocycle` + **`mixedB_cocycle_R`
with the scalar Gram `⟨(a,c,d),(a',c',d')⟩ = ac'+ca'+dd'`** (tex:583 — cleaner: honest diagonal
`dd'` on the (3,3) slot, no opaque ω₂ scalar), and `trivialSelfDual_R` (same descent, new
nondegeneracy witnesses). **Reused verbatim:** `d0_of_trivial`, `elemDual_smul_trivial`,
`card_fixedPts_elemDual_trivial`, `B1w_trivial_eq_bot` (TrivialSelfDual.lean:68,76,83,165), and all
of MixedBilinear's `stokesEval_*` bilinearity (§1.7). The nonsingularity of `ac'+ca'+dd'` is a
3×3 unit-determinant check (matrix `[[0,1,0],[1,0,0],[0,0,1]]`, paper eq:cupmatrix tex:241) —
shares machinery with R13.

### Q6 — minimal ordered list of new Γ_R declarations, and the one generalisation flag

**(a) To assemble `prop_5_15_R` (self-duality of the r_R word complex).** New decls, in
dependency order (each `→ mirrors`):

1. `wildValueR`, `WildRelR`, `wildValueExpR` (+ `_map`, `_eq_of_dvd`) → `Marking.wildValue`
   Basic.lean:48, `WildRel` Words.lean:121, `wildValueExp` Traced.lean:75 — **owned by R1**
   (`Roe/Words.lean`); `map_wildValueR` → Basic.lean:65.
2. `d1Fun_R`/`d1_R`/`Z1w_R`/`H1w_R`/`H2w_R`/`d1Fun_comp_d0_R` → Basic.lean:334–430 — spine (see
   generalisation flag).
3. `liftMarking_<r_R-factor>_u(_ramified)` + `liftMarking_wildValueR_u(_ramified)`
   → WildRow.lean (whole) — **R21** (⟦prop:jacobian⟧).
4. `expMod2_wildValueExpR` (`→(0,1,0,0)`) + `mixedB_wildRow(_right)_R` + `prop_5_8_left/right_R`
   → Traced.lean:97,319,431,349,452 — **R23** (⟦lem:stokes⟧).
5. `lemma_5_13_split_R`/`_ramified_R` (normal form `(0,0,0,d)`) → HessianRow.lean:647,696 — **R22**
   (⟦lem:normalforms⟧).
6. `heisMarking_<r_R-factor>_z*` + `heisMarking_wildValueR_z(_ramified)` +
   `lemma_5_13_pairing_split/ramified_R` → HessianRow.lean:331,535,752,775 — **R24** (⟦prop:hessian⟧).
7. `heisMarking_wildValueR_z_cocycle` + `mixedB_R`/`mixedB_cocycle_R` (Gram `ac'+ca'+dd'`) +
   `d1Fun_of_trivial_R` + `card_{range_d1,H2w,Z1w}_trivial_R` + `trivialSelfDual_R`
   → MixedBilinear.lean:295,350 + Heisenberg.lean:312 + TrivialSelfDual.lean (whole) — **R25**
   (⟦lem:trivial⟧).
8. `mixedB_left/right_congr_R`, `split_shapes_of_wild_R`, `x0Supported_mem_Z1w_ramified_R`,
   `clause3_of_normalForm_R`, `selfDual_of_{split,trivial_action,ramified,split_case,simple}_R`,
   `prop_5_15_R` → DualityAssembly.lean:205–574 — **R26** (⟦prop:duality⟧). Uses (reused verbatim)
   `tau_split_or_ramified`, `card_*_of_nontrivial*`, and the dévissage spine (2 & the flag below).
9. **No `prop_5_16_R`** — `prop_5_16` (LocalLiftingDuality.lean:544) is word-generic (Q1). Only a
   thin `cor_5_17_card_R` (calls `prop_5_15_R`) is needed if the §5.17 bridge is used.

**(b) To feed the §8 supply layer.** New decls (R31), each a thin wrapper:

10. `markC_admissible_R : (markC_R q).AdmissibleR` → WordCohBridge.lean:91 (Q3; needs `markC_R`,
    `AdmissibleR` from R1/R3).
11. `liftsOver_card_R(_of_nonempty)` → MStageCountGammaA.lean:488,603 — swap
    `markC_admissible→_R`, `prop_5_15→prop_5_15_R`, reuse `.2.1`; `z1Equiv`/`card_fixedPts_MB_dual`
    reused as-is (source-generic per MStageCountGammaA:485).
12. `lemma_8_6_R` (half-torsor) → SectionEight/Partition.lean:291 — consumes `prop_5_15_R` `.2.2`.
13. GaussZ `FinalGammaR` package (clone of `GaussZ/FinalGammaA.lean`) — consumes R27's r_R
    quadratic form through the **abstract** `qDouble`/`lemma_6_6`/`lemma_6_8`/`prop_6_9_*`
    (SectionSix — reused verbatim; §1.9). `qDouble` = `GaussZ/FinalGammaA/Counts.lean` (not
    SectionSix:212).

**The one generalisation flag (prefer over a clone).** Items **2, 5-part, 8-scaffold, R26** all
sit on the spine (§0.2) — `IsSelfDual(W)`, `chi*`, `delta*`, the LES, `selfdualW_two_of_three`,
`lemma_5_11`, `prop_5_15_of_simple` are **generic in `t` and forward `hw`, but hard-reference the
fixed `Marking.wildValue`** via `Z1w t`/`H2w t`/`mixedB t`. To reuse them for Γ_R **without a
~3 k-line clone of `Devissage/`**, the recommended edit is to **parameterise the spine over the
relator word** — add a natural "relator" datum `r : Marking C → C` (with `map_r`) and route
`d1Fun`/`Z1w`/`H1w`/`H2w`/`mixedB`/`IsSelfDual(W)`/`chi*`/`delta*`/`prop_5_15_of_simple` through
`r`; prove the dévissage once; instantiate `r := wildValue` (Γ_A, byte-identical capstone) and
`r := wildValueR` (Γ_R). This is a **serialised edit to frozen files** (Basic, Heisenberg,
Devissage/*, DevissageInduction) — the R30-pattern regression gate applies (full build green +
`check_axioms.sh` + Γ_A capstone `#print`s unchanged). **All other Γ_R work above is new files
(R21–R27, R31–R32).** If edits are truly forbidden, the fallback is the clone (proofs port
verbatim, but ~3 k lines — over the P3 budget). Recommend the orchestrator make this the explicit
R26/R30 design decision: **generalise the spine, don't clone the dévissage.**

---

## 3. Paper-tag ledger (r_R note ⟶ Γ_A mirror ⟶ ticket)

| note label (tex) | display | Γ_A mirror | ticket |
|---|---|---|---|
| `prop:jacobian` (496) | `L_w = Pb+(P+S⁻¹)c` | WildRow.lean:277,397 | R21 |
| `lem:normalforms` (541) | rep `(0,0,0,d)` | HessianRow.lean:647,696 | R22 |
| `lem:stokes` (606) | `(0,1,0,0)` | Traced.lean:97 + mixedB wild rows | R23 |
| `prop:hessian` (636) | `λ((1+U+U⁻¹)c)` | HessianRow.lean:331,535 | R24 |
| `lem:trivial` (576) | Gram `ac'+ca'+dd'` | MixedBilinear.lean:350 + TrivialSelfDual.lean:176 | R25 |
| `prop:duality` (676) | self-duality | DualityAssembly.lean:574 (`prop_5_15`) | R26 |
| `prop:quadratic` (712)/`cor:gauss` (752) | `Q_R⁰=q+b_q(·,U⁻¹·)` | SectionSix.lean:222,268,328 (abstract) | R27 |
| `prop:interface` (786) | Cor 6.19 | thm_4_2 / SourceData | R30–R32 |

*Recon complete. No Lean files read-modified; `roe-tickets.md` untouched.*
