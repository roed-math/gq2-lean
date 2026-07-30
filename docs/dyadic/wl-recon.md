# WL-recon — re-pricing WL-b/WL-c against the frozen `Γ_R`/`Γ_A` word-certificate base

**Ticket WL-recon** (dyadic campaign, lane WL; branch `dyadic-wl`, worktree `~/claude/gq2-dyadic-wl`,
from `dyadic` at `337647f`, census 11). Authorized at **SQ1 Q4** (board log 2026-07-30, ruling (iv)):
SQ1 discovered that `L_sq` at `n = 1` is Roe's candidate `Γ_R` *as a whole word*, and recorded in its
§7.5 that the frozen Roe certificate chain (`≈ 1855 ln`) "plausibly halves WL-b/WL-c". This ticket
replaces that conjecture with a measurement.

**Scope.** Read-only survey. No `.lean` file is edited; the only committed artefact is this memo.
Every file:line anchor below was verified by reading the source at `337647f`, and the `n = 1` word
identifications of §1.3 were **typechecked against the real repo** in a scratch spike (§1.3, §6.1).

**Authority order.** (1) the packet `refs/dyadic-presentations-formalization-proof.tex` and its
ledger §5.2 (`WordCertificate`'s six items); (2) S2.4's memo
(`~/claude/general_2adic/artifacts/reports/marked-stabilization-memo.md`) for the clause split and
the stabilization theorems; (3) SQ1 (`sq-design.md`) for the `L_sq ↔ Γ_R` identification;
(4) `plan.md` §0/§3 binding constraints.

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|---|---|
| **V1** | Is the `n = 1` base of lane WL really "the ℚ₂ case"? | **YES, and it is a theorem of the parameter structure, not a convention.** For type `L`, `n = [K:ℚ₂]` is odd and `f ∣ n` (`FieldParameters`, `GQ2/Dyadic/Parameters.lean:86-94`), so `n = 1 ⟹ f = 1 ⟹ q_K = 2 ⟹ K = ℚ₂` — and `paramsQ2` is type-`L`-compatible **`by decide`** (`Parameters.lean:844-848`). The `n = 1` base of WL-a/b/c is therefore *exactly and only* ℚ₂, which the frozen development proves completely. §1.1 |
| **V2** | Do **both** candidate `L` words have a frozen `n = 1` precedent? | **YES, and both identifications are `rfl` up to one cast.** The board's WL-a word `R_{L,K}` at `m = 0` is *letter for letter* `GQ2.Marking.wildRelator` (`GQ2/GammaA.lean:89`) — including `g₀ = σ₂²`, `h₀ = x₀^{g₀}x₀·d_g d₀ d₀² h_c`; and `R^sq_{L,1}` is `wildRelatorR` (`GQ2/Roe/GammaR.lean:77`). Spike-measured: every `ω₂`/conj/comm/mul/inv node is **definitional** against F2's `PWord` denotation; the only bridge is `zpow_natCast` on the `IntegerPower` nodes, discharged by one `norm_cast`. §1.3 |
| **V3** | How big is the frozen chain, really? | **8615 lines, not 1855.** SQ1's estimate counted six files; the word-certificate chain is `1499` (word/boundary) + `1389` (Fox/lifting) + `3961` (dévissage/Stokes/Hessian duality) + `1766` (quadratic/Gauss) = **8615**, plus `1058` of SD-`n`-side assembly. §1.4 |
| **V4** | Does the precedent halve WL-b/WL-c? | **No — it removes the risk, not the work.** Measured: it discharges **≈ 100 % of the mathematical content** of WL-b/WL-c at `n = 1` (every row, normal form, pairing, quadratic, constant and sign is a sorry-free theorem, for *both* candidate words) but **≈ 25 % of their Lean text**, because every frozen statement lives in the 4-generator `Marking`-record ℚ₂ vocabulary and every WL goal will live in the `PWord (Generator n)` general-`K` vocabulary. §2, §3 |
| **V5** | What about the handle half? | **SQ1's §7.5 did not separate it, and it is where the real saving is.** At `n = 1` there are no handles (`h = 0`), so the Roe chain contributes **0 %** to clauses 1b/2b/3/4/6-handle. Those are **≈ 85 % already landed** — MC2's h-generic `handleWord_*`/`commP_fib`/`handleWord_centLift_fib` (`GQ2/Dyadic/MarkedCore/Cores.lean:128…1455`) plus HM1–HM5, exactly as S2.4 §8.3 measured ("six of seven already sorry-free"). §2.6 |
| **V6** | WW subsumption: source or regression target? | **REGRESSION TARGET, decisively — and the board already says so.** WW1's own spec schedules "at `n = 1` the evaluator's rows equal the hand rows `liftMarking_wildValue_u` / `liftMarking_wildValueR_u`". The empirical proof is the dévissage layer: `GQ2/Devissage/*` (2394 ln) was **cloned** as `GQ2/Roe/Devissage/*` (2156 ln) for a one-relator change, and the clone's own docstring says the proofs "port **verbatim** onto the `r_R` spine … never unfolding the aux words". Five branch words × that cost ≈ 11 k lines of avoidable work. §4.1 |
| **V7** | Is anything in the frozen chain citable *as a lemma* at degree `n`? | **Yes, one substantial block: the quadratic/Gauss endgame.** `QuadraticFp2` (108), `SectionSix.lemma_6_6/6_8/prop_6_9_{unramified,ramified}` (1056) and `GaussSigns` (768) are stated over an abstract `q : V → ZMod 2` with no relator and no `Γ` — **1932 lines citable verbatim**, subject to one caveat: they are keyed to `Ttame` (the `q = 2` tame group), so general `q_K` needs F3's rebase, not a re-proof. §2.5, R2 |
| **V8** | Genuinely new, uncovered by any precedent | **Three items.** (i) `hHilb` — Witt cancellation over `𝔽₂` in dimension `n+2` (S2.4 §5.5; mathlib does not supply it); (ii) the **nonsplit-coefficient** composition-series extension (packet `lem:composition`, ledger B3 — the frozen chain's dévissage does it by cloning, WW3 must do it generically); (iii) **general `q_K`** everywhere the frozen chain reads a literal `2`. §2.7 |
| **V9** | Board hygiene | **Two stale rows found.** (a) The WL-a row still displays the *collector-cored* `R_{L,K}` (draft `eq:Lword`), which R2 superseded when it signed `L_sq` primary — an orchestrator re-point at G-1, costing nothing because both `n = 1` identifications are spike-verified. (b) SQ5 was told to carry "the FULL word-theorem restatement in SQ vocabulary" — **impossible as specified**: `GQ2/Roe/Main.lean` is plain-import and `SqCore/Sanity.lean` is spec'd `module` (SQ1 §3.3). That restatement is **AS4's**. §4.2, §4.3 |

**Bottom line in one sentence.** Lane WL's `n = 1` base is exactly ℚ₂, and ℚ₂ is *finished* — for both
candidate `L` words, at 8615 lines of sorry-free Lean, with the terminal theorem
`main_presentation_literal_roe_unconditional` hypothesis-free — so WL-b/WL-c carry **no mathematical
risk at the base and no discovery work anywhere**; but the frozen text is in the wrong vocabulary to
be imported, so the measured Lean saving is ≈ 25 %, not 50 %, and the tickets should be re-tiered
around where the *residual* risk actually sits (the scalar/Hilbert item and general `q_K`) rather
than around where the mathematics used to be hard.

---

## 1. The inventory

### 1.1 What `n = 1` means for lane WL — a theorem, not a convention

`GQ2/Dyadic/Parameters.lean:80-94` fixes the field parameters:

```lean
structure FieldParameters where
  n : ℕ            -- [K : ℚ₂]
  f : ℕ            -- residue degree
  qK : ℕ
  qK_eq : qK = 2 ^ f
  one_le_n : 1 ≤ n
  one_le_f : 1 ≤ f
  f_dvd_n : f ∣ n
```

Type `L` is the **odd-degree** family. So `n = 1` forces `f ∣ 1`, i.e. `f = 1`, i.e. `q_K = 2`, i.e.
`K = ℚ₂` — and the repo already pins the instance:

```lean
def paramsQ2 : FieldParameters :=
  { n := 1, f := 1, qK := 2, qK_eq := rfl, … }        -- Parameters.lean:844
example : Compatible paramsQ2 .L := by decide          -- Parameters.lean:848
```

**Consequence.** Where the board writes "WL-b: Fox certificate (`n = 1` base + handle stability)",
the `n = 1` base is not *an instance of* the general-`K` statement — it *is* the general-`K`
statement, with the `K`-quantifier collapsed to a point. Everything the frozen ℚ₂ development
proves about the `L` word is, verbatim, the content of that base. This is stronger than SQ1 §7.5
claimed and it is the reason the risk verdict (V4) is as strong as it is.

It also bounds the claim: **the base exercises nothing that distinguishes `q_K = 2` from
`q_K = 2^f`**, and nothing about handles (`h = 0`). See R1, R2.

### 1.2 Both `L` candidates, and which one is live

| | word | frozen group | frozen terminal theorem |
|---|---|---|---|
| board WL-a (draft `eq:Lword`) | `R_{L,K} = h₀·u₁⁻¹·x₁^σ·c₀·∏[x_{2j},x_{2j+1}]`, pro-2 core `x₀^{σ²}x₀[x₁,σ]·H_h` | `Γ_A` | `main_presentation_literal` (`GQ2/PresentationLiteral.lean:46`) |
| **R2-selected `L_sq`** | `R^sq_{L,n} = (x₀^σ)⁻¹(x₀⁻³τ)^{ω₂}x₁²[x₁,x₁^{σ₂}]·H_h`, pro-2 core `(x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]·H_h` | **`Γ_R`** | **`main_presentation_literal_roe_unconditional`** (`GQ2/Roe/Main.lean:563`) — hypothesis-free |

R2 (2026-07-30) signed `L_sq` **primary**; G-1 (= the simplification campaign's R5) is what freezes
the word and re-points this lane. The board's WL-a row still displays the collector-cored word — see
§4.2. Both identifications are spike-verified below, so the re-point costs nothing.

### 1.3 The `n = 1` identification, measured

Scratch spike (never committed):
`/private/tmp/claude-501/-Users-roed-claude-lmfdb/8d8a6b1f-8827-496c-854b-e383c5b269ac/scratchpad/WlSpike4.lean`,
run as `lean` with the `LEAN_PATH` of a sibling worktree built at `337647f`
(`gq2-dyadic-mc`; read-only — no `lake build`, no writes outside the scratchpad).

Both `L` words were built as `PWord (Generator 1)` terms out of F2's constructors
(`GQ2/Dyadic/Word/Syntax.lean`), with F2's derived letters `sigma2W` (`:576`) and `deltaW` (`:580`),
and evaluated through `Marking.eval` (`GQ2/Dyadic/Word/Eval.lean:610`) at F1's `n = 1` adapter
`Marking.ofQ2`.

**Result: 0 errors.**

| clause | statement | outcome |
|---|---|---|
| (a) | `eval (uW i) = t.u{0,1}Hat`, `eval (deltaW 0) = t.d0Hat`, `eval z0W = t.z0Hat`, `eval c0W = t.c0Hat`, `eval cRW = t.cRHat` | ✅ **by `rfl`** |
| (b) | `eval g0W = t.g0Hat` (`σ₂²`) | ✅ `show … ; norm_cast` — **the only obstruction is `ℤ`-power vs `ℕ`-power** |
| (c) | **`eval lWord = t.wildRelator`** — the board's WL-a word at `n = 1` **is** the frozen `Γ_A` wild relator | ✅ 4-line proof (`show`, then one `norm_cast`) |
| (d) | **`eval lSqWord = t.wildRelatorR`** — `R^sq_{L,1}` **is** the frozen `Γ_R` wild relator | ✅ 3-line proof |
| (e) | `eval tameW = t.tameRelator` | ✅ 2-line proof |
| (f) | `x ^ (2 : ℤ) = x ^ (2 : ℕ)` in an abstract group | ❌ **not `rfl`** — `zpow` is an opaque `DivInvMonoid` field; `norm_cast` / `zpow_natCast` discharges it |

**API finding for WL-a (record it in the dispatch prompt so it is not rediscovered).** F2's
`PWord.zpow` carries a `ℤ` exponent (faithful to the Python `IntegerPower` node) while every frozen
ledger letter uses `Monoid.npow`. They are **not definitionally equal**, so the `n = 1`
cross-identification is `rfl` on every other node and needs exactly one cast lemma. One
`theorem eval_zpow_nat (μ) (w) (k : ℕ) : eval μ (.zpow w k) = eval μ w ^ k := zpow_natCast _ k`
placed in `GQ2/Dyadic/Words/L.lean` covers all of it.

This is the **entire** cost of the board's "must recover the Roe–Turturean form — cross-identify
against `wildRelator`/`wildRelatorR`" requirement, which was WL-a's only flagged risk.

### 1.4 The frozen `Γ_R` word-certificate chain, by layer

All counts are `wc -l` at `337647f`; all declaration anchors verified by reading.

**Layer W — word, boundary, tame quotient (WL-a's `n = 1` base). 1499 lines.**

| file | ln | what it proves |
|---|---|---|
| `GQ2/Roe/Words.lean` | 282 | the finite ledger `aR`(:75)/`y1R`(:80)/`cR`(:84)/`wildValueR`(:94), `WildRelR`(:98), `AdmissibleR`(:108), `admissibleCountR`; the **de-ω₂-ified** `wildValueExpR`(:165) with `_map` naturality(:174) and the `_eq_` bridge(:183); abelian collapse `wildValueR_comm`; `wildValueExpR_zmod8`(:244) `decide`-pin |
| `GQ2/Roe/GammaR.lean` | 247 | the profinite letters `aRHat`(:61)/`y1RHat`(:66)/`cRHat`(:70) and **`wildRelatorR`(:77)**; the per-letter fidelity bridges (:99-128) and `map_wildRelatorR_eq_one_iff`; `IsAdmissibleUR`(:176), `NR`(:182), `GammaR`(:196), `NR_le_ker`(:205) |
| `GQ2/Roe/AdmissibleLimit.lean` | 319 | relators die in `Γ_R`; admissible-open characterisation; the wild core `wildCoreR` and `isProP_wildCoreR` |
| `GQ2/Roe/Tame.lean` | 454 | **packet item (1), tame specialization**: `wildRelR_of_trivial_wild`(:96) — killing `x₀,x₁` makes `r_R` automatic; the tame coordinate `phiR` with `phiR_surjective`(:359) and `ker_phiR = W_R`(:368); `wildCoreR_isMax`(:382) (`W_R = O₂(Γ_R)`, **without B10**); the unramified character `nuR`(:407), `nuR_surjective`(:428) |
| `GQ2/Roe/Sanity.lean` | 197 | small-group surjection-count cross-check of the transcription against the June LMFDB data |

**Layer F — Fox complex, rows, normal forms, lifting (WL-b's `n = 1` base). 1389 lines.**

| file | ln | what it proves |
|---|---|---|
| `GQ2/Roe/FoxBasic.lean` | 272 | `d1FunR`(:63) — the Fox derivative *as the `.u` coordinate of the evaluated relator*, never a formal derivative; `d1FunR_fst`(:69) (tame row shared **definitionally** with `Γ_A`), `d1FunR_add`(:86), `d1R`(:116), `d1FunR_comp_d0`(:131), the word complex `H0wR/Z1wR/B1wR/H1wR/H2wR`(:149-190); the traced mixed coordinate `mixedB_R`(:209) + `bridge_wildR`(:219) |
| `GQ2/Roe/WildRow.lean` | 333 | **packet item (3), the evaluated wild Fox row** (note Prop 4.1): the per-factor ledger, then **`liftMarking_wildValueR_u`(:219)** `= x₁ + (1+S⁻¹)x₂` (split) and **`_ramified`(:244)** `= S⁻¹x₂`; the `x₀ ↔ x₁` swap stress tests (:271, :281); trivial-module collapse `d1FunR_of_trivial`(:295) |
| `GQ2/Roe/NormalForms.lean` | 206 | note Lemma 4.2: **`lemma_5_13_split_R`(:95)** (the `Z¹_R`/`B¹_R` shapes `x₁ = 0 ∧ x₂ = 0`) and **`lemma_5_13_ramified_R`(:130)** (existence *and uniqueness* of the `x₁`-supported representative `(0,0,0,d)`) |
| `GQ2/Roe/CorrectionR.lean` | 268 | the relator-correction calculus: `wildValueR_correction` — correcting by central involutions shifts `r_R` by exactly the τ-correction |
| `GQ2/Roe/CoverLiftR.lean` | 310 | L4/L5: cover-lift kernel and relator-free descent, frame-free |

**Layer D — dévissage, Stokes, Hessian duality (WL-c items (4)). 3961 lines.**

| file | ln | what it proves |
|---|---|---|
| `GQ2/Roe/Stokes.lean` | 149 | note Lemma 5.1: the mod-2 exponent vector of `r_R` is `(0,1,0,0)`, so the trace `u_t + u_w` satisfies the finite-word Stokes endpoint. `expMod2_wildValueExpR`(:85), `_odd`(:107), endpoint(:118), `_three`(:132) `decide`-pin |
| `GQ2/Roe/TrivialSelfDual.lean` | 582 | the traced chain rows `prop_5_8_{left,right}_R` (`mixedB_tameRow_R` shared, `mixedB_wildRow_R` through `bridge_wildR` + the generic `lemma_5_7_left`); and the **trivial-module scalar Gram** `⟨(a,c,d),(a',c',d')⟩ = ac' + ca' + dd'` |
| `GQ2/Roe/Hessian.lean` | 395 | note Prop 5.2: the per-factor `.z` ledger (:90-236), then **`heisMarking_wildValueR_z`(:258)** `= λ(d)` and `_ramified`(:289) `= λ((1+U+U⁻¹)d)`; the pairings `mixedB_R_pairing_split`(:322)/`_ramified`(:335); **perfectness `pairingR_operator_injective`(:355)** (a thin re-export of the presentation-independent `sigma2_pairing_operator_injective`, `GQ2/TameSimple.lean:303`) |
| `GQ2/Roe/Devissage/*.lean` (9 files) | 2156 | the long-exact-sequence two-out-of-three `lemma_5_11_R` (`GeneratesBridge.lean:65`) along a composition series |
| `GQ2/Roe/Devissage.lean` + `DevissageInduction.lean` | 131 | hub + strong induction |
| `GQ2/Roe/DualityAssembly.lean` | 548 | `selfDual_of_simple_R`(:467) and **`prop_5_15_R`(:485)** — candidate deformation duality on every finite elementary `𝔽₂[C]`-module |

**Layer Q — quadratic form, Gauss signs, residue (WL-c item (6)). 1766 lines.**

| file | ln | what it proves |
|---|---|---|
| `GQ2/Roe/Gauss.lean` | 252 | note Prop 6.1: `QZeroR`(:71) `= q(d)` (split) / `q(d)+b_q(d,U⁻¹d)` (ramified); `QZeroR_split`(:82), `QZeroR_eq_qDouble`(:94), the polar form `polar_QZeroR`(:121) with operator `1+U+U⁻¹`, `QZeroR_nonsingular_ramified`(:134), the Gauss counts `QZeroR_zeroCount_{unramified,ramified}`(:175,:192) and the `∓2^m` finales `QZeroR_finsum_sign_*`(:208,:221) |
| `GQ2/GaussZ/KappaR.lean` | 285 | the unconditional Wall-shape `κ⁰` wild peel `liftMark_kappa0_wildValueR_fib_ramified` |
| `GQ2/GaussZ/RelatorGammaR.lean` | 153 | `relZPairR_kappa0_reindexHom` — the `Sd`-level reindexing retype |
| `GQ2/GaussZ/CoordGammaR.lean` | 131 | the `x₁`-supported gauge (`ofZ1wR`, `h1CoordGammaR`) replacing `Γ_A`'s `x₀`-supported one |
| `GQ2/GaussZ/GammaRD.lean` | 945 | the two `gaussZResidueD_gammaR_{unramified,ramified}` twins in `SourceData` field shape |

**Layer A — SD-`n`-side assembly (NOT WL's). 1058 lines.**
`GQ2/Roe/Supply.lean` (223: topological finite generation + `lemma_8_2_R`, the scalar character count
`#Hom(Γ_R,𝔽₂) = 8`), `GQ2/Roe/Prop23.lean` (233: `prop_2_3_R`), `GQ2/Roe/Main.lean` (602: `sourceR`(:388),
`eq_154_R`(:476), `main_presentation_literal_roe`(:541), **`main_presentation_literal_roe_unconditional`(:563)**).

**Totals.** WL-relevant `W + F + D + Q` = **8615**; whole `Γ_R` route = **9673**.
SQ1's §7.5 estimate of `≈ 1855` is `WildRow 333 + FoxBasic 272 + Stokes 149 + Hessian 395 +
Gauss 252 + Tame 454` — a correct sum over six files, but **4.6× short** of the chain, because it
omits the word/limit layer, the normal forms, the dévissage/duality engine and the whole `GaussZ`
`Γ_R` package.

### 1.5 The shared, already-generic substrate

Not `Γ_R`-specific, and the part WL should actually build on (the WC survey, `recon/wc-survey.md`
§3/§6, reached the same conclusion from the other side):

| asset | ln | genericity |
|---|---|---|
| `stokesEval` (`Heisenberg.lean:325`), `expMod2`(:330), `freeExp`(:382), **`lemma_5_7_left`(:445) / `_right`(:523)** | — | **already `{n}`-generic** (words in `FreeGroup (Fin n)`) |
| `GQ2/MixedBilinear.lean` | 419 | `{n}`-generic bilinearity toolkit |
| `GQ2/QuadraticFp2.lean` (`polar`:53, `IsQuadraticFp2`:58, `Nonsingular`:77, `arf`:91, `qDouble`:96) | 108 | **presentation-independent** |
| `GQ2/SectionSix.lean` — `lemma_6_6`(:222), `lemma_6_8`(:268), `prop_6_9_unramified`(:328), `prop_6_9_ramified`(:381) | 1056 | **`Γ`-agnostic**: stated over an abstract `q : V → ZMod 2` with `IsQuadraticFp2`/`Nonsingular`/`IsInvariant`; no relator occurs. *Keyed to `Ttame`* (`q = 2`) — see R2 |
| `GQ2/GaussSigns.lean` | 768 | ditto (`prop_6_9_unramified_of_{free,abelian,cyclic}`) |
| `sigma2_pairing_operator_injective` (`GQ2/TameSimple.lean:303`) | — | presentation-independent perfectness of `1+U+U⁻¹` |
| `handleWord`(:128), `map_handleWord`(:193), `handleWord_comm`(:233), `commP_wordLift_one`(:353), `handleWord_wordLift_one`(:362), `handleWord_of_one`(:1008), `diagCoeff`(:1212)/`_two`(:1216)/`_mod_four`(:1241), `fib_mul_of_base_one`(:1290), `prod_fib_of_bases_one`(:1298), `commP_fib`(:1370), `commP_base`(:1377), **`handleWord_centLift_fib`(:1422)**, `mRelWord_centLift_fib`(:1435), `nRelWord_centLift_fib`(:1455) | in 1907 | **h-generic and ambient-group-generic** — `GQ2/Dyadic/MarkedCore/Cores.lean`, landed by MC2 |
| HM1–HM5 (`MarkedCore/HandleMix*.lean`) | 4837 | the handle-mixing theorems, general `(α,h)`, landed 2026-07-30 |
| F2's `PWord` + denotation: `eval`(`Eval.lean:304`), `Marking.eval`(:610), `eval_killWild`(:648), `eval_pro2`(:656), `sigma2W`/`deltaW` | 1690 | generic in `n`, landed |

---

## 2. The port map

The packet's target is `WordCertificate` (ledger §5.2), six items:

```lean
structure WordCertificate (K : DyadicField) (P : ProTwoCore K.params.n)
    (R : PWord (Generator K.params.n)) where
  tameSpecialization   : specializeTame R = 1
  proTwoSpecialization : specializeProTwo R = P.word
  exactLifting         : ExactLiftingSemantics R
  stokes               : StokesDualityCertificate R
  scalar               : ScalarHilbertCertificate K R
  determinant          : AffineDeterminantCertificate K R
```

S2.4 §8.2 assigns **clauses 1–4 and 6 to WL** and clause 5's *marked* half to MC5. Below, for each
item: what the frozen chain gives at `n = 1`, what the degree-`n` extension needs, and what is new.

Reuse modes: **cite** = the frozen theorem is applicable to a WL goal as stated;
**wrapper** = applicable after a definitional/one-cast bridge; **template** = the proof script and
the target are known, the Lean text must be rewritten in WW vocabulary; **regression** = its only
role is a pin.

### 2.1 Items (1)+(2) — tame and pro-2 boundary → **WL-a**

| | |
|---|---|
| frozen at `n = 1` | `wildRelR_of_trivial_wild` (`Tame.lean:96`) + the fidelity bridges (`GammaR.lean:99-128`); pro-2 side is the group-level `maxPro2Bridge` (`MaxPro2Bridge.lean:426`), which SQ23 already re-exposed as `gammaRPro2EquivDSqZero` (`SqCore/Rank3.lean:342`) |
| reuse mode | **regression + template.** F2 already proves the *generic* forms: `Marking.eval_killWild` (`Eval.lean:648`) and `eval_pro2` (:656) are Gate-B/Gate-C as theorems, so items (1)+(2) at any `n` are one application each of F2 plus `handleWord_of_one` for the handle block |
| degree-`n` | S2.4 §5.1: `H ↦ 1` under `specializeTame` (`handleWord_of_one`, h-generic, landed); `specializeProTwo` fixes `H` because it contains no `τ`, no `σ₂`, no `ω₂`. **One line each, no hypotheses.** |
| new | nothing |
| **verdict** | **fully covered.** The frozen chain's value here is the `n = 1` regression pin (§1.3) and nothing else; F2 + MC2 already carry the mathematics |

### 2.2 Item (3) — `ExactLiftingSemantics` (the Fox certificate) → **WL-b**

| | |
|---|---|
| frozen at `n = 1` | the rows `liftMarking_wildValueR_u`(:219)/`_ramified`(:244) — the note's `L_w = Pb + (P+S⁻¹)c` at `P = 1` / `P = 0`, i.e. the published Jacobian `[S⁻¹(1+T), S⁻¹+1+T, 0, 0; 0, P, P+S⁻¹, 0]`; the normal forms `lemma_5_13_split_R`(:95)/`_ramified_R`(:130) with **uniqueness**; the complex `d1FunR_comp_d0`(:131); the `Γ_A` twins `liftMarking_wildValue_u` (`FoxHeisenberg/WildRow.lean:277`) / `_ramified`(:397) and `HessianRow.lean`'s `x0Supported` normal forms |
| reuse mode | **template + regression.** The frozen rows are *per-factor hand computations over a 4-field `Marking` record*; WW1's evaluator is structural recursion over `PWord`. No frozen row lemma can close a WW1 goal. But the frozen rows **fix the target exactly**, including the split/ramified case split and the precise hypothesis list (`hV₂`, `hx0`, `hx1`, `htau`; ramified adds `hTodd`), and WW1's spec already schedules them as the `n = 1` regression |
| degree-`n` | S2.4 §5.2: `D(R·H) = D(R) + R̄·D(H)` and `D(H) = 0` in the tame context — the old columns are unchanged, the `2h` new columns vanish, and the *same* row/column operations reach the *same* normal form with a zero block appended. Lever: `commP_wordLift_one`/`handleWord_wordLift_one` (h-generic, landed) |
| new | the degree-`n` rows themselves (WW1 output), the certificate replay object (WW2), and the fact that the lift torsor gains a free `A^{2h}` summand (feeds SD-`n`) |
| **verdict** | mathematics **100 % known**, Lean text **≈ 15 % reusable**. The 539 lines of frozen per-factor ledger (`WildRow` + `NormalForms`) are exactly what WW1 *replaces*, not what it reuses |

### 2.3 Item (4) — `StokesDualityCertificate` → **WL-c**

| | |
|---|---|
| frozen at `n = 1` | the ε-vector endpoint (`Stokes.lean`, 149 ln: `expMod2_wildValueExpR_odd`(:107), `expMod2_tame_add_wildValueExpR_odd`(:118)); the traced rows `prop_5_8_{left,right}_R` (`TrivialSelfDual.lean`); the degree-one pairing `mixedB_R_pairing_{split,ramified}` (`Hessian.lean:322,:335`) and **perfectness** `pairingR_operator_injective`(:355); the dévissage `lemma_5_11_R` and the capstone `prop_5_15_R` (`DualityAssembly.lean:485`) |
| reuse mode | **cite** for the presentation-independent core (`sigma2_pairing_operator_injective`, `TameSimple.lean:303`; the `{n}`-generic `lemma_5_7_left/right`); **template** for the rest |
| degree-`n` | S2.4 §5.4 (the clause it *closed*): `H` has trivial base and trivial first-order offset, so the cross term in `β(uv) = β(u)+β(v)+D^∨(u)(ū·D(v))` carries `D(H) = 0` and dies; the block's own central value is one hyperbolic block per handle. Lever: `handleWord_centLift_fib` (`Cores.lean:1422`, h-generic, landed). Clause 3 and clause 4 are *the same computation read in two atom families* |
| new | WW3's `PWord` denotation into `HeisLift`, the natural chain map `η_A`, and **packet `lem:composition` for nonsplit coefficients** — the one place where the frozen chain's approach (a 2156-line clone of a 2394-line dévissage) is the wrong model. See §4.1 |
| **verdict** | mathematics **100 % known** at `n = 1` and **proved** at degree `n` (S2.4 §5.4); Lean text **≈ 10 % reusable**, and the 2287-line dévissage is **WW3's to do once**, not WL-c's to do a fifth time |

### 2.4 Item (5) — `ScalarHilbertCertificate` → **WL-c** (relator side) / MC5 (marked side)

| | |
|---|---|
| frozen at `n = 1` | the trivial-module scalar Gram of `TrivialSelfDual.lean` (582 ln, the note's `⟨(a,c,d),(a',c',d')⟩ = ac' + ca' + dd'`); the `Γ_R` cup Gram `[[0,1,0],[1,0,0],[0,0,1]]` restated by SQ23 as `sqCore_cupGram` (`SqCore/Rank3.lean`, std-3), and the reading rule via `diagCoeff`/`diagCoeff_mod_four`/`diagCoeff_two` (`Cores.lean:1212,:1241,:1216`) |
| reuse mode | **cite** (SQ23's `sqCore_cupGram` is already in campaign vocabulary and prints std-3) |
| degree-`n` | S2.4 §5.5: the relator side is the degree-1 Gram `⊥ h` hyperbolic planes — the assembly MC2 already performs for `P_M`/`P_N` (`mRelWord_centLift_fib`:1435, `nRelWord_centLift_fib`:1455); the type-`L` analogue `lRelWord_centLift_fib` is **the same proof with a different factor list** |
| new | **`hHilb`** — the *arithmetic* side: `H¹(G_K,𝔽₂)` has dimension `n+2`, the mod-2 cup form is the Hilbert symbol, and Witt cancellation over `𝔽₂` puts it in `⟨1⟩ ⊥ H^{⊥(h+1)}`. **mathlib does not supply `𝔽₂`-quadratic-form classification / Witt cancellation** (S2.4 §8.1 flags it as "the least mathlib-supported item"). Clause 5's *marked* half is MC5's, not WL's (S2.4 §1, §8.2) |
| **verdict** | the **only WL item with residual mathematical risk**. The frozen chain covers the relator side at `n = 1` and MC2 covers it at degree `n`; `hHilb` is uncovered by any precedent |

### 2.5 Item (6) — `AffineDeterminantCertificate` (+ phase, + Gauss) → **WL-c**

| | |
|---|---|
| frozen at `n = 1` | `QZeroR` and its whole package (`Gauss.lean`, 252 ln) — the two-term quadratic, the polar with operator `1+U+U⁻¹`, nonsingularity, the `2^{n-1} ∓ 2^{n/2-1}` counts and the `∓2^m` finales; the extraspecial word evaluation `QZero_eq_relZPair_kappa0` (`GaussZ/RelatorGammaA.lean:223`) and the `Γ_R` residue twins (`GaussZ/GammaRD.lean`, 945 ln) |
| reuse mode | **CITE — the largest genuinely reusable block in the survey.** `Gauss.lean`'s own docstring records that the Arf/Gauss computations it calls (`SectionSix.lemma_6_6`/`lemma_6_8`/`prop_6_9_*`, `GaussZ.FinalGammaA.Action`) are "`Γ`-agnostic — abstract `q`/`qDouble q U`", and reading the statements confirms it: `prop_6_9_unramified` (`SectionSix.lean:328`) and `prop_6_9_ramified`(:381) quantify over `q : V → ZMod 2` with `IsQuadraticFp2 q`, `Nonsingular q`, `IsInvariant Hf q` — no relator, no `Γ`. **`QuadraticFp2` (108) + `SectionSix` (1056) + `GaussSigns` (768) = 1932 lines citable verbatim** |
| degree-`n` | S2.4 §5.3 + §5.6: the fibre adds with no cross term (`fib_mul_of_base_one`) and the handle fibre is `∑_j (κ(u_j,v_j)+κ(v_j,u_j))` — `h` hyperbolic planes, orthogonal because the handle letters are fresh; `ε(hyp) = +1` so the sign and the radical are the degree-1 ones; and `(−1)^n` is constant on odd `n`, which is `hSign` — **already recorded in the board's own WL note** ("unramified sign × `(−1)^{n−1} = +1` per handle pair") and available from LG5's `local_gauss_K` |
| new | WW4's `PWord` extraspecial evaluator + `HessianCertificate` (change of variables with inverse witness) + `PhaseCoverCertificate` (packet Lem 6.1 / Cor 6.2 / Def 6.3) — and the **general-`q_K` rebase** of the `Ttame`-keyed layer (R2) |
| **verdict** | mathematics **100 % known**; Lean text **≈ 40 % reusable by citation** — the best ratio of any item, and the reason WL-c's determinant half should drop a model tier |

### 2.6 The handle half, separately (V5)

SQ1's §7.5 priced "WL-b/WL-c" as one object. They are two:

```
WL-b/WL-c  =  (the n = 1 base)  ⊕  (handle stability)
```

At `n = 1`, `h = 0`. **The frozen ℚ₂ chain contains no handle at all** and therefore contributes
exactly nothing to clauses 1b/2b/3-handle/4-handle/6-handle. That half is covered instead by MC2 and
the HM lane, both landed: S2.4 §8.3's count is "of the seven group-theoretic facts §4–§5 need, six
are already sorry-free Lean theorems in `Cores.lean`, generic in the handle count and in the ambient
group", the seventh (`lRelWord_centLift_fib`) being "the same assembly as `mRelWord_centLift_fib`
with the type-`L` factor list". I re-verified all six anchors (§1.5) and the seventh's two models
(`Cores.lean:1435`, `:1455`).

So the correct decomposition of the "halving" claim is:

| half | precedent | coverage |
|---|---|---|
| `n = 1` base | frozen ℚ₂ chain (8615 ln) | mathematics **100 %**, Lean text **≈ 25 %** |
| handle stability | MC2 `Cores.lean` + HM1–HM5 (landed) | **≈ 85 %** — one new assembly (`lRelWord_centLift_fib`) plus bookkeeping |

### 2.7 What is genuinely new (V8)

1. **`hHilb`** — Witt cancellation over `𝔽₂` in dimension `n+2` (§2.4). No precedent, no mathlib
   support. *This is the item to schedule first, because it is the only one that can fail.*
2. **Nonsplit-coefficient composition-series extension** (packet `lem:composition`, ledger §3.3 B3):
   the frozen chain handles it by a full dévissage clone per word; WW3 must do it once generically,
   by five-lemma / mapping cones. Dimension equalities are explicitly *insufficient* (ledger B3).
3. **General `q_K`.** Everywhere the frozen chain reads `2` — `τ^σ = τ²`, `Ttame`, `powOmega2`,
   `omega2Exp` — the general-`K` word reads `q_K = 2^f`. F3 (`GQ2/Dyadic/{TameQuotientK,
   TameBoundary}.lean`, 2017 ln, landed) already carries the tame side; the *quadratic* side
   (`SectionSix`'s `Ttame` keying) does not yet. See R2.

---

## 3. Revised WL ticket specs

Board rows today (`tickets.md` lane WL): WL-a opus, WL-b opus, WL-c fable; unsized; all `G2`-gated
inside wave 2, which is itself **G-1**-gated. Nothing below is a dispatch trigger (§4.4).

| ID | content | files owned | deps | tier | est. ln |
|---|---|---|---|---|---|
| **WL-a** | the degree-`n` word as a `PWord (Generator n)` + `handlesProd` block; the boundary specializations via F2's `eval_killWild`/`eval_pro2` + `handleWord_of_one`; **the `n = 1` cross-identification against `wildRelator`/`wildRelatorR`** (§1.3: `show … ; norm_cast`, ~10 ln each, spike-verified) and the `eval_zpow_nat` bridge; the `ZMod 8` genuine-`ω₂` pin (`wildValueExpR_zmod8` pattern); F5 small-group counts | `GQ2/Dyadic/Words/L.lean` | F2 ✓, G-1 | **opus** | **300** |
| **WL-b** | instantiate WW1's evaluator at the `L` word; the two rows, split and ramified; the WW2 row/col-op certificate to normal form (target = the frozen `[S⁻¹(1+T), S⁻¹+1+T, 0, 0; 0, P, P+S⁻¹, 0]`, normal form = the frozen `x₁`-supported `(0,0,0,d)` with uniqueness); handle-column vanishing via `commP_wordLift_one`; **the `n = 1` regression against `liftMarking_wildValueR_u`/`liftMarking_wildValue_u`** | `GQ2/Dyadic/Certificates/LFox.lean` | WL-a, WW1, WW2 | **opus** | **420** |
| **WL-c1** | Stokes duality + Hessian + determinant + phase: the ε-vector endpoint on the `PWord`; the degree-one pairing and its perfectness (**cite** `sigma2_pairing_operator_injective`); the determinant form `⊥ h·hyp` via `handleWord_centLift_fib`; the Gauss sign via **cited** `prop_6_9_{unramified,ramified}` + `QuadraticFp2`; `hSign` from LG5 + the odd-`n` parity | `GQ2/Dyadic/Certificates/L.lean` | WL-b, WW3, WW4 | **opus** | **420** |
| **WL-c2** | the **scalar/Hilbert** certificate: the relator-side Gram `⊥ h` planes (the `lRelWord_centLift_fib` assembly, modelled on `mRelWord_centLift_fib`); and **`hHilb`** — the `𝔽₂` Witt-cancellation input, as a proved lemma if reachable, otherwise as an explicit hypothesis binder in the `BLabHypothesis` style (never an axiom — plan §0) | `GQ2/Dyadic/Certificates/LScalar.lean` (new) | WL-b, WW3 | **fable** | **220** |

**Total: 4 tickets, ≈ 1360 lines** (up from 3 tickets, unsized).

**Why split WL-c.** The four sub-items the board bundles have radically different residual risk:
determinant/phase/Stokes are template-plus-citation work with every constant known in advance
(opus), while the scalar item carries the campaign's least mathlib-supported obligation (fable). One
fable dispatch covering both would spend a scarce tier on 420 lines of well-specified fill; splitting
buys ~200 lines of fable back. If capacity forbids a fourth ticket, keep the split *inside* one fable
dispatch as an explicit two-phase brief and require a commit at the phase boundary.

**Sizing method.** Calibrated three ways: (i) against the frozen chain, discounted for vocabulary —
Layer F 1389 → WL-b 420 because WW1's structural recursion replaces the 539-line per-factor ledger
and the `Marking`-record plumbing does not recur; (ii) against **SQ23's outturn**, the campaign's
closest analogue (a brief where "everything is cited"): SQ1 §6 estimated SQ2 + SQ3 at **560** lines
and the pair landed at **853** (`SqCore/Cores.lean` 460 + `Rank3.lean` 393) — a **1.52×** overrun,
absorbed by docstrings, stress sections and the restated-instances plumbing that a citation-heavy
file accumulates; (iii) against MC2's per-core rate (≈ 950 ln/core with new proofs, ≈ 300 ln/core
when the mathematics is cited), which is the regime WL is in.

**The SQ23 overrun is applied, not ignored.** The numbers in the table are the *post*-multiplier
figures: the raw content estimates are ≈ 200 / 280 / 280 / 145 and each carries SQ23's 1.5× factor.
A worker quoting the table should treat the totals as the commitment and the raw figures as the
content budget.

**What the estimate would have been without the precedent.** The same four tickets, with the rows,
normal forms, pairings, quadratic and signs to be *discovered* rather than cited, and with no `n = 1`
regression to catch a transcription slip: ≈ 1800 lines and two of the four tickets at fable. So the
measured saving is **≈ 25 % of lines and one model tier**, not 50 %.

---

## 4. Interaction notes

### 4.1 WW subsumption — the Roe chain is a REGRESSION TARGET, not a source (V6)

**Verdict: the generic WW1–WW4 machinery subsumes the per-word ports, and the frozen chain's
correct role is (i) regression pins, (ii) proof templates, (iii) the AS4 wrapper — never a source
to port from.**

Three independent reasons, in increasing order of force.

1. **Vocabulary.** Every frozen word theorem is stated on `Marking` — a **4-field record**
   (`GQ2/Words.lean:66`) threaded through ~40 files — with the relator as a `def` on group elements.
   Every WL goal will be stated on `PWord (Generator n)` with `Marking n G` (`Parameters.lean:294`,
   `FunLike`). No frozen row, normal form, pairing or quadratic lemma can be *applied* to a WL goal;
   at best its statement can be transcribed. The WC survey reached this independently
   (`recon/wc-survey.md` §6, blocker 1).

2. **The board already schedules it that way.** WW1's spec: "Regression: at `n = 1` the evaluator's
   rows equal the hand rows `liftMarking_wildValue_u` (`GQ2/FoxHeisenberg/WildRow.lean:277`) /
   `liftMarking_wildValueR_u` (`GQ2/Roe/WildRow.lean:219`)." WW4's: "`GQ2/GaussZ/RelatorGammaA.lean:223`
   pattern, generalized." The architecture decision (plan §3 A1) was made before SQ1's discovery and
   is unaffected by it.

3. **The measured cost of the alternative.** The `Γ_A → Γ_R` port is the campaign's own controlled
   experiment in per-word cloning: `GQ2/Devissage/*` (2394 ln) was re-derived as
   `GQ2/Roe/Devissage/*` (2156 ln) for a change of **one relator**, and the clone's own module
   docstring states that "the proofs port **verbatim** onto the `r_R` spine (they only forward
   `hw : t.WildRelR` and use `d¹_R ∘ d⁰ = 0`, functoriality, the LES, and finite linear algebra —
   never unfolding the aux words)". A layer whose proofs never look at the word was nonetheless
   copied because it was written against a fixed word. Five branch words at that rate is **≈ 11 k
   lines** of avoidable work, and it is precisely what WW3 exists to prevent.

**One exception, and it is worth naming.** The quadratic/Gauss endgame (§2.5) is *already*
presentation-independent — `QuadraticFp2` + `SectionSix` + `GaussSigns` = 1932 lines over an abstract
`q`. Here "port" is wrong for the opposite reason: WW4 should be built to **consume** these, not to
re-derive them. Recommend adding to WW4's brief: *before designing `HessianCertificate`, check
whether the target factors through `IsQuadraticFp2`/`Nonsingular`/`arf`/`qDouble` so that
`prop_6_9_*` applies unchanged.*

### 4.2 With the SQ lane (SQ4, SQ5) — and a spec conflict to fix

* **SQ4** (`SqCore/Certificate.lean`, blocked on MC5) is the **marked-core** certificate — packet
  `def:core-certificate`, three items. WL owns `def:word-certificate`, six items. The two share no
  field (S2.4 §1: "`Aut(D_P)` does not occur in" the word certificate). No collision; no dependency
  either way except that AS1 consumes both.
* **SQ5** (`SqCore/Sanity.lean`) was told at merge time that "the FULL word-theorem restatement in
  SQ vocabulary [is] deferred to SQ5/WL-recon (needs the heavy `Roe.Main` import — deliberate)".
  **That is not implementable as specified.** `GQ2/Roe/Main.lean` is plain-import (it reaches
  `SourceData`/`SectionTenSources`/`PresentationLiteral`), and SQ1 §3.3 specifies
  `SqCore/Sanity.lean` with a `module` header; the module rule is one-directional (board protocol's
  ⚠ item, which names `Roe/Main` explicitly). A `module` file cannot import `Roe.Main`.
  **Recommendation:** SQ5 keeps only what SQ23 already landed at the pro-2 level
  (`gammaRPro2EquivDSqZero`, `SqCore/Rank3.lean:342`, std-3), and the *word-level* restatement moves
  to **AS4** (`GQ2/Dyadic/Instances/QTwo.lean`), which is plain-import by construction and whose
  charter is exactly this (merge-gate 8: "existing ℚ₂ capstone names still compile and the new
  `n = 1` route reproduces the statement"). Owner question Q2.
* **AS4 is cheaper than the board assumes.** Its target is
  `main_presentation_literal_roe_unconditional` — *hypothesis-free* since the L-campaign discharged
  `bLab`. So AS4 is a restatement plus the `n = 1` word identification of §1.3, not a re-derivation.

### 4.3 With the board's WL-a row (V9a)

The WL-a row still specifies the collector-cored `R_{L,K}` (draft `eq:Lword`) with pro-2 core
`x₀^{σ²}x₀[x₁,σ]·∏[x_{2j},x_{2j+1}]`. R2 signed **`L_sq`** primary on 2026-07-30, and S2.4 §2.2's
chain is written for `StandardCore.sq h`. The row is therefore stale pending G-1, which is
*designed* to re-point it ("releases the word-dependent lanes … re-points WW/W*/AS at the frozen
words", plan §6 gate G-1). **No action is needed before G-1**, and the re-point costs nothing
because §1.3 verifies the `n = 1` identification for *both* words. Worth recording only so that a
future WL-a worker does not implement the superseded word from a board row.

Note also that the board's parenthetical "`g₀ = σ₂²` — **not** `σ₂^{q_K}`" is confirmed against the
frozen source (`GQ2/Words.lean:104` `g0 = sigma2 ^ 2`, `GQ2/GammaA.lean:75`
`g0Hat = sigma2Hat ^ 2`) — but see R1: at `n = 1`, `q_K = 2`, so the frozen chain **cannot
discriminate** the two readings.

### 4.4 With G-1 timing

All of lane WL is **wave 2** and blocked on **G-1** (the simplification campaign's R5), which is
itself blocked on that campaign's R3 (the corrected `L_c`) and phase-4 items S4.3/S4.4/R4. This memo
is **preparation, not a dispatch trigger**. Its consumers, in order:

1. the **orchestrator**, at G-1, when re-pointing the WL rows (§4.3) and re-sizing them (§3);
2. **WW1/WW3/WW4's dispatch prompts**, which should carry §2's per-item target tables and §4.1's
   "consume, don't re-derive" note for the quadratic layer — these are *wave-1* tickets and can use
   the memo now;
3. **AS4**, whose scope shrinks (§4.2);
4. the **S2.4 memo's owner**, for the two corrections in §5 R3/R4, riding with the existing errata
   bundle.

---

## 5. Risks

| # | risk | assessment / mitigation |
|---|---|---|
| **R1** | **The `n = 1` base is blind to every `q_K`-vs-`2` substitution.** At `n = 1`, `q_K = 2` (§1.1), so the frozen chain cannot distinguish `τ^σ = τ^{q_K}` from `τ^σ = τ²`, nor `g₀ = σ₂^{q_K}` from `g₀ = σ₂²`, nor any `ω₂`-exponent convention that happens to agree at `f = 1`. A word transcription that is *wrong at general `K`* will still pass every `n = 1` regression | **Real and structural — the single most important limitation of the precedent.** Mitigation: WL-a must carry a **second** regression at `n = 2` or `n = 3` with `f > 1` against the F5 harness (`scripts/dyadic_sanity_counts.py`, pending) and the WW5 tree hash, not only the `n = 1` pin. Recommend adding this explicitly to the WL-a brief; it is cheap and it is the only thing standing between a `q_K` slip and AS5 |
| **R2** | **The citable Gauss layer is `Ttame`-keyed.** `prop_6_9_*` (`SectionSix.lean:328,:381`) is `Γ`-agnostic but takes `c : ContinuousMonoidHom Ttame Hf` — `Ttame` being the `q = 2` tame group. At general `q_K` the hypothesis shape changes | Bounded: F3 landed the general-`q` tame quotient (`GQ2/Dyadic/TameQuotientK.lean`, and `tq_two_equiv` is literally `refl`, so the `q = 2` instance is byte-compatible). The rebase is a hypothesis-shape change, not a re-proof. Budget it in **WL-c1**, and flag it in WW4's brief |
| **R3** | **S2.4 §8.1's inventory row is now wrong in a second place.** SQ1 corrected "`L_sq`: does not exist" for the *marked-core* input. The *word*-certificate row — "the `n = 1` adapter … AS: AS4: pending" — understates equally: the `n = 1` word theorem exists and is hypothesis-free for `L_sq` (`Roe/Main.lean:563`) and unconditional for the collector (`PresentationLiteral.lean:46`) | Bookkeeping. **Reported, not patched** (this ticket owns no other file). Should ride with the existing errata bundle alongside SQ1's `χ(σ) = 1` correction. Owner question Q1 |
| **R4** | **S2.4 §8.1 assigns `hHilb` to "WL-c" with no sizing and calls it "the least mathlib-supported item".** If it turns out to need a genuine `𝔽₂` Witt-cancellation development, WL-c2 is not a 220-line ticket | Mitigated by the split (§3): WL-c2 is isolated, fable-tiered, and may land the certificate with `hHilb` as an **explicit hypothesis binder** (the `BLabHypothesis` pattern, plan §0 — never an axiom; the nine obligations rule does not cover `hHilb`, which is an arithmetic *input*, but the hypothesis-binder discipline applies regardless). Recommend scheduling WL-c2 **first** among the WL certificate tickets, out of dependency order, precisely because it is the only one that can fail |
| **R5** | **The dévissage clone may be repeated a third time.** If WW3 is dispatched without §4.1's finding, the natural move for a WL-c worker facing nonsplit coefficients is to clone `GQ2/Roe/Devissage/*` a third time (≈ 2.2 k lines), and then WN0/WM0/WNP/WMP make it five | Mitigated by putting §4.1 in **WW3's** dispatch prompt (a wave-1 ticket, actionable now) and by an explicit prohibition in the WL-c briefs: *no file under `GQ2/Dyadic/Certificates/` may reproduce a per-word dévissage; the composition-series extension is WW3's and is consumed, not cloned* |
| **R6** | **Line estimates are calibrated, not measured.** §3's numbers rest on three analogies (frozen chain discounted for vocabulary; SQ23's 853-vs-810 outturn; MC2's per-core rate), not on a spike of WL-b/WL-c themselves — which is impossible today because WW1–WW4 do not exist | Accepted, and stated. The *risk* verdict (V4's "100 % of the mathematics") is spike- and read-verified and does not depend on the sizing; the sizing should be revisited once WW1 lands and its `n = 1` regression against `liftMarking_wildValueR_u` is green — at that moment WL-b's true rate is measurable for the first time |
| **R7** | **`Marking` is a 4-field record threaded through ~40 files** (WC survey §6, blocker 1). Anything that tries to reuse a frozen row *by generalizing it in place* will fan out across the frozen ℚ₂ development, which plan §3 A6 freezes | Structural, and it is exactly why §4.1's verdict is "regression target, not source". No frozen file is edited by any WL ticket |

---

## 6. Provenance

### 6.1 The spike

`WlSpike4.lean` (63 ln, scratchpad only, never committed), elaborated with
`LEAN_PATH="$(lake env printenv LEAN_PATH)" lean <path>` from the sibling worktree
`~/claude/gq2-dyadic-mc` (branch `dyadic-mc`, built at `337647f`) — read-only: no `lake build`, no
write outside the scratchpad, no edit to any lane's sources. **0 errors, 0 sorries, 0 warnings.**
Declarations proved: `eval_zpow_nat`, `eval_g0W`, **`eval_lWord`**, **`eval_lSqWord`**, `eval_tameW`.
Two earlier iterations (`WlSpike.lean`, `WlSpike2.lean`) established the negative half — that
`x ^ (2:ℤ) = x ^ (2:ℕ)` is *not* `rfl` for an abstract group and that `simp` does not bridge the
`OfNat` numeral, while `norm_cast` does.

### 6.2 Campaign §16 labelling

* **Claimed as proof:** §1.3's five identifications (spike-typechecked against the real repo at
  `337647f`); every file:line anchor in §1.4/§1.5 (read and verified); §1.1's `n = 1 ⟹ K = ℚ₂`
  (read off `FieldParameters` and the repo's own `by decide` instance).
* **Not promoted:** §3's line estimates (calibrated analogies — R6); §2's percentage coverages
  (informed judgement over a verified inventory, not measurements); §4.1's "≈ 11 k lines of
  avoidable work" (an extrapolation from one measured clone).
* **§16 stop conditions triggered: none.** Nothing in the survey contradicts the packet, and no
  statement was found to be false.

### 6.3 Numbered owner questions

1. **Errata routing.** R3 adds a second correction to S2.4 §8.1's inventory (the *word*-certificate
   `n = 1` inputs exist and are hypothesis-free for both `L` candidates). Ride with the existing
   errata bundle alongside SQ1's `χ(σ) = 1` correction, or hold? *Recommendation: ride with it —
   same file, same reviewer, zero marginal cost.*
2. **SQ5 vs AS4** (§4.2). The "full word-theorem restatement in SQ vocabulary" cannot live in a
   `module`-header `SqCore/Sanity.lean` because `GQ2/Roe/Main.lean` is plain-import. Move it to AS4
   (`GQ2/Dyadic/Instances/QTwo.lean`), or re-spec `SqCore/Sanity.lean` as plain-import?
   *Recommendation: move to AS4 — it is AS4's charter (merge-gate 8) and it keeps the SQ lane's
   import surface light.*
3. **WL-c split** (§3). Accept four WL tickets (WL-a, WL-b, WL-c1 opus, WL-c2 fable) in place of
   three, and schedule **WL-c2 first** among the certificate tickets because `hHilb` is the only
   WL item that can fail? *Recommendation: yes on both.*
4. **Wave-1 spillover.** §2's per-item target tables and §4.1's "consume, don't re-derive" note for
   the quadratic layer are useful to **WW1/WW3/WW4 now**, which are wave-1 and G-1-independent in
   their generic halves. Authorize the orchestrator to fold this memo's §2 + §4.1 into the WW
   dispatch prompts, or keep WW briefs as written until G-1?
5. **R1's second regression.** Authorize WL-a to carry a `q_K > 2` sanity pin (an `f > 1` instance
   against F5 + WW5's hash) in addition to the `n = 1` pin, given that the `n = 1` base is
   structurally blind to `q_K`-vs-`2` slips? *Recommendation: yes — it is the cheapest available
   insurance against the one class of error the frozen precedent cannot catch.*

---

## 7. One-paragraph summary

Lane WL's `n = 1` base is not merely *related to* the frozen ℚ₂ development — for type `L` the
parameter structure forces `n = 1 ⟹ f = 1 ⟹ q_K = 2 ⟹ K = ℚ₂`, so the base **is** ℚ₂, and ℚ₂ is
finished for *both* candidate `L` words: the board's collector-cored `R_{L,K}` at `m = 0` is
letter-for-letter `GQ2.Marking.wildRelator` and R2's `R^sq_{L,1}` is `wildRelatorR`, both verified in
a scratch spike where every `ω₂`/conjugation/commutator node is definitional and the sole bridge is
one `norm_cast` on the integer-power nodes. Behind those two words sit 8615 sorry-free lines (not
SQ1's 1855: the estimate omitted the word/limit layer, the normal forms, the 2287-line dévissage
engine and the whole `GaussZ` package) terminating in the hypothesis-free
`main_presentation_literal_roe_unconditional`. But the frozen text is written on a 4-field `Marking`
record over ℚ₂ and every WL goal will be written on `PWord (Generator n)` over general `K`, so no
frozen theorem applies to a WL goal: the measured saving is **≈ 25 % of Lean lines and one model
tier**, not the conjectured half — with the caveat that the *risk* saving is total, since every row,
normal form, pairing, quadratic, constant and sign is already a theorem. The handle half, which the
"halving" estimate did not separate, gets nothing from the Roe chain (there are no handles at
`n = 1`) and ≈ 85 % from MC2's h-generic `Cores.lean` plus the landed HM lane. Three items remain
genuinely new — `hHilb` (Witt cancellation over `𝔽₂`, the only WL item that can fail), the
nonsplit-coefficient composition-series extension, and general `q_K` — and the revised board is four
tickets, ≈ 1360 lines, with WL-c split so that one fable dispatch is spent on the item that deserves
it. The chain's correct role is settled by the campaign's own controlled experiment: a 2394-line
dévissage layer whose proofs "never unfold the aux words" was nonetheless cloned at 2156 lines for a
one-relator change, so the frozen development must be consumed as **regression targets, proof
templates and the AS4 wrapper — never as a source to port** — with the single exception of the
1932-line presentation-independent Gauss endgame, which WW4 should cite rather than rebuild.

---

*End of memo. Ticket WL-recon, branch `dyadic-wl`.*
