# WC-* recon survey — word / Fox / Stokes / Hessian infrastructure (2026-07-28)

Read-only survey of the repo at master `d0714a7`, taken at campaign setup. Seed material for
tickets F2 and WW1–WW5. File:line anchors verified at survey time.

## 1. How relator words are represented, and how ω₂ is handled

**There is no inductive word-syntax type anywhere in `GQ2/`.** No `PWord`, no
`one/gen/mul/inv/conj/comm/zpow/z2pow/profPow` constructor set, no reflection/denotation
function, no `decide`-driven word normalizer.

Words are represented in **three coexisting styles**:

**(a) Polymorphic "word shape" functions** — a word is a `def` taking group elements and
returning a group element, generic over `[Group G]`, naturality by `simp [map_mul, …]`:
- `GQ2.drWord {G} [Group G] (s x y : G) : G` — `GQ2/Roe/DRPresentation.lean:83`; naturality
  `map_drWord` :89. The only free-standing polymorphic word function.
- The Γ_A/Γ_R relators are phrased on the fixed 4-tuple structure:
  - `structure Marking (G) := (σ τ x₀ x₁ : G)` — `GQ2/Words.lean:66-71`; functorial action
    `Marking.map (f : G →* H)` — `GQ2/Subdirect.lean:34`.
  - Auxiliary letters as `Marking` methods: `sigma2`/`u`/`u0`/`u1`/`d0`/`z0`/`c0`/`g0`/`dg`/
    `hc`/`h0` — `GQ2/Words.lean:90-113`; relations `TameRel` :118, `WildRel` :121,
    `Pro2Core` :128, `Admissible` :132, `admissibleCount` :141.
  - Roe letters `aR` :75, `y1R` :80, `cR` :84, `wildValueR` :94, `WildRelR` :98,
    `AdmissibleR` :108 — `GQ2/Roe/Words.lean`.
  - Relator *values*: `Marking.tameValue` `GQ2/FoxHeisenberg/Basic.lean:38`,
    `Marking.wildValue` :48.

**(b) Elements of `FreeProfiniteGroup (Fin k)`** — the honest profinite relators:
- `univMarking : Marking (FreeProfiniteGroup (Fin 4))` — `GQ2/GammaA.lean:172`; profinite-ω₂
  letters and relators `tameRelator` :85, `wildRelator` :89 — `GQ2/GammaA.lean:61-89`.
- Roe: `aRHat` :61, `y1RHat` :66, `cRHat` :70, `wildRelatorR` :77 — `GQ2/Roe/GammaR.lean`.
- Bare profinite relators: `d0Relator : FreeProfiniteGroup (Fin 3)`
  `GQ2/DyadicPresentation.lean:45`; `drRelator` `GQ2/Roe/DRPresentation.lean:107`.

**(c) Elements of Mathlib's `FreeGroup (Fin 4)`** — only where the target must be an ordinary
free group so `FreeGroup.lift` applies (the Stokes layer): `freeMarking`
`GQ2/FoxHeisenberg/Traced.lean:67`; `fgTame` `GQ2/FoxHeisenberg/Heisenberg.lean:535`. Because
`FreeGroup` is not profinite, ω₂ cannot be applied there. The workaround is a
**de-ω₂-ified word with a literal `ℕ` exponent**: `wildValueExp t (e : ℕ)` `Traced.lean:75` and
`wildValueExpR t e` `GQ2/Roe/Words.lean:165`, plus bridges `wildValueExp_eq_wildValue`
`Traced.lean:122` / `_of_dvd` :133 and `wildValueExpR_eq_wildValueR` `Roe/Words.lean:183`, and
naturality `wildValueExp_map` :114 / `wildValueExpR_map` :174. **This "replace `^ω₂` by `^e` at
`e = omega2Exp (Monoid.exponent target)`" trick — profinite form + ℕ-exponent form + `_eq_`
bridge + `_map` naturality, ~4 hand-written lemmas per word — is the load-bearing pattern any
generic-n word certificate must reproduce (or generate from reflected syntax).**

**ω₂ handling.** Two layers, provably matched:
- *Finite level* — `GQ2/Words.lean:42` `omega2Exp (n : ℕ) : ℕ`; `powOmega2 x := x ^ omega2Exp
  (orderOf x)` :49 (notation `x^ω₂`). Congruences: `oddPart_dvd_omega2Exp` `GQ2/Omega2.lean:26`,
  `omega2Exp_modEq_one` :38, level-coherence `omega2Exp_modEq` :60, exponent-independence
  `powOmega2_pow_eq` :89, naturality `powOmega2_map` :96, Appendix-B pin
  `omega2Exp_appendixB_value` :108.
- *Profinite level* — `GQ2/Zhat.lean`: `Zhat : ProfiniteGrp` :119, `Zhat.ofInt` :126,
  `omega2 : Zhat` :155, `zpowHatHom` :175 / `zpowHat` with notation `x ^ᶻ γ` :181 (requires
  `[CompactSpace G] [TotallyDisconnectedSpace G]`), naturality `map_zpowHat` :207, and the
  headline `zpowHat_omega2` :226 / `map_zpowHat_omega2` :253
  (`f (x ^ᶻ ω₂) = powOmega2 (f x)`).
- Per-letter fidelity bridges profinite ↔ finite are hand-written: `GQ2/GammaA.lean:107-139`
  (11 lemmas for `h₀`'s ledger), then `map_tameRelator_eq_one_iff` :146,
  `map_wildRelator_eq_one_iff` :153; Roe twins `GQ2/Roe/GammaR.lean:99-128`. A reflected syntax
  would replace exactly these.
- ⚠ `Zhat` carries **only group structure** — no ring structure, so `ω₂·ω₂ = ω₂` is unavailable
  (`Zhat.lean:37-38`); `zpowHat_mul` (:195) gives only exponent-addition. `z2pow`/idempotence
  facts need new API (packet Lem. 2.2 finite evaluation is the intended workaround).

## 2. The 4-generator Fox complex / first-order derivative

Not matrices, not `decide` — **hand proofs, per-factor, via a semidirect-product lift**:
- `WordLift A C` (`= A ⋊ C`) — `GQ2/FoxHeisenberg/Basic.lean:76`, group instance :101.
- `liftMarking t x : Marking (WordLift A C)` `Basic.lean:321`; `d0 t : A →+ (Fin 4 → A)`
  `Basic.lean:326`; `d1Fun t x : A × A := ((liftMarking t x).tameValue.u,
  (liftMarking t x).wildValue.u)` `Basic.lean:334`. **The Fox derivative is literally "the `.u`
  coordinate of the evaluated relator", never a formal derivative.**
- Additivity by functoriality (not induction on words): `d1Fun_add` `Basic.lean:345`. Bundled
  `d1 t` :378; complex identity `d1Fun_comp_d0` :385; complex `H0w` :404, `Z1w` :407,
  `B1w` :411, `H1w` :415, `H2w` :427.
- **Closed-form rows hand-computed per relator factor.** Γ_A: `GQ2/FoxHeisenberg/WildRow.lean`
  (`liftMarking_u0_u` :41 … assembled `liftMarking_wildValue_u` :277; ramified twins :306-397).
  Tame row `d1Fun_tame` `Basic.lean:437`. Γ_R: `GQ2/Roe/FoxBasic.lean` (`d1FunR` :63,
  `d1FunR_fst` :69 — tame row shared definitionally, `d1FunR_add` :86, `d1R` :116,
  `d1FunR_comp_d0` :131, complex :149-190); rows `GQ2/Roe/WildRow.lean` (assembled
  `liftMarking_wildValueR_u` :219 / `_ramified` :244, swap stress tests :271/:281,
  trivial-module collapse `d1FunR_of_trivial` :295).
- The "Jacobian matrix" `[S⁻¹(1+T), S⁻¹+1+T, 0, 0 ; 0, P, P+S⁻¹, 0]` exists **only in
  docstrings** (`Roe/WildRow.lean:24`). No `Matrix`-valued Jacobian object exists.
- `decide` used only for tiny stress tests (`expMod2_fgTame` `Heisenberg.lean:540`,
  `expMod2_wildValueExpR_three` `Roe/Stokes.lean:132`, `wildValueExpR_zmod8`
  `Roe/Words.lean:244`).
- Consumption: `GQ2/WordCohBridge.lean` identifies `ContCoh.Z1 Γ_A A ≃+ Z1w (markC q)`
  (`z1Equiv` :438, `h1Equiv` :467) by evaluation at the four generators; `GQ2/WordCoh2.lean`
  does degree 2 via central extensions (`TwoCocycle` :40, `CentExt` :69, `relZPair` :173).

## 3. Stokes (second-order) and Heisenberg evaluation — two-tier generality

*Generic in `n`* (`{n : ℕ}`, words in `FreeGroup (Fin n)`), `GQ2/FoxHeisenberg/Heisenberg.lean`
`section Stokes` (line 319 ff.):
- `HeisLift A C` on `A × A^∨ × 𝔽₂ × C` — :36, mult :51.
- `stokesEval (c : Fin n → C) (x : Fin n → A) (y : Fin n → ElemDual A) :
  FreeGroup (Fin n) →* HeisLift A C` :325 (a plain `FreeGroup.lift`).
- `expMod2 (i : Fin n) : FreeGroup (Fin n) →* Multiplicative (ZMod 2)` :330; `freeExp` :382 +
  `freeExp_toAdd` :387.
- Conjugation models `conjPa` :363, `conjQlam` :463; factorizations `stokesEval_eq_rhs` :426,
  `stokesEval_eq_rhsR` :504.
- **Lemma 5.7 both forms, fully generic in n**: `lemma_5_7_left` :445, `lemma_5_7_right` :523.
- Bilinearity toolkit, generic in n: `GQ2/MixedBilinear.lean:31-110`.

*Fixed at 4 generators*: `heisMarking` `Heisenberg.lean:306`, `mixedB` :312, `markVec`
`Traced.lean:64`, `freeMarking` :67, bridges `heisMarking_eq_map` :151, `bridge_tame` :168,
`bridge_wild` :217, exponent pin `omega2Exp_exponent_heis_cast` :275, Prop-5.8 rows
`mixedB_tameRow` :196, `mixedB_wildRow` :319, `prop_5_8_left` :349, right versions :415-452.
Γ_R side: `mixedB_R` `GQ2/Roe/FoxBasic.lean:209`, `bridge_wildR` :219; Stokes ε-vector work
`GQ2/Roe/Stokes.lean` (`expMod2_wildValueExpR` :85, `_odd` :107, endpoint :118).

**The Stokes machinery is already `n`-generic; only the word inputs and the marking/pairing
wrappers are hard-wired to 4.**

## 4. Hessian / quadratic-form extraction

**Pure per-factor hand ledger, no certificate structure.**
- Normal forms: `x1Supported (d) : Fin 4 → V := ![0,0,0,d]` `GQ2/Roe/NormalForms.lean:68`
  (Γ_A twin `x0Supported` `GQ2/FoxHeisenberg/HessianRow.lean:44`); `lemma_5_13_split_R` :95,
  `lemma_5_13_ramified_R` :130 (existence AND uniqueness of the representative); Γ_A twins
  `HessianRow.lean:647,696`.
- Hessian ledger `GQ2/Roe/Hessian.lean`: base-slice facts :90-116; per-factor `.z`/`.a` entries
  :138-236 (e.g. `x1_sq_z` :187 diagonal `λ(d)`; `cR_z` :211 symplectic `λ(U⁻¹d)+λ(Ud)`);
  assembled `heisMarking_wildValueR_z` :258 (split `=λ(d)`) / `_ramified` :289
  (`=λ((1+U+U⁻¹)d)`); pairings `mixedB_R_pairing_split` :322 / `_ramified` :335; nondegeneracy
  `pairingR_operator_injective` :355 (thin re-export of `sigma2_pairing_operator_injective`
  `GQ2/TameSimple.lean:303`).
- **Proof style: chains of `rw [HeisLift.mul_z_of_trivial …]` peeling the product left-to-right,
  using "every right factor has `.a = 0`" to kill cross-terms.** No row/column-operation data,
  no change-of-variables object, no matrix, no `decide`.
- Quadratic layer (presentation-independent): `GQ2/QuadraticFp2.lean` (`polar` :53,
  `IsQuadraticFp2` :58, `Nonsingular` :77, `arf` :91, Wall doubling `qDouble` :96). Γ_R
  word-quadratic: `GQ2/Roe/Gauss.lean` (`QZeroR` :71, `QZeroR_split` :82, `QZeroR_eq_qDouble`
  :94, `polar_QZeroR` :121, `QZeroR_nonsingular_ramified` :134, Gauss counts :175/:192, sign
  finales :208/:221). Γ_A extraspecial route: `GQ2/GaussZ/RelatorGammaA.lean` (`Sd C V` :51,
  `kappa0Cocycle` :123, `graphSdHom` :165, punchline `QZero_eq_relZPair_kappa0` :223 — the two
  relator words evaluated in `CentExt κ⁰` ARE the paper's (83) quadratic). `relZPair` =
  `GQ2/WordCoh2.lean:173`. There is no `Extraspecial` definition (docstring-only phrase).
- **No certificate structure of any kind exists**: `grep -rn "structure .*Cert|Certificate"
  GQ2` returns nothing.

## 5. Γ_A / Γ_R and the profinite presentation infrastructure

Both are **marked-quotient (intersection-of-admissible-kernels) constructions** — the pro-2
condition on the wild part is part of the presentation datum:
- Generic infra: `FreeProfiniteGroup (X : Type u)` `GQ2/FreeProfinite.lean:38`, universal
  property `homEquiv` :56; `relatorSubgroup` (closed normal closure)
  `GQ2/ProfinitePresentation.lean:34`, `profinitePresentation` :43. **Already generic in `X`** —
  available at `Fin (n+3)` unchanged.
- Γ_A: `Marking.toHom` `GQ2/GammaA.lean:164`, `univMarking` :172,
  `surjective_of_map_generates` :186, `IsAdmissibleU` :206, `NA := ⨅ {admissible open normal U}`
  :211, `GammaA := profiniteQuotient NA` :226, certificate `NA_le_ker` :234. Literal Thm 1.2:
  `main_presentation_literal` `GQ2/PresentationLiteral.lean:46`.
- Γ_R: `IsAdmissibleUR` `GQ2/Roe/GammaR.lean:176`, `NR` :182, `GammaR` :196, `NR_le_ker` :205,
  pushforward `Marking.map_admissibleR` :144.
- Limit facts: `GQ2/AdmissibleLimit.lean` (`generates_univMarking_map` :104,
  `tameRelator_mem_NA` :155, directedness :231/:255, domination :278, characterization :336,
  `wildCore` :357, `isProP_wildCore` :375). Roe twin `GQ2/Roe/AdmissibleLimit.lean`.
- Bare presentations using `profinitePresentation` directly: `D0Full/D0`
  `GQ2/DyadicPresentation.lean:56,62`; `DRFull/DR` `GQ2/Roe/DRPresentation.lean:116,121` with
  `drLiftHom` :185.

## 6. Missing for generic-n words — all three confirmed

| Claim | Verdict |
|---|---|
| No reflected `PWord` syntax | **Confirmed** — no `inductive` in `GQ2`; words are polymorphic `def`s, `Marking` methods, or free-group elements |
| No generic Fox-Jacobian evaluator over group rings | **Confirmed** — no `MonoidAlgebra` anywhere (docstring in `Roe/Labute/GradedLie/Magnus.lean:39` explains it is *avoided*); rows are per-factor theorems |
| No elementary row/col-op certificate machinery | **Confirmed** — no `Certificate` structure, no `Matrix`-valued Jacobian (the only real `Matrix` use is `evalMatrix`/`coordMatrix` over `ℤ₂` in `MarkedMatching.lean:485,874`) |

Additional generic-n blockers to budget:
1. **`Marking` is a 4-field record** threaded through ~40 files. Anything (n+3)-generator needs
   a `Generator n → G` replacement or a parallel tower.
2. **ω₂ cannot be applied inside `FreeGroup`** — the two-form discipline (see §1c) must be
   generated, not hand-written, at generic n.
3. Per-letter fidelity bridges are hand-written and quadratic in word length.
4. `Zhat` has no ring structure (see §1).
5. Good reuse: `stokesEval`/`expMod2`/`freeExp`/`lemma_5_7_left/right` + all of
   `MixedBilinear.lean` are `{n}`-generic; `FreeProfiniteGroup`/`profinitePresentation` generic
   in `X`; `QuadraticFp2` and `sigma2_pairing_operator_injective` presentation-independent. The
   reflected-certificate work plugs into these rather than replacing them.
