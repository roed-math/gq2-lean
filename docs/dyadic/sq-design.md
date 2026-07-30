# SQ1 — `marked_square_core_rank3`: design memo for the `L_sq` rank-3 marked core

**Ticket SQ1** (dyadic campaign, lane SQ; branch `dyadic-sq1`, worktree `~/claude/gq2-dyadic-ww`,
from `dyadic` at `9439dc3`, census 11). Commissioned at gate **R2**, where the owner selected
**`L_sq` (the stabilized square-commutator)** as the primary word candidate against the S2.4
memo's `L_tw` recommendation. The commissioned deliverable is the rank-3 marked-core /
orientation theorem whose existence dissolves `L_sq`'s gate-C park by selection semantics
(S2.4 §7.3, §9.2(4)).

**Authority order.** (1) the packet `dyadic-presentations-formalization-proof.tex`;
(2) S2.4's memo (`~/claude/general_2adic/artifacts/reports/marked-stabilization-memo.md`),
whose §2.4 supplies the Lean-ready statement shape; (3) MC1 (`mc-design.md`) for memo format and
the frames/lifting vocabulary; (4) this campaign's `plan.md` §0 binding constraints.

**Scope.** The rank-3 core piece **only**. `HandleMixLift` (S2.4 §2.4, Lemma 6.3) and the
degree-`n` handle stabilization are explicitly **out of scope** — they are MC5's, and a parallel
spike MC-HM owns them. This memo writes no `.lean`; its only committed artefact is itself.
Every Lean claim below was typechecked against the real repo in a scratch spike (§5).

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|---|---|
| **V1** | Is `marked_square_core_rank3` a new theorem? | **NO.** The `L_sq` rank-3 pro-2 core **is `D_R`**, the frozen Roe development's core, *letter for letter* — `(x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]` = `GQ2.drWord` (`GQ2/Roe/DRPresentation.lean:83`), same conjugation and commutator conventions. The obligation is **discharged** by existing sorry-free ℚ₂ assets. Spike-verified (§5, clause (e)). §1.2 |
| **V2** | Orientation: closed form or Hensel? | **HENSEL — and already computed.** `χ_sq(σ,x₀,x₁) = (S, X, Y)` with `X` the unique root of `Z³+2Z²+1` in `ℤ₂` (Hensel at the approximate root `1`), `S·(X²+X+1) = −X³`, `Y = −X²`. No closed form exists (the cubic has no rational root); `X ≡ 5 (16)`, `S ≡ 13 (16)`, `Y ≡ 7 (16)`. This is exactly the page's `C_mark = 3` content, and it is **complete** in `GQ2/Roe/OrientationRoot.lean` + `ChiR.lean`. §1.4 |
| **V3** | Does `GQ2.Roe.Labute.bLab` apply? | **YES, DIRECTLY — no new instance, no new binder.** `BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:141`) is *literally specialized to `D_R`*, i.e. to this very core, and `bLab` (`GQ2/Roe/Labute/Assembly.lean:249`) proves it sorry-free at **std-3 only**. The single biggest cost driver of this ticket is **zero**. §2 |
| **V4** | Matching-engine port cost | **There is no engine port at rank 3.** `MarkedMatching.lean`'s masters→span→`evalMatrix`→solve→contract pipeline was *already run for this core* — its `f : D_R ≃ D₀` is the sq core's abstract isomorphism. SQ2+ is `≈ 780` lines of h-generic scaffolding + transport + interface, in **4 tickets**, all opus tier. Compare the ported-from-scratch alternative: `MarkedMatching`+`DRAbelianization`+`DRDemushkin`+`DRWordCoh` = **3246** lines. §3, §6 |
| **V5** | Does S2.4's data survive contact with the repo? | **Every prediction matches exactly** — frame `ℤ/2 ⊕ ℤ₂ ⊕ ℤ₂` with `t = x̄₁ − 2x̄₀` and forced row on `x̄₁` (S2.4 R6, verbatim); Gram `⟨x₁,x₁⟩=1, ⟨σ,x₀⟩=⟨x₀,σ⟩=1`, else `0` (S2.4 §1.1 PROBE F, verbatim). **One exception, and it is a genuine error**: S2.4 §1.1's "`χ(σ) = 1` for type `L`" is **FALSE for `L_sq`** — `χ_sq(σ) = S`, of infinite order. §1.8, §7 R1 |
| **V6** | Consequence for S2.4 §9.2(1) (candidate-independence of `HandleMixLift`) | **Weakened, for `L_sq` specifically.** §9.2(1) derives candidate-independence from "all three cores have `χ(σ) = 1` and `σ` in a hyperbolic pair". The second half holds for `L_sq`; the first does not. The `χ`-trivial subspace of the `L_sq` frame is **not** `⟨σ̄⟩ ⊕ (handle plane)` but a rank-1 free `ℤ₂`-module transverse to `σ̄`. Reported to MC5/MC-HM, **not patched here**. §1.4, §7 R1 |
| **V7** | Axiom hygiene | **Census stays 11.** `marked_square_core_rank3` prints `[propext, Classical.choice, dyadicOrientation, peripheralCyclotomicAction, Quot.sound]` = std-3 + **B3c + B8, both pre-existing**. The new h-generic definitions `chiSq`, `nuSq`, `dsqEquivDR` print **std-3 only**. Spike-measured (§5.3). |
| **V8** | Honest R2 re-read: does anything make `L_tw`'s fallback preferable? | **No — the opposite.** S2.4 §13 Q3 framed R2 as "which rank-three theorem would the owner rather commission"; the answer is now asymmetric: **`L_sq`'s is already delivered and unconditional**, `L_tw`'s (the rank-3 twisted square) remains verifier-only. Two caveats are recorded honestly in §7 (R1's `χ(σ)` correction; R4's ℚ₂-only reach of the discharge). Neither favours `L_tw`. §7.2 |

**Bottom line in one sentence.** The owner's R2 selection landed on the one type-`L` candidate
whose rank-3 obligation was *already proved in this repository* — `L_sq` at `n = 1` is Roe's own
candidate `Γ_R`, whose terminal theorem `main_presentation_literal_roe_unconditional`
(`GQ2/Roe/Main.lean:563`) is hypothesis-free — so the commissioned `marked_square_core_rank3`
reduces from "a 2-adic orientation computation" to an interface adapter.

---

## 1. The core's data, computed

### 1.1 The word, exactly

Read from the harness (READ-ONLY, other repo):
`~/claude/general_2adic/dyadic_search/families/q2.py:414` `pro2_core_square_commutator`,
`families/L.py:1454` `sq_core`, `L.PRO2_CORES["square-commutator"]` (`q2.py:396`),
`L.SQ_PRO2_CORES`. Core hash at `n = 1`: `69635f5b7c007aaf60664e305760c28a55f76be4bfb0ead768b75e898f775c7b`
(`L.SQ_CORE_HASHES[1]`).

```text
degree n = 2h+1, generators  σ, x₀, x₁, x₂, …, x_{2h+1}   (rank n+2 = 3+2h)

  C_sq(h)  =  (x₀^σ)⁻¹ · x₀⁻³ · x₁² · [x₁, x₁^σ]  ·  ∏_{j=1}^{h} [x_{2j}, x_{2j+1}]
             └──────────────── the rank-3 core ────────────────┘  └── handle block ──┘
```

Conventions (campaign §3, and identical in Lean): `x^g = g⁻¹xg`, `[x,y] = x⁻¹y⁻¹xy`,
`x⁻³ = (x³)⁻¹`. The full relator this core specializes from is
`R^sq_{L,n} = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}] · ∏[x_{2j},x_{2j+1}]`
(`L.py:1238`, `q2.square_commutator_word` at `q2.py:186`); gate C kills `τ` and sends
`g^{ω₂} ↦ g`, so `σ₂ ↦ σ` and `(x₀⁻³τ)^{ω₂} ↦ x₀⁻³`.

### 1.2 The identification: this core **is** `D_R`

`GQ2/Roe/DRPresentation.lean:83-84`:

```lean
def drWord {G : Type*} [Group G] (s x y : G) : G :=
  (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)
```

with the file's own docstring (`:17-31`) reading
`D_R = ⟨s, x, y | r₂ = (x^s)⁻¹x⁻³y²[y,y^s] = 1⟩_pro-2`, `s = σ`, `x = x₀`, `y = x₁`, and
`x^g = g⁻¹xg` / `[x,y] = x⁻¹y⁻¹xy` stated verbatim. Factor by factor:

| harness factor | Lean factor | match |
|---|---|---|
| `Inverse(Conjugate(X0, SIGMA))` | `(conjP x s)⁻¹` | ✓ |
| `IntegerPower(X0, -3)` | `(x ^ 3)⁻¹` | ✓ |
| `IntegerPower(X1, 2)` | `y ^ 2` | ✓ |
| `Commutator(X1, Conjugate(X1, SIGMA))` | `commP y (conjP y s)` | ✓ |

Same four factors, same order, same conventions. `sqWord s x y = drWord s x y` holds **by
`rfl`** (spike clause (a)).

The identification extends to the *whole word*, not merely the core.
`GQ2/Roe/Words.lean:20`:

```text
Γ_R = ⟨σ, τ, x₀, x₁ ∣ τ^σ = τ², r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}]⟩
```

which is `R^sq_{L,1}` plus the tame relation `τ^σ = τ^{q_K}` at `q_K = 2`. So **`L_sq` at
`n = 1` is Roe's candidate `Γ_R`**, and `GQ2/Roe/Main.lean:563`
`main_presentation_literal_roe_unconditional : Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)`
is the rank-3 word theorem, unconditional. (Discovery affecting the **WL lane**; see §7.5.)

**Why nobody noticed.** MC1 came within one line of it: `mc-design.md:163-166` cross-checks its
cup-Gram reading against "the ℚ₂ relator `r₂`" and finds `drCup_obs`. It read `r₂` as *the* ℚ₂
relator rather than as *the square-commutator candidate's core*. S2.4 §8.1's inventory row
(`the rank-3 inputs`) records `L_sq: does not exist` — correct about the campaign's own
artefacts, wrong about the repository, because the two campaigns index cores by different
names (`D_R` vs `pro2_core_square_commutator`).

### 1.3 The abelianization frame (the `BDecomposition` analogue)

Abelianizing kills both commutators and leaves the relation vector
`ρ_sq = −4x̄₀ + 2x̄₁` (`drWord_comm`, `DRPresentation.lean:97`:
`drWord s x y = (x⁴)⁻¹y²`; `abMk_relR`, `DRAbelianization.lean:361`). Smith normal form over
`ℤ₂` gives `(2,0,0)` in the basis `(t, σ̄, x̄₀)` with `t := x̄₁ − 2x̄₀`, so

```text
L_sq  :=  D_sq^{ab}  ≅  ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀,        x̄₁ = t + 2x̄₀   (forced row)
```

Repo: `BRDecomposition` (`GQ2/Roe/DRAbelianization.lean:450`, four fields), existence
`br_decomposition` (`:462`), forced row `br_decomposition_Y` (`:478`):
`e (abMk drY) = ofAdd (1, 0, 2)`. Coordinate functionals `sHomR` (`:259`), `xHomR` (`:268`),
`tHomR` (`:277`); combined `phiHomR` (`:295`); the iso `phiEquivR` (`:436`).

Side-by-side with the two precedents the campaign already cites:

| | `D₀` (`SectionThree.lean:422`) | **`D_sq` = `D_R`** (`DRAbelianization.lean:450`) | `D_M` (MC1 §2.1) |
|---|---|---|---|
| relation | `2Ā + 4S̄ = 0` | **`−4x̄₀ + 2x̄₁ = 0`** | `2Ā + 2^αC̄₀ = 0` |
| torsion `t` | `Ā + 2S̄` | **`x̄₁ − 2x̄₀`** | `Ā + 2^{α−1}C̄₀` |
| free `ℤ₂` coords | `S̄`, `Ȳ` | **`σ̄`, `x̄₀`** | `B̄, C̄₀, D̄` |
| forced row | `Ā ↦ (1,−2,0)` | **`x̄₁ ↦ (1,0,2)`** | `Ā ↦ (1,0,−2^{α−1},0)` |

Note the structural difference from the collector/`D₀` frame: for `D₀` the forced row carries
`−2` in the *`S̄`* slot; for `D_sq` it carries `+2` in the *`x̄₀`* slot, and the marked letter
`σ̄` is a **free coordinate untouched by the relation**. This is S2.4 R6's prediction
(`t = −2x̄₀ + x̄₁`, forced row on `x̄₁`) reproduced verbatim, and it means the SQ lane's
frame structure is `NDecomposition`-like (no forced row *on a marked letter*) rather than
`MDecomposition`-like.

**Torsion / `q`-invariant.** `t² = 1` (`tbarR_sq`, `:368`), torsion subgroup `≅ ℤ/2`
(`torsionEquivZMod2`, `:544`), hence `demushkinQ D_sq = 2` (`demushkinQ_DR_eq_two`, `:576`).

### 1.4 The orientation — **Hensel, not closed form** (the `C_mark = 3` coordinate)

This is the coordinate the page prices at 3 and the one the owner commissioned. Verdict:
**it is a genuine Hensel-root computation, and it is finished.**

The descent system. `IsLabuteOrientationDatum S X Y`
(`GQ2/Roe/CrossedDerivation.lean:183`) says the χ-twisted crossed derivation of `drWord`
vanishes identically:

```lean
def IsLabuteOrientationDatum (S X Y : ℤ_[2]ˣ) : Prop :=
  ∀ Ds Dx Dy : ℤ_[2],
    drWord (⟨Ds, S⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Dx, X⟩ ⟨Dy, Y⟩ = 1
```

Solved (`isLabuteOrientationDatum_iff`, `:201`; extraction `:316`) into four equations —
character relation `Y² = X⁴` plus the three Fox coefficients `c_x = c_s = c_y = 0`
(`cxR` `:104`, `csR` `:112`, `cyR` `:119`) — whose **unique** solution is

```text
X³ + 2X² + 1 = 0 ,      S·(X² + X + 1) = −X³ ,      Y = −X² .
```

The `Y = +X²` branch is refuted through `(X−1)(X²−X−1) = 0` then `c_y = 2 ≠ 0`
(`isUnit_sq_sub_self_sub_one_of_odd`, `OrientationRoot.lean:177`; `:316`ff).

**The root is Hensel and opaque.** `OrientationRoot.lean:99` `hensel_data` invokes mathlib's
`hensels_lemma` at the approximate root `1`, with gap `f(1) = 4`, `f′(1) = 7`, so
`‖f 1‖ = 1/4 < 1 = ‖f′ 1‖²`; then `:126`

```lean
noncomputable def rootX : ℤ_[2] := hensel_data.choose
```

`Z³ + 2Z² + 1` is irreducible over `ℚ` with no rational root, so **no closed form exists** and
the formalization claims none. The only concrete data are mod-`2^k` congruences, each a
`decide` over `ZMod (2^k)` *from* `rootX_isRoot`:

| datum | value | citation |
|---|---|---|
| `X mod 2` | `1` | `OrientationRoot.lean:160` |
| `X mod 8` | `5` | `ChiR.lean:179` (local) |
| `X mod 16` | `5` | `OrientationRoot.lean:154` |
| `X mod 32` | `21` (stress) | `OrientationRoot.lean:274` |
| `S mod 16` | `13` | `OrientationRoot.lean:194` |
| `Y mod 16` | `7` | `OrientationRoot.lean:216` |
| `v₂(X−1) = v₂(S−1)` | `2` | `OrientationRoot.lean:245`, `:265` |

Hensel is load-bearing **twice**: for existence (`drLiftHom` needs actual `ℤ₂ˣ` values) and for
uniqueness (`rootX_unique`, `:137`, upgrades ball-uniqueness to global via the mod-2 step;
consumed in unit form as `rootX_unique_pair`, `MarkedMatching.lean:648`, by
`isLabuteOrientation_ext`, `CrossedDerivation.lean:421`).

**The character.** `ChiR.lean:120`:

```lean
noncomputable def chiR : ContinuousMonoidHom (DR : Type) ℤ_[2]ˣ :=
  drLiftHom isProP_two_unitsPadicInt ![SvalUnit, rootXUnit, YvalUnit] (…)
```

with `chiR drS = S` (`:125`), `chiR drX = X` (`:126`), `chiR drY = Y` (`:127`);
`isLabuteOrientation_chiR` (`:134`); `chiR_surjective` (`:160`), i.e. `im χ = ℤ₂ˣ` — the
Labute image invariant, in the `f = 2` (full-unit-group) case, proved by Frattini +
`mod8_sq` + `hensel_sq` using `X ≡ 5 (8)`.

**On the frame.** `χ̄(t) = Y·X⁻² = −1` (`chiR_torsion`, `ChiR.lean:145` — the note's eq. (tR));
`χ̄(σ̄) = S ∈ 1 + 4ℤ₂`; `χ̄(x̄₀) = X ∈ 1 + 4ℤ₂` (both `≡ 5, 13 (16)`, hence of infinite order).
Therefore:

> **The `χ`-trivial subspace of the `L_sq` frame is a rank-1 free `ℤ₂`-module transverse to
> `σ̄`** — the kernel of `(a,b) ↦ S^a X^b` on `ℤ₂σ̄ ⊕ ℤ₂x̄₀`, which is rank 1 because `im χ̄`
> restricted there is the whole procyclic `1 + 4ℤ₂` (surjectivity). It is **not** `⟨σ̄⟩`.

Contrast the collector, where the descent equations on `x₀^{σ²}x₀[x₁,σ]` force
`(χ(x₀), χ(σ), χ(x₁)) = (−1, 1, (−3)⁻¹)` = `chiD0G`'s calibrated triple
(`MarkedMatching.lean:298-302`), so `χ(σ) = 1` and `σ̄` *is* χ-trivial. **This is the whole
geometric content of `C_mark = 3` versus `C_mark = 1`**, and it is why S2.4 §1.1's blanket
"`χ(σ) = 1` for type `L`" cannot be applied to `L_sq` (§7 R1).

### 1.5 The unramified marking `ν_sq`

Packet normalization `ν(σ) = 1`, `ν(x_i) = 0`, **with no forced row** (unlike `M`, where
`ν_M(A) = −2^{α−1}` is forced by `2Ā + 2^αC̄₀ = 0`): here the relation `−4x̄₀ + 2x̄₁ = 0`
involves only wild letters, all of which get `0`, and the consistency check
`ν(t) = ν(x̄₁) − 2ν(x̄₀) = 0` is free.

Repo: `nuDR` (`GQ2/Roe/MarkedPro2.lean:87`), values `ztwoOne, 1, 1` (`:92/94/96`),
`nuDR_surjective` (`:101`). Target `Ztwo`, continuously isomorphic to `Multiplicative ℤ_[2]` by
`ztwoEquivPadic` (`GQ2/ZtwoPowering.lean:302`) — the same target MC2 adopted for `nuM`/`nuN`.
This is the **full `ℤ₂`-valued** marking, so merge gate 6 (plan §7.6, "mod-2 is not enough") is
met at rank 3 without further work.

### 1.6 The mod-2 cup Gram

`H¹(D_sq, 𝔽₂) ≅ 𝔽₂³` (`drH1_bijective`, `DRDemushkin.lean:161`; `card_H1_DR = 8`, `:209`),
`H²(D_sq, 𝔽₂) ≅ 𝔽₂` (`card_H2_DR`, `:403`, squeezed between `obsH2_DR_injective`
(`DRWordCoh.lean:901`) above and the `x₁*` Bockstein below). The master identity
(`drCup_obs`, `DRDemushkin.lean:347`) is

```text
B(v, w) = v₀w₁ + v₁w₀ + v₂w₂        in the dual basis (σ*, x₀*, x₁*)
```

i.e., writing `⟨·,·⟩` for the pairing into `H² ≅ 𝔽₂`,

```text
G_sq = ⟨x₁,x₁⟩ = 1 ;  ⟨σ,x₀⟩ = ⟨x₀,σ⟩ = 1 ;  all six others 0
     = [[0,1,0],[1,0,0],[0,0,1]]                          det = 1 over 𝔽₂
```

All nine entries are separate theorems, `drCup_ss` … `drCup_yy`
(`DRDemushkin.lean:426-464`); both triangles are stated because graded commutativity of
`cup11` is not formalized (`:421`).

Reading rule (the reusable MC2 asset): the square `x₁²` contributes the diagonal Bockstein
entry because `diagCoeff 2 = 1`, and `x₀⁻³`/`x₀^σ` contribute `0` on the diagonal because
`diagCoeff` is `mod 4`-periodic with `diagCoeff 4 = 0` — `diagCoeff` (`Cores.lean:1212`),
`diagCoeff_mod_four` (`:1241`), `diagCoeff_two` (`:1216`). Off-diagonals come from the two
conjugations/commutators: `[x₁, x₁^σ]` pairs `x₁` with itself (already on the diagonal) and
`(x₀^σ)⁻¹` pairs `σ` with `x₀`.

**Form class.** `⟨1⟩ ⊥ (one hyperbolic plane)` in dimension 3 — the anisotropic direction is
`x₁*` (the radical of the polar form), orthogonal to the plane `⟨σ*, x₀*⟩`. This is S2.4 §1.1's
`⟨1⟩ ⊥ (h+1 hyperbolic planes)` at `h = 0`, with the transposition `x₀ ↔ x₁` relative to the
collector exactly as S2.4 describes. **Do not reformulate through `QuadraticForm`/Arf**: at
`p = 2` the diagonal is the Bockstein, which is *additive*, so this is the Gram matrix of a
symmetric bilinear form, not a polar form (`DRDemushkin.lean:41-47` records that the
`QuadraticForm` route briefly "refuted" the correct matrix).

### 1.7 Demushkin invariants

| invariant | value | citation | route |
|---|---|---|---|
| `IsDemushkin 2` | ✓ | `DRDemushkin.lean:473` | `H¹` finite + `#H² = 2` + nondegeneracy from `drCup_obs` |
| `demushkinRank 2` | `3` | `:506` | `padicValNat 2 (#H¹) = padicValNat 2 8` |
| `demushkinQ` | `2` | `:513` | torsion count in `D^{ab}` |
| `im χ` | `ℤ₂ˣ` (`f = 2`) | `ChiR.lean:160` | Frattini + `mod8_sq` |

### 1.8 Cross-check against S2.4's independent computations

| S2.4 claim | source | repo | verdict |
|---|---|---|---|
| Gram `⟨x₁,x₁⟩=1, ⟨x₀,σ⟩=⟨σ,x₀⟩=1`, else 0 | §1.1 PROBE F | `drCup_obs`, `drCup_ss`…`drCup_yy` | ✓ **exact** |
| form class `⟨1⟩ ⊥ (h+1 planes)` | §1.1 | `[[0,1,0],[1,0,0],[0,0,1]]` at `h=0` | ✓ **exact** |
| frame `t = −2x̄₀ + x̄₁`, forced row on `x̄₁` | R6 | `BRDecomposition` + `br_decomposition_Y` | ✓ **exact** |
| `χ ≡ 1` on every handle letter | §1.1 | `commP_wordLift_one` (`Cores.lean:353`), `handleWord_wordLift_one` (`:362`) | ✓ (h-generic, already Lean) |
| degree-`n` core = degree-1 core + handles | `SQ_C_MARK_FINDING` | `sqRelWord`/`sqRelator_zero` (spike (a'),(b1)) | ✓ |
| `C_mark = 3` = a 2-adic orientation computation | §9.1, §9.3(ii) | Hensel root of `Z³+2Z²+1` | ✓ **and done** |
| **`χ(σ) = 1` for type `L`** | §1.1, §9.2(1) | `chiR drS = SvalUnit`, `S ≡ 13 (16)` | ✗ **FALSE for `L_sq`** |
| `marked_square_core_rank3` does not exist | §8.1 inventory row | `markedPro2_R` + `bLab` | ✗ **it exists** |

Six of eight exact, two corrections. Both corrections are in the *favourable* direction for the
owner's R2 selection except insofar as R1 slightly enlarges MC5's analysis burden.

---

## 2. Classification input — does `bLab` apply?

**Verdict: yes, directly. No new instance, no new binder, no G-Lab decision for this core.**

This was flagged as "the single biggest cost driver". It is zero, for a reason stronger than
invariant-matching: `BLabHypothesis` is *not* an abstract quantified statement — it is
deliberately specialized to `D_R`, which is this core.
`GQ2/Roe/MarkedPro2.lean:141`:

```lean
def BLabHypothesis : Prop :=
  IsDemushkin 2 (DR : Type) →
    demushkinRank 2 (DR : Type) = 3 →
      demushkinQ (DR : Type) = 2 →
        (∃ χ : (DR : Type) →* ℤ_[2]ˣ,
          Continuous χ ∧ IsLabuteOrientation χ ∧ Function.Surjective χ) →
          Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type))
```

Its docstring (`:108-140`) records the specialization as *deliberate*: "Specializing to
`G := D_R` (rather than quantifying over abstract `G`) is deliberate: it quarantines exactly the
instance used". The four antecedents are the four facts of §1.3/§1.4/§1.7, all proved.

**And it is a theorem, not a hypothesis.** `GQ2/Roe/Labute/Assembly.lean:249`:

```lean
theorem bLab : BLabHypothesis := by
  intro _ _ _ _
  obtain ⟨⟨φ, hφ⟩⟩ := nonempty_contSurj_D0_DR
  obtain ⟨⟨ψ, hψ⟩⟩ := nonempty_contSurj_DR_D0
  have hcomp : Function.Surjective (φ.comp ψ : ContinuousMonoidHom (DR : Type) (DR : Type)) :=
    hφ.comp hψ
  have hinj : Function.Injective (⇑φ ∘ ⇑ψ) :=
    profinite_hopfian drFinsetTopGen (φ.comp ψ) hcomp
  exact ⟨continuousMulEquivOfBijective ψ ⟨hinj.of_comp, hψ⟩⟩
```

Sorry-free, `axiom`-free, `#print axioms bLab = [propext, Classical.choice, Quot.sound]`
(std-3), from the λ-tower stage lemma (`StageLemma/StageTwo.lean:361/374`), the levelwise sets
(`Levelwise.lean:904/989`, base level `k₀ = 3`) and the profinite Hopfian endgame
(`Reconstruction.lean:76`). This is the L-campaign result the owner explicitly ordered in place
of an axiom (2026-07-25/26).

**Comparison with the abstract-invariant test the ticket asked for.** Had `bLab` *not* been
specialized, the test would still pass: `(p, rank, q, im χ) = (2, 3, 2, ℤ₂ˣ)` is exactly the
Labute odd-rank `q = 2`, `f = 2` type, and MC1 §6.4 records that the *rank-four* analogues
`MLabHypothesis`/`NLabHypothesis` must be stated abstractly precisely because their other side
is `G_K(2)` rather than a presented group. At rank three over `ℚ₂` both sides are presented, so
the specialized form suffices — and is what we have.

**Consequence for gate G-Lab.** The SQ lane adds **nothing** to G-Lab's docket. G-Lab remains a
decision about `MLabHypothesis`/`NLabHypothesis` (the even families) only.

---

## 3. The matching-engine port plan

### 3.1 What does **not** port, and why

The ticket anticipated porting `MarkedMatching.lean:307-1112` (masters → mod-2 span →
`evalMatrix` invertibility → solve → contract) to a new core word, on the D_R precedent. **That
port has already happened, for this core, and is what the D_R files are.** The engine's two
halves both name `D_R` as the *source*:

* Part (a), orientation functoriality: `isLabuteOrientation_comp_iso` (`:576`) —
  masters `masterH` (`:307`) over `χ₀ = chiD0G` (`:293`); mod-2 reduction `masterMod2` (`:406`);
  generation engine `mem_closure_gens_of_iso` (`:441`); span transfer
  `toAdd_mem_span_of_mem_closure` (`:465`); `isUnit_evalMatrix` (`:525`, Nakayama via
  `isUnit_of_toZModPow_one_eq_one'` `:249`); the linear solve at `:579`
  (`Matrix.mulVec_surjective_iff_isUnit`); contract `masterContract` (`:355`); kill the relator
  by `map_drWord` + `dr_relation`.
* Part (b), the marking correction: the same engine in 2×2 form (`pairMod2` `:837`,
  `isUnit_coordMatrix` `:931`), the mod-16 parity `toZModPow_one_tau` (`:763`), the second
  solve `exists_correction` (`:980`, RHS `![1,0]` = the `ν_R` values), then `prop_3_8_lift`
  ⇒ `exists_matching_iso` (`:1112`) and `nuUrBar_symm_eq_sHom` (`:1145`).

`evalMatrix` (`:484`) has its rows indexed by `![drS, drX, drY]` pushed through `f`: the
"different core word" whose matching was solved is exactly `C_sq`. **The deltas the ticket
asked me to enumerate are all zero.**

### 3.2 What is actually needed

Three things, none of them engine work.

1. **An h-generic presented family `D_sq h`** with a *proved* bridge `D_sq 0 = D_R`, so that MC5
   has a degree-`n` object to state handle stability about and every rank-3 fact transports into
   it. This is the only genuinely new Lean content, and MC2's generic presentation layer
   (`presPro2` `:719`, `presGen` `:723`, `presPro2_topGen` `:769`, `presPro2_hom_ext` `:780`,
   `presLiftHom` `:812`, `presLiftHom_gen` `:832`) does the plumbing rank-generically —
   `presPro2 r = maxProPQuotient 2 (profinitePresentation {r})` is *the same encoding* as
   `DR = maxProPQuotient 2 DRFull`, so the bridge is `rw [sqRelator_zero]; rfl`
   (spike (b2)).
2. **The rank-3 marked-core certificate**, assembled from `bLab` + `isLabuteOrientation_comp_iso`
   + `markedPro2_R`, in a shape MC5's `MarkedCoreCertificate` can consume.
3. **An MC5-facing interface**: `chiSq h`, `nuSq h`, `SqDecomposition`, the h-generic handle
   lemmas (already in MC2: `handleWord_of_one` `:1008`, `handleWord_comm` `:233`,
   `commP_wordLift_one` `:353`, `handleWord_wordLift_one` `:362`, `map_handleWord` `:193`,
   `handleWord_centLift_fib` `:1422`).

### 3.3 File map and line estimates

New directory `GQ2/Dyadic/SqCore/`, namespace `GQ2.Dyadic.SqCore`. Module-style headers are
fine for the two leaf files (their imports — `GQ2.Dyadic.MarkedCore.Cores`,
`GQ2.Roe.DRPresentation`, `GQ2.Roe.ChiR`, `GQ2.Roe.DRAbelianization`, `GQ2.Roe.DRDemushkin` —
are all `module`); **`Rank3.lean` must be plain-import**, because `GQ2/Roe/MarkedPro2.lean` and
`GQ2/Roe/Labute/Assembly.lean` are plain-import (plan §3 A5 module rule, one-directional).

| file | ticket | content | est. lines | header |
|---|---|---|---|---|
| `GQ2/Dyadic/SqCore/Cores.lean` | **SQ2** | `sqRank`, `sqHandleIdxU/V`, `sqWord`, `sqRelWord`, naturality, abelian collapse, `sqRelator`, `DSq h`, generators, `sqMark` + 5 value lemmas, `sqLiftHom` + `sqLiftHom_gen`, topGen/hom_ext wrappers, `chiSq h`, `nuSq h` + 8 value lemmas, `sqRelator_zero`, `dsq_zero`, `dsqEquivDR` | **300** | `module` |
| `GQ2/Dyadic/SqCore/Rank3.lean` | **SQ3** | `SqDecomposition` + `sq_decomposition` + forced row; the Demushkin/orientation/cup/ν restatements at `h = 0`; `MarkedSqCoreRank3`; **`marked_square_core_rank3`**; the `#print axioms` stress examples | **260** | plain-import |
| `GQ2/Dyadic/SqCore/Certificate.lean` | **SQ4** | the MC5 adapter: `marked_square_core_rank3 → Nonempty (MarkedCoreCertificate ℚ₂ (StandardCore.sq 0))` once MC5's structure exists; the `h`-generic statement `marked_square_core_degree_n` and the reduction consuming MC5's `HandleMixLift` | **160** | plain-import |
| `GQ2/Dyadic/SqCore/Sanity.lean` | **SQ5** | stress pins: word-identity `rfl`, `drWord_zmod8`-style numeric pins at `h = 1`, `χ`/`ν` mod-16 values, cup-Gram re-derivation via `diagCoeff` | **90** | `module` |
| — | SQ2 | one import line each in `GQ2.lean` | 4 | — |
| **total** | | | **≈ 810** | |

Line estimates are calibrated against MC2 (`Cores.lean`, 1907 lines for *two* rank-four cores
with new closed-form orientation proofs) and the D_R files. The SQ lane is ~40 % of one MC2 core
because the orientation, the frame, the Gram and the matching are all *cited*, not proved.

### 3.4 Interfaces this lane must not break

* **plan §3 A6 (ℚ₂ path frozen).** SQ2–SQ5 add files only. **No edit to any `GQ2/Roe/*` or
  `GQ2/SectionThree.lean` file.** `dsq_zero` goes in the *new* file and points at the frozen
  names; the frozen capstones keep printing byte-identical axiom sets.
* **B8 threading.** MC2 deliberately threaded B8 as an explicit `PeripheralCyclotomicAction`
  hypothesis rather than consuming the axiom (board 2026-07-29 MC2 note (iii)). At rank 3 the
  discharge route runs through `prop_3_8_lift` (`GQ2/AnabelianBridge/Construction.lean:1089`,
  "Consumes axiom B8"), so `marked_square_core_rank3` consumes B8. **Recommendation: consume
  it.** The alternative — a B8-threaded clone of `exists_matching_iso`/`markedPro2_R` — would
  reprove ~200 frozen lines to remove an axiom that is already in the census and is genuinely a
  ℚ₂ fact here. MC2's hypothesis-threading exists for the *general-K* rank-four analogues, which
  is a different obligation. Owner question Q2.
* **Merge gate 6** (full `ℤ₂` marking): met, §1.5.
* **Merge gate 10** (kernel `decide` only): met — the only finite computations on this path are
  `decide` over `ZMod (2^k)` and `ZMod 2`; no `native_decide` anywhere in the chain.

---

## 4. Lean statement skeletons

Namespace `GQ2.Dyadic.SqCore`. Everything in §4.1–§4.2 typechecked in the spike; §4.3 is
shape-accurate against MC5's not-yet-existing structure.

### 4.1 SQ2 — `Cores.lean`

```lean
/-- The rank of the degree-`n = 2h+1` square-commutator core: `n + 2 = 3 + 2h`. -/
def sqRank (h : ℕ) : ℕ := 3 + 2 * h

/-- The `j`-th handle pair: letters `(3 + 2j, 4 + 2j)`. -/
def sqHandleIdxU {h : ℕ} (j : Fin h) : Fin (sqRank h) := ⟨3 + 2 * j, …⟩
def sqHandleIdxV {h : ℕ} (j : Fin h) : Fin (sqRank h) := ⟨4 + 2 * j, …⟩

/-- **The square-commutator core word shape** `(x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]`.  Spelled to be
DEFINITIONALLY `GQ2.drWord` (`GQ2/Roe/DRPresentation.lean:83`) — the identification is the
whole point of this lane. -/
def sqWord {G : Type*} [Group G] (s x y : G) : G :=
  (conjP x s)⁻¹ * (x ^ 3)⁻¹ * y ^ 2 * commP y (conjP y s)

theorem sqWord_eq_drWord {G : Type*} [Group G] (s x y : G) :
    sqWord s x y = drWord s x y := rfl                     -- ← the headline identification

/-- The full degree-`n` relator shape: core word on `σ, x₀, x₁` times the `h` handles. -/
def sqRelWord {h : ℕ} (m : Fin (sqRank h) → G) : G :=
  sqWord (m 0) (m 1) (m 2) *
    handleWord (fun j => m (sqHandleIdxU j)) (fun j => m (sqHandleIdxV j))

theorem sqRelWord_zero (m : Fin (sqRank 0) → G) : sqRelWord m = sqWord (m 0) (m 1) (m 2)
theorem map_sqWord (φ : F) (s x y : G) : φ (sqWord s x y) = sqWord (φ s) (φ x) (φ y)
theorem sqWord_comm {G} [CommGroup G] (s x y : G) : sqWord s x y = (x ^ 4)⁻¹ * y ^ 2

noncomputable def sqRelator (h : ℕ) : FreeProfiniteGroup (Fin (sqRank h)) :=
  sqRelWord (fun i => FreeProfiniteGroup.of i)
noncomputable def DSq (h : ℕ) : ProfiniteGrp := presPro2 (sqRelator h)

/-- **The bridge.**  At `h = 0` the presented core IS the frozen `D_R`. -/
theorem sqRelator_zero : sqRelator 0 = drRelator
theorem dsq_zero : DSq 0 = DR
noncomputable def dsqEquivDR : ContinuousMulEquiv (DSq 0 : Type) (DR : Type)

/-- The standard marking: three core values, `1` on every handle letter (MC2's `coreMark`
pattern, `Cores.lean:1018`). -/
def sqMark {H} [Group H] {h : ℕ} (a b c : H) : Fin (sqRank h) → H
theorem sqRelWord_sqMark (a b c : H) : sqRelWord (sqMark (h := h) a b c) = sqWord a b c

/-- Universal property, via MC2's generic `presLiftHom` (`Cores.lean:812`). -/
noncomputable def sqLiftHom (h : ℕ) (hH : IsProP 2 H) (m : Fin (sqRank h) → H)
    (hrel : sqRelWord m = 1) : ContinuousMonoidHom (DSq h : Type) H
@[simp] theorem sqLiftHom_gen … : sqLiftHom h hH m hrel (presGen (sqRelator h) i) = m i

/-- **`χ_sq`**, the canonical Labute orientation, h-generically: the Hensel-root values
`(σ, x₀, x₁) ↦ (S, X, Y)` and `1` on every handle letter (§1.4). -/
noncomputable def chiSq (h : ℕ) : ContinuousMonoidHom (DSq h : Type) ℤ_[2]ˣ :=
  sqLiftHom h isProP_two_unitsPadicInt (sqMark SvalUnit rootXUnit YvalUnit) …

/-- **`ν_sq`**, the full `ℤ₂`-valued unramified marking: `ν(σ) = 1`, `ν(x_i) = 0`, no forced
row (§1.5). -/
noncomputable def nuSq (h : ℕ) : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2]) :=
  sqLiftHom h PropOneOne.isProP_two_multPadicInt (sqMark (ofAdd 1) (ofAdd 0) (ofAdd 0)) …
```

### 4.2 SQ3 — `Rank3.lean`, including the headline

The frame, in the `BDecomposition`/`MDecomposition` house style:

```lean
/-- **The rank-3 frame of the `L_sq` core** (§1.3): `ℤ/2·t ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₀` with torsion
`t = x̄₁ − 2x̄₀`; the `x̄₁`-row is forced.  Stated against `D_R` and discharged verbatim from
`br_decomposition` (`GQ2/Roe/DRAbelianization.lean:462`). -/
structure SqDecomposition where
  e : ContinuousMulEquiv (topAbelianization (DR : Type))
        (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
  map_t     : e (abMk (drY * (drX ^ 2)⁻¹)) = ofAdd (1, 0, 0)
  map_sigma : e (abMk drS) = ofAdd (0, 1, 0)
  map_x0    : e (abMk drX) = ofAdd (0, 0, 1)

theorem sq_decomposition : Nonempty SqDecomposition
theorem sq_decomposition_forcedRow (B : SqDecomposition) : B.e (abMk drY) = ofAdd (1, 0, 2)
```

The headline, in S2.4 §2.4's statement shape but with the certificate unbundled so it can be
stated *before* MC5's `MarkedCoreCertificate` exists:

```lean
/-- **The `C_mark = 3` certificate at rank three** — packet `def:core-certificate`
(proof.tex:711) instantiated at `K = ℚ₂`, `P = C_sq`: the abstract Demushkin identification,
the cyclotomic orientation, and the marking-corrected identification with `G_{ℚ₂}(2)`
matching the FULL `ℤ₂`-valued unramified character. -/
structure MarkedSqCoreRank3 [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (R : LocalReciprocity) where
  /-- item 1: the abstract Demushkin isomorphism (Labute; via `bLab`). -/
  abstractEquiv : ContinuousMulEquiv (DR : Type) (D0 : Type)
  /-- item 2: the transported orientation IS the canonical Labute orientation. -/
  orientation :
    IsLabuteOrientation (chiD0G.toMonoidHom.comp abstractEquiv.toMulEquiv.toMonoidHom)
  /-- the `Ztwo ≅ Multiplicative ℤ₂` normalisation, pinned on the generator. -/
  iota     : ContinuousMulEquiv Ztwo (Multiplicative ℤ_[2])
  iota_one : iota ztwoOne = ofAdd ((1 : ℤ) : ℤ_[2])
  /-- item 3: the marking correction, absorbed into the identification. -/
  markedEquiv : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) (DR : Type)
  marked_nu   : ∀ g : AbsGalQ2,
    R.nu_ur (toAb g) = iota (nuDR (markedEquiv (maxProPMk 2 AbsGalQ2 g)))

/-- **`marked_square_core_rank3`** — the S2.4 obligation, DISCHARGED. -/
theorem marked_square_core_rank3 [CompactSpace AbsGalQ2]
    [TotallyDisconnectedSpace AbsGalQ2] (R : LocalReciprocity) :
    Nonempty (MarkedSqCoreRank3 R) := by
  obtain ⟨f⟩ : Nonempty (ContinuousMulEquiv (DR : Type) (D0 : Type)) :=
    bLab isDemushkin_DR demushkinRank_DR demushkinQ_DR
      ⟨chiR.toMonoidHom, chiR.continuous_toFun, isLabuteOrientation_chiR, chiR_surjective⟩
  obtain ⟨ι, hι, e, he⟩ := markedPro2_R R bLab
  exact ⟨⟨f, isLabuteOrientation_comp_iso f, ι, hι, e, he⟩⟩
```

### 4.3 SQ4 — `Certificate.lean`, the MC5 seam

Once MC5 lands `StandardCore`, `DP`, `chiP`, `nuP`, `chiK`, `nuK`, `MarkedCoreCertificate`
(mc-design.md §6.3) and `HandleMixLift`:

```lean
/-- MC5-interface form of the rank-3 result: S2.4 §2.2's `marked_square_core_rank3`. -/
theorem marked_square_core_rank3_certificate :
    Nonempty (MarkedCoreCertificate ℚ₂ (StandardCore.sq 0))

/-- S2.4 §2.2's chain, with the rank-3 input now a THEOREM rather than a hypothesis. -/
theorem marked_square_core_stabilize
    (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]
    (h : ℕ) (hodd : (params K).n = 2 * h + 1)
    (hData : markedDataEq K (StandardCore.sq h))     -- packet prop:marked-reduction
    (hMix  : HandleMixLift (StandardCore.sq h))      -- ← MC5/MC-HM, the ONLY residual
    : Nonempty (MarkedCoreCertificate K (StandardCore.sq h))
```

Note what changed relative to S2.4 §2.2: the `base : marked_square_core_rank3` **and**
`hLab : LabuteHypothesis (StandardCore.sq h)` binders are gone at `h = 0` (base is a theorem;
the rank-3 Labute instance is `bLab`). At `h ≥ 1` a degree-`n` Labute instance is still needed —
but that is the same `MLabHypothesis`-shaped obligation MC1 §6.4 already scoped, and it is
MC5's, not this lane's.

---

## 5. Feasibility spike

Scratch file (263 lines, never committed):
`/private/tmp/claude-501/-Users-roed-claude-lmfdb/8d8a6b1f-8827-496c-854b-e383c5b269ac/scratchpad/SqSpike.lean`,
run as `lake env lean <path>` in the worktree against the built cache at `9439dc3`.

### 5.1 Result: **0 errors, 0 sorries.**

Only 5 warnings, all the `unusedSectionVars` linter on five `sqMark_*` plumbing lemmas (fixed in
the real file by an `omit` line — recorded so SQ2 does not rediscover it).

| clause | statement | outcome |
|---|---|---|
| (a) | `sqWord s x y = drWord s x y` | ✅ **by `rfl`** |
| (a′) | `sqRelWord m = sqWord (m 0) (m 1) (m 2)` at `h = 0` | ✅ `handleWord_zero` + `mul_one` |
| (b1) | `sqRelator 0 = drRelator` | ✅ `rw [sqRelWord_zero]; rfl` |
| (b2) | **`DSq 0 = DR`** | ✅ `rw [DSq, sqRelator_zero]; rfl` |
| (b3) | `(DSq 0 : Type) = (DR : Type)` | ✅ |
| (b4) | `dsqEquivDR : ContinuousMulEquiv (DSq 0) (DR)` | ✅ `dsq_zero ▸ ContinuousMulEquiv.refl _` |
| (b5) | `sqRelWord (sqMark a b c) = sqWord a b c` | ✅ via MC2 `handleWord_of_one` |
| (b6) | **`chiSq h`** h-generic, + 5 value lemmas | ✅ via `sqLiftHom` + `drWord_comm` + `YvalUnit_sq_eq` |
| (b7) | **`nuSq h`** h-generic, + 3 value lemmas | ✅ via `sqWord_comm` |
| — | `sqLiftHom` (via MC2 `presLiftHom`) + `sqLiftHom_gen` | ✅ |
| (c1) | `Nonempty SqDecomposition` from `br_decomposition` | ✅ field-for-field |
| (c2) | forced row `x̄₁ ↦ (1,0,2)` from `br_decomposition_Y` | ✅ |
| (d1) | `IsDemushkin 2`, `rank = 3`, `q = 2` | ✅ cited |
| (d2) | `∃ χ, Continuous ∧ IsLabuteOrientation ∧ Surjective` | ✅ cited |
| (d3) | `χ(t) = −1` (`chiR_torsion`) | ✅ |
| (d4) | all **nine** Gram entries | ✅ cited |
| (d5) | `ν(σ) = 1`, `ν(x₀) = ν(x₁) = 0`, surjective | ✅ cited |
| **(e)** | **`marked_square_core_rank3` DISCHARGED** | ✅ 4-line proof |

### 5.2 Two API findings for SQ2

1. `rw [chiSq]` cannot rewrite under the `ContinuousMonoidHom` coercion, so the generator-value
   lemmas need a **dedicated `@[simp] sqLiftHom_gen`** wrapper around `presLiftHom_gen`
   (2 lines) and then term-mode `.trans`. This is exactly MC2's `mLiftHom_gen` pattern; MC2
   solved it the same way. Without the wrapper the eight value lemmas do not go through.
2. `dsq_zero` needs `rw [DSq, sqRelator_zero]` **then** `rfl` — `rw [… , presPro2, DR, DRFull]`
   fails with "Failed to rewrite using equation theorems for `DRFull`" (`DRFull` is a
   `noncomputable def` in a `module` file). Recorded so SQ2 does not lose time on it.

### 5.3 Axiom footprint (measured, `#print axioms`)

```text
marked_square_core_rank3 : [propext, Classical.choice, dyadicOrientation,
                            peripheralCyclotomicAction, Quot.sound]
chiSq        : [propext, Classical.choice, Quot.sound]     -- std-3
nuSq         : [propext, Classical.choice, Quot.sound]     -- std-3
dsqEquivDR   : [propext, Classical.choice, Quot.sound]     -- std-3
dsq_zero     : [propext, Classical.choice, Quot.sound]     -- std-3
sq_decomposition : [propext, Classical.choice, Quot.sound] -- std-3
```

`dyadicOrientation` = **B3c**, `peripheralCyclotomicAction` = **B8**; both are in the frozen
census (`GQ2/Foundations/Axioms.lean:165`, `:259`; `EXPECTED_AXIOMS=11`). **No new axiom, no
census flip, no G-AX gate.** The h-generic definitions are axiom-free beyond std-3, which means
`chiSq`/`nuSq` can be consumed by MC5 without dragging B3c/B8 into the rank-four lane.

---

## 6. Sized ticket list — the SQ implementation lane

Dependency order is linear. All are opus tier: the design is settled, the mathematics is cited,
and every seam has been spike-verified. One ticket = one dispatch; worktree `gq2-dyadic-sq`,
branch `dyadic-sq`.

| ID | content | files owned (exclusive) | deps | tier | est. lines |
|---|---|---|---|---|---|
| **SQ2** | h-generic core: word shape + `rfl`-identification with `drWord`, `sqRelator`, `DSq h`, `sqMark`, `sqLiftHom`/`sqLiftHom_gen`, `chiSq`/`nuSq` + value lemmas, `sqRelator_zero`, **`dsq_zero`**, `dsqEquivDR`. Reuse MC2's generic presentation layer; **do not** re-derive it. | `GQ2/Dyadic/SqCore/Cores.lean` (new) + its `GQ2.lean` import line | MC2 (landed) | opus | 300 |
| **SQ3** | the rank-3 marked core: `SqDecomposition` + existence + forced row; `MarkedSqCoreRank3`; **`marked_square_core_rank3`**; the four data restatements (Demushkin triple, orientation, cup Gram, ν); `#print axioms` stress examples pinning std-3 + B3c + B8. **Plain-import header.** | `GQ2/Dyadic/SqCore/Rank3.lean` (new) + import line | SQ2 | opus | 260 |
| **SQ4** | MC5 adapter: `marked_square_core_rank3_certificate` in MC5's `MarkedCoreCertificate` shape; `marked_square_core_degree_n`; the stabilize theorem consuming MC5's `HandleMixLift`. **Blocked on MC5** (`StandardCore`/`MarkedCoreCertificate` do not exist yet). **Plain-import.** | `GQ2/Dyadic/SqCore/Certificate.lean` (new) + import line | SQ3, **MC5** | opus | 160 |
| **SQ5** | stress/sanity pins: word identity by `rfl`, `Multiplicative (ZMod 8)`-style numeric relator pins at `h = 1` (the `drWord_zmod8` pattern, `DRPresentation.lean`), `χ`/`ν` mod-16 values, cup-Gram re-derivation through `diagCoeff`/`diagCoeff_mod_four` rather than by citation. | `GQ2/Dyadic/SqCore/Sanity.lean` (new) + import line | SQ2, SQ3 | opus | 90 |

**Total: 4 tickets, ≈ 810 lines.** SQ2+SQ3 (560 lines) close the commissioned obligation and are
unblocked *today*; SQ4 waits on MC5; SQ5 is parallel to SQ4.

**What this lane does NOT own** (guard against scope creep):
`HandleMixLift`, Lemma 6.3, and any degree-`n` handle stabilization (MC5 / MC-HM);
`MLabHypothesis`/`NLabHypothesis` and gate G-Lab (MC3/MC4/MC5); the `L_sq` **word** certificate
— Fox/Stokes/scalar/quadratic (WL lane, see §7.5); any edit to `GQ2/Roe/*` (plan A6).

---

## 7. Risks, corrections, and owner questions

### 7.1 Risks

| # | risk | assessment / mitigation |
|---|---|---|
| **R1** | **S2.4 §1.1's "`χ(σ) = 1` for type `L`" is false for `L_sq`**, and §9.2(1) uses it to argue that `HandleMixLift` is candidate-independent. `χ_sq(σ) = S ≡ 13 (16)`, of infinite order, so the χ-trivial subspace of the `L_sq` frame is a rank-1 free `ℤ₂`-module transverse to `σ̄`, not `⟨σ̄⟩ ⊕ (handle plane)`. | **Real, and it is MC5's to absorb, not this lane's.** Lemma 6.3 itself is stated frame-agnostically (S2.4 §2.4: hypothesis is "φ preserves the handle plane"), so its *conclusion* is unaffected; what changes is §6.4's identification of the reachable stabilizer block, which was computed in the `χ(σ)=1` frame. **Reported, not patched.** Owner question Q3. Note this cuts *against* S2.4's claim that S2.4 "cannot break the tie" — for `L_sq` the handle analysis is genuinely different, and possibly *harder*. |
| **R2** | **The discharge is ℚ₂-only.** `marked_square_core_rank3` is by construction a statement about `K = ℚ₂`; the campaign's target is all ramified-`i` `K`. | By design — S2.4 §2.2 asks exactly for the rank-3 base, and §9.5 records that this input "is not MC work: it is a ℚ₂-side theorem about a different core". The degree-`n`/general-`K` reach is `hData` + `hMix` in §4.3, both MC5's. No hidden debt. |
| **R3** | **`DSq 0 = DR` is an `Eq` of `ProfiniteGrp`, not an equivalence**, so transporting statements along it uses `▸`/`cast`, which is brittle under later refactors of `presPro2` or `DRFull`. | Mitigated two ways: (i) `dsqEquivDR` is provided as the *only* sanctioned consumer-facing form (spike (b4) — it typechecks); (ii) SQ3 states every rank-3 fact **directly about `DR`** (the frozen names) rather than about `DSq 0`, so the `cast` appears once, in `dsqEquivDR`, and nowhere else. Spike-verified: `SqDecomposition` is stated on `DR` and discharged with no cast at all. |
| **R4** | **B8 enters the rank-3 discharge** (through `prop_3_8_lift`), whereas MC2 deliberately avoided consuming it. A reviewer comparing the two lanes will see an inconsistency. | Deliberate and defensible (§3.4): at rank 3 over ℚ₂, B8 *is* the relevant published ℚ₂ input and is already in the census; MC2's threading exists because the rank-four cores need general-`K` analogues. Documented in SQ3's module docstring. Owner question Q2. |
| **R5** | **`MarkedCoreCertificate` and `StandardCore` do not exist**, so SQ4's exact field-by-field match to MC5 is unverifiable today; the `MarkedSqCoreRank3` bundle of §4.2 is my reconstruction from mc-design.md §6.3 + the packet field list. | SQ3's bundle is chosen to be *field-wise a superset* of mc-design.md §6.3's five fields (`abstractEquiv`/`orientation`/`correction`/`correction_chi`/`correction_nu`), with `correction` already absorbed into `markedEquiv` — which is how `markedPro2_R` delivers it. If MC5 wants the correction split out, `exists_matching_iso` (`MarkedMatching.lean:1112`) supplies it separately. Budget SQ4 for a re-shaping pass rather than a re-proof. |
| **R6** | **Stale-docstring hazard**: `GQ2/Roe/DRWordCoh.lean:913` points the Gram matrix at a nonexistent `GQ2/Roe/DRH2.lean`; `GQ2/Roe/Labute/TwoCentralTower.lean:65-66` still describes the file as carrying L2 fill `sorry`s that the L-campaign removed. | Cosmetic, no mathematical consequence, and **outside this lane's file ownership** (plan A6 freezes `GQ2/Roe/*`). Recorded for whoever owns a ℚ₂ docs pass. |
| **R7** | **The harness↔Lean identification rests on my factor-by-factor reading** of `q2.py:414` against `DRPresentation.lean:83`, not on a machine check. | The reading is short (four factors) and is reproduced in §1.2 for audit; the conventions are stated verbatim in both sources; and the identification's *consequences* are independently corroborated by four independent data matches (frame, Gram, form class, `C_mark` pricing) in §1.8. A cheap machine check is available and is folded into **SQ5**: emit `q2.pro2_core_square_commutator`'s normalized form and compare against a Lean-side printed `sqWord` spelling. |

### 7.2 Does anything make `L_tw`'s fallback preferable after all? — No.

Honest reporting, as requested. The case *for* revisiting R2 would need one of:

* **(a) the `L_sq` rank-3 obligation turning out harder than priced** — the opposite happened;
  it is discharged, unconditionally, at zero new axioms.
* **(b) `L_sq`'s marked data failing to match `G_{ℚ₂}(2)`'s** — it matches, and the matching is
  the frozen `markedPro2_R`.
* **(c) `L_sq` costing more downstream** — `L_tw`'s advantage in S2.4 §9.3(i) was precisely
  "the marked-core half is already done (core = collector's)". That advantage is now **shared**:
  `L_sq`'s marked-core half is also already done. `L_tw` retains no marked-core edge, and its
  rank-3 *word* remains verifier-only (5402/5402, unproved), whereas `L_sq`'s rank-3 word is
  `main_presentation_literal_roe_unconditional`.
* **(d) R1** — the one genuine cost `L_sq` carries that `L_tw` does not: because `χ_sq(σ) ≠ 1`,
  MC5's handle analysis must be redone in the `L_sq` frame rather than inherited from the
  collector's. This is a **partial** point for `L_tw`. It is bounded (one frame recomputation
  inside MC5, S2.4 §6.4-shaped) and is strictly smaller than proving `L_tw`'s rank-3 word.

Net: R2's selection of `L_sq` is **better founded than S2.4 knew**, and the memo's own tiebreak
criterion — "which rank-three theorem the owner would rather commission" (§13 Q3) — resolves
decisively, because one of the two is already in the repository. No recommendation to revisit.

### 7.3 Campaign §16 labelling

* **Claimed as proof:** everything in §1.2–§1.7 and §5 — each is a cited sorry-free Lean theorem
  or a spike-typechecked statement, named with file:line.
* **Not promoted:** the mod-`2^k` congruences of §1.4 are `decide`-checked *consequences* of
  `rootX_isRoot`, not independent witnesses of the root; they pin residues, never the root.
  `L.sq_core_path_search`'s bounded negatives (S2.4 §9.2) remain bounded searches and are, as
  S2.4 already notes, **off the critical path entirely** — the park dissolves by selection, and
  §1.2 shows the selected core is a genuine marked Demushkin core with a proved identification.
* **§16 stop conditions triggered: none.**

### 7.4 Recommended amendments (for whoever owns those files — this ticket edits none)

1. **S2.4 memo §1.1 / §9.2(1)**: qualify "`χ(σ) = 1` for type `L`" as a *collector/`L_tw`* fact;
   for `L_sq` record `χ(σ) = S`, the Hensel-root value. Re-examine §6.4's mixing-element
   analysis in the `L_sq` frame.
2. **S2.4 memo §8.1 inventory**, row "the rank-3 inputs": change `L_sq: does not exist` to
   `L_sq: available — the core IS D_R (GQ2/Roe/DRPresentation.lean:83); markedPro2_R + bLab`.
3. **`L.py` `sq_marking_table`** (`:1493`): the three gate-C records
   (`abstract_demuskin_identification`, `cyclotomic_orientation`, `unramified_z2_marking`) are
   all `PARKED`/`RECORDED AS OPEN`; all three now have Lean citations. A `L.py` owner should flip
   them, and `SQ_GATE_C_PARK_REASON` should record the selection-semantics resolution.
4. **`mc-design.md` §2.2(iii)**: its cross-check "the same reading applied to the ℚ₂ relator
   `r₂`" should say "to the `L_sq` core `r₂`, which is the ℚ₂ Roe relator" — the coincidence it
   observed is this memo's V1.

### 7.5 Discovery affecting the WL lane (reported, not designed)

`L_sq` at `n = 1` is `Γ_R` *as a whole word* (§1.2), so the WL lane's rank-3 **word**-certificate
base — S2.4 §2.1's `word_certificate_stabilize` at `h = 0` — also has a frozen precedent:
Fox rows `GQ2/Roe/WildRow.lean` (333 ln) and `FoxBasic.lean` (272 ln), Stokes
`GQ2/Roe/Stokes.lean` (149 ln), Hessian `GQ2/Roe/Hessian.lean` (395 ln), Gauss
`GQ2/Roe/Gauss.lean` (252 ln), tame `GQ2/Roe/Tame.lean` (454 ln), assembled at
`GQ2/Roe/Main.lean:563`. **This is a WL-lane finding and I have not designed against it** — the
WL tickets should be re-scoped before dispatch. It plausibly halves WL-b/WL-c.

### 7.6 Numbered owner questions

1. **Ticket shape.** SQ2+SQ3 (≈ 560 lines) discharge the commissioned obligation and are
   unblocked now. Dispatch them immediately, or hold the SQ lane until MC5 lands so SQ2–SQ4 go
   as one wave? Recommendation: **dispatch SQ2+SQ3 now** — they are MC5's *input*, and MC5's
   `HandleMixLift` analysis needs the `L_sq` frame (R1) that SQ3 pins down.
2. **B8.** Accept that `marked_square_core_rank3` consumes B3c + B8 (both already in the census,
   no flip), rather than cloning `exists_matching_iso`/`markedPro2_R` with a
   `PeripheralCyclotomicAction` binder to match MC2's style? Recommendation: **accept and
   document** (§3.4, R4).
3. **R1 routing.** The `χ_sq(σ) ≠ 1` correction invalidates the frame premise of S2.4 §6.4 for
   `L_sq`. Should it go (a) to MC-HM as an amended brief, (b) to the S2.4 memo's owner as an
   erratum, or (c) both? Recommendation: **both**; (a) is blocking for MC5, (b) is bookkeeping.
   MC1 §9 Q5 and S2.4 §13 Q4 already ask whether packet feedback travels now or later — this
   should ride with them.
4. **WL re-scope.** §7.5 is a genuine cross-lane discovery. Authorize a short WL-recon ticket to
   re-price WL-b/WL-c against the `Γ_R` word assets before the WL lane is dispatched?
5. **Harness flip.** May a future `general_2adic` worker flip `L.py`'s three gate-C records and
   `SQ_GATE_C_PARK_REASON` on the evidence of §1.2 (amendment 3)? This memo does not own that
   repo. Note the flip is *not* a Nielsen/Tietze certificate — it is gate C's
   "**selected** marked Demushkin core" clause (campaign §6), exactly as S2.4 §9.2(4) predicted.

---

## 8. One-paragraph summary

At gate R2 the owner selected `L_sq`, the stabilized square-commutator, and commissioned
`marked_square_core_rank3` — the rank-3 marked-core/orientation theorem the page prices at
`C_mark = 3`. That theorem already exists. The `L_sq` rank-3 pro-2 core
`(x₀^σ)⁻¹x₀⁻³x₁²[x₁,x₁^σ]` is, letter for letter, `GQ2.drWord` — the core of `D_R` in the frozen
Roe development — and the whole `L_sq` word at `n = 1` is Roe's candidate `Γ_R`, whose terminal
theorem is hypothesis-free. So the orientation (a genuine Hensel root of `Z³+2Z²+1`, no closed
form, `X ≡ 5 (16)`), the frame (`ℤ/2·t ⊕ ℤ₂σ̄ ⊕ ℤ₂x̄₀`, `t = x̄₁ − 2x̄₀`, forced row on `x̄₁`),
the mod-2 cup Gram (`[[0,1,0],[1,0,0],[0,0,1]]`), the full `ℤ₂` unramified marking and the
Labute classification instance are all already sorry-free Lean, and `bLab` — the single biggest
anticipated cost — applies directly because `BLabHypothesis` is *specialized to this very core*.
A 263-line spike typechecks the whole chain against the real repo with zero errors, discharges
`marked_square_core_rank3` in four lines, and measures its axiom print as std-3 + B3c + B8, so
the census stays 11. The residual implementation is four opus tickets and about 810 lines of
h-generic scaffolding, transport and interface — no matching-engine port at all. Two corrections
travel with this: S2.4's blanket "`χ(σ) = 1` for type `L`" is false for `L_sq` (its `σ` carries
the deep orientation value `S`, which is *why* `C_mark = 3`), and that weakens — for `L_sq`
specifically — S2.4 §9.2's argument that `HandleMixLift` is candidate-independent. Neither
correction favours reverting to `L_tw`, whose rank-3 word remains unproved while `L_sq`'s is a
theorem.

---

*End of memo. Ticket SQ1, branch `dyadic-sq1`.*
