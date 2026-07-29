# MC1 — MC-M / MC-N design memo: rank-four marked cores, frames, stabilizers, lifting

**Ticket MC1** (dyadic campaign, lane MC; board [`tickets.md`](tickets.md), plan
[`plan.md`](plan.md) §3 A3, gate **G-Lab**). Written on branch `dyadic-mc` (worktree
`~/claude/gq2-dyadic-mc`, synced to `dyadic` at `0ed4244`). Every Lean anchor below was opened
and read in this worktree; line numbers are from this checkout.

**Authority.** The packet
(`refs/dyadic-presentations-formalization-proof.tex`) governs; §7 (Def. 7.1 marked-core
certificate, Prop. 7.2 marked-matching reduction, lines 701–759), §8 (Prop. 8.1/Cor. 8.2, lines
761–824), §14 (completion criteria, lines 1077–1082). The draft
(`refs/dyadic-presentations.tex` §2.2, lines 259–347) supplies the core words and the marked
changes of variables; overrides per `refs/README.md`. Seed: `recon/mc-survey.md`.

---

## 0. Headline verdicts

| # | Question | Verdict |
|---|---|---|
| V1 | The two rank-four frames | **Both are `ℤ/2 ⊕ ℤ₂³`.** `M_α`: torsion generator `t = Ā·C̄₀^{2^{α-1}}` (α-dependent, forced `Ā`-row) — the *exact* rank-four analogue of `BDecomposition` with `2 ↦ m = 2^{α-1}`. `N_α`: torsion generator is the plain generator `x̄₀`, **no forced row**. §2.1, §3.1 |
| V2 | "M and N have different torsion" (board/survey claim) | **FALSE as stated — recorded as a correction (§7.1).** Both have `q = 2` and isomorphic abelianizations; the frames differ in *where the torsion sits* and, decisively, in `im χ` (`⟨−1⟩ × ⟨u⟩` for M, procyclic `⟨v⟩` for N). Conclusion ("two genuinely different frames") survives, for a different reason. |
| V3 | Canonical orientations | **Closed form, no Hensel root.** `χ_M = (1, −1, 1, (1−2^α)^{-1})` on `(A,B,C₀,D)`; `χ_N = (1, −(1+2^α)^{-1}, 1, 1)` on `(x₀,x₁,σ,x₂)`. Derived from the repo's own crossed-derivation rules and **calibrated against `chiD0G`'s `(−1,1,(−3)⁻¹)`** (§1.3). Recovers the packet's `u` and the draft's `v` exactly. No analogue of `GQ2/Roe/OrientationRoot.lean` is needed. |
| V4 | Mod-2 cup Gram | Same matrix for both cores in their own bases: `[[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]`, **α-independent for α ≥ 2**. §2.2/§3.2 |
| V5 | Smith–Witt stabilizers | Computed in closed form. `St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂)` (§3.3); `St_M` = 7 parameters `(τ,β,B_c,c₁,γ,d₁,e)` with one mod-2 coupling (§2.3). Defining conditions **α-independent**. |
| V6 | Lifting | **Three strata.** S1 elementary Nielsen lifts (constructed + verified here, axiom-free); S2 unit scalings — **discharged by the EXISTING axiom B8, no new axiom, no census bump** (§5.2, a new finding: B8 is stated for the *abstract* free pro-2 group of rank 2); S3 a residue of "mixing" transvections that is genuinely degree-≥3 Labute content (§5.3). |
| V7 | G-Lab | Two decisions, not one: (a) the Demushkin-classification hypotheses `MLabHypothesis`/`NLabHypothesis`; (b) **new** — the S3 lifting residue. Recommendation in §8. |
| V8 | Packet ↔ survey conflicts | None on mathematics. Two *gaps*: the compact-`M` change of variables is absent from the vendored draft (§7.2), and the packet's per-core statement quantifies over a stabilizer strictly larger than what our constructions reach (§5.3, §7.3). |

---

## 1. Setup

### 1.1 The presented cores

For a standard core `P` the packet (§7, line 706) writes

```
D_P = ⟨σ, x₀, …, x_n | P = 1⟩_{pro-2},   χ_P : D_P → ℤ₂ˣ,   ν_P : D_P → ℤ₂
```

so `D_P` has `n + 2` generators. **Rank four ⟺ n = 2.** For general even `n = 2 + 2h` the draft
appends `h = (n−2)/2` hyperbolic handles (`refs/dyadic-presentations.tex:347`). Encoding: MC2
builds `D_P` by `profinitePresentation` (`GQ2/ProfinitePresentation.lean:43`, already
rank-generic) followed by `maxProPQuotient 2`, exactly as `GQ2/Roe/DRPresentation.lean` builds
`DR` and `GQ2/DyadicPresentation.lean` builds `D0`. Note `Γ_R` has `n+3` generators
(`GQ2/Dyadic/Parameters.lean:133`, `generatorCount = n+3`) but `τ` dies in the pro-2 quotient —
the core has `n+2`.

The two families (draft eq. `Mpc-core`:302, `Ncompact-core`:328; `Parameters.lean:146`
`LabuteType.M/N`, validity `2 ≤ α` at :170):

```
P_M(α) = A²[A,B]·C₀^{2^α}[C₀,D]          (Labute letters a,b,c,d = A,B,C₀,D)
P_N(α) = x₀^{2+2^α}[x₀,x₁]·[σ,x₂]        (Labute letters a,b,c,d = x₀,x₁,σ,x₂)
```

with `m := 2^{α−1}`, and repo conventions `commP x y = x⁻¹y⁻¹xy`, `conjP x g = g⁻¹xg`
(`GQ2/Roe/DRPresentation.lean:83` docstring).

### 1.2 The three-term (peripheral) normal form — used throughout

Both relators collapse to a **product of three factors equal to 1**, twice nested:

```
P_M = ( A·A^B ) · ( C₀^{2^α−1} ) · ( C₀^D )          outer triple,  w_M := A·A^B
    with the inner triple  A · A^B · w_M^{-1} = 1
P_N = ( x₀^{1+2^α}·x₀^{x₁} ) · ( σ^{-1} ) · ( σ^{x₂} )   outer,  w_N := x₀^{1+2^α}·x₀^{x₁}
    with the inner triple  x₀^{1+2^α} · x₀^{x₁} · w_N^{-1} = 1
```

This is not decoration: the ℚ₂ core factors the same way,
`A²S⁴[S,Y] = A² · S³ · S^Y`, and the repo's `lambdaHom`
(`GQ2/AnabelianBridge/Construction.lean:486`) is *literally* the map `Δ → D₀`,
`P ↦ S³`, `T ↦ S^{-3}A^{-2} = S^Y` (via `d0_relation_hnn` :496), `C = (PT)⁻¹ ↦ A²`. §5.2 uses
this.

### 1.3 Calibration: the orientation calculus, checked against the repo

The canonical orientation is characterised by Labute descent
(`GQ2/Roe/CrossedDerivation.lean:183` `IsLabuteOrientationDatum`, :192
`IsLabuteOrientation`, :201 the four-equation extraction). The two rules that do all the work
are proved in that file:

* `conjP_wordLift` (:79) — `D(x^s) = S⁻¹Dx + S⁻¹(X−1)Ds`
* `commP_wordLift` (:91) — `D[g,h] = G⁻¹(H⁻¹−1)Dg + H⁻¹(1−G⁻¹)Dh`

together with the product rule `D(gh) = Dg + χ(g)Dh` and `D(g^k) = (1+χ(g)+⋯+χ(g)^{k−1})Dg`.

**Calibration on the ℚ₂ relator `A²S⁴[S,Y]`** (the shape `d0LiftHom` pins,
`GQ2/SectionThree.lean:445`). Writing `X_A, X_S, X_Y` for the character values:

| coefficient | equation | forced value |
|---|---|---|
| `D_A` | `1 + X_A = 0` | `X_A = −1` |
| `D_Y` | `X_Y⁻¹(1 − X_S⁻¹) = 0` | `X_S = 1` |
| `D_S` | `X_A²·4 + X_S⁻¹(X_Y⁻¹ − 1) = 0` | `X_Y = (−3)⁻¹` |

This reproduces `chiD0G`'s generator values `(−1, 1, (−3)⁻¹)`
(`GQ2/Roe/MarkedMatching.lean:298–303`, stress test at :1182) **exactly**. The same calculus is
applied to the rank-four cores below.

---

## 2. Core `M_α`

### 2.1 The abelianization 4-frame

Abelianising `P_M` kills the commutators and leaves the **relation vector**

```
ρ_M = 2Ā + 2^α C̄₀ = 2·(Ā + m C̄₀),      m = 2^{α−1}.
```

Smith normal form of `ρ_M` over `ℤ₂` is `(2,0,0,0)` in the basis `(t, B̄, C̄₀, D̄)` with
`t := Ā + m C̄₀`. Hence

```
L_M := D_M^{ab} ≅ ℤ/2·t ⊕ ℤ₂·B̄ ⊕ ℤ₂·C̄₀ ⊕ ℤ₂·D̄,        Ā = t − m C̄₀ (forced row).
```

*This is the rank-four analogue of `BDecomposition` (`GQ2/SectionThree.lean:422`) with the
substitution `2 ↦ m`*: there `D₀^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂` with `t = Ā·S̄²` (:426) and forced row
`Ā ↦ (1,−2,0)` (:418, computed at `Classification.lean:1014` `bE_A`). Setting `α = 2` gives
`m = 2` and deleting the `B`-coordinate returns the ℚ₂ frame on the nose. Torsion:
`demushkinQ D_M = 2` (compare `demushkinQ_DR_eq_two`, `GQ2/Roe/DRAbelianization.lean:576`).

### 2.2 The marked invariant triple

**(i) Canonical orientation.** Solving the descent system for `P_M = A²[A,B]C₀^{2^α}[C₀,D]`:

| coefficient | equation | forced value |
|---|---|---|
| `D_B` | `X_A X_B⁻¹(X_A − 1) = 0` | `X_A = 1` |
| `D_A` | `1 + X_A X_B⁻¹ = 0` | `X_B = −1` |
| `D_D` | `X_D⁻¹(1 − X_C⁻¹) = 0` | `X_C = 1` |
| `D_C` | `2^α + (X_D⁻¹ − 1) = 0` | `X_D = (1 − 2^α)⁻¹ =: u` |
| base | `X_A² X_C^{2^α} = 1` | `1 = 1` ✓ |

```
χ_M(A, B, C₀, D) = (1, −1, 1, u),   u = (1−2^α)⁻¹ ∈ 1 + 2^α ℤ₂ (depth exactly α),
im χ_M = ⟨−1⟩ × ⟨u⟩ = {±1}·(1 + 2^α ℤ₂)   — packet §8 line 765's `C = ⟨−1⟩×⟨u⟩`, recovered.
```

On the frame: `χ̄(t) = 1`, `χ̄(B̄) = −1`, `χ̄(C̄₀) = 1`, `χ̄(D̄) = u`.

**(ii) Torsion relation vector.** `ρ_M = 2t`; equivalently `t` is the unique element of order 2
of `L_M`, so *every* automorphism of `L_M` fixes it (the rank-three precedent is
`xi_fixes_t`, `GQ2/AnabelianBridge/Classification.lean:161`). The lift to `Λ := ℤ₂⁴` is
`Φ(ρ_M) ∈ ℤ₂ˣ·ρ_M`; the residual scalar acts trivially on `L_M`, so on `L_M` the
relation-vector clause is automatic and the α-dependence sits entirely in the forced `Ā`-row.

**(iii) Mod-2 cup Gram.** `L_M/2L_M = 𝔽₂⁴` on `(t̄=Ā, B̄, C̄₀, D̄)` (note `m` even, so
`t̄ = Ā` mod 2). Reading the initial form of `P_M`: the square `A²` gives the diagonal Bockstein
entry, `[A,B]` and `[C₀,D]` give hyperbolic off-diagonals, and `C₀^{2^α}` gives **no** diagonal
entry because `2^α ≡ 0 (mod 4)` for `α ≥ 2`:

```
G_M = ⟨A*,A*⟩=1, ⟨A*,B*⟩=⟨B*,A*⟩=1, ⟨C*,D*⟩=⟨D*,C*⟩=1, all others 0
    = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]     (dual basis of H¹, α-independent)
```

Cross-check: the same reading applied to the ℚ₂ relator `r₂` gives
`[[0,1,0],[1,0,0],[0,0,1]]`, which is exactly `drCup_obs`
(`GQ2/Roe/DRDemushkin.lean:347`, docstring :228–230) — the `x⁻⁴` term contributes 0 and `y²`
contributes 1, the same `mod 4` rule.

### 2.3 The Smith–Witt stabilizer `St_M`

`St_M := { φ ∈ Aut_cont(L_M) : χ̄∘φ = χ̄, φ preserves ρ_M, φ̄ ∈ O(G_M) }`.

*χ-conditions.* `χ̄(φ(v)) = (−1)^{v_B}·u^{v_D}` and `{±1} ∩ (1+2^αℤ₂) = 1`, `u` of infinite
order, so the D-row is pinned exactly and the B-row only mod 2:

```
φ(D̄) has D̄-coefficient 1;  φ(B̄), φ(C̄₀) have no D̄-component;
φ(B̄) has odd B̄-coefficient;  φ(C̄₀), φ(D̄) have even B̄-components.
```

*Witt/cup conditions* (solving `M̄ G_M M̄ᵀ = G_M` over `𝔽₂` under the above): two new relations —
`φ(C̄₀)` has **no** `t`-component, and

> **the `C̄₀`-component of `φ(B̄)` ≡ the `t`-component of `φ(D̄)` (mod 2)** — the coupling.

(Verified independently by the dual computation: `B ↦ B+C` alone breaks `⟨A*,C*⟩ = 0`; adding
`D ↦ D+A` restores it.)

**Closed form.** With `τ ∈ ℤ/2`, `β, γ ∈ ℤ₂ˣ`, `B_c, c₁, d₁, e ∈ ℤ₂`:

```
φ(t)   = t
φ(B̄)   = τ·t + β·B̄ + B_c·C̄₀
φ(C̄₀)  = 2c₁·B̄ + γ·C̄₀
φ(D̄)   = (B_c mod 2)·t + 2d₁·B̄ + e·C̄₀ + D̄
```

Seven parameters, one coupling. Every defining condition is **α-independent**; α enters only
through the dictionary `Ā = t − mC̄₀`. (Sanity: the rank-three specialisation — delete `B̄`,
so `β, B_c, c₁, d₁, τ` disappear — leaves `(γ, e)`, i.e. exactly the `(u,b)` of
`prop_3_8_classification`, `GQ2/AnabelianBridge/Classification.lean:342`.)

### 2.4 Nielsen generators of `St_M` (finite list, packet §14)

| # | family | parameter | frame action | stratum |
|---|---|---|---|---|
| M1 | `Λ_k` : `B ↦ A^k·B` | `k ∈ ℤ₂` | `τ = k mod 2`, `B_c = −km` | **S1** |
| M2 | `E_e` : `D ↦ C₀^e·D` | `e ∈ ℤ₂` | `e` | **S1** |
| M3 | `Σ_γ` : `C₀ ↦ C₀^γ`, `A ↦ A·C₀^{m(1−γ)}` | `γ ∈ ℤ₂ˣ` | `γ` | **S2** (B8) |
| M4 | `Σ_β` : `B ↦ B^β` | `β ∈ ℤ₂ˣ` | `β` | **S3** |
| M5 | `X_b` : `B ↦ B·C₀^{B_c}`, `D ↦ t^{B_c}·D` | `B_c ∈ ℤ₂` | `B_c` free part + coupled `τ_D` | **S3** |
| M6 | `Y_c` : `C₀ ↦ B^{2c₁}·C₀` | `c₁ ∈ ℤ₂` | `c₁` | **S3** |
| M7 | `Z_d` : `D ↦ B^{2d₁}·D` | `d₁ ∈ ℤ₂` | `d₁` | **S3** |

**Completeness argument** (Smith + Witt, in coordinates). Smith normal form of `ρ_M` gives the
frame of §2.1 and pins `φ(t) = t`; the χ-conditions pin the `D`-row and the parity of the
`B`-row; Witt cancellation splits `G_M` as `⟨A,B⟩ ⊥ ⟨C₀,D⟩` and the isometry equations reduce to
the two relations of §2.3. Given `φ ∈ St_M`, multiply successively by
`Σ_γ(γ⁻¹), Σ_β(β⁻¹), Y_c(−c₁), Z_d(−d₁), X_b(−B_c), Λ_k(−τ), E_e(−e)`; each step kills one
parameter and perturbs only parameters killed later (the group is filtered: the unipotent radical
is 2-step nilpotent with the seven families as root subgroups). The residue is the identity.
∎ (sketch — MC3 formalises it)

### 2.5 Lifts

Notation: images are given as words in `D_M`; validity means the relator dies **in `D_M`**, which
is what the universal property (`d0LiftHom`-pattern, `GQ2/SectionThree.lean:444`;
`drLiftHom`, `GQ2/Roe/DRPresentation.lean:185`) requires — relations may be used, cf.
`theta_relator` (`Construction.lean:864`) which consumes `d0_relation_hnn`.

**M1** `B ↦ A^k B`, others fixed. Then `w_M = A·A^B ↦ A·A^{A^kB} = A·A^B = w_M` **exactly**
(`A^{A^k} = A`), and the `(C₀,D)`-half is untouched, so `P_M ↦ P_M`. Axiom-free, one line.
(Variant `B ↦ B·A^k` gives `w_M ↦ w_M^{A^k}` and needs the compensating conjugation
`C₀,D ↦ C₀^{A^k}, D^{A^k}`; same frame action.)

**M2** `D ↦ C₀^k D`, others fixed. Then `C₀^D ↦ C₀^{C₀^kD} = C₀^D`, so
`z_M = C₀^{2^α−1}C₀^D ↦ z_M` exactly, and `P_M ↦ P_M`. This is the rank-four `Θ_b`: compare
`thetaHom` (`Construction.lean:880`, `Y ↦ Y·S^b` with `A ↦ A^{S^b}`) — same pattern, same
one-line commutator identity. Axiom-free.

**M3** is the `Ψ_u` analogue; see §5.2 (built from B8, twice).

**M4–M7** are the residue; see §5.3.

*Bijectivity*: each image system is unipotent-plus-unit mod 2, so the induced endomorphism is
surjective on the Frattini quotient, hence surjective (pro-2 Nakayama) and hence an
automorphism by `profinite_hopfian` + `continuousMulEquivOfBijective`
(`GQ2/Reconstruction.lean:76`, :44) — the route `psiEquiv`/`thetaEquiv` already use
(`Construction.lean:679`, :929).

### 2.6 `ν_M` in the frame (feeds MC5/F4)

Draft `Mpc-core` change of variables (lines 285–300): `A = x₀^{-1}C₀^{-m}`,
`B = x₁σ^{ε2^{r−1}}`, `C₀ = x₂σ^{2^r}`, `D = σ^η`, with `ν(σ)=1`, `ν(x_i)=0`. Hence

```
ν_M(A) = −m·2^r,  ν_M(B) = ε2^{r−1},  ν_M(C₀) = 2^r,  ν_M(D) = η
⇒ in the frame (t, B̄, C̄₀, D̄):   ν_M = (0, ε2^{r−1}, 2^r, η).
```

The `t`-entry **must** vanish (`t` is torsion, `ℤ₂` is torsion-free) and it does:
`ν(A) + mν(C₀) = −m2^r + m2^r = 0`. This is a free consistency check on the whole change of
variables and it passes.

---

## 3. Core `N_α`

### 3.1 The abelianization 4-frame

`ρ_N = (2+2^α)·x̄₀ = 2(1+2^{α−1})·x̄₀` and `1+2^{α−1} ∈ ℤ₂ˣ` for `α ≥ 2`, so the relation
submodule is exactly `2ℤ₂·x̄₀` and

```
L_N := D_N^{ab} ≅ ℤ/2·x̄₀ ⊕ ℤ₂·x̄₁ ⊕ ℤ₂·σ̄ ⊕ ℤ₂·x̄₂,     t := x̄₀,   no forced row.
```

**This is the structural difference from M**: in `N` the torsion generator *is* a marked
generator and the frame is completely α-independent; in `M` it is the α-dependent combination
`Ā·C̄₀^m`. (Both have `q = 2`; see the correction V2/§7.1.)

### 3.2 The marked invariant triple

**(i) Orientation.** For `P_N = x₀^{2+2^α}[x₀,x₁][σ,x₂]`:

| coefficient | equation | forced value |
|---|---|---|
| `D_{x₁}` | `X_b⁻¹(1 − X_a⁻¹) = 0` | `X_{x₀} = 1` |
| `D_{x₂}` | `X_d⁻¹(1 − X_c⁻¹) = 0` | `X_σ = 1` |
| `D_σ` | `X_σ⁻¹(X_{x₂}⁻¹ − 1) = 0` | `X_{x₂} = 1` |
| `D_{x₀}` | `(2+2^α) + (X_{x₁}⁻¹ − 1) = 0` | `X_{x₁} = −(1+2^α)⁻¹ =: v` |

```
χ_N(x₀, x₁, σ, x₂) = (1, v, 1, 1),   v = −(1+2^α)⁻¹,   im χ_N = ⟨v⟩ ≅ ℤ₂ procyclic.
```

Recovers the draft's `v` (line 333) exactly. **The M/N separation is here**: `im χ_M` is
`ℤ/2 × ℤ₂` (`−1` is an independent factor), `im χ_N` is procyclic (`−1 ∉ im χ_N`, because
`−1 = v^c` forces `c = 0`). That is Labute's even-rank `q = 2` invariant, and it is what the
`MLabHypothesis`/`NLabHypothesis` image clauses must encode (§6.4).

Note the third row: the `[σ,x₂]` factor contributes **zero** to every derivation coefficient and
`1` to the character relation once `χ(σ) = χ(x₂) = 1`. This is the general **handle lemma**
(§4.2) read off the repo's `commP_wordLift`.

**(ii) Relation vector.** `ρ_N = 2t`, `t = x̄₀`; same remarks as §2.2(ii), with no α-dependence.

**(iii) Cup Gram.** `x₀^{2+2^α}` has exponent `≡ 2 (mod 4)` ⇒ diagonal 1; `[x₀,x₁]` and `[σ,x₂]`
give hyperbolic pairs:

```
G_N = [[1,1,0,0],[1,0,0,0],[0,0,0,1],[0,0,1,0]]   in the dual basis of (x₀,x₁,σ,x₂).
```

Same matrix as `G_M` in its own basis — as it must be (nondegenerate non-alternating symmetric
`𝔽₂`-forms of rank 4 are all isometric). **The cup form is not what distinguishes M from N**;
`im χ` and the position of `t` are.

### 3.3 The Smith–Witt stabilizer `St_N`

*χ-conditions.* `χ̄(φ(v)) = v^{v_{x₁}}` and `v` has **infinite order**, so the `x₁`-row is pinned
*integrally* (not just mod 2):

```
φ(x̄₁) has x̄₁-coefficient exactly 1;   φ(σ̄), φ(x̄₂) have no x̄₁-component.
```

*Witt/cup conditions.* The `(σ,x₂)`-block must be invertible mod 2, and the mod-2 coupling

```
(p̄, q̄) = (τ̄_{x₂}·g₁ + τ̄_σ·g₂ ,  τ̄_{x₂}·h₁ + τ̄_σ·h₂)
```

links the `(σ̄,x̄₂)`-components `(p,q)` of `φ(x̄₁)` to the `t`-components `(τ_σ, τ_{x₂})` of
`φ(σ̄), φ(x̄₂)`. **Closed form**, with `τ ∈ ℤ/2`, `p,q ∈ ℤ₂`, `g = [[g₁,g₂],[h₁,h₂]] ∈ GL₂(ℤ₂)`:

```
φ(t)   = t
φ(x̄₁) = τ·t + x̄₁ + p·σ̄ + q·x̄₂
φ(σ̄)  = τ_σ·t + g₁·σ̄ + h₁·x̄₂
φ(x̄₂) = τ_{x₂}·t + g₂·σ̄ + h₂·x̄₂          (τ_σ, τ_{x₂} determined mod 2 by (p,q,g))

St_N ≅ (ℤ/2 × ℤ₂²) ⋊ GL₂(ℤ₂).
```

Completely α-independent. (Sanity check at rank two: for `G = ⟨a,b | a^{2+2^α}[a,b]⟩ = ℤ₂⋊ℤ₂`
the same recipe gives `St = {b̄ ↦ τt + b̄}`, and `Aut(G) = {a ↦ a^s, b ↦ a^k b}` realises exactly
that — the stabilizer is *sharp* in rank two.)

### 3.4 Nielsen generators of `St_N`

| # | family | parameter | frame action | stratum |
|---|---|---|---|---|
| N1 | `x₁ ↦ x₀^k·x₁` | `k ∈ ℤ₂` | `τ = k mod 2` | **S1** |
| N2 | `x₂ ↦ x₂·σ^k`, `(x₀,x₁) ↦ (x₀,x₁)^{σ^k}` | `k ∈ ℤ₂` | transvection `x̄₂ ↦ x̄₂ + kσ̄` | **S1** |
| N3 | `σ ↦ σ·x₂^k`, `(x₀,x₁) ↦ (x₀,x₁)^{x₂^k}` | `k ∈ ℤ₂` | transvection `σ̄ ↦ σ̄ + kx̄₂` | **S1** |
| N4 | handle determinant `det g = κ ∈ ℤ₂ˣ` | `κ` | `σ̄ ↦ κσ̄` (+shears) | **S2** (B8) |
| N5 | `x₁ ↦ x₁σ^p` (+ coupled `x₂ ↦ x₀^{p}x₂`) | `p ∈ ℤ₂` | `p` | **S3** |
| N6 | `x₁ ↦ x₁x₂^q` (+ coupled `σ ↦ x₀^{q}σ`) | `q ∈ ℤ₂` | `q` | **S3** |

N2/N3 generate `SL₂(ℤ₂)` on the handle block (elementary matrices generate `SL₂` over a local
ring); N4 supplies the determinant, so N2–N4 give all of `GL₂(ℤ₂)`.

**Completeness**: given `φ ∈ St_N`, kill the block by N2–N4, then `(p,q)` by N5/N6 (which carry
their coupled `t`-shifts), then `τ` by N1.

### 3.5 Lifts

**N1** `x₁ ↦ x₀^k x₁`: `w_N = x₀^{1+2^α}·x₀^{x₁} ↦ x₀^{1+2^α}·x₀^{x₀^kx₁} = w_N` exactly; the
handle is untouched. Axiom-free.

**N2** `x₂ ↦ x₂σ^k`: `[σ, x₂σ^k] = [σ,x₂]^{σ^k}` (one-line identity), so the handle factor picks
up the conjugator `σ^k`; the relator then needs `w_N ↦ w_N^{σ^k}`, supplied by conjugating the
whole `(x₀,x₁)`-half by `σ^k`. Net: `P_N ↦ P_N^{σ^k}`, which is `1` in `D_N`. Frame action is
the pure transvection (conjugation is trivial on the abelianization). **N3** is the mirror
(`[σx₂^k, x₂] = [σ,x₂]^{x₂^k}`). Both axiom-free.

**N4** see §5.2; **N5/N6** see §5.3.

### 3.6 `ν_N` in the frame

Compact row `r = 0` (draft :328): marked = Labute letters, `ν_N = (0, 0, 1, 0)` on
`(t, x̄₁, σ̄, x̄₂)`. Procyclic row `r ≥ 1` (draft :331–345): `σ = b^ρ`, `x₁ = cσ^{-2^r}`,
i.e. Labute `b = σ^η`, `c = x₁σ^{2^r}`, `d = x₂`, giving `ν_N = (0, η, 2^r, 0)` in the Labute
frame `(t, b̄, c̄, d̄)`. Again `ν(t) = 0` ✓.

---

## 4. Uniformity in `α ≥ 2`, and the handles

### 4.1 Where α appears

| object | `M_α` | `N_α` |
|---|---|---|
| relation vector | `2Ā + 2^αC̄₀` | `(2+2^α)x̄₀` |
| torsion generator | `t = Ā + mC̄₀` (**α-dependent**) | `t = x̄₀` (α-free) |
| forced row | `Ā ↦ (1, 0, −m, 0)` (**α-dependent**) | none |
| orientation | `χ(D) = (1−2^α)⁻¹` | `χ(x₁) = −(1+2^α)⁻¹` |
| cup Gram | α-free (needs `2^α ≡ 0 mod 4`, i.e. `α ≥ 2`) | α-free (needs `2+2^α ≡ 2 mod 4`) |
| stabilizer conditions | α-free | α-free |
| generator families | α-free except `Λ_k` (`B_c = −km`) | α-free |

So **the only α-dependence in the whole design is: the definition of `t` (M only), the forced
`Ā`-row (M only), the two scalars `u = (1−2^α)⁻¹`, `v = −(1+2^α)⁻¹`, and the exponent in the
relator word**. Everything else — stabilizer shape, generator list, lifting constructions — is
uniform. Two Lean-level consequences:

1. **`α` should be a parameter of the definitions, never a case split.** `Parameters.lean:177`
   already carries `Valid (.M α) ↔ 2 ≤ α`; MC2 should take `(α : ℕ) (hα : 2 ≤ α)` and use
   `2^α = 4·2^{α−2}` once, in the two places where `mod 4` is needed.
2. **⚠ The rank-three `decide` route for the cup Gram does not survive.**
   `drRelZ_drCC` (`GQ2/Roe/DRDemushkin.lean:339`) proves the Gram by `revert v w; decide` —
   a finite evaluation of the relator in a 16-element extension over all 64 coordinate pairs.
   With a relator exponent `2^α` this is not a finite check. MC2 must instead prove a small
   **exponent lemma** ("in a class-2 central extension, `x^{2k}` contributes `k·(x*⌣x*)`"), or a
   general "cup Gram from the relator's mod-Frattini³ normal form" lemma. Budget for it; it is
   reusable across all five branch words and is a real gap versus the survey's "DRDemushkin as
   template" line (`recon/mc-survey.md:138–141`).

### 4.2 Handles (feeds MC5)

**Handle lemma** (derived here from `commP_wordLift`, `GQ2/Roe/CrossedDerivation.lean:91`): if
`χ(u_j) = χ(v_j) = 1` then `D[u_j,v_j] = 0` and `χ([u_j,v_j]) = 1`. Hence appending
`∏_{j<h}[u_j,v_j]` to either core

* leaves the character relation and every derivation coefficient unchanged ⇒ **the orientation
  values on the core letters are unchanged and `χ ≡ 1` on all handle letters**;
* leaves the relation vector unchanged ⇒ **the torsion (`q = 2`) and the frame's first
  coordinate are unchanged**; the frame grows by `2h` free `ℤ₂`-coordinates;
* adds `h` hyperbolic blocks to the cup Gram (`⟨u_j*, v_j*⟩ = 1`, diagonal 0).

**But the stabilizer grows super-linearly**: the `2h` new χ-trivial coordinates are constrained
only by the cup form, so `St` acquires an `O(G)`-sized block coupling handles to the core plane —
including new *mixing* directions of exactly the S3 kind (§5.3). MC5's "handle stability" is
therefore **not** a formality; it is the same three-stratum problem at rank `n+2`. Recommendation:
MC5 states handle stability only for the subgroup generated by the listed families plus the
handle transvections (all S1, by the `[σ,x₂]`-identity of §3.5 applied to each handle), and
defers the general handle block to the same G-Lab decision as S3.

---

## 5. Lifting: the three strata

### 5.1 S1 — elementary Nielsen lifts (axiom-free, constructed above)

M1, M2, N1, N2, N3 and all handle transvections. Each is a two-line relator computation using
only `A^{A^k} = A`, `[σ,x₂σ^k] = [σ,x₂]^{σ^k}`, plus a compensating conjugation of the other
free factor so that the two halves of the relator acquire the *same* conjugator. The pattern is
exactly `theta_relator`/`thetaHom`/`thetaEquiv` (`Construction.lean:864/880/929`). No axioms, no
Labute input; these belong in MC3/MC4 as ordinary lemmas.

### 5.2 S2 — the unit scalings come from the **existing** axiom B8 (new finding)

`GQ2/PeripheralAction.lean` states B8 on the **abstract** group
`Δ = maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))` (:72) with `P = of 0`, `T = of 1`,
`C = (PT)⁻¹` (:75–83) and, for each `u ∈ ℤ₂ˣ`, a continuous automorphism sending each of `P, T,
C` to a cyclotomic conjugate (`PeripheralCyclotomicAction`, :92; axiom at
`GQ2/Foundations/Axioms.lean:225`). **Nothing in the bundle mentions `D₀`, `ℚ₂`, or rank three.**

Therefore B8 applies verbatim to any three-term factorisation `X·Y·Z = 1` in a core, via a
transport map `Δ → D_P`. Both rank-four cores have *two nested* such factorisations (§1.2), so
the scaling automorphism is built by **two applications of B8 with the same `u`**:

```
inner (M):  Δ → D_M,  P ↦ A,  T ↦ A^B,  C ↦ w_M⁻¹
   ⇒ A ↦ (A^u)^{λᵢ(c_P)},  B ↦ λᵢ(c_P)⁻¹·B·λᵢ(c_T),   and  w_M ↦ (w_M^u)^{λᵢ(c_C)} for free
outer (M):  Δ → D_M,  P ↦ w_M,  T ↦ C₀^{2^α−1},  C ↦ C₀^D
   ⇒ C₀ ↦ (C₀^u)^{λₒ(c_T)},  D ↦ λₒ(c_T)⁻¹·D·λₒ(c_C)
match the two conjugators of w_M by an inner twist of the (A,B)-half (frame-trivial)
```

and identically for `N` with `(w_N, σ⁻¹, σ^{x₂})` and `(x₀^{1+2^α}, x₀^{x₁}, w_N⁻¹)`.
Frame action (conjugation is invisible on the abelianization): `Ā ↦ uĀ`, `C̄₀ ↦ uC̄₀` for M —
i.e. **`γ = u`, family M3** — and `x̄₀ ↦ ux̄₀`, `σ̄ ↦ uσ̄` for N — i.e. **the handle determinant,
family N4**; `B̄`/`D̄` (resp. `x̄₁`/`x̄₂`) pick up uncontrolled shifts, absorbed afterwards by S1
shears. This is precisely how `prop_3_8_lift` is assembled:
`(thetaEquiv b').trans (psiEquiv R u)` (`Construction.lean:1094`), with `b'` computed from the
conjugator's coordinate (`bCoord_psiHom_Y`).

**Consequences.**
* No new axiom, **no census bump**, for the scalings. The AX lane should record this (it removes
  a candidate "AX7").
* MC3/MC4 acquire a B8 dependency in exactly two lemmas each. This is a *widening* of the MC
  lane's trust base relative to `GQ2/Roe/Labute/**` (which is axiom-free,
  `Assembly.lean:44–52`), but it is the same axiom the frozen ℚ₂ path already uses for the same
  purpose. Flag at merge; it does not violate plan §0.1 (B8 is not one of the nine obligations,
  and MC-M/MC-N remain *theorems* proved from a published input — the rank-three precedent
  exactly).
* Reusable Lean asset: MC2 should expose a **generic transport lemma** `peripheralTriple`
  ("given `X·Y·Z = 1` in a pro-2 group `H` with `⟨X,Y⟩` free pro-2 of rank 2, B8 yields a
  `u`-scaling endomorphism"), instantiated four times. `lambdaHom`/`pushed_identity`
  (`Construction.lean:486`, :501) is the rank-three instance to generalise.

### 5.3 S3 — the residue: mixing transvections

Families **M4 (`β`), M5 (free part of `B_c`), M6 (`c₁`), M7 (`d₁`)** and **N5, N6 (`p,q`)** move
a letter of one free factor into the *other* factor. They are genuinely outside S1 ∪ S2:

* they are not factor-preserving, so the "matched conjugator" recipe of §5.1 does not apply:
  `[a, b·s^p] = [a,s^p]·[a,b]^{s^p}`, and the defect `[a,s^p]` is a cross-factor commutator. The
  one repair that would work — replacing `s^p` by an element of `C_{D_P}(a)` with the same abelian
  class — is unavailable if centralizers in a Demushkin group are procyclic (expected, PD²
  analogy; *not verified here*, and the failure of one repair is not a proof of impossibility);
* B8's conjugators `λ(c_•)` are words in the *peripheral triple*, so the shifts they produce lie
  in the span of the triple's classes — never in the mixing direction (checked for both cores).

They *are* in the stabilizer (verified by direct isometry computation, §2.3/§3.3) and they *do*
extend to the class-2 quotient (that is what the stabilizer conditions say). So the obstruction,
if any, lives in **degree ≥ 3 of the Zassenhaus filtration** — exactly the "degree-`j` Nielsen
differential plus exceptional cokernel" content that the draft's Thm 2.1 sketch
(`refs/dyadic-presentations.tex:371–387`) and the levelwise campaign
(`GQ2/Roe/Labute/**`, 8953 lines) handle.

**Is S3 needed?** Yes, for the marked correction. Writing `ν' = ν_K∘f` in the frame:

* `N`, compact row: `(ν'∘φ)(x̄₁) = ν'(x̄₁) + p·ν'(σ̄) + q·ν'(x̄₂)` must be `0`; S1 ∪ S2 leave it
  equal to `ν'(x̄₁)`, which the marked data `(C,I,λ,γ)` does **not** pin (the `r = 0` congruence
  `ν' ≡ λ∘χ mod 2^r` is vacuous; `I = C` only forces `(ν'(σ̄),ν'(x̄₂))` unimodular).
* `M`: `(ν'∘φ)(B̄) = β·ν'(B̄) + B_c·ν'(C̄₀) = ε2^{r−1}` needs `β` (M4) or the free part of `B_c`
  (M5) in general.

So the per-core theorems as stated in the packet cannot be completed from S1 ∪ S2 alone. §8 gives
the options.

---

## 6. Lean statement skeletons (MC2–MC5)

Namespace `GQ2.Dyadic.MarkedCore`; plan §3 A5 file map. Skeletons are shape-accurate, not
type-checked (MC1 writes no Lean).

### 6.1 MC2 — `GQ2/Dyadic/MarkedCore/Cores.lean`

```lean
/-- The `M_α` core word shape (`a²[a,b]c^{2^α}[c,d]`), evaluated in any group. -/
def mWord {G : Type*} [Group G] (α : ℕ) (a b c d : G) : G :=
  a ^ 2 * commP a b * c ^ (2 ^ α) * commP c d

/-- The `N_α` core word shape (`a^{2+2^α}[a,b][c,d]`). -/
def nWord {G : Type*} [Group G] (α : ℕ) (a b c d : G) : G :=
  a ^ (2 + 2 ^ α) * commP a b * commP c d

/-- `h` hyperbolic handles on the trailing letters. -/
def handleWord {G : Type*} [Group G] {h : ℕ} (u v : Fin h → G) : G :=
  ∏ j, commP (u j) (v j)

theorem map_mWord {F G H} [Group G] [Group H] [FunLike F G H] [MonoidHomClass F G H]
    (φ : F) (α : ℕ) (a b c d : G) :
    φ (mWord α a b c d) = mWord α (φ a) (φ b) (φ c) (φ d)          -- naturality, cf. map_drWord

theorem mWord_comm {G} [CommGroup G] (α : ℕ) (a b c d : G) :
    mWord α a b c d = a ^ 2 * c ^ (2 ^ α)                          -- abelian collapse ⇒ ρ_M

/-- The three-term peripheral factorisation (§1.2) — the workhorse for §5.2. -/
theorem mWord_triple {G} [Group G] (α : ℕ) (a b c d : G) :
    mWord α a b c d = (a * conjP a b) * c ^ (2 ^ α - 1) * conjP c d

noncomputable def DM (α n : ℕ) : ProfiniteGrp := maxProPQuotient 2 (profinitePresentation {mRelator α n})
noncomputable def DN (α n : ℕ) : ProfiniteGrp := …

noncomputable def mLiftHom (α n : ℕ) (hH : IsProP 2 H) (m : Fin (n+2) → H)
    (hrel : mWord α (m 0) (m 1) (m 2) (m 3) * handleWord … = 1) :
    ContinuousMonoidHom (DM α n) H                                  -- d0LiftHom/drLiftHom clone

theorem dm_topGen (α n : ℕ) :
    (Subgroup.closure (Set.range (dmGen α n))).topologicalClosure = ⊤   -- dr_topGen pattern
theorem dm_hom_ext … -- dr_hom_ext pattern (DRAbelianization.lean:132, :151)

/-- Equation-(11) analogue for `M_α`: `D_M^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂ × ℤ₂`, torsion `t = A·C₀^{2^{α-1}}`. -/
structure MDecomposition (α n : ℕ) where
  e : ContinuousMulEquiv (topAbelianization (DM α n))
        (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]))            -- (+ ℤ₂^{2h} for handles
  map_t : e (abMk (dmA * dmC ^ (2 ^ (α - 1)))) = Multiplicative.ofAdd (1, 0, 0, 0)
  map_B : e (abMk dmB) = Multiplicative.ofAdd (0, 1, 0, 0)
  map_C : e (abMk dmC) = Multiplicative.ofAdd (0, 0, 1, 0)
  map_D : e (abMk dmD) = Multiplicative.ofAdd (0, 0, 0, 1)

theorem mE_A (B : MDecomposition α n) :
    B.e (abMk dmA) = Multiplicative.ofAdd (1, 0, -(2 ^ (α - 1) : ℤ_[2]), 0)   -- forced row

/-- `N_α`: the torsion generator is a marked generator; no forced row. -/
structure NDecomposition (α n : ℕ) where
  e   : ContinuousMulEquiv (topAbelianization (DN α n)) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2]))
  map_t : e (abMk dnX0) = Multiplicative.ofAdd (1, 0, 0, 0)
  map_B : e (abMk dnX1) = Multiplicative.ofAdd (0, 1, 0, 0)
  map_C : e (abMk dnSigma) = Multiplicative.ofAdd (0, 0, 1, 0)
  map_D : e (abMk dnX2) = Multiplicative.ofAdd (0, 0, 0, 1)

/-- Orientation, descent form (CrossedDerivation.lean:183 pattern). -/
def IsLabuteOrientationDatumM (α : ℕ) (Xa Xb Xc Xd : ℤ_[2]ˣ) : Prop :=
  ∀ Da Db Dc Dd : ℤ_[2],
    mWord α (⟨Da,Xa⟩ : WordLift ℤ_[2] ℤ_[2]ˣ) ⟨Db,Xb⟩ ⟨Dc,Xc⟩ ⟨Dd,Xd⟩ = 1

theorem isLabuteOrientationDatumM_iff (α : ℕ) (hα : 2 ≤ α) (Xa Xb Xc Xd : ℤ_[2]ˣ) :
    IsLabuteOrientationDatumM α Xa Xb Xc Xd ↔
      (Xa = 1 ∧ Xb = -1 ∧ Xc = 1 ∧ (Xd : ℤ_[2]) * (1 - 2 ^ α) = 1)     -- §2.2(i); closed form
theorem isLabuteOrientationDatumN_iff (α : ℕ) (hα : 2 ≤ α) … :
      (Xa = 1 ∧ (Xb : ℤ_[2]) * (1 + 2 ^ α) = -1 ∧ Xc = 1 ∧ Xd = 1)     -- §3.2(i)

noncomputable def chiM (α n : ℕ) : ContinuousMonoidHom (DM α n) ℤ_[2]ˣ    -- via mLiftHom
noncomputable def nuM (α n : ℕ) : ContinuousMonoidHom (DM α n) Ztwo       -- nuDR pattern (:87)

/-- Demushkin bookkeeping (generic `GQ2/Demushkin.lean`). -/
theorem card_H1_DM (α n : ℕ) : Nat.card (H1 (DM α n) (ZMod 2)) = 2 ^ (n + 2)
theorem card_H2_DM (α n : ℕ) : Nat.card (H2 (DM α n) (ZMod 2)) = 2
theorem isDemushkin_DM  : IsDemushkin 2 (DM α n)
theorem demushkinRank_DM : demushkinRank 2 (DM α n) = n + 2
theorem demushkinQ_DM    : demushkinQ (DM α n) = 2
/-- Cup Gram — see §4.1(2): prove via an exponent lemma, NOT `decide`. -/
theorem mCup_obs (α : ℕ) (hα : 2 ≤ α) (v w : Fin (n+2) → ZMod 2) :
    obsH2_DM (mH1 v ⌣ mH1 w) = v 0 * w 0 + v 0 * w 1 + v 1 * w 0 + v 2 * w 3 + v 3 * w 2 + ⋯
```

### 6.2 MC3 / MC4 — `M.lean` / `N.lean` (the obligations)

```lean
/-- The Smith–Witt stabilizer of the `M_α` invariant triple, in the frame of `MDecomposition`. -/
def IsMStabilizer (α n : ℕ) (B : MDecomposition α n)
    (φ : ContinuousMulEquiv (topAbelianization (DM α n)) (topAbelianization (DM α n))) : Prop :=
  (∀ x, chiMab α n (φ x) = chiMab α n x) ∧ mCupIsometry α n B φ

/-- Classification: closed form of the stabilizer (§2.3) — the rank-four `prop_3_8_classification`. -/
theorem mStabilizer_classification (α n : ℕ) (hα : 2 ≤ α) (B : MDecomposition α n)
    (φ : …) (hφ : IsMStabilizer α n B φ) :
    ∃! p : (ZMod 2 × ℤ_[2]ˣ × ℤ_[2] × ℤ_[2] × ℤ_[2]ˣ × ℤ_[2] × ℤ_[2]),   -- (τ,β,B_c,c₁,γ,d₁,e)
      B.e (φ (abMk dmB)) = Multiplicative.ofAdd (p.1, p.2.1, p.2.2.1, 0) ∧ …

/-- Generator-family lifts (§2.5): one `def` + one `_apply` lemma triple per family. -/
noncomputable def mLambda (k : ℤ_[2]) : ContinuousMulEquiv (DM α n) (DM α n)   -- M1, axiom-free
noncomputable def mTheta  (e : ℤ_[2]) : ContinuousMulEquiv (DM α n) (DM α n)   -- M2, axiom-free
noncomputable def mPsi (R : PeripheralCyclotomicAction) (γ : ℤ_[2]ˣ) :
    ContinuousMulEquiv (DM α n) (DM α n)                                        -- M3, via B8 ×2

/-- **MC-M** (the obligation). `hMix` is the S3 binder — see §8; it is a `def`, never an axiom. -/
theorem prop_MC_M_lift (α n : ℕ) (hα : 2 ≤ α) (B : MDecomposition α n)
    (R : PeripheralCyclotomicAction) (hMix : MMixHypothesis α n)
    (φ : …) (hφ : IsMStabilizer α n B φ) :
    ∃ Ψ : ContinuousMulEquiv (DM α n) (DM α n),
      ∀ x, B.e (abMk (Ψ x)) = B.e (φ (abMk x))
```

`N.lean` is the mirror with `NDecomposition`, `IsNStabilizer`, families N1–N6 and
`NMixHypothesis`. The matching engine (masters → mod-2 span → `evalMatrix` invertibility →
solve → contract, `GQ2/Roe/MarkedMatching.lean:307–1112`) ports with `Fin 3 ↦ Fin (n+2)`;
`isLabuteOrientation_comp_iso` (:576) and `isUnit_evalMatrix` (:525) are rank-generic in method,
and the mod-2 span argument (`mem_closure_gens_of_iso` :441, `toAdd_mem_span_of_mem_closure`
:465 — already stated for `Fin n`) needs only the generator set widened. `exists_correction`
(:980) becomes the `(n+2)`-variable linear solve of §5.3.

### 6.3 MC5 — `Certificate.lean`

```lean
/-- Packet Def. 7.1 (ledger §5.1 field list).  `K` is spelled as in LG2a
(`GQ2/Dyadic/LocalGauss/EulerShapiro.lean:782`): `K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])`
with `[FiniteDimensional ℚ_[2] K]`, and `G_K = ↥K.fixingSubgroup`. -/
structure MarkedCoreCertificate (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (P : StandardCore) where
  abstractEquiv  : ContinuousMulEquiv (DP P) (maxProPQuotient 2 ↥K.fixingSubgroup)
  orientation    : ∀ g, chiK K (abstractEquiv g) = chiP P g
  correction     : ContinuousMulEquiv (DP P) (DP P)
  correction_chi : ∀ g, chiP P (correction g) = chiP P g
  correction_nu  : ∀ g, nuK K (abstractEquiv (correction g)) = nuP P g

/-- Packet Prop. 7.2 — the marked-matching reduction. -/
theorem marked_matching_reduction (K) (α n) (hα : 2 ≤ α)
    (hLab   : MLabHypothesis α n)                    -- abstract Demushkin iso (G-Lab)
    (hRecip : MarkedRecip K)                         -- AX3 interface: (C, I, λ, γ)
    (hData  : markedDataEq K (.M α))                 -- equality of marked data
    (hLift  : ∀ φ, IsMStabilizer α n B φ → ∃ Ψ, …)   -- MC-M
    : Nonempty (MarkedCoreCertificate K (.M α))
```

Proof shape (packet lines 738–747): transport `ν_K` through `abstractEquiv` to `ν'`; Smith normal
form + Witt cancellation produce `φ ∈ St` with `ν'∘φ = ν_P` (the linear solve of §5.3, using the
frames of §2.6/§3.6); lift by `hLift`; compose.

### 6.4 The per-core hypothesis `def`s (never axioms)

Modelled exactly on `BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:141`), including its documented
conventions (`Nat.card`-encoded `IsDemushkin`/`demushkinRank`/`demushkinQ`; descent-characterised
orientation; `ℤ₂ˣ`-character house style). **Deviation from the rank-three form**: the ℚ₂ version
is specialised to the concrete `D_R` (:133–136 discusses the abstract-`G` alternative "and its
cost"); here the other side is `G_K(2)`, not a presented group, so the abstract-`G` form is
forced.

```lean
/-- The `M_α` image invariant: `⟨−1⟩ × ⟨(1−2^α)⁻¹⟩ = {±1}·(1+2^α ℤ₂)`. -/
noncomputable def imChiM (α : ℕ) : Subgroup ℤ_[2]ˣ :=
  (Subgroup.closure {-1, mUnit α}).topologicalClosure
/-- The `N_α` image invariant: the procyclic `⟨−(1+2^α)⁻¹⟩`. -/
noncomputable def imChiN (α : ℕ) : Subgroup ℤ_[2]ˣ :=
  (Subgroup.closure {nUnit α}).topologicalClosure

/-- **M-Lab (hypothesis form — never an axiom).** Labute's classification of Demushkin groups of
even rank with `q = 2` (Labute 1967, Thm 8; even-rank `q=2` types are separated by `im χ`),
specialised to the `M_α` core. -/
def MLabHypothesis (α n : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [T2Space G] [TotallyDisconnectedSpace G],
    IsDemushkin 2 G → demushkinRank 2 G = n + 2 → demushkinQ G = 2 →
      (∃ χ : G →* ℤ_[2]ˣ, Continuous χ ∧ IsLabuteOrientationOf χ ∧
        MonoidHom.range χ = imChiM α) →
        Nonempty (ContinuousMulEquiv G (DM α n))

def NLabHypothesis (α n : ℕ) : Prop := …   -- identical with `imChiN α`, `DN α n`
```

The `im χ` clause is exactly the M/N separator (§3.2(i)) and the analogue of B-Lab's
`Function.Surjective χ` encoding (:130–132).

---

## 7. Scope, corrections, conflicts

### 7.1 Correction: the "different torsion" premise

Two inherited statements are inaccurate.

* `tickets.md:280–282`: "`M_α` … and `N_α` … have different torsion, so two frames."
* `recon/mc-survey.md:121–123`: `M_α` and `N_α` "have *different* torsion structure from
  `A²S⁴[S,Y]`, so the 4-coordinate frames are genuinely new math, not a re-index."

**All three cores have `q = 2` and torsion subgroup `ℤ/2`**: `D₀^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂`
(`BDecomposition`, `SectionThree.lean:420–430`), `D_M^{ab} ≅ D_N^{ab} ≅ ℤ/2 ⊕ ℤ₂³` (§2.1, §3.1) —
as they must be, `M` and `N` being *the* two even-rank `q = 2` Labute families and `A²S⁴[S,Y]`
the odd-rank one. What is true, and is what the two statements were reaching for:

1. the `M`-frame **is** essentially a re-index of the ℚ₂ frame — same shape with `2 ↦ m = 2^{α−1}`
   plus one extra free coordinate — so `MDecomposition` can be written by copying
   `BDecomposition`; whereas
2. the `N`-frame is genuinely new: the torsion generator is a *marked generator* (`x̄₀`) and there
   is **no forced row**; and
3. the decisive separator between `M` and `N` is not torsion at all but `im χ`
   (`ℤ/2 × ℤ₂` vs procyclic, §3.2(i)) — which is also what the hypothesis `def`s must encode
   (§6.4).

Recorded here; the board is orchestrator-owned and MC1 does not edit it.

### 7.2 Gap: the compact-`M` change of variables is not in the vendored sources

Packet Prop. 8.1 (line 774) fixes the two surviving `M` rows as compact (`r = 0`) and procyclic
(`r ≥ 1`, `η` odd), and the plan's table (`plan.md:51`) writes the compact core as
"(compact `M` core)". The vendored draft displays only the procyclic substitution
(lines 285–300) and the superseded sign row (306–324); at `r = 0` the procyclic recipe
degenerates (`ε2^{r−1} = ε/2`). **F4/MC5 need the compact-`M` marked change of variables**; it is
not derivable from what is vendored. Owner question Q4 (§9).

### 7.3 Packet ↔ this memo

No mathematical conflict. One **scope** discrepancy to record: packet §14 (line 1077) states the
completion criterion as "a finite list of orientation-preserving Nielsen generators lifts the
Smith–Witt stabilizer". A finite generator list exists (§2.4, §3.4 — that part of the criterion
is met), but the memo's constructions realise only strata S1 ∪ S2; the S3 families are in the
stabilizer, are needed for the marking correction, and are not reachable by Nielsen moves or by
B8 (§5.3). Either the packet's author has a construction we have not reproduced, or the criterion
implicitly assumes the degree-≥3 Labute machinery. **Flagged, not silently resolved.**

### 7.4 Cross-campaign caveat (standard-cores assumption)

This memo is valid while the simplification campaign's winning words specialise to these standard
cores up to certified moves. Current evidence supports that: the twisted-square candidate's pro-2
specialisation was found machine-identical to the collector's marked core, and the campaign's
`R5` freeze (= our `G-1`) has not moved the core families. If a winner's pro-2 core is *not*
`Aut(F)`-equivalent to `P_M`/`P_N`, §§2–5 must be recomputed for the new word; §1.3's calculus,
§4.2's handle lemma, and §5.2's B8 transport are word-independent and survive.

### 7.5 Risks

| # | risk | mitigation |
|---|---|---|
| R1 | **S3 residue blocks MC3/MC4** (the central risk) | §8 decision; spike MC3a below |
| R2 | Cup Gram by `decide` does not survive the `2^α` exponent (§4.1) | budget the exponent lemma in MC2; it is reusable for all branch words |
| R3 | Handles enlarge the stabilizer with new S3-type directions (§4.2) | MC5 states handle stability for the generated subgroup; general case rides on the same decision |
| R4 | B8 dependency enters the MC lane (§5.2) | acceptable (frozen ℚ₂ path uses it identically); record in the axiom report so the MC capstone's print is expected, and keep `GQ2/Roe/Labute/**`-style axiom-free lemmas separate |
| R5 | `⟨A, A^B⟩`, `⟨C₀^{2^α−1}, C₀^D⟩` must be free pro-2 of rank 2 for the B8 transport | closed subgroups of free pro-2 groups are free pro-2; the rank-2 claim needs a short lemma — put it in MC2, not MC3 |
| R6 | The abstract-`G` form of `MLabHypothesis` (§6.4) is stronger than B-Lab's core-specific form | unavoidable (the other side is `G_K(2)`); note it at G-Lab since it widens what the owner is being asked to accept |
| R7 | Torsion/handle interaction: an α-dependent torsion generator (M) mixing with handle coordinates | the relation vector is untouched by handles (§4.2), so `t` stays `Ā·C̄₀^m`; verified, low risk |

---

## 8. The G-Lab decision sheet

G-Lab was scoped as *one* decision (discharge route for the Demushkin-classification
hypotheses). This memo finds it is **two**.

### Decision 1 — `MLabHypothesis` / `NLabHypothesis` (as planned)

| option | content | cost | verdict |
|---|---|---|---|
| **(a)** levelwise campaign per core | Rebuild `GQ2/Roe/Labute/**` for rank four, twice, uniformly in α. Calibration: the rank-three lane is **8953 lines, zero sorries, zero census axioms** (`Assembly.lean:44–52`), of which `TwoCentralTower.lean` (928 ln) and most of `GradedLie/Magnus.lean` (971 ln) are already rank-generic and reusable (`recon/mc-survey.md:104–118`). The relator-specific mass — `Levelwise.lean` (1570), `StageLemma/**` (3338), `SpanFoundation` (424), `Assembly` (281) — must be redone at rank 4 with a *parametric* base case (the rank-three `k₀ = 3` base lives in a group of order `2⁸`; at rank four with an `α`-dependent relator the base case is a family, not a `decide`). Estimate **6–8 k lines per core, 12–16 k total**, plus a new parametric-base technique that does not exist in the repo. | very high | not now |
| **(b)** published-literature axiom (Labute 1967) | One axiom per core under G-AX. Plan §4 already lists it as "**NOT an axiom by default**" (`plan.md:195`). | ~0 | **not recommended** (campaign preference; and it is the single largest trust widening on offer) |
| **(c)** stay parametrized | Keep the two `def`s as binders; every downstream capstone carries them, exactly as `main_presentation_literal_roe` carried `BLabHypothesis` before L6 (`AxiomLedger.lean:128–133`). | 0 | **recommended now** |

**Recommendation (Decision 1): (c), stay parametrized**, with (a) held open as the eventual
discharge. Rationale: the ℚ₂ campaign shipped in exactly this state for months and the eventual
discharge (`bLab`) printed *identically* to the assumed version — i.e. the binder cost nothing
downstream — and rank-four levelwise work should not be started before the word selection (G-1)
is frozen and MC2–MC5 are green.

### Decision 2 — the S3 lifting residue (new; §5.3)

| option | content | cost | verdict |
|---|---|---|---|
| **(A)** prove S3 by a levelwise/graded-Lie argument on the presented cores | The degree-≥3 correction argument, per core, uniform in α. Same machinery class as Decision 1(a) but a *smaller* target (correct one relator to a conjugate power, rather than build an isomorphism from cohomological data). Estimate **2–4 k lines per core**, unknown-risk. | high | later |
| **(B)** isolate S3 as its own binder `MMixHypothesis α n` / `NMixHypothesis α n` | A one-line `def` per core, consumed by MC3/MC4 exactly like `hBLab`. MC3/MC4 stay otherwise unconditional: the classification (§2.3/§3.3), the S1 lifts, the S2 lifts, the matching engine port and the completeness argument all land. | ~0 | **recommended** |
| **(C)** fold S3 into `MLabHypothesis`/`NLabHypothesis` by stating them in *marked* form | i.e. return to the draft's two-character Thm 2.1 shape. Fewer binders, but it re-imports what the packet deliberately removed and makes the binder much stronger. | ~0 | no |
| **(D)** new axiom | Forbidden in substance: S3 *is* MC-M/MC-N content (plan §0.1, merge gate 7.4). | — | **excluded** |

**Recommendation (Decision 2): (B) now, plus a bounded spike.** Concretely:

* MC3/MC4 take `hMix` as an explicit binder and prove everything else (this keeps the lane on
  schedule and produces the classification + two thirds of the lifting unconditionally);
* add **MC3a — S3 spike** (fable, ~1 day, `docs/dyadic/mc-s3-spike.md`): attempt the degree-3
  correction for the single family N5 (`x₁ ↦ x₁σ^p`) on `D_N`, where the relator is smallest and
  the handle structure cleanest. A success turns Decision 2 into (A) with a known technique; a
  documented failure with an explicit degree-3 obstruction is equally decision-grade and should be
  sent back to the packet's author (§7.3).

**Two-sentence summary for the owner.** Keep both Demushkin-classification hypotheses as
hypothesis binders (option c) — the ℚ₂ precedent shows the binder is free downstream and the
rank-four levelwise campaign (≈6–8 k lines *per core*) should not start before G-1 freezes the
words. Separately, a newly-identified lifting residue inside MC-M/MC-N itself should also be
bound (as `MMixHypothesis`/`NMixHypothesis`) rather than axiomatised, with a one-day spike to
decide whether it can be proved directly; the unit scalings, by contrast, need **no** new axiom —
the existing B8 covers them.

---

## 9. Open questions for the owner

1. **Decision 2** above: accept `MMixHypothesis`/`NMixHypothesis` as binders and authorise the
   MC3a spike? (If not, MC3/MC4 must be re-scoped to "classification + S1/S2 lifts only" and MC5
   becomes conditional in a less legible way.)
2. **B8 in the MC lane** (§5.2): approve MC3/MC4 depending on axiom B8 for the unit scalings? It
   is not a census change, but it widens the MC lane's print relative to the axiom-free
   `GQ2/Roe/Labute/**` precedent. (Alternative: bind the scalings too, keeping the whole MC lane
   axiom-free at the cost of a third binder.)
3. **Abstract-`G` hypothesis form** (§6.4, R6): confirm that `MLabHypothesis` may quantify over
   all pro-2 `G` with the stated invariants (forced, since the other side is `G_K(2)`), rather
   than the core-specific form used for `BLabHypothesis`.
4. **Compact-`M` change of variables** (§7.2): can the owner supply it (from the packet author or
   `~/claude/general_2adic`)? F4, MC5 and the `WM0` lane all need it, and it is absent from the
   vendored sources.
5. **Packet feedback** (§7.3): should the S3 finding be sent to the packet's author now (it
   affects the stated §14 completion criterion for two of the nine obligations), or held until
   the MC3a spike reports?
6. **Rank/degree scope**: MC2–MC5 as designed cover rank four plus handles for all even `n`. Is
   the `L` family (odd `n`, rank `n+2 ≥ 5`) expected to reuse this lane's stabilizer machinery
   (its rank-three base is the frozen ℚ₂ core, so only the handle strata are new), or does it stay
   with the `WL` lane?

---

## 10. Discoveries affecting other tickets

* **MC2**: (i) the cup Gram cannot be proved by `decide` (§4.1 R2) — budget an exponent lemma;
  (ii) the orientations are closed-form, so **no `OrientationRoot`-style Hensel work is needed**
  (a real saving versus the rank-three lane); (iii) add the "free pro-2 rank 2" lemma for the two
  peripheral pairs (R5) and the generic B8 transport lemma (§5.2) — both are MC2 assets, not MC3.
* **MC3/MC4**: the stabilizer classification is *pure linear algebra over `ℤ₂`/`𝔽₂`* (§2.3, §3.3)
  and is independent of the lifting question — it can and should land first, unconditionally.
* **MC5**: `ν_P` in frame coordinates is computed here for three of the four rows (§2.6, §3.6),
  each passing the `ν(t) = 0` consistency check; the marked correction is the explicit `3×3`
  linear solve of §5.3, the rank-four `exists_correction`.
* **F4 / branch lane**: the compact-`M` substitution gap (§7.2); and `im χ_M = {±1}(1+2^αℤ₂)`,
  `im χ_N = ⟨−(1+2^α)⁻¹⟩` are the branch classifier's `C`, recomputed independently here and
  agreeing with packet §8 and draft §2.2.
* **AX lane**: **no new axiom is needed for the rank-four scalings** — B8 as written is abstract
  and reusable (§5.2). Any future "AX7 = rank-four peripheral action" proposal should be closed
  in favour of reusing B8.
* **WW lane**: the three-term peripheral normal form (§1.2) and the HNN forms
  (`C₀^D = …`, `σ^{x₂} = …`) are the shapes the `PWord` syntax must support cheaply
  (`conj`, `zpow`, `comm`); `mWord_triple` is the reflected-word identity WW1's Fox evaluator will
  want, and the `mod 4` exponent rule of §2.2(iii) is the same rule the Stokes/Hessian layer uses
  for diagonal terms.
* **SD lane**: rank enters only as `demushkinRank = n+2`, `card_H1 = 2^{n+2}` (§6.1) — consistent
  with SD-n's `8 ↦ 2^{n+2}` parameterisation (`plan.md:107`).
