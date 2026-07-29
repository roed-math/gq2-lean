# LG1 — LG-K design memo: field-generic deep-unit package + Euler-characteristic Shapiro spike

**Ticket LG1** (dyadic campaign, lane LG; board `docs/dyadic/tickets.md`). Read against repo
state `d0714a7`-lineage on branch `dyadic-lg`; all file:line anchors verified in this worktree
on 2026-07-29. Authority: packet `docs/dyadic/refs/dyadic-presentations-formalization-proof.tex`
§6 (Prop 6.6 = `prop:local-polar`, Lem 6.7 = `lem:hermitian-line`, Prop 6.8 =
`prop:unramified-sign`, Def 6.11 = `def:deep-package`, Prop 6.12 = `prop:deep-lagrangian`,
Prop 6.14 = `prop:ramified-sign`, Thm 6.15 = `thm:local-gauss`) and §12; packet overrides drafts
(`refs/README.md`).

**Headline verdicts.**

| Question | Verdict |
|---|---|
| §1 Euler-characteristic spike | **DERIVABLE from ℚ₂-B7 via explicit coinduced-module Shapiro in degrees 0/1/2. AX2 is NOT needed.** Complete lemma list L0–L6 below; every comparison formula hand-verified in this memo. One opus ticket (~850 ± 250 lines), no blocked item. |
| §2 clone-vs-retype | **13/13 clone-into-`GQ2/Dyadic/LocalGauss/`, 0 in-place edits of frozen files.** Plus a **survey scope correction**: 6 more `AbsGalQ2`-typed dependency files (~2.5 k lines) missing from the survey's §2 right column. |
| §3 (−1)^n parity | `arf_eq_of_free` (`GQ2/GaussSigns.lean:682`) applied to `H¹(G_K,V)` with `m' := m`, `s := n`, `U := C` acting via the `cActionH1` pattern; `c_cyclic` re-proved verbatim over F3's `T_q`. No new parity mathematics. |
| §5 AX6 | **Confirmed unnecessary.** `lemma_6_15_{square,free,involution}` are abstract-`G` (`GQ2/SectionSix.lean:672/:698/:714`), the Ledger aux files have **zero** `AbsGalQ2` occurrences, B9 is per-`k` (`GQ2/Foundations/Axioms.lean:268`). |

---

## 1. THE SPIKE — general-K Euler characteristic by Shapiro. Verdict: DERIVABLE

### 1.1 What B7 actually says (exact shape to mirror)

`GQ2/Foundations/Axioms.lean:117`:

```lean
axiom absGalQ2_localEulerCharacteristic (M : Type*) [AddCommGroup M] [TopologicalSpace M]
    [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M] :
    Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
      Nat.card (H1 AbsGalQ2 M)
        = Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) * 2 ^ padicValNat 2 (Nat.card M)
```

Two facts matter for the spike. (i) **B7 is quantified over ALL finite discrete modules**, not
just 2-primary ones — `2 ^ padicValNat 2 (Nat.card M)` is the 2-part of `#M`. So the induced
module of *any* finite `G_K`-module is a legal argument. (ii) The docstring
(`GQ2/EulerCharacteristic.lean:14–57`) fixes the convention `v₂(#M) = padicValNat 2 (Nat.card M)`
and notes the `H⁰`-finiteness clause is redundant-but-retained; the K-version mirrors both.

### 1.2 The derivation (no χ-multiplicativity needed)

Let `U : Subgroup AbsGalQ2` be open with `[Finite (AbsGalQ2 ⧸ U)]` (in application
`U = K.fixingSubgroup` or `ι.range`; `n := U.index = Nat.card (AbsGalQ2 ⧸ U)`). For a finite
discrete `↥U`-module `V`, form the **coinduced module** `IndMod U V` and apply B7 **to it**;
transport all three cardinalities and all three finiteness clauses through degree-wise Shapiro
bijections. Since `#(IndMod U V) = (#V)^n` and `padicValNat 2 ((#V)^n) = n * padicValNat 2 (#V)`
(mathlib `padicValNat.pow`, needs `Nat.card V ≠ 0` ✓ finite nonempty), B7 at `IndMod U V` *is*
the K-statement. No multiplicativity of χ, no dévissage.

**The module (transversal model).** The repo precedent `PermMod U := (AbsGalQ2 ⧸ U) → ZMod 2`
(`GQ2/Shapiro/Finiteness.lean:49`) is the trivial-coefficient special case. Generalize keeping
the plain-function carrier:

```lean
def IndMod (U : Subgroup AbsGalQ2) (V : Type) : Type := (AbsGalQ2 ⧸ U) → V
-- action, via the Shapiro word  wElt g x = ⟨(sect (g⁻¹•x))⁻¹ * g⁻¹ * sect x⟩ ∈ U  (:179):
--   (g • Φ) x := (wElt g x)⁻¹ • Φ (g⁻¹ • x)
```

Write `τ(g,x) := (wElt g x)⁻¹`. `wElt_mul` (`Finiteness.lean:183`) inverts to the transport rule
`τ(g₁g₂, x) = τ(g₁,x) · τ(g₂, g₁⁻¹•x)`, which gives `one_smul`/`mul_smul` directly (checked).
All of `sect`/`sect_base`/`wElt_mem`/`wElt_mul`/`smul_base_of_mem` (`:157/:166/:169/:183/:112`)
are **coefficient-free** and reusable verbatim (they live in `namespace PermMod` but mention no
module). `IndMod` must be an **instance-opaque plain `def`** — the pi-type trap is documented at
`Finiteness.lean:46–48` and again for `RegMod` in `GQ2/Shapiro/Extend.lean` (docstring) — with
instances `AddCommGroup` (pi), `TopologicalSpace := ⊥` + `DiscreteTopology`, `Finite` (pi),
`DistribMulAction AbsGalQ2` (τ-twist), and `ContinuousSMul` as a theorem-then-`haveI`
(`PermMod.continuousSMul :105` pattern; the extra τ-factor is continuous by the `hcU` argument
already written at `:210–:214`, and `[ContinuousSMul ↥U V]` + discreteness handles the smul).
Cardinality: `Nat.card (IndMod U V) = Nat.card V ^ Nat.card (AbsGalQ2 ⧸ U)` = mathlib
`Nat.card_fun` (exists: `Mathlib/SetTheory/Cardinal/Finite.lean:242`).

**Base identities** (each verified by hand; all follow from `sect_base` and `smul_base_of_mem`):

- (B1) `wElt u ⟦1⟧ = u⁻¹` for `u ∈ U` — already computed inline at `Finiteness.lean:233–239`;
  hence `(u • Φ) ⟦1⟧ = u • (Φ ⟦1⟧)`, i.e. **`ev : IndMod U V →+ V`, `Φ ↦ Φ ⟦1⟧` is
  `U`-equivariant** (generalizes `ev`/`ev_compat` `:118/:126`).
- (B2) `(s_x⁻¹ • Ψ) ⟦1⟧ = Ψ x` and dually `Ψ ⟦1⟧ = (s_x • Ψ) x`, where `s_x := sect x` (uses
  (B3)).
- (B3) `wElt (sect x) x = 1` (both `sect`-collapses).

**Degree 0.** `H0comap` of `ev` gives `H0 AbsGalQ2 (IndMod U V) →+ H0 ↥U V`; the inverse is
`v ↦ const v` — the *constant* function is `G`-invariant iff its value is `U`-invariant, because
`(g • const v) x = τ(g,x) • v` with `τ(g,x) ∈ U`; and conversely a `G`-invariant `Φ` satisfies
`Φ x = τ(s_x, x)⁻¹ • Φ ⟦1⟧ = Φ ⟦1⟧` by (B3). So `H⁰(G, Ind V) ≃ H⁰(U, V)` **by constants/ev**,
an explicit `AddEquiv` (`H0congr`-style; cf. `GQ2/CupSymmetry.lean:216`). ~50 lines.

**Degree 1.** `θ₁ := mapCoeff1 (ev) ∘ res1` exactly as `theta` (`Finiteness.lean:134`). The
section **must generalize with an inverse twist**: `σ₁(c)(g)(x) := c (τ(g,x))` (equivalently
`c ((wElt g x)⁻¹)`; the existing `sigmaFun :194` uses `c (wElt g x)`, which only works because
`𝔽₂`-inversion is trivial — flagged so the implementer does not copy it blindly). Verified:

- `Z1`-membership: `σ₁(c)(g₁g₂)(x) = c(τ(g₁,x)·τ(g₂,g₁⁻¹x)) = σ₁(c)(g₁)(x) + (g₁ • σ₁(c)(g₂))(x)`
  — the 1-cocycle rule at the transported pair; continuity as in `sigmaFun_continuous :197`.
- Round-trip A (on the nose, `Z¹`-level): `θ₁(σ₁ c)(u) = c(τ(u,⟦1⟧)) = c(u)` by (B1) — no
  `CharTwo.neg_eq` needed anymore (cf. `sigma_eval :231`).
- Round-trip B (on the nose modulo an **explicit** coboundary): for `C ∈ Z1(G, IndMod U V)`,
  `σ₁(θ₁ C) − C = δ⁰ m` with `m ∈ IndMod U V`, `m x := C (sect x) x`. Proof: expand
  `C(τ(g,x)) = C(s_x⁻¹ · g · s_{g⁻¹x})` by the cocycle rule twice, evaluate at `⟦1⟧` via (B2),
  and use `Z1_apply_inv` (`GQ2/Cohomology.lean:401`) on `C(s_x⁻¹)`. (Full computation done for
  this memo; ~40–60 Lean lines.)
- `σ₁` maps `B¹ → B¹`: `σ₁(δ⁰ v) = δ⁰ (const v)` (checked; one line each way).

Hence `θ₁` is a bijection on `H¹` with two-sided inverse `σ₁`, giving
`Nat.card (H1 ↥U V) = Nat.card (H1 AbsGalQ2 (IndMod U V))` and (from B7-finiteness of the
right side, `Foundations.finite_H1`, `GQ2/EulerCharacteristic.lean:75`) finiteness of the left.
This **strictly extends** `finite_H1_open` (`Finiteness.lean:262`), which proved surjectivity
only, for trivial `𝔽₂` only.

**Degree 2.** `θ₂ := mapCoeff2 (ev) ∘ res2` — both components exist (`mapCoeff2`
`GQ2/Cohomology.lean:441`, `res2` `:336`, both built on `H2comap :301`/`Z2comap :279`). Section:

```
σ₂(c)(g₁,g₂)(x) := c (τ(g₁,x), τ(g₂, g₁⁻¹•x))
```

- `Z2`-membership: writing `a := τ(g₁,x)`, `b := τ(g₂,g₁⁻¹x)`, `d := τ(g₃,g₂⁻¹g₁⁻¹x)`, the
  2-cocycle identity for `σ₂(c)` at `(g₁,g₂,g₃)` evaluated at `x` is **literally**
  `(δ²c)(a,b,d) = 0` (checked; the transport rule converts every argument). Continuity: same
  finite-intersection pattern.
- Round-trip A (on the nose): `θ₂(σ₂ c)(u₁,u₂) = c(τ(u₁,⟦1⟧), τ(u₂,⟦1⟧)) = c(u₁,u₂)` by (B1)
  and `u₁⁻¹•⟦1⟧ = ⟦1⟧`.
- `σ₂` maps `B² → B²`: `σ₂(δ¹ψ) = δ¹(Σψ)` where `(Σψ)(g)(x) := ψ(τ(g,x))` (checked; the same
  transport computation as `Z1`-membership).
- Round-trip B — **the one nontrivial lemma**. For `C ∈ Z2(G, IndMod U V)`:

  ```
  σ₂(θ₂ C) − C = δ¹ h,   h(g)(x) := C (s_x, τ(g,x)) x − C (g, s_{g⁻¹•x}) x .
  ```

  I derived `h` by the standard prism homotopy against the `U`-equivariant retraction
  `ρ(g) := g · s_{⟦g⁻¹⟧} ∈ U` (note `τ(g,x) = ρ(s_x⁻¹ g)`; the degree-1 specialization of the
  same formula reproduces `m x = C (sect x) x` above, a consistency check) — **and then verified
  it directly**: expand `σ₂θ₂C(g₁,g₂)(x) = (s₀ • C(τ₁,τ₂)) x` by (B2)-dual, apply the 2-cocycle
  rule (★) three times, at `(s₀, τ₁, τ₂)`, `(g₁, s₁, τ₂)`, `(g₁, g₂, s₂)` (where
  `s₀ = s_x, s₁ = s_{g₁⁻¹x}, s₂ = s_{g₂⁻¹g₁⁻¹x}`, and `s₀τ₁ = g₁s₁`, `s₁τ₂ = g₂s₂`), and the
  ten resulting terms cancel exactly against `δ¹h − C`. All continuity side-conditions
  (`h ∈ C1`) are of the locally-constant finite-intersection form already used at `:197–:216`.
  Estimate ~80–150 lines including prep lemmas.

Hence `Nat.card (H2 ↥U V) = Nat.card (H2 AbsGalQ2 (IndMod U V))` + finiteness (via
`Foundations.finite_H2`, `EulerCharacteristic.lean:79`).

### 1.3 Deliverable statement (mirrors B7's exact shape)

```lean
-- GQ2/Dyadic/LocalGauss/EulerShapiro.lean  (module-style is legal: imports
-- GQ2.Shapiro.Finiteness (MODULE) + GQ2.EulerCharacteristic (MODULE) only)
theorem localEulerCharacteristic_open (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)]
    (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [Finite V] :
    Finite (H0 ↥U V) ∧ Finite (H1 ↥U V) ∧ Finite (H2 ↥U V) ∧
      Nat.card (H1 ↥U V)
        = Nat.card (H0 ↥U V) * Nat.card (H2 ↥U V)
          * 2 ^ (U.index * padicValNat 2 (Nat.card V))
```

`U.index = Nat.card (AbsGalQ2 ⧸ U)` definitionally; consumers thread `hn : U.index = n` against
F1's `FieldParameters.n` rather than deriving `index = [K:ℚ₂]` from Galois theory (that rank
equality is *not* needed anywhere in the LG chain — only the exponent shape is).
`#print axioms` target: **std-3 + B7 only.**

### 1.4 Gap list (each item: content, template, size class)

| # | Lemma(s) | Template / anchor | Size |
|---|---|---|---|
| L0 | `IndMod` def + 6 instances + `card_indMod = #V ^ #(G⧸U)` | `PermMod` block `Finiteness.lean:49–:129`; `Nat.card_fun` | small (~130 ln) |
| L1 | τ-API: `τ(g₁g₂,x)` rule, (B1)/(B2)/(B3), continuity of `τ(·,x)` and `g ↦ s_{g⁻¹x}` | `wElt_mul :183`, inline `:233–:239`, `hcU :210–:214` | small (~80) |
| L2 | degree-0 `AddEquiv` constants/ev + `Nat.card` transport | `H0congr` `CupSymmetry.lean:216`, `card_H0_congr` `MuTwoPolarDual.lean` | small (~50) |
| L3 | degree-1: `θ₁` (general `V`), `σ₁` **with inverse twist**, Z1-mem, continuity, RT-A, RT-B (`m x = C (sect x) x`), `B¹`-preservation, `card_H1` equality | `theta :134`, `sigmaFun* :194–:255`, `Z1_apply_inv` | real dev (~220) |
| L4 | degree-2: `θ₂`, `σ₂`, Z2-mem, continuity, RT-A, `Σψ`/`B²`-preservation, **RT-B with `h(g)(x) = C(s_x,τ(g,x))x − C(g,s_{g⁻¹x})x`**, `card_H2` equality | `mapCoeff2/res2/Z2comap`; formulas in §1.2 (hand-verified) | real dev (~300) |
| L5 | assembly `localEulerCharacteristic_open` (+ `padicValNat.pow`, exponent glue) | `finite_H1_open :262` | small (~60) |
| L6 | *(deferrable)* abstract-Γ corollary along `ι : G ≃ₜ* ι.range` + group-side `H^i`-congr | comap both ways (`H1comap :289`), Z-level `rfl` round-trips | small (~80), only if LG2 picks abstract-Γ typing anywhere it consumes Euler |

Nothing is **blocked**; L3/L4 are "real development" only in the sense of length — every
identity is verified above at the formula level. Risk assessment: LOW. The two places a wrong
guess would have cost weeks — the σ-twist direction and the degree-2 homotopy `h` — are settled
in this memo, not left to the implementer.

**Consequence for AX2** (board lane AX): **close AX2 with "derived — no census flip"**. The
implementing Lean ticket is *not* currently on the board: recommend a new **LG2a** (opus,
file `GQ2/Dyadic/LocalGauss/EulerShapiro.lean`, depends only on the existing tree, unblocks
LG3/LG4 in parallel with LG2). Fallback axiom, **only** if the owner overrides (statement =
§1.3 with `axiom` and citation NSW 7.3.1 at `K`, `χ(K,A) = ‖#A‖_K`); I recommend against — the
derivation is cheaper than the axiom-review cycle.

### 1.5 Repo-API audit backing clause (a) of the ticket

`GQ2.ContCoh` (`GQ2/Cohomology.lean`): `H0 :75`, `Z1/Z2/B1/B2 :120–:129`, `H1 :132`, `H2 :141`,
`H1mk/H2mk :138/:147`, comap trio `H0comap/Z1comap/Z2comap/H1comap/H2comap :264–:311`,
`res0/1/2 :328–:337`, `mapCoeff0/1/2 :425–:442`, `inf0/1/2 :461–:470`, `Z1_apply_inv :401`,
`mem_Z1_iff/mem_Z2_iff`. **Everything needed exists**; what does *not* exist (and is exactly
L0–L4): any coinduced module beyond `PermMod`/`RegMod`, any Shapiro beyond degree-1
surjectivity at trivial coefficients, any degree-0/2 Shapiro, group-side `H^i`-congr.
`Shapiro/` inventory: `Finiteness.lean` = `PermMod` + `theta`/surjectivity + `finite_H1_open`
(:262); `Extend.lean` = `familiesExtend_of_package` (:272, inverse Shapiro at `RegMod` through a
*surjection* `ρ`, not a subgroup — different mechanism, not reusable for the Euler spike);
`Read.lean` = explicit-witness Shapiro read for `H¹(G, 𝔽₂[G/N])` (`hcoh` keystone);
`Deepness.lean` = the `hvanish` producers (§5); `Ledger{,/Free,/Involution}` = Lemma 6.15
coboundary engine (abstract).

---

## 2. Clone-vs-retype for the 13 `AbsGalQ2`-typed files

**Architecture decision (binding for LG2–LG5).** Two ambient encodings are possible:
abstract `Γ` + `IsLocalDualizingGroup Γ 2` (`GQ2/TateDuality.lean:244`), or
`Γ := ↥U`, `U : Subgroup AbsGalQ2` open finite-index. Decide **per layer**:

- **Abstract `Γ`** for the pure-cohomology quadratic layer (Q0loc quadratic structure, Euler
  collapse, H⁰-vanish, Hom-count engine): these mention no Kummer/valuation objects, and
  `TateDualityG Γ 2` (`TateDuality.lean:208`) is already the right duality carrier — the ℚ₂
  `TateDuality n` is just its `AbsGalQ2`-abbrev (`:237`).
- **`↥U`-anchored** for everything touching Kummer theory: `deepPart`
  (`GQ2/SectionSix.lean:844`) needs `IsDeepUnit (N : Subgroup (Kummer.GaloisGroup ℚ_[2]))`
  (`:742`) — there is no abstract-Γ home for a deep unit. The inner splitting-field group
  `N_K := ker ρ_K ≤ ↥U` must be re-anchored in `AbsGalQ2` as `N := (ker ρ_K).map U.subtype`
  (or via `subgroupOf` in the reverse direction). Precedent for nested-subgroup plumbing:
  `(L.fixingSubgroup).subgroupOf (k.fixingSubgroup)` throughout `lemma_6_16`
  (`SectionSix.lean:767`) and `Shapiro/Deepness.lean:190–:216`.
- Build ONE reusable **group-side `H^i`-congr** (transport along `ContinuousMulEquiv` +
  matched module) in LG2 — it collapses the `↥(N_K)`-vs-`↥N`-as-ambient-subgroup friction to a
  single lemma and provides L6 for free. This does not exist today (only coefficient-side
  `H0/H1/H2congr`, `CupSymmetry.lean:153/:188/:216`).

**A6 consequence:** all 13 files are **cloned** (content re-typed under `GQ2.Dyadic`,
`GQ2/Dyadic/LocalGauss/*`), zero in-place edits. In-place parameterization would touch frozen
proof bodies wholesale (the ambient appears in nearly every binder) and cannot keep the ℚ₂
files textually stable; wrappers cannot bridge a changed ambient type. The ℚ₂ originals stay
byte-identical ⇒ merge gate 8 (byte-identical capstone axiom prints) is trivially safe.
Post-G3 dedup (re-deriving the ℚ₂ files from the generic clones at `Γ := AbsGalQ2`) is
possible but out of campaign scope.

Per file (survey §2 right column; "→" = target file; headline decls = post-rebase signatures;
friction ratings relative to a mechanical `s/AbsGalQ2/Γ/`):

| # | File (hits/lines) | Decision → target | Headline decls after rebase | Friction / notes |
|---|---|---|---|---|
| 1 | `DeepPart/Q0locLayer.lean` (117/626) | **split-clone**: quadratic block (:44–:306) → `LocalGauss/Q0.lean` (abstract Γ); `deepPartSubgroup` (:430) + join (:547) → `LocalGauss/DeepPackage.lean` (↥U) | `graphPullback_add_sub_mem_B2 (Γ)`, `isQuadraticFp2_Q0loc (D : TateDualityG Γ 2)`, `nonsingular_Q0loc`, `card_Q0loc_zero_eq_of_dim_of_vanish` with `(m*n)`-slots and the B7 calls (`finite_H1 :568`, `card_H1_eq_card_of_simple :580`) replaced by LG2a's theorem | LOW for the quadratic block (proofs are ambient-agnostic — checked `graphPullback_add_sub_mem_B2`'s body); MEDIUM for the join (Euler rewires; `2*m ↦ 2*(m*n)` in the Arf count, engine `zeroCount_of_arf_*` already takes arbitrary `m`) |
| 2 | `LocalKummer.lean` (149/1001) | split-clone: `phiRes`/`AdmissibleFam`/`InflationVanishes` (:304)/`FamiliesExtend` (:898)/`h1EquivFam`/`inflationVanishes_of_oddNormal` (:493) → Γ-generic file; `deepClasses`/Kummer side → ↥U-anchored | `InflationVanishes (ρ : ContinuousMonoidHom Γ C)`, `FamiliesExtend ρ`, `h1EquivFam : H1 Γ V ≃ AdmissibleFam ρ`, `inflationVanishes_of_oddNormal` (coprime averaging — ambient-free) | LOW-MEDIUM. `inflationVanishes_ramifiedTame` (:587) consumes `Ttame` ⇒ its K-twin is re-proved over F3's `T_q` (same odd-normal `⟨cτ⟩` argument; packet Lem 3.1 gives pro-odd tame inertia at every `q = 2^f`) |
| 3 | `DeepDualityK.lean` (93/580) | clone → `LocalGauss/PairingK.lean` (↥U + anchored `N_K`) | `subgroup_isLocalDualizingGroup : IsOpen (W:Set AbsGalQ2) → W.FiniteIndex → IsLocalDualizingGroup ↥W 2` (generalize `ker_isLocalDualizingGroup :70` — new small lemma; open-embedding composition), `tateDualityK_K := tateDualityAt … `, `pairingK (:145)`, `pairingK_nondeg (:159)`, isotropy `pairingK_deep_deep (:514)`/`pairingK_mid_deep (:534)`/`…le_pairPerp… (:554/:567)` | MEDIUM-HIGH: this is the nested-subtype epicenter (`↥(N_K)` cohomology vs `IsDeepUnit` at the `AbsGalQ2`-image). Group-congr lemma (above) is the mitigation. The `(k, hker)` parameter pattern (`hker : x ∈ ker ρ ↔ x ∈ k.fixingSubgroup`) survives as `(L, hker′)` for the splitting field `L ⊇ K` |
| 4 | `VanishClose.lean` (77/425) | clone → part of `LocalGauss/Ramified.lean` (↥U; **plain-import forced**) | `lemma_6_17_vanish_final_K` — same 20-hypothesis shape (:205) with `c : ContinuousMonoidHom (T_q f) C`, `(R, horient)` replaced by the AX3/AX4 K-interface binder | MEDIUM: assembly-only, but the c2c4 route (odd tame inertia ⇒ involution ext unramified, `hunram` discharge) must be restated against `MarkedRecip_K` — **coordinate with AX3: its consumer list must include this discharge** |
| 5 | `DeepCount/Transport.lean` (75/373) | clone (↥U + anchored `N_K`) | `h1KerToFix`-analogue between `H1 ↥(N_K)` and `H1 (L.fixingSubgroup)`, `card_quot_deep_le_card_mid_ker (:301)` — signature already threads per-field `(k=L, π, e, f)` data | LOW-MEDIUM: the `(π,e,f)` hypotheses are **absolute (L-intrinsic)**, base-change-invariant — deep/mid cutoffs are `‖·−1‖ <,≤ ‖2‖` (`SectionSix.lean:742`, `DeepDuality.lean:1004`), no `e_K` enters |
| 6 | `AdmissibleCount.lean` (68/516) | clone (↥U) | `card_deepPart_sq_of_duality (:466)` at Γ ambient; same deferred inputs `hinf/hext/hduality` | MEDIUM: Hom-count plumbing; the engine it calls is untouched (see #8) |
| 7 | `UnramifiedModel.lean` (60/673) | clone → `LocalGauss/Unramified.lean` (plain-import; §3 below) | `c_cyclic_q` (T_q twin of :69), `cCoeff/cActionH1` (Γ-generic — its own docstring says the functoriality section is "general"), `arf_Q0loc_unramified : arf (Q0loc D dat ρ) = (n : ZMod 2)`, `prop_6_18_unramified_K` (two parity corollaries) | MEDIUM: endpoint *changes route* (engine instead of Hermitian line — §3); Schur-transfer inputs simplify (field-linearity replaces `H¹`-simplicity, which is FALSE for `n ≥ 2`) |
| 8 | `DeepDuality.lean` (54/1395) | **mostly reuse verbatim**; clone only the `AbsGalQ2`-typed conj/transport sections | `card_equivHoms_deep_eq_quot (:874)` — abstract in `(C, M, U)`, **no retype**; `IsMidUnit (:1004)`/`midClassesSubgroup` — already `N`-relative over `Kummer.GaloisGroup ℚ_[2]`, **no retype** | LOW: the 54 hits are concentrated in the conjugation-action plumbing; most of the file is consumed as-is |
| 9 | `DeepPart/MuTwoPolarDual.lean` (42/337) | clone (Γ abstract) | `card_H1_eq_card_of_H0_H2_trivial_K` — collapse now reads `#H¹ = (#M)^n` = `2^(k*n)` from LG2a (**the single point where `n` enters the dimension clause** — survey §2(c) CONFIRMED, see §4); `card_H0_eq_one_of_surjective (:…)` retype-trivial; μ₂ bricks global — no change; `#H² = 1` via `D.perfect20` at Γ | LOW |
| 10 | `ResidueLift.lean` (26/365) | clone (↥U + `IntermediateField` tower) | `splitField`-analogue over `K` (splitting field `L` with `K ≤ L`), `exists_residueTrivial_tameLift` over the K-tame quotient, `lemma_6_17_dim_final_K (:333)` | MEDIUM-HIGH: most entangled file — Galois-correspondence plumbing for the tower `ℚ₂ ≤ K ≤ L` and the tame lift now comes from AX4's K-quotient. The in-proof Shapiro-finiteness discharge (:345–:350) is replaced by LG2a's finiteness clause |
| 11 | `DimAssembly.lean` (16/279) | clone | `lemma_6_17_dim_of_hduality`/`_of_hext_hduality (:199/:249)` at Γ + `T_q` | LOW (assembly) |
| 12 | `DeepCount/Finale.lean` (13/122) | clone | `hduality_of_data (:46)` at Γ | LOW |
| 13 | `DimClose.lean` (8/105) | clone | `lemma_6_17_dim_of_residueLift (:55)` at Γ | LOW |

**Survey scope correction (matters for LG4's budget).** The survey's §2 right column omits six
`AbsGalQ2`-typed files that the vanishing lane (survey §1's own chain!) runs through — verified
occurrence counts in this worktree:

| File | AbsGalQ2 hits / lines | Role | Retype verdict |
|---|---|---|---|
| `GQ2/OrbitVanish.lean` | 63/740 | `Q0loc_vanish_of_datum_decomp` (:298) orbit reducer | clone (↥U) |
| `GQ2/InvolutionSplice.lean` | 69/634 | `hvanish_cup_ker` (:544) + splices | clone (↥U + anchors) |
| `GQ2/Shapiro/Read.lean` | 69/443 | `hcoh` coordinate read; first half abstract-`G`, `§PerOrbit` pinned at `G_ℚ₂` | clone the PerOrbit half only |
| `GQ2/Shapiro/Extend.lean` | 50/426 | `familiesExtend_of_package` (:272) | clone (ρ-surjection mechanism is ambient-agnostic) |
| `GQ2/RepIndependence.lean` | 35/210 | `lemma_6_14` naturality + `h2ofFun_eq_of_sub_mem_B2` | clone (small) |
| `GQ2/SectionSix.lean` | 21/1056 | `Q0loc` (:157), `deepPart` (:844), `lemma_6_15_*` wrappers (:672/:698/:714 — **abstract already**), `lemma_6_16` (:767 — **(k,L)-generic already**), `IsDeepUnit` (:742 — **N-relative already**) | clone only `Q0loc`/`deepPart` (~150 lines); the rest reused verbatim |
| *(context)* `GQ2/OrbitDecomp.lean` | 0/1061 | orbit data layer | **verbatim** |

Adjusted mechanical-retype surface: ~6.7 k (survey) + ~2.5 k (above) ≈ **9.2 k lines**, of
which the genuinely low-risk share is large but LG4's ticket sizing should assume the bigger
number. Everything in the survey's *left* column re-verified as consumed verbatim
(`HilbertLedger.lean` `cup_deep_deep :898`/`cup_mid_deep :907` are per-`k`;
`dyadicUnitFiltration'` `UnitFiltrationCounts.lean:390` per-`k`; `HermitianCount`,
`GaussSigns`, `QuadraticFp2`, `DeepCount/{Filtration,Bounds}` ambient-free).

---

## 3. The (−1)^n unramified-parity plan (LG3)

**Where `n` threads.** `arf_eq_of_free_norm_one` (`GQ2/GaussSigns.lean:613`) and the sharper
`arf_eq_of_free` (`:682`) prove `arf q = (s : ZMod 2)` for a nonsingular `q` on a space of size
`2^{2·(m'·s)}` under a free `q`-preserving action of `U` with (`:613`) `#U = 2^{m'}+1`, or
(`:682`) `#U ∣ 2^{2m'}−1`, `#U ∤ 2^{m'}−1`, `#U > 2`. **Instantiate on `H¹(G_K, V)` itself
with `m' := m`, `s := n`, `U := C`** (the finite acting image), where `#V = 2^{2m}` and
`#H¹ = (#V)^n = 2^{2(m·n)}` by LG2a's Euler collapse. Then `arf(Q⁰) = n (mod 2)`, and
`zeroCount_of_arf_zero/one` (already `m`-generic; used at `Q0locLayer.lean:585+`) give
`2^{2mn−1} + 2^{mn−1}` (n even) / `2^{2mn−1} − 2^{mn−1}` (n odd) = packet
`Gsum = (−1)^n 2^{n·dim V/2}` (Prop 6.8). The ℚ₂ instance is the `s = 1` case (the current
`prop_6_18_unramified` derives `arf = 1` with the trivial `H¹ ≃+ (Fin 1 → H¹)` packet —
`UnramifiedModel.lean:585+` comment block).

**Engine inputs at general `n`, and what replaces the ℚ₂ crutches:**

1. `hcard`: `#H¹ = 2^{2(m·n)}` — LG2a + `card_H0_eq_one_of_surjective` + `#H² = 1`
   (perfect20 + polar self-duality, MuTwoPolarDual clone). *This is the only place `n` enters.*
2. `hfree`: at ℚ₂ this rode on `cCoeff_faithful_and_simple` (Schur transfer: `H¹ ≅ V` simple).
   **That transfer is unavailable for `n ≥ 2`** (`H¹ ≅ V^n` is not simple). Replacement, checked
   here: `𝔽₂[C]` acts on `H¹` through `mapCoeff1` (`cCoeff`/`cActionH1`,
   `UnramifiedModel.lean:88+`); any `a ∈ 𝔽₂[C]` with `a·V = 0` acts as `mapCoeff1 0 = 0`
   (additive functoriality `mapCoeff1_id/comp` — the file's own "general" section), so the
   action factors through the image field `F := 𝔽₂[C] ≅ 𝔽_{2^{2m}}`, making `H¹` an
   `F`-vector space — **freeness of `C∖{1} ⊂ F^×` on `H¹∖{0}` is field-linearity, automatic,
   `n`-independent**.
3. `hUq` (`C`-invariance of `Q⁰` on `H¹`): `RepIndependence.lemma_6_14` naturality + the datum
   coboundary `graphPullback_comap_smul_sub_mem_B2` — exactly the ℚ₂ route
   (`UnramifiedModel.lean:560–:585`), retyped.
4. `hUsq/hUnot/hU2` (for `:682`): `V`-side facts — `C ⊂ F^×` so `#C ∣ 2^{2m}−1`;
   `𝔽₂[C] = F` (faithful simple over cyclic `C`) forbids `C` inside the middle subfield so
   `#C ∤ 2^m−1`; `#C` odd `> 1` gives `> 2`. All `n`-independent, all present in the existing
   `prop_6_9_unramified_of_cyclic ← _of_abelian ← _of_free` chain (`GaussSigns.lean:451/:410/:389`)
   at the `Q⁰_A` twin — port the extraction, not the mathematics.

**What replaces `c_cyclic` at general residue degree `f`.** `c_cyclic`
(`UnramifiedModel.lean:69`) is *not* `f = 1`-mathematics; it is `q = 2`-**typed**: its input is
`c : ContinuousMonoidHom Ttame C` and its proof is `hfaith` + `hunram` ⇒ `c τ = 1`, then
two-generator topological generation (`SectionThree.gen_ttame_quotient`) collapses `C` to
`⟨c σ⟩`. The general statement is the verbatim twin over F3's `T_q = ⟨σ,τ ∣ τ^σ = τ^{2^f}⟩`:

```lean
theorem c_cyclic_q (c : ContinuousMonoidHom (Tq f) C) (hc : Function.Surjective ⇑c)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hunram : ∀ v : V, c (tameTauQ f) • v = v) :
    ∀ x : C, x ∈ Subgroup.zpowers (c (tameSigmaQ f))
```

sole new dependency: F3's generation lemma (`gen_tq_quotient`, the `T_q`-twin of
`gen_ttame_quotient`) — **flag to F3's spec**. On "procyclic of order prime to 2": the odd
order of the unramified image is *not* a hypothesis anywhere; it is the downstream Schur
consequence `C ⊆ 𝔽_{2^{2m}}^×` (odd ambient `2^{2m}−1`), and stays automatic at every `f`.

**LG3 skeleton** (primary statement + parity corollaries; see §6 for context):

```lean
theorem arf_Q0loc_unramified_K … (hEuler : Nat.card (H1 Γ V) = 2 ^ (2 * (m * n))) … :
    arf (Q0loc D dat ρ (V := V)) = (n : ZMod 2)
theorem prop_6_18_unramified_K_even (hn : Even n) … :
    Nat.card {x : H1 Γ V // Q0loc D dat ρ x = 0} = 2 ^ (2*m*n − 1) + 2 ^ (m*n − 1)
theorem prop_6_18_unramified_K_odd  (hn : Odd n)  … : … = 2 ^ (2*m*n − 1) − 2 ^ (m*n − 1)
```

The Hermitian-line file (`DeepPart/HermitianCount.lean`, ambient-free) is **not needed** on
this route; it remains the `n = 1` regression cross-check (LG5) and the packet-faithful
alternative (diagonalize + multiply per Prop 6.8) if the engine route hits an unexpected snag —
it will not: every engine input is enumerated above.

---

## 4. Deep-package plan (LG4), per packet Def 6.11

Repo shape: **no bundled `structure DeepUnitPackage`** — mirror the ℚ₂ architecture where the
"package" is the pair of discharged clauses fed to the join
(`card_Q0loc_zero_eq_of_dim_of_vanish`, `Q0locLayer.lean:547`); the packet's Def 6.11 is the
*mathematical* grouping, `DetRamified.prop_6_18_ramified` (`DetRamified.lean:53`) the assembly
precedent. (Deviation-of-surface from the packet noted; contents identical. The ledger's named
`SquareClass` input materializes as the per-field hypothesis block of
`card_quot_deep_le_card_mid_ker`, already field-data-parametric.)

Leaf-by-leaf, with the discharging chain after retyping (all anchors = current ℚ₂ decls):

- **(a) projective inflation–restriction** `H¹(K,V) ≅ Hom_H(V^∨, L^×/L^{×2})`:
  `h1EquivFam` (`LocalKummer.lean:906+`) from `InflationVanishes` (:304) — discharged by
  `inflationVanishes_of_oddNormal` (:493, base-free averaging) at the `T_q`-tame instantiation
  (twin of `inflationVanishes_ramifiedTame` :587) — and `FamiliesExtend` (:898) — discharged by
  `Shapiro.familiesExtend_of_package` (`Extend.lean:272`) retyped. `n` does not enter.
- **(b) Hilbert orthogonality on the square-class filtration**: consumed **verbatim** — the
  whole layer is `L`-intrinsic and base-free: `cup_deep_deep/cup_mid_deep`
  (`HilbertLedger.lean:898/:907`, per-`k`, B11a), `DeepCount/{Filtration,Bounds}` (0 hits),
  `dyadicUnitFiltration'` (`UnitFiltrationCounts.lean:390`). Only the splices
  `pairingK_deep_deep/mid_deep` + `card_quot_deep_le_card_mid_ker` retype (§2 #3, #5). The
  deep/mid cutoffs are the π-free `‖A−1‖ < ‖2‖` / `≤ ‖2‖` (`SectionSix.lean:742`,
  `DeepDuality.lean:1004`) — **absolute, so `e_L` bookkeeping is unchanged under base change**.
  `n` does not enter.
- **(c) `X₊ = Hom_H(V^∨, U_{e_L+1})` of dimension `n·dim V/2`**: `deepPart`
  (`SectionSix.lean:844`) retyped to Γ-ambient with `AbsGalQ2`-anchored `N_K`; dim clause via
  the chain `lemma_6_17_dim_final → … → card_deepPart_sq_of_duality`
  (`AdmissibleCount.lean:466`) with the abstract engine `card_equivHoms_deep_eq_quot`
  (`DeepDuality.lean:874`) **verbatim**, `hduality_of_data` (`Finale.lean:46`) retyped. The
  chain yields `#X₊² = #H¹` for any base; the *value* `2^{2mn}` (hence
  `dim X₊ = mn = n·dim V/2`) comes **only** from the Euler collapse (LG2a) —
  **survey §2(c)'s claim CONFIRMED**: `n` enters the dimension clause exactly once, through
  `#H¹ = (#V)^n`; the filtration/duality side is `n`-blind.
- **(d) vanishing of the normalized graph obstruction on `X₊`**:
  `Q0loc_vanish_of_datum_decomp` (`OrbitVanish.lean:298`) retyped; its `hcoh` inputs are the
  **abstract** `lemma_6_15_{square,free,involution}` (`SectionSix.lean:672/:698/:714`, over any
  `G` + open `N`) — verbatim; its `hvanish` inputs are `hvanish_cup` (per-`k`,
  `Deepness.lean:55`), `hvanish_evensNorm` (abstract `G`, `:71`), `hvanish_involution`
  ((k,L)-pair, `:190`) with `lemma_6_16` (`SectionSix.lean:767`, any finite dyadic `k ≤ L`) —
  all **verbatim**; the middle-layer case split follows packet Rem. 6.13 (odd tame-inertia
  characters vs trivial-inertia exceptional pieces — **no "even inertia order" case**, packet
  override #6): odd tame inertia at every `q = 2^f` is packet Lem 3.1 = F3's leaf. The `hunram`
  side-condition of each involution orbit (order-2 image ∉ odd inertia ⇒ `L/k` unramified)
  re-derives from the AX3/AX4 K-interface (the c2c4 route; `(R, horient)` slot of
  `lemma_6_17_vanish_final`, `VanishClose.lean:205`). `n` does not enter.

Then packet Prop 6.12 (Lagrangian) = `deepPartSubgroup` (`Q0locLayer.lean:430`) +
`arf_zero_of_card_sq` (generic), and Prop 6.14 (`+` sign) = `zeroCount_of_arf_zero` with
`m ↦ m*n` — mechanical. **Ramified endpoint:**
`prop_6_18_ramified_K : … zero-count = 2^{2mn−1} + 2^{mn−1}` mirroring `DetRamified.lean:53`.

**Where `n` enters LG4: only via the Euler collapse feeding (c) and the final count exponents.
Survey claim confirmed, with the one refinement that the *statement* of the join theorem also
carries `n` in its `hcard`/count exponents (trivially).**

---

## 5. AX6 verdict: CONFIRMED unnecessary

- The Shapiro–Evens **orbit formula** is in-repo, std-3, and abstract:
  `lemma_6_15_square/free/involution` are stated over `{G : Type*}` with `N : Subgroup G`,
  `IsOpen (N : Set G)` (`SectionSix.lean:672/:698/:714`); the coboundary engine
  `Shapiro/Ledger/Free.lean` (580 ln) and `…/Involution.lean` (1159 ln) contain **zero**
  `AbsGalQ2` occurrences (grep-verified).
- The `hvanish` producers are abstract or per-field: `hvanish_evensNorm` abstract `G`
  (`Deepness.lean:71`); `hvanish_cup` and `hvanish_involution(_of_deepClass)` quantified over
  `k (≤ L) : IntermediateField ℚ_[2] ℚ̄₂`, `[FiniteDimensional ℚ_[2] k]` (`:55/:190/:231`).
- B9 `relativeStiefelWhitney_dyadic` is per-`k`, arbitrary finite dyadic base
  (`Foundations/Axioms.lean:268`; docstring: "base-general within the dyadic setting"), and the
  Evens-norm bridge `EvensKahn(Derived)` has zero `AbsGalQ2` hits.

Nothing in the (d)-chain needs a new `K`-quantified Shapiro–Evens statement: the only
`K`-dependence is which `(k, L, N)` get instantiated. **AX6 stays off the board.** (Caveat
recorded: the *per-orbit assembly* files `OrbitVanish`/`Read`§PerOrbit/`InvolutionSplice` are
`AbsGalQ2`-typed and must be retyped — §2's scope correction — but they consume, not restate,
the Evens content; no axiom is implicated.)

---

## 6. Statement skeletons LG2–LG5, module headers, lane graph

Module-rule facts (headers grep-verified): MODULE = `Cohomology`, `TateDuality`, `CupProduct`,
`Corestriction`, `SectionSix`, `OrbitData`, `Q0locLayer`, `LocalKummer`, `DeepDuality(K)`,
`MuTwoPolarDual`, `GaussSigns`, `HermitianCount`, `HilbertLedger`, `UnitFiltration(Counts)`,
`DeepCount/*`, `Shapiro/{Finiteness,Ledger*}`, `EulerCharacteristic`, `RepIndependence`.
PLAIN = `OrbitDecomp`, `Shapiro/{Read,Extend,Deepness}`, `OrbitVanish`, `InvolutionSplice`,
`VanishClose`, `UnramifiedModel`, `DetRamified`, `ResidueLift`, `DimAssembly`, `DimClose`,
`CorestrictionCohomology`. R31a is one-directional (module cannot import plain), so:

| New file | Header | Why |
|---|---|---|
| `LocalGauss/EulerShapiro.lean` (LG2a) | **module** | imports only `Shapiro.Finiteness` + `EulerCharacteristic` (+`Cohomology`), all MODULE |
| `LocalGauss/Q0.lean` (LG2) | **module** | imports `SectionSix`/`Q0locLayer`/`TateDuality` (MODULE) |
| `LocalGauss/PairingK.lean` (LG2) | **module** | imports `DeepDualityK`-side (MODULE) |
| `LocalGauss/Unramified.lean` (LG3) | **plain** | needs `mapCoeff1`-functoriality + Schur-transfer content cloned from `UnramifiedModel` (plain) and cross-refs it for the `n=1` regression |
| `LocalGauss/DeepPackage.lean`, `LocalGauss/Ramified.lean` (LG4) | **plain (forced)** | import the `OrbitDecomp → Read/Extend/Deepness → OrbitVanish` plain chain |
| `LocalGauss/Main.lean` (LG5) | **plain (forced)** | imports LG3/LG4 plain files + `DetRamified` for regressions |

When in doubt, plain (board rule). `GQ2.lean` imports are orchestrator-added at merge.

**LG2** (`Q0.lean`, `PairingK.lean`; namespace `GQ2.Dyadic`):

```lean
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable {C V …} (D : TateDualityG Γ 2) (dat : FactorSet C V) (ρ : ContinuousMonoidHom Γ C)
def Q0loc : H1 Γ V → ZMod 2                                   -- clone of SectionSix:157
theorem isQuadraticFp2_Q0loc / nonsingular_Q0loc / polar_Q0loc -- clone of Q0locLayer:44–:306
theorem subgroup_isLocalDualizingGroup (W : Subgroup AbsGalQ2)
    (hW : IsOpen (W : Set AbsGalQ2)) [W.FiniteIndex] : IsLocalDualizingGroup ↥W 2
noncomputable def H1congrGroup (e : Γ ≃ₜ* Γ') (module transport data) : H1 Γ M ≃+ H1 Γ' M'
-- plus the packet Prop 6.6 statement (well-definedness + B_{Q⁰} = inv ∘ ∪): the ℚ₂ names
-- polar_Q0loc / graphPullback_add_sub_mem_B2 at Γ, with D.perfect11 nondegeneracy
```

**LG2a** (`EulerShapiro.lean`): §1.3 statement + L0–L5. Closes AX2.

**LG3** (`Unramified.lean`): `c_cyclic_q`, `cCoeffK/cActionH1K`, `arf_Q0loc_unramified_K`,
`prop_6_18_unramified_K_{even,odd}` (§3). Depends: LG2, LG2a, F1 (`n, f`), F3
(`T_q`, `gen_tq_quotient`), AX3/AX4 interfaces as hypothesis binders.

**LG4** (`DeepPackage.lean`, `Ramified.lean`): retyped `deepPart`, `deepPartSubgroup`,
`InflationVanishes/FamiliesExtend` twins + discharges, `pairingK` isotropy splices,
`lemma_6_17_dim_final_K`, `lemma_6_17_vanish_final_K`, join
`card_Q0loc_zero_eq_of_dim_of_vanish_K` (exponents `2*(m*n)`), endpoint
`prop_6_18_ramified_K`. Depends: LG2, LG2a; AX3/AX4 binders; B9/B11a as-is; the §2
scope-correction files.

**LG5** (`Main.lean`): packet Thm 6.15 —

```lean
theorem local_gauss_K … (hn : U.index = n) … :
    Nat.card (H1 Γ V) = 2 ^ (2 * m * n) ∧
    arf (Q0loc D dat ρ) = if ramified then 0 else (n : ZMod 2)
-- + zero-count corollaries; regressions: n=1 pins against DetRamified.prop_6_18_ramified
-- (:53) and UnramifiedModel.prop_6_18_unramified (:585); n=2 unramified pin sign = +1;
-- ramified sign = +1 at every n.
```

**Lane graph** (arrows = hard deps):

```
LG2a (EulerShapiro) ──┬──────────────► LG3 (Unramified) ──┐
LG2  (Q0/PairingK) ───┤                                   ├─► LG5 (Main)
                      └──► LG4 (DeepPackage/Ramified) ────┘
F1 ─► LG3,LG5 (n,f)     F3 ─► LG3 (T_q gen), LG4 (Lem 3.1 odd inertia)
AX3/AX4 (hypothesis binders until census) ─► LG3, LG4
```

LG2 ∥ LG2a fully parallel; LG3 ∥ LG4 after both.

---

## 7. Risk register + cross-lane notes

1. **Survey census gap (fact, not risk):** +6 `AbsGalQ2`-typed files ≈ 2.5 k lines beyond the
   13 (see §2 table). LG4's dispatch must be sized for ~9 k lines of clone-retype, or split
   into LG4a (vanishing-lane retype) + LG4b (dim-lane + assembly).
2. **Nested-subtype friction** (`Subgroup ↥U` vs `Subgroup AbsGalQ2`): the top technical risk
   in LG2/LG4. Mitigation: the `H1congrGroup` transport lemma built once in LG2 (small — comap
   both ways, Z-level round trips are `rfl`-adjacent), plus the `subgroupOf` precedent
   (`lemma_6_16`, `Deepness.lean:190`). Watch for action-instance diamonds on `↥↥`-types
   (probe-`example` style as `DeepDualityK.lean:49–:61`).
3. **AX3/AX4 coordination:** LG4's involution `hunram` discharge (c2c4 route) and LG3/LG4's
   `(c, hfac)` boundary data consume the K-reciprocity/tame interfaces. Until censuses land,
   thread them as explicit binders (board rule); AX3's memo must list this consumer, AX4's
   normalization must fix `tameSigmaQ/tameTauQ` marking compatibly with F3's `T_q`.
4. **F3 leaf dependencies:** `gen_tq_quotient` (two-generator topological generation of `T_q`
   quotients — twin of `SectionThree.gen_ttame_quotient`) and packet Lem 3.1 (pro-odd tame
   inertia at `q = 2^f`) are consumed by LG3/LG4 — confirm they are in F3's acceptance list.
5. **Axiom hygiene:** LG2a's theorem is a *theorem* — it must NOT enter
   `GQ2/Foundations/Axioms.lean`; `EXPECTED_AXIOMS` unchanged; AX2 closes with no census flip.
   Grep-guard suggestion for F6: `localEulerCharacteristic` must never match an
   `axiom`-declaration line outside B7's.
6. **σ-twist trap:** the existing `sigmaFun` (`c(wElt g x)`, no inverse) is correct only at
   `𝔽₂`. Any implementer generalizing by copy-paste will produce a non-cocycle at nontrivial
   `V`. The correct section is `c(τ(g,x)) = c((wElt g x)⁻¹)` (§1.2). Same trap in degree 2.
7. **Parity-route change:** LG3 abandons the ℚ₂ Hermitian-line *route* (not the result) for the
   `arf_eq_of_free` engine because the Schur transfer (`H¹` simple) is false at `n ≥ 2`. If a
   reviewer insists on packet-literal Prop 6.8 (diagonalize Hermitian lines), that is a
   heavier alternative (`E`-structure + diagonalization over `E/E₀` on `H¹`) — feasible via
   `HermitianCount` but not recommended; record as an owner-visible deviation of proof route.
8. **Simplification campaign / MC lane:** LG is word-independent — no interaction with the
   `L/M_α/N_α` word selection; the only shared surfaces are F1's `FieldParameters` (LG must
   consume its `n`, `f`, `qK = 2^f` — do not introduce a second `n`) and, at AS1, the
   `DyadicLocalInput K` record: its `eulerChar` field (packet §12 table row 1,
   `DyadicLocalData.eulerChar`) should be **dropped in favor of the derived theorem** — tell
   SD1/AS1 so the record shape freezes without it. MC needs nothing from LG; no file overlap.
9. **`IntermediateField` openness/finiteness glue:** consumers must supply
   `IsOpen (K.fixingSubgroup : Set AbsGalQ2)` + `[Finite (AbsGalQ2 ⧸ K.fixingSubgroup)]`;
   mathlib's Krull-topology API (`IntermediateField.fixingSubgroup_isOpen` for
   finite-dimensional) is expected to cover it — the repo's existing `hkeropen` computations
   (`DeepDualityK.lean:72–:75`, `ResidueLift.lean:345+`) are the fallback pattern. Small,
   verify at LG2a implementation time.
10. **Uncertainty inventory (explicit):** (i) the exact mathlib name/signature of
    `padicValNat.pow` was verified against the vendored mathlib
    (`Mathlib/NumberTheory/Padics/PadicVal/Basic.lean:391`) — stable; (ii) the degree-2 RT-B
    Lean proof length is an estimate (the mathematics is verified, the `abel`-shuffle size is
    not); (iii) whether `RepIndependence.lemma_6_14`'s retype hits hidden `AbsGalQ2`-defeq
    (35 hits/210 lines — small enough to absorb); (iv) `Kummer.GaloisGroup ℚ_[2]` vs
    `AbsGalQ2` are the same type through `Field.absoluteGaloisGroup` (`GQ2/Kummer.lean:68`,
    `GQ2/Statement.lean:40`) — the repo already mixes them freely, but clones should pick one
    spelling per file.
