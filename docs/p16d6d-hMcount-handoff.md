# P-16d6d — `hMcountM` handoff: `#MLifts = |M_B|²` (the (139) M-lift count)

**Written 2026-07-06 (Opus).** Self-contained roadmap for the sole remaining sorry of P-16d6d,
`GQ2.SectionEight.hMcountM_local` (`GQ2/Half139Local.lean`). Companion to `docs/p16d6d-handoff.md`
(the P-16d6d scoping doc) and the file docstring of `Half139Local.lean` (the 5-step summary).

## Status this session

The **plumbing half of P-16d6d is done and committed** (commit `P-16d6d: local (139) plumbing …`):

| decl (`GQ2.SectionEight`, `GQ2/Half139Local.lean`) | statement | axioms |
|---|---|---|
| `rhoPrime_surjective` | `Surjective (RF.rhoPrime b F D hD ρ)` (any source) | std-3 |
| `hlem86M_local` | `∀ ρ, 2·#{central M-lifts} = #(M-lifts)` for `G_ℚ₂` | std-3 + B6 + B7 |
| `half139_local` | the (139) identity in `RecursionInputs.half139` shape | std-3 + B6 + B7 (+ the `hMcountM` sorry) |
| `hMcountM_local` | **`#MLifts = |M_B|²`** — the sole sorry | (target: std-3 + B6 + B7) |

`half139_local` is the P-16d6d deliverable consumed at P-16d6e; it is complete **modulo
`hMcountM_local`**. Gate: `lake build GQ2.Half139Local` green; `scripts/check_axioms.sh` passes
(`Half139Local.lean` on the allowlist).

**`hMcountM` is a shared deep input.** The concurrent P-16d6b (`PhaseMuIndep.lean`, now CLOSED
sorry-free) does **not** prove `#MLifts`; it takes it as the hypothesis `hML`/`κM` of
`tcocycle_mu_indep`, deferred to the P-16d6e assembly. So `hMcountM_local` (this doc) is the one
place `#MLifts = |M_B|²` gets proved for `G_ℚ₂`. The `Γ_A` twin needs the same over `Γ_A` (via
`prop_5_15`, the `HalfTorsorGammaA` self-duality) — a parallel P-16c-style build, out of scope here.

---

## The count, and why it is `|M_B|²` (the math)

`MLifts D ρ'` (`D = En.radData l h`, `D.M = RF.MB = M_B`, `ρ' = rhoPrime … ρ : G_ℚ₂ → YB/M_B`) is
the set of continuous hom-lifts of `ρ'` through `YB ↠ YB/M_B`. Standard extension theory:

* When **nonempty**, `MLifts D ρ' ≃ Z¹_cont(G_ℚ₂, M_B)` where `M_B` is a `G_ℚ₂`-module by
  `ρ'`-conjugation (`f ↦ (γ ↦ f γ · f₀ γ⁻¹)` for a base lift `f₀`; `M_B` abelian by `MB_elem`).
* `#Z¹_cont(G_ℚ₂, M_B) = |M_B|² · #H²(G_ℚ₂, M_B)` — this is `card_Z1_eq`
  (`LocalLiftingDuality.lean:264`) combined with `card_H2_eq_fixedPts`
  (`LocalLiftingDuality.lean:213`), since `#fixedPts C (ElemDual M_B) = #H²(G_ℚ₂, M_B)`.
* So the count is `|M_B|² · #H²(G_ℚ₂, M_B)`, and the claim `= |M_B|²` is **exactly
  `#H²(G_ℚ₂, M_B) = 1`**.

**Sanity check that rules out the naive reading:** with *trivial* `G_ℚ₂`-action on `M_B`,
`#Z¹ = #Hom_cont(G_ℚ₂, M_B) = |M_B|³` (because `H¹(G_ℚ₂, 𝔽₂)` is 3-dimensional:
`ℚ₂ˣ/(ℚ₂ˣ)² ≅ (ℤ/2)³`). So the action is genuinely nontrivial and the `|M_B|²` value **requires**
`#H²(G_ℚ₂, M_B) = 1`, i.e. the vanishing of the `YC`-coinvariants `(M_B)_{YC} = 0` (local duality:
`H²(G_ℚ₂, M_B) ≅ ((M_B^∨)^{YC})^∨ ≅ ((M_B)_{YC})^∨`).

### Why `(M_B)_{YC} = 0` — the key structural fact (from minimality of `K`)

This is the crux the P-16d6d scoping doc flagged as "the real content" but did **not** resolve; here
is the full argument. Layers (all in `RecursionFrame`/`MinimalBlock`, `SectionEight.lean:1345–1372`,
`SectionSeven.lean:121–152`):

* `YB = Y/R`, `YC = Y/K`, `R = Blk.R = Φ(Blk.K)` (`frattiniLike`), so
  `M_B = Blk.K.map piB = K/R`, `T_B = (K∩S).map piB = (K∩S)/R`, and
  `V := M_B/T_B ≅ K/(K∩S) ≅ KS/S = P/S` (the block's chief factor). `YC = Y/K` acts on `M_B` by
  conjugation.

**Claim.** `M_B = K/R` has **no nonzero trivial `YC`-quotient** (⟺ `(M_B)_{YC} = 0`).

*Proof.* Suppose `π : M_B ↠ 𝔽₂` is a nonzero `YC`-module map (trivial target action). Its kernel
`M'` is a `YC`-submodule of index 2.
1. `π` cannot kill `T_B`: otherwise it factors through `V = M_B/T_B = P/S`, which is a **nontrivial
   chief factor** (`Blk.chief` + `Blk.nontrivial_action`) hence irreducible with **no** trivial
   quotient — contradiction. So `π|_{T_B} ≠ 0`, i.e. `T_B ⊄ M'`, i.e. `M' ∩ T_B` has index 2 in
   `T_B`, and `M' + T_B = M_B`.
2. Let `K'` be the preimage of `M'` in `K` (so `R = Φ(K) ≤ K' ≤ K`, `[K:K'] = 2`). `M'` a
   `YC`-submodule ⟹ `K'` is `Y`-normal. From `M' + T_B = M_B` (i.e. `K'·(K∩S) = K`) we get
   `K'·S ⊇ K`, so `K' ⊔ S ⊇ K ⊔ S = KS = P`, and `≤ P`; hence `K' ⊔ S = P`.
3. `Blk.minimal K' (…) (K' ≤ K) (K' ⊔ S = P)` forces `K' = K`, contradicting `[K:K'] = 2`. ∎

Equivalent purely-subgroup form (no module language), the cleanest thing to formalize first:
**`⁅(⊤ : Subgroup Y), Blk.K⁆ ⊔ Blk.R = Blk.K`** (the augmentation subgroup `[Y,K]·Φ(K)` is all of
`K`). Proof: `W := ⁅⊤,K⁆ ⊔ R` is `Y`-normal (`commutator` normal + `frattiniLike_normal`),
`W ≤ K`; its image in `V = P/S` is `⁅Y,V⁆`, which is a nonzero (`nontrivial_action`) `YC`-submodule
of the chief factor `V`, hence `= V` (`chief`), so `W ⊔ S = P`; then `Blk.minimal ⟹ W = K`.

---

## The build — 5 steps, with exact references

All over `Γ = G_ℚ₂ = AbsGalQ2`. Work inside `hMcountM_local`'s proof (or factor into private
lemmas in `Half139Local.lean`).

### Step 1 — the additive `M`-module + actions
Define `MBmod := Additive ↥(En.radData l h).M` (`= Additive ↥RF.MB`). Set up, by **copying
`RadicalEdgeLocal.lean:73–135`** with `D.T ⤳ D.M`:
* `DistribMulAction AbsGalQ2 MBmod` by `ρ'`-conjugation: `γ • m = out(ρ' γ) · m · out(ρ' γ)⁻¹`.
  Well-defined by `D.hM` (normality: conjugation stays in `M`) and independent of the coset rep by
  `D.hcomm` (`M` abelian — the direct analogue of `RadicalEdgeLocal.conj_eq_of_mk_eq`, which is
  stated for `D.T` using `D.hcomm` on `T ≤ M`; here use it on `M` itself).
* `DistribMulAction RF.YC MBmod` (the `C`-action `card_Z1_eq` needs), factoring the above through
  `ρ'`; `hcomp : γ • m = ρ' γ • m` on the nose.
* `ContinuousSMul AbsGalQ2 MBmod` (discrete-target factorization, as in
  `RadicalEdgeLocal.lean:135–147`), `2`-torsion `hA₂` from `RF.MB_elem`.

⚠ The one genuinely new bit vs. the `D.T` copy: `card_Z1_eq` also wants the **`C`-action** and
`hcomp`. `RadicalEdgeLocal` only builds the `AbsGalQ2` action (it feeds B6's pairing, not
`card_Z1_eq`). Add the `RF.YC`-action explicitly (it is `c • m = out(c) · m · out(c)⁻¹` via
`QuotientGroup.out`, or transport the `AbsGalQ2`-action along `ρ'`-surjectivity).

### Step 2 — the torsor bridge `MLifts ≃ Z¹`, incl. **nonemptiness**
`MLifts D ρ' ≃ Z¹_cont(AbsGalQ2, MBmod)` via `f ↦ (γ ↦ Additive.ofMul (f γ · f₀ γ⁻¹ ∈ M_B))` for a
base lift `f₀`. The cocycle law and continuity are routine. **Nonemptiness of `MLifts` is a
theorem, not an assumption:** the lifting obstruction of `ρ'` through `YB ↠ YB/M_B` lives in
`H²(AbsGalQ2, M_B)`, which is `0` by Step 4. So a base lift exists and the bijection holds.
* ⚠ **No `H²`-obstruction-vanishing ⇒ continuous-lift-exists lemma currently in-repo.** Options:
  (a) build the standard obstruction class + "vanishes ⇒ lift" for continuous profinite cohomology
  (general, reusable — a real addition); or (b) a bespoke existence argument using `Y ↠ YC`
  splitting off `R = Φ(K)` (`R` is Frattini, so `Y ↠ YB = Y/R` is a Frattini cover — Gaschütz /
  the repo's `eq_top_of_map_frattini_quotient_top` / `surj_of_piB_surj` family may give a lift of
  `ρ'` directly, sidestepping `H²`). **Recommend scoping (b) first** — Frattini-cover liftability
  is likely already available in `RStageObstructionBuild.lean` / `FinitelyGenerated.lean`.

### Step 3 — `card_Z1_eq`
`card_Z1_eq hρ hcomp hA₂ : #Z¹(AbsGalQ2, MBmod) = |MBmod|² · #fixedPts RF.YC (ElemDual MBmod)`
(`LocalLiftingDuality.lean:264`, axiom B7 via the Euler characteristic). Feed `hρ =
rhoPrime_surjective …`, `hcomp`/`hA₂` from Step 1. Note `|MBmod| = |↥RF.MB| = Nat.card ↥RF.MB`
(`Additive` preserves cardinality; `Nat.card_congr`/`Nat.card_eq_of_bijective` on `Additive.toMul`).

### Step 4 — `#fixedPts RF.YC (ElemDual MBmod) = 1`  ← **the group theory is ALREADY PROVED**
`#fixedPts RF.YC (ElemDual MBmod)` = # of `YC`-invariant `𝔽₂`-functionals on `M_B` = `#(M_B^∨)^C`.
The vanishing `(M_B^∨)^C = 0` (⟹ card 1) is **exactly `GQ2.SectionSeven.lemma_7_1_dual`**
(`SectionSeven.lean:449`, **PROVED std-3, no axioms, no sorry** — verified):
```
lemma_7_1_dual (B : MinimalBlock L) :
  ¬ ∃ X : Subgroup Y, X.Normal ∧ B.R ≤ X ∧ X ≤ B.K ∧ (X.subgroupOf B.K).index = 2
```
Its docstring: *"(M^∨)^C = 0 — K has no Y-normal subgroup of index 2 above R (a nonzero invariant
functional on M would be its kernel)"* — the full minimality + chief-dichotomy argument I sketched
above is already carried out there (and in the companion `lemma_7_1_radical`/`lemma_7_1_head`).

**So Step 4 is NOT new math** — only a **bridge** from the subgroup statement to the module
`fixedPts`: given `0 ≠ λ ∈ fixedPts RF.YC (ElemDual MBmod)`, its kernel `ker λ ≤ M_B = Blk.K/Blk.R`
pulls back to a `Y`-normal `X` with `Blk.R ≤ X ≤ Blk.K` and `(X.subgroupOf Blk.K).index = 2`
(index 2 ⟸ `λ` surjective onto `𝔽₂`; `Y`-normal ⟸ `λ` `YC`-invariant so `ker λ` is a `YC`-submodule,
and `YC = Y/Blk.K`-submodules of `Blk.K/Blk.R` ↔ `Y`-normal subgroups between `Blk.R` and `Blk.K`);
`lemma_7_1_dual` refutes it, so `fixedPts = {0}`, card 1. Bridge ≈ 50–80 ln (the submodule↔normal
subgroup correspondence for `M_B = K/R` + index/kernel bookkeeping).

### Step 5 — assemble
`#MLifts = #Z¹ = |M_B|² · 1 = |M_B|²`. Chain Steps 2, 3, 4.

---

## Effort / risk

* **Step 1** ~70–100 ln, mechanical (copy `RadicalEdgeLocal` D.T block, add the `YC`-action).
* **Step 3** ~30 ln once Step 1's instances are in scope.
* **Step 4** ~50–80 ln: **the math is done** (`lemma_7_1_dual`, std-3) — only the
  submodule↔`Y`-normal-subgroup bridge to `fixedPts` remains.
* **Step 2** the hardest / least in-repo support (nonemptiness). Scope the Frattini-cover route (b)
  before building general `H²`-obstruction machinery.

Recommended order: **Steps 1 + 3 + 4 first** (the count `#Z¹ = |M_B|²`, now unblocked — Step 4's
crux `lemma_7_1_dual` is already proved), reducing `hMcountM` to the single Step-2 nonemptiness
sorry; then Step 2. (Steps 1+3+4 need no new mathematics — Step 1 copies the `RadicalEdgeLocal`
D.T module block, Step 3 is `card_Z1_eq`, Step 4 bridges to the proved `lemma_7_1_dual`.)

Expected axioms at close: **std-3 + B6 + B7** (B6 `card_H2_eq_fixedPts`, B7 `card_Z1_eq`); the
P-16d6d ticket column `⊆ {B6,B7,B9}` — **B9 should not be needed**.
