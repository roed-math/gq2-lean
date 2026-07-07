# P-18 plan — §10 tame-frame exhaustion, eq. (154), `main_surjection_count`

**Purpose.**  Design + ticket split for P-18 (paper §10, pp. 47–48: Lemma 10.1 + the (154)
assembly), producing `main_surjection_count` (`GQ2/Statement.lean:49`, the file's ONLY sorry).
Written 2026-07-07 (Fable), against the paper text and the verified Lean interfaces (§3).
Decomposition: **P-18a–e** (board rows).

---

## 0. TL;DR — the key design resolution

The formalization-shape worry for Lemma 10.1 (does the partition need Möbius inversion over a
poset of wild kernels?) **dissolves on reading the paper**: Lemma 10.1 fixes **`L = O₂(G)`, the
2-core** — ONE marked target `𝒴_G = (G, O₂(G), π : G ↠ G/O₂(G), θ = 0)` for all `f`, with only
the **tame frame `α : T_tame ↠ G/O₂(G)`** varying.  Since the image `f(W)` of the source's pro-2
wild kernel `W = ker(tame coordinate of b)` is a normal 2-subgroup of `G`, it lands in `O₂(G)`
**automatically, for every `f`** — so the boundary-framing condition `π∘f = α∘t` is *exactly* the
"induces frame `α`" condition.  Cells = `BoundaryLifts` sets verbatim; disjointness = uniqueness
of the induced `α` (from `t` surjective).  **No poset induction, no Möbius, no per-`f` marked
kernels.**

```
|Sur(Γ, G)|  =  Σ_{α : Ttame ↠ G/O₂(G)}  e^β_Γ(𝒴_G, F_α)          (Lemma 10.1, per source)
e^β_{Γ_A}(𝒴_G, F_α) = e^β_{G_ℚ₂}(𝒴_G, F_α)                        (thm_4_2 at E = 0, per α)
⟹  |Sur(Γ_A, G)| = |Sur(G_ℚ₂, G)|                                  (eq. (154))
⟹  contSurjCount G = admissibleCount G                             (+ prop_2_3 ✓)
```

**All of P-18a–d are unblocked today**; only P-18e's final axiom trace rides the sorried
`thm_4_2` (P-17i) — and per house convention it consumes it directly (the sorry is allowlisted
upstream in `SectionNine`), so P-18 can run to completion in parallel with P-17i/P-16d6e.

---

## 1. Paper content (pp. 47–48, read 2026-07-07)

**Lemma 10.1 (Exhaustion by tame boundary frames).**  *Let `G` be finite and put `L = O₂(G)`.
For either source `Γ`, every epimorphism `f : Γ ↠ G` determines a unique tame boundary frame
`T_tame ↠ G/L`.  Conversely, with decoration `E = 0`, a boundary-framed epimorphism to `G` with a
fixed tame frame is exactly an ordinary epimorphism to `G` inducing that frame.  Distinct tame
frames give disjoint sets of epimorphisms.*

Proof ingredients (paper): the characteristic marked wild subgroup maps into `O₂(G) = L` (image
of the pro-2 wild kernel is a normal 2-subgroup); Prop 3.2 makes the induced quotient map a tame
frame; with `E = 0` the boundary-framed condition records only the induced tame quotient map and
the marked 2-kernel; uniqueness of the induced map gives disjointness.

**Assembly (p. 48):** partition `Sur(Γ, G)` by Lemma 10.1, apply Theorem 4.2 per frame (`E = 0`),
sum over the finite frame set, use Prop 2.3 → eq. (154) → (with Lemma 2.5, already wired in
`main_presentation` ✓) Theorem 1.2.

---

## 2. The Lean encoding

New file **`GQ2/SectionTen.lean`** (leaf; imports `GQ2.SectionNine` for `thm_4_2`,
`GQ2.BoundaryFrame`, `GQ2.Statement`-adjacent pieces as needed — check for cycles: `Statement`
imports little; `main_surjection_count` lives in `Statement.lean`, so either SectionTen imports
Statement and proves a `main_surjection_count'` that a one-line splice transplants, or —
cleaner — `Statement.lean` gains `import GQ2.SectionTen` and the sorry is filled by
`SectionTen.eq_154 … |>.symm.trans (prop_2_3 …)`-style.  **P-18a decides** (watch: `GQ2.lean`
import order, and `Prop23`/`Statement` cycle risk).

* **`E₀` (the trivial decoration).**  `E = 0` encoded as a trivial finite `CommGroup` with
  discrete topology.  Candidates: `PUnit` (Mathlib instances: `CommGroup`, unique topology,
  `DiscreteTopology` via subsingleton) or `Multiplicative (ZMod 1)`.  P-18a picks; `hE2` is
  `fun e => Subsingleton.elim _ _`-trivial, `psiBar := 1`.

* **`twoCore G : Subgroup G`** (the 2-core `O₂(G)`, finite `G`) — **not in Mathlib** (no `pCore`).
  Define as the sSup of normal 2-subgroups; three lemmas:
  - `twoCore_normal : (twoCore G).Normal` (sSup of normals is normal);
  - `twoCore_isPGroup : IsPGroup 2 (twoCore G)` — the only real content: the join of two normal
    2-subgroups is a normal 2-subgroup (second iso `Subgroup.quotientInfEquivProdNormalQuotient`
    + `IsPGroup` closure under extension via `Subgroup.card_eq_card_quotient_mul_card_subgroup`,
    or a direct card-divisibility argument on `N₁N₂ = N₁ ⊔ N₂` from `Subgroup.mul_normal`), then
    finite induction up the sSup (finitely many subgroups; `Finset.sup` route);
  - `le_twoCore : N.Normal → IsPGroup 2 N → N ≤ twoCore G` (`le_sSup`).
  Plus the **pro-2 image bridge**: `IsProP 2 K → (f : continuous hom, finite discrete codomain) →
  IsPGroup 2 (image of K)` — from `IsProP`'s definition (`GQ2/MaxProP.lean:47`; the repo already
  extracts `IsPGroup` on finite quotients from `IsProP`, cf. `piBd_isProP` usage in
  `BoundaryConstruction.lean:182` — reuse that shape; the image is a finite continuous quotient
  of `K`).

* **`tameTarget G : MarkedTarget (G ⧸ twoCore G) E₀ G`** — fields: `LY := twoCore G`,
  `normal`/`isPGroup_two` from the 2-core lemmas, `piY := QuotientGroup.mk' (twoCore G)`,
  `piY_surjective := mk'_surjective`, `ker_piY := QuotientGroup.ker_mk' `, `thetaY := 1`.
  (Verified against `MarkedTarget`'s actual fields, `BoundaryFrame.lean`.)

* **`tameFrame (α) : BoundaryFrame (G ⧸ twoCore G) E₀`** — `alpha := α`, `alpha_surjective`,
  `exponent_two := trivial`, `psiBar := 1`.  Note `BoundaryFrame.frameMap` is **definitionally**
  `x ↦ (α x.1, ψ̄ x.2)`, so with `E₀` the `IsBoundaryLift` condition is literally
  `∀ γ, π(f γ) = α ((b γ).1)` — the paper's fixed-frame condition, nothing to unfold away.

* **The frame index.**  `TameFrames G := {α : ContinuousMonoidHom Ttame (G ⧸ twoCore G) //
  Function.Surjective α}`.  Finiteness: `Ttame` is topologically 2-generated
  (`SectionThree.gen_ttame_quotient`, `GQ2/Prop32.lean:134`) ⟹ continuous homs into a finite
  discrete group form a finite type (the repo's t.f.g.-hom-finiteness machinery,
  `FinitelyGenerated`/`Reconstruction`/`finite_boundaryLifts` pattern).

* **`lemma_10_1` (Γ-generic).**  Stated over `(b : ContinuousMonoidHom Γ ↥boundarySubgroup)`
  with hypotheses `htame : Function.Surjective (fun γ => ((b γ : Ttame × PiBd)).1)` and
  `hwild : IsProP 2 (ker (pr₁ ∘ b))`:
  ```
  lemma_10_1 : ContSurj Γ G ≃ (α : TameFrames G) × BoundaryLifts b (tameFrame α) (tameTarget G)
  ```
  - forward: `f ↦ ⟨induced α_f, f, framing⟩` — `α_f` descends `π ∘ f` through `pr₁ ∘ b` because
    `f(ker(pr₁∘b)) ≤ twoCore G` (pro-2 image bridge + `Subgroup.Normal.map` under surjective `f` +
    `le_twoCore`); continuity of `α_f` via the quotient (discrete codomain); surjectivity of
    `α_f` from `f`, `π` surjective.
  - backward: forget.  Uniqueness/disjointness: `α∘(pr₁∘b) = α'∘(pr₁∘b)` + `htame` ⟹ `α = α'`.
  Count form (needs `hfg` for cell finiteness via `finite_boundaryLifts` + index `Fintype`):
  ```
  card_contSurj_eq : Nat.card (ContSurj Γ G) = ∑ᶠ α : TameFrames G,
      exactImageCount b (tameFrame α) (tameTarget G)
  ```
  (`Nat.card` of the sigma + `Nat.card_sigma`.)

* **`eq_154`** `(G) [instances] : Nat.card (ContSurj GammaA G) = Nat.card (ContSurj AbsGalQ2 G)`
  — pick `B₀ := prop_3_14_proved.some` (or `boundaryMapsWitness` directly,
  `GQ2/BoundaryMapsWitness.lean:467`), apply `card_contSurj_eq` for `b := B₀.bA` and `b := B₀.bF`
  (per-source hypotheses from P-18d), and `thm_4_2 B₀ (tameFrame α) (tameTarget G) hE2` per `α`.
  Note `pr₁ ∘ B₀.bA = B₀.tameA` and `pr₁ ∘ B₀.bF = B₀.tameF` **definitionally**
  (`bA_apply_coe`/`bF_apply_coe`).

* **`main_surjection_count`** := `eq_154 G ▸ prop_2_3` (contSurjCount `= |Sur(G_ℚ₂,G)|`
  definitionally, `Statement.lean:32`; `prop_2_3 : Nat.card (ContSurj GammaA G) =
  admissibleCount G`, `GQ2/Prop23.lean:207` ✓ — exact shape match).  Statement.lean's single
  sorry (line 49) filled ⟹ **`Statement.lean` comes OFF the `SORRY_ALLOWLIST`** (P-18e, same
  commit).

---

## 3. Verified interface inventory (all checked against source, 2026-07-07)

| fact | where | status |
|---|---|---|
| `MarkedTarget` fields (`LY` normal 2-group, `piY` surj, `ker_piY`, `thetaY`) | `BoundaryFrame.lean` | ✓ read |
| `BoundaryFrame` fields (`alpha`+surj, `exponent_two`, `psiBar`); `frameMap = (α∘pr₁, ψ̄∘pr₂)` **by definition** | `BoundaryFrame.lean` | ✓ read |
| `BoundaryLifts b F T = {f : ContSurj Γ Y // ∀ γ, (π(fγ), θ(fγ)) = frameMap (b γ)}`; `exactImageCount = Nat.card` | `BoundaryFrame.lean:350/358` | ✓ read |
| `finite_boundaryLifts` (from `hfg`) | `BoundaryFrame.lean` | ✓ |
| `BoundaryMaps` **F-side clauses: `tameF_surjective`, `wild_isProP : IsProP 2 (ker tameF)`, `wild_isMax`** | `BoundaryFrame.lean:383+` | ✓ — the local Lemma-10.1 hypotheses are ALREADY BUNDLED |
| `BoundaryMaps` A-side: `tameA` pinned on generators (σ↦tameSigma, τ↦tameTau, x₀,x₁↦1) + `surjA`; **no `tameA_surjective`, no A-side `wild_isProP`** | same | ⚠ P-18d |
| `prop_3_14_proved : Nonempty BoundaryMaps`; explicit `boundaryMapsWitness` | `BoundaryMapsWitness.lean:467/505` | ✓ (P-25) |
| `isProP_wildCore : IsProP 2 wildCore` (Γ_A wild pair's closed normal closure) | `AdmissibleLimit.lean:374` (P-04) | ✓ exists |
| witness `tameA := phiA` — ker(phiA) ↔ `wildCore` identification | `BoundaryMapsWitness.lean:468` + `BoundaryConstruction` | **P-18d dig** |
| `IsProP` def | `MaxProP.lean:47` | ✓ |
| `Ttame` top. 2-generated | `Prop32.lean:134` `gen_ttame_quotient` | ✓ |
| `thm_4_2 (B) (F) (T) (hE2)` : per-target source equality | `SectionNine.lean:1708` (sorried, P-17i) | consumption point (P-18e only) |
| `prop_2_3` | `Prop23.lean:207` | ✓ (P-05) |
| `Statement.lean` sorry count | line 49 only | ✓ single |
| `main_presentation` (schematic) | `Statement.lean:75` | ✓ proved — P-19 needs only `main_surjection_count` |

---

## 4. Ticket split (board rows P-18a–e)

* **P-18a (F, ⭐⭐) — design + statements.**  `docs/section10-extraction.md` (deviations ledger:
  the sigma-equiv encoding of "unique frame"; `E₀` choice; `twoCore` as sSup; the hypothesis-form
  Γ-generic 10.1) + `GQ2/SectionTen.lean` skeleton: `E₀`, `twoCore` def + **sorried** lemmas,
  `tameTarget`/`tameFrame`/`TameFrames`, **sorried** `lemma_10_1` + `card_contSurj_eq` + `eq_154`;
  `SORRY_ALLOWLIST += SectionTen.lean` (same commit).  Also decides the `Statement.lean` splice
  direction (import order).
* **P-18b (O, ⭐⭐) — the 2-core layer.**  Prove `twoCore_normal`/`twoCore_isPGroup`/`le_twoCore`
  + the pro-2 image bridge.  Pure finite group theory, zero arithmetic; parallel-friendly.
* **P-18c (O, ⭐⭐) — Γ-generic Lemma 10.1.**  The equiv + count form over `(b, htame, hwild)`;
  `TameFrames` finiteness (Ttame t.f.g.); `Nat.card_sigma` assembly.  Fiddliest bits: continuity
  of the descended `α_f` and the `Subtype`/`ContSurj` plumbing.
* **P-18d (O, ⭐⭐) — per-source hypotheses.**  **F-side: FREE** (`tameF_surjective` +
  `wild_isProP` are `BoundaryMaps` clauses; `pr₁∘bF = tameF` is `rfl`).  **A-side (the ⚠ item)**:
  (i) `tameA_surjective` — from the generator clauses (`tameA_sigma`/`tameA_tau`) +
  `gen_ttame_quotient` (image contains a topologically generating pair; closed range by
  compactness); (ii) `IsProP 2 (ker tameA)` — dig the witness construction (`phiA`,
  `BoundaryConstruction`): if `phiA` descends through `Γ_A/wildCore ≅ Ttame` then
  `ker = wildCore` and `isProP_wildCore` closes it.  **Fallback (owner sign-off)**: amend
  `BoundaryMaps` with the symmetric A-side clauses (`tameA_surjective`, `wildA_isProP`) —
  discharged in `BoundaryMapsWitness` from the same material; benign but co-owned.
  **Cross-benefit**: (i) also discharges the `hheadA`/`hheadF` hypotheses of
  `prop_8_9_of`/`prop_8_9_aux` (head-surjectivity = `α` surj ∘ tame surj) — coordinate with
  **P-16d6e**, which needs exactly these.
* **P-18e (O, ⭐) — assembly + splice.**  `eq_154` (consumes `thm_4_2` directly — sorryAx flows
  from the allowlisted `SectionNine` sorry until P-17i lands, then the trace auto-cleans);
  `main_surjection_count` filled in `Statement.lean`; **Statement.lean off the allowlist**;
  `GQ2.lean` import wiring; board note for P-19 (which is then a ~15-line instantiation:
  `main_presentation GammaA gammaA_topologicallyFinitelyGenerated
  absGalQ2_isTopologicallyFinitelyGenerated (fun G _ _ _ _ => prop_2_3)`).

**Dependency order**: a → {b ∥ c ∥ d} → e.  (c formally deps a+b's statements; b's sorried
statements land in a, proofs in b.)  **a–d are unblocked NOW**; e is writable immediately too,
with its axiom trace carrying `sorryAx` through `thm_4_2` until P-17i.

---

## 5. Expected axiom trace at close

`main_surjection_count` = std-3 ∪ (witness: B3c/B5/B8/B10′ via `boundaryMapsWitness`) ∪
(`thm_4_2`: B1 + B3c/B6/B7/B7′/B8/B9 transitively, per App. D) ∪ (`prop_2_3`: ∅ beyond std-3)
— plus `sorryAx` via `thm_4_2` **until P-17i closes**, then automatically clean.  Audit at
P-18e close; the B-set should match the App. D row for Theorem 1.2.

## 6. Risks / deviations (for P-20)

1. **A-side pro-2 kernel** (P-18d(ii)) — the only genuine unknown; two routes, one needs owner
   sign-off.  Time-box the dig before proposing the amendment.
2. `twoCore` join-closure (P-18b) — elementary but Mathlib-gap; if
   `Subgroup.quotientInfEquivProdNormalQuotient` friction appears, the direct card argument on
   `Subgroup.mul_normal` is the fallback.
3. Import-cycle check for the `Statement.lean` splice (P-18a) — `Statement` currently sits early
   in the import order; `SectionTen` imports `SectionNine` (heavy).  If `Statement ← SectionTen`
   creates a cycle with `Prop23`/`Reconstruction`, transplant the proof instead (comment-pointer
   pattern, P-08/P-10 precedent).
4. The paper's "unique tame boundary frame" is encoded as the sigma-equivalence — flagged as a
   faithful-encoding deviation (no separate uniqueness statement).
