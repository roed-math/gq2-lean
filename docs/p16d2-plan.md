# P-16d2 — R-stage obstruction module: reduction (landed) + construction route (escalation)

**Ticket**: P-16d2 (`docs/p16-ticket-split.md`, P-16d item 1 "sharpened residue").  Build the
`(W, o, e, hmB, hobs, hfib)` datum that `GQ2.SectionEight.stageR136_of` consumes to prove the (136)
display of Prop 8.9, for the concrete R-stage.  **Deps** P-13f (`prop_5_15`, landed) + `prop_5_16`
(landed); **Ax** B6, B7.  **Owner** Opus, 2026-07-05.

## Status: reduction landed std-3; datum-construction escalated

* ✅ **Reduction landed** — `GQ2/RStageObstruction.lean`, `stageR136_ofObstruction`, **std-3,
  sorry-free**.  It repackages `stageR136_of`'s `W`/`o`/`e` interface into the natural obstruction
  shape and discharges the double-dual bookkeeping, so a caller need only supply the obstruction as
  a **linear functional on the scalar-character space**:

  ```
  obs : BoundaryLifts b F RF.TB → Module.Dual (ZMod 2) D_Rmod        (D_Rmod ≃ RF.DR)
  hmB  : ∀ λ ≠ 0,  m_{Γ,λ}(B) = #{ g // obs g λ = 0 }
  hobs : ∀ g,      obs g = 0  ↔  g lifts to Y
  hfib : ∀ g,      obs g = 0  →  #(fibre of liftB over g) = z_R
  ⟹  (136):  |D_R|·e_Γ(Y) = z_R · Σ_λ (2 m_{Γ,λ}(B) − e_Γ(B)).
  ```

  Internally `W := D_Rmodᵛ`, `o := obs`, and `e : D_R ≃ Wᵛ = D_Rmodᵛᵛ` is the finite-dimensional
  double-dual `Module.evalEquiv`; `hmB`/`hobs`/`hfib` pass through verbatim.  This is the reusable
  "obstruction module" object the ticket names, and it is the interface the concrete witness will
  target.

* 🔨 **Option A underway** (user-approved 2026-07-05) — `GQ2/RStageObstructionBuild.lean`, std-3:
  the compat structure `RCoverData RF` (the `coverMap_λ : Y →* (scalarCover λ).cover` family with
  `p_λ ∘ coverMap_λ = π_B`) is defined, and the **easy `hobs` direction**
  `lifts_scalarCover_of_liftB` (lifts-to-`Y` ⟹ lifts-through-every-`p_λ`) is proved.  Kept
  self-contained (no edit to the co-owned `Enrichment`; foldable in later).  **Remaining** = the
  obstruction-theory core (steps 2–5 below): the obstruction map `obs` + its linearity, the hard
  separation, and the `z_R` torsor count — a multi-session build needing a new twisted
  `Z¹(Γ,R)` / `H²(Γ,R)` cochain layer for the `R`-extension (and one more `RCoverData` field, the
  `D_R ≃ (R^∨)^C` functional link, for `obs`/`toDR`).  The reduction
  `stageR136_ofObstruction` is the sink these feed.

## The gap: the scalar covers are not linked to the radical extension

`RecursionFrame.scalarCover : (l : DR) → l ≠ 0 → CentralCover YB` stores each `p_λ : B_λ ↠ B` as an
**abstract central `𝔽₂`-cover of `B`**.  Its docstring reads "the pushout `K_λ = K/ker λ`, realized
as `Y/ker λ ↠ Y/R`" — but that is *documentation*, not a field: nothing in the frame (or in
`Enrichment`, which adds only the per-`λ` square forms `q_λ`/`q̄_λ` and factor sets `dat_λ`) exposes
a map relating `p_λ` to the **single** radical extension `Y ↠ B = Y/R` (`ker π_B = R = Φ(K)`).

Two properties of `obs` depend on exactly that link and are **not derivable without it**:

* **(Lin) — linearity of the obstruction.**  We need `obs g : D_R → 𝔽₂` (`λ ↦ [g lifts through
  p_λ]`, as an element of `D_Rᵛ`) to be `𝔽₂`-linear.  This holds because `obs g λ = λ_*(Obs_R(g))`,
  the pushforward along `λ : R → 𝔽₂` of the *one* radical-extension obstruction
  `Obs_R(g) ∈ H²(Γ, R)`, and `λ ↦ λ_*` is linear (functoriality of `H²` in the coefficient
  module).  If the `p_λ` are unrelated covers, there is no common `Obs_R(g)` and no reason for
  linearity.
* **(Sep) — the `hobs` separation.**  `obs g = 0 ⟺ ∀ λ ∈ D_R, g` lifts through `p_λ`, and we need
  this `⟺ g` lifts to `Y`.  With the pushout link, "lifts through every `p_λ`" ⟺ "`Obs_R(g)`
  dies against every `λ ∈ (R^∨)^C`", and the Frattini structure (`R = Φ(K)`,
  `eq_top_of_map_frattini_quotient_top`) is what forces this to be lifting to `Y`.  Without the
  link the two sides are unrelated.

Per the project rule ("if a proof needs an unstated input, that is a **design escalation** — flag
on the board, discuss; never an axiom"), this is flagged rather than hacked.

## Two ways to close it (recommend the frame extension)

**Option A — extend the frame with the pushout compatibility (recommended).**  Add to
`RecursionFrame` (or, less invasively, to `Enrichment`, keeping the bare frame untouched) a
compatible **realization family**

```
cover_map : (l : DR) → (h : l ≠ 0) → Y →* (scalarCover l h).cover      -- q_λ : Y ↠ B_λ
cover_map_lifts_piB : (scalarCover l h).p ∘ cover_map l h = piB          -- p_λ ∘ q_λ = π_B
cover_map_ker : (cover_map l h).ker = (ker λ  as a subgroup of R ≤ Y)    -- kernel is ker λ
```

i.e. the datum that `p_λ` really is `Y/ker λ ↠ Y/R`.  From it, `Obs_R(g) ∈ H²(Γ,R)` is the single
radical obstruction and `obs g λ = λ_*(Obs_R(g))` gives (Lin); (Sep) follows from
`⋂_{λ∈(R^∨)^C} ker λ` and the Frattini surjectivity.  **This is a co-owned `SectionEight.lean` edit
to a structure — needs a fleet-lead / owner sign-off** (the `Enrichment`-extension variant is the
lighter touch, mirroring how P-16d1 added `Enrichment` without editing the bare frame).

**Option B — build the witness only for the concrete `𝒴`-frame (P-16d5/d6).**  There the covers
*are* `Y/ker λ` by construction, so the compatibility holds definitionally and `obs`/(Lin)/(Sep)
are provable in place; P-16d2 then reduces to "provide the concrete `obs` for `𝒴`" and folds into
the witness.  Cleaner for correctness, but couples P-16d2 to d5/d6 (loses the reusable abstraction).

## Construction route (once the compatibility is available)

*De-risked precondition*: `R = Φ(K)` **is elementary abelian** (and central in `K`, `K⁴ = 1`) by
`GQ2.SectionSeven.lemma_7_2` (proved, std-3): its middle conjunct is `∀ r ∈ B.R, r*r = 1`.  So
`R^∨`, `D_R = (R^∨)^C`, and `z_R = 2^{2·dim R + dim D_R} = |R|²·|D_R|` are all well-founded — the
obstruction/duality picture does not rest on an unverified exponent hypothesis.

1. **`W`, `e`, `he0`** — done, generic: `stageR136_ofObstruction` (this file).  `D_Rmod` = `D_R`
   given `𝔽₂`-module structure (it is `(R^∨)^C`, naturally a subspace of `R^∨`, elementary abelian
   by `lemma_7_2`); `W = D_Rmodᵛ`.
2. **`Obs_R : BoundaryLifts(B) → H²(Γ, R)`** — the radical-extension obstruction, per lift `g`, via
   the pushout family (Option A/B).  Per-`λ`, `λ_*(Obs_R(g)) ∈ H²(Γ,𝔽₂)` is exactly the
   `GQ2.SectionEight.CentralObstruction.ob` of the central cover `p_λ`
   (`central_iff_ob_eq_zero`), so `obs g λ := ob_{p_λ}(g)` and **(Lin)** is `ob`-functoriality in
   `λ` (the covers share the lift family through `cover_map`).
3. **`hmB`** — near-definitional: `m_{Γ,λ}(B)` (`RecursionFrame.mB`) *is* `#{g // g lifts through
   p_λ}`, and `obs g λ = 0 ⟺ g` lifts through `p_λ` by `central_iff_ob_eq_zero`.
4. **`hobs`** — (Sep): `obs g = 0 ⟺ ∀λ, ob_{p_λ}(g)=0 ⟺ Obs_R(g)=0 ⟺ g` lifts to `Y`; the last
   `⟺` is the pushout universal property + the Frattini surjectivity
   `GQ2.eq_top_of_map_frattini_quotient_top` (a lift's image is automatically all of `Y`).
5. **`hfib`** — the `z_R` torsor count, **this is where B6/B7 enter**.  The fibre of `liftB` over a
   liftable `g` is a torsor under the twisted cocycles `Z¹(Γ, R)` (the lift-difference cocycle;
   `fiberLiftEquiv` is the rank-1 `𝔽₂` prototype).  Its size is the **5.15/5.16 numeric**:
   `#Z¹(Γ, R) = |R|² · #(ElemDual R)^C` — exactly
   * **local** (`Γ = G_ℚ₂`): `GQ2.LocalLiftingDuality.card_Z1_eq` / `prop_5_16_bundle` clause 2,
   * **candidate** (`Γ = Γ_A`): `prop_5_15`'s `IsSelfDual R` clause 2
     (`#Z1w = |R|² · #(ElemDual R)^C`),

   and `#(ElemDual R)^C = |D_R|` is `card_DR` (the `C`-invariant `λ`-kernels ↔ `(R^∨)^C`).  Hence
   the fibre size is `|R|² · |D_R| = z_R` (`RecursionFrame.zR`) on the nose.  So **`hfib` is
   design-independent modulo the fibre-is-a-`Z¹`-torsor identification** — and that identification
   uses only the *honest* extension `Y ↠ B` (`RF.piB`, kernel `R`), **not** the per-`λ` scalar
   covers, so it is not blocked by the compatibility gap above (only `obs`/`hmB`/`hobs` are).  It
   does still need a twisted-`Z¹(Γ,R)`-torsor layer for `R`-coefficients (the repo has the rank-1
   `𝔽₂` prototype `fiberLiftEquiv`; general-`R` is new infra).  Note `R ≤ ker π_Y = L_Y`
   (`K ≤ P ≤ L_Y`, so `Φ(K) ≤ K ≤ L_Y`), so the `π_Y`-framing is `R`-twist-invariant; the
   `θ_Y`-framing interaction is the one point to check.

## Files / handoff

* `GQ2/RStageObstruction.lean` — the reduction (landed, std-3).  Not yet imported by `GQ2.lean`
  (leaf awaiting the P-16d6 splice, which will `import GQ2.RStageObstruction`); the guard scans it
  textually and it is violation-free.
* Blocker owner: whoever holds the `RecursionFrame`/`Enrichment` structure (co-owned
  `SectionEight.lean`).  Recommended: add the `cover_map` compatibility to `Enrichment`
  (light touch), then discharge steps 2–5 in a follow-up `RStageObstruction`-consumer, feeding
  `stageR136_ofObstruction`.
