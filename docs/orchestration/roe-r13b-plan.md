# R13b validated execution plan (research pass, 2026-07-24 night)

Produced by the first R13b dispatch (research-only — the agent lacked write tools; the
math is validated). Executor: follow this plan directly. Worktree `~/claude/gq2-roe`,
branch `roe`; R8 has SINCE COMMITTED (e045a1c), so the R8-gating below is now dischargeable;
tip at memo-writing time f713db8.

## The critical de-risk (validated green via `lean_run_code`, reuse verbatim)

The ticket funnels through computing `drWord`'s fibre in the generic
`WordCoh2.CentExt(φ_i⊗φ_j)` over 𝔽₂³. This compiles green, no timeout, and reproduces the
paper's Gram matrix exactly:

```lean
import GQ2.WordCoh2
import GQ2.Roe.DRPresentation
open GQ2 GQ2.WordCoh2
abbrev L3 := Multiplicative (Fin 3 → ZMod 2)
def cc (i j : Fin 3) : TwoCocycle L3 where
  κ a b := (Multiplicative.toAdd a i) * (Multiplicative.toAdd b j)
  norm := by simp
  cocyc a b c := by
    show (Multiplicative.toAdd a i)*(Multiplicative.toAdd b j)
        + (Multiplicative.toAdd (a*b) i)*(Multiplicative.toAdd c j)
      = (Multiplicative.toAdd a i)*(Multiplicative.toAdd (b*c) j)
        + (Multiplicative.toAdd b i)*(Multiplicative.toAdd c j)
    rw [show Multiplicative.toAdd (a*b) = Multiplicative.toAdd a + Multiplicative.toAdd b from rfl,
        show Multiplicative.toAdd (b*c) = Multiplicative.toAdd b + Multiplicative.toAdd c from rfl]
    simp only [Pi.add_apply]; ring
def lg (i j k : Fin 3) : CentExt (cc i j) := ((Multiplicative.ofAdd (Pi.single k 1) : L3), (0:ZMod 2))
def gram (i j : Fin 3) : ZMod 2 := (drWord (lg i j 0) (lg i j 1) (lg i j 2)).2
-- ALL NINE PASS by `decide`:  gram 0 1 = 1, gram 1 0 = 1, gram 2 2 = 1, rest = 0
```

Result = `[[0,1,0],[1,0,0],[0,0,1]]` in (s,x,y) order, including the Bockstein diagonals
(ss = 0, xx = 0, yy = 1).

## Gating correction

The obstruction/bridge route computes ss/xx by `decide` — NOT R8-gated. The only R8-gated
sorry is `demushkinQ_DR` (1-liner `:= GQ2.demushkinQ_DR_eq_two`), and R8 is now committed.
**End-state target: DRDemushkin 13 → 0 sorries.**

## Sorry ledger and routes

| sorry | route |
|---|---|
| `card_H2_DR = 2` | ≤2 from `obsH2_DR` injective; ≥2 from `drCup_yy ≠ 0` |
| `drCup_sx, drCup_xs, drCup_yy` (≠0) | `obsDR(cup) = gram = 1`; needs only the well-defined obs hom |
| `drCup_ss,sy,xx,xy,ys,yx` (=0) | `obsDR(cup) = gram = 0` + obs injective |
| `nondegen_left/right` | Gram linear algebra via `drH1_bijective` + entries (det = 1 over 𝔽₂) |
| `demushkinQ_DR` | `:= GQ2.demushkinQ_DR_eq_two` (R8, committed) |

## Architecture (single obstruction hom)

`obsH2_DR : H²(D_R,𝔽₂) → 𝔽₂`. Easy half (additive, kills B²) → the three ≠0 entries +
lower bound. Hard half (`ker ⊆ B²`, i.e. injective) → `#H² ≤ 2`, the six =0 entries,
nondegen. Single relator ⇒ obstruction lands in 𝔽₂ directly (no Γ_A "balance" condition).
Key simplification: `drLiftHom` (DRPresentation.lean:185) is a ready-made splitting-section
constructor, replacing WordCoh2's `NA_le_ker_shiftLift`/`sectionHom`.

## Reusable infrastructure (cite, don't re-prove)

- Generic in `L`, reuse as-is (GQ2/WordCoh2.lean): `TwoCocycle` (L37), `CentExt` +
  Group/proj/incl/`base_eq_one_iff` (L67–145), `TwoCocycle.comap` (L563), `zeroCocycle`
  (L772), `coboundaryCocycle`+`Psi` (L803/815), `FiberProd`+additivity (L625–742),
  `TwoCocycle.ext` (L1153).
- Generic in the group: `exists_openNormalSubgroup_factor_two` (WordCoh2.lean:955) — the
  profinite factoring core.
- Clone for F₃/`ker drPi` levels (mechanical): `exists_twoCocycle_factor` /
  `exists_oneCochain_factor` (L1011/1072), `LevelFactor`+`obs_congr` (L1160–1318),
  `obs_ker_le`/`obs_B2_eq_zero`/`obsH2_injective` (L1361–1450).
- ContCoh/cup: `cup11_mk_mk` is `rfl` (CupProduct.lean:183) —
  `cup(drH1 u, drH1 v) = H2mk⟨(g,h) ↦ z_u(g)·z_v(h)⟩`; `trivialCupPairing`/`IsDemushkin`
  (Demushkin.lean:95/109); worked ℤ/2 micro-template with a nonzero ContCoh cup square:
  Demushkin.lean:230–453 (`wCyclicTwo`, `h2CyclicTwoEval`).
- D_R side: `drLiftHom`/`drWord`/`dr_relation` (DRPresentation.lean); `drH1_bijective`,
  `card_H1_DR`, `drPi` (surj/cont), `dr_hom_ext` (R8), private helpers
  (DRDemushkin.lean:137–265).

## File plan

- NEW `GQ2/Roe/DRWordCoh.lean` (~800 ln): generic-algebra reuse; `drRelZ`/shift/comap/
  additivity; factoring at F₃/`ker drPi`; `LevelFactor`+`obs_congr`; `obsDR` (kills B²);
  `ker ⊆ B²` via the `drLiftHom` section; `obsH2_DR` injective; `#H² ≤ 2`.
- NEW `GQ2/Roe/DRH2.lean` (~300 ln, optional split): `D_R ↠ 𝔽₂³`, `w_{u,v}` factors,
  `obsDR(cup u v) = gram` (the validated `decide`), `card_H2_DR`.
- FILLS `GQ2/Roe/DRDemushkin.lean`; `GQ2.lean` gains `import GQ2.Roe.DRWordCoh` (+`DRH2`)
  before `DRDemushkin`.

## Hard seams (3 honest cycles each, then commit-green + report)

1. `obs_congr` well-definedness across common refinements.
2. Coboundary extraction from the `drLiftHom` section through the maxProP layer
   (`DR = maxProPQuotient 2 DRFull`, vs WordCoh2's `GA = F₄/NA` where pro-2 is folded
   into `NA`).
3. Matching the factored `w_{u,v}` cocycle to `cc` at the 𝔽₂³ level (needs the explicit
   `D_R ↠ 𝔽₂³` from the dual-basis characters).

The easy half + all nine Gram values + lower bound are low-risk (bridge already green).
The upper-bound injectivity is the main risk; there is no abstract "one-relator ⇒ #H² ≤ p"
shortcut in-repo (that is exactly why WordCoh2 exists).
