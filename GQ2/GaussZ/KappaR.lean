/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GaussZ.FinalGammaA
import GQ2.Roe.DualityAssembly
import GQ2.WordCoh2R

/-!
# The κ⁰ ledger for the `Γ_R` Gauss residue

The `Γ_R` twin of `GQ2/GaussZ/FinalGammaA/Kappa.lean` (obligation ii.7, supply layer): the
`x₁`-supported section of `H¹_{R,word}` and the split and ramified *Roe* wild-value
calculations in the concrete `κ⁰`-extension `CentExt (kappa0Cocycle dat hdat)`.

**The gauge swap** (`docs/orchestration/roe-r31-survey-gaussz.md`): the `Γ_A` normal form is
`x₀`-supported (`![0,0,c,0]`, slot 2; `Z¹_w`-shape `x 1 = x 3 = 0`), while the `Γ_R` normal
form is `x₁`-supported (`![0,0,0,d]`, slot 3; `Z¹_{R}`-shape `x 1 = 0 ∧ x 2 = 0`,
`GQ2/Roe/NormalForms.lean`).  Accordingly the structural pack here zeroes the `x₀`-slot
(`hx0v`) where `Γ_A` zeroed the `x₁`-slot.

**The word collapse.**  The Roe wild relator `r_R = (x₀^σ)⁻¹ · a · x₁² · c` (note
eq. (1.2) ⟦eq:relators⟧) is *much* softer than `Γ_A`'s `r_A` on the `x₁`-supported gauge:
with `x₀ ↦ 1` in the extension (zero `V`-part + trivial head), the first factor dies, the
`ω₂`-word `a = (x₀⁻³τ)^{ω₂}` collapses to `powOmega2 τ = 1` (`τ` of odd tame-inertia
order), and what remains is `x₁² · [x₁, x₁^{σ₂}]` — the diagonal `q(d)` plus the `V`-slice
commutator polar `b_q(d, σ₂⁻¹d)`.  There is **no `d₀`/`h₀` telescope**: the ramified
evaluation `liftMark_kappa0_wildValueR_fib_ramified` is the *unconditional* Wall shape
`q(d) + b_q(d, σ₂⁻¹·d)` — exactly `FoxH.QZeroR` (`GQ2/Roe/Gauss.lean`, ⟦eq:QR⟧) — with no
ramified hypothesis at all (the `Γ_A` twin needed `htauf`/`hqg0`); the split evaluation is
the corollary killing the polar term by the split `σ₂`-triviality `hU`.

The generic toolkit (`sdSec`, `liftMark_kappa0_tameValue_fib`, `sdToWL`/`sdBaseMarking`/
`sdOffsets`, the `m`-calculus, `kappa0_cc_one`, `commP_fib_cc_one`, …) is **imported from
`GQ2/GaussZ/FinalGammaA/Kappa.lean` and reused verbatim**, never cloned; only the tame
first-component peel is restated at `relZPairR` (`relZPairR_kappa0_fst_eq_zero`, a
definitional retype of `liftMark_kappa0_tameValue_fib` — the tame relator is shared).

All std-3; no axioms, no sorries.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH WordCoh2 WordCoh2R QuadraticFp2

/-! ## The `x₁`-supported section of `H¹_{R,word}`  (generic marking level)

The note's "only `x₁` varies" gauge (Lemma 4.2's normal forms, ⟦lem:normalforms⟧), as a
bijective parametrization `V ≃ H¹_{R,word}`: membership and bijectivity fall out of the
banked shape characterizations (`lemma_5_13_split_R` / `lemma_5_13_ramified_R`,
`GQ2/Roe/NormalForms.lean`; `normalForm_of_shapes_R` / `x1Supported_mem_Z1wR_ramified`,
`GQ2/Roe/DualityAssembly.lean`).  Both regimes provide a unique `x₁`-supported normal form,
so one `∃!`-kernel serves both — unlike the `Γ_A` split case, whose surjectivity had to
normalize the `σ`-row by hand. -/

section X1Section

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **The `x₁`-supported tuples are Roe word cocycles** (split regime): immediate from the
`lemma_5_13_split_R` `Z¹_R`-shape (`x 1 = 0 ∧ x 2 = 0`).  No `σ₂`-tameness `hU` is needed
(one fewer hypothesis than `Γ_A`'s `x0Supported_mem_Z1w_split`): the Roe wild row carries no
`σ₂`-dependency. -/
theorem x1Supported_mem_Z1wR_split (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) (d : V) :
    x1Supported d ∈ Z1wR (A := V) t :=
  x1mem_of_Z1wRShape t (lemma_5_13_split_R t ht hw hV₂ hsimple hcore htau hVS).1 d

/-- The `H¹_{R,word}`-class equality criterion in `h1wMkR` vocabulary (`H1wR` is a
semireducible `def`, so the quotient lemmas do not elaborate against it directly — the
`GaussZLocal.H1mk_eq_iff` idiom, as for `Γ_A`'s `h1wMk_eq_iff`). -/
theorem h1wMkR_eq_iff {t : Marking C} [Finite V] (x y : ↥(Z1wR (A := V) t)) :
    h1wMkR t x = h1wMkR t y
      ↔ (x - y : ↥(Z1wR (A := V) t)).1 ∈ B1wR (A := V) t := by
  show (QuotientAddGroup.mk x
      : ↥(Z1wR (A := V) t) ⧸ (B1wR (A := V) t).addSubgroupOf (Z1wR (A := V) t))
    = QuotientAddGroup.mk y ↔ _
  exact QuotientAddGroup.eq_iff_sub_mem

/-- **The `∃!`-kernel of both section bijectivities**: given membership of the `x₁`-supported
tuples and a unique `x₁`-supported normal form for every Roe cocycle, the section
`v ↦ [x1Supported v]` is bijective.  Injectivity: two witnesses of the same unique `d`;
surjectivity: the normal-form witness of any representative. -/
private theorem x1Section_bijective_of_normalForm [Finite V] (t : Marking C)
    (hmem : ∀ d : V, x1Supported d ∈ Z1wR (A := V) t)
    (hnf : ∀ x ∈ Z1wR (A := V) t, ∃! d : V, x - x1Supported d ∈ B1wR (A := V) t) :
    Function.Bijective (fun v : V => h1wMkR t ⟨x1Supported v, hmem v⟩) := by
  constructor
  · -- injective: `v` and `v'` both witness the unique normal form of `x1Supported v`
    intro v v' hvv'
    have hsub : x1Supported v - x1Supported v' ∈ B1wR (A := V) t :=
      (h1wMkR_eq_iff _ _).mp hvv'
    obtain ⟨d, -, huniq⟩ := hnf (x1Supported v) (hmem v)
    have h1 : v = d := huniq v (by
      show x1Supported v - x1Supported v ∈ B1wR (A := V) t
      rw [sub_self]
      exact zero_mem _)
    have h2 : v' = d := huniq v' hsub
    exact h1.trans h2.symm
  · -- surjective: the normal-form witness of any representative
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z =>
      obtain ⟨d, hd, -⟩ := hnf z.1 z.2
      refine ⟨d, ?_⟩
      show h1wMkR t ⟨x1Supported d, hmem d⟩ = QuotientAddGroup.mk z
      rw [show (QuotientAddGroup.mk z
          : ↥(Z1wR (A := V) t) ⧸ (B1wR (A := V) t).addSubgroupOf (Z1wR (A := V) t))
        = h1wMkR t z from rfl,
        h1wMkR_eq_iff]
      show ((⟨x1Supported d, hmem d⟩ - z : ↥(Z1wR (A := V) t)) : Fin 4 → V)
        ∈ B1wR (A := V) t
      have hneg : ((⟨x1Supported d, hmem d⟩ - z : ↥(Z1wR (A := V) t)) : Fin 4 → V)
          = -(z.1 - x1Supported d) := by
        funext i
        show x1Supported d i - z.1 i = -(z.1 i - x1Supported d i)
        abel
      rw [hneg]
      exact neg_mem hd

/-- **The `x₁`-supported section of `H¹_{R,word}` is bijective** (split regime): the unique
normal form comes from the split shapes (`normalForm_of_shapes_R` at `lemma_5_13_split_R`).
`Γ_R` twin of `x0Section_bijective_split`, minus the `σ₂`-tameness `hU`. -/
theorem x1Section_bijective_split_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo C V) [Finite V]
    (hcore : t.Pro2Core) (htau : ∀ v : V, t.τ • v = v)
    (hVS : ∀ v : V, t.σ • v = v → v = 0) :
    Function.Bijective (fun v : V => h1wMkR t ⟨x1Supported v,
      x1Supported_mem_Z1wR_split t ht hw hV₂ hsimple hcore htau hVS v⟩) := by
  obtain ⟨hZ, hB⟩ := lemma_5_13_split_R (V := V) t ht hw hV₂ hsimple hcore htau hVS
  exact x1Section_bijective_of_normalForm t _ (normalForm_of_shapes_R t hZ hB hVS)

/-- **The `x₁`-supported section of `H¹_{R,word}` is bijective** (ramified regime): the unique
normal form is `lemma_5_13_ramified_R` directly.  `Γ_R` twin of
`x0Section_bijective_ramified`. -/
theorem x1Section_bijective_ramified_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (hV₂ : ∀ v : V, v + v = 0) [Finite V]
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0)
    (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    Function.Bijective (fun v : V => h1wMkR t ⟨x1Supported v,
      x1Supported_mem_Z1wR_ramified t ht hV₂ hx0 hx1 htau hTodd v⟩) :=
  x1Section_bijective_of_normalForm t _ (lemma_5_13_ramified_R t ht hw hV₂ hx0 hx1 htau hTodd)

end X1Section

/-! ## The κ⁰-ledger: the tame peel and the Roe wild values

The tame relator is **shared** with `Γ_A`, so the first-component peel is the imported
`liftMark_kappa0_tameValue_fib` retyped at `relZPairR`.  The Roe wild value collapses on the
`x₁`-supported structural pack with no telescope: see the file docstring. -/

section Kappa0LedgerR

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]
variable {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- The A-3 interface form at the **Roe** relator pair: the FIRST relator-`z` component
vanishes on base-slice `σ`/`τ`-slots (the tame relator is shared with `Γ_A`, so this is the
imported `liftMark_kappa0_tameValue_fib` on the nose). -/
theorem relZPairR_kappa0_fst_eq_zero [Finite C] [Finite V] (t : Marking (Sd C V))
    (hσ : t.σ.v = 0) (hτ : t.τ.v = 0) :
    (relZPairR t (kappa0Cocycle dat hdat)).1 = 0 :=
  liftMark_kappa0_tameValue_fib dat hdat t hσ hτ

/-- **The ramified Roe wild κ⁰-value is the Wall double — unconditionally** (note
⟦prop:quadratic⟧/⟦eq:QR⟧): with the `x₁`-supported structural pack (`σ`/`τ`/`x₀`-slots of
zero `V`-part, wild `cc`-slots `1`, `τ.cc` of odd order), the lifted Roe wild relator value
has fibre

  `q(x₁.v) + polar q x₁.v (σ₂⁻¹ • x₁.v)`   (`σ₂ = Marking.sigma2 (sdBaseMarking tS)`),

i.e. exactly `FoxH.QZeroR q σ₂ (x₁.v)`.  Unlike the `Γ_A` twin
(`liftMark_kappa0_wildValue_fib_ramified`) **no ramified hypothesis enters**: the word
`r_R = (x₀^σ)⁻¹ · a · x₁² · c` has no `d₀`/`h₀` telescope — `x₀` lifts to `1` (killing the
first factor and collapsing `a` to `powOmega2 τ = 1` by `hτodd`), `x₁²` deposits the diagonal
`q` (one `kappa0_cc_one` step), and `c = [x₁, x₁^{σ₂}]` is a `V`-slice commutator whose fibre
is the polar form (`commP_fib_cc_one`). -/
theorem liftMark_kappa0_wildValueR_fib_ramified [Finite C] [Finite V]
    (tS : Marking (Sd C V))
    (hσv : tS.σ.v = 0) (hτv : tS.τ.v = 0) (hx0v : tS.x₀.v = 0)
    (hx0cc : tS.x₀.cc = 1) (hx1cc : tS.x₁.cc = 1)
    (hV₂ : ∀ w : V, w + w = 0)
    (hτodd : Odd (orderOf tS.τ.cc)) :
    (liftMark tS (kappa0Cocycle dat hdat)).wildValueR.fib
      = q tS.x₁.v + polar q tS.x₁.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₁.v) := by
  classical
  set M := liftMark tS (kappa0Cocycle dat hdat) with hM
  -- generator slot forms
  have hMx0 : M.x₀ = 1 := CentExt.ext (Sd.ext hx0v hx0cc) rfl
  have hMτ : M.τ = sdSec dat hdat tS.τ.cc := CentExt.ext (Sd.ext hτv rfl) rfl
  have hMσ : M.σ = sdSec dat hdat tS.σ.cc := CentExt.ext (Sd.ext hσv rfl) rfl
  have hMx1bv : M.x₁.base.v = tS.x₁.v := rfl
  have hMx1bcc : M.x₁.base.cc = 1 := hx1cc
  -- the first factor dies: `(x₀^σ)⁻¹ = 1`
  have hconj : (conjP M.x₀ M.σ)⁻¹ = 1 := by
    rw [conjP, hMx0, mul_one, inv_mul_cancel, inv_one]
  -- the `ω₂`-word collapses: `a = (x₀⁻³τ)^{ω₂} = powOmega2 τ = 1` (odd order)
  have haR : M.aR = 1 := by
    show powOmega2 ((M.x₀ ^ 3)⁻¹ * M.τ) = 1
    rw [hMx0, one_pow, inv_one, one_mul, hMτ, ← powOmega2_map,
      powOmega2_eq_one_of_odd hτodd, map_one]
  -- the `x₁`-square: the diagonal `q`-cell
  have hx1sqcc : (M.x₁ ^ 2).base.cc = 1 := by
    rw [pow_two, CentExt.mul_base, Sd.mul_cc, hMx1bcc, one_mul]
  have hx1sqf : (M.x₁ ^ 2).fib = q tS.x₁.v := by
    rw [pow_two, CentExt.mul_fib, kappa0_cc_one dat hdat _ _ hMx1bcc, hMx1bv, hdat.f_diag]
    show (0 : ZMod 2) + 0 + q tS.x₁.v = q tS.x₁.v
    rw [add_zero, zero_add]
  -- `σ₂` is a base-slice section value
  have hs2 : M.sigma2 = sdSec dat hdat (Marking.sigma2 (sdBaseMarking tS)) := by
    show powOmega2 M.σ = _
    rw [hMσ, ← powOmega2_map]
    rfl
  -- `y₁ = x₁^{σ₂}`: base `(σ₂⁻¹ • x₁.v, 1)`
  have hy1v : M.y1R.base.v = (Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₁.v := by
    show (conjP M.x₁ M.sigma2).base.v = _
    rw [hs2, conjP_sdSec_base, sd_conjP_v, hMx1bv]
  have hy1cc : M.y1R.base.cc = 1 := by
    show (conjP M.x₁ M.sigma2).base.cc = 1
    rw [hs2, conjP_sdSec_base]
    show (Marking.sigma2 (sdBaseMarking tS))⁻¹ * tS.x₁.cc * Marking.sigma2 (sdBaseMarking tS)
      = 1
    rw [hx1cc, mul_one, inv_mul_cancel]
  -- `c = [x₁, y₁]`: the polar-form cell in the abelian `V`-slice
  have hcRf : M.cR.fib
      = polar q tS.x₁.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₁.v) := by
    show (commP M.x₁ M.y1R).fib = _
    rw [commP_fib_cc_one dat hdat M.x₁ M.y1R hMx1bcc hy1cc hV₂, hMx1bv, hy1v]
  have hcRbase : M.cR.base = 1 := by
    show (commP M.x₁ M.y1R).base = 1
    rw [show (commP M.x₁ M.y1R).base = commP M.x₁.base M.y1R.base from rfl]
    exact sd_commP_cc_one M.x₁.base M.y1R.base hMx1bcc hy1cc
  -- assemble the Roe wild word
  show ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2 * M.cR).fib
    = q tS.x₁.v + polar q tS.x₁.v ((Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₁.v)
  rw [hconj, haR, one_mul, one_mul,
    mul_fib_of_v_zero_right dat hdat _ _
      (show M.cR.base.v = 0 from by rw [hcRbase]; rfl),
    hx1sqf, hcRf]

/-- **The split Roe wild κ⁰-value is the diagonal `q`** (note ⟦prop:quadratic⟧/⟦eq:QR⟧,
`T = 1` case): the Wall double of the unconditional evaluation collapses because the split
`σ₂`-triviality `hU` kills the polar term (`b_q(d, d) = 0`, the alternating law from
`f_polar` in characteristic 2).  `Γ_R` twin of `liftMark_kappa0_wildValue_fib_split` — with
the whole `htau`/`hU`-telescope pack reduced to the single `hU`. -/
theorem liftMark_kappa0_wildValueR_fib_split [Finite C] [Finite V]
    (tS : Marking (Sd C V))
    (hσv : tS.σ.v = 0) (hτv : tS.τ.v = 0) (hx0v : tS.x₀.v = 0)
    (hx0cc : tS.x₀.cc = 1) (hx1cc : tS.x₁.cc = 1)
    (hV₂ : ∀ w : V, w + w = 0)
    (hU : ∀ w : V, Marking.sigma2 (sdBaseMarking tS) • w = w)
    (hτodd : Odd (orderOf tS.τ.cc)) :
    (liftMark tS (kappa0Cocycle dat hdat)).wildValueR.fib = q tS.x₁.v := by
  rw [liftMark_kappa0_wildValueR_fib_ramified dat hdat tS hσv hτv hx0v hx0cc hx1cc hV₂ hτodd,
    show (Marking.sigma2 (sdBaseMarking tS))⁻¹ • tS.x₁.v = tS.x₁.v from
      inv_smul_eq_iff.mpr (hU tS.x₁.v).symm]
  have hpol := hdat.f_polar tS.x₁.v tS.x₁.v
  rw [CharTwo.add_self_eq_zero] at hpol
  rw [← hpol, add_zero]

end Kappa0LedgerR

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.2) = ⟦eq:relators⟧ — the Roe wild relator `r_R` whose κ⁰-fibre is evaluated here.
  * Lemma 4.2 = ⟦lem:normalforms⟧ — the `x₁`-supported normal forms behind the section
    bijections `x1Section_bijective_{split,ramified}_R`.
  * Proposition 6.1 = ⟦prop:quadratic⟧/⟦eq:QR⟧ — the evaluated fibre is `FoxH.QZeroR`'s
    two-term shape `q(d) + b_q(d, σ₂⁻¹d)` (`liftMark_kappa0_wildValueR_fib_ramified`),
    collapsing to `q(d)` in the split regime (`liftMark_kappa0_wildValueR_fib_split`).
-/
