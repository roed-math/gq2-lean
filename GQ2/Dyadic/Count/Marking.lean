/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Separating
import GQ2.Dyadic.Count.Lifts
import GQ2.Phase140.GammaA.Foundation

/-!
# Dyadic campaign, ticket CB-6: the marking route, degree-generically

CB-5 banked `sepWordN`, the degree-generic `sep_word`, and established that it does **not** close
`IsTwoSeparating` — the fork CB-4 promoted to a binder — because that fork is a statement about
`H²(Γ, A)` at *module* coefficients and the repository has no degree-`2` comparison there.  The
`ℚ₂` candidate-side proof of `hsep` (`Phase140GammaA.hsep_gammaA`) never forms `H²(Γ_A, T)`
either: it runs the **marking route**, and `sepWordN` is that route's engine.

This file ports the marking route off `Fin 4`/`Marking` to an arbitrary alphabet `ι` and an
arbitrary relator family `W : ρ → PWord ι`, and closes `SourceDataN.hsep` on the candidate side
with it.

## Section map

| § | content | status |
|---|---------|--------|
| 1 | the cover-lift kernel: `sum_relatorFib_eq_zero` | closed |
| 2 | the invariant-dual relator sum, over the abstract carrier | closed |
| 3 | **`hsepN_marking`** — the `hsep` clause by the marking route | closed |
| 4 | the verbatim `SourceDataN.hsep` field goal, marking-route form | closed |
| 5 | branch instantiation of `Count/Separating.lean` §5 at `Vmod` | closed |

## Numeric leaves

**Nothing in this file reads a count.**  No `Nat.card`, no `SourceNumerics`, no degree `n` occurs
in any statement below; `IsSelfDualN` is never mentioned and `StokesDuality` is consumed through
`sepWordN` only, i.e. through its `h2_inj` clause.  CB-SG's exponent warning therefore has no
purchase here: there is no exponent to check against `standardNumerics`.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.AffineTLift

/-! ## §1. The cover-lift kernel

`RStageGammaA.redValues_eq_of_coverLift` (`GQ2/RStage/GammaA.lean:740`), at an arbitrary alphabet
and relator family.  The `ℚ₂` statement is *"the two reduced relator values agree"*, which over
`𝔽₂` is *"their sum is zero"*; with `ρ` relators instead of two the honest statement is that the
**traced** sum of the reduced relator values vanishes — and this is exactly the input `sepWordN`
consumes.

The `ℚ₂` proof is a four-field hand computation with `corrMark` and the `L1`
`tameValue_correction`/`wildValue_correction` pair.  Generically none of that is needed: CB-3's
correction law (`Count/Lifts.lean` §2) says the relator values of two markings over a common lower
marking differ by `j (d¹x)`, the lift's own relator values are trivial (`hpres.rel` at the lift),
and CB-VAR's `sum_heisD1_zmod2` kills the traced sum of a `d¹`-image. -/

section CoverLift

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {G : Type} [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {c : ι → C} {J : Set ι}
  (pi : G →* C) (j : ZMod 2 → G)

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [TopologicalSpace G] [DiscreteTopology G] [Finite G] [TopologicalSpace C] [DiscreteTopology C]
  [Finite C] [DistribMulAction C (ZMod 2)] in
/-- **Two markings over a common lower marking differ by kernel offsets.**  The generic form of
the four `hmem` steps of `redValues_eq_of_coverLift`. -/
theorem exists_kernel_offset {Y : Type} [Group Y] (q : G →* Y) (j : ZMod 2 → G)
    (hjsurj : ∀ g : G, q g = 1 → ∃ a : ZMod 2, g = j a)
    (f₀ u : ι → G) (hcov : ∀ i, q (f₀ i) = q (u i)) :
    ∃ x : ι → ZMod 2, ∀ i, f₀ i = j (x i) * u i := by
  classical
  choose x hx using fun i => hjsurj (f₀ i * (u i)⁻¹)
    (by rw [map_mul, map_inv, hcov i, mul_inv_cancel])
  exact ⟨x, fun i => by rw [← hx i]; group⟩

/-- **The cover-lift kernel, degree-generically.**  If the lower map lifts through the `𝔽₂`-cover
(the lift being `gc`), then the traced sum of the fibre coordinates of the relator values of *any*
set-lift marking `i ↦ j (x i) · gc (gen i)` vanishes.

`RStageGammaA.redValues_eq_of_coverLift` at arbitrary `ι`/`ρ`; the hypotheses on `j` say that its
image is a central `2`-torsion copy of `𝔽₂`, which is what a central double cover supplies (§2
instantiates `j` at `a ↦ z ^ a.val` and gets `x` from `exists_kernel_offset`).

Note that `pi` needs **no** kernel property here: it is only the base of the word complex in which
`d¹` is read, and the offsets `x` are supplied by the caller. -/
theorem sum_relatorFib_eq_zero
    (htrivC : ∀ (g : C) (m : ZMod 2), g • m = m)
    (hjmul : ∀ a b : ZMod 2, j (a + b) = j a * j b)
    (hjcomm : ∀ (g : G) (a : ZMod 2), j a * g = g * j a)
    (hjinj : Function.Injective j)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w)
    (gc : ContinuousMonoidHom Γ G) (hgc : ∀ i, pi (gc (gen i)) = c i)
    (x : ι → ZMod 2) (ζ : ρ → ZMod 2)
    (hζ : ∀ k, PWord.eval (fun i => j (x i) * gc (gen i)) (W k) = j (ζ k)) :
    ∑ k, ζ k = 0 := by
  classical
  letI : DistribMulAction G (ZMod 2) := DistribMulAction.compHom (ZMod 2) pi
  have hact : ∀ (g : G) (a : ZMod 2), g • a = pi g • a := fun _ _ => rfl
  have hjconj : ∀ (g : G) (a : ZMod 2), j (g • a) = g * j a * g⁻¹ := by
    intro g a
    rw [hact, htrivC, ← hjcomm g a]
    group
  have hkey : ∀ k, j (ζ k) = j (heisD1 (A := ZMod 2) c w x k) := by
    intro k
    rw [← hζ k, eval_corrected_heisD1 pi j hact hjmul hjconj hgc hres x k, hpres.rel gc k,
      mul_one]
  rw [show ζ = heisD1 (A := ZMod 2) c w x from funext fun k => hjinj (hkey k)]
  exact sum_heisD1_zmod2 hr hend x

end CoverLift

/-! ### The `𝔽₂`-fibre of a central double cover

`CentralCover` (`GQ2/RadicalEdge/Data.lean:35`) is exactly the datum §1 wants: `a ↦ z ^ a.val`
realizes `𝔽₂` as a central `2`-torsion subgroup which is the whole kernel. -/

section CoverFibre

variable {Y : Type} [Group Y] [Finite Y] (Q : CentralCover Y)

/-- The `𝔽₂`-parametrization of the kernel of a central double cover. -/
noncomputable def coverJ (a : ZMod 2) : Q.cover := Q.z ^ a.val

@[simp] theorem coverJ_zero : coverJ Q 0 = 1 := by
  rw [coverJ, ZMod.val_zero, pow_zero]

@[simp] theorem coverJ_one : coverJ Q 1 = Q.z := by
  rw [coverJ, ZMod.val_one, pow_one]

theorem coverJ_add (a b : ZMod 2) : coverJ Q (a + b) = coverJ Q a * coverJ Q b :=
  Q.z_pow_val_add a b

theorem coverJ_comm (g : Q.cover) (a : ZMod 2) : coverJ Q a * g = g * coverJ Q a :=
  (Commute.pow_left (Q.central g) _)

theorem coverJ_injective : Function.Injective (coverJ Q) := by
  intro a b hab
  rcases ZMod.eq_zero_or_eq_one a with rfl | rfl <;>
    rcases ZMod.eq_zero_or_eq_one b with rfl | rfl
  · rfl
  · exact absurd (by simpa using hab.symm) Q.z_ne
  · exact absurd (by simpa using hab) Q.z_ne
  · rfl

/-- **The kernel of a central double cover is exactly the `𝔽₂`-fibre.**  `ker p = ⟨z⟩` and
`z² = 1`, so every kernel element is `z⁰` or `z¹`. -/
theorem exists_coverJ_of_mem_ker {g : Q.cover} (hg : Q.p g = 1) : ∃ a : ZMod 2, g = coverJ Q a := by
  have hmem : g ∈ Q.p.ker := MonoidHom.mem_ker.mpr hg
  rw [Q.ker_eq] at hmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hz2 : Q.z ^ (2 : ℤ) = 1 := by
    rw [show ((2 : ℤ)) = ((2 : ℕ) : ℤ) from rfl, zpow_natCast, pow_two]
    exact Q.z_sq
  obtain ⟨m, hm | hm⟩ := Int.even_or_odd' n
  · exact ⟨0, by rw [hm, coverJ_zero, zpow_mul, hz2, one_zpow]⟩
  · exact ⟨1, by rw [hm, coverJ_one, zpow_add_one, zpow_mul, hz2, one_zpow, one_mul]⟩

end CoverFibre

/-! ## §2. The invariant-dual relator sum, over the abstract carrier

`Phase140GammaA.invariant_dual_relatorSum_eq_zero` (`private`, `Fin 4`-pinned through `Marking`
and `redValues_eq_of_coverLift`), at an arbitrary alphabet and relator family and over the
abstract carrier `(D, DD, S, σ, ρ)`.

This is the theorem that turns the `hsep` hypothesis — "every `χ`-obstruction of `c` vanishes" —
into `sepWordN`'s hypothesis: *every `d⁰`-invariant elementary dual kills the traced sum of the
relator values of a set-lift marking*.  The per-character `𝔽₂`-cover layer
(`Phase140GammaA.charKer`/`charCover`/`charCoverMap`/`exists_lift_charCover`) is already
`Γ`-generic and carrier-abstract and is used verbatim; the `Fin 4` content is §1's. -/

section Reduction

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg}

/-- The reduction `B/T ↠ B/M` (`T ≤ M`). -/
def piTM (D : RadicalCoverData Bg) : (Bg ⧸ D.T) →* Bg ⧸ D.M :=
  QuotientGroup.map D.T D.M (MonoidHom.id Bg) (by rw [Subgroup.comap_id]; exact D.hTM)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
@[simp] theorem piTM_mk (b : Bg) : piTM D (QuotientGroup.mk b) = QuotientGroup.mk b := rfl

variable {DD : DescData D}

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **`liftC0` is injective** — the `hkerC0` clause read as injectivity.  Re-derived because the
`ℚ₂` copies (`Phase140GammaA.mk_eq_of_mkT_eq`, `Count/Separation.lean`'s `fLift_mk_MN`) both keep
it inline. -/
theorem liftC0_injective (DD : DescData D) : Function.Injective (liftC0 DD) := by
  intro x y hxy
  induction x using QuotientGroup.induction_on with
  | H bx =>
    induction y using QuotientGroup.induction_on with
    | H by' =>
      rw [liftC0_mk, liftC0_mk] at hxy
      refine (QuotientGroup.eq (s := D.M)).mpr ?_
      rw [← DD.hkerC0, MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

omit [DiscreteTopology Bg] in
/-- **A `π_T`-lift lies over `ρ` for `π_M` too** — `Phase140GammaA.mk_eq_of_mkT_eq` in the form the
marking route wants: the whole hom, not one value at a time. -/
theorem piTM_qLiftsOver (gQ : QLiftsOver DD rho) (γ : Γ) : piTM D (gQ.1 γ) = rho γ := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk_surjective (s := D.T) (gQ.1 γ)
  rw [← hy, piTM_mk]
  refine liftC0_injective DD ?_
  rw [liftC0_mk, ← piQbar_mk DD y,
    show (piT (D := D) y) = (QuotientGroup.mk y : Bg ⧸ D.T) from rfl, hy]
  exact gQ.2 γ

end Reduction

section InvariantDual

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι]
  {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {D : RadicalCoverData Bg} {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T}
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)]
  [DistribMulAction (Bg ⧸ D.M) (ZMod 2)]
  {rho : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
  {gen : ι → Γ} {W : ρ → PWord ι} {w : ρ → FreeGroup ι} {cM : ι → Bg ⧸ D.M} {J : Set ι}

open Phase140GammaA RadicalEdgeGammaA

omit [Fintype ι] [Fintype ρ] [DecidableEq ι] [TopologicalSpace Bg] [DiscreteTopology Bg]
  [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [DistribMulAction (Bg ⧸ D.M) (ZMod 2)] in
/-- **A `C`-fixed elementary dual of `Additive T` is conjugation-invariant** — the induced
character is a `TCharC`.  `Phase140GammaA.fixed_elemDual_conj_apply`, over the abstract carrier. -/
theorem fixed_elemDual_conj_applyN (lam : ElemDual (Additive ↥D.T))
    (hfix : lam ∈ fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) (bb : Bg) (t : ↥D.T) :
    lam (Additive.ofMul (⟨bb * (t : Bg) * bb⁻¹, D.hT.conj_mem (t : Bg) t.2 bb⟩ : ↥D.T))
      = lam (Additive.ofMul t) := by
  conv_lhs => rw [← hfix (QuotientGroup.mk bb)]
  rw [ElemDual.smul_apply]
  congr 1
  refine Additive.toMul.injective (Subtype.ext ?_)
  rw [cActT_toMul, cactFun_eq D _ (b := bb⁻¹) (by rw [QuotientGroup.mk_inv])]
  show bb⁻¹ * (bb * (t : Bg) * bb⁻¹) * bb⁻¹⁻¹ = (t : Bg)
  group

/-- **The invariant-dual relator sum vanishes** — the candidate-side input of `sepWordN`.

`Phase140GammaA.invariant_dual_relatorSum_eq_zero` at arbitrary `ι`/`ρ`.  A `d⁰`-invariant
elementary dual `λ` induces a `C`-invariant character `χ_λ`; if `χ_λ = 0` every relator value is
killed outright, and otherwise `β_{χ_λ}(c) = 0` produces a lift of `g_c` through the `χ_λ`-cover
(`exists_lift_charCover`), which by §1 forces the traced sum of the reduced relator values — i.e.
`∑ₖ χ_λ(vₖ)` — to vanish. -/
theorem invariant_dual_relatorSum_eq_zeroN
    (S : CountSections DD σ) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (htrivC : ∀ (g : Bg ⧸ D.M) (m : ZMod 2), g • m = m)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres2 : ResolvesAt W w (WordLift (ZMod 2) (Bg ⧸ D.M)))
    (hcc : ∀ i, rho (gen i) = cM i) (hend : IsStokesEndpoint w)
    (u : VCocycle DD rho) (hvan : ∀ χ : ↥(TCharC D), betaChi S hσ χ u = 0)
    (f₀ : ι → Bg)
    (hproj : ∀ i, (QuotientGroup.mk (f₀ i) : Bg ⧸ D.T) = (qOfCocycle DD rho σ hσ u).1 (gen i))
    (hvmem : ∀ k, PWord.eval f₀ (W k) ∈ D.T)
    (lam : ElemDual (Additive ↥D.T))
    (hlam : lam ∈ fixedPts (Bg ⧸ D.M) (ElemDual (Additive ↥D.T))) :
    lam (∑ k, Additive.ofMul (⟨PWord.eval f₀ (W k), hvmem k⟩ : ↥D.T)) = 0 := by
  classical
  set chi : ↥(TCharC D) := ⟨fun t => lam (Additive.ofMul t),
    ⟨fun t t' => map_add lam (Additive.ofMul t) (Additive.ofMul t'),
     fun bb t => fixed_elemDual_conj_applyN lam hlam bb t⟩⟩ with hchi
  rw [map_sum]
  by_cases hz : chi = 0
  · refine Finset.sum_eq_zero fun k _ => ?_
    have h0 := congrArg (fun ξ : ↥(TCharC D) => ξ.1 ⟨PWord.eval f₀ (W k), hvmem k⟩) hz
    simpa using h0
  · -- the lift of `g_c` through the `χ`-cover
    obtain ⟨gc, hgclift⟩ := exists_lift_charCover htriv S hσ chi hz u
      (iotaB_eq_zero_iff.mp (hvan chi))
    -- §1's data: the word-complex base, and the `𝔽₂`-fibre of the cover
    have hgc : ∀ i, ((piTM D).comp (charCover chi hz).p) (gc (gen i)) = cM i := by
      intro i
      show piTM D ((charCover chi hz).p (gc (gen i))) = cM i
      rw [hgclift (gen i), piTM_qLiftsOver, hcc i]
    have hcov : ∀ i, (charCover chi hz).p (charCoverMap chi hz (f₀ i))
        = (charCover chi hz).p (gc (gen i)) := by
      intro i
      rw [hgclift (gen i),
        show (charCover chi hz).p (charCoverMap chi hz (f₀ i))
          = ((charCover chi hz).p.comp (charCoverMap chi hz)) (f₀ i) from rfl,
        charCover_p_comp chi hz]
      exact hproj i
    obtain ⟨x, hx⟩ := exists_kernel_offset (ι := ι) (charCover chi hz).p
      (coverJ (charCover chi hz)) (fun g hg => exists_coverJ_of_mem_ker _ hg)
      (fun i => charCoverMap chi hz (f₀ i)) (fun i => gc (gen i)) hcov
    refine sum_relatorFib_eq_zero ((piTM D).comp (charCover chi hz).p)
      (coverJ (charCover chi hz)) htrivC (coverJ_add _) (coverJ_comm _) (coverJ_injective _)
      hpres hres2 (fun k => lower_rel (A := ZMod 2) rho hcc hpres hres2 k) hend gc hgc x _ ?_
    intro k
    rw [show (fun i => coverJ (charCover chi hz) (x i) * gc (gen i))
        = fun i => charCoverMap chi hz (f₀ i) from (funext hx).symm,
      show (fun i => charCoverMap chi hz (f₀ i))
        = fun i => discreteCMH (charCoverMap chi hz) (f₀ i) from rfl,
      ← PWord.map_eval (discreteCMH (charCoverMap chi hz)) f₀ (W k)]
    show charCoverMap chi hz ((⟨PWord.eval f₀ (W k), hvmem k⟩ : ↥D.T) : Bg) = _
    exact charCoverMap_coe_eq_zpow chi hz ⟨PWord.eval f₀ (W k), hvmem k⟩

end InvariantDual

end GQ2.Dyadic.Count
