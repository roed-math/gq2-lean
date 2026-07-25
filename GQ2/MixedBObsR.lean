/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.MixedBObs
import GQ2.WordCoh2R

/-!
# The mixed Heisenberg pairing as a Roe relator obstruction (`mixedB_R = relZPairR`)

The `Γ_R` twin of `GQ2/MixedBObs.lean`.  The Heisenberg 2-cocycle `kappaHeis`, the structural
isomorphism `PhiHeis : CentExt kappaHeis →* HeisLift A C`, and the base marking `mBaseMarking`
are **word-independent** and reused verbatim from the `Γ_A` file; only the two statements that
read a *relator* off a marking are re-derived at `Marking.wildValueR`:

* `mixedB_eq_relZPairR` — the traced Heisenberg central coordinate of the **Roe** wild relator,
  `mixedB_R t x y` (`GQ2/Roe/FoxBasic.lean`), is the traced fibre coordinate `relZPairR` of
  `kappaHeis`'s lifted base marking.  Same proof as the `Γ_A` original, with
  `Marking.map_wildValue` swapped for `Marking.map_wildValueR`.
* `obs_inflation_R` — the `WordCoh2R` obstruction of a continuous 2-cocycle on `Γ_R` that
  factors *pointwise* through a finite group `L` is the Roe relator-`z` pair of the pushforward
  marking `gammaGenR.map H`.  Stated at `F₄ ⧸ N_R` (**not** at the Demushkin quotient `DR`, where
  `GQ2/Roe/DRWordCoh.lean`'s `obs_DR` lives), exactly as `Γ_A` builds `obs` at `F₄ ⧸ N_A`.

Together these are the source-generic, edge-free half of the `Γ_R` ledger identity
`obs_R(varCoc u) = mixedB_R t_ρ x_w y_φ`; the edge-specific half is assembled in
`GQ2/LedgerGammaR.lean`.
-/

namespace GQ2

namespace MixedBObsR

open FoxH WordCoh2 WordCoh2R MixedBObs

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **`mixedB_R` is a Roe relator-`z` pair.**  The traced Heisenberg central coordinate of the
Roe wild relator equals the traced fibre coordinate of `kappaHeis`'s lifted base marking — i.e.
`mixedB_R` *is* a `WordCoh2R` relator obstruction.  `Γ_R` twin of
`MixedBObs.mixedB_eq_relZPair`. -/
theorem mixedB_eq_relZPairR [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A)
    (y : Fin 4 → ElemDual A) :
    mixedB_R t x y = (relZPairR (mBaseMarking t x y) kappaHeis).1
                   + (relZPairR (mBaseMarking t x y) kappaHeis).2 := by
  have htame := Marking.map_tameValue PhiHeis (liftMark (mBaseMarking t x y) kappaHeis)
  have hwild := Marking.map_wildValueR PhiHeis (liftMark (mBaseMarking t x y) kappaHeis)
  rw [map_liftMark_mBase] at htame hwild
  show (heisMarking t x y).tameValue.z + (heisMarking t x y).wildValueR.z = _
  rw [htame, hwild]
  rfl

/-! ## Obstruction of an inflated cocycle

The `WordCoh2R` obstruction `obs_R` of a continuous 2-cocycle on `Γ_R` that factors *pointwise*
through a finite group `L` (`φ(a,b) = κ(H a)(H b)`) is the Roe relator-`z` pair of the pushforward
marking `gammaGenR.map H`.  This packages the entire `LevelFactorR` / `relZPairR_comap` computation
once and generically, so the edge-specific ledger identity is a one-line application. -/

section Inflation

open WordCohBridgeR ContCoh

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
  (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)

omit [ContinuousSMul GR (ZMod 2)] in
/-- **Obstruction of an inflated cocycle.**  If a continuous 2-cocycle `φ` on `Γ_R` factors
pointwise through a finite group `L` as `φ(a,b) = κ(H a)(H b)` for a continuous hom
`H : Γ_R → L` and a 2-cocycle `κ` on `L`, its Roe obstruction is the Roe relator-`z` pair of the
pushforward marking `gammaGenR.map H`.  `Γ_R` twin of `MixedBObs.obs_inflation`, at `F₄ ⧸ N_R`. -/
theorem obs_inflation_R {L : Type*} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
    (H : ContinuousMonoidHom GR L) (κ : TwoCocycle L) (φ : Z2 GR (ZMod 2))
    (hφ : ∀ a b, φ.1 (a, b) = κ.κ (H a) (H b)) :
    obs_R htriv φ = (relZPairR (gammaGenR.map H.toMonoidHom) κ).1
                  + (relZPairR (gammaGenR.map H.toMonoidHom) κ).2 := by
  set G := H.comp (quotientMk NR)
  have hNR : NR ≤ G.toMonoidHom.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    show H (quotientMk NR g) = 1
    rw [(quotientMk_eq_one_iff NR).mpr hg, map_one]
  have hopen : IsOpen ((G.toMonoidHom.ker : Subgroup (FreeProfiniteGroup (Fin 4)))
      : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((G.toMonoidHom.ker : Subgroup (FreeProfiniteGroup (Fin 4)))
        : Set (FreeProfiniteGroup (Fin 4))) = G ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set L)).preimage G.continuous_toFun
  set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := G.toMonoidHom.ker, isOpen' := hopen }
  have hUsub : NR ≤ U.toSubgroup := hNR
  set Gbar := QuotientGroup.kerLift G.toMonoidHom
  have hhom : Gbar.comp (QuotientGroup.mk' U.toSubgroup)
      = H.toMonoidHom.comp (quotientMk NR).toMonoidHom := by
    ext g
    exact QuotientGroup.kerLift_mk G.toMonoidHom g
  have hGbarproj : ∀ a : GR, Gbar (levelProjR U hUsub a) = H a := by
    intro a
    obtain ⟨g, rfl⟩ := quotientMk_surjective NR a
    rw [levelProjR_quotientMk]
    exact QuotientGroup.kerLift_mk G.toMonoidHom g
  have hnorm : φ.1 (1, 1) = 0 := by rw [hφ, map_one, κ.norm]
  have hfact : ∀ p q, normalizeCochainR φ.1 (p, q)
      = (κ.comap Gbar).κ (levelProjR U hUsub p) (levelProjR U hUsub q) := by
    intro p q
    rw [TwoCocycle.comap_κ, hGbarproj, hGbarproj, ← hφ]
    show φ.1 (p, q) - φ.1 (1, 1) = φ.1 (p, q)
    rw [hnorm, sub_zero]
  have hmark : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).map Gbar
      = gammaGenR.map H.toMonoidHom := by
    rw [Marking.map_map, gammaGenR, Marking.map_map, hhom]
  show obsFun_R htriv φ = _
  rw [obsFun_eq_R htriv φ ⟨U, hNR, κ.comap Gbar, hfact⟩]
  show (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup)) (κ.comap Gbar)).1
      + (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup)) (κ.comap Gbar)).2 = _
  rw [← relZPairR_comap, hmark]

end Inflation

end MixedBObsR

end GQ2
