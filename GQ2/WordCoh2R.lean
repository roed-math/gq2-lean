/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.WordCoh2
import GQ2.WordCohBridgeR
import GQ2.Roe.WildRow

/-!
# The `Γ_R` degree-2 presentation comparison — the obstruction layer

The Roe-candidate twin of `GQ2/WordCoh2.lean`'s obstruction block: an injection
`H²(Γ_R, 𝔽₂) ↪ 𝔽₂` (`obsH2_R`/`obsH2_R_injective`), obtained by evaluating the two `Γ_R` relator
words — the **shared** tame relator and the **Roe** wild relator
`r_R = (x₀^σ)⁻¹ · a · x₁² · c` (`Marking.wildValueR`) — on a central extension of a finite
admissible level.  Together with a nonzero variation class this gives `#H²(Γ_R, 𝔽₂) = 2`
(`GQ2/HalfTorsorGammaR.lean`), the `SourceData.cardH2` leaf for `Γ_R`.

**What is new and what is inherited.**  `GQ2/WordCoh2.lean` develops its central-extension
machinery for an *arbitrary* group `L`: `TwoCocycle`, `CentExt` (+ `proj`/`incl`), `liftMark`,
`shiftLiftMark`, `isPGroup_shiftLift_wildCore`, the level-change pair `TwoCocycle.comap`/`projExt`,
the Baer-sum comparison object `FiberProd` (+ `pr1`/`pr2`/`prSum`/`liftMarkFP`), the split and
coboundary cocycles `zeroCocycle`/`coboundaryCocycle` (+ `fibHom0`/`Psi`), the shift comparison
`shiftCompare`/`wlBase`, and the compactness lemma `exists_openNormalSubgroup_factor_two`.  All of
that is **imported and reused verbatim** — it never mentions a relator.  What is re-derived here is
exactly the part that reads the *wild* relator off a marking, plus the part typed at `N_R`:

* the relator-`z` pair `relZPairR t c = (tame.fib, wild_R.fib)` and its three structural laws
  (`relZPairR_comap`, `relZPairR_add`, `relZPairR_zero`/`obs_coboundaryR_eq`);
* the wild shift law `shiftLiftMark_wildValueR_fib` (from `FoxH.liftMarking_wildValueR_u`, whose
  row `x₁ + (1 + S⁻¹)·x₂` replaces `Γ_A`'s `x₁ + (1 + S⁻¹)·x₃` — the *same* fibre shift `a 1`);
* the splitting section over `N_R` (`NR_le_ker_shiftLiftR`/`sectionHomR`), which runs the
  `IsAdmissibleUR`/`isAdmissibleUR_iff_NR_le` route in place of `IsAdmissibleU`/`isAdmissibleU_iff_NA_le`;
* the `N_R`-typed factoring/assembly chain and the obstruction homomorphism itself
  (`LevelFactorR`, `obs_R`, `obs_ker_eq_B2_R`, `obsH2_R`).

Statement shapes mirror the `Γ_A` originals binder-for-binder, so downstream ports read verbatim
modulo the `_R` suffix.
-/

namespace GQ2

namespace WordCoh2R

open ContCoh FoxH WordCoh2 WordCohBridgeR

/-! ## The Roe relator-`z` pair -/

section RelZR

variable {L : Type*} [Group L]

private theorem shiftLiftMark_map_projR (t : Marking L) (a : Fin 4 → ZMod 2) (c : TwoCocycle L) :
    (shiftLiftMark t a c).map (CentExt.proj c) = t := rfl

/-- The **Roe** wild relator value of the lifted marking projects to that of the base marking
(needs `L` finite: `Marking.map_wildValueR`'s `ω₂`-naturality is finite-only, and `CentExt c` is
finite).  `Γ_R` twin of `WordCoh2.liftMark_wildValue_base`. -/
theorem liftMark_wildValueR_base [Finite L] (t : Marking L) (c : TwoCocycle L) :
    (liftMark t c).wildValueR.base = t.wildValueR :=
  liftMark_map_proj t c ▸ (Marking.map_wildValueR (CentExt.proj c) (liftMark t c)).symm

/-- The **Roe relator-`z` pair** of `c` relative to a base marking `t`: the fibre coordinates of
the tame and *Roe* wild relator values of the lifted marking — the degree-2 obstruction of `c`,
pre-quotient by `im d1_triv`.  `Γ_R` twin of `WordCoh2.relZPair`; only the second component
differs (`wildValueR` for `wildValue`). -/
noncomputable def relZPairR [Finite L] (t : Marking L) (c : TwoCocycle L) : ZMod 2 × ZMod 2 :=
  ((liftMark t c).tameValue.fib, (liftMark t c).wildValueR.fib)

/-- **Sanity 1/2.**  The tame component of `relZPairR` is definitionally `relZPair`'s — the tame
relator is shared with `Γ_A`. -/
theorem relZPairR_fst [Finite L] (t : Marking L) (c : TwoCocycle L) :
    (relZPairR t c).1 = (relZPair t c).1 := rfl

/-- **Sanity 2/2.**  The wild component of `relZPairR` is the Roe wild relator's fibre. -/
theorem relZPairR_snd [Finite L] (t : Marking L) (c : TwoCocycle L) :
    (relZPairR t c).2 = (liftMark t c).wildValueR.fib := rfl

/-- The shifted lift's Roe wild relator value projects to the base's (needs `L` finite). -/
theorem shiftLiftMark_wildValueR_base [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2)
    (c : TwoCocycle L) : (shiftLiftMark t a c).wildValueR.base = t.wildValueR :=
  shiftLiftMark_map_projR t a c ▸
    (Marking.map_wildValueR (CentExt.proj c) (shiftLiftMark t a c)).symm

/-- **Roe wild relator dies exactly.**  When the base marking satisfies the Roe wild relation and
the shifted wild `z`-value is `0`, the shifted lift's Roe wild relator value is the identity of the
extension. -/
theorem shiftLiftMark_wildValueR_eq_one [Finite L] (t : Marking L) (hw : t.WildRelR)
    (a : Fin 4 → ZMod 2) (c : TwoCocycle L) (hz : (shiftLiftMark t a c).wildValueR.fib = 0) :
    (shiftLiftMark t a c).wildValueR = 1 := by
  apply CentExt.ext
  · rw [shiftLiftMark_wildValueR_base, (Marking.wildValueR_eq_one_iff t).mpr hw]; rfl
  · rw [hz]; rfl

end RelZR

/-! ## The Roe wild shift law

Shifting the lifted marking's fibre coordinates by `a` moves the *Roe* wild fibre obstruction by
`a 1` — the same shift as the tame one, and the same as `Γ_A`'s wild shift, even though the
underlying Fox row differs (`x₁ + (1 + S⁻¹)·x₂` here versus `x₁ + (1 + S⁻¹)·x₃` there): at the
trivial action of `CentExt c` on `𝔽₂` both collapse to `a 1` in characteristic `2`. -/

section ShiftLawsR

variable {L : Type*} [Group L] {c : TwoCocycle L}

attribute [local instance] WordCoh2.trivAction

private theorem shiftCompare_fibR (p : WordLift (ZMod 2) (CentExt c)) :
    (shiftCompare p).fib = p.u + p.g.fib :=
  CentExt.incl_mul_fib p.u p.g

/-- The Roe wild relator value's base coordinate of the lift recovers that of `liftMark t c`. -/
theorem liftMarking_wildValueR_g [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).wildValueR.g = (liftMark t c).wildValueR :=
  map_wlBase_liftMarking t a ▸
    (Marking.map_wildValueR wlBase (liftMarking (liftMark t c) a)).symm

/-- The Roe wild fibre shift of the lift is `a 1` (`liftMarking_wildValueR_u` at trivial action,
char 2: the row `a 1 + a 2 + S⁻¹·a 2` collapses to `a 1`). -/
theorem liftMarking_wildValueR_u_eq [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).wildValueR.u = a 1 := by
  rw [liftMarking_wildValueR_u (liftMark t c) a (fun v => CharTwo.add_self_eq_zero v)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  show a 1 + a 2 + a 2 = a 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **Roe wild shift law**: shifting the lift by `a` changes the Roe wild fibre obstruction by
`a 1`. -/
theorem shiftLiftMark_wildValueR_fib [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (shiftLiftMark t a c).wildValueR.fib = (liftMark t c).wildValueR.fib + a 1 := by
  rw [← map_shiftCompare_liftMarking t a, Marking.map_wildValueR, shiftCompare_fibR,
      liftMarking_wildValueR_u_eq, liftMarking_wildValueR_g, add_comm]

/-- **The `d¹`-adjustment.**  When the tame and Roe wild fibre obstructions of `liftMark t c`
agree, the constant shift `a ≡ (liftMark t c).tameValue.fib` makes *both* shifted relator fibres
vanish — the hypothesis feeding `NR_le_ker_shiftLiftR`. -/
theorem exists_shiftR_of_relZ_eq [Finite L] (t : Marking L)
    (hrel : (liftMark t c).tameValue.fib = (liftMark t c).wildValueR.fib) :
    ∃ a : Fin 4 → ZMod 2, (shiftLiftMark t a c).tameValue.fib = 0
      ∧ (shiftLiftMark t a c).wildValueR.fib = 0 := by
  refine ⟨fun _ => (liftMark t c).tameValue.fib, ?_, ?_⟩
  · rw [shiftLiftMark_tameValue_fib, CharTwo.add_self_eq_zero]
  · rw [shiftLiftMark_wildValueR_fib, ← hrel, CharTwo.add_self_eq_zero]

end ShiftLawsR

/-! ## Level change and additivity

`relZPairR` is natural in the base group (`relZPairR_comap`) and additive in the cocycle
(`relZPairR_add`) — the two structural laws making the obstruction well defined and a
homomorphism.  Both comparison objects (`projExt`, `FiberProd`) are reused from `WordCoh2`. -/

section LevelChangeR

variable {L L' : Type*} [Group L] [Group L']

/-- **Level-independence of the Roe relator obstruction.**  Pulling `c` back along `φ` and pushing
the base marking forward by `φ` give the same `relZPairR`. -/
theorem relZPairR_comap [Finite L] [Finite L'] (t' : Marking L') (c : TwoCocycle L) (φ : L' →* L) :
    relZPairR (t'.map φ) c = relZPairR t' (c.comap φ) := by
  have ht := Marking.map_tameValue (projExt c φ) (liftMark t' (c.comap φ))
  have hw := Marking.map_wildValueR (projExt c φ) (liftMark t' (c.comap φ))
  rw [map_projExt_liftMark] at ht hw
  apply Prod.ext
  · show (liftMark (t'.map φ) c).tameValue.fib = (liftMark t' (c.comap φ)).tameValue.fib
    rw [ht]; rfl
  · show (liftMark (t'.map φ) c).wildValueR.fib = (liftMark t' (c.comap φ)).wildValueR.fib
    rw [hw]; rfl

end LevelChangeR

section AdditivityR

variable {L : Type*} [Group L]

/-- The pointwise sum of two 2-cocycles evaluates pointwise (`WordCoh2.TwoCocycle.add_κ` is
private, so it is restated here). -/
private theorem add_κR (c₁ c₂ : TwoCocycle L) (a b : L) :
    (c₁ + c₂).κ a b = c₁.κ a b + c₂.κ a b := rfl

private theorem map_pr1_liftMarkFPR (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.pr1 = liftMark t c₁ := rfl

private theorem map_pr2_liftMarkFPR (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.pr2 = liftMark t c₂ := rfl

private theorem map_prSum_liftMarkFPR (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.prSum = liftMark t (c₁ + c₂) := by
  simp only [liftMarkFP, Marking.map, liftMark, Marking.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact CentExt.ext rfl (add_zero (0 : ZMod 2))

/-- **Additivity of the Roe relator obstruction.**  Same fibre-product argument as
`WordCoh2.relZPair_add`, now with `Marking.map_wildValueR` on the second component. -/
theorem relZPairR_add [Finite L] (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    relZPairR t (c₁ + c₂) = relZPairR t c₁ + relZPairR t c₂ := by
  have ht1 := Marking.map_tameValue FiberProd.pr1 (liftMarkFP t c₁ c₂)
  have hw1 := Marking.map_wildValueR FiberProd.pr1 (liftMarkFP t c₁ c₂)
  have ht2 := Marking.map_tameValue FiberProd.pr2 (liftMarkFP t c₁ c₂)
  have hw2 := Marking.map_wildValueR FiberProd.pr2 (liftMarkFP t c₁ c₂)
  have hts := Marking.map_tameValue FiberProd.prSum (liftMarkFP t c₁ c₂)
  have hws := Marking.map_wildValueR FiberProd.prSum (liftMarkFP t c₁ c₂)
  rw [map_pr1_liftMarkFPR] at ht1 hw1
  rw [map_pr2_liftMarkFPR] at ht2 hw2
  rw [map_prSum_liftMarkFPR] at hts hws
  apply Prod.ext
  · show (liftMark t (c₁ + c₂)).tameValue.fib
        = (liftMark t c₁).tameValue.fib + (liftMark t c₂).tameValue.fib
    rw [hts, ht1, ht2]; rfl
  · show (liftMark t (c₁ + c₂)).wildValueR.fib
        = (liftMark t c₁).wildValueR.fib + (liftMark t c₂).wildValueR.fib
    rw [hws, hw1, hw2]; rfl

end AdditivityR

/-! ## Vanishing on coboundaries -/

section CoboundaryObstructionR

variable {L : Type*} [Group L]

/-- The trivial marking (all four generators `1`) satisfies the **Roe** wild relation.  Both
`ω₂`-subwords of `r_R` (inside `aR` and inside `cR`'s `sigma2`) are powers of `1`. -/
theorem trivialMarking_wildValueR : (⟨1, 1, 1, 1⟩ : Marking L).wildValueR = 1 := by
  rw [Marking.wildValueR_eq_one_iff]
  simp [Marking.WildRelR, Marking.wildValueR, Marking.aR, Marking.cR, Marking.y1R,
    Marking.sigma2, conjP, commP, powOmega2]

/-- The split extension has **balanced (zero) Roe relator obstruction**. -/
theorem relZPairR_zero [Finite L] (t : Marking L) :
    relZPairR t (zeroCocycle : TwoCocycle L) = (0, 0) := by
  have hmap : (liftMark t (zeroCocycle : TwoCocycle L)).map fibHom0
      = (⟨1, 1, 1, 1⟩ : Marking (Multiplicative (ZMod 2))) := rfl
  apply Prod.ext
  · have h := Marking.map_tameValue fibHom0 (liftMark t (zeroCocycle : TwoCocycle L))
    rw [hmap, trivialMarking_tameValue] at h
    exact (Multiplicative.ofAdd.injective h.symm : _)
  · have h := Marking.map_wildValueR fibHom0 (liftMark t (zeroCocycle : TwoCocycle L))
    rw [hmap, trivialMarking_wildValueR] at h
    exact (Multiplicative.ofAdd.injective h.symm : _)

private theorem Psi_fibR (lam : L → ZMod 2) (hlam1 : lam 1 = 0)
    (p : CentExt (coboundaryCocycle lam hlam1)) : (Psi lam hlam1 p).fib = p.fib + lam p.base := rfl

/-- **The Roe obstruction of a finite-level coboundary** is `λ (tame relator) + λ (Roe wild
relator)`.  At an `R`-admissible level both relators die, so this is `0` — the vanishing of
`obs_R` on `B²`. -/
theorem obs_coboundaryR_eq [Finite L] (t : Marking L) (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    (relZPairR t (coboundaryCocycle lam hlam1)).1 + (relZPairR t (coboundaryCocycle lam hlam1)).2
      = lam t.tameValue + lam t.wildValueR := by
  have hz1 : (liftMark t (zeroCocycle : TwoCocycle L)).tameValue.fib = 0 :=
    congrArg Prod.fst (relZPairR_zero t)
  have hz2 : (liftMark t (zeroCocycle : TwoCocycle L)).wildValueR.fib = 0 :=
    congrArg Prod.snd (relZPairR_zero t)
  have htame : (relZPairR t (coboundaryCocycle lam hlam1)).1
      = ![lam t.σ, lam t.τ, lam t.x₀, lam t.x₁] 1 + lam t.tameValue := by
    have h := congrArg CentExt.fib
      (Marking.map_tameValue (Psi lam hlam1) (liftMark t (coboundaryCocycle lam hlam1)))
    rw [map_Psi_liftMark, shiftLiftMark_tameValue_fib, hz1, zero_add, Psi_fibR,
      liftMark_tameValue_base] at h
    rw [show (relZPairR t (coboundaryCocycle lam hlam1)).1
        = (liftMark t (coboundaryCocycle lam hlam1)).tameValue.fib from rfl, h]
    abel_nf
    simp [CharTwo.two_eq_zero]
  have hwild : (relZPairR t (coboundaryCocycle lam hlam1)).2
      = ![lam t.σ, lam t.τ, lam t.x₀, lam t.x₁] 1 + lam t.wildValueR := by
    have h := congrArg CentExt.fib
      (Marking.map_wildValueR (Psi lam hlam1) (liftMark t (coboundaryCocycle lam hlam1)))
    rw [map_Psi_liftMark, shiftLiftMark_wildValueR_fib, hz2, zero_add, Psi_fibR,
      liftMark_wildValueR_base] at h
    rw [show (relZPairR t (coboundaryCocycle lam hlam1)).2
        = (liftMark t (coboundaryCocycle lam hlam1)).wildValueR.fib from rfl, h]
    abel_nf
    simp [CharTwo.two_eq_zero]
  rw [htame, hwild]
  abel_nf
  simp [CharTwo.two_eq_zero]

end CoboundaryObstructionR

/-! ## The splitting section: `N_R ≤ ker (classify (shifted lift))`

The injectivity crux, an exact mirror of `WordCoh2.NA_le_ker_shiftLift` with
`IsAdmissibleU`/`isAdmissibleU_iff_NA_le` swapped for `IsAdmissibleUR`/`isAdmissibleUR_iff_NR_le`
and `Marking.map_wildRelator_eq_one_iff` for `Marking.map_wildRelatorR_eq_one_iff`.  The `Pro2Core`
clause reuses the word-independent `WordCoh2.isPGroup_shiftLift_wildCore`. -/

/-- **`N_R ≤ ker` for the shifted lift.**  (`[Finite (F₄ ⧸ U)]` is needed at statement level for
`CentExt c` to be finite.) -/
theorem NR_le_ker_shiftLiftR (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)]
    (hU : NR ≤ U.toSubgroup) (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValueR.fib
      = 0) :
    NR ≤ (Marking.classify
      (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c)).toMonoidHom.ker := by
  set t_L := univMarking.map (QuotientGroup.mk' U.toSubgroup) with ht_L
  have hadmL : t_L.AdmissibleR := isAdmissibleUR_of_NR_le hU
  set m := Marking.classify (shiftLiftMark t_L a c) with hm
  have hut : univMarking.map m.toMonoidHom = shiftLiftMark t_L a c := by
    rw [hm, Marking.classify, univMarking_map_toHom]
  have htame : m.toMonoidHom univMarking.tameRelator = 1 :=
    (Marking.map_tameRelator_eq_one_iff m univMarking).mpr (by
      rw [hut]
      exact (Marking.tameValue_eq_one_iff _).mp
        (shiftLiftMark_tameValue_eq_one t_L hadmL.2.1 a c htame0))
  have hwild : m.toMonoidHom univMarking.wildRelatorR = 1 :=
    (Marking.map_wildRelatorR_eq_one_iff m univMarking).mpr (by
      rw [hut]
      exact (Marking.wildValueR_eq_one_iff _).mp
        (shiftLiftMark_wildValueR_eq_one t_L hadmL.2.2.1 a c hwild0))
  have hker_open :
      IsOpen ((m.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) :=
    (isOpen_discrete ({1} : Set (CentExt c))).preimage m.continuous_toFun
  let V : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := m.toMonoidHom.ker, isOpen' := hker_open }
  have hx0 : m.toMonoidHom univMarking.x₀ = (shiftLiftMark t_L a c).x₀ := congrArg Marking.x₀ hut
  have hx1 : m.toMonoidHom univMarking.x₁ = (shiftLiftMark t_L a c).x₁ := congrArg Marking.x₁ hut
  haveI : DiscreteTopology (FreeProfiniteGroup (Fin 4) ⧸
      (V.toOpenSubgroup : Subgroup (FreeProfiniteGroup (Fin 4)))) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup
  have hadm : IsAdmissibleUR V := by
    refine ⟨generates_univMarking_map _, ?_, ?_, ?_⟩
    · exact (Marking.map_tameRelator_eq_one_iff (quotientMk V.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr htame))
    · exact (Marking.map_wildRelatorR_eq_one_iff (quotientMk V.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hwild))
    · rw [Marking.Pro2Core]
      have hval : ∀ g : FreeProfiniteGroup (Fin 4),
          QuotientGroup.kerLift m.toMonoidHom (QuotientGroup.mk' V.toSubgroup g)
            = m.toMonoidHom g :=
        fun g => QuotientGroup.kerLift_mk m.toMonoidHom g
      have hcomap : IsPGroup 2 (Subgroup.comap (QuotientGroup.kerLift m.toMonoidHom)
          (Subgroup.normalClosure
            {(shiftLiftMark t_L a c).x₀, (shiftLiftMark t_L a c).x₁})) :=
        IsPGroup.comap_of_injective
          (isPGroup_shiftLift_wildCore t_L a c hadmL.2.2.2)
          (QuotientGroup.kerLift m.toMonoidHom) (QuotientGroup.kerLift_injective m.toMonoidHom)
      refine IsPGroup.to_le hcomap (Subgroup.normalClosure_le_normal ?_)
      rintro w (rfl | rfl)
      · show QuotientGroup.kerLift m.toMonoidHom (QuotientGroup.mk' V.toSubgroup univMarking.x₀)
            ∈ Subgroup.normalClosure {(shiftLiftMark t_L a c).x₀, (shiftLiftMark t_L a c).x₁}
        rw [hval, hx0]
        exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
      · show QuotientGroup.kerLift m.toMonoidHom (QuotientGroup.mk' V.toSubgroup univMarking.x₁)
            ∈ Subgroup.normalClosure {(shiftLiftMark t_L a c).x₀, (shiftLiftMark t_L a c).x₁}
        rw [hval, hx1]
        exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)
  exact (isAdmissibleUR_iff_NR_le V).mp hadm

/-- **The splitting section** `Γ_R → CentExt c` produced by `NR_le_ker_shiftLiftR`. -/
noncomputable def sectionHomR (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NR ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValueR.fib
      = 0) :
    ContinuousMonoidHom GR (CentExt c) :=
  quotientLift NR
    (Marking.classify (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c))
    (NR_le_ker_shiftLiftR U hU c a htame0 hwild0)

/-- The section splits the base projection: `proj ∘ s` is the level projection `Γ_R ↠ F₄ ⧸ U`. -/
theorem projC_comp_sectionHomR (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NR ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValueR.fib
      = 0) (g : FreeProfiniteGroup (Fin 4)) :
    (sectionHomR U hU c a htame0 hwild0 (quotientMk NR g)).base
      = QuotientGroup.mk' U.toSubgroup g := by
  haveI : DiscreteTopology (FreeProfiniteGroup (Fin 4) ⧸
      (U.toOpenSubgroup : Subgroup (FreeProfiniteGroup (Fin 4)))) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul U.toOpenSubgroup
  set t_L := univMarking.map (QuotientGroup.mk' U.toSubgroup) with ht_L
  set m := Marking.classify (shiftLiftMark t_L a c) with hm
  let projC : ContinuousMonoidHom (CentExt c) (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) :=
    ⟨CentExt.proj c, continuous_of_discreteTopology⟩
  have hut : univMarking.map m.toMonoidHom = shiftLiftMark t_L a c := by
    rw [hm, Marking.classify, univMarking_map_toHom]
  have hcomp : projC.comp m = quotientMk U.toSubgroup := by
    have e1 : univMarking.map (projC.comp m).toMonoidHom = t_L := by
      show univMarking.map ((CentExt.proj c).comp m.toMonoidHom) = t_L
      rw [← Marking.map_map, hut, shiftLiftMark_map_projR]
    have e2 : univMarking.map (quotientMk U.toSubgroup).toMonoidHom = t_L := rfl
    rw [← Marking.toHom_hom_univMarking_map (projC.comp m),
        ← Marking.toHom_hom_univMarking_map (quotientMk U.toSubgroup), e1, e2]
  show CentExt.proj c (sectionHomR U hU c a htame0 hwild0 (quotientMk NR g)) = _
  rw [sectionHomR, quotientLift_quotientMk]
  exact DFunLike.congr_fun hcomp g

/-! ## Coboundary extraction -/

section CoboundaryR

open ContCoh

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]

omit [ContinuousSMul GR (ZMod 2)] in
/-- **Coboundary extraction.**  With `𝔽₂` a trivial `Γ_R`-module, the level cocycle pulled back
through the splitting section is a continuous 2-coboundary `dOne (fib ∘ s)`.  Word-independent
given the section, so this is the verbatim `Γ_R` retyping of `WordCoh2.cocycle_mem_B2`. -/
theorem cocycle_mem_B2_R (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NR ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValueR.fib
      = 0)
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m) :
    (fun p : GR × GR =>
        c.κ (sectionHomR U hU c a htame0 hwild0 p.1).base
            (sectionHomR U hU c a htame0 hwild0 p.2).base)
      ∈ B2 GR (ZMod 2) := by
  set s := sectionHomR U hU c a htame0 hwild0 with hs
  have key : ∀ x y z : ZMod 2, y - (x + y + z) + x = z := by decide
  refine ⟨fun x => (s x).fib, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_C1_iff]
    exact (continuous_of_discreteTopology (f := CentExt.fib)).comp s.continuous_toFun
  · funext p
    obtain ⟨x, y⟩ := p
    show x • (s y).fib - (s (x * y)).fib + (s x).fib = c.κ (s x).base (s y).base
    rw [htriv, map_mul s, CentExt.mul_fib]
    exact key (s x).fib (s y).fib (c.κ (s x).base (s y).base)

end CoboundaryR

/-! ## The level projection and the injectivity keystone -/

/-- The level projection `Γ_R = F₄ ⧸ N_R ↠ F₄ ⧸ U` for `N_R ≤ U`. -/
noncomputable def levelProjR (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hU : NR ≤ U.toSubgroup) :
    ContinuousMonoidHom GR (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) :=
  quotientLift NR (quotientMk U.toSubgroup) (hU.trans_eq (QuotientGroup.ker_mk' _).symm)

@[simp] theorem levelProjR_quotientMk (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hU : NR ≤ U.toSubgroup) (g : FreeProfiniteGroup (Fin 4)) :
    levelProjR U hU (quotientMk NR g) = QuotientGroup.mk' U.toSubgroup g := rfl

section InjectivityR

open ContCoh

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]

omit [ContinuousSMul GR (ZMod 2)] in
/-- **Injectivity keystone.**  A finite-level cocycle with balanced Roe relator obstruction
inflates to a continuous 2-coboundary on `Γ_R`. -/
theorem inflated_cocycle_mem_B2_R (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NR ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hrel : (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).tameValue.fib
          = (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).wildValueR.fib)
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m) :
    (fun p : GR × GR => c.κ (levelProjR U hU p.1) (levelProjR U hU p.2)) ∈ B2 GR (ZMod 2) := by
  obtain ⟨a, htame0, hwild0⟩ :=
    exists_shiftR_of_relZ_eq (univMarking.map (QuotientGroup.mk' U.toSubgroup)) hrel
  have hbase : ∀ x : GR,
      (sectionHomR U hU c a htame0 hwild0 x).base = levelProjR U hU x := by
    intro x
    obtain ⟨g, rfl⟩ := quotientMk_surjective NR x
    rw [projC_comp_sectionHomR, levelProjR_quotientMk]
  have hfun : (fun p : GR × GR => c.κ (levelProjR U hU p.1) (levelProjR U hU p.2))
      = fun p => c.κ (sectionHomR U hU c a htame0 hwild0 p.1).base
          (sectionHomR U hU c a htame0 hwild0 p.2).base := by
    funext p; rw [hbase, hbase]
  rw [hfun]
  exact cocycle_mem_B2_R U hU c a htame0 hwild0 htriv

end InjectivityR

/-! ## Factoring a continuous cocycle through a finite level

The compactness core `WordCoh2.exists_openNormalSubgroup_factor_two` is stated for an arbitrary
profinite group, so it is reused verbatim; only the transport to `F₄ ⧸ U := comap N_R V` is
retyped. -/

section FactoringR

/-- **Factoring a normalized continuous 2-cocycle** on `Γ_R`. -/
theorem exists_twoCocycle_factor_R (κ : GR × GR → ZMod 2)
    (hκc : Continuous κ) (hκ1 : κ (1, 1) = 0)
    (hκcoc : ∀ a b c : GR, κ (a, b) + κ (a * b, c) = κ (a, b * c) + κ (b, c)) :
    ∃ (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) (hU : NR ≤ U.toSubgroup)
      (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)),
      ∀ x y : GR, κ (x, y) = c.κ (levelProjR U hU x) (levelProjR U hU y) := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two κ hκc
  have hUopen : IsOpen ((V.toSubgroup.comap (QuotientGroup.mk' NR) :
      Subgroup (FreeProfiniteGroup (Fin 4))) : Set (FreeProfiniteGroup (Fin 4))) :=
    V.toOpenSubgroup.isOpen.preimage (quotientMk NR).continuous_toFun
  haveI hUnormal : (V.toSubgroup.comap (QuotientGroup.mk' NR)).Normal :=
    V.isNormal'.comap _
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := V.toSubgroup.comap (QuotientGroup.mk' NR)
      isOpen' := hUopen }
  have hU : NR ≤ U.toSubgroup :=
    (QuotientGroup.ker_mk' NR).symm.trans_le
      (Subgroup.ker_le_comap (f := QuotientGroup.mk' NR) V.toSubgroup)
  refine ⟨U, hU, ?_, ?_⟩
  · refine
      { κ := fun p q => Quotient.liftOn₂ p q
          (fun x y => κ (QuotientGroup.mk x, QuotientGroup.mk y)) ?_
        norm := ?_
        cocyc := ?_ }
    · intro x₁ y₁ x₂ y₂ hx hy
      have hxU : x₁⁻¹ * x₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NR) :=
        QuotientGroup.leftRel_apply.mp hx
      have hyU : y₁⁻¹ * y₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NR) :=
        QuotientGroup.leftRel_apply.mp hy
      have hxv : (QuotientGroup.mk x₁ : GR)⁻¹ * QuotientGroup.mk x₂ ∈ V := by
        have h := (Subgroup.mem_comap).mp hxU
        rwa [map_mul, map_inv] at h
      have hyv : (QuotientGroup.mk y₁ : GR)⁻¹ * QuotientGroup.mk y₂ ∈ V := by
        have h := (Subgroup.mem_comap).mp hyU
        rwa [map_mul, map_inv] at h
      simpa using (hV (QuotientGroup.mk x₁) (QuotientGroup.mk y₁) _ hxv _ hyv).symm
    · show κ (QuotientGroup.mk 1, QuotientGroup.mk 1) = 0
      rw [QuotientGroup.mk_one]; exact hκ1
    · intro a b c
      induction a using QuotientGroup.induction_on with | H x =>
      induction b using QuotientGroup.induction_on with | H y =>
      induction c using QuotientGroup.induction_on with | H z =>
      show κ (QuotientGroup.mk x, QuotientGroup.mk y)
            + κ (QuotientGroup.mk (x * y), QuotientGroup.mk z)
          = κ (QuotientGroup.mk x, QuotientGroup.mk (y * z))
            + κ (QuotientGroup.mk y, QuotientGroup.mk z)
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hκcoc _ _ _
  · intro x y
    induction x using QuotientGroup.induction_on with | H a =>
    induction y using QuotientGroup.induction_on with | H b =>
    rfl

/-- **Factoring a continuous 1-cochain** on `Γ_R`. -/
theorem exists_oneCochain_factor_R (ψ : GR → ZMod 2) (hψc : Continuous ψ) :
    ∃ (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) (hU : NR ≤ U.toSubgroup)
      (lam : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup → ZMod 2),
      ∀ x : GR, ψ x = lam (levelProjR U hU x) := by
  haveI : IsClosed (NR : Set (FreeProfiniteGroup (Fin 4))) := NR_isClosed
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two
    (fun p => ψ p.1) (hψc.comp continuous_fst)
  have hUopen : IsOpen ((V.toSubgroup.comap (QuotientGroup.mk' NR) :
      Subgroup (FreeProfiniteGroup (Fin 4))) : Set (FreeProfiniteGroup (Fin 4))) :=
    V.toOpenSubgroup.isOpen.preimage (quotientMk NR).continuous_toFun
  haveI hUnormal : (V.toSubgroup.comap (QuotientGroup.mk' NR)).Normal :=
    V.isNormal'.comap _
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := V.toSubgroup.comap (QuotientGroup.mk' NR)
      isOpen' := hUopen }
  have hU : NR ≤ U.toSubgroup :=
    (QuotientGroup.ker_mk' NR).symm.trans_le
      (Subgroup.ker_le_comap (f := QuotientGroup.mk' NR) V.toSubgroup)
  refine ⟨U, hU, fun p => Quotient.liftOn p (fun x => ψ (QuotientGroup.mk x)) ?_, ?_⟩
  · intro x₁ x₂ hx
    have hxU : x₁⁻¹ * x₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NR) :=
      QuotientGroup.leftRel_apply.mp hx
    have hxv : (QuotientGroup.mk x₁ : GR)⁻¹ * QuotientGroup.mk x₂ ∈ V := by
      have h := (Subgroup.mem_comap).mp hxU
      rwa [map_mul, map_inv] at h
    simpa using (hV (QuotientGroup.mk x₁) (QuotientGroup.mk x₁) _ hxv 1 (one_mem _)).symm
  · intro x
    induction x using QuotientGroup.induction_on with | H a =>
    rfl

end FactoringR

/-! ## Injectivity, assembled -/

section AssemblyR

open ContCoh

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]

omit [ContinuousSMul GR (ZMod 2)] in
/-- **Injectivity, consumable form.**  A continuous cochain factoring through a finite level whose
Roe relator obstruction is balanced is a continuous 2-coboundary. -/
theorem mem_B2_of_factor_balanced_R (κ : GR × GR → ZMod 2)
    (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
    (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NR ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hfact : ∀ x y : GR, κ (x, y) = c.κ (levelProjR U hU x) (levelProjR U hU y))
    (hbal : (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).tameValue.fib
          = (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).wildValueR.fib) :
    κ ∈ B2 GR (ZMod 2) := by
  have heq : κ = fun p => c.κ (levelProjR U hU p.1) (levelProjR U hU p.2) := by
    funext p; exact hfact p.1 p.2
  rw [heq]
  exact inflated_cocycle_mem_B2_R U hU c hbal htriv

end AssemblyR

/-! ## The obstruction map and `#H²(Γ_R, 𝔽₂) ≤ 2` -/

section CardBoundR

open ContCoh

/-- A factorization of a `Γ_R`-cochain `κ` through a finite `R`-admissible level. -/
structure LevelFactorR (κ : GR × GR → ZMod 2) where
  /-- The finite `R`-admissible level `F₄ ⧸ U`. -/
  U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))
  /-- `N_R ≤ U`, so `Γ_R = F₄ ⧸ N_R ↠ F₄ ⧸ U`. -/
  hU : NR ≤ U.toSubgroup
  /-- The finite-level 2-cocycle whose inflation is `κ`. -/
  c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)
  /-- `κ` is the inflation of `c` along `levelProjR`. -/
  hfact : ∀ x y, κ (x, y) = c.κ (levelProjR U hU x) (levelProjR U hU y)

/-- The Roe relator obstruction of a factorization: the sum of the tame and Roe wild relator
fibre-`z` values of the finite-level cocycle. -/
noncomputable def LevelFactorR.obs {κ : GR × GR → ZMod 2} (F : LevelFactorR κ) : ZMod 2 :=
  (relZPairR (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).1
    + (relZPairR (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).2

/-- **Level-independence.**  `F.obs` may be computed at any finer level `W` (`relZPairR_comap`). -/
theorem LevelFactorR.obs_eq_comap {κ : GR × GR → ZMod 2}
    (F : LevelFactorR κ) (W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (proj : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
          →* (FreeProfiniteGroup (Fin 4) ⧸ F.U.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' F.U.toSubgroup) :
    F.obs = (relZPairR (univMarking.map (QuotientGroup.mk' W.toSubgroup)) (F.c.comap proj)).1
          + (relZPairR (univMarking.map (QuotientGroup.mk' W.toSubgroup)) (F.c.comap proj)).2 := by
  have htU : univMarking.map (QuotientGroup.mk' F.U.toSubgroup)
           = (univMarking.map (QuotientGroup.mk' W.toSubgroup)).map proj := by
    rw [Marking.map_map, hproj]
  unfold LevelFactorR.obs
  rw [htU, relZPairR_comap]

/-- **Well-definedness.**  `F.obs` depends only on `κ`, not on the chosen factorization. -/
theorem LevelFactorR.obs_congr {κ : GR × GR → ZMod 2} (F₁ F₂ : LevelFactorR κ) :
    F₁.obs = F₂.obs := by
  set W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) := F₁.U ⊓ F₂.U with hWdef
  have hW1 : W.toSubgroup ≤ F₁.U.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have hW2 : W.toSubgroup ≤ F₂.U.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  set p1 : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
        →* (FreeProfiniteGroup (Fin 4) ⧸ F₁.U.toSubgroup) :=
    QuotientGroup.map W.toSubgroup F₁.U.toSubgroup (MonoidHom.id _)
      (by rw [Subgroup.comap_id]; exact hW1) with hp1def
  set p2 : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
        →* (FreeProfiniteGroup (Fin 4) ⧸ F₂.U.toSubgroup) :=
    QuotientGroup.map W.toSubgroup F₂.U.toSubgroup (MonoidHom.id _)
      (by rw [Subgroup.comap_id]; exact hW2) with hp2def
  have hp1 : p1.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' F₁.U.toSubgroup := by
    ext g; rw [hp1def, MonoidHom.comp_apply, QuotientGroup.map_mk']; rfl
  have hp2 : p2.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' F₂.U.toSubgroup := by
    ext g; rw [hp2def, MonoidHom.comp_apply, QuotientGroup.map_mk']; rfl
  rw [F₁.obs_eq_comap W p1 hp1, F₂.obs_eq_comap W p2 hp2]
  have hcc : F₁.c.comap p1 = F₂.c.comap p2 := by
    apply TwoCocycle.ext
    funext a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W.toSubgroup a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective W.toSubgroup b
    have e1g : p1 (QuotientGroup.mk' W.toSubgroup g) = QuotientGroup.mk' F₁.U.toSubgroup g := by
      rw [← MonoidHom.comp_apply, hp1]
    have e1h : p1 (QuotientGroup.mk' W.toSubgroup h) = QuotientGroup.mk' F₁.U.toSubgroup h := by
      rw [← MonoidHom.comp_apply, hp1]
    have e2g : p2 (QuotientGroup.mk' W.toSubgroup g) = QuotientGroup.mk' F₂.U.toSubgroup g := by
      rw [← MonoidHom.comp_apply, hp2]
    have e2h : p2 (QuotientGroup.mk' W.toSubgroup h) = QuotientGroup.mk' F₂.U.toSubgroup h := by
      rw [← MonoidHom.comp_apply, hp2]
    have hf1 : κ (quotientMk NR g, quotientMk NR h)
        = F₁.c.κ (QuotientGroup.mk' F₁.U.toSubgroup g) (QuotientGroup.mk' F₁.U.toSubgroup h) :=
      F₁.hfact (quotientMk NR g) (quotientMk NR h)
    have hf2 : κ (quotientMk NR g, quotientMk NR h)
        = F₂.c.κ (QuotientGroup.mk' F₂.U.toSubgroup g) (QuotientGroup.mk' F₂.U.toSubgroup h) :=
      F₂.hfact (quotientMk NR g) (quotientMk NR h)
    rw [TwoCocycle.comap_κ, TwoCocycle.comap_κ, e1g, e1h, e2g, e2h, ← hf1, ← hf2]
  rw [hcc]

/-- The two projections `F₄ ⧸ W → F₄ ⧸ U` (for `N_R ≤ W ≤ U`) and the level maps compose. -/
theorem levelProjR_comp (W U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hUW : NR ≤ W.toSubgroup) (hU : NR ≤ U.toSubgroup)
    (proj : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
          →* (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' U.toSubgroup)
    (x : GR) : proj (levelProjR W hUW x) = levelProjR U hU x := by
  obtain ⟨g, rfl⟩ := quotientMk_surjective NR x
  show proj (QuotientGroup.mk' W.toSubgroup g) = QuotientGroup.mk' U.toSubgroup g
  rw [← MonoidHom.comp_apply, hproj]

/-- Normalize a 2-cochain at `(1,1)` by subtracting the (coboundary) constant `κ (1,1)`. -/
noncomputable def normalizeCochainR (κ : GR × GR → ZMod 2) : GR × GR → ZMod 2 :=
  κ - fun _ => κ (1, 1)

private theorem normalizeCochainR_add (κ κ' : GR × GR → ZMod 2) :
    normalizeCochainR (κ + κ') = normalizeCochainR κ + normalizeCochainR κ' := by
  funext p; simp only [normalizeCochainR, Pi.add_apply, Pi.sub_apply]; abel

variable [DistribMulAction GR (ZMod 2)] [ContinuousSMul GR (ZMod 2)]
variable (htriv : ∀ (x : GR) (m : ZMod 2), x • m = m)
include htriv

omit [ContinuousSMul GR (ZMod 2)] in
/-- Under the trivial action, a constant 2-cochain is a continuous coboundary. -/
theorem const2_mem_B2_R (v : ZMod 2) :
    (fun _ : GR × GR => v) ∈ B2 GR (ZMod 2) := by
  rw [B2, AddSubgroup.mem_map]
  refine ⟨fun _ => v, continuous_const, ?_⟩
  funext p
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, htriv]
  abel

omit [ContinuousSMul GR (ZMod 2)] in
/-- The normalization of a continuous 2-cocycle factors through a finite `R`-admissible level. -/
theorem nonempty_levelFactorR_normalize (φ : Z2 GR (ZMod 2)) :
    Nonempty (LevelFactorR (normalizeCochainR φ.1)) := by
  have hφcont : Continuous φ.1 := (mem_Z2_iff.mp φ.2).1
  have hφcoc := (mem_Z2_iff.mp φ.2).2
  have hcont : Continuous (normalizeCochainR φ.1) := hφcont.sub continuous_const
  have hnorm : normalizeCochainR φ.1 (1, 1) = 0 := by
    simp only [normalizeCochainR, Pi.sub_apply, sub_self]
  have hcoc : ∀ a b c, normalizeCochainR φ.1 (a, b) + normalizeCochainR φ.1 (a * b, c)
      = normalizeCochainR φ.1 (a, b * c) + normalizeCochainR φ.1 (b, c) := by
    intro a b c
    have hz := hφcoc a b c
    rw [htriv] at hz
    simp only [normalizeCochainR, Pi.sub_apply]
    linear_combination -hz
  obtain ⟨U, hU, c, hfact⟩ := exists_twoCocycle_factor_R (normalizeCochainR φ.1) hcont hnorm hcoc
  exact ⟨U, hU, c, hfact⟩

/-- The per-cocycle Roe obstruction: the relator obstruction of any factorization of the
normalization. -/
noncomputable def obsFun_R (φ : Z2 GR (ZMod 2)) : ZMod 2 :=
  (nonempty_levelFactorR_normalize htriv φ).some.obs

omit [ContinuousSMul GR (ZMod 2)] in
/-- `obsFun_R` may be computed at *any* factorization of the normalization. -/
theorem obsFun_eq_R (φ : Z2 GR (ZMod 2)) (F : LevelFactorR (normalizeCochainR φ.1)) :
    obsFun_R htriv φ = F.obs :=
  LevelFactorR.obs_congr _ F

omit [ContinuousSMul GR (ZMod 2)] in
/-- **Additivity of the Roe obstruction.**  Both `φ` and `ψ` factor through a common refinement
`W = U_φ ⊓ U_ψ`, where their finite-level cocycles pull back and *add* (`relZPairR_add`). -/
theorem obsFun_add_R (φ ψ : Z2 GR (ZMod 2)) :
    obsFun_R htriv (φ + ψ) = obsFun_R htriv φ + obsFun_R htriv ψ := by
  set Fφ := (nonempty_levelFactorR_normalize htriv φ).some with hFφ
  set Fψ := (nonempty_levelFactorR_normalize htriv ψ).some with hFψ
  set W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) := Fφ.U ⊓ Fψ.U with hWdef
  have hUW : NR ≤ W.toSubgroup := le_inf Fφ.hU Fψ.hU
  have hW1 : W.toSubgroup ≤ Fφ.U.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have hW2 : W.toSubgroup ≤ Fψ.U.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  set pφ : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
        →* (FreeProfiniteGroup (Fin 4) ⧸ Fφ.U.toSubgroup) :=
    QuotientGroup.map W.toSubgroup Fφ.U.toSubgroup (MonoidHom.id _)
      (by rw [Subgroup.comap_id]; exact hW1) with hpφdef
  set pψ : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
        →* (FreeProfiniteGroup (Fin 4) ⧸ Fψ.U.toSubgroup) :=
    QuotientGroup.map W.toSubgroup Fψ.U.toSubgroup (MonoidHom.id _)
      (by rw [Subgroup.comap_id]; exact hW2) with hpψdef
  have hpφ : pφ.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' Fφ.U.toSubgroup := by
    ext g; rw [hpφdef, MonoidHom.comp_apply, QuotientGroup.map_mk']; rfl
  have hpψ : pψ.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' Fψ.U.toSubgroup := by
    ext g; rw [hpψdef, MonoidHom.comp_apply, QuotientGroup.map_mk']; rfl
  have hFsum : obsFun_R htriv (φ + ψ)
      = (relZPairR (univMarking.map (QuotientGroup.mk' W.toSubgroup))
          (Fφ.c.comap pφ + Fψ.c.comap pψ)).1
      + (relZPairR (univMarking.map (QuotientGroup.mk' W.toSubgroup))
          (Fφ.c.comap pφ + Fψ.c.comap pψ)).2 := by
    refine obsFun_eq_R htriv (φ + ψ) ⟨W, hUW, Fφ.c.comap pφ + Fψ.c.comap pψ, ?_⟩
    intro x y
    rw [add_κR, TwoCocycle.comap_κ, TwoCocycle.comap_κ,
      levelProjR_comp W Fφ.U hUW Fφ.hU pφ hpφ x, levelProjR_comp W Fφ.U hUW Fφ.hU pφ hpφ y,
      levelProjR_comp W Fψ.U hUW Fψ.hU pψ hpψ x, levelProjR_comp W Fψ.U hUW Fψ.hU pψ hpψ y,
      ← Fφ.hfact x y, ← Fψ.hfact x y]
    show normalizeCochainR (φ.1 + ψ.1) (x, y)
        = normalizeCochainR φ.1 (x, y) + normalizeCochainR ψ.1 (x, y)
    rw [normalizeCochainR_add, Pi.add_apply]
  rw [obsFun_eq_R htriv φ Fφ, obsFun_eq_R htriv ψ Fψ, hFsum,
    Fφ.obs_eq_comap W pφ hpφ, Fψ.obs_eq_comap W pψ hpψ, relZPairR_add, Prod.fst_add, Prod.snd_add]
  abel

/-- The **Roe obstruction homomorphism** `Z²_cont(Γ_R, 𝔽₂) →+ 𝔽₂`. -/
noncomputable def obs_R : Z2 GR (ZMod 2) →+ ZMod 2 :=
  AddMonoidHom.mk' (obsFun_R htriv) (obsFun_add_R htriv)

omit [ContinuousSMul GR (ZMod 2)] in
/-- The kernel of the Roe obstruction lands in the 2-coboundaries. -/
theorem obs_ker_le_R :
    (obs_R htriv).ker ≤ (B2 GR (ZMod 2)).addSubgroupOf (Z2 GR (ZMod 2)) := by
  intro φ hφ
  rw [AddMonoidHom.mem_ker] at hφ
  rw [AddSubgroup.mem_addSubgroupOf]
  set F := (nonempty_levelFactorR_normalize htriv φ).some with hF
  have hobs0 : F.obs = 0 := by rw [← obsFun_eq_R htriv φ F]; exact hφ
  have hbal : (liftMark (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).tameValue.fib
      = (liftMark (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).wildValueR.fib :=
    CharTwo.add_eq_zero.mp hobs0
  have hnB2 : normalizeCochainR φ.1 ∈ B2 GR (ZMod 2) :=
    mem_B2_of_factor_balanced_R (normalizeCochainR φ.1) htriv F.U F.hU F.c F.hfact hbal
  have hconst : φ.1 = normalizeCochainR φ.1 + fun _ => φ.1 (1, 1) := by
    funext p; simp only [normalizeCochainR, Pi.sub_apply, Pi.add_apply]; abel
  rw [hconst]
  exact AddSubgroup.add_mem _ hnB2 (const2_mem_B2_R htriv (φ.1 (1, 1)))

omit [ContinuousSMul GR (ZMod 2)] in
/-- **`obs_R` kills `B²`.**  A continuous coboundary normalizes to `δ¹ψ'` (`ψ' 1 = 0`), which
factors through a finite `R`-admissible level as `coboundaryCocycle λ`; its obstruction is
`λ(tameValue) + λ(wildValueR) = λ 1 + λ 1 = 0` since both `Γ_R` relators die at that level
(`isAdmissibleUR_of_NR_le`). -/
theorem obs_B2_eq_zero_R :
    (B2 GR (ZMod 2)).addSubgroupOf (Z2 GR (ZMod 2)) ≤ (obs_R htriv).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  rw [AddSubgroup.mem_addSubgroupOf, B2, AddSubgroup.mem_map] at hx
  obtain ⟨ψ, hψc, hψeq⟩ := hx
  have hψcont : Continuous ψ := mem_C1_iff.mp hψc
  have hx1 : x.1 = dOne GR (ZMod 2) ψ := hψeq.symm
  set ψ' : GR → ZMod 2 := ψ - fun _ => ψ 1 with hψ'def
  obtain ⟨U, hU, lam, hlamfact⟩ := exists_oneCochain_factor_R ψ' (hψcont.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlamfact 1
    rw [show levelProjR U hU 1 = 1 from map_one _] at h
    rw [← h]; simp [hψ'def]
  have hfact : ∀ p q, normalizeCochainR x.1 (p, q)
      = (coboundaryCocycle lam hlam1).κ (levelProjR U hU p) (levelProjR U hU q) := by
    intro p q
    show normalizeCochainR x.1 (p, q)
      = lam (levelProjR U hU p) + lam (levelProjR U hU q)
        + lam (levelProjR U hU p * levelProjR U hU q)
    rw [← map_mul (levelProjR U hU) p q, ← hlamfact p, ← hlamfact q, ← hlamfact (p * q), hx1]
    simp only [normalizeCochainR, Pi.sub_apply, hψ'def, dOne, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, htriv, mul_one, CharTwo.sub_eq_add]
    abel
  have hobs : obsFun_R htriv x = 0 := by
    rw [obsFun_eq_R htriv x ⟨U, hU, coboundaryCocycle lam hlam1, hfact⟩]
    show (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        (coboundaryCocycle lam hlam1)).1
      + (relZPairR (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        (coboundaryCocycle lam hlam1)).2 = 0
    rw [obs_coboundaryR_eq]
    have hadmU : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).AdmissibleR :=
      isAdmissibleUR_of_NR_le hU
    rw [(Marking.tameValue_eq_one_iff _).mpr hadmU.2.1,
      (Marking.wildValueR_eq_one_iff _).mpr hadmU.2.2.1, hlam1, add_zero]
  exact hobs

omit [ContinuousSMul GR (ZMod 2)] in
/-- **`ker obs_R = B²`.**  The Roe obstruction is trivial on coboundaries and nowhere else, so it
descends to an *injection* `H²(Γ_R, 𝔽₂) ↪ 𝔽₂`. -/
theorem obs_ker_eq_B2_R :
    (obs_R htriv).ker = (B2 GR (ZMod 2)).addSubgroupOf (Z2 GR (ZMod 2)) :=
  le_antisymm (obs_ker_le_R htriv) (obs_B2_eq_zero_R htriv)

/-- The **descended Roe obstruction** `H²(Γ_R, 𝔽₂) →+ 𝔽₂`. -/
noncomputable def obsH2_R : H2 GR (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift _ (obs_R htriv) (fun _ h => obs_B2_eq_zero_R htriv h)

omit [ContinuousSMul GR (ZMod 2)] in
/-- **`#H²(Γ_R, 𝔽₂) ≤ 2`**: a continuous 2-cocycle whose Roe obstruction is nonzero is *not* a
coboundary.  The degree-2 presentation comparison for `Γ_R`. -/
theorem obsH2_R_injective : Function.Injective (obsH2_R htriv) := by
  rw [injective_iff_map_eq_zero]
  intro a
  induction a using QuotientAddGroup.induction_on with | H φ =>
  intro ha
  exact (QuotientAddGroup.eq_zero_iff φ).mpr (obs_ker_le_R htriv (AddMonoidHom.mem_ker.mpr ha))

end CardBoundR

end WordCoh2R

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.2) = ⟦eq:relators⟧ — the Roe wild relator, read off the central extension by
    `relZPairR`; its death at every `R`-admissible level is what makes `obs_R` kill `B²`.
  * Definition 1.1 = ⟦def:GammaR⟧ — `IsAdmissibleUR`/`N_R`, via `NR_le_ker_shiftLiftR`.
-/
