/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.WordCohBridge
import GQ2.Roe.FoxBasic
import GQ2.Roe.Prop23
import GQ2.Roe.Tame

/-!
# The `Γ_R` degree-≤1 presentation comparison

The Roe-candidate twin of `GQ2/WordCohBridge.lean`: for a finite discrete `C`-module `A` and a
continuous surjection `q : Γ_R ↠ C`, the continuous `H¹` of `Γ_R` (with `A` a `Γ_R`-module through
`q`) is computed by the **Roe word complex** `Z1wR`/`H1wR` (`GQ2/Roe/FoxBasic.lean`) of the pushed
marking `t_q = markC_R q`:

  `z1EquivR : ContCoh.Z1 Γ_R A ≃+ Z1wR (markC_R q)`   (evaluation at the four marked generators),

descending to `h1EquivR : ContCoh.H1 Γ_R A ≃+ H1wR (markC_R q)`.  This is the substrate the whole
`Γ_R` supply lane (tickets R31c–R31g) is stated against — the `Γ_R` replacement for B6/Tate duality,
through which the word-complex self-duality `prop_5_15_R` transports to `H¹(Γ_R)`.

**What is new and what is inherited.**  The entire argument is relator-agnostic *except* one step:
the wild relator of `Γ_R` is `r_R = (x₀^σ)⁻¹ · a · x₁² · c` (note eq. (1.2) ⟦eq:relators⟧,
`Marking.wildValueR`), not `Γ_A`'s `r_A`, so the two "wild relator dies" lemmas
(`liftMarking_evalR_wildRelR`, `liftMarking_Z1wR_wildRelR`) are re-derived from
`wildRelatorR_mem_NR` (`GQ2/Roe/AdmissibleLimit.lean`) and `Marking.map_wildRelatorR_eq_one_iff`
(`GQ2/Roe/GammaR.lean`).  Everything genuinely word-independent is **imported from the `Γ_A` file
and reused verbatim**, never re-defined: the base projection `WordCohBridge.gHom`/`gHomC`, the
elementary-2 kernel `WordCohBridge.isPGroup_gHom_ker`, the `Pro2Core` crux
`WordCohBridge.isPGroup_liftMarking_wildCore`, and `WordCohBridge.liftMarking_map_gHom` — together
with the discrete `WordLift` topology instances registered there.  Likewise `markC_R` /
`markC_admissible_R` are consumed from `GQ2/Roe/Prop23.lean`, not re-proved.

**Level.**  As on the `Γ_A` side, this file is built over the raw quotient
`GR := FreeProfiniteGroup (Fin 4) ⧸ N_R` (defeq to the bundled `GammaR`,
`RStageGammaR.gammaR_eq_quotient`), because all the marking machinery
(`quotientMk`/`quotientLift`/`Marking.pushR`/`Marking.descendR`) lives over the raw quotient and
`q.comp (quotientMk NR)` must unify.

The spine: a continuous crossed cocycle `z : GR → A` (for the `q`-conjugation action) is exactly the
`.u`-component of a continuous hom `φ_z : GR → WordLift A C = A ⋊ C` lifting `q` (`(φ_z γ).g = q γ`).
Evaluating `φ_z` at the generators lands in `Z1wR` because both `Γ_R` relators die in `GR`;
conversely a Roe word cocycle `x ∈ Z1wR` gives an `R`-admissible marking of `WordLift`, which
descends to the hom, whose `.u`-component is the cocycle.
-/

namespace GQ2

open ContCoh FoxH

namespace WordCohBridgeR

/-- The raw quotient `Γ_R = F₄ ⧸ N_R` (defeq to `GammaR` by `RStageGammaR.gammaR_eq_quotient`, but
with the `QuotientGroup` instances the marking machinery is stated against). -/
abbrev GR : Type := FreeProfiniteGroup (Fin 4) ⧸ NR

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A]
  [DistribMulAction GR A] [ContinuousSMul GR A]

variable (q : ContinuousMonoidHom GR C)
  (hcompat : ∀ (γ : GR) (a : A), γ • a = q γ • a)

/-- The `WordLift A C = A ⋊ C` hom `γ ↦ ⟨z γ, q γ⟩` attached to a continuous crossed cocycle `z`.
The cocycle identity `z(γδ) = z γ + q γ • z δ` is exactly the `WordLift` product law on the
`.u`-slot.  Word-independent — the verbatim `Γ_R` retyping of `WordCohBridge.wordHom`. -/
noncomputable def wordHomR (z : Z1 GR A) : ContinuousMonoidHom GR (WordLift A C) where
  toFun γ := ⟨z.1 γ, q γ⟩
  map_one' := by
    ext
    · show z.1 1 = 0; exact Z1_apply_one z
    · show q 1 = 1; exact map_one q
  map_mul' γ δ := by
    have hz := (mem_Z1_iff.mp z.2).2 γ δ
    ext
    · show z.1 (γ * δ) = z.1 γ + q γ • z.1 δ
      rw [hz, hcompat]
    · show q (γ * δ) = q γ * q δ; exact map_mul q _ _
  continuous_toFun := by
    show Continuous (fun γ => (⟨z.1 γ, q γ⟩ : WordLift A C))
    have hg : Continuous (fun γ : GR => ((z.1 γ, q γ) : A × C)) :=
      ((mem_Z1_iff.mp z.2).1).prodMk q.continuous_toFun
    exact (continuous_of_discreteTopology
      (f := (WordLift.equivProd (A := A) (C := C)).symm)).comp hg

/-! ## The canonical marking of `Γ_R`

Only the four *scalars* `gammaSigmaR`/`gammaTauR`/`gammaX0R`/`gammaX1R` exist (`GQ2/Roe/Tame.lean`);
`gammaGenR` bundles them into a `Marking GR`, which is the form `evalR` and the L4/L5 cover-lift
kernel (ticket R31e) consume. -/

/-- The canonical marking of `Γ_R` by the images of the four free generators — the `Γ_R` twin of
`WordCohBridge.gammaGen`, and the bundled form of `gammaSigmaR`/`gammaTauR`/`gammaX0R`/`gammaX1R`
(`GQ2/Roe/Tame.lean`). -/
noncomputable def gammaGenR : Marking GR := univMarking.map (quotientMk NR).toMonoidHom

/-- **Sanity 1/4.**  `gammaGenR.σ` is the banked scalar `gammaSigmaR`. -/
@[simp] theorem gammaGenR_σ : gammaGenR.σ = gammaSigmaR := rfl

/-- **Sanity 2/4.**  `gammaGenR.τ` is the banked scalar `gammaTauR`. -/
@[simp] theorem gammaGenR_τ : gammaGenR.τ = gammaTauR := rfl

/-- **Sanity 3/4.**  `gammaGenR.x₀` is the banked scalar `gammaX0R`. -/
@[simp] theorem gammaGenR_x₀ : gammaGenR.x₀ = gammaX0R := rfl

/-- **Sanity 4/4.**  `gammaGenR.x₁` is the banked scalar `gammaX1R`. -/
@[simp] theorem gammaGenR_x₁ : gammaGenR.x₁ = gammaX1R := rfl

omit [DiscreteTopology C] [Finite C] in
/-- `t_q = q ∘ (canonical Γ_R-marking)` on each generator (the `Marking.map_map` collapse) — the
`Γ_R` twin of `WordCohBridge.markC_map`. -/
theorem markC_R_map : markC_R q = gammaGenR.map q.toMonoidHom := by
  show Marking.pushR q = (univMarking.map (quotientMk NR).toMonoidHom).map q.toMonoidHom
  rw [Marking.pushR, Marking.map_map]
  rfl

/-- Evaluation of a continuous crossed cocycle at the four marked generators of `Γ_R`. -/
noncomputable def evalR (z : Z1 GR A) : Fin 4 → A :=
  ![z.1 gammaGenR.σ, z.1 gammaGenR.τ, z.1 gammaGenR.x₀, z.1 gammaGenR.x₁]

omit [Finite A] [ContinuousSMul GR A] [Finite C] in
/-- The lifted marking at `evalR z` is the pushforward of `wordHomR` along the canonical marking —
the identity underlying "`evalR` lands in `Z1wR`". -/
theorem liftMarking_evalR (z : Z1 GR A) :
    liftMarking (markC_R q) (evalR z) = gammaGenR.map (wordHomR q hcompat z).toMonoidHom := by
  rw [markC_R_map]
  refine Marking.mk.injEq .. ▸ ⟨?_, ?_, ?_, ?_⟩ <;>
    · apply WordLift.ext <;> rfl

omit [Finite A] [ContinuousSMul GR A] [Finite C] in
/-- The lifted marking at `evalR z`, rewritten as the pushforward of the universal marking along
`φ_z ∘ quotientMk : F₄ → WordLift` — the form the relator-death lemmas consume. -/
theorem liftMarking_evalR_univ (z : Z1 GR A) :
    liftMarking (markC_R q) (evalR z)
      = univMarking.map ((wordHomR q hcompat z).comp (quotientMk NR)).toMonoidHom := by
  rw [liftMarking_evalR]
  show (univMarking.map (quotientMk NR).toMonoidHom).map (wordHomR q hcompat z).toMonoidHom = _
  rw [Marking.map_map]
  rfl

omit [Finite A] [ContinuousSMul GR A] [Finite C] in
include hcompat in
/-- The tame relation holds for the lifted marking at `evalR z` (the tame relator — **shared** with
`Γ_A` — dies in `Γ_R`, `tameRelator_mem_NR`). -/
theorem liftMarking_evalR_tameRel (z : Z1 GR A) :
    (liftMarking (markC_R q) (evalR z)).TameRel := by
  rw [liftMarking_evalR_univ q hcompat z, ← Marking.map_tameRelator_eq_one_iff]
  show (wordHomR q hcompat z) (quotientMk NR univMarking.tameRelator) = 1
  rw [(quotientMk_eq_one_iff NR).mpr tameRelator_mem_NR, map_one]

omit [ContinuousSMul GR A] in
include hcompat in
/-- **The one genuinely new ingredient.**  The *Roe* wild relation holds for the lifted marking at
`evalR z`: the Roe wild relator word `r_R` dies in `Γ_R` (`wildRelatorR_mem_NR`,
`GQ2/Roe/AdmissibleLimit.lean`), and dying profinitely is the same as `WildRelR` of the pushed
marking (`Marking.map_wildRelatorR_eq_one_iff`, `GQ2/Roe/GammaR.lean`).  This is the sole place
where the `Γ_A` proof of `WordCohBridge.liftMarking_eval_wildRel` does not transfer. -/
theorem liftMarking_evalR_wildRelR (z : Z1 GR A) :
    (liftMarking (markC_R q) (evalR z)).WildRelR := by
  rw [liftMarking_evalR_univ q hcompat z, ← Marking.map_wildRelatorR_eq_one_iff]
  show (wordHomR q hcompat z) (quotientMk NR univMarking.wildRelatorR) = 1
  rw [(quotientMk_eq_one_iff NR).mpr wildRelatorR_mem_NR, map_one]

include hcompat in
omit [ContinuousSMul GR A] in
/-- **Forward: `evalR` lands in `Z1wR`.** The evaluation of a continuous crossed cocycle at the four
generators is a *Roe* word cocycle, because both `Γ_R` relators die in `Γ_R`. -/
theorem eval_mem_Z1wR (z : Z1 GR A) : evalR z ∈ Z1wR (markC_R q) := by
  have ht : (liftMarking (markC_R q) (evalR z)).tameValue = 1 :=
    (Marking.tameValue_eq_one_iff _).mpr (liftMarking_evalR_tameRel q hcompat z)
  have hw : (liftMarking (markC_R q) (evalR z)).wildValueR = 1 :=
    (Marking.wildValueR_eq_one_iff _).mpr (liftMarking_evalR_wildRelR q hcompat z)
  show d1FunR (markC_R q) (evalR z) = 0
  rw [d1FunR, ht, hw]
  rfl

omit [Finite A] [ContinuousSMul GR A] in
/-- `evalR` is additive (it is pointwise evaluation of the additive `z.1`). -/
theorem evalR_add (z z' : Z1 GR A) : evalR (z + z') = evalR z + evalR z' := by
  funext i
  fin_cases i <;> rfl

include hcompat in
/-- The forward map `Z1(Γ_R, A) →+ Z1wR t_q` (evaluation at the four marked generators), bundled
additively. -/
noncomputable def toZ1wRHom : Z1 GR A →+ Z1wR (A := A) (markC_R q) :=
  AddMonoidHom.mk'
    (fun z => ⟨evalR z, eval_mem_Z1wR q hcompat z⟩)
    (fun z z' => Subtype.ext (evalR_add z z'))

omit [ContinuousSMul GR A] in
@[simp] theorem toZ1wRHom_coe (z : Z1 GR A) :
    (toZ1wRHom q hcompat z : Fin 4 → A) = evalR z := rfl

/-! ## The backward direction

`WordCohBridge.gHom` (the base projection `WordLift A C →* C`), `isPGroup_gHom_ker`,
`isPGroup_liftMarking_wildCore` (the `Pro2Core` crux) and `liftMarking_map_gHom` are all
relator-independent, so they are **imported and reused**, not cloned. -/

omit [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction GR A] [ContinuousSMul GR A] in
/-- For a Roe word cocycle `x ∈ Z1wR`, the lifted marking satisfies the tame relation: the `.u`-slot
dies because `x` is a cocycle, the `.g`-slot because `t_q` is `R`-admissible. -/
theorem liftMarking_Z1wR_tameRel (hq : Function.Surjective q) (x : Z1wR (A := A) (markC_R q)) :
    (liftMarking (markC_R q) x.1).TameRel := by
  have h0 : d1FunR (markC_R q) x.1 = 0 := AddMonoidHom.mem_ker.mp x.2
  have hu : (liftMarking (markC_R q) x.1).tameValue.u = 0 := (Prod.ext_iff.mp h0).1
  have hg : (liftMarking (markC_R q) x.1).tameValue.g = (markC_R q).tameValue := by
    have h := Marking.map_tameValue (WordCohBridge.gHom (A := A) (C := C))
      (liftMarking (markC_R q) x.1)
    rw [WordCohBridge.liftMarking_map_gHom] at h
    exact h.symm
  rw [← Marking.tameValue_eq_one_iff]
  refine WordLift.ext (by rw [hu]; rfl) ?_
  rw [hg, (Marking.tameValue_eq_one_iff _).mpr (markC_admissible_R q hq).2.1]
  rfl

omit [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction GR A] [ContinuousSMul GR A] in
/-- For a Roe word cocycle `x ∈ Z1wR`, the lifted marking satisfies the **Roe** wild relation — the
`Z1wR`-side twin of `WordCohBridge.liftMarking_Z1w_wildRel`, re-derived at `Marking.wildValueR`
(naturality `Marking.map_wildValueR`, `GQ2/Roe/Words.lean`) and `markC_admissible_R`'s `.2.2.1`
clause (which is `WildRelR`, pinned by `markC_admissible_R_clauses`). -/
theorem liftMarking_Z1wR_wildRelR (hq : Function.Surjective q) (x : Z1wR (A := A) (markC_R q)) :
    (liftMarking (markC_R q) x.1).WildRelR := by
  have h0 : d1FunR (markC_R q) x.1 = 0 := AddMonoidHom.mem_ker.mp x.2
  have hu : (liftMarking (markC_R q) x.1).wildValueR.u = 0 := (Prod.ext_iff.mp h0).2
  have hg : (liftMarking (markC_R q) x.1).wildValueR.g = (markC_R q).wildValueR := by
    have h := Marking.map_wildValueR (WordCohBridge.gHom (A := A) (C := C))
      (liftMarking (markC_R q) x.1)
    rw [WordCohBridge.liftMarking_map_gHom] at h
    exact h.symm
  rw [← Marking.wildValueR_eq_one_iff]
  refine WordLift.ext (by rw [hu]; rfl) ?_
  rw [hg, (Marking.wildValueR_eq_one_iff _).mpr (markC_admissible_R q hq).2.2.1]
  rfl

omit [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction GR A] [ContinuousSMul GR A] in
/-- **Backward, gateway step.**  For a Roe word cocycle `x ∈ Z1wR t_q`, the classified lift
`c := classify (liftMarking t_q x) : F₄ →ₜ* WordLift A C` kills `N_R`.  Its kernel is an
`R`-admissible open: `Generates` is automatic (`generates_univMarking_map`), both `Γ_R` relators die
(`x` is a cocycle ⇒ `.u`-slot dies, `t_q` `R`-admissible ⇒ `.g`-slot dies), and the wild core is
pro-2 by the reused `WordCohBridge.isPGroup_liftMarking_wildCore` (transferred into `F₄ ⧸ ker c`
along the injective `kerLift c`), using that `A` is elementary-2.  `Γ_R` twin of
`WordCohBridge.NA_le_ker_classify`, with `IsAdmissibleU`/`isAdmissibleU_iff_NA_le` swapped for
`IsAdmissibleUR`/`isAdmissibleUR_iff_NR_le`. -/
theorem NR_le_ker_classify_R (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) :
    NR ≤ (Marking.classify (liftMarking (markC_R q) x.1)).toMonoidHom.ker := by
  set c := Marking.classify (liftMarking (markC_R q) x.1) with hc
  have hut : univMarking.map c.toMonoidHom = liftMarking (markC_R q) x.1 := by
    rw [hc, Marking.classify, univMarking_map_toHom]
  have htame : c.toMonoidHom univMarking.tameRelator = 1 :=
    (Marking.map_tameRelator_eq_one_iff c univMarking).mpr
      (by rw [hut]; exact liftMarking_Z1wR_tameRel q hq x)
  have hwild : c.toMonoidHom univMarking.wildRelatorR = 1 :=
    (Marking.map_wildRelatorR_eq_one_iff c univMarking).mpr
      (by rw [hut]; exact liftMarking_Z1wR_wildRelR q hq x)
  have hker_open :
      IsOpen ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = c ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set (WordLift A C))).preimage c.continuous_toFun
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := c.toMonoidHom.ker, isOpen' := hker_open }
  have hx0 : c.toMonoidHom univMarking.x₀ = (liftMarking (markC_R q) x.1).x₀ :=
    congrArg Marking.x₀ hut
  have hx1 : c.toMonoidHom univMarking.x₁ = (liftMarking (markC_R q) x.1).x₁ :=
    congrArg Marking.x₁ hut
  haveI : DiscreteTopology (FreeProfiniteGroup (Fin 4) ⧸
      (U.toOpenSubgroup : Subgroup (FreeProfiniteGroup (Fin 4)))) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul U.toOpenSubgroup
  have hadm : IsAdmissibleUR U := by
    refine ⟨generates_univMarking_map _, ?_, ?_, ?_⟩
    · exact (Marking.map_tameRelator_eq_one_iff (quotientMk U.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr htame))
    · exact (Marking.map_wildRelatorR_eq_one_iff (quotientMk U.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hwild))
    · rw [Marking.Pro2Core]
      have hval : ∀ g : FreeProfiniteGroup (Fin 4),
          QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup g)
            = c.toMonoidHom g :=
        fun g => QuotientGroup.kerLift_mk c.toMonoidHom g
      have hcomap : IsPGroup 2 (Subgroup.comap (QuotientGroup.kerLift c.toMonoidHom)
          (Subgroup.normalClosure
            {(liftMarking (markC_R q) x.1).x₀, (liftMarking (markC_R q) x.1).x₁})) :=
        IsPGroup.comap_of_injective
          (WordCohBridge.isPGroup_liftMarking_wildCore hA₂ (markC_R q)
            (markC_admissible_R q hq).2.2.2 x.1)
          (QuotientGroup.kerLift c.toMonoidHom) (QuotientGroup.kerLift_injective c.toMonoidHom)
      refine IsPGroup.to_le hcomap ?_
      apply Subgroup.normalClosure_le_normal
      intro w hw
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with h | h <;> subst h
      · show QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup univMarking.x₀)
            ∈ Subgroup.normalClosure
              {(liftMarking (markC_R q) x.1).x₀, (liftMarking (markC_R q) x.1).x₁}
        rw [hval, hx0]
        exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
      · show QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup univMarking.x₁)
            ∈ Subgroup.normalClosure
              {(liftMarking (markC_R q) x.1).x₀, (liftMarking (markC_R q) x.1).x₁}
        rw [hval, hx1]
        exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)
  exact (isAdmissibleUR_iff_NR_le U).mp hadm

/-- The descended `WordLift`-valued hom of a Roe word cocycle: `Marking.classify (liftMarking t_q x)`
pushed through `Γ_R = F₄ ⧸ N_R` (legitimate by `NR_le_ker_classify_R`). -/
noncomputable def liftHomR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) : ContinuousMonoidHom GR (WordLift A C) :=
  quotientLift NR (Marking.classify (liftMarking (markC_R q) x.1)) (NR_le_ker_classify_R q hq hA₂ x)

omit [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction GR A] [ContinuousSMul GR A] in
private theorem liftHomR_quotientMk (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) (g : FreeProfiniteGroup (Fin 4)) :
    liftHomR q hq hA₂ x (quotientMk NR g) = Marking.classify (liftMarking (markC_R q) x.1) g :=
  quotientLift_quotientMk NR _ _ g

omit [TopologicalSpace A] [DiscreteTopology A] [DistribMulAction GR A] [ContinuousSMul GR A] in
/-- The descended hom lifts `q` on the base coordinate: `(liftHomR x γ).g = q γ`.  (Both
`gHomC ∘ liftHomR` and `q` are the descent of the same `F₄ → C` hom, since projecting the lifted
marking recovers `t_q` — the reused `WordCohBridge.liftMarking_map_gHom`.) -/
theorem liftHomR_g (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) (γ : GR) : (liftHomR q hq hA₂ x γ).g = q γ := by
  set c := Marking.classify (liftMarking (markC_R q) x.1) with hc
  have hut : univMarking.map c.toMonoidHom = liftMarking (markC_R q) x.1 := by
    rw [hc, Marking.classify, univMarking_map_toHom]
  have hcomp : (WordCohBridge.gHomC (A := A) (C := C)).comp c = q.comp (quotientMk NR) := by
    have e1 : univMarking.map ((WordCohBridge.gHomC (A := A) (C := C)).comp c).toMonoidHom
        = markC_R q := by
      show univMarking.map (WordCohBridge.gHom.comp c.toMonoidHom) = markC_R q
      rw [← Marking.map_map, hut, WordCohBridge.liftMarking_map_gHom]
    have e2 : univMarking.map (q.comp (quotientMk NR)).toMonoidHom = markC_R q := rfl
    rw [← Marking.toHom_hom_univMarking_map ((WordCohBridge.gHomC (A := A) (C := C)).comp c),
        ← Marking.toHom_hom_univMarking_map (q.comp (quotientMk NR)), e1, e2]
  obtain ⟨g, rfl⟩ := quotientMk_surjective NR γ
  show WordCohBridge.gHom (liftHomR q hq hA₂ x (quotientMk NR g)) = q (quotientMk NR g)
  rw [liftHomR_quotientMk]
  exact DFunLike.congr_fun hcomp g

include hcompat in
/-- **Backward map** `Z1wR t_q → Z1(Γ_R, A)`: take the `.u`-component of the descended hom.
Continuity is `WordLift.u ∘ liftHomR`; the cocycle identity is the `WordLift` product law on `.u`,
using `(liftHomR x γ).g = q γ` (`liftHomR_g`) and the compatibility of the two actions. -/
noncomputable def ofZ1wR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) : Z1 GR A :=
  ⟨fun γ => (liftHomR q hq hA₂ x γ).u, mem_Z1_iff.mpr
    ⟨(continuous_of_discreteTopology (f := fun p : WordLift A C => p.u)).comp
        (liftHomR q hq hA₂ x).continuous_toFun,
     fun γ δ => by
       show (liftHomR q hq hA₂ x (γ * δ)).u
         = (liftHomR q hq hA₂ x γ).u + γ • (liftHomR q hq hA₂ x δ).u
       rw [map_mul]
       show (liftHomR q hq hA₂ x γ).u + (liftHomR q hq hA₂ x γ).g • (liftHomR q hq hA₂ x δ).u
         = (liftHomR q hq hA₂ x γ).u + γ • (liftHomR q hq hA₂ x δ).u
       rw [liftHomR_g, hcompat]⟩⟩

/-! ## The equivalence -/

include hcompat in
omit [ContinuousSMul GR A] in
/-- **Right inverse** (`toZ1wRHom ∘ ofZ1wR = id` on `Z1wR`).  Evaluating the descended hom at the
four generators returns `x`. -/
theorem toZ1wRHom_ofZ1wR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1wR (A := A) (markC_R q)) :
    toZ1wRHom q hcompat (ofZ1wR q hcompat hq hA₂ x) = x := by
  have hut : univMarking.map (Marking.classify (liftMarking (markC_R q) x.1)).toMonoidHom
      = liftMarking (markC_R q) x.1 := by rw [Marking.classify, univMarking_map_toHom]
  apply Subtype.ext
  rw [toZ1wRHom_coe]
  funext i
  fin_cases i
  · show (liftHomR q hq hA₂ x (quotientMk NR univMarking.σ)).u = x.1 0
    rw [liftHomR_quotientMk]; exact congrArg WordLift.u (congrArg Marking.σ hut)
  · show (liftHomR q hq hA₂ x (quotientMk NR univMarking.τ)).u = x.1 1
    rw [liftHomR_quotientMk]; exact congrArg WordLift.u (congrArg Marking.τ hut)
  · show (liftHomR q hq hA₂ x (quotientMk NR univMarking.x₀)).u = x.1 2
    rw [liftHomR_quotientMk]; exact congrArg WordLift.u (congrArg Marking.x₀ hut)
  · show (liftHomR q hq hA₂ x (quotientMk NR univMarking.x₁)).u = x.1 3
    rw [liftHomR_quotientMk]; exact congrArg WordLift.u (congrArg Marking.x₁ hut)

include hcompat in
omit [ContinuousSMul GR A] in
/-- **Left inverse** (`ofZ1wR ∘ toZ1wRHom = id` on `Z1`).  The descended hom of `evalR z` *is*
`wordHomR z`: both equal `(wordHomR z).comp (quotientMk N_R)` after `quotientMk` (by
`liftMarking_evalR_univ` + `Marking.toHom_hom_univMarking_map`), so their `.u`-slots agree. -/
theorem ofZ1wR_toZ1wRHom (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (z : Z1 GR A) : ofZ1wR q hcompat hq hA₂ (toZ1wRHom q hcompat z) = z := by
  have hclass : Marking.classify (liftMarking (markC_R q) (evalR z))
      = (wordHomR q hcompat z).comp (quotientMk NR) := by
    rw [Marking.classify, liftMarking_evalR_univ]
    exact Marking.toHom_hom_univMarking_map _
  have key : ∀ γ : GR, liftHomR q hq hA₂ (toZ1wRHom q hcompat z) γ = wordHomR q hcompat z γ := by
    intro γ
    obtain ⟨g, rfl⟩ := quotientMk_surjective NR γ
    rw [liftHomR_quotientMk]
    show Marking.classify (liftMarking (markC_R q) (evalR z)) g
      = wordHomR q hcompat z (quotientMk NR g)
    rw [hclass]; rfl
  apply Subtype.ext
  funext γ
  show (liftHomR q hq hA₂ (toZ1wRHom q hcompat z) γ).u = z.1 γ
  rw [key γ]; rfl

include hcompat in
/-- **The degree-1 comparison for `Γ_R`**: continuous crossed cocycles of `Γ_R` valued in the
elementary-2 module `A` are exactly the *Roe* word cocycles of the pushed marking
`t_q = markC_R q`, via evaluation at the four marked generators.  Binder shape mirrors
`WordCohBridge.z1Equiv` exactly, so downstream `Nat.card_congr (z1EquivR θ hcomp hθs hA₂).toEquiv`
calls read verbatim as on the `Γ_A` side. -/
noncomputable def z1EquivR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) :
    Z1 GR A ≃+ Z1wR (A := A) (markC_R q) where
  toFun := toZ1wRHom q hcompat
  invFun := ofZ1wR q hcompat hq hA₂
  left_inv := ofZ1wR_toZ1wRHom q hcompat hq hA₂
  right_inv := toZ1wRHom_ofZ1wR q hcompat hq hA₂
  map_add' := (toZ1wRHom q hcompat).map_add'

include hcompat in
omit [ContinuousSMul GR A] in
/-- **Smoke test (`z1EquivR` round trip).**  The bundled equivalence really is `evalR` in the
forward direction and inverts it. -/
theorem z1EquivR_apply_coe (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) (z : Z1 GR A) :
    ((z1EquivR q hcompat hq hA₂ z : Z1wR (A := A) (markC_R q)) : Fin 4 → A) = evalR z ∧
      (z1EquivR q hcompat hq hA₂).symm (z1EquivR q hcompat hq hA₂ z) = z :=
  ⟨rfl, (z1EquivR q hcompat hq hA₂).symm_apply_apply z⟩

omit [Finite A] [DiscreteTopology C] [Finite C] in
include hcompat in
/-- **Degree-0 compatibility.**  Evaluation carries a `Γ_R`-coboundary `dZero m` to the
word-coboundary `d0 t_q m`: on each generator `gammaGenR.slot • m = t_q.slot • m`, since `q`
intertwines the two actions (`hcompat`) and `q gammaGenR.slot = t_q.slot` by construction.  (`d⁰`
does not see the relator, so this is word-independent — but it is stated at `markC_R`.) -/
theorem eval_dZeroR (m : A) :
    evalR (⟨dZero GR A m, B1_le_Z1 ⟨m, rfl⟩⟩ : Z1 GR A) = d0 (markC_R q) m := by
  have hσ : (markC_R q).σ = q gammaGenR.σ := congrArg Marking.σ (markC_R_map q)
  have hτ : (markC_R q).τ = q gammaGenR.τ := congrArg Marking.τ (markC_R_map q)
  have h0 : (markC_R q).x₀ = q gammaGenR.x₀ := congrArg Marking.x₀ (markC_R_map q)
  have h1 : (markC_R q).x₁ = q gammaGenR.x₁ := congrArg Marking.x₁ (markC_R_map q)
  funext i
  fin_cases i
  · show gammaGenR.σ • m - m = (markC_R q).σ • m - m; rw [hcompat, hσ]
  · show gammaGenR.τ • m - m = (markC_R q).τ • m - m; rw [hcompat, hτ]
  · show gammaGenR.x₀ • m - m = (markC_R q).x₀ • m - m; rw [hcompat, h0]
  · show gammaGenR.x₁ • m - m = (markC_R q).x₁ • m - m; rw [hcompat, h1]

include hcompat in
/-- **The degree-1 comparison in cohomology for `Γ_R`**: `H¹(Γ_R, A) ≃+ H¹_{R,word}(t_q)`, obtained
by descending `z1EquivR` through the coboundary correspondence `B¹ ↔ B¹_word` (`eval_dZeroR`;
`B1wR = B1w`, the relator does not enter `d⁰`).  Binder shape mirrors `WordCohBridge.h1Equiv`. -/
noncomputable def h1EquivR (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) :
    ContCoh.H1 GR A ≃+ H1wR (A := A) (markC_R q) :=
  QuotientAddGroup.congr _ _ (z1EquivR q hcompat hq hA₂) <| by
    ext w
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, B1, B1wR,
      AddMonoidHom.mem_range]
    constructor
    · rintro ⟨z, ⟨m, hm⟩, rfl⟩
      refine ⟨m, ?_⟩
      have hz : z = ⟨dZero GR A m, B1_le_Z1 ⟨m, rfl⟩⟩ := Subtype.ext hm.symm
      show d0 (markC_R q) m = evalR z
      rw [hz, ← eval_dZeroR q hcompat m]
    · rintro ⟨m, hm⟩
      refine ⟨⟨dZero GR A m, B1_le_Z1 ⟨m, rfl⟩⟩, ⟨m, rfl⟩, ?_⟩
      apply Subtype.ext
      show evalR (⟨dZero GR A m, B1_le_Z1 ⟨m, rfl⟩⟩ : Z1 GR A) = w.1
      rw [eval_dZeroR q hcompat m]; exact hm

include hcompat in
/-- **Smoke test (`h1EquivR` round trip).**  The `H¹`-level equivalence is the descent of
`z1EquivR`: it sends the class of `z` to the class of `evalR z`, and inverts. -/
theorem h1EquivR_mk (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) (z : Z1 GR A) :
    h1EquivR q hcompat hq hA₂ (QuotientAddGroup.mk z)
        = h1wMkR (markC_R q) (toZ1wRHom q hcompat z) ∧
      (h1EquivR q hcompat hq hA₂).symm (h1EquivR q hcompat hq hA₂ (QuotientAddGroup.mk z))
        = QuotientAddGroup.mk z :=
  ⟨rfl, (h1EquivR q hcompat hq hA₂).symm_apply_apply _⟩

end WordCohBridgeR

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * eq. (1.2) = ⟦eq:relators⟧ — the Roe wild relator whose death in `Γ_R` is the sole new
    ingredient (`liftMarking_evalR_wildRelR`, `liftMarking_Z1wR_wildRelR`).
  * Definition 1.1 = ⟦def:GammaR⟧ — `IsAdmissibleUR`/`N_R`, via `NR_le_ker_classify_R`.
-/
