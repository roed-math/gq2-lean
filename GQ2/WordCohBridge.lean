import GQ2.FoxHeisenberg
import GQ2.Prop23
import GQ2.AdmissibleLimit

/-!
# The Γ_A degree-≤1 presentation comparison  (ticket P-16c1)

For a finite discrete `C`-module `A` and a continuous surjection `q : Γ_A ↠ C`, the continuous
`H¹` of `Γ_A` (with `A` a `Γ_A`-module through `q`) is computed by the **Fox–Heisenberg word
complex** `Z1w`/`H1w` of the pushed marking `t_q = Marking.push q`:

  `z1Equiv : ContCoh.Z1 Γ_A A ≃+ Z1w t_q`   (evaluation at the four marked generators),

descending to `h1Equiv : ContCoh.H1 Γ_A A ≃+ H1w t_q`.  This is the Γ_A-side replacement for
B6/Tate duality that P-16c (`lemma_8_6_gammaA`) needs — the word-complex self-duality `prop_5_15`
then transports to `H¹(Γ_A)`.  Reusable beyond §8 (the degree-1 half of the presentation
comparison, wanted again for Theorem 4.2).

**Level.**  `Γ_A = GammaA = ProfiniteGrp.of (F₄ ⧸ N_A)` re-wraps the raw quotient with fresh
(defeq-but-not-syntactic) group/topology instances, whereas all the marking machinery
(`quotientMk`/`quotientLift`/`Marking.push`/`Marking.descend`) lives over the raw
`FreeProfiniteGroup (Fin 4) ⧸ N_A`.  To keep `q.comp (quotientMk NA)` unifying, this file is
built over the raw quotient `GA := FreeProfiniteGroup (Fin 4) ⧸ N_A`; the carrier is defeq to
`GammaA`, so the results transport to the `GammaA` statement (`z1EquivGammaA` at the end).

The spine: a continuous crossed cocycle `z : GA → A` (for the `q`-conjugation action) is exactly
the `.u`-component of a continuous hom `φ_z : GA → WordLift A C = A ⋊ C` lifting `q`
(`(φ_z γ).g = q γ`).  Evaluating `φ_z` at the generators lands in `Z1w` because the relators die
in `GA`; conversely a word cocycle `x ∈ Z1w` gives an admissible marking of `WordLift`, which
`Marking.descend`s to the hom, whose `.u`-component is the cocycle (`ker_char_NA_le_iff` pattern:
`Generates` is automatic for a quotient of `F₄`).
-/

namespace GQ2

open ContCoh FoxH

namespace WordCohBridge

/-- The raw quotient `Γ_A = F₄ ⧸ N_A` (defeq to `GammaA`, but with the `QuotientGroup` instances
the marking machinery is stated against). -/
abbrev GA : Type := FreeProfiniteGroup (Fin 4) ⧸ NA

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A]
  [DistribMulAction GA A] [ContinuousSMul GA A]

/-- The (discrete) topology on `WordLift A C` making it a valid codomain for continuous homs. -/
instance : TopologicalSpace (WordLift A C) := ⊥
instance : DiscreteTopology (WordLift A C) := ⟨rfl⟩

variable (q : ContinuousMonoidHom GA C)
  (hcompat : ∀ (γ : GA) (a : A), γ • a = q γ • a)

/-- The `WordLift A C = A ⋊ C` hom `γ ↦ ⟨z γ, q γ⟩` attached to a continuous crossed cocycle
`z`.  The cocycle identity `z(γδ) = z γ + q γ • z δ` is exactly the `WordLift` product law on the
`.u`-slot. -/
noncomputable def wordHom (z : Z1 GA A) : ContinuousMonoidHom GA (WordLift A C) where
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
    have hg : Continuous (fun γ : GA => ((z.1 γ, q γ) : A × C)) :=
      ((mem_Z1_iff.mp z.2).1).prodMk q.continuous_toFun
    exact (continuous_of_discreteTopology
      (f := (WordLift.equivProd (A := A) (C := C)).symm)).comp hg


/-- The canonical marking of `Γ_A` by the images of the four free generators. -/
noncomputable def gammaGen : Marking GA := univMarking.map (quotientMk NA).toMonoidHom

/-- The pushed marking `t_q : Marking C` of the surjection `q` — the marking against which the
word complex `Z1w`/`H1w` is formed. -/
noncomputable def markC : Marking C := Marking.push q

theorem markC_admissible (hq : Function.Surjective q) : (markC q).Admissible :=
  Marking.push_admissible q hq

/-- `t_q = q ∘ (canonical Γ_A-marking)` on each generator (the `Marking.map_map` collapse). -/
theorem markC_map : markC q = (gammaGen).map q.toMonoidHom := by
  show Marking.push q = (univMarking.map (quotientMk NA).toMonoidHom).map q.toMonoidHom
  rw [Marking.push, Marking.map_map]
  rfl

/-- Evaluation of a continuous crossed cocycle at the four marked generators of `Γ_A`. -/
noncomputable def eval (z : Z1 GA A) : Fin 4 → A :=
  ![z.1 gammaGen.σ, z.1 gammaGen.τ, z.1 gammaGen.x₀, z.1 gammaGen.x₁]

/-- The lifted marking at `eval z` is the pushforward of `wordHom` along the canonical marking —
the identity underlying "eval lands in `Z1w`". -/
theorem liftMarking_eval (z : Z1 GA A) :
    liftMarking (markC q) (eval z) = (gammaGen).map (wordHom q hcompat z).toMonoidHom := by
  rw [markC_map]
  refine Marking.mk.injEq .. ▸ ⟨?_, ?_, ?_, ?_⟩ <;>
    · apply WordLift.ext <;> rfl

/-- The lifted marking at `eval z`, rewritten as the pushforward of the universal marking along
`φ_z ∘ quotientMk : F₄ → WordLift` — the form the relator-death lemmas consume. -/
theorem liftMarking_eval_univ (z : Z1 GA A) :
    liftMarking (markC q) (eval z)
      = univMarking.map ((wordHom q hcompat z).comp (quotientMk NA)).toMonoidHom := by
  rw [liftMarking_eval]
  show (univMarking.map (quotientMk NA).toMonoidHom).map (wordHom q hcompat z).toMonoidHom = _
  rw [Marking.map_map]
  rfl

include hcompat in
/-- The tame relation holds for the lifted marking at `eval z` (the tame relator dies in `Γ_A`). -/
theorem liftMarking_eval_tameRel (z : Z1 GA A) :
    (liftMarking (markC q) (eval z)).TameRel := by
  rw [liftMarking_eval_univ q hcompat z, ← Marking.map_tameRelator_eq_one_iff]
  show (wordHom q hcompat z) (quotientMk NA univMarking.tameRelator) = 1
  rw [(quotientMk_eq_one_iff NA).mpr tameRelator_mem_NA, map_one]

include hcompat in
/-- The wild relation holds for the lifted marking at `eval z` (the wild relator dies in `Γ_A`). -/
theorem liftMarking_eval_wildRel (z : Z1 GA A) :
    (liftMarking (markC q) (eval z)).WildRel := by
  rw [liftMarking_eval_univ q hcompat z, ← Marking.map_wildRelator_eq_one_iff]
  show (wordHom q hcompat z) (quotientMk NA univMarking.wildRelator) = 1
  rw [(quotientMk_eq_one_iff NA).mpr wildRelator_mem_NA, map_one]

include hcompat in
/-- **Forward: `eval` lands in `Z1w`.** The evaluation of a continuous crossed cocycle at the four
generators is a word cocycle, because both relators die in `Γ_A`. -/
theorem eval_mem_Z1w (z : Z1 GA A) : eval z ∈ Z1w (markC q) := by
  have ht : (liftMarking (markC q) (eval z)).tameValue = 1 :=
    (Marking.tameValue_eq_one_iff _).mpr (liftMarking_eval_tameRel q hcompat z)
  have hw : (liftMarking (markC q) (eval z)).wildValue = 1 :=
    (Marking.wildValue_eq_one_iff _).mpr (liftMarking_eval_wildRel q hcompat z)
  show d1Fun (markC q) (eval z) = 0
  rw [d1Fun, ht, hw]
  rfl

/-- `eval` is additive (it is pointwise evaluation of the additive `z.1`). -/
theorem eval_add (z z' : Z1 GA A) : eval (z + z') = eval z + eval z' := by
  funext i
  fin_cases i <;> rfl

include hcompat in
/-- The forward map `Z1(Γ_A, A) →+ Z1w t_q` (evaluation at the four marked generators), bundled
additively. -/
noncomputable def toZ1wHom : Z1 GA A →+ Z1w (A := A) (markC q) :=
  AddMonoidHom.mk'
    (fun z => ⟨eval z, eval_mem_Z1w q hcompat z⟩)
    (fun z z' => Subtype.ext (eval_add z z'))

@[simp] theorem toZ1wHom_coe (z : Z1 GA A) : (toZ1wHom q hcompat z : Fin 4 → A) = eval z := rfl

/-! ## The `Pro2Core` crux: the wild core of a lifted marking is pro-2. -/

/-- The base projection `WordLift A C →* C` (the `.g` component). -/
def gHom : WordLift A C →* C where
  toFun := WordLift.g
  map_one' := WordLift.one_g
  map_mul' := WordLift.mul_g


/-- The base projection as a *continuous* hom (`WordLift` is discrete). -/
def gHomC : ContinuousMonoidHom (WordLift A C) C := ⟨gHom, continuous_of_discreteTopology⟩


/-- The kernel of the base projection is elementary-2 (it is `A` with `g = 1`). -/
theorem isPGroup_gHom_ker (hA₂ : ∀ a : A, a + a = 0) :
    IsPGroup 2 (gHom (A := A) (C := C)).ker := by
  intro g
  refine ⟨1, ?_⟩
  have hg1 : (g.1).g = 1 := MonoidHom.mem_ker.mp g.2
  apply Subtype.ext
  rw [SubmonoidClass.coe_pow, pow_one, pow_two]
  apply WordLift.ext
  · show g.1.u + g.1.g • g.1.u = (1 : WordLift A C).u
    rw [hg1, one_smul, WordLift.one_u]; exact hA₂ _
  · show g.1.g * g.1.g = (1 : WordLift A C).g
    rw [hg1, WordLift.one_g, mul_one]

/-- **The `Pro2Core` crux**: the wild core `⟪(x₂,t.x₀), (x₃,t.x₁)⟫` of a lifted marking is a
`2`-group — an extension of the (pro-2, `t.Pro2Core`) base wild core by the elementary-2 `A`.
Proved with `IsPGroup.comap_of_ker_isPGroup`: the core is `≤ gHom⁻¹(base core)`. -/
theorem isPGroup_liftMarking_wildCore (hA₂ : ∀ a : A, a + a = 0) (t : Marking C)
    (ht2 : IsPGroup 2 (Subgroup.normalClosure {t.x₀, t.x₁})) (x : Fin 4 → A) :
    IsPGroup 2 (Subgroup.normalClosure
      {(liftMarking t x).x₀, (liftMarking t x).x₁}) := by
  have hcomap : IsPGroup 2 (Subgroup.comap (gHom (A := A) (C := C))
      (Subgroup.normalClosure {t.x₀, t.x₁})) :=
    ht2.comap_of_ker_isPGroup (gHom (A := A) (C := C)) (isPGroup_gHom_ker hA₂)
  have hle : Subgroup.normalClosure {(liftMarking t x).x₀, (liftMarking t x).x₁}
      ≤ Subgroup.comap (gHom (A := A) (C := C)) (Subgroup.normalClosure {t.x₀, t.x₁}) := by
    apply Subgroup.normalClosure_le_normal
    intro w hw
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with h | h <;> rw [h] <;>
      exact Subgroup.subset_normalClosure (by first | exact .inl rfl | exact .inr rfl)
  exact hcomap.to_le hle

/-- Projecting a lifted marking back through `gHom` recovers the base marking. -/
theorem liftMarking_map_gHom (t : Marking C) (x : Fin 4 → A) :
    (liftMarking t x).map (gHom (A := A) (C := C)) = t := by
  refine Marking.mk.injEq .. ▸ ⟨rfl, rfl, rfl, rfl⟩

/-- For a word cocycle `x ∈ Z1w`, the lifted marking satisfies the tame relation: the `.u`-slot
dies because `x` is a cocycle, the `.g`-slot because `t_q` is admissible. -/
theorem liftMarking_Z1w_tameRel (hq : Function.Surjective q) (x : Z1w (A := A) (markC q)) :
    (liftMarking (markC q) x.1).TameRel := by
  have h0 : d1Fun (markC q) x.1 = 0 := AddMonoidHom.mem_ker.mp x.2
  have hu : (liftMarking (markC q) x.1).tameValue.u = 0 := (Prod.ext_iff.mp h0).1
  have hg : (liftMarking (markC q) x.1).tameValue.g = 1 := by
    have : gHom ((liftMarking (markC q) x.1).tameValue) = (markC q).tameValue := by
      rw [← Marking.map_tameValue, liftMarking_map_gHom]
    exact this.trans ((Marking.tameValue_eq_one_iff _).mpr (markC_admissible q hq).2.1)
  rw [← Marking.tameValue_eq_one_iff]
  exact WordLift.ext (by rw [hu]; rfl) (by rw [hg]; rfl)

/-- For a word cocycle `x ∈ Z1w`, the lifted marking satisfies the wild relation. -/
theorem liftMarking_Z1w_wildRel (hq : Function.Surjective q) (x : Z1w (A := A) (markC q)) :
    (liftMarking (markC q) x.1).WildRel := by
  have h0 : d1Fun (markC q) x.1 = 0 := AddMonoidHom.mem_ker.mp x.2
  have hu : (liftMarking (markC q) x.1).wildValue.u = 0 := (Prod.ext_iff.mp h0).2
  have hg : (liftMarking (markC q) x.1).wildValue.g = 1 := by
    have : gHom ((liftMarking (markC q) x.1).wildValue) = (markC q).wildValue := by
      rw [← Marking.map_wildValue, liftMarking_map_gHom]
    exact this.trans ((Marking.wildValue_eq_one_iff _).mpr (markC_admissible q hq).2.2.1)
  rw [← Marking.wildValue_eq_one_iff]
  exact WordLift.ext (by rw [hu]; rfl) (by rw [hg]; rfl)

/-- **Backward, gateway step.**  For a word cocycle `x ∈ Z1w t_q`, the classified lift
`c := classify (liftMarking t_q x) : F₄ →ₜ* WordLift A C` kills `N_A`.  Its kernel is an
admissible open: `Generates` is automatic (`generates_univMarking_map`), both relators die
(`x` is a cocycle ⇒ `.u`-slot dies, `t_q` admissible ⇒ `.g`-slot dies), and the wild core is
pro-2 by `isPGroup_liftMarking_wildCore` (transferred into `F₄ ⧸ ker c` along the injective
`kerLift c`), using that `A` is elementary-2. -/
theorem NA_le_ker_classify (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) :
    NA ≤ (Marking.classify (liftMarking (markC q) x.1)).toMonoidHom.ker := by
  set c := Marking.classify (liftMarking (markC q) x.1) with hc
  have hut : univMarking.map c.toMonoidHom = liftMarking (markC q) x.1 := by
    rw [hc, Marking.classify, univMarking_map_toHom]
  have htame : c.toMonoidHom univMarking.tameRelator = 1 :=
    (Marking.map_tameRelator_eq_one_iff c univMarking).mpr
      (by rw [hut]; exact liftMarking_Z1w_tameRel q hq x)
  have hwild : c.toMonoidHom univMarking.wildRelator = 1 :=
    (Marking.map_wildRelator_eq_one_iff c univMarking).mpr
      (by rw [hut]; exact liftMarking_Z1w_wildRel q hq x)
  have hker_open :
      IsOpen ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = c ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set (WordLift A C))).preimage c.continuous_toFun
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := c.toMonoidHom.ker, isOpen' := hker_open }
  have hx0 : c.toMonoidHom univMarking.x₀ = (liftMarking (markC q) x.1).x₀ :=
    congrArg Marking.x₀ hut
  have hx1 : c.toMonoidHom univMarking.x₁ = (liftMarking (markC q) x.1).x₁ :=
    congrArg Marking.x₁ hut
  haveI : DiscreteTopology (FreeProfiniteGroup (Fin 4) ⧸
      (U.toOpenSubgroup : Subgroup (FreeProfiniteGroup (Fin 4)))) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul U.toOpenSubgroup
  have hadm : IsAdmissibleU U := by
    refine ⟨generates_univMarking_map _, ?_, ?_, ?_⟩
    · exact (Marking.map_tameRelator_eq_one_iff (quotientMk U.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr htame))
    · exact (Marking.map_wildRelator_eq_one_iff (quotientMk U.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hwild))
    · rw [Marking.Pro2Core]
      have hval : ∀ g : FreeProfiniteGroup (Fin 4),
          QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup g)
            = c.toMonoidHom g :=
        fun g => QuotientGroup.kerLift_mk c.toMonoidHom g
      have hcomap : IsPGroup 2 (Subgroup.comap (QuotientGroup.kerLift c.toMonoidHom)
          (Subgroup.normalClosure
            {(liftMarking (markC q) x.1).x₀, (liftMarking (markC q) x.1).x₁})) :=
        IsPGroup.comap_of_injective
          (isPGroup_liftMarking_wildCore hA₂ (markC q) (markC_admissible q hq).2.2.2 x.1)
          (QuotientGroup.kerLift c.toMonoidHom) (QuotientGroup.kerLift_injective c.toMonoidHom)
      refine IsPGroup.to_le hcomap ?_
      apply Subgroup.normalClosure_le_normal
      intro w hw
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
      rcases hw with h | h <;> subst h
      · show QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup univMarking.x₀)
            ∈ Subgroup.normalClosure
              {(liftMarking (markC q) x.1).x₀, (liftMarking (markC q) x.1).x₁}
        rw [hval, hx0]
        exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
      · show QuotientGroup.kerLift c.toMonoidHom (QuotientGroup.mk' U.toSubgroup univMarking.x₁)
            ∈ Subgroup.normalClosure
              {(liftMarking (markC q) x.1).x₀, (liftMarking (markC q) x.1).x₁}
        rw [hval, hx1]
        exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)
  exact (isAdmissibleU_iff_NA_le U).mp hadm

/-- The descended `WordLift`-valued hom of a word cocycle: `Marking.classify (liftMarking t_q x)`
pushed through `Γ_A = F₄ ⧸ N_A` (legitimate by `NA_le_ker_classify`). -/
noncomputable def liftHom (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) : ContinuousMonoidHom GA (WordLift A C) :=
  quotientLift NA (Marking.classify (liftMarking (markC q) x.1)) (NA_le_ker_classify q hq hA₂ x)

theorem liftHom_quotientMk (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) (g : FreeProfiniteGroup (Fin 4)) :
    liftHom q hq hA₂ x (quotientMk NA g) = Marking.classify (liftMarking (markC q) x.1) g :=
  quotientLift_quotientMk NA _ _ g

/-- The descended hom lifts `q` on the base coordinate: `(liftHom x γ).g = q γ`.  (Both
`gHomC ∘ liftHom` and `q` are the descent of the same `F₄ → C` hom, since projecting the lifted
marking recovers `t_q` — `liftMarking_map_gHom`.) -/
theorem liftHom_g (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) (γ : GA) : (liftHom q hq hA₂ x γ).g = q γ := by
  set c := Marking.classify (liftMarking (markC q) x.1) with hc
  have hut : univMarking.map c.toMonoidHom = liftMarking (markC q) x.1 := by
    rw [hc, Marking.classify, univMarking_map_toHom]
  have hcomp : gHomC.comp c = q.comp (quotientMk NA) := by
    have e1 : univMarking.map (gHomC.comp c).toMonoidHom = markC q := by
      show univMarking.map (gHom.comp c.toMonoidHom) = markC q
      rw [← Marking.map_map, hut, liftMarking_map_gHom]
    have e2 : univMarking.map (q.comp (quotientMk NA)).toMonoidHom = markC q := rfl
    rw [← Marking.toHom_hom_univMarking_map (gHomC.comp c),
        ← Marking.toHom_hom_univMarking_map (q.comp (quotientMk NA)), e1, e2]
  obtain ⟨g, rfl⟩ := quotientMk_surjective NA γ
  show gHom (liftHom q hq hA₂ x (quotientMk NA g)) = q (quotientMk NA g)
  rw [liftHom_quotientMk]
  exact DFunLike.congr_fun hcomp g

include hcompat in
/-- **Backward map** `Z1w t_q → Z1(Γ_A, A)`: take the `.u`-component of the descended hom.
Continuity is `WordLift.u ∘ liftHom`; the cocycle identity is the `WordLift` product law on
`.u`, using `(liftHom x γ).g = q γ` (`liftHom_g`) and the compatibility of the two actions. -/
noncomputable def ofZ1w (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) : Z1 GA A :=
  ⟨fun γ => (liftHom q hq hA₂ x γ).u, mem_Z1_iff.mpr
    ⟨(continuous_of_discreteTopology (f := fun p : WordLift A C => p.u)).comp
        (liftHom q hq hA₂ x).continuous_toFun,
     fun γ δ => by
       show (liftHom q hq hA₂ x (γ * δ)).u
         = (liftHom q hq hA₂ x γ).u + γ • (liftHom q hq hA₂ x δ).u
       rw [map_mul]
       show (liftHom q hq hA₂ x γ).u + (liftHom q hq hA₂ x γ).g • (liftHom q hq hA₂ x δ).u
         = (liftHom q hq hA₂ x γ).u + γ • (liftHom q hq hA₂ x δ).u
       rw [liftHom_g, hcompat]⟩⟩


/-! ## The equivalence (P-16c1, remaining)

The forward map `toZ1wHom` and backward map `ofZ1w` are complete and verified below, together
with both round trips and the additive equivalence `z1Equiv`.  Neither round trip needs the
topological generation of `Γ_A`: both factor through `quotientMk` surjectivity and the
`univMarking.map` uniqueness `Marking.toHom_hom_univMarking_map`.  The `H¹` corollary `h1Equiv`
descends `z1Equiv` through `B1 ↔ B1w` (degree-0 half of the comparison) — the next sub-step.
-/

include hcompat in
/-- **Right inverse** (`toZ1wHom ∘ ofZ1w = id` on `Z1w`).  Evaluating the descended hom at the
four generators returns `x`: `(liftHom x (quotientMk N_A (univMarking.slot))).u
= (Marking.classify (liftMarking t_q x) (univMarking.slot)).u = ((liftMarking t_q x).slot).u
= x.slot`. -/
theorem toZ1wHom_ofZ1w (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (x : Z1w (A := A) (markC q)) :
    toZ1wHom q hcompat (ofZ1w q hcompat hq hA₂ x) = x := by
  have hut : univMarking.map (Marking.classify (liftMarking (markC q) x.1)).toMonoidHom
      = liftMarking (markC q) x.1 := by rw [Marking.classify, univMarking_map_toHom]
  apply Subtype.ext
  rw [toZ1wHom_coe]
  funext i
  fin_cases i
  · show (liftHom q hq hA₂ x (quotientMk NA univMarking.σ)).u = x.1 0
    rw [liftHom_quotientMk]; exact congrArg WordLift.u (congrArg Marking.σ hut)
  · show (liftHom q hq hA₂ x (quotientMk NA univMarking.τ)).u = x.1 1
    rw [liftHom_quotientMk]; exact congrArg WordLift.u (congrArg Marking.τ hut)
  · show (liftHom q hq hA₂ x (quotientMk NA univMarking.x₀)).u = x.1 2
    rw [liftHom_quotientMk]; exact congrArg WordLift.u (congrArg Marking.x₀ hut)
  · show (liftHom q hq hA₂ x (quotientMk NA univMarking.x₁)).u = x.1 3
    rw [liftHom_quotientMk]; exact congrArg WordLift.u (congrArg Marking.x₁ hut)

include hcompat in
/-- **Left inverse** (`ofZ1w ∘ toZ1wHom = id` on `Z1`).  The descended hom of `eval z` *is*
`wordHom z`: both equal `(wordHom z).comp (quotientMk N_A)` after `quotientMk` (by
`liftMarking_eval_univ` + `Marking.toHom_hom_univMarking_map`), so their `.u`-slots agree. -/
theorem ofZ1w_toZ1wHom (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0)
    (z : Z1 GA A) : ofZ1w q hcompat hq hA₂ (toZ1wHom q hcompat z) = z := by
  have hclass : Marking.classify (liftMarking (markC q) (eval z))
      = (wordHom q hcompat z).comp (quotientMk NA) := by
    rw [Marking.classify, liftMarking_eval_univ]
    exact Marking.toHom_hom_univMarking_map _
  have key : ∀ γ : GA, liftHom q hq hA₂ (toZ1wHom q hcompat z) γ = wordHom q hcompat z γ := by
    intro γ
    obtain ⟨g, rfl⟩ := quotientMk_surjective NA γ
    rw [liftHom_quotientMk]
    show Marking.classify (liftMarking (markC q) (eval z)) g = wordHom q hcompat z (quotientMk NA g)
    rw [hclass]; rfl
  apply Subtype.ext
  funext γ
  show (liftHom q hq hA₂ (toZ1wHom q hcompat z) γ).u = z.1 γ
  rw [key γ]; rfl

include hcompat in
/-- **The degree-1 comparison** (P-16c1): continuous crossed cocycles of `Γ_A` valued in the
elementary-2 module `A` are exactly the Fox–Heisenberg word cocycles of the pushed marking
`t_q = Marking.push q`, via evaluation at the four marked generators. -/
noncomputable def z1Equiv (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) :
    Z1 GA A ≃+ Z1w (A := A) (markC q) where
  toFun := toZ1wHom q hcompat
  invFun := ofZ1w q hcompat hq hA₂
  left_inv := ofZ1w_toZ1wHom q hcompat hq hA₂
  right_inv := toZ1wHom_ofZ1w q hcompat hq hA₂
  map_add' := (toZ1wHom q hcompat).map_add'

include hcompat in
/-- **Degree-0 compatibility.**  Evaluation carries a `Γ_A`-coboundary `dZero m` to the
word-coboundary `d0 t_q m`: on each generator `gammaGen.slot • m = t_q.slot • m`, since `q`
intertwines the two actions (`hcompat`) and `q gammaGen.slot = t_q.slot` by construction. -/
theorem eval_dZero (m : A) :
    eval (⟨dZero GA A m, B1_le_Z1 ⟨m, rfl⟩⟩ : Z1 GA A) = d0 (markC q) m := by
  have hσ : (markC q).σ = q gammaGen.σ := congrArg Marking.σ (markC_map q)
  have hτ : (markC q).τ = q gammaGen.τ := congrArg Marking.τ (markC_map q)
  have h0 : (markC q).x₀ = q gammaGen.x₀ := congrArg Marking.x₀ (markC_map q)
  have h1 : (markC q).x₁ = q gammaGen.x₁ := congrArg Marking.x₁ (markC_map q)
  funext i
  fin_cases i
  · show gammaGen.σ • m - m = (markC q).σ • m - m; rw [hcompat, hσ]
  · show gammaGen.τ • m - m = (markC q).τ • m - m; rw [hcompat, hτ]
  · show gammaGen.x₀ • m - m = (markC q).x₀ • m - m; rw [hcompat, h0]
  · show gammaGen.x₁ • m - m = (markC q).x₁ • m - m; rw [hcompat, h1]

include hcompat in
/-- **The degree-1 comparison in cohomology** (P-16c1): `H¹(Γ_A, A) ≃+ H¹_word(t_q)`, obtained by
descending `z1Equiv` through the coboundary correspondence `B¹ ↔ B¹_word` (`eval_dZero`). -/
noncomputable def h1Equiv (hq : Function.Surjective q) (hA₂ : ∀ a : A, a + a = 0) :
    ContCoh.H1 GA A ≃+ H1w (A := A) (markC q) :=
  QuotientAddGroup.congr _ _ (z1Equiv q hcompat hq hA₂) <| by
    ext w
    simp only [AddSubgroup.mem_map, AddSubgroup.mem_addSubgroupOf, B1, B1w,
      AddMonoidHom.mem_range]
    constructor
    · rintro ⟨z, ⟨m, hm⟩, rfl⟩
      refine ⟨m, ?_⟩
      have hz : z = ⟨dZero GA A m, B1_le_Z1 ⟨m, rfl⟩⟩ := Subtype.ext hm.symm
      show d0 (markC q) m = eval z
      rw [hz, ← eval_dZero q hcompat m]
    · rintro ⟨m, hm⟩
      refine ⟨⟨dZero GA A m, B1_le_Z1 ⟨m, rfl⟩⟩, ⟨m, rfl⟩, ?_⟩
      apply Subtype.ext
      show eval (⟨dZero GA A m, B1_le_Z1 ⟨m, rfl⟩⟩ : Z1 GA A) = w.1
      rw [eval_dZero q hcompat m]; exact hm

end WordCohBridge

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Theorem 4.2 = ⟦thm-fixedframe⟧
-/
