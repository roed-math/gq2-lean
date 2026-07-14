import GQ2.WordCohBridge

/-!
# The Γ_A degree-2 presentation comparison — foundation  (ticket P-16c2)

Building on the degree-≤1 bridge `GQ2/WordCohBridge.lean` (`z1Equiv`/`h1Equiv`), this file develops
the degree-2 half: an injection `H²(Γ_A, 𝔽₂) ↪ 𝔽₂² ⧸ im d1_triv = H2w(t_triv)` (evaluation of the two
relator words on a central extension), whose target has cardinality `2` (`card_H2w_trivial`), giving
`#H²(Γ_A, 𝔽₂) ≤ 2` — the source-side cohomological input `lemma_8_6_gammaA` (P-16c) needs.

**This file, so far — the central-extension foundation.**  A `ZMod 2`-valued 2-cocycle `κ` on a group
`L` (normalized at `(1,1)`) is packaged as `TwoCocycle L`, and `CentExt c` is the central extension
`L ×_κ ZMod 2`: carrier `L × ZMod 2`, product `(l,z)·(l',z') = (l·l', z + z' + κ l l')`.  The kernel
`{(1, z)} ≅ ZMod 2` is central; the base projection is `CentExt c →* L`.  When `L` is finite discrete
so is `CentExt c` — the codomain for a `Marking` whose relator values read off the cocycle's obstruction.

The remaining θ construction (factor a continuous cocycle through a finite admissible level, mark the
extension by `(ḡᵢ, 0)`, read the tame/wild relator `z`-values, quotient by `im d1_triv`, prove additivity,
vanishing on coboundaries, and injectivity via `Marking.descend`) is the next work; see the tail comment.
-/

namespace GQ2

namespace WordCoh2

open ContCoh FoxH

variable {L : Type*} [Group L]

/-- A `ZMod 2`-valued 2-cocycle on `L`, normalized at `(1,1)` — the datum of a central extension of
`L` by `ZMod 2` (trivial action).  The single cocycle identity `κ(a,b) + κ(ab,c) = κ(a,bc) + κ(b,c)`
forces `κ(1,·) = κ(·,1) = κ(1,1)`; the `norm` field pins that constant to `0`. -/
structure TwoCocycle (L : Type*) [Group L] where
  /-- The underlying 2-cochain. -/
  κ : L → L → ZMod 2
  /-- Normalization at the identity. -/
  norm : κ 1 1 = 0
  /-- The 2-cocycle identity (trivial coefficients). -/
  cocyc : ∀ a b c : L, κ a b + κ (a * b) c = κ a (b * c) + κ b c

namespace TwoCocycle

variable (c : TwoCocycle L)

/-- `κ` vanishes on the left axis (`κ(1,l) = 0`). -/
theorem κ_one_left (l : L) : c.κ 1 l = 0 := by
  simpa [c.norm] using c.cocyc 1 1 l

/-- `κ` vanishes on the right axis (`κ(l,1) = 0`). -/
theorem κ_one_right (l : L) : c.κ l 1 = 0 := by
  simpa [c.norm] using c.cocyc l 1 1

/-- Symmetry of `κ` on inverse pairs (`κ(l,l⁻¹) = κ(l⁻¹,l)`) — the fact underlying the inverse law
of the central extension. -/
theorem κ_inv (l : L) : c.κ l l⁻¹ = c.κ l⁻¹ l := by
  simpa [c.κ_one_left, c.κ_one_right] using c.cocyc l l⁻¹ l

end TwoCocycle

/-- The central extension `L ×_κ ZMod 2` of `L` by `ZMod 2` attached to a 2-cocycle `κ`: carrier
`L × ZMod 2`, product `(l,z)·(l',z') = (l·l', z + z' + κ l l')`. -/
def CentExt (_c : TwoCocycle L) : Type _ := L × ZMod 2

namespace CentExt

variable {c : TwoCocycle L}

/-- Base coordinate of an element of the extension. -/
def base (p : CentExt c) : L := p.1

/-- Fibre (`ZMod 2`) coordinate of an element of the extension. -/
def fib (p : CentExt c) : ZMod 2 := p.2

@[ext] theorem ext {p q : CentExt c} (h1 : p.base = q.base) (h2 : p.fib = q.fib) : p = q :=
  Prod.ext h1 h2

instance : Group (CentExt c) where
  mul p q := (p.1 * q.1, p.2 + q.2 + c.κ p.1 q.1)
  one := (1, 0)
  inv p := (p.1⁻¹, p.2 + c.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply Prod.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2 + q.2 + c.κ p.1 q.1 + r.2 + c.κ (p.1 * q.1) r.1
        = p.2 + (q.2 + r.2 + c.κ q.1 r.1) + c.κ p.1 (q.1 * r.1)
      linear_combination c.cocyc p.1 q.1 r.1
  one_mul p := by
    apply Prod.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2 + c.κ 1 p.1 = p.2
      rw [c.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply Prod.ext
    · exact mul_one p.1
    · show p.2 + 0 + c.κ p.1 1 = p.2
      rw [c.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply Prod.ext
    · exact inv_mul_cancel p.1
    · show p.2 + c.κ p.1 p.1⁻¹ + p.2 + c.κ p.1⁻¹ p.1 = 0
      rw [c.κ_inv]
      exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] theorem mul_base (p q : CentExt c) : (p * q).base = p.base * q.base := rfl
@[simp] theorem mul_fib (p q : CentExt c) : (p * q).fib = p.fib + q.fib + c.κ p.base q.base := rfl
@[simp] theorem one_base : (1 : CentExt c).base = 1 := rfl
@[simp] theorem one_fib : (1 : CentExt c).fib = 0 := rfl

/-- The base projection `L ×_κ ZMod 2 →* L`, a group homomorphism. -/
def proj (c : TwoCocycle L) : CentExt c →* L where
  toFun := CentExt.base
  map_one' := rfl
  map_mul' := mul_base


/-- The central inclusion `ZMod 2 → L ×_κ ZMod 2`, `z ↦ (1, z)`. -/
def incl (c : TwoCocycle L) : ZMod 2 → CentExt c := fun z => (1, z)

@[simp] theorem incl_base (z : ZMod 2) : (incl c z).base = 1 := rfl
@[simp] theorem incl_fib (z : ZMod 2) : (incl c z).fib = z := rfl

/-- An element of the extension lies over the base identity iff it is in the central `ZMod 2`. -/
theorem base_eq_one_iff (p : CentExt c) : p.base = 1 ↔ p = incl c p.fib :=
  ⟨fun h => CentExt.ext h rfl, fun h => by rw [h]; rfl⟩

/-- `incl 0` is the identity of the extension. -/
@[simp] theorem incl_zero : incl c (0 : ZMod 2) = 1 := rfl


/-- The fibre of `incl z · p` is `z + p.fib` (the base being `p.base`). -/
@[simp] theorem incl_mul_fib (z : ZMod 2) (p : CentExt c) : (incl c z * p).fib = z + p.fib := by
  show z + p.fib + c.κ 1 p.base = z + p.fib
  rw [c.κ_one_left, add_zero]


instance : TopologicalSpace (CentExt c) := ⊥
instance : DiscreteTopology (CentExt c) := ⟨rfl⟩
instance [Finite L] : Finite (CentExt c) := inferInstanceAs (Finite (L × ZMod 2))

end CentExt

/-! ## Lifting a level marking and reading the relator obstruction -/

/-- Lift a marking of the base group `L` to the central extension by placing each generator over it
with zero fibre coordinate.  Its base projection is the original marking. -/
def liftMark (t : Marking L) (c : TwoCocycle L) : Marking (CentExt c) :=
  ⟨(t.σ, 0), (t.τ, 0), (t.x₀, 0), (t.x₁, 0)⟩

@[simp] theorem liftMark_map_proj (t : Marking L) (c : TwoCocycle L) :
    (liftMark t c).map (CentExt.proj c) = t := rfl

/-- The tame relator value of the lifted marking projects to that of the base marking. -/
theorem liftMark_tameValue_base (t : Marking L) (c : TwoCocycle L) :
    (liftMark t c).tameValue.base = t.tameValue :=
  liftMark_map_proj t c ▸ (Marking.map_tameValue (CentExt.proj c) (liftMark t c)).symm

/-- The wild relator value of the lifted marking projects to that of the base marking (needs `L`
finite: `Marking.map_wildValue`'s `ω₂`-naturality is finite-only, and `CentExt c` is finite). -/
theorem liftMark_wildValue_base [Finite L] (t : Marking L) (c : TwoCocycle L) :
    (liftMark t c).wildValue.base = t.wildValue :=
  liftMark_map_proj t c ▸ (Marking.map_wildValue (CentExt.proj c) (liftMark t c)).symm

/-- The **relator-`z` pair** of `c` relative to a base marking `t`: the fibre coordinates of the
tame and wild relator values of the lifted marking — the degree-2 obstruction of `c`, pre-quotient
by `im d1_triv`. -/
noncomputable def relZPair [Finite L] (t : Marking L) (c : TwoCocycle L) : ZMod 2 × ZMod 2 :=
  ((liftMark t c).tameValue.fib, (liftMark t c).wildValue.fib)

/-- When the base marking satisfies the tame relation, the lifted tame relator value is exactly the
central element `(1, tameZ)` — the relator "dies into the fibre". -/
theorem liftMark_tameValue_eq_incl (t : Marking L) (ht : t.TameRel) (c : TwoCocycle L) :
    (liftMark t c).tameValue = CentExt.incl c (liftMark t c).tameValue.fib := by
  rw [← CentExt.base_eq_one_iff, liftMark_tameValue_base]
  exact (Marking.tameValue_eq_one_iff t).mpr ht

/-- When the base marking satisfies the wild relation, the lifted wild relator value is exactly the
central element `(1, wildZ)`. -/
theorem liftMark_wildValue_eq_incl [Finite L] (t : Marking L) (hw : t.WildRel)
    (c : TwoCocycle L) :
    (liftMark t c).wildValue = CentExt.incl c (liftMark t c).wildValue.fib := by
  rw [← CentExt.base_eq_one_iff, liftMark_wildValue_base]
  exact (Marking.wildValue_eq_one_iff t).mpr hw

/-! ## The shifted lift and its wild `Pro2Core`

For the injectivity of `θ` we adjust the fibre coordinates of the lifted marking by `a : Fin 4 → 𝔽₂`
(so the relators can be made to die *exactly*), then run the `NA_le_ker` machinery of c1.  The
`Pro2Core` clause of admissibility is the hard sub-step; it holds by the same argument as c1
(`isPGroup_liftMarking_wildCore`): the wild core lands in `proj⁻¹(base wild core)`, a `2`-group as an
extension of the base wild core by the central `𝔽₂`. -/

/-- The lifted marking with the four fibre coordinates shifted by `a`. -/
def shiftLiftMark (t : Marking L) (a : Fin 4 → ZMod 2) (c : TwoCocycle L) : Marking (CentExt c) :=
  ⟨(t.σ, a 0), (t.τ, a 1), (t.x₀, a 2), (t.x₁, a 3)⟩

@[simp] theorem shiftLiftMark_map_proj (t : Marking L) (a : Fin 4 → ZMod 2) (c : TwoCocycle L) :
    (shiftLiftMark t a c).map (CentExt.proj c) = t := rfl

/-- The base projection's kernel `{(1, z)} ≅ 𝔽₂` is elementary-2. -/
theorem isPGroup_proj_ker (c : TwoCocycle L) : IsPGroup 2 (CentExt.proj c).ker := by
  intro g
  have hb : g.1.base = 1 := MonoidHom.mem_ker.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [SubmonoidClass.coe_pow, pow_one, pow_two]
  exact CentExt.ext (by simp [hb]) (by simp [hb, c.norm, CharTwo.add_self_eq_zero])

/-- **The `Pro2Core` crux for the extension.**  If the base marking's wild core is a `2`-group, so
is the shifted lift's — an extension of it by the central `𝔽₂` (`IsPGroup.comap_of_injective` route,
exactly as c1's `isPGroup_liftMarking_wildCore`). -/
theorem isPGroup_shiftLift_wildCore (t : Marking L) (a : Fin 4 → ZMod 2) (c : TwoCocycle L)
    (ht2 : IsPGroup 2 (Subgroup.normalClosure {t.x₀, t.x₁})) :
    IsPGroup 2 (Subgroup.normalClosure
      {(shiftLiftMark t a c).x₀, (shiftLiftMark t a c).x₁}) := by
  refine (ht2.comap_of_ker_isPGroup (CentExt.proj c) (isPGroup_proj_ker c)).to_le
    (Subgroup.normalClosure_le_normal ?_)
  rintro w (rfl | rfl)
  · exact Subgroup.subset_normalClosure (Set.mem_insert _ _)
  · exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ rfl)

/-- The shifted lift's tame relator value projects to the base's. -/
theorem shiftLiftMark_tameValue_base (t : Marking L) (a : Fin 4 → ZMod 2) (c : TwoCocycle L) :
    (shiftLiftMark t a c).tameValue.base = t.tameValue :=
  shiftLiftMark_map_proj t a c ▸
    (Marking.map_tameValue (CentExt.proj c) (shiftLiftMark t a c)).symm

/-- The shifted lift's wild relator value projects to the base's (needs `L` finite). -/
theorem shiftLiftMark_wildValue_base [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2)
    (c : TwoCocycle L) : (shiftLiftMark t a c).wildValue.base = t.wildValue :=
  shiftLiftMark_map_proj t a c ▸
    (Marking.map_wildValue (CentExt.proj c) (shiftLiftMark t a c)).symm

/-- **Tame relator dies exactly.**  When the base marking satisfies the tame relation and the shifted
tame `z`-value is `0`, the shifted lift's tame relator value is the identity of the extension. -/
theorem shiftLiftMark_tameValue_eq_one (t : Marking L) (ht : t.TameRel) (a : Fin 4 → ZMod 2)
    (c : TwoCocycle L) (hz : (shiftLiftMark t a c).tameValue.fib = 0) :
    (shiftLiftMark t a c).tameValue = 1 := by
  apply CentExt.ext
  · rw [shiftLiftMark_tameValue_base, (Marking.tameValue_eq_one_iff t).mpr ht, CentExt.one_base]
  · rw [hz, CentExt.one_fib]

/-- **Wild relator dies exactly.**  When the base marking satisfies the wild relation and the shifted
wild `z`-value is `0`, the shifted lift's wild relator value is the identity of the extension. -/
theorem shiftLiftMark_wildValue_eq_one [Finite L] (t : Marking L) (hw : t.WildRel)
    (a : Fin 4 → ZMod 2) (c : TwoCocycle L) (hz : (shiftLiftMark t a c).wildValue.fib = 0) :
    (shiftLiftMark t a c).wildValue = 1 := by
  apply CentExt.ext
  · rw [shiftLiftMark_wildValue_base, (Marking.wildValue_eq_one_iff t).mpr hw, CentExt.one_base]
  · rw [hz, CentExt.one_fib]

/-! ## The splitting section: `N_A ≤ ker (classify (shifted lift))`

The injectivity crux, an exact mirror of c1's `WordCohBridge.NA_le_ker_classify`: over a finite
admissible level `L = F₄ ⧸ U` (`N_A ≤ U`), if the shifted lift's relators die exactly, the
classified `F₄ → CentExt c` hom kills `N_A` — `ker` is an admissible open (`Generates` automatic,
relators die, `Pro2Core` from `isPGroup_shiftLift_wildCore` transferred along `kerLift`). -/

/-- **`N_A ≤ ker` for the shifted lift.**  (`[Finite (F₄ ⧸ U)]` is needed at statement level for
`CentExt c` to be finite — it is not a global instance; callers supply it via
`Subgroup.quotient_finite_of_isOpen _ U.isOpen'`.) -/
theorem NA_le_ker_shiftLift (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)]
    (hU : NA ≤ U.toSubgroup) (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValue.fib
      = 0) :
    NA ≤ (Marking.classify
      (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c)).toMonoidHom.ker := by
  set t_L := univMarking.map (QuotientGroup.mk' U.toSubgroup) with ht_L
  have hadmL : t_L.Admissible := isAdmissibleU_of_NA_le hU
  set m := Marking.classify (shiftLiftMark t_L a c) with hm
  have hut : univMarking.map m.toMonoidHom = shiftLiftMark t_L a c := by
    rw [hm, Marking.classify, univMarking_map_toHom]
  have htame : m.toMonoidHom univMarking.tameRelator = 1 :=
    (Marking.map_tameRelator_eq_one_iff m univMarking).mpr (by
      rw [hut]
      exact (Marking.tameValue_eq_one_iff _).mp
        (shiftLiftMark_tameValue_eq_one t_L hadmL.2.1 a c htame0))
  have hwild : m.toMonoidHom univMarking.wildRelator = 1 :=
    (Marking.map_wildRelator_eq_one_iff m univMarking).mpr (by
      rw [hut]
      exact (Marking.wildValue_eq_one_iff _).mp
        (shiftLiftMark_wildValue_eq_one t_L hadmL.2.2.1 a c hwild0))
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
  have hadm : IsAdmissibleU V := by
    refine ⟨generates_univMarking_map _, ?_, ?_, ?_⟩
    · exact (Marking.map_tameRelator_eq_one_iff (quotientMk V.toSubgroup) univMarking).mp
        ((QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr htame))
    · exact (Marking.map_wildRelator_eq_one_iff (quotientMk V.toSubgroup) univMarking).mp
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
  exact (isAdmissibleU_iff_NA_le V).mp hadm

/-- **The splitting section** `Γ_A → CentExt c` produced by `NA_le_ker_shiftLift`: the descended
`classify` of the (relator-killing) shifted lift. -/
noncomputable def sectionHom (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NA ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValue.fib
      = 0) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA)
      (CentExt c) :=
  quotientLift NA (Marking.classify (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup))
    a c)) (NA_le_ker_shiftLift U hU c a htame0 hwild0)

/-- The section splits the base projection: `proj ∘ s` is the level projection `Γ_A ↠ F₄ ⧸ U`
(pointwise, `proj (s (mk_{N_A} g)) = mk_U g`).  Proof by `Marking.toHom_hom_univMarking_map`
uniqueness: both `projC ∘ classify(shifted lift)` and `quotientMk U` push `univMarking` to `t_L`. -/
theorem projC_comp_sectionHom (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NA ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValue.fib
      = 0) (g : FreeProfiniteGroup (Fin 4)) :
    (sectionHom U hU c a htame0 hwild0 (quotientMk NA g)).base = QuotientGroup.mk' U.toSubgroup g := by
  haveI : DiscreteTopology (FreeProfiniteGroup (Fin 4) ⧸
      (U.toOpenSubgroup : Subgroup (FreeProfiniteGroup (Fin 4)))) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul U.toOpenSubgroup
  set t_L := univMarking.map (QuotientGroup.mk' U.toSubgroup) with ht_L
  set m := Marking.classify (shiftLiftMark t_L a c) with hm
  -- the base projection as a continuous hom (`CentExt c` is discrete; `F₄ ⧸ U` is topological here)
  let projC : ContinuousMonoidHom (CentExt c) (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) :=
    ⟨CentExt.proj c, continuous_of_discreteTopology⟩
  have hut : univMarking.map m.toMonoidHom = shiftLiftMark t_L a c := by
    rw [hm, Marking.classify, univMarking_map_toHom]
  have hcomp : projC.comp m = quotientMk U.toSubgroup := by
    have e1 : univMarking.map (projC.comp m).toMonoidHom = t_L := by
      show univMarking.map ((CentExt.proj c).comp m.toMonoidHom) = t_L
      rw [← Marking.map_map, hut, shiftLiftMark_map_proj]
    have e2 : univMarking.map (quotientMk U.toSubgroup).toMonoidHom = t_L := rfl
    rw [← Marking.toHom_hom_univMarking_map (projC.comp m),
        ← Marking.toHom_hom_univMarking_map (quotientMk U.toSubgroup), e1, e2]
  show CentExt.proj c (sectionHom U hU c a htame0 hwild0 (quotientMk NA g)) = _
  rw [sectionHom, quotientLift_quotientMk]
  exact DFunLike.congr_fun hcomp g

/-! ## Coboundary extraction — the θ-injectivity payoff

Once the shifted lift's relators die, the level cocycle pulled back to `Γ_A` (as the base-coordinate
pairing of the section) is `dOne` of the continuous 1-cochain `λ = fib ∘ s`, hence a continuous
2-coboundary.  This is the concrete "extension splits ⇒ cocycle is a coboundary" step. -/

section Coboundary

open ContCoh

variable [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **Coboundary extraction.**  With `𝔽₂` a trivial `Γ_A`-module, the 2-cocycle
`(x,y) ↦ c.κ ((s x).base) ((s y).base)` — the level cocycle pulled back through the splitting
section `s` — is a continuous 2-coboundary `dOne (fib ∘ s)`.  (`dOne λ (x,y) = λ(y) − λ(xy) + λ(x)`
at trivial action; the section's fibre law `λ(xy) = λ(x) + λ(y) + c.κ((s x).base,(s y).base)` makes
this equal to the pairing, an 8-case `𝔽₂` identity.) -/
theorem cocycle_mem_B2 (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NA ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)) (a : Fin 4 → ZMod 2)
    (htame0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).tameValue.fib
      = 0)
    (hwild0 : (shiftLiftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) a c).wildValue.fib
      = 0)
    (htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m) :
    (fun p : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) =>
        c.κ (sectionHom U hU c a htame0 hwild0 p.1).base
            (sectionHom U hU c a htame0 hwild0 p.2).base)
      ∈ B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) := by
  set s := sectionHom U hU c a htame0 hwild0 with hs
  have key : ∀ x y z : ZMod 2, y - (x + y + z) + x = z := by decide
  refine ⟨fun x => (s x).fib, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_C1_iff]
    exact (continuous_of_discreteTopology (f := CentExt.fib)).comp s.continuous_toFun
  · funext p
    obtain ⟨x, y⟩ := p
    show x • (s y).fib - (s (x * y)).fib + (s x).fib = c.κ (s x).base (s y).base
    rw [htriv, map_mul s, CentExt.mul_fib]
    exact key (s x).fib (s y).fib (c.κ (s x).base (s y).base)

end Coboundary

/-! ## The shift laws — how a generator shift moves the fibre obstruction

`shiftLiftMark t a c` is `liftMark t c` with generator `i` left-multiplied by the central
`incl (a i)`.  Evaluating the tame/wild relator words, *each* fibre obstruction shifts by exactly
`a 1` (the `τ`-coordinate): the tame and wild relators both have odd `τ`-content and even content in
`σ, x₀, x₁` (mod 2) — the same content computation as the trivial-module differential
`d¹ = (a₁, a₁)` of `FoxH.d1Fun_of_trivial`.  We transport that computation through the comparison
hom `WordLift (ZMod 2) (CentExt c) →* CentExt c`, `⟨z, g⟩ ↦ incl z · g`, which realizes
`shiftLiftMark t a c` as `(liftMarking (liftMark t c) a).map _`.  (Note both fibres move by the *same*
`a 1`, so the shift always stays in the diagonal `Δ = im d¹_triv` — exactly what makes `θ` land in
`𝔽₂²/Δ` and its kernel adjustable by a shift.) -/

section ShiftLaws

open FoxH

variable {L : Type*} [Group L] {c : TwoCocycle L}

/-- The extension acts trivially on the coefficient `ZMod 2`. -/
local instance trivAction : DistribMulAction (CentExt c) (ZMod 2) where
  smul _ z := z
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The comparison hom `⟨z, g⟩ ↦ incl z · g`, `WordLift (ZMod 2) (CentExt c) →* CentExt c`. -/
def shiftCompare : WordLift (ZMod 2) (CentExt c) →* CentExt c where
  toFun p := CentExt.incl c p.u * p.g
  map_one' := mul_one 1
  map_mul' p q := by
    apply CentExt.ext
    · simp only [CentExt.mul_base, WordLift.mul_g, CentExt.incl_base, one_mul]
    · simp only [CentExt.mul_fib, CentExt.mul_base, WordLift.mul_u, WordLift.mul_g,
        CentExt.incl_fib, CentExt.incl_base, c.κ_one_left, one_mul,
        show ∀ (g : CentExt c) (z : ZMod 2), g • z = z from fun _ _ => rfl]
      abel

@[simp] theorem shiftCompare_apply (p : WordLift (ZMod 2) (CentExt c)) :
    shiftCompare p = CentExt.incl c p.u * p.g := rfl

theorem shiftCompare_fib (p : WordLift (ZMod 2) (CentExt c)) :
    (shiftCompare p).fib = p.u + p.g.fib :=
  CentExt.incl_mul_fib p.u p.g

/-- The base projection `⟨z, g⟩ ↦ g`, `WordLift (ZMod 2) (CentExt c) →* CentExt c`. -/
def wlBase : WordLift (ZMod 2) (CentExt c) →* CentExt c where
  toFun := WordLift.g
  map_one' := rfl
  map_mul' _ _ := rfl

/-- `shiftCompare ⟨z, (g, 0)⟩ = (g, z)` — the central shift applied to a zero-fibre lift. -/
theorem shiftCompare_liftGen (g : L) (z : ZMod 2) :
    shiftCompare (⟨z, ((g, 0) : CentExt c)⟩ : WordLift (ZMod 2) (CentExt c)) = ((g, z) : CentExt c) :=
  CentExt.ext (one_mul g) <| by
    show z + (0 : ZMod 2) + c.κ 1 g = z
    rw [c.κ_one_left, add_zero, add_zero]

/-- `liftMarking (liftMark t c) a` projects (via `wlBase`) back to `liftMark t c`. -/
@[simp] theorem map_wlBase_liftMarking (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).map wlBase = liftMark t c := rfl

/-- `liftMarking (liftMark t c) a` maps (via `shiftCompare`) to `shiftLiftMark t a c`. -/
theorem map_shiftCompare_liftMarking (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).map shiftCompare = shiftLiftMark t a c := by
  simp only [liftMarking, liftMark, Marking.map, shiftLiftMark, Marking.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact shiftCompare_liftGen _ _

/-- The tame relator value's base coordinate of the lift recovers that of `liftMark t c`. -/
theorem liftMarking_tameValue_g (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).tameValue.g = (liftMark t c).tameValue :=
  map_wlBase_liftMarking t a ▸ (Marking.map_tameValue wlBase (liftMarking (liftMark t c) a)).symm

/-- The wild relator value's base coordinate of the lift recovers that of `liftMark t c`. -/
theorem liftMarking_wildValue_g [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).wildValue.g = (liftMark t c).wildValue :=
  map_wlBase_liftMarking t a ▸ (Marking.map_wildValue wlBase (liftMarking (liftMark t c) a)).symm

/-- The tame fibre shift of the lift is `a 1` (trivial action, char 2 — relation-free). -/
theorem liftMarking_tameValue_u_eq (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).tameValue.u = a 1 := by
  set T := liftMarking (liftMark t c) a with hT
  show (conjP T.τ T.σ * (T.τ ^ 2)⁻¹).u = a 1
  rw [WordLift.mul_u_of_trivial _ _ (fun _ => rfl),
      WordLift.conjP_u_of_trivial T.τ T.σ (fun _ => rfl) (fun _ => rfl),
      WordLift.inv_u_of_trivial _ (fun _ => rfl), pow_two,
      WordLift.mul_u_of_trivial _ _ (fun _ => rfl)]
  show a 1 + -(a 1 + a 1) = a 1
  rw [CharTwo.add_self_eq_zero, neg_zero, add_zero]

/-- The wild fibre shift of the lift is `a 1` (`liftMarking_wildValue_u` at trivial action, char 2). -/
theorem liftMarking_wildValue_u_eq [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (liftMarking (liftMark t c) a).wildValue.u = a 1 := by
  rw [liftMarking_wildValue_u (liftMark t c) a (fun v => CharTwo.add_self_eq_zero v)
      (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)]
  show a 1 + a 3 + a 3 = a 1
  rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]

/-- **Tame shift law**: shifting the lift by `a` changes the tame fibre obstruction by `a 1`. -/
theorem shiftLiftMark_tameValue_fib (t : Marking L) (a : Fin 4 → ZMod 2) :
    (shiftLiftMark t a c).tameValue.fib = (liftMark t c).tameValue.fib + a 1 := by
  rw [← map_shiftCompare_liftMarking t a, Marking.map_tameValue, shiftCompare_fib,
      liftMarking_tameValue_u_eq, liftMarking_tameValue_g, add_comm]

/-- **Wild shift law**: shifting the lift by `a` changes the wild fibre obstruction by `a 1`. -/
theorem shiftLiftMark_wildValue_fib [Finite L] (t : Marking L) (a : Fin 4 → ZMod 2) :
    (shiftLiftMark t a c).wildValue.fib = (liftMark t c).wildValue.fib + a 1 := by
  rw [← map_shiftCompare_liftMarking t a, Marking.map_wildValue, shiftCompare_fib,
      liftMarking_wildValue_u_eq, liftMarking_wildValue_g, add_comm]

/-- **The `d¹`-adjustment.**  When the tame and wild fibre obstructions of `liftMark t c` agree
(i.e. `relZPair ∈ Δ = im d¹_triv`), the constant shift `a ≡ (liftMark t c).tameValue.fib` makes
*both* shifted relator fibres vanish — the hypothesis feeding `NA_le_ker_shiftLift`. -/
theorem exists_shift_of_relZ_eq [Finite L] (t : Marking L)
    (hrel : (liftMark t c).tameValue.fib = (liftMark t c).wildValue.fib) :
    ∃ a : Fin 4 → ZMod 2, (shiftLiftMark t a c).tameValue.fib = 0
      ∧ (shiftLiftMark t a c).wildValue.fib = 0 := by
  refine ⟨fun _ => (liftMark t c).tameValue.fib, ?_, ?_⟩
  · rw [shiftLiftMark_tameValue_fib, CharTwo.add_self_eq_zero]
  · rw [shiftLiftMark_wildValue_fib, ← hrel, CharTwo.add_self_eq_zero]

end ShiftLaws

/-! ## Level change: pulling a cocycle back along a group hom

For the well-definedness of `θ` across refinements, we record that the relator obstruction
`relZPair` is *natural*: pulling a cocycle `c` back along `φ : L' →* L` and pushing the base marking
forward by `φ` give the same obstruction.  The comparison hom is `projExt : CentExt (c.comap φ) →*
CentExt c`, `(l, z) ↦ (φ l, z)`. -/

section LevelChange

variable {L L' : Type*} [Group L] [Group L']

/-- Pull back a 2-cocycle along a group hom `φ : L' →* L`. -/
def TwoCocycle.comap (c : TwoCocycle L) (φ : L' →* L) : TwoCocycle L' where
  κ a b := c.κ (φ a) (φ b)
  norm := by simp only [map_one]; exact c.norm
  cocyc a b d := by simp only [map_mul]; exact c.cocyc (φ a) (φ b) (φ d)

@[simp] theorem TwoCocycle.comap_κ (c : TwoCocycle L) (φ : L' →* L) (a b : L') :
    (c.comap φ).κ a b = c.κ (φ a) (φ b) := rfl

/-- The base hom `φ` lifts to a hom of central extensions `CentExt (c.comap φ) →* CentExt c`. -/
def projExt (c : TwoCocycle L) (φ : L' →* L) : CentExt (c.comap φ) →* CentExt c where
  toFun p := ((φ p.base, p.fib) : CentExt c)
  map_one' := CentExt.ext (map_one φ) rfl
  map_mul' p q := CentExt.ext (map_mul φ p.base q.base) rfl

@[simp] theorem projExt_fib (c : TwoCocycle L) (φ : L' →* L) (p : CentExt (c.comap φ)) :
    (projExt c φ p).fib = p.fib := rfl

/-- `liftMark t' (c.comap φ)` maps to `liftMark (t'.map φ) c` under `projExt`. -/
theorem map_projExt_liftMark (t' : Marking L') (c : TwoCocycle L) (φ : L' →* L) :
    (liftMark t' (c.comap φ)).map (projExt c φ) = liftMark (t'.map φ) c := rfl

/-- **Level-independence of the relator obstruction.**  Pulling `c` back along `φ` and pushing the
base marking forward by `φ` give the same `relZPair`. -/
theorem relZPair_comap [Finite L] [Finite L'] (t' : Marking L') (c : TwoCocycle L) (φ : L' →* L) :
    relZPair (t'.map φ) c = relZPair t' (c.comap φ) := by
  have ht := Marking.map_tameValue (projExt c φ) (liftMark t' (c.comap φ))
  have hw := Marking.map_wildValue (projExt c φ) (liftMark t' (c.comap φ))
  rw [map_projExt_liftMark] at ht hw
  apply Prod.ext
  · show (liftMark (t'.map φ) c).tameValue.fib = (liftMark t' (c.comap φ)).tameValue.fib
    rw [ht, projExt_fib]
  · show (liftMark (t'.map φ) c).wildValue.fib = (liftMark t' (c.comap φ)).wildValue.fib
    rw [hw, projExt_fib]

end LevelChange

/-! ## Additivity of the relator obstruction (the Baer sum)

`relZPair t (c₁ + c₂) = relZPair t c₁ + relZPair t c₂`.  The comparison object is the *fiber
product* `FiberProd c₁ c₂ = L ×_κ 𝔽₂²`, the central extension of `L` by `𝔽₂ × 𝔽₂` with the pair
cocycle `(κ₁, κ₂)`.  Its three coefficient homs `pr₁, pr₂, prSum` (first fibre, second fibre, fibre
sum) carry the fiber-product lift onto `liftMark t c₁`, `liftMark t c₂`, `liftMark t (c₁ + c₂)`; the
relator values then add by `Marking.map_{tame,wild}Value` (exactly the `d1Fun_add` pattern).  Note
`prSum : FiberProd →* CentExt (c₁ + c₂)` is a hom precisely because the summed fibre matches
`κ₁ + κ₂`; the naive `CentExt (c₁ + c₂) →* CentExt c₁ × CentExt c₂` is *not* a homomorphism. -/

section Additivity

variable {L : Type*} [Group L]

/-- Pointwise sum of 2-cocycles. -/
instance : Add (TwoCocycle L) where
  add c₁ c₂ :=
    { κ := fun a b => c₁.κ a b + c₂.κ a b
      norm := by rw [c₁.norm, c₂.norm, add_zero]
      cocyc := fun a b d => by
        have h1 := c₁.cocyc a b d; have h2 := c₂.cocyc a b d; linear_combination h1 + h2 }

@[simp] theorem TwoCocycle.add_κ (c₁ c₂ : TwoCocycle L) (a b : L) :
    (c₁ + c₂).κ a b = c₁.κ a b + c₂.κ a b := rfl

/-- The fiber product `CentExt c₁ ×_L CentExt c₂`: a central extension of `L` by `𝔽₂ × 𝔽₂`. -/
def FiberProd (_c₁ _c₂ : TwoCocycle L) : Type _ := L × ZMod 2 × ZMod 2

namespace FiberProd

variable {c₁ c₂ : TwoCocycle L}

/-- Base coordinate. -/
def base (p : FiberProd c₁ c₂) : L := p.1
/-- First fibre coordinate. -/
def fibA (p : FiberProd c₁ c₂) : ZMod 2 := p.2.1
/-- Second fibre coordinate. -/
def fibB (p : FiberProd c₁ c₂) : ZMod 2 := p.2.2

@[ext] theorem ext {p q : FiberProd c₁ c₂} (h1 : p.base = q.base) (h2 : p.fibA = q.fibA)
    (h3 : p.fibB = q.fibB) : p = q :=
  Prod.ext h1 (Prod.ext h2 h3)

instance : Group (FiberProd c₁ c₂) where
  mul p q := (p.1 * q.1, p.2.1 + q.2.1 + c₁.κ p.1 q.1, p.2.2 + q.2.2 + c₂.κ p.1 q.1)
  one := (1, 0, 0)
  inv p := (p.1⁻¹, p.2.1 + c₁.κ p.1 p.1⁻¹, p.2.2 + c₂.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply FiberProd.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2.1 + q.2.1 + c₁.κ p.1 q.1 + r.2.1 + c₁.κ (p.1 * q.1) r.1
        = p.2.1 + (q.2.1 + r.2.1 + c₁.κ q.1 r.1) + c₁.κ p.1 (q.1 * r.1)
      linear_combination c₁.cocyc p.1 q.1 r.1
    · show p.2.2 + q.2.2 + c₂.κ p.1 q.1 + r.2.2 + c₂.κ (p.1 * q.1) r.1
        = p.2.2 + (q.2.2 + r.2.2 + c₂.κ q.1 r.1) + c₂.κ p.1 (q.1 * r.1)
      linear_combination c₂.cocyc p.1 q.1 r.1
  one_mul p := by
    apply FiberProd.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2.1 + c₁.κ 1 p.1 = p.2.1; rw [c₁.κ_one_left, add_zero, zero_add]
    · show (0 : ZMod 2) + p.2.2 + c₂.κ 1 p.1 = p.2.2; rw [c₂.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply FiberProd.ext
    · exact mul_one p.1
    · show p.2.1 + 0 + c₁.κ p.1 1 = p.2.1; rw [c₁.κ_one_right, add_zero, add_zero]
    · show p.2.2 + 0 + c₂.κ p.1 1 = p.2.2; rw [c₂.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply FiberProd.ext
    · exact inv_mul_cancel p.1
    · show p.2.1 + c₁.κ p.1 p.1⁻¹ + p.2.1 + c₁.κ p.1⁻¹ p.1 = 0
      rw [c₁.κ_inv]
      exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _
    · show p.2.2 + c₂.κ p.1 p.1⁻¹ + p.2.2 + c₂.κ p.1⁻¹ p.1 = 0
      rw [c₂.κ_inv]
      exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] theorem mul_base (p q : FiberProd c₁ c₂) : (p * q).base = p.base * q.base := rfl

/-- Projection to the first central extension. -/
def pr1 : FiberProd c₁ c₂ →* CentExt c₁ where
  toFun p := ((p.base, p.fibA) : CentExt c₁)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the second central extension. -/
def pr2 : FiberProd c₁ c₂ →* CentExt c₂ where
  toFun p := ((p.base, p.fibB) : CentExt c₂)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The fibre-sum hom to the sum extension — a homomorphism because `fibA + fibB` tracks `κ₁ + κ₂`. -/
def prSum : FiberProd c₁ c₂ →* CentExt (c₁ + c₂) where
  toFun p := ((p.base, p.fibA + p.fibB) : CentExt (c₁ + c₂))
  map_one' := CentExt.ext rfl (add_zero (0 : ZMod 2))
  map_mul' p q := CentExt.ext rfl <| by
    show (p.fibA + q.fibA + c₁.κ p.base q.base) + (p.fibB + q.fibB + c₂.κ p.base q.base)
        = (p.fibA + p.fibB) + (q.fibA + q.fibB) + (c₁.κ p.base q.base + c₂.κ p.base q.base)
    ring

@[simp] theorem pr1_fib (p : FiberProd c₁ c₂) : (pr1 p).fib = p.fibA := rfl
@[simp] theorem pr2_fib (p : FiberProd c₁ c₂) : (pr2 p).fib = p.fibB := rfl
@[simp] theorem prSum_fib (p : FiberProd c₁ c₂) : (prSum p).fib = p.fibA + p.fibB := rfl

instance [Finite L] : Finite (FiberProd c₁ c₂) := inferInstanceAs (Finite (L × ZMod 2 × ZMod 2))

end FiberProd

/-- The fiber-product lift of a base marking (both fibres zero). -/
def liftMarkFP (t : Marking L) (c₁ c₂ : TwoCocycle L) : Marking (FiberProd c₁ c₂) :=
  ⟨(t.σ, 0, 0), (t.τ, 0, 0), (t.x₀, 0, 0), (t.x₁, 0, 0)⟩

@[simp] theorem map_pr1_liftMarkFP (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.pr1 = liftMark t c₁ := rfl

@[simp] theorem map_pr2_liftMarkFP (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.pr2 = liftMark t c₂ := rfl

@[simp] theorem map_prSum_liftMarkFP (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    (liftMarkFP t c₁ c₂).map FiberProd.prSum = liftMark t (c₁ + c₂) := by
  simp only [liftMarkFP, Marking.map, liftMark, Marking.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact CentExt.ext rfl (add_zero (0 : ZMod 2))

/-- **Additivity of the relator obstruction.** -/
theorem relZPair_add [Finite L] (t : Marking L) (c₁ c₂ : TwoCocycle L) :
    relZPair t (c₁ + c₂) = relZPair t c₁ + relZPair t c₂ := by
  have ht1 := Marking.map_tameValue FiberProd.pr1 (liftMarkFP t c₁ c₂)
  have hw1 := Marking.map_wildValue FiberProd.pr1 (liftMarkFP t c₁ c₂)
  have ht2 := Marking.map_tameValue FiberProd.pr2 (liftMarkFP t c₁ c₂)
  have hw2 := Marking.map_wildValue FiberProd.pr2 (liftMarkFP t c₁ c₂)
  have hts := Marking.map_tameValue FiberProd.prSum (liftMarkFP t c₁ c₂)
  have hws := Marking.map_wildValue FiberProd.prSum (liftMarkFP t c₁ c₂)
  rw [map_pr1_liftMarkFP] at ht1 hw1
  rw [map_pr2_liftMarkFP] at ht2 hw2
  rw [map_prSum_liftMarkFP] at hts hws
  apply Prod.ext
  · show (liftMark t (c₁ + c₂)).tameValue.fib
        = (liftMark t c₁).tameValue.fib + (liftMark t c₂).tameValue.fib
    rw [hts, ht1, ht2, FiberProd.prSum_fib, FiberProd.pr1_fib, FiberProd.pr2_fib]
  · show (liftMark t (c₁ + c₂)).wildValue.fib
        = (liftMark t c₁).wildValue.fib + (liftMark t c₂).wildValue.fib
    rw [hws, hw1, hw2, FiberProd.prSum_fib, FiberProd.pr1_fib, FiberProd.pr2_fib]

end Additivity

/-! ## Vanishing on coboundaries: `obs` kills `B²` (upgrading `#H² ≤ 2` to `H² ↪ 𝔽₂`)

The obstruction `obs` (the sum of the tame and wild relator fibre values) vanishes on continuous
2-coboundaries.  The mechanism: a finite-level coboundary `κ = δ¹λ` gives a central extension
`CentExt (δ¹λ)` that is *trivialised* by `Ψ_λ : (l, z) ↦ (l, z + λ l)` onto the split extension
`CentExt 0`.  Under `Ψ_λ`, the lifted marking becomes the `λ`-shifted split marking, whose relator
fibres are `a 1` (the shift laws) plus `λ` of the (dying) relator base — so both relator fibres pick
up the *same* value and their sum is `0`.  Combined with `obs_ker_le`, this makes `obs` descend to an
injection `H²(Γ_A, 𝔽₂) ↪ 𝔽₂` — the degree-2 presentation-comparison, reusable Thm-4.2-ward. -/

section CoboundaryObstruction

variable {L : Type*} [Group L]

/-- The trivial marking (all four generators `1`) satisfies the tame relation. -/
theorem trivialMarking_tameValue : (⟨1, 1, 1, 1⟩ : Marking L).tameValue = 1 := by
  rw [Marking.tameValue_eq_one_iff]
  simp [Marking.TameRel, conjP]

/-- The trivial marking (all four generators `1`) satisfies the wild relation. -/
theorem trivialMarking_wildValue : (⟨1, 1, 1, 1⟩ : Marking L).wildValue = 1 := by
  rw [Marking.wildValue_eq_one_iff]
  simp [Marking.WildRel, Marking.h0, Marking.u1, Marking.u, Marking.c0, Marking.d0,
    Marking.u0, Marking.z0, Marking.sigma2, Marking.g0, Marking.dg, Marking.hc,
    conjP, commP, powOmega2]

/-- The **trivial (split) 2-cocycle** `κ ≡ 0`: `CentExt zeroCocycle = L × 𝔽₂` is the direct product. -/
def zeroCocycle : TwoCocycle L where
  κ _ _ := 0
  norm := rfl
  cocyc _ _ _ := rfl

/-- The fibre projection `CentExt zeroCocycle →* Multiplicative 𝔽₂` — a homomorphism because the
split extension is the direct product (`κ ≡ 0`). -/
def fibHom0 : CentExt (zeroCocycle : TwoCocycle L) →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd p.fib
  map_one' := rfl
  map_mul' p q := by
    show Multiplicative.ofAdd (p * q).fib = Multiplicative.ofAdd p.fib * Multiplicative.ofAdd q.fib
    rw [CentExt.mul_fib, show (zeroCocycle : TwoCocycle L).κ p.base q.base = (0 : ZMod 2) from rfl,
      add_zero, ofAdd_add]

/-- The split extension has **balanced (zero) relator obstruction**: both relator fibres vanish, as
they are the image of the trivial marking `⟨1, 1, 1, 1⟩` under `fibHom0`. -/
theorem relZPair_zero [Finite L] (t : Marking L) :
    relZPair t (zeroCocycle : TwoCocycle L) = (0, 0) := by
  have hmap : (liftMark t (zeroCocycle : TwoCocycle L)).map fibHom0
      = (⟨1, 1, 1, 1⟩ : Marking (Multiplicative (ZMod 2))) := rfl
  apply Prod.ext
  · have h := Marking.map_tameValue fibHom0 (liftMark t (zeroCocycle : TwoCocycle L))
    rw [hmap, trivialMarking_tameValue] at h
    exact (Multiplicative.ofAdd.injective h.symm : _)
  · have h := Marking.map_wildValue fibHom0 (liftMark t (zeroCocycle : TwoCocycle L))
    rw [hmap, trivialMarking_wildValue] at h
    exact (Multiplicative.ofAdd.injective h.symm : _)

/-- The **coboundary 2-cocycle** `δ¹λ`: `κ (a, b) = λ a + λ b + λ (a b)` (trivial action, `char 2`).
Requires the normalization `λ 1 = 0`. -/
def coboundaryCocycle (lam : L → ZMod 2) (hlam1 : lam 1 = 0) : TwoCocycle L where
  κ a b := lam a + lam b + lam (a * b)
  norm := by simp [hlam1]
  cocyc a b c := by
    show lam a + lam b + lam (a * b) + (lam (a * b) + lam c + lam (a * b * c))
      = lam a + lam (b * c) + lam (a * (b * c)) + (lam b + lam c + lam (b * c))
    rw [mul_assoc a b c]
    abel_nf
    simp [CharTwo.two_eq_zero]

/-- The **trivialization hom** `Ψ_λ : (l, z) ↦ (l, z + λ l)`, an iso `CentExt (δ¹λ) ≃* CentExt 0`
of the coboundary extension with the split extension. -/
def Psi (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    CentExt (coboundaryCocycle lam hlam1) →* CentExt (zeroCocycle : TwoCocycle L) where
  toFun p := ((p.base, p.fib + lam p.base) : CentExt (zeroCocycle : TwoCocycle L))
  map_one' := CentExt.ext rfl (by show (0 : ZMod 2) + lam 1 = 0; simp [hlam1])
  map_mul' p q := by
    refine CentExt.ext rfl ?_
    · show (p * q).fib + lam (p * q).base
          = (p.fib + lam p.base) + (q.fib + lam q.base) + (zeroCocycle : TwoCocycle L).κ p.base q.base
      rw [CentExt.mul_fib, CentExt.mul_base,
        show (zeroCocycle : TwoCocycle L).κ p.base q.base = (0 : ZMod 2) from rfl,
        show (coboundaryCocycle lam hlam1).κ p.base q.base
          = lam p.base + lam q.base + lam (p.base * q.base) from rfl]
      abel_nf
      simp [CharTwo.two_eq_zero]

@[simp] theorem Psi_fib (lam : L → ZMod 2) (hlam1 : lam 1 = 0)
    (p : CentExt (coboundaryCocycle lam hlam1)) : (Psi lam hlam1 p).fib = p.fib + lam p.base := rfl

/-- `Ψ_λ` carries the lifted marking of the coboundary extension onto the `λ`-shifted split
marking. -/
theorem map_Psi_liftMark (t : Marking L) (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    (liftMark t (coboundaryCocycle lam hlam1)).map (Psi lam hlam1)
      = shiftLiftMark t ![lam t.σ, lam t.τ, lam t.x₀, lam t.x₁] zeroCocycle := by
  simp only [liftMark, Marking.map, shiftLiftMark, Marking.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> exact CentExt.ext rfl (by simp [Psi, CentExt.fib, CentExt.base])

/-- **The obstruction of a finite-level coboundary** is `λ (tame relator) + λ (wild relator)`.  At an
admissible level both relators die, so this is `0` — the vanishing of `obs` on `B²`. -/
theorem obs_coboundary_eq [Finite L] (t : Marking L) (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    (relZPair t (coboundaryCocycle lam hlam1)).1 + (relZPair t (coboundaryCocycle lam hlam1)).2
      = lam t.tameValue + lam t.wildValue := by
  have hz1 : (liftMark t (zeroCocycle : TwoCocycle L)).tameValue.fib = 0 :=
    congrArg Prod.fst (relZPair_zero t)
  have hz2 : (liftMark t (zeroCocycle : TwoCocycle L)).wildValue.fib = 0 :=
    congrArg Prod.snd (relZPair_zero t)
  have htame : (relZPair t (coboundaryCocycle lam hlam1)).1
      = ![lam t.σ, lam t.τ, lam t.x₀, lam t.x₁] 1 + lam t.tameValue := by
    have h := congrArg CentExt.fib
      (Marking.map_tameValue (Psi lam hlam1) (liftMark t (coboundaryCocycle lam hlam1)))
    rw [map_Psi_liftMark, shiftLiftMark_tameValue_fib, hz1, zero_add, Psi_fib,
      liftMark_tameValue_base] at h
    rw [show (relZPair t (coboundaryCocycle lam hlam1)).1
        = (liftMark t (coboundaryCocycle lam hlam1)).tameValue.fib from rfl, h]
    abel_nf
    simp [CharTwo.two_eq_zero]
  have hwild : (relZPair t (coboundaryCocycle lam hlam1)).2
      = ![lam t.σ, lam t.τ, lam t.x₀, lam t.x₁] 1 + lam t.wildValue := by
    have h := congrArg CentExt.fib
      (Marking.map_wildValue (Psi lam hlam1) (liftMark t (coboundaryCocycle lam hlam1)))
    rw [map_Psi_liftMark, shiftLiftMark_wildValue_fib, hz2, zero_add, Psi_fib,
      liftMark_wildValue_base] at h
    rw [show (relZPair t (coboundaryCocycle lam hlam1)).2
        = (liftMark t (coboundaryCocycle lam hlam1)).wildValue.fib from rfl, h]
    abel_nf
    simp [CharTwo.two_eq_zero]
  rw [htame, hwild]
  abel_nf
  simp [CharTwo.two_eq_zero]

end CoboundaryObstruction

/-! ## The injectivity keystone: a balanced inflated cocycle is a coboundary

Assembling the shift laws (`exists_shift_of_relZ_eq`) with `cocycle_mem_B2`: if a finite-level
2-cocycle `c` has *balanced* relator obstruction (`tame.fib = wild.fib`, i.e. `relZPair ∈ Δ = im
d¹_triv`), then the 2-cocycle it inflates to on `Γ_A` — `(x, y) ↦ c.κ (level x) (level y)` — is a
continuous 2-coboundary.  This is the hard half of `θ`-injectivity: a class killed by `θ` (balanced
obstruction) is trivial.  Factoring a *continuous* `Γ_A`-cocycle into this inflated form (through a
finite level) is the remaining topological input; the algebra is complete here. -/

section Injectivity

open ContCoh

variable [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]

/-- The level projection `Γ_A = F₄ ⧸ N_A ↠ F₄ ⧸ U` for `N_A ≤ U`. -/
noncomputable def levelProj (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hU : NA ≤ U.toSubgroup) :
    ContinuousMonoidHom (FreeProfiniteGroup (Fin 4) ⧸ NA)
      (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) :=
  quotientLift NA (quotientMk U.toSubgroup) (hU.trans_eq (QuotientGroup.ker_mk' _).symm)

omit [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] [TopologicalSpace (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
@[simp] theorem levelProj_quotientMk (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hU : NA ≤ U.toSubgroup) (g : FreeProfiniteGroup (Fin 4)) :
    levelProj U hU (quotientMk NA g) = QuotientGroup.mk' U.toSubgroup g := rfl

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **Injectivity keystone.**  A finite-level cocycle with balanced relator obstruction inflates to
a continuous 2-coboundary on `Γ_A`.  (`[Finite (F₄ ⧸ U)]` at statement level, as for
`NA_le_ker_shiftLift`.) -/
theorem inflated_cocycle_mem_B2 (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NA ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hrel : (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).tameValue.fib
          = (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).wildValue.fib)
    (htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m) :
    (fun p : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) =>
        c.κ (levelProj U hU p.1) (levelProj U hU p.2))
      ∈ B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) := by
  obtain ⟨a, htame0, hwild0⟩ :=
    exists_shift_of_relZ_eq (univMarking.map (QuotientGroup.mk' U.toSubgroup)) hrel
  have hbase : ∀ x : FreeProfiniteGroup (Fin 4) ⧸ NA,
      (sectionHom U hU c a htame0 hwild0 x).base = levelProj U hU x := by
    intro x
    obtain ⟨g, rfl⟩ := quotientMk_surjective NA x
    rw [projC_comp_sectionHom, levelProj_quotientMk]
  have hfun : (fun p : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) =>
        c.κ (levelProj U hU p.1) (levelProj U hU p.2))
      = fun p => c.κ (sectionHom U hU c a htame0 hwild0 p.1).base
          (sectionHom U hU c a htame0 hwild0 p.2).base := by
    funext p; rw [hbase, hbase]
  rw [hfun]
  exact cocycle_mem_B2 U hU c a htame0 hwild0 htriv

end Injectivity

/-! ## Factoring a continuous cocycle through a finite level (the topological input)

The remaining input to `θ`: a continuous 2-cochain on the profinite `Γ_A` is *uniformly* locally
constant, hence factors through a finite quotient `F₄ ⧸ U` (`N_A ≤ U`).  The core is a compactness
argument (`exists_openNormalSubgroup_factor_two`): a continuous `f : G × G → M` to a discrete space
is invariant under right-translation of both arguments by a single open normal subgroup.  Applied to
a normalized continuous 2-cocycle `κ` on `Γ_A` and transported to `F₄ ⧸ U := comap N_A V`, it yields
a genuine `TwoCocycle (F₄ ⧸ U)` inflating to `κ` — the hypothesis that `inflated_cocycle_mem_B2`
consumes. -/

section Factoring

/-- **Uniform local constancy** (2-variable form): a continuous map `f : G × G → M` from a profinite
group to a discrete space is invariant under right-translation of *both* arguments by a single open
normal subgroup `V` — equivalently, `f` factors through `(G ⧸ V) × (G ⧸ V)`.  Proof: each point has a
basic clopen box on which `f` is constant (`isOpen_prod_iff` + `exist_openNormalSubgroup_sub_open_nhds_of_one`);
compactness extracts a finite subcover; `V` is the (finite) intersection of the boxes' subgroups. -/
theorem exists_openNormalSubgroup_factor_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : G × G → M) (hf : Continuous f) :
    ∃ V : OpenNormalSubgroup G, ∀ x y : G, ∀ u ∈ V, ∀ v ∈ V, f (x * u, y * v) = f (x, y) := by
  have hbox : ∀ p : G × G, ∃ W : OpenNormalSubgroup G,
      ∀ u ∈ W, ∀ v ∈ W, f (p.1 * u, p.2 * v) = f p := by
    intro p
    have hop : IsOpen (f ⁻¹' {f p}) := (isOpen_discrete _).preimage hf
    obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ := isOpen_prod_iff.mp hop p.1 p.2 rfl
    have hOA : IsOpen ((fun w => p.1 * w) ⁻¹' A) := hA.preimage (continuous_const.mul continuous_id)
    have hOB : IsOpen ((fun w => p.2 * w) ⁻¹' B) := hB.preimage (continuous_const.mul continuous_id)
    have h1A : (1 : G) ∈ (fun w => p.1 * w) ⁻¹' A := by simpa using hpA
    have h1B : (1 : G) ∈ (fun w => p.2 * w) ⁻¹' B := by simpa using hpB
    obtain ⟨WA, hWA⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOA h1A
    obtain ⟨WB, hWB⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOB h1B
    refine ⟨WA ⊓ WB, fun u hu v hv => ?_⟩
    have huA : p.1 * u ∈ A := hWA (SetLike.le_def.mp inf_le_left hu)
    have hvB : p.2 * v ∈ B := hWB (SetLike.le_def.mp inf_le_right hv)
    have hmem : (p.1 * u, p.2 * v) ∈ f ⁻¹' {f p} := hAB (Set.mk_mem_prod huA hvB)
    simpa using hmem
  choose W hW using hbox
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : G × G => (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)))
    (fun p => (((W p).toOpenSubgroup.isOpen.prod (W p).toOpenSubgroup.isOpen)).preimage
      (by fun_prop))
    (fun q _ => Set.mem_iUnion.mpr ⟨q, by
      rw [Set.mem_preimage, Set.mem_prod, inv_mul_cancel, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩⟩)
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ((1, 1) : G × G)))
    exact ⟨i, hi⟩
  refine ⟨t.inf' hne W, fun x y u hu v hv => ?_⟩
  have hxy : (x, y) ∈ ⋃ p ∈ t,
      (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)) := ht (Set.mem_univ _)
  rw [Set.mem_iUnion₂] at hxy
  obtain ⟨p, hpt, hp⟩ := hxy
  rw [Set.mem_preimage, Set.mem_prod] at hp
  obtain ⟨hx, hy⟩ := hp
  have hVle : t.inf' hne W ≤ W p := Finset.inf'_le _ hpt
  have huWp : u ∈ W p := SetLike.le_def.mp hVle hu
  have hvWp : v ∈ W p := SetLike.le_def.mp hVle hv
  have hfxy : f (x, y) = f p := by
    have h := hW p (p.1⁻¹ * x) hx (p.2⁻¹ * y) hy
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  have hfxuyv : f (x * u, y * v) = f p := by
    have hxu : p.1⁻¹ * (x * u) ∈ W p := by rw [← mul_assoc]; exact mul_mem hx huWp
    have hyv : p.2⁻¹ * (y * v) ∈ W p := by rw [← mul_assoc]; exact mul_mem hy hvWp
    have h := hW p (p.1⁻¹ * (x * u)) hxu (p.2⁻¹ * (y * v)) hyv
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  rw [hfxuyv, hfxy]

/-- **Factoring a normalized continuous 2-cocycle.**  A continuous `κ : Γ_A × Γ_A → 𝔽₂` that is
normalized (`κ (1,1) = 0`) and satisfies the 2-cocycle identity descends to a genuine
`TwoCocycle (F₄ ⧸ U)` at some finite level `N_A ≤ U`, inflating back to `κ` through `levelProj`. -/
theorem exists_twoCocycle_factor
    (κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2)
    (hκc : Continuous κ) (hκ1 : κ (1, 1) = 0)
    (hκcoc : ∀ a b c : FreeProfiniteGroup (Fin 4) ⧸ NA,
      κ (a, b) + κ (a * b, c) = κ (a, b * c) + κ (b, c)) :
    ∃ (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) (hU : NA ≤ U.toSubgroup)
      (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)),
      ∀ x y : FreeProfiniteGroup (Fin 4) ⧸ NA,
        κ (x, y) = c.κ (levelProj U hU x) (levelProj U hU y) := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two κ hκc
  have hUopen : IsOpen ((V.toSubgroup.comap (QuotientGroup.mk' NA) :
      Subgroup (FreeProfiniteGroup (Fin 4))) : Set (FreeProfiniteGroup (Fin 4))) :=
    V.toOpenSubgroup.isOpen.preimage (quotientMk NA).continuous_toFun
  haveI hUnormal : (V.toSubgroup.comap (QuotientGroup.mk' NA)).Normal :=
    V.isNormal'.comap _
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := V.toSubgroup.comap (QuotientGroup.mk' NA)
      isOpen' := hUopen }
  have hU : NA ≤ U.toSubgroup :=
    (QuotientGroup.ker_mk' NA).symm.trans_le
      (Subgroup.ker_le_comap (f := QuotientGroup.mk' NA) V.toSubgroup)
  refine ⟨U, hU, ?_, ?_⟩
  · refine
      { κ := fun p q => Quotient.liftOn₂ p q
          (fun x y => κ (QuotientGroup.mk x, QuotientGroup.mk y)) ?_
        norm := ?_
        cocyc := ?_ }
    · intro x₁ y₁ x₂ y₂ hx hy
      have hxU : x₁⁻¹ * x₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NA) :=
        QuotientGroup.leftRel_apply.mp hx
      have hyU : y₁⁻¹ * y₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NA) :=
        QuotientGroup.leftRel_apply.mp hy
      have hxv : (QuotientGroup.mk x₁ : FreeProfiniteGroup (Fin 4) ⧸ NA)⁻¹
          * QuotientGroup.mk x₂ ∈ V := by
        have h := (Subgroup.mem_comap).mp hxU
        rwa [map_mul, map_inv] at h
      have hyv : (QuotientGroup.mk y₁ : FreeProfiniteGroup (Fin 4) ⧸ NA)⁻¹
          * QuotientGroup.mk y₂ ∈ V := by
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

/-- **Factoring a continuous 1-cochain.**  A continuous `ψ : Γ_A → 𝔽₂` descends to a function on a
finite admissible level `N_A ≤ U` (via the same compactness lemma applied to `ψ ∘ fst`). -/
theorem exists_oneCochain_factor
    (ψ : FreeProfiniteGroup (Fin 4) ⧸ NA → ZMod 2) (hψc : Continuous ψ) :
    ∃ (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) (hU : NA ≤ U.toSubgroup)
      (lam : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup → ZMod 2),
      ∀ x : FreeProfiniteGroup (Fin 4) ⧸ NA, ψ x = lam (levelProj U hU x) := by
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two
    (fun p => ψ p.1) (hψc.comp continuous_fst)
  have hUopen : IsOpen ((V.toSubgroup.comap (QuotientGroup.mk' NA) :
      Subgroup (FreeProfiniteGroup (Fin 4))) : Set (FreeProfiniteGroup (Fin 4))) :=
    V.toOpenSubgroup.isOpen.preimage (quotientMk NA).continuous_toFun
  haveI hUnormal : (V.toSubgroup.comap (QuotientGroup.mk' NA)).Normal :=
    V.isNormal'.comap _
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := V.toSubgroup.comap (QuotientGroup.mk' NA)
      isOpen' := hUopen }
  have hU : NA ≤ U.toSubgroup :=
    (QuotientGroup.ker_mk' NA).symm.trans_le
      (Subgroup.ker_le_comap (f := QuotientGroup.mk' NA) V.toSubgroup)
  refine ⟨U, hU, fun p => Quotient.liftOn p (fun x => ψ (QuotientGroup.mk x)) ?_, ?_⟩
  · intro x₁ x₂ hx
    have hxU : x₁⁻¹ * x₂ ∈ V.toSubgroup.comap (QuotientGroup.mk' NA) :=
      QuotientGroup.leftRel_apply.mp hx
    have hxv : (QuotientGroup.mk x₁ : FreeProfiniteGroup (Fin 4) ⧸ NA)⁻¹
        * QuotientGroup.mk x₂ ∈ V := by
      have h := (Subgroup.mem_comap).mp hxU
      rwa [map_mul, map_inv] at h
    simpa using (hV (QuotientGroup.mk x₁) (QuotientGroup.mk x₁) _ hxv 1 (one_mem _)).symm
  · intro x
    induction x using QuotientGroup.induction_on with | H a =>
    rfl

end Factoring

/-! ## Injectivity, assembled: a balanced continuous cocycle is a coboundary

Combining the factoring (`exists_twoCocycle_factor`) with the injectivity keystone
(`inflated_cocycle_mem_B2`): a continuous 2-cocycle `κ` on `Γ_A` that factors through a finite level
`c` with *balanced* relator obstruction is a continuous 2-coboundary.  This is the kernel-side of
`θ`-injectivity in its consumable form. -/

section Assembly

open ContCoh

variable [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **Injectivity, consumable form.**  If a continuous cochain `κ` factors through a finite level
`c` (`κ = c.κ ∘ (levelProj × levelProj)`) whose relator obstruction is balanced
(`tame.fib = wild.fib`), then `κ` is a continuous 2-coboundary. -/
theorem mem_B2_of_factor_balanced
    (κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2)
    (htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m)
    (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    [Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)] (hU : NA ≤ U.toSubgroup)
    (c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hfact : ∀ x y : FreeProfiniteGroup (Fin 4) ⧸ NA,
      κ (x, y) = c.κ (levelProj U hU x) (levelProj U hU y))
    (hbal : (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).tameValue.fib
          = (liftMark (univMarking.map (QuotientGroup.mk' U.toSubgroup)) c).wildValue.fib) :
    κ ∈ B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) := by
  have heq : κ = fun p => c.κ (levelProj U hU p.1) (levelProj U hU p.2) := by
    funext p; exact hfact p.1 p.2
  rw [heq]
  exact inflated_cocycle_mem_B2 U hU c hbal htriv

end Assembly

/-! ## The obstruction map and the cardinality bound `#H²(Γ_A, 𝔽₂) ≤ 2`

Assembling everything.  The **obstruction** `obs : Z²_cont(Γ_A, 𝔽₂) →+ 𝔽₂` sends a continuous
2-cocycle to the sum of its tame and wild relator obstructions, computed after normalizing at `(1,1)`
and factoring through a finite admissible level.  The value is *level-independent* (`relZPair_comap`)
and *additive* (`relZPair_add`), and its kernel lands in `B²` (`mem_B2_of_factor_balanced`).  Hence
`H² = Z²/B²` is a quotient of `Z²/ker obs ↪ 𝔽₂`, giving `#H²(Γ_A, 𝔽₂) ≤ #𝔽₂ = 2`. -/

/-- Two `TwoCocycle`s with equal cochain are equal (the `norm`/`cocyc` fields are propositions). -/
theorem TwoCocycle.ext {L : Type*} [Group L] {c d : TwoCocycle L} (h : c.κ = d.κ) : c = d := by
  cases c; cases d; subst h; rfl

section CardBound

open ContCoh

/-- An open normal subgroup of the compact free profinite group has finite quotient. -/
instance quotient_finite_openNormal
    (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) :
    Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen U.toSubgroup U.isOpen'

/-- A factorization of a `Γ_A`-cochain `κ` through a finite admissible level:
`κ (x, y) = c.κ (levelProj x) (levelProj y)`. -/
structure LevelFactor
    (κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2) where
  /-- The finite admissible level `F₄ ⧸ U`. -/
  U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))
  /-- `N_A ≤ U`, so `Γ_A = F₄ ⧸ N_A ↠ F₄ ⧸ U`. -/
  hU : NA ≤ U.toSubgroup
  /-- The finite-level 2-cocycle whose inflation is `κ`. -/
  c : TwoCocycle (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)
  /-- `κ` is the inflation of `c` along `levelProj`. -/
  hfact : ∀ x y, κ (x, y) = c.κ (levelProj U hU x) (levelProj U hU y)

/-- The relator obstruction of a factorization: the sum of the tame and wild relator fibre-`z`
values of the finite-level cocycle. -/
noncomputable def LevelFactor.obs
    {κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2}
    (F : LevelFactor κ) : ZMod 2 :=
  (relZPair (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).1
    + (relZPair (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).2

/-- **Level-independence.**  `F.obs` may be computed at any finer level `W` (via a projection
`proj : F₄ ⧸ W → F₄ ⧸ F.U` with `proj ∘ mk_W = mk_{F.U}`) through the pulled-back cocycle
`F.c.comap proj` — this is `relZPair_comap`. -/
theorem LevelFactor.obs_eq_comap
    {κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2}
    (F : LevelFactor κ) (W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (proj : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
          →* (FreeProfiniteGroup (Fin 4) ⧸ F.U.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' F.U.toSubgroup) :
    F.obs = (relZPair (univMarking.map (QuotientGroup.mk' W.toSubgroup)) (F.c.comap proj)).1
          + (relZPair (univMarking.map (QuotientGroup.mk' W.toSubgroup)) (F.c.comap proj)).2 := by
  have htU : univMarking.map (QuotientGroup.mk' F.U.toSubgroup)
           = (univMarking.map (QuotientGroup.mk' W.toSubgroup)).map proj := by
    rw [Marking.map_map, hproj]
  unfold LevelFactor.obs
  rw [htU, relZPair_comap]

/-- **Well-definedness.**  `F.obs` depends only on `κ`, not on the chosen factorization: two
factorizations agree at their common refinement `F₁.U ⊓ F₂.U`, where both finite-level cocycles pull
back to the same cocycle (both inflate to `κ`). -/
theorem LevelFactor.obs_congr
    {κ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2}
    (F₁ F₂ : LevelFactor κ) : F₁.obs = F₂.obs := by
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
    -- `levelProj U hU (quotientMk NA ·) = mk' U ·` is `rfl`, so `hfact` reads directly at `mk'`.
    have hf1 : κ (quotientMk NA g, quotientMk NA h)
        = F₁.c.κ (QuotientGroup.mk' F₁.U.toSubgroup g) (QuotientGroup.mk' F₁.U.toSubgroup h) :=
      F₁.hfact (quotientMk NA g) (quotientMk NA h)
    have hf2 : κ (quotientMk NA g, quotientMk NA h)
        = F₂.c.κ (QuotientGroup.mk' F₂.U.toSubgroup g) (QuotientGroup.mk' F₂.U.toSubgroup h) :=
      F₂.hfact (quotientMk NA g) (quotientMk NA h)
    rw [TwoCocycle.comap_κ, TwoCocycle.comap_κ, e1g, e1h, e2g, e2h, ← hf1, ← hf2]
  rw [hcc]

/-- The two projections `F₄ ⧸ W → F₄ ⧸ U` (for `N_A ≤ W ≤ U`, via `proj`) and the level maps
`Γ_A → F₄ ⧸ W → F₄ ⧸ U` compose to the level map `Γ_A → F₄ ⧸ U`. -/
theorem levelProj_comp (W U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)))
    (hUW : NA ≤ W.toSubgroup) (hU : NA ≤ U.toSubgroup)
    (proj : (FreeProfiniteGroup (Fin 4) ⧸ W.toSubgroup)
          →* (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' W.toSubgroup) = QuotientGroup.mk' U.toSubgroup)
    (x : FreeProfiniteGroup (Fin 4) ⧸ NA) :
    proj (levelProj W hUW x) = levelProj U hU x := by
  obtain ⟨g, rfl⟩ := quotientMk_surjective NA x
  show proj (QuotientGroup.mk' W.toSubgroup g) = QuotientGroup.mk' U.toSubgroup g
  rw [← MonoidHom.comp_apply, hproj]

/-- Normalize a 2-cochain at `(1,1)` by subtracting the (coboundary) constant `κ (1,1)`. -/
noncomputable def normalizeCochain (κ : (FreeProfiniteGroup (Fin 4) ⧸ NA)
    × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2) :
    (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2 :=
  κ - fun _ => κ (1, 1)

theorem normalizeCochain_add (κ κ' : (FreeProfiniteGroup (Fin 4) ⧸ NA)
    × (FreeProfiniteGroup (Fin 4) ⧸ NA) → ZMod 2) :
    normalizeCochain (κ + κ') = normalizeCochain κ + normalizeCochain κ' := by
  funext p; simp only [normalizeCochain, Pi.add_apply, Pi.sub_apply]; abel

variable [DistribMulAction (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
  [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)]
variable (htriv : ∀ (x : FreeProfiniteGroup (Fin 4) ⧸ NA) (m : ZMod 2), x • m = m)
include htriv

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- Under the trivial action, a constant 2-cochain is a continuous coboundary (`= δ¹` of a constant
1-cochain). -/
theorem const2_mem_B2 (v : ZMod 2) :
    (fun _ : (FreeProfiniteGroup (Fin 4) ⧸ NA) × (FreeProfiniteGroup (Fin 4) ⧸ NA) => v)
      ∈ B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) := by
  rw [B2, AddSubgroup.mem_map]
  refine ⟨fun _ => v, continuous_const, ?_⟩
  funext p
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, htriv]
  abel

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- The normalization of a continuous 2-cocycle factors through a finite admissible level. -/
theorem nonempty_levelFactor_normalize (φ : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) :
    Nonempty (LevelFactor (normalizeCochain φ.1)) := by
  have hφcont : Continuous φ.1 := (mem_Z2_iff.mp φ.2).1
  have hφcoc := (mem_Z2_iff.mp φ.2).2
  have hcont : Continuous (normalizeCochain φ.1) := hφcont.sub continuous_const
  have hnorm : normalizeCochain φ.1 (1, 1) = 0 := by
    simp only [normalizeCochain, Pi.sub_apply, sub_self]
  have hcoc : ∀ a b c, normalizeCochain φ.1 (a, b) + normalizeCochain φ.1 (a * b, c)
      = normalizeCochain φ.1 (a, b * c) + normalizeCochain φ.1 (b, c) := by
    intro a b c
    have hz := hφcoc a b c
    rw [htriv] at hz
    simp only [normalizeCochain, Pi.sub_apply]
    linear_combination -hz
  obtain ⟨U, hU, c, hfact⟩ := exists_twoCocycle_factor (normalizeCochain φ.1) hcont hnorm hcoc
  exact ⟨U, hU, c, hfact⟩

/-- The per-cocycle obstruction: the relator obstruction of any factorization of the normalization. -/
noncomputable def obsFun (φ : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) : ZMod 2 :=
  (nonempty_levelFactor_normalize htriv φ).some.obs

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- `obsFun` may be computed at *any* factorization of the normalization (well-definedness). -/
theorem obsFun_eq (φ : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2))
    (F : LevelFactor (normalizeCochain φ.1)) : obsFun htriv φ = F.obs :=
  LevelFactor.obs_congr _ F

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **Additivity of the obstruction.**  Both `φ` and `ψ` factor through a common refinement
`W = U_φ ⊓ U_ψ`, where their finite-level cocycles pull back and *add* (`relZPair_add`). -/
theorem obsFun_add (φ ψ : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) :
    obsFun htriv (φ + ψ) = obsFun htriv φ + obsFun htriv ψ := by
  set Fφ := (nonempty_levelFactor_normalize htriv φ).some with hFφ
  set Fψ := (nonempty_levelFactor_normalize htriv ψ).some with hFψ
  set W : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) := Fφ.U ⊓ Fψ.U with hWdef
  have hUW : NA ≤ W.toSubgroup := le_inf Fφ.hU Fψ.hU
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
  have hFsum : obsFun htriv (φ + ψ)
      = (relZPair (univMarking.map (QuotientGroup.mk' W.toSubgroup))
          (Fφ.c.comap pφ + Fψ.c.comap pψ)).1
      + (relZPair (univMarking.map (QuotientGroup.mk' W.toSubgroup))
          (Fφ.c.comap pφ + Fψ.c.comap pψ)).2 := by
    refine obsFun_eq htriv (φ + ψ) ⟨W, hUW, Fφ.c.comap pφ + Fψ.c.comap pψ, ?_⟩
    intro x y
    rw [TwoCocycle.add_κ, TwoCocycle.comap_κ, TwoCocycle.comap_κ,
      levelProj_comp W Fφ.U hUW Fφ.hU pφ hpφ x, levelProj_comp W Fφ.U hUW Fφ.hU pφ hpφ y,
      levelProj_comp W Fψ.U hUW Fψ.hU pψ hpψ x, levelProj_comp W Fψ.U hUW Fψ.hU pψ hpψ y,
      ← Fφ.hfact x y, ← Fψ.hfact x y]
    show normalizeCochain (φ.1 + ψ.1) (x, y)
        = normalizeCochain φ.1 (x, y) + normalizeCochain ψ.1 (x, y)
    rw [normalizeCochain_add, Pi.add_apply]
  rw [obsFun_eq htriv φ Fφ, obsFun_eq htriv ψ Fψ, hFsum,
    Fφ.obs_eq_comap W pφ hpφ, Fψ.obs_eq_comap W pψ hpψ, relZPair_add, Prod.fst_add, Prod.snd_add]
  abel

/-- The **obstruction homomorphism** `Z²_cont(Γ_A, 𝔽₂) →+ 𝔽₂`. -/
noncomputable def obs : Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) →+ ZMod 2 :=
  AddMonoidHom.mk' (obsFun htriv) (obsFun_add htriv)

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- The kernel of the obstruction lands in the 2-coboundaries: an `obs`-trivial cocycle is balanced,
hence a coboundary (`mem_B2_of_factor_balanced`), after adding back the normalization constant. -/
theorem obs_ker_le :
    (obs htriv).ker ≤ (B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)).addSubgroupOf
      (Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) := by
  intro φ hφ
  rw [AddMonoidHom.mem_ker] at hφ
  rw [AddSubgroup.mem_addSubgroupOf]
  set F := (nonempty_levelFactor_normalize htriv φ).some with hF
  have hobs0 : F.obs = 0 := by rw [← obsFun_eq htriv φ F]; exact hφ
  have hbal : (liftMark (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).tameValue.fib
      = (liftMark (univMarking.map (QuotientGroup.mk' F.U.toSubgroup)) F.c).wildValue.fib :=
    CharTwo.add_eq_zero.mp hobs0
  have hnB2 : normalizeCochain φ.1 ∈ B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) :=
    mem_B2_of_factor_balanced (normalizeCochain φ.1) htriv F.U F.hU F.c F.hfact hbal
  have hconst : φ.1 = normalizeCochain φ.1 + fun _ => φ.1 (1, 1) := by
    funext p; simp only [normalizeCochain, Pi.sub_apply, Pi.add_apply]; abel
  rw [hconst]
  exact AddSubgroup.add_mem _ hnB2 (const2_mem_B2 htriv (φ.1 (1, 1)))

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **`obs` kills `B²`** (the vanishing on coboundaries).  A continuous coboundary `κ = δ¹ψ`
normalizes to `δ¹ψ'` (`ψ' 1 = 0`), which factors through a finite admissible level as
`coboundaryCocycle λ`; its obstruction is `λ(tameValue) + λ(wildValue) = λ 1 + λ 1 = 0` since both
relators die at that level.  Combined with `obs_ker_le`, this makes `obs` descend to an injection
`H²(Γ_A, 𝔽₂) ↪ 𝔽₂` — the degree-2 presentation-comparison. -/
theorem obs_B2_eq_zero :
    (B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)).addSubgroupOf
      (Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) ≤ (obs htriv).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  rw [AddSubgroup.mem_addSubgroupOf, B2, AddSubgroup.mem_map] at hx
  obtain ⟨ψ, hψc, hψeq⟩ := hx
  have hψcont : Continuous ψ := mem_C1_iff.mp hψc
  have hx1 : x.1 = dOne (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) ψ := hψeq.symm
  set ψ' : FreeProfiniteGroup (Fin 4) ⧸ NA → ZMod 2 := ψ - fun _ => ψ 1 with hψ'def
  obtain ⟨U, hU, lam, hlamfact⟩ := exists_oneCochain_factor ψ' (hψcont.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlamfact 1
    rw [show levelProj U hU 1 = 1 from map_one _] at h
    rw [← h]; simp [hψ'def]
  have hfact : ∀ p q, normalizeCochain x.1 (p, q)
      = (coboundaryCocycle lam hlam1).κ (levelProj U hU p) (levelProj U hU q) := by
    intro p q
    show normalizeCochain x.1 (p, q)
      = lam (levelProj U hU p) + lam (levelProj U hU q)
        + lam (levelProj U hU p * levelProj U hU q)
    rw [← map_mul (levelProj U hU) p q, ← hlamfact p, ← hlamfact q, ← hlamfact (p * q), hx1]
    simp only [normalizeCochain, Pi.sub_apply, Pi.add_apply, hψ'def, dOne, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, htriv, mul_one, CharTwo.sub_eq_add]
    abel
  have hobs : obsFun htriv x = 0 := by
    rw [obsFun_eq htriv x ⟨U, hU, coboundaryCocycle lam hlam1, hfact⟩]
    show (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        (coboundaryCocycle lam hlam1)).1
      + (relZPair (univMarking.map (QuotientGroup.mk' U.toSubgroup))
        (coboundaryCocycle lam hlam1)).2 = 0
    rw [obs_coboundary_eq]
    have hadmU : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).Admissible :=
      isAdmissibleU_of_NA_le hU
    rw [(Marking.tameValue_eq_one_iff _).mpr hadmU.2.1,
      (Marking.wildValue_eq_one_iff _).mpr hadmU.2.2.1, hlam1, add_zero]
  exact hobs

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
/-- **`ker obs = B²`** (P-16c4, lemma A).  The obstruction is trivial on coboundaries and nowhere
else, so it descends to an *injection* `H²(Γ_A, 𝔽₂) ↪ 𝔽₂` — the reusable degree-2
presentation-comparison.  (`obs_ker_le` ⊆, `obs_B2_eq_zero` ⊇.) -/
theorem obs_ker_eq_B2 :
    (obs htriv).ker = (B2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)).addSubgroupOf
      (Z2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)) :=
  le_antisymm (obs_ker_le htriv) (obs_B2_eq_zero htriv)

/-- The **descended obstruction** `H²(Γ_A, 𝔽₂) →+ 𝔽₂`, and its injectivity: a continuous 2-cocycle
whose obstruction is nonzero is *not* a coboundary. -/
noncomputable def obsH2 : H2 (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift _ (obs htriv) (fun _ h => obs_B2_eq_zero htriv h)

omit [ContinuousSMul (FreeProfiniteGroup (Fin 4) ⧸ NA) (ZMod 2)] in
theorem obsH2_injective : Function.Injective (obsH2 htriv) := by
  rw [injective_iff_map_eq_zero]
  intro a
  induction a using QuotientAddGroup.induction_on with | H φ =>
  intro ha
  exact (QuotientAddGroup.eq_zero_iff φ).mpr (obs_ker_le htriv (AddMonoidHom.mem_ker.mpr ha))


end CardBound

end WordCoh2

end GQ2
