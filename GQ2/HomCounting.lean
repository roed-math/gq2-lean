import GQ2.RegularSummand

/-!
# The equivariant-Hom counting engine  (ticket P-15f5)

The single-step multiplicativity of equivariant-Hom counts across an equivariant short exact
presentation, from a regular-summand package (the Lemma-6.11 output shape, taken as a
*hypothesis*): for `C`-modules and an exact `W' —j→ W —π→ W''` of finite 2-torsion modules,

`#Hom_C(V, W) = #Hom_C(V, W') · #Hom_C(V, W'')`.

Design: `equivHoms C V W` is the subgroup of `V →+ W` cut out by `C`-equivariance;
post-composition with `π` is an additive map `Φ` between these Hom groups; the count is
Lagrange (`AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup`) + the first isomorphism
theorem (`QuotientAddGroup.quotientKerEquivOfSurjective`), with

* **surjectivity of `Φ`** supplied by the banked `equivariant_lift_of_regular_summand`
  (`GQ2/RegularSummand.lean`; since P-17e4 the producing `lemma_6_11` node is itself proved
  std-3, so the whole package is `sorryAx`-free), and
* **`ker Φ ≃ Hom_C(V, W')`** from the kernel identification along `j` (choice-lift through the
  injection).

The iterated product over a full filtration is intentionally left to the consumer
(P-15f6/P-15f8): concrete graded presentations vary, and each step is one application of
`card_equivHoms_of_exact`.  This file is std-3 sorry-free and axiom-free.
-/

namespace GQ2

section HomCounting

variable {C : Type} [Group C]
variable {V W W' W'' : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup W']
  [AddCommGroup W''] [DistribMulAction C V] [DistribMulAction C W] [DistribMulAction C W']
  [DistribMulAction C W'']

/-- The `C`-equivariant additive maps `V →+ W`, as an additive subgroup of `V →+ W`
(equivariance is closed under `0`, `+`, `−` since the actions are additive). -/
def equivHoms (C : Type) [Group C] (V W : Type) [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction C V] [DistribMulAction C W] : AddSubgroup (V →+ W) where
  carrier := {f | ∀ (c : C) (v : V), f (c • v) = c • f v}
  zero_mem' := fun c v => by
    rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, smul_zero]
  add_mem' := fun {f g} hf hg c v => by
    rw [AddMonoidHom.add_apply, AddMonoidHom.add_apply, hf c v, hg c v, smul_add]
  neg_mem' := fun {f} hf c v => by
    rw [AddMonoidHom.neg_apply, AddMonoidHom.neg_apply, hf c v, smul_neg]


/-- Post-composition with an equivariant `π : W →+ W''`, as an additive map between the
equivariant-Hom groups. -/
def postCompHom (π : W →+ W'') (hπeq : ∀ (c : C) (w : W), π (c • w) = c • π w) :
    ↥(equivHoms C V W) →+ ↥(equivHoms C V W'') :=
  AddMonoidHom.mk'
    (fun f => ⟨π.comp f.1, fun c v => by
      show π (f.1 (c • v)) = c • π (f.1 v)
      rw [f.2 c v, hπeq]⟩)
    (fun f g => by
      apply Subtype.ext
      show π.comp (f.1 + g.1) = π.comp f.1 + π.comp g.1
      ext v
      simp)


/-- **The kernel identification**: composing with an equivariant injection `j : W' →+ W` whose
range is `ker π` identifies `Hom_C(V, W')` with the kernel of post-composition by `π`. -/
theorem card_ker_postCompHom (j : W' →+ W)
    (hjeq : ∀ (c : C) (w : W'), j (c • w) = c • j w) (hjinj : Function.Injective j)
    (π : W →+ W'') (hπeq : ∀ (c : C) (w : W), π (c • w) = c • π w)
    (hexact : ∀ w : W, π w = 0 ↔ w ∈ Set.range j) :
    Nat.card ↥(postCompHom (V := V) π hπeq).ker = Nat.card ↥(equivHoms C V W') := by
  classical
  refine (Nat.card_congr (Equiv.ofBijective
    (fun f' : ↥(equivHoms C V W') =>
      (⟨⟨j.comp f'.1, fun c v => by
          show j (f'.1 (c • v)) = c • j (f'.1 v)
          rw [f'.2 c v, hjeq]⟩, by
        rw [AddMonoidHom.mem_ker]
        apply Subtype.ext
        show π.comp (j.comp f'.1) = 0
        ext v
        exact (hexact _).mpr ⟨f'.1 v, rfl⟩⟩ : ↥(postCompHom (V := V) π hπeq).ker))
    ⟨?_, ?_⟩)).symm
  · -- injective
    intro f' g' h
    have h1 : j.comp f'.1 = j.comp g'.1 :=
      congrArg (fun x => ((x : ↥(equivHoms C V W)) : V →+ W)) (Subtype.ext_iff.mp h)
    exact Subtype.ext (AddMonoidHom.ext fun v => hjinj (DFunLike.congr_fun h1 v))
  · -- surjective: choice-lift each value through `j`
    rintro ⟨⟨f, hfeq⟩, hfker⟩
    have hker : ∀ v : V, π (f v) = 0 := by
      intro v
      have h0 : π.comp f = 0 := Subtype.ext_iff.mp (AddMonoidHom.mem_ker.mp hfker)
      exact DFunLike.congr_fun h0 v
    have hmem : ∀ v : V, ∃ w' : W', j w' = f v := fun v => (hexact _).mp (hker v)
    set u : V → W' := fun v => Function.invFun j (f v) with hu_def
    have hju : ∀ v : V, j (u v) = f v := fun v => Function.invFun_eq (hmem v)
    have humap : ∀ a b : V, u (a + b) = u a + u b := by
      intro a b
      apply hjinj
      rw [map_add, hju, hju, hju, map_add]
    have hueq : ∀ (c : C) (v : V), u (c • v) = c • u v := by
      intro c v
      apply hjinj
      rw [hju, hjeq, hju, hfeq]
    refine ⟨⟨AddMonoidHom.mk' u humap, hueq⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    show j.comp (AddMonoidHom.mk' u humap) = f
    ext v
    exact hju v

/-- **The counting step (P-15f5)**: given a regular-summand package `(ι, r)` for `V` (the
Lemma-6.11 output shape, as a hypothesis) and a `C`-equivariant short exact presentation
`W' —j→ W —π→ W''` of finite 2-torsion modules, the equivariant-Hom counts multiply:

`#Hom_C(V, W) = #Hom_C(V, W') · #Hom_C(V, W'')`.

Lagrange along `ker (π ∘ −)` + first isomorphism theorem; surjectivity of post-composition is
the banked `equivariant_lift_of_regular_summand`.  Iterating over a filtration
`M = F₀ ⊇ … ⊇ F_n = 0` (one application per graded step, at the consumer's concrete
presentation of `grⱼ`) yields `#Hom_C(V, M) = ∏ⱼ #Hom_C(V, grⱼ)` — the `Hom(V^∨, −)`-exactness
count of the Lemma-6.17 dimension clause. -/
theorem card_equivHoms_of_exact [Finite C] [Finite V] [Finite W] [Finite W'']
    (h2W : ∀ w : W, w + w = 0) (h2W'' : ∀ w : W'', w + w = 0)
    {N : ℕ} (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V)
    (hι : ∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : V, r (ι v) = v)
    (j : W' →+ W) (hjeq : ∀ (c : C) (w : W'), j (c • w) = c • j w)
    (hjinj : Function.Injective j)
    (π : W →+ W'') (hπeq : ∀ (c : C) (w : W), π (c • w) = c • π w)
    (hπsurj : Function.Surjective ⇑π)
    (hexact : ∀ w : W, π w = 0 ↔ w ∈ Set.range j) :
    Nat.card ↥(equivHoms C V W)
      = Nat.card ↥(equivHoms C V W') * Nat.card ↥(equivHoms C V W'') := by
  classical
  haveI : Finite (V →+ W) := Finite.of_injective _ DFunLike.coe_injective
  haveI : Finite (V →+ W'') := Finite.of_injective _ DFunLike.coe_injective
  set Φ := postCompHom (V := V) π hπeq with hΦ_def
  -- surjectivity of post-composition, from the regular-summand lift
  have hΦsurj : Function.Surjective ⇑Φ := by
    intro g
    obtain ⟨g₀, hg₀eq, hg₀⟩ := equivariant_lift_of_regular_summand h2W h2W'' ι r hι hr hri
      π hπeq hπsurj g.1 g.2
    exact ⟨⟨g₀, hg₀eq⟩, Subtype.ext (AddMonoidHom.ext hg₀)⟩
  -- Lagrange + first isomorphism theorem
  have hlag : Nat.card ↥(equivHoms C V W)
      = Nat.card (↥(equivHoms C V W) ⧸ Φ.ker) * Nat.card ↥Φ.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have hquot : Nat.card (↥(equivHoms C V W) ⧸ Φ.ker) = Nat.card ↥(equivHoms C V W'') :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective Φ hΦsurj).toEquiv
  have hker : Nat.card ↥Φ.ker = Nat.card ↥(equivHoms C V W') :=
    card_ker_postCompHom j hjeq hjinj π hπeq hexact
  rw [hlag, hquot, hker, Nat.mul_comm]


/-- **Transport**: the equivariant-Hom count only depends on the target up to equivariant
additive isomorphism — the consumer's tool for swapping in a concrete model of a graded
piece. -/
theorem card_equivHoms_congr (e : W ≃+ W'')
    (heq : ∀ (c : C) (w : W), e (c • w) = c • e w) :
    Nat.card ↥(equivHoms C V W) = Nat.card ↥(equivHoms C V W'') := by
  refine Nat.card_congr (Equiv.ofBijective
    (fun f : ↥(equivHoms C V W) =>
      (⟨e.toAddMonoidHom.comp f.1, fun c v => by
        show e (f.1 (c • v)) = c • e (f.1 v)
        rw [f.2 c v, heq]⟩ : ↥(equivHoms C V W''))) ⟨?_, ?_⟩)
  · intro f g h
    exact Subtype.ext (AddMonoidHom.ext fun v =>
      e.injective (DFunLike.congr_fun (Subtype.ext_iff.mp h) v))
  · intro g
    refine ⟨⟨e.symm.toAddMonoidHom.comp g.1, fun c v => by
      show e.symm (g.1 (c • v)) = c • e.symm (g.1 v)
      rw [g.2 c v]
      apply e.injective
      rw [AddEquiv.apply_symm_apply, heq, AddEquiv.apply_symm_apply]⟩, ?_⟩
    exact Subtype.ext (AddMonoidHom.ext fun v => e.apply_symm_apply (g.1 v))

end HomCounting

end GQ2
