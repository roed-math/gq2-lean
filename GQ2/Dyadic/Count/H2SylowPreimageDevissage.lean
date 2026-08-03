/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2SylowTransfer
import Mathlib.GroupTheory.PGroup

/-!
# Coefficient devissage over a Sylow-2 action image

After restriction to the preimage of a Sylow `2`-subgroup, every coefficient action factors
through a finite `2`-group.  In characteristic two, the only simple module for such a group is
the trivial one-dimensional module.  This file formalizes that algebraic reduction and isolates
the remaining cohomological input.

Passing to the Sylow preimage does not by itself prove degree-two right exactness.  It reduces
the simple coefficient kernels occurring in a composition series to trivial `ZMod 2`, then a
strong induction reduces every elementary quotient to the scalar-kernel tail; surjectivity
across each such extension is exactly the `H^3(-, ZMod 2)`-vanishing/CD-2 input.
-/

namespace GQ2

namespace FoxH

noncomputable section

variable {P V : Type*} [Group P] [Finite P]
  [AddCommGroup V] [Finite V] [DistribMulAction P V]

/-- The additive subgroup of vectors fixed by the whole acting group. -/
def fixedAddSubgroup : AddSubgroup V where
  carrier := {v | ∀ p : P, p • v = v}
  zero_mem' := by simp
  add_mem' := by
    intro a b ha hb p
    rw [smul_add, ha p, hb p]
  neg_mem' := by
    intro a ha p
    rw [smul_neg, ha p]

@[simp] theorem mem_fixedAddSubgroup_iff {v : V} :
    v ∈ fixedAddSubgroup (P := P) (V := V) ↔ ∀ p : P, p • v = v :=
  Iff.rfl

/-- A nonzero finite elementary module has even cardinality. -/
theorem two_dvd_natCard_of_nontrivial_two_torsion
    [Nontrivial V] (hV₂ : ∀ v : V, v + v = 0) : 2 ∣ Nat.card V := by
  letI : Fintype V := Fintype.ofFinite V
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hord : addOrderOf v = 2 :=
    addOrderOf_eq_prime (by rw [two_nsmul]; exact hV₂ v) hv
  rw [Nat.card_eq_fintype_card]
  rw [← hord]
  exact addOrderOf_dvd_card

/-- A finite `2`-group acting on a nonzero finite elementary abelian group has a nonzero fixed
vector. -/
theorem exists_ne_zero_fixed_of_isPGroup_two
    (hP : IsPGroup 2 P) [Nontrivial V] (hV₂ : ∀ v : V, v + v = 0) :
    ∃ v : V, v ≠ 0 ∧ ∀ p : P, p • v = v := by
  have hzero : (0 : V) ∈ MulAction.fixedPoints P V := by
    exact MulAction.mem_fixedPoints.mpr (fun _ ↦ smul_zero _)
  obtain ⟨v, hvfix, hne⟩ :=
    hP.exists_fixed_point_of_prime_dvd_card_of_fixed_point V
      (two_dvd_natCard_of_nontrivial_two_torsion hV₂) hzero
  refine ⟨v, ?_, ?_⟩
  · exact Ne.symm hne
  · exact MulAction.mem_fixedPoints.mp hvfix

/-- Over a finite `2`-group, every simple finite elementary module has trivial action.

This is the characteristic-two local-group fact needed by the Sylow-preimage route. -/
theorem smul_eq_self_of_isPGroup_two_of_simple
    (hP : IsPGroup 2 P) (hV₂ : ∀ v : V, v + v = 0)
    (hsimple : IsSimpleModTwo P V) : ∀ (p : P) (v : V), p • v = v := by
  letI : Nontrivial V := hsimple.1
  obtain ⟨v, hv0, hvfix⟩ := exists_ne_zero_fixed_of_isPGroup_two hP hV₂
  have hne : fixedAddSubgroup (P := P) (V := V) ≠ ⊥ := by
    intro hbot
    have hv : v ∈ (⊥ : AddSubgroup V) := hbot ▸ hvfix
    exact hv0 (AddSubgroup.mem_bot.mp hv)
  have hstable : ∀ (p : P) (w : V), w ∈ fixedAddSubgroup (P := P) (V := V) →
      p • w ∈ fixedAddSubgroup (P := P) (V := V) := by
    intro p w hw
    rw [mem_fixedAddSubgroup_iff] at hw ⊢
    rw [hw p]
    exact hw
  have htop : fixedAddSubgroup (P := P) (V := V) = ⊤ :=
    (hsimple.2 (fixedAddSubgroup (P := P) (V := V)) hstable).resolve_left hne
  intro p w
  have hw : w ∈ fixedAddSubgroup (P := P) (V := V) := htop.symm ▸ AddSubgroup.mem_top w
  exact (mem_fixedAddSubgroup_iff.mp hw) p

/-- Any two-element additive module is simple, independently of the action. -/
theorem isSimpleModTwo_of_natCard_eq_two
    (hcard : Nat.card V = 2) : IsSimpleModTwo P V := by
  have hnt : Nontrivial V :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  refine ⟨hnt, ?_⟩
  intro W _hstable
  by_cases hW : W = ⊥
  · exact Or.inl hW
  · right
    haveI : Nontrivial ↑W := (AddSubgroup.nontrivial_iff_ne_bot W).mpr hW
    obtain ⟨⟨w, hwW⟩, hw0⟩ := exists_ne (0 : W)
    have hw0' : w ≠ 0 := fun hw ↦ hw0 (Subtype.ext hw)
    obtain ⟨v, hv0, hvuniq⟩ := (Nat.card_eq_two_iff' (0 : V)).mp hcard
    have hwv : w = v := hvuniq w hw0'
    apply eq_top_iff.mpr
    intro x _hx
    by_cases hx0 : x = 0
    · simpa [hx0] using W.zero_mem
    · have hxv : x = v := hvuniq x hx0
      rw [hxv, ← hwv]
      exact hwW

omit [Finite P] in
/-- A simple finite elementary module with trivial action has exactly two elements. -/
theorem natCard_eq_two_of_simple_of_trivial
    (hV₂ : ∀ v : V, v + v = 0) (hsimple : IsSimpleModTwo P V)
    (htriv : ∀ (p : P) (v : V), p • v = v) : Nat.card V = 2 := by
  letI : Nontrivial V := hsimple.1
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  let W : AddSubgroup V := AddSubgroup.zmultiples v
  have hvW : v ∈ W := AddSubgroup.mem_zmultiples_iff.mpr ⟨1, by simp⟩
  have hWne : W ≠ ⊥ := by
    intro hbot
    have : v = 0 := AddSubgroup.mem_bot.mp (hbot ▸ hvW)
    exact hv this
  have hstable : ∀ (p : P) (w : V), w ∈ W → p • w ∈ W := by
    intro p w hw
    rw [htriv p w]
    exact hw
  have hWtop : W = ⊤ := (hsimple.2 W hstable).resolve_left hWne
  have hord : addOrderOf v = 2 :=
    addOrderOf_eq_prime (by rw [two_nsmul]; exact hV₂ v) hv
  calc
    Nat.card V = Nat.card ↑(⊤ : AddSubgroup V) :=
      (Nat.card_congr AddSubgroup.topEquiv.toEquiv).symm
    _ = Nat.card ↑W := congrArg (fun X : AddSubgroup V ↦ Nat.card ↑X) hWtop.symm
    _ = addOrderOf v := Nat.card_zmultiples v
    _ = 2 := hord

/-- Hence every simple elementary module over a finite `2`-group is literally a scalar
two-element kernel. -/
theorem natCard_eq_two_of_isPGroup_two_of_simple
    (hP : IsPGroup 2 P) (hV₂ : ∀ v : V, v + v = 0)
    (hsimple : IsSimpleModTwo P V) : Nat.card V = 2 :=
  natCard_eq_two_of_simple_of_trivial hV₂ hsimple
    (smul_eq_self_of_isPGroup_two_of_simple hP hV₂ hsimple)

end

end FoxH

namespace ContCoh

noncomputable section

variable {G C : Type} {V : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup V] [Finite V]
  [DistribMulAction G V] [DistribMulAction C V]

/-- The restriction of a finite quotient map to the preimage of a Sylow subgroup, with codomain
restricted to that Sylow subgroup. -/
def sylowTwoPreimageHom (rho : ContinuousMonoidHom G C) (P : Sylow 2 C) :
    ContinuousMonoidHom (sylowTwoPreimage rho P) P where
  toFun u := ⟨rho u.1, u.2⟩
  map_one' := Subtype.ext (map_one rho)
  map_mul' u v := Subtype.ext (map_mul rho u.1 v.1)
  continuous_toFun :=
    (rho.continuous_toFun.comp continuous_subtype_val).subtype_mk _

/-- A surjective finite quotient remains surjective after restricting from the Sylow preimage
to the Sylow subgroup. -/
theorem sylowTwoPreimageHom_surjective (rho : ContinuousMonoidHom G C)
    (hrho : Function.Surjective rho) (P : Sylow 2 C) :
    Function.Surjective (sylowTwoPreimageHom rho P) := by
  intro p
  obtain ⟨g, hg⟩ := hrho p.1
  refine ⟨⟨g, ?_⟩, ?_⟩
  · change rho g ∈ P.1
    rw [hg]
    exact p.2
  · exact Subtype.ext hg

/-- If the action of a Sylow preimage is pulled back from the ambient finite action image, then
every simple elementary module for the preimage is trivial.

This is the precise representation-theoretic gain from the odd-index/Sylow reduction. -/
theorem smul_eq_self_of_simple_sylowTwoPreimage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hcompat : ∀ (g : G) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) V) :
    ∀ (u : sylowTwoPreimage rho P) (v : V), u • v = v := by
  have hsimpleP : FoxH.IsSimpleModTwo P V := by
    refine ⟨hsimple.1, ?_⟩
    intro W hW
    apply hsimple.2 W
    intro u w hw
    have hu : u.1 • w = (sylowTwoPreimageHom rho P u) • w := by
      exact hcompat u.1 w
    change u.1 • w ∈ W
    rw [hu]
    exact hW (sylowTwoPreimageHom rho P u) w hw
  have htrivP : ∀ (p : P) (v : V), p • v = v :=
    FoxH.smul_eq_self_of_isPGroup_two_of_simple P.2 hV₂ hsimpleP
  intro u v
  change u.1 • v = v
  rw [hcompat u.1 v]
  exact htrivP (sylowTwoPreimageHom rho P u) v

/-- A simple elementary module on a Sylow preimage has two elements.  Thus the simple kernels
left by coefficient devissage are exactly scalar `ZMod 2` kernels, not merely abstract trivial
modules. -/
theorem natCard_eq_two_of_simple_sylowTwoPreimage
    (rho : ContinuousMonoidHom G C) (P : Sylow 2 C)
    (hcompat : ∀ (g : G) (v : V), g • v = rho g • v)
    (hV₂ : ∀ v : V, v + v = 0)
    (hsimple : FoxH.IsSimpleModTwo (sylowTwoPreimage rho P) V) : Nat.card V = 2 :=
  FoxH.natCard_eq_two_of_simple_of_trivial hV₂ hsimple
    (smul_eq_self_of_simple_sylowTwoPreimage rho P hcompat hV₂ hsimple)

/-! ## The exact residual scalar-kernel tail -/

variable {A B : Type}
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
  [DistribMulAction C A]
  [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
  [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
  [DistribMulAction C B]

/-- The residual CD-2 premise after the acting finite image is a `2`-group: right exactness only
for elementary coefficient quotients whose kernel has two elements.

Such a kernel is additively `ZMod 2`; the `2`-group lemma above makes its action trivial.  In a
long exact cohomology sequence this premise is exactly the vanishing of the connecting map
`H²(G,B) → H³(G,ZMod 2)`. -/
def TwoGroupActionScalarKernelH2Tail (rho : ContinuousMonoidHom G C) : Prop :=
  ∀ (A B : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
    [DistribMulAction C A]
    [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
    [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
    [DistribMulAction C B]
    (g : A →+ B)
    (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b),
    (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective g → Nat.card ↑g.ker = 2 →
        H2RightExactAt g continuous_of_discreteTopology hgG

/-- A scalar-kernel tail is sufficient once an elementary coefficient quotient is exhibited as
a composite of scalar-kernel quotients.  This is the formal composition-series endpoint; the
individual factors are precisely the CD-2/H³ tails, while composition itself is unconditional. -/
theorem h2RightExactAt_of_scalarKernelFactorization
    (rho : ContinuousMonoidHom G C)
    (T : TwoGroupActionScalarKernelH2Tail rho)
    {D : Type} [AddCommGroup D] [TopologicalSpace D] [IsTopologicalAddGroup D]
    [DiscreteTopology D] [Finite D] [DistribMulAction G D] [ContinuousSMul G D]
    [DistribMulAction C D]
    (f : A →+ B) (g : B →+ D)
    (hfG : ∀ (x : G) (a : A), f (x • a) = x • f a)
    (hfC : ∀ (c : C) (a : A), f (c • a) = c • f a)
    (hgG : ∀ (x : G) (b : B), g (x • b) = x • g b)
    (hgC : ∀ (c : C) (b : B), g (c • b) = c • g b)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b)
    (hcompatD : ∀ (x : G) (d : D), x • d = rho x • d)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hD₂ : ∀ d : D, d + d = 0)
    (hfs : Function.Surjective f) (hgs : Function.Surjective g)
    (hfker : Nat.card ↑f.ker = 2) (hgker : Nat.card ↑g.ker = 2) :
    H2RightExactAt (g.comp f) continuous_of_discreteTopology
      (fun x a ↦ by simp only [AddMonoidHom.comp_apply]; rw [hfG, hgG]) := by
  exact h2RightExactAt_comp f continuous_of_discreteTopology hfG
    g continuous_of_discreteTopology hgG
    (T A B f hfG hfC hcompatA hcompatB hA₂ hB₂ hfs hfker)
    (T B D g hgG hgC hcompatB hcompatD hB₂ hD₂ hgs hgker)

/-- Continuity of an action pulled back from a finite discrete group to a discrete module. -/
private theorem continuousSMul_comp_finite
    {G C M : Type} [Monoid G] [TopologicalSpace G]
    [Monoid C] [TopologicalSpace C] [DiscreteTopology C]
    [TopologicalSpace M] [DiscreteTopology M] [SMul C M]
    (rho : ContinuousMonoidHom G C) [SMul G M]
    (hcompat : ∀ (g : G) (m : M), g • m = rho g • m) : ContinuousSMul G M := by
  constructor
  have hfac : (fun p : G × M ↦ p.1 • p.2) =
      (fun p : C × M ↦ p.1 • p.2) ∘ (fun p : G × M ↦ (rho p.1, p.2)) := by
    funext p
    exact hcompat p.1 p.2
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((rho.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

/-- Over a surjective finite `2`-group action image, the scalar-kernel tail proves right
exactness for every finite elementary coefficient quotient.

The proof is a strong induction on the cardinality of the kernel.  A simple kernel has two
elements by `natCard_eq_two_of_isPGroup_two_of_simple`, so it is handled by `T`.  Otherwise a
proper nonzero stable subgroup factors the coefficient quotient into two maps with smaller
kernels, and `h2RightExactAt_comp` assembles the lifts. -/
theorem h2RightExactAt_of_twoGroupActionScalarKernelTail
    (rho : ContinuousMonoidHom G C) (hrho : Function.Surjective rho)
    (hP : IsPGroup 2 C) (T : TwoGroupActionScalarKernelH2Tail rho)
    (g : A →+ B)
    (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
    (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
    (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
    (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b)
    (hA₂ : ∀ a : A, a + a = 0) (hB₂ : ∀ b : B, b + b = 0)
    (hgsurj : Function.Surjective g) :
    H2RightExactAt g continuous_of_discreteTopology hgG := by
  suffices H : ∀ (n : ℕ)
      (A B : Type) [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
      [DiscreteTopology A] [Finite A] [DistribMulAction G A] [ContinuousSMul G A]
      [DistribMulAction C A]
      [AddCommGroup B] [TopologicalSpace B] [IsTopologicalAddGroup B]
      [DiscreteTopology B] [Finite B] [DistribMulAction G B] [ContinuousSMul G B]
      [DistribMulAction C B]
      (g : A →+ B)
      (hgG : ∀ (x : G) (a : A), g (x • a) = x • g a)
      (hgC : ∀ (c : C) (a : A), g (c • a) = c • g a)
      (hcompatA : ∀ (x : G) (a : A), x • a = rho x • a)
      (hcompatB : ∀ (x : G) (b : B), x • b = rho x • b),
      Nat.card ↑g.ker = n → (∀ a : A, a + a = 0) → (∀ b : B, b + b = 0) →
      Function.Surjective g → H2RightExactAt g continuous_of_discreteTopology hgG by
    exact H (Nat.card ↑g.ker) A B g hgG hgC hcompatA hcompatB rfl hA₂ hB₂ hgsurj
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
      intro A B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hgG hgC hcompatA hcompatB
        hcard hA₂ hB₂ hsurj
      have hKstableG : ∀ (x : G) (a : A), a ∈ g.ker → x • a ∈ g.ker := by
        intro x a ha
        rw [AddMonoidHom.mem_ker, hgG, AddMonoidHom.mem_ker.mp ha, smul_zero]
      have hKstableC : ∀ (c : C) (a : A), a ∈ g.ker → c • a ∈ g.ker := by
        intro c a ha
        rw [AddMonoidHom.mem_ker, hgC, AddMonoidHom.mem_ker.mp ha, smul_zero]
      letI : DistribMulAction G ↑g.ker := FoxH.stableSubAction g.ker hKstableG
      letI : DistribMulAction C ↑g.ker := FoxH.stableSubAction g.ker hKstableC
      rcases subsingleton_or_nontrivial ↑g.ker with hsub | hnt
      · have hinj : Function.Injective g := (injective_iff_map_eq_zero g).mpr (fun a ha ↦ by
          have hak : ⟨a, AddMonoidHom.mem_ker.mpr ha⟩ = (0 : g.ker) := hsub.elim _ _
          exact congrArg Subtype.val hak)
        let E : A ≃+ B := AddEquiv.ofBijective g ⟨hinj, hsurj⟩
        let S : EquivariantAddSection (G := G) g := {
          sect := E.symm.toAddMonoidHom
          continuous_sect := continuous_of_discreteTopology
          sect_equivariant := fun x b ↦ by
            change E.symm (x • b) = x • E.symm b
            apply E.injective
            rw [E.apply_symm_apply]
            change x • b = g (x • E.symm b)
            rw [hgG]
            exact congrArg (x • ·) (show g (E.symm b) = b from E.apply_symm_apply b).symm
          right_inv := E.apply_symm_apply
        }
        exact H2RightExactAt.of_equivariantAddSection g continuous_of_discreteTopology hgG S
      · letI : Nontrivial ↑g.ker := hnt
        by_cases hsimp : FoxH.IsSimpleModTwo G ↑g.ker
        · have hsimpC : FoxH.IsSimpleModTwo C ↑g.ker := by
            refine ⟨hsimp.1, ?_⟩
            intro W hWC
            apply hsimp.2 W
            intro x w hw
            have hx : x • w = rho x • w := by
              apply Subtype.ext
              exact hcompatA x w.1
            rw [hx]
            exact hWC (rho x) w hw
          have hkcard : Nat.card ↑g.ker = 2 :=
            FoxH.natCard_eq_two_of_isPGroup_two_of_simple hP
              (fun a ↦ Subtype.ext (hA₂ a.1)) hsimpC
          exact T A B g hgG hgC hcompatA hcompatB hA₂ hB₂ hsurj hkcard
        · rw [FoxH.IsSimpleModTwo] at hsimp
          push Not at hsimp
          obtain ⟨WK, hWKstableG, hWKbot, hWKtop⟩ := hsimp hnt
          have hWKstableC : ∀ (c : C) (w : ↑g.ker), w ∈ WK → c • w ∈ WK := by
            intro c w hw
            obtain ⟨x, rfl⟩ := hrho c
            have hx : x • w = rho x • w := by
              apply Subtype.ext
              exact hcompatA x w.1
            rw [← hx]
            exact hWKstableG x w hw
          let W : AddSubgroup A := WK.map g.ker.subtype
          have hWle : W ≤ g.ker := AddSubgroup.map_subtype_le WK
          have hWstableG : ∀ (x : G) (a : A), a ∈ W → x • a ∈ W := by
            rintro x _ ⟨w, hw, rfl⟩
            refine ⟨x • w, hWKstableG x w hw, ?_⟩
            rfl
          have hWstableC : ∀ (c : C) (a : A), a ∈ W → c • a ∈ W := by
            rintro c _ ⟨w, hw, rfl⟩
            refine ⟨c • w, hWKstableC c w hw, ?_⟩
            rfl
          letI : TopologicalSpace (A ⧸ W) := ⊥
          letI : DiscreteTopology (A ⧸ W) := ⟨rfl⟩
          letI : DistribMulAction G (A ⧸ W) := FoxH.stableQuotAction W hWstableG
          letI : DistribMulAction C (A ⧸ W) := FoxH.stableQuotAction W hWstableC
          have hcompatQ : ∀ (x : G) (a : A ⧸ W), x • a = rho x • a := by
            intro x a
            induction a using QuotientAddGroup.induction_on with
            | _ a => exact congrArg (QuotientAddGroup.mk' W) (hcompatA x a)
          letI : ContinuousSMul G (A ⧸ W) := continuousSMul_comp_finite rho hcompatQ
          let qA : A →+ A ⧸ W := QuotientAddGroup.mk' W
          let gbar : (A ⧸ W) →+ B := QuotientAddGroup.lift W g hWle
          have hqG : ∀ (x : G) (a : A), qA (x • a) = x • qA a :=
            FoxH.stableQuotAction_mk'_equivariant W hWstableG
          have hqC : ∀ (c : C) (a : A), qA (c • a) = c • qA a :=
            FoxH.stableQuotAction_mk'_equivariant W hWstableC
          have hgbarG : ∀ (x : G) (a : A ⧸ W), gbar (x • a) = x • gbar a := by
            intro x a
            induction a using QuotientAddGroup.induction_on with
            | _ a =>
                change (QuotientAddGroup.lift W g hWle) (qA (x • a)) =
                  x • (QuotientAddGroup.lift W g hWle) (qA a)
                calc
                  _ = g (x • a) := QuotientAddGroup.lift_mk W hWle (x • a)
                  _ = x • g a := hgG x a
                  _ = _ := congrArg (x • ·) (QuotientAddGroup.lift_mk W hWle a).symm
          have hgbarC : ∀ (c : C) (a : A ⧸ W), gbar (c • a) = c • gbar a := by
            intro c a
            induction a using QuotientAddGroup.induction_on with
            | _ a =>
                change (QuotientAddGroup.lift W g hWle) (qA (c • a)) =
                  c • (QuotientAddGroup.lift W g hWle) (qA a)
                calc
                  _ = g (c • a) := QuotientAddGroup.lift_mk W hWle (c • a)
                  _ = c • g a := hgC c a
                  _ = _ := congrArg (c • ·) (QuotientAddGroup.lift_mk W hWle a).symm
          have hqsurj : Function.Surjective qA := QuotientAddGroup.mk'_surjective W
          have hgbarsurj : Function.Surjective gbar := by
            intro b
            obtain ⟨a, rfl⟩ := hsurj b
            exact ⟨qA a, QuotientAddGroup.lift_mk W hWle a⟩
          have hQ₂ : ∀ a : A ⧸ W, a + a = 0 := FoxH.two_torsion_quot W hA₂
          have hqker : qA.ker = W := QuotientAddGroup.ker_mk' W
          have hWcard : Nat.card ↑W = Nat.card ↑WK := by
            let fWK : WK → W := fun w ↦ ⟨w.1.1, ⟨w.1, w.2, rfl⟩⟩
            have hfWK : Function.Bijective fWK := by
              constructor
              · intro w₁ w₂ hw
                exact Subtype.ext (Subtype.ext (congrArg (fun w : W ↦ w.1) hw))
              · intro w
                rcases w.2 with ⟨k, hk, hkw⟩
                exact ⟨⟨k, hk⟩, Subtype.ext hkw⟩
            exact (Nat.card_congr (Equiv.ofBijective fWK hfWK)).symm
          have hq_lt : Nat.card ↑qA.ker < n := by
            rw [hqker, hWcard, ← hcard]
            exact FoxH.card_lt_of_ne_top WK hWKtop
          have hgb_lt : Nat.card ↑gbar.ker < n := by
            let phi : ↑g.ker → ↑gbar.ker := fun k ↦
              ⟨qA k.1, by
                rw [AddMonoidHom.mem_ker]
                exact QuotientAddGroup.lift_mk W hWle k.1 ▸ AddMonoidHom.mem_ker.mp k.2⟩
            have hphisurj : Function.Surjective phi := by
              rintro ⟨y, hy⟩
              obtain ⟨a, rfl⟩ := hqsurj y
              have ha : a ∈ g.ker := by
                rw [AddMonoidHom.mem_ker]
                change (QuotientAddGroup.lift W g hWle) ((QuotientAddGroup.mk' W) a) = 0 at hy
                exact (QuotientAddGroup.lift_mk W hWle a).symm.trans hy
              exact ⟨⟨a, ha⟩, rfl⟩
            have hphini : ¬ Function.Injective phi := by
              letI : Nontrivial ↑WK := (AddSubgroup.nontrivial_iff_ne_bot WK).mpr hWKbot
              have hWKne : ∃ w : WK, w ≠ 0 := exists_ne 0
              obtain ⟨w, hw⟩ := hWKne
              intro hi
              have hphi : phi w = phi 0 := by
                apply Subtype.ext
                change qA w.1.1 = qA (0 : A)
                rw [← sub_eq_zero]
                exact (QuotientAddGroup.eq_zero_iff _).mpr ⟨w, w.2, by simp⟩
              exact hw (Subtype.ext (hi hphi))
            letI : Fintype ↑g.ker := Fintype.ofFinite _
            letI : Fintype ↑gbar.ker := Fintype.ofFinite _
            rw [← hcard, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
            exact Fintype.card_lt_of_surjective_not_injective phi hphisurj hphini
          have hRq := IH _ hq_lt A (A ⧸ W) qA hqG hqC hcompatA hcompatQ rfl
            hA₂ hQ₂ hqsurj
          have hRgb := IH _ hgb_lt (A ⧸ W) B gbar hgbarG hgbarC hcompatQ hcompatB rfl
            hQ₂ hB₂ hgbarsurj
          have hcomp := h2RightExactAt_comp qA continuous_of_discreteTopology hqG
            gbar continuous_of_discreteTopology hgbarG hRq hRgb
          intro z
          obtain ⟨x, hx⟩ := hcomp z
          refine ⟨x, ?_⟩
          simpa [qA, gbar] using hx

end

end ContCoh

end GQ2
