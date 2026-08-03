/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleAssembly

/-!
# The module-valued degree-two comparison at equal cardinality

The assembled module-valued word map is already injective.  Since the word cokernel is
finite whenever the relator set and coefficient group are finite, equality of the two
`Nat.card`s is the only additional hypothesis needed to make that particular map bijective.
This file packages the resulting canonical (relative to the presentation and resolver data)
additive equivalence.

No cardinal equality is asserted here.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## A two-element additive group

This small cardinality lemma handles the scalar orientation in source-comparison packages.
Unlike an equivalence obtained from a specified comparison map, it is noncanonical: it chooses
the unique nonzero element of the two-element group.
-/

/-- A two-torsion additive group with the cardinality of `ZMod 2` is additively equivalent to
`ZMod 2`.  Finiteness and nontriviality are consequences of the stated cardinal equality. -/
noncomputable def addEquivZModTwo_of_card_eq
    {B : Type*} [AddCommGroup B] (hB₂ : ∀ b : B, b + b = 0)
    (hcard : Nat.card B = Nat.card (ZMod 2)) : B ≃+ ZMod 2 := by
  letI : Finite B := (Nat.card_ne_zero.mp (by rw [hcard, Nat.card_zmod]; decide)).2
  letI : Nontrivial B := Finite.one_lt_card_iff_nontrivial.mp (by
    rw [hcard, Nat.card_zmod]
    decide)
  let b : B := Classical.choose (exists_ne (0 : B))
  have hb : b ≠ 0 := Classical.choose_spec (exists_ne (0 : B))
  let toB : ZMod 2 →+ B :=
    ZMod.lift 2 ⟨zmultiplesHom B b, by
      show ((2 : ℕ) : ℤ) • b = 0
      rw [natCast_zsmul]
      simpa [two_nsmul] using hB₂ b⟩
  have hone : toB 1 = b := by
    show ZMod.lift 2 _ ((1 : ℤ) : ZMod 2) = b
    rw [ZMod.lift_coe]
    exact one_zsmul b
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  have hinj : Function.Injective toB := by
    rw [injective_iff_map_eq_zero]
    intro z hz
    rcases hcases z with rfl | rfl
    · rfl
    · exact (hb (hone.symm.trans hz)).elim
  letI : Fintype B := Fintype.ofFinite B
  have hbij : Function.Bijective toB :=
    (Fintype.bijective_iff_injective_and_card toB).mpr ⟨hinj, by
      simpa only [Nat.card_eq_fintype_card] using hcard.symm⟩
  exact (AddEquiv.ofBijective toB hbij).symm

section Equivalence

variable {iota rel : Type*} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {Gamma A C : Type}
  [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [CompactSpace Gamma] [TotallyDisconnectedSpace Gamma]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DiscreteTopology A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A] [DistribMulAction C A]
  {gen : iota → Gamma} {W : rel → PWord iota} {w : rel → FreeGroup iota}
  {J : Set iota}

omit [Fintype iota] [DecidableEq iota] in
/-- Equal finite cardinalities upgrade the assembled injection to a bijection.  Finiteness of
the word target follows from finiteness of `rel` and `A`; finiteness of source `H²` is then
derived from the already-proved injection. -/
theorem globalModuleH2Word_bijective_of_card_eq
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hcard : Nat.card (H2 Gamma A) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w A)) :
    Function.Bijective
      (globalModuleH2Word hpres rho hcompat hwildLevel hA₂ hresolve) := by
  let f := globalModuleH2Word hpres rho hcompat hwildLevel hA₂ hresolve
  have hinj : Function.Injective f :=
    globalModuleH2Word_injective hpres rho hcompat hwildLevel hA₂ hresolve
  letI : Finite (H2 Gamma A) := Finite.of_injective f hinj
  letI : Fintype (H2 Gamma A) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (gen i)) w A) := Fintype.ofFinite _
  refine (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, ?_⟩
  simpa only [Nat.card_eq_fintype_card] using hcard

/-- The additive equivalence furnished by the concrete assembled map under equal
cardinalities. -/
noncomputable def globalModuleH2WordEquiv_of_card_eq
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hcard : Nat.card (H2 Gamma A) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w A)) :
    H2 Gamma A ≃+ WordH2 (fun i ↦ rho (gen i)) w A :=
  AddEquiv.ofBijective
    (globalModuleH2Word hpres rho hcompat hwildLevel hA₂ hresolve)
    (globalModuleH2Word_bijective_of_card_eq
      hpres rho hcompat hwildLevel hA₂ hresolve hcard)

omit [Fintype iota] [DecidableEq iota] in
/-- Representative regression: the equivalence still evaluates a cocycle by the global
relator obstruction; passing through `AddEquiv.ofBijective` changes no forward computation. -/
@[simp] theorem globalModuleH2WordEquiv_of_card_eq_mk
    (hpres : IsAdmissibleMarkedPresentation Gamma gen W J)
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (a : A), g • a = rho g • a)
    (hwildLevel : ∀ V : OpenNormalSubgroup Gamma,
      IsWildTwo J (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)))
    (hA₂ : ∀ a : A, a + a = 0)
    (hresolve : ∀ (V : OpenNormalSubgroup Gamma)
        (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
        DistribMulAction.compHom A rhoV
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup)))
    (hcard : Nat.card (H2 Gamma A) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w A))
    (f : Z2 Gamma A) :
    globalModuleH2WordEquiv_of_card_eq
        hpres rho hcompat hwildLevel hA₂ hresolve hcard (H2mk Gamma A f) =
      QuotientAddGroup.mk' (heisD1 (A := A) (fun i ↦ rho (gen i)) w).range
        (moduleObsFam W gen rho hcompat f) := rfl

end Equivalence

end GQ2.Dyadic.Count
