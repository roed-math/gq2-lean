/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleGlobal
import GQ2.Dyadic.Count.HTwoModuleReflection

/-!
# Assembly of the module-valued degree-two word obstruction

This file combines the global, choice-independent relator obstruction with the
finite-level reflection theorem.  Under an admissible marked presentation and the
explicit action-compatible finite-level resolver hypotheses, it constructs the full
`ModuleH2WordData`, and hence an injection from continuous module-valued `H²` to the
word cokernel.

The result is coefficient-generic: the finite discrete coefficient group may carry
an arbitrary continuous action factoring through the specified finite group `C`.
No surjectivity, bijectivity, or cardinal equality is asserted.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

section Assembly

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

/-- **Concrete module-valued `H²` comparison data.**  The global obstruction reads at
every action-compatible finite factor as the intrinsic module relator vector.  Feeding
that readback to the finite reflection theorem supplies the last field of
`ModuleH2WordData`.

The hypotheses retained here are exactly the source inputs used by the construction:
admissibility of the marked presentation, factorization of the action through `rho`,
wildness at every finite level, exponent two in the coefficient group, and a resolver
at every action-compatible finite quotient. -/
noncomputable def globalModuleH2WordData
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
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup))) :
    ModuleH2WordData (Gamma := Gamma) (A := A) (C := C)
      (fun i ↦ rho (gen i)) w := by
  let D := globalModuleH2WordDescentData hpres rho hcompat (fun _ ↦ rfl) hresolve
  refine D.withReflection ?_
  apply reflects_coboundary_of_moduleFactor_read hpres rho hcompat hwildLevel hA₂
    D.obstruction hresolve
  intro f V hV
  dsimp only
  let rhoV : (Gamma ⧸ V.toSubgroup) →* C := quotientActionHom rho V hV
  letI : DistribMulAction (Gamma ⧸ V.toSubgroup) A :=
    DistribMulAction.compHom A rhoV
  intro z hfactor
  let F : ModuleLevelFactor rho (moduleNormalize f.1) :=
    { V := V
      hV := hV
      z := z
      hfact := hfactor }
  change moduleObsFun W gen rho hcompat f =
    fun k ↦ moduleRel (W k)
      (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) z
  rw [moduleObsFun_eq W gen rho hcompat f F]
  rfl

/-- The concrete coefficient-generic map from continuous `H²` to the word
cokernel. -/
noncomputable def globalModuleH2Word
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
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup))) :
    H2 Gamma A →+ WordH2 (fun i ↦ rho (gen i)) w A :=
  moduleH2Word
    (globalModuleH2WordData hpres rho hcompat hwildLevel hA₂ hresolve)

omit [Fintype iota] [Fintype rel] [DecidableEq iota] in
/-- Regression theorem: on a cocycle representative, the assembled map is exactly
the quotient class of the global relator obstruction. -/
@[simp] theorem globalModuleH2Word_mk
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
    (f : Z2 Gamma A) :
    globalModuleH2Word hpres rho hcompat hwildLevel hA₂ hresolve (H2mk Gamma A f) =
      QuotientAddGroup.mk' (heisD1 (A := A) (fun i ↦ rho (gen i)) w).range
        (moduleObsFam W gen rho hcompat f) := rfl

omit [Fintype iota] [Fintype rel] [DecidableEq iota] in
/-- The assembled arbitrary-coefficient `H²` word map is injective. -/
theorem globalModuleH2Word_injective
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
      ResolvesAt W w (WordLift A (Gamma ⧸ V.toSubgroup))) :
    Function.Injective
      (globalModuleH2Word hpres rho hcompat hwildLevel hA₂ hresolve) :=
  moduleH2Word_injective _

end Assembly

end GQ2.Dyadic.Count
