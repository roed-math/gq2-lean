/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModule
import GQ2.Dyadic.Count.Variation

/-!
# The finite Heisenberg module cocycle

The central term in `HeisLift.mul_z` is the dual-first pairing `lam (g • a')`.  This file
packages that term as a module cocycle and proves that its intrinsic module relator is exactly
the central coordinate of the corresponding Heisenberg evaluation.
-/

namespace GQ2.Dyadic.Count

noncomputable section

open GQ2 GQ2.FoxH GQ2.Dyadic ContCoh

section FiniteHeisenberg

variable {X : Type*} {C : Type} [Group C]
  {A : Type} [AddCommGroup A] [DistribMulAction C A]

local instance heisModuleScalarAction :
    DistribMulAction (WordLift (A × ElemDual A) C) (ZMod 2) :=
  scalarActionZmodTwo _

/-- The Heisenberg cocycle as a module cocycle with trivial scalar action. -/
noncomputable def moduleKappaHeis :
    ModuleTwoCocycle (WordLift (A × ElemDual A) C) (ZMod 2) where
  κ p q := p.u.2 (p.g • q.u.1)
  norm := by simp [WordLift.one_u]
  cocyc p q r := by
    rw [scalarActionZmodTwo_triv]
    have h := (kappaHeisN (A := A) (C := C)).cocyc p q r
    change (kappaHeisN (A := A) (C := C)).κ q r +
        (kappaHeisN (A := A) (C := C)).κ p (q * r) =
      (kappaHeisN (A := A) (C := C)).κ (p * q) r +
        (kappaHeisN (A := A) (C := C)).κ p q
    simpa only [add_comm] using h.symm

/-- The module extension of `moduleKappaHeis` maps to the Heisenberg lift, with its fibre
coordinate becoming the Heisenberg central coordinate. -/
noncomputable def modulePhiHeis :
    ModuleExt (moduleKappaHeis (A := A) (C := C)) →* HeisLift A C where
  toFun p := ⟨p.g.u.1, p.g.u.2, p.u, p.g.g⟩
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem modulePhiHeis_lift (c : X → C) (x : X → A)
    (y : X → ElemDual A) (i : X) :
    modulePhiHeis
        (ModuleExt.lift (moduleKappaHeis (A := A) (C := C)) (heisBase c x y) i) =
      heisGen c x y i := rfl

variable [Finite A] [Finite C]

local instance moduleHeisTopologicalSpace : TopologicalSpace (HeisLift A C) := ⊥
local instance moduleHeisDiscreteTopology : DiscreteTopology (HeisLift A C) := ⟨rfl⟩

/-- At the Heisenberg module cocycle, the intrinsic module relator is exactly the central
coordinate of the Heisenberg evaluation. -/
theorem moduleRel_moduleKappaHeis (W : PWord X) (c : X → C) (x : X → A)
    (y : X → ElemDual A) :
    moduleRel W (heisBase c x y) (moduleKappaHeis (A := A) (C := C)) =
      (PWord.eval (heisGen c x y) W).z := by
  let F : ContinuousMonoidHom
      (ModuleExt (moduleKappaHeis (A := A) (C := C))) (HeisLift A C) :=
    ⟨modulePhiHeis, continuous_of_discreteTopology⟩
  have h := PWord.map_eval F
    (ModuleExt.lift (moduleKappaHeis (A := A) (C := C)) (heisBase c x y)) W
  have hgen : (fun i => F
      (ModuleExt.lift (moduleKappaHeis (A := A) (C := C)) (heisBase c x y) i)) =
      heisGen c x y := rfl
  rw [hgen] at h
  exact congrArg HeisLift.z h

end FiniteHeisenberg

end

end GQ2.Dyadic.Count
