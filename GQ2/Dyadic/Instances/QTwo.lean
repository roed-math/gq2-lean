/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.CertificateMain
import GQ2.Dyadic.Words.L
import GQ2.Roe.Main

/-!
# The `n = 1` wrapper: the L-word machinery recovers the `ℚ₂` theorem (ticket AS4)

Work in progress.
-/

namespace GQ2.Dyadic.QTwo

open GQ2 GQ2.Dyadic.Words.LSq CategoryTheory

/-! ## §1 The `n = 1` alphabet is the `ℚ₂` alphabet -/

/-- The `n = 1` letter `σ, τ, x₀, x₁` as the index `0, 1, 2, 3` of `GQ2.univMarking`. -/
def genToFin : Generator 1 → Fin 4
  | .sigma => 0
  | .tau => 1
  | .wild i => i.succ.succ

/-- The inverse table. -/
def finToGen : Fin 4 → Generator 1 := ![.sigma, .tau, .wild 0, .wild 1]

@[simp] theorem finToGen_genToFin (g : Generator 1) : finToGen (genToFin g) = g := by
  revert g; decide

@[simp] theorem genToFin_finToGen (i : Fin 4) : genToFin (finToGen i) = i := by
  revert i; decide

/-- The alphabet equivalence `{σ, τ, x₀, x₁} ≃ Fin 4`. -/
def alphEquiv : Generator 1 ≃ Fin 4 where
  toFun := genToFin
  invFun := finToGen
  left_inv := finToGen_genToFin
  right_inv := genToFin_finToGen

/-! ## §2 The free profinite groups agree -/

/-- Two continuous homs out of a free profinite group agreeing on the generators are equal. -/
theorem free_hom_ext {X : Type} {P : ProfiniteGrp} {f g : FreeProfiniteGroup X ⟶ P}
    (h : ∀ x, f (FreeProfiniteGroup.of x) = g (FreeProfiniteGroup.of x)) : f = g :=
  (FreeProfiniteGroup.homEquiv X P).injective <| funext fun x => by
    rw [FreeProfiniteGroup.homEquiv_apply, FreeProfiniteGroup.homEquiv_apply]; exact h x

/-- `F(σ, τ, x₀, x₁) ⟶ F₄`, letter by letter. -/
noncomputable def toQ2Free : FreeProfiniteGroup (Generator 1) ⟶ FreeProfiniteGroup (Fin 4) :=
  (FreeProfiniteGroup.homEquiv (Generator 1) (FreeProfiniteGroup (Fin 4))).symm
    fun g => FreeProfiniteGroup.of (genToFin g)

/-- `F₄ ⟶ F(σ, τ, x₀, x₁)`, letter by letter. -/
noncomputable def ofQ2Free : FreeProfiniteGroup (Fin 4) ⟶ FreeProfiniteGroup (Generator 1) :=
  (FreeProfiniteGroup.homEquiv (Fin 4) (FreeProfiniteGroup (Generator 1))).symm
    fun i => FreeProfiniteGroup.of (finToGen i)

@[simp] theorem toQ2Free_of (g : Generator 1) :
    toQ2Free (FreeProfiniteGroup.of g) = FreeProfiniteGroup.of (genToFin g) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem ofQ2Free_of (i : Fin 4) :
    ofQ2Free (FreeProfiniteGroup.of i) = FreeProfiniteGroup.of (finToGen i) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem ofQ2Free_comp_toQ2Free : toQ2Free ≫ ofQ2Free = 𝟙 _ :=
  free_hom_ext fun x => by simp

theorem toQ2Free_comp_ofQ2Free : ofQ2Free ≫ toQ2Free = 𝟙 _ :=
  free_hom_ext fun x => by simp

/-- The alphabet transport `F(σ, τ, x₀, x₁) → F₄`, as a continuous monoid hom. -/
noncomputable def toQ2F : ContinuousMonoidHom ((FreeProfiniteGroup (Generator 1)) : Type)
    ((FreeProfiniteGroup (Fin 4)) : Type) := toQ2Free.hom

/-- Its inverse. -/
noncomputable def ofQ2F : ContinuousMonoidHom ((FreeProfiniteGroup (Fin 4)) : Type)
    ((FreeProfiniteGroup (Generator 1)) : Type) := ofQ2Free.hom

@[simp] theorem toQ2F_of (g : Generator 1) :
    toQ2F (FreeProfiniteGroup.of g) = FreeProfiniteGroup.of (genToFin g) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem ofQ2F_of (i : Fin 4) :
    ofQ2F (FreeProfiniteGroup.of i) = FreeProfiniteGroup.of (finToGen i) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem ofQ2F_toQ2F (w : ((FreeProfiniteGroup (Generator 1)) : Type)) :
    ofQ2F (toQ2F w) = w := by
  rw [show ofQ2F (toQ2F w) = (toQ2Free ≫ ofQ2Free) w from rfl, ofQ2Free_comp_toQ2Free,
    ProfiniteGrp.id_apply]

@[simp] theorem toQ2F_ofQ2F (w : ((FreeProfiniteGroup (Fin 4)) : Type)) :
    toQ2F (ofQ2F w) = w := by
  rw [show toQ2F (ofQ2F w) = (ofQ2Free ≫ toQ2Free) w from rfl, toQ2Free_comp_ofQ2Free,
    ProfiniteGrp.id_apply]

theorem toQ2F_surjective : Function.Surjective toQ2F := fun w => ⟨ofQ2F w, toQ2F_ofQ2F w⟩

theorem ofQ2F_surjective : Function.Surjective ofQ2F := fun w => ⟨toQ2F w, ofQ2F_toQ2F w⟩

theorem toQ2F_injective : Function.Injective toQ2F := fun a b h => by
  rw [← ofQ2F_toQ2F a, h, ofQ2F_toQ2F]

/-- **The universal marking, transported.**  The `n = 1` tautological marking of
`F(σ, τ, x₀, x₁)` pushed along the alphabet transport is `GQ2.univMarking` — read in the
`Marking 1` vocabulary through `Marking.ofQ2`. -/
theorem freeMarking_map_toQ2F :
    (freeMarking 1).map ⇑toQ2F = Marking.ofQ2 univMarking := by
  ext g
  match g with
  | .sigma => exact toQ2F_of _
  | .tau => exact toQ2F_of _
  | .wild ⟨0, _⟩ => exact toQ2F_of _
  | .wild ⟨1, _⟩ => exact toQ2F_of _
  | .wild ⟨k + 2, hk⟩ => exact absurd hk (by omega)

end GQ2.Dyadic.QTwo
