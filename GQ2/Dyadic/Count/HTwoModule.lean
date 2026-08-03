/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Lifts

/-!
# Degree-two comparison with nontrivial module coefficients: the exact frontier

`Count.HTwo` constructs an injection

`H²(Γ, 𝔽₂) → WordH²(𝔽₂)`

by turning a scalar cocycle into a *central* extension.  That construction is not
coefficient-generic: for a nontrivial `C`-module `A`, the extension is a twisted
semidirect product, normalization subtracts `g • φ(1,1)` rather than the constant
`φ(1,1)`, and changing generator lifts is measured by the Fox differential for
the nontrivial action.

This file records the reusable algebraic core of the module-coefficient route and
packages the remaining comparison problem as an explicit data structure.  In
particular it does **not** assert an isomorphism: even after the comparison map is
constructed, identities among relators can give it a cokernel.

## What is closed here

* `ModuleTwoCocycle`: normalized `A`-valued cocycles for an arbitrary action;
* `ModuleExt`: the associated twisted semidirect extension;
* pullback and coefficient additivity of module cocycles;
* `moduleNormalize`: the correct normalization for nontrivial coefficients,
  together with its normalization, cocycle, additivity, and cohomology lemmas;
* the semidirect lift-shift law `moduleWord_eval_shift`, identifying the correction
  with `heisD1` for arbitrary module coefficients;
* `moduleRelFam_coboundary_mem_range`, the finite-level coboundary-to-`heisD1`
  computation required by the descent half of the comparison;
* `ModuleH2WordData`: the exact two obstruction properties needed to descend an
  additive obstruction to `H²` and prove injectivity;
* `moduleH2Word` and `moduleH2Word_injective`: the coefficient-generic assembly,
  conditional only on that explicit obstruction data.

## What remains

To instantiate `ModuleH2WordData` for the dyadic presentation, two global assembly
steps remain after the finite factorization and shift calculations in this file:

1. package the finite-level vectors `moduleRel` into a choice-independent additive map
   `Z2 Γ A →+ (rel → A)`.  `moduleRel_comap` supplies refinement naturality and
   `moduleRelFam_coboundary_mem_range` supplies the finite-level coboundary law; the
   common-refinement/additivity bookkeeping is not yet assembled;
2. use the admissible presentation to show that a word-coboundary obstruction splits
   `ModuleExt` (the semidirect replacement for `mem_B2_of_pObsFam_mem_range`).  For an
   elementary `2`-module this additionally needs the explicit wildness check for the
   shifted semidirect marking.

Surjectivity onto `WordH²` is a separate,
stronger asphericity/identities-among-relators assertion and is deliberately absent.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## 1. Module-valued normalized cocycles -/

section ModuleCocycle

variable {L A B : Type*} [Group L]
  [AddCommGroup A] [DistribMulAction L A]
  [AddCommGroup B] [DistribMulAction L B]

/-- A normalized inhomogeneous `2`-cocycle with values in an arbitrary `L`-module. -/
structure ModuleTwoCocycle (L A : Type*) [Group L] [AddCommGroup A]
    [DistribMulAction L A] where
  /-- The underlying cochain. -/
  κ : L → L → A
  /-- Normalization at `(1,1)`.  The cocycle law then forces normalization on both axes. -/
  norm : κ 1 1 = 0
  /-- The inhomogeneous cocycle identity. -/
  cocyc : ∀ g h k : L, g • κ h k + κ g (h * k) = κ (g * h) k + κ g h

namespace ModuleTwoCocycle

variable (z : ModuleTwoCocycle L A)

theorem κ_one_left (g : L) : z.κ 1 g = 0 := by
  have h := z.cocyc 1 1 g
  simpa [z.norm] using h

theorem κ_one_right (g : L) : z.κ g 1 = 0 := by
  have h := z.cocyc g 1 1
  simpa [z.norm] using h

theorem κ_inv (g : L) : g⁻¹ • z.κ g g⁻¹ = z.κ g⁻¹ g := by
  have h := z.cocyc g⁻¹ g g⁻¹
  simpa [z.κ_one_left, z.κ_one_right] using h

/-- Two module cocycles are equal when their underlying cochains are equal. -/
@[ext] theorem ext {z z' : ModuleTwoCocycle L A} (h : z.κ = z'.κ) : z = z' := by
  cases z
  cases z'
  cases h
  rfl

/-- Pointwise addition of module cocycles. -/
instance : Add (ModuleTwoCocycle L A) where
  add z z' :=
    { κ := fun g h => z.κ g h + z'.κ g h
      norm := by rw [z.norm, z'.norm, add_zero]
      cocyc := fun g h k => by
        rw [smul_add]
        calc
          g • z.κ h k + g • z'.κ h k + (z.κ g (h * k) + z'.κ g (h * k))
              = (g • z.κ h k + z.κ g (h * k))
                + (g • z'.κ h k + z'.κ g (h * k)) := by abel
          _ = (z.κ (g * h) k + z.κ g h) + (z'.κ (g * h) k + z'.κ g h) := by
                rw [z.cocyc, z'.cocyc]
          _ = z.κ (g * h) k + z'.κ (g * h) k + (z.κ g h + z'.κ g h) := by abel }

@[simp] theorem add_κ (z z' : ModuleTwoCocycle L A) (g h : L) :
    (z + z').κ g h = z.κ g h + z'.κ g h := rfl

/-- The normalized module cocycle attached to a normalized `1`-cochain. -/
def coboundary (lam : L → A) (hlam1 : lam 1 = 0) : ModuleTwoCocycle L A where
  κ g h := g • lam h - lam (g * h) + lam g
  norm := by simp [hlam1]
  cocyc g h k := by
    simp only [smul_add, smul_sub, mul_smul]
    rw [mul_assoc g h k]
    abel

@[simp] theorem coboundary_κ (lam : L → A) (hlam1 : lam 1 = 0) (g h : L) :
    (coboundary lam hlam1).κ g h = g • lam h - lam (g * h) + lam g := rfl

/-- Push a cocycle through an equivariant additive homomorphism. -/
def map (f : A →+ B) (hf : ∀ (g : L) (a : A), f (g • a) = g • f a)
    (z : ModuleTwoCocycle L A) : ModuleTwoCocycle L B where
  κ g h := f (z.κ g h)
  norm := by rw [z.norm, map_zero]
  cocyc g h k := by
    rw [← hf, ← map_add, z.cocyc, map_add]

@[simp] theorem map_κ (f : A →+ B) (hf) (z : ModuleTwoCocycle L A) (g h : L) :
    (z.map f hf).κ g h = f (z.κ g h) := rfl

section Pullback

variable {L' : Type*} [Group L'] [DistribMulAction L' A]

/-- Pull a module cocycle back along a homomorphism compatible with the two actions. -/
def comap (z : ModuleTwoCocycle L A) (f : L' →* L)
    (hf : ∀ (g : L') (a : A), g • a = f g • a) : ModuleTwoCocycle L' A where
  κ g h := z.κ (f g) (f h)
  norm := by rw [map_one, z.norm]
  cocyc g h k := by
    rw [hf, map_mul, map_mul]
    exact z.cocyc (f g) (f h) (f k)

@[simp] theorem comap_κ (z : ModuleTwoCocycle L A) (f : L' →* L) (hf)
    (g h : L') : (z.comap f hf).κ g h = z.κ (f g) (f h) := rfl

end Pullback

end ModuleTwoCocycle

/-! ## 2. The twisted semidirect extension -/

/-- The extension `A ⋊_κ L` attached to a module-valued cocycle. -/
@[ext] structure ModuleExt (z : ModuleTwoCocycle L A) where
  /-- Fibre coordinate. -/
  u : A
  /-- Base coordinate. -/
  g : L

namespace ModuleExt

variable {z : ModuleTwoCocycle L A}

instance : One (ModuleExt z) := ⟨0, 1⟩

instance : Mul (ModuleExt z) :=
  ⟨fun p q => ⟨p.u + p.g • q.u + z.κ p.g q.g, p.g * q.g⟩⟩

instance : Inv (ModuleExt z) :=
  ⟨fun p => ⟨-(p.g⁻¹ • (p.u + z.κ p.g p.g⁻¹)), p.g⁻¹⟩⟩

@[simp] theorem one_u : (1 : ModuleExt z).u = 0 := rfl
@[simp] theorem one_g : (1 : ModuleExt z).g = 1 := rfl
@[simp] theorem mul_u (p q : ModuleExt z) :
    (p * q).u = p.u + p.g • q.u + z.κ p.g q.g := rfl
@[simp] theorem mul_g (p q : ModuleExt z) : (p * q).g = p.g * q.g := rfl
@[simp] theorem inv_u (p : ModuleExt z) :
    p⁻¹.u = -(p.g⁻¹ • (p.u + z.κ p.g p.g⁻¹)) := rfl
@[simp] theorem inv_g (p : ModuleExt z) : p⁻¹.g = p.g⁻¹ := rfl

instance : Group (ModuleExt z) where
  mul_assoc p q r := by
    apply ModuleExt.ext
    · simp only [mul_u, mul_g, smul_add, mul_smul]
      have hz := z.cocyc p.g q.g r.g
      have hz' : z.κ p.g q.g + z.κ (p.g * q.g) r.g =
          p.g • z.κ q.g r.g + z.κ p.g (q.g * r.g) := by
        rw [add_comm (z.κ p.g q.g), hz]
      calc
        _ = p.u + p.g • q.u + p.g • q.g • r.u
              + (z.κ (p.g * q.g) r.g + z.κ p.g q.g) := by abel
        _ = p.u + p.g • q.u + p.g • q.g • r.u
              + (p.g • z.κ q.g r.g + z.κ p.g (q.g * r.g)) := by
                rw [add_comm (z.κ (p.g * q.g) r.g), hz']
        _ = _ := by abel
    · exact mul_assoc _ _ _
  one_mul p := by
    apply ModuleExt.ext
    · simp [z.κ_one_left]
    · exact one_mul _
  mul_one p := by
    apply ModuleExt.ext
    · simp [z.κ_one_right]
    · exact mul_one _
  inv_mul_cancel p := by
    apply ModuleExt.ext
    · simp only [inv_u, inv_g, mul_u, smul_add, z.κ_inv]
      change -(p.g⁻¹ • p.u + z.κ p.g⁻¹ p.g) + p.g⁻¹ • p.u + z.κ p.g⁻¹ p.g = 0
      abel
    · exact inv_mul_cancel _

/-- Projection to the base group. -/
def baseProj (z : ModuleTwoCocycle L A) : ModuleExt z →* L where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem baseProj_apply (z : ModuleTwoCocycle L A) (p : ModuleExt z) :
    baseProj z p = p.g := rfl

/-- Inclusion of the additive fibre over the identity. -/
def incl (z : ModuleTwoCocycle L A) (a : A) : ModuleExt z := ⟨a, 1⟩

@[simp] theorem incl_u (a : A) : (incl z a).u = a := rfl
@[simp] theorem incl_g (a : A) : (incl z a).g = 1 := rfl
@[simp] theorem incl_zero : incl z (0 : A) = 1 := rfl

/-- Multiplication in the identity fibre is addition in the coefficient module. -/
theorem incl_add (a b : A) : incl z (a + b) = incl z a * incl z b := by
  apply ModuleExt.ext
  · simp [z.κ_one_left]
  · simp

/-- Moving a fibre element past an extension element applies the base action. -/
theorem mul_incl (p : ModuleExt z) (a : A) :
    p * incl z a = incl z (p.g • a) * p := by
  apply ModuleExt.ext
  · simp [z.κ_one_left, z.κ_one_right, add_comm]
  · simp

/-- Conjugation on the fibre is exactly the action of the base coordinate. -/
theorem conj_incl (p : ModuleExt z) (a : A) :
    incl z (p.g • a) = p * incl z a * p⁻¹ := by
  rw [mul_incl, mul_inv_cancel_right]

theorem base_eq_one_iff (p : ModuleExt z) : p.g = 1 ↔ p = incl z p.u :=
  ⟨fun h => ModuleExt.ext rfl h, fun h => by rw [h]; rfl⟩

/-- The zero-fibre lift of a base marking. -/
def lift (z : ModuleTwoCocycle L A) {X : Type*} (m : X → L) : X → ModuleExt z :=
  fun x => ⟨0, m x⟩

@[simp] theorem lift_u {X : Type*} (m : X → L) (x : X) : (lift z m x).u = 0 := rfl
@[simp] theorem lift_g {X : Type*} (m : X → L) (x : X) : (lift z m x).g = m x := rfl

/-- A normalized coboundary extension maps to the split semidirect product by adding the
splitting cochain to the fibre coordinate. -/
def coboundaryToSplit (lam : L → A) (hlam1 : lam 1 = 0) :
    ModuleExt (ModuleTwoCocycle.coboundary lam hlam1) →* WordLift A L where
  toFun p := ⟨p.u + lam p.g, p.g⟩
  map_one' := by
    apply WordLift.ext
    · simp [hlam1]
    · rfl
  map_mul' p q := by
    apply WordLift.ext
    · simp only [mul_u, mul_g, ModuleTwoCocycle.coboundary_κ, WordLift.mul_u,
        smul_add]
      abel
    · rfl

@[simp] theorem coboundaryToSplit_u (lam : L → A) (hlam1 : lam 1 = 0)
    (p : ModuleExt (ModuleTwoCocycle.coboundary lam hlam1)) :
    (coboundaryToSplit lam hlam1 p).u = p.u + lam p.g := rfl

@[simp] theorem coboundaryToSplit_g (lam : L → A) (hlam1 : lam 1 = 0)
    (p : ModuleExt (ModuleTwoCocycle.coboundary lam hlam1)) :
    (coboundaryToSplit lam hlam1 p).g = p.g := rfl

@[simp] theorem coboundaryToSplit_lift {X : Type*} (lam : L → A) (hlam1 : lam 1 = 0)
    (m : X → L) (x : X) :
    coboundaryToSplit lam hlam1 (lift (ModuleTwoCocycle.coboundary lam hlam1) m x) =
      foxLift m (fun i => lam (m i)) x := by
  apply WordLift.ext <;> simp [coboundaryToSplit, lift, foxLift]

/-- `ModuleExt` has the expected finite carrier. -/
def equivProd (z : ModuleTwoCocycle L A) : ModuleExt z ≃ A × L where
  toFun p := (p.u, p.g)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance [Finite A] [Finite L] : Finite (ModuleExt z) :=
  Finite.of_equiv _ (equivProd z).symm

instance : TopologicalSpace (ModuleExt z) := ⊥
instance : DiscreteTopology (ModuleExt z) := ⟨rfl⟩

section Pullback

variable {L' : Type*} [Group L'] [DistribMulAction L' A]

/-- Pullback of extensions along a compatible base homomorphism. -/
def mapBase (z : ModuleTwoCocycle L A) (f : L' →* L)
    (hf : ∀ (g : L') (a : A), g • a = f g • a) :
    ModuleExt (z.comap f hf) →* ModuleExt z where
  toFun p := ⟨p.u, f p.g⟩
  map_one' := ModuleExt.ext rfl (map_one f)
  map_mul' p q := by
    apply ModuleExt.ext
    · show p.u + p.g • q.u + z.κ (f p.g) (f q.g)
          = p.u + f p.g • q.u + z.κ (f p.g) (f q.g)
      rw [hf]
    · exact map_mul f p.g q.g

@[simp] theorem mapBase_u (z : ModuleTwoCocycle L A) (f : L' →* L) (hf)
    (p : ModuleExt (z.comap f hf)) : (mapBase z f hf p).u = p.u := rfl

@[simp] theorem mapBase_g (z : ModuleTwoCocycle L A) (f : L' →* L) (hf)
    (p : ModuleExt (z.comap f hf)) : (mapBase z f hf p).g = f p.g := rfl

end Pullback

end ModuleExt

end ModuleCocycle

/-! ## 3. Intrinsic relator fibres in a module extension -/

section ModuleRelator

variable {X : Type*} {L A : Type} [Group L] [TopologicalSpace L] [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]

/-- The fibre coordinate of an intrinsic relator evaluated at zero-fibre lifts. -/
noncomputable def moduleRel (W : PWord X) (m : X → L) (z : ModuleTwoCocycle L A) : A :=
  (PWord.eval (ModuleExt.lift z m) W).u

/-- The base coordinate of an evaluated lifted relator is its value downstairs. -/
theorem moduleRel_base (W : PWord X) (m : X → L) (z : ModuleTwoCocycle L A) :
    (PWord.eval (ModuleExt.lift z m) W).g = PWord.eval m W := by
  let F : ContinuousMonoidHom (ModuleExt z) L :=
    ⟨ModuleExt.baseProj z, continuous_of_discreteTopology⟩
  have h := PWord.map_eval F (ModuleExt.lift z m) W
  change F (PWord.eval (ModuleExt.lift z m) W) = PWord.eval m W
  rw [h]
  congr 1

/-- When the relation holds downstairs, its lifted value lies in the additive fibre. -/
theorem moduleWord_eval_lift_eq_incl (W : PWord X) (m : X → L)
    (z : ModuleTwoCocycle L A) (hrel : PWord.eval m W = 1) :
    PWord.eval (ModuleExt.lift z m) W = ModuleExt.incl z (moduleRel W m z) := by
  apply ModuleExt.ext
  · rfl
  · rw [moduleRel_base, hrel]
    rfl

/-- **The module-valued shift law.**  Changing the zero-fibre lift of each generator by
`a x` changes every intrinsic relator value by exactly the word differential.  The
`ResolvesAt` hypothesis is target-local: it resolves the reflected relator in the split
word lift `A ⋊ L`, which is precisely the target in which `heisD1` is evaluated.

No triviality of the action and no exponent-sum simplification is used.  The proof applies
the generic correction law to the twisted extension `ModuleExt z`; conjugation in its fibre
is the given `L`-action by `ModuleExt.conj_incl`. -/
theorem moduleWord_eval_shift {rel : Type*} (W : rel → PWord X)
    (w : rel → FreeGroup X) (m : X → L) (z : ModuleTwoCocycle L A)
    (hres : ResolvesAt W w (WordLift A L)) (a : X → A) (k : rel) :
    PWord.eval (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k)
      = ModuleExt.incl z (heisD1 (A := A) m w a k) *
          PWord.eval (ModuleExt.lift z m) (W k) := by
  letI actExt : DistribMulAction (ModuleExt z) A :=
    DistribMulAction.compHom A (ModuleExt.baseProj z)
  apply eval_corrected_heisD1
    (pi := ModuleExt.baseProj z) (j := ModuleExt.incl z)
    (hact := fun _ _ => rfl)
    (hjmul := ModuleExt.incl_add)
    (hjconj := fun p b => ModuleExt.conj_incl p b)
    (hf₀ := fun _ => rfl) hres a k

/-- Fibre-coordinate form of `moduleWord_eval_shift`: the shifted relator fibre is
`heisD1` plus the zero-fibre relator obstruction. -/
theorem moduleRel_shift {rel : Type*} (W : rel → PWord X)
    (w : rel → FreeGroup X) (m : X → L) (z : ModuleTwoCocycle L A)
    (hres : ResolvesAt W w (WordLift A L)) (a : X → A) (k : rel) :
    (PWord.eval (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k)).u
      = heisD1 (A := A) m w a k + moduleRel (W k) m z := by
  have h := congrArg ModuleExt.u (moduleWord_eval_shift W w m z hres a k)
  simpa [moduleRel, z.κ_one_left] using h

/-- A zero-fibre relator in a normalized coboundary extension is the word differential,
up to the value of the splitting cochain on the downstairs relator.  This is the strongest
form of the coboundary computation: it does not yet assume that the relator dies downstairs. -/
theorem moduleRel_coboundary_add_base {rel : Type*} (W : rel → PWord X)
    (w : rel → FreeGroup X) (m : X → L) (lam : L → A) (hlam1 : lam 1 = 0)
    (hres : ResolvesAt W w (WordLift A L)) (k : rel) :
    moduleRel (W k) m (ModuleTwoCocycle.coboundary lam hlam1) +
        lam (PWord.eval m (W k))
      = heisD1 (A := A) m w (fun x => lam (m x)) k := by
  let z := ModuleTwoCocycle.coboundary lam hlam1
  let F : ContinuousMonoidHom (ModuleExt z) (WordLift A L) :=
    ⟨ModuleExt.coboundaryToSplit lam hlam1, continuous_of_discreteTopology⟩
  have hmap := PWord.map_eval F (ModuleExt.lift z m) (W k)
  have hgen : (fun x => F (ModuleExt.lift z m x)) =
      foxLift m (fun x => lam (m x)) := by
    funext x
    exact ModuleExt.coboundaryToSplit_lift lam hlam1 m x
  rw [hgen] at hmap
  have hu := congrArg WordLift.u hmap
  have hbase := moduleRel_base (W k) m z
  have hfibre : moduleRel (W k) m z + lam (PWord.eval m (W k)) =
      (PWord.eval (foxLift m (fun x => lam (m x))) (W k)).u := by
    change (PWord.eval (ModuleExt.lift z m) (W k)).u +
        lam (PWord.eval m (W k)) = _
    rw [← hbase]
    exact hu
  rw [hfibre, heisD1_eq_lift_foxLift_u, hres (foxLift m (fun x => lam (m x))) k]

/-- When the relator holds downstairs, the relator fibre of a normalized coboundary
extension is exactly `heisD1` of the generator values of its splitting cochain. -/
theorem moduleRel_coboundary_eq_heisD1 {rel : Type*} (W : rel → PWord X)
    (w : rel → FreeGroup X) (m : X → L) (lam : L → A) (hlam1 : lam 1 = 0)
    (hres : ResolvesAt W w (WordLift A L)) (hrel : ∀ k, PWord.eval m (W k) = 1)
    (k : rel) :
    moduleRel (W k) m (ModuleTwoCocycle.coboundary lam hlam1) =
      heisD1 (A := A) m w (fun x => lam (m x)) k := by
  have h := moduleRel_coboundary_add_base W w m lam hlam1 hres k
  simpa [hrel k, hlam1] using h

/-- Finite-level `map_coboundary`: the full relator-fibre vector of a coboundary
extension lies in the image of the word differential. -/
theorem moduleRelFam_coboundary_mem_range {rel : Type*} (W : rel → PWord X)
    (w : rel → FreeGroup X) (m : X → L) (lam : L → A) (hlam1 : lam 1 = 0)
    (hres : ResolvesAt W w (WordLift A L)) (hrel : ∀ k, PWord.eval m (W k) = 1) :
    (fun k => moduleRel (W k) m (ModuleTwoCocycle.coboundary lam hlam1)) ∈
      (heisD1 (A := A) m w).range := by
  refine ⟨fun x => lam (m x), ?_⟩
  funext k
  exact (moduleRel_coboundary_eq_heisD1 W w m lam hlam1 hres hrel k).symm

section Pullback

variable {L' : Type} [Group L'] [TopologicalSpace L'] [DiscreteTopology L'] [Finite L']
  [DistribMulAction L' A]

omit [TopologicalSpace L] [DiscreteTopology L] [TopologicalSpace L'] [DiscreteTopology L'] in
/-- Relator fibres are natural under a compatible change of finite base level. -/
theorem moduleRel_comap (W : PWord X) (m : X → L') (z : ModuleTwoCocycle L A)
    (f : L' →* L) (hf : ∀ (g : L') (a : A), g • a = f g • a) :
    moduleRel W (fun x => f (m x)) z = moduleRel W m (z.comap f hf) := by
  let F : ContinuousMonoidHom (ModuleExt (z.comap f hf)) (ModuleExt z) :=
    ⟨ModuleExt.mapBase z f hf, continuous_of_discreteTopology⟩
  have h := PWord.map_eval F (ModuleExt.lift (z.comap f hf) m) W
  have hgen : (fun x => F (ModuleExt.lift (z.comap f hf) m x)) =
      ModuleExt.lift z (fun x => f (m x)) := by
    funext x
    rfl
  have hu := congrArg ModuleExt.u h
  change (PWord.eval (ModuleExt.lift (z.comap f hf) m) W).u
      = (PWord.eval (fun x => F (ModuleExt.lift (z.comap f hf) m x)) W).u at hu
  rw [hgen] at hu
  show (PWord.eval (ModuleExt.lift z (fun x => f (m x))) W).u
      = (PWord.eval (ModuleExt.lift (z.comap f hf) m) W).u
  exact hu.symm

end Pullback

end ModuleRelator

/-! ## 4. Correct normalization for nontrivial coefficients -/

section Normalize

variable {G A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
  [DistribMulAction G A] [ContinuousSMul G A]

/-- Normalize a module-valued cochain.  For a nontrivial action the correction is
`g • φ(1,1)`, not the constant `φ(1,1)` used by the scalar construction. -/
def moduleNormalize (f : G × G → A) : G × G → A :=
  fun p => f p - p.1 • f (1, 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] in
theorem moduleNormalize_one (f : G × G → A) : moduleNormalize f (1, 1) = 0 := by
  simp [moduleNormalize]

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] in
theorem moduleNormalize_add (f f' : G × G → A) :
    moduleNormalize (f + f') = moduleNormalize f + moduleNormalize f' := by
  funext p
  simp only [moduleNormalize, Pi.add_apply, smul_add]
  abel

omit [IsTopologicalGroup G] in
theorem continuous_moduleNormalize {f : G × G → A} (hf : Continuous f) :
    Continuous (moduleNormalize f) := by
  exact hf.sub ((continuous_fst.smul continuous_const))

omit [TopologicalSpace G] [IsTopologicalGroup G] [TopologicalSpace A]
  [IsTopologicalAddGroup A] [ContinuousSMul G A] in
/-- Normalization preserves the inhomogeneous cocycle identity. -/
theorem moduleNormalize_cocyc {f : G × G → A}
    (hf : ∀ g h k : G, g • f (h, k) + f (g, h * k) = f (g * h, k) + f (g, h)) :
    ∀ g h k : G,
      g • moduleNormalize f (h, k) + moduleNormalize f (g, h * k)
        = moduleNormalize f (g * h, k) + moduleNormalize f (g, h) := by
  intro g h k
  simp only [moduleNormalize, smul_sub, mul_smul]
  have hcoc := hf g h k
  calc
    _ = (g • f (h, k) + f (g, h * k))
          - g • h • f (1, 1) - g • f (1, 1) := by abel
    _ = (f (g * h, k) + f (g, h))
          - g • h • f (1, 1) - g • f (1, 1) := by rw [hcoc]
    _ = _ := by abel

omit [IsTopologicalGroup G] [ContinuousSMul G A] in
/-- The normalization correction is the coboundary of the constant cochain. -/
theorem sub_moduleNormalize_mem_B2 (f : G × G → A) :
    f - moduleNormalize f ∈ B2 G A := by
  rw [B2, AddSubgroup.mem_map]
  refine ⟨fun _ => f (1, 1), continuous_const, ?_⟩
  funext p
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, moduleNormalize, Pi.sub_apply]
  abel

/-- A continuous cocycle gives a normalized module cocycle on the same group. -/
noncomputable def moduleTwoCocycleOfZ2 (f : Z2 G A) : ModuleTwoCocycle G A where
  κ g h := moduleNormalize f.1 (g, h)
  norm := moduleNormalize_one f.1
  cocyc := moduleNormalize_cocyc (mem_Z2_iff.mp f.2).2

omit [IsTopologicalGroup G] [ContinuousSMul G A] in
@[simp] theorem moduleTwoCocycleOfZ2_κ (f : Z2 G A) (g h : G) :
    (moduleTwoCocycleOfZ2 f).κ g h = moduleNormalize f.1 (g, h) := rfl

end Normalize

/-! ## 5. Finite-level factorization compatible with the module action -/

section Factoring

variable {G C A : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [DiscreteTopology A]
  [DistribMulAction G A] [ContinuousSMul G A] [DistribMulAction C A]

/-- The action kernel as an open normal subgroup. -/
def moduleActionKerON (rho : ContinuousMonoidHom G C) : OpenNormalSubgroup G where
  toSubgroup := rho.toMonoidHom.ker
  isOpen' := by
    have hset : (rho.toMonoidHom.ker : Subgroup G).carrier = rho ⁻¹' {1} := by
      ext g
      simp
    rw [hset]
    exact (isOpen_discrete ({1} : Set C)).preimage rho.continuous_toFun

/-- The lower action map descended to a quotient contained in its kernel. -/
def quotientActionHom (rho : ContinuousMonoidHom G C) (V : OpenNormalSubgroup G)
    (hV : V.toSubgroup ≤ rho.toMonoidHom.ker) : (G ⧸ V.toSubgroup) →* C :=
  QuotientGroup.lift V.toSubgroup rho.toMonoidHom hV

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DiscreteTopology C] [Finite C] in
@[simp] theorem quotientActionHom_mk (rho : ContinuousMonoidHom G C)
    (V : OpenNormalSubgroup G) (hV : V.toSubgroup ≤ rho.toMonoidHom.ker) (g : G) :
    quotientActionHom rho V hV (QuotientGroup.mk' V.toSubgroup g) = rho g :=
  QuotientGroup.lift_mk' _ _ _

omit [Finite C] in
/-- **Action-compatible finite factorization.**  A continuous module-valued cocycle factors
through a finite quotient which lies inside the kernel of the lower action map.  Consequently the
quotient inherits the required action on `A`, and the factored cocycle is an honest
`ModuleTwoCocycle` for that action.

This is the coefficient-generic replacement for `WordCoh.nonempty_levelFactor_normalize`. -/
theorem exists_moduleTwoCocycle_factor (rho : ContinuousMonoidHom G C)
    (hcompat : ∀ (g : G) (a : A), g • a = rho g • a) (f : Z2 G A) :
    ∃ V : OpenNormalSubgroup G, ∃ hV : V.toSubgroup ≤ rho.toMonoidHom.ker,
      let rhoV := quotientActionHom rho V hV
      letI : DistribMulAction (G ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
      ∃ z : ModuleTwoCocycle (G ⧸ V.toSubgroup) A, ∀ x y : G,
        moduleNormalize f.1 (x, y) =
          z.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y) := by
  set fN : G × G → A := moduleNormalize f.1 with hfN
  have hfNc : Continuous fN := by
    rw [hfN]
    exact continuous_moduleNormalize (mem_Z2_iff.mp f.2).1
  obtain ⟨U, hU⟩ := GQ2.Dyadic.WordCoh.exists_openNormalSubgroup_factor_two fN hfNc
  set K : OpenNormalSubgroup G := moduleActionKerON rho with hK
  set V : OpenNormalSubgroup G := U ⊓ K with hVdef
  have hVU : V.toSubgroup ≤ U.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have hVK : V.toSubgroup ≤ rho.toMonoidHom.ker := by
    intro x hx
    have hxK : x ∈ K.toSubgroup := SetLike.le_def.mp inf_le_right hx
    exact hxK
  refine ⟨V, hVK, ?_⟩
  dsimp only
  let rhoV : (G ⧸ V.toSubgroup) →* C := quotientActionHom rho V hVK
  letI : DistribMulAction (G ⧸ V.toSubgroup) A := DistribMulAction.compHom A rhoV
  refine ⟨{
    κ := fun p q => Quotient.liftOn₂ p q (fun x y => fN (x, y)) ?_
    norm := ?_
    cocyc := ?_ }, ?_⟩
  · intro x₁ y₁ x₂ y₂ hx hy
    have hxv : x₁⁻¹ * x₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hx
    have hyv : y₁⁻¹ * y₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hy
    have hu := hU x₁ y₁ _ (hVU hxv) _ (hVU hyv)
    rw [mul_inv_cancel_left, mul_inv_cancel_left] at hu
    exact hu.symm
  · show fN (1, 1) = 0
    rw [hfN]
    exact moduleNormalize_one f.1
  · intro a b d
    induction a using QuotientGroup.induction_on with
    | H x =>
      induction b using QuotientGroup.induction_on with
      | H y =>
        induction d using QuotientGroup.induction_on with
        | H t =>
          change rhoV (QuotientGroup.mk' V.toSubgroup x) • fN (y, t) + fN (x, y * t)
              = fN (x * y, t) + fN (x, y)
          rw [show rhoV (QuotientGroup.mk' V.toSubgroup x) = rho x from
            quotientActionHom_mk rho V hVK x]
          rw [← hcompat]
          rw [hfN]
          exact moduleNormalize_cocyc (mem_Z2_iff.mp f.2).2 x y t
  · intro x y
    rfl

end Factoring

/-! ## 6. Exact assembly interface for the coefficient-generic rung -/

section Assembly

variable {iota rel : Type*} [Fintype iota] [Fintype rel] [DecidableEq iota]
  {Gamma A C : Type*} [Group Gamma] [TopologicalSpace Gamma] [IsTopologicalGroup Gamma]
  [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [Finite A]
  [DistribMulAction Gamma A] [ContinuousSMul Gamma A]
  [Group C] [DistribMulAction C A]
  (gen : iota → Gamma) (c : iota → C) (w : rel → FreeGroup iota)

/-- The exact output required from the semidirect obstruction construction.

`obstruction` is the relator fibre vector.  The first law is precisely what is
needed for descent through `B²`; the second is precisely what is needed for
injectivity.  Neither law asserts surjectivity onto the word cokernel. -/
structure ModuleH2WordData where
  /-- The additive relator obstruction on continuous `2`-cocycles. -/
  obstruction : Z2 Gamma A →+ (rel → A)
  /-- Coboundaries have word-coboundary obstruction. -/
  map_coboundary : ∀ f : Z2 Gamma A, f.1 ∈ B2 Gamma A →
    obstruction f ∈ (heisD1 (A := A) c w).range
  /-- Conversely, a word-coboundary obstruction splits the extension. -/
  reflects_coboundary : ∀ f : Z2 Gamma A,
    obstruction f ∈ (heisD1 (A := A) c w).range → f.1 ∈ B2 Gamma A

variable {gen c w}

/-- The obstruction before descent, read in the word cokernel. -/
noncomputable def moduleWordH2Obs
    (D : ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w) :
    Z2 Gamma A →+ WordH2 c w A :=
  (QuotientAddGroup.mk' (heisD1 (A := A) c w).range).comp D.obstruction

/-- The coefficient-generic `H² → WordH²` map assembled from semidirect obstruction data. -/
noncomputable def moduleH2Word
    (D : ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w) :
    H2 Gamma A →+ WordH2 c w A :=
  QuotientAddGroup.lift _ (moduleWordH2Obs D) fun _ hf =>
    (QuotientAddGroup.eq_zero_iff _).mpr
      (D.map_coboundary _ (AddSubgroup.mem_addSubgroupOf.mp hf))

omit [Fintype iota] [Fintype rel] [DecidableEq iota] [IsTopologicalGroup Gamma]
  [Finite A] [ContinuousSMul Gamma A] in
@[simp] theorem moduleH2Word_mk
    (D : ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w) (f : Z2 Gamma A) :
    moduleH2Word D (H2mk Gamma A f) = moduleWordH2Obs D f := rfl

omit [Fintype iota] [Fintype rel] [DecidableEq iota] [IsTopologicalGroup Gamma]
  [Finite A] [ContinuousSMul Gamma A] in
/-- The coefficient-generic rung is injective.  This proves exactly an injection;
no identities-among-relators/asphericity hypothesis is smuggled into the result. -/
theorem moduleH2Word_injective
    (D : ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w) :
    Function.Injective (moduleH2Word D) := by
  rw [injective_iff_map_eq_zero]
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H f =>
      intro hy
      refine (QuotientAddGroup.eq_zero_iff f).mpr (AddSubgroup.mem_addSubgroupOf.mpr ?_)
      apply D.reflects_coboundary f
      exact (QuotientAddGroup.eq_zero_iff _).mp hy

omit [Fintype iota] [DecidableEq iota] [IsTopologicalGroup Gamma]
  [ContinuousSMul Gamma A] in
/-- The cardinal inequality supplied by the module-coefficient rung. -/
theorem card_H2_le_card_moduleWordH2
    (D : ModuleH2WordData (Gamma := Gamma) (A := A) (C := C) c w) :
    Nat.card (H2 Gamma A) ≤ Nat.card (WordH2 c w A) :=
  Nat.card_le_card_of_injective _ (moduleH2Word_injective D)

end Assembly

end GQ2.Dyadic.Count
