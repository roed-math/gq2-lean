/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.HTwoModuleSurjectivity

/-!
# Relation-module characters and finite relator realization

This file isolates a genuinely classical relation-module input behind the remaining
degree-two surjectivity theorem.  For a generating marking `m : X → L`, put

`F = FreeGroup X`, `R = ker (FreeGroup.lift m)`.

A `FreeRelationCharacter m A` is a homomorphism `R → A` which is equivariant for
conjugation by `F` and the induced `L`-action.  Equivalently, it is a homomorphism from the
relation module `R / [R,R]` to `A`; when `A` has exponent two it factors through the mod-2
relation module `R / (R² [R,R])`.  No cocycle, continuous cohomology group, or word cokernel
occurs in the definition.

The main construction is the elementary transgression attached to a normalized Schreier
section of `F → L`.  It turns a relation character into a normalized module 2-cocycle and a
homomorphism `F → A ⋊_κ L`.  Consequently, if relation characters can be prescribed on the
defining relators, every relator vector is realized modulo the Fox differential.

This is the missing bridge needed to make a future Labute/mildness or relation-module-basis
theorem feed the existing continuous-to-word comparison API.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic

noncomputable section

/-! ## Uniform order bounds for transgressed extensions -/

namespace ModuleExt

variable {L A : Type} [Group L] [AddCommGroup A] [DistribMulAction L A]

/-- Over an elementary coefficient group, the order of an element of a twisted module
extension divides twice the order of its base coordinate.  This is the nonsplit analogue of
`WordLift.orderOf_dvd_two_mul_orderOf_base`: after raising to the base order, the element lies
in the fibre, and its square vanishes.  The argument uses only normalization of the module
cocycle, so it applies in particular to cocycles transgressed from relation characters. -/
theorem orderOf_dvd_two_mul_orderOf_base
    (z : ModuleTwoCocycle L A) (hA₂ : ∀ a : A, a + a = 0) (p : ModuleExt z) :
    orderOf p ∣ 2 * orderOf p.g := by
  refine orderOf_dvd_of_pow_eq_one ?_
  have hg : (p ^ orderOf p.g).g = 1 := by
    change baseProj z (p ^ orderOf p.g) = 1
    rw [map_pow]
    change p.g ^ orderOf p.g = 1
    exact pow_orderOf_eq_one _
  have hsq : (p ^ orderOf p.g) * (p ^ orderOf p.g) = 1 := by
    apply ModuleExt.ext
    · simp only [mul_u, hg, one_smul, z.norm, add_zero, one_u]
      exact hA₂ _
    · simp [mul_g, hg]
  calc
    p ^ (2 * orderOf p.g) =
        (p ^ orderOf p.g) * (p ^ orderOf p.g) := by
      rw [two_mul, pow_add]
    _ = 1 := hsq

/-- Uniform form of `orderOf_dvd_two_mul_orderOf_base`: if `N` kills all base element
orders, then `2 * N` kills every element of every normalized twisted module extension. -/
theorem orderOf_dvd_two_mul
    (z : ModuleTwoCocycle L A) (hA₂ : ∀ a : A, a + a = 0) {N : ℕ}
    (hbase : ∀ g : L, orderOf g ∣ N) (p : ModuleExt z) :
    orderOf p ∣ 2 * N :=
  (orderOf_dvd_two_mul_orderOf_base z hA₂ p).trans
    (mul_dvd_mul_left 2 (hbase p.g))

end ModuleExt

section RelationCharacter

variable {X L A : Type} [Group L] [AddCommGroup A] [DistribMulAction L A]

/-- The kernel of the evaluation map from the abstract free group at a marking. -/
abbrev FreeRelationKernel (m : X → L) : Type :=
  ↥(FreeGroup.lift m).ker

/-- Conjugation by a free word preserves the relation kernel. -/
def relationKernelConj (m : X → L) (f : FreeGroup X)
    (r : FreeRelationKernel m) : FreeRelationKernel m :=
  ⟨f * r.1 * f⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, r.property]
    group⟩

/-- A relation-module character.  The multiplicative wrapper lets the underlying map be
stated as an ordinary group homomorphism; `toAdd` recovers its additive value.  For
exponent-two coefficients this is a character of the mod-2 relation module. -/
structure FreeRelationCharacter (m : X → L) (A : Type) [AddCommGroup A]
    [DistribMulAction L A] where
  toMonoidHom : FreeRelationKernel m →* Multiplicative A
  conjugation : ∀ (f : FreeGroup X) (r : FreeRelationKernel m),
    toMonoidHom (relationKernelConj m f r) =
      Multiplicative.ofAdd
        (FreeGroup.lift m f • Multiplicative.toAdd (toMonoidHom r))

namespace FreeRelationCharacter

variable {m : X → L} (chi : FreeRelationCharacter m A)

/-- Additive value of a relation character. -/
def val (r : FreeRelationKernel m) : A :=
  Multiplicative.toAdd (chi.toMonoidHom r)

@[simp] theorem ofAdd_val (r : FreeRelationKernel m) :
    Multiplicative.ofAdd (chi.val r) = chi.toMonoidHom r := by
  exact ofAdd_toAdd _

@[simp] theorem val_one : chi.val 1 = 0 := by
  apply Multiplicative.ofAdd.injective
  simp

theorem val_mul (r s : FreeRelationKernel m) :
    chi.val (r * s) = chi.val r + chi.val s := by
  apply Multiplicative.ofAdd.injective
  simp [ofAdd_val]

theorem val_conjugation (f : FreeGroup X) (r : FreeRelationKernel m) :
    chi.val (relationKernelConj m f r) = FreeGroup.lift m f • chi.val r := by
  have h := congrArg Multiplicative.toAdd (chi.conjugation f r)
  simpa [val] using h

end FreeRelationCharacter

end RelationCharacter

section SchreierTransgression

variable {X L A : Type} [Group L] [AddCommGroup A] [DistribMulAction L A]
  {m : X → L}

local notation "F" => FreeGroup X
local notation "ev" => FreeGroup.lift m

/-- A normalized set-theoretic section of a surjective free-group evaluation map. -/
def relationSection (heval : Function.Surjective ev) (g : L) : F :=
  by
    classical
    exact if g = 1 then 1 else Function.surjInv heval g

@[simp] theorem relationSection_one (heval : Function.Surjective ev) :
    relationSection heval 1 = 1 := by
  simp [relationSection]

theorem relationSection_spec (heval : Function.Surjective ev) (g : L) :
    ev (relationSection heval g) = g := by
  classical
  by_cases hg : g = 1
  · simp [relationSection, hg]
  · simp [relationSection, hg, Function.surjInv_eq heval g]

/-- The Schreier factor of a normalized section, as an element of the relation kernel. -/
def relationDefect (heval : Function.Surjective ev) (g h : L) :
    FreeRelationKernel m :=
  ⟨relationSection heval g * relationSection heval h *
      (relationSection heval (g * h))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv,
      relationSection_spec, relationSection_spec, relationSection_spec]
    group⟩

/-- The kernel component of a free word relative to the normalized section. -/
def relationKernelPart (heval : Function.Surjective ev) (f : F) :
    FreeRelationKernel m :=
  ⟨f * (relationSection heval (ev f))⁻¹, by
    rw [MonoidHom.mem_ker, map_mul, map_inv, relationSection_spec]
    group⟩

@[simp] theorem relationKernelPart_one (heval : Function.Surjective ev) :
    relationKernelPart heval 1 = 1 := by
  apply Subtype.ext
  simp [relationKernelPart]

/-- The factor-set identity for a normalized Schreier section. -/
theorem relationDefect_cocycle (heval : Function.Surjective ev) (g h k : L) :
    relationKernelConj m (relationSection heval g) (relationDefect heval h k) *
        relationDefect heval g (h * k) =
      relationDefect heval g h * relationDefect heval (g * h) k := by
  apply Subtype.ext
  simp only [relationKernelConj, relationDefect, Subgroup.coe_mul]
  group

/-- Decomposition of the kernel component of a product. -/
theorem relationKernelPart_mul (heval : Function.Surjective ev) (f g : F) :
    relationKernelPart heval (f * g) =
      relationKernelPart heval f *
        relationKernelConj m (relationSection heval (ev f))
          (relationKernelPart heval g) *
        relationDefect heval (ev f) (ev g) := by
  apply Subtype.ext
  simp only [relationKernelPart, relationKernelConj, relationDefect, map_mul,
    Subgroup.coe_mul]
  group

/-- The normalized cocycle transgressed from a relation-module character. -/
def relationCharacterCocycle (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) : ModuleTwoCocycle L A where
  κ g h := chi.val (relationDefect heval g h)
  norm := by
    have hdef : relationDefect heval 1 1 = 1 := by
      apply Subtype.ext
      simp [relationDefect]
    rw [hdef, FreeRelationCharacter.val_one]
  cocyc := by
    intro g h k
    have hconj := chi.val_conjugation (relationSection heval g)
      (relationDefect heval h k)
    rw [relationSection_spec] at hconj
    calc
      g • chi.val (relationDefect heval h k) +
            chi.val (relationDefect heval g (h * k)) =
          chi.val (relationKernelConj m (relationSection heval g)
              (relationDefect heval h k)) +
            chi.val (relationDefect heval g (h * k)) := by rw [hconj]
      _ = chi.val (relationKernelConj m (relationSection heval g)
              (relationDefect heval h k) * relationDefect heval g (h * k)) :=
            (chi.val_mul _ _).symm
      _ = chi.val (relationDefect heval g h * relationDefect heval (g * h) k) :=
            congrArg chi.val (relationDefect_cocycle heval g h k)
      _ = chi.val (relationDefect heval g h) +
            chi.val (relationDefect heval (g * h) k) := chi.val_mul _ _
      _ = chi.val (relationDefect heval (g * h) k) +
            chi.val (relationDefect heval g h) := add_comm _ _

@[simp] theorem relationCharacterCocycle_apply
    (heval : Function.Surjective ev) (chi : FreeRelationCharacter m A) (g h : L) :
    (relationCharacterCocycle heval chi).κ g h =
      chi.val (relationDefect heval g h) := rfl

/-- Fibre coordinate of the canonical lift of a free word. -/
def relationLiftCoord (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) (f : F) : A :=
  chi.val (relationKernelPart heval f)

@[simp] theorem relationLiftCoord_one (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) : relationLiftCoord heval chi 1 = 0 := by
  simp [relationLiftCoord]

/-- The homomorphism from the free group into the extension defined by transgression. -/
def relationLift (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) :
    F →* ModuleExt (relationCharacterCocycle heval chi) where
  toFun f := ⟨relationLiftCoord heval chi f, ev f⟩
  map_one' := by
    apply ModuleExt.ext
    · exact relationLiftCoord_one heval chi
    · exact map_one ev
  map_mul' f g := by
    apply ModuleExt.ext
    · change relationLiftCoord heval chi (f * g) =
        relationLiftCoord heval chi f + ev f • relationLiftCoord heval chi g +
          chi.val (relationDefect heval (ev f) (ev g))
      rw [relationLiftCoord, relationKernelPart_mul, chi.val_mul, chi.val_mul,
        chi.val_conjugation, relationSection_spec]
      rfl
    · exact map_mul ev f g

@[simp] theorem relationLift_u (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) (f : F) :
    (relationLift heval chi f).u = relationLiftCoord heval chi f := rfl

@[simp] theorem relationLift_g (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) (f : F) :
    (relationLift heval chi f).g = ev f := rfl

/-- On each free generator, the canonical lift is a fibre shift of the zero-fibre lift. -/
theorem relationLift_of (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) (x : X) :
    relationLift heval chi (FreeGroup.of x) =
      ModuleExt.incl (relationCharacterCocycle heval chi)
          (relationLiftCoord heval chi (FreeGroup.of x)) *
        ModuleExt.lift (relationCharacterCocycle heval chi) m x := by
  apply ModuleExt.ext
  · simp only [ModuleExt.mul_u, ModuleExt.incl_u, ModuleExt.incl_g,
      ModuleExt.lift_u, ModuleExt.lift_g, one_smul, add_zero]
    rw [(relationCharacterCocycle heval chi).κ_one_left]
    exact (add_zero _).symm
  · simp

/-- A relation word has precisely its relation-character value under the canonical lift. -/
theorem relationLift_relation (heval : Function.Surjective ev)
    (chi : FreeRelationCharacter m A) (w : F) (hw : ev w = 1) :
    relationLift heval chi w =
      ModuleExt.incl (relationCharacterCocycle heval chi)
        (chi.val ⟨w, MonoidHom.mem_ker.mpr hw⟩) := by
  apply ModuleExt.ext
  · change chi.val (relationKernelPart heval w) = chi.val ⟨w, _⟩
    congr 1
    apply Subtype.ext
    simp [relationKernelPart, hw]
  · exact hw

end SchreierTransgression

section RelatorEvaluation

variable {X rel L A : Type} [Group L] [TopologicalSpace L]
  [DiscreteTopology L] [Finite L]
  [AddCommGroup A] [DistribMulAction L A] [Finite A]
  {m : X → L}

/-- A relation character takes prescribed values on a resolved relator family. -/
def RelationCharacterRealizes (w : rel → FreeGroup X)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (r : rel → A) (chi : FreeRelationCharacter m A) : Prop :=
  ∀ k, chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩ = r k

/-- The classical relation-module evaluation condition: every requested vector on the defining
relators extends to an equivariant character of the full relation kernel. -/
def RelationModuleRelatorSurjective (w : rel → FreeGroup X)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1) : Prop :=
  ∀ r : rel → A, ∃ chi : FreeRelationCharacter m A,
    RelationCharacterRealizes w hrel r chi

omit [TopologicalSpace L] [DiscreteTopology L] [Finite L] in
/-- A finite marking which generates algebraically is the image of the abstract free group. -/
theorem freeGroup_lift_surjective_of_closure
    (hgen : Subgroup.closure (Set.range m) = ⊤) :
    Function.Surjective (FreeGroup.lift m) := by
  rw [← MonoidHom.range_eq_top]
  refine le_antisymm (le_top) ?_
  rw [← hgen, Subgroup.closure_le]
  rintro _ ⟨x, rfl⟩
  exact ⟨FreeGroup.of x, by simp⟩

/-- Relation-module evaluation surjectivity gives finite cocycle relator realization. -/
theorem relatorRealization_of_relationModule
    (W : rel → PWord X) (w : rel → FreeGroup X)
    (hres : ResolvesAt W w (WordLift A L))
    (hgen : Subgroup.closure (Set.range m) = ⊤)
    (hrel : ∀ k, FreeGroup.lift m (w k) = 1)
    (hRM : RelationModuleRelatorSurjective (A := A) w hrel)
    (hresExt : ∀ chi : FreeRelationCharacter m A,
      ResolvesAt W w (ModuleExt (relationCharacterCocycle
        (freeGroup_lift_surjective_of_closure hgen) chi))) :
    ∀ r : rel → A, ∃ z : ModuleTwoCocycle L A,
      (fun k => moduleRel (W k) m z) - r ∈
        (heisD1 (A := A) m w).range := by
  intro r
  obtain ⟨chi, hchi⟩ := hRM r
  let heval : Function.Surjective (FreeGroup.lift m) :=
    freeGroup_lift_surjective_of_closure hgen
  let z := relationCharacterCocycle heval chi
  let a : X → A := fun x => relationLiftCoord heval chi (FreeGroup.of x)
  refine ⟨z, ⟨-a, ?_⟩⟩
  funext k
  have hliftHom : FreeGroup.lift
      (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) =
      relationLift heval chi := by
    apply FreeGroup.ext_hom
    intro x
    rw [FreeGroup.lift_apply_of]
    exact (relationLift_of heval chi x).symm
  have hword : PWord.eval
      (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k) =
      ModuleExt.incl z (r k) := by
    calc
      PWord.eval (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (W k) =
          FreeGroup.lift
            (fun x => ModuleExt.incl z (a x) * ModuleExt.lift z m x) (w k) :=
        (hresExt chi _ k).symm
      _ = relationLift heval chi (w k) := congrArg (fun f => f (w k)) hliftHom
      _ = ModuleExt.incl z
          (chi.val ⟨w k, MonoidHom.mem_ker.mpr (hrel k)⟩) :=
        relationLift_relation heval chi (w k) (hrel k)
      _ = ModuleExt.incl z (r k) := congrArg (ModuleExt.incl z) (hchi k)
  have hshift := moduleRel_shift W w m z hres a k
  rw [hword] at hshift
  simp only [Pi.sub_apply]
  rw [map_neg]
  have hz : heisD1 (A := A) m w a k + moduleRel (W k) m z = r k := by
    simpa using hshift.symm
  exact neg_eq_of_add_eq_zero_right (by rw [add_sub, hz, sub_self])

end RelatorEvaluation

end

end GQ2.Dyadic.Count
