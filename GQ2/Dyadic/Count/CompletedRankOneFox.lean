/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedModTwoFoxBoundary

/-!
# Rank-one coordinates for the completed mod-two Fox boundary

The completed regular module on one generator is canonically the completed group algebra.
This file constructs that equivalence, exposes arbitrary completed regular modules one basis
coordinate at a time, and rewrites the improved square Fox boundary as multiplication by its
completed Fox-derivative row.

Consequently injectivity of the completed boundary is *equivalent* to triviality of the common
left annihilator of that row.  No annihilator theorem is assumed here; proving it for the actual
improved relator remains the classical one-relator input.
-/

namespace GQ2.ContCoh

noncomputable section

open GQ2.Dyadic.Count GQ2.Dyadic.SqCore

/-! ## The finite rank-one equivalence -/

/-- Forget the unique basis label in a rank-one regular module. -/
def prodUnitEquiv (Q : Type) : Q × Unit ≃ Q where
  toFun p := p.1
  invFun q := (q, ())
  left_inv p := by rcases p with ⟨q, ⟨⟩⟩; rfl
  right_inv _ := rfl

/-- `F₂[Q]^(Unit)` is canonically the group algebra `F₂[Q]`. -/
def regularUnitFinsuppEquiv (Q : Type) :
    (Q × Unit →₀ ZMod 2) ≃ₗ[ZMod 2] (Q →₀ ZMod 2) :=
  Finsupp.domLCongr (prodUnitEquiv Q)

/-- `F₂[Q]^(Unit)` is canonically the group algebra `F₂[Q]`. -/
def regularUnitGroupAlgebraEquiv (Q : Type) [Group Q] :
    RegularModTwoRelationModule Q Unit ≃ₗ[ZMod 2] MonoidAlgebra (ZMod 2) Q where
  toFun c := MonoidAlgebra.ofCoeff (regularUnitFinsuppEquiv Q c)
  invFun a := (regularUnitFinsuppEquiv Q).symm (MonoidAlgebra.coeff a)
  left_inv c := by
    change (regularUnitFinsuppEquiv Q).symm (regularUnitFinsuppEquiv Q c) = c
    exact (regularUnitFinsuppEquiv Q).symm_apply_apply c
  right_inv a := by
    apply MonoidAlgebra.coeff_injective
    change regularUnitFinsuppEquiv Q
        ((regularUnitFinsuppEquiv Q).symm (MonoidAlgebra.coeff a)) =
      MonoidAlgebra.coeff a
    exact (regularUnitFinsuppEquiv Q).apply_symm_apply _
  map_add' x y := by
    apply MonoidAlgebra.coeff_injective
    change regularUnitFinsuppEquiv Q (x + y) =
      regularUnitFinsuppEquiv Q x + regularUnitFinsuppEquiv Q y
    exact map_add _ _ _
  map_smul' a x := by
    apply MonoidAlgebra.coeff_injective
    change regularUnitFinsuppEquiv Q (a • x) =
      a • regularUnitFinsuppEquiv Q x
    exact map_smul _ _ _

@[simp]
theorem regularUnitGroupAlgebraEquiv_single
    (Q : Type) [Group Q] (q : Q) (a : ZMod 2) :
    regularUnitGroupAlgebraEquiv Q (Finsupp.single (q, ()) a) =
      MonoidAlgebra.single q a := by
  apply MonoidAlgebra.coeff_injective
  change regularUnitFinsuppEquiv Q (Finsupp.single (q, ()) a) =
    Finsupp.single q a
  rw [regularUnitFinsuppEquiv, Finsupp.domLCongr_single]
  rfl

@[simp]
theorem regularUnitGroupAlgebraEquiv_symm_single
    (Q : Type) [Group Q] (q : Q) (a : ZMod 2) :
    (regularUnitGroupAlgebraEquiv Q).symm (MonoidAlgebra.single q a) =
      Finsupp.single (q, ()) a := by
  apply (regularUnitGroupAlgebraEquiv Q).injective
  simp

@[simp]
theorem regularUnitGroupAlgebraEquiv_apply
    (Q : Type) [Group Q] (c : RegularModTwoRelationModule Q Unit) (q : Q) :
    regularUnitGroupAlgebraEquiv Q c q = c (q, ()) :=
  rfl

variable (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- Rank-one identification commutes with the transition maps in the two inverse systems. -/
theorem regularUnitGroupAlgebraEquiv_transition
    {U V : OpenNormalSubgroup G} (h : U ≤ V)
    (c : ModTwoRegularModuleLevel G U Unit) :
    regularUnitGroupAlgebraEquiv (G ⧸ V.toSubgroup)
        (modTwoRegularModuleTransition G h Unit c) =
      modTwoGroupAlgebraTransition G h
        (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup) c) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, ⟨⟩⟩
      simp [ih]

/-! ## The completed rank-one equivalence -/

/-- Map a completed rank-one regular module to the completed group algebra coordinatewise. -/
def completedRegularUnitToGroupAlgebra :
    ModTwoCompletedRegularModule G Unit →ₗ[ZMod 2] ModTwoCompletedGroupAlgebra G where
  toFun c :=
    ⟨fun U => regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U c), by
      intro U V h
      rw [← regularUnitGroupAlgebraEquiv_transition G h]
      exact congrArg (regularUnitGroupAlgebraEquiv (G ⧸ V.toSubgroup))
        (ModTwoCompletedRegularModule.coordinate_compatible G Unit c h)⟩
  map_add' x y := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    change regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U (x + y)) =
      regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
          (ModTwoCompletedRegularModule.coordinate G Unit U x) +
        regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
          (ModTwoCompletedRegularModule.coordinate G Unit U y)
    rw [map_add, map_add]
  map_smul' a x := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    change regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U (a • x)) =
      a • regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U x)
    rw [map_smul, map_smul]

/-- Map the completed group algebra back to the completed rank-one regular module. -/
def completedGroupAlgebraToRegularUnit :
    ModTwoCompletedGroupAlgebra G →ₗ[ZMod 2] ModTwoCompletedRegularModule G Unit where
  toFun a :=
    ⟨fun U => (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
        (ModTwoCompletedGroupAlgebra.coordinate G U a), by
      intro U V h
      apply (regularUnitGroupAlgebraEquiv (G ⧸ V.toSubgroup)).injective
      rw [regularUnitGroupAlgebraEquiv_transition G h]
      simp only [LinearEquiv.apply_symm_apply]
      exact ModTwoCompletedGroupAlgebra.coordinate_compatible G a h⟩
  map_add' x y := by
    apply ModTwoCompletedRegularModule.ext G Unit
    intro U
    change (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
        (ModTwoCompletedGroupAlgebra.coordinate G U (x + y)) =
      (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
          (ModTwoCompletedGroupAlgebra.coordinate G U x) +
        (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
          (ModTwoCompletedGroupAlgebra.coordinate G U y)
    rw [map_add, map_add]
  map_smul' a x := by
    apply ModTwoCompletedRegularModule.ext G Unit
    intro U
    change (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
        (ModTwoCompletedGroupAlgebra.coordinate G U (a • x)) =
      a • (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm
        (ModTwoCompletedGroupAlgebra.coordinate G U x)
    rw [map_smul, map_smul]

/-- The canonical completed linear equivalence `F₂[[G]]^(Unit) ≃ F₂[[G]]`. -/
def completedRegularUnitGroupAlgebraEquiv :
    ModTwoCompletedRegularModule G Unit ≃ₗ[ZMod 2] ModTwoCompletedGroupAlgebra G where
  toLinearMap := completedRegularUnitToGroupAlgebra G
  invFun := completedGroupAlgebraToRegularUnit G
  left_inv c := by
    apply ModTwoCompletedRegularModule.ext G Unit
    intro U
    exact (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).symm_apply_apply _
  right_inv a := by
    apply ModTwoCompletedGroupAlgebra.ext G
    intro U
    exact (regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)).apply_symm_apply _

@[simp]
theorem completedRegularUnitGroupAlgebraEquiv_coordinate
    (U : OpenNormalSubgroup G) (c : ModTwoCompletedRegularModule G Unit) :
    ModTwoCompletedGroupAlgebra.coordinate G U
        (completedRegularUnitGroupAlgebraEquiv G c) =
      regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U c) :=
  rfl

/-! ## Basis components -/

variable {Q J : Type} [Group Q]

local instance instDecidableEqJ : DecidableEq J := Classical.decEq J

/-- Extract one basis component of a finite regular module as a group-algebra element. -/
def regularModTwoComponent (j : J) :
    RegularModTwoRelationModule Q J →ₗ[ZMod 2] MonoidAlgebra (ZMod 2) Q := by
  classical
  exact (Finsupp.lsum (ZMod 2) fun p : Q × J =>
    LinearMap.toSpanSingleton (ZMod 2) (MonoidAlgebra (ZMod 2) Q)
      (if p.2 = j then MonoidAlgebra.single p.1 1 else 0))

@[simp]
theorem regularModTwoComponent_single
    (j j' : J) (q : Q) (a : ZMod 2) :
    regularModTwoComponent (Q := Q) j (Finsupp.single (q, j') a) =
      if j' = j then MonoidAlgebra.single q a else 0 := by
  classical
  rw [regularModTwoComponent, Finsupp.lsum_single]
  by_cases h : j' = j
  · simp [h, smul_eq_mul]
  · simp [h]

@[simp]
theorem regularModTwoComponent_apply
    (j : J) (c : RegularModTwoRelationModule Q J) (q : Q) :
    regularModTwoComponent (Q := Q) j c q = c (q, j) := by
  classical
  induction c using Finsupp.induction with
  | zero => rfl
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, k⟩
      by_cases hk : k = j
      · subst k
        simp [Finsupp.add_apply, Finsupp.single_apply, ih]
      · simp [Finsupp.add_apply, ih, hk]

variable {Q' : Type} [Group Q']

/-- Taking a basis component commutes with pushforward along a group homomorphism. -/
theorem regularModTwoComponent_pushforward
    (φ : Q →* Q') (j : J) (c : RegularModTwoRelationModule Q J) :
    regularModTwoComponent (Q := Q') j (regularModTwoPushforward φ J c) =
      MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) φ
        (regularModTwoComponent (Q := Q) j c) := by
  classical
  induction c using Finsupp.induction with
  | zero =>
      change 0 = MonoidAlgebra.mapDomain (⇑φ) 0
      exact (MonoidAlgebra.mapDomain_zero _).symm
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, k⟩
      calc
        regularModTwoComponent j
            (regularModTwoPushforward φ J (Finsupp.single (q, k) a + c)) =
          regularModTwoComponent j
              (regularModTwoPushforward φ J (Finsupp.single (q, k) a)) +
            regularModTwoComponent j (regularModTwoPushforward φ J c) := by
              rw [map_add, map_add]
        _ = (if k = j then MonoidAlgebra.single (φ q) a else 0) +
            MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) φ
              (regularModTwoComponent j c) := by
              rw [regularModTwoPushforward_single,
                regularModTwoComponent_single, ih]
        _ = MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) φ
            ((if k = j then MonoidAlgebra.single q a else 0) +
              regularModTwoComponent j c) := by
              rw [map_add]
              congr 1
              by_cases hk : k = j
              · simp [hk]
              · rw [if_neg hk, if_neg hk]
                change 0 = MonoidAlgebra.mapDomain (⇑φ) 0
                exact (MonoidAlgebra.mapDomain_zero _).symm
        _ = MonoidAlgebra.mapDomainAlgHom (ZMod 2) (ZMod 2) φ
            (regularModTwoComponent j (Finsupp.single (q, k) a + c)) := by
              have hc : regularModTwoComponent j
                    (Finsupp.single (q, k) a + c) =
                  (if k = j then MonoidAlgebra.single q a else 0) +
                    regularModTwoComponent j c := by
                rw [map_add, regularModTwoComponent_single]
              rw [hc, map_add]

/-- Taking a basis component turns regular translation into left multiplication. -/
theorem regularModTwoComponent_translate
    (g : Q) (j : J) (c : RegularModTwoRelationModule Q J) :
    regularModTwoComponent (Q := Q) j (regularModTwoTranslate Q J g c) =
      MonoidAlgebra.single g 1 * regularModTwoComponent (Q := Q) j c := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨q, k⟩
      calc
        regularModTwoComponent j
            (regularModTwoTranslate Q J g (Finsupp.single (q, k) a + c)) =
          regularModTwoComponent j
              (regularModTwoTranslate Q J g (Finsupp.single (q, k) a)) +
            regularModTwoComponent j (regularModTwoTranslate Q J g c) := by
              rw [map_add, map_add]
        _ = (if k = j then MonoidAlgebra.single (g * q) a else 0) +
            MonoidAlgebra.single g 1 * regularModTwoComponent j c := by
              rw [regularModTwoTranslate_single,
                regularModTwoComponent_single, ih]
        _ = MonoidAlgebra.single g 1 *
            ((if k = j then MonoidAlgebra.single q a else 0) +
              regularModTwoComponent j c) := by
              rw [mul_add]
              congr 1
              by_cases hk : k = j
              · simp [hk, MonoidAlgebra.single_mul_single]
              · simp [hk]
        _ = MonoidAlgebra.single g 1 *
            regularModTwoComponent j (Finsupp.single (q, k) a + c) := by
              rw [map_add, regularModTwoComponent_single]

/-! ## Completed basis components -/

/-- Extract one basis component from a completed regular module. -/
def ModTwoCompletedRegularModule.component (J : Type) (j : J) :
    ModTwoCompletedRegularModule G J →ₗ[ZMod 2] ModTwoCompletedGroupAlgebra G where
  toFun c :=
    ⟨fun U => regularModTwoComponent j
        (ModTwoCompletedRegularModule.coordinate G J U c), by
      intro U V h
      rw [modTwoGroupAlgebraTransition]
      rw [← regularModTwoComponent_pushforward]
      exact congrArg (regularModTwoComponent j)
        (ModTwoCompletedRegularModule.coordinate_compatible G J c h)⟩
  map_add' x y := by
    apply Subtype.ext
    funext U
    exact map_add (regularModTwoComponent j)
      (ModTwoCompletedRegularModule.coordinate G J U x)
      (ModTwoCompletedRegularModule.coordinate G J U y)
  map_smul' a x := by
    apply Subtype.ext
    funext U
    exact map_smul (regularModTwoComponent j) a
      (ModTwoCompletedRegularModule.coordinate G J U x)

@[simp]
theorem ModTwoCompletedRegularModule.component_coordinate
    (J : Type) (j : J) (U : OpenNormalSubgroup G)
    (c : ModTwoCompletedRegularModule G J) :
    ModTwoCompletedGroupAlgebra.coordinate G U
        (ModTwoCompletedRegularModule.component G J j c) =
      regularModTwoComponent j
        (ModTwoCompletedRegularModule.coordinate G J U c) :=
  rfl

/-- All basis components together detect equality in a completed regular module. -/
theorem ModTwoCompletedRegularModule.component_jointly_injective
    (J : Type) :
    Function.Injective (fun c : ModTwoCompletedRegularModule G J =>
      fun j : J => ModTwoCompletedRegularModule.component G J j c) := by
  intro x y hxy
  apply ModTwoCompletedRegularModule.ext G J
  intro U
  ext p
  rcases p with ⟨q, j⟩
  have h := congrArg
    (fun a : ModTwoCompletedGroupAlgebra G =>
      ModTwoCompletedGroupAlgebra.coordinate G U a q)
    (congrFun hxy j)
  change regularModTwoComponent j
      (ModTwoCompletedRegularModule.coordinate G J U x) q =
    regularModTwoComponent j
      (ModTwoCompletedRegularModule.coordinate G J U y) q at h
  simpa only [regularModTwoComponent_apply] using h

/-- Component extraction is equivariant for the completed regular actions. -/
theorem ModTwoCompletedRegularModule.component_smul
    (J : Type) (j : J) (g : G) (c : ModTwoCompletedRegularModule G J) :
    ModTwoCompletedRegularModule.component G J j (g • c) =
      g • ModTwoCompletedRegularModule.component G J j c := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  change regularModTwoComponent j
      (regularModTwoTranslate (G ⧸ U.toSubgroup) J
        (QuotientGroup.mk' U.toSubgroup g)
        (ModTwoCompletedRegularModule.coordinate G J U c)) =
    MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 *
      regularModTwoComponent j
        (ModTwoCompletedRegularModule.coordinate G J U c)
  exact regularModTwoComponent_translate _ _ _

/-- The rank-one equivalence is precisely extraction of the unique basis component. -/
theorem completedRegularUnitGroupAlgebraEquiv_apply_eq_component
    (c : ModTwoCompletedRegularModule G Unit) :
    completedRegularUnitGroupAlgebraEquiv G c =
      ModTwoCompletedRegularModule.component G Unit () c := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  ext q
  simp only [completedRegularUnitGroupAlgebraEquiv_coordinate,
    ModTwoCompletedRegularModule.component_coordinate,
    regularUnitGroupAlgebraEquiv_apply, regularModTwoComponent_apply]

/-- The rank-one completed equivalence is `G`-equivariant. -/
theorem completedRegularUnitGroupAlgebraEquiv_smul
    (g : G) (c : ModTwoCompletedRegularModule G Unit) :
    completedRegularUnitGroupAlgebraEquiv G (g • c) =
      g • completedRegularUnitGroupAlgebraEquiv G c := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  change regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
      (regularModTwoTranslate (G ⧸ U.toSubgroup) Unit
        (QuotientGroup.mk' U.toSubgroup g)
        (ModTwoCompletedRegularModule.coordinate G Unit U c)) =
    MonoidAlgebra.single (QuotientGroup.mk' U.toSubgroup g) 1 *
      regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U c)
  have h := regularModTwoComponent_translate
    (Q := G ⧸ U.toSubgroup) (J := Unit)
    (QuotientGroup.mk' U.toSubgroup g) ()
    (ModTwoCompletedRegularModule.coordinate G Unit U c)
  rw [show regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (regularModTwoTranslate (G ⧸ U.toSubgroup) Unit
          (QuotientGroup.mk' U.toSubgroup g)
          (ModTwoCompletedRegularModule.coordinate G Unit U c)) =
      regularModTwoComponent ()
        (regularModTwoTranslate (G ⧸ U.toSubgroup) Unit
          (QuotientGroup.mk' U.toSubgroup g)
          (ModTwoCompletedRegularModule.coordinate G Unit U c)) by
        ext q
        simp,
    show regularUnitGroupAlgebraEquiv (G ⧸ U.toSubgroup)
        (ModTwoCompletedRegularModule.coordinate G Unit U c) =
      regularModTwoComponent ()
        (ModTwoCompletedRegularModule.coordinate G Unit U c) by
        ext q
        simp]
  exact h

/-! ## The completed Fox-derivative row -/

variable {I : Type}

/-- At finite level, the `i`th component of a rank-one Fox boundary is left multiplication by
the `i`th component of the Fox derivative. -/
theorem finiteLevelRankOneFoxBoundary_component
    {Q : Type} [Group Q] (m : I → Q) (w : FreeGroup I) (i : I)
    (c : RegularModTwoRelationModule Q Unit) :
    regularModTwoComponent i
        ((finiteLevelModTwoFoxBoundary m (fun _ : Unit => w)).map c) =
      regularUnitGroupAlgebraEquiv Q c *
        regularModTwoComponent i (modTwoFoxDerivative m w) := by
  classical
  induction c using Finsupp.induction with
  | zero => simp
  | single_add p a c hp ha ih =>
      rcases p with ⟨g, ⟨⟩⟩
      rw [map_add, map_add, finiteLevelModTwoFoxBoundary_single,
        map_smul, regularModTwoComponent_translate, ih, map_add,
        regularUnitGroupAlgebraEquiv_single, add_mul]
      rw [show MonoidAlgebra.single g a =
          a • MonoidAlgebra.single g (1 : ZMod 2) by
        ext q
        simp [smul_eq_mul]]
      congr 1
      exact (Algebra.smul_mul_assoc a
          (MonoidAlgebra.single g (1 : ZMod 2))
          (regularModTwoComponent i (modTwoFoxDerivative m w))).symm

/-- The `i`th completed Fox derivative, represented by its compatible finite-quotient
components. -/
def completedModTwoFoxDerivativeRow
    (m : I → G) (w : FreeGroup I) (i : I) :
    ModTwoCompletedGroupAlgebra G :=
  ⟨fun U => regularModTwoComponent i
      (modTwoFoxDerivative
        (fun k => QuotientGroup.mk' U.toSubgroup (m k)) w), by
    intro U V h
    rw [modTwoGroupAlgebraTransition]
    rw [← regularModTwoComponent_pushforward]
    rw [regularModTwoPushforward_modTwoFoxDerivative]
    rfl⟩

@[simp]
theorem completedModTwoFoxDerivativeRow_coordinate
    (m : I → G) (w : FreeGroup I) (i : I)
    (U : OpenNormalSubgroup G) :
    ModTwoCompletedGroupAlgebra.coordinate G U
        (completedModTwoFoxDerivativeRow G m w i) =
      regularModTwoComponent i
        (modTwoFoxDerivative
          (fun k => QuotientGroup.mk' U.toSubgroup (m k)) w) :=
  rfl

/-- The concrete assembled completed Fox boundary is coordinatewise multiplication by its
completed derivative row.  This does not use a density or continuity argument: it follows at
each finite quotient from the explicit finite Fox matrix. -/
theorem completedRankOneFoxBoundary_component
    (m : I → G) (w : FreeGroup I) (i : I)
    (c : ModTwoCompletedRegularModule G Unit) :
    ModTwoCompletedRegularModule.component G I i
        ((completedModTwoFoxBoundary m (fun _ : Unit => w)).map c) =
      completedRegularUnitGroupAlgebraEquiv G c *
        completedModTwoFoxDerivativeRow G m w i := by
  apply ModTwoCompletedGroupAlgebra.ext G
  intro U
  rw [ModTwoCompletedRegularModule.component_coordinate,
    completedModTwoFoxBoundary_coordinate,
    finiteLevelRankOneFoxBoundary_component]
  rw [map_mul, completedRegularUnitGroupAlgebraEquiv_coordinate,
    completedModTwoFoxDerivativeRow_coordinate]

/-! ## The improved square row and its exact injectivity criterion -/

/-- The completed Fox-derivative row of the actual improved square relator. -/
def sqCompletedModTwoFoxDerivativeRow (h : ℕ) (i : Fin (sqRank h)) :
    ModTwoCompletedGroupAlgebra (DSq h : Type) :=
  completedModTwoFoxDerivativeRow (DSq h : Type)
    (sqGen h) (sqDiscreteRelator h) i

@[simp]
theorem sqCompletedModTwoFoxDerivativeRow_coordinate
    (h : ℕ) (i : Fin (sqRank h))
    (U : OpenNormalSubgroup (DSq h : Type)) :
    ModTwoCompletedGroupAlgebra.coordinate (DSq h : Type) U
        (sqCompletedModTwoFoxDerivativeRow h i) =
      regularModTwoComponent i
        (modTwoFoxDerivative
          (fun k => QuotientGroup.mk' U.toSubgroup (sqGen h k))
          (sqDiscreteRelator h)) :=
  rfl

/-- Componentwise row formula for the actual improved completed Fox boundary. -/
theorem sqCompletedModTwoFoxBoundary_component
    (h : ℕ) (i : Fin (sqRank h))
    (c : ModTwoCompletedRegularModule (DSq h : Type) Unit) :
    ModTwoCompletedRegularModule.component (DSq h : Type) (Fin (sqRank h)) i
        ((sqCompletedModTwoFoxBoundary h).map c) =
      completedRegularUnitGroupAlgebraEquiv (DSq h : Type) c *
        sqCompletedModTwoFoxDerivativeRow h i :=
  completedRankOneFoxBoundary_component (DSq h : Type)
    (sqGen h) (sqDiscreteRelator h) i c

/-- Triviality of the common left annihilator of a row in a ring. -/
def HasTrivialCommonLeftAnnihilator
    {R K : Type} [Semiring R] (row : K → R) : Prop :=
  ∀ a : R, (∀ k, a * row k = 0) → a = 0

/-- Injectivity of the actual completed improved-square Fox boundary is exactly the assertion
that its derivative row has trivial common left annihilator. -/
theorem sqCompletedModTwoFoxBoundary_injective_iff_commonAnnihilator
    (h : ℕ) :
    Function.Injective (sqCompletedModTwoFoxBoundary h).map ↔
      HasTrivialCommonLeftAnnihilator
        (sqCompletedModTwoFoxDerivativeRow h) := by
  constructor
  · intro hinj a ha
    let c := (completedRegularUnitGroupAlgebraEquiv (DSq h : Type)).symm a
    have hb : (sqCompletedModTwoFoxBoundary h).map c = 0 := by
      apply ModTwoCompletedRegularModule.component_jointly_injective
        (DSq h : Type) (Fin (sqRank h))
      funext i
      change ModTwoCompletedRegularModule.component
          (DSq h : Type) (Fin (sqRank h)) i
            ((sqCompletedModTwoFoxBoundary h).map c) =
        ModTwoCompletedRegularModule.component
          (DSq h : Type) (Fin (sqRank h)) i 0
      rw [sqCompletedModTwoFoxBoundary_component, map_zero,
        LinearEquiv.apply_symm_apply]
      exact ha i
    have hc : c = 0 := by
      apply hinj
      simpa using hb
    calc
      a = completedRegularUnitGroupAlgebraEquiv (DSq h : Type) c := by
        exact (completedRegularUnitGroupAlgebraEquiv
          (DSq h : Type)).apply_symm_apply a |>.symm
      _ = completedRegularUnitGroupAlgebraEquiv (DSq h : Type) 0 :=
        congrArg (completedRegularUnitGroupAlgebraEquiv (DSq h : Type)) hc
      _ = 0 := map_zero _
  · intro hann x y hxy
    have hzero : (sqCompletedModTwoFoxBoundary h).map (x - y) = 0 := by
      calc
        (sqCompletedModTwoFoxBoundary h).map (x - y) =
            (sqCompletedModTwoFoxBoundary h).map x -
              (sqCompletedModTwoFoxBoundary h).map y :=
          map_sub (sqCompletedModTwoFoxBoundary h).map x y
        _ = 0 := by
          rw [hxy]
          exact sub_self ((sqCompletedModTwoFoxBoundary h).map y)
    have ha : completedRegularUnitGroupAlgebraEquiv
        (DSq h : Type) (x - y) = 0 := by
      apply hann
      intro i
      rw [← sqCompletedModTwoFoxBoundary_component, hzero, map_zero]
    have hsub : x - y = 0 := by
      apply (completedRegularUnitGroupAlgebraEquiv (DSq h : Type)).injective
      simpa using ha
    exact sub_eq_zero.mp hsub

end

end GQ2.ContCoh
