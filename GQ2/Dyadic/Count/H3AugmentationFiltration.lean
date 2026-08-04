/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.CompletedModTwoGroupAlgebra

/-!
# From initial-form regularity to a zero common annihilator

The completed Fox row is injective once its entries have zero common left annihilator in the
completed group algebra.  A classical Magnus--Labute proof obtains that conclusion one
augmentation layer at a time: a nonzero leading form of a coefficient cannot annihilate every
leading Fox derivative.

This file formalizes that filtration argument independently of the still-missing pro-two
identity theorem.  `RowInitialFormRegular F shift d` is the honest associated-graded input: on
every layer `F n / F (n+1)`, the row of right multiplications by the degree-`shift` initial
forms of `d i` is defined and has zero common kernel.  If `F 0` is the whole ring and the
filtration is separated, iteration proves that the row has zero common annihilator in the
original ring.

The second section supplies the concrete algebraic augmentation filtration on the repository's
explicit `F₂[[G]]`.  Thus a future initial-form or strong-freeness theorem has a strictly
lower-level target:

* prove separation of the powers of the completed augmentation ideal;
* prove `CompletedRowAugmentationInitialRegular d` for the actual completed Fox row.

Neither condition mentions cohomology, finite-level pointwise injectivity, compatible-family
detection, or global injectivity.  The first condition is a topological/Magnus separation
statement; the second is the missing associated-graded Labute calculation.
-/

namespace GQ2.ContCoh

noncomputable section

/-! ## The abstract filtered-ring argument -/

section FilteredRow

universe uA uI

variable {A : Type uA} {I : Type uI} [Ring A]

/-- A row `d : I → A` is regular at degree `shift` on every successive layer of a filtration
`F` if a coefficient in `F n` whose products with the whole row vanish through the next
expected product layer `F (n + shift + 1)` must itself lie in `F (n+1)`.

Equivalently, whenever the quotient maps are constructed, the map
`F n / F (n+1) → (F (n+shift) / F (n+shift+1))^I` induced by right multiplication by the
row has zero kernel, provided multiplication by `d i` has the advertised filtration degree.
This implication form avoids postulating that separate multiplicativity property for an
arbitrary filtration; the elementary annihilator iteration does not need it. -/
def RowLayerRegular (F : ℕ → AddSubgroup A) (shift : ℕ) (d : I → A) : Prop :=
  ∀ (n : ℕ) (a : A), a ∈ F n →
    (∀ i : I, a * d i ∈ F (n + shift + 1)) → a ∈ F (n + 1)

/-- Multiplication by a row has filtration degree `shift`.  Together with
`RowLayerRegular`, this is precisely the data needed to interpret the latter implication as
injectivity of the row on associated-graded layers. -/
def RowRespectsFiltrationAtShift (F : ℕ → AddSubgroup A) (shift : ℕ)
    (d : I → A) : Prop :=
  ∀ (n : ℕ) (a : A), a ∈ F n → ∀ i : I, a * d i ∈ F (n + shift)

/-- Honest initial-form regularity: the row has a fixed filtration degree and its induced row
on every associated-graded layer has zero common kernel. -/
def RowInitialFormRegular (F : ℕ → AddSubgroup A) (shift : ℕ) (d : I → A) : Prop :=
  RowRespectsFiltrationAtShift F shift d ∧ RowLayerRegular F shift d

/-- A filtration is separated when membership in every layer forces an element to vanish. -/
def AdditiveFiltrationSeparated (F : ℕ → AddSubgroup A) : Prop :=
  ∀ a : A, (∀ n : ℕ, a ∈ F n) → a = 0

/-- A row has zero common left annihilator. -/
def RowCommonLeftAnnihilatorFree (d : I → A) : Prop :=
  ∀ a : A, (∀ i : I, a * d i = 0) → a = 0

/-- **Filtered annihilator lemma.**  Layerwise initial-form regularity and separation imply
that the original row has zero common left annihilator.

The proof is the standard filtration iteration.  An annihilator begins in `F 0`; regularity
moves it from `F n` into `F (n+1)`, because all row products are zero.  Separation then kills
it. -/
theorem rowCommonLeftAnnihilatorFree_of_layerRegular
    (F : ℕ → AddSubgroup A) (shift : ℕ) (d : I → A)
    (hzero : F 0 = ⊤)
    (hsep : AdditiveFiltrationSeparated F)
    (hregular : RowLayerRegular F shift d) :
    RowCommonLeftAnnihilatorFree d := by
  intro a ha
  apply hsep a
  intro n
  induction n with
  | zero => rw [hzero]; exact Set.mem_univ a
  | succ n hn =>
      apply hregular n a hn
      intro i
      rw [ha i]
      exact (F (n + shift + 1)).zero_mem

/-- Bundled associated-graded form of the filtered annihilator lemma. -/
theorem rowCommonLeftAnnihilatorFree_of_initialFormRegular
    (F : ℕ → AddSubgroup A) (shift : ℕ) (d : I → A)
    (hzero : F 0 = ⊤)
    (hsep : AdditiveFiltrationSeparated F)
    (hregular : RowInitialFormRegular F shift d) :
    RowCommonLeftAnnihilatorFree d :=
  rowCommonLeftAnnihilatorFree_of_layerRegular F shift d hzero hsep hregular.2

/-- The filtered proof can be used pointwise without unfolding the common-annihilator
predicate. -/
theorem eq_zero_of_layerRegular_of_mul_row_eq_zero
    (F : ℕ → AddSubgroup A) (shift : ℕ) (d : I → A)
    (hzero : F 0 = ⊤)
    (hsep : AdditiveFiltrationSeparated F)
    (hregular : RowLayerRegular F shift d)
    (a : A) (ha : ∀ i : I, a * d i = 0) : a = 0 :=
  rowCommonLeftAnnihilatorFree_of_layerRegular F shift d hzero hsep hregular a ha

end FilteredRow

/-! ## The concrete augmentation filtration on `F₂[[G]]` -/

section CompletedAugmentation

universe u

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G]

/-- The algebraic augmentation ideal in the explicit completed group algebra, generated by
the group-like differences `[g] - 1`.

For a Magnus proof one may eventually identify this ideal with the kernel of the continuous
augmentation map.  The filtered annihilator lemma only needs its powers, so no such equality is
assumed here. -/
def modTwoCompletedAugmentationIdeal : Ideal (ModTwoCompletedGroupAlgebra G) :=
  Ideal.span (Set.range fun g : G => ModTwoCompletedGroupAlgebra.of G g - 1)

/-- The algebraic augmentation-power filtration `I^n` of `F₂[[G]]`. -/
def modTwoCompletedAugmentationFiltration (n : ℕ) :
    AddSubgroup (ModTwoCompletedGroupAlgebra G) :=
  (modTwoCompletedAugmentationIdeal G ^ n).toAddSubgroup

@[simp]
theorem modTwoCompletedAugmentationFiltration_zero :
    modTwoCompletedAugmentationFiltration G 0 = ⊤ := by
  simp [modTwoCompletedAugmentationFiltration]

/-- Separation of the algebraic augmentation-power filtration.  This is kept as a named
property because establishing it for the inverse-limit model is one of the two genuine
Magnus-topology obligations, rather than a formal consequence of the carrier definition. -/
abbrev ModTwoCompletedAugmentationSeparated : Prop :=
  AdditiveFiltrationSeparated (modTwoCompletedAugmentationFiltration G)

/-- The associated-graded regularity condition for a row in `F₂[[G]]`: on every augmentation
layer, its degree-one initial forms have zero common left annihilator.  Degree one is the
correct shift for Fox derivatives of a relator whose first nonzero initial form has degree
two. -/
def CompletedRowAugmentationInitialRegular {I : Type}
    (d : I → ModTwoCompletedGroupAlgebra G) : Prop :=
  RowInitialFormRegular (modTwoCompletedAugmentationFiltration G) 1 d

/-- **Concrete Magnus--Labute adapter.**  Separation of the augmentation powers plus
regularity of the row on every initial-form layer implies zero common left annihilator in
`F₂[[G]]` itself. -/
theorem completedRowCommonLeftAnnihilatorFree_of_augmentationInitialRegular
    {I : Type} (d : I → ModTwoCompletedGroupAlgebra G)
    (hsep : ModTwoCompletedAugmentationSeparated (G := G))
    (hregular : CompletedRowAugmentationInitialRegular G d) :
  RowCommonLeftAnnihilatorFree d :=
  rowCommonLeftAnnihilatorFree_of_initialFormRegular
    (modTwoCompletedAugmentationFiltration G) 1 d
    (modTwoCompletedAugmentationFiltration_zero G) hsep hregular

end CompletedAugmentation

end


end GQ2.ContCoh
