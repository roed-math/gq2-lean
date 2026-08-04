/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FiniteTwoLocalReciprocityHigherKummer

/-!
# Scalar endomorphisms of higher roots of unity

This file closes the coefficient-algebra gap below higher Tate--Kummer--Artin compatibility.
For every positive `n`, the group `MuN n` is cyclic of order `n`, so its additive endomorphism
group is (noncanonically) additively equivalent to `ZMod n`.  More importantly, the conjugation
action on this endomorphism group is canonical and trivial: every additive endomorphism of a
cyclic group commutes with every additive automorphism.

The existing `HigherMuNDualScalarization` structure is parameterized by an arbitrary action on
`ZMod (2 ^ m)`.  Such an arbitrary action need not be trivial once `m > 1`, so no theorem can
construct that structure for every possible instance.  We therefore provide both sharp forms:

* `HigherMuNDualScalarization.ofTrivialAction` works with any supplied coefficient action once
  its triviality is proved;
* `canonicalHigherMuNDualScalarization` installs the explicit trivial action and constructs the
  scalarization unconditionally for every `K` and `m`.

No primitive root is fixed globally.  The additive equivalence uses the standard choice-based
cyclic-group equivalence; triviality and equivariance are independent of that choice.
-/

namespace GQ2.Dyadic

open scoped Classical

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

/-! ## The abstract cyclic endomorphism calculation -/

/-- A noncanonical additive equivalence `MuN n ≃+ ZMod n`, obtained solely from cyclicity and
the cardinality of the roots-of-unity group. -/
noncomputable def muNZModAddEquiv (n : ℕ) [NeZero n] : MuN n ≃+ ZMod n :=
  addEquivOfAddCyclicCardEq (G := MuN n) (G' := ZMod n)
    ((Nat.card_congr Additive.toMul).trans
      (HasEnoughRootsOfUnity.natCard_rootsOfUnity (AlgebraicClosure ℚ_[2]) n) |>.trans
        (Nat.card_zmod n).symm)

/-- Conjugation by an additive equivalence transports additive endomorphisms. -/
def addEndCongr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) : (A →+ A) ≃+ (B →+ B) where
  toFun f := e.toAddMonoidHom.comp (f.comp e.symm.toAddMonoidHom)
  invFun f := e.symm.toAddMonoidHom.comp (f.comp e.toAddMonoidHom)
  left_inv f := by
    ext x
    simp
  right_inv f := by
    ext x
    simp
  map_add' f h := by
    ext x
    simp

/-- Evaluation at `1` identifies the additive endomorphisms of `ZMod n` with `ZMod n`.
The inverse sends `a` to multiplication by `a`. -/
def zmodEndEvalOne (n : ℕ) : (ZMod n →+ ZMod n) ≃+ ZMod n where
  toFun f := f 1
  invFun a :=
    { toFun := fun x => x * a
      map_zero' := zero_mul a
      map_add' := fun x y => add_mul x y a }
  left_inv f := by
    ext x
    have h := ZMod.map_smul f x 1
    simpa [smul_eq_mul] using h.symm
  right_inv a := one_mul a
  map_add' f h := by simp

/-- Unfold the `MuDual` type synonym as its underlying additive endomorphism group. -/
def muDualEndAddEquiv (n : ℕ) [NeZero n] :
    MuDual n (MuN n) ≃+ (MuN n →+ MuN n) where
  toFun f := f
  invFun f := f
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

/-- **Higher roots-of-unity dual scalarization.**  Additive endomorphisms of `MuN n` are
noncanonically the scalars `ZMod n`. -/
noncomputable def muDualMuNScalarEquiv (n : ℕ) [NeZero n] :
    MuDual n (MuN n) ≃+ ZMod n :=
  (muDualEndAddEquiv n).trans <|
    (addEndCongr (muNZModAddEquiv n)).trans (zmodEndEvalOne n)

/-- Any two additive endomorphisms of a cyclic additive group commute. -/
theorem addEnd_commute_of_isAddCyclic {A : Type*} [AddCommGroup A] [IsAddCyclic A]
    (f h : A →+ A) : f.comp h = h.comp f := by
  obtain ⟨gen, hgen⟩ := exists_zsmul_surjective A
  obtain ⟨a, ha⟩ := hgen (h gen)
  obtain ⟨b, hb⟩ := hgen (f gen)
  ext x
  obtain ⟨k, rfl⟩ := hgen x
  simp only [AddMonoidHom.comp_apply, map_zsmul]
  rw [← ha, ← hb, map_zsmul, map_zsmul, smul_smul, smul_smul]
  rw [← hb, ← ha, smul_smul, smul_smul]
  congr 1
  ring

/-- Consequently every additive endomorphism of a cyclic module is equivariant for every
distributive group action on that module. -/
theorem addEnd_equivariant_of_isAddCyclic
    {G A : Type*} [Group G] [AddCommGroup A] [IsAddCyclic A]
    [DistribMulAction G A] (g : G) (f : A →+ A) (x : A) :
    f (g • x) = g • f x := by
  have h := DFunLike.congr_fun
    (addEnd_commute_of_isAddCyclic f
      (DistribMulAction.toAddEquiv A g).toAddMonoidHom) x
  exact h

/-- **Canonical triviality of the Tate-dual action.**  The conjugation action on
`MuDual n (MuN n) = Hom(MuN n, MuN n)` is trivial for every acting group. -/
theorem muDualMuN_smul_trivial {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (n : ℕ) [NeZero n]
    [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
    (g : G) (f : MuDual n (MuN n)) : g • f = f := by
  apply MuDual.ext
  intro x
  rw [muDual_smul_apply]
  change g • (muDualEndAddEquiv n f) (g⁻¹ • x) = f x
  rw [addEnd_equivariant_of_isAddCyclic
    (g := g⁻¹) (f := (muDualEndAddEquiv n f))]
  simp only [smul_inv_smul]
  rfl

/-! ## Adapters to the higher-reciprocity interface -/

/-- Construct the existing scalarization structure for any explicitly trivial action on the
target `ZMod (2 ^ m)`.  The source action is trivial by `muDualMuN_smul_trivial`, not by an
assumption on the cyclotomic action on `MuN (2 ^ m)`. -/
noncomputable def HigherMuNDualScalarization.ofTrivialAction
    {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
    (m : ℕ) [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    (htriv : ∀ (g : ↥(K.fixingSubgroup)) (a : ZMod (2 ^ m)), g • a = a) :
    HigherMuNDualScalarization K m where
  equiv := muDualMuNScalarEquiv (2 ^ m)
  equivariant g x := by
    rw [muDualMuN_smul_trivial, htriv]
  smul_trivial := htriv

/-- The explicit trivial action on the scalar target at exponent `2 ^ m`. -/
@[implicit_reducible] def higherTrivialZModAction
    (G : Type*) [Group G] (m : ℕ) : DistribMulAction G (ZMod (2 ^ m)) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The explicit trivial scalar action is continuous. -/
theorem continuousSMul_higherTrivialZModAction
    (G : Type*) [Group G] [TopologicalSpace G] (m : ℕ) :
    letI := higherTrivialZModAction G m
    ContinuousSMul G (ZMod (2 ^ m)) := by
  letI := higherTrivialZModAction G m
  exact ⟨continuous_snd⟩

/-- **Unconditional higher scalarization.**  With the canonical trivial scalar action installed,
`MuDual (2 ^ m) (MuN (2 ^ m))` is equivariantly additively equivalent to `ZMod (2 ^ m)` for every
finite dyadic field `K` and every `m`. -/
noncomputable def canonicalHigherMuNDualScalarization
    (K : IntermediateField ℚ_[2] ℚbar2) [FiniteDimensional ℚ_[2] K] (m : ℕ) :
    letI := higherTrivialZModAction ↥(K.fixingSubgroup) m
    letI := continuousSMul_higherTrivialZModAction ↥(K.fixingSubgroup) m
    HigherMuNDualScalarization K m := by
  letI := higherTrivialZModAction ↥(K.fixingSubgroup) m
  letI : ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m)) :=
    continuousSMul_higherTrivialZModAction ↥(K.fixingSubgroup) m
  exact HigherMuNDualScalarization.ofTrivialAction m (fun _ _ => rfl)

#print axioms muDualMuNScalarEquiv
#print axioms muDualMuN_smul_trivial
#print axioms canonicalHigherMuNDualScalarization

end


end GQ2.Dyadic
