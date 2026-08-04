/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import Mathlib.GroupTheory.FiniteAbelian.Basic
import GQ2.Dyadic.FiniteTwoLocalReciprocity
import GQ2.DeepCount.Filtration
import GQ2.Foundations.Interfaces

/-!
# The cyclic-character boundary for finite pro-2 reciprocity

The finite local-CFT supply in `FiniteTwoLocalReciprocity` asks for factorization of maps from
`Kˣ` to arbitrary finite `2`-groups.  Since `Kˣ` is commutative, this file reduces that supply
exactly to its finite **cyclic** `2`-group characters.  These are the characters that a
higher-power Kummer sequence and local Tate duality would naturally produce.

The reduction is completely group-theoretic.  A finite abelian `2`-group is a finite product of
cyclic groups; an arbitrary map from `Kˣ` has commutative image.  Thus no arbitrary finite
norm-residue theorem is hidden in the passage from cyclic characters to the full supply.

The existing Kummer implementation is also recorded precisely: `kummerClassKMonoidHom` is a
surjection onto `H¹(G_K, 𝔽₂)` with square kernel.  There is no corresponding construction in the
repository for `μ_(2^m)` when `m > 1`, and `MarkedRecip` has no theorem identifying evaluation of
even the mod-`2` Galois character on `rec_K(a)` with the Kummer/Tate pairing.  Consequently the
cyclic-character supply below is an exact landing point for the missing higher-power
Kummer--reciprocity compatibility, not a new axiom.
-/

namespace GQ2.Dyadic

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

noncomputable local instance instT2SpaceTopAbCyclicRecip
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-! ## The exact cyclic-character reduction -/

/-- **Finite cyclic `2`-character reciprocity supply.**  Every character of `Kˣ` with values
in a finite cyclic `2`-group factors through `(G_K(2))^ab`, compatibly with marked reciprocity.

Every finite cyclic `2`-group is (noncanonically) `Z/2^m`; quantifying over the abstract target
avoids inserting a choice of generator into the interface. -/
structure FiniteCyclicTwoReciprocitySupply (B : MarkedRecip R K) : Prop where
  factor : ∀ (C : Type) [CommGroup C] [TopologicalSpace C] [Finite C]
      [DiscreteTopology C], IsPGroup 2 C → IsCyclic C → ∀ f : (↥K)ˣ →* C,
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K))) C,
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a

namespace FiniteCyclicTwoReciprocitySupply

variable {B : MarkedRecip R K}

/-- The full finite local-CFT factorization supply restricts to cyclic targets. -/
def ofFiniteTwoLocalReciprocitySupply (S : FiniteTwoLocalReciprocitySupply B) :
    FiniteCyclicTwoReciprocitySupply B where
  factor := by
    intro C _ _ _ _ hC _ f
    exact S.factor C hC f

/-- Cyclic factorization assembles over a finite product, hence factors every map from `Kˣ`
to a finite commutative `2`-group. -/
private theorem factor_commutative (S : FiniteCyclicTwoReciprocitySupply B)
    (C : Type) [CommGroup C] [TopologicalSpace C] [Finite C] [DiscreteTopology C]
    (hC : IsPGroup 2 C) (f : (↥K)ˣ →* C) :
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K))) C,
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a := by
  classical
  obtain ⟨ι, instι, n, hn, ⟨e⟩⟩ := CommGroup.equiv_prod_multiplicative_zmod_of_finite C
  letI : Fintype ι := instι
  letI (i : ι) : NeZero (n i) := NeZero.of_gt (hn i)
  let proj (i : ι) : C →* Multiplicative (ZMod (n i)) :=
    (Pi.evalMonoidHom (fun i : ι ↦ Multiplicative (ZMod (n i))) i).comp e.toMonoidHom
  have hproj (i : ι) : Function.Surjective (proj i) := by
    intro z
    refine ⟨e.symm (Function.update 1 i z), ?_⟩
    simp [proj]
  have hp (i : ι) : IsPGroup 2 (Multiplicative (ZMod (n i))) :=
    hC.of_surjective (proj i) (hproj i)
  choose phi hphi using fun i ↦ S.factor (Multiplicative (ZMod (n i))) (hp i)
    (inferInstance : IsCyclic (Multiplicative (ZMod (n i)))) ((proj i).comp f)
  let phiProd : ContinuousMonoidHom
      (topAbelianization (maxProPQuotient 2 (GalK K)))
      ((i : ι) → Multiplicative (ZMod (n i))) :=
    { toMonoidHom := MonoidHom.pi (fun i ↦ (phi i).toMonoidHom)
      continuous_toFun := continuous_pi (fun i ↦ (phi i).continuous_toFun) }
  let eInv : ContinuousMonoidHom ((i : ι) → Multiplicative (ZMod (n i))) C :=
    ⟨e.symm.toMonoidHom, continuous_of_discreteTopology⟩
  refine ⟨eInv.comp phiProd, fun a ↦ ?_⟩
  apply e.injective
  have heInv : e ((eInv.comp phiProd)
      (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a))) =
      phiProd (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) := by
    change e (e.symm (phiProd
      (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)))) = _
    exact e.apply_symm_apply _
  rw [heInv]
  funext i
  have hphiProd : phiProd
      (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) i =
      (phi i) (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) := rfl
  rw [hphiProd]
  simpa [proj] using hphi i a

/-- **Constructor from cyclic characters.**  The cyclic-character theorem is sufficient for
the full finite local-CFT supply.  For a map to an arbitrary finite `2`-group, first replace the
target by its commutative image and then use the preceding finite-product assembly. -/
def toFiniteTwoLocalReciprocitySupply (S : FiniteCyclicTwoReciprocitySupply B) :
    FiniteTwoLocalReciprocitySupply B where
  factor := by
    intro P _ _ _ _ hP f
    letI : CommGroup f.range :=
      MonoidHom.commGroupOfSurjective f.rangeRestrict f.rangeRestrict_surjective
    have hRange : IsPGroup 2 f.range := hP.to_subgroup f.range
    obtain ⟨psi, hpsi⟩ := S.factor_commutative f.range hRange f.rangeRestrict
    let incl : ContinuousMonoidHom f.range P :=
      ⟨f.range.subtype, continuous_subtype_val⟩
    refine ⟨incl.comp psi, fun a ↦ ?_⟩
    exact congrArg Subtype.val (hpsi a)

/-- Cyclic `2`-primary character compatibility already implies completed reciprocity
injectivity. -/
theorem completed_injective (S : FiniteCyclicTwoReciprocitySupply B) :
    Function.Injective (proTwoReciprocityToTopAb B) :=
  S.toFiniteTwoLocalReciprocitySupply.completed_injective

/-- **Regression theorem.**  Finite pro-`2` local reciprocity is exactly factorization of all
finite cyclic `2`-primary characters. -/
theorem iff_finiteTwoLocalReciprocitySupply :
    FiniteCyclicTwoReciprocitySupply B ↔ FiniteTwoLocalReciprocitySupply B :=
  ⟨toFiniteTwoLocalReciprocitySupply, ofFiniteTwoLocalReciprocitySupply⟩

end FiniteCyclicTwoReciprocitySupply

namespace FiniteTwoLocalReciprocitySupply

variable {B : MarkedRecip R K}

/-- Public constructor spelling from the finite cyclic character theorem. -/
def ofCyclicCharacters (S : FiniteCyclicTwoReciprocitySupply B) :
    FiniteTwoLocalReciprocitySupply B :=
  S.toFiniteTwoLocalReciprocitySupply

/-- Public regression spelling: the full supply and the cyclic-character supply are equivalent. -/
theorem iff_cyclicCharacters :
    FiniteTwoLocalReciprocitySupply B ↔ FiniteCyclicTwoReciprocitySupply B :=
  FiniteCyclicTwoReciprocitySupply.iff_finiteTwoLocalReciprocitySupply.symm

end FiniteTwoLocalReciprocitySupply

/-! ## What the current Kummer implementation actually supplies -/

open ContCoh

/-- The existing mod-`2` Kummer class as a multiplicative homomorphism. -/
def kummerClassKMonoidHom :
    (↥K)ˣ →* Multiplicative (H1 ↥(K.fixingSubgroup) (ZMod 2)) where
  toFun a := Multiplicative.ofAdd (kummerClassK K a)
  map_one' := by rw [kummerClassK_one]; rfl
  map_mul' a b := by rw [kummerClassK_mul]; rfl

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- The current Kummer homomorphism is surjective. -/
theorem kummerClassKMonoidHom_surjective :
    Function.Surjective (kummerClassKMonoidHom (K := K)) := by
  intro c
  obtain ⟨a, ha⟩ := kummerClassK_surjective K c.toAdd
  refine ⟨a, Multiplicative.toAdd.injective ?_⟩
  exact ha

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- Its kernel is exactly the square classes. -/
theorem kummerClassKMonoidHom_eq_one_iff (a : (↥K)ˣ) :
    kummerClassKMonoidHom (K := K) a = 1 ↔ IsSquare a := by
  constructor
  · intro ha
    have ha0 : kummerClassK K a = 0 := by
      exact Multiplicative.ofAdd.injective ha
    obtain ⟨w, hw⟩ := exists_sq_of_kummerClassK_eq_zero K a ha0
    have hw0 : w ≠ 0 := fun h0 ↦ a.ne_zero (by rw [← hw, h0]; simp)
    refine ⟨Units.mk0 w hw0, ?_⟩
    apply Units.ext
    simpa [sq] using hw.symm
  · rintro ⟨u, rfl⟩
    change Multiplicative.ofAdd (kummerClassK K (u * u)) = 1
    rw [kummerClassK_mul_self]
    rfl

/-- Every mod-`2` character of `Kˣ` descends uniquely through the Kummer surjection. -/
def modTwoCharacterOnKummer (f : (↥K)ˣ →* Multiplicative (ZMod 2)) :
    Multiplicative (H1 ↥(K.fixingSubgroup) (ZMod 2)) →* Multiplicative (ZMod 2) :=
  (kummerClassKMonoidHom (K := K)).liftOfSurjective
    kummerClassKMonoidHom_surjective ⟨f, by
      intro a ha
      rw [MonoidHom.mem_ker] at ha ⊢
      obtain ⟨u, rfl⟩ := (kummerClassKMonoidHom_eq_one_iff a).mp ha
      rw [map_mul]
      apply Multiplicative.toAdd.injective
      exact CharTwo.add_self_eq_zero _⟩

omit [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- Evaluation after descending a mod-`2` character through Kummer recovers the original
character on `Kˣ`. -/
@[simp] theorem modTwoCharacterOnKummer_kummerClassKMonoidHom
    (f : (↥K)ˣ →* Multiplicative (ZMod 2)) (a : (↥K)ˣ) :
    modTwoCharacterOnKummer (K := K) f (kummerClassKMonoidHom (K := K) a) = f a := by
  simp [modTwoCharacterOnKummer]

/-- The mod-`2` shadow of the required reciprocity compatibility.  This is a useful checkpoint,
but it is strictly only the first cyclic layer: the exact regression theorem above requires the
same factorization for every finite cyclic `2`-group. -/
def ModTwoReciprocityCharacterSupply (B : MarkedRecip R K) : Prop :=
  ∀ f : (↥K)ˣ →* Multiplicative (ZMod 2),
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K))) (Multiplicative (ZMod 2)),
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a

/-- The same first-layer requirement expressed on the Kummer side: every functional on
`H¹(G_K, 𝔽₂)` is evaluation of a continuous character of `(G_K(2))^ab` along `rec_K`.

Local Tate duality supplies the abstract dual of `H¹`; the missing compatibility is the
identity asserting that its cup/Kummer character agrees with evaluation on `B.recip a`. -/
def ModTwoKummerReciprocitySupply (B : MarkedRecip R K) : Prop :=
  ∀ ell : Multiplicative (H1 ↥(K.fixingSubgroup) (ZMod 2)) →*
      Multiplicative (ZMod 2),
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K))) (Multiplicative (ZMod 2)),
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) =
          ell (kummerClassKMonoidHom (K := K) a)

/-- **Mod-`2` Kummer regression.**  Because the current Kummer map is a surjection with square
kernel, its reciprocity-compatibility formulation is exactly factorization of all mod-`2`
characters of `Kˣ`. -/
theorem modTwoReciprocityCharacterSupply_iff_kummer (B : MarkedRecip R K) :
    ModTwoReciprocityCharacterSupply B ↔ ModTwoKummerReciprocitySupply B := by
  constructor
  · intro S ell
    exact S (ell.comp (kummerClassKMonoidHom (K := K)))
  · intro S f
    obtain ⟨phi, hphi⟩ := S (modTwoCharacterOnKummer (K := K) f)
    refine ⟨phi, fun a ↦ ?_⟩
    rw [hphi a, modTwoCharacterOnKummer_kummerClassKMonoidHom]

/-- Any full cyclic-character supply has the mod-`2` shadow. -/
theorem FiniteCyclicTwoReciprocitySupply.modTwo
    {B : MarkedRecip R K} (S : FiniteCyclicTwoReciprocitySupply B) :
    ModTwoReciprocityCharacterSupply B := by
  intro f
  exact S.factor (Multiplicative (ZMod 2))
    (IsPGroup.of_card (n := 1) (by simp)) inferInstance f

end

end GQ2.Dyadic
