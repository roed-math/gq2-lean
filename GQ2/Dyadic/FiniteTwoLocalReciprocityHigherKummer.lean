/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FiniteTwoLocalReciprocityTateKummer

/-!
# The higher Kummer boundary for finite pro-2 reciprocity

This file separates the completed local-reciprocity argument into its exact `2^m` layers.
There are two parts.

* `TwoPowerReciprocityCharacterSupply` asks for factorization only into the standard cyclic
  groups `Multiplicative (ZMod (2 ^ m))`.  It is proved equivalent to the abstract cyclic
  supply and hence to the full finite `2`-group supply.
* `HigherKummerClassData` and `HigherTateKummerArtinCompatibility` state precisely what a
  higher Kummer sequence and the Artin/Hilbert formula must provide at one exponent `n`.
  B6's existing `perfect11` field, applied to `M = MuN n`, then produces the required
  factorization at that exponent.

The use of `M = MuN n` is important.  It asks B6 for

`H¹(G_K, MuDual n (MuN n)) ≃ Hom(H¹(G_K, MuN n), ZMod n)`,

so no unproved transposed-perfectness assertion is inserted.  The compatibility proposition
  directly assigns the resulting `Hom(μ_n, μ_n)` class its continuous scalar Galois character and
states the Artin formula.

The first missing implementation API is therefore sharp: the repository has no higher Kummer
homomorphism `Kˣ → H¹(G_K, μ_n)`, with surjectivity and `n`th-power kernel.  It also has no
generic equivariant coefficient identification `MuDual n (MuN n) ≃ ZMod n` from which the
scalar character in the Artin formula could be constructed.  Both are parameters below, not
new axioms.  At `n = 2`, the earlier file remains the concrete regression using the existing
mod-2 Kummer implementation.
-/

namespace GQ2.Dyadic

open ContCoh

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/- The Kummer API is pinned to `K.fixingSubgroup`, while the dyadic reciprocity API names the
definitionally equal type `GalK K`.  Re-export the two topological properties across that
instance firewall for the higher coefficient constructions below. -/
noncomputable local instance instCompactSpaceFixingSubgroupHigher :
    CompactSpace ↥(K.fixingSubgroup) :=
  inferInstanceAs (CompactSpace (GalK K))

noncomputable local instance instTotallyDisconnectedSpaceFixingSubgroupHigher :
    TotallyDisconnectedSpace ↥(K.fixingSubgroup) :=
  inferInstanceAs (TotallyDisconnectedSpace (GalK K))

/-! ## Exact replacement of abstract cyclic targets by the standard `2^m` targets -/

/-- Factorization of every character with standard cyclic target `Z/2^m`. -/
def TwoPowerReciprocityCharacterSupply (B : MarkedRecip R K) : Prop :=
  ∀ (m : ℕ) (f : (↥K)ˣ →* Multiplicative (ZMod (2 ^ m))),
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K)))
          (Multiplicative (ZMod (2 ^ m))),
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a

namespace TwoPowerReciprocityCharacterSupply

variable {B : MarkedRecip R K}

/-- The abstract cyclic supply restricts to each standard `2^m` target. -/
theorem ofFiniteCyclicTwoReciprocitySupply
    (S : FiniteCyclicTwoReciprocitySupply B) :
    TwoPowerReciprocityCharacterSupply B := by
  intro m f
  exact S.factor (Multiplicative (ZMod (2 ^ m)))
    (IsPGroup.of_card (n := m) (by simp)) inferInstance f

/-- Standard `2^m` targets suffice for every abstract finite cyclic `2`-group. -/
theorem toFiniteCyclicTwoReciprocitySupply
    (S : TwoPowerReciprocityCharacterSupply B) :
    FiniteCyclicTwoReciprocitySupply B := by
  refine ⟨?_⟩
  intro C _ _ _ _ hC hcyc f
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card.mp hC)
  let e0 : Multiplicative (ZMod (Nat.card C)) ≃* C :=
    zmodCyclicMulEquiv hcyc
  let e : Multiplicative (ZMod (2 ^ m)) ≃* C := by
    rw [← hm]
    exact e0
  obtain ⟨psi, hpsi⟩ := S m (e.symm.toMonoidHom.comp f)
  let eCont : ContinuousMonoidHom (Multiplicative (ZMod (2 ^ m))) C :=
    ⟨e.toMonoidHom, continuous_of_discreteTopology⟩
  refine ⟨eCont.comp psi, fun a ↦ ?_⟩
  change e (psi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a))) = f a
  rw [hpsi a]
  simp [e]

/-- **All-layer regression.**  Quantifying over the standard groups `Z/2^m` loses no
information compared with quantifying over arbitrary finite cyclic `2`-groups. -/
theorem iff_finiteCyclicTwoReciprocitySupply :
    TwoPowerReciprocityCharacterSupply B ↔ FiniteCyclicTwoReciprocitySupply B :=
  ⟨toFiniteCyclicTwoReciprocitySupply, ofFiniteCyclicTwoReciprocitySupply⟩

/-- Consequently the standard `2^m` character theorem is exactly the full finite local-CFT
factorization supply. -/
theorem iff_finiteTwoLocalReciprocitySupply :
    TwoPowerReciprocityCharacterSupply B ↔ FiniteTwoLocalReciprocitySupply B :=
  iff_finiteCyclicTwoReciprocitySupply.trans
    FiniteCyclicTwoReciprocitySupply.iff_finiteTwoLocalReciprocitySupply

/-- All standard cyclic layers imply injectivity of completed reciprocity. -/
theorem completed_injective (S : TwoPowerReciprocityCharacterSupply B) :
    Function.Injective (proTwoReciprocityToTopAb B) :=
  (toFiniteCyclicTwoReciprocitySupply S).completed_injective

/-- **`m = 1` regression.**  The all-power theorem contains exactly the existing mod-`2`
character supply as its first nontrivial layer. -/
theorem modTwo (S : TwoPowerReciprocityCharacterSupply B) :
    ModTwoReciprocityCharacterSupply B :=
  S 1

end TwoPowerReciprocityCharacterSupply

/-! ## The honest higher Kummer input at one exponent -/

/-- The algebraic data supplied by the degree-one Kummer sequence at exponent `n`.

The kernel is stated on units, so `eq_one_iff` says exactly
`ker(κ_n) = (Kˣ)^n`.  Together with `surjective`, this is the usual isomorphism
`Kˣ/(Kˣ)^n ≃ H¹(G_K, μ_n)`. -/
structure HigherKummerClassData (K : IntermediateField ℚ_[2] ℚbar2) (n : ℕ)
    [NeZero n] where
  kummer : (↥K)ˣ →* Multiplicative (H1 ↥(K.fixingSubgroup) (MuN n))
  surjective : Function.Surjective kummer
  eq_one_iff : ∀ a : (↥K)ˣ, kummer a = 1 ↔ ∃ b : (↥K)ˣ, b ^ n = a

namespace HigherKummerClassData

variable {n : ℕ} [NeZero n]

/-- Every `Z/n`-valued character of `Kˣ` descends through higher Kummer. -/
def characterOnKummer (κ : HigherKummerClassData K n)
    (f : (↥K)ˣ →* Multiplicative (ZMod n)) :
    Multiplicative (H1 ↥(K.fixingSubgroup) (MuN n)) →* Multiplicative (ZMod n) :=
  κ.kummer.liftOfSurjective κ.surjective ⟨f, by
    intro a ha
    rw [MonoidHom.mem_ker] at ha ⊢
    obtain ⟨b, rfl⟩ := (κ.eq_one_iff a).mp ha
    rw [map_pow]
    apply Multiplicative.toAdd.injective
    change n • Multiplicative.toAdd (f b) = 0
    simp⟩

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
@[simp] theorem characterOnKummer_kummer
    (κ : HigherKummerClassData K n)
    (f : (↥K)ˣ →* Multiplicative (ZMod n)) (a : (↥K)ˣ) :
    κ.characterOnKummer f (κ.kummer a) = f a := by
  simp [characterOnKummer]

end HigherKummerClassData

/-- **Concrete first-layer regression.**  The repository's existing mod-2 Kummer class,
transported along `ZMod 2 ≃ μ₂`, already supplies `HigherKummerClassData K 2`.  Thus the new
interface does not move the known first obstruction backwards. -/
noncomputable def modTwoHigherKummerClassData : HigherKummerClassData K 2 where
  kummer :=
    (H1congr (G := ↥(K.fixingSubgroup)) LocalLiftingDuality.muNTwoEquiv.symm
      (FieldData.muNTwoEquiv_symm_equivariant K)).toAddMonoidHom.toMultiplicative.comp
        (kummerClassKMonoidHom (K := K))
  surjective := by
    intro y
    let e := H1congr (G := ↥(K.fixingSubgroup)) LocalLiftingDuality.muNTwoEquiv.symm
      (FieldData.muNTwoEquiv_symm_equivariant K)
    obtain ⟨x, hx⟩ := e.surjective y.toAdd
    obtain ⟨a, ha⟩ := kummerClassKMonoidHom_surjective (K := K) (Multiplicative.ofAdd x)
    refine ⟨a, Multiplicative.toAdd.injective ?_⟩
    change e (kummerClassK K a) = y.toAdd
    rw [← hx]
    exact congrArg e (congrArg Multiplicative.toAdd ha)
  eq_one_iff := by
    intro a
    let e := H1congr (G := ↥(K.fixingSubgroup)) LocalLiftingDuality.muNTwoEquiv.symm
      (FieldData.muNTwoEquiv_symm_equivariant K)
    constructor
    · intro ha
      have he0 : e (kummerClassK K a) = 0 := by
        exact Multiplicative.ofAdd.injective ha
      have hk0 : kummerClassK K a = 0 := by
        apply e.injective
        rw [map_zero]
        exact he0
      have hka : kummerClassKMonoidHom (K := K) a = 1 :=
        Multiplicative.ofAdd.injective hk0
      obtain ⟨u, hu⟩ := (kummerClassKMonoidHom_eq_one_iff a).mp hka
      exact ⟨u, by simpa [pow_two] using hu.symm⟩
    · rintro ⟨u, rfl⟩
      change Multiplicative.ofAdd (e (kummerClassK K (u ^ 2))) = 1
      rw [show u ^ 2 = u * u by simp [pow_two], kummerClassK_mul_self]
      rw [map_zero]
      rfl

/-! ## B6 plus the higher Artin formula -/

/-- B6 at `G_K` and arbitrary exponent.  The earlier `FieldData.tateDualityGalK` is the
specialized `n = 2` spelling; the underlying axiom and local-dualizing-group theorem are
already uniform in `n`. -/
noncomputable def tateDualityGalKAt (K : IntermediateField ℚ_[2] ℚbar2)
    [FiniteDimensional ℚ_[2] K] (n : ℕ) [NeZero n] :
    TateDualityG ↥(K.fixingSubgroup) n :=
  tateDualityAt ↥(K.fixingSubgroup) n (FieldData.galK_isLocalDualizingGroup K n)

/-- Convert a multiplicative functional on higher Kummer cohomology into additive notation. -/
def higherKummerFunctionalToAdd {n : ℕ} [NeZero n]
    (ell : Multiplicative (H1 ↥(K.fixingSubgroup) (MuN n)) →* Multiplicative (ZMod n)) :
    H1 ↥(K.fixingSubgroup) (MuN n) →+ ZMod n where
  toFun x := Multiplicative.toAdd (ell (Multiplicative.ofAdd x))
  map_zero' := congrArg Multiplicative.toAdd (map_one ell)
  map_add' x y := congrArg Multiplicative.toAdd
    (map_mul ell (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

/-- **Higher Tate--Kummer--Artin compatibility at exponent `n`.**

For every class in the B6 Tate-dual slot `Hom(μ_n, μ_n)`, this proposition supplies its scalar continuous
character on `G_K(2)^ab` and identifies evaluation on the marked Artin symbol with the local
Tate pairing against the higher Kummer class.

The existential character is deliberate.  A future coefficient API
`MuDual n (MuN n) ≃+ ZMod n`, with equivariance and the trivial scalar action, should construct
it canonically.  The present repository contains that bridge only in special mod-2 forms. -/
def HigherTateKummerArtinCompatibilityAt
    (B : MarkedRecip R K) {n : ℕ} [NeZero n]
    (D : TateDualityG ↥(K.fixingSubgroup) n) (κ : HigherKummerClassData K n) : Prop :=
  ∀ c : H1 ↥(K.fixingSubgroup) (MuDual n (MuN n)),
    ∃ chi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K)))
          (Multiplicative (ZMod n)),
      ∀ a : (↥K)ˣ,
        chi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) =
          Multiplicative.ofAdd
            (D.inv (cup11 (muDualPairing n (MuN n))
              (muDualPairing_equivariant n (MuN n)) c (κ.kummer a).toAdd))

/-! ### The coefficient bridge immediately below Artin compatibility -/

/-- A scalar cohomology class with trivial action is canonically a continuous character of
`G_K`.  This is the arbitrary-coefficient version of `h1GalKCharacter`. -/
def h1GalKCharacterOfTrivial {A : Type*} [AddCommGroup A] [TopologicalSpace A]
    [DiscreteTopology A] [DistribMulAction ↥(K.fixingSubgroup) A]
    [ContinuousSMul ↥(K.fixingSubgroup) A]
    (htriv : ∀ (g : ↥(K.fixingSubgroup)) (a : A), g • a = a)
    (x : H1 ↥(K.fixingSubgroup) A) :
    ContinuousMonoidHom ↥(K.fixingSubgroup) (Multiplicative A) := by
  let z : Z1 ↥(K.fixingSubgroup) A := H1equivZ1OfTrivial htriv x
  exact
    { toFun := fun g => Multiplicative.ofAdd (z.1 g)
      map_one' := congrArg Multiplicative.ofAdd (Z1_apply_one z)
      map_mul' := fun g h => congrArg Multiplicative.ofAdd
        (((mem_Z1_iff_of_trivial htriv).mp z.2).2 g h)
      continuous_toFun := ((mem_Z1_iff_of_trivial htriv).mp z.2).1 }

/-- `Multiplicative (ZMod (2^m))` is pro-`2`. -/
theorem isProPTwo_multiplicativeZMod_twoPow (m : ℕ) :
    IsProP 2 (Multiplicative (ZMod (2 ^ m))) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := m) (by simp))

/-- Descend a `Z/2^m`-valued cohomology character through `G_K(2)^ab`. -/
def h1GalKMaxProTwoAbCharacterAt
    (m : ℕ) [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    (htriv : ∀ (g : ↥(K.fixingSubgroup)) (a : ZMod (2 ^ m)), g • a = a)
    (x : H1 ↥(K.fixingSubgroup) (ZMod (2 ^ m))) :
    ContinuousMonoidHom
      (topAbelianization (maxProPQuotient 2 ↥(K.fixingSubgroup)))
        (Multiplicative (ZMod (2 ^ m))) :=
  SectionThree.abLiftG
    ((maxProPHomEquiv (isProPTwo_multiplicativeZMod_twoPow m)).symm
      (h1GalKCharacterOfTrivial (K := K) htriv x))

/-- The still-missing coefficient API at exponent `2^m`: the Tate dual
`MuDual (2^m) (MuN (2^m)) = Hom(μ_(2^m), μ_(2^m))` is the trivial scalar module
`Z/2^m`, equivariantly.

Mathematically this is the scalar-endomorphism identification for the cyclic group of roots
of unity.  It is
kept separate from the Kummer sequence and the Artin formula because the current repository
implements neither this generic equivalence nor the required equivariance. -/
structure HigherMuNDualScalarization
    (K : IntermediateField ℚ_[2] ℚbar2) (m : ℕ)
    [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))] where
  equiv : MuDual (2 ^ m) (MuN (2 ^ m)) ≃+ ZMod (2 ^ m)
  equivariant : ∀ (g : ↥(K.fixingSubgroup)) (x : MuDual (2 ^ m) (MuN (2 ^ m))),
    equiv (g • x) = g • equiv x
  smul_trivial : ∀ (g : ↥(K.fixingSubgroup)) (a : ZMod (2 ^ m)), g • a = a

/-- The scalar character attached to a Tate-dual `Hom(μ_n, μ_n)` cohomology class, assuming
the explicit coefficient bridge above. -/
def higherTateDualCharacter
    (m : ℕ) [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    (S : HigherMuNDualScalarization K m)
    (c : H1 ↥(K.fixingSubgroup) (MuDual (2 ^ m) (MuN (2 ^ m)))) :
    ContinuousMonoidHom
      (topAbelianization (maxProPQuotient 2 ↥(K.fixingSubgroup)))
        (Multiplicative (ZMod (2 ^ m))) :=
  h1GalKMaxProTwoAbCharacterAt m S.smul_trivial
    (H1congr S.equiv S.equivariant c)

/-- Pointwise Artin/Hilbert formula after choosing the explicit Tate-dual scalarization. -/
def HigherTateKummerArtinFormulaWithScalarization
    (B : MarkedRecip R K) (m : ℕ)
    [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    (D : TateDualityG ↥(K.fixingSubgroup) (2 ^ m))
    (κ : HigherKummerClassData K (2 ^ m))
    (S : HigherMuNDualScalarization K m) : Prop :=
  ∀ (c : H1 ↥(K.fixingSubgroup) (MuDual (2 ^ m) (MuN (2 ^ m)))) (a : (↥K)ˣ),
    higherTateDualCharacter (K := K) m S c
        (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) =
      Multiplicative.ofAdd
        (D.inv (cup11 (muDualPairing (2 ^ m) (MuN (2 ^ m)))
          (muDualPairing_equivariant (2 ^ m) (MuN (2 ^ m))) c (κ.kummer a).toAdd))

/-- An explicit equivariant Tate-dual scalarization plus its pointwise Artin formula supplies the
abstract compatibility used by the closure theorem. -/
theorem HigherTateKummerArtinFormulaWithScalarization.toCompatibilityAt
    {B : MarkedRecip R K} (m : ℕ)
    [DistribMulAction ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    [ContinuousSMul ↥(K.fixingSubgroup) (ZMod (2 ^ m))]
    {D : TateDualityG ↥(K.fixingSubgroup) (2 ^ m)}
    {κ : HigherKummerClassData K (2 ^ m)}
    {S : HigherMuNDualScalarization K m}
    (H : HigherTateKummerArtinFormulaWithScalarization B m D κ S) :
    HigherTateKummerArtinCompatibilityAt B D κ := by
  intro c
  exact ⟨higherTateDualCharacter (K := K) m S c, H c⟩

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)]
  [TotallyDisconnectedSpace (GalK K)] in
/-- B6 represents every functional on higher Kummer cohomology by a class in its canonical
`Hom(μ_n, μ_n)` slot.  This is exactly the existing orientation of `perfect11`; no transpose
or cardinality theorem is assumed. -/
theorem exists_tateKummer_row_eq_higherKummerFunctional
    {n : ℕ} [NeZero n] (D : TateDualityG ↥(K.fixingSubgroup) n)
    (ell : Multiplicative (H1 ↥(K.fixingSubgroup) (MuN n)) →* Multiplicative (ZMod n)) :
    ∃ c : H1 ↥(K.fixingSubgroup) (MuDual n (MuN n)), ∀ y,
      D.inv (cup11 (muDualPairing n (MuN n))
        (muDualPairing_equivariant n (MuN n)) c y) =
        higherKummerFunctionalToAdd (K := K) ell y := by
  obtain ⟨c, hc⟩ := (D.perfect11 (MuN n) (nsmul_muN_eq_zero n)).2
    (higherKummerFunctionalToAdd (K := K) ell)
  refine ⟨c, fun y ↦ ?_⟩
  exact DFunLike.congr_fun hc y

/-- **One-exponent closure theorem.**  Higher Kummer exactness, B6 perfectness, and the
pointwise higher Artin formula factor every `Z/n`-valued character through `G_K(2)^ab`. -/
theorem higherKummer_tate_artin_factor
    {B : MarkedRecip R K} {n : ℕ} [NeZero n]
    (D : TateDualityG ↥(K.fixingSubgroup) n) (κ : HigherKummerClassData K n)
    (H : HigherTateKummerArtinCompatibilityAt B D κ)
    (f : (↥K)ˣ →* Multiplicative (ZMod n)) :
    ∃ phi : ContinuousMonoidHom
        (topAbelianization (maxProPQuotient 2 (GalK K)))
          (Multiplicative (ZMod n)),
      ∀ a : (↥K)ˣ,
        phi (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = f a := by
  let ell := κ.characterOnKummer f
  obtain ⟨c, hc⟩ :=
    exists_tateKummer_row_eq_higherKummerFunctional (K := K) D ell
  obtain ⟨chi, hchi⟩ := H c
  refine ⟨chi, fun a ↦ ?_⟩
  rw [hchi a]
  apply Multiplicative.toAdd.injective
  change D.inv (cup11 (muDualPairing n (MuN n))
      (muDualPairing_equivariant n (MuN n)) c (κ.kummer a).toAdd) =
    Multiplicative.toAdd (f a)
  rw [hc]
  exact congrArg Multiplicative.toAdd (κ.characterOnKummer_kummer f a)

/-- The all-exponent higher Kummer and Artin formulas produce every standard `2^m` layer. -/
theorem twoPowerReciprocityCharacterSupply_of_higherKummer_tate_artin
    {B : MarkedRecip R K}
    (H : ∀ m : ℕ,
      ∃ (κ : HigherKummerClassData K (2 ^ m))
        (D : TateDualityG ↥(K.fixingSubgroup) (2 ^ m)),
        HigherTateKummerArtinCompatibilityAt B D κ) :
    TwoPowerReciprocityCharacterSupply B := by
  intro m f
  obtain ⟨κ, D, hcompat⟩ := H m
  exact higherKummer_tate_artin_factor D κ hcompat f

/-- Canonical B6 spelling of the all-layer reduction.  Tate duality itself is not additional
input: `tateDualityGalKAt` constructs it from the repository's existing B6 axiom at every
`2^m`.  Only higher Kummer and the Artin formula remain as hypotheses. -/
theorem twoPowerReciprocityCharacterSupply_of_canonical_higherKummer_artin
    {B : MarkedRecip R K}
    (H : ∀ m : ℕ, ∃ κ : HigherKummerClassData K (2 ^ m),
      HigherTateKummerArtinCompatibilityAt B (tateDualityGalKAt K (2 ^ m)) κ) :
    TwoPowerReciprocityCharacterSupply B := by
  apply twoPowerReciprocityCharacterSupply_of_higherKummer_tate_artin
  intro m
  obtain ⟨κ, hκ⟩ := H m
  exact ⟨κ, tateDualityGalKAt K (2 ^ m), hκ⟩

/-- **Campaign closure.**  The all-`2^m` higher Kummer/Artin boundary implies the full finite
`2`-group reciprocity supply. -/
theorem finiteTwoLocalReciprocitySupply_of_higherKummer_tate_artin
    {B : MarkedRecip R K}
    (H : ∀ m : ℕ,
      ∃ (κ : HigherKummerClassData K (2 ^ m))
        (D : TateDualityG ↥(K.fixingSubgroup) (2 ^ m)),
        HigherTateKummerArtinCompatibilityAt B D κ) :
    FiniteTwoLocalReciprocitySupply B :=
  TwoPowerReciprocityCharacterSupply.iff_finiteTwoLocalReciprocitySupply.mp
    (twoPowerReciprocityCharacterSupply_of_higherKummer_tate_artin H)

/-- In particular, the all-layer higher Kummer/Artin theorem proves injectivity of completed
reciprocity. -/
theorem completed_reciprocity_injective_of_higherKummer_tate_artin
    {B : MarkedRecip R K}
    (H : ∀ m : ℕ,
      ∃ (κ : HigherKummerClassData K (2 ^ m))
        (D : TateDualityG ↥(K.fixingSubgroup) (2 ^ m)),
        HigherTateKummerArtinCompatibilityAt B D κ) :
    Function.Injective (proTwoReciprocityToTopAb B) :=
  (twoPowerReciprocityCharacterSupply_of_higherKummer_tate_artin H).completed_injective

/-- Canonical-B6 campaign closure directly to completed reciprocity injectivity. -/
theorem completed_reciprocity_injective_of_canonical_higherKummer_artin
    {B : MarkedRecip R K}
    (H : ∀ m : ℕ, ∃ κ : HigherKummerClassData K (2 ^ m),
      HigherTateKummerArtinCompatibilityAt B (tateDualityGalKAt K (2 ^ m)) κ) :
    Function.Injective (proTwoReciprocityToTopAb B) :=
  (twoPowerReciprocityCharacterSupply_of_canonical_higherKummer_artin H).completed_injective

/-! The preceding all-layer assumptions are not new axioms: they are ordinary theorem
parameters.  B6 itself is already available uniformly in `m` as

`tateDualityAt (GalK K) (2 ^ m) (FieldData.galK_isLocalDualizingGroup K (2 ^ m))`.

Thus the unfinished work is exactly construction of `HigherKummerClassData` and proof of
`HigherTateKummerArtinCompatibilityAt` (or, one layer below it, the missing equivariant
endomorphism/scalar coefficient bridge and the standard Artin/Hilbert formula). -/

#print axioms TwoPowerReciprocityCharacterSupply.iff_finiteTwoLocalReciprocitySupply
#print axioms exists_tateKummer_row_eq_higherKummerFunctional
#print axioms finiteTwoLocalReciprocitySupply_of_higherKummer_tate_artin
#print axioms modTwoHigherKummerClassData
#print axioms completed_reciprocity_injective_of_canonical_higherKummer_artin

end


end GQ2.Dyadic
