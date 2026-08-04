/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageFieldLabuteFinite
import GQ2.Roe.Labute.SpanFoundation

/-!
# The reverse finite-quotient boundary for the square Labute presentation

The finite-level square presentation currently asks for a continuous epimorphism from the
arithmetic group onto every finite quotient of `DSq h`.  This file reduces that apparently
large family to the canonical two-central tower.  It then shows that, once the already-built
forward epimorphism `DSq h → G` is available, equality of the orders of the two level quotients
is enough to construct the reverse epimorphism at that level.

Thus the reverse direction does not require a second generator-and-relator construction.  Its
remaining content is the numerical statement that the forward map loses no elements at every
two-central level.  This is the form naturally approachable by a graded Lie or finite-stage
Labute calculation.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 GQ2.Roe.Labute ContCoh

variable {h : ℕ}

/-! ## The exact cofinal-tower reduction -/

/-- Reverse epimorphisms only at the canonical two-central quotients of `DSq h`. -/
def SqReverseTwoCentralLevelSurjections
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ, Nonempty (ContSurj G (levelQuot (SqCore.DSq h : Type) k))

/-- Reverse epimorphisms onto all open-normal quotients of `DSq h`. -/
def SqReverseFiniteQuotientSurjections
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ V : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
    Nonempty (ContSurj G ((SqCore.DSq h : Type) ⧸ V.toSubgroup))

/-- Every two-central subgroup of `DSq h` is an open normal subgroup. -/
noncomputable def dsqTwoCentralOpenNormal (h k : ℕ) :
    OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)) where
  toSubgroup := twoCentralSeries (SqCore.DSq h : Type) k
  isOpen' := isOpen_twoCentralSeries (SqCore.DSq h : Type)
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h) k

@[simp] theorem dsqTwoCentralOpenNormal_toSubgroup (h k : ℕ) :
    (dsqTwoCentralOpenNormal h k).toSubgroup =
      twoCentralSeries (SqCore.DSq h : Type) k :=
  rfl

/-- The tower condition is exactly equivalent to the original reverse finite-quotient
condition.  Cofinality of the two-central series supplies the nontrivial implication. -/
theorem sqReverseFiniteQuotientSurjections_iff_twoCentralLevel
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (h : ℕ) :
    SqReverseFiniteQuotientSurjections G h ↔
      SqReverseTwoCentralLevelSurjections G h := by
  constructor
  · intro hall k
    change Nonempty (ContSurj G
      ((SqCore.DSq h : Type) ⧸ twoCentralSeries (SqCore.DSq h : Type) k))
    exact hall (dsqTwoCentralOpenNormal h k)
  · intro htower V
    obtain ⟨k, hk⟩ := exists_twoCentralSeries_le (SqCore.DSq h : Type)
      (dsqFinsetTopGen h) (SqCore.isProP_DSq h) V.isOpen'
    letI : DiscreteTopology
        ((SqCore.DSq h : Type) ⧸ twoCentralSeries (SqCore.DSq h : Type) k) :=
      QuotientGroup.discreteTopology
        (isOpen_twoCentralSeries (SqCore.DSq h : Type) (dsqFinsetTopGen h)
          (SqCore.isProP_DSq h) k)
    obtain ⟨⟨f, hf⟩⟩ := htower k
    exact ⟨⟨(projMap hk).comp f, (projMap_surjective hk).comp hf⟩⟩

/-! ## Functoriality on the two-central tower -/

/-- A continuous homomorphism induces a continuous homomorphism on every two-central level. -/
noncomputable def twoCentralLevelMap
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (k : ℕ) :
    ContinuousMonoidHom (levelQuot P k) (levelQuot Q k) := by
  let q : ContinuousMonoidHom P (levelQuot Q k) :=
    ⟨(levelMk Q k).comp f.toMonoidHom,
      (continuous_levelMk Q k).comp f.continuous_toFun⟩
  exact quotientLift (twoCentralSeries P k) q fun x hx ↦ by
    rw [MonoidHom.mem_ker]
    exact (QuotientGroup.eq_one_iff _).mpr
      (map_twoCentralSeries_le f.toMonoidHom f.continuous_toFun k ⟨x, hx, rfl⟩)

@[simp] theorem twoCentralLevelMap_levelMk
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (k : ℕ) (x : P) :
    twoCentralLevelMap f k (levelMk P k x) = levelMk Q k (f x) :=
  rfl

/-- An epimorphism remains an epimorphism on every two-central quotient. -/
theorem twoCentralLevelMap_surjective
    {P Q : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    (f : ContinuousMonoidHom P Q) (hf : Function.Surjective f) (k : ℕ) :
    Function.Surjective (twoCentralLevelMap f k) := by
  intro y
  obtain ⟨q, rfl⟩ := levelMk_surjective Q k y
  obtain ⟨p, rfl⟩ := hf q
  exact ⟨levelMk P k p, rfl⟩

/-! ## The cardinality endpoint -/

/-- Equality of the finite two-central quotient orders is the numerical reverse input. -/
def SqTwoCentralLevelCardAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ,
    Nat.card (levelQuot (SqCore.DSq h : Type) k) = Nat.card (levelQuot G k)

/-- Equality of the orders of the successive graded pieces
`λₖ / λₖ₊₁`.  This is the weakest purely numerical associated-graded input needed below:
it remembers no chosen basis and no bracket, restricted-power, or orientation structure. -/
def SqTwoCentralLayerCardAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (h : ℕ) : Prop :=
  ∀ k : ℕ,
    Nat.card (zLayer (SqCore.DSq h : Type) k) = Nat.card (zLayer G k)

/-! ## The first graded layer and continuous mod-`2` characters -/

/-- The first interesting layer is the whole level-two quotient:
`Z₁ = λ₁/λ₂ = G/λ₂`.  (The formal layer `Z₀` is the junk-convention
quotient `λ₀/λ₁ = 1`.) -/
theorem zLayer_one_eq_top
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    zLayer G 1 = ⊤ := by
  change (twoCentralSeries G 1).map (levelMk G 2) = ⊤
  rw [twoCentralSeries_one, Subgroup.map_top_of_surjective _ (levelMk_surjective G 2)]

/-- Every continuous mod-`2` character kills squares and commutators, hence kills `λ₂`. -/
theorem twoCentralSeries_two_le_continuousCharacter_ker
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (c : ContinuousMonoidHom G (Multiplicative (ZMod 2))) :
    twoCentralSeries G 2 ≤ c.toMonoidHom.ker := by
  rw [twoCentralSeries_succ G (by omega), twoCentralSucc]
  refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) ?_
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨v, -, rfl⟩
    change v ^ 2 ∈ c.toMonoidHom.ker
    rw [MonoidHom.mem_ker, map_pow]
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, two_nsmul, Count.zmod2_add_self]
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
  · have hset : (c.toMonoidHom.ker : Set G) = c ⁻¹' {1} := by
      ext g
      simp [MonoidHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage c.continuous_toFun isClosed_singleton

/-- Restriction along `G → G/λ₂` is an equivalence on continuous mod-`2` characters. -/
noncomputable def continuousCharacterLevelTwoEquiv
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    ContinuousMonoidHom (levelQuot G 2) (Multiplicative (ZMod 2)) ≃
      ContinuousMonoidHom G (Multiplicative (ZMod 2)) where
  toFun f := f.comp ⟨levelMk G 2, continuous_levelMk G 2⟩
  invFun c := quotientLift (twoCentralSeries G 2) c
    (twoCentralSeries_two_le_continuousCharacter_ker c)
  left_inv f := by
    ext q
    obtain ⟨g, rfl⟩ := levelMk_surjective G 2 q
    rfl
  right_inv c := by
    ext g
    rfl

/-- On a discrete group, multiplicative mod-`2` characters are additive homomorphisms out of
the additive spelling of that group. -/
def continuousCharacterEquivAddHom
    (A : Type) [Group A] [TopologicalSpace A] [DiscreteTopology A] :
    ContinuousMonoidHom A (Multiplicative (ZMod 2)) ≃ (Additive A →+ ZMod 2) where
  toFun f :=
    { toFun := fun a => Multiplicative.toAdd (f a.toMul)
      map_zero' := congrArg Multiplicative.toAdd f.map_one
      map_add' := fun a b => congrArg Multiplicative.toAdd (f.map_mul a.toMul b.toMul) }
  invFun f :=
    { toFun := fun a => Multiplicative.ofAdd (f (Additive.ofMul a))
      map_one' := congrArg Multiplicative.ofAdd f.map_zero
      map_mul' := fun a b =>
        congrArg Multiplicative.ofAdd (f.map_add (Additive.ofMul a) (Additive.ofMul b))
      continuous_toFun := continuous_of_discreteTopology }
  left_inv _ := rfl
  right_inv _ := rfl

/-- **Frattini/character cardinal bridge.**  For a finitely generated pro-`2` group, the
number of continuous mod-`2` characters is exactly the order of `Z₁ = λ₁/λ₂`.
This is finite elementary-abelian duality after factoring every character through `G/λ₂`. -/
theorem card_continuousCharacter_eq_card_zLayer_one
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    Nat.card (ContinuousMonoidHom G (Multiplicative (ZMod 2))) =
      Nat.card (zLayer G 1) := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : Finite Q := finite_levelQuot G hfg hpro 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := fun a b => by
        have ha : a ∈ zLayer G 1 := by rw [zLayer_one_eq_top]; trivial
        exact (Subgroup.mem_center_iff.mp (zLayer_le_center G 1 ha) b).symm }
  have htwo : ∀ a : Additive Q, a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    rw [← pow_two]
    exact zLayer_sq G (by rw [zLayer_one_eq_top]; trivial)
  calc
    Nat.card (ContinuousMonoidHom G (Multiplicative (ZMod 2))) =
        Nat.card (ContinuousMonoidHom Q (Multiplicative (ZMod 2))) :=
      Nat.card_congr (continuousCharacterLevelTwoEquiv G).symm
    _ = Nat.card (Additive Q →+ ZMod 2) :=
      Nat.card_congr (continuousCharacterEquivAddHom Q)
    _ = Nat.card (Additive Q) := QuadraticFp2.card_addHom_zmod2 _ htwo
    _ = Nat.card Q := Nat.card_congr Additive.toMul
    _ = Nat.card (zLayer G 1) := by
      rw [zLayer_one_eq_top]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm

/-- **Frattini/`H¹` bridge.**  With the (unique) scalar action on `𝔽₂`, the first
two-central layer has the same cardinality as continuous `H¹`. -/
theorem card_H1_zmodTwo_eq_card_zLayer_one
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    Nat.card (H1 G (ZMod 2)) = Nat.card (zLayer G 1) := by
  calc
    Nat.card (H1 G (ZMod 2)) = Nat.card (Z1 G (ZMod 2)) :=
      Nat.card_congr (H1equivZ1OfTrivial Count.smul_zmod2).toEquiv
    _ = Nat.card (ContinuousMonoidHom G (Multiplicative (ZMod 2))) :=
      Count.card_hom_eq_card_Z1.symm
    _ = Nat.card (zLayer G 1) := card_continuousCharacter_eq_card_zLayer_one hfg hpro

private theorem multiplicativeZModTwo_sq (x : Multiplicative (ZMod 2)) : x ^ 2 = 1 := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one, two_nsmul, Count.zmod2_add_self]

private theorem multiplicativeZModTwo_fourth (x : Multiplicative (ZMod 2)) : x ^ 4 = 1 := by
  rw [show 4 = 2 * 2 by norm_num, pow_mul, multiplicativeZModTwo_sq]

/-- Mod-`2` characters of the improved square presentation are arbitrary generator values:
its literal square-commutator relator dies in every elementary abelian target. -/
noncomputable def dsqCharacterEquivFun (h : ℕ) :
    ContinuousMonoidHom (SqCore.DSq h : Type) (Multiplicative (ZMod 2)) ≃
      (Fin (SqCore.sqRank h) → Multiplicative (ZMod 2)) where
  toFun f i := f (SqCore.sqGen h i)
  invFun m := SqCore.sqLiftHom h isProPTwo_multiplicativeZModTwo m (by
    rw [SqCore.sqRelWord_comm, multiplicativeZModTwo_fourth, multiplicativeZModTwo_sq]
    simp)
  left_inv f := SqCore.dsq_hom_ext _ _ fun i => by simp
  right_inv m := funext fun i => by simp

/-- The improved `DSq h` presentation has exactly `2^(3+2h)` mod-`2` characters. -/
theorem card_continuousCharacter_dsq (h : ℕ) :
    Nat.card (ContinuousMonoidHom (SqCore.DSq h : Type) (Multiplicative (ZMod 2))) =
      2 ^ SqCore.sqRank h := by
  rw [Nat.card_congr (dsqCharacterEquivFun h), Nat.card_fun, Nat.card_fin,
    Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- The first positive layer of `DSq h` has rank `sqRank h = 3 + 2h`. -/
theorem card_zLayer_one_dsq (h : ℕ) :
    Nat.card (zLayer (SqCore.DSq h : Type) 1) = 2 ^ SqCore.sqRank h := by
  rw [← card_continuousCharacter_eq_card_zLayer_one
    (dsqFinsetTopGen h) (SqCore.isProP_DSq h)]
  exact card_continuousCharacter_dsq h

/-- The formal junk layer `Z₀ = λ₀/λ₁` is trivial for every group. -/
theorem card_zLayer_zero
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    Nat.card (zLayer G 0) = 1 := by
  letI : Subsingleton (levelQuot G 1) := QuotientGroup.subsingleton_quotient_top
  exact Nat.card_unique

/-! ## The exact lower two-central Hilbert-function supply -/

/-- The `n`-th positive lower two-central Hilbert coefficient, indexed so coefficient `0` is
`Z₁ = λ₁/λ₂`.  Since every layer is elementary abelian, this is its `𝔽₂`-dimension. -/
noncomputable def lowerTwoCentralHilbertCoefficient
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (n : ℕ) : ℕ :=
  padicValNat 2 (Nat.card (zLayer G (n + 1)))

/-- Every positive layer order is `2` to its lower two-central Hilbert coefficient. -/
theorem card_zLayer_succ_eq_two_pow_hilbertCoefficient
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) (n : ℕ) :
    Nat.card (zLayer G (n + 1)) = 2 ^ lowerTwoCentralHilbertCoefficient G n := by
  haveI : Finite (levelQuot G (n + 2)) := finite_levelQuot G hfg hpro (n + 2)
  have hP : IsPGroup 2 (zLayer G (n + 1)) := fun z => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    exact zLayer_sq G z.property⟩
  obtain ⟨d, hd⟩ := IsPGroup.iff_card.mp hP
  rw [lowerTwoCentralHilbertCoefficient, hd, padicValNat.prime_pow]

/-- Coefficientwise equality of the positive lower two-central Hilbert functions.  This is
the weakest all-degree numerical supply: it asks for dimensions only, with no bases, bracket,
restricted-power operation, or orientation data. -/
def SqTwoCentralHilbertSeriesAgreement
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (h : ℕ) : Prop :=
  ∀ n, lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) n =
    lowerTwoCentralHilbertCoefficient G n

/-- **Exact Hilbert-series boundary.**  Coefficient agreement is equivalent to agreement of
all formal layer orders; `Z₀` is automatic and positive layer orders are powers of `2`. -/
theorem twoCentralHilbertSeriesAgreement_iff_layerCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] {h : ℕ}
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    SqTwoCentralHilbertSeriesAgreement G h ↔ SqTwoCentralLayerCardAgreement G h := by
  constructor
  · intro hcoeff k
    cases k with
    | zero => rw [card_zLayer_zero, card_zLayer_zero]
    | succ n =>
        rw [card_zLayer_succ_eq_two_pow_hilbertCoefficient
              (G := (SqCore.DSq h : Type)) (dsqFinsetTopGen h) (SqCore.isProP_DSq h),
          card_zLayer_succ_eq_two_pow_hilbertCoefficient hfg hpro, hcoeff n]
  · intro hlayer n
    exact congrArg (padicValNat 2) (hlayer (n + 1))

/-- Low-degree model regression: coefficient `0` of the improved presentation is its literal
generator rank. -/
theorem dsq_lowerTwoCentralHilbertCoefficient_zero (h : ℕ) :
    lowerTwoCentralHilbertCoefficient (SqCore.DSq h : Type) 0 = SqCore.sqRank h := by
  change padicValNat 2 (Nat.card (zLayer (SqCore.DSq h : Type) 1)) = SqCore.sqRank h
  rw [card_zLayer_one_dsq, padicValNat.prime_pow]

/-- Low-degree group regression: coefficient `0` is the mod-`2` `H¹`/Demushkin rank. -/
theorem lowerTwoCentralHilbertCoefficient_zero_eq_demushkinRank
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    lowerTwoCentralHilbertCoefficient G 0 = demushkinRank 2 G := by
  change padicValNat 2 (Nat.card (zLayer G 1)) =
    padicValNat 2 (Nat.card (H1 G (ZMod 2)))
  exact congrArg (padicValNat 2) (card_H1_zmodTwo_eq_card_zLayer_one hfg hpro).symm

/-- The order of a level quotient is obtained from the preceding level by multiplying by the
order of its two-central graded layer. -/
theorem card_levelQuot_succ
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) (k : ℕ) :
    Nat.card (zLayer G k) * Nat.card (levelQuot G k) =
      Nat.card (levelQuot G (k + 1)) := by
  haveI : Finite (levelQuot G (k + 1)) := finite_levelQuot G hfg hpro (k + 1)
  have hindex : (zLayer G k).index = Nat.card (levelQuot G k) := by
    rw [zLayer_eq_ker_levelProj, Subgroup.index,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective (levelProj G k)
        (levelProj_surjective G k)).toEquiv]
  simpa [hindex] using Subgroup.card_mul_index (zLayer G k)

/-! ## The quadratic lower two-central layer -/

/-- The dimension of the unrestricted quadratic restricted-Lie words on `d` degree-one
generators: `d` squares and `d(d-1)/2` brackets. -/
def lowerTwoCentralQuadraticDimension (d : ℕ) : ℕ :=
  d * (d + 1) / 2

/-- The expected dimension after one nonzero quadratic relation.  This is the coefficient of
degree two in the lower `2`-central Hilbert function; it is not a Jennings--Zassenhaus
coefficient. -/
def lowerTwoCentralOneRelatorQuadraticDimension (d : ℕ) : ℕ :=
  lowerTwoCentralQuadraticDimension d - 1

/-- Cardinal form of the expected degree-two lower `2`-central calculation for a group of
degree-one rank `d`. -/
def LowerTwoCentralDegreeTwoExpectedCard
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) : Prop :=
  Nat.card (zLayer G 2) = 2 ^ lowerTwoCentralOneRelatorQuadraticDimension d

/-- **Exact cohomological seam for degree two.**  This is the cardinal shadow of the
Hochschild--Serre five-term sequence for
`1 → λ₂(G) → G → G/λ₂(G) → 1`: the dual of `λ₂/λ₃` is the kernel of inflation from the
degree-two cohomology of the elementary-abelian quotient.  The right side records the standard
`d(d+1)/2` count for that cohomology.  For a Demushkin group, cup-product nondegeneracy makes
inflation onto its one-dimensional `H²`; the theorem immediately below isolates the remaining
formal consequence.

This definition is deliberately an interface, not an axiom.  The current cohomology library
does not yet connect its five-term/transgression API to `twoCentralSeries`. -/
def LowerTwoCentralFiveTermCardFormula
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] : Prop :=
  Nat.card (zLayer G 2) * Nat.card (H2 G (ZMod 2)) =
    2 ^ lowerTwoCentralQuadraticDimension (demushkinRank 2 G)

/-! ### A canonical field-side five-term interface -/

/-- Canonical degree-two inflation for the Frattini/lower-two-central extension
`1 → λ₂(G) → G → G/λ₂(G) → 1`, with trivial `𝔽₂` coefficients. -/
noncomputable def lowerTwoCentralH2Inflation
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    H2 Q (ZMod 2) →+ H2 G (ZMod 2) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact inf2 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl)

/-- Canonical degree-one inflation for the same Frattini quotient. -/
noncomputable def lowerTwoCentralH1Inflation
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    H1 Q (ZMod 2) →+ H1 G (ZMod 2) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  exact inf1 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl)

/-- Every mod-`2` degree-one class factors through `G/λ₂(G)`: in character language this is
exactly `continuousCharacterLevelTwoEquiv`. -/
theorem lowerTwoCentralH1Inflation_surjective
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    Function.Surjective (lowerTwoCentralH1Inflation G) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only
  intro x
  obtain ⟨z, rfl⟩ := H1mk_surjective (G := G) (M := ZMod 2) x
  let cG : ContinuousMonoidHom G (Multiplicative (ZMod 2)) := Count.homEquivZ1.symm z
  let cQ : ContinuousMonoidHom Q (Multiplicative (ZMod 2)) :=
    (continuousCharacterLevelTwoEquiv G).symm cG
  let zQ : Z1 Q (ZMod 2) := Count.homEquivZ1 cQ
  refine ⟨H1mk Q (ZMod 2) zQ, ?_⟩
  rw [show lowerTwoCentralH1Inflation G =
      inf1 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl) from rfl,
    inf1_H1mk]
  congr 1

/-- Inflation along `G → G/λ₂(G)` respects the trivial-coefficient cup product. -/
theorem lowerTwoCentralH2Inflation_trivialCupPairing
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (x y :
      let Q := levelQuot G 2
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      H1 Q (ZMod 2)) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    let Q := levelQuot G 2
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    lowerTwoCentralH2Inflation G
        (trivialCupPairing 2 Q (fun _ _ => rfl) x y) =
      trivialCupPairing 2 G (fun _ _ => rfl)
        (lowerTwoCentralH1Inflation G x) (lowerTwoCentralH1Inflation G y) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := Q) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := Q) (M := ZMod 2) y
  simp only [trivialCupPairing]
  rw [show lowerTwoCentralH2Inflation G =
      inf2 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl) from rfl,
    show lowerTwoCentralH1Inflation G =
      inf1 ⟨levelMk G 2, continuous_levelMk G 2⟩ (fun _ _ => rfl) from rfl,
    cup11_mk_mk, inf2_H2mk, inf1_H1mk, inf1_H1mk, cup11_mk_mk]
  congr 1

/-- The exact five-term input still absent from the cohomology library: the mod-`2` dual of
`λ₂/λ₃` is the kernel of canonical degree-two inflation from `G/λ₂`.  Stating an additive
equivalence is exactly the `H¹(λ₂,𝔽₂)^G ≃ ker(inf²)` portion of Hochschild--Serre, after the
standard identification of invariants with `Hom(λ₂/λ₃,𝔽₂)`. -/
def LowerTwoCentralFiveTermKernelDuality
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  Nonempty ((Additive (zLayer G 2) →+ ZMod 2) ≃+
    ↥(lowerTwoCentralH2Inflation G).ker)

/-- Surjectivity of canonical degree-two inflation.  For a positive-rank Demushkin group this
is the cup-product consequence: lift two degree-one classes to `G/λ₂`, then use a nonzero cup
to hit the one-dimensional `H²(G,𝔽₂)`.  It is separated from the actual five-term kernel
identification because the two statements have different proofs. -/
def LowerTwoCentralH2InflationSurjective
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] : Prop :=
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  Function.Surjective (lowerTwoCentralH2Inflation G)

/-- **The inflation-surjectivity component is unconditional for positive-rank Demushkin
groups.**  Degree-one classes factor through the Frattini quotient, cup products commute with
inflation, and nondegeneracy produces a nonzero class in the image.  Since Demushkin `H²` has
order two, that nonzero class together with zero exhausts the codomain. -/
theorem lowerTwoCentralH2InflationSurjective_of_demushkin
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G)
    (hrank :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      0 < demushkinRank 2 G) :
    LowerTwoCentralH2InflationSurjective G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  dsimp only [LowerTwoCentralH2InflationSurjective]
  letI : Finite (H1 G (ZMod 2)) := hD.finiteH1
  letI : Fintype (H1 G (ZMod 2)) := Fintype.ofFinite _
  have hH1card : Fintype.card (H1 G (ZMod 2)) = 2 ^ demushkinRank 2 G := by
    rw [← Nat.card_eq_fintype_card]
    exact hD.card_H1_eq_pow
  have hH1large : 1 < Fintype.card (H1 G (ZMod 2)) := by
    rw [hH1card]
    exact Nat.one_lt_pow hrank.ne' (by omega)
  obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hH1large
  let x := a - b
  have hx : x ≠ 0 := sub_ne_zero.mpr hab
  obtain ⟨y, hcup⟩ := hD.nondegen_left' (fun _ _ => rfl) x hx
  obtain ⟨xQ, hxQ⟩ := lowerTwoCentralH1Inflation_surjective G x
  obtain ⟨yQ, hyQ⟩ := lowerTwoCentralH1Inflation_surjective G y
  let cupQ := trivialCupPairing 2 Q (fun _ _ => rfl) xQ yQ
  have hcupImage : lowerTwoCentralH2Inflation G cupQ =
      trivialCupPairing 2 G (fun _ _ => rfl) x y := by
    dsimp only [cupQ]
    rw [lowerTwoCentralH2Inflation_trivialCupPairing, hxQ, hyQ]
  obtain ⟨w, hw, hwuniq⟩ :=
    (Nat.card_eq_two_iff' (0 : H2 G (ZMod 2))).mp hD.cardH2
  intro z
  by_cases hz : z = 0
  · exact ⟨0, by rw [map_zero, hz]⟩
  · have hcupw : trivialCupPairing 2 G (fun _ _ => rfl) x y = w := hwuniq _ hcup
    have hzw : z = w := hwuniq z hz
    refine ⟨cupQ, ?_⟩
    rw [hcupImage, hcupw, hzw]

/-- The second independent finite-group input: for the elementary-abelian Frattini quotient of
rank `d`, degree-two mod-`2` cohomology has dimension `d(d+1)/2`. -/
def LowerTwoCentralElementaryH2CardFormula
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (d : ℕ) : Prop :=
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  Nat.card (H2 Q (ZMod 2)) = 2 ^ lowerTwoCentralQuadraticDimension d

/-- **Narrow finite-group cohomology API.**  Every finite elementary-abelian `2`-group of
order `2^d` has mod-`2` `H²` of order `2^(d(d+1)/2)`.  This is the standard computation
`H*(C₂^d,𝔽₂) ≅ 𝔽₂[t₁,…,t_d]` in degree two.

The repository currently has no comparison from its continuous inhomogeneous cochains to
Mathlib's finite-group cohomology, and no Künneth theorem for this `H2`; consequently this is a
`def`-shaped reusable interface, not an axiom. -/
def FiniteElementaryAbelianTwoH2CardFormula : Prop :=
  ∀ (V : Type) [CommGroup V] [TopologicalSpace V] [IsTopologicalGroup V]
    [DiscreteTopology V] [Finite V],
    (∀ v : V, v ^ 2 = 1) → ∀ d : ℕ, Nat.card V = 2 ^ d →
      letI : DistribMulAction V (ZMod 2) := scalarActionZmodTwo V
      letI : ContinuousSMul V (ZMod 2) := scalarActionZmodTwo_continuousSMul V
      Nat.card (H2 V (ZMod 2)) = 2 ^ lowerTwoCentralQuadraticDimension d

/-- The universal finite elementary-abelian computation specializes to the Frattini quotient
once its order is known. -/
theorem lowerTwoCentralElementaryH2CardFormula_of_finiteElementary
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) {d : ℕ}
    (hcard : Nat.card (levelQuot G 2) = 2 ^ d) :
    LowerTwoCentralElementaryH2CardFormula G d := by
  let Q := levelQuot G 2
  letI : DiscreteTopology Q := discreteTopology_levelQuot G hfg hpro 2
  letI : Finite Q := finite_levelQuot G hfg hpro 2
  letI : CommGroup Q :=
    { (inferInstance : Group Q) with
      mul_comm := fun a b => by
        have ha : a ∈ zLayer G 1 := by rw [zLayer_one_eq_top]; trivial
        exact (Subgroup.mem_center_iff.mp (zLayer_le_center G 1 ha) b).symm }
  have htwo : ∀ q : Q, q ^ 2 = 1 := by
    intro q
    exact zLayer_sq G (by rw [zLayer_one_eq_top]; trivial)
  dsimp only [LowerTwoCentralElementaryH2CardFormula]
  exact H Q htwo d hcard

/-- A finitely generated Demushkin group's Frattini quotient has order `2^rank`. -/
theorem card_levelQuot_two_eq_two_pow_demushkinRank
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G) :
    Nat.card (levelQuot G 2) =
      2 ^ (letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
        demushkinRank 2 G) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  calc
    Nat.card (levelQuot G 2) = Nat.card (zLayer G 1) := by
      rw [zLayer_one_eq_top]
      exact (Nat.card_congr Subgroup.topEquiv.toEquiv).symm
    _ = Nat.card (H1 G (ZMod 2)) :=
      (card_H1_zmodTwo_eq_card_zLayer_one hfg hD.isProP).symm
    _ = 2 ^ demushkinRank 2 G := hD.card_H1_eq_pow

/-- Hence the universal finite-group theorem supplies the elementary-abelian input for every
finitely generated Demushkin group. -/
theorem lowerTwoCentralElementaryH2CardFormula_of_demushkin
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G) :
    LowerTwoCentralElementaryH2CardFormula G
      (letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
       demushkinRank 2 G) := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  exact lowerTwoCentralElementaryH2CardFormula_of_finiteElementary H G hfg hD.isProP
    (card_levelQuot_two_eq_two_pow_demushkinRank G hfg hD)

/-- **Sharp assembly of the field-side seam.**  Kernel duality from the five-term sequence,
surjectivity of inflation, and the standard elementary-abelian `H²` count imply the exact
cardinal formula used by the degree-two presentation reduction.  This theorem contains all
finite duality and rank-nullity bookkeeping; future cohomological work need only provide the
three mathematically standard inputs in its statement. -/
theorem lowerTwoCentralFiveTermCardFormula_of_kernelDuality
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (hdual : LowerTwoCentralFiveTermKernelDuality G)
    (hsurj : LowerTwoCentralH2InflationSurjective G)
    (helem : LowerTwoCentralElementaryH2CardFormula G
      (letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
       demushkinRank 2 G)) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    LowerTwoCentralFiveTermCardFormula G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  let Q := levelQuot G 2
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  let inf := lowerTwoCentralH2Inflation G
  dsimp only [LowerTwoCentralFiveTermKernelDuality] at hdual
  dsimp only [LowerTwoCentralH2InflationSurjective] at hsurj
  dsimp only [LowerTwoCentralElementaryH2CardFormula] at helem
  obtain ⟨edual⟩ := hdual
  haveI : Finite (H2 Q (ZMod 2)) :=
    Nat.finite_of_card_ne_zero (by rw [helem]; exact (Nat.two_pow_pos _).ne')
  haveI : Finite (H2 G (ZMod 2)) := Finite.of_surjective inf hsurj
  haveI : Finite (levelQuot G 3) := finite_levelQuot G hfg hpro 3
  haveI : Finite (zLayer G 2) := Subtype.finite
  letI : CommGroup (zLayer G 2) :=
    { (inferInstance : Group (zLayer G 2)) with
      mul_comm := fun a b =>
        Subtype.ext (Subgroup.mem_center_iff.mp (zLayer_le_center G 2 a.2) b.1).symm }
  have htwo : ∀ a : Additive (zLayer G 2), a + a = 0 := by
    intro a
    apply Additive.toMul.injective
    change a.toMul * a.toMul = 1
    apply Subtype.ext
    simpa [pow_two] using zLayer_sq G a.toMul.2
  have hdualCard : Nat.card (Additive (zLayer G 2) →+ ZMod 2) =
      Nat.card (zLayer G 2) := by
    rw [QuadraticFp2.card_addHom_zmod2 _ htwo, Nat.card_congr Additive.toMul]
  have hkerCard : Nat.card (Additive (zLayer G 2) →+ ZMod 2) =
      Nat.card ↥inf.ker := Nat.card_congr edual.toEquiv
  have hquotRange : Nat.card (H2 Q (ZMod 2) ⧸ inf.ker) =
      Nat.card ↥inf.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange inf).toEquiv
  have hrangeCard : Nat.card ↥inf.range = Nat.card (H2 G (ZMod 2)) := by
    rw [AddMonoidHom.range_eq_top_of_surjective inf hsurj]
    exact Nat.card_congr AddSubgroup.topEquiv.toEquiv
  have hdomain : Nat.card (H2 Q (ZMod 2)) =
      Nat.card (H2 Q (ZMod 2) ⧸ inf.ker) * Nat.card ↥inf.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup inf.ker
  unfold LowerTwoCentralFiveTermCardFormula
  calc
    Nat.card (zLayer G 2) * Nat.card (H2 G (ZMod 2)) =
        Nat.card (Additive (zLayer G 2) →+ ZMod 2) *
          Nat.card (H2 G (ZMod 2)) := by rw [hdualCard]
    _ = Nat.card ↥inf.ker * Nat.card (H2 G (ZMod 2)) := by rw [hkerCard]
    _ = Nat.card (H2 Q (ZMod 2)) := by
      rw [← hrangeCard, ← hquotRange, mul_comm]
      exact hdomain.symm
    _ = 2 ^ lowerTwoCentralQuadraticDimension (demushkinRank 2 G) := helem

/-- For a positive-rank Demushkin group, inflation surjectivity is no longer an input.  Thus the
field-side cardinal formula is reduced to exactly two missing ingredients: five-term kernel
duality and the elementary-abelian `H²` cardinal computation. -/
theorem lowerTwoCentralFiveTermCardFormula_of_kernelDuality_demushkin
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G)
    (hrank :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      0 < demushkinRank 2 G)
    (hdual : LowerTwoCentralFiveTermKernelDuality G)
    (helem : LowerTwoCentralElementaryH2CardFormula G
      (letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
       demushkinRank 2 G)) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    LowerTwoCentralFiveTermCardFormula G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  exact lowerTwoCentralFiveTermCardFormula_of_kernelDuality G hfg hD.isProP hdual
    (lowerTwoCentralH2InflationSurjective_of_demushkin G hD hrank) helem

/-- After isolating the universal finite elementary-abelian computation, the full cardinal
formula for a positive-rank finitely generated Demushkin group has only the five-term kernel
duality as a group-specific input. -/
theorem lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G)
    (hD :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
      IsDemushkin 2 G)
    (hrank :
      letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
      0 < demushkinRank 2 G)
    (hdual : LowerTwoCentralFiveTermKernelDuality G) :
    letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
    letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
    LowerTwoCentralFiveTermCardFormula G := by
  letI : DistribMulAction G (ZMod 2) := scalarActionZmodTwo G
  letI : ContinuousSMul G (ZMod 2) := scalarActionZmodTwo_continuousSMul G
  exact lowerTwoCentralFiveTermCardFormula_of_kernelDuality_demushkin G hfg hD hrank hdual
    (lowerTwoCentralElementaryH2CardFormula_of_demushkin H G hfg hD)

/-- The model-side degree-two supply.  The completed Magnus/PBW development already proves
that the certified quadratic relation generates the entire completed degree-two relation
kernel.  What is not yet in the library is the bridge from that augmentation-ideal statement
to the primitive lower `2`-central quotient `λ₂/λ₃`; this proposition records exactly the
cardinality consequence needed from such a bridge. -/
def SqLowerTwoCentralDegreeTwoExpectedCardSupply : Prop :=
  ∀ h : ℕ,
    LowerTwoCentralDegreeTwoExpectedCard (SqCore.DSq h : Type) (SqCore.sqRank h)

/-- A positive-rank Demushkin group satisfying the exact five-term cardinal formula has the
predicted one-relator degree-two layer.  Thus the missing arithmetic-side input is now exactly
the bridge stated above, rather than an assumed presentation or an all-degree Hilbert series. -/
theorem lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    (hD : IsDemushkin 2 G) (hrank : 0 < demushkinRank 2 G)
    (hfive : LowerTwoCentralFiveTermCardFormula G) :
    LowerTwoCentralDegreeTwoExpectedCard G (demushkinRank 2 G) := by
  let d := demushkinRank 2 G
  have hmul : 2 ≤ d * (d + 1) := by
    dsimp [d]
    nlinarith
  have hquad : 0 < lowerTwoCentralQuadraticDimension d := by
    exact Nat.div_pos hmul (by omega)
  have hsplit : lowerTwoCentralQuadraticDimension d =
      lowerTwoCentralOneRelatorQuadraticDimension d + 1 := by
    rw [lowerTwoCentralOneRelatorQuadraticDimension]
    omega
  unfold LowerTwoCentralFiveTermCardFormula at hfive
  rw [hD.cardH2] at hfive
  change Nat.card (zLayer G 2) =
    2 ^ lowerTwoCentralOneRelatorQuadraticDimension d
  have hcancel : Nat.card (zLayer G 2) * 2 =
      2 ^ lowerTwoCentralOneRelatorQuadraticDimension d * 2 := by
    rw [← pow_succ, ← hsplit]
    exact hfive
  exact Nat.mul_right_cancel (m := 2) (by omega) hcancel

/-- Cardinal exactness at degree two computes coefficient `1` of the lower `2`-central Hilbert
function. -/
theorem lowerTwoCentralHilbertCoefficient_one_of_expectedCard
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) {d : ℕ}
    (hcard : LowerTwoCentralDegreeTwoExpectedCard G d) :
    lowerTwoCentralHilbertCoefficient G 1 =
      lowerTwoCentralOneRelatorQuadraticDimension d := by
  unfold LowerTwoCentralDegreeTwoExpectedCard at hcard
  have hpows : 2 ^ lowerTwoCentralHilbertCoefficient G 1 =
      2 ^ lowerTwoCentralOneRelatorQuadraticDimension d :=
    (card_zLayer_succ_eq_two_pow_hilbertCoefficient hfg hpro 1).symm.trans hcard
  simpa only [padicValNat.prime_pow] using congrArg (padicValNat 2) hpows

/-- The frozen rank-three Roe calculation determines the first genuinely quadratic layer
exactly: `|λ₂(D_R)/λ₃(D_R)| = 256 / 8 = 32`.  The upper and lower bounds themselves were proved
in `Levelwise`; here we expose the layer cardinality through the general tower recurrence. -/
theorem card_zLayer_two_dr : Nat.card (zLayer (DR : Type) 2) = 32 := by
  have hcard := card_levelQuot_succ (DR : Type) drFinsetTopGen isProP_DR 2
  rw [GQ2.Roe.Labute.card_levelQuot_two,
    GQ2.Roe.Labute.card_levelQuot_three] at hcard
  omega

/-- Rank-three model regression: the improved square presentation is the frozen Roe group, so
its quadratic lower `2`-central layer also has order `2^5`. -/
theorem card_zLayer_two_dsq_zero :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 2) = 32 := by
  exact SqCore.dsq_zero ▸ card_zLayer_two_dr

/-- The rank-three improved presentation satisfies the expected one-relator quadratic formula
without any cohomological seam. -/
theorem lowerTwoCentralDegreeTwoExpectedCard_dsq_zero :
    LowerTwoCentralDegreeTwoExpectedCard (SqCore.DSq 0 : Type) (SqCore.sqRank 0) := by
  rw [LowerTwoCentralDegreeTwoExpectedCard, card_zLayer_two_dsq_zero]
  norm_num [lowerTwoCentralOneRelatorQuadraticDimension,
    lowerTwoCentralQuadraticDimension, SqCore.sqRank]

/-- The model-side degree-two supply is already discharged at `h = 0`. -/
theorem sqLowerTwoCentralDegreeTwoExpectedCardSupply_zero :
    LowerTwoCentralDegreeTwoExpectedCard (SqCore.DSq 0 : Type) (SqCore.sqRank 0) :=
  lowerTwoCentralDegreeTwoExpectedCard_dsq_zero

/-- Equivalently, coefficient `1` of the rank-three lower `2`-central Hilbert function is `5`. -/
theorem dsq_lowerTwoCentralHilbertCoefficient_one_zero :
    lowerTwoCentralHilbertCoefficient (SqCore.DSq 0 : Type) 1 = 5 := by
  change padicValNat 2 (Nat.card (zLayer (SqCore.DSq 0 : Type) 2)) = 5
  rw [card_zLayer_two_dsq_zero, show (32 : ℕ) = 2 ^ 5 by norm_num,
    padicValNat.prime_pow]

/-- Agreement of all graded-layer orders implies agreement of all level-quotient orders. -/
theorem twoCentralLevelCardAgreement_of_layerCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hGfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (hlayer : SqTwoCentralLayerCardAgreement G h) :
    SqTwoCentralLevelCardAgreement G h := by
  intro k
  induction k with
  | zero =>
      haveI : Subsingleton (levelQuot (SqCore.DSq h : Type) 0) :=
        QuotientGroup.subsingleton_quotient_top
      haveI : Subsingleton (levelQuot G 0) := QuotientGroup.subsingleton_quotient_top
      rw [Nat.card_unique, Nat.card_unique]
  | succ k ih =>
      calc
        Nat.card (levelQuot (SqCore.DSq h : Type) (k + 1)) =
            Nat.card (zLayer (SqCore.DSq h : Type) k) *
              Nat.card (levelQuot (SqCore.DSq h : Type) k) :=
          (card_levelQuot_succ (SqCore.DSq h : Type) (dsqFinsetTopGen h)
            (SqCore.isProP_DSq h) k).symm
        _ = Nat.card (zLayer G k) * Nat.card (levelQuot G k) := by
          rw [hlayer k, ih]
        _ = Nat.card (levelQuot G (k + 1)) := card_levelQuot_succ G hGfg hpro k

/-- Conversely, level-order agreement determines every graded-layer order by cancellation in
the finite extension `1 → Zₖ → Qₖ₊₁ → Qₖ → 1`. -/
theorem twoCentralLayerCardAgreement_of_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hGfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G)
    (hlevel : SqTwoCentralLevelCardAgreement G h) :
    SqTwoCentralLayerCardAgreement G h := by
  intro k
  haveI : Finite (levelQuot (SqCore.DSq h : Type) k) :=
    finite_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
      (SqCore.isProP_DSq h) k
  apply Nat.mul_right_cancel (Nat.card_pos (α := levelQuot (SqCore.DSq h : Type) k))
  calc
    Nat.card (zLayer (SqCore.DSq h : Type) k) *
          Nat.card (levelQuot (SqCore.DSq h : Type) k) =
        Nat.card (levelQuot (SqCore.DSq h : Type) (k + 1)) :=
      card_levelQuot_succ (SqCore.DSq h : Type) (dsqFinsetTopGen h)
        (SqCore.isProP_DSq h) k
    _ = Nat.card (levelQuot G (k + 1)) := hlevel (k + 1)
    _ = Nat.card (zLayer G k) * Nat.card (levelQuot G k) :=
      (card_levelQuot_succ G hGfg hpro k).symm
    _ = Nat.card (zLayer G k) *
          Nat.card (levelQuot (SqCore.DSq h : Type) k) := by rw [hlevel k]

/-- **Exact graded numerical boundary.**  For finitely generated pro-2 groups, equality of the
successive two-central layer orders is equivalent to equality of all tower orders. -/
theorem twoCentralLayerCardAgreement_iff_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hGfg : IsTopologicallyFinGen G) (hpro : IsProP 2 G) :
    SqTwoCentralLayerCardAgreement G h ↔ SqTwoCentralLevelCardAgreement G h :=
  ⟨twoCentralLevelCardAgreement_of_layerCardAgreement hGfg hpro,
    twoCentralLayerCardAgreement_of_levelCardAgreement hGfg hpro⟩

/-- At one level, a forward epimorphism together with equality of quotient orders produces a
reverse epimorphism. -/
theorem nonempty_reverseTwoCentralLevel_of_card_eq
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (k : ℕ)
    (hcard : Nat.card (levelQuot (SqCore.DSq h : Type) k) =
      Nat.card (levelQuot G k)) :
    Nonempty (ContSurj G (levelQuot (SqCore.DSq h : Type) k)) := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective f.toMonoidHom f.continuous_toFun hf
      (dsqFinsetTopGen h)
  letI : DiscreteTopology (levelQuot (SqCore.DSq h : Type) k) :=
    QuotientGroup.discreteTopology
      (isOpen_twoCentralSeries (SqCore.DSq h : Type) (dsqFinsetTopGen h)
        (SqCore.isProP_DSq h) k)
  letI : DiscreteTopology (levelQuot G k) :=
    QuotientGroup.discreteTopology (isOpen_twoCentralSeries G hGfg hpro k)
  let e : ContinuousMulEquiv
      (levelQuot (SqCore.DSq h : Type) k) (levelQuot G k) := by
    haveI : Finite (levelQuot (SqCore.DSq h : Type) k) :=
      finite_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
        (SqCore.isProP_DSq h) k
    haveI : Finite (levelQuot G k) := finite_levelQuot G hGfg hpro k
    exact continuousMulEquivOfBijective (twoCentralLevelMap f k)
      ((Nat.bijective_iff_surjective_and_card _).mpr
        ⟨twoCentralLevelMap_surjective f hf k, hcard⟩)
  let q : ContinuousMonoidHom G (levelQuot G k) :=
    ⟨levelMk G k, continuous_levelMk G k⟩
  let b : ContinuousMonoidHom G (levelQuot (SqCore.DSq h : Type) k) :=
    (e.symm : ContinuousMonoidHom _ _).comp q
  refine ⟨⟨b, ?_⟩⟩
  intro y
  obtain ⟨z, rfl⟩ := e.symm.surjective y
  obtain ⟨g, rfl⟩ := levelMk_surjective G k z
  exact ⟨g, rfl⟩

/-- The complete reverse finite-quotient condition follows from equality of the natural finite
two-central quotient orders.  The forward epimorphism is exactly the one already assembled from
the improved-relator finite-level markings. -/
theorem reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (hcard : SqTwoCentralLevelCardAgreement G h) :
    SqReverseFiniteQuotientSurjections G h := by
  rw [sqReverseFiniteQuotientSurjections_iff_twoCentralLevel]
  intro k
  exact nonempty_reverseTwoCentralLevel_of_card_eq hpro f hf k (hcard k)

/-- Conversely, the original reverse condition forces equality of the two-central quotient
orders once a forward epimorphism is fixed.  Indeed the reverse finite-level maps assemble to a
global reverse epimorphism, and both global epimorphisms remain onto on the two-central tower. -/
theorem twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) (hback : SqReverseFiniteQuotientSurjections G h) :
    SqTwoCentralLevelCardAgreement G h := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective f.toMonoidHom f.continuous_toFun hf
      (dsqFinsetTopGen h)
  have hfin : ∀ V : OpenNormalSubgroup (ProfiniteGrp.of (SqCore.DSq h : Type)),
      Finite (ContSurj G ((SqCore.DSq h : Type) ⧸ V.toSubgroup)) := by
    intro V
    haveI : Finite ((SqCore.DSq h : Type) ⧸ V.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'
    haveI := finite_continuousMonoidHom hGfg
      ((SqCore.DSq h : Type) ⧸ V.toSubgroup)
    exact Subtype.finite
  obtain ⟨⟨b, hb⟩⟩ := exists_contSurj_of_levelwise_nonempty hback hfin
  intro k
  haveI : Finite (levelQuot (SqCore.DSq h : Type) k) :=
    finite_levelQuot (SqCore.DSq h : Type) (dsqFinsetTopGen h)
      (SqCore.isProP_DSq h) k
  haveI : Finite (levelQuot G k) := finite_levelQuot G hGfg hpro k
  apply le_antisymm
  · exact Nat.card_le_card_of_surjective _ (twoCentralLevelMap_surjective b hb k)
  · exact Nat.card_le_card_of_surjective _ (twoCentralLevelMap_surjective f hf k)

/-- **Exact reverse boundary.**  In the presence of the already-constructed forward
epimorphism, the old family indexed by all open normal subgroups is equivalent to equality of
the finite two-central quotient orders. -/
theorem reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hpro : IsProP 2 G) (f : ContinuousMonoidHom (SqCore.DSq h : Type) G)
    (hf : Function.Surjective f) :
    SqReverseFiniteQuotientSurjections G h ↔ SqTwoCentralLevelCardAgreement G h :=
  ⟨twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections hpro f hf,
    reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement hpro f hf⟩

/-- Specialization to the forward-generator package used by the odd-degree field theorem. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G)
    (hcard : SqTwoCentralLevelCardAgreement G h) :
    SqReverseFiniteQuotientSurjections G h :=
  reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement hpro
    (D.forward hpro) (D.forward_surjective hpro) hcard

/-- Generator-package regression: after the improved-relator forward map is built, the reverse
hypothesis is *exactly* level-cardinality agreement and need not be stated again over all open
normal subgroups. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_levelCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G) :
    SqReverseFiniteQuotientSurjections G h ↔ SqTwoCentralLevelCardAgreement G h :=
  reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement hpro
    (D.forward hpro) (D.forward_surjective hpro)

/-- Graded-cardinality specialization of the forward-generator package.  No bases or
associated-graded operations need to be chosen: equality of the order of each elementary
abelian layer already reconstructs the entire tower cardinality. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_layerCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G)
    (hlayer : SqTwoCentralLayerCardAgreement G h) :
    SqReverseFiniteQuotientSurjections G h := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective (D.forward hpro).toMonoidHom
      (D.forward hpro).continuous_toFun (D.forward_surjective hpro)
      (dsqFinsetTopGen h)
  exact D.reverseFiniteQuotientSurjections_of_levelCardAgreement hpro
    (twoCentralLevelCardAgreement_of_layerCardAgreement hGfg hpro hlayer)

/-- With the improved-relator forward data fixed, the original reverse family is exactly
agreement of the cardinalities of the successive two-central graded pieces. -/
theorem SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_layerCardAgreement
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    {chiG : ContinuousMonoidHom G ℤ_[2]ˣ}
    (D : SqCyclotomicForwardGeneratorData h chiG) (hpro : IsProP 2 G) :
    SqReverseFiniteQuotientSurjections G h ↔ SqTwoCentralLayerCardAgreement G h := by
  have hGfg : IsTopologicallyFinGen G :=
    IsTopologicallyFinGen.of_surjective (D.forward hpro).toMonoidHom
      (D.forward hpro).continuous_toFun (D.forward_surjective hpro)
      (dsqFinsetTopGen h)
  exact (D.reverseFiniteQuotientSurjections_iff_levelCardAgreement hpro).trans
    (twoCentralLayerCardAgreement_iff_levelCardAgreement hGfg hpro).symm

/-! ## Field-facing composition -/

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-! ### Degree-zero Hilbert regression on the arithmetic group -/

/-- Field-side form of the exact five-term seam.  The explicit local instances ensure that
`H²(-, 𝔽₂)` uses the same trivial scalar action as the existing Demushkin theorem. -/
def OddDegreeGalKLowerTwoCentralFiveTermCardSupply : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)],
    Odd (Module.finrank ℚ_[2] K) →
      let Q := maxProPQuotient 2 (GalK K)
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      LowerTwoCentralFiveTermCardFormula Q

/-- Canonical degree-two inflation from the Frattini quotient of `G_K(2)` is surjective for
every finite dyadic field.  This is the direct field specialization of Demushkin
nondegeneracy; no odd-degree or `q = 2` assumption is involved. -/
theorem maxProTwoGalK_lowerTwoCentralH2InflationSurjective
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)] :
    LowerTwoCentralH2InflationSurjective (maxProPQuotient 2 (GalK K)) := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralH2InflationSurjective_of_demushkin Q
  · exact isDemushkin_maxProTwoGalK (K := K)
  · rw [demushkinRank_maxProTwoGalK (K := K)]
    omega

/-- The universal finite elementary-abelian `H²` computation specializes to the Frattini
quotient of `G_K(2)`, with dimension `[K : ℚ₂] + 2`. -/
theorem maxProTwoGalK_lowerTwoCentralElementaryH2CardFormula
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    LowerTwoCentralElementaryH2CardFormula (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  have helem := lowerTwoCentralElementaryH2CardFormula_of_demushkin H Q hfg
    (isDemushkin_maxProTwoGalK (K := K))
  rwa [demushkinRank_maxProTwoGalK (K := K)] at helem

/-- Consequently, for `G_K(2)` the exact lower-two-central cardinal formula is reduced to the
universal finite elementary-abelian computation and the five-term kernel-duality statement. -/
theorem maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
    (H : FiniteElementaryAbelianTwoH2CardFormula)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)))
    (hdual : LowerTwoCentralFiveTermKernelDuality
      (maxProPQuotient 2 (GalK K))) :
    let Q := maxProPQuotient 2 (GalK K)
    letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
    letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
    LowerTwoCentralFiveTermCardFormula Q := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  apply lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary H Q hfg
    (isDemushkin_maxProTwoGalK (K := K))
  · rw [demushkinRank_maxProTwoGalK (K := K)]
    omega
  · exact hdual

/-- The exact five-term seam plus the already-proved Demushkin cup-product theorem computes
the arithmetic quadratic layer. -/
theorem maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hfive :
      let Q := maxProPQuotient 2 (GalK K)
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      LowerTwoCentralFiveTermCardFormula Q) :
    LowerTwoCentralDegreeTwoExpectedCard (maxProPQuotient 2 (GalK K))
      (Module.finrank ℚ_[2] K + 2) := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  have hrank : 0 < demushkinRank 2 Q := by
    rw [demushkinRank_maxProTwoGalK (K := K)]
    omega
  have hcard := lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm
    (isDemushkin_maxProTwoGalK (K := K)) hrank hfive
  rwa [demushkinRank_maxProTwoGalK (K := K)] at hcard

/-- The first positive lower two-central Hilbert coefficient of `G_K(2)` is the existing
field-side Demushkin rank `[K : ℚ₂] + 2`.  Topological finite generation is explicit because
it is supplied below by the already-built forward presentation data. -/
theorem maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 0 =
      Module.finrank ℚ_[2] K + 2 := by
  let Q := maxProPQuotient 2 (GalK K)
  letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
  letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
  rw [lowerTwoCentralHilbertCoefficient_zero_eq_demushkinRank hfg
      isProP_maxProPQuotient,
    demushkinRank_maxProTwoGalK (K := K)]

/-- **Literal odd-degree rank regression.**  At coefficient `0`, the lower two-central
Hilbert functions of the improved `DSq ((n-1)/2)` presentation and `G_K(2)` agree.  No `q = 2`
or classification input is used: this is just the `H¹` rank theorem and odd-degree arithmetic. -/
theorem oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_zero
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    lowerTwoCentralHilbertCoefficient
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 0 =
      lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 0 := by
  rw [dsq_lowerTwoCentralHilbertCoefficient_zero,
    maxProTwoGalK_lowerTwoCentralHilbertCoefficient_zero K hfg]
  obtain ⟨k, hk⟩ := hodd
  rw [hk]
  simp only [SqCore.sqRank]
  omega

/-- In the repository's formal indexing, the preceding theorem proves agreement at `Z₁`;
agreement at junk layer `Z₀` is automatic. -/
theorem oddDegreeGalKSq_firstTwoLayerCardAgreement
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)] [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    ∀ k < 2,
      Nat.card (zLayer
          (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) k) =
        Nat.card (zLayer (maxProPQuotient 2 (GalK K)) k) := by
  intro k hk
  interval_cases k
  · rw [card_zLayer_zero, card_zLayer_zero]
  · rw [card_zLayer_succ_eq_two_pow_hilbertCoefficient
        (G := (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type))
        (dsqFinsetTopGen _) (SqCore.isProP_DSq _),
      card_zLayer_succ_eq_two_pow_hilbertCoefficient hfg isProP_maxProPQuotient,
      oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_zero K hodd hfg]

/-! ### Degree-two reduction and regressions -/

/-- If the model and arithmetic quadratic layers have their common one-relator cardinal, then
their `Z₂ = λ₂/λ₃` orders agree.  Oddness is used only to identify the literal improved-model
rank `3 + 2h` with `[K : ℚ₂] + 2`. -/
theorem oddDegreeGalKSq_zLayer_two_cardAgreement_of_expectedCards
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2)))
    (hfield : LowerTwoCentralDegreeTwoExpectedCard
      (maxProPQuotient 2 (GalK K)) (Module.finrank ℚ_[2] K + 2)) :
    Nat.card (zLayer
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) := by
  have hrank : SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2) =
      Module.finrank ℚ_[2] K + 2 := by
    obtain ⟨k, hk⟩ := hodd
    rw [hk]
    simp only [SqCore.sqRank]
    omega
  unfold LowerTwoCentralDegreeTwoExpectedCard at hmodel hfield
  rw [hmodel, hfield, hrank]

/-- The two exact missing supplies prove the first genuinely quadratic layer-card agreement for
every odd-degree field. -/
theorem oddDegreeGalKSq_zLayer_two_cardAgreement_of_degreeTwoSupplies
    (hmodel : SqLowerTwoCentralDegreeTwoExpectedCardSupply)
    (hfield : OddDegreeGalKLowerTwoCentralFiveTermCardSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    Nat.card (zLayer
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) :=
  oddDegreeGalKSq_zLayer_two_cardAgreement_of_expectedCards K hodd
    (hmodel ((Module.finrank ℚ_[2] K - 1) / 2))
    (maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm K
      (hfield K hodd))

/-- Coefficient `1` (the quadratic lower `2`-central coefficient) agrees under the same two
exact supplies. -/
theorem oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_one_of_degreeTwoSupplies
    (hmodel : SqLowerTwoCentralDegreeTwoExpectedCardSupply)
    (hfield : OddDegreeGalKLowerTwoCentralFiveTermCardSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K)) :
    lowerTwoCentralHilbertCoefficient
        (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) 1 =
      lowerTwoCentralHilbertCoefficient (maxProPQuotient 2 (GalK K)) 1 := by
  exact congrArg (padicValNat 2)
    (oddDegreeGalKSq_zLayer_two_cardAgreement_of_degreeTwoSupplies
      hmodel hfield K hodd)

/-- Together with the unconditional degree-zero calculation, the two exact degree-two supplies
prove layer-card agreement for all formal layers `k < 3`. -/
theorem oddDegreeGalKSq_firstThreeLayerCardAgreement_of_degreeTwoSupplies
    (hmodel : SqLowerTwoCentralDegreeTwoExpectedCardSupply)
    (hfield : OddDegreeGalKLowerTwoCentralFiveTermCardSupply)
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hodd : Odd (Module.finrank ℚ_[2] K))
    (hfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K))) :
    ∀ k < 3,
      Nat.card (zLayer
          (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type) k) =
        Nat.card (zLayer (maxProPQuotient 2 (GalK K)) k) := by
  intro k hk
  by_cases hk' : k < 2
  · exact oddDegreeGalKSq_firstTwoLayerCardAgreement K hodd hfg k hk'
  · have hk2 : k = 2 := by omega
    subst k
    exact oddDegreeGalKSq_zLayer_two_cardAgreement_of_degreeTwoSupplies
      hmodel hfield K hodd

/-- **Degree-one specialization.**  At `n = 1` the model side of the quadratic calculation is
already unconditional (`DSq 0 = D_R`).  Consequently only the arithmetic five-term seam remains;
the `ℚ₂` case is not used as an inductive base for higher degree. -/
theorem degreeOneGalKSq_zLayer_two_cardAgreement_of_fiveTerm
    (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)]
    (hone : Module.finrank ℚ_[2] K = 1)
    (hfive :
      let Q := maxProPQuotient 2 (GalK K)
      letI : DistribMulAction Q (ZMod 2) := scalarActionZmodTwo Q
      letI : ContinuousSMul Q (ZMod 2) := scalarActionZmodTwo_continuousSMul Q
      LowerTwoCentralFiveTermCardFormula Q) :
    Nat.card (zLayer (SqCore.DSq 0 : Type) 2) =
      Nat.card (zLayer (maxProPQuotient 2 (GalK K)) 2) := by
  have hh : (Module.finrank ℚ_[2] K - 1) / 2 = 0 := by omega
  have hodd : Odd (Module.finrank ℚ_[2] K) := by rw [hone]; exact odd_one
  have hmodel : LowerTwoCentralDegreeTwoExpectedCard
      (SqCore.DSq ((Module.finrank ℚ_[2] K - 1) / 2) : Type)
      (SqCore.sqRank ((Module.finrank ℚ_[2] K - 1) / 2)) := by
    rw [hh]
    exact lowerTwoCentralDegreeTwoExpectedCard_dsq_zero
  have hagree := oddDegreeGalKSq_zLayer_two_cardAgreement_of_expectedCards K hodd hmodel
    (maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm K hfive)
  rw [hh] at hagree
  exact hagree

/-- Sharpened finite-level field presentation.  The forward clause still uses the literal
improved relator and the corrected cyclotomic value fibres.  The reverse clause is replaced,
equivalently, by the order equality on the canonical two-central tower. -/
def OddDegreeGalKSqCyclotomicLevelCardPresentation : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)],
    (_hodd : Odd (Module.finrank ℚ_[2] K)) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        let h := (Module.finrank ℚ_[2] K - 1) / 2
        (∀ U : OpenNormalSubgroup
            (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
            Nonempty (SqCyclotomicFiniteLevelEpiData (K := K) h U)) ∧
          SqTwoCentralLevelCardAgreement (maxProPQuotient 2 (GalK K)) h

/-- Graded numerical form of the field presentation.  Its only reverse-side premise is equality
of the orders of `λₖ/λₖ₊₁` for the arithmetic group and the improved square presentation. -/
def OddDegreeGalKSqCyclotomicLayerCardPresentation : Prop :=
  ∀ (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]
    [CompactSpace (GalK K)] [T2Space (GalK K)]
    [TotallyDisconnectedSpace (GalK K)],
    (_hodd : Odd (Module.finrank ℚ_[2] K)) →
      demushkinQ (maxProPQuotient 2 (GalK K)) = 2 →
        let h := (Module.finrank ℚ_[2] K - 1) / 2
        (∀ U : OpenNormalSubgroup
            (ProfiniteGrp.of (maxProPQuotient 2 (GalK K))),
            Nonempty (SqCyclotomicFiniteLevelEpiData (K := K) h U)) ∧
          SqTwoCentralLayerCardAgreement (maxProPQuotient 2 (GalK K)) h

/-- Graded-layer orders reconstruct the field-facing level-cardinality presentation. -/
theorem oddDegreeGalKSqCyclotomicLevelCardPresentation_of_layerCardPresentation
    (hlayer : OddDegreeGalKSqCyclotomicLayerCardPresentation) :
    OddDegreeGalKSqCyclotomicLevelCardPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, hgraded⟩ := hlayer K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  have hGfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)) :=
    IsTopologicallyFinGen.of_surjective
      (D.forward isProP_maxProPQuotient).toMonoidHom
      (D.forward isProP_maxProPQuotient).continuous_toFun
      (D.forward_surjective isProP_maxProPQuotient) (dsqFinsetTopGen h)
  exact ⟨hforward, twoCentralLevelCardAgreement_of_layerCardAgreement hGfg
    isProP_maxProPQuotient hgraded⟩

/-- Level-cardinality agreement also recovers every graded-layer order. -/
theorem oddDegreeGalKSqCyclotomicLayerCardPresentation_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqCyclotomicLayerCardPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, htower⟩ := hlevel K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  have hGfg : IsTopologicallyFinGen (maxProPQuotient 2 (GalK K)) :=
    IsTopologicallyFinGen.of_surjective
      (D.forward isProP_maxProPQuotient).toMonoidHom
      (D.forward isProP_maxProPQuotient).continuous_toFun
      (D.forward_surjective isProP_maxProPQuotient) (dsqFinsetTopGen h)
  exact ⟨hforward, twoCentralLayerCardAgreement_of_levelCardAgreement hGfg
    isProP_maxProPQuotient htower⟩

/-- The graded-layer and tower-cardinality field seams are exactly equivalent. -/
theorem oddDegreeGalKSqCyclotomicLayerCardPresentation_iff_levelCardPresentation :
    OddDegreeGalKSqCyclotomicLayerCardPresentation ↔
      OddDegreeGalKSqCyclotomicLevelCardPresentation :=
  ⟨oddDegreeGalKSqCyclotomicLevelCardPresentation_of_layerCardPresentation,
    oddDegreeGalKSqCyclotomicLayerCardPresentation_of_levelCardPresentation⟩

/-- The sharpened tower-cardinality presentation supplies the original finite-level seam; the
equivalence theorem above is the only place where the old all-open-normal reverse family is
reconstructed. -/
theorem oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqCyclotomicFiniteLevelPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, hcard⟩ := hlevel K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  exact ⟨hforward,
    D.reverseFiniteQuotientSurjections_of_levelCardAgreement
      isProP_maxProPQuotient hcard⟩

/-- The original all-open-normal formulation also supplies the sharpened level-cardinality
form.  This is the field-facing converse needed to record that no mathematical strength was
added in the refactoring. -/
theorem oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation
    (hfinite : OddDegreeGalKSqCyclotomicFiniteLevelPresentation) :
    OddDegreeGalKSqCyclotomicLevelCardPresentation := by
  intro K _ _ _ _ hodd hq
  dsimp only
  obtain ⟨hforward, hback⟩ := hfinite K hodd hq
  let h := (Module.finrank ℚ_[2] K - 1) / 2
  obtain ⟨D⟩ := forwardGeneratorData_of_finiteLevel h hforward
  exact ⟨hforward,
    (D.reverseFiniteQuotientSurjections_iff_levelCardAgreement
      isProP_maxProPQuotient).mp hback⟩

/-- **Field-facing regression/equivalence.**  The new natural-number-indexed tower-cardinality
seam is exactly the old reverse finite-quotient seam, once the unchanged improved-relator
forward clause is included. -/
theorem oddDegreeGalKSqCyclotomicLevelCardPresentation_iff_finiteLevelPresentation :
    OddDegreeGalKSqCyclotomicLevelCardPresentation ↔
      OddDegreeGalKSqCyclotomicFiniteLevelPresentation :=
  ⟨oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation,
    oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation⟩

/-- **Field-facing graded regression.**  Forward finite value-fibre data plus equality of the
successive layer orders is exactly the original finite-level presentation. -/
theorem oddDegreeGalKSqCyclotomicLayerCardPresentation_iff_finiteLevelPresentation :
    OddDegreeGalKSqCyclotomicLayerCardPresentation ↔
      OddDegreeGalKSqCyclotomicFiniteLevelPresentation :=
  oddDegreeGalKSqCyclotomicLayerCardPresentation_iff_levelCardPresentation.trans
    oddDegreeGalKSqCyclotomicLevelCardPresentation_iff_finiteLevelPresentation

/-- Field-facing endpoint: forward improved-relator finite data plus equality of two-central
quotient orders proves the full oriented Labute classification. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqOrientedLabuteClassification :=
  oddDegreeGalKSqOrientedLabuteClassification_of_finiteLevelPresentation
    (oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation hlevel)

/-- Generator-presentation form of the same sharpened endpoint. -/
theorem oddDegreeGalKSqGeneratorPresentation_of_levelCardPresentation
    (hlevel : OddDegreeGalKSqCyclotomicLevelCardPresentation) :
    OddDegreeGalKSqCyclotomicGeneratorPresentation :=
  oddDegreeGalKSqGeneratorPresentation_of_finiteLevelPresentation
    (oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation hlevel)

/-- Field-facing endpoint from the weakest numerical associated-graded seam. -/
theorem oddDegreeGalKSqOrientedLabuteClassification_of_layerCardPresentation
    (hlayer : OddDegreeGalKSqCyclotomicLayerCardPresentation) :
    OddDegreeGalKSqOrientedLabuteClassification :=
  oddDegreeGalKSqOrientedLabuteClassification_of_levelCardPresentation
    (oddDegreeGalKSqCyclotomicLevelCardPresentation_of_layerCardPresentation hlayer)

/-- Generator-presentation form of the graded-layer endpoint. -/
theorem oddDegreeGalKSqGeneratorPresentation_of_layerCardPresentation
    (hlayer : OddDegreeGalKSqCyclotomicLayerCardPresentation) :
    OddDegreeGalKSqCyclotomicGeneratorPresentation :=
  oddDegreeGalKSqGeneratorPresentation_of_levelCardPresentation
    (oddDegreeGalKSqCyclotomicLevelCardPresentation_of_layerCardPresentation hlayer)

#print axioms sqReverseFiniteQuotientSurjections_iff_twoCentralLevel
#print axioms card_continuousCharacter_eq_card_zLayer_one
#print axioms card_H1_zmodTwo_eq_card_zLayer_one
#print axioms card_continuousCharacter_dsq
#print axioms card_zLayer_one_dsq
#print axioms twoCentralHilbertSeriesAgreement_iff_layerCardAgreement
#print axioms oddDegreeGalKSq_lowerTwoCentralHilbertCoefficient_zero
#print axioms oddDegreeGalKSq_firstTwoLayerCardAgreement
#print axioms lowerTwoCentralH2Inflation
#print axioms lowerTwoCentralH1Inflation_surjective
#print axioms lowerTwoCentralH2Inflation_trivialCupPairing
#print axioms lowerTwoCentralH2InflationSurjective_of_demushkin
#print axioms lowerTwoCentralElementaryH2CardFormula_of_finiteElementary
#print axioms card_levelQuot_two_eq_two_pow_demushkinRank
#print axioms lowerTwoCentralElementaryH2CardFormula_of_demushkin
#print axioms lowerTwoCentralFiveTermCardFormula_of_kernelDuality
#print axioms lowerTwoCentralFiveTermCardFormula_of_kernelDuality_demushkin
#print axioms lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
#print axioms maxProTwoGalK_lowerTwoCentralH2InflationSurjective
#print axioms maxProTwoGalK_lowerTwoCentralElementaryH2CardFormula
#print axioms maxProTwoGalK_lowerTwoCentralFiveTermCardFormula_of_kernelDuality_finiteElementary
#print axioms lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm
#print axioms card_zLayer_two_dr
#print axioms card_zLayer_two_dsq_zero
#print axioms lowerTwoCentralDegreeTwoExpectedCard_dsq_zero
#print axioms dsq_lowerTwoCentralHilbertCoefficient_one_zero
#print axioms maxProTwoGalK_lowerTwoCentralDegreeTwoExpectedCard_of_fiveTerm
#print axioms oddDegreeGalKSq_zLayer_two_cardAgreement_of_degreeTwoSupplies
#print axioms oddDegreeGalKSq_firstThreeLayerCardAgreement_of_degreeTwoSupplies
#print axioms degreeOneGalKSq_zLayer_two_cardAgreement_of_fiveTerm
#print axioms twoCentralLevelMap_surjective
#print axioms card_levelQuot_succ
#print axioms twoCentralLevelCardAgreement_of_layerCardAgreement
#print axioms twoCentralLayerCardAgreement_of_levelCardAgreement
#print axioms twoCentralLayerCardAgreement_iff_levelCardAgreement
#print axioms nonempty_reverseTwoCentralLevel_of_card_eq
#print axioms reverseFiniteQuotientSurjections_of_twoCentralLevelCardAgreement
#print axioms twoCentralLevelCardAgreement_of_reverseFiniteQuotientSurjections
#print axioms reverseFiniteQuotientSurjections_iff_twoCentralLevelCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_levelCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_levelCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_of_layerCardAgreement
#print axioms SqCyclotomicForwardGeneratorData.reverseFiniteQuotientSurjections_iff_layerCardAgreement
#print axioms oddDegreeGalKSqCyclotomicLayerCardPresentation_iff_levelCardPresentation
#print axioms oddDegreeGalKSqCyclotomicFiniteLevelPresentation_of_levelCardPresentation
#print axioms oddDegreeGalKSqCyclotomicLevelCardPresentation_of_finiteLevelPresentation
#print axioms oddDegreeGalKSqCyclotomicLevelCardPresentation_iff_finiteLevelPresentation
#print axioms oddDegreeGalKSqCyclotomicLayerCardPresentation_iff_finiteLevelPresentation
#print axioms oddDegreeGalKSqOrientedLabuteClassification_of_levelCardPresentation
#print axioms oddDegreeGalKSqOrientedLabuteClassification_of_layerCardPresentation

end

end GQ2.Dyadic.LSquare
