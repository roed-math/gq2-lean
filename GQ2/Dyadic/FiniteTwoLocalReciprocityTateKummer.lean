/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.FiniteTwoLocalReciprocityKummer
import GQ2.Dyadic.FieldData

/-!
# The local Tate--Kummer--Artin compatibility seam

Local Tate duality makes the mod-`2` cup pairing on `H¹(G_K, 𝔽₂)` perfect, and the in-repository
Kummer theorem identifies `Kˣ/(Kˣ)²` with that cohomology group.  These facts alone do **not**
identify the resulting pairing with evaluation on the marked reciprocity map.  The missing
classical local-CFT statement is the Artin/Hilbert formula

`χ_x(rec_K(a)) = inv_K(x ∪ κ(a))`.

This file states that formula using canonical objects already present in the repository and
proves that it supplies every mod-`2` reciprocity character.  It also gives the equivalent
kernel form, which pinpoints the absent finite-layer norm-residue theorem.  No new axiom is
introduced: every result is parametrized over the compatibility proposition.

The higher `2^m` layers remain genuinely separate.  The repository has neither higher-power
Kummer classes nor the corresponding Artin-pairing compatibility; the exact all-layer target
continues to be `FiniteCyclicTwoReciprocitySupply`.
-/

namespace GQ2.Dyadic

open ContCoh

noncomputable section

local notation "ℚbar2" => AlgebraicClosure ℚ_[2]

variable {R : LocalReciprocity}
  {K : IntermediateField ℚ_[2] ℚbar2} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

/-! ## Canonical characters attached to mod-2 cohomology classes -/

/-- A mod-`2` cohomology class, regarded as a continuous character of `G_K`.  The coefficient
action is trivial, so `B¹ = 0` and `H¹ = Z¹`; this construction involves no choice of cocycle. -/
def h1GalKCharacter (x : H1 (GalK K) (ZMod 2)) :
    ContinuousMonoidHom (GalK K) (Multiplicative (ZMod 2)) := by
  let z : Z1 (GalK K) (ZMod 2) :=
    H1equivZ1OfTrivial (FieldData.smul_zmodTwo_galK K) x
  exact
    { toFun := fun g => Multiplicative.ofAdd (z.1 g)
      map_one' := congrArg Multiplicative.ofAdd (Z1_apply_one z)
      map_mul' := fun g h => congrArg Multiplicative.ofAdd
        (((mem_Z1_iff_of_trivial (FieldData.smul_zmodTwo_galK K)).mp z.2).2 g h)
      continuous_toFun :=
        ((mem_Z1_iff_of_trivial (FieldData.smul_zmodTwo_galK K)).mp z.2).1 }

/-- `Multiplicative 𝔽₂` is a pro-`2` group. -/
theorem isProPTwo_multiplicativeZModTwo_tateKummer :
    IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- The canonical mod-`2` character on `G_K(2)^ab` attached to a class in `H¹(G_K, 𝔽₂)`. -/
def h1GalKMaxProTwoAbCharacter (x : H1 (GalK K) (ZMod 2)) :
    ContinuousMonoidHom
      (topAbelianization (maxProPQuotient 2 (GalK K))) (Multiplicative (ZMod 2)) :=
  SectionThree.abLiftG
    ((maxProPHomEquiv isProPTwo_multiplicativeZModTwo_tateKummer).symm
      (h1GalKCharacter (K := K) x))

/-- Evaluation of the descended character on an abelianized maximal-pro-`2` image agrees with
the original `H¹` character. -/
@[simp] theorem h1GalKMaxProTwoAbCharacter_topAbToTopAbMaxProP
    (x : H1 (GalK K) (ZMod 2)) (g : GalK K) :
    h1GalKMaxProTwoAbCharacter (K := K) x
        (topAbToTopAbMaxProP (p := 2) (GalK K) (SectionThree.abMk g)) =
      h1GalKCharacter (K := K) x g := by
  rw [topAbToTopAbMaxProP_abMk, h1GalKMaxProTwoAbCharacter,
    SectionThree.abLiftG_abMk, maxProPHomEquiv_symm_apply_maxProPMk]

/-! ## The precise missing compatibility -/

/-- **Mod-`2` Tate--Kummer--Artin compatibility.**  The canonical Galois character attached to
`x ∈ H¹(G_K, 𝔽₂)`, evaluated on the marked Artin symbol of `a`, is the local Tate pairing of
`x` with the Kummer class of `a`.

This is the standard Hilbert-symbol/Artin-reciprocity formula.  It is not a consequence of the
current `MarkedRecip` fields: those contain norm functoriality to `ℚ₂`, but no finite-layer
norm-residue theorem over `K`. -/
def ModTwoTateKummerArtinCompatibility (B : MarkedRecip R K) : Prop :=
  ∀ (x : H1 ↥(K.fixingSubgroup) (ZMod 2)) (a : (↥K)ˣ),
    h1GalKMaxProTwoAbCharacter (K := K) x
        (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) =
      Multiplicative.ofAdd (FieldData.cupFormK K x (kummerClassK K a))

/-- Kernel-only form of the Artin/Hilbert compatibility.  Since `𝔽₂` has two elements, equality
of the two characters is equivalent to agreement of their kernels. -/
def ModTwoTateKummerKernelCompatibility (B : MarkedRecip R K) : Prop :=
  ∀ (x : H1 ↥(K.fixingSubgroup) (ZMod 2)) (a : (↥K)ˣ),
    h1GalKMaxProTwoAbCharacter (K := K) x
          (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = 1 ↔
      FieldData.cupFormK K x (kummerClassK K a) = 0

/-- The pointwise Artin formula implies its finite-layer kernel form. -/
theorem ModTwoTateKummerArtinCompatibility.kernelCompatibility
    {B : MarkedRecip R K} (H : ModTwoTateKummerArtinCompatibility B) :
    ModTwoTateKummerKernelCompatibility B := by
  intro x a
  rw [H x a]
  rfl

/-- Over `𝔽₂`, the kernel form recovers the full pointwise Artin formula. -/
theorem ModTwoTateKummerKernelCompatibility.artinCompatibility
    {B : MarkedRecip R K} (H : ModTwoTateKummerKernelCompatibility B) :
    ModTwoTateKummerArtinCompatibility B := by
  intro x a
  apply Multiplicative.toAdd.injective
  let u := (h1GalKMaxProTwoAbCharacter (K := K) x
    (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a))).toAdd
  let v := FieldData.cupFormK K x (kummerClassK K a)
  change u = v
  rcases ZMod.eq_zero_or_eq_one u with hu | hu <;>
    rcases ZMod.eq_zero_or_eq_one v with hv | hv
  · exact hu.trans hv.symm
  · exfalso
    have hker := (H x a).mp
      (Multiplicative.toAdd.injective (by simpa [u] using hu))
    exact zero_ne_one (hker.symm.trans hv)
  · exfalso
    have hker := (H x a).mpr hv
    have : u = 0 := by
      exact congrArg Multiplicative.toAdd hker
    exact zero_ne_one (this.symm.trans hu)
  · exact hu.trans hv.symm

/-- **Regression:** the pointwise and finite-layer kernel formulations of the mod-`2`
Artin/Hilbert theorem are equivalent. -/
theorem modTwoTateKummerArtinCompatibility_iff_kernel (B : MarkedRecip R K) :
    ModTwoTateKummerArtinCompatibility B ↔
      ModTwoTateKummerKernelCompatibility B :=
  ⟨ModTwoTateKummerArtinCompatibility.kernelCompatibility,
    ModTwoTateKummerKernelCompatibility.artinCompatibility⟩

/-- Classical finite-layer spelling of the missing theorem: the quadratic Galois character
attached to `b` kills `rec_K(a)` exactly when `a` is a norm from `K(√b)`, written as the norm
form `x² - b y²`. -/
def ModTwoArtinNormCompatibility (B : MarkedRecip R K) : Prop :=
  ∀ (b a : (↥K)ˣ),
    h1GalKMaxProTwoAbCharacter (K := K) (kummerClassK K b)
          (topAbToTopAbMaxProP (p := 2) (GalK K) (B.recip a)) = 1 ↔
      ∃ x y : ↥K, (a : ↥K) = x ^ 2 - (b : ↥K) * y ^ 2

/-- The mod-`2` Tate kernel condition is exactly the quadratic norm-residue theorem.  The
right-hand identification uses the repository's B11a Hilbert-symbol norm criterion; Kummer
surjectivity lets the converse reduce an arbitrary `H¹` class to a Kummer class. -/
theorem modTwoTateKummerKernelCompatibility_iff_artinNorm
    (B : MarkedRecip R K) :
    ModTwoTateKummerKernelCompatibility B ↔ ModTwoArtinNormCompatibility B := by
  constructor
  · intro H b a
    rw [H (kummerClassK K b) a]
    change FieldData.invGalK K
        (kummerClassK K b ⌣[FieldData.smul_zmodTwo_galK K] kummerClassK K a) = 0 ↔ _
    rw [map_eq_zero_iff (FieldData.invGalK K) (FieldData.invGalK K).injective]
    exact hilbertSymbol_normCriterion_finiteDyadic K
      (FieldData.smul_zmodTwo_galK K) b a
  · intro H x a
    obtain ⟨b, rfl⟩ := kummerClassK_surjective K x
    rw [H b a]
    change (∃ u v : ↥K, (a : ↥K) = u ^ 2 - (b : ↥K) * v ^ 2) ↔
      FieldData.invGalK K
        (kummerClassK K b ⌣[FieldData.smul_zmodTwo_galK K] kummerClassK K a) = 0
    rw [map_eq_zero_iff (FieldData.invGalK K) (FieldData.invGalK K).injective]
    exact (hilbertSymbol_normCriterion_finiteDyadic K
      (FieldData.smul_zmodTwo_galK K) b a).symm

/-- **Exact literature-strength regression.**  The pointwise Tate--Kummer--Artin formula is
equivalent to the quadratic finite-layer norm-residue theorem.  Thus local Tate duality and
the existing Hilbert-symbol norm criterion leave precisely the reciprocity/norm compatibility,
not an additional cohomological calculation. -/
theorem modTwoTateKummerArtinCompatibility_iff_artinNorm
    (B : MarkedRecip R K) :
    ModTwoTateKummerArtinCompatibility B ↔ ModTwoArtinNormCompatibility B :=
  (modTwoTateKummerArtinCompatibility_iff_kernel B).trans
    (modTwoTateKummerKernelCompatibility_iff_artinNorm B)

/-! ## Consequence: every mod-2 character factors -/

/-- Convert a multiplicative functional on the additive group `H¹` into its additive spelling. -/
def modTwoKummerFunctionalToAdd
    (ell : Multiplicative (H1 ↥(K.fixingSubgroup) (ZMod 2)) →*
      Multiplicative (ZMod 2)) :
    H1 ↥(K.fixingSubgroup) (ZMod 2) →+ ZMod 2 where
  toFun x := Multiplicative.toAdd (ell (Multiplicative.ofAdd x))
  map_zero' := congrArg Multiplicative.toAdd (map_one ell)
  map_add' x y := congrArg Multiplicative.toAdd
    (map_mul ell (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))

/-- Local Tate perfectness represents every functional on `H¹(G_K,𝔽₂)` by a cup-pairing row.
This is the B6 part of the reduction; the subsequent evaluation on `rec_K` is exactly the
separate Artin compatibility hypothesis. -/
theorem exists_cupFormK_row_eq_modTwoKummerFunctional
    (ell : Multiplicative (H1 ↥(K.fixingSubgroup) (ZMod 2)) →*
      Multiplicative (ZMod 2)) :
    ∃ x : H1 ↥(K.fixingSubgroup) (ZMod 2), ∀ y,
      FieldData.cupFormK K x y = modTwoKummerFunctionalToAdd (K := K) ell y := by
  let D := FieldData.tateDualityGalK K
  let e := H1congr (G := ↥(K.fixingSubgroup)) zmodMuDualEquiv
    zmodMuDualEquiv_equivariant
  obtain ⟨c, hc⟩ := (D.perfect11 (ZMod 2) (by decide)).2
    (modTwoKummerFunctionalToAdd (K := K) ell)
  refine ⟨e.symm c, fun y => ?_⟩
  have hcval := DFunLike.congr_fun hc y
  change D.inv
      (cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)) c y) =
    modTwoKummerFunctionalToAdd (K := K) ell y at hcval
  rw [← e.apply_symm_apply c, FieldData.cup11_muDual_eq_cup_mul K] at hcval
  exact hcval

/-- **The missing Artin formula closes the whole mod-`2` reciprocity layer.**  Perfectness of
the local Tate pairing first writes an arbitrary Kummer functional as a cup row; the pointwise
compatibility then identifies that row with evaluation of the canonical Galois character. -/
theorem ModTwoTateKummerArtinCompatibility.toModTwoKummerReciprocitySupply
    {B : MarkedRecip R K} (H : ModTwoTateKummerArtinCompatibility B) :
    ModTwoKummerReciprocitySupply B := by
  intro ell
  obtain ⟨x, hx⟩ := exists_cupFormK_row_eq_modTwoKummerFunctional (K := K) ell
  refine ⟨h1GalKMaxProTwoAbCharacter (K := K) x, fun a => ?_⟩
  rw [H x a]
  apply Multiplicative.toAdd.injective
  change FieldData.cupFormK K x (kummerClassK K a) =
    Multiplicative.toAdd (ell (Multiplicative.ofAdd (kummerClassK K a)))
  exact hx (kummerClassK K a)

/-- Hence the pointwise Tate--Kummer--Artin formula implies factorization of every mod-`2`
character of `Kˣ`. -/
theorem ModTwoTateKummerArtinCompatibility.toModTwoReciprocityCharacterSupply
    {B : MarkedRecip R K} (H : ModTwoTateKummerArtinCompatibility B) :
    ModTwoReciprocityCharacterSupply B :=
  (modTwoReciprocityCharacterSupply_iff_kummer B).mpr
    H.toModTwoKummerReciprocitySupply

/-! The implication above stops at the first cyclic layer.  A pro-`2` completion is not
separated by mod-`2` characters alone; completed injectivity still requires the full family of
cyclic `2^m` characters encoded by `FiniteCyclicTwoReciprocitySupply`. -/

#print axioms exists_cupFormK_row_eq_modTwoKummerFunctional
#print axioms modTwoTateKummerArtinCompatibility_iff_artinNorm
#print axioms ModTwoTateKummerArtinCompatibility.toModTwoReciprocityCharacterSupply

end

end GQ2.Dyadic
