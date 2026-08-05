/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Instances.GammaLSylowPreimageMarkedFrame
import GQ2.UnramifiedQuadraticNorms
import GQ2.UnramifiedNorm
import GQ2.Dyadic.RamificationInertiaBridge

/-!
# The unramified Hilbert value `(2, u)_K = −1`

`GammaLSylowPreimageMarkedFrame` §4 isolates one `𝔽₂` number as the whole cost of the marked
Frattini frame: `NuUrOmegaCupOne B`, the cup value `b_K([2], ν̄) = 1`.  This file supplies the
two halves of that number which are *arithmetic*, and names precisely the one half which is not.

## What is proved

* **§1 the cup ⟺ Hilbert dictionary.**  `cupFormK_kummer_eq_zero_iff` and
  `cupFormK_kummer_eq_one_iff`: for `a b : Kˣ`,
  `b_K([a],[b]) = 0 ↔ b = x² − a y²` is solvable, and (since the values live in `𝔽₂`)
  `b_K([a],[b]) = 1` exactly when it is not.  This is `hilbertSymbol_normCriterion_finiteDyadic`
  (**B11a**) read through `FieldData.cupFormK = inv_K ∘ ⌣`; the invariant map is an `AddEquiv`,
  so it neither creates nor destroys the vanishing.
* **§2 the norm computation** `not_normForm_two_of_unramified`: over an **odd-degree** `K`, `2` is
  **not** a norm from an unramified quadratic `K(δa)/K`.  This is the sharp opposite of B11b
  (`unramifiedQuadratic_units_are_norms`, which makes every *unit* a norm): a norm
  `2 = z·σz` forces `‖z‖² = ‖2‖`, equal value groups pull `‖z‖` back to `‖w‖` for some `w ∈ K`,
  discreteness writes `‖w‖ = ‖π‖^m`, and `‖2‖ = ‖π‖^e` then reads `e = 2m`.  The fundamental
  identity `n = e·f` (`SpectralLocalField.field_finrank_eq_e_mul_f`) makes `e` odd whenever `n`
  is, and the contradiction is closed.  Combined with §1: `b_K([u],[2]) = 1` — the value
  `(2, u)_K = −1` of the file title, for **any** unit `u` cutting out an unramified quadratic
  extension.
* **§3 the assembly** `nuUrOmegaCupOne_of_unramifiedKummerClass`: `NuUrOmegaCupOne B` follows from
  §§1–2 together with one identification, `ν̄ = [u]` in `H¹(G_K, 𝔽₂)`.  The `ω` side needs no
  hypothesis: `cyclotomicModEightOmegaClassK_eq_kummerTwo` already proves `ω = [2]` by a cocycle
  computation.  `NuUrUnramifiedKummerClass` packages the identification as a `def`-shaped `Prop`
  (never an axiom), and `nuUrOmegaCupOne_of_nuUrUnramifiedKummerClass` is the one-line consumer.
  The nonsquareness `δu ∉ K` is *not* part of the datum: at the level-`L` row `r = 0` it follows
  from `ν̄ ≠ 0` (`nuUrModTwoClassKTwo_ne_zero`, §2 of the frame file at `a = c = 0`) through
  `sqrt_notMem_of_kummerClass_ne_zero`.

## The residual, exactly

`NuUrUnramifiedKummerClass B` is an **Artin ⟷ Kummer** statement and nothing less: it says the
character `ν̄`, which the `MarkedRecip` bundle pins only *through* `rec_K` (`nu_ur_recip_unit`,
`nu_ur_recip_uniformizer`), is the Galois character `g ↦ g(√u)/√u` of an unramified `u`.  Nothing
in `MarkedRecip` connects `rec_K` to Galois cohomology over `K`: the finite-layer norm-residue
clause `(a_K)` is deliberately omitted from the bundle, and its mod-2 shadow is exactly
`ModTwoTateKummerArtinCompatibility`.  Note that the *value* is now free of that compatibility —
only the *identification of the class* is not, and §2 is what the compatibility would otherwise
have to be combined with.

There is a route to the identification that does **not** need the missing `K`-layer clause, since
the norm-residue theorem *is* carried at the base by **B5** (`LocalReciprocity.norm_reciprocity`,
`nu_ur_recip : ν_ur ∘ rec = −v₂`).  In three steps, none of them formalized here:

1. *At `ℚ₂`.*  Take `F = ℚ₂(√−3)`, the unramified quadratic layer (`−3 ≡ 5 (mod 8)`).  It is
   abelian Galois, so `norm_reciprocity F` says `rec` induces `ℚ₂ˣ ↠ Gal(F/ℚ₂)` with kernel
   `N(Fˣ)`; `N(Fˣ) = {v₂ even}` (⊆ by `‖N z‖ = ‖z‖²` and equal value groups, ⊇ by B11b plus
   `4 = N 2`).  The Kummer character of `−3` has the same kernel on `rec(ℚ₂ˣ)`, so by
   `denseRange_recip` the mod-2 unramified character of `G_{ℚ₂}` **is** `[−3]`.
2. *Down to `K`.*  `MarkedRecip.norm_compat` (`incl∗ ∘ rec_K = rec ∘ N_{K/ℚ₂}`) plus
   `nu_ur_recip` give `ν_ur ∘ incl∗ = (ν_ur^K)^f` on `rec_K(Kˣ)`, hence everywhere by
   `denseRange_recip`; `f ∣ n` is odd, so mod `2` the restriction of `ν̄_{ℚ₂}` to `G_K` is `ν̄_K`.
   The valuation input is `v₂(N x) = f · v_K(x)`, i.e. `UnitNormIndex.e_mul_val_norm` widened off
   `[IsGalois ℚ_[2] F]` (only `‖N x‖ = ‖x‖ ^ n` is needed, and that is
   `Algebra.norm_eq_prod_embeddings` against `UnramifiedQuadraticNorms.norm_galois`).
3. *The Kummer class restricts on the nose.*  `kummerClassK` is `H1mk` of `g ↦ kummerCocycleFun`
   evaluated at `(g : Kummer.GaloisGroup ℚ_[2])`, the **same** function for every base, so
   `[−3]_K` is literally `[−3]_{ℚ₂}` restricted; and `K(√−3)/K` is unramified because
   `ℚ₂(√−3)/ℚ₂` is (this last step is the one genuinely new analytic obligation, an odd-order
   root-of-unity separation argument of the `le_of_conj_residue_trivial`/`TeichmullerLift` kind).

## Axioms

§1 is std-3 + **B11a** + **B6** (the latter only definitionally, through `FieldData.cupFormK`).
§2 is std-3 (its `DyadicUnitFiltration` argument is proved in-repository, B13 being a `def` since
the 2026-07-24 flip).  §3 is std-3 + **B6** + **B11a**.  The `#print axioms` block at the end of
the file is the record.  No `sorry`, no new axiom, no `native_decide`.
-/

namespace GQ2.Dyadic.LSquare

noncomputable section

open GQ2 ContCoh
open FrattiniFrameSupply

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

namespace MarkedFrame

/-! ## §1 The cup form against the Hilbert norm criterion

`FieldData.cupFormK K x y = inv_K(x ⌣ y)` with `inv_K` an `AddEquiv`, so the cup form vanishes
exactly when the cup product does; B11a turns the latter into the solvability of the norm form.
Over `𝔽₂` "not zero" is "one", which is the shape the frame consumer wants. -/

section Dictionary

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

/-- **The dictionary, vanishing form.**  `b_K([a],[b]) = 0` exactly when `b` is represented by
the norm form `x² − a y²` of `K(√a)`, i.e. exactly when the Hilbert symbol `(a,b)_K` is `+1`. -/
theorem cupFormK_kummer_eq_zero_iff (a b : (↥K)ˣ) :
    FieldData.cupFormK K (kummerClassK K a) (kummerClassK K b) = 0 ↔
      ∃ x y : ↥K, (b : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  rw [← hilbertSymbol_normCriterion_finiteDyadic K (FieldData.smul_zmodTwo_galK K) a b]
  constructor
  · intro h
    exact (FieldData.invGalK K).injective (h.trans (map_zero (FieldData.invGalK K)).symm)
  · intro h
    show FieldData.invGalK K _ = 0
    rw [h, map_zero]

/-- **The dictionary, value form.**  The cup value is the mod-two Hilbert symbol: `b_K([a],[b])`
is `1` exactly when `b` is *not* a norm from `K(√a)`. -/
theorem cupFormK_kummer_eq_one_iff (a b : (↥K)ˣ) :
    FieldData.cupFormK K (kummerClassK K a) (kummerClassK K b) = 1 ↔
      ¬ ∃ x y : ↥K, (b : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  rw [← cupFormK_kummer_eq_zero_iff K a b]
  rcases ZMod.eq_zero_or_eq_one (FieldData.cupFormK K (kummerClassK K a) (kummerClassK K b))
    with h | h <;> rw [h] <;> simp

end Dictionary

/-! ## §2 Two is not a norm from an unramified quadratic extension, in odd degree

B11b (`unramifiedQuadratic_units_are_norms`) says the norm group of an unramified quadratic
`K(δa)/K` contains every unit.  The complementary fact is proved here from the same
spectral-norm vocabulary, at the one element that matters: `2`, whose `K`-valuation is the
absolute ramification index `e`, odd exactly when `[K : ℚ₂]` is. -/

section NormSide

variable {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]

/-- **`e` is odd in odd degree.**  The fundamental identity `n = e·f` of the filtration
(`SpectralLocalField.field_finrank_eq_e_mul_f`) makes `e` a divisor of `n`. -/
theorem odd_filtration_e_of_odd_finrank (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) : Odd FF.e := by
  rw [SpectralLocalField.field_finrank_eq_e_mul_f (K := K) (FF := FF)] at hodd
  exact (Nat.odd_mul.mp hodd).1

/-- **The norm computation.**  If `K(δa)/K` is a genuine quadratic extension with equal norm
value groups (the repository's unramifiedness convention) and `[K : ℚ₂]` is odd, then `2` is not
represented by the norm form of `a`; equivalently `2 ∉ N(K(δa)ˣ)`, i.e. `(a, 2)_K = −1`.

A representation `2 = x² − a y²` is the norm `z·σz` of `z = x + yδa`, so `‖z‖² = ‖2‖`.  Equal
value groups produce `w ∈ Kˣ` with `‖w‖ = ‖z‖`, discreteness of the value group writes
`‖w‖ = ‖π‖^m`, and the normalization `‖2‖ = ‖π‖^e` then forces `e = 2m`. -/
theorem not_normForm_two_of_unramified (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K) (hunram : HasEqualNormValueGroups K δa) :
    ¬ ∃ x y : ↥K, ((twoUnit K : (↥K)ˣ) : ↥K) = x ^ 2 - (a : ↥K) * y ^ 2 := by
  rintro ⟨x, y, hxy⟩
  obtain ⟨σ, hσ⟩ := UnramifiedQuadraticNorms.exists_conj hδ2 hδk
  have htwo : ((x ^ 2 - (a : ↥K) * y ^ 2 : ↥K) : ℚ̄₂) = (2 : ℚ̄₂) := by
    rw [← hxy]
    show (((2 : ↥K)) : ℚ̄₂) = (2 : ℚ̄₂)
    exact map_ofNat (algebraMap (↥K) ℚ̄₂) 2
  have hprod : ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) * σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa) = (2 : ℚ̄₂) := by
    rw [UnramifiedQuadraticNorms.conj_apply hσ, UnramifiedQuadraticNorms.norm_coord hδ2, htwo]
  have hz0 : (x : ℚ̄₂) + (y : ℚ̄₂) * δa ≠ 0 := by
    intro h
    rw [h, zero_mul] at hprod
    exact two_ne_zero hprod.symm
  have hconj : ‖σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa)‖ = ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ :=
    UnramifiedQuadraticNorms.norm_conj_eq K σ _
  have hzz : ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ * ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ = ‖(2 : ℚ̄₂)‖ := by
    calc ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖ * ‖(x : ℚ̄₂) + (y : ℚ̄₂) * δa‖
        = ‖((x : ℚ̄₂) + (y : ℚ̄₂) * δa) * σ ((x : ℚ̄₂) + (y : ℚ̄₂) * δa)‖ := by
          rw [norm_mul, hconj]
      _ = ‖(2 : ℚ̄₂)‖ := by rw [hprod]
  obtain ⟨w, hw0, hw⟩ := hunram _ hz0 ⟨x, y, rfl⟩
  have hwne : ((w : ↥K) : ℚ̄₂) ≠ 0 := fun h => hw0 (by exact_mod_cast h)
  obtain ⟨m, hm⟩ := UnramifiedNorm.norm_eq_zpow FF (SetLike.coe_mem w) hwne
  have hπ0 : ‖FF.π‖ ≠ 0 := (norm_pos_iff.mpr FF.hπ_ne).ne'
  have hpow : ‖FF.π‖ ^ (2 * m) = ‖FF.π‖ ^ ((FF.e : ℤ)) := by
    rw [two_mul, zpow_add₀ hπ0, ← hm, ← hw, hzz, FF.he, zpow_natCast]
  have he2 : (FF.e : ℤ) = 2 * m :=
    (zpow_right_injective₀ (norm_pos_iff.mpr FF.hπ_ne) (ne_of_lt FF.hπ_lt) hpow).symm
  obtain ⟨j, hj⟩ := odd_filtration_e_of_odd_finrank FF hodd
  omega

/-- **The Hilbert value.**  In odd degree the symbol `(u, 2)_K` is `−1` for every `u` cutting out
an unramified quadratic extension — the `𝔽₂` number `NuUrOmegaCupOne` is made of. -/
theorem cupFormK_kummer_unramified_two_eq_one (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K) (hunram : HasEqualNormValueGroups K δa) :
    FieldData.cupFormK K (kummerClassK K a) (kummerClassK K (twoUnit K)) = 1 :=
  (cupFormK_kummer_eq_one_iff K a (twoUnit K)).mpr
    (not_normForm_two_of_unramified FF hodd hδ2 hδk hunram)

/-- The same value in the order the frame reads it (`ω` in the left slot), by symmetry of the cup
form in characteristic two. -/
theorem cupFormK_two_kummer_unramified_eq_one (FF : DyadicUnitFiltration K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) {a : (↥K)ˣ} {δa : ℚ̄₂}
    (hδ2 : δa ^ 2 = ((a : ↥K) : ℚ̄₂)) (hδk : δa ∉ K) (hunram : HasEqualNormValueGroups K δa) :
    FieldData.cupFormK K (kummerClassK K (twoUnit K)) (kummerClassK K a) = 1 := by
  rw [(FieldData.isCupFormFp2_cupFormK K).symm]
  exact cupFormK_kummer_unramified_two_eq_one FF hodd hδ2 hδk hunram

end NormSide

/-! ## §3 The frame value, over the single remaining identification

`ω` is already known to be `[2]` (`cyclotomicModEightOmegaClassK_eq_kummerTwo`, a cocycle
computation, no reciprocity).  So `NuUrOmegaCupOne B` reduces to §2 the moment `ν̄` is known to be
the Kummer class of an unramified unit. -/

section Assembly

variable {R : LocalReciprocity} {K : IntermediateField ℚ_[2] ℚ̄₂} [FiniteDimensional ℚ_[2] K]
  [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)]

local instance : DistribMulAction (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo _

local instance : ContinuousSMul (maxProPQuotient 2 (GalK K)) (ZMod 2) :=
  scalarActionZmodTwo_continuousSMul _

/-- `ν̄ ≠ 0`: the level clause at `r = 0` produces an element on which `ν̄` reads `1`.  (This is
`nuUrModTwoClassKTwo_ne_smul_add_smul` at `a = c = 0`.) -/
theorem nuUrModTwoClassKTwo_ne_zero (B : MarkedRecip R K) (hr : B.r = 0) :
    nuUrModTwoClassKTwo B ≠ 0 := by
  have h := nuUrModTwoClassKTwo_ne_smul_add_smul B hr 0 0
  simpa using h

omit [FiniteDimensional ℚ_[2] K] [CompactSpace (GalK K)] [TotallyDisconnectedSpace (GalK K)] in
/-- A square root of a Kummer class's representative cannot lie in `K` once the class is
nonzero: `δu ∈ K` makes `u` a square, and `[v²] = 0`. -/
theorem sqrt_notMem_of_kummerClass_ne_zero {u : (↥K)ˣ} {δu : ℚ̄₂}
    (hδ2 : δu ^ 2 = ((u : ↥K) : ℚ̄₂)) (hne : kummerClassK K u ≠ 0) : δu ∉ K := by
  intro hmem
  have hδ0 : (⟨δu, hmem⟩ : ↥K) ≠ 0 := by
    intro h
    apply u.ne_zero
    have : δu = 0 := congrArg Subtype.val h
    have h2 : ((u : ↥K) : ℚ̄₂) = 0 := by rw [← hδ2, this]; ring
    exact_mod_cast h2
  refine hne ?_
  have hsq : (Units.mk0 (⟨δu, hmem⟩ : ↥K) hδ0) * (Units.mk0 (⟨δu, hmem⟩ : ↥K) hδ0) = u := by
    apply Units.ext
    apply Subtype.ext
    show δu * δu = ((u : ↥K) : ℚ̄₂)
    rw [← hδ2]; ring
  rw [← hsq, kummerClassK_mul_self]

/-- **The residual identification**, as a `def`-shaped `Prop` (never an axiom): the mod-two
unramified character `ν̄` of the bundle is the Kummer class of a unit `u` whose square root
generates an unramified quadratic extension of `K`.

This is an Artin ⟷ Kummer statement.  `MarkedRecip` pins `ν_ur` only through `rec_K`, and carries
no clause relating `rec_K` to Galois cohomology over `K`; the mod-two form of the missing clause
is `ModTwoTateKummerArtinCompatibility`.  Once this datum is available, §§1–2 give the cup value
outright — in particular the value costs **no** further arithmetic.

Note what is *not* asked for: `δu ∉ K` (i.e. that `u` is a genuine nonsquare) is a *consequence*
at level `r = 0`, by `sqrt_notMem_of_kummerClass_ne_zero` against `nuUrModTwoClassKTwo_ne_zero`. -/
def NuUrUnramifiedKummerClass (B : MarkedRecip R K) : Prop :=
  ∃ (u : (↥K)ˣ) (δu : ℚ̄₂), δu ^ 2 = ((u : ↥K) : ℚ̄₂) ∧
    HasEqualNormValueGroups K δu ∧
    h1MaxProTwoEquivGalK (K := K) (nuUrModTwoClassKTwo B) = kummerClassK K u

/-- **The cup value from the identification.**  `b_K([2], ν̄) = 1` for an odd-degree `K`, given
that `ν̄` is the Kummer class of an unramified unit. -/
theorem nuUrOmegaCupOne_of_unramifiedKummerClass (B : MarkedRecip R K)
    (FF : DyadicUnitFiltration K) (hodd : Odd (Module.finrank ℚ_[2] K)) {u : (↥K)ˣ} {δu : ℚ̄₂}
    (hδ2 : δu ^ 2 = ((u : ↥K) : ℚ̄₂)) (hδk : δu ∉ K) (hunram : HasEqualNormValueGroups K δu)
    (hclass : h1MaxProTwoEquivGalK (K := K) (nuUrModTwoClassKTwo B) = kummerClassK K u) :
    NuUrOmegaCupOne B := by
  show frattiniFrameCup _ _ = 1
  rw [frattiniFrameCup, hclass, h1MaxProTwoEquivGalK_cyclotomicModEightOmegaClassKTwo,
    cyclotomicModEightOmegaClassK_eq_kummerTwo]
  exact cupFormK_two_kummer_unramified_eq_one FF hodd hδ2 hδk hunram

/-- The packaged consumer: the residual `Prop` of this file discharges the residual `Prop` of
`GammaLSylowPreimageMarkedFrame` §4, in odd degree, at the level-`L` row `r = 0`.  The `r = 0`
hypothesis is used only to see that `ν̄ ≠ 0`, hence that `u` is a nonsquare; it is exactly the
hypothesis the frame consumer `oddDegreeGalKSqMarkedForwardSupply` already carries. -/
theorem nuUrOmegaCupOne_of_nuUrUnramifiedKummerClass (B : MarkedRecip R K)
    (hodd : Odd (Module.finrank ℚ_[2] K)) (hr : B.r = 0) (h : NuUrUnramifiedKummerClass B) :
    NuUrOmegaCupOne B := by
  obtain ⟨u, δu, hδ2, hunram, hclass⟩ := h
  have hne : kummerClassK K u ≠ 0 := by
    rw [← hclass]
    intro h0
    exact nuUrModTwoClassKTwo_ne_zero B hr
      ((h1MaxProTwoEquivGalK (K := K)).injective (h0.trans (map_zero _).symm))
  exact nuUrOmegaCupOne_of_unramifiedKummerClass B (dyadicUnitFiltration K) hodd hδ2
    (sqrt_notMem_of_kummerClass_ne_zero hδ2 hne) hunram hclass

end Assembly

end MarkedFrame

end

#print axioms MarkedFrame.cupFormK_kummer_eq_zero_iff
#print axioms MarkedFrame.cupFormK_kummer_eq_one_iff
#print axioms MarkedFrame.odd_filtration_e_of_odd_finrank
#print axioms MarkedFrame.not_normForm_two_of_unramified
#print axioms MarkedFrame.cupFormK_kummer_unramified_two_eq_one
#print axioms MarkedFrame.cupFormK_two_kummer_unramified_eq_one
#print axioms MarkedFrame.nuUrModTwoClassKTwo_ne_zero
#print axioms MarkedFrame.sqrt_notMem_of_kummerClass_ne_zero
#print axioms MarkedFrame.NuUrUnramifiedKummerClass
#print axioms MarkedFrame.nuUrOmegaCupOne_of_unramifiedKummerClass
#print axioms MarkedFrame.nuUrOmegaCupOne_of_nuUrUnramifiedKummerClass

end GQ2.Dyadic.LSquare
