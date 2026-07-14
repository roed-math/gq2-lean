import Mathlib
import GQ2.Cohomology

/-!
# The mod-2 Kummer class `kˣ → H¹(k, 𝔽₂)`  (ticket T-13, infra I5)

For a field `k` of characteristic `≠ 2` (we assume `CharZero k`, which covers `ℚ₂` and all of its
finite extensions — the fields the paper works over) and `a ∈ kˣ`, the **Kummer class** `[a]` is the
class in `H¹(G_k, 𝔽₂)` of the explicit continuous 1-cocycle

  `κ_a : G_k → 𝔽₂`,   `κ_a(g) = 0` if `g·√a = √a`,  `κ_a(g) = 1` if `g·√a = −√a`,

where `√a` is any square root of `a` in a fixed algebraic closure `k̄`.  This is the connecting
homomorphism of the Kummer short exact sequence `1 → μ₂ → k̄ˣ →^{(·)²} k̄ˣ → 1`, specialized to
`n = 2`, under the identification `μ₂ = {±1} ⊆ k` with `𝔽₂ = ZMod 2` (additive, with the **trivial**
`G_k`-action, since `±1 ∈ k`).  See Serre, *Galois Cohomology* I §2 and *Local Fields* X, or
Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields* (Kummer theory `H¹(k, μ_n) ≅ kˣ/(kˣ)ⁿ`).

The Galois group is Mathlib's `Field.absoluteGaloisGroup k = k̄ ≃ₐ[k] k̄` (the genuine `Gal(k̄/k)`,
`k̄ = AlgebraicClosure k`); we spell it out as `GaloisGroup k` (a reducible abbreviation, so that
the `MulAction` on `k̄` and the Krull topology are found by instance search).  For `k = ℚ₂` this is
the
project's `AbsGalQ2` **by definition** (`example`s at the end certify this).

## Conventions (review targets)
* **Coefficients.** `𝔽₂ := ZMod 2` with the **trivial** `G_k`-action (`kummerTriv`); the cocycle
  encodes the sign `g·√a / √a ∈ {±1}` as `0 / 1 ∈ ZMod 2`.  So `H¹(G_k, 𝔽₂) = ` continuous
  homomorphisms `G_k → 𝔽₂` (`ContCoh.mem_Z1_iff_of_trivial`).
* **Cocycle sign.** `κ_a(g) = 0 ⟺ g` fixes `√a`; `κ_a(g) = 1 ⟺ g` negates it.  Root choice is
  irrelevant: `κ` for `√a` and for `−√a` is the *same function* (`kummerCocycleFun_neg`).

## Deliverables (this file, all proved at the standard three axioms)
* `kummerCocycleFun`, `kummerCocycle : ContCoh.Z1 (GaloisGroup k) (ZMod 2)` — the explicit
  continuous 1-cocycle (continuity from openness of the stabilizer of `√a` in the Krull topology).
* `kummerClass : kˣ → ContCoh.H1 (GaloisGroup k) (ZMod 2)` — the Kummer class map.
* Stress tests: `kummerCocycle_isHom` (it is a continuous homomorphism), `kummerClass_one`
  (`[1] = 0`), `kummerClass_mul` (`[ab] = [a] + [b]`, multiplicativity of the Kummer map), and
  `kummerClass_eq_zero_iff` (`[a] = 0 ⟺ a` is a square — injectivity of `kˣ/(kˣ)² ↪ H¹`, which
  uses the fixed-field theorem `InfiniteGalois.mem_range_algebraMap_iff_fixed`).
-/

namespace GQ2.Kummer

open scoped Classical
open GQ2

variable {K : Type*} [Field K] [CharZero K]

/-- The absolute Galois group `Gal(k̄/k)` as `k̄ ≃ₐ[k] k̄`.  A reducible abbreviation (so instance
search sees the `AlgEquiv` action on `k̄`); definitionally `Field.absoluteGaloisGroup K`. -/
abbrev GaloisGroup (K : Type*) [Field K] : Type _ := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K

/-! ## Coefficients: `𝔽₂ = ZMod 2` with the trivial action -/

/-- The **trivial** action of `Gal(k̄/k)` on `𝔽₂ = ZMod 2` (`±1 ∈ k` is fixed).  This is the
coefficient action for the Kummer class; no other action of an absolute Galois group on `ZMod 2`
exists, so registering it globally is safe. -/
instance : DistribMulAction (GaloisGroup K) (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl


omit [CharZero K] in
/-- The action on `𝔽₂` is trivial. -/
lemma kummerTriv : ∀ (g : GaloisGroup K) (m : ZMod 2), g • m = m := fun _ _ => rfl

instance : ContinuousSMul (GaloisGroup K) (ZMod 2) := ⟨continuous_snd⟩

/-! ## The Kummer cocycle function and its pointwise algebra -/

/-- The Kummer cocycle function `κ : G_k → 𝔽₂` attached to a square root `α = √a ∈ k̄`:
`κ(g) = 0` if `g` fixes `α`, else `1`. -/
noncomputable def kummerCocycleFun (α : AlgebraicClosure K) : GaloisGroup K → ZMod 2 :=
  fun g => if g • α = α then 0 else 1

variable {α β : AlgebraicClosure K}

omit [CharZero K] in
@[simp] lemma kummerCocycleFun_eq0 {g : GaloisGroup K} (h : g • α = α) :
    kummerCocycleFun α g = 0 := if_pos h

/-- A square root of a **unit** is not its own negative (characteristic `≠ 2`). -/
lemma alpha_ne_neg {a : Kˣ} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) (a : K)) : α ≠ -α := by
  have hα0 : α ≠ 0 := fun h0 =>
    a.ne_zero <| (FaithfulSMul.algebraMap_eq_zero_iff K (AlgebraicClosure K)).1
      (by rw [← hα, h0]; ring)
  intro h
  have h2 : (2 : AlgebraicClosure K) * α = 0 := by linear_combination h
  rcases mul_eq_zero.1 h2 with h' | h'
  · exact two_ne_zero h'
  · exact hα0 h'

/-- If `α` is a genuine square root of a **unit** `a` and `g` negates it, the cocycle reads `1`
(here `α ≠ -α`, so `g • α = -α` really is `≠ α`). -/
lemma kummerCocycleFun_eq1 {a : Kˣ} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) (a : K))
    {g : GaloisGroup K} (h : g • α = -α) : kummerCocycleFun α g = 1 :=
  if_neg (fun e => alpha_ne_neg hα (e.symm.trans h))

omit [CharZero K] in
/-- The Galois image of a square root of `a ∈ kˣ` is `±√a`. -/
lemma two_values {a : Kˣ} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) (a : K))
    (g : GaloisGroup K) : g • α = α ∨ g • α = -α := by
  have key : (g • α) ^ 2 = α ^ 2 := by
    rw [AlgEquiv.smul_def, ← map_pow, hα, AlgEquiv.commutes]
  have hfac : (g • α - α) * (g • α + α) = 0 := by linear_combination key
  exact (mul_eq_zero.1 hfac).imp sub_eq_zero.1 add_eq_zero_iff_eq_neg.1

omit [CharZero K] in
/-- Changing the square root by a sign leaves the cocycle unchanged. -/
lemma kummerCocycleFun_neg (α : AlgebraicClosure K) :
    kummerCocycleFun (-α) = kummerCocycleFun α := by
  funext g
  simp only [kummerCocycleFun, smul_neg, neg_inj]


/-! ## Continuity via the Krull topology -/
omit [CharZero K] in
/-- `{g | g • α = α}` is (cl)open: it is the stabilizer of `α`, open in the Krull topology because
`k̄/k` is algebraic (`stabilizer_isOpen_of_isIntegral`). -/
lemma stab_isClopen (α : AlgebraicClosure K) : IsClopen {g : GaloisGroup K | g • α = α} := by
  have heq : {g : GaloisGroup K | g • α = α}
      = (MulAction.stabilizer (GaloisGroup K) α : Set _) := by
    ext g; exact (MulAction.mem_stabilizer_iff).symm
  rw [heq]
  refine ⟨?_, stabilizer_isOpen_of_isIntegral (K := K) α⟩
  exact (OpenSubgroup.mk _ (stabilizer_isOpen_of_isIntegral (K := K) α)).isClosed

omit [CharZero K] in
lemma kummerCocycleFun_continuous (α : AlgebraicClosure K) :
    Continuous (kummerCocycleFun α) := by
  refine IsLocallyConstant.continuous ?_
  rw [IsLocallyConstant.iff_exists_open]
  intro g
  by_cases hg : g • α = α
  · refine ⟨{g : GaloisGroup K | g • α = α}, (stab_isClopen α).2, hg, fun x hx => ?_⟩
    have hx' : x • α = α := hx
    simp only [kummerCocycleFun, if_pos hx', if_pos hg]
  · refine ⟨{g : GaloisGroup K | g • α = α}ᶜ, (stab_isClopen α).1.isOpen_compl, hg, fun x hx => ?_⟩
    have hx' : ¬ (x • α = α) := hx
    simp only [kummerCocycleFun, if_neg hx', if_neg hg]

/-! ## The cocycle is a continuous homomorphism -/

/-- `κ_a` is a homomorphism: `κ_a(gh) = κ_a(g) + κ_a(h)`.  With the trivial action this is the
1-cocycle identity. -/
lemma kummerCocycleFun_hom {a : Kˣ} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) (a : K))
    (g h : GaloisGroup K) :
    kummerCocycleFun α (g * h) = kummerCocycleFun α g + kummerCocycleFun α h := by
  rcases two_values hα g with hg | hg <;> rcases two_values hα h with hh | hh
  · rw [kummerCocycleFun_eq0 hg, kummerCocycleFun_eq0 hh,
        kummerCocycleFun_eq0 (by rw [mul_smul, hh, hg])]; decide
  · rw [kummerCocycleFun_eq0 hg, kummerCocycleFun_eq1 hα hh,
        kummerCocycleFun_eq1 hα (by rw [mul_smul, hh, smul_neg, hg])]; decide
  · rw [kummerCocycleFun_eq1 hα hg, kummerCocycleFun_eq0 hh,
        kummerCocycleFun_eq1 hα (by rw [mul_smul, hh, hg])]; decide
  · rw [kummerCocycleFun_eq1 hα hg, kummerCocycleFun_eq1 hα hh,
        kummerCocycleFun_eq0 (by rw [mul_smul, hh, smul_neg, hg, neg_neg])]; decide


/-! ## Packaging into `Z¹` and `H¹` -/

/-- The Kummer cocycle as an element of `Z¹(G_k, 𝔽₂)` (continuous 1-cocycles).  Depends on a chosen
square root `α` of the unit `a`. -/
noncomputable def kummerCocycle {a : Kˣ} (hα : α ^ 2 = algebraMap K (AlgebraicClosure K) (a : K)) :
    ContCoh.Z1 (GaloisGroup K) (ZMod 2) :=
  ⟨kummerCocycleFun α,
    (ContCoh.mem_Z1_iff_of_trivial kummerTriv).2
      ⟨kummerCocycleFun_continuous α, kummerCocycleFun_hom hα⟩⟩

/-- A fixed square root `√a ∈ k̄` of `a ∈ kˣ` (exists as `k̄` is algebraically closed). -/
noncomputable def sqrtOf (a : Kˣ) : AlgebraicClosure K :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (a : K)) (n := 2)
    (by norm_num)).choose

omit [CharZero K] in
lemma sqrtOf_sq (a : Kˣ) : (sqrtOf a) ^ 2 = algebraMap K (AlgebraicClosure K) (a : K) :=
  (IsAlgClosed.exists_pow_nat_eq (algebraMap K (AlgebraicClosure K) (a : K)) (n := 2)
    (by norm_num)).choose_spec

/-- The **Kummer class** `[a] ∈ H¹(G_k, 𝔽₂)` of a unit `a ∈ kˣ`. -/
noncomputable def kummerClass (a : Kˣ) : ContCoh.H1 (GaloisGroup K) (ZMod 2) :=
  ContCoh.H1mk _ _ (kummerCocycle (sqrtOf_sq a))


/-! ## Stress tests -/
omit [CharZero K] in
/-- Auxiliary: under the trivial action, `[z] = 0` in `H¹` iff the cocycle `z` is the zero
function (`B¹ = ⊥`). -/
lemma H1mk_eq_zero_iff {z : ContCoh.Z1 (GaloisGroup K) (ZMod 2)} :
    ContCoh.H1mk _ _ z = 0 ↔ (z : GaloisGroup K → ZMod 2) = 0 := by
  rw [← AddMonoidHom.mem_ker]
  change (z : ↥(ContCoh.Z1 (GaloisGroup K) (ZMod 2))) ∈ (QuotientAddGroup.mk' _).ker ↔ _
  rw [QuotientAddGroup.ker_mk', AddSubgroup.mem_addSubgroupOf,
      ContCoh.B1_eq_bot_of_trivial kummerTriv, AddSubgroup.mem_bot]


/-- **Stress test (injectivity of `kˣ/(kˣ)² ↪ H¹`).** `[a] = 0` iff `a` is a square in `kˣ`.
The nontrivial direction uses that the fixed field of `G_k` is `k`
(`InfiniteGalois.mem_range_algebraMap_iff_fixed`, valid since `k̄/k` is Galois for perfect `k`). -/
theorem kummerClass_eq_zero_iff (a : Kˣ) : kummerClass a = 0 ↔ IsSquare a := by
  rw [kummerClass, H1mk_eq_zero_iff]
  -- underlying function is `kummerCocycleFun (sqrtOf a)`; it is `0` iff every `g` fixes `√a`.
  have hfix : (kummerCocycle (sqrtOf_sq a) : GaloisGroup K → ZMod 2) = 0
      ↔ ∀ g : GaloisGroup K, g • sqrtOf a = sqrtOf a := by
    rw [funext_iff]
    refine forall_congr' (fun g => ?_)
    show kummerCocycleFun (sqrtOf a) g = 0 ↔ _
    simp [kummerCocycleFun, ite_eq_left_iff]
  rw [hfix]
  -- `∀ g, g • √a = √a` ↔ `√a ∈ range (algebraMap k k̄)` ↔ `IsSquare a`.
  have hrange : (∀ g : GaloisGroup K, g • sqrtOf a = sqrtOf a)
      ↔ sqrtOf a ∈ Set.range (algebraMap K (AlgebraicClosure K)) := by
    rw [InfiniteGalois.mem_range_algebraMap_iff_fixed]
    refine forall_congr' (fun g => ?_)
    rw [AlgEquiv.smul_def]
  rw [hrange]
  constructor
  · rintro ⟨b, hb⟩
    -- `b : k`, `algebraMap b = √a`; then `b² = a`.
    have hb2 : (b : K) ^ 2 = (a : K) := by
      apply FaithfulSMul.algebraMap_injective K (AlgebraicClosure K)
      rw [map_pow, hb, sqrtOf_sq]
    have hb0 : b ≠ 0 := by
      rintro rfl
      rw [zero_pow (by norm_num)] at hb2
      exact a.ne_zero hb2.symm
    refine ⟨Units.mk0 b hb0, ?_⟩
    apply Units.ext
    show (a : K) = b * b
    rw [← hb2]; ring
  · rintro ⟨r, hr⟩
    -- `a = r * r`; then `algebraMap r` is a square root, so `√a = ± algebraMap r ∈ range`.
    have hr2 : (algebraMap K (AlgebraicClosure K) (r : K)) ^ 2 = (sqrtOf a) ^ 2 := by
      rw [sqrtOf_sq, ← map_pow, sq, ← Units.val_mul, ← hr]
    have h2 : (algebraMap K (AlgebraicClosure K) (r : K) - sqrtOf a)
        * (algebraMap K (AlgebraicClosure K) (r : K) + sqrtOf a) = 0 := by linear_combination hr2
    rcases mul_eq_zero.1 h2 with h | h
    · exact ⟨(r : K), (sub_eq_zero.1 h)⟩
    · exact ⟨-(r : K), by rw [map_neg, add_eq_zero_iff_eq_neg.1 h, neg_neg]⟩

/-! ## `AbsGalQ2` sanity checks (faithfulness anchor)

For `k = ℚ₂`, `GaloisGroup ℚ₂` is definitionally `Field.absoluteGaloisGroup ℚ₂`, i.e. the project's
`AbsGalQ2`; so `kummerClass (K := ℚ_[2])` is literally the Kummer map into `H¹(G_ℚ₂, 𝔽₂)`. -/

example : GaloisGroup ℚ_[2] = Field.absoluteGaloisGroup ℚ_[2] := rfl

/-- The `ℚ₂` Kummer map, `(ℚ₂)ˣ → H¹(G_ℚ₂, 𝔽₂)`. -/
noncomputable example : (ℚ_[2])ˣ → ContCoh.H1 (GaloisGroup ℚ_[2]) (ZMod 2) := kummerClass

end GQ2.Kummer
