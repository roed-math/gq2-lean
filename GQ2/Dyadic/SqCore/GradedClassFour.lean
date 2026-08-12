/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.SqCore.GradedBridge

/-!
# W69-CLASS4: the class-four calculus, and the class-four relator

Wave 67 reduced the `h ≥ 1` residual to the per-class family `SqClassClearingSupply h k`
(`SqCore/GradedLimit.lean`) and wave 68 discharged `k = 3` on the tower
(`SqCore/GradedBridge.lean`), leaving `BridgeFinalResidual h`: the instances `k ≥ 4`.  This
file attacks `k = 4`.

Wave 68 recorded exactly why its argument does not replay one class up.  It used two facts
about `Q₃ = levelQuot G 3` and both fail at `Q₄`: `commP` is not bimultiplicative there, and
`(q²)² = 1` is *false* there for `D_sq h`.  So class four must carry the `x₀`-slot's fourth
power and a genuine triple bracket.  §1 and §2 below build exactly that.

## §1 The `Q₄` calculus

`Q₄` is not class two; it is class three with an exponent-two top.  Write `Y = λ₂/λ₄` for the
image of `γ₂` (`lambdaImage G 2 4`) and `Z = λ₃/λ₄ = zLayer G 3` for the central involutive
layer.  The calculus is:

* the three free identities with their correction terms, `cfour_commP_mul_left`,
  `cfour_commP_mul_right`, `cfour_sq_mul` (the corrections are the triple brackets that
  `Levelwise`'s `Q₃` statements do not have to carry);
* `commP p q ∈ Y` and `p ^ 2 ∈ Y`; and for `y ∈ Y`, `commP y q ∈ Z` and `y ^ 2 ∈ Z`;
* ⭐ **`cfour_commP_left_hom` / `cfour_commP_right_hom`**: bimultiplicativity is *not* lost
  outright - it survives verbatim **against a `Y`-slot**, because then the correction term is a
  bracket with a central element.  This is the exact sense in which wave 68's calculus
  degrades, and it is enough for everything below;
* ⭐ **`cfour_commP_lambdaTwo`**: `⁅γ₂, γ₂⁆ ≤ γ₄`, so `Y` is abelian in `Q₄`.  The proof is the
  one closed-subgroup argument of the file: `{g | ⁅v, g⁆ ∈ γ₄}` is closed (a preimage of the
  closed `γ₄`), contains every square (the bracket already lies in the exponent-two `Z`) and
  contains `⁅G, G⁆` (the bracket map is a homomorphism into the *abelian* `Z`), hence contains
  `twoCentralSucc ⊤ = γ₂`;
* ⭐ **`cfour_pow_four_mul`**: `(p·q)⁴ = p⁴·q⁴·(commP q p)²`.  The fourth-power map is not a
  homomorphism at class four; its defect is the square of a bracket, and *that* square is what
  makes the two handle letters' fourth powers cancel in §4.

## §2 The relator modulo `γ₄`

⭐⭐ `cfour_sqWord`: in `Q₄`,

```text
  sqWord s x y = commP s x * x ^ 4 * y ^ 2 * commP y (commP y s).
```

Both of wave 68's collapses are visible as the two terms it does not have: the fourth power
`x⁴` survives (it is `(x⁴)⁻¹`, and `x⁴ ∈ Z` has order two, so the inverse may be dropped -
this is the term `bridge_pow_four_iff` isolates, and `dsqSigma_pow_four_not_mem_twoCentralSeries_four`
forbids discarding), and the twisted commutator `commP y (conjP y s)` becomes the genuine
triple bracket `commP y (commP y s)` instead of dying.  Hence ⭐⭐ `cfour_sqRelWord`.

Lane W69-CLASS4.  New file; no edits to existing files.  Prefixes `cfour` / `classFour` /
`sqClassFour`.
-/

open Multiplicative

namespace GQ2

open Roe.Labute

namespace Dyadic

namespace SqCore

open MarkedCore

/-! ## §1 The `Q₄` calculus

Three free identities first: at class two the correction terms are invisible, at class three
they are the triple brackets and they must be carried. -/

section FreeIdentities

variable {Q : Type*} [Group Q]

/-- **The bracket in its left slot**, with the correction term the class-two calculus can
drop: `commP (p·q) r = commP p r · ⁅commP p r, q⁆ · commP q r`. -/
theorem cfour_commP_mul_left (p q r : Q) :
    commP (p * q) r = commP p r * commP (commP p r) q * commP q r := by
  simp only [commP]; group

/-- **The bracket in its right slot**, with its correction term. -/
theorem cfour_commP_mul_right (p q r : Q) :
    commP p (q * r) = commP p r * commP p q * commP (commP p q) r := by
  simp only [commP]; group

/-- **The square of a product**, with its correction term. -/
theorem cfour_sq_mul (p q : Q) :
    (p * q) ^ 2 = p ^ 2 * q ^ 2 * commP q p * commP (commP q p) q := by
  simp only [commP, pow_two]; group

/-- The bracket against `1` is trivial. -/
theorem cfour_comm_one (p : Q) : commP p 1 = 1 := by simp only [commP]; group

/-- The bracket of `1` is trivial. -/
theorem cfour_one_comm (p : Q) : commP 1 p = 1 := by simp only [commP]; group

/-- A trivial bracket means the entries commute (the converse of `bridge_comm_of_commute`). -/
theorem cfour_commute_of_comm {p q : Q} (h : commP p q = 1) : Commute p q := by
  refine (commute_iff_eq p q).mpr ?_
  have h2 : q * p * commP p q = q * p := by rw [h, mul_one]
  simp only [commP] at h2
  calc p * q = q * p * (p⁻¹ * q⁻¹ * p * q) := by group
    _ = q * p := h2

/-- A bracket of an element against itself is trivial (restated for this file's namespace). -/
theorem cfour_comm_self (p : Q) : commP p p = 1 := bridge_comm_self p

end FreeIdentities

section UpstairsSteps

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `γ₂ = twoCentralSucc ⊤`, the recursion at its first genuine step. -/
theorem cfour_lambda_two : twoCentralSeries G 2 = twoCentralSucc (⊤ : Subgroup G) := by
  have h := twoCentralSeries_succ (G := G) (le_refl 1)
  rwa [twoCentralSeries_one] at h

/-- `γ₃ = twoCentralSucc γ₂`. -/
theorem cfour_lambda_three :
    twoCentralSeries G 3 = twoCentralSucc (twoCentralSeries G 2) :=
  twoCentralSeries_succ (G := G) (by norm_num)

/-- `γ₄ = twoCentralSucc γ₃`. -/
theorem cfour_lambda_four :
    twoCentralSeries G 4 = twoCentralSucc (twoCentralSeries G 3) :=
  twoCentralSeries_succ (G := G) (by norm_num)

/-- A bracket against `γ₂` sinks to `γ₃`. -/
theorem cfour_commP_mem_three {v : G} (hv : v ∈ twoCentralSeries G 2) (g : G) :
    commP v g ∈ twoCentralSeries G 3 := by
  rw [cfour_lambda_three]
  exact commP_mem_twoCentralSucc hv g

/-- A bracket against `γ₃` sinks to `γ₄`. -/
theorem cfour_commP_mem_four {v : G} (hv : v ∈ twoCentralSeries G 3) (g : G) :
    commP v g ∈ twoCentralSeries G 4 := by
  rw [cfour_lambda_four]
  exact commP_mem_twoCentralSucc hv g

/-- Every bracket of `G` lies in `γ₂`. -/
theorem cfour_commP_mem_two (a g : G) : commP a g ∈ twoCentralSeries G 2 := by
  rw [cfour_lambda_two]
  exact commP_mem_twoCentralSucc (Subgroup.mem_top a) g

end UpstairsSteps

section LayerFacts

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of `γ₂` in `Q₄`: the layer in which every bracket and every square lives. -/
theorem cfour_commP_mem_lambdaTwo (p q : levelQuot G 4) :
    commP p q ∈ lambdaImage G 2 4 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 4 p
  obtain ⟨b, rfl⟩ := levelMk_surjective G 4 q
  refine ⟨commP a b, cfour_commP_mem_two a b, ?_⟩
  simp only [commP, map_mul, map_inv]

/-- Every square of `Q₄` lies in the image of `γ₂`. -/
theorem cfour_sq_mem_lambdaTwo (p : levelQuot G 4) : p ^ 2 ∈ lambdaImage G 2 4 := by
  obtain ⟨a, rfl⟩ := levelMk_surjective G 4 p
  exact ⟨a ^ 2, sq_mem_twoCentralSeries_succ (G := G) (Subgroup.mem_top a), by rw [map_pow]⟩

/-- A bracket with a `Y`-slot on the left lands in the central layer `Z`. -/
theorem cfour_commP_mem_zLayer_left {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (q : levelQuot G 4) : commP y q ∈ zLayer G 3 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨b, rfl⟩ := levelMk_surjective G 4 q
  refine ⟨commP v b, cfour_commP_mem_three hv b, ?_⟩
  simp only [commP, map_mul, map_inv]

/-- A bracket with a `Y`-slot on the right lands in the central layer `Z`. -/
theorem cfour_commP_mem_zLayer_right (q : levelQuot G 4) {y : levelQuot G 4}
    (hy : y ∈ lambdaImage G 2 4) : commP q y ∈ zLayer G 3 := by
  have h : commP q y = (commP y q)⁻¹ := by simp only [commP]; group
  rw [h]
  exact (zLayer G 3).inv_mem (cfour_commP_mem_zLayer_left hy q)

/-- A square of a `Y`-element lands in the central layer `Z`. -/
theorem cfour_sq_mem_zLayer {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4) :
    y ^ 2 ∈ zLayer G 3 := by
  obtain ⟨v, hv, rfl⟩ := hy
  exact ⟨v ^ 2, sq_mem_twoCentralSeries_succ (G := G) hv, by rw [map_pow]⟩

/-- A `Z`-element kills a bracket from the left. -/
theorem cfour_commP_zLayer_left {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (q : levelQuot G 4) : commP z q = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq

/-- A `Z`-element kills a bracket from the right. -/
theorem cfour_commP_zLayer_right {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (q : levelQuot G 4) : commP q z = 1 :=
  bridge_comm_of_commute (zLayer_commute hz q).eq.symm

/-- ⭐ **Bimultiplicativity survives against a `Y`-slot**: the correction term of
`cfour_commP_mul_left` is a bracket with a central element.  This is the precise sense in which
wave 68's `commP_mul_left_of_three` degrades one class up. -/
theorem cfour_commP_left_hom (p q : levelQuot G 4) {y : levelQuot G 4}
    (hy : y ∈ lambdaImage G 2 4) : commP (p * q) y = commP p y * commP q y := by
  rw [cfour_commP_mul_left,
    cfour_commP_zLayer_left (cfour_commP_mem_zLayer_right p hy) q, mul_one]

/-- ⭐ **Bimultiplicativity survives against a `Y`-slot**, right-hand version. -/
theorem cfour_commP_right_hom {y : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (q r : levelQuot G 4) : commP y (q * r) = commP y r * commP y q := by
  rw [cfour_commP_mul_right,
    cfour_commP_zLayer_left (cfour_commP_mem_zLayer_left hy q) r, mul_one]

/-- A square in the far slot of a bracket against a `Y`-element dies: the bracket is a
homomorphism into the exponent-two layer `Z`. -/
theorem cfour_commP_sq_left (p : levelQuot G 4) {y : levelQuot G 4}
    (hy : y ∈ lambdaImage G 2 4) : commP (p ^ 2) y = 1 := by
  rw [pow_two, cfour_commP_left_hom p p hy, ← pow_two]
  exact zLayer_sq G (cfour_commP_mem_zLayer_right p hy)

end LayerFacts

/-! ### `⁅γ₂, γ₂⁆ ≤ γ₄`

The one place in the file where the topology is used.  Everything else is algebra in `Q₄`. -/

section LambdaTwoAbelian

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The set of `g` whose bracket against a fixed `γ₂`-element `v` has already died to class
four.  It is a subgroup by `cfour_commP_mul_right` (the correction term is a bracket against
`γ₃`, hence already in `γ₄`), and it is closed as a preimage of the closed `γ₄`. -/
def cfourAnnih {v : G} (hv : v ∈ twoCentralSeries G 2) : Subgroup G where
  carrier := {g : G | commP v g ∈ twoCentralSeries G 4}
  one_mem' := by
    simp only [Set.mem_setOf_eq, cfour_comm_one]
    exact Subgroup.one_mem _
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [cfour_commP_mul_right]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hb ha)
      (cfour_commP_mem_four (cfour_commP_mem_three hv a) b)
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have hid := cfour_commP_mul_right v a a⁻¹
    rw [mul_inv_cancel, cfour_comm_one] at hid
    have hsplit : commP v a⁻¹ = (commP v a * commP (commP v a) a⁻¹)⁻¹ :=
      eq_inv_of_mul_eq_one_left (by rw [← mul_assoc, ← hid])
    rw [hsplit]
    exact Subgroup.inv_mem _ (Subgroup.mul_mem _ ha
      (cfour_commP_mem_four (cfour_commP_mem_three hv a) a⁻¹))

theorem cfour_mem_annih {v : G} (hv : v ∈ twoCentralSeries G 2) {g : G} :
    g ∈ cfourAnnih hv ↔ commP v g ∈ twoCentralSeries G 4 := Iff.rfl

/-- The annihilator is closed: it is the preimage of the closed subgroup `γ₄` under the
continuous map `g ↦ commP v g`. -/
theorem cfour_isClosed_annih {v : G} (hv : v ∈ twoCentralSeries G 2) :
    IsClosed ((cfourAnnih hv : Subgroup G) : Set G) := by
  have hset : ((cfourAnnih hv : Subgroup G) : Set G)
      = (fun g : G => commP v g) ⁻¹' ((twoCentralSeries G 4 : Subgroup G) : Set G) := rfl
  rw [hset]
  refine IsClosed.preimage ?_ (isClosed_twoCentralSeries G 4)
  simp only [commP]
  fun_prop

/-- The bracket against a fixed `γ₂`-element, as a homomorphism `G →* Q₄`.  Its values are
central (they lie in `Z`), which is what makes it multiplicative and what makes it kill every
commutator. -/
def cfourCommHom {v : G} (hv : v ∈ twoCentralSeries G 2) : G →* levelQuot G 4 :=
  MonoidHom.mk' (fun g => levelMk G 4 (commP v g)) (by
    intro a b
    have hz : levelMk G 4 (commP v a) ∈ zLayer G 3 :=
      ⟨commP v a, cfour_commP_mem_three hv a, rfl⟩
    have h1 : levelMk G 4 (commP (commP v a) b) = 1 :=
      (lim_mem_twoCentralSeries_iff_levelMk 4 _).mp
        (cfour_commP_mem_four (cfour_commP_mem_three hv a) b)
    rw [cfour_commP_mul_right, map_mul, map_mul, h1, mul_one]
    exact (zLayer_commute hz (levelMk G 4 (commP v b))).symm.eq)

theorem cfour_commHom_apply {v : G} (hv : v ∈ twoCentralSeries G 2) (g : G) :
    cfourCommHom hv g = levelMk G 4 (commP v g) := rfl

theorem cfour_commHom_mem {v : G} (hv : v ∈ twoCentralSeries G 2) (g : G) :
    cfourCommHom hv g ∈ zLayer G 3 :=
  ⟨commP v g, cfour_commP_mem_three hv g, rfl⟩

/-- ⭐ **`⁅γ₂, γ₂⁆ ≤ γ₄`**: the image of `γ₂` is abelian in `Q₄`.  The annihilator of a
`γ₂`-element is a closed subgroup containing every square (the bracket already lies in the
exponent-two layer `Z`) and every commutator (`cfourCommHom` is a homomorphism into the
*abelian* `Z`), hence contains `twoCentralSucc ⊤ = γ₂`. -/
theorem cfour_commutator_lambdaTwo {v w : G} (hv : v ∈ twoCentralSeries G 2)
    (hw : w ∈ twoCentralSeries G 2) : commP v w ∈ twoCentralSeries G 4 := by
  have hsub : twoCentralSeries G 2 ≤ cfourAnnih hv := by
    rw [cfour_lambda_two, twoCentralSucc]
    refine Subgroup.topologicalClosure_minimal _ (sup_le ?_ ?_) (cfour_isClosed_annih hv)
    · refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨g, -, rfl⟩
      show commP v (g ^ 2) ∈ twoCentralSeries G 4
      rw [pow_two, cfour_commP_mul_right]
      have h3 := cfour_commP_mem_three hv g
      have hsq : commP v g * commP v g ∈ twoCentralSeries G 4 := by
        rw [← pow_two]
        exact sq_mem_twoCentralSeries_succ (G := G) h3
      exact Subgroup.mul_mem _ hsq (cfour_commP_mem_four h3 g)
    · refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [commutatorElement_def, cfour_mem_annih,
        lim_mem_twoCentralSeries_iff_levelMk 4 (commP v (a * b * a⁻¹ * b⁻¹))]
      have hval : levelMk G 4 (commP v (a * b * a⁻¹ * b⁻¹))
          = cfourCommHom hv (a * b * a⁻¹ * b⁻¹) := rfl
      rw [hval, map_mul, map_mul, map_mul, map_inv, map_inv,
        (zLayer_commute (cfour_commHom_mem hv a) (cfourCommHom hv b)).eq]
      group
  exact hsub hw

/-- ⭐ **`Y` is abelian in `Q₄`**: two brackets, or two squares, or a bracket and a square,
commute on the nose. -/
theorem cfour_commP_lambdaTwo {y y' : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (hy' : y' ∈ lambdaImage G 2 4) : commP y y' = 1 := by
  obtain ⟨v, hv, rfl⟩ := hy
  obtain ⟨v', hv', rfl⟩ := hy'
  have h : commP (levelMk G 4 v) (levelMk G 4 v') = levelMk G 4 (commP v v') := by
    simp only [commP, map_mul, map_inv]
  rw [h]
  exact (QuotientGroup.eq_one_iff _).mpr (cfour_commutator_lambdaTwo hv hv')

end LambdaTwoAbelian

/-! ### Fourth powers

`p ↦ p⁴` is not a homomorphism at class four.  Its defect is the *square* of a bracket, and
that is exactly the shape that cancels in §4. -/

section FourthPowers

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Every fourth power of `Q₄` lies in the central involutive layer `Z`. -/
theorem cfour_pow_four_mem_zLayer (p : levelQuot G 4) : p ^ 4 ∈ zLayer G 3 := by
  have h : p ^ 4 = (p ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h]
  exact cfour_sq_mem_zLayer (cfour_sq_mem_lambdaTwo p)

/-- A fourth power is its own inverse: this is the term wave 68 could discard and class four
cannot. -/
theorem cfour_pow_four_inv (p : levelQuot G 4) : (p ^ 4)⁻¹ = p ^ 4 :=
  zLayer_inv_self (cfour_pow_four_mem_zLayer p)

/-- The square of a `Y`-element is insensitive to a `Y`-factor: `(y·y')² = y²·y'²`. -/
theorem cfour_sq_mul_lambdaTwo {y y' : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (hy' : y' ∈ lambdaImage G 2 4) : (y * y') ^ 2 = y ^ 2 * y' ^ 2 := by
  rw [cfour_sq_mul, cfour_commP_lambdaTwo hy' hy, cfour_one_comm, mul_one, mul_one]

/-- ⭐ **The fourth power of a product**: `(p·q)⁴ = p⁴·q⁴·(commP q p)²`.  The defect is the
square of the bracket - central, of order two, and a `Y`-square, which is what makes it
cancellable. -/
theorem cfour_pow_four_mul (p q : levelQuot G 4) :
    (p * q) ^ 4 = p ^ 4 * q ^ 4 * (commP q p) ^ 2 := by
  have hc : commP q p ∈ lambdaImage G 2 4 := cfour_commP_mem_lambdaTwo q p
  have hcc : commP (commP q p) q ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hc q
  have h2 : (p * q) ^ 2 = p ^ 2 * q ^ 2 * commP q p * commP (commP q p) q := cfour_sq_mul p q
  have hstep : ((p * q) ^ 2) ^ 2 = (p ^ 2 * q ^ 2 * commP q p) ^ 2 := by
    rw [h2, cfour_sq_mul, cfour_commP_zLayer_right hcc _,
      cfour_commP_zLayer_left hcc _, mul_one, mul_one, zLayer_sq G hcc, mul_one]
  have hsq2 : (p ^ 2 * q ^ 2 * commP q p) ^ 2
      = ((p ^ 2 * q ^ 2) ^ 2) * (commP q p) ^ 2 :=
    cfour_sq_mul_lambdaTwo ((lambdaImage G 2 4).mul_mem (cfour_sq_mem_lambdaTwo p)
      (cfour_sq_mem_lambdaTwo q)) hc
  have hsq3 : (p ^ 2 * q ^ 2) ^ 2 = p ^ 4 * q ^ 4 := by
    rw [cfour_sq_mul_lambdaTwo (cfour_sq_mem_lambdaTwo p) (cfour_sq_mem_lambdaTwo q),
      ← pow_mul, ← pow_mul]
  have h4 : (p * q) ^ 4 = ((p * q) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, hstep, hsq2, hsq3]

end FourthPowers

/-! ## §2 The relator modulo `γ₄`

Wave 68's `bridge_sqWord` reads `sqWord a b c = commP a b * c ^ 2` in `Q₃`: the fourth power
dies because `b²` is already central of order two, and the twisted commutator dies because
`conjP c a` differs from `c` by a central factor.  One class up **both** survive, and they are
exactly the two obstructions wave 68 recorded. -/

section RelatorModFour

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- ⭐⭐ **The core word modulo `γ₄`**: `sqWord a b c = commP a b · b⁴ · c² · ⁅c, ⁅c, a⁆⁆`.

Against wave 68's `bridge_sqWord` two terms are new, and they are precisely the two class-three
collapses that fail one class up.

* The **fourth power** `b⁴` survives.  It appears in the free identity as `((b²)²)⁻¹`; at class
  three `b²` was already central of order two so the factor was `1`, while at class four only
  the *inverse* may be dropped (`cfour_pow_four_inv`, since `b⁴ ∈ Z`).  This is the term
  `bridge_pow_four_iff` isolates, and the tree's
  `dsqSigma_pow_four_not_mem_twoCentralSeries_four` forbids discarding it for `D_sq h`.
* The **triple bracket** `commP c (commP c a)` survives.  At class three `conjP c a = c · commP c a`
  differed from `c` by a central factor, so the whole term collapsed to a self-bracket; at class
  four `commP c a` is only a `Y`-element, and what is left is a genuine triple bracket in `Z`. -/
theorem cfour_sqWord (a b c : levelQuot G 4) :
    sqWord a b c = commP a b * b ^ 4 * c ^ 2 * commP c (commP c a) := by
  have hid : sqWord a b c = commP a b * ((b ^ 2) ^ 2)⁻¹ * c ^ 2 * commP c (conjP c a) := by
    simp only [sqWord, conjP, commP]
    group
  have hb2 : ((b ^ 2) ^ 2 : levelQuot G 4) = b ^ 4 := by rw [← pow_mul]
  have hb : (((b ^ 2) ^ 2 : levelQuot G 4))⁻¹ = b ^ 4 := by
    rw [hb2]; exact cfour_pow_four_inv b
  have hconj : conjP c a = c * commP c a := by simp only [conjP, commP]; group
  have hcc : commP c (conjP c a) = commP c (commP c a) := by
    rw [hconj, cfour_commP_mul_right, cfour_comm_self, cfour_one_comm, mul_one, mul_one]
  rw [hid, hb, hcc]

/-- ⭐⭐ **The relator modulo `γ₄`**: the `σ`/`x₀` bracket, the `x₀`-slot's **fourth power**, the
`x₁`-square, the `x₁`/`σ` **triple bracket**, and the handle brackets.  Compare
`bridge_sqRelWord`, which carries only the first, the third and the last: the class-four
obligation is genuinely larger, and the two extra terms are what §3 has to move. -/
theorem cfour_sqRelWord {k : ℕ} (m : Fin (sqRank k) → levelQuot G 4) :
    sqRelWord m = commP (m 0) (m 1) * m 1 ^ 4 * m 2 ^ 2 * commP (m 2) (commP (m 2) (m 0)) *
      handleWord (fun i => m (sqHandleIdxU i)) (fun i => m (sqHandleIdxV i)) := by
  rw [sqRelWord, cfour_sqWord]

end RelatorModFour

/-! ## §3 The relator lives in an abelian group

Every factor of `cfour_sqRelWord` - the two brackets, the fourth power, the square, the triple
bracket, the handle word - lies in `Y`, and `Y` is abelian by `cfour_commP_lambdaTwo`.  So the
class-four obligation, unlike the class-three one, may be **reordered at will**: it is an
equation in an abelian group.  This is what replaces wave 68's "everything in sight is central"
and it is what makes the class-four computation finite rather than a bracket jungle. -/

section AbelianRelator

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The central layer sits inside the `γ₂`-layer. -/
theorem cfour_zLayer_le_lambdaTwo : zLayer G 3 ≤ lambdaImage G 2 4 := by
  rintro _ ⟨v, hv, rfl⟩
  exact ⟨v, twoCentralSeries_antitone (G := G) (by norm_num) hv, rfl⟩

/-- Two `Y`-elements commute. -/
theorem cfour_commute_lambdaTwo {y y' : levelQuot G 4} (hy : y ∈ lambdaImage G 2 4)
    (hy' : y' ∈ lambdaImage G 2 4) : Commute y y' :=
  cfour_commute_of_comm (cfour_commP_lambdaTwo hy hy')

/-- A handle word lies in `Y`: it is a product of brackets. -/
theorem cfour_handleWord_mem_lambdaTwo {k : ℕ} (u v : Fin k → levelQuot G 4) :
    handleWord u v ∈ lambdaImage G 2 4 := by
  refine Subgroup.list_prod_mem _ fun x hx => ?_
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
  exact cfour_commP_mem_lambdaTwo (u i) (v i)

/-- ⭐ **The relator lies in `Y`** at every tuple of `Q₄`.  (Upstairs this is wave 67's
`lim_sqRelWord_mem_twoCentralSeries_two`, read in `Q₄`.) -/
theorem cfour_sqRelWord_mem_lambdaTwo {k : ℕ} (m : Fin (sqRank k) → levelQuot G 4) :
    sqRelWord m ∈ lambdaImage G 2 4 := by
  rw [cfour_sqRelWord]
  refine Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (cfour_commP_mem_lambdaTwo _ _) ?_) (cfour_sq_mem_lambdaTwo _))
    (cfour_zLayer_le_lambdaTwo (cfour_commP_mem_zLayer_right _
      (cfour_commP_mem_lambdaTwo _ _)))) (cfour_handleWord_mem_lambdaTwo _ _)
  exact cfour_zLayer_le_lambdaTwo (cfour_pow_four_mem_zLayer _)

end AbelianRelator

/-! ## §4 The undressed frame: the whole class-four obligation is the Eichler defect

Wave 68's handle surgery needed its inserted factor to be **central**.  At class four the
inserted factor is only a `Y`-element - but `Y` is abelian (§3) and every handle bracket lies
in `Y`, so the same surgery goes through with `Commute` in place of centrality.  The payoff is
`cfour_relator_base`: **with the trivial dressing the class-four relator is exactly the Eichler
defect**, nothing else.  The generator relation `dsq_relation` absorbs every other factor on the
nose, at class four just as at class three, and no commutativity is used for that step. -/

section HandleSurgery

variable {Q : Type*} [Group Q]

/-- One entry of a product over `Fin n` picking up a right factor that **commutes with every
entry** passes it to the whole product.  This is `bridge_prod_map_update_center` with
centrality weakened to `Commute`, which is all §3 supplies at class four. -/
theorem cfour_prod_map_update (n : ℕ) :
    ∀ (F : Fin n → Q) (j : Fin n) (z : Q), (∀ i, Commute (F i) z) →
      ((List.finRange n).map fun k => if k = j then F k * z else F k).prod
        = ((List.finRange n).map F).prod * z := by
  induction n with
  | zero => exact fun F j z _ => j.elim0
  | succ n ih =>
    intro F j z hz
    rw [List.finRange_succ, List.map_cons, List.map_cons, List.prod_cons, List.prod_cons,
      List.map_map, List.map_map]
    cases j using Fin.cases with
    | zero =>
      rw [if_pos rfl]
      have htail : (List.finRange n).map ((fun k => if k = 0 then F k * z else F k)
            ∘ Fin.succ) = (List.finRange n).map (F ∘ Fin.succ) := by
        refine List.map_congr_left fun k _ => ?_
        simp [Fin.succ_ne_zero]
      have hcomm : Commute ((List.finRange n).map (F ∘ Fin.succ)).prod z := by
        refine Commute.list_prod_left _ _ fun x hx => ?_
        obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
        exact hz i.succ
      rw [htail, mul_assoc, ← hcomm.eq, ← mul_assoc]
    | succ j' =>
      rw [if_neg (Fin.succ_ne_zero j').symm]
      have htail : (List.finRange n).map ((fun k => if k = Fin.succ j' then F k * z else F k)
            ∘ Fin.succ)
          = (List.finRange n).map fun k => if k = j' then (F ∘ Fin.succ) k * z
              else (F ∘ Fin.succ) k := by
        refine List.map_congr_left fun k _ => ?_
        simp only [Function.comp_apply, Fin.succ_inj]
      rw [htail, ih (F ∘ Fin.succ) j' z fun i => hz i.succ, ← mul_assoc]

/-- **A handle word with one bracket changed by a commuting factor.** -/
theorem cfour_handleWord_update {n : ℕ} (u v u' v' : Fin n → Q) (j : Fin n) (z : Q)
    (hz : ∀ i, Commute (commP (u' i) (v' i)) z)
    (hne : ∀ i, i ≠ j → commP (u i) (v i) = commP (u' i) (v' i))
    (hj : commP (u j) (v j) = commP (u' j) (v' j) * z) :
    handleWord u v = handleWord u' v' * z := by
  have hmap : ((List.finRange n).map fun i => commP (u i) (v i))
      = ((List.finRange n).map fun i => if i = j then commP (u' i) (v' i) * z
          else commP (u' i) (v' i)) := by
    refine List.map_congr_left fun i _ => ?_
    by_cases hij : i = j
    · rw [if_pos hij]
      subst hij
      exact hj
    · rw [if_neg hij]
      exact hne i hij
  rw [handleWord, hmap, cfour_prod_map_update n _ j z hz, handleWord]

end HandleSurgery

section BaseDefect

variable {h : ℕ} (nu' : ContinuousMonoidHom (DSq h : Type) (Multiplicative ℤ_[2])) (j : Fin h)

/-- **The class-four Eichler defect**: the amount by which the two cleared handle letters miss
the plain handle bracket in `Q₄`.  At class three wave 68 evaluated it
(`bridge_handle_comm`: it is `commP w^{ν'(u)} v · commP u w^{ν'(v)}`, an element of the central
layer of `Q₃`); at class four it is a `Y`-element and is the entire obligation. -/
noncomputable def cfourEichDefect : levelQuot (DSq h : Type) 4 :=
  (commP (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU j)))
      (levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV j))))⁻¹ *
    commP (levelMk (DSq h : Type) 4 (sqEichU h nu' j))
      (levelMk (DSq h : Type) 4 (sqEichV h nu' j))

/-- The defect is a `Y`-element. -/
theorem cfour_eichDefect_mem : cfourEichDefect nu' j ∈ lambdaImage (DSq h : Type) 2 4 :=
  Subgroup.mul_mem _ (Subgroup.inv_mem _ (cfour_commP_mem_lambdaTwo _ _))
    (cfour_commP_mem_lambdaTwo _ _)

/-- Away from the two twisted slots the undressed frame is the generator frame. -/
theorem cfour_base_eq_gen {i : Fin (sqRank h)} (hU : (i : ℕ) ≠ (sqHandleIdxU j : ℕ))
    (hV : (i : ℕ) ≠ (sqHandleIdxV j : ℕ)) : sqArbBase h nu' j i = sqGen h i := by
  simp only [sqArbBase, if_neg hU, if_neg hV]

/-- ⭐⭐ **The undressed frame's class-four relator is exactly the Eichler defect.**  Every
other factor of `cfour_sqRelWord` is absorbed by the generator relation `dsq_relation` - the
fourth power and the triple bracket included, and with no commutativity used. -/
theorem cfour_relator_base :
    sqRelWord (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j i))
      = cfourEichDefect nu' j := by
  have hgen : sqRelWord (fun i => levelMk (DSq h : Type) 4 (sqGen h i)) = 1 := by
    rw [← map_sqRelWord, dsq_relation, map_one]
  have h0 : sqArbBase h nu' j 0 = sqGen h 0 := cfour_base_eq_gen nu' j
    (by rw [sqVal_zero, sqHandleIdxU_val]; omega) (by rw [sqVal_zero, sqHandleIdxV_val]; omega)
  have h1 : sqArbBase h nu' j 1 = sqGen h 1 := cfour_base_eq_gen nu' j
    (by rw [sqVal_one, sqHandleIdxU_val]; omega) (by rw [sqVal_one, sqHandleIdxV_val]; omega)
  have h2 : sqArbBase h nu' j 2 = sqGen h 2 := cfour_base_eq_gen nu' j
    (by rw [sqVal_two, sqHandleIdxU_val]; omega) (by rw [sqVal_two, sqHandleIdxV_val]; omega)
  have hhandle : handleWord
      (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j (sqHandleIdxU i)))
      (fun i => levelMk (DSq h : Type) 4 (sqArbBase h nu' j (sqHandleIdxV i)))
      = handleWord (fun i => levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxU i)))
          (fun i => levelMk (DSq h : Type) 4 (sqGen h (sqHandleIdxV i))) *
        cfourEichDefect nu' j := by
    refine cfour_handleWord_update _ _ _ _ j _ (fun i => cfour_commute_lambdaTwo
      (cfour_commP_mem_lambdaTwo _ _) (cfour_eichDefect_mem nu' j)) ?_ ?_
    · intro i hi
      simp only [sqArbBase_handleU_ne hi, sqArbBase_handleV_ne hi]
    · simp only [sqArbBase_handleU, sqArbBase_handleV, cfourEichDefect]
      rw [mul_inv_cancel_left]
  rw [sqRelWord] at hgen
  rw [sqRelWord, h0, h1, h2, hhandle, ← mul_assoc, hgen, one_mul]

end BaseDefect

/-! ## §5 The dressing knobs

A dressing correction taken **inside `γ₂`** leaves the class-three picture alone and moves the
class-four relator by a single central factor, computed here slot by slot.  These are the class-four
analogue of `bridge_row_image`'s consumer: `bridge_row_image` says a `γ₂`-valued correction can
always be arranged to have exactly trivial rows, and these lemmas say what such a correction buys.

The three core slots behave differently, and the difference is the whole story:

* slot `σ` buys the bracket `commP c (m 1)`, slot `x₀` buys `commP (m 0) c` - **pure brackets**;
* slot `x₁` buys `c² · commP c (m 2)` - a **square bundled with a bracket against `m 2`**, and
  it is the only slot of the relator carrying a square, hence the only source of squares.

The `x₀`-slot's fourth power buys **nothing**: `c⁴ = 1` and `(commP c (m 1))² = 1` for `c ∈ Y`,
so `cfour_pow_four_mul`'s defect is invisible to a `γ₂`-valued correction.  The triple bracket
also buys nothing (`cfour_dress_zero`, `cfour_dress_two`, both leave it fixed). -/

section Knobs

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A `Z`-element commutes with everything, in the form the shuffles below consume. -/
theorem cfour_zLayer_comm {z : levelQuot G 4} (hz : z ∈ zLayer G 3) (x : levelQuot G 4) :
    z * x = x * z := (zLayer_commute hz x).eq

/-- Moving a central factor from the first slot of a five-fold product to the end. -/
theorem cfour_shuffle {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (A B C D E : levelQuot G 4) : A * z * B * C * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [cfour_zLayer_comm hz]
  simp only [mul_assoc]

/-- Moving a central factor from the middle of a five-fold product to the end. -/
theorem cfour_shuffle_mid {z : levelQuot G 4} (hz : z ∈ zLayer G 3)
    (A B C D E : levelQuot G 4) : A * B * (C * z) * D * E = A * B * C * D * E * z := by
  simp only [mul_assoc]
  rw [cfour_zLayer_comm hz]
  simp only [mul_assoc]

/-- The `x₀`-slot's fourth power is blind to a `Y`-valued correction: both `c⁴` and the
`cfour_pow_four_mul` defect `(commP c p)²` die. -/
theorem cfour_pow_four_dress (p : levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) : (p * c) ^ 4 = p ^ 4 := by
  have hc4 : c ^ 4 = 1 := by
    have h : c ^ 4 = (c ^ 2) ^ 2 := by rw [← pow_mul]
    rw [h]
    exact zLayer_sq G (cfour_sq_mem_zLayer hc)
  rw [cfour_pow_four_mul, hc4, mul_one,
    zLayer_sq G (cfour_commP_mem_zLayer_left hc p), mul_one]

/-- The triple bracket is blind to a `Y`-valued correction of the `σ`-slot. -/
theorem cfour_triple_dress_zero (p q : levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) :
    commP p (commP p (q * c)) = commP p (commP p q) := by
  rw [cfour_commP_mul_right p q c, cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo p q) hc,
    mul_one, cfour_commP_mul_right p (commP p c) (commP p q),
    cfour_commP_zLayer_right (cfour_commP_mem_zLayer_right p hc) p, cfour_one_comm,
    mul_one, mul_one]

/-- ⭐ **The `σ`-slot knob**: a `γ₂`-valued correction of the `σ`-slot moves the class-four
relator by the single bracket `commP c (m 1)`. -/
theorem cfour_dress_zero {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) (h0 : m' 0 = m 0 * c) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP c (m 1) := by
  have hfac1 : commP (m' 0) (m' 1) = commP (m 0) (m 1) * commP c (m 1) := by
    rw [h0, h1, cfour_commP_mul_left,
      cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one]
  rw [cfour_sqRelWord, cfour_sqRelWord, hfac1, h1, h2, h0,
    cfour_triple_dress_zero (m 2) (m 0) hc]
  simp only [hU, hV]
  exact cfour_shuffle (cfour_commP_mem_zLayer_left hc (m 1)) _ _ _ _ _

/-- ⭐ **The `x₀`-slot knob**: a `γ₂`-valued correction of the `x₀`-slot moves the class-four
relator by `commP (m 0) c`.  The fourth power contributes nothing
(`cfour_pow_four_dress`). -/
theorem cfour_dress_one {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) (h0 : m' 0 = m 0) (h1 : m' 1 = m 1 * c) (h2 : m' 2 = m 2)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * commP (m 0) c := by
  have hfac1 : commP (m' 0) (m' 1) = commP (m 0) c * commP (m 0) (m 1) := by
    rw [h0, h1, cfour_commP_mul_right,
      cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo (m 0) (m 1)) hc, mul_one]
  have hz : commP (m 0) c ∈ zLayer G 3 := cfour_commP_mem_zLayer_right (m 0) hc
  rw [cfour_sqRelWord, cfour_sqRelWord, hfac1, h1, h2, h0, cfour_pow_four_dress (m 1) hc]
  simp only [hU, hV, mul_assoc]
  rw [cfour_zLayer_comm hz]
  simp only [mul_assoc]

/-- ⭐ **The `x₁`-slot knob**: a `γ₂`-valued correction of the `x₁`-slot moves the class-four
relator by `c² · commP c (m 2)`.  This is the **only** knob producing a square, because `m 2 ^ 2`
is the only square in the relator; and the square arrives **bundled** with a bracket against
`m 2` that no other knob can produce, because `m 2` is the one frame slot that never appears as
a bracket partner elsewhere in the relator. -/
theorem cfour_dress_two {n : ℕ} (m m' : Fin (sqRank n) → levelQuot G 4) {c : levelQuot G 4}
    (hc : c ∈ lambdaImage G 2 4) (h0 : m' 0 = m 0) (h1 : m' 1 = m 1) (h2 : m' 2 = m 2 * c)
    (hU : ∀ i, m' (sqHandleIdxU i) = m (sqHandleIdxU i))
    (hV : ∀ i, m' (sqHandleIdxV i) = m (sqHandleIdxV i)) :
    sqRelWord m' = sqRelWord m * (c ^ 2 * commP c (m 2)) := by
  have hzc : commP c (m 2) ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hc (m 2)
  have hfac3 : (m' 2) ^ 2 = m 2 ^ 2 * (c ^ 2 * commP c (m 2)) := by
    rw [h2, cfour_sq_mul, cfour_commP_zLayer_left hzc c, mul_one, mul_assoc]
  have hzc0 : commP c (m 0) ∈ zLayer G 3 := cfour_commP_mem_zLayer_left hc (m 0)
  have hzt : commP (m 2) (commP (m 2) (m 0)) ∈ zLayer G 3 :=
    cfour_commP_mem_zLayer_right (m 2) (cfour_commP_mem_lambdaTwo (m 2) (m 0))
  have hW : commP (m 2) (m 0) * commP c (m 0) ∈ lambdaImage G 2 4 :=
    Subgroup.mul_mem _ (cfour_commP_mem_lambdaTwo (m 2) (m 0)) (cfour_zLayer_le_lambdaTwo hzc0)
  have hinner : commP (m 2 * c) (m 0) = commP (m 2) (m 0) * commP c (m 0) := by
    rw [cfour_commP_mul_left (m 2) c (m 0),
      cfour_commP_lambdaTwo (cfour_commP_mem_lambdaTwo (m 2) (m 0)) hc, mul_one]
  have houter : commP (m 2) (commP (m 2) (m 0) * commP c (m 0))
      = commP (m 2) (commP (m 2) (m 0)) := by
    rw [cfour_commP_mul_right (m 2) (commP (m 2) (m 0)) (commP c (m 0)),
      cfour_commP_zLayer_right hzc0 (m 2), one_mul,
      cfour_commP_zLayer_left hzt (commP c (m 0)), mul_one]
  have hfac4 : commP (m' 2) (commP (m' 2) (m' 0)) = commP (m 2) (commP (m 2) (m 0)) := by
    rw [h0, h2, hinner, cfour_commP_mul_left (m 2) c (commP (m 2) (m 0) * commP c (m 0)),
      cfour_commP_lambdaTwo hc hW, mul_one, houter,
      cfour_commP_zLayer_left hzt c, mul_one]
  rw [cfour_sqRelWord, cfour_sqRelWord, hfac3, hfac4, h0, h1]
  simp only [hU, hV]
  exact cfour_shuffle_mid (Subgroup.mul_mem _ (cfour_sq_mem_zLayer hc) hzc) _ _ _ _ _

end Knobs

/-! ## §6 Axiom pins -/

section AxiomPins

#print axioms cfour_commP_mul_left
#print axioms cfour_commP_mul_right
#print axioms cfour_sq_mul
#print axioms cfour_comm_self
#print axioms cfour_comm_one
#print axioms cfour_one_comm
#print axioms cfour_lambda_two
#print axioms cfour_lambda_three
#print axioms cfour_lambda_four
#print axioms cfour_commP_mem_three
#print axioms cfour_commP_mem_four
#print axioms cfour_commP_mem_two
#print axioms cfour_commP_mem_lambdaTwo
#print axioms cfour_sq_mem_lambdaTwo
#print axioms cfour_commP_mem_zLayer_left
#print axioms cfour_commP_mem_zLayer_right
#print axioms cfour_sq_mem_zLayer
#print axioms cfour_commP_zLayer_left
#print axioms cfour_commP_zLayer_right
#print axioms cfour_commP_left_hom
#print axioms cfour_commP_right_hom
#print axioms cfour_commP_sq_left
#print axioms cfourAnnih
#print axioms cfour_mem_annih
#print axioms cfour_isClosed_annih
#print axioms cfourCommHom
#print axioms cfour_commHom_apply
#print axioms cfour_commHom_mem
#print axioms cfour_commutator_lambdaTwo
#print axioms cfour_commP_lambdaTwo
#print axioms cfour_pow_four_mem_zLayer
#print axioms cfour_pow_four_inv
#print axioms cfour_sq_mul_lambdaTwo
#print axioms cfour_pow_four_mul
#print axioms cfour_sqWord
#print axioms cfour_sqRelWord
#print axioms cfour_commute_of_comm
#print axioms cfour_zLayer_le_lambdaTwo
#print axioms cfour_commute_lambdaTwo
#print axioms cfour_handleWord_mem_lambdaTwo
#print axioms cfour_sqRelWord_mem_lambdaTwo
#print axioms cfour_prod_map_update
#print axioms cfour_handleWord_update
#print axioms cfourEichDefect
#print axioms cfour_eichDefect_mem
#print axioms cfour_base_eq_gen
#print axioms cfour_relator_base
#print axioms cfour_zLayer_comm
#print axioms cfour_shuffle
#print axioms cfour_shuffle_mid
#print axioms cfour_pow_four_dress
#print axioms cfour_triple_dress_zero
#print axioms cfour_dress_zero
#print axioms cfour_dress_one
#print axioms cfour_dress_two

end AxiomPins

end SqCore

end Dyadic

end GQ2
