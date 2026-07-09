import GQ2.EvensKahn

/-!
# B12 discharge — surjectivity of `kummerClassK` (hom/kernel layer, ticket B12-1)

Groundwork for proving `GQ2.kummerClassK_surjective` (`Foundations/Axioms.lean`) in-repo,
retiring axiom **B12** (census 15 → 14).  See `docs/b12-tickets.md` / `docs/b12-proof-plan.md`.

This file is the **hom/kernel layer** (B12-1): it turns a degree-1 class
`c ∈ H¹(G_k, 𝔽₂)` — via `H1mk_surjective`, some cocycle `z ∈ Z¹` — into an open, index-2
subgroup of `G_k = k.fixingSubgroup` (its kernel, when `z ≠ 0`), plus the bookkeeping needed to
reconnect a Kummer cocycle to `z` at the end (`eq_of_zero_set`, `mem_zHom_ker`) and the `z = 0`
base case (`kummerClassK_one`).  It lives strictly upstream of `Foundations/Axioms.lean`
(imports only `GQ2.EvensKahn` + Mathlib) so the eventual flip is the zero-churn B11 pattern.

The Krull bridge that consumes `zHom_ker_isOpen` + `zHom_index_ker` to produce the quadratic
subextension is ticket B12-2; the capstone assembly is B12-3.
-/

namespace GQ2.KummerSurjectivity

open GQ2 ContCoh Kummer

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (k : IntermediateField ℚ_[2] ℚ̄₂)

/-- The `k.fixingSubgroup`-action on `ZMod 2` is trivial (it factors through `Kummer`'s trivial
action on `𝔽₂`).  This is the `htriv` input of `mem_Z1_iff_of_trivial` for `G = G_k`. -/
lemma htriv_fs : ∀ (g : ↥k.fixingSubgroup) (m : ZMod 2), g • m = m := fun _ _ ↦ rfl

/-- A degree-1 cocycle `z ∈ Z¹(G_k, 𝔽₂)` as a genuine group homomorphism
`G_k →* Multiplicative (ZMod 2)` (trivial action ⇒ `z` is additive, `Z1_apply_one` ⇒ `z 1 = 0`).
Its kernel is the index-2 subgroup that the Krull bridge (B12-2) turns into a quadratic
subextension. -/
noncomputable def zHom (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) :
    ↥k.fixingSubgroup →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (z.1 g)
  map_one' := by
    show Multiplicative.ofAdd (z.1 1) = 1
    rw [Z1_apply_one z]; rfl
  map_mul' a b := by
    show Multiplicative.ofAdd (z.1 (a * b))
      = Multiplicative.ofAdd (z.1 a) * Multiplicative.ofAdd (z.1 b)
    rw [((mem_Z1_iff_of_trivial (htriv_fs k)).mp z.2).2 a b, ofAdd_add]

variable {k}

@[simp] lemma zHom_apply (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) (g : ↥k.fixingSubgroup) :
    zHom k z g = Multiplicative.ofAdd (z.1 g) := rfl

/-- The kernel of `zHom` is exactly the zero-set of the cocycle. -/
lemma mem_zHom_ker {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} {g : ↥k.fixingSubgroup} :
    g ∈ (zHom k z).ker ↔ z.1 g = 0 := by
  rw [MonoidHom.mem_ker, zHom_apply, ofAdd_eq_one]

/-- The kernel of `zHom` is open: it is the preimage of the (open, discrete) point `{0}` under
the continuous cocycle `z`. -/
lemma zHom_ker_isOpen (z : Z1 (↥k.fixingSubgroup) (ZMod 2)) :
    IsOpen ((zHom k z).ker : Set ↥k.fixingSubgroup) := by
  have hset : ((zHom k z).ker : Set ↥k.fixingSubgroup) = z.1 ⁻¹' {0} := by
    ext g; rw [SetLike.mem_coe, mem_zHom_ker]; rfl
  rw [hset]
  exact ((mem_Z1_iff.mp z.2).1).isOpen_preimage _ (isOpen_discrete _)

/-- When the cocycle is nonzero, `zHom` is surjective (its 2-element codomain leaves no room
for a proper nontrivial image). -/
lemma zHom_surjective {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} (hz : z.1 ≠ 0) :
    Function.Surjective (zHom k z) := by
  obtain ⟨g₀, hg₀⟩ := Function.ne_iff.mp hz
  have h1 : z.1 g₀ = 1 := (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) _ hg₀
  intro y
  obtain ⟨x, rfl⟩ := Multiplicative.ofAdd.surjective y
  rcases (by decide : ∀ x : ZMod 2, x = 0 ∨ x = 1) x with rfl | rfl
  · exact ⟨1, by rw [zHom_apply, Z1_apply_one z]⟩
  · exact ⟨g₀, by rw [zHom_apply, h1]⟩

/-- When the cocycle is nonzero, the kernel has index 2. -/
lemma zHom_index_ker {z : Z1 (↥k.fixingSubgroup) (ZMod 2)} (hz : z.1 ≠ 0) :
    (zHom k z).ker.index = 2 := by
  rw [Subgroup.index_ker, MonoidHom.range_eq_top_of_surjective _ (zHom_surjective hz),
    Nat.card_congr Subgroup.topEquiv.toEquiv, Nat.card_eq_fintype_card]
  decide

/-- Two `𝔽₂`-valued functions with the same zero-set are equal (the only nonzero value is `1`).
This reconnects a Kummer cocycle to `z` in the capstone (B12-3): equal kernels ⇒ equal cocycles
⇒ equal `H¹`-classes. -/
lemma eq_of_zero_set {f f' : ↥k.fixingSubgroup → ZMod 2}
    (h : ∀ g, f g = 0 ↔ f' g = 0) : f = f' := by
  funext g
  by_cases hf : f g = 0
  · rw [hf, (h g).mp hf]
  · rw [(by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) (f g) hf,
      (by decide : ∀ x : ZMod 2, x ≠ 0 → x = 1) (f' g) (fun c => hf ((h g).mpr c))]

/-- **The `z = 0` base case.**  `[1] = 0`: the Kummer class of the unit `1` vanishes.  Ported
(direct proof) from `HilbertLedger.kummerClassK_one`, which is downstream of the axiom file.
`sqrtCl 1` is a square root of `1` in `ℚ̄₂`, hence `±1 ∈ ℚ₂`, hence Galois-fixed, so the cocycle
is identically `0`. -/
theorem kummerClassK_one : kummerClassK k (1 : (↥k)ˣ) = 0 := by
  have hfix : ∀ g : GaloisGroup ℚ_[2], g • sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂)) = sqrtCl 1 := by
    intro g
    have hsq : sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂)) = sqrtCl (1 : ℚ̄₂) := by norm_num
    rw [hsq]
    have h2 : (sqrtCl (1 : ℚ̄₂) - 1) * (sqrtCl (1 : ℚ̄₂) + 1) = 0 := by
      have := sqrtCl_sq (1 : ℚ̄₂); linear_combination this
    rcases mul_eq_zero.1 h2 with h' | h'
    · have : sqrtCl (1 : ℚ̄₂) = 1 := by linear_combination h'
      rw [this, AlgEquiv.smul_def, map_one]
    · have : sqrtCl (1 : ℚ̄₂) = -1 := by linear_combination h'
      rw [this, AlgEquiv.smul_def, map_neg, map_one]
  have hzero : (kummerClassK k (1 : (↥k)ˣ)) = H1mk _ _ 0 := by
    rw [kummerClassK]
    congr 1
    apply Subtype.ext
    funext g
    show kummerCocycleFun (sqrtCl ((((1 : (↥k)ˣ) : ↥k) : ℚ̄₂))) _ = 0
    exact kummerCocycleFun_eq0 (hfix _)
  rw [hzero, map_zero]

end GQ2.KummerSurjectivity
