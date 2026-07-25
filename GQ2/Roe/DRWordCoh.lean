/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.DRAbelianization
public import GQ2.Cohomology

@[expose] public section

/-!
# The `D_R` degree-2 presentation comparison — single-relator obstruction (ticket R13b)

The `D_R = ⟨s, x, y | r₂⟩_{pro-2}` analogue of the (non-`module`) Γ_A degree-2 bridge
`GQ2/WordCoh2.lean`.  Because `D_R` has a **single** relator, the relator obstruction is a *single*
`𝔽₂` value (not the tame/wild pair of Γ_A), so there is no "balance" (`im d¹`) condition: the
obstruction map lands in `𝔽₂` directly and injectivity is exactly the `#H² ≤ 2` statement.

`GQ2/WordCoh2.lean` is not a `module`, so its generic central-extension algebra cannot be imported
here; the `## Generic central-extension algebra` section below re-derives the pieces we need
(`TwoCocycle`, `CentExt`, `FiberProd`, `zeroCocycle`, `coboundaryCocycle`, `Psi`,
`TwoCocycle.comap`/`projExt`, `exists_openNormalSubgroup_factor_two`) verbatim in the `GQ2.DRCoh`
namespace.  On top of that:

* `drRelZ m c` — the fibre of `drWord` evaluated at the zero-fibre lift of a triple `m : Fin 3 → L`;
  naturality (`drRelZ_comap`), additivity (`drRelZ_add`), coboundary law (`drRelZ_coboundary`);
* the profinite factoring `exists_twoCocycle_factor_DR` (the generic compactness core applied to the
  pro-2 group `D_R` *directly* — the relation is inherited by every finite quotient `D_R ⧸ V`);
* `DRLevelFactor`/`obs`/`obs_congr` — the level-independent single-`𝔽₂` obstruction;
* the injectivity keystone: when `obs = 0` the relator dies exactly, so `drLiftHom` directly builds a
  splitting section `D_R → CentExt c` and the pulled-back cocycle is a continuous coboundary;
* `obsH2_DR : H²(D_R, 𝔽₂) →+ 𝔽₂`, its injectivity, and the bridge `obsFun_DR_eq_of_factor` computing
  the obstruction at *any* finite quotient — consumed by `GQ2/Roe/DRH2.lean` and `DRDemushkin.lean`.
-/

namespace GQ2

/-! ## Generic central-extension algebra (re-derived from `GQ2/WordCoh2.lean`)

Verbatim ports of the generic-in-`L` declarations of the non-`module` `GQ2/WordCoh2.lean`, placed in
the fresh `GQ2.DRCoh` namespace to avoid any clash with `GQ2.WordCoh2.*` (both are visible in the
top-level `GQ2.lean` aggregate). -/

namespace DRCoh

variable {L : Type*} [Group L]

/-- A `ZMod 2`-valued 2-cocycle on `L`, normalized at `(1,1)` (`WordCoh2.TwoCocycle`). -/
structure TwoCocycle (L : Type*) [Group L] where
  /-- The underlying 2-cochain. -/
  κ : L → L → ZMod 2
  /-- Normalization at the identity. -/
  norm : κ 1 1 = 0
  /-- The 2-cocycle identity (trivial coefficients). -/
  cocyc : ∀ a b c : L, κ a b + κ (a * b) c = κ a (b * c) + κ b c

namespace TwoCocycle

variable (c : TwoCocycle L)

theorem κ_one_left (l : L) : c.κ 1 l = 0 := by simpa [c.norm] using c.cocyc 1 1 l

theorem κ_one_right (l : L) : c.κ l 1 = 0 := by simpa [c.norm] using c.cocyc l 1 1

theorem κ_inv (l : L) : c.κ l l⁻¹ = c.κ l⁻¹ l := by
  simpa [c.κ_one_left, c.κ_one_right] using c.cocyc l l⁻¹ l

end TwoCocycle

/-- The central extension `L ×_κ ZMod 2` (`WordCoh2.CentExt`). -/
def CentExt (_c : TwoCocycle L) : Type _ := L × ZMod 2

namespace CentExt

variable {c : TwoCocycle L}

/-- Base coordinate. -/
def base (p : CentExt c) : L := p.1
/-- Fibre coordinate. -/
def fib (p : CentExt c) : ZMod 2 := p.2

@[ext] theorem ext {p q : CentExt c} (h1 : p.base = q.base) (h2 : p.fib = q.fib) : p = q :=
  Prod.ext h1 h2

instance : Group (CentExt c) where
  mul p q := (p.1 * q.1, p.2 + q.2 + c.κ p.1 q.1)
  one := (1, 0)
  inv p := (p.1⁻¹, p.2 + c.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply Prod.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2 + q.2 + c.κ p.1 q.1 + r.2 + c.κ (p.1 * q.1) r.1
        = p.2 + (q.2 + r.2 + c.κ q.1 r.1) + c.κ p.1 (q.1 * r.1)
      linear_combination c.cocyc p.1 q.1 r.1
  one_mul p := by
    apply Prod.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2 + c.κ 1 p.1 = p.2
      rw [c.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply Prod.ext
    · exact mul_one p.1
    · show p.2 + 0 + c.κ p.1 1 = p.2
      rw [c.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply Prod.ext
    · exact inv_mul_cancel p.1
    · show p.2 + c.κ p.1 p.1⁻¹ + p.2 + c.κ p.1⁻¹ p.1 = 0
      rw [c.κ_inv]
      exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] theorem mul_base (p q : CentExt c) : (p * q).base = p.base * q.base := rfl
@[simp] theorem mul_fib (p q : CentExt c) : (p * q).fib = p.fib + q.fib + c.κ p.base q.base := rfl
@[simp] private theorem one_base : (1 : CentExt c).base = 1 := rfl
@[simp] private theorem one_fib : (1 : CentExt c).fib = 0 := rfl

/-- The base projection `CentExt c →* L`. -/
def proj (c : TwoCocycle L) : CentExt c →* L where
  toFun := CentExt.base
  map_one' := rfl
  map_mul' := mul_base

/-- The central inclusion `ZMod 2 → CentExt c`. -/
def incl (c : TwoCocycle L) : ZMod 2 → CentExt c := fun z => (1, z)

@[simp] private theorem incl_base (z : ZMod 2) : (incl c z).base = 1 := rfl
@[simp] private theorem incl_fib (z : ZMod 2) : (incl c z).fib = z := rfl

theorem base_eq_one_iff (p : CentExt c) : p.base = 1 ↔ p = incl c p.fib :=
  ⟨fun h => CentExt.ext h rfl, fun h => by rw [h]; rfl⟩

@[simp] theorem incl_zero : incl c (0 : ZMod 2) = 1 := rfl

@[simp] theorem incl_mul_fib (z : ZMod 2) (p : CentExt c) : (incl c z * p).fib = z + p.fib := by
  show z + p.fib + c.κ 1 p.base = z + p.fib
  rw [c.κ_one_left, add_zero]

instance : TopologicalSpace (CentExt c) := ⊥
instance : DiscreteTopology (CentExt c) := ⟨rfl⟩
instance [Finite L] : Finite (CentExt c) := inferInstanceAs (Finite (L × ZMod 2))

end CentExt

/-! ### Level change: pulling a cocycle back along a group hom -/

section LevelChange

variable {L L' : Type*} [Group L] [Group L']

/-- Pull back a 2-cocycle along `φ : L' →* L`. -/
def TwoCocycle.comap (c : TwoCocycle L) (φ : L' →* L) : TwoCocycle L' where
  κ a b := c.κ (φ a) (φ b)
  norm := by simp only [map_one]; exact c.norm
  cocyc a b d := by simp only [map_mul]; exact c.cocyc (φ a) (φ b) (φ d)

@[simp] theorem TwoCocycle.comap_κ (c : TwoCocycle L) (φ : L' →* L) (a b : L') :
    (c.comap φ).κ a b = c.κ (φ a) (φ b) := rfl

/-- The base hom `φ` lifts to `CentExt (c.comap φ) →* CentExt c`. -/
def projExt (c : TwoCocycle L) (φ : L' →* L) : CentExt (c.comap φ) →* CentExt c where
  toFun p := ((φ p.base, p.fib) : CentExt c)
  map_one' := CentExt.ext (map_one φ) rfl
  map_mul' p q := CentExt.ext (map_mul φ p.base q.base) rfl

@[simp] theorem projExt_fib (c : TwoCocycle L) (φ : L' →* L) (p : CentExt (c.comap φ)) :
    (projExt c φ p).fib = p.fib := rfl

end LevelChange

/-! ### Additivity infrastructure: sum cocycle and fiber product -/

section Additivity

variable {L : Type*} [Group L]

/-- Pointwise sum of 2-cocycles. -/
instance : Add (TwoCocycle L) where
  add c₁ c₂ :=
    { κ := fun a b => c₁.κ a b + c₂.κ a b
      norm := by rw [c₁.norm, c₂.norm, add_zero]
      cocyc := fun a b d => by
        have h1 := c₁.cocyc a b d; have h2 := c₂.cocyc a b d; linear_combination h1 + h2 }

@[simp] theorem TwoCocycle.add_κ (c₁ c₂ : TwoCocycle L) (a b : L) :
    (c₁ + c₂).κ a b = c₁.κ a b + c₂.κ a b := rfl

/-- The fiber product `CentExt c₁ ×_L CentExt c₂`. -/
def FiberProd (_c₁ _c₂ : TwoCocycle L) : Type _ := L × ZMod 2 × ZMod 2

namespace FiberProd

variable {c₁ c₂ : TwoCocycle L}

/-- Base coordinate. -/
def base (p : FiberProd c₁ c₂) : L := p.1
/-- First fibre coordinate. -/
def fibA (p : FiberProd c₁ c₂) : ZMod 2 := p.2.1
/-- Second fibre coordinate. -/
def fibB (p : FiberProd c₁ c₂) : ZMod 2 := p.2.2

@[ext] private theorem ext {p q : FiberProd c₁ c₂} (h1 : p.base = q.base) (h2 : p.fibA = q.fibA)
    (h3 : p.fibB = q.fibB) : p = q :=
  Prod.ext h1 (Prod.ext h2 h3)

instance : Group (FiberProd c₁ c₂) where
  mul p q := (p.1 * q.1, p.2.1 + q.2.1 + c₁.κ p.1 q.1, p.2.2 + q.2.2 + c₂.κ p.1 q.1)
  one := (1, 0, 0)
  inv p := (p.1⁻¹, p.2.1 + c₁.κ p.1 p.1⁻¹, p.2.2 + c₂.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply FiberProd.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2.1 + q.2.1 + c₁.κ p.1 q.1 + r.2.1 + c₁.κ (p.1 * q.1) r.1
        = p.2.1 + (q.2.1 + r.2.1 + c₁.κ q.1 r.1) + c₁.κ p.1 (q.1 * r.1)
      linear_combination c₁.cocyc p.1 q.1 r.1
    · show p.2.2 + q.2.2 + c₂.κ p.1 q.1 + r.2.2 + c₂.κ (p.1 * q.1) r.1
        = p.2.2 + (q.2.2 + r.2.2 + c₂.κ q.1 r.1) + c₂.κ p.1 (q.1 * r.1)
      linear_combination c₂.cocyc p.1 q.1 r.1
  one_mul p := by
    apply FiberProd.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2.1 + c₁.κ 1 p.1 = p.2.1; rw [c₁.κ_one_left, add_zero, zero_add]
    · show (0 : ZMod 2) + p.2.2 + c₂.κ 1 p.1 = p.2.2; rw [c₂.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply FiberProd.ext
    · exact mul_one p.1
    · show p.2.1 + 0 + c₁.κ p.1 1 = p.2.1; rw [c₁.κ_one_right, add_zero, add_zero]
    · show p.2.2 + 0 + c₂.κ p.1 1 = p.2.2; rw [c₂.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply FiberProd.ext
    · exact inv_mul_cancel p.1
    · show p.2.1 + c₁.κ p.1 p.1⁻¹ + p.2.1 + c₁.κ p.1⁻¹ p.1 = 0
      rw [c₁.κ_inv]; exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _
    · show p.2.2 + c₂.κ p.1 p.1⁻¹ + p.2.2 + c₂.κ p.1⁻¹ p.1 = 0
      rw [c₂.κ_inv]; exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] private theorem mul_base (p q : FiberProd c₁ c₂) : (p * q).base = p.base * q.base := rfl

/-- Projection to the first central extension. -/
def pr1 : FiberProd c₁ c₂ →* CentExt c₁ where
  toFun p := ((p.base, p.fibA) : CentExt c₁)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the second central extension. -/
def pr2 : FiberProd c₁ c₂ →* CentExt c₂ where
  toFun p := ((p.base, p.fibB) : CentExt c₂)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The fibre-sum hom to the sum extension. -/
def prSum : FiberProd c₁ c₂ →* CentExt (c₁ + c₂) where
  toFun p := ((p.base, p.fibA + p.fibB) : CentExt (c₁ + c₂))
  map_one' := CentExt.ext rfl (add_zero (0 : ZMod 2))
  map_mul' p q := CentExt.ext rfl <| by
    show (p.fibA + q.fibA + c₁.κ p.base q.base) + (p.fibB + q.fibB + c₂.κ p.base q.base)
        = (p.fibA + p.fibB) + (q.fibA + q.fibB) + (c₁.κ p.base q.base + c₂.κ p.base q.base)
    ring

@[simp] theorem pr1_fib (p : FiberProd c₁ c₂) : (pr1 p).fib = p.fibA := rfl
@[simp] theorem pr2_fib (p : FiberProd c₁ c₂) : (pr2 p).fib = p.fibB := rfl
@[simp] theorem prSum_fib (p : FiberProd c₁ c₂) : (prSum p).fib = p.fibA + p.fibB := rfl

instance [Finite L] : Finite (FiberProd c₁ c₂) := inferInstanceAs (Finite (L × ZMod 2 × ZMod 2))

end FiberProd

end Additivity

/-! ### The split and coboundary cocycles -/

section SplitCoboundary

variable {L : Type*} [Group L]

/-- The trivial (split) 2-cocycle `κ ≡ 0`. -/
def zeroCocycle : TwoCocycle L where
  κ _ _ := 0
  norm := rfl
  cocyc _ _ _ := rfl

/-- The fibre projection `CentExt zeroCocycle →* Multiplicative 𝔽₂`. -/
def fibHom0 : CentExt (zeroCocycle : TwoCocycle L) →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd p.fib
  map_one' := rfl
  map_mul' p q := by
    show Multiplicative.ofAdd (p * q).fib = Multiplicative.ofAdd p.fib * Multiplicative.ofAdd q.fib
    rw [CentExt.mul_fib, show (zeroCocycle : TwoCocycle L).κ p.base q.base = (0 : ZMod 2) from rfl,
      add_zero, ofAdd_add]

/-- The coboundary 2-cocycle `δ¹λ`. -/
def coboundaryCocycle (lam : L → ZMod 2) (hlam1 : lam 1 = 0) : TwoCocycle L where
  κ a b := lam a + lam b + lam (a * b)
  norm := by simp [hlam1]
  cocyc a b c := by
    show lam a + lam b + lam (a * b) + (lam (a * b) + lam c + lam (a * b * c))
      = lam a + lam (b * c) + lam (a * (b * c)) + (lam b + lam c + lam (b * c))
    rw [mul_assoc a b c]
    abel_nf
    simp [CharTwo.two_eq_zero]

/-- The trivialization hom `Ψ_λ : (l, z) ↦ (l, z + λ l)`. -/
def Psi (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    CentExt (coboundaryCocycle lam hlam1) →* CentExt (zeroCocycle : TwoCocycle L) where
  toFun p := ((p.base, p.fib + lam p.base) : CentExt (zeroCocycle : TwoCocycle L))
  map_one' := CentExt.ext rfl (by show (0 : ZMod 2) + lam 1 = 0; simp [hlam1])
  map_mul' p q := by
    refine CentExt.ext rfl ?_
    · show (p * q).fib + lam (p * q).base
          = (p.fib + lam p.base) + (q.fib + lam q.base)
            + (zeroCocycle : TwoCocycle L).κ p.base q.base
      rw [CentExt.mul_fib, CentExt.mul_base,
        show (zeroCocycle : TwoCocycle L).κ p.base q.base = (0 : ZMod 2) from rfl,
        show (coboundaryCocycle lam hlam1).κ p.base q.base
          = lam p.base + lam q.base + lam (p.base * q.base) from rfl]
      abel_nf
      simp [CharTwo.two_eq_zero]

@[simp] theorem Psi_fib (lam : L → ZMod 2) (hlam1 : lam 1 = 0)
    (p : CentExt (coboundaryCocycle lam hlam1)) : (Psi lam hlam1 p).fib = p.fib + lam p.base := rfl

end SplitCoboundary

/-- Two `TwoCocycle`s with equal cochain are equal. -/
theorem TwoCocycle.ext {L : Type*} [Group L] {c d : TwoCocycle L} (h : c.κ = d.κ) : c = d := by
  cases c; cases d; subst h; rfl

/-! ### Factoring a continuous 2-variable map through a finite quotient -/

/-- **Uniform local constancy** (2-variable form) — `WordCoh2.exists_openNormalSubgroup_factor_two`,
generic in the profinite group `G`. -/
theorem exists_openNormalSubgroup_factor_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : G × G → M) (hf : Continuous f) :
    ∃ V : OpenNormalSubgroup G, ∀ x y : G, ∀ u ∈ V, ∀ v ∈ V, f (x * u, y * v) = f (x, y) := by
  have hbox : ∀ p : G × G, ∃ W : OpenNormalSubgroup G,
      ∀ u ∈ W, ∀ v ∈ W, f (p.1 * u, p.2 * v) = f p := by
    intro p
    have hop : IsOpen (f ⁻¹' {f p}) := (isOpen_discrete _).preimage hf
    obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ := isOpen_prod_iff.mp hop p.1 p.2 rfl
    have hOA : IsOpen ((fun w => p.1 * w) ⁻¹' A) := hA.preimage (continuous_const.mul continuous_id)
    have hOB : IsOpen ((fun w => p.2 * w) ⁻¹' B) := hB.preimage (continuous_const.mul continuous_id)
    have h1A : (1 : G) ∈ (fun w => p.1 * w) ⁻¹' A := by simpa using hpA
    have h1B : (1 : G) ∈ (fun w => p.2 * w) ⁻¹' B := by simpa using hpB
    obtain ⟨WA, hWA⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOA h1A
    obtain ⟨WB, hWB⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOB h1B
    refine ⟨WA ⊓ WB, fun u hu v hv => ?_⟩
    have huA : p.1 * u ∈ A := hWA (SetLike.le_def.mp inf_le_left hu)
    have hvB : p.2 * v ∈ B := hWB (SetLike.le_def.mp inf_le_right hv)
    have hmem : (p.1 * u, p.2 * v) ∈ f ⁻¹' {f p} := hAB (Set.mk_mem_prod huA hvB)
    simpa using hmem
  choose W hW using hbox
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : G × G => (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)))
    (fun p => (((W p).toOpenSubgroup.isOpen.prod (W p).toOpenSubgroup.isOpen)).preimage
      (by fun_prop))
    (fun q _ => Set.mem_iUnion.mpr ⟨q, by
      rw [Set.mem_preimage, Set.mem_prod, inv_mul_cancel, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩⟩)
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ((1, 1) : G × G)))
    exact ⟨i, hi⟩
  refine ⟨t.inf' hne W, fun x y u hu v hv => ?_⟩
  have hxy : (x, y) ∈ ⋃ p ∈ t,
      (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)) := ht (Set.mem_univ _)
  rw [Set.mem_iUnion₂] at hxy
  obtain ⟨p, hpt, hp⟩ := hxy
  rw [Set.mem_preimage, Set.mem_prod] at hp
  obtain ⟨hx, hy⟩ := hp
  have hVle : t.inf' hne W ≤ W p := Finset.inf'_le _ hpt
  have huWp : u ∈ W p := SetLike.le_def.mp hVle hu
  have hvWp : v ∈ W p := SetLike.le_def.mp hVle hv
  have hfxy : f (x, y) = f p := by
    have h := hW p (p.1⁻¹ * x) hx (p.2⁻¹ * y) hy
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  have hfxuyv : f (x * u, y * v) = f p := by
    have hxu : p.1⁻¹ * (x * u) ∈ W p := by rw [← mul_assoc]; exact mul_mem hx huWp
    have hyv : p.2⁻¹ * (y * v) ∈ W p := by rw [← mul_assoc]; exact mul_mem hy hvWp
    have h := hW p (p.1⁻¹ * (x * u)) hxu (p.2⁻¹ * (y * v)) hyv
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  rw [hfxuyv, hfxy]

end DRCoh

open GQ2.DRCoh ContCoh

/-! ## The single-relator obstruction `drRelZ` -/

section RelZ

variable {L : Type*} [Group L]

/-- The three `D_R` generators `m 0, m 1, m 2` placed in `CentExt c` with zero fibre. -/
def drLift (m : Fin 3 → L) (c : TwoCocycle L) (k : Fin 3) : CentExt c := ((m k, 0) : CentExt c)

@[simp] theorem drLift_base (m : Fin 3 → L) (c : TwoCocycle L) (k : Fin 3) :
    (drLift m c k).base = m k := rfl

@[simp] theorem drLift_fib (m : Fin 3 → L) (c : TwoCocycle L) (k : Fin 3) :
    (drLift m c k).fib = 0 := rfl

/-- The **single-relator obstruction** of a 2-cocycle `c` relative to the marking `m : Fin 3 → L`:
the fibre coordinate of `drWord` evaluated at the zero-fibre lift.  The `D_R` analogue of
`WordCoh2.relZPair`, but a *single* `𝔽₂` value (one relator). -/
def drRelZ (m : Fin 3 → L) (c : TwoCocycle L) : ZMod 2 :=
  (drWord (drLift m c 0) (drLift m c 1) (drLift m c 2)).fib

/-- The base of the lifted relator value is the base relator value. -/
theorem drRelZ_base (m : Fin 3 → L) (c : TwoCocycle L) :
    (drWord (drLift m c 0) (drLift m c 1) (drLift m c 2)).base = drWord (m 0) (m 1) (m 2) := by
  have h := map_drWord (CentExt.proj c) (drLift m c 0) (drLift m c 1) (drLift m c 2)
  simpa only [CentExt.proj, MonoidHom.coe_mk, OneHom.coe_mk, drLift_base] using h

end RelZ

section RelZComap

variable {L L' : Type*} [Group L] [Group L']

/-- **Level-independence.**  Pulling `c` back along `φ` and pushing the marking forward by `φ` give
the same obstruction (`WordCoh2.relZPair_comap`, single relator). -/
theorem drRelZ_comap (m : Fin 3 → L') (c : TwoCocycle L) (φ : L' →* L) :
    drRelZ (fun k => φ (m k)) c = drRelZ m (c.comap φ) := by
  have h := map_drWord (projExt c φ) (drLift m (c.comap φ) 0) (drLift m (c.comap φ) 1)
    (drLift m (c.comap φ) 2)
  have hlift : ∀ k, projExt c φ (drLift m (c.comap φ) k) = drLift (fun k => φ (m k)) c k :=
    fun _ => rfl
  rw [hlift, hlift, hlift] at h
  show (drWord (drLift (fun k => φ (m k)) c 0) _ _).fib = (drWord (drLift m (c.comap φ) 0) _ _).fib
  rw [← h, projExt_fib]

end RelZComap

section RelZAdd

variable {L : Type*} [Group L]

/-- The fiber-product lift of a marking (both fibres zero). -/
def drLiftFP (m : Fin 3 → L) (c₁ c₂ : TwoCocycle L) (k : Fin 3) : FiberProd c₁ c₂ :=
  ((m k, 0, 0) : FiberProd c₁ c₂)

private theorem map_pr1_drLiftFP (m : Fin 3 → L) (c₁ c₂ : TwoCocycle L) (k : Fin 3) :
    FiberProd.pr1 (drLiftFP m c₁ c₂ k) = drLift m c₁ k := rfl

private theorem map_pr2_drLiftFP (m : Fin 3 → L) (c₁ c₂ : TwoCocycle L) (k : Fin 3) :
    FiberProd.pr2 (drLiftFP m c₁ c₂ k) = drLift m c₂ k := rfl

private theorem map_prSum_drLiftFP (m : Fin 3 → L) (c₁ c₂ : TwoCocycle L) (k : Fin 3) :
    FiberProd.prSum (drLiftFP m c₁ c₂ k) = drLift m (c₁ + c₂) k :=
  CentExt.ext rfl (add_zero (0 : ZMod 2))

/-- **Additivity of the relator obstruction** (`WordCoh2.relZPair_add`, single relator). -/
theorem drRelZ_add (m : Fin 3 → L) (c₁ c₂ : TwoCocycle L) :
    drRelZ m (c₁ + c₂) = drRelZ m c₁ + drRelZ m c₂ := by
  have h1 := map_drWord FiberProd.pr1 (drLiftFP m c₁ c₂ 0) (drLiftFP m c₁ c₂ 1) (drLiftFP m c₁ c₂ 2)
  have h2 := map_drWord FiberProd.pr2 (drLiftFP m c₁ c₂ 0) (drLiftFP m c₁ c₂ 1) (drLiftFP m c₁ c₂ 2)
  have hs := map_drWord FiberProd.prSum (drLiftFP m c₁ c₂ 0) (drLiftFP m c₁ c₂ 1)
    (drLiftFP m c₁ c₂ 2)
  simp only [map_pr1_drLiftFP] at h1
  simp only [map_pr2_drLiftFP] at h2
  simp only [map_prSum_drLiftFP] at hs
  show (drWord (drLift m (c₁ + c₂) 0) _ _).fib = (drWord (drLift m c₁ 0) _ _).fib
    + (drWord (drLift m c₂ 0) _ _).fib
  rw [← hs, ← h1, ← h2, FiberProd.prSum_fib, FiberProd.pr1_fib, FiberProd.pr2_fib]

end RelZAdd

section RelZCoboundary

variable {L : Type*} [Group L]

/-- Every relator value dies in `Multiplicative (ZMod 2)` (the abelian collapse `−4x + 2y ≡ 0`). -/
private theorem drWord_multZMod2_eq_one (u v w : Multiplicative (ZMod 2)) : drWord u v w = 1 := by
  revert u v w; decide

/-- **The obstruction of the split cocycle vanishes** (`WordCoh2.relZPair_zero`). -/
theorem drRelZ_zero (m : Fin 3 → L) : drRelZ m (zeroCocycle : TwoCocycle L) = 0 := by
  have h := map_drWord (fibHom0 (L := L)) (drLift m zeroCocycle 0) (drLift m zeroCocycle 1)
    (drLift m zeroCocycle 2)
  have hgen : ∀ k, fibHom0 (drLift m (zeroCocycle : TwoCocycle L) k) = 1 := fun _ => rfl
  rw [hgen, hgen, hgen, drWord_multZMod2_eq_one] at h
  have hval : Multiplicative.ofAdd (drRelZ m (zeroCocycle : TwoCocycle L))
      = (1 : Multiplicative (ZMod 2)) := h
  simpa using Multiplicative.ofAdd.injective hval

/-- **The obstruction of a coboundary** is `lam` of the base relator value
(`WordCoh2.obs_coboundary_eq`, single relator).  It vanishes when the marking satisfies the
relation. -/
theorem drRelZ_coboundary (m : Fin 3 → L) (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    drRelZ m (coboundaryCocycle lam hlam1) = lam (drWord (m 0) (m 1) (m 2)) := by
  set θ : CentExt (coboundaryCocycle lam hlam1) →* Multiplicative (ZMod 2) :=
    (fibHom0 (L := L)).comp (Psi lam hlam1) with hθ
  have h := map_drWord θ (drLift m (coboundaryCocycle lam hlam1) 0)
    (drLift m (coboundaryCocycle lam hlam1) 1) (drLift m (coboundaryCocycle lam hlam1) 2)
  have hgen : ∀ k,
      θ (drLift m (coboundaryCocycle lam hlam1) k) = Multiplicative.ofAdd (lam (m k)) := by
    intro k
    show Multiplicative.ofAdd ((Psi lam hlam1 (drLift m (coboundaryCocycle lam hlam1) k)).fib) = _
    rw [Psi_fib, drLift_fib, drLift_base, zero_add]
  rw [hgen, hgen, hgen, drWord_multZMod2_eq_one] at h
  have hval : Multiplicative.ofAdd
      ((drWord (drLift m (coboundaryCocycle lam hlam1) 0) (drLift m (coboundaryCocycle lam hlam1) 1)
        (drLift m (coboundaryCocycle lam hlam1) 2)).fib
      + lam (drWord (m 0) (m 1) (m 2))) = (1 : Multiplicative (ZMod 2)) := by
    rw [← h]
    show _ = Multiplicative.ofAdd
      ((Psi lam hlam1 (drWord (drLift m (coboundaryCocycle lam hlam1) 0) _ _)).fib)
    rw [Psi_fib, drRelZ_base]
  have hsum : drRelZ m (coboundaryCocycle lam hlam1) + lam (drWord (m 0) (m 1) (m 2)) = 0 :=
    Multiplicative.ofAdd.injective (hval.trans ofAdd_zero.symm)
  rw [eq_neg_of_add_eq_zero_left hsum, CharTwo.neg_eq]

end RelZCoboundary

end GQ2
