/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.LFox
import GQ2.Dyadic.Certificates.N0
import GQ2.Dyadic.Word.StokesDual

/-!
# Dyadic campaign, ticket WL-c: Stokes, scalar, Hessian and phase certificates for `L_sq`

The closing file of the type-`L` lane (packet Def. 9.1 items (5)–(6) for **row 1** of the R5
selection freeze), on top of WL-a's word (`GQ2/Dyadic/Words/L.lean`), WL-b's Fox certificate
(`GQ2/Dyadic/Certificates/LFox.lean`), WW3's second-order layer
(`GQ2/Dyadic/Word/Stokes.lean`) and WW4's Hessian/phase interface
(`GQ2/Dyadic/Word/{Hessian,Phase}.lean`).

```
R^{sq}_{L,n} = (x₀^σ)⁻¹ (x₀⁻³τ)^{ω₂} x₁² [x₁, x₁^{σ₂}] · ∏_{j=1}^{h} [x_{2j}, x_{2j+1}]
```

`n = 2h + 1`.  Per WL-recon's Q3 split the file is written in the order **c2 then c1**: the
scalar/Hilbert layer first (it was the lane's only can-fail item), then Stokes/Hessian/
determinant/phase.

-/

namespace GQ2.Dyadic.Certificates.LSqStokes

open GQ2.FoxH GQ2.Dyadic.Words.LSq GQ2.Dyadic.Certificates.LSq

/-! # Part c2 — the scalar / Hilbert layer

## §1 `hHilb`, reduced

S2.4 §5.5 asks for the *arithmetic* half of packet item (5): `H¹(G_K, 𝔽₂) = K^×/(K^×)²` has
dimension `n + 2`, its mod-2 cup form is the Hilbert symbol, and — "by Witt cancellation over
`𝔽₂`" — every such form is isometric to `⟨1⟩ ⊥ H^{⊥(h+1)}` with `(n+1)/2 = h + 1`.  WL-recon
V8/R4 flags this as the lane's only can-fail item, "the least mathlib-supported", and
authorises landing it as a hypothesis binder.

**It does not need Witt cancellation, and it is a theorem.**  The reduction below replaces the
quadratic-form classification by three elementary observations, and the residue is a *symplectic*
normal form, which is proved here from scratch:

1. The Bockstein diagonal is automatically additive.  For any symmetric biadditive
   `b : W → W → 𝔽₂`, `b(v+w,v+w) = b(v,v) + b(w,w) + 2·b(v,w) = b(v,v) + b(w,w)`
   (`IsCupFormFp2.diag_add`).  So `z ↦ z ∪ z` is a linear functional for free; the draft's
   Labute identity `z∪z = z∪κ` is *the statement that `κ` represents it*, not an extra
   constraint on the form.
2. `κ` is a vector: nondegeneracy turns the functional `d` into a vector `e` with
   `b e w = b w w`.  Then `e` is automatically in the radical of the alternating part
   `b' = b + d⊗d`, and `d e = b e e`.
3. **`q_K = 2` is exactly `b e e = 1`** — the anisotropy of that radical.  For type `L`,
   `n` odd forces `i ∉ K`, hence `q_K = 2`; and this single `𝔽₂` equation is the *whole*
   arithmetic content beyond nondegeneracy.  With it, `W = ⟨e⟩ ⊥ ker d` orthogonally, `b`
   restricted to `ker d` is alternating and nondegenerate, and the symplectic normal form
   finishes.

So `exists_cupForm_normalForm` below is unconditional given `IsCupFormFp2 b`, `NondegFp2 b` and
the `e`-datum.  **Nothing in part c2 is a hypothesis binder and nothing is an axiom**, and no
`𝔽₂` quadratic-form classification is used — the missing mathlib theory wl-recon priced is not
on the path.

What stays outside a *word* ticket is only the identification of `(H¹(G_K,𝔽₂), ⌣)` with a `W`
satisfying those hypotheses.  The vocabulary for it already exists in the repo for a general
dyadic `K` — `H1 k.fixingSubgroup (ZMod 2)`, `kummerClassK` (`GQ2/EvensKahn.lean:437`) with
`kummerClassK_surjective`, the trivial cup pairing `⌣[·]` (`GQ2/Demushkin.lean:95`) and the
Hilbert-symbol identification (census axiom **B11a**,
`hilbertSymbol_normCriterion_finiteDyadic`, `GQ2/Foundations/Axioms.lean:433`) — so the residue
is three *named* field-side facts, none of them a form classification:

* `dim_{𝔽₂} H¹(G_K,𝔽₂) = n + 2` — derivable from `absGalK_localEulerCharacteristic`
  (`GQ2/Dyadic/LocalGauss/EulerShapiro.lean:782`), not currently stated anywhere;
* perfectness of the cup pairing (local duality) — supplying `NondegFp2`;
* `q_K = 2`, i.e. `(−1,−1)_K = −1` — supplying `e` and `b e e = 1`.

Those are AS1/AS4's, not WL's: no word ticket owns a field. -/

section CupForm

variable {W : Type*} [AddCommGroup W]

/-- A **cup–Bockstein form** on an `𝔽₂`-space: symmetric and biadditive.  The diagonal
`v ↦ b v v` is the Bockstein square; `diag_add` below shows it is additive automatically, which
is why `sqCore_cupGram` records the `L_sq` core datum as *the Gram matrix of a symmetric bilinear
form* and not as a quadratic form with an Arf invariant. -/
structure IsCupFormFp2 (b : W → W → ZMod 2) : Prop where
  /-- Symmetry — graded commutativity of `⌣` in characteristic two. -/
  symm : ∀ v w, b v w = b w v
  /-- Additivity in the first slot (with symmetry this gives biadditivity). -/
  add_left : ∀ u v w, b (u + v) w = b u w + b v w

namespace IsCupFormFp2

variable {b : W → W → ZMod 2} (hb : IsCupFormFp2 b)

include hb

theorem add_right (u v w : W) : b u (v + w) = b u v + b u w := by
  rw [hb.symm u, hb.add_left, hb.symm v, hb.symm w]

theorem zero_left (w : W) : b 0 w = 0 := by
  have h := hb.add_left 0 0 w
  rw [add_zero] at h
  rw [← CharTwo.add_self_eq_zero (b 0 w)]
  exact h

theorem zero_right (v : W) : b v 0 = 0 := by rw [hb.symm, hb.zero_left]

/-- **The Bockstein diagonal is additive, for free**: the two cross terms cancel in
characteristic two.  This is the observation that removes the quadratic-form classification
from `hHilb`. -/
theorem diag_add (v w : W) : b (v + w) (v + w) = b v v + b w w := by
  rw [hb.add_left, hb.add_right, hb.add_right, hb.symm w v, add_assoc,
    ← add_assoc (b v w), CharTwo.add_self_eq_zero, zero_add]

/-- The diagonal, as an additive map. -/
def diagHom : W →+ ZMod 2 where
  toFun v := b v v
  map_zero' := hb.zero_left 0
  map_add' v w := hb.diag_add v w

@[simp] theorem diagHom_apply (v : W) : hb.diagHom v = b v v := rfl

/-- `𝔽₂`-homogeneity in the first slot: over `𝔽₂` biadditivity already gives bilinearity. -/
theorem smul_left [Module (ZMod 2) W] (c : ZMod 2) (v w : W) : b (c • v) w = c * b v w := by
  rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, hb.zero_left, zero_mul]
  · rw [one_smul, one_mul]

theorem smul_right [Module (ZMod 2) W] (c : ZMod 2) (v w : W) : b v (c • w) = c * b v w := by
  rw [hb.symm, hb.smul_left, hb.symm]

end IsCupFormFp2

/-- Nondegeneracy of a pairing: only `0` pairs trivially with everything. -/
def NondegFp2 (b : W → W → ZMod 2) : Prop := ∀ v : W, (∀ w, b v w = 0) → v = 0

/-- **A symplectic form over `𝔽₂`**: biadditive, alternating, nondegenerate.  Symmetry is a
consequence (`IsSymplecticFp2.symm`), not a field. -/
structure IsSymplecticFp2 (b : W → W → ZMod 2) : Prop where
  /-- Additivity in the first slot. -/
  add_left : ∀ u v w, b (u + v) w = b u w + b v w
  /-- Additivity in the second slot. -/
  add_right : ∀ u v w, b u (v + w) = b u v + b u w
  /-- Alternating. -/
  alt : ∀ v, b v v = 0
  /-- Nondegenerate. -/
  nondeg : NondegFp2 b

namespace IsSymplecticFp2

variable {b : W → W → ZMod 2} (hb : IsSymplecticFp2 b)

include hb

theorem zero_left (w : W) : b 0 w = 0 := by
  have h := hb.add_left 0 0 w
  rw [add_zero] at h
  rw [← CharTwo.add_self_eq_zero (b 0 w)]
  exact h

theorem zero_right (v : W) : b v 0 = 0 := by
  have h := hb.add_right v 0 0
  rw [add_zero] at h
  rw [← CharTwo.add_self_eq_zero (b v 0)]
  exact h

/-- Alternating + biadditive ⇒ symmetric (char 2). -/
theorem symm (v w : W) : b v w = b w v := by
  have h := hb.alt (v + w)
  rw [hb.add_left, hb.add_right, hb.add_right, hb.alt, hb.alt, zero_add, add_zero] at h
  rw [CharTwo.add_eq_iff_eq_add.mp h, zero_add]

theorem smul_left [Module (ZMod 2) W] (c : ZMod 2) (v w : W) : b (c • v) w = c * b v w := by
  rcases ZMod.eq_zero_or_eq_one c with rfl | rfl
  · rw [zero_smul, hb.zero_left, zero_mul]
  · rw [one_smul, one_mul]

theorem smul_right [Module (ZMod 2) W] (c : ZMod 2) (v w : W) : b v (c • w) = c * b v w := by
  rw [hb.symm, hb.smul_left, hb.symm]

end IsSymplecticFp2

end CupForm

/-! ### §1.1 The symplectic normal form over `𝔽₂`

The one piece of genuine linear algebra: a nondegenerate alternating `𝔽₂`-form on a finite space
is an orthogonal sum of hyperbolic planes.  Proved by the standard plane-splitting induction
(pick `v ≠ 0`, complete it to a hyperbolic pair, split off the orthogonal complement), with the
recursion carried on `Nat.card`.  This is what S2.4 §5.5 reached for as "Witt cancellation"; the
alternating case needs no cancellation theorem. -/

section Symplectic

/-- The standard hyperbolic Gram on `Fin m → 𝔽₂ × 𝔽₂` — `m` orthogonal hyperbolic planes. -/
def hypGram {m : ℕ} (p r : Fin m → ZMod 2 × ZMod 2) : ZMod 2 :=
  ∑ j, ((p j).1 * (r j).2 + (p j).2 * (r j).1)

@[simp] theorem hypGram_zero (p r : Fin 0 → ZMod 2 × ZMod 2) : hypGram p r = 0 := by
  simp [hypGram]

theorem hypGram_cons {m : ℕ} (p₀ r₀ : ZMod 2 × ZMod 2)
    (p r : Fin m → ZMod 2 × ZMod 2) :
    hypGram (Fin.cons p₀ p) (Fin.cons r₀ r)
      = (p₀.1 * r₀.2 + p₀.2 * r₀.1) + hypGram p r := by
  simp [hypGram, Fin.sum_univ_succ]

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- The orthogonal complement of a hyperbolic pair, as a submodule. -/
def hypPerp (b : W → W → ZMod 2) (hb : IsSymplecticFp2 b) (v w : W) : Submodule (ZMod 2) W where
  carrier := {u | b v u = 0 ∧ b w u = 0}
  add_mem' := fun hx hy => by
    exact ⟨by rw [hb.add_right, hx.1, hy.1, add_zero],
      by rw [hb.add_right, hx.2, hy.2, add_zero]⟩
  zero_mem' := ⟨hb.zero_right v, hb.zero_right w⟩
  smul_mem' := fun c _ hx => by
    exact ⟨by rw [hb.smul_right, hx.1, mul_zero], by rw [hb.smul_right, hx.2, mul_zero]⟩

@[simp] theorem mem_hypPerp {b : W → W → ZMod 2} {hb : IsSymplecticFp2 b} {v w u : W} :
    u ∈ hypPerp b hb v w ↔ b v u = 0 ∧ b w u = 0 := Iff.rfl

/-- The projection onto the hyperbolic complement. -/
theorem hypProj_mem {b : W → W → ZMod 2} (hb : IsSymplecticFp2 b) {v w : W}
    (hvw : b v w = 1) (u : W) :
    u + (b w u) • v + (b v u) • w ∈ hypPerp b hb v w := by
  have hwv : b w v = 1 := by rw [← hb.symm]; exact hvw
  constructor
  · rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hb.alt, hvw, mul_zero,
      add_zero, mul_one, CharTwo.add_self_eq_zero]
  · rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hb.alt, hwv, mul_one,
      mul_zero, add_zero, CharTwo.add_self_eq_zero]

/-- The restricted form on the complement is again symplectic. -/
theorem isSymplectic_restrict {b : W → W → ZMod 2} (hb : IsSymplecticFp2 b) {v w : W}
    (hvw : b v w = 1) :
    IsSymplecticFp2 (fun x y : hypPerp b hb v w => b (x : W) (y : W)) where
  add_left u v' w' := hb.add_left _ _ _
  add_right u v' w' := hb.add_right _ _ _
  alt u := hb.alt _
  nondeg := by
    intro u hu
    have huv : b (u : W) v = 0 := by rw [hb.symm]; exact u.2.1
    have huw : b (u : W) w = 0 := by rw [hb.symm]; exact u.2.2
    have hu0 : (u : W) = 0 := by
      refine hb.nondeg _ fun y => ?_
      have hy : (y + (b w y) • v + (b v y) • w : W) ∈ hypPerp b hb v w :=
        hypProj_mem hb hvw y
      have hval : b (u : W) (y + (b w y) • v + (b v y) • w) = 0 := hu ⟨_, hy⟩
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, huv, huw,
        mul_zero, mul_zero, add_zero, add_zero] at hval
      exact hval
    exact Subtype.ext hu0

/-- The plane-splitting Gram identity: `b` is the hyperbolic plane on `(v,w)` **plus** the
restricted form on the complement, read through the projection.  This is the whole content of
the induction step; everything else is bookkeeping. -/
theorem hypSplit_gram {b : W → W → ZMod 2} (hb : IsSymplecticFp2 b) {v w : W}
    (hvw : b v w = 1) (x y : W) :
    b x y = (b w x * b v y + b v x * b w y)
      + b (x + (b w x) • v + (b v x) • w) (y + (b w y) • v + (b v y) • w) := by
  have hwv : b w v = 1 := by rw [← hb.symm]; exact hvw
  have hxv : b x v = b v x := hb.symm x v
  have hxw : b x w = b w x := hb.symm x w
  rw [hb.add_left, hb.add_left, hb.add_right, hb.add_right, hb.add_right, hb.add_right,
    hb.add_right, hb.add_right]
  simp only [hb.smul_left, hb.smul_right, hb.alt, hvw, hwv, hxv, hxw, mul_zero, mul_one,
    add_zero, zero_add]
  ring_nf
  simp [show (4 : ZMod 2) = 0 from by decide]

end Symplectic

/-! ### §1.2 The recursion

`Nat.card`-decreasing induction on the plane splitting.  The bound variable `N` carries the
recursion so that the statement can stay universe-polymorphic in `W` (the complement is a
submodule of `W`, hence in the same universe). -/

section SymplecticNormalForm

universe u

/-- `M × (Fin m → M) ≃ₗ Fin (m+1) → M`, the `Fin.cons`/`Fin.tail` pair as a linear equivalence.
Stated for `ZMod 2` only, which is all the recursion needs. -/
def consLinearEquiv (m : ℕ) (M : Type*) [AddCommGroup M] [Module (ZMod 2) M] :
    (M × (Fin m → M)) ≃ₗ[ZMod 2] (Fin (m + 1) → M) where
  toFun p := Fin.cons p.1 p.2
  map_add' p q := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c p := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  invFun z := (z 0, Fin.tail z)
  left_inv p := by simp [Fin.tail_cons]
  right_inv z := by simp [Fin.cons_self_tail]

@[simp] theorem consLinearEquiv_apply {m : ℕ} {M : Type*} [AddCommGroup M] [Module (ZMod 2) M]
    (p : M × (Fin m → M)) : consLinearEquiv m M p = Fin.cons p.1 p.2 := rfl

variable {W : Type u} [AddCommGroup W] [Module (ZMod 2) W]

/-- The plane-splitting equivalence `W ≃ₗ (𝔽₂ × 𝔽₂) × (v,w)^⊥`. -/
noncomputable def hypSplitEquiv {b : W → W → ZMod 2} (hb : IsSymplecticFp2 b) {v w : W}
    (hvw : b v w = 1) : W ≃ₗ[ZMod 2] (ZMod 2 × ZMod 2) × hypPerp b hb v w where
  toFun u := ((b w u, b v u), ⟨u + (b w u) • v + (b v u) • w, hypProj_mem hb hvw u⟩)
  map_add' u u' := by
    refine Prod.ext (Prod.ext (hb.add_right _ _ _) (hb.add_right _ _ _)) (Subtype.ext ?_)
    show u + u' + (b w (u + u')) • v + (b v (u + u')) • w
      = (u + (b w u) • v + (b v u) • w) + (u' + (b w u') • v + (b v u') • w)
    rw [hb.add_right, hb.add_right, add_smul, add_smul]
    abel
  map_smul' c u := by
    refine Prod.ext (Prod.ext (hb.smul_right _ _ _) (hb.smul_right _ _ _)) (Subtype.ext ?_)
    show c • u + (b w (c • u)) • v + (b v (c • u)) • w
      = c • (u + (b w u) • v + (b v u) • w)
    rw [hb.smul_right, hb.smul_right, smul_add, smul_add, mul_smul, mul_smul]
  invFun p := p.1.1 • v + p.1.2 • w + (p.2 : W)
  left_inv u := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    show (b w u) • v + (b v u) • w + (u + (b w u) • v + (b v u) • w) = u
    calc (b w u) • v + (b v u) • w + (u + (b w u) • v + (b v u) • w)
        = u + ((b w u) • v + (b w u) • v) + ((b v u) • w + (b v u) • w) := by abel
      _ = u := by rw [h2, h2, add_zero, add_zero]
  right_inv p := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    have hwv : b w v = 1 := by rw [← hb.symm]; exact hvw
    have hbw : b w (p.1.1 • v + p.1.2 • w + (p.2 : W)) = p.1.1 := by
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hwv, hb.alt w,
        mul_one, mul_zero, add_zero, p.2.2.2, add_zero]
    have hbv : b v (p.1.1 • v + p.1.2 • w + (p.2 : W)) = p.1.2 := by
      rw [hb.add_right, hb.add_right, hb.smul_right, hb.smul_right, hvw, hb.alt v,
        mul_zero, mul_one, zero_add, p.2.2.1, add_zero]
    refine Prod.ext (Prod.ext hbw hbv) (Subtype.ext ?_)
    show p.1.1 • v + p.1.2 • w + (p.2 : W)
        + (b w (p.1.1 • v + p.1.2 • w + (p.2 : W))) • v
        + (b v (p.1.1 • v + p.1.2 • w + (p.2 : W))) • w = (p.2 : W)
    rw [hbw, hbv]
    calc p.1.1 • v + p.1.2 • w + (p.2 : W) + p.1.1 • v + p.1.2 • w
        = (p.2 : W) + (p.1.1 • v + p.1.1 • v) + (p.1.2 • w + p.1.2 • w) := by abel
      _ = (p.2 : W) := by rw [h2, h2, add_zero, add_zero]

/-- The recursion carrier.  `N` bounds `Nat.card W`, so the statement stays in one universe. -/
theorem exists_symplectic_equiv_aux :
    ∀ (N : ℕ) {W : Type u} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
      (b : W → W → ZMod 2), IsSymplecticFp2 b → Nat.card W ≤ N →
      ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] (Fin m → ZMod 2 × ZMod 2)),
        ∀ x y, b x y = hypGram (φ x) (φ y) := by
  intro N
  induction N with
  | zero =>
    intro W _ _ _ b _ hcard
    exact absurd hcard (by simpa using Nat.card_pos (α := W).ne')
  | succ N ih =>
    intro W _ _ _ b hb hcard
    by_cases hzero : ∀ x : W, x = 0
    · refine ⟨0, ?_, ?_⟩
      · exact
          { toFun := fun _ => 0
            map_add' := fun _ _ => by simp
            map_smul' := fun _ _ => by simp
            invFun := fun _ => 0
            left_inv := fun x => (hzero x).symm
            right_inv := fun y => funext fun i => i.elim0 }
      · intro x y
        rw [hzero x, hb.zero_left]
        simp [hypGram]
    · push_neg at hzero
      obtain ⟨v, hv⟩ := hzero
      have hex : ∃ w, b v w ≠ 0 := by
        by_contra hcon
        push_neg at hcon
        exact hv (hb.nondeg v hcon)
      obtain ⟨w, hw⟩ := hex
      have hvw : b v w = 1 := by
        rcases ZMod.eq_zero_or_eq_one (b v w) with h | h
        · exact absurd h hw
        · exact h
      have hwv : b w v = 1 := by rw [← hb.symm]; exact hvw
      have hvnot : v ∉ hypPerp b hb v w := by
        intro hmem
        exact one_ne_zero (hwv ▸ hmem.2)
      have hlt : Nat.card (hypPerp b hb v w) < Nat.card W := by
        have hsub : ((hypPerp b hb v w : Submodule (ZMod 2) W) : Set W) ⊂ Set.univ :=
          ⟨Set.subset_univ _, fun hle => hvnot (hle (Set.mem_univ v))⟩
        have hne := Set.ncard_lt_ncard hsub Set.finite_univ
        rw [Set.ncard_univ] at hne
        exact hne
      obtain ⟨m, φ', hφ'⟩ :=
        ih (fun x y : hypPerp b hb v w => b (x : W) (y : W))
          (isSymplectic_restrict hb hvw) (by omega)
      refine ⟨m + 1, (hypSplitEquiv hb hvw).trans
        (((LinearEquiv.refl (ZMod 2) (ZMod 2 × ZMod 2)).prodCongr φ').trans
          (consLinearEquiv m (ZMod 2 × ZMod 2))), fun x y => ?_⟩
      show b x y = hypGram (Fin.cons (b w x, b v x) (φ' _))
        (Fin.cons (b w y, b v y) (φ' _))
      rw [hypGram_cons, ← hφ']
      exact hypSplit_gram hb hvw x y

/-- **The symplectic normal form over `𝔽₂`** — a nondegenerate alternating biadditive form on a
finite `𝔽₂`-space is an orthogonal sum of hyperbolic planes, in an explicit linear equivalence
with the inverse witness built in.

Neither this repo nor the pinned mathlib had any `𝔽₂` form classification: mathlib's
diagonalization chain (`equivalent_weightedSumSquares`) is gated on `Invertible (2 : K)`, and
there is no hyperbolic plane, no Witt decomposition and no Witt cancellation anywhere in
`Mathlib/LinearAlgebra/QuadraticForm/`.  This is the piece S2.4 §5.5 called for. -/
theorem exists_symplectic_equiv [Finite W] (b : W → W → ZMod 2) (hb : IsSymplecticFp2 b) :
    ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] (Fin m → ZMod 2 × ZMod 2)),
      ∀ x y, b x y = hypGram (φ x) (φ y) :=
  exists_symplectic_equiv_aux (Nat.card W) b hb le_rfl

/-! ### §1.3 `hHilb` itself

The cup-form normal form `⟨1⟩ ⊥ H^{⊥m}`.  The vector `e` is *the arithmetic datum*: on
`H¹(G_K,𝔽₂) = K^×/(K^×)²` it is the class `κ` of the cyclotomic character (equivalently of `−1`),
`he` is the draft's Labute identity `z ∪ z = z ∪ κ` (`draft.tex:372–375`), and `he1` is
`(−1,−1)_K = −1`, i.e. **`q_K = 2`** — which for type `L` follows from `n` odd (`i ∉ K`).
Nothing else about the field is used. -/

/-- The kernel of the Bockstein diagonal, as an `𝔽₂`-subspace. -/
def cupKer {b : W → W → ZMod 2} (hb : IsCupFormFp2 b) : Submodule (ZMod 2) W where
  carrier := {u | b u u = 0}
  add_mem' := fun hx hy => by
    show b _ _ = 0
    rw [hb.diag_add, hx, hy, add_zero]
  zero_mem' := hb.zero_left 0
  smul_mem' := fun c u hu => by
    show b _ _ = 0
    rw [hb.smul_left, hb.smul_right, hu, mul_zero, mul_zero]

@[simp] theorem mem_cupKer {b : W → W → ZMod 2} {hb : IsCupFormFp2 b} {u : W} :
    u ∈ cupKer hb ↔ b u u = 0 := Iff.rfl

/-- On the diagonal kernel the form is symplectic — alternating by construction, nondegenerate
by the `e`-splitting. -/
theorem isSymplectic_cupKer {b : W → W → ZMod 2} (hb : IsCupFormFp2 b) (hnd : NondegFp2 b)
    {e : W} (he : ∀ w, b e w = b w w) (he1 : b e e = 1) :
    IsSymplecticFp2 (fun x y : cupKer hb => b (x : W) (y : W)) where
  add_left u v w := hb.add_left _ _ _
  add_right u v w := hb.add_right _ _ _
  alt u := u.2
  nondeg := by
    intro u hu
    have hsq : ∀ c : ZMod 2, c * c = c := by decide
    have hu0 : (u : W) = 0 := by
      refine hnd _ fun y => ?_
      have hmem : (y + (b y y) • e : W) ∈ cupKer hb := by
        show b _ _ = 0
        rw [hb.diag_add, hb.smul_left, hb.smul_right, he1, mul_one, hsq,
          CharTwo.add_self_eq_zero]
      have hval : b (u : W) (y + (b y y) • e) = 0 := hu ⟨_, hmem⟩
      rw [hb.add_right, hb.smul_right, hb.symm (u : W) e, he, u.2, mul_zero,
        add_zero] at hval
      exact hval
    exact Subtype.ext hu0

/-- The `⟨1⟩ ⊥ (symplectic)` splitting `W ≃ₗ 𝔽₂ × ker d` along the anisotropic vector `e`. -/
noncomputable def cupSplitEquiv {b : W → W → ZMod 2} (hb : IsCupFormFp2 b) {e : W}
    (he : ∀ w, b e w = b w w) (he1 : b e e = 1) : W ≃ₗ[ZMod 2] ZMod 2 × cupKer hb where
  toFun u := (b e u, ⟨u + (b e u) • e, by
    show b _ _ = 0
    have hsq : ∀ c : ZMod 2, c * c = c := by decide
    rw [hb.diag_add, hb.smul_left, hb.smul_right, he1, mul_one, hsq, he,
      CharTwo.add_self_eq_zero]⟩)
  map_add' u u' := by
    refine Prod.ext (hb.add_right _ _ _) (Subtype.ext ?_)
    show u + u' + (b e (u + u')) • e = (u + (b e u) • e) + (u' + (b e u') • e)
    rw [hb.add_right, add_smul]
    abel
  map_smul' c u := by
    refine Prod.ext (hb.smul_right _ _ _) (Subtype.ext ?_)
    show c • u + (b e (c • u)) • e = c • (u + (b e u) • e)
    rw [hb.smul_right, smul_add, mul_smul]
  invFun p := p.1 • e + (p.2 : W)
  left_inv u := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    show (b e u) • e + (u + (b e u) • e) = u
    calc (b e u) • e + (u + (b e u) • e) = u + ((b e u) • e + (b e u) • e) := by abel
      _ = u := by rw [h2, add_zero]
  right_inv p := by
    have h2 : ∀ x : W, x + x = 0 := GQ2.Dyadic.Certificates.module_zmod2_two_torsion
    have hke : b e (p.2 : W) = 0 := by rw [he]; exact p.2.2
    have hbe : b e (p.1 • e + (p.2 : W)) = p.1 := by
      rw [hb.add_right, hb.smul_right, he1, mul_one, hke, add_zero]
    refine Prod.ext hbe (Subtype.ext ?_)
    show p.1 • e + (p.2 : W) + (b e (p.1 • e + (p.2 : W))) • e = (p.2 : W)
    rw [hbe]
    calc p.1 • e + (p.2 : W) + p.1 • e = (p.2 : W) + (p.1 • e + p.1 • e) := by abel
      _ = (p.2 : W) := by rw [h2, add_zero]

/-- The `⟨1⟩ ⊥ (rest)` Gram identity along the splitting. -/
theorem cupSplit_gram {b : W → W → ZMod 2} (hb : IsCupFormFp2 b) {e : W}
    (he : ∀ w, b e w = b w w) (he1 : b e e = 1) (a a' : ZMod 2) (k k' : cupKer hb) :
    b (a • e + (k : W)) (a' • e + (k' : W)) = a * a' + b (k : W) (k' : W) := by
  have hk : b (k : W) (k : W) = 0 := k.2
  have hk' : b (k' : W) (k' : W) = 0 := k'.2
  rw [hb.add_left, hb.add_right, hb.add_right, hb.smul_left, hb.smul_left,
    hb.smul_right, hb.smul_right, he1, mul_one, he, hk', mul_zero, add_zero,
    hb.symm (k : W) e, he, hk, mul_zero, zero_add]

/-- **`hHilb`, as a theorem.**  A nondegenerate `𝔽₂` cup–Bockstein form carrying an anisotropic
Labute vector `e` (`b e w = b w w`, `b e e = 1`) is isometric to `⟨1⟩ ⊥ H^{⊥m}` — the
`⟨1⟩ ⊥ (h+1) hyperbolic planes` of S2.4 §5.5, with `m` read off as `(dim W − 1)/2`.

This is the statement wl-recon V8/R4 priced as the lane's only can-fail item, on the strength of
"mathlib does not supply `𝔽₂`-quadratic-form classification / Witt cancellation".  The survey is
correct about mathlib; the *inference* was not, because the object is a symmetric bilinear form
whose diagonal is automatically linear (`IsCupFormFp2.diag_add`), so no quadratic-form
classification and no cancellation theorem is involved — only `exists_symplectic_equiv`. -/
theorem exists_cupForm_normalForm [Finite W] {b : W → W → ZMod 2} (hb : IsCupFormFp2 b)
    (hnd : NondegFp2 b) {e : W} (he : ∀ w, b e w = b w w) (he1 : b e e = 1) :
    ∃ (m : ℕ) (φ : W ≃ₗ[ZMod 2] ZMod 2 × (Fin m → ZMod 2 × ZMod 2)),
      ∀ x y, b x y = (φ x).1 * (φ y).1 + hypGram (φ x).2 (φ y).2 := by
  obtain ⟨m, ψ, hψ⟩ :=
    exists_symplectic_equiv (fun x y : cupKer hb => b (x : W) (y : W))
      (isSymplectic_cupKer hb hnd he he1)
  set φ₀ := cupSplitEquiv hb he he1 with hφ₀
  refine ⟨m, φ₀.trans ((LinearEquiv.refl (ZMod 2) (ZMod 2)).prodCongr ψ), fun x y => ?_⟩
  have hx : (φ₀ x).1 • e + ((φ₀ x).2 : W) = x := φ₀.left_inv x
  have hy : (φ₀ y).1 • e + ((φ₀ y).2 : W) = y := φ₀.left_inv y
  show b x y = (φ₀ x).1 * (φ₀ y).1 + hypGram (ψ (φ₀ x).2) (ψ (φ₀ y).2)
  rw [← hψ]
  calc b x y = b ((φ₀ x).1 • e + ((φ₀ x).2 : W)) ((φ₀ y).1 • e + ((φ₀ y).2 : W)) := by
        rw [hx, hy]
    _ = (φ₀ x).1 * (φ₀ y).1 + b ((φ₀ x).2 : W) ((φ₀ y).2 : W) :=
        cupSplit_gram hb he he1 _ _ _ _

end SymplecticNormalForm

/-! ## §2 The relator side: the degree-`n` cup Gram of `L_sq`

S2.4 §5.5's *relator* half, in MC2's own vocabulary (`GQ2/Dyadic/MarkedCore/Cores.lean`):
the fibre of the `L_sq` relator shape at a central lift into a cup cocycle.  This is the
type-`L` analogue of `mRelWord_centLift_fib`/`nRelWord_centLift_fib` — the assembly wl-recon
§2.4 names `lRelWord_centLift_fib` and calls "the same proof with a different factor list".

The value read off `sqRelWord_centLift_fib` is, in the letter basis `σ, x₀, x₁, u₁, v₁, …`,

```
⟨1⟩ on x₁      ⊥   H on (σ, x₀)   ⊥   H^{⊥h} on the handle pairs
```

on a space of rank `sqRank h = 3 + 2h = n + 2` — i.e. **`⟨1⟩ ⊥ H^{⊥(h+1)}`**, matching
`exists_cupForm_normalForm`'s target exactly, and reproducing `SqCore.sqCore_cupGram`
(`[[0,1,0],[1,0,0],[0,0,1]]` on `(σ*, x₀*, x₁*)`) at `h = 0`.  The two sides of packet item (5)
therefore meet in the *same* normal form, which is what the clause asserts.

Mechanism, factor by factor (all three of WL-b's "invisible at first order" items are visible
here, and two of them cancel):

* `(x₀^σ)⁻¹` contributes the `(σ,x₀)` **hyperbolic pair** plus a `κ(x₀,x₀)` Bockstein charge
  from the inversion seam;
* `x₀⁻³` contributes a second `κ(x₀,x₀)` (`diagCoeff 3 = 1`, the odd-cube augmentation-1
  mechanism WL-b measured at first order) — the two cancel, which is `diagCoeff 4 = 0`
  read on `x₀`'s total exponent `−4`;
* `x₁²` contributes the **anisotropic diagonal** `κ(x₁,x₁)` (`diagCoeff 2 = 1`);
* `[x₁, x₁^{σ₂}]` contributes **nothing**: on an elementary abelian base `x₁^{σ₂}` and `x₁`
  have the same image, so the block is a commutator of two lifts of one element
  (`commP_eq_one_of_base_eq`).  The `σ₂`-slot is invisible *here* — but not at second order
  (§4 below), which is the precise sense in which the square-commutator block does its work
  one degree up. -/

section RelatorGram

open GQ2 GQ2.Dyadic.MarkedCore GQ2.Dyadic.SqCore

variable {L : Type*} [Group L] {c : GQ2.DRCoh.TwoCocycle L} (hc : IsCupCocycle c)

include hc

/-- Two elements of the central extension over the **same** base commute: their `commP` is
trivial.  This is what kills the square-commutator block at the Gram level. -/
theorem commP_eq_one_of_base_eq {p q : GQ2.DRCoh.CentExt c} (hb : p.base = q.base) :
    commP p q = 1 := by
  have hinv : ∀ z : L, z⁻¹ = z := hc.inv_eq
  refine GQ2.DRCoh.CentExt.ext ?_ ?_
  · show p.base⁻¹ * q.base⁻¹ * p.base * q.base = 1
    rw [← hb, hinv, mul_assoc, mul_assoc, hc.expTwo, mul_one, hc.expTwo]
  · show p.fib + c.κ p.base p.base⁻¹ + (q.fib + c.κ q.base q.base⁻¹)
        + c.κ p.base⁻¹ q.base⁻¹ + p.fib + c.κ (p.base⁻¹ * q.base⁻¹) p.base + q.fib
        + c.κ (p.base⁻¹ * q.base⁻¹ * p.base) q.base = 0
    rw [← hb, hinv, hc.expTwo, one_mul, c.κ_one_left]
    ring_nf
    simp [show (4 : ZMod 2) = 0 from by decide, show (2 : ZMod 2) = 0 from by decide]

/-- The `σ`-conjugate of a central lift has the same base (the base group is abelian). -/
@[simp] theorem conjP_centLift_base (x s : L) :
    (conjP (centLift c x) (centLift c s)).base = x := by
  show s⁻¹ * x * s = x
  rw [hc.inv_eq, hc.comm s x, mul_assoc, hc.expTwo, mul_one]

/-- …and fibre the `(σ,x)` off-diagonal pair — the hyperbolic entry. -/
theorem conjP_centLift_fib (x s : L) :
    (conjP (centLift c x) (centLift c s)).fib = c.κ s x + c.κ x s := by
  show (centLift c s).fib + c.κ s s⁻¹ + (centLift c x).fib + c.κ s⁻¹ x
      + (centLift c s).fib + c.κ (s⁻¹ * x) s = _
  simp only [MarkedCore.centLift_fib, hc.inv_eq, hc.addLeft, zero_add, add_zero]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide]

/-- The core word has trivial base: on the abelianization `L_sq`'s core is `x₀⁻⁴ x₁²`. -/
@[simp] theorem sqWord_centLift_base (s x y : L) :
    (sqWord (centLift c s) (centLift c x) (centLift c y)).base = 1 := by
  have hcomm : commP (centLift c y) (conjP (centLift c y) (centLift c s)) = 1 :=
    commP_eq_one_of_base_eq hc (by rw [MarkedCore.centLift_base, conjP_centLift_base hc])
  have hx3 : x ^ 3 = x := by rw [pow_succ, hc.pow_two_eq_one, one_mul]
  have hA1b : (conjP (centLift c x) (centLift c s))⁻¹.base = x := by
    rw [MarkedCore.centExt_inv_base, conjP_centLift_base hc, hc.inv_eq]
  have hA2b : ((centLift c x) ^ 3)⁻¹.base = x := by
    rw [MarkedCore.centExt_inv_base, MarkedCore.centExt_pow_base, MarkedCore.centLift_base,
      hx3, hc.inv_eq]
  have hA3b : ((centLift c y) ^ 2).base = 1 := by
    rw [MarkedCore.centExt_pow_base, MarkedCore.centLift_base, hc.pow_two_eq_one]
  rw [sqWord, hcomm, mul_one, GQ2.DRCoh.CentExt.mul_base, GQ2.DRCoh.CentExt.mul_base,
    hA1b, hA2b, hA3b, hc.expTwo, mul_one]

/-- **The `L_sq` rank-3 core Gram value** — `⟨1⟩` on `x₁` and one hyperbolic plane on
`(σ, x₀)`.  This is `SqCore.sqCore_cupGram`'s matrix `[[0,1,0],[1,0,0],[0,0,1]]`, computed as a
relator fibre rather than as nine separate cup values, and generic in the cocycle. -/
theorem sqWord_centLift_fib (s x y : L) :
    (sqWord (centLift c s) (centLift c x) (centLift c y)).fib
      = c.κ y y + (c.κ s x + c.κ x s) := by
  have hcomm : commP (centLift c y) (conjP (centLift c y) (centLift c s)) = 1 :=
    commP_eq_one_of_base_eq hc (by rw [MarkedCore.centLift_base, conjP_centLift_base hc])
  have hx3 : x ^ 3 = x := by rw [pow_succ, hc.pow_two_eq_one, one_mul]
  have hA1b : (conjP (centLift c x) (centLift c s))⁻¹.base = x := by
    rw [MarkedCore.centExt_inv_base, conjP_centLift_base hc, hc.inv_eq]
  have hA1f : (conjP (centLift c x) (centLift c s))⁻¹.fib
      = c.κ s x + c.κ x s + c.κ x x := by
    rw [MarkedCore.centExt_inv_fib, conjP_centLift_fib hc, conjP_centLift_base hc, hc.inv_eq]
  have hA2b : ((centLift c x) ^ 3)⁻¹.base = x := by
    rw [MarkedCore.centExt_inv_base, MarkedCore.centExt_pow_base, MarkedCore.centLift_base,
      hx3, hc.inv_eq]
  have hA2f : ((centLift c x) ^ 3)⁻¹.fib = 0 := by
    rw [MarkedCore.centExt_inv_fib, MarkedCore.centLift_pow_fib (hc.kappa_pow_left x),
      MarkedCore.centExt_pow_base, MarkedCore.centLift_base, hx3, hc.inv_eq,
      show MarkedCore.diagCoeff 3 = 1 from by decide, one_mul, CharTwo.add_self_eq_zero]
  have hA3b : ((centLift c y) ^ 2).base = 1 := by
    rw [MarkedCore.centExt_pow_base, MarkedCore.centLift_base, hc.pow_two_eq_one]
  have hA3f : ((centLift c y) ^ 2).fib = c.κ y y := by
    rw [MarkedCore.centLift_pow_fib (hc.kappa_pow_left y),
      show MarkedCore.diagCoeff 2 = 1 from by decide, one_mul]
  rw [sqWord, hcomm, mul_one, GQ2.DRCoh.CentExt.mul_fib, GQ2.DRCoh.CentExt.mul_fib,
    GQ2.DRCoh.CentExt.mul_base, hA1b, hA1f, hA2b, hA2f, hA3b, hA3f, c.κ_one_right]
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide]

/-- **The full degree-`n` `L_sq` relator Gram value**, handles included — the `⟨1⟩ ⊥ H^{⊥(h+1)}`
of S2.4 §5.5 at rank `sqRank h = n + 2`, in the letter basis.  The `h`-generic handle block is
MC2's `handleWord_centLift_fib`, cited; nothing about the type-`L` word enters it. -/
theorem sqRelWord_centLift_fib {h : ℕ} (m : Fin (sqRank h) → L) :
    (sqRelWord (fun i => centLift c (m i))).fib
      = c.κ (m 2) (m 2) + (c.κ (m 0) (m 1) + c.κ (m 1) (m 0))
        + ∑ j, (c.κ (m (sqHandleIdxU j)) (m (sqHandleIdxV j))
            + c.κ (m (sqHandleIdxV j)) (m (sqHandleIdxU j))) := by
  rw [sqRelWord, MarkedCore.fib_mul_of_base_one (sqWord_centLift_base hc _ _ _),
    sqWord_centLift_fib hc, hc.handleWord_centLift_fib]

end RelatorGram

/-! # Part c1 — Stokes, duality, Hessian, determinant, phase

## §3 The second-order (Stokes) forms of `L_sq`

The four core factors of `R^{sq}_{L,n}` plus the handle tail, evaluated in the Heisenberg lift
at a simple-tame-module marking (`hwild` on every wild letter, `hτ` for the unramified class;
`σ` and `σ₂` are never restricted), one degree above WL-b's Fox rows.

Three things WL-b measured as **invisible at first order** are visible here, and this is the
whole reason the `L_sq` lane needs a second-order layer of its own:

* the **`x₁`-column** — `x₁²` has an odd `C(2,2)`, so it produces the diagonal `y₁(a₁)`;
* the **`σ₂`-slot** — `[x₁, x₁^{σ₂}]` contributes `y₁((S₂ + S₂⁻¹)a₁)` with `S₂ = S^{E ω₂}`,
  the operator that at first order could not be seen at all;
* **`q_K`** — through `C(q_K,2)`, odd exactly at `q_K ≡ 2 (mod 4)`, i.e. at `q_K = 2`
  (`heisZ_tameRelW_unram`, WN0-c's row, cited: it is word-independent).

The `x₀`-block is the mirror image of the compact-`N` boundary block on a different column
(WL-b's finding one degree up): `(x₀^σ)⁻¹` supplies the `S⁻¹`-twisted jet and the `(σ,x₀)` cross,
`x₀^{-3}` behaves as a *single* letter with zero central charge (`heisF_lSqNegCube` — the
second-order face of the odd-cube augmentation-1 mechanism), and the `ω₂`-block carries the
`e`/`C(e,2)` resolver sensitivity. -/

section StokesRows

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
  (y : Generator (2 * h + 1) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- An odd multiple of a `2`-torsion element is itself. -/
theorem odd_nsmul_eq_self {M : Type*} [AddCommGroup M] (hM : ∀ v : M, v + v = 0) {k : ℕ}
    (hk : Odd k) (v : M) : k • v = v := by
  obtain ⟨m, rfl⟩ := hk
  rw [add_nsmul, one_nsmul, mul_nsmul, two_nsmul, hM, smul_zero, zero_add]

/-- **Factor 1** — `(x₀^σ)⁻¹` carries the `S⁻¹`-twisted jet `(−S⁻¹a₀, −S⁻¹y₀)` and central value
`y_σ(a₀) + y₀(a_σ) + y₀(a₀)`; the diagonal `y₀(a₀)` is the `β(u⁻¹)`-rule's Bockstein term.  The
compact-`N` boundary block on the `x₀` column — WL-b's "same formal row, different column"
finding, one degree up. -/
theorem heisF_lSqInvConj (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma)))
      = ⟨-(t.σ⁻¹ • x (coreLetter h 0)), -(t.σ⁻¹ • y (coreLetter h 0)),
          y .sigma (x (coreLetter h 0)) + y (coreLetter h 0) (x .sigma)
            + y (coreLetter h 0) (x (coreLetter h 0)),
          (conjR (t (coreLetter h 0)) t.σ)⁻¹⟩ := by
  have h0 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 0)
  rw [heisEvalZ_inv, heisEvalZ_conj, heisEvalZ_gen, heisEvalZ_gen,
    heisConjR_of_trivial _ _ h0]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show -((conjR (t (coreLetter h 0)) t.σ)⁻¹ • t.σ⁻¹ • x (coreLetter h 0)) = _
    rw [mem_trivAct.mp (inv_mem (trivAct_conjR (LSq.trivAct_coreLetter t hwild 0) t.σ))]
  · show -((conjR (t (coreLetter h 0)) t.σ)⁻¹ • t.σ⁻¹ • y (coreLetter h 0)) = _
    rw [smul_elemDual_of_trivial
      (mem_trivAct.mp (inv_mem (trivAct_conjR (LSq.trivAct_coreLetter t hwild 0) t.σ)))]
  · show (0 : ZMod 2) + y .sigma (x (coreLetter h 0)) + y (coreLetter h 0) (x .sigma)
        + (t.σ⁻¹ • y (coreLetter h 0)) (t.σ⁻¹ • x (coreLetter h 0)) = _
    rw [ElemDual.smul_apply, inv_inv, smul_inv_smul, zero_add]
  · rfl

/-- **Factor 2a, the odd cube** — `x₀^{-3}` denotes as a *single letter* with **zero** central
charge: the two `C(3,2)`-carries cancel across the inversion.  This is the second-order face of
the augmentation-1 mechanism WL-b found at first order (the geometric sum over a trivially-acting
base has odd length), and it is why the `x₀`-diagonal of the whole row is the one that
`(x₀^σ)⁻¹` alone contributes. -/
theorem heisF_lSqNegCube (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 0)) (-3))
      = ⟨x (coreLetter h 0), y (coreLetter h 0), 0,
          (t (coreLetter h 0) ^ (3 : ℕ))⁻¹⟩ := by
  have h0 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 0)
  have h0p : ∀ a : A, (t (coreLetter h 0) ^ (3 : ℕ)) • a = a := by
    intro a; rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, h0, h0, h0]
  rw [heisEvalZ_zpow, heisEvalZ_gen, Words.LSq.zpow_neg_three, heisPow_of_trivial _ h0]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show -((t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • (3 : ℕ) • x (coreLetter h 0)) = _
    rw [mem_trivAct.mp (inv_mem (mem_trivAct.mpr h0p)),
      odd_nsmul_eq_self hA₂ (by decide), neg_eq_self hA₂]
  · show -((t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • (3 : ℕ) • y (coreLetter h 0)) = _
    rw [smul_elemDual_of_trivial (mem_trivAct.mp (inv_mem (mem_trivAct.mpr h0p))),
      odd_nsmul_eq_self ElemDual.add_self_eq_zero (by decide),
      neg_eq_self ElemDual.add_self_eq_zero]
  · show (3 : ℕ) • (0 : ZMod 2) + ((3 : ℕ).choose 2) • y (coreLetter h 0) (x (coreLetter h 0))
        + ((3 : ℕ) • y (coreLetter h 0)) ((3 : ℕ) • x (coreLetter h 0)) = 0
    rw [smul_zero, zero_add, odd_nsmul_eq_self hA₂ (by decide),
      odd_nsmul_eq_self ElemDual.add_self_eq_zero (by decide),
      nsmul_zmod2_odd (by decide : Odd ((3 : ℕ).choose 2)), CharTwo.add_self_eq_zero]
  · rfl

/-- **Factor 2b** — the `ω₂`-block's inner word `x₀^{-3}τ` (in the certificate's `prodList`
spelling): jet `(a₀ + a_τ, y₀ + y_τ)`, central value `y₀(a_τ)`. -/
theorem heisF_lSqInner (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂
        (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau])
      = ⟨x (coreLetter h 0) + x .tau, y (coreLetter h 0) + y .tau,
          y (coreLetter h 0) (x .tau),
          (t (coreLetter h 0) ^ (3 : ℕ))⁻¹ * t.τ⟩ := by
  have h0 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 0)
  have h0p : ∀ a : A, (t (coreLetter h 0) ^ (3 : ℕ)) • a = a := by
    intro a; rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, h0, h0, h0]
  have h0i : ∀ a : A, (t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • a = a :=
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr h0p))
  rw [PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, heisEvalZ_mul,
    heisEvalZ_mul, heisF_lSqNegCube t x y E E₂ hA₂ hwild, heisEvalZ_gen, heisEvalZ_one,
    mul_one]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · show x (coreLetter h 0) + (t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • x .tau = _
    rw [h0i]
  · show y (coreLetter h 0) + (t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • y .tau = _
    rw [smul_elemDual_of_trivial h0i]
  · show (0 : ZMod 2) + 0 + y (coreLetter h 0) ((t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • x .tau) = _
    rw [h0i, zero_add, zero_add]
  · rfl

/-- **Factor 2c** — `(x₀⁻³τ)^{ω₂}` at a resolver value `E ω₂ = e`: the `e`-th power of the inner
word by the trivial-base power law.  The `C(e,2)`-term dies exactly on `e ≡ 0, 1 (mod 4)` —
ticket S1.T's "the lift level is 4, not 2" on the type-`L` row. -/
theorem heisF_lSqOmegaBlock (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    heisEvalZ ⇑t x y E E₂
        (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
      = ⟨e • (x (coreLetter h 0) + x .tau), e • (y (coreLetter h 0) + y .tau),
          e • y (coreLetter h 0) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 0) + y .tau)
                (x (coreLetter h 0) + x .tau)),
          ((t (coreLetter h 0) ^ (3 : ℕ))⁻¹ * t.τ) ^ e⟩ := by
  have h0 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 0)
  have h0p : ∀ a : A, (t (coreLetter h 0) ^ (3 : ℕ)) • a = a := by
    intro a; rw [pow_succ, pow_succ, pow_one, mul_smul, mul_smul, h0, h0, h0]
  have h0i : ∀ a : A, (t (coreLetter h 0) ^ (3 : ℕ))⁻¹ • a = a :=
    mem_trivAct.mp (inv_mem (mem_trivAct.mpr h0p))
  have hbase : ∀ v : A, ((t (coreLetter h 0) ^ (3 : ℕ))⁻¹ * t.τ) • v = v := fun v => by
    rw [mul_smul, hτ, h0i]
  rw [PWord.omega2Pow, heisEvalZ_profPow, heisF_lSqInner t x y E E₂ hA₂ hwild, hE,
    zpow_natCast, heisPow_of_trivial _ hbase]

/-- **Factor 3** — `x₁²` is jet-zero central with value the **diagonal** `y₁(a₁)`: `C(2,2) = 1`.
This is the `⟨1⟩` of `⟨1⟩ ⊥ H^{⊥(h+1)}`, and the column WL-b's first-order row could not see. -/
theorem heisF_lSqSquare (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 1)) 2)
      = ⟨0, 0, y (coreLetter h 1) (x (coreLetter h 1)), t (coreLetter h 1) ^ (2 : ℕ)⟩ := by
  have h1 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 1)
  rw [heisEvalZ_zpow, heisEvalZ_gen, Words.LSq.zpow_two, heisPow_of_trivial _ h1]
  refine HeisLift.ext ?_ ?_ ?_ ?_
  · exact even_nsmul_eq_zero hA₂ (by decide) _
  · exact even_nsmul_eq_zero ElemDual.add_self_eq_zero (by decide) _
  · show (2 : ℕ) • (0 : ZMod 2) + ((2 : ℕ).choose 2) • _ = _
    rw [smul_zero, zero_add, nsmul_zmod2_odd (by decide : Odd ((2 : ℕ).choose 2))]
  · rfl

/-- **Factor 4, the square-commutator block** — `[x₁, x₁^{σ₂}]` is jet-zero central with value
`y₁(S₂⁻¹a₁) + y₁(S₂a₁) = y₁((S₂ + S₂⁻¹)a₁)`, where `S₂ = S^{E ω₂}` is the `σ₂`-operator.

**This is where `σ₂` finally does work.**  WL-b proved the block invisible at first order with no
hypothesis on `σ₂` anywhere; at second order the block *is* the `σ₂`-operator, and it is the
Wall-doubling `1 + U + U⁻¹` operator of the frozen `Γ_R` pairing seen at the letter level.  The
`σ₂` *offsets* `a_{σ₂}, y_{σ₂}` still do not appear — only the operator. -/
theorem heisF_lSqComm (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂
        (.comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) sigma2W))
      = ⟨0, 0, y (coreLetter h 1) ((t.σ ^ E omega2)⁻¹ • x (coreLetter h 1))
            + y (coreLetter h 1) ((t.σ ^ E omega2) • x (coreLetter h 1)),
          commR (t (coreLetter h 1))
            (conjR (t (coreLetter h 1)) (heisEvalZ ⇑t x y E E₂ sigma2W).g)⟩ := by
  have h1 := mem_trivAct.mp (LSq.trivAct_coreLetter t hwild 1)
  have hg : (heisEvalZ ⇑t x y E E₂ sigma2W).g = t.σ ^ E omega2 := by
    rw [sigma2W, PWord.omega2Pow, heisEvalZ_profPow]
    show (heisEvalZ ⇑t x y E E₂ (.gen Generator.sigma) ^ E omega2).g = _
    rw [show ∀ (p : HeisLift A C) (k : ℤ), (p ^ k).g = p.g ^ k from fun p k =>
      map_zpow HeisLift.gHom p k]
    rfl
  rw [heisEvalZ_comm, heisEvalZ_conj, heisEvalZ_gen,
    heisConjR_of_trivial _ _ h1,
    heisCommR_of_trivial _ _ h1
      (by show ∀ a : A, (conjR (t (coreLetter h 1)) _) • a = a
          exact mem_trivAct.mp (trivAct_conjR (LSq.trivAct_coreLetter t hwild 1) _))]
  refine HeisLift.ext rfl rfl ?_ rfl
  show y (coreLetter h 1) ((heisEvalZ ⇑t x y E E₂ sigma2W).g⁻¹ • x (coreLetter h 1))
      + ((heisEvalZ ⇑t x y E E₂ sigma2W).g⁻¹ • y (coreLetter h 1)) (x (coreLetter h 1)) = _
  rw [hg, ElemDual.smul_apply, inv_inv]

/-- **Factor 5, membership** — the handle block is jet-zero at every handle count. -/
theorem heisF_lSqHandles_mem (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    heisEvalZ ⇑t x y E E₂ (handlesW h) ∈ heisJetZero A C := by
  rw [handlesW]
  refine (heisEvalZ_prodList_jetZero ⇑t x y E E₂ ?_).1
  intro w hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (LSq.trivAct_handleU t hwild j))
      (mem_trivAct.mp (LSq.trivAct_handleV t hwild j))]
  exact ⟨rfl, rfl⟩

/-- **Factor 5, value** — `H_h` contributes exactly the `h` identity-operator hyperbolic planes,
at any handle count.  `S`, `T` and `σ₂` all stay out of the handle block. -/
theorem heisF_lSqHandles_z (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) :
    (heisEvalZ ⇑t x y E E₂ (handlesW h)).z
      = ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [handlesW]
  have hmem : ∀ w ∈ (List.finRange h).map fun j =>
      (PWord.comm (.gen (handleU j)) (.gen (handleV j)) : PWord (Generator (2 * h + 1))),
      heisEvalZ ⇑t x y E E₂ w ∈ heisJetZero A C := by
    intro w hw
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
      heisCommR_of_trivial _ _ (mem_trivAct.mp (LSq.trivAct_handleU t hwild j))
        (mem_trivAct.mp (LSq.trivAct_handleV t hwild j))]
    exact ⟨rfl, rfl⟩
  rw [(heisEvalZ_prodList_jetZero ⇑t x y E E₂ hmem).2, List.map_map, Fin.sum_univ_def]
  congr 1
  refine List.map_congr_left fun j _ => ?_
  show (heisEvalZ ⇑t x y E E₂ (.comm (.gen (handleU j)) (.gen (handleV j)))).z = _
  rw [heisEvalZ_comm, heisEvalZ_gen, heisEvalZ_gen,
    heisCommR_of_trivial _ _ (mem_trivAct.mp (LSq.trivAct_handleU t hwild j))
      (mem_trivAct.mp (LSq.trivAct_handleV t hwild j))]

/-- The handle tail's denotation, uniformly in `h`.  ⚠ `handleTail 0 = []` — the `n = 1` tree has
no handle node at all (WL-a authoring rule 2), so every induction on `h` needs this `cases`
split; `handlesW 0 = .one` makes the two branches agree. -/
theorem heisEvalZ_lSqHandleTail :
    ((handleTail h).map (heisEvalZ ⇑t x y E E₂)).prod = heisEvalZ ⇑t x y E E₂ (handlesW h) := by
  cases h with
  | zero => rw [handleTail, List.map_nil, List.prod_nil, handlesW_zero, heisEvalZ_one]
  | succ k => rw [handleTail, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

/-- **The `L_sq` second-order (Stokes) row, unramified class, exact in the resolver**: the
central coordinate of the word's `heisEvalZ`-denotation at any marking whose wild letters and
`τ` act trivially, with `E ω₂ = e`.

Block reading: the `x₀`-block `(σ,x₀)`-cross ⊕ `x₀`-diagonal ⊕ the `ω₂`-boundary with its `e`-
and `C(e,2)`-sensitivities ⊕ the **`x₁`-diagonal** ⊕ the **`σ₂`-operator block** ⊕ the `h`
identity-operator hyperbolic planes.  The last two are new relative to the compact-`N` row and
are exactly the pieces WL-b's first-order Fox row provably cannot see. -/
theorem heisZ_lSq_unram (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (lSqW h)).z
      = (y .sigma (x (coreLetter h 0)) + y (coreLetter h 0) (x .sigma)
          + y (coreLetter h 0) (x (coreLetter h 0)))
        + (e • y (coreLetter h 0) (x .tau)
            + (e.choose 2) • ((y (coreLetter h 0) + y .tau)
                (x (coreLetter h 0) + x .tau))
            + e • y (coreLetter h 0) (t.σ • (x (coreLetter h 0) + x .tau)))
        + y (coreLetter h 1) (x (coreLetter h 1))
        + (y (coreLetter h 1) ((t.σ ^ E omega2)⁻¹ • x (coreLetter h 1))
            + y (coreLetter h 1) ((t.σ ^ E omega2) • x (coreLetter h 1)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hHmem := heisF_lSqHandles_mem t x y E E₂ hwild
  have hHz := heisF_lSqHandles_z t x y E E₂ hwild
  rw [lSqW, heisEvalZ_prodList, List.map_append, List.prod_append,
    heisEvalZ_lSqHandleTail t x y E E₂]
  simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  set Q1 := heisEvalZ ⇑t x y E E₂
    (.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma))) with hQ1
  set Q2 := heisEvalZ ⇑t x y E E₂
    (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
    with hQ2
  set Q3 := heisEvalZ ⇑t x y E E₂ (.zpow (.gen (coreLetter h 1)) 2) with hQ3
  set Q4 := heisEvalZ ⇑t x y E E₂
    (.comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) sigma2W)) with hQ4
  set Q5 := heisEvalZ ⇑t x y E E₂ (handlesW h) with hQ5
  have e1 := heisF_lSqInvConj t x y E E₂ hwild
  have e2 := heisF_lSqOmegaBlock t x y E E₂ hA₂ hwild hτ hE
  have e3 := heisF_lSqSquare t x y E E₂ hA₂ hwild
  have e4 := heisF_lSqComm t x y E E₂ hwild
  have h3jz : Q3 ∈ heisJetZero A C := by rw [hQ3, e3]; exact ⟨rfl, rfl⟩
  have h4jz : Q4 ∈ heisJetZero A C := by rw [hQ4, e4]; exact ⟨rfl, rfl⟩
  have h34jz : Q3 * Q4 ∈ heisJetZero A C := mul_mem h3jz h4jz
  have h234a : (Q2 * (Q3 * Q4)).a = Q2.a := by
    rw [HeisLift.mul_a, h34jz.1, smul_zero, add_zero]
  have h234z : (Q2 * (Q3 * Q4)).z = Q2.z + (Q3.z + Q4.z) := by
    rw [heisMul_z_of_a_eq_zero _ _ h34jz.1, heisJetZero_mul_z h3jz]
  have h1g : ∀ v : A, Q1.g • v = v := by
    rw [hQ1, e1]
    exact fun v =>
      mem_trivAct.mp (inv_mem (trivAct_conjR (LSq.trivAct_coreLetter t hwild 0) t.σ)) v
  have hcore : (Q1 * (Q2 * (Q3 * Q4))).z
      = Q1.z + (Q2.z + (Q3.z + Q4.z)) + Q1.l Q2.a := by
    rw [HeisLift.mul_z, h234z, h234a, h1g]
  rw [heisMul_z_of_a_eq_zero _ _ hHmem.1, hcore, hQ1, hQ2, hQ3, hQ4, hQ5, e1, e2, e3, e4,
    hHz]
  dsimp only
  rw [ElemDual.neg_apply, ElemDual.smul_apply, inv_inv, CharTwo.neg_eq, smul_comm, map_nsmul]
  abel

/-- **The certificate form at the honest resolver class** `e ≡ 1 (mod 4)` — the class the genuine
`ω₂` inhabits on every finite `2`-group target.  The `x₀`-block collapses to
`y_σ(a₀) + y₀(a_σ + (1+S)(a₀ + a_τ))` — the second-order shadow of WL-b's `S⁻¹ + P` block on
the `x₀` column — and the `x₁`-block keeps its diagonal and its `σ₂`-operator term. -/
theorem heisZ_lSq_res_one (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (lSqW h)).z
      = y .sigma (x (coreLetter h 0))
        + y (coreLetter h 0)
            (x .sigma + ((x (coreLetter h 0) + x .tau) + t.σ • (x (coreLetter h 0) + x .tau)))
        + y (coreLetter h 1) (x (coreLetter h 1))
        + (y (coreLetter h 1) ((t.σ ^ E omega2)⁻¹ • x (coreLetter h 1))
            + y (coreLetter h 1) ((t.σ ^ E omega2) • x (coreLetter h 1)))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_lSq_unram t x y E E₂ hA₂ hwild hτ hE,
    nsmul_zmod2_odd (odd_of_mod_four_eq_one he), nsmul_zmod2_odd (odd_of_mod_four_eq_one he),
    nsmul_zmod2_even (choose_two_even_of_mod_four he)]
  simp only [map_add]
  abel

/-- **The scalar (split) collapse**: with `σ` acting trivially too, the `(1+S)`-block dies and the
`σ₂`-block dies as well (`S₂ = 1`, so `S₂ + S₂⁻¹ = 0` in characteristic two).  What is left is the
`(σ,x₀)` cross, the `x₁` diagonal and the `h` planes — **the `⟨1⟩ ⊥ H^{⊥(h+1)}` Gram of §2, read
off the word instead of off the relator fibre.** -/
theorem heisZ_lSq_scalar (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    (hσ : ∀ v : A, t.σ • v = v) {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    (heisEvalZ ⇑t x y E E₂ (lSqW h)).z
      = y .sigma (x (coreLetter h 0)) + y (coreLetter h 0) (x .sigma)
        + y (coreLetter h 1) (x (coreLetter h 1))
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  have hσn : ∀ (n : ℕ) (v : A), (t.σ ^ n) • v = v := by
    intro n
    induction n with
    | zero => intro v; rw [pow_zero, one_smul]
    | succ n ih => intro v; rw [pow_succ, mul_smul, hσ, ih]
  have hσz : ∀ (k : ℤ) (v : A), (t.σ ^ k) • v = v := by
    intro k v
    cases k with
    | ofNat n => rw [Int.ofNat_eq_coe, zpow_natCast]; exact hσn n v
    | negSucc n => rw [zpow_negSucc, inv_smul_eq_iff]; exact (hσn (n + 1) v).symm
  rw [heisZ_lSq_res_one t x y E E₂ hA₂ hwild hτ hE he, hσ, hσz, ← zpow_neg, hσz,
    show (x (coreLetter h 0) + x .tau) + (x (coreLetter h 0) + x .tau) = 0 from hA₂ _,
    add_zero, CharTwo.add_self_eq_zero, add_zero]

/-- The `L_sq` denotation splits off its handle tail, uniformly in `h` and generically in the
target — the `PWord.evalZ` form of `heisEvalZ_lSqHandleTail`, with the same `cases h` split. -/
theorem evalZ_lSqW {G : Type*} [Group G] (μ : Generator (2 * h + 1) → G)
    (E' : Zhat → ℤ) (E₂' : ℤ_[2] → ℤ) :
    PWord.evalZ μ E' E₂' (lSqW h)
      = ((lSqCore h).map (PWord.evalZ μ E' E₂')).prod * PWord.evalZ μ E' E₂' (handlesW h) := by
  rw [lSqW, PWord.evalZ_prodList, List.map_append, List.prod_append]
  congr 1
  cases h with
  | zero => rw [handleTail, List.map_nil, List.prod_nil, handlesW_zero, PWord.evalZ_one]
  | succ k =>
    rw [handleTail, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]

end StokesRows

/-! ## §4 The resolved relator family, the endpoint condition and the duality payload

The two-relator family of `⟨σ, τ, x₀, …, x_{2h+1} ∣ τ^σ(τ^{q_K})⁻¹, R^{sq}_{L,n}⟩`, resolved at
the constant integer representative `e` of `ω₂`, in WW2's Jacobian row order (tame first, wild
second — WL-b's convention).

`lSq_isStokesEndpoint` proves display (40)'s endpoint condition for **all** `h`, every even `q`
and every odd `e`: the traced per-letter exponents are `1 − q + e` on `τ`, `−1 − 3e` on `x₀` and
`2` on `x₁`, all even; `σ` and the handle letters carry `0`.  As in WN0-c this is a general
theorem, not a per-instance `decide`. -/

section Family

variable {h q e : ℕ}

/-- **The resolved `L_sq` relator family**. -/
noncomputable def lSqFam (h q e : ℕ) : Fin 2 → FreeGroup (Generator (2 * h + 1)) :=
  ![heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 * h + 1) q),
    heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h)]

@[simp] theorem lSqFam_zero :
    lSqFam h q e 0
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 * h + 1) q) := rfl

@[simp] theorem lSqFam_one :
    lSqFam h q e 1 = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h) := rfl

/-- The handle block's resolved word has trivial mod-2 exponent vector (commutators). -/
theorem heisEps_lSqHandles (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 * h + 1)) :
    heisEps i (PWord.evalZ FreeGroup.of E E₂ (handlesW h)) = 1 := by
  rw [handlesW, PWord.evalZ_prodList, map_list_prod]
  refine List.prod_eq_one ?_
  intro m hm
  simp only [List.map_map, List.mem_map] at hm
  obtain ⟨j, -, rfl⟩ := hm
  show heisEps i (PWord.evalZ FreeGroup.of _ _
    (.comm (.gen (handleU j)) (.gen (handleV j)))) = 1
  rw [PWord.evalZ_comm]
  exact monoidHom_commR_eq_one _ _ _

/-- **The endpoint condition holds at every `L_sq` instance** (any `h`, `q` even, `e` odd). -/
theorem lSq_isStokesEndpoint (hq : Even q) (he : Odd e) : IsStokesEndpoint (lSqFam h q e) := by
  intro i
  rw [Fin.sum_univ_two, lSqFam_zero, lSqFam_one]
  have htame : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
      (tameRelW (2 * h + 1) q))
      = heisEps i (FreeGroup.of Generator.tau)
        * (heisEps i (FreeGroup.of Generator.tau) ^ (q : ℤ))⁻¹ := by
    rw [tameRelW, heisToFree, PWord.evalZ_mul, PWord.evalZ_conj, PWord.evalZ_inv,
      PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, map_mul, map_conjR,
      conjR_eq_self_of_comm, map_inv, map_zpow]
  have hwild : heisEps i (heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h))
      = (heisEps i (FreeGroup.of (coreLetter h 0)))⁻¹
        * ((heisEps i (FreeGroup.of (coreLetter h 0)) ^ (-3 : ℤ)
            * heisEps i (FreeGroup.of Generator.tau)) ^ (e : ℤ))
        * (heisEps i (FreeGroup.of (coreLetter h 1)) ^ (2 : ℤ)) := by
    rw [heisToFree, evalZ_lSqW]
    simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
    rw [map_mul, heisEps_lSqHandles, mul_one, map_mul, map_mul, map_mul,
      PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, map_inv,
      map_conjR, conjR_eq_self_of_comm, PWord.omega2Pow, PWord.evalZ_profPow, map_zpow,
      PWord.prodList_cons, PWord.prodList_cons, PWord.prodList_nil, PWord.evalZ_mul,
      PWord.evalZ_mul, PWord.evalZ_zpow, PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one,
      mul_one, map_mul, map_zpow, PWord.evalZ_zpow, PWord.evalZ_gen, map_zpow,
      PWord.evalZ_comm, monoidHom_commR_eq_one, mul_one]
    rw [mul_assoc]
  rw [htame, hwild]
  simp only [heisEps_of, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd, zsmul_eq_mul]
  have hqz : ((q : ℤ) : ZMod 2) = 0 := by
    rw [Int.cast_natCast]; exact natCast_zmod2_even hq
  have hez : ((e : ℤ) : ZMod 2) = 1 := by
    rw [Int.cast_natCast]; exact natCast_zmod2_odd he
  rw [hqz, hez]
  push_cast
  ring_nf
  simp [show (2 : ZMod 2) = 0 from by decide, show (4 : ZMod 2) = 0 from by decide]

end Family

/-! ### The Stokes duality payload -/

section Duality

universe u

variable {C : Type*} [Group C]

/-- **Packet Lem 5.1 at the `L_sq` family**: WW3's `stokesDuality_of_simple` engine instantiated,
with the relator hypotheses converted through `lift_heisToFree_eq_one_iff` and the endpoint
condition discharged by `lSq_isStokesEndpoint`.  Per-simple-module duality stays the hypothesis
slot it is in the frozen `ℚ₂` chain (gate-F / AS-lane discharge). -/
theorem lSq_stokesDuality {h q e : ℕ} [Finite C] (t : Marking (2 * h + 1) C)
    (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 * h + 1) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h) = 1)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (lSqFam h q e) V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality ⇑t (lSqFam h q e) A := by
  refine stokesDuality_of_simple ⇑t (lSqFam h q e) ?_ (lSq_isStokesEndpoint hq he) hsimp A hA₂
  intro k
  fin_cases k
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrt
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrw

/-- **The traced Stokes pairing of the family** is the sum of the two second-order values — the
bridge between `stokesGram` entries and the closed forms `heisZ_tameRelW_unram` (WN0-c's row,
cited: it is word-independent, and it is where `q_K` enters at second order) and
`heisZ_lSq_unram`. -/
theorem heisEta1_lSqFam_apply {h q e : ℕ} {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
    (y : Generator (2 * h + 1) → ElemDual A) :
    heisEta1 ⇑t (lSqFam h q e) x y
      = (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
          (tameRelW (2 * h + 1) q)).z
        + (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (lSqW h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, lSqFam_zero, lSqFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end Duality

/-! ## §5 The scalar certificate: the `n = 1` Gram matrices, by kernel `decide`

The cup–Bockstein comparison matrix (`stokesGram`) of the `L_sq` family at `h = 0`, `q_K = 2`, on
the scalar module `A = 𝔽₂` (trivial action), at the standard letter basis in the packet column
order `σ, τ, x₀, x₁`; rows index the primal basis vector, columns the dual one.

Two pins, differing **only** in the resolver class of `ω₂`:

* `e = 1` — the honest class for a `2`-group target.  Bockstein diagonals at `τ` (tame,
  `C(q_K,2)` odd at `q_K = 2`) and at **`x₁`** (wild, `C(2,2) = 1`); cup blocks `(σ,τ)` and
  `(σ,x₀)`.  Restricted to the wild-plus-`σ` letters this is `SqCore.sqCore_cupGram`'s
  `[[0,1,0],[1,0,0],[0,0,1]]` — `⟨1⟩ ⊥ H`, §2's normal form at `h = 0`.
* `e = 3` — exactly the `{τ, x₀}²`-block moves, the `C(e,2)`-block of `heisZ_lSq_unram` switching
  on.  The pair makes ticket S1.T's "the lift level is 4, not 2" a kernel-checked matrix
  statement on `L_sq`'s own column (WN0-c's twin moves `{τ, x₂}²`).

Note where the `q_K`-sensitivity sits: the `τ`-diagonal is `C(q_K,2) mod 2`, odd **iff**
`q_K ≡ 2 (mod 4)`, i.e. iff `q_K = 2`.  At `q_K = 4` that entry vanishes.  WL-b proved the *wild*
Fox row cannot see `q_K` at all; at second order the sensitivity reappears, but still only
through the (word-independent) tame row. -/

section ScalarGram

/-- The trivial action for the scalar pins (WW3's `local instance` idiom — not exported). -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The all-trivial (scalar/split) marking of the `n = 1` `L_sq` alphabet. -/
def lSqScalarMark : Marking 1 (Multiplicative (ZMod 2)) := Marking.ofLetters 1 1 ![1, 1]

/-- The packet column order `σ, τ, x₀, x₁`. -/
def lSqScalarLetter : Fin 4 → Generator 1 := ![.sigma, .tau, .wild 0, .wild 1]

/-- The standard primal basis: a unit offset on one letter. -/
def lSqScalarX (p : Fin 4) : Generator 1 → ZMod 2 :=
  fun g => if g = lSqScalarLetter p then 1 else 0

/-- The standard dual basis: the identity functional on one letter. -/
noncomputable def lSqScalarY (p : Fin 4) : Generator 1 → ElemDual (ZMod 2) :=
  fun g => if g = lSqScalarLetter p then (AddMonoidHom.id (ZMod 2) : ElemDual (ZMod 2)) else 0

/-- **The `L_sq` scalar Gram at the honest resolver class** (`e = 1`, `q_K = 2`). -/
theorem lSq_scalarGram :
    stokesGram ⇑lSqScalarMark (lSqFam 0 2 1) lSqScalarX lSqScalarY
      = !![0,1,1,0; 1,1,0,0; 1,0,0,0; 0,0,0,1] := by
  decide +kernel

/-- **The `e = 3` twin**: the `{τ, x₀}²`-block moves with the resolver class. -/
theorem lSq_scalarGram_three :
    stokesGram ⇑lSqScalarMark (lSqFam 0 2 3) lSqScalarX lSqScalarY
      = !![0,1,1,0; 1,0,1,0; 1,1,1,0; 0,0,0,1] := by
  decide +kernel

end ScalarGram

/-! ## §6 The Hessian certificate: the word connected to the rank-3 core's endpoint

WW4 deliberately left `L_sq` out of its worked rows ("rank-3 core, not a plus form"), so this
section builds the connection.  The route is WW4's own: `hessRelZ`/`hessEvalZ` at the κ⁰-cocycle
`kappa0Cocycle dat hdat` on `V ⋊ C`, at a graph-type marking (`σ, τ` on the κ-free `C`-line, wild
letters on the Heisenberg slice).

**The endpoint is the Wall doubling, not a plus form.**  At the `x₁`-supported normal form
(`v (lSqIdx0 h) = 0` — the shape WL-b's Fox certificate reaches, and the frozen
`lemma_5_13_ramified_R`'s `(0,0,0,d)`) the evaluated Hessian of the whole degree-`n` word is

```
q(c₁) + b_q(c₁, S₂⁻¹ c₁) + Σ_j b_q(d_j, e_j),        S₂ = s^{E ω₂},
```

and at `h = 0` this is **`qDouble q U`** on the nose (`GQ2/QuadraticFp2.lean:96`, the paper's
eq. (83)) with `U = S₂⁻¹`.  That identification is the whole point: `qDouble` is the
presentation-independent object the frozen `Γ_R` endgame is written against (`QZeroR = q(d) +
b_q(d, U⁻¹d)`, `GQ2/Roe/Gauss.lean:71`, whose polar operator is `1 + U + U⁻¹`), so the
`QuadraticFp2` + `SectionSix` + `GaussSigns` layer applies to this row **by citation** — see
`lSq_endpoint_nonsingular`/`lSq_endpoint_arf`, which are one-line consequences of `lemma_6_6`.
This is wl-recon §4.1's "consume, don't re-derive", executed.

Unlike the compact-`N` row the conjugated wild letter here carries a **live** slot, so the
κ⁰-consumption is larger: the slice-conjugation law `hessSlice_conj_line` uses `m`, the
equivariant-lift correction, not only `f_diag`/`f_polar`.  All of `m`'s clauses are `q`-blind, so
the endpoint value is still twist-immune; the *calculus* is not. -/

section Hessian

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- The wild-letter slot `x₀` of the `L_sq` alphabet. -/
def lSqIdx0 (h : ℕ) : Fin (2 * h + 1 + 1) := ⟨0, by omega⟩

/-- The wild-letter slot `x₁` of the `L_sq` alphabet — the one the normal form is supported on. -/
def lSqIdx1 (h : ℕ) : Fin (2 * h + 1 + 1) := ⟨1, by omega⟩

/-- The first handle-letter slot, matching `Words.LSq.handleU`. -/
def lSqIdxU {h : ℕ} (j : Fin h) : Fin (2 * h + 1 + 1) :=
  ⟨2 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- The second handle-letter slot, matching `Words.LSq.handleV`. -/
def lSqIdxV {h : ℕ} (j : Fin h) : Fin (2 * h + 1 + 1) :=
  ⟨3 + 2 * (j : ℕ), by have := j.isLt; omega⟩

/-- **The graph-type κ⁰-marking of the `L_sq` alphabet**: `σ ↦ ((0,s))`, `τ ↦ ((0,u))` on the
`C`-line, wild letter `x_i` on the Heisenberg slice at offset `v i`. -/
def lSqHessMark {h : ℕ} (s u : C) (v : Fin (2 * h + 1 + 1) → V) :
    Generator (2 * h + 1) → SemiProd C V
  | .sigma => ((0 : V), s)
  | .tau => ((0 : V), u)
  | .wild i => (v i, (1 : C))

/-- **The slice-conjugation law**: conjugating a Heisenberg slice by a `C`-line element twists the
offset by the inverse and charges the fibre by the equivariant-lift correction `m`.  This is the
`L_sq`-specific piece of κ⁰-calculus that the compact-`N` row never needed (there the conjugated
letter's slot was zero). -/
theorem hessSlice_conj_line (d : V) (g : C) :
    conjR (hessSlice dat hdat d 0) (hessLine dat hdat g)
      = hessSlice dat hdat (g⁻¹ • d) (dat.m g⁻¹ d) := by
  have hinv : (hessLine dat hdat g)⁻¹ = hessLine dat hdat g⁻¹ := by
    rw [show hessLine dat hdat g = hessLineHom dat hdat g from rfl,
      show hessLine dat hdat g⁻¹ = hessLineHom dat hdat g⁻¹ from rfl, ← map_inv]
  rw [conjR, hinv]
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show (0 : V) + g⁻¹ • d + (g⁻¹ * 1) • (0 : V) = g⁻¹ • d
    rw [smul_zero, add_zero, zero_add]
  · show g⁻¹ * 1 * g = 1
    rw [mul_one, inv_mul_cancel]
  · show (0 : ZMod 2) + 0 + (dat.f 0 (g⁻¹ • d) + dat.m g⁻¹ d) + 0
        + (dat.f ((0 : V) + g⁻¹ • d) ((g⁻¹ * 1) • (0 : V)) + dat.m (g⁻¹ * 1) 0)
      = dat.m g⁻¹ d
    rw [hdat.f_zero_left, smul_zero, hdat.f_zero_right, factorSet_m_zero dat hdat]
    simp only [zero_add, add_zero]

/-- The handle tail evaluates to the central inclusion of `Σ_j b_q(d_j, e_j)`. -/
theorem hess_lSqHandles_eval {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (v : Fin (2 * h + 1 + 1) → V) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂ (handlesW h)
      = WordCoh.CentExt.incl _ (∑ j, polar q (v (lSqIdxU j)) (v (lSqIdxV j))) := by
  rw [handlesW, PWord.evalZ_prodList, List.map_map]
  have hcong : (List.finRange h).map
        (PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
          ∘ fun j => PWord.comm (.gen (handleU j)) (.gen (handleV j)))
      = (List.finRange h).map fun j =>
          WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (polar q (v (lSqIdxU j)) (v (lSqIdxV j))) := by
    refine List.map_congr_left fun j _ => ?_
    show PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
        (.comm (.gen (handleU j)) (.gen (handleV j))) = _
    rw [PWord.evalZ_comm, PWord.evalZ_gen, PWord.evalZ_gen,
      show WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) (handleU j)
        = hessSlice dat hdat (v (lSqIdxU j)) 0 from rfl,
      show WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) (handleV j)
        = hessSlice dat hdat (v (lSqIdxV j)) 0 from rfl,
      hessSlice_commR dat hdat hV2]
  rw [hcong,
    show ((List.finRange h).map fun j => WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (polar q (v (lSqIdxU j)) (v (lSqIdxV j))))
      = ((List.finRange h).map fun j => polar q (v (lSqIdxU j)) (v (lSqIdxV j))).map
          (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)) from List.map_map.symm,
    centExt_incl_list_prod, ← Fin.sum_univ_def]

/-- **The word-side Hessian equation, general `h`, every resolver** (packet Def. 9.1(6) at freeze
row 1): at the `x₁`-supported normal form the evaluated class-two value of the frozen `L_sq` word
is the **Wall doubling** of `q` by the `σ₂`-operator, plus the handle planes. -/
theorem hessRelZ_lSq {h : ℕ} (hV2 : ∀ v : V, v + v = 0) (s u : C)
    (v : Fin (2 * h + 1 + 1) → V) (hv0 : v (lSqIdx0 h) = 0) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hessRelZ (lSqHessMark s u v) (kappa0Cocycle dat hdat) E E₂ (lSqW h)
      = q (v (lSqIdx1 h))
        + polar q (v (lSqIdx1 h)) ((s ^ E omega2)⁻¹ • v (lSqIdx1 h))
        + ∑ j, polar q (v (lSqIdxU j)) (v (lSqIdxV j)) := by
  have hx0 : WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) (coreLetter h 0) = 1 := by
    show hessSlice dat hdat (v (lSqIdx0 h)) 0 = 1
    rw [hv0]; rfl
  have hx1 : WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) (coreLetter h 1)
      = hessSlice dat hdat (v (lSqIdx1 h)) 0 := rfl
  have hsig : WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) Generator.sigma
      = hessLineHom dat hdat s := rfl
  rw [hessRelZ, hessEvalZ, evalZ_lSqW]
  simp only [lSqCore, List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  have e1 : PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
      (.inv (.conj (.gen (coreLetter h 0)) (.gen .sigma))) = 1 := by
    rw [PWord.evalZ_inv, PWord.evalZ_conj, PWord.evalZ_gen, PWord.evalZ_gen, hx0, one_conjR,
      inv_one]
  have e2 : PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
      (PWord.omega2Pow (PWord.prodList [.zpow (.gen (coreLetter h 0)) (-3), .gen .tau]))
      = hessLine dat hdat (u ^ E omega2) := by
    rw [PWord.omega2Pow, PWord.evalZ_profPow, PWord.prodList_cons, PWord.prodList_cons,
      PWord.prodList_nil, PWord.evalZ_mul, PWord.evalZ_mul, PWord.evalZ_zpow,
      PWord.evalZ_gen, PWord.evalZ_gen, PWord.evalZ_one, mul_one, hx0, one_zpow, one_mul,
      show WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat) Generator.tau
        = hessLineHom dat hdat u from rfl, ← map_zpow]
    rfl
  have e3 : PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
      (.zpow (.gen (coreLetter h 1)) 2)
      = WordCoh.CentExt.incl _ (q (v (lSqIdx1 h))) := by
    rw [PWord.evalZ_zpow, PWord.evalZ_gen, hx1, Words.LSq.zpow_two, sq]
    exact hessSq_of_fibre dat hdat hV2 _ rfl
  have e4 : PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂
      (.comm (.gen (coreLetter h 1)) (.conj (.gen (coreLetter h 1)) sigma2W))
      = WordCoh.CentExt.incl _
          (polar q (v (lSqIdx1 h)) ((s ^ E omega2)⁻¹ • v (lSqIdx1 h))) := by
    rw [PWord.evalZ_comm, PWord.evalZ_conj, PWord.evalZ_gen, hx1,
      show PWord.evalZ (WordCoh.lift (lSqHessMark s u v) (kappa0Cocycle dat hdat)) E E₂ sigma2W
        = hessLine dat hdat (s ^ E omega2) from by
          rw [sigma2W, PWord.omega2Pow, PWord.evalZ_profPow, PWord.evalZ_gen, hsig,
            ← map_zpow]
          rfl,
      hessSlice_conj_line dat hdat, hessSlice_commR dat hdat hV2]
  rw [e1, e2, e3, e4, hess_lSqHandles_eval dat hdat hV2 s u v E E₂, one_mul,
    centExt_incl_mul, mul_assoc, centExt_incl_mul, WordCoh.CentExt.mul_fib, hessLine_fib,
    WordCoh.CentExt.incl_fib,
    show (kappa0Cocycle dat hdat).κ
        (WordCoh.CentExt.base (hessLine dat hdat (u ^ E omega2)))
        (WordCoh.CentExt.base (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
          (q (v (lSqIdx1 h))
            + polar q (v (lSqIdx1 h)) ((s ^ E omega2)⁻¹ • v (lSqIdx1 h))
            + ∑ j, polar q (v (lSqIdxU j)) (v (lSqIdxV j))))) = 0 from
      (kappa0Cocycle dat hdat).κ_one_right _,
    zero_add, add_zero]

/-- **The `h = 0` word-side equation IS the Wall doubling** `qDouble q U` at `U = S₂⁻¹` — the
frozen `Γ_R` endpoint `QZeroR` (`GQ2/Roe/Gauss.lean:71`) in campaign vocabulary.  This is the
identification that lets the presentation-independent `SectionSix`/`GaussSigns` layer be *cited*
for this row rather than rebuilt. -/
theorem hessRelZ_lSq_qDouble (hV2 : ∀ v : V, v + v = 0) (s u : C) (c₁ : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    hessRelZ (lSqHessMark s u ![0, c₁]) (kappa0Cocycle dat hdat) E E₂ (lSqW 0)
      = qDouble q (fun w => (s ^ E omega2)⁻¹ • w) c₁ := by
  rw [hessRelZ_lSq (h := 0) dat hdat hV2 s u ![0, c₁] rfl E E₂, Fin.sum_univ_zero, add_zero]
  rfl

/-- The word's evaluated Hessian, as a function of the `x₁`-offset, **is** `qDouble q U`. -/
theorem lSq_word_eq_qDouble (hV2 : ∀ v : V, v + v = 0) (s u : C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    (fun c₁ : V => hessRelZ (lSqHessMark s u ![0, c₁]) (kappa0Cocycle dat hdat) E E₂ (lSqW 0))
      = qDouble q (fun w => (s ^ E omega2)⁻¹ • w) :=
  funext fun c₁ => hessRelZ_lSq_qDouble dat hdat hV2 s u c₁ E E₂

end Hessian

/-! ## §7 Handle stability at second order

WL-b stated first-order handle stability three ways, the sharpest being an `AddMonoidHom`
factorization through `coreRestrict h`.  At second order the statement cannot be a factorization —
the handle planes are a genuine new summand — so it is an **exact decomposition**: the degree-`n`
row is the `n = 1` row, read at the core-restricted data, **plus** `h` identity-operator
hyperbolic planes.  WL-b's `coreEmbed`/`coreMarking`/`coreRestrict` kit carries the statement
unchanged; `coreRestrict h (ElemDual A)` transports the dual offsets. -/

section HandleStability

variable {h : ℕ} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (t : Marking (2 * h + 1) C) (x : Generator (2 * h + 1) → A)
  (y : Generator (2 * h + 1) → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

@[simp] theorem coreRestrict_coreLetter {V : Type*} [AddCommGroup V]
    (v : Generator (2 * h + 1) → V) (i : Fin 2) :
    LSq.coreRestrict h V v (coreLetter 0 i) = v (coreLetter h i) := rfl

@[simp] theorem coreRestrict_sigma {V : Type*} [AddCommGroup V]
    (v : Generator (2 * h + 1) → V) : LSq.coreRestrict h V v .sigma = v .sigma := rfl

@[simp] theorem coreRestrict_tau {V : Type*} [AddCommGroup V]
    (v : Generator (2 * h + 1) → V) : LSq.coreRestrict h V v .tau = v .tau := rfl

/-- **Handle stability at second order**: the degree-`n` Stokes row is the `n = 1` row at the
core-restricted data ⊕ the `h` identity-operator hyperbolic planes, as an identity — the
second-order form of WL-b's "`n = 1` certificate ⊕ `2h` zero columns". -/
theorem heisZ_lSq_handle_stable (hA₂ : ∀ a : A, a + a = 0)
    (hwild : ∀ (i : Fin (2 * h + 1 + 1)) (v : A), t.x i • v = v) (hτ : ∀ v : A, t.τ • v = v)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) :
    (heisEvalZ ⇑t x y E E₂ (lSqW h)).z
      = (heisEvalZ ⇑(LSq.coreMarking t) (LSq.coreRestrict h A x)
            (LSq.coreRestrict h (ElemDual A) y) E E₂ (lSqW 0)).z
        + ∑ j, (y (handleU j) (x (handleV j)) + y (handleV j) (x (handleU j))) := by
  rw [heisZ_lSq_unram t x y E E₂ hA₂ hwild hτ hE,
    heisZ_lSq_unram (h := 0) (LSq.coreMarking t) (LSq.coreRestrict h A x)
      (LSq.coreRestrict h (ElemDual A) y) E E₂ hA₂ (LSq.coreMarking_hwild t hwild) hτ hE,
    Fin.sum_univ_zero]
  simp only [coreRestrict_coreLetter, coreRestrict_sigma, coreRestrict_tau,
    LSq.coreMarking_σ, ElemDual.add_apply, map_add, smul_add]
  abel

end HandleStability

/-! ## §8 The determinant/phase consumables — **cited**, not rebuilt

The endpoint of this row is `qDouble q U`, so wl-recon §2.5's "largest genuinely reusable block"
applies verbatim: `GQ2/QuadraticFp2.lean` + `GQ2/SectionSix.lean` + `GQ2/GaussSigns.lean` are
stated over an abstract `q` with no relator and no `Γ`, and `lemma_6_6` is *exactly* the Wall
doubling theorem this row needs.  The three theorems below are the citations, plus the handle
factor, which is a `Phase.lean` computation and is **independent of the head form** — that is the
sense in which `ε(hyp) = +1` and "the handles do not move the sign". -/

section Phase

open GQ2.SectionSix GQ2.QuadraticFp2

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

include hdat in
/-- `q` is `C`-invariant — a *derived* clause of `IsEquivariantFactorSet` (`m_quad` at `v = w`),
not a hypothesis.  This is what feeds `lemma_6_6`'s `hUq`. -/
theorem factorSet_q_invariant (hV2 : ∀ v : V, v + v = 0) (c : C) (v : V) : q (c • v) = q v := by
  have hm := hdat.m_quad c v v
  rw [hV2, factorSet_m_zero dat hdat, hdat.f_diag, hdat.f_diag, zero_add,
    CharTwo.add_self_eq_zero] at hm
  have h2 := CharTwo.add_eq_iff_eq_add.mp hm.symm
  rw [zero_add] at h2
  exact h2

/-- The action of a group element as an additive equivalence — the `U` of the Wall doubling. -/
def smulAddEquiv (g : C) : V ≃+ V where
  toFun v := g • v
  invFun v := g⁻¹ • v
  left_inv v := inv_smul_smul g v
  right_inv v := smul_inv_smul g v
  map_add' u v := smul_add g u v

@[simp] theorem smulAddEquiv_apply (g : C) (v : V) : smulAddEquiv g v = g • v := rfl

include hdat in
/-- **The endpoint is nonsingular and its Arf shifts by the `1 + U` rank** — `lemma_6_6` cited at
`U = σ₂⁻¹`, with `hUq` discharged by `factorSet_q_invariant`.  Nothing about the `L_sq` word is
re-derived here; the whole `SectionSix` layer is presentation-independent. -/
theorem lSq_endpoint_wall [Finite V] (hV2 : ∀ v : V, v + v = 0) (hq2 : IsQuadraticFp2 q)
    (hns : Nonsingular q) (g : C) (hg2 : ∃ n : ℕ, (fun v : V => g • v)^[2 ^ n] = id) :
    Nonsingular (qDouble q (fun w : V => g • w)) ∧
      ∃ k : ℕ, Nat.card (onePlusU (smulAddEquiv (V := V) g)).range = 2 ^ k ∧
        arf (qDouble q (fun w : V => g • w)) = arf q + (k : ZMod 2) :=
  lemma_6_6 q hq2 hV2 hns (smulAddEquiv g) (fun v => factorSet_q_invariant dat hdat hV2 g v) hg2

include hdat in
/-- **The word's evaluated endpoint is nonsingular** — the previous theorem transported along
`lSq_word_eq_qDouble`, i.e. read at the *word* rather than at an abstract form. -/
theorem lSq_word_endpoint_nonsingular [Finite V] (hV2 : ∀ v : V, v + v = 0)
    (hq2 : IsQuadraticFp2 q) (hns : Nonsingular q) (s u : C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hg2 : ∃ n : ℕ, (fun v : V => (s ^ E omega2)⁻¹ • v)^[2 ^ n] = id) :
    Nonsingular (fun c₁ : V =>
      hessRelZ (lSqHessMark s u ![0, c₁]) (kappa0Cocycle dat hdat) E E₂ (lSqW 0)) := by
  rw [lSq_word_eq_qDouble dat hdat hV2 s u E E₂]
  exact (lSq_endpoint_wall dat hdat hV2 hq2 hns _ hg2).1

/-- The zero form is quadratic (the handle-plane head). -/
theorem isQuadraticFp2_zero' : IsQuadraticFp2 (fun _ : V => (0 : ZMod 2)) := by
  refine ⟨rfl, fun u v w => ?_, fun u v w => ?_⟩ <;>
    · show (0 : ZMod 2) + 0 + 0 = (0 + 0 + 0) + (0 + 0 + 0)
      decide

/-- **The handle factor is `2^{d·h}` whatever the head is** — so `h` hyperbolic planes multiply
the Gauss residue by a positive power of two and move neither the sign nor the radical.  This is
S2.4 §5.6's `ε(hyp) = +1` at the level the `L_sq` row needs it, and it is *head-agnostic*: the
`qDouble` head of this row is never unfolded. -/
theorem lSq_handle_form_gaussSum [Module (ZMod 2) V] [Fintype V] (hq2 : IsQuadraticFp2 q)
    (hns : Nonsingular q) {d : ℕ} (hcard : Fintype.card V = 2 ^ d) (Q₀ : V → ZMod 2) (h : ℕ) :
    gaussSum (fun p : V × (Fin h → V × V) =>
        Q₀ p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2)
      = gaussSum Q₀ * 2 ^ (d * h) := by
  have hsplit : (fun p : V × (Fin h → V × V) => Q₀ p.1 + ∑ j, polar q (p.2 j).1 (p.2 j).2)
      = fun p => Q₀ p.1 + ∑ j, plusFormD (fun _ => 0) q (p.2 j) := by
    funext p
    refine congrArg (HAdd.hAdd (Q₀ p.1)) (Finset.sum_congr rfl fun j _ => ?_)
    show polar q (p.2 j).1 (p.2 j).2 = 0 + polar q (p.2 j).1 (p.2 j).2
    rw [zero_add]
  rw [hsplit, gaussSum_prod_add Q₀ (fun w : Fin h → V × V =>
      ∑ j, plusFormD (fun _ => 0) q (w j)), gaussSum_pi_sum,
    gaussSum_plusFormD (isQuadraticFp2_zero' (V := V)) hq2 hns, hcard]
  push_cast
  ring

/-- On a rank-one (`𝔽₂`) coefficient module the handle planes are **invisible**, at every `h` —
WN0-c's `polar_zmod2_eq_zero`, cited: the statement is word-independent. -/
theorem lSq_scalar_handle_term_zero {h : ℕ} (Q : ZMod 2 → ZMod 2) (hQ : IsQuadraticFp2 Q)
    (dvec evec : Fin h → ZMod 2) : ∑ j, polar Q (dvec j) (evec j) = 0 :=
  Finset.sum_eq_zero fun _ _ => GQ2.Dyadic.Certificates.polar_zmod2_eq_zero Q hQ _ _

end Phase

/-! ## §9 Instance pins: `n = 1`, the handle witness, and `q_K = 4` -/

section Pins

open GQ2.QuadraticFp2

/-- The `n = 1` (`h = 0`, `q_K = 2`) endpoint-condition pin at the odd representative `e = 3`,
matching the frozen `Γ_A`/`Γ_R` stress pin. -/
theorem qTwo_isStokesEndpoint : IsStokesEndpoint (lSqFam 0 2 3) :=
  lSq_isStokesEndpoint (by decide) (by decide)

/-- The endpoint condition is **blind to `q_K`**: it holds at `q_K = 4` too.  WL-b proved the
first-order wild row cannot see `q_K`; at second order the `L_sq` word's own contribution is
still `q_K`-blind, and the sensitivity lives entirely in the (word-independent) tame row —
`lSq_scalarGram_qFour` is where it becomes visible. -/
theorem qFour_isStokesEndpoint : IsStokesEndpoint (lSqFam 0 4 1) :=
  lSq_isStokesEndpoint (by decide) (by decide)

section QFourGram

local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- **The `q_K = 4` scalar Gram**: exactly the `τ`-diagonal dies, because `C(4,2) = 6` is even
while `C(2,2) = 1` is odd — `diagCoeff` is `mod 4`-periodic (MC2's rule).  Together with
`lSq_scalarGram` this is the second-order `q_K` discriminator of the lane, and it confirms WL-b's
finding from the other side: the difference is one *tame* entry, and no wild entry moves. -/
theorem lSq_scalarGram_qFour :
    stokesGram ⇑lSqScalarMark (lSqFam 0 4 1) lSqScalarX lSqScalarY
      = !![0,1,1,0; 1,0,0,0; 1,0,0,0; 0,0,0,1] := by
  decide +kernel

end QFourGram

section HandleWitness

/-- The trivial action for the witness (local, non-exporting — WN0-c's `handleDat` cannot be
cited across the file boundary because its own instance is `local`; the datum is restated, not
re-derived). -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2 × ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

/-- The bilinear refinement `f((a,b),(c,d)) = a·d` of the hyperbolic plane `stressQh`. -/
def lSqHandleDat : FactorSet (Multiplicative (ZMod 2)) (ZMod 2 × ZMod 2) where
  f v w := v.1 * w.2
  m _ _ := 0

theorem lSqHandleDat_equivariant : IsEquivariantFactorSet stressQh lSqHandleDat := by
  constructor <;> decide

/-- **The handle plane is visible to the extraspecial evaluation**: at the `h = 1` `L_sq` word,
zero core offsets and the hyperbolic handle pair `((1,0), (0,1))`, the evaluated Hessian is
`b_{q_h}((1,0),(0,1)) = 1 ≠ 0` — while the same tail is invisible at first order (WL-b's zero
handle Fox columns) and on rank-one modules (`lSq_scalar_handle_term_zero`). -/
theorem lSq_stress_handle_visible :
    hessRelZ (lSqHessMark (h := 1) 1 1 ![0, 0, (1, 0), (0, 1)])
        (kappa0Cocycle lSqHandleDat lSqHandleDat_equivariant) (fun _ => 1) (fun _ => 1)
        (lSqW 1)
      = 1 := by
  rw [hessRelZ_lSq (h := 1) lSqHandleDat lSqHandleDat_equivariant (by decide) 1 1
    ![0, 0, (1, 0), (0, 1)] rfl (fun _ => 1) (fun _ => 1)]
  decide

end HandleWitness

end Pins

end GQ2.Dyadic.Certificates.LSqStokes
