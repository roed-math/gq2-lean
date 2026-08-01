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

end StokesRows

end GQ2.Dyadic.Certificates.LSqStokes
