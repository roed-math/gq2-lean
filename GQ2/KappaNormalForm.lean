/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.RegularSummand
import GQ2.InvolutionDatum
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# P-17e5: the κ⁰ normal form on permutation modules and the tame assembly

The analytic heart of the paper's **Lemma 6.3** (κ⁰ base-class existence), own file for the
`kappa0_exists` splice in `GQ2/SectionNine.lean` (which imports this file — hence this file
carries *copies* of the small factor-set assembly lemmas that live in the
`GQ2.SectionNine` namespace; the scoping note `docs/p17e-kappa0-scoping.md` already anticipated
promoting them to a low shared file and deferred it to avoid churn on the co-owned §9 file.
**P-15f2b pass (2026-07-07)**: the generic-in-`V` copies (`datum_*`, `polar_*`,
`isQuadraticFp2_*`, `quadratic_expansion`, `polar_sum_right`) are now **public** — the §6.2
orbit decomposition `GQ2/OrbitDecomp.lean` consumes them; names checked clash-free repo-wide).

## Contents

* `PermW H K` — the permutation module `𝔽₂[H]^K` (the codomain of `lemma_6_11`'s split pair),
  a **reducible** synonym of `Fin K → H → ZMod 2` carrying the blockwise left-translation
  `DistribMulAction H` instance.  ⚠ Because the synonym is reducible, the instance is keyed on
  the raw function type `Fin K → H → ZMod 2` (same `H` in both positions); no other instance
  can currently apply there (`ZMod 2` carries no action of an abstract `H`), and the only
  importer is the §9 layer.
* `quadratic_eq_double_sum` — the expansion of a quadratic map in basis coordinates, in
  ordered-pair form: for any kernel `f₀` with `f₀ p p = Q(e_p)` and
  `f₀ p p' + f₀ p' p = polar Q (e_p) (e_{p'})`, one has `Q F = ∑_{p,p'} F_p F_{p'} f₀(p,p')`.
* `invBlockSquare`/`isEquivariantFactorSet_invBlockDatum` — the **involution correction**
  `E_{n,u}` (paper Lemma 6.2): P-17e3's `invOrbitDatum`, instantiated at `N = ⊥` and
  transported to block `n` of `PermW H K` by `comapHom`/`comap` (no new orientation
  bookkeeping).
* `exists_datum_of_invariant_quadratic` — the **normal form** (paper (75)/(76) + Lemma 6.2,
  assembly): every `H`-invariant quadratic map on `PermW H K` admits an equivariant
  factor-set datum.  Deviation (documented): instead of decomposing into individual orbit
  polynomials `S_j`/`C_{j,k,g}` we build a *single* invariant biadditive refinement from the
  relative-position coordinates `β n m u := polar Q (e_{n,1}) (e_{m,u})` — possible exactly
  off the involution locus, which is corrected by subtracting the `E_{n,u}` first.
  Equivalent to the paper's normal form with far less case machinery.
* `kappa0_exists_tame` — the full assembly over an abstract finite tame-generated group:
  2-torsion derivation from nonsingularity, faithful-image reduction (via
  `DistribMulAction.toAddAut`, no quotient groups), the odd/unramified branch (`t` acts
  trivially ⟹ `t = 1` ⟹ `|Ĥ|` odd by the O₂-linchpin ⟹ averaging), and the ramified branch
  (`lemma_6_11_of_tame_pair` ⟹ split pair ⟹ normal form ⟹ pullback).
  `SectionNine.kappa0_exists` becomes a two-reduction splice of this.

No axioms; `Ax = ∅` (std-3 throughout).
-/

namespace GQ2

open QuadraticFp2
open scoped Classical

/-! ## The permutation module `𝔽₂[H]^K` with the left-translation action -/

/-- The permutation module `𝔽₂[H]^K` — the codomain of `lemma_6_11`'s split pair — as a
**reducible** synonym; the `DistribMulAction H` instance below is the blockwise
left-translation `(h • F) n x = F n (h⁻¹x)` (mirroring `RegRep`'s convention). -/
abbrev PermW (H : Type) (K : ℕ) : Type := Fin K → H → ZMod 2

/-- Blockwise left translation on `𝔽₂[H]^K`.  ⚠ Keyed on the raw function type (see the module
docstring): do not introduce competing actions of `H` on `Fin K → H → ZMod 2`. -/
instance {H : Type} [Group H] {K : ℕ} : DistribMulAction H (PermW H K) where
  smul h F := fun n x => F n (h⁻¹ * x)
  one_smul F := by funext n x; show F n _ = F n x; rw [inv_one, one_mul]
  mul_smul c d F := by funext n x; show F n _ = F n _; rw [mul_inv_rev, mul_assoc]
  smul_zero c := rfl
  smul_add c F G := rfl

theorem PermW.smul_apply {H : Type} [Group H] {K : ℕ} (h : H) (F : PermW H K) (n : Fin K)
    (x : H) : (h • F) n x = F n (h⁻¹ * x) := rfl

section NormalForm

variable {H : Type} [Group H] {K : ℕ}

omit [Group H] in
/-- The coordinate basis of `PermW H K` (the indicator of the coordinate `(n, x)`). -/
noncomputable def permBas (n : Fin K) (x : H) : PermW H K :=
  fun m y => if m = n ∧ y = x then 1 else 0

omit [Group H] in
theorem permBas_apply (n : Fin K) (x : H) (m : Fin K) (y : H) :
    permBas n x m y = if m = n ∧ y = x then (1 : ZMod 2) else 0 := rfl

/-- Left translation carries basis vectors to basis vectors: `h • e_{(n,x)} = e_{(n,hx)}`. -/
theorem permBas_smul (h : H) (n : Fin K) (x : H) :
    h • (permBas n x : PermW H K) = permBas n (h * x) := by
  funext m y
  show (if m = n ∧ h⁻¹ * y = x then (1 : ZMod 2) else 0)
    = if m = n ∧ y = h * x then (1 : ZMod 2) else 0
  rw [inv_mul_eq_iff_eq_mul]

omit [Group H] in
/-- Every `F : PermW H K` is the sum of the basis vectors at its support. -/
theorem permBas_support_decomp [Fintype H] (F : PermW H K) :
    F = ∑ p ∈ Finset.univ.filter (fun p : Fin K × H => F p.1 p.2 = 1), permBas p.1 p.2 := by
  funext m y
  rw [Finset.sum_apply, Finset.sum_apply]
  have hterm : ∀ p : Fin K × H,
      permBas p.1 p.2 m y = if p = (m, y) then (1 : ZMod 2) else 0 := by
    intro p
    rw [permBas_apply]
    have hiff : (m = p.1 ∧ y = p.2) ↔ p = (m, y) := by
      simp [Prod.ext_iff, eq_comm]
    rw [if_congr hiff rfl rfl]
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    Finset.sum_ite_eq' _ (m, y) (fun _ => (1 : ZMod 2))]
  rcases ZMod.eq_zero_or_eq_one (F m y) with h | h <;> simp [h]

/-! ## The expansion of a quadratic map in coordinates (ordered-pair form) -/

/-- The polar form is additive in the second argument over finite sums (with
`polar Q x 0 = 0` from char 2). -/
theorem polar_sum_right {V : Type*} [AddCommGroup V] {Q : V → ZMod 2}
    (hQ : IsQuadraticFp2 Q) {ι : Type*} (v : ι → V) (x : V) (s : Finset ι) :
    polar Q x (∑ i ∈ s, v i) = ∑ i ∈ s, polar Q x (v i) := by
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    show Q (x + 0) + Q x + Q 0 = 0
    rw [add_zero, hQ.map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  | @insert b s' hb IH =>
    rw [Finset.sum_insert hb, hQ.polar_add_right, IH, Finset.sum_insert hb]

/-- **Expansion of a quadratic map over a family, ordered-pair form**: if `f₀` matches `Q` on
the diagonal and symmetrizes to the polar form off it, then
`Q (∑_{i∈s} v i) = ∑_{i,j∈s} f₀ i j`.  (No `Sym2`: the two off-diagonal orders share the
polar value between them.) -/
theorem quadratic_expansion {V : Type*} [AddCommGroup V] {Q : V → ZMod 2}
    (hQ : IsQuadraticFp2 Q) {ι : Type*} (v : ι → V) (f₀ : ι → ι → ZMod 2)
    (hdiag : ∀ i, f₀ i i = Q (v i))
    (hpolar : ∀ i j, i ≠ j → f₀ i j + f₀ j i = polar Q (v i) (v j)) (s : Finset ι) :
    Q (∑ i ∈ s, v i) = ∑ i ∈ s, ∑ j ∈ s, f₀ i j := by
  induction s using Finset.induction_on with
  | empty => simpa using hQ.map_zero
  | @insert a s ha IH =>
    rw [Finset.sum_insert ha]
    have hstep : Q (v a + ∑ i ∈ s, v i)
        = Q (v a) + Q (∑ i ∈ s, v i) + polar Q (v a) (∑ i ∈ s, v i) := by
      simp only [polar]
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    rw [hstep, IH, polar_sum_right hQ]
    have hrow : ∀ i : ι, (∑ j ∈ insert a s, f₀ i j) = f₀ i a + ∑ j ∈ s, f₀ i j :=
      fun i => Finset.sum_insert ha
    rw [Finset.sum_insert ha, hrow a, Finset.sum_congr rfl fun i _ => hrow i,
      Finset.sum_add_distrib, hdiag a]
    have hpol : ∀ i ∈ s, polar Q (v a) (v i) = f₀ a i + f₀ i a := by
      intro i hi
      exact (hpolar a i (fun h => ha (h ▸ hi))).symm
    rw [Finset.sum_congr rfl hpol, Finset.sum_add_distrib]
    ring

omit [Group H] in
/-- **Expansion on the permutation module**: any quadratic `Q` is the full coordinate double
sum against any diagonal/polar-compatible kernel `f₀`. -/
private theorem quadratic_eq_double_sum [Fintype H]
    {Q : PermW H K → ZMod 2} (hQ : IsQuadraticFp2 Q)
    (f₀ : (Fin K × H) → (Fin K × H) → ZMod 2)
    (hdiag : ∀ p, f₀ p p = Q (permBas p.1 p.2))
    (hpolar : ∀ p p', p ≠ p' →
      f₀ p p' + f₀ p' p = polar Q (permBas p.1 p.2) (permBas p'.1 p'.2))
    (F : PermW H K) :
    Q F = ∑ p : Fin K × H, ∑ p' : Fin K × H, F p.1 p.2 * F p'.1 p'.2 * f₀ p p' := by
  have hcoeff : ∀ (c : ZMod 2) (z : ZMod 2), c * z = if c = 1 then z else 0 := by
    intro c z
    rcases ZMod.eq_zero_or_eq_one c with h0 | h1
    · rw [h0, zero_mul, if_neg (by decide)]
    · rw [h1, one_mul, if_pos rfl]
  calc Q F
      = Q (∑ p ∈ Finset.univ.filter (fun p : Fin K × H => F p.1 p.2 = 1), permBas p.1 p.2) := by
        rw [← permBas_support_decomp]
    _ = ∑ p ∈ Finset.univ.filter (fun p : Fin K × H => F p.1 p.2 = 1),
          ∑ p' ∈ Finset.univ.filter (fun p : Fin K × H => F p.1 p.2 = 1), f₀ p p' :=
        quadratic_expansion hQ (fun p : Fin K × H => permBas p.1 p.2) f₀ hdiag hpolar _
    _ = ∑ p : Fin K × H, ∑ p' : Fin K × H, F p.1 p.2 * F p'.1 p'.2 * f₀ p p' := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.sum_filter]
        by_cases hp : F p.1 p.2 = 1
        · rw [if_pos hp]
          refine Finset.sum_congr rfl fun p' _ => ?_
          rw [mul_assoc, hcoeff (F p.1 p.2), if_pos hp, hcoeff (F p'.1 p'.2)]
        · rw [if_neg hp]
          exact (Finset.sum_eq_zero fun p' _ => by
            rw [mul_assoc, hcoeff (F p.1 p.2), if_neg hp]).symm

end NormalForm

/-! ## Private copies of the §9 factor-set assembly layer

These live in `namespace GQ2.SectionNine`, which will import this file for the splice — so we
carry private copies (verbatim proofs).  See the module docstring. -/

section DatumLemmas

variable {C V : Type*} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- Private copy of `SectionNine.isEquivariantFactorSet_of_invariant`. -/
theorem datum_of_invariant {q : V → ZMod 2} {f : V → V → ZMod 2}
    (hcoc : ∀ v w x, f (v + w) x + f v w = f v (w + x) + f w x)
    (hdiag : ∀ v, f v v = q v) (hpolar : ∀ v w, f v w + f w v = polar q v w)
    (h0l : ∀ v, f 0 v = 0) (h0r : ∀ v, f v 0 = 0)
    (hinv : ∀ (c : C) (v w : V), f (c • v) (c • w) = f v w) :
    IsEquivariantFactorSet q (⟨f, fun _ _ => 0⟩ : FactorSet C V) where
  f_cocycle := hcoc
  f_diag := hdiag
  f_polar := hpolar
  f_zero_left := h0l
  f_zero_right := h0r
  m_quad c v w := by
    show (0 : ZMod 2) + 0 + 0 = f (c • v) (c • w) + f v w
    rw [hinv c v w, add_zero, add_zero]
    exact (CharTwo.add_self_eq_zero _).symm
  m_mul c d v := by simp
  m_one _ := rfl

/-- Private copy of `SectionNine.isEquivariantFactorSet_of_biadditive_invariant`. -/
theorem datum_of_biadditive_invariant {q : V → ZMod 2} {f : V → V → ZMod 2}
    (hl : ∀ v v' w, f (v + v') w = f v w + f v' w)
    (hr : ∀ v w w', f v (w + w') = f v w + f v w')
    (hdiag : ∀ v, f v v = q v)
    (hinv : ∀ (c : C) (v w : V), f (c • v) (c • w) = f v w) :
    IsEquivariantFactorSet q (⟨f, fun _ _ => 0⟩ : FactorSet C V) := by
  have h0l : ∀ v, f 0 v = 0 := by
    intro v; have h := hl 0 0 v; rw [add_zero] at h; exact h.trans (CharTwo.add_self_eq_zero _)
  have h0r : ∀ v, f v 0 = 0 := by
    intro v; have h := hr v 0 0; rw [add_zero] at h; exact h.trans (CharTwo.add_self_eq_zero _)
  have hpolar : ∀ v w, f v w + f w v = polar q v w := by
    intro v w
    have h1 := hdiag (v + w)
    rw [hl, hr, hr, hdiag v, hdiag w] at h1
    simp only [polar]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1
  refine datum_of_invariant ?_ hdiag hpolar h0l h0r hinv
  intro v w x; rw [hl v w x, hr v w x]; ring

/-- Private copy of `SectionNine.IsEquivariantFactorSet.add`. -/
theorem datum_add {q q' : V → ZMod 2} {dat dat' : FactorSet C V}
    (h : IsEquivariantFactorSet q dat) (h' : IsEquivariantFactorSet q' dat') :
    IsEquivariantFactorSet (fun v => q v + q' v)
      (⟨fun v w => dat.f v w + dat'.f v w,
        fun c v => dat.m c v + dat'.m c v⟩ : FactorSet C V) where
  f_cocycle v w x := by
    linear_combination (norm := (ring_nf)) h.f_cocycle v w x + h'.f_cocycle v w x
  f_diag v := by
    show dat.f v v + dat'.f v v = q v + q' v
    rw [h.f_diag, h'.f_diag]
  f_polar v w := by
    have e1 := h.f_polar v w; have e2 := h'.f_polar v w
    simp only [polar] at e1 e2 ⊢
    linear_combination (norm := (ring_nf)) e1 + e2
  f_zero_left v := by
    show dat.f 0 v + dat'.f 0 v = 0
    rw [h.f_zero_left, h'.f_zero_left, add_zero]
  f_zero_right v := by
    show dat.f v 0 + dat'.f v 0 = 0
    rw [h.f_zero_right, h'.f_zero_right, add_zero]
  m_quad c v w := by
    linear_combination (norm := (ring_nf)) h.m_quad c v w + h'.m_quad c v w
  m_mul c d v := by
    linear_combination (norm := (ring_nf)) h.m_mul c d v + h'.m_mul c d v
  m_one v := by
    show dat.m 1 v + dat'.m 1 v = 0
    rw [h.m_one, h'.m_one, add_zero]

/-- Private copy of `SectionNine.IsEquivariantFactorSet.comap`. -/
theorem datum_comap {W : Type*} [AddCommGroup W] [DistribMulAction C W]
    {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (i : V →+ W)
    (hi : ∀ (c : C) (v : V), i (c • v) = c • i v) :
    IsEquivariantFactorSet (fun v => q (i v)) (dat.comap i) where
  f_cocycle v w x := by
    show dat.f (i (v + w)) (i x) + dat.f (i v) (i w)
      = dat.f (i v) (i (w + x)) + dat.f (i w) (i x)
    rw [map_add, map_add]; exact hdat.f_cocycle (i v) (i w) (i x)
  f_diag v := hdat.f_diag (i v)
  f_polar v w := by
    show dat.f (i v) (i w) + dat.f (i w) (i v) = polar (fun v => q (i v)) v w
    rw [hdat.f_polar (i v) (i w)]; simp only [polar, map_add]
  f_zero_left v := by
    show dat.f (i 0) (i v) = 0
    rw [map_zero]; exact hdat.f_zero_left (i v)
  f_zero_right v := by
    show dat.f (i v) (i 0) = 0
    rw [map_zero]; exact hdat.f_zero_right (i v)
  m_quad c v w := by
    show dat.m c (i (v + w)) + dat.m c (i v) + dat.m c (i w)
       = dat.f (i (c • v)) (i (c • w)) + dat.f (i v) (i w)
    rw [map_add, hi c v, hi c w]; exact hdat.m_quad c (i v) (i w)
  m_mul c d v := by
    show dat.m (c * d) (i v) = dat.m c (i (d • v)) + dat.m d (i v)
    rw [hi d v]; exact hdat.m_mul c d (i v)
  m_one v := hdat.m_one (i v)

/-- Private copy of `SectionNine.IsEquivariantFactorSet.comapHom`. -/
private theorem datum_comapHom {D : Type*} [Group D] [DistribMulAction D V]
    {q : V → ZMod 2} {dat : FactorSet D V}
    (hdat : IsEquivariantFactorSet q dat) (π : C →* D)
    (hπ : ∀ (c : C) (v : V), c • v = π c • v) :
    IsEquivariantFactorSet q (⟨dat.f, fun c v => dat.m (π c) v⟩ : FactorSet C V) where
  f_cocycle := hdat.f_cocycle
  f_diag := hdat.f_diag
  f_polar := hdat.f_polar
  f_zero_left := hdat.f_zero_left
  f_zero_right := hdat.f_zero_right
  m_quad c v w := by
    show dat.m (π c) (v + w) + dat.m (π c) v + dat.m (π c) w
       = dat.f (c • v) (c • w) + dat.f v w
    rw [hπ c v, hπ c w]; exact hdat.m_quad (π c) v w
  m_mul c d v := by
    show dat.m (π (c * d)) v = dat.m (π c) (d • v) + dat.m (π d) v
    rw [map_mul, hπ d v]; exact hdat.m_mul (π c) (π d) v
  m_one v := by
    show dat.m (π 1) v = 0
    rw [map_one]; exact hdat.m_one v

/-- Private copy of `SectionNine.kappa0_exists_of_split`. -/
private theorem datum_of_split {W : Type*} [AddCommGroup W] [DistribMulAction C W]
    {q : V → ZMod 2} {qW : W → ZMod 2}
    (datW : FactorSet C W) (hdatW : IsEquivariantFactorSet qW datW)
    (i : V →+ W) (hi : ∀ (c : C) (v : V), i (c • v) = c • i v) (hq : ∀ v, qW (i v) = q v) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat := by
  refine ⟨datW.comap i, ?_⟩
  have hpb := datum_comap hdatW i hi
  rwa [show (fun v => qW (i v)) = q from funext hq] at hpb

/-- A datum forces **invariance of its square map** (on a 2-torsion module):
`m_quad` at `(v, v)` collapses to `f(cv, cv) = f(v, v)`. -/
theorem datum_isInvariant {q : V → ZMod 2} {dat : FactorSet C V}
    (hdat : IsEquivariantFactorSet q dat) (h2 : ∀ v : V, v + v = 0) : IsInvariant C q := by
  intro c v
  have hm0 : dat.m c 0 = 0 := by
    have h := hdat.m_quad c 0 0
    rw [add_zero, smul_zero, hdat.f_zero_left, add_zero] at h
    have h2' : dat.m c 0 + dat.m c 0 = 0 := CharTwo.add_self_eq_zero _
    rw [add_assoc, h2', add_zero] at h
    exact h
  have h := hdat.m_quad c v v
  rw [h2 v, hm0, zero_add, CharTwo.add_self_eq_zero (dat.m c v)] at h
  -- h : 0 = f (cv) (cv) + f v v
  have h' : dat.f (c • v) (c • v) = dat.f v v := by
    have h4 := congrArg (fun z => z + dat.f v v) h
    simp only [zero_add] at h4
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero] at h4
    exact h4.symm
  rw [← hdat.f_diag (c • v), ← hdat.f_diag v]
  exact h'

/-- Private copy of `SectionNine.exists_biadditive_refinement`. -/
private theorem exists_biadditive_refinement' {V : Type*} [AddCommGroup V] [Finite V]
    (h2 : ∀ v : V, v + v = 0) (q : V → ZMod 2) (hq : IsQuadraticFp2 q) :
    ∃ f : V → V → ZMod 2, (∀ v v' w : V, f (v + v') w = f v w + f v' w)
      ∧ (∀ v w w' : V, f v (w + w') = f v w + f v w') ∧ (∀ v, f v v = q v) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact h2 v)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hsmul : ∀ (a : ZMod 2) (x : V), q (a • x) = (a * a) • q x := by
    intro a x
    rcases ZMod.eq_zero_or_eq_one a with rfl | rfl
    · simp [hq.map_zero]
    · simp
  have hcomp0 : ∀ x y : V, q (x + y) = q x + q y + polar q x y := by
    intro x y
    simp only [polar]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
  let Bil : LinearMap.BilinForm (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w')))
        (fun v v' => by
          ext w
          simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply,
            LinearMap.add_apply]
          exact hq.polar_add_left v v' w))
  have hBilapp : ∀ v w, Bil v w = polar q v w := fun v w => rfl
  let Qm : QuadraticMap (ZMod 2) V (ZMod 2) :=
    { toFun := q
      toFun_smul := hsmul
      exists_companion' := ⟨Bil, fun x y => by rw [hBilapp]; exact hcomp0 x y⟩ }
  let bm := Module.finBasis (ZMod 2) V
  refine ⟨fun v w => Qm.toBilin bm v w, fun v v' w => ?_, fun v w w' => ?_, fun v => ?_⟩
  · simp only [map_add, LinearMap.add_apply]
  · simp only [map_add]
  · show Qm.toBilin bm v v = q v
    exact DFunLike.congr_fun (QuadraticMap.toQuadraticMap_toBilin Qm bm) v

/-- Private copy of `SectionNine.kappa0_exists_of_odd` (the odd/unramified branch). -/
private theorem datum_of_odd {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    {V : Type*} [AddCommGroup V] [Finite V] [DistribMulAction H V] (h2 : ∀ v : V, v + v = 0)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant H q) :
    ∃ dat : FactorSet H V, IsEquivariantFactorSet q dat := by
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨f₀, hl₀, hr₀, hdiag₀⟩ := exists_biadditive_refinement' h2 q hq
  have hinv' : ∀ (c : H) (x : V), q (c • x) = q x := hinv
  have oddsmul : ∀ x : ZMod 2, Fintype.card H • x = x := by
    intro x
    have hc1 : (Fintype.card H : ZMod 2) = 1 := by
      have hodd' : Odd (Fintype.card H) := by rwa [Nat.card_eq_fintype_card] at hodd
      obtain ⟨k, hk⟩ := hodd'
      rw [hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide]
      ring
    rw [nsmul_eq_mul, hc1, one_mul]
  refine ⟨⟨fun v w => ∑ h : H, f₀ (h • v) (h • w), fun _ _ => 0⟩,
    datum_of_biadditive_invariant ?_ ?_ ?_ ?_⟩
  · intro v v' w
    simp only [smul_add, hl₀]
    exact Finset.sum_add_distrib
  · intro v w w'
    simp only [smul_add, hr₀]
    exact Finset.sum_add_distrib
  · intro v
    have step : ∀ h : H, f₀ (h • v) (h • v) = q v := fun h => (hdiag₀ (h • v)).trans (hinv' h v)
    simp only [step, Finset.sum_const, Finset.card_univ]
    exact oddsmul (q v)
  · intro g v w
    simp only [← mul_smul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => rfl)

/-- A datum with a **biadditive** factor set forces its square map to be quadratic. -/
theorem datum_isQuadratic {q : V → ZMod 2} {dat : FactorSet C V}
    (hdat : IsEquivariantFactorSet q dat)
    (hfl : ∀ v v' w, dat.f (v + v') w = dat.f v w + dat.f v' w)
    (hfr : ∀ v w w', dat.f v (w + w') = dat.f v w + dat.f v w') : IsQuadraticFp2 q where
  map_zero := by
    have h := hdat.f_diag 0
    rw [hdat.f_zero_left] at h
    exact h.symm
  polar_add_left u v w := by
    have h1 := hdat.f_polar (u + v) w
    have h2 := hdat.f_polar u w
    have h3 := hdat.f_polar v w
    rw [hfl, hfr] at h1
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 - h2 - h3
  polar_add_right u v w := by
    have h1 := hdat.f_polar u (v + w)
    have h2 := hdat.f_polar u v
    have h3 := hdat.f_polar u w
    rw [hfl, hfr] at h1
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 - h2 - h3

end DatumLemmas

/-! ## The involution-block correction `E_{n,u}`  (paper Lemma 6.2, transported)

P-17e3's `invOrbitDatum` lives over `G ⧸ N` acting on `RegRep N`.  We instantiate it at
`G := H`, `N := ⊥` and transport along the canonical `H ≃* H ⧸ ⊥` (`comapHom`) and the block
projection `PermW H K →+ RegRep ⊥` (`comap`) — no new orientation bookkeeping.  The package
records the two coordinate facts the normal form consumes: `E` vanishes on basis vectors, and
its polar form is the indicator of the `u`-pairing on block `n`. -/

section InvolutionBlock

variable {H : Type} [Group H] {K : ℕ}

private theorem ite_sq (c : Prop) [Decidable c] :
    (if c then (1 : ZMod 2) else 0) * (if c then (1 : ZMod 2) else 0)
      = if c then (1 : ZMod 2) else 0 := by
  by_cases h : c
  · rw [if_pos h, mul_one]
  · rw [if_neg h, mul_zero]

/-- The per-element core of the involution-block polar computation: for a single coordinate
`z`, the symmetrized product of the two basis indicators against the `u`-shift collapses to the
`u`-pairing indicator on block `n` (paired with the `{z = x, z = x'}` support). Bridge-free —
the `E_{n,u}` proof feeds each coset representative `z = ρ w.out` into this. -/
private theorem permBas_pair_indicator (n m m' : Fin K) (x x' : H) {u : H}
    (hu2 : u * u = 1) (z : H) :
    permBas m x n z * permBas m' x' n (z * u) + permBas m' x' n z * permBas m x n (z * u)
      = if m = n ∧ m' = n ∧ x' = x * u then
          (if z = x then (1 : ZMod 2) else 0) + (if z = x' then (1 : ZMod 2) else 0)
        else 0 := by
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_left hu2
  rw [permBas_apply, permBas_apply, permBas_apply, permBas_apply]
  by_cases hm : m = n
  · by_cases hm' : m' = n
    · subst hm
      subst hm'
      simp only [true_and]
      by_cases hxx' : x' = x * u
      · rw [if_pos hxx']
        have hiff1 : (z * u = x') ↔ (z = x) := by
          constructor
          · intro h
            exact mul_right_cancel (h.trans hxx')
          · intro h
            rw [h, ← hxx']
        have hiff2 : (z * u = x) ↔ (z = x') := by
          constructor
          · intro h
            have h1 : z = x * u⁻¹ := eq_mul_inv_of_mul_eq h
            rw [hu'] at h1
            rw [h1, ← hxx']
          · intro h
            rw [h, hxx', mul_assoc, hu2, mul_one]
        rw [if_congr hiff1 rfl rfl, if_congr hiff2 rfl rfl, ite_sq, ite_sq]
      · rw [if_neg hxx']
        have hc1 : z = x → ¬ z * u = x' := by
          intro h1 h2
          exact hxx' (by rw [← h2, h1])
        have hc2 : z = x' → ¬ z * u = x := by
          intro h1 h2
          exact hxx' (by rw [← h2, mul_assoc, hu2, mul_one, h1])
        by_cases hz1 : z = x
        · rw [if_pos hz1, one_mul, if_neg (hc1 hz1), zero_add]
          by_cases hz2 : z = x'
          · rw [if_pos hz2, one_mul, if_neg (hc2 hz2)]
          · rw [if_neg hz2, zero_mul]
        · rw [if_neg hz1, zero_mul, zero_add]
          by_cases hz2 : z = x'
          · rw [if_pos hz2, one_mul, if_neg (hc2 hz2)]
          · rw [if_neg hz2, zero_mul]
    · have h1 : ¬(n = m' ∧ z * u = x') := fun h => hm' h.1.symm
      have h2 : ¬(n = m' ∧ z = x') := fun h => hm' h.1.symm
      have h3 : ¬(m = n ∧ m' = n ∧ x' = x * u) := fun h => hm' h.2.1
      rw [if_neg h1, if_neg h2, if_neg h3, mul_zero, zero_mul, add_zero]
  · have h1 : ¬(n = m ∧ z = x) := fun h => hm h.1.symm
    have h2 : ¬(n = m ∧ z * u = x) := fun h => hm h.1.symm
    have h3 : ¬(m = n ∧ m' = n ∧ x' = x * u) := fun h => hm h.1
    rw [if_neg h1, if_neg h2, if_neg h3, zero_mul, mul_zero, add_zero]

/-- **The involution-block datum**: for an involution `u` of `H` and a block `n`, there is a
quadratic map `E` on `𝔽₂[H]^K` with an equivariant factor-set datum whose basis diagonal is
zero and whose basis polar form is the indicator of `{x' = xu}` on block `n` (the orbit
polynomial `E_{n,u}` of the paper's normal form, Lemma 6.2). -/
theorem exists_invBlock_datum [Fintype H] (n : Fin K) {u : H} (hu2 : u * u = 1)
    (hu1 : u ≠ 1) :
    ∃ (E : PermW H K → ZMod 2) (dat : FactorSet H (PermW H K)),
      IsEquivariantFactorSet E dat ∧ IsQuadraticFp2 E ∧
      (∀ p : Fin K × H, E (permBas p.1 p.2) = 0) ∧
      (∀ p p' : Fin K × H, p ≠ p' →
        polar E (permBas p.1 p.2) (permBas p'.1 p'.2)
          = if p.1 = n ∧ p'.1 = n ∧ p'.2 = p.2 * u then 1 else 0) := by
  -- the ⊥-quotient bridge
  set π : H →* H ⧸ (⊥ : Subgroup H) := QuotientGroup.mk' (⊥ : Subgroup H) with hπdef
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff]
    exact QuotientGroup.ker_mk' _
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  set eqv : H ≃* H ⧸ (⊥ : Subgroup H) := MulEquiv.ofBijective π ⟨hπinj, hπsurj⟩ with heqv
  set ρ : H ⧸ (⊥ : Subgroup H) → H := ⇑eqv.symm with hρdef
  have hρπ : ∀ x : H, ρ (π x) = x := fun x => eqv.symm_apply_apply x
  have hπρ : ∀ w : H ⧸ (⊥ : Subgroup H), π (ρ w) = w := fun w => eqv.apply_symm_apply w
  have hρmul : ∀ w w' : H ⧸ (⊥ : Subgroup H), ρ (w * w') = ρ w * ρ w' := fun w w' =>
    map_mul eqv.symm w w'
  have hρinv : ∀ w : H ⧸ (⊥ : Subgroup H), ρ w⁻¹ = (ρ w)⁻¹ := fun w => map_inv eqv.symm w
  have hρinj : Function.Injective ρ := eqv.symm.injective
  -- the involution downstairs and the base datum (P-17e3)
  set gbar : H ⧸ (⊥ : Subgroup H) := π u with hgbar
  have hg2 : gbar * gbar = 1 := by rw [hgbar, ← map_mul, hu2, map_one]
  have hbase := isEquivariantFactorSet_invOrbitDatum (⊥ : Subgroup H) gbar hg2
  -- transport the acting group along `π` (the action instance is `compHom`, so `hπ` is `rfl`)
  letI actH : DistribMulAction H (RegRep (⊥ : Subgroup H)) :=
    DistribMulAction.compHom _ π
  have hstep1 := datum_comapHom (C := H) hbase π (fun c v => rfl)
  -- the block projection, equivariant for the transported action
  set j : PermW H K →+ RegRep (⊥ : Subgroup H) :=
    { toFun := fun F => fun w => F n (ρ w)
      map_zero' := rfl
      map_add' := fun F G => rfl } with hjdef
  have hj : ∀ (h : H) (F : PermW H K), j (h • F) = h • j F := by
    intro h F
    funext w
    show F n (h⁻¹ * ρ w) = (j F) ((π h)⁻¹ * w)
    show F n (h⁻¹ * ρ w) = F n (ρ ((π h)⁻¹ * w))
    rw [hρmul, hρinv, hρπ]
  have hfinal := datum_comap hstep1 j hj
  -- the package
  refine ⟨_, _, hfinal, ?_, ?_, ?_⟩
  · -- quadraticity, from the biadditivity of the (transported) involution factor set
    refine datum_isQuadratic hfinal ?_ ?_
    · intro v v' w
      show (invOrbitDatum (⊥ : Subgroup H) gbar).f (j (v + v')) (j w) = _
      rw [map_add]
      exact invOrbitDatum_f_add_left (⊥ : Subgroup H) gbar (j v) (j v') (j w)
    · intro v w w'
      show (invOrbitDatum (⊥ : Subgroup H) gbar).f (j v) (j (w + w')) = _
      rw [map_add]
      exact invOrbitDatum_f_add_right (⊥ : Subgroup H) gbar (j v) (j w) (j w')
  · -- the basis diagonal vanishes: no coordinate is `u`-paired with itself
    intro p
    show (invOrbitDatum (⊥ : Subgroup H) gbar).f (j (permBas p.1 p.2)) (j (permBas p.1 p.2)) = 0
    rw [invOrbitDatum_f_apply]
    refine (finsum_congr fun w => ?_).trans finsum_zero
    show (j (permBas p.1 p.2)) w.out * (j (permBas p.1 p.2)) (w.out * gbar) = 0
    show permBas p.1 p.2 n (ρ w.out) * permBas p.1 p.2 n (ρ (w.out * gbar)) = 0
    rw [permBas_apply, permBas_apply]
    by_cases h1 : n = p.1 ∧ ρ w.out = p.2
    · rw [if_pos h1]
      have h2 : ¬(n = p.1 ∧ ρ (w.out * gbar) = p.2) := by
        rintro ⟨-, h2⟩
        have h3 : ρ (w.out * gbar) = ρ w.out := h2.trans h1.2.symm
        have h4 : w.out * gbar = w.out := hρinj h3
        have h5 : gbar = 1 := by
          have := mul_eq_left.mp h4
          exact this
        rw [hgbar] at h5
        have h6 : u ∈ (⊥ : Subgroup H) := (QuotientGroup.eq_one_iff u).mp h5
        exact hu1 (Subgroup.mem_bot.mp h6)
      rw [if_neg h2, mul_zero]
    · rw [if_neg h1, zero_mul]
  · -- the basis polar form is the `u`-pairing indicator on block `n`
    intro p p' hpp'
    obtain ⟨m, x⟩ := p
    obtain ⟨m', x'⟩ := p'
    -- polar via `f_polar` of the datum
    rw [← hfinal.f_polar (permBas m x) (permBas m' x')]
    -- both `f`-terms are single-indicator finsums
    show ((invOrbitDatum (⊥ : Subgroup H) gbar).f (j (permBas m x)) (j (permBas m' x'))
        + (invOrbitDatum (⊥ : Subgroup H) gbar).f (j (permBas m' x')) (j (permBas m x)))
      = if (m, x).1 = n ∧ (m', x').1 = n ∧ (m', x').2 = (m, x).2 * u then 1 else 0
    show ((invOrbitDatum (⊥ : Subgroup H) gbar).f (j (permBas m x)) (j (permBas m' x'))
        + (invOrbitDatum (⊥ : Subgroup H) gbar).f (j (permBas m' x')) (j (permBas m x)))
      = if m = n ∧ m' = n ∧ x' = x * u then 1 else 0
    rw [invOrbitDatum_f_apply, invOrbitDatum_f_apply,
      ← finsum_add_distrib (Set.toFinite _) (Set.toFinite _)]
    have hterm : ∀ w : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar,
        (j (permBas m x)) w.out * (j (permBas m' x')) (w.out * gbar)
          + (j (permBas m' x')) w.out * (j (permBas m x)) (w.out * gbar)
        = if m = n ∧ m' = n ∧ x' = x * u then
            (if ρ w.out = x then (1 : ZMod 2) else 0)
              + (if ρ w.out = x' then (1 : ZMod 2) else 0)
          else 0 := by
      intro w
      show permBas m x n (ρ w.out) * permBas m' x' n (ρ (w.out * gbar))
          + permBas m' x' n (ρ w.out) * permBas m x n (ρ (w.out * gbar)) = _
      have hshift : ρ (w.out * gbar) = ρ w.out * u := by
        rw [hρmul]
        congr 1
        rw [hgbar]
        exact hρπ u
      rw [hshift]
      exact permBas_pair_indicator n m m' x x' hu2 (ρ w.out)
    by_cases hcond : m = n ∧ m' = n ∧ x' = x * u
    · rw [if_pos hcond]
      have hterm' : ∀ w : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar,
          (j (permBas m x)) w.out * (j (permBas m' x')) (w.out * gbar)
            + (j (permBas m' x')) w.out * (j (permBas m x)) (w.out * gbar)
          = (if ρ w.out = x then (1 : ZMod 2) else 0)
            + (if ρ w.out = x' then (1 : ZMod 2) else 0) :=
        fun w => (hterm w).trans (if_pos hcond)
      rw [finsum_congr hterm']
      -- exactly one `⟨ḡ⟩`-coset carries the pair `{x, x' = xu}`
      have hxne : x ≠ x' := fun h =>
        hpp' (Prod.ext (hcond.1.trans hcond.2.1.symm) h)
      set w₀ : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar :=
        ((π x : H ⧸ (⊥ : Subgroup H)) : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar)
        with hw₀def
      have hval : ∀ w : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar, w ≠ w₀ →
          ((if ρ w.out = x then (1 : ZMod 2) else 0)
            + (if ρ w.out = x' then (1 : ZMod 2) else 0)) = 0 := by
        intro w hw
        have hne1 : ¬ ρ w.out = x := by
          intro hρ
          apply hw
          have hout : w.out = π x := by rw [← hπρ w.out, hρ]
          rw [← Quotient.out_eq w, hout, hw₀def]
        have hne2 : ¬ ρ w.out = x' := by
          intro hρ
          apply hw
          have hout : w.out = π x' := by rw [← hπρ w.out, hρ]
          have hco : ((π x' : H ⧸ (⊥ : Subgroup H)) :
              (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar) = w₀ := by
            rw [hw₀def, QuotientGroup.eq]
            have hxy : (π x')⁻¹ * π x = gbar⁻¹ := by
              rw [hgbar, hcond.2.2, ← map_inv, ← map_mul, ← map_inv]
              congr 1
              group
            rw [hxy]
            exact Subgroup.inv_mem _ (Subgroup.mem_zpowers gbar)
          rw [← Quotient.out_eq w, hout]
          exact hco
        rw [if_neg hne1, if_neg hne2, add_zero]
      have hw₀val : ((if ρ w₀.out = x then (1 : ZMod 2) else 0)
          + (if ρ w₀.out = x' then (1 : ZMod 2) else 0)) = 1 := by
        have h1 : (π x)⁻¹ * w₀.out ∈ Subgroup.zpowers gbar := by
          rw [← QuotientGroup.eq]
          exact ((Quotient.out_eq w₀).trans hw₀def).symm
        rcases zpowers_sq_dichotomy (⊥ : Subgroup H) gbar hg2 h1 with h | h
        · have hout : w₀.out = π x := (inv_mul_eq_one.mp h).symm
          rw [hout, hρπ, if_pos rfl, if_neg hxne, add_zero]
        · have hout : w₀.out = π x * gbar := inv_mul_eq_iff_eq_mul.mp h
          have hρout : ρ w₀.out = x' := by
            rw [hout, hρmul, hρπ, hgbar, hρπ, ← hcond.2.2]
          rw [hρout, if_neg (fun h => hxne h.symm), if_pos rfl, zero_add]
      rw [finsum_eq_single _ w₀ hval, hw₀val]
    · rw [if_neg hcond]
      have hterm' : ∀ w : (H ⧸ (⊥ : Subgroup H)) ⧸ Subgroup.zpowers gbar,
          (j (permBas m x)) w.out * (j (permBas m' x')) (w.out * gbar)
            + (j (permBas m' x')) w.out * (j (permBas m x)) (w.out * gbar) = 0 :=
        fun w => (hterm w).trans (if_neg hcond)
      rw [finsum_congr hterm', finsum_zero]

end InvolutionBlock

/-! ## The normal form: every invariant quadratic map on `𝔽₂[H]^K` has a datum

The paper's step 2 of Lemma 6.3.  Deviation (documented in the module docstring): a single
invariant biadditive refinement `f(F,G) = ∑ F_{n,x} G_{m,y} φ(n, m, x⁻¹y)` replaces the
square/free orbit-polynomial sums; the `φ`-kernel exists exactly off the involution locus,
which is corrected by the `E_{n,u}` data first. -/

section NormalFormMain

variable {H : Type} [Group H] {K : ℕ}

theorem polar_finset_sum {V : Type*} [AddCommGroup V] {ι : Type*} (s : Finset ι)
    (qs : ι → V → ZMod 2) (v w : V) :
    polar (fun x => ∑ i ∈ s, qs i x) v w = ∑ i ∈ s, polar (qs i) v w := by
  simp only [polar]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]

theorem isQuadraticFp2_finset_sum {V : Type*} [AddCommGroup V] {ι : Type*}
    (s : Finset ι) (qs : ι → V → ZMod 2) (h : ∀ i ∈ s, IsQuadraticFp2 (qs i)) :
    IsQuadraticFp2 (fun v => ∑ i ∈ s, qs i v) where
  map_zero := Finset.sum_eq_zero fun i hi => (h i hi).map_zero
  polar_add_left u v w := by
    rw [polar_finset_sum, polar_finset_sum, polar_finset_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).polar_add_left u v w
  polar_add_right u v w := by
    rw [polar_finset_sum, polar_finset_sum, polar_finset_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i hi => (h i hi).polar_add_right u v w

theorem isQuadraticFp2_add {V : Type*} [AddCommGroup V] {q q' : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hq' : IsQuadraticFp2 q') :
    IsQuadraticFp2 (fun v => q v + q' v) where
  map_zero := by rw [hq.map_zero, hq'.map_zero, add_zero]
  polar_add_left u v w := by
    have e1 := hq.polar_add_left u v w
    have e2 := hq'.polar_add_left u v w
    simp only [polar] at e1 e2 ⊢
    linear_combination e1 + e2
  polar_add_right u v w := by
    have e1 := hq.polar_add_right u v w
    have e2 := hq'.polar_add_right u v w
    simp only [polar] at e1 e2 ⊢
    linear_combination e1 + e2

theorem polar_add_map {V : Type*} [AddCommGroup V] (q q' : V → ZMod 2) (v w : V) :
    polar (fun x => q x + q' x) v w = polar q v w + polar q' v w := by
  simp only [polar]
  ring

/-- A datum for each summand gives a datum for a finite sum of square maps. -/
private theorem exists_datum_finset_sum {C V : Type*} [Group C] [AddCommGroup V]
    [DistribMulAction C V] {ι : Type*} (s : Finset ι) (qs : ι → V → ZMod 2)
    (h : ∀ i ∈ s, ∃ dat : FactorSet C V, IsEquivariantFactorSet (qs i) dat) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet (fun v => ∑ i ∈ s, qs i v) dat := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨⟨fun _ _ => 0, fun _ _ => 0⟩, ?_⟩
    have h0 : (fun v : V => ∑ i ∈ (∅ : Finset ι), qs i v) = fun _ => (0 : ZMod 2) := by
      funext v
      exact Finset.sum_empty
    rw [h0]
    exact datum_of_biadditive_invariant (fun _ _ _ => (add_zero (0 : ZMod 2)).symm)
      (fun _ _ _ => (add_zero (0 : ZMod 2)).symm) (fun _ => rfl) (fun _ _ _ => rfl)
  | @insert a s ha IH =>
    obtain ⟨datS, hdatS⟩ := IH (fun i hi => h i (Finset.mem_insert_of_mem hi))
    obtain ⟨datA, hdatA⟩ := h a (Finset.mem_insert_self a s)
    have hfun : (fun v : V => ∑ i ∈ insert a s, qs i v)
        = fun v => qs a v + ∑ i ∈ s, qs i v := by
      funext v
      exact Finset.sum_insert ha
    rw [hfun]
    exact ⟨_, datum_add hdatA hdatS⟩

/-- Polar invariance under the diagonal action, for any `H`-invariant map on `PermW H K`. -/
private theorem permBas_polar_smul_invariant (q : PermW H K → ZMod 2) (hq : IsInvariant H q)
    (c : H) (v w : PermW H K) : polar q (c • v) (c • w) = polar q v w := by
  simp only [polar]
  rw [← smul_add, hq, hq, hq]

/-- Diagonal orbit-constancy: an `H`-invariant map is constant on each block orbit of basis
vectors, `q (e_{n,x}) = q (e_{n,1})`. -/
private theorem permBas_diag_const (q : PermW H K → ZMod 2) (hq : IsInvariant H q)
    (n : Fin K) (x : H) : q (permBas n x) = q (permBas n 1) := by
  have h1 : permBas n x = x • (permBas n 1 : PermW H K) := by
    rw [permBas_smul, mul_one]
  rw [h1, hq]

/-- The polar coordinates of an `H`-invariant map depend only on relative position:
`polar q (e_{n,x}) (e_{m,y}) = polar q (e_{n,1}) (e_{m,x⁻¹y})`. -/
private theorem permBas_polar_rel (q : PermW H K → ZMod 2) (hq : IsInvariant H q)
    (n m : Fin K) (x y : H) :
    polar q (permBas n x) (permBas m y) = polar q (permBas n 1) (permBas m (x⁻¹ * y)) := by
  have h1 : permBas n 1 = x⁻¹ • (permBas n x : PermW H K) := by
    rw [permBas_smul, inv_mul_cancel]
  have h2 : permBas m (x⁻¹ * y) = x⁻¹ • (permBas m y : PermW H K) := by
    rw [permBas_smul]
  rw [h1, h2, permBas_polar_smul_invariant q hq]

/-- **The κ⁰ normal form** (Lemma 6.3, step 2): every `H`-invariant quadratic map on the
permutation module `𝔽₂[H]^K` admits an equivariant factor-set datum. -/
theorem exists_datum_of_invariant_quadratic [Finite H]
    (Q : PermW H K → ZMod 2) (hQ : IsQuadraticFp2 Q) (hinv : IsInvariant H Q) :
    ∃ dat : FactorSet H (PermW H K), IsEquivariantFactorSet Q dat := by
  haveI : Fintype H := Fintype.ofFinite H
  have h2W : ∀ F : PermW H K, F + F = 0 := fun F => by
    funext n x
    exact CharTwo.add_self_eq_zero _
  -- the β-coordinates of Q and the bad (involution) locus
  set β : Fin K → Fin K → H → ZMod 2 :=
    fun n m u => polar Q (permBas n 1) (permBas m u) with hβdef
  set Bad : Finset (Fin K × H) :=
    Finset.univ.filter (fun p => p.2 * p.2 = 1 ∧ p.2 ≠ 1 ∧ β p.1 p.1 p.2 = 1) with hBaddef
  -- the involution corrections (P-17e3, transported)
  have hEex : ∀ p : {p : Fin K × H // p ∈ Bad},
      ∃ (E : PermW H K → ZMod 2) (dat : FactorSet H (PermW H K)),
        IsEquivariantFactorSet E dat ∧ IsQuadraticFp2 E ∧
        (∀ r : Fin K × H, E (permBas r.1 r.2) = 0) ∧
        (∀ r r' : Fin K × H, r ≠ r' →
          polar E (permBas r.1 r.2) (permBas r'.1 r'.2)
            = if r.1 = p.1.1 ∧ r'.1 = p.1.1 ∧ r'.2 = r.2 * p.1.2 then 1 else 0) := by
    intro p
    have hp : p.1 ∈ Finset.univ.filter
        (fun p : Fin K × H => p.2 * p.2 = 1 ∧ p.2 ≠ 1 ∧ β p.1 p.1 p.2 = 1) := p.2
    rw [Finset.mem_filter] at hp
    exact exists_invBlock_datum p.1.1 hp.2.1 hp.2.2.1
  choose E datE hdatE hquadE hdiagE hpolarE using hEex
  -- the corrected map Q'
  set SE : PermW H K → ZMod 2 := fun F => ∑ p : {p : Fin K × H // p ∈ Bad}, E p F with hSEdef
  set Q' : PermW H K → ZMod 2 := fun F => Q F + SE F with hQ'def
  have hSEquad : IsQuadraticFp2 SE :=
    isQuadraticFp2_finset_sum Finset.univ (fun p F => E p F) (fun p _ => hquadE p)
  have hQ'quad : IsQuadraticFp2 Q' := isQuadraticFp2_add hQ hSEquad
  have hSEinv : IsInvariant H SE := by
    intro c F
    refine Finset.sum_congr rfl fun p _ => ?_
    exact datum_isInvariant (hdatE p) h2W c F
  have hQ'inv : IsInvariant H Q' := by
    intro c F
    show Q (c • F) + SE (c • F) = Q F + SE F
    rw [hinv, hSEinv]
  -- polar of Q' at basis coordinates: β plus the bad-orbit indicators
  have hpolarQ' : ∀ (p p' : Fin K × H), p ≠ p' →
      polar Q' (permBas p.1 p.2) (permBas p'.1 p'.2)
        = polar Q (permBas p.1 p.2) (permBas p'.1 p'.2)
          + ∑ b : {p : Fin K × H // p ∈ Bad},
            (if p.1 = b.1.1 ∧ p'.1 = b.1.1 ∧ p'.2 = p.2 * b.1.2 then (1 : ZMod 2) else 0) := by
    intro p p' hpp'
    show polar (fun F => Q F + SE F) _ _ = _
    rw [polar_add_map, hSEdef]
    congr 1
    rw [polar_finset_sum]
    exact Finset.sum_congr rfl fun b _ => hpolarE b p p' hpp'
  -- the involution coordinates of Q' vanish
  have hβ'inv : ∀ (n : Fin K) (u : H), u * u = 1 → u ≠ 1 →
      polar Q' (permBas n 1) (permBas n u) = 0 := by
    intro n u huu hu1
    have hne : ((n, 1) : Fin K × H) ≠ (n, u) := by
      intro h
      exact hu1 (congrArg Prod.snd h).symm
    rw [hpolarQ' (n, 1) (n, u) hne]
    by_cases hmem : ((n, u) : Fin K × H) ∈ Bad
    · -- the (n,u)-term contributes 1, cancelling β n n u = 1
      have hβ1 : β n n u = 1 := by
        have h := hmem
        rw [hBaddef, Finset.mem_filter] at h
        exact h.2.2.2
      have hsum : (∑ b : {p : Fin K × H // p ∈ Bad},
          (if (n : Fin K) = b.1.1 ∧ (n : Fin K) = b.1.1 ∧ u = (1 : H) * b.1.2
            then (1 : ZMod 2) else 0)) = 1 := by
        have hcong : ∀ b : {p : Fin K × H // p ∈ Bad},
            (if (n : Fin K) = b.1.1 ∧ (n : Fin K) = b.1.1 ∧ u = (1 : H) * b.1.2
              then (1 : ZMod 2) else 0)
            = if b = ⟨(n, u), hmem⟩ then 1 else 0 := by
          intro b
          refine if_congr ?_ rfl rfl
          constructor
          · rintro ⟨h1, -, h3⟩
            refine Subtype.ext (Prod.ext h1.symm ?_)
            rw [one_mul] at h3
            exact h3.symm
          · rintro rfl
            simp
        rw [Finset.sum_congr rfl fun b _ => hcong b,
          Finset.sum_ite_eq' _ (⟨(n, u), hmem⟩ : {p : Fin K × H // p ∈ Bad})
            (fun _ => (1 : ZMod 2)), if_pos (Finset.mem_univ _)]
      show β n n u + _ = 0
      rw [hsum, hβ1]
      decide
    · -- no term contributes, and β n n u = 0 since (n,u) is not bad
      have hβ0 : β n n u = 0 := by
        rcases ZMod.eq_zero_or_eq_one (β n n u) with h0 | h1
        · exact h0
        · exact absurd (by
            rw [hBaddef, Finset.mem_filter]
            exact ⟨Finset.mem_univ _, huu, hu1, h1⟩) hmem
      have hsum : (∑ b : {p : Fin K × H // p ∈ Bad},
          (if (n : Fin K) = b.1.1 ∧ (n : Fin K) = b.1.1 ∧ u = (1 : H) * b.1.2
            then (1 : ZMod 2) else 0)) = 0 := by
        refine Finset.sum_eq_zero fun b _ => ?_
        refine if_neg ?_
        rintro ⟨h1, -, h3⟩
        apply hmem
        rw [one_mul] at h3
        have hb : b.1 = (n, u) := Prod.ext h1.symm h3.symm
        rw [← hb]
        exact b.2
      show β n n u + _ = 0
      rw [hsum, hβ0, add_zero]
  -- the ordering gadget for the half-choice
  set ord : H → ℕ := fun h => ((Fintype.equivFin H) h : ℕ) with horddef
  have hordinj : Function.Injective ord := fun a b hab =>
    (Fintype.equivFin H).injective (Fin.val_injective hab)
  -- the kernel φ and its ordered-pair coordinates f₀
  set χ : Fin K → Fin K → H → ZMod 2 := fun n m u =>
    if n < m then 1 else if m < n then 0 else if ord u < ord u⁻¹ then 1 else 0 with hχdef
  set φ : Fin K → Fin K → H → ZMod 2 := fun n m u =>
    if n = m ∧ u = 1 then Q' (permBas n 1)
    else polar Q' (permBas n 1) (permBas m u) * χ n m u with hφdef
  set f₀ : (Fin K × H) → (Fin K × H) → ZMod 2 :=
    fun p p' => φ p.1 p'.1 (p.2⁻¹ * p'.2) with hf₀def
  -- diagonal compatibility
  have hf₀diag : ∀ p : Fin K × H, f₀ p p = Q' (permBas p.1 p.2) := by
    intro p
    have harg : p.2⁻¹ * p.2 = 1 := inv_mul_cancel p.2
    show (if p.1 = p.1 ∧ p.2⁻¹ * p.2 = 1 then Q' (permBas p.1 1)
      else polar Q' (permBas p.1 1) (permBas p.1 (p.2⁻¹ * p.2)) * χ p.1 p.1 (p.2⁻¹ * p.2))
      = Q' (permBas p.1 p.2)
    rw [if_pos ⟨rfl, harg⟩]
    exact (permBas_diag_const Q' hQ'inv p.1 p.2).symm
  -- polar compatibility
  have hf₀polar : ∀ p p' : Fin K × H, p ≠ p' →
      f₀ p p' + f₀ p' p = polar Q' (permBas p.1 p.2) (permBas p'.1 p'.2) := by
    intro p p' hpp'
    obtain ⟨m, x⟩ := p
    obtain ⟨m', x'⟩ := p'
    set u : H := x⁻¹ * x' with hudef
    have hu' : x'⁻¹ * x = u⁻¹ := by
      rw [hudef, mul_inv_rev, inv_inv]
    have hnd : ¬(m = m' ∧ u = 1) := by
      rintro ⟨rfl, hu1⟩
      apply hpp'
      have hxx : x = x' := by
        have h1 : x⁻¹ * x' = 1 := hu1
        rw [← inv_mul_cancel x] at h1
        exact (mul_left_cancel h1).symm
      rw [hxx]
    have hnd' : ¬(m' = m ∧ u⁻¹ = 1) := by
      rintro ⟨h1, h2⟩
      exact hnd ⟨h1.symm, by rw [← inv_inv u, h2, inv_one]⟩
    show φ m m' u + φ m' m (x'⁻¹ * x) = _
    rw [hu', hφdef]
    simp only []
    rw [if_neg hnd, if_neg hnd']
    -- β'-symmetry: polar Q' (e_{m',1}) (e_{m,u⁻¹}) = polar Q' (e_{m,1}) (e_{m',u})
    have hsymm : polar Q' (permBas m' 1) (permBas m u⁻¹)
        = polar Q' (permBas m 1) (permBas m' u) := by
      rw [polar_comm]
      have h1 := permBas_polar_rel Q' hQ'inv m m' u⁻¹ 1
      rw [inv_inv, mul_one] at h1
      exact h1
    rw [hsymm, ← mul_add]
    -- the coordinate to hit
    have hcoord : polar Q' (permBas m x) (permBas m' x')
        = polar Q' (permBas m 1) (permBas m' u) := by
      rw [permBas_polar_rel Q' hQ'inv m m' x x', hudef]
    rw [hcoord]
    -- case analysis on the χ-sum
    rcases lt_trichotomy m m' with hlt | heq | hgt
    · have hχ : χ m m' u + χ m' m u⁻¹ = 1 := by
        rw [hχdef]
        simp only []
        rw [if_pos hlt, if_neg (asymm hlt), if_pos hlt, add_zero]
      rw [hχ, mul_one]
    · subst heq
      have hune : u ≠ 1 := fun h => hnd ⟨rfl, h⟩
      by_cases huu : u = u⁻¹
      · -- involution coordinate: the polar vanishes
        have huu2 : u * u = 1 := by
          nth_rewrite 2 [huu]
          exact mul_inv_cancel u
        have hz := hβ'inv m u huu2 hune
        rw [hz, zero_mul]
      · have hχ : χ m m u + χ m m u⁻¹ = 1 := by
          rw [hχdef]
          simp only []
          rw [if_neg (lt_irrefl m), if_neg (lt_irrefl m), if_neg (lt_irrefl m),
            if_neg (lt_irrefl m), inv_inv]
          have hordne : ord u ≠ ord u⁻¹ := fun h => huu (hordinj h)
          rcases lt_trichotomy (ord u) (ord u⁻¹) with h | h | h
          · rw [if_pos h, if_neg (asymm h), add_zero]
          · exact absurd h hordne
          · rw [if_neg (asymm h), if_pos h, zero_add]
        rw [hχ, mul_one]
    · have hχ : χ m m' u + χ m' m u⁻¹ = 1 := by
        rw [hχdef]
        simp only []
        rw [if_neg (asymm hgt), if_pos hgt, if_pos hgt, zero_add]
      rw [hχ, mul_one]
  -- the invariant biadditive refinement of Q'
  set f : PermW H K → PermW H K → ZMod 2 := fun F G =>
    ∑ p : Fin K × H, ∑ p' : Fin K × H, F p.1 p.2 * G p'.1 p'.2 * f₀ p p' with hfdef
  have hfl : ∀ v v' w : PermW H K, f (v + v') w = f v w + f v' w := by
    intro v v' w
    rw [hfdef]
    simp only []
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    show (v p.1 p.2 + v' p.1 p.2) * w p'.1 p'.2 * f₀ p p' = _
    ring
  have hfr : ∀ v w w' : PermW H K, f v (w + w') = f v w + f v w' := by
    intro v w w'
    rw [hfdef]
    simp only []
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p' _ => ?_
    show v p.1 p.2 * ((w p'.1 p'.2 + w' p'.1 p'.2)) * f₀ p p' = _
    ring
  have hfdiag : ∀ F : PermW H K, f F F = Q' F := fun F =>
    (quadratic_eq_double_sum hQ'quad f₀ hf₀diag hf₀polar F).symm
  have hfinv : ∀ (c : H) (v w : PermW H K), f (c • v) (c • w) = f v w := by
    intro c v w
    rw [hfdef]
    simp only []
    -- reindex both coordinates by (n, x) ↦ (n, c⁻¹x); f₀ only sees relative positions
    have hf₀shift : ∀ p p' : Fin K × H,
        f₀ (p.1, c⁻¹ * p.2) (p'.1, c⁻¹ * p'.2) = f₀ p p' := by
      intro p p'
      show φ p.1 p'.1 ((c⁻¹ * p.2)⁻¹ * (c⁻¹ * p'.2)) = φ p.1 p'.1 (p.2⁻¹ * p'.2)
      congr 1
      group
    set σ : (Fin K × H) ≃ (Fin K × H) :=
      (Equiv.refl (Fin K)).prodCongr (Equiv.mulLeft c⁻¹) with hσdef
    have hσapp : ∀ p : Fin K × H, σ p = (p.1, c⁻¹ * p.2) := fun p => rfl
    calc ∑ p : Fin K × H, ∑ p' : Fin K × H, (c • v) p.1 p.2 * (c • w) p'.1 p'.2 * f₀ p p'
        = ∑ p : Fin K × H, ∑ p' : Fin K × H,
            v (σ p).1 (σ p).2 * w (σ p').1 (σ p').2 * f₀ (σ p) (σ p') := by
          refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun p' _ => ?_
          rw [hσapp, hσapp, hf₀shift]
          rfl
      _ = ∑ p : Fin K × H, ∑ p' : Fin K × H, v p.1 p.2 * w p'.1 p'.2 * f₀ p p' := by
          rw [← Equiv.sum_comp σ
            (fun p => ∑ p' : Fin K × H, v p.1 p.2 * w p'.1 p'.2 * f₀ p p')]
          refine Finset.sum_congr rfl fun p _ => ?_
          exact Equiv.sum_comp σ (fun p' => v (σ p).1 (σ p).2 * w p'.1 p'.2 * f₀ (σ p) p')
  have hdatQ' : IsEquivariantFactorSet Q'
      (⟨f, fun _ _ => 0⟩ : FactorSet H (PermW H K)) :=
    datum_of_biadditive_invariant hfl hfr hfdiag hfinv
  -- add back the corrections: Q' + SE = Q in characteristic 2
  obtain ⟨datS, hdatS⟩ := exists_datum_finset_sum (C := H) Finset.univ (fun p F => E p F)
    (fun p _ => ⟨datE p, hdatE p⟩)
  have hfinal := datum_add hdatQ' hdatS
  have heq : (fun F => Q' F + ∑ p ∈ Finset.univ, E p F) = Q := by
    funext F
    show (Q F + SE F) + SE F = Q F
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero]
  rw [heq] at hfinal
  exact ⟨_, hfinal⟩

end NormalFormMain

/-! ## The tame assembly (Lemma 6.3, all pieces)

`kappa0_exists_tame` is the full statement over an abstract finite tame-generated group; the
`SectionNine.kappa0_exists` splice unpacks `ActsThroughTame`/`IsSimpleModTwo` and pulls back
along the surjection with `comapHom`. -/

section TameAssembly

/-- **2-torsion from simplicity + nonsingularity**: on a simple `H`-module, a nonsingular
quadratic map forces `v + v = 0` for all `v`.  The 2-torsion subgroup is `H`-stable, so it is
`⊥` or `⊤`; if `⊥` then `|V|` is odd, whence every polar pairing `polar q v₀ ·` kills the whole
module (a unit multiple of an odd-order sum), contradicting nonsingularity. -/
private theorem two_torsion_of_nonsingular_simple {H : Type} [Group H] {V : Type}
    [AddCommGroup V] [Finite V] [Nontrivial V] [DistribMulAction H V] {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ v : V, v + v = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype V := Fintype.ofFinite V
  set W₂ : AddSubgroup V :=
    { carrier := {v : V | v + v = 0}
      zero_mem' := by rw [Set.mem_setOf_eq, add_zero]
      add_mem' := fun {a b} ha hb => by
        rw [Set.mem_setOf_eq] at ha hb ⊢
        calc a + b + (a + b) = (a + a) + (b + b) := by abel
          _ = 0 := by rw [ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        rw [Set.mem_setOf_eq] at ha ⊢
        rw [← neg_add, ha, neg_zero] } with hW₂
  have hstable : ∀ (g : H) (w : V), w ∈ W₂ → g • w ∈ W₂ := by
    intro g w hw
    show g • w + g • w = 0
    rw [← smul_add, (hw : w + w = 0), smul_zero]
  rcases hsimple W₂ hstable with hbot | htop
  · -- no 2-torsion ⟹ |V| odd ⟹ all polar pairings vanish, against nonsingularity
    exfalso
    have hodd : Odd (Fintype.card V) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card 2 heven.two_dvd
      have ha2 : a + a = 0 := by
        have h1 : (2 : ℕ) • a = 0 := by
          rw [← ha]
          exact addOrderOf_nsmul_eq_zero a
        rwa [two_nsmul] at h1
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, addOrderOf_zero] at ha
        omega
      have : a ∈ W₂ := ha2
      rw [hbot, AddSubgroup.mem_bot] at this
      exact ha0 this
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := hns v₀ hv₀
    set ψ : V →+ ZMod 2 := AddMonoidHom.mk' (fun w' => polar q v₀ w')
      (fun w' w'' => hq.polar_add_right v₀ w' w'') with hψ
    have hcard : Fintype.card V • w = 0 := card_nsmul_eq_zero
    have h0 : ψ w = 0 := by
      have h1 : Fintype.card V • ψ w = ψ (Fintype.card V • w) := (map_nsmul ψ _ _).symm
      rw [hcard, map_zero] at h1
      have hc1 : (Fintype.card V : ZMod 2) = 1 := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk]
        push_cast
        linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      rwa [nsmul_eq_mul, hc1, one_mul] at h1
    exact hw h0
  · intro v
    exact (htop ▸ AddSubgroup.mem_top v : v ∈ W₂)

/-- **κ⁰ existence over a finite tame-generated group** (paper Lemma 6.3): a nonsingular
invariant quadratic map on a nontrivial simple module for a finite group generated by a tame
pair `(s, t)` admits an equivariant factor-set datum.

Proof: 2-torsion follows from simplicity + nonsingularity (an odd-order module has zero polar
pairings); the action factors through the faithful image `Ĥ ≤ AddAut V` (`toAddAut`), where
either `t̂` acts trivially — then `t̂ = 1`, `|Ĥ|` is odd (an involution would commute with
`t̂` and die by the O₂-linchpin `two_torsion_of_centralizer_eq_one`), and averaging gives the
datum (`datum_of_odd`) — or the module is ramified and `lemma_6_11_of_tame_pair` split-embeds
`V` into `𝔽₂[Ĥ]^N`, where the normal form `exists_datum_of_invariant_quadratic` applies and
pulls back (`datum_of_split`). -/
theorem kappa0_exists_tame {H : Type} [Group H] [Finite H]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction H V]
    {s t : H} (hgen : Subgroup.closure {s, t} = ⊤) (hrel : s⁻¹ * t * s = t ^ 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant H q) (hnt : Nontrivial V)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ dat : FactorSet H V, IsEquivariantFactorSet q dat := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype V := Fintype.ofFinite V
  -- V is 2-torsion: the 2-torsion subgroup is stable, and `⊥` contradicts nonsingularity
  have hV2 : ∀ v : V, v + v = 0 := two_torsion_of_nonsingular_simple hq hns hsimple
  -- the faithful image Ĥ ≤ Perm V, with the tautological (distributive) action
  set α : H →* Equiv.Perm V := MulAction.toPermHom H V with hα
  haveI hfin : Finite ↥α.range := by
    have h1 : (Set.range ⇑α).Finite := Set.finite_range ⇑α
    exact h1.to_subtype
  letI actR : DistribMulAction ↥α.range V :=
    { smul := fun g v => (g : Equiv.Perm V) v
      one_smul := fun v => rfl
      mul_smul := fun g h v => rfl
      smul_zero := fun g => by
        obtain ⟨h, hh⟩ := g.2
        show (g : Equiv.Perm V) 0 = 0
        rw [← hh]
        exact smul_zero h
      smul_add := fun g v w => by
        obtain ⟨h, hh⟩ := g.2
        show (g : Equiv.Perm V) (v + w) = (g : Equiv.Perm V) v + (g : Equiv.Perm V) w
        rw [← hh]
        exact smul_add h v w }
  set πh : H →* ↥α.range := α.rangeRestrict with hπh
  have hπhsurj : Function.Surjective πh := α.rangeRestrict_surjective
  have hcompat : ∀ (h : H) (v : V), h • v = πh h • v := fun h v => rfl
  -- transported data over the faithful image
  have hinv' : IsInvariant ↥α.range q := by
    intro c v
    obtain ⟨h, rfl⟩ := hπhsurj c
    rw [← hcompat, hinv]
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : ↥α.range), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hsimple W fun g w hw => ?_
    rw [hcompat]
    exact hW (πh g) w hw
  have hfaith' : ∀ g : ↥α.range, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    have h1 : (g : Equiv.Perm V) = 1 := Equiv.ext fun v => hg v
    exact Subtype.ext h1
  have hgen' : Subgroup.closure {πh s, πh t} = ⊤ := by
    have himg : Subgroup.closure (⇑πh '' ({s, t} : Set H)) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen]
      exact Subgroup.map_top_of_surjective _ hπhsurj
    rwa [Set.image_insert_eq, Set.image_singleton] at himg
  have hrel' : (πh s)⁻¹ * πh t * πh s = πh t ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    exact congrArg πh hrel
  -- a datum over the faithful image pulls back along `πh`
  suffices hdat' : ∃ dat : FactorSet ↥α.range V, IsEquivariantFactorSet q dat by
    obtain ⟨dat, hdat⟩ := hdat'
    exact ⟨_, datum_comapHom hdat πh hcompat⟩
  -- dichotomy on the inertia action
  by_cases hram : ∃ v : V, πh t • v ≠ v
  · -- ramified: split-embed into the permutation module and use the normal form
    have hsimple'' : ∀ W : AddSubgroup V,
        (∀ (h : ↥α.range), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
      hsimple' W fun g w hw => hW g w hw
    obtain ⟨N, ι, ret, hι, hret, hretr⟩ :=
      lemma_6_11_of_tame_pair hgen' hrel' hV2 hfaith' hsimple'' hram
    -- the split pair lands in `PermW ↥α.range N` (definitionally)
    have hιinst : ∀ (c : ↥α.range) (v : V), ι (c • v) = c • ι v := by
      intro c v
      funext n x
      rw [hι c v n x]
      rfl
    set qW : PermW ↥α.range N → ZMod 2 := fun F => q (ret F) with hqW
    have hqWquad : IsQuadraticFp2 qW := by
      constructor
      · show q (ret 0) = 0
        rw [map_zero, hq.map_zero]
      · intro a b c
        show polar _ _ _ = polar _ _ _ + polar _ _ _
        simp only [hqW, polar, map_add]
        exact hq.polar_add_left (ret a) (ret b) (ret c)
      · intro a b c
        show polar _ _ _ = polar _ _ _ + polar _ _ _
        simp only [hqW, polar, map_add]
        exact hq.polar_add_right (ret a) (ret b) (ret c)
    have hqWinv : IsInvariant ↥α.range qW := by
      intro c F
      show q (ret (c • F)) = q (ret F)
      have h1 : ret (c • F) = c • ret F := hret c F
      rw [h1, hinv']
    obtain ⟨datW, hdatW⟩ := exists_datum_of_invariant_quadratic qW hqWquad hqWinv
    exact datum_of_split datW hdatW ι hιinst (fun v => by
      show q (ret (ι v)) = q v
      rw [hretr v])
  · -- unramified: `t̂ = 1`, the group has odd order, average
    have hram' : ∀ v : V, πh t • v = v := by
      intro v
      by_contra hv
      exact hram ⟨v, hv⟩
    have ht1 : πh t = 1 := hfaith' (πh t) hram'
    have hodd : Odd (Nat.card ↥α.range) := by
      haveI : Fintype ↥α.range := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, ← Nat.not_even_iff_odd]
      intro heven
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 heven.two_dvd
      have hz2 : z ^ 2 = 1 := by
        rw [← hz]
        exact pow_orderOf_eq_one z
      have hzt : z * πh t = πh t * z := by
        rw [ht1, mul_one, one_mul]
      have hsimple'' : ∀ W : AddSubgroup V,
          (∀ (h : ↥α.range), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
        hsimple' W fun g w hw => hW g w hw
      have hz1 : z = 1 :=
        two_torsion_of_centralizer_eq_one hgen' hrel' hV2 hfaith' hsimple''
          (exists_ne (0 : V)) hz2 hzt
      rw [hz1, orderOf_one] at hz
      omega
    exact datum_of_odd hodd hV2 q hq hinv'

end TameAssembly

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.2 = ⟦lem-halforbitcocycle⟧
  * Lemma 6.3 = ⟦lem-basedetclass⟧
-/
