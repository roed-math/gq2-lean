/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.Devissage.SelfDual
public import GQ2.Devissage.LESCore

@[expose] public section

/-!
# §5.11 dévissage on the `r_R` spine: the long exact sequence — SES of complexes and connecting maps

Mechanical R-spine clone of `GQ2/Devissage/LESCore.lean` (campaign decision,
`docs/orchestration/roe-r20-recon.md`); proofs ported verbatim.  Spine renames `Z1w → Z1wR`, `H1w →
H1wR`, `H2w → H2wR`, `d1Fun → d1FunR`, `d1 → d1R`, `mixedB → mixedB_R`, `WildRel → WildRelR`,
`IsSelfDual(W) → IsSelfDual(W)_R`, with R-suffixed public names.  The `(A)` degreewise-exactness
helpers `pi_g_surjective`, `pi_exact`, `prod_g_surjective`, `prod_exact` are reused from
`GQ2.Devissage.LESCore`, never cloned.
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## The long exact sequence

A module SES `0 → A' --f--> A --g--> A'' → 0` (with `C`-equivariant `f`, `g`) induces a short
exact sequence of word complexes; the degreewise functors `(·)⁴` and `(·)²` are exact.  From this
we build the connecting maps and the nine-term LES. -/

section LES

variable {A' A A'' : Type*}
  [AddCommGroup A'] [DistribMulAction C A'] [Finite A']
  [AddCommGroup A] [DistribMulAction C A] [Finite A]
  [AddCommGroup A''] [DistribMulAction C A''] [Finite A''] [Finite C]
  (f : A' →+ A) (g : A →+ A'')
  (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a) (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
  (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : f.range = g.ker)

/-! ### The connecting map `δ¹ : H¹w(A'') → H²w(A')` (snake) -/

include hsurj in
/-- A chosen lift of a degree-1 `A''`-cochain to `A⁴` (via `g` surjective). -/
noncomputable def snakeLift_R (c'' : Fin 4 → A'') : Fin 4 → A := fun i => (hsurj (c'' i)).choose

omit [Finite A] [Finite A''] in
include hsurj in
@[simp] theorem snakeLift_spec_R (c'' : Fin 4 → A'') (i : Fin 4) :
    g (snakeLift_R g hsurj c'' i) = c'' i :=
  (hsurj (c'' i)).choose_spec

include hg hsurj in
/-- For a cocycle `c'' ∈ Z¹w(A'')`, `d¹` of its lift lands in `ker(g × g)`. -/
theorem snake_d1_mem_R (t : Marking C) (c'' : Z1wR (A := A'') t) :
    (g.prodMap g) (d1R t (snakeLift_R g hsurj c''.1)) = 0 := by
  have h1 : d1R t (fun i => g (snakeLift_R g hsurj c''.1 i))
      = (g.prodMap g) (d1R t (snakeLift_R g hsurj c''.1)) := by
    rw [AddMonoidHom.coe_prodMap]; exact d1_natural_R t g hg (snakeLift_R g hsurj c''.1)
  rw [← h1, show (fun i => g (snakeLift_R g hsurj c''.1 i)) = c''.1 from
    funext (snakeLift_spec_R g hsurj c''.1)]
  exact AddMonoidHom.mem_ker.mp c''.2

include hg hsurj hexact in
/-- The `A'²`-element the snake extracts: `(f × f)(snakeZ_R) = d¹(lift c'')`. -/
noncomputable def snakeZ_R (t : Marking C) (c'' : Z1wR (A := A'') t) : A' × A' :=
  ((prod_exact f g hexact (d1R t (snakeLift_R g hsurj c''.1))).mp
    (snake_d1_mem_R g hg hsurj t c'')).choose

omit [DistribMulAction C A'] [Finite A'] in
include hg hsurj hexact in
theorem snakeZ_spec_R (t : Marking C) (c'' : Z1wR (A := A'') t) :
    (f.prodMap f) (snakeZ_R f g hg hsurj hexact t c'') = d1R t (snakeLift_R g hsurj c''.1) :=
  ((prod_exact f g hexact (d1R t (snakeLift_R g hsurj c''.1))).mp
    (snake_d1_mem_R g hg hsurj t c'')).choose_spec

include hf hg hinj hsurj hexact in
/-- **Well-definedness of the snake**: for *any* lift `c` of `c''` and *any* `z` with
`(f×f)(z) = d¹(c)`, the class `[z] ∈ H²w(A')` equals `[snakeZ_R c'']` — so `δ¹` will not depend on
the chosen lift, hence descends to a hom on `H¹w(A'')`. -/
theorem snakeZ_welldef_R (t : Marking C) (c'' : Z1wR (A := A'') t)
    (c : Fin 4 → A) (z : A' × A') (hc : (fun i => g (c i)) = c''.1)
    (hz : (f.prodMap f) z = d1R t c) :
    (QuotientAddGroup.mk z : H2wR (A := A') t)
      = QuotientAddGroup.mk (snakeZ_R f g hg hsurj hexact t c'') := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  -- `c − snakeLift_R` maps to `0` under `g`, so it is `f` of some `w : A'⁴`.
  have hker : (fun i => g ((c - snakeLift_R g hsurj c''.1) i)) = 0 := by
    funext i
    simp only [Pi.sub_apply, map_sub, snakeLift_spec_R, congrFun hc i, sub_self, Pi.zero_apply]
  obtain ⟨w, hw⟩ := (pi_exact f g hexact (c - snakeLift_R g hsurj c''.1)).mp hker
  -- `(f×f)(z − snakeZ_R) = d¹(c) − d¹(snakeLift_R) = d¹(f∘w) = (f×f)(d¹ w)`,
  -- so `z − snakeZ_R = d¹ w`.
  have hd1w : (f.prodMap f) (d1R t w) = d1R t (c - snakeLift_R g hsurj c''.1) := by
    rw [show (c - snakeLift_R g hsurj c''.1) = (fun i => f (w i)) from hw.symm]
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural_R t f hf w).symm
  have hzz : (f.prodMap f) (z - snakeZ_R f g hg hsurj hexact t c'') = (f.prodMap f) (d1R t w) := by
    rw [map_sub, hz, snakeZ_spec_R, hd1w, map_sub]
  have : z - snakeZ_R f g hg hsurj hexact t c'' = d1R t w := hfinj hzz
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  exact ⟨w, this.symm⟩

include hf hg hinj hsurj hexact in
/-- The connecting map on cocycles, `Z¹w(A'') →+ H²w(A')`, `c'' ↦ [snakeZ_R c'']` (a hom by
`snakeZ_welldef_R`, using additive lifts). -/
noncomputable def delta1raw_R (t : Marking C) : Z1wR (A := A'') t →+ H2wR (A := A') t where
  toFun c'' := QuotientAddGroup.mk (snakeZ_R f g hg hsurj hexact t c'')
  map_zero' :=
    ((snakeZ_welldef_R f g hf hg hinj hsurj hexact t 0 0 0
      (by funext i; simp) (by simp only [map_zero])).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' c''₁ c''₂ := by
    refine ((snakeZ_welldef_R f g hf hg hinj hsurj hexact t (c''₁ + c''₂)
      (snakeLift_R g hsurj c''₁.1 + snakeLift_R g hsurj c''₂.1)
      (snakeZ_R f g hg hsurj hexact t c''₁ + snakeZ_R f g hg hsurj hexact t c''₂) ?_ ?_).symm).trans
      (QuotientAddGroup.mk_add _ _ _)
    · funext i; simp only [Pi.add_apply, map_add, snakeLift_spec_R]; rfl
    · rw [map_add, snakeZ_spec_R, snakeZ_spec_R, ← map_add]

include hf hg hinj hsurj hexact in
/-- **The snake connecting map** `δ¹ : H¹w(A'') → H²w(A')`.  Descends `delta1raw_R` through the
`B¹w`-quotient: a coboundary `c'' = d⁰(a'')` lifts to `d⁰(â)`, whose `d¹` is `0`, so its class
is `0`. -/
noncomputable def delta1_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) :
    H1wR (A := A'') t →+ H2wR (A := A') t :=
  QuotientAddGroup.lift _ (delta1raw_R f g hf hg hinj hsurj hexact t) <| by
    rintro c'' hc''
    rw [AddSubgroup.mem_addSubgroupOf] at hc''
    obtain ⟨a'', ha''⟩ := hc''
    obtain ⟨a, ha⟩ := hsurj a''
    show QuotientAddGroup.mk (snakeZ_R f g hg hsurj hexact t c'') = 0
    refine ((snakeZ_welldef_R f g hf hg hinj hsurj hexact t c'' (d0 t a) 0 ?_ ?_).symm).trans
      (QuotientAddGroup.mk_zero _)
    · rw [← d0_natural t g hg a, ha]; exact ha''
    · rw [map_zero]; exact (d1FunR_comp_d0 t ht hw a).symm

/-! ### The connecting map `δ⁰ : H⁰w(A'') → H¹w(A')` (snake)

The mirror of `δ¹` one degree down.  Lift `a'' ∈ H⁰w(A'')` to `a ∈ A`; then `d⁰a ∈ ker(g∘·)`
(as `g∘d⁰a = d⁰(g a) = d⁰a'' = 0`), so `d⁰a = f∘w` for a unique `w : A'⁴`, which is a cocycle
(`f∘d¹w = d¹(f∘w) = d¹d⁰a = 0`, `f` injective).  `δ⁰(a'') := [w] ∈ H¹w(A')`; the class is
independent of the lift `a` (a different lift shifts `w` by a coboundary).  The domain `H⁰w` is an
honest subgroup (no quotient), so — unlike `δ¹` — no descent is needed, only lift-independence. -/
omit [Finite A] [Finite A''] [Finite C] in
include hg hsurj in
/-- For `a'' ∈ H⁰w(A'')`, `d⁰` of the chosen lift lands in `ker(g∘·)` (degree 1). -/
theorem snake0_d0_mem_R (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => g (d0 t (hsurj a''.1).choose i)) = 0 := by
  rw [← d0_natural t g hg, (hsurj a''.1).choose_spec]
  exact AddMonoidHom.mem_ker.mp a''.2

include hg hsurj hexact in
/-- The `A'⁴`-cochain the degree-0 snake extracts: `f∘(snake0Z'_R) = d⁰(lift a'')`. -/
noncomputable def snake0Z'_R (t : Marking C) (a'' : H0w (A := A'') t) : Fin 4 → A' :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp (snake0_d0_mem_R g hg hsurj t a'')).choose

omit [DistribMulAction C A'] [Finite A'] [Finite A] [Finite A''] [Finite C] in
include hg hsurj hexact in
theorem snake0Z'_spec_R (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => f (snake0Z'_R f g hg hsurj hexact t a'' i)) = d0 t (hsurj a''.1).choose :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp
    (snake0_d0_mem_R g hg hsurj t a'')).choose_spec

omit [Finite A''] in
include hf hg hinj hsurj hexact in
/-- `snake0Z'_R ∈ Z¹w(A')`: its `d¹` vanishes (pull `d¹∘d⁰ = 0` back through the injection `f`). -/
theorem snake0Z'_mem_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (a'' : H0w (A := A'') t) : d1R t (snake0Z'_R f g hg hsurj hexact t a'') = 0 := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  apply hfinj
  rw [map_zero]
  have hnat : (f.prodMap f) (d1R t (snake0Z'_R f g hg hsurj hexact t a''))
      = d1R t (fun i => f (snake0Z'_R f g hg hsurj hexact t a'' i)) := by
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural_R t f hf _).symm
  rw [hnat, snake0Z'_spec_R]
  exact d1FunR_comp_d0 t ht hw _

include hf hg hinj hsurj hexact in
omit [Finite A''] in
/-- Lift-independence of `δ⁰`: *any* lift `a` of `a''` with cocycle `w` (`f∘w = d⁰a`) gives the
same class `[w] = δ⁰(a'')`.  A second lift differs by `f a'`, shifting `w` by `d⁰a'`. -/
theorem delta0_welldef_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (a'' : H0w (A := A'') t) (a : A) (w : Fin 4 → A') (hwmem : d1R t w = 0)
    (ha : g a = a''.1) (hfw : (fun i => f (w i)) = d0 t a) :
    (QuotientAddGroup.mk ⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ : H1wR (A := A') t)
      = QuotientAddGroup.mk ⟨snake0Z'_R f g hg hsurj hexact t a'',
          AddMonoidHom.mem_ker.mpr (snake0Z'_mem_R f g hf hg hinj hsurj hexact t ht hw a'')⟩ := by
  set w₀ := snake0Z'_R f g hg hsurj hexact t a'' with hw₀
  -- `a − lift` is in `ker g = range f`.
  have hga : g (a - (hsurj a''.1).choose) = 0 := by
    rw [map_sub, ha, (hsurj a''.1).choose_spec, sub_self]
  obtain ⟨a', ha'⟩ :=
    AddMonoidHom.mem_range.mp (by rw [hexact]; exact AddMonoidHom.mem_ker.mpr hga)
  -- `f∘(w − w₀) = d⁰a − d⁰(lift) = d⁰(a − lift) = d⁰(f a') = f∘(d⁰a')`, so `w − w₀ = d⁰a'`.
  have hww₀ : (w - w₀ : Fin 4 → A') = d0 t a' := by
    funext i
    apply hinj
    have ex := congrFun (snake0Z'_spec_R f g hg hsurj hexact t a'') i
    rw [Pi.sub_apply, map_sub, congrFun hfw i, ex, ← congrFun (d0_natural t f hf a') i, ha',
      map_sub, Pi.sub_apply]
  -- Hence the difference of the two cocycles is a coboundary, so the classes agree.
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  refine AddMonoidHom.mem_range.mpr ⟨a', ?_⟩
  have hcoe : (↑(⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ - ⟨w₀,
      AddMonoidHom.mem_ker.mpr (snake0Z'_mem_R f g hf hg hinj hsurj hexact t ht hw a'')⟩ :
      Z1wR (A := A') t) : Fin 4 → A') = w - w₀ := rfl
  rw [hcoe]; exact hww₀.symm

include hf hg hinj hsurj hexact in
/-- **The degree-0 connecting map** `δ⁰ : H⁰w(A'') →+ H¹w(A')`. -/
noncomputable def delta0_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR) :
    H0w (A := A'') t →+ H1wR (A := A') t where
  toFun a'' := QuotientAddGroup.mk ⟨snake0Z'_R f g hg hsurj hexact t a'',
    AddMonoidHom.mem_ker.mpr (snake0Z'_mem_R f g hf hg hinj hsurj hexact t ht hw a'')⟩
  map_zero' :=
    ((delta0_welldef_R f g hf hg hinj hsurj hexact t ht hw 0 0 0 (by simp) (by simp)
      (by funext i; simp)).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' x y := by
    refine Eq.trans ?_ (QuotientAddGroup.mk_add _ _ _)
    exact (delta0_welldef_R f g hf hg hinj hsurj hexact t ht hw (x + y)
      ((hsurj x.1).choose + (hsurj y.1).choose)
      (snake0Z'_R f g hg hsurj hexact t x + snake0Z'_R f g hg hsurj hexact t y)
      (by rw [map_add, snake0Z'_mem_R f g hf hg hinj hsurj hexact t ht hw x,
            snake0Z'_mem_R f g hf hg hinj hsurj hexact t ht hw y, add_zero])
      (by rw [map_add, (hsurj x.1).choose_spec, (hsurj y.1).choose_spec]; rfl)
      (by funext i
          rw [Pi.add_apply, map_add,
            congrFun (snake0Z'_spec_R f g hg hsurj hexact t x) i,
            congrFun (snake0Z'_spec_R f g hg hsurj hexact t y) i, ← Pi.add_apply, ← map_add])).symm

end LES

end GQ2.FoxH
