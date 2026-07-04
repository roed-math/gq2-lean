import GQ2.FoxHeisenberg

/-!
# §5.11 dévissage: two-out-of-three for `IsSelfDual` along a module SES  (ticket P-13e)

`lemma_5_11` (`GQ2/FoxHeisenberg.lean`) is the two-out-of-three property of the `IsSelfDual`
package along a short exact sequence `0 → A' → A → A'' → 0` of finite elementary `𝔽₂[C]`-modules.
The proof device is the **long exact cohomology sequence** of the word complex
`C(A) : A --d⁰--> A⁴ --d¹--> A²` (displays (30)/(49)/(50)): the degreewise functors `A ↦ A`,
`A ↦ Fin 4 → A`, `A ↦ A × A` are **exact** (identity / finite products), and `d⁰`, `d¹` are
**natural** in the coefficient module (this file's `d0_natural`/`d1_natural`), so the module SES
induces a short exact sequence of complexes, whence a nine-term LES

  `0 → H⁰(A') → H⁰(A) → H⁰(A'') → H¹(A') → H¹(A) → H¹(A'') → H²(A') → H²(A) → H²(A'') → 0`.

A key simplification: **rank-nullity on `d¹`** gives `dim Z¹w = 2·dim A + dim H²w` for *every* `A`
(`Z1w = ker d¹`, `H2w = coker d¹`), so the two card clauses of `IsSelfDual` are **equivalent** —
the card part reduces to the single clause `#H²w(A) = #fixedPts(ElemDual A)`.

This file builds that infrastructure bottom-up.  `Ax = ∅`; heavy work lives here, `lemma_5_11`
gets a one-line splice in `FoxHeisenberg.lean`.
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

/-! ## Naturality of the word complex under coefficient maps

The maps `d⁰`, `d¹` commute with a `C`-equivariant additive map `φ : A →+ B` (applied degreewise),
so `φ` induces a chain map `C(A) → C(B)`.  These are the arrows of the SES of complexes. -/

section Naturality

variable {A B : Type*} [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B]

/-- **`d⁰` is natural**: `d⁰_B(φ v) = φ ∘ d⁰_A(v)` for a `C`-equivariant `φ`. -/
theorem d0_natural (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (v : A) :
    d0 t (φ v) = fun i => φ (d0 t v i) := by
  funext i
  fin_cases i <;> simp [d0, hφ]

/-- **`d¹` is natural**: `d¹_B(φ ∘ x) = (φ, φ) ∘ d¹_A(x)` for a `C`-equivariant `φ` — the finite
Fox rule pushed through the coefficient map (`WordLift.map φ` + `Marking.map_{tame,wild}Value`). -/
theorem d1_natural [Finite A] [Finite B] [Finite C] (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) (x : Fin 4 → A) :
    d1Fun t (fun i => φ (x i)) = (φ (d1Fun t x).1, φ (d1Fun t x).2) := by
  set Φ := WordLift.map (C := C) φ hφ with hΦ
  have hL : (liftMarking t x).map Φ = liftMarking t (fun i => φ (x i)) := rfl
  refine Prod.ext ?_ ?_
  · show (liftMarking t (fun i => φ (x i))).tameValue.u = φ ((liftMarking t x).tameValue.u)
    rw [← hL, Marking.map_tameValue, WordLift.map_u]
  · show (liftMarking t (fun i => φ (x i))).wildValue.u = φ ((liftMarking t x).wildValue.u)
    rw [← hL, Marking.map_wildValue, WordLift.map_u]

end Naturality

/-! ## Functoriality of the cohomology

A `C`-equivariant `φ : A →+ B` induces maps `Z¹w`, `H²w`, `H¹w` — the arrows the module SES turns
into the LES. -/

section Functoriality

variable {A B : Type*} [AddCommGroup A] [DistribMulAction C A]
  [AddCommGroup B] [DistribMulAction C B] [Finite A] [Finite B] [Finite C]

/-- `d¹`-kernel is preserved: `x ∈ Z¹w(A) ⟹ φ ∘ x ∈ Z¹w(B)`. -/
theorem d1_ker_map (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) {x : Fin 4 → A} (hx : d1 t x = 0) :
    d1 t (fun i => φ (x i)) = 0 := by
  have : d1Fun t (fun i => φ (x i)) = (φ (d1Fun t x).1, φ (d1Fun t x).2) := d1_natural t φ hφ x
  have hx' : d1Fun t x = 0 := hx
  show d1Fun t (fun i => φ (x i)) = 0
  rw [this, hx']
  simp

/-- The induced map `Z¹w(A) →+ Z¹w(B)`. -/
noncomputable def Z1wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : Z1w (A := A) t →+ Z1w (A := B) t where
  toFun x := ⟨fun i => φ (x.1 i),
    AddMonoidHom.mem_ker.mpr (d1_ker_map t φ hφ (AddMonoidHom.mem_ker.mp x.2))⟩
  map_zero' := by ext i; simp
  map_add' x y := by ext i; simp

/-- The induced map `H²w(A) →+ H²w(B)`, descended from `(φ, φ) : A × A →+ B × B` through the
`im d¹`-quotient (well-defined by `d1_natural`). -/
noncomputable def H2wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H2w (A := A) t →+ H2w (A := B) t :=
  QuotientAddGroup.map ((d1 (A := A) t).range) ((d1 (A := B) t).range) (φ.prodMap φ) <| by
    rintro z hz
    obtain ⟨x, rfl⟩ := hz
    rw [AddSubgroup.mem_comap]
    exact ⟨fun i => φ (x i), d1_natural t φ hφ x⟩

/-- The induced map `H⁰w(A) →+ H⁰w(B)`: `φ` restricted to the `d⁰`-kernels (`d⁰`-naturality sends
`ker d⁰_A` into `ker d⁰_B`). -/
def H0wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H0w (A := A) t →+ H0w (A := B) t where
  toFun a := ⟨φ a.1, by
    rw [H0w, AddMonoidHom.mem_ker, d0_natural t φ hφ a.1,
      show d0 t a.1 = 0 from AddMonoidHom.mem_ker.mp a.2]
    funext i; simp⟩
  map_zero' := by apply Subtype.ext; simp
  map_add' x y := by apply Subtype.ext; simp

/-- The induced map `H¹w(A) →+ H¹w(B)`, descended from `Z1wMap` through the `B¹w`-quotient
(coboundaries map to coboundaries by `d⁰`-naturality). -/
noncomputable def H1wMap (t : Marking C) (φ : A →+ B)
    (hφ : ∀ (c : C) (a : A), φ (c • a) = c • φ a) : H1w (A := A) t →+ H1w (A := B) t :=
  QuotientAddGroup.map _ _ (Z1wMap t φ hφ) <| by
    rintro z hz
    rw [AddSubgroup.mem_comap, AddSubgroup.mem_addSubgroupOf]
    rw [AddSubgroup.mem_addSubgroupOf] at hz
    obtain ⟨a, ha⟩ := (AddMonoidHom.mem_range).mp hz
    exact (AddMonoidHom.mem_range).mpr ⟨φ a, by
      show d0 t (φ a) = fun i => φ (z.1 i)
      simp only [d0_natural t φ hφ a, ha]⟩

end Functoriality

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

include hsurj in
/-- Degree-1 (`(·)⁴`) surjectivity: `g` applied componentwise is surjective. -/
theorem pi_g_surjective : Function.Surjective (fun (x : Fin 4 → A) (i : Fin 4) => g (x i)) := by
  intro y; choose x hx using fun i => hsurj (y i); exact ⟨x, funext hx⟩

include hexact in
/-- Degree-1 exactness: `ker(g∘·) = range(f∘·)` on `Fin 4 → A`. -/
theorem pi_exact (y : Fin 4 → A) :
    (fun i => g (y i)) = 0 ↔ ∃ x : Fin 4 → A', (fun i => f (x i)) = y := by
  constructor
  · intro hy
    have hmem : ∀ i, y i ∈ f.range := by
      intro i
      rw [hexact, AddMonoidHom.mem_ker]
      exact congrFun hy i
    choose x hx using fun i => (AddMonoidHom.mem_range).mp (hmem i)
    exact ⟨x, funext hx⟩
  · rintro ⟨x, rfl⟩
    funext i
    show g (f (x i)) = 0
    have : f (x i) ∈ g.ker := by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨x i, rfl⟩
    exact AddMonoidHom.mem_ker.mp this

include hsurj in
/-- Degree-2 (`(·)²`) surjectivity: `g × g` is surjective. -/
theorem prod_g_surjective : Function.Surjective (g.prodMap g) := by
  rintro ⟨u, v⟩
  obtain ⟨a, ha⟩ := hsurj u
  obtain ⟨b, hb⟩ := hsurj v
  exact ⟨(a, b), by simp [AddMonoidHom.coe_prodMap, ha, hb]⟩

include hexact in
/-- Degree-2 exactness: `ker(g × g) = range(f × f)` on `A × A`. -/
theorem prod_exact (p : A × A) :
    (g.prodMap g) p = 0 ↔ ∃ q : A' × A', (f.prodMap f) q = p := by
  have hmem : ∀ x : A, x ∈ f.range ↔ g x = 0 := fun x => by
    rw [hexact, AddMonoidHom.mem_ker]
  rw [show (g.prodMap g) p = (g p.1, g p.2) from by rw [AddMonoidHom.coe_prodMap]; rfl,
    Prod.mk_eq_zero]
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨a, ha⟩ := (hmem p.1).mpr h1
    obtain ⟨b, hb⟩ := (hmem p.2).mpr h2
    exact ⟨(a, b), by rw [AddMonoidHom.coe_prodMap]; exact Prod.ext ha hb⟩
  · rintro ⟨q, hq⟩
    rw [AddMonoidHom.coe_prodMap] at hq
    exact ⟨(hmem p.1).mp ⟨q.1, congrArg Prod.fst hq⟩,
      (hmem p.2).mp ⟨q.2, congrArg Prod.snd hq⟩⟩

/-! ### The connecting map `δ¹ : H¹w(A'') → H²w(A')` (snake) -/

include hsurj in
/-- A chosen lift of a degree-1 `A''`-cochain to `A⁴` (via `g` surjective). -/
noncomputable def snakeLift (c'' : Fin 4 → A'') : Fin 4 → A := fun i => (hsurj (c'' i)).choose

include hsurj in
@[simp] theorem snakeLift_spec (c'' : Fin 4 → A'') (i : Fin 4) : g (snakeLift g hsurj c'' i) = c'' i :=
  (hsurj (c'' i)).choose_spec

include hg hsurj in
/-- For a cocycle `c'' ∈ Z¹w(A'')`, `d¹` of its lift lands in `ker(g × g)`. -/
theorem snake_d1_mem (t : Marking C) (c'' : Z1w (A := A'') t) :
    (g.prodMap g) (d1 t (snakeLift g hsurj c''.1)) = 0 := by
  have h1 : d1 t (fun i => g (snakeLift g hsurj c''.1 i))
      = (g.prodMap g) (d1 t (snakeLift g hsurj c''.1)) := by
    rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg (snakeLift g hsurj c''.1)
  rw [← h1, show (fun i => g (snakeLift g hsurj c''.1 i)) = c''.1 from
    funext (snakeLift_spec g hsurj c''.1)]
  exact AddMonoidHom.mem_ker.mp c''.2

include hg hsurj hexact in
/-- The `A'²`-element the snake extracts: `(f × f)(snakeZ) = d¹(lift c'')`. -/
noncomputable def snakeZ (t : Marking C) (c'' : Z1w (A := A'') t) : A' × A' :=
  ((prod_exact f g hexact (d1 t (snakeLift g hsurj c''.1))).mp
    (snake_d1_mem g hg hsurj t c'')).choose

include hg hsurj hexact in
theorem snakeZ_spec (t : Marking C) (c'' : Z1w (A := A'') t) :
    (f.prodMap f) (snakeZ f g hg hsurj hexact t c'') = d1 t (snakeLift g hsurj c''.1) :=
  ((prod_exact f g hexact (d1 t (snakeLift g hsurj c''.1))).mp
    (snake_d1_mem g hg hsurj t c'')).choose_spec

include hf hg hinj hsurj hexact in
/-- **Well-definedness of the snake**: for *any* lift `c` of `c''` and *any* `z` with
`(f×f)(z) = d¹(c)`, the class `[z] ∈ H²w(A')` equals `[snakeZ c'']` — so `δ¹` will not depend on
the chosen lift, hence descends to a hom on `H¹w(A'')`. -/
theorem snakeZ_welldef (t : Marking C) (c'' : Z1w (A := A'') t)
    (c : Fin 4 → A) (z : A' × A') (hc : (fun i => g (c i)) = c''.1)
    (hz : (f.prodMap f) z = d1 t c) :
    (QuotientAddGroup.mk z : H2w (A := A') t)
      = QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  -- `c − snakeLift` maps to `0` under `g`, so it is `f` of some `w : A'⁴`.
  have hker : (fun i => g ((c - snakeLift g hsurj c''.1) i)) = 0 := by
    funext i
    simp only [Pi.sub_apply, map_sub, snakeLift_spec, congrFun hc i, sub_self, Pi.zero_apply]
  obtain ⟨w, hw⟩ := (pi_exact f g hexact (c - snakeLift g hsurj c''.1)).mp hker
  -- `(f×f)(z − snakeZ) = d¹(c) − d¹(snakeLift) = d¹(f∘w) = (f×f)(d¹ w)`, so `z − snakeZ = d¹ w`.
  have hd1w : (f.prodMap f) (d1 t w) = d1 t (c - snakeLift g hsurj c''.1) := by
    rw [show (c - snakeLift g hsurj c''.1) = (fun i => f (w i)) from hw.symm]
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w).symm
  have hzz : (f.prodMap f) (z - snakeZ f g hg hsurj hexact t c'') = (f.prodMap f) (d1 t w) := by
    rw [map_sub, hz, snakeZ_spec, hd1w, map_sub]
  have : z - snakeZ f g hg hsurj hexact t c'' = d1 t w := hfinj hzz
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff]
  exact ⟨w, this.symm⟩

include hf hg hinj hsurj hexact in
/-- The connecting map on cocycles, `Z¹w(A'') →+ H²w(A')`, `c'' ↦ [snakeZ c'']` (a hom by
`snakeZ_welldef`, using additive lifts). -/
noncomputable def delta1raw (t : Marking C) : Z1w (A := A'') t →+ H2w (A := A') t where
  toFun c'' := QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'')
  map_zero' :=
    ((snakeZ_welldef f g hf hg hinj hsurj hexact t 0 0 0
      (by funext i; simp) (by simp only [map_zero])).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' c''₁ c''₂ := by
    refine ((snakeZ_welldef f g hf hg hinj hsurj hexact t (c''₁ + c''₂)
      (snakeLift g hsurj c''₁.1 + snakeLift g hsurj c''₂.1)
      (snakeZ f g hg hsurj hexact t c''₁ + snakeZ f g hg hsurj hexact t c''₂) ?_ ?_).symm).trans
      (QuotientAddGroup.mk_add _ _ _)
    · funext i; simp only [Pi.add_apply, map_add, snakeLift_spec]; rfl
    · rw [map_add, snakeZ_spec, snakeZ_spec, ← map_add]

include hf hg hinj hsurj hexact in
/-- **The snake connecting map** `δ¹ : H¹w(A'') → H²w(A')`.  Descends `delta1raw` through the
`B¹w`-quotient: a coboundary `c'' = d⁰(a'')` lifts to `d⁰(â)`, whose `d¹` is `0`, so its class
is `0`. -/
noncomputable def delta1 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H1w (A := A'') t →+ H2w (A := A') t :=
  QuotientAddGroup.lift _ (delta1raw f g hf hg hinj hsurj hexact t) <| by
    rintro c'' hc''
    rw [AddSubgroup.mem_addSubgroupOf] at hc''
    obtain ⟨a'', ha''⟩ := hc''
    obtain ⟨a, ha⟩ := hsurj a''
    show QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') = 0
    refine ((snakeZ_welldef f g hf hg hinj hsurj hexact t c'' (d0 t a) 0 ?_ ?_).symm).trans
      (QuotientAddGroup.mk_zero _)
    · rw [← d0_natural t g hg a, ha]; exact ha''
    · rw [map_zero]; exact (d1Fun_comp_d0 t ht hw a).symm

/-! ### The connecting map `δ⁰ : H⁰w(A'') → H¹w(A')` (snake)

The mirror of `δ¹` one degree down.  Lift `a'' ∈ H⁰w(A'')` to `a ∈ A`; then `d⁰a ∈ ker(g∘·)`
(as `g∘d⁰a = d⁰(g a) = d⁰a'' = 0`), so `d⁰a = f∘w` for a unique `w : A'⁴`, which is a cocycle
(`f∘d¹w = d¹(f∘w) = d¹d⁰a = 0`, `f` injective).  `δ⁰(a'') := [w] ∈ H¹w(A')`; the class is
independent of the lift `a` (a different lift shifts `w` by a coboundary).  The domain `H⁰w` is an
honest subgroup (no quotient), so — unlike `δ¹` — no descent is needed, only lift-independence. -/

include hg hsurj in
/-- For `a'' ∈ H⁰w(A'')`, `d⁰` of the chosen lift lands in `ker(g∘·)` (degree 1). -/
theorem snake0_d0_mem (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => g (d0 t (hsurj a''.1).choose i)) = 0 := by
  rw [← d0_natural t g hg, (hsurj a''.1).choose_spec]
  exact AddMonoidHom.mem_ker.mp a''.2

include hg hsurj hexact in
/-- The `A'⁴`-cochain the degree-0 snake extracts: `f∘(snake0Z') = d⁰(lift a'')`. -/
noncomputable def snake0Z' (t : Marking C) (a'' : H0w (A := A'') t) : Fin 4 → A' :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp (snake0_d0_mem g hg hsurj t a'')).choose

include hg hsurj hexact in
theorem snake0Z'_spec (t : Marking C) (a'' : H0w (A := A'') t) :
    (fun i => f (snake0Z' f g hg hsurj hexact t a'' i)) = d0 t (hsurj a''.1).choose :=
  ((pi_exact f g hexact (d0 t (hsurj a''.1).choose)).mp (snake0_d0_mem g hg hsurj t a'')).choose_spec

include hf hg hinj hsurj hexact in
/-- `snake0Z' ∈ Z¹w(A')`: its `d¹` vanishes (pull `d¹∘d⁰ = 0` back through the injection `f`). -/
theorem snake0Z'_mem (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) : d1 t (snake0Z' f g hg hsurj hexact t a'') = 0 := by
  have hfinj : Function.Injective (f.prodMap f) := by
    rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
  apply hfinj
  rw [map_zero]
  have hnat : (f.prodMap f) (d1 t (snake0Z' f g hg hsurj hexact t a''))
      = d1 t (fun i => f (snake0Z' f g hg hsurj hexact t a'' i)) := by
    rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf _).symm
  rw [hnat, snake0Z'_spec]
  exact d1Fun_comp_d0 t ht hw _

include hf hg hinj hsurj hexact in
/-- Lift-independence of `δ⁰`: *any* lift `a` of `a''` with cocycle `w` (`f∘w = d⁰a`) gives the
same class `[w] = δ⁰(a'')`.  A second lift differs by `f a'`, shifting `w` by `d⁰a'`. -/
theorem delta0_welldef (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) (a : A) (w : Fin 4 → A') (hwmem : d1 t w = 0)
    (ha : g a = a''.1) (hfw : (fun i => f (w i)) = d0 t a) :
    (QuotientAddGroup.mk ⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ : H1w (A := A') t)
      = QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
          AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ := by
  set w₀ := snake0Z' f g hg hsurj hexact t a'' with hw₀
  -- `a − lift` is in `ker g = range f`.
  have hga : g (a - (hsurj a''.1).choose) = 0 := by
    rw [map_sub, ha, (hsurj a''.1).choose_spec, sub_self]
  obtain ⟨a', ha'⟩ := (AddMonoidHom.mem_range).mp (by rw [hexact]; exact AddMonoidHom.mem_ker.mpr hga)
  -- `f∘(w − w₀) = d⁰a − d⁰(lift) = d⁰(a − lift) = d⁰(f a') = f∘(d⁰a')`, so `w − w₀ = d⁰a'`.
  have hww₀ : (w - w₀ : Fin 4 → A') = d0 t a' := by
    funext i
    apply hinj
    have ex := congrFun (snake0Z'_spec f g hg hsurj hexact t a'') i
    rw [Pi.sub_apply, map_sub, congrFun hfw i, ex, ← congrFun (d0_natural t f hf a') i, ha',
      map_sub, Pi.sub_apply]
  -- Hence the difference of the two cocycles is a coboundary, so the classes agree.
  rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff,
    AddSubgroup.mem_addSubgroupOf]
  refine (AddMonoidHom.mem_range).mpr ⟨a', ?_⟩
  have hcoe : (↑(⟨w, AddMonoidHom.mem_ker.mpr hwmem⟩ - ⟨w₀,
      AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ :
      Z1w (A := A') t) : Fin 4 → A') = w - w₀ := rfl
  rw [hcoe]; exact hww₀.symm

include hf hg hinj hsurj hexact in
/-- **The degree-0 connecting map** `δ⁰ : H⁰w(A'') →+ H¹w(A')`. -/
noncomputable def delta0 (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) :
    H0w (A := A'') t →+ H1w (A := A') t where
  toFun a'' := QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
    AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩
  map_zero' :=
    ((delta0_welldef f g hf hg hinj hsurj hexact t ht hw 0 0 0 (by simp) (by simp)
      (by funext i; simp)).symm).trans (QuotientAddGroup.mk_zero _)
  map_add' x y := by
    refine Eq.trans ?_ (QuotientAddGroup.mk_add _ _ _)
    exact (delta0_welldef f g hf hg hinj hsurj hexact t ht hw (x + y)
      ((hsurj x.1).choose + (hsurj y.1).choose)
      (snake0Z' f g hg hsurj hexact t x + snake0Z' f g hg hsurj hexact t y)
      (by rw [map_add, snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw x,
            snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw y, add_zero])
      (by rw [map_add, (hsurj x.1).choose_spec, (hsurj y.1).choose_spec]; rfl)
      (by funext i
          rw [Pi.add_apply, map_add,
            congrFun (snake0Z'_spec f g hg hsurj hexact t x) i,
            congrFun (snake0Z'_spec f g hg hsurj hexact t y) i, ← Pi.add_apply, ← map_add])).symm

end LES

end GQ2.FoxH
