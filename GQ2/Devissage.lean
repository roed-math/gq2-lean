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

include hsurj hexact

/-- Degree-1 (`(·)⁴`) surjectivity: `g` applied componentwise is surjective. -/
theorem pi_g_surjective : Function.Surjective (fun (x : Fin 4 → A) (i : Fin 4) => g (x i)) := by
  intro y; choose x hx using fun i => hsurj (y i); exact ⟨x, funext hx⟩

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

/-- Degree-2 (`(·)²`) surjectivity: `g × g` is surjective. -/
theorem prod_g_surjective : Function.Surjective (g.prodMap g) := by
  rintro ⟨u, v⟩
  obtain ⟨a, ha⟩ := hsurj u
  obtain ⟨b, hb⟩ := hsurj v
  exact ⟨(a, b), by simp [AddMonoidHom.coe_prodMap, ha, hb]⟩

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

end LES

end GQ2.FoxH
