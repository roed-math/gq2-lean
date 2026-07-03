import Mathlib

/-!
# Quadratic maps to `𝔽₂` on finite elementary abelian `2`-groups  (ticket P-14 def-layer)

The paper's §6 determinant obstructions are quadratic maps `q : V → 𝔽₂` on finite elementary
abelian `2`-groups (equivalently `𝔽₂`-vector spaces), with their **polar forms**
`B(v,w) = q(v+w) + q(v) + q(w)`, **nonsingularity** (trivial polar radical), the **Arf
invariant**, and the **Wall doubling** `q_U(x) = q(x) + B(x, U⁻¹x) = q(x) + B(x, Ux)` of an
orthogonal operator `U` (char 2: `U⁻¹x` and `Ux` give the same doubling since `B` is
`U`-invariant; we take the paper's (83) shape directly).

**Encoding decisions** (`docs/section67-extraction.md` §D1):

* Modules are the project's plain classes (`[AddCommGroup V]` + a `Prop` for exponent 2 where
  needed) — no `Module (ZMod 2)` bundling, matching `GQ2/DiscreteModule.lean`'s conventions.
  Quadratic maps are **plain functions** `q : V → ZMod 2` with the predicate `IsQuadraticFp2`
  (normalization + biadditive polar), mirroring how `GQ2/Cohomology.lean` treats cochains.
* **`arf` is the democratic (majority) invariant** (Browder): `arf q = 0` iff the zeros of `q`
  are the strict majority.  For a *nonsingular* form on a finite even-dimensional space this
  agrees with the classical Arf invariant (`#q⁻¹(0) = 2^{d−1} + (−1)^{arf} 2^{d/2−1}`), and it is
  the only reading §§6–9 consume (the base determinant **Gauss sums** of Props 6.9/6.18).
  Mathlib has no Arf invariant; this definition is total and choice-free.  **Deviation flagged**
  in the extraction note.

No `sorry` in this file — everything here is definitional or elementary.
-/

namespace GQ2

namespace QuadraticFp2

variable {V : Type*} [AddCommGroup V]

/-- The **polar form** of `q : V → 𝔽₂`: `B(v,w) = q(v+w) + q(v) + q(w)`. -/
def polar (q : V → ZMod 2) (v w : V) : ZMod 2 := q (v + w) + q v + q w

/-- `q` is a **quadratic map to `𝔽₂`**: it is normalized (`q 0 = 0`) and its polar form is
biadditive.  (Over `𝔽₂` there is no scalar condition; on an exponent-2 group this is the standard
notion of a quadratic form, cf. paper §6 and Serre CiA.) -/
structure IsQuadraticFp2 (q : V → ZMod 2) : Prop where
  map_zero : q 0 = 0
  polar_add_left : ∀ u v w : V, polar q (u + v) w = polar q u w + polar q v w
  polar_add_right : ∀ u v w : V, polar q u (v + w) = polar q u v + polar q u w

/-- The polar form is symmetric (immediately from commutativity of `+`). -/
theorem polar_comm (q : V → ZMod 2) (v w : V) : polar q v w = polar q w v := by
  unfold polar
  rw [add_comm v w]
  ring

/-- Polarization at equal arguments computes `q(2v)`; on an exponent-2 group it vanishes, i.e.
the polar form is **alternating** (`B(v,v) = 0`), because `q(2v) = q(0) = 0`. -/
theorem polar_self (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0) (v : V) :
    polar q v v = 0 := by
  unfold polar
  rw [h2 v, hq.map_zero, zero_add]
  exact CharTwo.add_self_eq_zero _

/-- **Nonsingularity**: the polar radical is trivial — every nonzero vector pairs nontrivially
with something.  (For finite `V` this is the paper's nondegeneracy; no dual-space bundling.) -/
def Nonsingular (q : V → ZMod 2) : Prop :=
  ∀ v : V, v ≠ 0 → ∃ w : V, polar q v w ≠ 0

/-- **Invariance** of `q` under an action of `C` on `V`. -/
def IsInvariant (C : Type*) [SMul C V] (q : V → ZMod 2) : Prop :=
  ∀ (c : C) (v : V), q (c • v) = q v

/-- The **zero count** `#q⁻¹(0)` of a form on a finite group — the (unsigned) content of the
paper's base determinant Gauss sums (Props 6.9/6.18, eqs. (91)/(115)). -/
noncomputable def zeroCount (q : V → ZMod 2) : ℕ := Nat.card {v : V // q v = 0}

/-- The **Arf invariant**, democratically (Browder): `0` iff the zeros form a strict majority.
Agrees with the classical Arf invariant for nonsingular forms on finite even-dimensional spaces
(where `#q⁻¹(0) = 2^{d−1} ± 2^{d/2−1} ≠ 2^{d−1}`); total and choice-free in general. -/
noncomputable def arf (q : V → ZMod 2) : ZMod 2 :=
  if 2 * zeroCount q > Nat.card V then 0 else 1

/-- The **Wall doubling** of `q` by an operator `U : V → V` (paper Lemma 6.6 and eq. (83)):
`q_U(x) = q(x) + B(x, Ux)`.  (Char 2, `B` `U`-invariant: same as the paper's `B(x, U⁻¹x)`.) -/
def qDouble (q : V → ZMod 2) (U : V → V) (x : V) : ZMod 2 := q x + polar q x (U x)

@[simp] theorem qDouble_id_of_alternating (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (x : V) : qDouble q id x = q x := by
  rw [qDouble, id, polar_self q hq h2, add_zero]

/-- Doubling by the identity operator written as `U = 1` on `AddAut`-style operators: with
`U x = x` the doubling term is `B(x,x) = 0`. -/
theorem qDouble_of_fixed (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (h2 : ∀ v : V, v + v = 0)
    {U : V → V} (hU : ∀ x, U x = x) (x : V) : qDouble q U x = q x := by
  rw [qDouble, hU, polar_self q hq h2, add_zero]

end QuadraticFp2

end GQ2
