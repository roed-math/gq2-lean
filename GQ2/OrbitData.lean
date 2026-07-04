import GQ2.QuadraticFp2

/-!
# Orbit-data def-layer for §6  (extracted from `GQ2/SectionSix.lean`)

The factor-set / regular-representation / orbit-datum **definitions** of Lemmas 6.1–6.2
(eqs. (59)–(76)), lifted out of `GQ2/SectionSix.lean` into this lower shared file.

**Why.**  The §6 proof own-files (`GQ2/ShapiroLedger.lean`, and future ones) need these defs to
state and prove their `_aux` lemmas, but must not import `SectionSix` — otherwise splicing an
own-file's proved lemma back into `SectionSix`
(`lemma_6_15_free := ShapiroLedger.lemma_6_15_free_aux …`) is a **circular import**.  Placing the
def-layer here, in the **top-level `namespace GQ2`** (not `GQ2.SectionSix`), lets both
`SectionSix` and the own-files reach the names unqualified with no per-file edits (they are all in
`namespace GQ2`).  See `docs/orbit-data-refactor.md`.

Moved verbatim from `SectionSix`.  No axioms; `Ax = ∅`.
-/

namespace GQ2

open QuadraticFp2

/-! ## Factor-set data  (Lemma 6.1, eqs. (59)–(62)) -/

section FactorSets

variable (C V : Type*) [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- **Factor-set datum** for a `C`-module `V` (Lemma 6.1): a normalized factor set `f` together
with the central corrections `m_c` of a chosen equivariant lift.  The defining identities
(59)/(60) and the compatibility with a quadratic form `q` are the Prop bundle
`IsEquivariantFactorSet` below. -/
structure FactorSet where
  /-- The normalized factor set `f : V × V → 𝔽₂`. -/
  f : V → V → ZMod 2
  /-- The equivariant-lift corrections `m_c : V → 𝔽₂` (eq. (59)/(60)). -/
  m : C → V → ZMod 2

variable {C V}

/-- The identities making `(f, m)` an **equivariant factor-set datum for `q`** (Lemma 6.1):
`f` has square map `q` and polar form `B_q`, is normalized, and `m` satisfies (59)/(60) with
`m_1 = 0`. -/
structure IsEquivariantFactorSet (q : V → ZMod 2) (dat : FactorSet C V) : Prop where
  /-- `f` is a genuine **factor set**: the (trivial-action, additive) 2-cocycle identity on `V`
  — the associativity of the central extension `E_f` (Lemma 6.1's "normalized factor set").
  [Field added in the P-15 pass: caught by proving `graphPullback_mem_Z2`, which is false
  without it; all of the paper's concrete factor sets ((75)/(76)/(73)/(95)) are bilinear in the
  coordinates, hence satisfy it.  Deviation ledger updated.] -/
  f_cocycle : ∀ v w x, dat.f (v + w) x + dat.f v w = dat.f v (w + x) + dat.f w x
  f_diag : ∀ v, dat.f v v = q v
  f_polar : ∀ v w, dat.f v w + dat.f w v = polar q v w
  f_zero_left : ∀ v, dat.f 0 v = 0
  f_zero_right : ∀ v, dat.f v 0 = 0
  /-- Eq. (59): `m_c(v+w) + m_c(v) + m_c(w) = f(cv, cw) + f(v, w)`. -/
  m_quad : ∀ (c : C) (v w : V),
    dat.m c (v + w) + dat.m c v + dat.m c w = dat.f (c • v) (c • w) + dat.f v w
  /-- Eq. (60): `m_{cd}(v) = m_c(dv) + m_d(v)`. -/
  m_mul : ∀ (c d : C) (v : V), dat.m (c * d) v = dat.m c (d • v) + dat.m d v
  /-- Eq. (60): `m_1 = 0`. -/
  m_one : ∀ v, dat.m 1 v = 0

/-- The **base central cocycle** `κ⁰_q` on `V ⋊ C` (eq. (61)):
`κ⁰((v,c),(w,d)) = f(v, c·w) + m_c(w)`, as a raw function on pairs. -/
def kappa0 (dat : FactorSet C V) : (V × C) → (V × C) → ZMod 2 :=
  fun p q ↦ dat.f p.1 (p.2 • q.1) + dat.m p.2 q.1

/-- The **graph pullback** `(b, ρ)^* κ⁰_q` (eq. (62)) along a lower map `ρ : Γ → C` and a
1-cochain `b : Γ → V`: `(g, h) ↦ f(b(g), ρ(g)·b(h)) + m_{ρ(g)}(b(h))`.  This is the only form
in which the base class enters the §6 statements. -/
def graphPullback {Γ : Type*} (dat : FactorSet C V) (ρ : Γ → C) (b : Γ → V) :
    Γ × Γ → ZMod 2 :=
  fun p ↦ dat.f (b p.1) (ρ p.1 • b p.2) + dat.m (ρ p.1) (b p.2)

/-- Pullback of a factor-set datum along an equivariant additive map `i : V →+ W`
(the `(i ⋊ 1)^*` of eq. (77), datum level). -/
def FactorSet.comap {W : Type*} [AddCommGroup W] [DistribMulAction C W]
    (dat : FactorSet C W) (i : V →+ W) : FactorSet C V where
  f v w := dat.f (i v) (i w)
  m c v := dat.m c (i v)

end FactorSets

/-! ## The regular representation and orbit data  (Lemma 6.2, eqs. (67)–(76))

`RegRep`/`*OrbitDatum` need only `[Group G] [N.Normal]` (the topological/`DistribMulAction G 𝔽₂`
context that surrounds them in `SectionSix` is not used by the defs themselves). -/

section OrbitData

variable {G : Type*} [Group G]
variable (N : Subgroup G) [N.Normal]

/-- The regular permutation module `𝔽₂[G/N]` (coordinates `X_h`, `h ∈ G/N`), as a type synonym
carrying the left-regular action `(c·x)_h = x_{c⁻¹h}` (Lemma 6.2's convention). -/
def RegRep : Type _ := (G ⧸ N) → ZMod 2

instance : AddCommGroup (RegRep N) := inferInstanceAs (AddCommGroup ((G ⧸ N) → ZMod 2))

/-- The left-regular action on `𝔽₂[G/N]`. -/
instance : DistribMulAction (G ⧸ N) (RegRep N) where
  smul c x := fun h ↦ x (c⁻¹ * h)
  one_smul x := by funext h; show x _ = x h; rw [inv_one, one_mul]
  mul_smul c d x := by funext h; show x _ = x _; rw [mul_inv_rev, mul_assoc]
  smul_zero c := rfl
  smul_add c x y := rfl

/-- The **square-orbit datum** `S` (eq. (75)): `f(x,y) = Σ_h x_h y_h`, `m = 0`. -/
noncomputable def squareOrbitDatum : FactorSet (G ⧸ N) (RegRep N) where
  f x y := ∑ᶠ h : G ⧸ N, x h * y h
  m _ _ := 0

/-- The **free-orbit datum** `C_{j,k,ḡ}` (eq. (76)) on two regular summands with shift `ḡ`:
`f((x,x'),(y,y')) = Σ_h x_h y'_{hḡ}`, `m = 0`. -/
noncomputable def freeOrbitDatum (gbar : G ⧸ N) : FactorSet (G ⧸ N) (RegRep N × RegRep N) where
  f x y := ∑ᶠ h : G ⧸ N, x.1 h * y.2 (h * gbar)
  m _ _ := 0

open scoped Classical in
/-- The **involution-orbit datum** `E_ḡ` (Lemma 6.2, eqs. (67)–(70)) for an involution
`ḡ ∈ G/N`: with `R` the canonical transversal of the `⟨ḡ⟩`-cosets,
`f_g(x,y) = Σ_{u∈R} x_u y_{uḡ}` and `m^g_c(x) = Σ_{u∈R} ε_c(u)·x_{π_c(u)} x_{π_c(u)ḡ}`
(orientation bookkeeping (67) via the canonical representatives). -/
noncomputable def invOrbitDatum (gbar : G ⧸ N) : FactorSet (G ⧸ N) (RegRep N) where
  f x y := ∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers gbar, x u.out * y (u.out * gbar)
  m c x := ∑ᶠ u : (G ⧸ N) ⧸ Subgroup.zpowers gbar,
    (if c⁻¹ * u.out = ((c⁻¹ * u.out : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers gbar).out
      then 0 else 1) *
      (x ((c⁻¹ * u.out : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers gbar).out *
        x ((((c⁻¹ * u.out : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers gbar).out) * gbar))

end OrbitData

end GQ2
