/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.KappaNormalForm
import GQ2.OrbitVanish

/-!
# P-15f2b: the §6.2 orbit-sum decomposition on a multi-block regular module

The **orbit decomposition** of a `(G/N)`-invariant quadratic map `Q` on the block module
`𝔽₂[G/N]^K = Fin K → RegRep N` into the paper's three orbit-polynomial types
((75)/(76)/Lemma 6.2): the equivariant factor-set datum for `Q` is the `sumDatum` of

* **square** summands `(squareOrbitDatum N).comap (blockProj j)` — one per block `j` with
  `Q(e_{j,1}) = 1`;
* **involution** summands `(invOrbitDatum N ū).comap (blockProj j)` — one per block-involution
  position `(j, ū)` (`ū² = 1 ≠ ū`) with polar coordinate `1`;
* **free** summands `(freeOrbitDatum N ū).comap (blockProj₂ j k)` — one per chosen orientation
  representative of the swap-orbit `{(j,k,ū), (k,j,ū⁻¹)}` with polar coordinate `1` (the
  same-block case `j = k` uses the non-injective pair projection).

Every summand is a **definitional `FactorSet.comap` of a literal `OrbitData` datum**, so the
per-orbit graph pullbacks are *syntactically* the Lemma-6.15 inputs
(`SectionSix.lemma_6_15_square/free/involution`) at the block coordinates of the cocycle — no
per-orbit datum bridging is needed downstream (P-15f2c).

This is the remaining clause of the P-15f2b interface (`docs/p15f2b-foundation-notes.md`); the
banked normal form `exists_datum_of_invariant_quadratic` (P-17e5) deliberately took the
non-orbit-decomposed single-β route and cannot supply it.  Layer plan:

* **Carrier layer**: the coordinate basis `blockBas`, its translation action, and the support
  decomposition (mirrors `permBas`/`permBas_support_decomp` on `PermW`).
* **Coordinate layer**: the diagonal/relative-position coordinates `blockDiag`/`blockPolar` of an
  invariant `Q` and their invariance reductions (mirrors the `have`-blocks of
  `exists_datum_of_invariant_quadratic`).
* **Orientation layer**: the swap `posSwap` on positions, the free/involution classification,
  and the orientation transversal `freeReps` (a noncomputable linear order picks one
  representative per free swap-orbit; the order never appears in any statement).
* **Summand layer** (§6.2): the three block datums, their equivariance, and their basis
  diagonal/polar evaluations.
* **Assembly**: the matching of basis coordinates and the capstone
  `IsEquivariantFactorSet Q (sumDatum … orbitDatum)` over an abstract pair `(G, N)`.

Galois-free: everything is finite group theory over `(G, N)`, `[Finite (G ⧸ N)]`.
No axioms; `Ax = ∅` (std-3 throughout).
-/

namespace GQ2

open QuadraticFp2
open scoped Classical

private theorem zmod2_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

/-! ## The carrier `𝔽₂[G/N]^K` and its coordinate basis -/

section BlockBasis

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {K : ℕ}

/-- The single-coordinate indicator of the regular module `𝔽₂[G/N]`. -/
noncomputable def regInd (y : G ⧸ N) : RegRep N :=
  fun h => if h = y then 1 else 0

omit [N.Normal] in
theorem regInd_apply (y h : G ⧸ N) : regInd N y h = if h = y then (1 : ZMod 2) else 0 := rfl

/-- Left translation carries indicators to indicators: `c • e_y = e_{c·y}`. -/
theorem regInd_smul (c y : G ⧸ N) : c • regInd N y = regInd N (c * y) := by
  funext h
  show (if c⁻¹ * h = y then (1 : ZMod 2) else 0) = if h = c * y then 1 else 0
  refine if_congr ?_ rfl rfl
  exact inv_mul_eq_iff_eq_mul

/-- The `(j, y)`-coordinate basis vector of the block module `𝔽₂[G/N]^K`. -/
noncomputable def blockBas (j : Fin K) (y : G ⧸ N) : Fin K → RegRep N :=
  fun i => if i = j then regInd N y else 0

omit [N.Normal] in
theorem blockBas_apply (j : Fin K) (y : G ⧸ N) (i : Fin K) (h : G ⧸ N) :
    blockBas N j y i h = if i = j ∧ h = y then (1 : ZMod 2) else 0 := by
  by_cases hij : i = j
  · show (if i = j then regInd N y else 0) h = _
    rw [if_pos hij, regInd_apply]
    refine if_congr ?_ rfl rfl
    exact (and_iff_right hij).symm
  · show (if i = j then regInd N y else 0) h = _
    rw [if_neg hij, if_neg (fun hc => hij hc.1)]
    rfl

/-- Left translation on the block module carries basis vectors to basis vectors:
`c • e_{(j,y)} = e_{(j,cy)}`. -/
theorem blockBas_smul (c : G ⧸ N) (j : Fin K) (y : G ⧸ N) :
    c • blockBas N j y = blockBas N j (c * y) := by
  funext i
  show c • (if i = j then regInd N y else 0) = if i = j then regInd N (c * y) else 0
  by_cases hij : i = j
  · rw [if_pos hij, if_pos hij, regInd_smul]
  · rw [if_neg hij, if_neg hij, smul_zero]

omit [N.Normal] in
/-- Pointwise evaluation of a finite sum in `RegRep N`. -/
theorem regRep_sum_apply {ι : Type*} (s : Finset ι) (f : ι → RegRep N) (h : G ⧸ N) :
    (∑ o ∈ s, f o) h = ∑ o ∈ s, f o h := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | @insert b s' hb IH =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← IH]
    rfl

omit [N.Normal] in
/-- Blockwise evaluation of a finite sum in the block module. -/
theorem block_sum_apply {ι : Type*} (s : Finset ι) (f : ι → (Fin K → RegRep N)) (i : Fin K) :
    (∑ o ∈ s, f o) i = ∑ o ∈ s, f o i := by
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty, Finset.sum_empty]; rfl
  | @insert b s' hb IH =>
    rw [Finset.sum_insert hb, Finset.sum_insert hb, ← IH]
    rfl

omit [N.Normal] in
/-- Every element of the block module is the sum of the basis vectors at its support
(mirrors `permBas_support_decomp`). -/
theorem blockBas_support_decomp [Fintype (G ⧸ N)] (F : Fin K → RegRep N) :
    F = ∑ p ∈ Finset.univ.filter (fun p : Fin K × (G ⧸ N) => F p.1 p.2 = 1),
      blockBas N p.1 p.2 := by
  funext i h
  have happ : (∑ p ∈ Finset.univ.filter (fun p : Fin K × (G ⧸ N) => F p.1 p.2 = 1),
      blockBas N p.1 p.2) i h
      = ∑ p ∈ Finset.univ.filter (fun p : Fin K × (G ⧸ N) => F p.1 p.2 = 1),
          blockBas N p.1 p.2 i h := by
    rw [block_sum_apply]
    exact regRep_sum_apply N _ _ h
  rw [happ]
  have hterm : ∀ p : Fin K × (G ⧸ N),
      blockBas N p.1 p.2 i h = if p = (i, h) then (1 : ZMod 2) else 0 := by
    intro p
    rw [blockBas_apply]
    refine if_congr ?_ rfl rfl
    constructor
    · rintro ⟨h1, h2⟩
      exact Prod.ext h1.symm h2.symm
    · rintro rfl
      exact ⟨rfl, rfl⟩
  rw [Finset.sum_congr rfl fun p _ => hterm p,
    Finset.sum_ite_eq' _ (i, h) (fun _ => (1 : ZMod 2))]
  by_cases hmem : (i, h) ∈ Finset.univ.filter (fun p : Fin K × (G ⧸ N) => F p.1 p.2 = 1)
  · rw [if_pos hmem]
    rw [Finset.mem_filter] at hmem
    exact hmem.2
  · rw [if_neg hmem]
    rw [Finset.mem_filter] at hmem
    rcases zmod2_cases (F i h) with h0 | h1
    · exact h0
    · exact absurd ⟨Finset.mem_univ _, h1⟩ hmem

end BlockBasis

/-! ## Coordinates of an invariant quadratic map -/

section Coordinates

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {K : ℕ}

/-- The **diagonal coordinate** of `Q` on block `j` (the basis diagonal is constant along each
block by invariance). -/
noncomputable def blockDiag (Q : (Fin K → RegRep N) → ZMod 2) (j : Fin K) : ZMod 2 :=
  Q (blockBas N j 1)

/-- The **relative-position polar coordinate** of `Q` between blocks `j, k` at relative
position `u` (all basis polar values reduce to these by invariance). -/
noncomputable def blockPolar (Q : (Fin K → RegRep N) → ZMod 2) (j k : Fin K) (u : G ⧸ N) :
    ZMod 2 :=
  polar Q (blockBas N j 1) (blockBas N k u)

/-- Polar invariance under the simultaneous action, for any invariant map. -/
theorem polar_smul_invariant {Q : (Fin K → RegRep N) → ZMod 2}
    (hinv : IsInvariant (G ⧸ N) Q) (c : G ⧸ N) (v w : Fin K → RegRep N) :
    polar Q (c • v) (c • w) = polar Q v w := by
  simp only [polar]
  rw [← smul_add, hinv, hinv, hinv]

/-- Diagonal orbit-constancy: `Q(e_{j,x}) = Q(e_{j,1})`. -/
theorem q_blockBas_eq {Q : (Fin K → RegRep N) → ZMod 2} (hinv : IsInvariant (G ⧸ N) Q)
    (j : Fin K) (x : G ⧸ N) : Q (blockBas N j x) = blockDiag N Q j := by
  have h1 : blockBas N j x = x • blockBas N j 1 := by rw [blockBas_smul, mul_one]
  rw [h1, hinv]
  rfl

/-- Polar coordinates in relative position: `B_Q(e_{j,x}, e_{k,y}) = β_{j,k}(x⁻¹y)`. -/
theorem polar_blockBas_eq {Q : (Fin K → RegRep N) → ZMod 2} (hinv : IsInvariant (G ⧸ N) Q)
    (j k : Fin K) (x y : G ⧸ N) :
    polar Q (blockBas N j x) (blockBas N k y) = blockPolar N Q j k (x⁻¹ * y) := by
  have h1 : blockBas N j 1 = x⁻¹ • blockBas N j x := by rw [blockBas_smul, inv_mul_cancel]
  have h2 : blockBas N k (x⁻¹ * y) = x⁻¹ • blockBas N k y := by rw [blockBas_smul]
  show _ = polar Q (blockBas N j 1) (blockBas N k (x⁻¹ * y))
  rw [h1, h2]
  exact (polar_smul_invariant N hinv x⁻¹ _ _).symm

/-- β-symmetry: `β_{j,k}(u) = β_{k,j}(u⁻¹)` (polar symmetry + invariance). -/
theorem blockPolar_symm {Q : (Fin K → RegRep N) → ZMod 2} (hinv : IsInvariant (G ⧸ N) Q)
    (j k : Fin K) (u : G ⧸ N) : blockPolar N Q j k u = blockPolar N Q k j u⁻¹ := by
  show polar Q (blockBas N j 1) (blockBas N k u) = _
  rw [polar_comm, polar_blockBas_eq N hinv k j u 1, mul_one]

end Coordinates

/-! ## Position classification and the swap -/

section Positions

variable {Γ : Type*} [Group Γ] {K : ℕ}

/-- The **swap** on relative positions: `(j, k, u) ↦ (k, j, u⁻¹)` (the two orders of an
unordered coordinate-pair orbit). -/
def posSwap (p : Fin K × Fin K × Γ) : Fin K × Fin K × Γ :=
  (p.2.1, p.1, p.2.2⁻¹)

theorem posSwap_posSwap (p : Fin K × Fin K × Γ) : posSwap (posSwap p) = p := by
  show (p.1, p.2.1, p.2.2⁻¹⁻¹) = p
  rw [inv_inv]

/-- A **free position**: distinct blocks, or same-block relative position of order `> 2`.
(The complements are the diagonal `(j,j,1)` and the involution positions `(j,j,u)`, `u² = 1 ≠ u`.) -/
def IsFreePos (p : Fin K × Fin K × Γ) : Prop :=
  p.1 ≠ p.2.1 ∨ p.2.2 * p.2.2 ≠ 1

theorem isFreePos_posSwap {p : Fin K × Fin K × Γ} (h : IsFreePos p) : IsFreePos (posSwap p) := by
  rcases h with h | h
  · exact Or.inl (Ne.symm h)
  · refine Or.inr ?_
    show p.2.2⁻¹ * p.2.2⁻¹ ≠ 1
    intro hc
    rw [← mul_inv_rev, inv_eq_one] at hc
    exact h hc

/-- The swap moves every free position (fixed points are exactly the involution positions and
the diagonal). -/
theorem posSwap_ne_self {p : Fin K × Fin K × Γ} (h : IsFreePos p) : posSwap p ≠ p := by
  intro hc
  rcases h with h | h
  · exact h (congrArg Prod.fst hc).symm
  · have h3 : p.2.2⁻¹ = p.2.2 := congrArg (fun q : Fin K × Fin K × Γ => q.2.2) hc
    apply h
    calc p.2.2 * p.2.2 = p.2.2⁻¹ * p.2.2 := by rw [h3]
      _ = 1 := inv_mul_cancel _

/-- A noncomputable linear order on the position type, used only to orient the free swap-pairs
(never appears in a statement). -/
@[reducible] noncomputable def posOrder [Fintype Γ] : LinearOrder (Fin K × Fin K × Γ) :=
  LinearOrder.lift' (Fintype.equivFin (Fin K × Fin K × Γ)) (Equiv.injective _)

end Positions

/-! ## The free-pair orientation transversal -/

section Orientation

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {K : ℕ} [Fintype (G ⧸ N)]

/-- The **orientation transversal**: one representative per free swap-orbit with polar
coordinate `1`.  The choice is made by the (hidden) linear order `posOrder`; consumers use only
the three lemmas below, which never mention the order. -/
noncomputable def freeReps (Q : (Fin K → RegRep N) → ZMod 2) :
    Finset (Fin K × Fin K × (G ⧸ N)) :=
  letI := posOrder (Γ := G ⧸ N) (K := K)
  Finset.univ.filter fun p =>
    IsFreePos p ∧ blockPolar N Q p.1 p.2.1 p.2.2 = 1 ∧ p < posSwap p

theorem mem_freeReps_isFree {Q : (Fin K → RegRep N) → ZMod 2}
    {p : Fin K × Fin K × (G ⧸ N)} (hp : p ∈ freeReps N Q) :
    IsFreePos p ∧ blockPolar N Q p.1 p.2.1 p.2.2 = 1 := by
  letI := posOrder (Γ := G ⧸ N) (K := K)
  have := Finset.mem_filter.mp hp
  exact ⟨this.2.1, this.2.2.1⟩

/-- Every free position with polar coordinate `1` is covered: itself or its swap is the chosen
representative. -/
theorem mem_freeReps_or_swap {Q : (Fin K → RegRep N) → ZMod 2}
    (hinv : IsInvariant (G ⧸ N) Q) {p : Fin K × Fin K × (G ⧸ N)}
    (hfree : IsFreePos p) (hβ : blockPolar N Q p.1 p.2.1 p.2.2 = 1) :
    p ∈ freeReps N Q ∨ posSwap p ∈ freeReps N Q := by
  letI := posOrder (Γ := G ⧸ N) (K := K)
  have hβ' : blockPolar N Q (posSwap p).1 (posSwap p).2.1 (posSwap p).2.2 = 1 := by
    show blockPolar N Q p.2.1 p.1 p.2.2⁻¹ = 1
    rw [← blockPolar_symm N hinv]
    exact hβ
  rcases lt_or_gt_of_ne (Ne.symm (posSwap_ne_self hfree)) with hlt | hgt
  · exact Or.inl (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfree, hβ, hlt⟩)
  · refine Or.inr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isFreePos_posSwap hfree, hβ', ?_⟩)
    rw [posSwap_posSwap]
    exact hgt

/-- The transversal is exclusive: never both a position and its swap. -/
theorem not_mem_freeReps_both {Q : (Fin K → RegRep N) → ZMod 2}
    {p : Fin K × Fin K × (G ⧸ N)} :
    ¬(p ∈ freeReps N Q ∧ posSwap p ∈ freeReps N Q) := by
  letI := posOrder (Γ := G ⧸ N) (K := K)
  rintro ⟨h1, h2⟩
  have hlt1 : p < posSwap p := (Finset.mem_filter.mp h1).2.2.2
  have hlt2 : posSwap p < posSwap (posSwap p) := (Finset.mem_filter.mp h2).2.2.2
  rw [posSwap_posSwap] at hlt2
  exact lt_asymm hlt1 hlt2

end Orientation

/-! ## The three §6.2 orbit summands on the block module

Each summand is a **definitional `FactorSet.comap` of a literal `OrbitData` datum** along a block
projection, so downstream graph pullbacks are syntactically the Lemma-6.15 inputs at the block
coordinates of the cocycle. -/

section Summands

variable {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {K : ℕ} [Finite (G ⧸ N)]

omit [N.Normal] [Finite (G ⧸ N)] in
private theorem zmod2_sq_add (a b : ZMod 2) : (a + b) * (a + b) = a * a + b * b := by
  revert a b; decide

/-- The block projection as an additive map. -/
def blockProj (j : Fin K) : (Fin K → RegRep N) →+ RegRep N where
  toFun F := F j
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The ordered-pair block projection (`j = k` allowed). -/
def blockProj₂ (j k : Fin K) : (Fin K → RegRep N) →+ RegRep N × RegRep N where
  toFun F := (F j, F k)
  map_zero' := rfl
  map_add' _ _ := rfl

theorem blockProj_smul (j : Fin K) (c : G ⧸ N) (F : Fin K → RegRep N) :
    blockProj N j (c • F) = c • blockProj N j F := rfl

theorem blockProj₂_smul (j k : Fin K) (c : G ⧸ N) (F : Fin K → RegRep N) :
    blockProj₂ N j k (c • F) = c • blockProj₂ N j k F := rfl

/-- **Square summand** (eq. (75)): the square-orbit datum on block `j`, extended by zero. -/
noncomputable def squareBlockDatum (j : Fin K) : FactorSet (G ⧸ N) (Fin K → RegRep N) :=
  (squareOrbitDatum N).comap (blockProj N j)

/-- **Free summand** (eq. (76)): the free-orbit datum with shift `u` between blocks `j, k`
(possibly equal — the same-block case comaps along the diagonal pair projection). -/
noncomputable def freeBlockDatum (j k : Fin K) (u : G ⧸ N) :
    FactorSet (G ⧸ N) (Fin K → RegRep N) :=
  (freeOrbitDatum N u).comap (blockProj₂ N j k)

/-- **Involution summand** (Lemma 6.2): the involution-orbit datum at `u` on block `j`,
extended by zero. -/
noncomputable def invBlockDatum (j : Fin K) (u : G ⧸ N) :
    FactorSet (G ⧸ N) (Fin K → RegRep N) :=
  (invOrbitDatum N u).comap (blockProj N j)

/-- The square map of the square summand. -/
noncomputable def squareBlockMap (j : Fin K) : (Fin K → RegRep N) → ZMod 2 :=
  fun F => ∑ᶠ h : G ⧸ N, F j h * F j h

/-- The square map of the free summand. -/
noncomputable def freeBlockMap (j k : Fin K) (u : G ⧸ N) : (Fin K → RegRep N) → ZMod 2 :=
  fun F => ∑ᶠ h : G ⧸ N, F j h * F k (h * u)

/-- The square map of the involution summand. -/
noncomputable def invBlockMap (j : Fin K) (u : G ⧸ N) : (Fin K → RegRep N) → ZMod 2 :=
  fun F => ∑ᶠ w : (G ⧸ N) ⧸ Subgroup.zpowers u, F j w.out * F j (w.out * u)

/-! ### Equivariance of the three summands -/

private theorem sq_f_add_left (x x' y : RegRep N) :
    (squareOrbitDatum N).f (x + x') y
      = (squareOrbitDatum N).f x y + (squareOrbitDatum N).f x' y := by
  show ∑ᶠ h : G ⧸ N, (x h + x' h) * y h
      = (∑ᶠ h : G ⧸ N, x h * y h) + ∑ᶠ h : G ⧸ N, x' h * y h
  simp only [add_mul]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

private theorem sq_f_add_right (x y y' : RegRep N) :
    (squareOrbitDatum N).f x (y + y')
      = (squareOrbitDatum N).f x y + (squareOrbitDatum N).f x y' := by
  show ∑ᶠ h : G ⧸ N, x h * (y h + y' h)
      = (∑ᶠ h : G ⧸ N, x h * y h) + ∑ᶠ h : G ⧸ N, x h * y' h
  simp only [mul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

private theorem isEqFS_squareOrbitDatum :
    IsEquivariantFactorSet (fun x : RegRep N => ∑ᶠ h : G ⧸ N, x h * x h)
      (squareOrbitDatum N) := by
  refine datum_of_biadditive_invariant (sq_f_add_left N) (sq_f_add_right N) (fun v => rfl) ?_
  intro c x y
  show ∑ᶠ h : G ⧸ N, x (c⁻¹ * h) * y (c⁻¹ * h) = ∑ᶠ h : G ⧸ N, x h * y h
  exact finsum_comp_equiv (Equiv.mulLeft c⁻¹) (f := fun h => x h * y h)

private theorem free_f_add_left (u : G ⧸ N) (x x' y : RegRep N × RegRep N) :
    (freeOrbitDatum N u).f (x + x') y
      = (freeOrbitDatum N u).f x y + (freeOrbitDatum N u).f x' y := by
  show ∑ᶠ h : G ⧸ N, (x.1 h + x'.1 h) * y.2 (h * u)
      = (∑ᶠ h : G ⧸ N, x.1 h * y.2 (h * u)) + ∑ᶠ h : G ⧸ N, x'.1 h * y.2 (h * u)
  simp only [add_mul]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

private theorem free_f_add_right (u : G ⧸ N) (x y y' : RegRep N × RegRep N) :
    (freeOrbitDatum N u).f x (y + y')
      = (freeOrbitDatum N u).f x y + (freeOrbitDatum N u).f x y' := by
  show ∑ᶠ h : G ⧸ N, x.1 h * (y.2 (h * u) + y'.2 (h * u))
      = (∑ᶠ h : G ⧸ N, x.1 h * y.2 (h * u)) + ∑ᶠ h : G ⧸ N, x.1 h * y'.2 (h * u)
  simp only [mul_add]
  exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)

private theorem isEqFS_freeOrbitDatum (u : G ⧸ N) :
    IsEquivariantFactorSet
      (fun x : RegRep N × RegRep N => ∑ᶠ h : G ⧸ N, x.1 h * x.2 (h * u))
      (freeOrbitDatum N u) := by
  refine datum_of_biadditive_invariant (free_f_add_left N u) (free_f_add_right N u)
    (fun v => rfl) ?_
  intro c v w
  show ∑ᶠ h : G ⧸ N, v.1 (c⁻¹ * h) * w.2 (c⁻¹ * (h * u))
      = ∑ᶠ h : G ⧸ N, v.1 h * w.2 (h * u)
  simp only [← mul_assoc]
  exact finsum_comp_equiv (Equiv.mulLeft c⁻¹) (f := fun h => v.1 h * w.2 (h * u))

/-- The square summand is an equivariant factor set for its square map. -/
theorem isEquivariantFactorSet_squareBlockDatum (j : Fin K) :
    IsEquivariantFactorSet (squareBlockMap N j) (squareBlockDatum N j) :=
  datum_comap (isEqFS_squareOrbitDatum N) (blockProj N j) (fun c v => blockProj_smul N j c v)

/-- The free summand is an equivariant factor set for its square map. -/
theorem isEquivariantFactorSet_freeBlockDatum (j k : Fin K) (u : G ⧸ N) :
    IsEquivariantFactorSet (freeBlockMap N j k u) (freeBlockDatum N j k u) :=
  datum_comap (isEqFS_freeOrbitDatum N u) (blockProj₂ N j k)
    (fun c v => blockProj₂_smul N j k c v)

/-- The involution summand is an equivariant factor set for its square map (banked
`isEquivariantFactorSet_invOrbitDatum` + comap). -/
theorem isEquivariantFactorSet_invBlockDatum (j : Fin K) {u : G ⧸ N} (hu2 : u * u = 1) :
    IsEquivariantFactorSet (invBlockMap N j u) (invBlockDatum N j u) :=
  datum_comap (isEquivariantFactorSet_invOrbitDatum N u hu2) (blockProj N j)
    (fun c v => blockProj_smul N j c v)

/-! ### Quadraticity of the three square maps -/

theorem isQuadraticFp2_squareBlockMap (j : Fin K) : IsQuadraticFp2 (squareBlockMap N j) := by
  refine datum_isQuadratic (isEquivariantFactorSet_squareBlockDatum N j) ?_ ?_
  · intro v v' w
    show (squareOrbitDatum N).f (blockProj N j (v + v')) (blockProj N j w) = _
    rw [map_add]
    exact sq_f_add_left N _ _ _
  · intro v w w'
    show (squareOrbitDatum N).f (blockProj N j v) (blockProj N j (w + w')) = _
    rw [map_add]
    exact sq_f_add_right N _ _ _

theorem isQuadraticFp2_freeBlockMap (j k : Fin K) (u : G ⧸ N) :
    IsQuadraticFp2 (freeBlockMap N j k u) := by
  refine datum_isQuadratic (isEquivariantFactorSet_freeBlockDatum N j k u) ?_ ?_
  · intro v v' w
    show (freeOrbitDatum N u).f (blockProj₂ N j k (v + v')) (blockProj₂ N j k w) = _
    rw [map_add]
    exact free_f_add_left N u _ _ _
  · intro v w w'
    show (freeOrbitDatum N u).f (blockProj₂ N j k v) (blockProj₂ N j k (w + w')) = _
    rw [map_add]
    exact free_f_add_right N u _ _ _

theorem isQuadraticFp2_invBlockMap (j : Fin K) {u : G ⧸ N} (hu2 : u * u = 1) :
    IsQuadraticFp2 (invBlockMap N j u) := by
  refine datum_isQuadratic (isEquivariantFactorSet_invBlockDatum N j hu2) ?_ ?_
  · intro v v' w
    show (invOrbitDatum N u).f (blockProj N j (v + v')) (blockProj N j w) = _
    rw [map_add]
    exact invOrbitDatum_f_add_left N u _ _ _
  · intro v w w'
    show (invOrbitDatum N u).f (blockProj N j v) (blockProj N j (w + w')) = _
    rw [map_add]
    exact invOrbitDatum_f_add_right N u _ _ _

/-! ### Basis evaluations: factor sets, diagonals, polars -/

/-- The free summand's factor set at basis vectors: the single-position indicator. -/
theorem freeBlockDatum_f_blockBas (j k : Fin K) (u : G ⧸ N)
    (m m' : Fin K) (x y : G ⧸ N) :
    (freeBlockDatum N j k u).f (blockBas N m x) (blockBas N m' y)
      = if j = m ∧ k = m' ∧ x * u = y then 1 else 0 := by
  show (∑ᶠ h : G ⧸ N, blockBas N m x j h * blockBas N m' y k (h * u)) = _
  have hterm : ∀ h : G ⧸ N, blockBas N m x j h * blockBas N m' y k (h * u)
      = if (j = m ∧ h = x) ∧ (k = m' ∧ h * u = y) then 1 else 0 := by
    intro h
    rw [blockBas_apply, blockBas_apply]
    by_cases h1 : j = m ∧ h = x
    · by_cases h2 : k = m' ∧ h * u = y
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, one_mul]
      · rw [if_pos h1, if_neg h2, if_neg fun hc => h2 hc.2, one_mul]
    · rw [if_neg h1, zero_mul, if_neg fun hc => h1 hc.1]
  rw [finsum_congr hterm, finsum_eq_single _ x (fun b hb => if_neg fun hc => hb hc.1.2)]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨⟨hj, -⟩, hk, hxy⟩
    exact ⟨hj, hk, hxy⟩
  · rintro ⟨hj, hk, hxy⟩
    exact ⟨⟨hj, rfl⟩, hk, hxy⟩

/-- The square summand's diagonal at basis vectors: `1` exactly on its own block. -/
theorem squareBlockMap_blockBas (j m : Fin K) (y : G ⧸ N) :
    squareBlockMap N j (blockBas N m y) = if j = m then 1 else 0 := by
  show (∑ᶠ h : G ⧸ N, blockBas N m y j h * blockBas N m y j h) = _
  have hterm : ∀ h : G ⧸ N, blockBas N m y j h * blockBas N m y j h
      = if j = m ∧ h = y then 1 else 0 := by
    intro h
    rw [blockBas_apply]
    by_cases hc : j = m ∧ h = y
    · rw [if_pos hc, mul_one]
    · rw [if_neg hc, mul_zero]
  rw [finsum_congr hterm]
  by_cases hjm : j = m
  · rw [finsum_eq_single _ y (fun b hb => if_neg fun hc => hb hc.2), if_pos ⟨hjm, rfl⟩,
      if_pos hjm]
  · rw [if_neg hjm]
    exact finsum_eq_zero_of_forall_eq_zero fun h => if_neg fun hc => hjm hc.1

/-- The free summand's diagonal at basis vectors vanishes off `u = 1` (in particular on every
free position). -/
theorem freeBlockMap_blockBas (j k : Fin K) (u : G ⧸ N) (m : Fin K) (y : G ⧸ N) :
    freeBlockMap N j k u (blockBas N m y) = if j = m ∧ k = m ∧ u = 1 then 1 else 0 := by
  have h := (isEquivariantFactorSet_freeBlockDatum N j k u).f_diag (blockBas N m y)
  rw [freeBlockDatum_f_blockBas] at h
  rw [← h]
  refine if_congr (and_congr_right fun _ => and_congr_right fun _ => ?_) rfl rfl
  exact mul_eq_left

/-- The involution summand's diagonal at basis vectors vanishes (`u ≠ 1`). -/
theorem invBlockMap_blockBas (j : Fin K) {u : G ⧸ N} (hu1 : u ≠ 1)
    (m : Fin K) (y : G ⧸ N) : invBlockMap N j u (blockBas N m y) = 0 := by
  show (∑ᶠ w : (G ⧸ N) ⧸ Subgroup.zpowers u,
      blockBas N m y j w.out * blockBas N m y j (w.out * u)) = 0
  refine finsum_eq_zero_of_forall_eq_zero fun w => ?_
  rw [blockBas_apply, blockBas_apply]
  by_cases h1 : j = m ∧ w.out = y
  · have h2 : ¬(j = m ∧ w.out * u = y) := by
      rintro ⟨-, hc⟩
      rw [h1.2] at hc
      exact hu1 (mul_eq_left.mp hc)
    rw [if_pos h1, if_neg h2, mul_zero]
  · rw [if_neg h1, zero_mul]

/-- The square summand's polar form vanishes identically (`x ↦ Σ x_h²` is additive over `𝔽₂`). -/
theorem polar_squareBlockMap (j : Fin K) (v w : Fin K → RegRep N) :
    polar (squareBlockMap N j) v w = 0 := by
  have hadd : squareBlockMap N j (v + w) = squareBlockMap N j v + squareBlockMap N j w := by
    show ∑ᶠ h : G ⧸ N, (v + w) j h * (v + w) j h = _
    have hterm : ∀ h : G ⧸ N, (v + w) j h * (v + w) j h
        = v j h * v j h + w j h * w j h := by
      intro h
      show (v j h + w j h) * (v j h + w j h) = _
      exact zmod2_sq_add _ _
    rw [finsum_congr hterm]
    exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)
  show squareBlockMap N j (v + w) + squareBlockMap N j v + squareBlockMap N j w = 0
  rw [hadd]
  exact (by decide : ∀ a b : ZMod 2, a + b + a + b = 0) _ _

/-- The free summand's polar at basis vectors: the two-order position indicator. -/
theorem polar_freeBlockMap_blockBas (j k : Fin K) (u : G ⧸ N)
    (m m' : Fin K) (x y : G ⧸ N) :
    polar (freeBlockMap N j k u) (blockBas N m x) (blockBas N m' y)
      = (if j = m ∧ k = m' ∧ x * u = y then 1 else 0)
        + (if j = m' ∧ k = m ∧ y * u = x then 1 else 0) := by
  rw [← (isEquivariantFactorSet_freeBlockDatum N j k u).f_polar,
    freeBlockDatum_f_blockBas, freeBlockDatum_f_blockBas]

/-! ### The involution summand's basis evaluation (the `Quotient.out` bookkeeping) -/

/-- With `u² = 1`, the canonical `⟨u⟩`-coset representative of `x` is `x` or `x·u`. -/
theorem out_dichotomy {u : G ⧸ N} (hu2 : u * u = 1) (x : G ⧸ N) :
    ((x : (G ⧸ N) ⧸ Subgroup.zpowers u) : (G ⧸ N) ⧸ Subgroup.zpowers u).out = x
      ∨ ((x : (G ⧸ N) ⧸ Subgroup.zpowers u) : (G ⧸ N) ⧸ Subgroup.zpowers u).out = x * u := by
  set t := ((x : (G ⧸ N) ⧸ Subgroup.zpowers u) : (G ⧸ N) ⧸ Subgroup.zpowers u).out with ht
  have hmem : t⁻¹ * x ∈ Subgroup.zpowers u := by
    rw [← QuotientGroup.eq, ht]
    exact Quotient.out_eq _
  rcases zpowers_sq_dichotomy N u hu2 hmem with h | h
  · left
    exact inv_mul_eq_one.mp h
  · right
    have hx : x = t * u := inv_mul_eq_iff_eq_mul.mp h
    rw [hx, mul_assoc, hu2, mul_one]

/-- With `u² = 1`, `x` and `x·u` lie in the same `⟨u⟩`-coset. -/
theorem mk_mul_self_eq {u : G ⧸ N} (hu2 : u * u = 1) (x : G ⧸ N) :
    ((x * u : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u)
      = ((x : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u) := by
  rw [QuotientGroup.eq]
  refine Subgroup.mem_zpowers_iff.mpr ⟨-1, ?_⟩
  show u ^ (-1 : ℤ) = (x * u)⁻¹ * x
  rw [zpow_neg_one, mul_inv_rev, mul_assoc, inv_mul_cancel, mul_one]

/-- The involution summand's factor set at basis vectors: the `out`-guarded position indicator. -/
theorem invBlockDatum_f_blockBas (j : Fin K) (u : G ⧸ N)
    (m m' : Fin K) (x y : G ⧸ N) :
    (invBlockDatum N j u).f (blockBas N m x) (blockBas N m' y)
      = if m = j ∧ m' = j
          ∧ ((x : (G ⧸ N) ⧸ Subgroup.zpowers u) : (G ⧸ N) ⧸ Subgroup.zpowers u).out = x
          ∧ x * u = y
        then 1 else 0 := by
  show (∑ᶠ w : (G ⧸ N) ⧸ Subgroup.zpowers u,
      blockBas N m x j w.out * blockBas N m' y j (w.out * u)) = _
  have hterm : ∀ w : (G ⧸ N) ⧸ Subgroup.zpowers u,
      blockBas N m x j w.out * blockBas N m' y j (w.out * u)
        = if (j = m ∧ w.out = x) ∧ (j = m' ∧ w.out * u = y) then 1 else 0 := by
    intro w
    rw [blockBas_apply, blockBas_apply]
    by_cases h1 : j = m ∧ w.out = x
    · by_cases h2 : j = m' ∧ w.out * u = y
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩, one_mul]
      · rw [if_pos h1, if_neg h2, if_neg fun hc => h2 hc.2, one_mul]
    · rw [if_neg h1, zero_mul, if_neg fun hc => h1 hc.1]
  rw [finsum_congr hterm,
    finsum_eq_single _ ((x : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u)
      (fun w hw => if_neg fun hc => hw (by rw [← Quotient.out_eq w, hc.1.2]))]
  refine if_congr ?_ rfl rfl
  constructor
  · rintro ⟨⟨hj, hout⟩, hj', houty⟩
    refine ⟨hj.symm, hj'.symm, hout, ?_⟩
    rw [← hout]
    exact houty
  · rintro ⟨hm, hm', hout, hxy⟩
    refine ⟨⟨hm.symm, hout⟩, hm'.symm, ?_⟩
    rw [hout]
    exact hxy

/-- The involution summand's polar at basis vectors: the `u`-pairing indicator on block `j`
(the two `out`-guards sum to exactly one across the coset `{x, xu}`). -/
theorem polar_invBlockMap_blockBas (j : Fin K) {u : G ⧸ N}
    (hu2 : u * u = 1) (hu1 : u ≠ 1) (m m' : Fin K) (x y : G ⧸ N) :
    polar (invBlockMap N j u) (blockBas N m x) (blockBas N m' y)
      = if m = j ∧ m' = j ∧ x * u = y then 1 else 0 := by
  rw [← (isEquivariantFactorSet_invBlockDatum N j hu2).f_polar,
    invBlockDatum_f_blockBas, invBlockDatum_f_blockBas]
  by_cases hxy : x * u = y
  · -- same coset `{x, y}`: exactly one of the two `out`-guards fires
    have hyx : y * u = x := by rw [← hxy, mul_assoc, hu2, mul_one]
    have hxney : x ≠ y := by
      intro hc
      apply hu1
      rw [hc] at hxy
      exact mul_eq_left.mp hxy
    have hcoset : ((y : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u)
        = ((x : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u) := by
      rw [← hxy]
      exact mk_mul_self_eq N hu2 x
    have houty : ((y : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u).out
        = ((x : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u).out := by
      rw [hcoset]
    by_cases hblocks : m = j ∧ m' = j
    · rcases out_dichotomy N hu2 x with hox | hoxu
      · -- `out = x`: the first guard fires, the second cannot
        have hnoty : ((y : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u).out ≠ y := by
          rw [houty, hox]
          exact hxney
        rw [if_pos ⟨hblocks.1, hblocks.2, hox, hxy⟩, if_neg (fun hc => hnoty hc.2.2.1),
          if_pos ⟨hblocks.1, hblocks.2, hxy⟩, add_zero]
      · -- `out = x·u = y`: the second guard fires, the first cannot
        have hoy : ((y : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u).out = y := by
          rw [houty, hoxu]
          exact hxy
        have hnotx : ((x : G ⧸ N) : (G ⧸ N) ⧸ Subgroup.zpowers u).out ≠ x := by
          rw [hoxu]
          exact fun hc => hu1 (mul_eq_left.mp hc)
        rw [if_neg (fun hc => hnotx hc.2.2.1), if_pos ⟨hblocks.2, hblocks.1, hoy, hyx⟩,
          if_pos ⟨hblocks.1, hblocks.2, hxy⟩, zero_add]
    · rw [if_neg (fun hc => hblocks ⟨hc.1, hc.2.1⟩), if_neg (fun hc => hblocks ⟨hc.2.1, hc.1⟩),
        if_neg (fun hc => hblocks ⟨hc.1, hc.2.1⟩), add_zero]
  · -- off-position: everything vanishes
    have hyx : ¬(y * u = x) := by
      intro hc
      apply hxy
      rw [← hc, mul_assoc, hu2, mul_one]
    rw [if_neg (fun hc => hxy hc.2.2.2), if_neg (fun hc => hyx hc.2.2.2),
      if_neg (fun hc => hxy hc.2.2), add_zero]

end Summands

end GQ2
