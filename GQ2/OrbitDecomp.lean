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

end GQ2
