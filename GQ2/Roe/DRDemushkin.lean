/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Demushkin
public import GQ2.Roe.DRPresentation

@[expose] public section

/-!
# `D_R` is a rank-3 Demushkin group with `q = 2`  (Roe note Lemma 3.2, ⟦lem:initial⟧)

**Skeleton (ticket R7; fills are R12 — `H¹` side — and R13 — `H²` and cup Gram; the
`q`-invariant fill consumes ticket R8's abelianization decomposition).**  Statements are final;
proofs may be `sorry`.

The note's Lemma 3.2: the degree-two initial form of `r₂` is `y² + [x,s]`, so `D_R` is a
rank-three Demushkin group whose cup–Bockstein matrix in the basis dual to `(s, x, y)` is

  `[[0,1,0], [1,0,0], [0,0,1]]`,   ⟦eq:cupmatrix⟧

which is nonsingular.  Per the campaign plan (§3 Route L), *no Zassenhaus filtration is
formalized*: the dimension counts and the Gram matrix are stated in the repo's
cochain/cup vocabulary (`GQ2.ContCoh` + `GQ2.trivialCupPairing`), the route the tree already
knows (`Demushkin.lean`, `WordCoh2.lean`, `CardH2GammaA.lean`), and feed the abstract
`IsDemushkin` predicate — its first load-bearing use.

## Encoding

* Dimensions are `Nat.card` clauses, as in `IsDemushkin`: `dim H¹ = 3` is
  `#H¹(D_R, 𝔽₂) = 8` and `dim H² = 1` is `#H²(D_R, 𝔽₂) = 2`.
* The **dual basis** of `(s, x, y)`: every triple `v : Fin 3 → 𝔽₂` extends to a (continuous)
  character `D_R → 𝔽₂` — the relator dies in any elementary-abelian target since its
  abelianization is `−4x̄ + 2ȳ` (`drWord_comm`) — giving classes `drH1 v ∈ H¹(D_R, 𝔽₂)`;
  `drSStar, drXStar, drYStar` are the coordinate vectors.  That `drH1` is a *bijection*
  `𝔽₂³ ≃ H¹` is the rank-3 statement in basis form (`drH1_bijective` + `card_H1_DR`).
* **The `p = 2` pitfall (R2 spike)**: at `p = 2` the diagonal of ⟦eq:cupmatrix⟧ is the
  Bockstein — `u ∪ u = β(u)` is *additive* in `u` — so the matrix is the **Gram matrix of the
  symmetric bilinear cup form** `GQ2.trivialCupPairing` (with the Bockstein on the diagonal),
  **not** the polar form of a quadratic form (the polar is alternating and would have zero
  diagonal).  The nine entries are stated below as cup values against the dual basis, with
  `#H² = 2` making "`≠ 0`" mean "`= the generator`".  Do not reformulate through
  `QuadraticForm`/Arf: the spike documents how that briefly "refuted" the correct matrix.

## Statement inventory

`card_H1_DR`, `drH1_bijective` (R12); `card_H2_DR`, the nine Gram entries `drCup_*` (R13);
`isDemushkin_DR` (assembly: nondegeneracy from the Gram entries and the basis);
`demushkinRank_DR = 3` (proved from `card_H1_DR`); `demushkinQ_DR = 2` (from R8's
`B_R = C₂t ⊕ ℤ₂s̄ ⊕ ℤ₂x̄`, note eq. (3.6) ⟦eq:BRsplit⟧) — the invariant quadruple consumed by
the B-Lab hypothesis (`GQ2/Roe/MarkedPro2.lean`).
-/

namespace GQ2

open ContCoh

/-! ## The trivial coefficient action

`Aut(ℤ/2) = 1`, so *every* distributive action on `𝔽₂` is trivial; registering the literal
trivial action globally is the house convention (`GQ2/Kummer.lean`, `RStage/GammaA.lean`). -/

instance instDistribMulActionDR : DistribMulAction (DR : Type) (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

instance : ContinuousSMul (DR : Type) (ZMod 2) := ⟨continuous_snd⟩

/-- The `D_R`-action on `𝔽₂` is trivial (definitional). -/
theorem drSmul_trivial : ∀ (g : (DR : Type)) (m : ZMod 2), g • m = m := fun _ _ => rfl

/-! ## The dual basis of `H¹(D_R, 𝔽₂)` -/

/-- `Multiplicative (ZMod 2)` is pro-2 (a finite 2-group; local clone of
`GQ2.isProP_two_multZMod2`, which lives downstream in `GQ2/SectionThree.lean`). -/
theorem isProP_two_multZMod2_roe : IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- The multiplicative `𝔽₂`-character of `D_R` with generator values
`s, x, y ↦ v 0, v 1, v 2` (additively): well-defined for **every** triple `v` because the
relator abelianizes to `−4x̄ + 2ȳ = 0` (`drWord_comm`), which is vacuous mod 2 — the Burnside
face of `dim H¹ = 3`. -/
noncomputable def drCharM (v : Fin 3 → ZMod 2) :
    ContinuousMonoidHom (DR : Type) (Multiplicative (ZMod 2)) :=
  drLiftHom isProP_two_multZMod2_roe (fun i => Multiplicative.ofAdd (v i)) (by
    rw [drWord_comm]
    exact (by decide : ∀ a b : Multiplicative (ZMod 2), (a ^ 4)⁻¹ * b ^ 2 = 1) _ _)

@[simp] theorem drCharM_drS (v : Fin 3 → ZMod 2) :
    drCharM v drS = Multiplicative.ofAdd (v 0) := drLiftHom_S _ _ _

@[simp] theorem drCharM_drX (v : Fin 3 → ZMod 2) :
    drCharM v drX = Multiplicative.ofAdd (v 1) := drLiftHom_X _ _ _

@[simp] theorem drCharM_drY (v : Fin 3 → ZMod 2) :
    drCharM v drY = Multiplicative.ofAdd (v 2) := drLiftHom_Y _ _ _

/-- The additive 1-cocycle of the character `drCharM v` (for the trivial action, continuous
1-cocycles *are* continuous additive characters). -/
noncomputable def drZ1 (v : Fin 3 → ZMod 2) : Z1 (DR : Type) (ZMod 2) :=
  ⟨fun g => Multiplicative.toAdd (drCharM v g), by
    refine mem_Z1_iff.mpr ⟨continuous_toAdd.comp (drCharM v).continuous_toFun, ?_⟩
    intro g h
    show Multiplicative.toAdd (drCharM v (g * h))
        = Multiplicative.toAdd (drCharM v g) + g • Multiplicative.toAdd (drCharM v h)
    rw [map_mul, toAdd_mul]
    rfl⟩

/-- The `H¹(D_R, 𝔽₂)`-class with coordinates `v` in the basis dual to `(s, x, y)`. -/
noncomputable def drH1 (v : Fin 3 → ZMod 2) : H1 (DR : Type) (ZMod 2) :=
  H1mk (DR : Type) (ZMod 2) (drZ1 v)

/-- `s* ∈ H¹(D_R, 𝔽₂)`: the class dual to `s`. -/
noncomputable def drSStar : H1 (DR : Type) (ZMod 2) := drH1 ![1, 0, 0]
/-- `x* ∈ H¹(D_R, 𝔽₂)`: the class dual to `x`. -/
noncomputable def drXStar : H1 (DR : Type) (ZMod 2) := drH1 ![0, 1, 0]
/-- `y* ∈ H¹(D_R, 𝔽₂)`: the class dual to `y`. -/
noncomputable def drYStar : H1 (DR : Type) (ZMod 2) := drH1 ![0, 0, 1]

/-! ## `dim H¹ = 3`  (fill: R12) -/

/-- **The dual basis is a basis** — `v ↦ drH1 v` is a bijection `𝔽₂³ ≃ H¹(D_R, 𝔽₂)`
⟦lem:initial⟧.  Fill (R12): injectivity evaluates classes on the generators (coboundaries
vanish — the action is trivial); surjectivity is the Burnside/Frattini argument — a continuous
1-cocycle for the trivial action is a continuous character, determined by its generator values
via topological generation (R8 infrastructure), and `drCharM` realizes every triple. -/
theorem drH1_bijective : Function.Bijective drH1 := by
  sorry

/-- **`dim_𝔽₂ H¹(D_R, 𝔽₂) = 3`**, in `Nat.card` form ⟦lem:initial⟧ — the rank clause of the
note's Lemma 3.2.  Fill (R12): transport `Nat.card (Fin 3 → ZMod 2) = 8` along
`drH1_bijective`. -/
theorem card_H1_DR : Nat.card (H1 (DR : Type) (ZMod 2)) = 8 := by
  sorry

/-- `H¹(D_R, 𝔽₂)` is finite (clause 1 of `IsDemushkin`; from `card_H1_DR`). -/
theorem finite_H1_DR : Finite (H1 (DR : Type) (ZMod 2)) :=
  Nat.finite_of_card_ne_zero (by rw [card_H1_DR]; norm_num)

/-! ## `dim H² = 1`  (fill: R13) -/

/-- **`dim_𝔽₂ H²(D_R, 𝔽₂) = 1`**, in `Nat.card` form ⟦lem:initial⟧ — "the presentation is
minimal and has one relation".  Fill (R13), one-relator central-extension route (clone of the
`WordCoh2`/`CardH2GammaA` pattern): the upper bound from the single relator through the word
cohomology bridge, the lower bound from a concrete finite central-extension witness detecting a
nonzero class (equivalently, from any nonzero Gram entry below). -/
theorem card_H2_DR : Nat.card (H2 (DR : Type) (ZMod 2)) = 2 := by
  sorry

/-! ## The cup–Bockstein Gram matrix  ⟦eq:cupmatrix⟧  (fill: R13)

The nine entries of the matrix `[[0,1,0],[1,0,0],[0,0,1]]` of the symmetric bilinear cup form
on `H¹(D_R, 𝔽₂)` in the dual basis `(s*, x*, y*)` — rows and columns in that order, diagonal
entries the Bocksteins (`u ∪ u = β(u)` at `p = 2`; see the module docstring for the
quadratic-form trap).  With `card_H2_DR`, "`≠ 0`" says "`= the generator of H² ≅ 𝔽₂`".  Both
triangles are stated since graded-commutativity of `cup11` is not formalized (the
`IsDemushkin.nondegen_left/right` precedent). -/

/-- Gram entry `(s, s) = 0`: the Bockstein `β(s*) = s* ∪ s*` vanishes (no `s²` in the initial
form of `r₂`). -/
theorem drCup_ss : drSStar ⌣[drSmul_trivial] drSStar = 0 := by
  sorry

/-- Gram entry `(s, x) = 1`: `s* ∪ x* ≠ 0` — the `[x, s]`-term of the initial form
`y² + [x,s]` ⟦lem:initial⟧. -/
theorem drCup_sx : drSStar ⌣[drSmul_trivial] drXStar ≠ 0 := by
  sorry

/-- Gram entry `(s, y) = 0`. -/
theorem drCup_sy : drSStar ⌣[drSmul_trivial] drYStar = 0 := by
  sorry

/-- Gram entry `(x, s) = 1` (the transpose of `drCup_sx`; stated separately since
graded-commutativity is not formalized). -/
theorem drCup_xs : drXStar ⌣[drSmul_trivial] drSStar ≠ 0 := by
  sorry

/-- Gram entry `(x, x) = 0`: the Bockstein `β(x*)` vanishes — `x` enters `r₂` with exponent
`−4 ≡ 0 (mod 4)`. -/
theorem drCup_xx : drXStar ⌣[drSmul_trivial] drXStar = 0 := by
  sorry

/-- Gram entry `(x, y) = 0`. -/
theorem drCup_xy : drXStar ⌣[drSmul_trivial] drYStar = 0 := by
  sorry

/-- Gram entry `(y, s) = 0`. -/
theorem drCup_ys : drYStar ⌣[drSmul_trivial] drSStar = 0 := by
  sorry

/-- Gram entry `(y, x) = 0`. -/
theorem drCup_yx : drYStar ⌣[drSmul_trivial] drXStar = 0 := by
  sorry

/-- Gram entry `(y, y) = 1`: the Bockstein `β(y*) = y* ∪ y* ≠ 0` — the `y²`-term of the
initial form `y² + [x,s]` ⟦lem:initial⟧, and the diagonal `1` that makes the matrix
nonsingular over `𝔽₂` (`det = 1`). -/
theorem drCup_yy : drYStar ⌣[drSmul_trivial] drYStar ≠ 0 := by
  sorry

/-! ## The Demushkin package -/

/-- **`D_R` is a Demushkin pro-2 group** ⟦lem:initial⟧ — "this is exactly the defining
cohomological condition".  The first load-bearing use of the abstract `IsDemushkin` predicate.
Nondegeneracy fill (R13, after the Gram entries): a class `a·s* + b·x* + c·y*` cups with `x*`
to `a`, with `s*` to `b`, and with `y*` to `c` — the matrix `[[0,1,0],[1,0,0],[0,0,1]]` is
nonsingular — using `drH1_bijective` to write an arbitrary nonzero class in coordinates. -/
theorem isDemushkin_DR : IsDemushkin 2 (DR : Type) :=
  { smul_trivial := drSmul_trivial
    isProP := isProP_DR
    finiteH1 := finite_H1_DR
    cardH2 := card_H2_DR
    nondegen_left := by sorry
    nondegen_right := by sorry }

/-- **`D_R` has Demushkin rank 3** ⟦lem:initial⟧ (`8 = 2³`; proved from `card_H1_DR`). -/
theorem demushkinRank_DR : demushkinRank 2 (DR : Type) = 3 :=
  demushkinRank_eq_of_card (by rw [card_H1_DR]; norm_num)

/-- **`D_R` has `q`-invariant 2** ⟦eq:BR⟧/⟦eq:BRsplit⟧ (note (3.4)–(3.6)): the topological
abelianization is `B_R = ⟨s̄, x̄, ȳ | −4x̄ + 2ȳ = 0⟩ = C₂·t ⊕ ℤ₂·s̄ ⊕ ℤ₂·x̄` with
`t = ȳ − 2x̄`, whose torsion subgroup has order 2.  Fill: from ticket R8's `BRDecomposition`
(the `BDecomposition` clone; see the R7 design memo §R8). -/
theorem demushkinQ_DR : demushkinQ (DR : Type) = 2 := by
  sorry

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Lemma 3.2 = ⟦lem:initial⟧
  * eq. (3.2) = ⟦eq:cupmatrix⟧
  * eq. (3.4)–(3.6) = ⟦eq:BR⟧/⟦eq:tR⟧/⟦eq:BRsplit⟧ (`demushkinQ_DR`; fill via ticket R8)
-/
