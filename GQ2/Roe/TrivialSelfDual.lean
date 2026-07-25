/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.FoxBasic
public import GQ2.Roe.WildRow
public import GQ2.Roe.Stokes
public import GQ2.TrivialSelfDual

@[expose] public section

/-!
# The traced chain rows and the trivial-module self-duality for `r_R`  (⟦lem:stokes⟧, ⟦lem:trivial⟧)

The `Γ_R` counterparts of `GQ2.FoxHeisenberg.Traced`'s wild chain-map rows and
`GQ2.TrivialSelfDual`'s base case of the Prop. 5.15 dévissage, for the Roe candidate word
`r_R = (x₀^σ)⁻¹ · (x₀⁻³τ)^{ω₂} · x₁² · [x₁, x₁^{σ₂}]` (`GQ2.Roe.Words`).

## The traced chain rows (⟦lem:stokes⟧, Prop 5.8)

`prop_5_8_left_R`/`prop_5_8_right_R`: the traced mixed coordinate `mixedB_R`
(`GQ2.Roe.FoxBasic`) at a coboundary `d⁰a` splits into the dual first-relation Fox rows,
`B_{R,ρ,A}(d⁰a, y) = ⟨a, L^{A^∨}_t(y) + L^{A^∨}_w(y)⟩`.  The tame row (`mixedB_tameRow_R`) is
`Γ_A`'s verbatim (the tame relator is shared, `d1FunR_fst`); the wild row (`mixedB_wildRow_R`) runs
the Roe wild bridge `bridge_wildR` through the generic finite-word Stokes formula `lemma_5_7_left`,
its two `ε`-corrections `y_τ(τ·a)` matching the tame ones because the Roe wild ε-vector is
`(0,1,0,0)` at the odd `ω₂`-representative (R23's `expMod2_wildValueExpR_odd` at
`omega2Exp_exponent_heis_cast`) — the endpoint condition ⟦lem:stokes⟧.

## The trivial module (⟦lem:trivial⟧)

For `V = 𝔽₂` with trivial action, `d¹_R(a,b,c,d) = (b,b)` (R21's `d1R_of_trivial`), so
`Z¹_R = {x | x₁ = 0}` has coordinates `(a,c,d) = (x₀,x₂,x₃)` and `B¹_R = ⊥`, giving the two card
clauses.  The degree-one pairing is the scalar Gram ⟦eq:scalarform⟧

  `⟨(a,c,d),(a',c',d')⟩ = a·c' + c·a' + d·d'`,   matrix `[[0,1,0],[1,0,0],[0,0,1]]` (⟦eq:cupmatrix⟧),

whose closed form `mixedB_cocycle_R` is the Roe twin of `mixedB_cocycle`
(`GQ2.MixedBilinear`) — **cleaner**: the honest diagonal `d·d'` on the `(3,3)` slot comes from the
square `x₁²`, and the opaque `ω₂` scalar `aR.z` is confined to the `(2,2)` slot (with `Γ_A`'s
`u₁.z` moved from `(3,3)` to `(2,2)` by the `x₀ ↔ x₁` wild-column swap), killed on the single-slot
duals used for nondegeneracy.  Nonsingularity is a `3×3` unit-determinant `decide`.
-/

namespace GQ2

namespace FoxH

/-! ## The traced chain rows of Prop 5.8 for `r_R` (⟦lem:stokes⟧) -/

section TracedRowsR

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The tame row of Prop 5.8 (41) for `r_R`** — `Γ_A`'s `mixedB_tameRow` reused verbatim: the
tame relator is shared, so its mixed central coordinate is unchanged, and the first Fox component
`(d1FunR t y).1 = (d1Fun t y).1` (`d1FunR_fst`). -/
theorem mixedB_tameRow_R (t : Marking C) (ht : t.TameRel) (a : A) (y : Fin 4 → ElemDual A) :
    (heisMarking t (d0 t a) y).tameValue.z
      = (d1FunR (A := ElemDual A) t y).1 a + y 1 (t.τ • a) :=
  mixedB_tameRow t ht a y

/-- The wild `hr` for `r_R`: the free Roe word `wildValueExpR freeMarking (omega2Exp N)` has
trivial lower value at `N = exponent (H(A)⋊C)`, from `WildRelR` — the `Γ_R` twin of
`lift_markVec_wildValueExp_eq_one`, with the two `ω₂`-subword orders (`σ`, `x₀⁻³τ`) dividing `N`. -/
theorem lift_markVec_wildValueExpR_eq_one [Finite A] [Finite C] (t : Marking C) (hw : t.WildRelR) :
    FreeGroup.lift (markVec t)
        (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))) = 1 := by
  have hfm : freeMarking.map (FreeGroup.lift (markVec t)) = t := by
    simp only [freeMarking, Marking.map, markVec, FreeGroup.lift_apply_of, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.tail_cons]
  rw [wildValueExpR_map, hfm,
    ← wildValueExpR_eq_wildValueR_of_dvd Monoid.exponent_ne_zero_of_finite t
      (orderOf_dvd_exponent_heis t.σ) (orderOf_dvd_exponent_heis ((t.x₀ ^ 3)⁻¹ * t.τ))]
  exact (Marking.wildValueR_eq_one_iff t).mpr hw

/-- The wild `.l`-bridge for `r_R`: the `.l`-coordinate of the `y`-only Roe-wild evaluation is
`d¹_R`'s wild row on the dual (the `Γ_R` analogue of `stokesEval_wild_l`). -/
theorem stokesEval_wildR_l [Finite A] [Finite C] (t : Marking C) (y : Fin 4 → ElemDual A) :
    (stokesEval (markVec t) 0 y
        (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C))))).l
      = (liftMarking t y).wildValueR.u := by
  have hlg : lgHom (stokesEval (markVec t) 0 y
      (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
      = (liftMarking t y).wildValueR := by
    rw [wildValueExpR_map, wildValueExpR_map]
    have hmap : (freeMarking.map (stokesEval (markVec t) 0 y)).map lgHom = liftMarking t y := by
      rw [liftMarking_eq_map]; rfl
    rw [hmap, ← wildValueExpR_eq_wildValueR_of_dvd Monoid.exponent_ne_zero_of_finite
      (liftMarking t y) (orderOf_dvd_exponent_heis_wl _) (orderOf_dvd_exponent_heis_wl _)]
  exact congrArg WordLift.u hlg

/-- **The wild row of Prop 5.8 (41) for `r_R`**: the wild summand at the coboundary `d⁰a` equals
the pairing `⟨a, L^{A^∨}_w(y)⟩` plus the ε-correction `y_τ(τ·a)` — the same correction as the tame
row, because the Roe wild ε-vector reduces to `(0,1,0,0)` at the odd `ω₂`-representative
(`expMod2_wildValueExpR_odd` at `omega2Exp_exponent_heis_cast`, ⟦lem:stokes⟧). -/
theorem mixedB_wildRow_R [Finite A] [Finite C] (t : Marking C) (hw : t.WildRelR) (a : A)
    (y : Fin 4 → ElemDual A) :
    (heisMarking t (d0 t a) y).wildValueR.z
      = (d1FunR (A := ElemDual A) t y).2 a + y 1 (t.τ • a) := by
  rw [bridge_wildR, d0_eq_markVec,
    lemma_5_7_left (markVec t) _ (lift_markVec_wildValueExpR_eq_one t hw) a y]
  congr 1
  · rw [stokesEval_wildR_l]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := fun i =>
      congrFun (expMod2_wildValueExpR_odd (omega2Exp_exponent_heis_cast (A := A) (C := C))) i
    simp only [hvec]
    rw [Fin.sum_univ_four]
    simp [markVec]

/-- **Prop 5.8, display (41) for `r_R`**: `B_{R,ρ,A}(d⁰a, y) = ⟨a, L^{A^∨}_t(y) + L^{A^∨}_w(y)⟩`,
the dual first-relation Fox rows.  Assembled exactly as `Γ_A`'s `prop_5_8_left`: the two
`y_τ(τ·a)` ε-corrections cancel in char 2 (⟦lem:stokes⟧, "Their sum is zero"). -/
theorem prop_5_8_left_R [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (a : A) (y : Fin 4 → ElemDual A) :
    mixedB_R t (d0 t a) y
      = ((d1FunR (A := ElemDual A) t y).1 + (d1FunR (A := ElemDual A) t y).2) a := by
  show (heisMarking t (d0 t a) y).tameValue.z + (heisMarking t (d0 t a) y).wildValueR.z = _
  rw [mixedB_tameRow_R t ht a y, mixedB_wildRow_R t hw a y, ElemDual.add_apply,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

/-- **The tame row of Prop 5.8 (42) for `r_R`** (dual form) — `Γ_A`'s `mixedB_tameRow_right`
reused: shared tame relator, `d1FunR_fst`. -/
theorem mixedB_tameRow_right_R (t : Marking C) (ht : t.TameRel) (x : Fin 4 → A)
    (lam : ElemDual A) :
    (heisMarking t x (d0 (A := ElemDual A) t lam)).tameValue.z
      = lam ((d1FunR t x).1) + lam (x 1) :=
  mixedB_tameRow_right t ht x lam

/-- The `.a`-bridge for `r_R`: the `.a`-coordinate of the `x`-only Roe-wild evaluation is `d¹_R`'s
wild row on `A` (the `Γ_R` analogue of `stokesEval_wild_a`; the `A⋊C` exponent divisibility is
re-derived through the public section `secWA` so no private helper is needed). -/
theorem stokesEval_wildR_a [Finite A] [Finite C] (t : Marking C) (x : Fin 4 → A) :
    (stokesEval (markVec t) x 0
        (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C))))).a
      = (liftMarking t x).wildValueR.u := by
  have hwa : ∀ (w : WordLift A C), orderOf w ∣ Monoid.exponent (HeisLift A C) := fun w => by
    have hinj : Function.Injective (secWA (A := A) (C := C)) := fun p q h =>
      WordLift.ext (congrArg HeisLift.a h) (congrArg HeisLift.g h)
    rw [← orderOf_injective (secWA (A := A)) hinj w]; exact Monoid.order_dvd_exponent _
  have hag : agHom (stokesEval (markVec t) x 0
      (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
      = (liftMarking t x).wildValueR := by
    rw [wildValueExpR_map, wildValueExpR_map]
    have hmap : (freeMarking.map (stokesEval (markVec t) x 0)).map agHom = liftMarking t x := by
      rw [liftMarking_eq_map_a]; rfl
    rw [hmap, ← wildValueExpR_eq_wildValueR_of_dvd Monoid.exponent_ne_zero_of_finite
      (liftMarking t x) (hwa _) (hwa _)]
  exact congrArg WordLift.u hag

/-- **The wild row of Prop 5.8 (42) for `r_R`** (dual form): `⟨L^A_w(x), λ⟩ + λ(x_τ)`. -/
theorem mixedB_wildRow_right_R [Finite A] [Finite C] (t : Marking C) (hw : t.WildRelR)
    (x : Fin 4 → A) (lam : ElemDual A) :
    (heisMarking t x (d0 (A := ElemDual A) t lam)).wildValueR.z
      = lam ((d1FunR t x).2) + lam (x 1) := by
  rw [bridge_wildR, d0_eq_markVec,
    lemma_5_7_right (markVec t) _ (lift_markVec_wildValueExpR_eq_one t hw) x lam]
  congr 1
  · rw [stokesEval_wildR_a]; rfl
  · have hvec : ∀ i, Multiplicative.toAdd
        (expMod2 i (wildValueExpR freeMarking (omega2Exp (Monoid.exponent (HeisLift A C)))))
        = (![0, 1, 0, 0] : Fin 4 → ZMod 2) i := fun i =>
      congrFun (expMod2_wildValueExpR_odd (omega2Exp_exponent_heis_cast (A := A) (C := C))) i
    simp only [hvec]
    rw [Fin.sum_univ_four]
    simp

/-- **Prop 5.8, display (42) for `r_R`**: `B_{R,ρ,A}(x, d⁰λ) = ⟨L_t(x)+L_w(x), λ⟩`.  Assembled as
`Γ_A`'s `prop_5_8_right`: the two `λ(x_τ)` corrections cancel (char 2). -/
theorem prop_5_8_right_R [Finite A] [Finite C] (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (x : Fin 4 → A) (lam : ElemDual A) :
    mixedB_R t x (d0 (A := ElemDual A) t lam)
      = lam ((d1FunR t x).1 + (d1FunR t x).2) := by
  show (heisMarking t x (d0 (A := ElemDual A) t lam)).tameValue.z
      + (heisMarking t x (d0 (A := ElemDual A) t lam)).wildValueR.z = _
  rw [mixedB_tameRow_right_R t ht x lam, mixedB_wildRow_right_R t hw x lam, map_add,
    add_add_add_comm, CharTwo.add_self_eq_zero, add_zero]

end TracedRowsR

/-! ## The trivial module `𝔽₂` is self-dual for `r_R` (⟦lem:trivial⟧) -/

section TrivialR

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- On the trivial module `Z¹_R = {x | x₁ = 0}` (the note's coordinates `(a,c,d) = (x₀,x₂,x₃)`). -/
theorem mem_Z1wR_trivial_iff (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) (x : Fin 4 → A) :
    x ∈ Z1wR (A := A) t ↔ x 1 = 0 := by
  rw [mem_Z1wR_iff, d1FunR_of_trivial t ht hw htriv hA₂, Prod.mk_eq_zero, and_self]

omit [Finite C] [Finite A] in
/-- On the trivial module `B¹_R = ⊥` (`d⁰ = 0`, relator-free `B1wR_eq_B1w`), so `H¹_R = Z¹_R`. -/
theorem B1wR_trivial_eq_bot (t : Marking C) (htriv : ∀ (c : C) (a : A), c • a = a) :
    B1wR (A := A) t = ⊥ := by
  rw [B1wR_eq_B1w]; exact B1w_trivial_eq_bot t htriv

/-- On the trivial module `range d¹_R = Δ` (the diagonal `a ↦ (a,a)`), of cardinality `#A`. -/
theorem card_range_d1R_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (d1R (A := A) t).range = Nat.card A := by
  have hdgapp : ∀ a : A, ((AddMonoidHom.id A).prod (AddMonoidHom.id A)) a = (a, a) := fun _ => rfl
  have hinj : Function.Injective ⇑((AddMonoidHom.id A).prod (AddMonoidHom.id A)) :=
    fun a b h => congrArg Prod.fst h
  have hrange : (d1R (A := A) t).range = ((AddMonoidHom.id A).prod (AddMonoidHom.id A)).range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨x 1, by simp only [d1R_of_trivial t ht hw htriv hA₂ x, hdgapp]⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨fun _ => a, by simp only [d1R_of_trivial t ht hw htriv hA₂ (fun _ => a), hdgapp]⟩
  rw [hrange]
  exact (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm

/-- **Card clause for `H²_R`**: `#H²_R = #A` on the trivial module (`H²_R = (A×A)/Δ`). -/
theorem card_H2wR_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (H2wR (A := A) t) = Nat.card A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hlag :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (d1R (A := A) t).range
  rw [card_range_d1R_trivial t ht hw htriv hA₂, Nat.card_prod] at hlag
  show Nat.card ((A × A) ⧸ (d1R (A := A) t).range) = Nat.card A
  exact Nat.eq_of_mul_eq_mul_right hpos hlag.symm

/-- **Card clause for `Z¹_R`**: `#Z¹_R = (#A)³` on the trivial module (`Z¹_R = {x | x₁ = 0}`). -/
theorem card_Z1wR_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (Z1wR (A := A) t) = Nat.card A ^ 3 := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hfiso : Nat.card ((Fin 4 → A) ⧸ (d1R (A := A) t).ker) = Nat.card A := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (d1R (A := A) t)).toEquiv,
      card_range_d1R_trivial t ht hw htriv hA₂]
  have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (d1R (A := A) t).ker
  rw [hfiso] at hlag
  have hcard4 : Nat.card (Fin 4 → A) = Nat.card A ^ 4 := by
    rw [Nat.card_fun, Nat.card_fin]
  rw [hcard4] at hlag
  show Nat.card ((d1R (A := A) t).ker) = Nat.card A ^ 3
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hlag]; ring

/-! ### The wild `.z` peel on cocycles (⟦lem:trivial⟧, the Gram closed form)

The Roe wild word `wildValueR = (x₀^σ)⁻¹ · aR · x₁² · cR` (`aR = (x₀⁻³τ)^{ω₂}`) evaluated at
`heisMarking t x y` on the split cocycles `{x₁ = 0, y₁ = 0}`, peeled factor-by-factor with the
generic `HeisLift` API (every `.g` acts trivially via `htriv`).  The honest diagonal `y₃(x₃)`
comes from `x₁²`; the symplectic `y₂(x₀) − y₀(x₂)` from `(x₀^σ)⁻¹`; `cR` cancels in char 2; and
the opaque `ω₂` scalar `aR.z` is confined to the `(2,2)` slot. -/

omit [Finite C] [Finite A] in
/-- On the trivial module, `.g` of a `HeisLift` element acts trivially — every element of `C`
does (`htriv`). -/
private theorem hgtrivR (htriv : ∀ (c : C) (a : A), c • a = a) (w : HeisLift A C) (v : A) :
    w.g • v = v := htriv w.g v

omit [Finite C] [Finite A] in
/-- **Wild `.z`, the `(x₀^σ)` factor**: its central coordinate is the symplectic pairing of the
`σ`- and `x₀`-slots, `y₂(x₀) − y₀(x₂)` — the `(0,2)/(2,0)` Gram entries (the `x₀ ↔ x₁` swap of
`Γ_A`'s `heisMarking_x1sig_z_trivial`). -/
private theorem heisMarking_x0sig_z_trivial (htriv : ∀ (g : C) (a : A), g • a = a) (t : Marking C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (conjP (heisMarking t x y).x₀ (heisMarking t x y).σ).z = y 2 (x 0) - y 0 (x 2) := by
  have hdtriv : ∀ (g : C) (lam : ElemDual A), g • lam = lam := fun g lam => by
    ext a; rw [ElemDual.smul_apply, htriv]
  show (conjP (⟨x 2, y 2, 0, t.x₀⟩ : HeisLift A C) ⟨x 0, y 0, 0, t.σ⟩).z = _
  simp only [conjP, HeisLift.mul_z, HeisLift.mul_l, HeisLift.mul_g, HeisLift.inv_z, HeisLift.inv_l,
    HeisLift.inv_g, htriv, hdtriv, ElemDual.add_apply, ElemDual.neg_apply]
  generalize y 2 (x 0) = a
  generalize y 0 (x 2) = b
  generalize y 0 (x 0) = d
  generalize y 2 (x 2) = e
  revert a b d e
  decide

omit [Finite C] [Finite A] in
/-- **Wild `.z`, the `x₁²` factor**: the honest Heisenberg diagonal `y₃(x₃)` — the `(3,3)` Gram
entry.  `x₁.a = x₃, x₁.l = y₃, x₁.z = 0`, so `(x₁·x₁).z = y₃(x₃)`. -/
theorem heisMarking_x1sq_z_cocycle (htriv : ∀ (g : C) (a : A), g • a = a) (t : Marking C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    ((heisMarking t x y).x₁ ^ 2).z = y 3 (x 3) := by
  rw [pow_two, HeisLift.mul_z_of_trivial _ _ (fun v => htriv t.x₁ v)]
  show (0 : ZMod 2) + 0 + y 3 (x 3) = y 3 (x 3)
  simp

omit [Finite C] [Finite A] in
/-- **Wild `.z`, the `cR = [x₁, x₁^{σ₂}]` factor vanishes on the trivial module**: the two
symplectic commutator terms `y₃(x₃) + y₃(x₃)` cancel in char 2 (`U = σ₂` acts trivially; the
general-cocycle analogue of R24's `heisMarking_cR_z_split_cancels`). -/
theorem heisMarking_cR_z_cocycle (htriv : ∀ (g : C) (a : A), g • a = a) (t : Marking C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).cR.z = 0 := by
  set M := heisMarking t x y with hM
  have hx1g : ∀ v : A, M.x₁.g • v = v := fun v => htriv t.x₁ v
  have hsig2g : ∀ v : A, M.sigma2.g • v = v := hgtrivR htriv M.sigma2
  have hy1g : ∀ v : A, M.y1R.g • v = v := HeisLift.conjP_g_trivial M.x₁ M.sigma2 hx1g
  have hsiginvg : ∀ v : A, M.sigma2⁻¹.g • v = v := fun v => HeisLift.inv_g_trivial M.sigma2 hsig2g v
  have hmulg : ∀ v : A, (M.sigma2⁻¹ * M.x₁).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hsiginvg hx1g v
  have hy1a : M.y1R.a = x 3 := by
    show (conjP M.x₁ M.sigma2).a = x 3
    rw [conjP, HeisLift.mul_a_of_trivial _ _ hmulg, HeisLift.mul_a_of_trivial _ _ hsiginvg,
      HeisLift.inv_a_of_trivial _ hsig2g]
    show -M.sigma2.a + M.x₁.a + M.sigma2.a = x 3
    show -M.sigma2.a + x 3 + M.sigma2.a = x 3
    abel
  have hy1l : M.y1R.l = y 3 := by
    show (conjP M.x₁ M.sigma2).l = y 3
    rw [conjP, HeisLift.mul_l_of_trivial _ _ hmulg, HeisLift.mul_l_of_trivial _ _ hsiginvg,
      HeisLift.inv_l_of_trivial _ hsig2g]
    show -M.sigma2.l + M.x₁.l + M.sigma2.l = y 3
    show -M.sigma2.l + y 3 + M.sigma2.l = y 3
    abel
  show (commP M.x₁ M.y1R).z = 0
  rw [HeisLift.commP_z_of_trivial M.x₁ M.y1R hx1g hy1g, hy1a, hy1l]
  show y 3 (x 3) + y 3 (x 3) = 0
  exact CharTwo.add_self_eq_zero _

/-- The `.a`-coordinate of `aR` at `heisMarking` is its primal Fox derivative on `A`
(the `agHom`-projection to `liftMarking`): `aR.a = (liftMarking t x).aR.u`. -/
theorem heisMarking_aR_a_eq (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) :
    (heisMarking t x y).aR.a = (liftMarking t x).aR.u := by
  have hmap : Marking.map agHom (heisMarking t x y) = liftMarking t x := rfl
  have h : agHom ((heisMarking t x y).aR) = (liftMarking t x).aR := by
    rw [← Marking.map_aR agHom (heisMarking t x y), hmap]
  exact congrArg WordLift.u h

omit [Finite C] [Finite A] in
/-- Conjugation `.a` on the trivial module fixes the primal offset (`g.a` may be nonzero): the
`g.a` contributions cancel in `g⁻¹pg`. -/
private theorem conjP_a_of_both_trivial (p g : HeisLift A C) (hpg : ∀ v : A, p.g • v = v)
    (hgg : ∀ v : A, g.g • v = v) : (conjP p g).a = p.a := by
  rw [conjP, HeisLift.mul_a_of_trivial _ _
      (fun v => HeisLift.mul_g_trivial _ _ (HeisLift.inv_g_trivial g hgg) hpg v),
    HeisLift.mul_a_of_trivial _ _ (fun v => HeisLift.inv_g_trivial g hgg v),
    HeisLift.inv_a_of_trivial _ hgg]
  abel

omit [Finite C] [Finite A] in
/-- Conjugation `.l` on the trivial module fixes the dual offset (dual of `conjP_a_of_both_trivial`). -/
private theorem conjP_l_of_both_trivial (p g : HeisLift A C) (hpg : ∀ v : A, p.g • v = v)
    (hgg : ∀ v : A, g.g • v = v) : (conjP p g).l = p.l := by
  rw [conjP, HeisLift.mul_l_of_trivial _ _
      (fun v => HeisLift.mul_g_trivial _ _ (HeisLift.inv_g_trivial g hgg) hpg v),
    HeisLift.mul_l_of_trivial _ _ (fun v => HeisLift.inv_g_trivial g hgg v),
    HeisLift.inv_l_of_trivial _ hgg]
  abel

/-- **Wild `.z` assembly on cocycles**: peeling `wildValueR = (x₀^σ)⁻¹ · aR · x₁² · cR` keeps the
symplectic `y₂(x₀) − y₀(x₂)` (from `(x₀^σ)⁻¹`, its `inv_z` diagonal `y₂(x₂)` cancelling the
`aR`-cross-term `−y₂(aR.a) = −y₂(x₂)` because `aR.a = x₂`), the honest diagonal `y₃(x₃)` (from
`x₁²`), the opaque `ω₂` scalar `aR.z` (the `(2,2)` slot), and `cR.z = 0`. -/
theorem heisMarking_wildValueR_z_cocycle (htriv : ∀ (g : C) (a : A), g • a = a)
    (hV₂ : ∀ v : A, v + v = 0) (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A)
    (hx1 : x 1 = 0) :
    (heisMarking t x y).wildValueR.z
      = y 2 (x 0) - y 0 (x 2) + y 3 (x 3) + (heisMarking t x y).aR.z := by
  set M := heisMarking t x y with hM
  have hx0l_v : M.x₀.l = y 2 := rfl
  have hx0a_v : M.x₀.a = x 2 := rfl
  -- `.g` trivialities of the four factors and their partial products
  have hP1g : ∀ v : A, ((conjP M.x₀ M.σ)⁻¹).g • v = v := fun v =>
    HeisLift.inv_g_trivial _ (HeisLift.conjP_g_trivial M.x₀ M.σ (fun w => htriv t.x₀ w)) v
  have hP2g : ∀ v : A, M.aR.g • v = v := hgtrivR htriv M.aR
  have hP3g : ∀ v : A, (M.x₁ ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ (fun w => htriv t.x₁ w) (fun w => htriv t.x₁ w) v
  have hP12g : ∀ v : A, ((conjP M.x₀ M.σ)⁻¹ * M.aR).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hP1g hP2g v
  have hP123g : ∀ v : A, ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hP12g hP3g v
  -- `conjP x₀ σ` coordinates on the trivial module
  have hconjl : (conjP M.x₀ M.σ).l = M.x₀.l :=
    conjP_l_of_both_trivial M.x₀ M.σ (fun v => htriv t.x₀ v) (fun v => htriv t.σ v)
  have hconja : (conjP M.x₀ M.σ).a = M.x₀.a :=
    conjP_a_of_both_trivial M.x₀ M.σ (fun v => htriv t.x₀ v) (fun v => htriv t.σ v)
  have hP1z : ((conjP M.x₀ M.σ)⁻¹).z = y 2 (x 0) - y 0 (x 2) + y 2 (x 2) := by
    rw [HeisLift.inv_z, heisMarking_x0sig_z_trivial htriv t x y, hconjl, hconja, hx0l_v, hx0a_v]
  have hP1l : ((conjP M.x₀ M.σ)⁻¹).l = -M.x₀.l := by
    rw [HeisLift.inv_l_of_trivial _ (HeisLift.conjP_g_trivial M.x₀ M.σ (fun w => htriv t.x₀ w)),
      hconjl]
  -- leaf `.a`/`.z`
  have haRa : M.aR.a = x 2 := by
    rw [heisMarking_aR_a_eq, liftMarking_aR_u t x hV₂ (fun v => htriv t.x₀ v) (fun v => htriv t.τ v),
      hx1, add_zero]
  have hx1sqz : (M.x₁ ^ 2).z = y 3 (x 3) := heisMarking_x1sq_z_cocycle htriv t x y
  have hx1sqa : (M.x₁ ^ 2).a = 0 := by
    rw [pow_two, HeisLift.mul_a_of_trivial _ _ (fun v => htriv t.x₁ v)]; exact hV₂ (x 3)
  have hcRz : M.cR.z = 0 := heisMarking_cR_z_cocycle htriv t x y
  have hcRa : M.cR.a = 0 := HeisLift.commP_a_of_trivial M.x₁ M.y1R (fun v => htriv t.x₁ v)
    (HeisLift.conjP_g_trivial M.x₁ M.sigma2 (fun v => htriv t.x₁ v))
  -- the four-factor peel
  have e12 : ((conjP M.x₀ M.σ)⁻¹ * M.aR).z = y 2 (x 0) - y 0 (x 2) + M.aR.z := by
    rw [HeisLift.mul_z_of_trivial _ _ hP1g, hP1z, hP1l, haRa, hx0l_v, ElemDual.neg_apply]
    abel
  have e123 : ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2).z
      = y 2 (x 0) - y 0 (x 2) + M.aR.z + y 3 (x 3) := by
    rw [HeisLift.mul_z_of_trivial _ _ hP12g, e12, hx1sqz, hx1sqa, map_zero, add_zero]
  show ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2 * M.cR).z = _
  rw [HeisLift.mul_z_of_trivial _ _ hP123g, e123, hcRz, hcRa, map_zero, add_zero, add_zero]
  abel

omit [Finite C] [Finite A] in
/-- `aR.z = 0` when `y₂ = 0` (on cocycles): `aR = powOmega2((x₀⁻³τ))` and the base has `l = z = 0`,
so its powers do too — the `Γ_R` analogue of `heisMarking_u1_z_of_y3_zero`, on the `(2,2)` slot. -/
theorem heisMarking_aR_z_of_y2_zero (t : Marking C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) (hy1 : y 1 = 0) (hy2 : y 2 = 0) :
    (heisMarking t x y).aR.z = 0 := by
  set M := heisMarking t x y with hM
  have hx0l : M.x₀.l = 0 := hy2
  have hpow := heisLift_pow_l_z_zero M.x₀ hx0l rfl 3
  have hinvl : ((M.x₀ ^ 3)⁻¹).l = 0 := by rw [HeisLift.inv_l, hpow.1, smul_zero, neg_zero]
  have hinvz : ((M.x₀ ^ 3)⁻¹).z = 0 := by
    rw [HeisLift.inv_z, hpow.2, hpow.1, ElemDual.zero_apply, add_zero]
  have hτl : M.τ.l = 0 := hy1
  have hτz : M.τ.z = 0 := rfl
  show (powOmega2 ((M.x₀ ^ 3)⁻¹ * M.τ)).z = 0
  rw [powOmega2]
  refine (heisLift_pow_l_z_zero _ ?_ ?_ _).2
  · rw [HeisLift.mul_l, hinvl, zero_add, hτl, smul_zero]
  · rw [HeisLift.mul_z, hinvz, hτz, hinvl, ElemDual.zero_apply]; abel

omit [Finite C] [Finite A] in
/-- `aR.z = 0` when `x₂ = 0` (on cocycles), dually (`heisLift_pow_a_z_zero`). -/
theorem heisMarking_aR_z_of_x2_zero (t : Marking C)
    (x : Fin 4 → A) (y : Fin 4 → ElemDual A) (hx1 : x 1 = 0) (hx2 : x 2 = 0) :
    (heisMarking t x y).aR.z = 0 := by
  set M := heisMarking t x y with hM
  have hx0a : M.x₀.a = 0 := hx2
  have hpow := heisLift_pow_a_z_zero M.x₀ hx0a rfl 3
  have hinva : ((M.x₀ ^ 3)⁻¹).a = 0 := by rw [HeisLift.inv_a, hpow.1, smul_zero, neg_zero]
  have hinvz : ((M.x₀ ^ 3)⁻¹).z = 0 := by
    rw [HeisLift.inv_z, hpow.2, hpow.1, map_zero, add_zero]
  have hτa : M.τ.a = 0 := hx1
  have hτz : M.τ.z = 0 := rfl
  show (powOmega2 ((M.x₀ ^ 3)⁻¹ * M.τ)).z = 0
  rw [powOmega2]
  refine (heisLift_pow_a_z_zero _ ?_ ?_ _).2
  · rw [HeisLift.mul_a, hinva, zero_add, hτa, smul_zero]
  · rw [HeisLift.mul_z, hinvz, hτz, hτa, smul_zero, map_zero]; abel

/-- **The trivial-module degree-one pairing on cocycles** (⟦lem:trivial⟧, ⟦eq:scalarform⟧):
`mixedB_R t x y = y₂(x₀) − y₀(x₂) + y₃(x₃) + aR.z`, the tame part vanishing
(`stokesEval_tame_z_trivial_cocycle`) and the wild part from the peel.  The opaque `aR.z` is the
`ω₂` scalar, confined to the `(2,2)` slot (killed on single-slot duals with `y₂ = 0` or `x₂ = 0`);
the scalar Gram is `[[0,1,0],[1,0,0],[0,0,1]]` (`scalarGramR_nonsingular`). -/
theorem mixedB_cocycle_R (htriv : ∀ (g : C) (a : A), g • a = a) (hV₂ : ∀ v : A, v + v = 0)
    (t : Marking C) (x : Fin 4 → A) (y : Fin 4 → ElemDual A) (hx1 : x 1 = 0) (hy1 : y 1 = 0) :
    mixedB_R t x y = y 2 (x 0) - y 0 (x 2) + y 3 (x 3) + (heisMarking t x y).aR.z := by
  show (heisMarking t x y).tameValue.z + (heisMarking t x y).wildValueR.z = _
  rw [bridge_tame, stokesEval_tame_z_trivial_cocycle htriv (markVec t) x y hx1 hy1,
    heisMarking_wildValueR_z_cocycle htriv hV₂ t x y hx1, zero_add]

/-- **The Roe self-duality package** (`Γ_R` twin of `IsSelfDual`, over the `r_R` complex `d¹_R`):
the display-(56) numerics and a perfect degree-one pairing descending `mixedB_R`.  This is the
base-case return type of the `r_R` dévissage entry point (consumed by R26). -/
def IsSelfDual_R (t : Marking C) (A : Type*) [AddCommGroup A] [DistribMulAction C A] [Finite A] :
    Prop :=
  (Nat.card (H2wR (A := A) t) = Nat.card (fixedPts C (ElemDual A))) ∧
  (Nat.card (Z1wR (A := A) t) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
  ∃ P : H1wR (A := A) t → H1wR (A := ElemDual A) t → ZMod 2,
    (∀ (x : Z1wR (A := A) t) (y : Z1wR (A := ElemDual A) t),
        P (h1wMkR t x) (h1wMkR t y) = mixedB_R t x.val y.val) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧
    (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

/-- **The `r_R` dévissage base case** (⟦lem:trivial⟧): the trivial module `𝔽₂` is self-dual for the
Roe complex.  Both card clauses (`card_H2wR_trivial`/`card_Z1wR_trivial` with
`card_fixedPts_elemDual_trivial`) and the degree-one pairing (the scalar Gram ⟦eq:scalarform⟧) hold:
`mixedB_R` descends to `H¹_R = Z¹_R` (since `B¹_R = ⊥`), its closed form `mixedB_cocycle_R` has
unit-determinant Gram `[[0,1,0],[1,0,0],[0,0,1]]` (the `ω₂` scalar `aR.z` sits only on the `(2,2)`
slot, killed by the paired single-slot dual), and `elemDual_separates` supplies the witnesses.
Consumed by R26's `selfDual_of_simple_R`/`prop_5_15_of_simple_R`. -/
theorem trivialSelfDual_R (t : Marking C) (ht : t.TameRel) (hw : t.WildRelR)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDual_R t A := by
  refine ⟨?_, ?_, ?_⟩
  · rw [card_H2wR_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]
  · rw [card_Z1wR_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]; ring
  · have htrivD : ∀ (c : C) (l : ElemDual A), c • l = l := elemDual_smul_trivial htriv
    have hA₂d : ∀ l : ElemDual A, l + l = 0 := fun l => l.add_self_eq_zero
    have hNA : (B1wR (A := A) t).addSubgroupOf (Z1wR (A := A) t) = ⊥ := by
      rw [B1wR_trivial_eq_bot t htriv, AddSubgroup.bot_addSubgroupOf]
    have hND : (B1wR (A := ElemDual A) t).addSubgroupOf (Z1wR (A := ElemDual A) t) = ⊥ := by
      rw [B1wR_trivial_eq_bot t htrivD, AddSubgroup.bot_addSubgroupOf]
    refine ⟨Quotient.lift₂ (fun (a : Z1wR (A := A) t) (b : Z1wR (A := ElemDual A) t) =>
        mixedB_R t a.val b.val) (fun a₁ b₁ a₂ b₂ h₁ h₂ => ?_), fun x y => rfl, ?_, ?_⟩
    · have ea : a₁ = a₂ := by
        have h := QuotientAddGroup.leftRel_apply.mp h₁; rwa [hNA, AddSubgroup.mem_bot,
          neg_add_eq_zero] at h
      have eb : b₁ = b₂ := by
        have h := QuotientAddGroup.leftRel_apply.mp h₂; rwa [hND, AddSubgroup.mem_bot,
          neg_add_eq_zero] at h
      rw [ea, eb]
    · -- left nondegeneracy
      intro h hh
      induction h using QuotientAddGroup.induction_on with
      | H a =>
        have ha1 : a.val 1 = 0 := (mem_Z1wR_trivial_iff t ht hw htriv hA₂ a.val).mp a.2
        have haval : a.val ≠ 0 := fun h0 => hh (by rw [show a = 0 from Subtype.ext h0]; rfl)
        by_cases h2 : a.val 2 = 0
        · by_cases h0 : a.val 0 = 0
          · have h3 : a.val 3 ≠ 0 := fun h3 => haval (funext fun j => by fin_cases j <;> simp_all)
            obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h3
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 3 lam,
              (mem_Z1wR_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
            show mixedB_R t a.val (Pi.single 3 lam) ≠ 0
            rw [mixedB_cocycle_R htriv hA₂ t a.val (Pi.single 3 lam) ha1 (by simp),
              heisMarking_aR_z_of_y2_zero t a.val (Pi.single 3 lam) (by simp) (by simp)]
            simpa using hlam
          · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h0
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 2 lam,
              (mem_Z1wR_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
            show mixedB_R t a.val (Pi.single 2 lam) ≠ 0
            rw [mixedB_cocycle_R htriv hA₂ t a.val (Pi.single 2 lam) ha1 (by simp),
              heisMarking_aR_z_of_x2_zero t a.val (Pi.single 2 lam) ha1 h2]
            simpa using hlam
        · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h2
          refine ⟨QuotientAddGroup.mk ⟨Pi.single 0 lam,
            (mem_Z1wR_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
          show mixedB_R t a.val (Pi.single 0 lam) ≠ 0
          rw [mixedB_cocycle_R htriv hA₂ t a.val (Pi.single 0 lam) ha1 (by simp),
            heisMarking_aR_z_of_y2_zero t a.val (Pi.single 0 lam) (by simp) (by simp)]
          simpa using hlam
    · -- right nondegeneracy
      intro h hh
      induction h using QuotientAddGroup.induction_on with
      | H b =>
        have hb1 : b.val 1 = 0 := (mem_Z1wR_trivial_iff t ht hw htrivD hA₂d b.val).mp b.2
        have hbval : b.val ≠ 0 := fun h0 => hh (by rw [show b = 0 from Subtype.ext h0]; rfl)
        by_cases h2 : b.val 2 = 0
        · by_cases h0 : b.val 0 = 0
          · have h3 : b.val 3 ≠ 0 := fun h3 => hbval (funext fun j => by fin_cases j <;> simp_all)
            obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h3
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 3 v,
              (mem_Z1wR_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
            show mixedB_R t (Pi.single 3 v) b.val ≠ 0
            rw [mixedB_cocycle_R htriv hA₂ t (Pi.single 3 v) b.val (by simp) hb1,
              heisMarking_aR_z_of_x2_zero t (Pi.single 3 v) b.val (by simp) (by simp)]
            simpa using hv
          · obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h0
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 2 v,
              (mem_Z1wR_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
            show mixedB_R t (Pi.single 2 v) b.val ≠ 0
            rw [mixedB_cocycle_R htriv hA₂ t (Pi.single 2 v) b.val (by simp) hb1,
              heisMarking_aR_z_of_y2_zero t (Pi.single 2 v) b.val hb1 h2]
            simpa using hv
        · obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h2
          refine ⟨QuotientAddGroup.mk ⟨Pi.single 0 v,
            (mem_Z1wR_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
          show mixedB_R t (Pi.single 0 v) b.val ≠ 0
          rw [mixedB_cocycle_R htriv hA₂ t (Pi.single 0 v) b.val (by simp) hb1,
            heisMarking_aR_z_of_x2_zero t (Pi.single 0 v) b.val (by simp) (by simp)]
          simpa using hv

end TrivialR

/-! ## Nonsingularity of the scalar Gram (⟦eq:scalarform⟧/⟦eq:cupmatrix⟧)

The cup–Bockstein form `⟨(a,c,d),(a',c',d')⟩ = a·c' + c·a' + d·d'` on `H¹_R(𝔽₂) = 𝔽₂³` has matrix
`[[0,1,0],[1,0,0],[0,0,1]]` (⟦eq:cupmatrix⟧); a `decide` confirms it is nonsingular (left and right
nondegenerate), the finite `𝔽₂`-linear-algebra stress test underlying `trivialSelfDual_R`. -/

/-- The scalar cup–Bockstein form on `H¹_R(𝔽₂)` in coordinates `(a,c,d)` (⟦eq:scalarform⟧). -/
def scalarGramR (v w : Fin 3 → ZMod 2) : ZMod 2 := v 0 * w 1 + v 1 * w 0 + v 2 * w 2

/-- **Nonsingularity of the scalar Gram** (⟦eq:cupmatrix⟧, the `3×3` unit-determinant check): the
form `a·c' + c·a' + d·d'` is left- and right-nondegenerate over `ZMod 2`, by `decide`. -/
theorem scalarGramR_nonsingular :
    (∀ v : Fin 3 → ZMod 2, v ≠ 0 → ∃ w, scalarGramR v w ≠ 0) ∧
    (∀ w : Fin 3 → ZMod 2, w ≠ 0 → ∃ v, scalarGramR v w ≠ 0) := by
  constructor <;> decide

end FoxH

end GQ2
