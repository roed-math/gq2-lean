import GQ2.FoxHeisenberg

/-!
# P-13f, part (i): the trivial module `𝔽₂` is self-dual

The base case of the `prop_5_15` dévissage: `IsSelfDual t A` when `C` acts **trivially** on the
finite elementary-2 module `A` (the trivial simple `𝔽₂[C]`-module is `𝔽₂` with trivial action).

With every generator acting trivially the differentials collapse (`d⁰ = 0`, and — via the split
wild row and `d1Fun_tame`, in char 2 — `d¹ x = (x₁, x₁)`), so the cohomology is elementary:

* `Z¹ = {x | x₁ = 0} ≅ A³`,  `B¹ = 0`,  `H¹ = Z¹ ≅ A³`;
* `H² = (A×A)/Δ ≅ A`, matching `#(A^∨)^C = #A^∨ = #A`;

which gives the two card clauses of `IsSelfDual`.  The degree-one pairing is the traced mixed
coordinate `mixedB`, whose perfection is the paper's table (25) — the `3×3` Gram computation.
-/

namespace GQ2.FoxH

open scoped Classical

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- **`d¹` on the trivial module** collapses to the diagonal `x ↦ (x₁, x₁)`: the tame row
(`d1Fun_tame`) is `x₀−x₀ + x₁ − (x₁+x₁) = x₁` and the wild row (`liftMarking_wildValue_u`,
`x₁ + (1+S⁻¹)x₃`) is `x₁ + x₃ + x₃ = x₁`, both in char 2 with every generator acting trivially. -/
theorem d1Fun_of_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) (x : Fin 4 → A) :
    d1Fun t x = (x 1, x 1) := by
  have h1 : (d1Fun t x).1 = x 1 := by
    rw [d1Fun_tame t ht x]
    simp only [htriv]
    rw [hA₂ (x 1)]
    abel
  have h2 : (d1Fun t x).2 = x 1 := by
    show (liftMarking t x).wildValue.u = x 1
    rw [liftMarking_wildValue_u t x hA₂ (fun v => htriv t.x₀ v) (fun v => htriv t.x₁ v)
        (fun v => htriv t.τ v) (fun v => htriv t.sigma2 v)]
    simp only [htriv]
    rw [add_assoc, hA₂ (x 3), add_zero]
  exact Prod.ext h1 h2

/-- `d¹` bundled, on the trivial module. -/
theorem d1_of_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) (x : Fin 4 → A) :
    d1 t x = (x 1, x 1) :=
  d1Fun_of_trivial t ht hw htriv hA₂ x

/-- `d⁰ = 0` on the trivial module. -/
theorem d0_of_trivial (t : Marking C) (htriv : ∀ (c : C) (a : A), c • a = a) (v : A) :
    d0 t v = 0 := by
  funext i
  fin_cases i <;> simp [d0, htriv]

/-! ## The two cardinality clauses -/

/-- Contragredience of a trivial action is trivial. -/
theorem elemDual_smul_trivial (htriv : ∀ (c : C) (a : A), c • a = a) (g : C) (lam : ElemDual A) :
    g • lam = lam := by
  ext a; rw [ElemDual.smul_apply, htriv]

/-- `#(A^∨)^C = #A^∨ = #A`: the dual of a finite elementary-2 module has the same cardinality
(finite `𝔽₂`-vector space is self-dual in cardinality), and every point is `C`-fixed here. -/
theorem card_fixedPts_elemDual_trivial (htriv : ∀ (c : C) (a : A), c • a = a)
    (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (fixedPts C (ElemDual A)) = Nat.card A := by
  have hset : fixedPts C (ElemDual A) = Set.univ := by
    ext lam
    simp only [fixedPts, Set.mem_setOf_eq, Set.mem_univ, iff_true]
    exact fun g => elemDual_smul_trivial htriv g lam
  rw [hset, Nat.card_congr (Equiv.Set.univ _)]
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  have e1 : (A →+ ZMod 2) ≃+ Module.Dual (ZMod 2) A := AddMonoidHom.toZModLinearMapEquiv 2
  obtain ⟨e2⟩ : Nonempty (A ≃ₗ[ZMod 2] Module.Dual (ZMod 2) A) :=
    Basis.linearEquiv_dual_iff_finiteDimensional.mpr inferInstance
  calc Nat.card (ElemDual A) = Nat.card (A →+ ZMod 2) := rfl
    _ = Nat.card (Module.Dual (ZMod 2) A) := Nat.card_congr e1.toEquiv
    _ = Nat.card A := (Nat.card_congr e2.toEquiv).symm

/-- On the trivial module `range d¹ = Δ` (the diagonal `a ↦ (a,a)`), of cardinality `#A`. -/
theorem card_range_d1_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (d1 (A := A) t).range = Nat.card A := by
  have hdgapp : ∀ a : A, ((AddMonoidHom.id A).prod (AddMonoidHom.id A)) a = (a, a) := fun _ => rfl
  have hinj : Function.Injective ⇑((AddMonoidHom.id A).prod (AddMonoidHom.id A)) :=
    fun a b h => congrArg Prod.fst h
  have hrange : (d1 (A := A) t).range = ((AddMonoidHom.id A).prod (AddMonoidHom.id A)).range := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact ⟨x 1, by simp only [d1_of_trivial t ht hw htriv hA₂ x, hdgapp]⟩
    · rintro _ ⟨a, rfl⟩
      exact ⟨fun _ => a, by simp only [d1_of_trivial t ht hw htriv hA₂ (fun _ => a), hdgapp]⟩
  rw [hrange]
  exact (Nat.card_congr (AddMonoidHom.ofInjective hinj).toEquiv).symm

/-- **Card clause for `H²`**: `#H²w = #A` on the trivial module (`H² = (A×A)/Δ`). -/
theorem card_H2w_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (H2w (A := A) t) = Nat.card A := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hlag :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (d1 (A := A) t).range
  rw [card_range_d1_trivial t ht hw htriv hA₂, Nat.card_prod] at hlag
  -- hlag : Nat.card A * Nat.card A = Nat.card ((A×A) ⧸ range) * Nat.card A
  show Nat.card ((A × A) ⧸ (d1 (A := A) t).range) = Nat.card A
  exact Nat.eq_of_mul_eq_mul_right hpos hlag.symm

/-- **Card clause for `Z¹`**: `#Z¹w = (#A)³` on the trivial module (`Z¹ = {x | x₁ = 0}`). -/
theorem card_Z1w_trivial (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (Z1w (A := A) t) = Nat.card A ^ 3 := by
  have hpos : 0 < Nat.card A := Nat.card_pos
  have hfiso : Nat.card ((Fin 4 → A) ⧸ (d1 (A := A) t).ker) = Nat.card A := by
    rw [Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (d1 (A := A) t)).toEquiv,
      card_range_d1_trivial t ht hw htriv hA₂]
  have hlag := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (d1 (A := A) t).ker
  rw [hfiso] at hlag
  -- hlag : Nat.card (Fin 4 → A) = Nat.card A * Nat.card (ker)
  have hcard4 : Nat.card (Fin 4 → A) = Nat.card A ^ 4 := by
    rw [Nat.card_fun,
      show Nat.card (Fin 4) = 4 from by rw [Nat.card_eq_fintype_card, Fintype.card_fin]]
  rw [hcard4] at hlag
  -- (Nat.card A)^4 = Nat.card A * Nat.card (ker)
  show Nat.card ((d1 (A := A) t).ker) = Nat.card A ^ 3
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hlag]; ring

/-! ## `IsSelfDual` for the trivial module

The two card clauses are `card_H2w_trivial`/`card_Z1w_trivial` combined with
`card_fixedPts_elemDual_trivial`.  The degree-one pairing (clause 3) is the paper's **table (25)** —
the explicit `3×3` Gram matrix of the traced mixed coordinate `mixedB` on the cocycle basis
`{x₀, x₂, x₃}` (recall `Z¹ = {x | x₁ = 0}`, `B¹ = 0`, so `H¹ = Z¹`), whose nonsingularity gives
perfection via the evaluation pairing `dualEval : A × A^∨ → 𝔽₂`.

That Gram computation is **not yet available**: `mixedB` on general (all-four-coordinate) offsets
requires the degree-one `.z`-coordinate toolkit (`heisMarking_*_z`), which the repo currently proves
only for **x₀-supported** reps (`heisMarking_wildValue_z`, the split case).  It also needs `mixedB`
bilinearity (unproven) to assemble the Gram matrix from basis pairs.  Both are sizeable additions,
tracked as the remaining half of P-13f(i). -/

/-- **P-13f, part (i)**: the trivial module `𝔽₂` is self-dual.  Card clauses fully proven; the
degree-one pairing (clause 3, the table-(25) Gram computation) is the outstanding piece — see the
section note above. -/
theorem trivialSelfDual (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDual t A := by
  refine ⟨?_, ?_, ?_⟩
  · -- `#H²w = #(A^∨)^C`  (both `= #A`)
    rw [card_H2w_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]
  · -- `#Z¹w = (#A)² · #(A^∨)^C`  (`(#A)³ = (#A)² · #A`)
    rw [card_Z1w_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]
    ring
  · -- The degree-one pairing: table (25).  Outstanding (see section note).
    sorry

end GQ2.FoxH
