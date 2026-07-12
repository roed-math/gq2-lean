import GQ2.FoxHeisenberg
import GQ2.MixedBilinear

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
    rw [liftMarking_wildValue_u t x hA₂ (htriv t.x₀) (htriv t.x₁) (htriv t.τ) (htriv t.sigma2)]
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
  have hset : fixedPts C (ElemDual A) = Set.univ :=
    Set.eq_univ_of_forall fun lam g => elemDual_smul_trivial htriv g lam
  rw [hset, Nat.card_congr (Equiv.Set.univ _)]
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  have e1 : (A →+ ZMod 2) ≃+ Module.Dual (ZMod 2) A := AddMonoidHom.toZModLinearMapEquiv 2
  obtain ⟨e2⟩ : Nonempty (A ≃ₗ[ZMod 2] Module.Dual (ZMod 2) A) :=
    Basis.linearEquiv_dual_iff_finiteDimensional.mpr inferInstance
  exact Nat.card_congr (e1.toEquiv.trans e2.toEquiv.symm)

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
    rw [Nat.card_fun, Nat.card_fin]
  rw [hcard4] at hlag
  -- (Nat.card A)^4 = Nat.card A * Nat.card (ker)
  show Nat.card ((d1 (A := A) t).ker) = Nat.card A ^ 3
  refine Nat.eq_of_mul_eq_mul_left hpos ?_
  rw [← hlag]; ring

/-! ## `IsSelfDual` for the trivial module

The two card clauses are `card_H2w_trivial`/`card_Z1w_trivial` combined with
`card_fixedPts_elemDual_trivial`.  The degree-one pairing (clause 3) is the paper's **table (25)** —
the `3×3` Gram matrix of `mixedB` on the cocycle basis `{x₀, x₂, x₃}` (recall `Z¹ = {x | x₁ = 0}`,
`B¹ = 0`, so `H¹ = Z¹`).

The pairing is built in `GQ2/MixedBilinear.lean` (all std-3): `mixedB` bilinearity, and the closed
form `mixedB_cocycle : mixedB t x y = y₂(x₂) + y₃(x₀) − y₀(x₃) + u₁.z` on cocycles, with the ω₂
scalar `u₁.z` confined to the `(3,3)` slot (`heisMarking_u1_z_of_{x3,y3}_zero`).  The Gram matrix is
therefore unit-determinant regardless of `u₁.z`, and `elemDual_separates` gives nondegeneracy.
`trivialSelfDual` descends `mixedB` to `H¹w = Z¹w` via `Quotient.lift₂` and closes both
nondegeneracy conditions by the case analysis below — **fully proven, std-3**. -/

/-- The `𝔽₂`-dual separates points of a finite elementary-2 module. -/
theorem elemDual_separates (hA₂ : ∀ a : A, a + a = 0) {a : A} (ha : a ≠ 0) :
    ∃ lam : ElemDual A, lam a ≠ 0 := by
  haveI : Module (ZMod 2) A := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hA₂ v)
  obtain ⟨f, hf⟩ := Module.Projective.exists_dual_ne_zero (ZMod 2) ha
  exact ⟨f.toAddMonoidHom, hf⟩

/-- On the trivial module `Z¹w = {x | x₁ = 0}`. -/
theorem mem_Z1w_trivial_iff (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) (x : Fin 4 → A) :
    x ∈ Z1w (A := A) t ↔ x 1 = 0 := by
  show x ∈ (d1 (A := A) t).ker ↔ _
  rw [AddMonoidHom.mem_ker, d1_of_trivial t ht hw htriv hA₂, Prod.mk_eq_zero, and_self]

/-- On the trivial module `B¹w = ⊥` (`d⁰ = 0`), so `H¹w = Z¹w` and the class map is injective. -/
theorem B1w_trivial_eq_bot (t : Marking C) (htriv : ∀ (c : C) (a : A), c • a = a) :
    B1w (A := A) t = ⊥ := by
  rw [eq_bot_iff]
  rintro y ⟨v, rfl⟩
  exact (AddSubgroup.mem_bot).mpr (d0_of_trivial t htriv v)

/-- **P-13f, part (i)**: the trivial module `𝔽₂` is self-dual.  Both card clauses and the degree-one
pairing (table (25)) are proven: `mixedB` descends to `H¹w = Z¹w` (since `B¹w = ⊥`), its closed form
`mixedB_cocycle = y₂(x₂)+y₃(x₀)−y₀(x₃)+u₁.z` has unit-determinant Gram matrix (the ω₂ scalar `u₁.z`
sits only on the `(3,3)` slot, killed by choosing the paired dual coordinate `≠ 3`), and
`elemDual_separates` supplies the nonzero dual functionals. -/
theorem trivialSelfDual (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (htriv : ∀ (c : C) (a : A), c • a = a) (hA₂ : ∀ a : A, a + a = 0) :
    IsSelfDual t A := by
  refine ⟨?_, ?_, ?_⟩
  · -- `#H²w = #(A^∨)^C`  (both `= #A`)
    rw [card_H2w_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]
  · -- `#Z¹w = (#A)² · #(A^∨)^C`  (`(#A)³ = (#A)² · #A`)
    rw [card_Z1w_trivial t ht hw htriv hA₂, card_fixedPts_elemDual_trivial htriv hA₂]
    ring
  · -- The degree-one pairing (table 25): descend `mixedB` and prove perfection.
    have htrivD : ∀ (c : C) (l : ElemDual A), c • l = l := elemDual_smul_trivial htriv
    have hA₂d : ∀ l : ElemDual A, l + l = 0 := fun l => l.add_self_eq_zero
    have hNA : (B1w (A := A) t).addSubgroupOf (Z1w (A := A) t) = ⊥ := by
      rw [B1w_trivial_eq_bot t htriv, AddSubgroup.bot_addSubgroupOf]
    have hND : (B1w (A := ElemDual A) t).addSubgroupOf (Z1w (A := ElemDual A) t) = ⊥ := by
      rw [B1w_trivial_eq_bot t htrivD, AddSubgroup.bot_addSubgroupOf]
    refine ⟨Quotient.lift₂ (fun (a : Z1w (A := A) t) (b : Z1w (A := ElemDual A) t) =>
        mixedB t a.val b.val) (fun a₁ b₁ a₂ b₂ h₁ h₂ => ?_), fun x y => rfl, ?_, ?_⟩
    · -- well-defined: the class group is `⊥`, so the relation is equality
      have ea : a₁ = a₂ := by
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
        have ha1 : a.val 1 = 0 := (mem_Z1w_trivial_iff t ht hw htriv hA₂ a.val).mp a.2
        have haval : a.val ≠ 0 := fun h0 => hh (by rw [show a = 0 from Subtype.ext h0]; rfl)
        by_cases h2 : a.val 2 = 0
        · by_cases h3 : a.val 3 = 0
          · have h0 : a.val 0 ≠ 0 := fun h0 => haval (funext fun j => by fin_cases j <;> simp_all)
            obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h0
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 3 lam,
              (mem_Z1w_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
            show mixedB t a.val (Pi.single 3 lam) ≠ 0
            rw [mixedB_cocycle htriv hA₂ t a.val (Pi.single 3 lam) ha1 (by simp),
              heisMarking_u1_z_of_x3_zero htriv t a.val (Pi.single 3 lam) ha1 (by simp) h3]
            simpa using hlam
          · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h3
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 0 lam,
              (mem_Z1w_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
            show mixedB t a.val (Pi.single 0 lam) ≠ 0
            rw [mixedB_cocycle htriv hA₂ t a.val (Pi.single 0 lam) ha1 (by simp),
              heisMarking_u1_z_of_y3_zero htriv t a.val (Pi.single 0 lam) ha1 (by simp) (by simp)]
            simpa using hlam
        · obtain ⟨lam, hlam⟩ := elemDual_separates hA₂ h2
          refine ⟨QuotientAddGroup.mk ⟨Pi.single 2 lam,
            (mem_Z1w_trivial_iff (A := ElemDual A) t ht hw htrivD hA₂d _).mpr (by simp)⟩, ?_⟩
          show mixedB t a.val (Pi.single 2 lam) ≠ 0
          rw [mixedB_cocycle htriv hA₂ t a.val (Pi.single 2 lam) ha1 (by simp),
            heisMarking_u1_z_of_y3_zero htriv t a.val (Pi.single 2 lam) ha1 (by simp) (by simp)]
          simpa using hlam
    · -- right nondegeneracy
      intro h hh
      induction h using QuotientAddGroup.induction_on with
      | H b =>
        have hb1 : b.val 1 = 0 := (mem_Z1w_trivial_iff t ht hw htrivD hA₂d b.val).mp b.2
        have hbval : b.val ≠ 0 := fun h0 => hh (by rw [show b = 0 from Subtype.ext h0]; rfl)
        by_cases h2 : b.val 2 = 0
        · by_cases h3 : b.val 3 = 0
          · have h0 : b.val 0 ≠ 0 := fun h0 => hbval (funext fun j => by fin_cases j <;> simp_all)
            obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h0
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 3 v,
              (mem_Z1w_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
            show mixedB t (Pi.single 3 v) b.val ≠ 0
            rw [mixedB_cocycle htriv hA₂ t (Pi.single 3 v) b.val (by simp) hb1,
              heisMarking_u1_z_of_y3_zero htriv t (Pi.single 3 v) b.val (by simp) hb1 h3]
            simpa using hv
          · obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h3
            refine ⟨QuotientAddGroup.mk ⟨Pi.single 0 v,
              (mem_Z1w_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
            show mixedB t (Pi.single 0 v) b.val ≠ 0
            rw [mixedB_cocycle htriv hA₂ t (Pi.single 0 v) b.val (by simp) hb1,
              heisMarking_u1_z_of_x3_zero htriv t (Pi.single 0 v) b.val (by simp) hb1 (by simp)]
            simpa using hv
        · obtain ⟨v, hv⟩ := DFunLike.ne_iff.mp h2
          refine ⟨QuotientAddGroup.mk ⟨Pi.single 2 v,
            (mem_Z1w_trivial_iff t ht hw htriv hA₂ _).mpr (by simp)⟩, ?_⟩
          show mixedB t (Pi.single 2 v) b.val ≠ 0
          rw [mixedB_cocycle htriv hA₂ t (Pi.single 2 v) b.val (by simp) hb1,
            heisMarking_u1_z_of_x3_zero htriv t (Pi.single 2 v) b.val (by simp) hb1 (by simp)]
          simpa using hv

end GQ2.FoxH
