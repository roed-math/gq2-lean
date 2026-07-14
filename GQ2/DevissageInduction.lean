import GQ2.Devissage
import GQ2.TrivialSelfDual

/-!
# The dévissage induction: `prop_5_15` from the simple case  (ticket P-13f, induction half)

`prop_5_15_of_simple`: if `IsSelfDual t B` holds for every **simple** finite elementary-2
`C`-module `B` (hypothesis `hsimp` — the split/ramified dispatch, the other P-13f half), then it
holds for *every* finite elementary-2 `C`-module `A`.

Strong induction on `Nat.card A`:

* `Subsingleton A` — the zero module carries the trivial action, so `trivialSelfDual`
  (P-13f part (i), proved) applies;
* `IsSimpleModTwo C A` — the hypothesis `hsimp`;
* otherwise `A` has a `C`-stable additive subgroup `W ∉ {⊥, ⊤}`; the short exact sequence
  `0 → W → A → A ⧸ W → 0` (with the transported actions below) has both ends of strictly
  smaller cardinality, so the inductive hypothesis applies to them, and `lemma_5_11`
  (P-13e, proved — the mapping-cone two-out-of-three for `IsSelfDual`) yields the middle.

Infrastructure (reusable): the transported actions `stableSubAction` on `↥W` and
`stableQuotAction` on `A ⧸ W` for a `C`-stable `W`, the equivariance of `W.subtype` and
`QuotientAddGroup.mk' W`, exactness, the char-2 transfer to both subquotients, and the strict
cardinality drops.

Glue (landed): `GQ2.FoxH.prop_5_15` in `GQ2/DualityAssembly.lean` composes
`prop_5_15_of_simple t ht hw hgen` with the simple-case assembly `selfDual_of_simple`
(dispatched via the `tau_split_or_ramified` dichotomy).  Paper: Prop. 5.15, proof by
dévissage along a composition series (§5.3); `Ax = ∅` (std-3).
-/

namespace GQ2

namespace FoxH

universe u

variable {C : Type*} [Group C] [Finite C]

section StableActions

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The restricted action on a `C`-stable additive subgroup. -/
@[reducible] def stableSubAction (W : AddSubgroup A) (hW : ∀ (g : C) (w : A), w ∈ W → g • w ∈ W) :
    DistribMulAction C ↥W where
  smul c w := ⟨c • (w : A), hW c w w.2⟩
  one_smul w := Subtype.ext (one_smul C (w : A))
  mul_smul c₁ c₂ w := Subtype.ext (mul_smul c₁ c₂ (w : A))
  smul_zero c := Subtype.ext (smul_zero c)
  smul_add c w₁ w₂ := Subtype.ext (smul_add c (w₁ : A) (w₂ : A))

/-- The descended action on the quotient by a `C`-stable additive subgroup. -/
@[reducible] def stableQuotAction (W : AddSubgroup A) (hW : ∀ (g : C) (w : A), w ∈ W → g • w ∈ W) :
    DistribMulAction C (A ⧸ W) where
  smul c := QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A c)
    (fun w hw => hW c w hw)
  one_smul q := QuotientAddGroup.induction_on q fun a => by
    show QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A 1) _
      (QuotientAddGroup.mk a) = QuotientAddGroup.mk a
    rw [QuotientAddGroup.map_mk]
    show (QuotientAddGroup.mk ((1 : C) • a) : A ⧸ W) = QuotientAddGroup.mk a
    rw [one_smul]
  mul_smul c₁ c₂ q := QuotientAddGroup.induction_on q fun a => by
    show QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A (c₁ * c₂)) _
        (QuotientAddGroup.mk a)
      = QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A c₁) _
          (QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A c₂) _
            (QuotientAddGroup.mk a))
    rw [QuotientAddGroup.map_mk, QuotientAddGroup.map_mk, QuotientAddGroup.map_mk]
    show (QuotientAddGroup.mk ((c₁ * c₂) • a) : A ⧸ W) = QuotientAddGroup.mk (c₁ • c₂ • a)
    rw [mul_smul]
  smul_zero c := map_zero _
  smul_add c q₁ q₂ := map_add _ q₁ q₂

omit [Finite C] in
/-- `W.subtype` is `C`-equivariant for the restricted action. -/
theorem stableSubAction_subtype_equivariant (W : AddSubgroup A)
    (hW : ∀ (g : C) (w : A), w ∈ W → g • w ∈ W) :
    letI := stableSubAction W hW
    ∀ (c : C) (w : ↥W), W.subtype (c • w) = c • W.subtype w :=
  fun _ _ => rfl

omit [Finite C] in
/-- `QuotientAddGroup.mk' W` is `C`-equivariant for the descended action. -/
theorem stableQuotAction_mk'_equivariant (W : AddSubgroup A)
    (hW : ∀ (g : C) (w : A), w ∈ W → g • w ∈ W) :
    letI := stableQuotAction W hW
    ∀ (c : C) (a : A), QuotientAddGroup.mk' W (c • a) = c • QuotientAddGroup.mk' W a := by
  intro c a
  show (QuotientAddGroup.mk (c • a) : A ⧸ W)
    = QuotientAddGroup.map W W (DistribSMul.toAddMonoidHom A c) _ (QuotientAddGroup.mk a)
  rw [QuotientAddGroup.map_mk]
  rfl

/-- Exactness of `0 → W → A → A ⧸ W → 0` at the middle. -/
theorem subtype_range_eq_mk'_ker (W : AddSubgroup A) :
    W.subtype.range = (QuotientAddGroup.mk' W).ker :=
  (AddSubgroup.range_subtype W).trans (QuotientAddGroup.ker_mk' W).symm

/-- Char-2 transfers to a subgroup. -/
theorem two_torsion_sub (W : AddSubgroup A) (hA₂ : ∀ a : A, a + a = 0) :
    ∀ w : ↥W, w + w = 0 :=
  fun w => Subtype.ext (hA₂ (w : A))

/-- Char-2 transfers to a quotient. -/
theorem two_torsion_quot (W : AddSubgroup A) (hA₂ : ∀ a : A, a + a = 0) :
    ∀ q : A ⧸ W, q + q = 0 := by
  intro q
  induction q using QuotientAddGroup.induction_on with | _ a =>
  show (QuotientAddGroup.mk a : A ⧸ W) + QuotientAddGroup.mk a = 0
  rw [← QuotientAddGroup.mk_add, hA₂, QuotientAddGroup.mk_zero]

end StableActions

section CardDrops

variable {A : Type*} [AddCommGroup A] [Finite A]

/-- A proper additive subgroup has strictly smaller cardinality (via Lagrange:
the quotient is nontrivial). -/
theorem card_lt_of_ne_top (W : AddSubgroup A) (hWtop : W ≠ ⊤) :
    Nat.card ↥W < Nat.card A := by
  obtain ⟨a, ha⟩ : ∃ a : A, a ∉ W := by
    by_contra h
    push Not at h
    exact hWtop (eq_top_iff.mpr fun a _ => h a)
  exact Finite.card_subtype_lt ha

/-- The quotient by a nonzero additive subgroup has strictly smaller cardinality. -/
theorem card_quot_lt_of_ne_bot (W : AddSubgroup A) (hWbot : W ≠ ⊥) :
    Nat.card (A ⧸ W) < Nat.card A := by
  have hlag : Nat.card A = Nat.card (A ⧸ W) * Nat.card ↥W :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup W
  haveI : Nontrivial ↥W := (AddSubgroup.nontrivial_iff_ne_bot W).mpr hWbot
  have h2 : 2 ≤ Nat.card ↥W := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
  have hpos : 0 < Nat.card (A ⧸ W) := Nat.card_pos
  calc Nat.card (A ⧸ W) < Nat.card (A ⧸ W) * 2 := by omega
    _ ≤ Nat.card (A ⧸ W) * Nat.card ↥W := Nat.mul_le_mul_left _ h2
    _ = Nat.card A := hlag.symm

end CardDrops

/-- **Prop 5.15, dévissage half (P-13f)**: `IsSelfDual` for *all* finite elementary-2
`C`-modules, parameterized over the simple case (`hsimp` — the split/ramified dispatch).
Strong induction on `Nat.card A`; the induction step is `lemma_5_11` (P-13e) along
`0 → W → A → A ⧸ W → 0` for a `C`-stable `W ∉ {⊥, ⊤}`; the subsingleton base is
`trivialSelfDual` (P-13f part (i)). -/
theorem prop_5_15_of_simple (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates)
    (hsimp : ∀ (B : Type u) [AddCommGroup B] [DistribMulAction C B] [Finite B],
      (∀ b : B, b + b = 0) → IsSimpleModTwo C B → IsSelfDual t B)
    {A : Type u} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : IsSelfDual t A := by
  suffices h : ∀ (n : ℕ) (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A],
      Nat.card A = n → (∀ a : A, a + a = 0) → IsSelfDual t A by
    exact h (Nat.card A) A rfl hA₂
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
    intro A instAdd instAct instFin hcard hA₂
    rcases subsingleton_or_nontrivial A with hsub | hnt
    · -- zero module: the action is trivial
      exact trivialSelfDual t ht hw (fun _ _ => Subsingleton.elim _ _) hA₂
    · by_cases hsimple : IsSimpleModTwo C A
      · exact hsimp A hA₂ hsimple
      · -- extract a proper nonzero `C`-stable subgroup
        rw [IsSimpleModTwo] at hsimple
        push Not at hsimple
        obtain ⟨W, hWstable, hWbot, hWtop⟩ := hsimple hnt
        -- transported actions
        letI := stableSubAction W hWstable
        letI := stableQuotAction W hWstable
        -- char-2 on the subquotients
        have hW₂ : ∀ w : ↥W, w + w = 0 := two_torsion_sub W hA₂
        have hQ₂ : ∀ q : A ⧸ W, q + q = 0 := two_torsion_quot W hA₂
        -- strict cardinality drops
        have hltW : Nat.card ↥W < n := hcard ▸ card_lt_of_ne_top W hWtop
        have hltQ : Nat.card (A ⧸ W) < n := hcard ▸ card_quot_lt_of_ne_bot W hWbot
        -- inductive hypotheses on the ends
        have ihW : IsSelfDual t ↥W := IH _ hltW ↥W rfl hW₂
        have ihQ : IsSelfDual t (A ⧸ W) := IH _ hltQ (A ⧸ W) rfl hQ₂
        -- dévissage (P-13e) along `0 → W → A → A ⧸ W → 0`
        exact (lemma_5_11 t ht hw hgen hA₂ W.subtype (QuotientAddGroup.mk' W)
          (stableSubAction_subtype_equivariant W hWstable)
          (stableQuotAction_mk'_equivariant W hWstable)
          (AddSubgroup.subtype_injective W)
          (QuotientAddGroup.mk'_surjective W)
          (subtype_range_eq_mk'_ker W)).1 ⟨ihW, ihQ⟩

end FoxH

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Prop 5.15 = ⟦prop-defduality⟧
-/
