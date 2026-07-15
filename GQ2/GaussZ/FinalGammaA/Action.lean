/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.GaussZ.FinalGammaA.Counts

/-!
# Actionization of the `Γ_A` Gauss counts

Transport of the signed counts to the faithful quotient action.

See `GQ2.GaussZ.FinalGammaA` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction ContCoh WordCohBridge FoxH RStageGammaA WordCoh2 QuadraticFp2

/-! ## A-4.5b: the actionization — counts at the faithful quotient

The SectionSix count pins (`prop_6_9_*`) take faithfulness and the ELEMENT-level tame
dichotomy, neither of which the seam has (`hfaith` is not block-derivable — the e6/e7
amendment).  The resolution: quotient the acting group by the action kernel.  The induced
action of `C ⧸ K` has the same orbit values (so `hsimple`/`hinv` transport verbatim), is
faithful BY CONSTRUCTION (`kerLift_injective`-shaped), and converts the action-level
dichotomy into the element-level one (`c' τ = 1 ⟺ c τ acts trivially`). -/

section Actionization

/-- **The unramified zero count from action-level hypotheses** (`prop_6_9_unramified`
through the faithful quotient): no `hfaith`, and `hunram` in the action form the seam
carries. -/
theorem zeroCount_unramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount q = 2 ^ (2 * m - 1) - 2 ^ (m - 1) := by
  classical
  -- the action kernel, directly as the acts-trivially subgroup
  set K : Subgroup C :=
    { carrier := {g : C | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul C v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => inv_smul_eq_iff.mpr (ha v).symm } with hK
  haveI hKn : K.Normal :=
    ⟨fun a ha g v => by rw [mul_smul, mul_smul, ha (g⁻¹ • v), smul_inv_smul]⟩
  letI instTQ : TopologicalSpace (C ⧸ K) := ⊥
  haveI instDQ : DiscreteTopology (C ⧸ K) := ⟨rfl⟩
  -- the descended action of the faithful quotient (same values on every class)
  letI instAQ : DistribMulAction (C ⧸ K) V :=
    { smul := fun x v => Quotient.liftOn' x (fun g => g • v) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab
        show a • v = b • v
        have hb : b = a * (a⁻¹ * b) := by group
        rw [hb, mul_smul, hab v])
      one_smul := fun v => one_smul C v
      mul_smul := fun x y v => Quotient.inductionOn₂' x y fun a b => mul_smul a b v
      smul_zero := fun x => Quotient.inductionOn' x fun a => smul_zero a
      smul_add := fun x v w => Quotient.inductionOn' x fun a => smul_add a v w }
  have hval : ∀ (g : C) (v : V), (QuotientGroup.mk g : C ⧸ K) • v = g • v :=
    fun g v => rfl
  -- the induced tame marking (continuity is free from the discrete source)
  set c' : ContinuousMonoidHom Ttame (C ⧸ K) :=
    ⟨(QuotientGroup.mk' K).comp c.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑(QuotientGroup.mk' K))).comp
        c.continuous_toFun⟩ with hc'
  have hc'surj : Function.Surjective ⇑c' := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨t, ht⟩ := hc x
    exact ⟨t, by show QuotientGroup.mk' K (c t) = _; rw [ht]⟩
  -- faithfulness by construction
  have hfaith' : ∀ g : C ⧸ K, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.eq_one_iff]
    exact fun v => (hval x v).symm.trans (hg v)
  -- the ledger hypotheses transport verbatim (same action values)
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : C ⧸ K), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hsimple W (fun g w hw => by
      have h := hW (QuotientGroup.mk g) w hw
      rwa [hval] at h)
  have hinv' : IsInvariant (C ⧸ K) q := by
    intro g v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval]
    exact hinv x v
  -- the action-level dichotomy becomes the element-level one
  have hunram' : c' tameTau = 1 := by
    show QuotientGroup.mk' K (c tameTau) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hunram
  exact SectionSix.prop_6_9_unramified c' hc'surj hfaith' hsimple' hV hunram'
    q hq hns hinv' m hm hcard

/-- **The unramified `V`-sum**: `∑ᶠ sign(q̄ v) = −2^m` from action-level hypotheses — the
value the unramified seam consumes after the `x₀`-supported section reindex. -/
theorem finsum_sign_unramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (q v) = -(2 ^ m : ℤ) :=
  finsum_sign_eq_neg_of_zeroCount q m hm
    (zeroCount_unramified_of_action c hc hsimple hV hunram q hq hns hinv m hm hcard) hcard

/-- **THE RAMIFIED PACK, DISCHARGED** (the Γ_A Gauss-sum package): `prop_6_9_ramified`'s isotypic pack
`(s r a Wt e he hVU hrank)` derived from the faithful simple ramified hypotheses via
`GQ2/RamifiedPack.lean` — the single isotype `P ∣ X^d − 1` (`exists_single_isotype`), the free
`D = AdjoinRoot P`-structure `V ≃+ D^{sV}` (`exists_isotypic_equiv`), `f = deg P` even by the
polar-adjoint involution (`even_natDegree_of_aeval_inv_eq_zero`), the `⟨cτ⟩`-module `Wt := D`
(`rootAction`/`adjoinRoot_add_self`/`isSimpleModTwo_rootAction`/`equiv_zpowers_smul`), the
σ-semilinear descent count `#V^U = 2^{r·sV}` (`card_fixed_powOmega2`), and the rank parity from
the first isomorphism theorem. -/
theorem zeroCount_qDouble_ramified_of_faithful {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  -- the standing tame facts
  have hgen : Subgroup.closure ({c tameSigma, c tameTau} : Set C) = ⊤ :=
    SectionThree.gen_ttame_quotient c.toMonoidHom c.continuous_toFun hc
  have hrelC : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
    have hrel := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using hrel
  have hoddC : Odd (orderOf (c tameTau)) := LocalKummer.odd_orderOf_tameInertia c
  have hposT : 0 < orderOf (c tameTau) := orderOf_pos _
  have hV2 : ∀ v : V, v + v = 0 := by
    -- the 2-torsion subgroup is `C`-stable and nonzero (additive Cauchy), hence `⊤`
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set T : AddSubgroup V :=
      { carrier := {v : V | v + v = 0}
        zero_mem' := by
          show (0 : V) + 0 = 0
          rw [add_zero]
        add_mem' := fun {u₁ u₂} h1 h2 => by
          show (u₁ + u₂) + (u₁ + u₂) = 0
          calc (u₁ + u₂) + (u₁ + u₂) = (u₁ + u₁) + (u₂ + u₂) := by abel
            _ = 0 := by rw [show u₁ + u₁ = 0 from h1, show u₂ + u₂ = 0 from h2, add_zero]
        neg_mem' := fun {u} h => by
          show -u + -u = 0
          calc -u + -u = -(u + u) := by abel
            _ = 0 := by rw [show u + u = 0 from h, neg_zero] } with hT
    have hstab : ∀ g : C, ∀ w ∈ T, g • w ∈ T := by
      intro g w hw
      show g • w + g • w = 0
      rw [← smul_add, show w + w = 0 from hw, smul_zero]
    have h2card : (2 : ℕ) ∣ Nat.card V := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    obtain ⟨v₀, hv₀⟩ := exists_prime_addOrderOf_dvd_card' 2 h2card
    have hv₀mem : v₀ ∈ T := by
      show v₀ + v₀ = 0
      have := addOrderOf_nsmul_eq_zero v₀
      rwa [hv₀, two_nsmul] at this
    have hv₀ne : v₀ ≠ 0 := by
      intro h0
      rw [h0, addOrderOf_zero] at hv₀
      omega
    rcases hsimple T hstab with hbot | htop
    · exact absurd (hbot ▸ hv₀mem) (fun hm' => hv₀ne (AddSubgroup.mem_bot.mp hm'))
    · exact fun v => htop.ge (AddSubgroup.mem_top v)
  have hVne : ∃ v : V, v ≠ 0 := by
    have h1 : 1 < Nat.card V := by
      rw [hcard]
      exact Nat.one_lt_two_pow_iff.mpr (by omega)
    haveI : Nontrivial V := Finite.one_lt_card_iff_nontrivial.mp h1
    exact exists_ne 0
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV2 v)
  -- the single isotype and the free `D`-structure
  obtain ⟨P, hmon, hirr, hdvdP, hkill⟩ := RamifiedPack.exists_single_isotype
    (c tameSigma) (c tameTau) hgen hrelC hoddC hposT hsimple hVne
  haveI := Fact.mk hirr
  obtain ⟨sV, e, hs1, he⟩ := RamifiedPack.exists_isotypic_equiv (c tameTau) P hirr hkill hVne
  -- root facts
  have hroot0 : AdjoinRoot.root P ≠ 0 := RamifiedPack.root_ne_zero (c tameTau) P hposT hdvdP
  have hroot1 : AdjoinRoot.root P ≠ 1 := by
    intro h1
    refine hram ?_
    have hx : AdjoinRoot.root P ^ 1 = AdjoinRoot.root P ^ 0 := by
      rw [pow_one, pow_zero, h1]
    have ht := RamifiedPack.t_pow_eq_of_root_pow_eq (c tameTau) P hfaith hx e he
    rwa [pow_one, pow_zero] at ht
  -- `f = deg P` is even, `f = 2^a·r`
  have hqt : ∀ v : V, q (c tameTau • v) = q v := fun v => hinv (c tameTau) v
  have hkill' := RamifiedPack.aeval_actEnd_inv_eq_zero (c tameTau) q hq hns hqt hkill
  have h0 := RamifiedPack.aeval_root_inv_eq_zero (c tameTau) P hroot0 hs1 e he hkill'
  have heven := RamifiedPack.even_natDegree_of_aeval_inv_eq_zero P hmon hroot0 hroot1 h0
  have hdeg0 : P.natDegree ≠ 0 := by
    haveI := RamifiedPack.finite_adjoinRoot P hmon
    have h2 : 1 < Nat.card (AdjoinRoot P) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [RamifiedPack.card_adjoinRoot P hmon] at h2
    exact Nat.one_lt_two_pow_iff.mp h2
  obtain ⟨a, r, ha, hr, hfar⟩ := RamifiedPack.exists_two_pow_mul_odd hdeg0 heven
  -- the pack fields at `Wt := AdjoinRoot P`
  letI := RamifiedPack.rootAction (c tameTau) P hposT hdvdP
  have hWt2 := RamifiedPack.adjoinRoot_add_self P
  have hWtsimple := RamifiedPack.isSimpleModTwo_rootAction (c tameTau) P hposT hdvdP
  have hWcard : Nat.card (AdjoinRoot P) = 2 ^ (2 ^ a * r) := by
    rw [RamifiedPack.card_adjoinRoot P hmon, hfar]
  have hepack := RamifiedPack.equiv_zpowers_smul (c tameTau) P hposT hdvdP e he
  have hVU := RamifiedPack.card_fixed_powOmega2 (c tameTau) P (c tameSigma) hgen hrelC hfaith
    hsimple hmon hdvdP hr ha hfar hs1 e he
  -- §6: the rank parity from the first isomorphism theorem
  have hrank : ∀ k : ℕ,
      Nat.card (SectionSix.onePlusU
          (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))).range = 2 ^ k
        → (k : ZMod 2) = (sV : ZMod 2) := by
    intro k hk
    set N := SectionSix.onePlusU (DistribMulAction.toAddEquiv V (powOmega2 (c tameSigma)))
      with hN
    have h1 : Nat.card V = Nat.card ↥N.range * Nat.card ↥N.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.ker]
      congr 1
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange N).toEquiv
    have h2 : Nat.card ↥N.ker = 2 ^ (r * sV) := by
      rw [← hVU]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [AddMonoidHom.mem_ker]
      show v + powOmega2 (c tameSigma) • v = 0 ↔ powOmega2 (c tameSigma) • v = v
      constructor
      · intro hv
        calc powOmega2 (c tameSigma) • v
            = v + (v + powOmega2 (c tameSigma) • v) := by rw [← add_assoc, hV2 v, zero_add]
          _ = v := by rw [hv, add_zero]
      · intro hv
        rw [hv]
        exact hV2 v
    rw [hcard, hk, h2, ← pow_add] at h1
    have h3 : 2 * m = k + r * sV := Nat.pow_right_injective (by norm_num) h1
    have h4 : k ≡ sV [MOD 2] := by
      rcases hr with ⟨j, hj⟩
      have hrs : r * sV = 2 * (j * sV) + sV := by rw [hj]; ring
      unfold Nat.ModEq
      omega
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr h4
  -- close with the pack
  exact SectionSix.prop_6_9_ramified c hc hfaith hsimple hram q hq hns hinv hV2
    sV r a hr ha hs1 (AdjoinRoot P) hWt2 hWtsimple hWcard e hepack hVU hrank m hm hcard

/-- **The ramified zero count from action-level hypotheses**: the A-4.5b actionization
pushed through `qDouble` — the faithful quotient has the same `σ₂`-action values
(`powOmega2_map` along `mk'`), the action-level `hram` element-izes, and the proved
faithful-level count applies verbatim. -/
theorem zeroCount_qDouble_ramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 (c tameSigma) • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  -- the faithful quotient (the A-4.5b actionization, verbatim)
  set K : Subgroup C :=
    { carrier := {g : C | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul C v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => inv_smul_eq_iff.mpr (ha v).symm } with hK
  haveI hKn : K.Normal :=
    ⟨fun a ha g v => by rw [mul_smul, mul_smul, ha (g⁻¹ • v), smul_inv_smul]⟩
  letI instTQ : TopologicalSpace (C ⧸ K) := ⊥
  haveI instDQ : DiscreteTopology (C ⧸ K) := ⟨rfl⟩
  letI instAQ : DistribMulAction (C ⧸ K) V :=
    { smul := fun x v => Quotient.liftOn' x (fun g => g • v) (fun a b hab => by
        rw [QuotientGroup.leftRel_apply] at hab
        show a • v = b • v
        have hb : b = a * (a⁻¹ * b) := by group
        rw [hb, mul_smul, hab v])
      one_smul := fun v => one_smul C v
      mul_smul := fun x y v => Quotient.inductionOn₂' x y fun a b => mul_smul a b v
      smul_zero := fun x => Quotient.inductionOn' x fun a => smul_zero a
      smul_add := fun x v w => Quotient.inductionOn' x fun a => smul_add a v w }
  have hval : ∀ (g : C) (v : V), (QuotientGroup.mk g : C ⧸ K) • v = g • v :=
    fun g v => rfl
  set c' : ContinuousMonoidHom Ttame (C ⧸ K) :=
    ⟨(QuotientGroup.mk' K).comp c.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑(QuotientGroup.mk' K))).comp
        c.continuous_toFun⟩ with hc'
  have hc'surj : Function.Surjective ⇑c' := fun y => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    obtain ⟨t, ht⟩ := hc x
    exact ⟨t, by show QuotientGroup.mk' K (c t) = _; rw [ht]⟩
  have hfaith' : ∀ g : C ⧸ K, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [QuotientGroup.eq_one_iff]
    exact fun v => (hval x v).symm.trans (hg v)
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : C ⧸ K), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hsimple W (fun g w hw => by
      have h := hW (QuotientGroup.mk g) w hw
      rwa [hval] at h)
  have hinv' : IsInvariant (C ⧸ K) q := by
    intro g v
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective g
    rw [hval]
    exact hinv x v
  -- the action-level ramification element-izes at the faithful quotient
  have hram' : c' tameTau ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := hram
    refine hv ?_
    have hmem : c tameTau ∈ K := by
      rw [show c' tameTau = QuotientGroup.mk' K (c tameTau) from rfl,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact hmem v
  -- the `σ₂`-action is unchanged (`powOmega2` commutes with `mk'`)
  have hfun : qDouble q (powOmega2 (c' tameSigma) • ·)
      = qDouble q (powOmega2 (c tameSigma) • ·) := by
    funext x
    show q x + polar q x (powOmega2 (c' tameSigma) • x)
      = q x + polar q x (powOmega2 (c tameSigma) • x)
    have hσ₂ : powOmega2 (c' tameSigma) • x = powOmega2 (c tameSigma) • x := by
      have h := powOmega2_map (QuotientGroup.mk' K) (c tameSigma)
      rw [show c' tameSigma = QuotientGroup.mk' K (c tameSigma) from rfl, ← h]
      exact hval (powOmega2 (c tameSigma)) x
    rw [hσ₂]
  rw [← hfun]
  exact zeroCount_qDouble_ramified_of_faithful c' hc'surj hfaith' hsimple' hram'
    q hq hns hinv' m hm hcard

/-- **The ramified `V`-sum**: `∑ᶠ sign(qDouble) = +2^m` — the plus finale on the
ramified count. -/
theorem finsum_sign_ramified_of_action {C : Type} [Group C] [TopologicalSpace C]
    [DiscreteTopology C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
    [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ v : V, sign (qDouble q (powOmega2 (c tameSigma) • ·) v) = (2 ^ m : ℤ) :=
  finsum_sign_eq_pos_of_zeroCount _ m hm
    (zeroCount_qDouble_ramified_of_action c hc hsimple hram q hq hns hinv m hm hcard) hcard

end Actionization

end AffineTLift

end SectionEight

end GQ2
