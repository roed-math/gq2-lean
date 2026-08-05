/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.RamifiedPackPow
import GQ2.Dyadic.TameQuotientK
import GQ2.GaussZ.FinalGammaA.Action

/-!
# The ramified candidate zero count at a general two-power tame relation

`GQ2.SectionEight.AffineTLift.zeroCount_qDouble_ramified_of_action` is the `ℚ₂` statement: it
consumes a marking `c : T_tame ↠ C` and therefore the relation `s⁻¹ t s = t²`.  This file
carries it to the relation

  `s⁻¹ t s = t ^ 2 ^ F`,  `F` odd

which is what the dyadic campaign's tame quotient `T_q` provides at residue cardinality
`q = 2 ^ F`.

Two structural observations make this cheap:

* **`lemma_6_8` and `prop_6_9_ramified` never use the tame relation.**  Their `c` enters only
  through the two elements `c σ` and `c τ`; the hypotheses `Function.Surjective c`, `hsimple`
  and `hram` of `lemma_6_8` are literally unused (they are `_`-bound in the source).  So the
  element-level forms `lemma_6_8_elem` / `prop_6_9_ramified_elem` below are transcriptions, not
  generalizations.
* All the `q`-dependence sits in the **pack construction** — the single isotype and the
  Frobenius fixed-space count — which `GQ2/Dyadic/RamifiedPackPow.lean` supplies.

`Odd F` is needed, and is sharp; see `GQ2/Dyadic/Instances/GammaLSourceArfGeneral.lean` for the
`F = 2` (`q = 4`) refutation.
-/

namespace GQ2.Dyadic.RamifiedPow

open GQ2 GQ2.SectionEight GQ2.QuadraticFp2 Polynomial
open GQ2.SectionSix (onePlusU)

/-! ## The element-level Gauss-sign pair -/

section Elem

variable {V : Type*} [AddCommGroup V] [Finite V]
variable {Hf : Type*} [Group Hf] [Finite Hf] [DistribMulAction Hf V]

omit [Finite V] in
/-- `U = S^{ω₂}` acts with 2-power order (the element-level form of the private
`SectionSix.exists_iterate_powOmega2_eq_id`). -/
theorem exists_iterate_powOmega2_eq_id_elem (S : Hf) :
    ∃ n, (⇑(DistribMulAction.toAddEquiv V (powOmega2 S)))^[2 ^ n] = id := by
  refine ⟨(orderOf S).factorization 2, ?_⟩
  have hp1 : powOmega2 S ^ 2 ^ (orderOf S).factorization 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (GQ2.FoxH.orderOf_powOmega2_dvd_two_pow S)
  funext v
  show (powOmega2 S • ·)^[2 ^ (orderOf S).factorization 2] v = v
  rw [smul_iterate_apply, hp1, one_smul]

/-- **Lemma 6.8, element level.**  A transcription of `GQ2.SectionSix.lemma_6_8` with the tame
marking `c` replaced by the pair of elements `(S, T) = (c σ, c τ)`; the original proof uses no
other feature of `c`, and in particular never uses the tame relation. -/
theorem lemma_6_8_elem (S T : Hf)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant Hf q)
    (hV2 : ∀ v : V, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers T) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers T) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r))
    (e : V ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers T) (v : V) (j : Fin s), e ((t : Hf) • v) j = t • e v j)
    (hVU : Nat.card {v : V // powOmega2 S • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 S))).range = 2 ^ k →
        (k : ZMod 2) = (s : ZMod 2)) :
    arf q = (s : ZMod 2) ∧
      Nat.card {v : V // powOmega2 S • v = v} = 2 ^ (r * s) ∧
      (∃ k : ℕ,
        Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 S))).range = 2 ^ k ∧
          (k : ZMod 2) = (s : ZMod 2)) ∧
      arf (qDouble q (powOmega2 S • ·)) = 0 := by
  classical
  letI := Fintype.ofFinite V
  set U := DistribMulAction.toAddEquiv V (powOmega2 S) with hU
  have hUq : ∀ v, q (U v) = q v := fun v => hinv (powOmega2 S) v
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := exists_iterate_powOmega2_eq_id_elem S
  obtain ⟨k, hk⟩ := GQ2.QuadraticFp2.exists_card_range_eq_two_pow hV2 (onePlusU U)
  have h88b : (k : ZMod 2) = (s : ZMod 2) := hrank k hk
  have h87 : arf q = (s : ZMod 2) := by
    letI : DistribMulAction (Subgroup.zpowers T) V :=
      DistribMulAction.compHom V (Subgroup.zpowers T).subtype
    have hTmem : T ∈ Subgroup.zpowers T := Subgroup.mem_zpowers _
    have hTgen : ∀ g : Subgroup.zpowers T,
        g ∈ Subgroup.zpowers (⟨T, hTmem⟩ : Subgroup.zpowers T) := by
      intro g
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, Subtype.ext (by push_cast; exact hn)⟩
    have hVfaith : ∀ g : Subgroup.zpowers T, (∀ v : V, g • v = v) → g = 1 :=
      fun g hg => Subtype.ext (hfaith (g : Hf) (fun v => hg v))
    refine GaussSigns.arf_eq_s_ramified ⟨T, hTmem⟩ hTgen hVfaith hWtsimple hV2 hWt2
      q hq hns (fun g v => hinv (g : Hf) v) (2 ^ (a - 1) * r) s ?_ hs1 ?_ e he
    · exact Nat.one_le_iff_ne_zero.mpr
        (Nat.mul_ne_zero (by positivity) (by rcases hr with ⟨j, hj⟩; omega))
    · rw [hWcard]; congr 1
      have h2a : (2 : ℕ) ^ a = 2 * 2 ^ (a - 1) := by
        rw [mul_comm, ← pow_succ]; congr 1; omega
      rw [h2a]; ring
  refine ⟨h87, hVU, ⟨k, hk, h88b⟩, ?_⟩
  exact GaussSigns.arf_qDouble_eq_zero q U hq hV2 hns hUq hU2 (onePlusU U) (fun _ => rfl) hk h87
    h88b

/-- **Proposition 6.9, ramified case, element level.**  Transcription of
`GQ2.SectionSix.prop_6_9_ramified`. -/
theorem prop_6_9_ramified_elem (S T : Hf)
    (hfaith : ∀ h : Hf, (∀ v : V, h • v = v) → h = 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant Hf q)
    (hV2 : ∀ v : V, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers T) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers T) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r))
    (e : V ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers T) (v : V) (j : Fin s), e ((t : Hf) • v) j = t • e v j)
    (hVU : Nat.card {v : V // powOmega2 S • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 S))).range = 2 ^ k →
        (k : ZMod 2) = (s : ZMod 2))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 S • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  set U := DistribMulAction.toAddEquiv V (powOmega2 S) with hU
  have hUq : ∀ v, q (U v) = q v := fun v => hinv (powOmega2 S) v
  have hU2 : ∃ n, (⇑U)^[2 ^ n] = id := exists_iterate_powOmega2_eq_id_elem S
  have h4 : arf (qDouble q (powOmega2 S • ·)) = 0 :=
    (lemma_6_8_elem S T hfaith q hq hns hinv hV2 s r a hr ha hs1 Wt hWt2 hWtsimple
      hWcard e he hVU hrank).2.2.2
  exact GaussSigns.zeroCount_qDouble_of_arf_zero q U hq hV2 hns hUq hU2 h4 m hm hcard

end Elem

/-! ## The faithful ramified count at the two-power relation -/

section Faithful

variable {C : Type} [Group C] [Finite C] {V : Type} [AddCommGroup V] [Finite V]
variable [DistribMulAction C V]

/-- **The ramified zero count at `s⁻¹ t s = t^{2^F}` (`F` odd), faithful case.**  The
general-`q` twin of `GQ2.SectionEight.AffineTLift.zeroCount_qDouble_ramified_of_faithful`; the
pack fields are built by `GQ2/Dyadic/RamifiedPackPow.lean`. -/
theorem zeroCount_qDouble_ramified_of_faithful_pow (s t : C) {F : ℕ} (hFodd : Odd F)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hfaith : ∀ g : C, (∀ v : V, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : t ≠ 1)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 s • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  have hFpos : 1 ≤ F := hFodd.pos
  have hEven : Even ((2 : ℕ) ^ F) := by
    obtain ⟨j, hj⟩ : ∃ j, F = j + 1 := ⟨F - 1, by omega⟩
    exact ⟨2 ^ j, by rw [hj, pow_succ]; ring⟩
  have hoddC : Odd (orderOf t) :=
    GQ2.Dyadic.TameQ.odd_order (orderOf_pos s).ne' (Nat.two_pow_pos F).ne' hEven hrel
  have hposT : 0 < orderOf t := orderOf_pos _
  have hV2 : ∀ v : V, v + v = 0 := by
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
  have hconj : ∀ g : C, ∃ j : ℕ, g⁻¹ * t * g = t ^ 2 ^ j := fun g =>
    (conj_eq_two_pow_pow s t F hgen hrel hoddC hposT g).1
  obtain ⟨P, hmon, hirr, hdvdP, hkill⟩ :=
    exists_single_isotype_of_conj t hconj hposT hsimple hVne
  haveI := Fact.mk hirr
  obtain ⟨sV, e, hs1, he⟩ := RamifiedPack.exists_isotypic_equiv t P hirr hkill hVne
  have hroot0 : AdjoinRoot.root P ≠ 0 := RamifiedPack.root_ne_zero t P hposT hdvdP
  have hroot1 : AdjoinRoot.root P ≠ 1 := by
    intro h1
    refine hram ?_
    have hx : AdjoinRoot.root P ^ 1 = AdjoinRoot.root P ^ 0 := by
      rw [pow_one, pow_zero, h1]
    have ht := RamifiedPack.t_pow_eq_of_root_pow_eq t P hfaith hx e he
    rwa [pow_one, pow_zero] at ht
  have hqt : ∀ v : V, q (t • v) = q v := fun v => hinv t v
  have hkill' := RamifiedPack.aeval_actEnd_inv_eq_zero t q hq hns hqt hkill
  have h0 := RamifiedPack.aeval_root_inv_eq_zero t P hroot0 hs1 e he hkill'
  have heven := RamifiedPack.even_natDegree_of_aeval_inv_eq_zero P hmon hroot0 hroot1 h0
  have hdeg0 : P.natDegree ≠ 0 := by
    haveI := RamifiedPack.finite_adjoinRoot P hmon
    have h2 : 1 < Nat.card (AdjoinRoot P) := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [RamifiedPack.card_adjoinRoot P hmon] at h2
    exact Nat.one_lt_two_pow_iff.mp h2
  obtain ⟨a, r, ha, hr, hfar⟩ := RamifiedPack.exists_two_pow_mul_odd hdeg0 heven
  letI := RamifiedPack.rootAction t P hposT hdvdP
  have hWt2 := RamifiedPack.adjoinRoot_add_self P
  have hWtsimple := RamifiedPack.isSimpleModTwo_rootAction t P hposT hdvdP
  have hWcard : Nat.card (AdjoinRoot P) = 2 ^ (2 ^ a * r) := by
    rw [RamifiedPack.card_adjoinRoot P hmon, hfar]
  have hepack := RamifiedPack.equiv_zpowers_smul t P hposT hdvdP e he
  have hVU := card_fixed_powOmega2_pow t P s hFodd hgen hrel hfaith hsimple hmon hdvdP hr ha
    hfar hs1 e he
  -- the rank parity from the first isomorphism theorem
  have hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv V (powOmega2 s))).range = 2 ^ k
        → (k : ZMod 2) = (sV : ZMod 2) := by
    intro k hk
    set N := onePlusU (DistribMulAction.toAddEquiv V (powOmega2 s)) with hN
    have h1 : Nat.card V = Nat.card ↥N.range * Nat.card ↥N.ker := by
      rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup N.ker]
      congr 1
      exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange N).toEquiv
    have h2 : Nat.card ↥N.ker = 2 ^ (r * sV) := by
      rw [← hVU]
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [AddMonoidHom.mem_ker]
      show v + powOmega2 s • v = 0 ↔ powOmega2 s • v = v
      constructor
      · intro hv
        calc powOmega2 s • v
            = v + (v + powOmega2 s • v) := by rw [← add_assoc, hV2 v, zero_add]
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
  exact prop_6_9_ramified_elem s t hfaith q hq hns hinv hV2 sV r a hr ha hs1
    (AdjoinRoot P) hWt2 hWtsimple hWcard e hepack hVU hrank m hm hcard

/-- **The ramified zero count at `s⁻¹ t s = t^{2^F}` (`F` odd), from action-level hypotheses.**
The A-4.5b actionization of `zeroCount_qDouble_ramified_of_faithful_pow`: pass to the faithful
quotient `C ⧸ K` by the action kernel, where the generation, the relation and the action-level
`hram` all transport, and where `powOmega2` is unchanged (`powOmega2_map` along `mk'`). -/
theorem zeroCount_qDouble_ramified_of_action_pow (s t : C) {F : ℕ} (hFodd : Odd F)
    (hgen : Subgroup.closure ({s, t} : Set C) = ⊤)
    (hrel : s⁻¹ * t * s = t ^ 2 ^ F)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : C), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    zeroCount (qDouble q (powOmega2 s • ·)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  classical
  set K : Subgroup C :=
    { carrier := {g : C | ∀ v : V, g • v = v}
      one_mem' := fun v => one_smul C v
      mul_mem' := fun {a b} ha hb v => by rw [mul_smul, hb v, ha v]
      inv_mem' := fun {a} ha v => inv_smul_eq_iff.mpr (ha v).symm } with hK
  haveI hKn : K.Normal :=
    ⟨fun a ha g v => by rw [mul_smul, mul_smul, ha (g⁻¹ • v), smul_inv_smul]⟩
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
  set s' : C ⧸ K := QuotientGroup.mk s with hs'
  set t' : C ⧸ K := QuotientGroup.mk t with ht'
  have hgen' : Subgroup.closure ({s', t'} : Set (C ⧸ K)) = ⊤ := by
    have himg : (QuotientGroup.mk' K) '' ({s, t} : Set C) = ({s', t'} : Set (C ⧸ K)) := by
      rw [Set.image_insert_eq, Set.image_singleton]
      rfl
    have hmap := congrArg (Subgroup.map (QuotientGroup.mk' K)) hgen
    rwa [MonoidHom.map_closure, himg,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective K)] at hmap
  have hrel' : s'⁻¹ * t' * s' = t' ^ 2 ^ F := by
    have h := congrArg (QuotientGroup.mk' K) hrel
    rw [map_mul, map_mul, map_inv, map_pow] at h
    exact h
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
  have hram' : t' ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ := hram
    refine hv ?_
    have hmem : t ∈ K := by
      rw [ht', show (QuotientGroup.mk t : C ⧸ K) = QuotientGroup.mk' K t from rfl,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    exact hmem v
  have hfun : qDouble q (powOmega2 s' • ·) = qDouble q (powOmega2 s • ·) := by
    funext x
    show q x + polar q x (powOmega2 s' • x) = q x + polar q x (powOmega2 s • x)
    have hσ₂ : powOmega2 s' • x = powOmega2 s • x := by
      have h := powOmega2_map (QuotientGroup.mk' K) s
      rw [hs', show (QuotientGroup.mk s : C ⧸ K) = QuotientGroup.mk' K s from rfl, ← h]
      exact hval (powOmega2 s) x
    rw [hσ₂]
  rw [← hfun]
  exact zeroCount_qDouble_ramified_of_faithful_pow s' t' hFodd hgen' hrel' hfaith' hsimple'
    hram' q hq hns hinv' m hm hcard

end Faithful

end GQ2.Dyadic.RamifiedPow
