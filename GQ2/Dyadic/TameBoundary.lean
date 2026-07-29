/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.TameQuotientK
import GQ2.Dyadic.Word.Eval
import GQ2.BoundaryMapsWitness

/-!
# The common boundary at a general residue cardinality (dyadic campaign, ticket F3)

The packet's §3 above the statement layer: Lemma 3.1 (tame inertia is pro-odd), Lemma 3.2
(`ker ν₂` is pro-odd), Proposition 3.4 (the tame and maximal-pro-`2` specializations of an
admissible `Γ_R`) and Theorem 3.5 (joint boundary surjectivity — relative Goursat over `ℤ₂`).

`Tq`, `nuTq`, `tame_relation_q`, `gen_tq_quotient`, `o2_Tq_eq_bot` and `tq_two_equiv` live one
layer down, in the leaf `GQ2/Dyadic/TameQuotientK.lean`, because `GQ2/Foundations/Axioms.lean`
must be able to import them (AX4 memo Q4).  This file may — and does — import the `ℚ₂` proof
stack, so the pure-algebra fibred-product kit (`GQ2.SectionThree.fiberProductExists`,
`proPKernel_image_ge`) is reused rather than restated.  **No `ℚ₂` file is edited** (plan A6).

## Contents

* **§1 — packet Lemma 3.1** (`tqTau_odd_order_map`, `map_tqTau_eq_one_of_isPGroup`,
  `maxProPMk_tqTau`): in every finite quotient of `T_q` the image of `τ` has order prime to `q`;
  in particular `τ` dies in every pro-`2` quotient.  The `q = 2` precedents are
  `GQ2.Tame.tame_odd_order` and `GQ2.map_tameTau_eq_one`.
* **§2 — packet Lemma 3.2** (`ker_nuTq_le_proPKernel`, `map_eq_one_of_nuTq_eq_one`): `ker ν₂` is
  pro-odd, in the operative form the boundary argument consumes — it is contained in the pro-`2`
  kernel of `T_q`, so every continuous map to a pro-`2` group factors through `ν₂`.  The `q = 2`
  precedent is `GQ2.ker_nuT_le_proPKernel`.
* **§3 — packet Theorem 3.5** (`boundarySubgroupQ`, `hkerQ_uniform`,
  `boundary_jointly_surjective`): the relative Goursat step over `ℤ₂`.  A common quotient of
  `ker(T_q → ℤ₂)` (pro-odd) and `ker(D → ℤ₂)` (pro-`2`, since `D` is) is trivial, so the map to
  the fibre product `∂ = T_q ×_{ℤ₂} D` is surjective.  The statement is generic in the source, so
  it covers both halves of the packet's theorem — the `Γ_R` side and the `G_K` side ("*the field
  case is identical, using the wild inertia and maximal pro-2 quotient of `G_K`*").
* **§4 — packet Proposition 3.4** (`GammaR`, `KillsWild`, `tameR`, `gammaR_tame_equiv`,
  `prop_3_4_one`, `prop_3_4_two`, `prop_3_4_three`): the two specializations of an admissible
  `Γ_R`, driven by F2's substitution operators `killWild` / `pro2` and their soundness theorems
  `Marking.eval_killWild` / `Marking.eval_pro2` (never by hand rewrites).
* **§5 — the mandated `q`-distinguishing regression** (`tqHomEquiv`, `card_hom_tq_zmodThree_*`):
  a kernel-`decide` count of `Hom_cont(T_q, ℤ/3)` separating `q = 2` from `q = 4`.  This is AX4
  memo risk **R2**'s guard: an unpinned residue degree would assert `T_2 ≅ T_4`, and the count
  refutes that.  See the note at §5 on the memo's arithmetic.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionThree

/-! ## §1. Packet Lemma 3.1: tame inertia is pro-odd -/

section LemmaThreeOne

variable {q : ℕ}

/-- **Packet Lemma 3.1, finite-image form.**  In every finite continuous quotient of `T_q` (at
even `q ≠ 0`) the image of `τ` has odd order.  Packet: *"The elements `τ` and `τ^q` are
conjugate, hence have the same order.  But `ord(τ^q) = m/gcd(m, q)`, so `gcd(m, q) = 1`."*  No
surjectivity is needed: the relation alone forces it. -/
theorem tqTau_odd_order_map (hq0 : q ≠ 0) (hqe : Even q) {H : Type*} [Group H] [Finite H]
    (f : Tq q →* H) : Odd (orderOf (f (tqTau q))) :=
  TameQ.odd_order (orderOf_pos (f (tqSigma q))).ne' hq0 hqe (tame_rel_map_q f)

/-- **τ-death in a finite `2`-group** at general `q`: a homomorphism from `T_q` into a finite
`2`-group kills the tame generator.  (`q = 2` precedent: `GQ2.map_tameTau_eq_one`.) -/
theorem map_tqTau_eq_one_of_isPGroup (hq0 : q ≠ 0) (hqe : Even q) {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsPGroup 2 Q) (f : Tq q →* Q) : f (tqTau q) = 1 := by
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQ) (f (tqTau q))
  have hodd := tqTau_odd_order_map hq0 hqe f
  rw [hk] at hodd
  rcases Nat.eq_zero_or_pos k with rfl | hpos
  · rw [pow_zero] at hk
    exact orderOf_eq_one_iff.mp hk
  · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩))

/-- **`τ` dies in the maximal pro-`2` quotient** `T_q(2)`.  (`q = 2` precedent:
`GQ2.maxProPMk_tameTau`.) -/
theorem maxProPMk_tqTau (hq0 : q ≠ 0) (hqe : Even q) :
    maxProPMk 2 (Tq q) (tqTau q) = 1 := by
  refine (quotientMk_eq_one_iff (proPKernel 2 (Tq q))).mpr ?_
  rw [proPKernel, Subgroup.mem_iInf]
  rintro ⟨U, hU⟩
  exact (QuotientGroup.eq_one_iff _).mp
    (map_tqTau_eq_one_of_isPGroup hq0 hqe hU (QuotientGroup.mk' U.toSubgroup))

end LemmaThreeOne

/-! ## §2. Packet Lemma 3.2: `ker ν₂` is pro-odd

The operative form: `ker ν₂ ≤ proPKernel 2 (T_q)`.  Equivalently, `ν₂ : T_q ↠ ℤ₂` *is* the
maximal pro-`2` quotient of `T_q`, so nothing pro-`2` survives inside its kernel.  The proof
builds the `ẑ`-power section `ẑ ↦ (σ̄)^ẑ` out of the maximal pro-`2` quotient, matches it against
`maxProPMk` on the two topological generators (using §1's τ-death), and concludes by density. -/

section LemmaThreeTwo

variable {q : ℕ}

/-- **Packet Lemma 3.2** (operative form): `ker ν₂ ≤ proPKernel 2 (T_q)`.  (`q = 2` precedent:
`GQ2.ker_nuT_le_proPKernel`.) -/
theorem ker_nuTq_le_proPKernel (hq0 : q ≠ 0) (hqe : Even q) :
    (nuTq q).toMonoidHom.ker ≤ proPKernel 2 (Tq q) := by
  set s : maxProPQuotient 2 (Tq q) := maxProPMk 2 (Tq q) (tqSigma q)
  let zhatHom : ContinuousMonoidHom Zhat (maxProPQuotient 2 (Tq q)) :=
    ⟨{ toFun := fun γ => s ^ᶻ γ, map_one' := zpowHat_one s,
       map_mul' := fun a b => zpowHat_mul s a b }, continuous_zpowHat s⟩
  let ρ' : ContinuousMonoidHom Ztwo (maxProPQuotient 2 (Tq q)) :=
    (maxProPHomEquiv (G := Zhat) isProP_maxProPQuotient).symm zhatHom
  have hρ : ∀ z : Zhat, ρ' (maxProPMk 2 Zhat z) = s ^ᶻ z := fun z => rfl
  have key : ∀ y, (maxProPMk 2 (Tq q)) y = (ρ'.comp (nuTq q)) y := by
    refine TopGen.monoidHom_eq (f := (maxProPMk 2 (Tq q)).toMonoidHom)
      (g := (ρ'.comp (nuTq q)).toMonoidHom)
      (maxProPMk 2 (Tq q)).continuous_toFun (ρ'.comp (nuTq q)).continuous_toFun (topGen_tq q) ?_
    rintro z (rfl | rfl)
    · show maxProPMk 2 (Tq q) (tqSigma q) = ρ' (nuTq q (tqSigma q))
      rw [nuTq_tqSigma, show ztwoOne = maxProPMk 2 Zhat (Zhat.ofInt 1) from rfl, hρ,
        zpowHat_ofInt, zpow_one]
    · show maxProPMk 2 (Tq q) (tqTau q) = ρ' (nuTq q (tqTau q))
      rw [nuTq_tqTau, map_one, maxProPMk_tqTau hq0 hqe]
  intro x hx
  have hnu : nuTq q x = 1 := hx
  have hmk : maxProPMk 2 (Tq q) x = 1 := by
    rw [key x]; show ρ' (nuTq q x) = 1; rw [hnu, map_one]
  exact (QuotientGroup.eq_one_iff x).mp hmk

/-- **The factoring**: a continuous hom `φ : T_q → Q` into a pro-`2` group kills everything `ν₂`
kills.  (`q = 2` precedent: `GQ2.map_eq_one_of_nuT_eq_one`.) -/
theorem map_eq_one_of_nuTq_eq_one (hq0 : q ≠ 0) (hqe : Even q) {Q : Type*} [Group Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hQ : IsProP 2 Q) (φ : ContinuousMonoidHom (Tq q) Q)
    {x : Tq q} (hx : nuTq q x = 1) : φ x = 1 :=
  proPKernel_le_ker hQ φ (ker_nuTq_le_proPKernel hq0 hqe hx)

end LemmaThreeTwo

/-! ## §3. Packet Theorem 3.5: joint boundary surjectivity

*"The image projects onto both factors.  Apply the relative form of Goursat's lemma over `ℤ₂`.
Any failure of surjectivity would give a nontrivial common quotient of `ker(T_{q_K} → ℤ₂)` and
`ker(D_K → ℤ₂)`.  The former is pro-odd by Lemma 3.2; the latter is pro-`2`, because `D_K` is
pro-`2`.  Their only common profinite quotient is trivial."*

In the formalization the Goursat step is packaged by the `ℚ₂` development's pure-algebra
`fiberProductExists`: it needs a source-side surjection, the compatibility square, and the
kernel condition `pro2X(ker tameX) ⊇ ker ν₂`.  That kernel condition is `hkerQ_uniform` below,
and *it* is where the pro-odd/pro-`2` dichotomy enters, through §2. -/

section ThmThreeFive

variable {q : ℕ}

/-- The general-`q` boundary `∂ = T_q ×_{ℤ₂} D`, as the equalizer subgroup of `T_q × D`
(the general form of `GQ2.boundarySubgroup`, eq. (26)). -/
def boundarySubgroupQ (q : ℕ) {D : Type} [Group D] [TopologicalSpace D]
    (nu2 : ContinuousMonoidHom D Ztwo) : Subgroup (Tq q × D) where
  carrier := {x | nuTq q x.1 = nu2 x.2}
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_one, Prod.snd_one, map_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

@[simp] theorem mem_boundarySubgroupQ {D : Type} [Group D] [TopologicalSpace D]
    (nu2 : ContinuousMonoidHom D Ztwo) (x : Tq q × D) :
    x ∈ boundarySubgroupQ q nu2 ↔ nuTq q x.1 = nu2 x.2 := Iff.rfl

variable {dom D : Type} [Group dom] [TopologicalSpace dom] [IsTopologicalGroup dom]
  [CompactSpace dom] [T2Space dom] [TotallyDisconnectedSpace dom]
  [Group D] [TopologicalSpace D]

/-- **The kernel condition of the relative Goursat step.**  `pro2X` maps `ker tameX` onto
`ker ν₂`, via `ker ν₂ ≤ proPKernel 2 (T_q) ≤ tameX(proPKernel 2 dom) ≤ tameX(ker pro2X)`.

This is where the packet's *"pro-odd versus pro-2"* dichotomy is used: the first inclusion is
Lemma 3.2 (§2) and the last one is the hypothesis that the pro-`2` kernel of the source dies in
`D`.  The `q = 2` precedent is `GQ2.SectionThree.hker_uniform`. -/
theorem hkerQ_uniform (hq0 : q ≠ 0) (hqe : Even q)
    (nu2 : ContinuousMonoidHom D Ztwo)
    (tameX : ContinuousMonoidHom dom (Tq q)) (pro2X : ContinuousMonoidHom dom D)
    (htame : Function.Surjective tameX) (hpro : Function.Surjective pro2X)
    (hkerpro : proPKernel 2 dom ≤ pro2X.toMonoidHom.ker)
    (hcompat : ∀ g, nuTq q (tameX g) = nu2 (pro2X g))
    (b : D) (hb : nu2 b = 1) :
    ∃ g : dom, tameX g = 1 ∧ pro2X g = b := by
  obtain ⟨g₀, hg₀⟩ := hpro b
  have htk : nuTq q (tameX g₀) = 1 := by rw [hcompat g₀, hg₀]; exact hb
  have htg0 : tameX g₀ ∈ proPKernel 2 (Tq q) := ker_nuTq_le_proPKernel hq0 hqe htk
  have hmem : tameX g₀ ∈ (proPKernel 2 dom).map tameX.toMonoidHom :=
    proPKernel_image_ge tameX htame htg0
  obtain ⟨k, hk, hkval⟩ := Subgroup.mem_map.mp hmem
  have hkval' : tameX k = tameX g₀ := hkval
  refine ⟨g₀ * k⁻¹, ?_, ?_⟩
  · show tameX (g₀ * k⁻¹) = 1
    rw [map_mul, map_inv, hkval', mul_inv_cancel]
  · have hkpro : pro2X k = 1 := by
      have hmem2 : k ∈ pro2X.toMonoidHom.ker := hkerpro hk
      rwa [MonoidHom.mem_ker] at hmem2
    show pro2X (g₀ * k⁻¹) = b
    rw [map_mul, map_inv, hkpro, inv_one, mul_one, hg₀]

/-- **Packet Theorem 3.5 (joint boundary surjectivity).**  A profinite group carrying a
surjection onto `T_q`, a surjection onto a pro-`2` group `D` whose kernel contains the source's
pro-`2` kernel, and the `ν`-compatibility square, maps **onto** the fibre product
`∂ = T_q ×_{ℤ₂} D`.

The statement is deliberately generic in the source `dom`, so it serves both halves of the
packet's theorem: the `Γ_R` side (§4) and the `G_K` side, where `tameX = tameF_K`,
`pro2X = pro2F_K` and the compatibility square is AX4's `compatF` — *"the field case is
identical, using the wild inertia and maximal pro-2 quotient of `G_K`"*. -/
theorem boundary_jointly_surjective (hq0 : q ≠ 0) (hqe : Even q)
    (nu2 : ContinuousMonoidHom D Ztwo)
    (tameX : ContinuousMonoidHom dom (Tq q)) (pro2X : ContinuousMonoidHom dom D)
    (htame : Function.Surjective tameX) (hpro : Function.Surjective pro2X)
    (hkerpro : proPKernel 2 dom ≤ pro2X.toMonoidHom.ker)
    (hcompat : ∀ g, nuTq q (tameX g) = nu2 (pro2X g)) :
    Function.Surjective (fun g : dom =>
      (⟨(tameX g, pro2X g), hcompat g⟩ : ↥(boundarySubgroupQ q nu2))) := by
  rintro ⟨⟨t, p⟩, hmem⟩
  obtain ⟨g, hg1, hg2⟩ := fiberProductExists (nuTq q).toMonoidHom nu2.toMonoidHom
    tameX.toMonoidHom pro2X.toMonoidHom htame hcompat
    (hkerQ_uniform hq0 hqe nu2 tameX pro2X htame hpro hkerpro hcompat) t p hmem
  exact ⟨g, Subtype.ext (Prod.ext hg1 hg2)⟩

/-- The pro-`2` kernel hypothesis is automatic when `pro2X` *is* the maximal pro-`2` quotient
map, i.e. when `ker pro2X = proPKernel 2 dom` — the shape both the `Γ_R` side and the `G_K` side
(`BoundaryMaps.ker_pro2F`) supply. -/
theorem boundary_jointly_surjective_of_maxProP (hq0 : q ≠ 0) (hqe : Even q)
    (nu2 : ContinuousMonoidHom D Ztwo)
    (tameX : ContinuousMonoidHom dom (Tq q)) (pro2X : ContinuousMonoidHom dom D)
    (htame : Function.Surjective tameX) (hpro : Function.Surjective pro2X)
    (hkerpro : pro2X.toMonoidHom.ker = proPKernel 2 dom)
    (hcompat : ∀ g, nuTq q (tameX g) = nu2 (pro2X g)) :
    Function.Surjective (fun g : dom =>
      (⟨(tameX g, pro2X g), hcompat g⟩ : ↥(boundarySubgroupQ q nu2))) :=
  boundary_jointly_surjective hq0 hqe nu2 tameX pro2X htame hpro hkerpro.ge hcompat

end ThmThreeFive

/-! ## §5. The mandated `q`-distinguishing regression

AX4 memo risk **R2**: if the axiom's residue degree `f` were left free, the axiom would assert
`G_K/W ≅ T_{2^f}` for *every* `f`, hence `T_2 ≅ T_4`, from which `False` follows by a finite
count.  The guard is a count that actually separates the two groups.

The universal property of the presentation gives, for every profinite target `P`,

  `Hom_cont(T_q, P) ≃ {(a, b) ∈ P × P ∣ b^a = b^q}`

(`tqHomEquiv`), and at the abelian target `ℤ/3` the condition collapses to `b^{q-1} = 1`.  So
`#Hom(T_2, ℤ/3) = 3` (the `τ`-coordinate is forced to be trivial; only the unramified `Ẑ`
coordinate contributes) while `#Hom(T_4, ℤ/3) = 9` (the `τ`-coordinate contributes a factor of
`3`, because `T_4^{ab} = Ẑ × ℤ/3`).

**Arithmetic note for the AX4 memo.**  The memo's §4 quotes these counts as *"`#Hom(T_4, ℤ/3)`
`= 3` versus `#Hom(T_2, ℤ/3) = 1`"*.  Those are the counts of the **`τ`-coordinate alone**
(`#Hom(ℤ/(q−1), ℤ/3)`), which omit the free `Ẑ`-factor `Hom_cont(Ẑ, ℤ/3) ≅ ℤ/3`; the full hom
counts are `3` and `9`.  Both forms are landed below (`card_tqTau_slot_zmodThree_*` gives the
memo's `1` and `3`), and both separate `q = 2` from `q = 4`, so the guard is unaffected — but
the memo's numbers should be read as the inertia-slot count. -/

section Regression

variable {q : ℕ}

/-- The continuous hom out of `T_q` classified by a pair `(a, b)` satisfying the tame relation. -/
noncomputable def tqClassify (q : ℕ) (P : ProfiniteGrp.{0}) {a b : P} (h : conjP b a = b ^ q) :
    ContinuousMonoidHom (Tq q) P :=
  presentationLift {tameWordQ q} ((FreeProfiniteGroup.homEquiv (Fin 2) P).symm ![a, b]).hom <| by
    rintro r rfl
    have e0 : ((FreeProfiniteGroup.homEquiv (Fin 2) P).symm ![a, b]).hom
        (FreeProfiniteGroup.of 0) = a := FreeProfiniteGroup.homEquiv_symm_of _ _ _
    have e1 : ((FreeProfiniteGroup.homEquiv (Fin 2) P).symm ![a, b]).hom
        (FreeProfiniteGroup.of 1) = b := FreeProfiniteGroup.homEquiv_symm_of _ _ _
    show ((FreeProfiniteGroup.homEquiv (Fin 2) P).symm ![a, b]).hom (tameWordQ q) = 1
    rw [tameWordQ]
    simp only [conjP, map_mul, map_inv, map_pow, e0, e1]
    simpa only [conjP] using mul_inv_eq_one.mpr h

@[simp] theorem tqClassify_tqSigma (q : ℕ) (P : ProfiniteGrp.{0}) {a b : P} (h : conjP b a = b ^ q) :
    tqClassify q P h (tqSigma q) = a :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of 0)).trans
    (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] theorem tqClassify_tqTau (q : ℕ) (P : ProfiniteGrp.{0}) {a b : P} (h : conjP b a = b ^ q) :
    tqClassify q P h (tqTau q) = b :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of 1)).trans
    (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

/-- **The universal property of `T_q`**: continuous homs `T_q → P` are exactly the pairs
`(a, b) ∈ P × P` with `b^a = b^q`. -/
noncomputable def tqHomEquiv (q : ℕ) (P : ProfiniteGrp.{0}) :
    ContinuousMonoidHom (Tq q) P ≃ {p : P × P // conjP p.2 p.1 = p.2 ^ q} where
  toFun φ := ⟨(φ (tqSigma q), φ (tqTau q)), by
    have h := congrArg φ (tame_relation_q q)
    simpa only [conjP, map_mul, map_inv, map_pow] using h⟩
  invFun p := tqClassify q P p.2
  left_inv φ := by
    refine DFunLike.ext _ _ fun x => ?_
    refine contMonoidHom_eq_of_gens ?_ ?_ x
    · rw [tqClassify_tqSigma]
    · rw [tqClassify_tqTau]
  right_inv p := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact tqClassify_tqSigma q P p.2
    · exact tqClassify_tqTau q P p.2

/-- The hom count of `T_q` into any profinite target, as an explicit finite count of pairs. -/
theorem card_hom_tq (q : ℕ) (P : ProfiniteGrp.{0}) :
    Nat.card (ContinuousMonoidHom (Tq q) P) = Nat.card {p : P × P // conjP p.2 p.1 = p.2 ^ q} :=
  Nat.card_congr (tqHomEquiv q P)

/-- `ℤ/3` written multiplicatively — the odd finite test target of AX4 memo §4. -/
abbrev ZmodThree : Type := Multiplicative (ZMod 3)

instance : TopologicalSpace ZmodThree := ⊥
instance : DiscreteTopology ZmodThree := ⟨rfl⟩

/-- `ℤ/3` as a profinite group. -/
noncomputable def profiniteZmodThree : ProfiniteGrp := ProfiniteGrp.of ZmodThree

theorem card_hom_tq_zmodThree (q : ℕ) :
    Nat.card (ContinuousMonoidHom (Tq q) profiniteZmodThree)
      = Nat.card {p : ZmodThree × ZmodThree // conjP p.2 p.1 = p.2 ^ q} :=
  card_hom_tq q profiniteZmodThree

/-- **`#Hom_cont(T_2, ℤ/3) = 3`**: only the unramified `Ẑ`-coordinate contributes, because the
`q = 2` relation forces `τ ↦ 1` in an abelian target of odd exponent. -/
theorem card_hom_tq_zmodThree_two :
    Nat.card (ContinuousMonoidHom (Tq 2) profiniteZmodThree) = 3 := by
  rw [card_hom_tq_zmodThree, Nat.card_eq_fintype_card]
  decide

/-- **`#Hom_cont(T_4, ℤ/3) = 9`**: `T_4^{ab} = Ẑ × ℤ/3`, so the tame coordinate contributes a
factor of `3`.  Together with `card_hom_tq_zmodThree_two` this is the AX4 memo's R2 guard:
`T_2` and `T_4` are **not** isomorphic, so a tame axiom with an unpinned residue degree is
inconsistent. -/
theorem card_hom_tq_zmodThree_four :
    Nat.card (ContinuousMonoidHom (Tq 4) profiniteZmodThree) = 9 := by
  rw [card_hom_tq_zmodThree, Nat.card_eq_fintype_card]
  decide

/-- **The `q`-distinguishing regression.**  `T_2` and `T_4` have different `ℤ/3`-hom counts,
hence are not isomorphic as topological groups.  `q_K = 4` is the residue cardinality of
`ℚ₂(√5)`, the only `q ≠ 2` instance in the campaign's quadratic table. -/
theorem hom_count_distinguishes_tq_two_four :
    Nat.card (ContinuousMonoidHom (Tq 2) profiniteZmodThree)
      ≠ Nat.card (ContinuousMonoidHom (Tq 4) profiniteZmodThree) := by
  rw [card_hom_tq_zmodThree_two, card_hom_tq_zmodThree_four]
  decide

/-- The **inertia-slot** count `#{b ∈ ℤ/3 ∣ b^q = b} = #Hom(ℤ/(q−1), ℤ/3)`, i.e. the numbers
quoted in AX4 memo §4 (`1` at `q = 2`, `3` at `q = 4`).  These are the full hom counts divided
by the `Ẑ`-factor `#Hom_cont(Ẑ, ℤ/3) = 3`. -/
theorem card_tqTau_slot_zmodThree_two :
    Nat.card {b : ZmodThree // b ^ 2 = b} = 1 := by
  rw [Nat.card_eq_fintype_card]; decide

theorem card_tqTau_slot_zmodThree_four :
    Nat.card {b : ZmodThree // b ^ 4 = b} = 3 := by
  rw [Nat.card_eq_fintype_card]; decide

end Regression

end GQ2.Dyadic
