/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.TameQuotientK
import GQ2.Dyadic.Word.Eval
import GQ2.Dyadic.AdmissibleR
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

⚠ **`GammaR` itself is no longer defined here** (ticket **GR1**).  The campaign's `Γ_R` carries a
pro-`2` clause on the wild part *as part of its definition* — plan §1, and the simplification
campaign's §3: *"a bare two-relator profinite quotient is not interchangeable with this
definition"* — and F3's original `profinitePresentation (gammaRelators n q R)` did not.  CB-W
proved that the bare object's wild part is never pro-`2` (`Count/Wild.lean` §4), so `hwild` was
unprovable and `WordCertificate` empty.  `GammaR`, `gammaMk`, `gammaGen`, `gammaMarking`,
`freeMarking`, `tameRelatorGen`, `gammaRelators` and the bare object `GammaBare` now live in the
leaf `GQ2/Dyadic/AdmissibleR.lean`, which builds `Γ_R = F ⧸ N_R` as the admissible limit on the
`GQ2/GammaA.lean:211` pattern.  Everything below is unchanged except that the two hom-out-of-`Γ_R`
constructions (`TameSpec.tameOfSpec`, `prop_3_4_two`) go through `gammaLift` — the **restricted**
universal property — instead of `presentationLift`, each discharging the wild-`2` clause from a
one-line lemma of that leaf.

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
* **§4 — packet Proposition 3.4** (`TameSpec.TameSpecializes`, `TameSpec.tameOfSpec`,
  `TameSpec.gammaR_tame_equiv_of_spec`, `TameSpec.prop_3_4_one_of_spec`, `prop_3_4_two`,
  `TameSpec.prop_3_4_three_of_spec`): the two specializations of an admissible `Γ_R`, driven by
  F2's substitution operators `killWild` / `pro2` and their soundness theorems
  `Marking.eval_killWild` / `Marking.eval_pro2` (never by hand rewrites).  §4 closes with
  `TameSpec.gammaR_boundary_surjective_of_spec`, §3's theorem instantiated at those two
  specializations — the packet's Theorem 3.5 for the word side, end to end.

## ⚠ Gate B: which admissibility predicate to use  (ticket F3b)

§4 carries **two** Gate-B predicates, and picking the wrong one wastes a lane's day.

* **`TameSpec.TameSpecializes n q R`** — *the primary one*.  `(tameMarking n q).eval R = 1`,
  i.e. the ledger's `specializeTame R = 1`: the wild word dies under the tame marking of `T_q`.
  Satisfiable, satisfied by all five frozen branch words, and the hypothesis of every
  construction in §4 (`tameOfSpec`, `psiOfSpec`, `gammaR_tame_equiv_of_spec`, `ker_tameOfSpec`,
  `prop_3_4_one_of_spec`, `prop_3_4_three_of_spec`, `nuTwoOfSpec`,
  `gammaR_boundary_surjective_of_spec`).  A branch lane discharges it in one line, from its own
  landed tame-boundary theorem, by whichever of the two routes matches that theorem's shape —
  `tameSpecializes_of_tau_pow` when the kill-wild value is bare `τ^{ω₂}` (compact `N`, `Npc`,
  `L_sq`), `tameSpecializes_of_tau` when the lane states death as an implication from
  `τ^{ω₂} = 1` (compact `M`, `Mpc`, whose values carry an `𝓔`-block and an orbit norm).  Both
  bottom out in Lemma 3.1: `τ^{ω₂} = 1` in `T_q` (`zpowHat_omega2_tqTau`, §1).
* **`KillsWild R`** — F3's original, quantified over *every* profinite group and *every*
  marking.  It is **refuted** by all five frozen branch words (`Words/{N0,Npc,M0,Mpc,L}.lean`
  each carry a landed `not_killsWild`), because the tame-killed value of a `δ`-letter word is
  `τ^{ω₂}`, nontrivial already in `Multiplicative (ZMod 8)`.  It is kept — the refutations are
  theorems, and `KillsWild → TameSpecializes` does hold
  (`TameSpec.tameSpecializes_of_killsWild`) — so every `KillsWild`-shaped declaration survives
  verbatim, as a one-line wrapper over its `TameSpec` twin.  **Do not state anything new
  against it.**
* **§5 — the mandated `q`-distinguishing regression** (`tqHomEquiv`, `card_hom_tq_zmodThree_*`):
  a kernel-`decide` count of `Hom_cont(T_q, ℤ/3)` separating `q = 2` from `q = 4`.  This is AX4
  memo risk **R2**'s guard: an unpinned residue degree would assert `T_2 ≅ T_4`, and the count
  refutes that.  See the note at §5 on the memo's arithmetic.
-/

namespace GQ2.Dyadic

open GQ2.SectionThree

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

/-- **`ω₂` kills the tame generator**: `τ^{ω₂} = 1` in `T_q`.  This is the operative,
element-level face of Lemma 3.1 — *"tame inertia is pro-odd, and `ω₂` is the `2`-primary
projection, so it annihilates it"* — and it is the fact the branch lanes need at the tame
boundary: every frozen wild word evaluates, after killing the wild letters, to a word in
`τ^{ω₂}` (`Words/*.eval_killWildLetters_*`), so *this* lemma is what turns those values into
`1` over `T_q`.  See `TameSpec.tameSpecializes_of_tau_pow`, which packages exactly that step.

The proof is §1's finite-image statement pushed through every open normal subgroup: in each
finite quotient the image of `τ` has odd order (`tqTau_odd_order_map`), and `ω₂` acts on a
finite group as `powOmega2` (`zpowHat_omega2`), which kills odd-order elements
(`GQ2.powOmega2_eq_one_of_odd`). -/
theorem zpowHat_omega2_tqTau (hq0 : q ≠ 0) (hqe : Even q) :
    (tqTau q) ^ᶻ omega2 = 1 := by
  refine eq_one_of_forall_mem_openNormalSubgroup fun U => ?_
  haveI : Finite (((Tq q) : Type) ⧸ U.toSubgroup) := inferInstance
  set mk : ContinuousMonoidHom ((Tq q) : Type) (((Tq q) : Type) ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩ with hmk
  have hone : mk ((tqTau q) ^ᶻ omega2) = 1 := by
    rw [map_zpowHat_omega2]
    exact powOmega2_eq_one_of_odd (tqTau_odd_order_map hq0 hqe mk.toMonoidHom)
  exact (QuotientGroup.eq_one_iff _).mp hone

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

/-! ## §4. Packet Proposition 3.4: the two specializations of an admissible `Γ_R`

*"Assume that killing all `x_i` makes the wild word `R` trivial, and that killing `τ` and
replacing every profinite exponent by its `2`-component changes `R` to a pro-`2` word `P`.
Then: (1) `W_R = O₂(Γ_R)` and `Γ_R/W_R ≅ T_{q_K}`; (2) the maximal pro-`2` quotient of `Γ_R` is
`D_P = ⟨σ, x₀, …, x_n ∣ P = 1⟩_{pro-2}`; (3) the induced unramified character has `ν(σ) = 1` and
`ν(x_i) = 0`."*

The two hypotheses are exactly F2's two substitution operators.  `killWild` drives (1) through
`Marking.eval_killWild`, and `pro2` drives (2) through `Marking.eval_pro2`; no relator is
rewritten by hand.  Part (2) is stated in **universal-property form** — continuous homs
`Γ_R → Q` into a pro-`2` group `Q` are exactly the markings of `{σ, x₀, …, x_n}` in `Q` killing
`P = pro2 R` — which is what "the maximal pro-`2` quotient is `D_P`" *means*, and avoids
committing the campaign to a second presented object before the WW lane fixes the words. -/

section PropThreeFour

variable {n q : ℕ} {R : PWord (Generator n)}

/-! ### The candidate group

`freeMarking`, `tameRelatorGen`, `gammaRelators`, `GammaR`, `gammaMk`, `gammaGen` and
`gammaMarking` are **`GQ2/Dyadic/AdmissibleR.lean`'s** (ticket GR1), where `Γ_R = F ⧸ N_R` is
built as the admissible limit — the intersection of the open normal subgroups whose finite
quotient kills both relators *and* has `2`-group wild normal closure.  The two facts §4 uses
about that construction are the ones the bare presentation also had: the relators die
(`relator_gammaMk_eq_one`) and the projection is surjective (`gammaMk_surjective`).  The third,
new one — every finite quotient of `Γ_R` satisfies the pro-`2` clause
(`isPGroup_two_wildNormalClosure`) — is what discharges `hwild`, downstream. -/

/-- The tame relation holds in `Γ_R`. -/
theorem gammaR_tame_relation :
    conjP (gammaGen n q R .tau) (gammaGen n q R .sigma) = gammaGen n q R .tau ^ q := by
  have h := relator_gammaMk_eq_one (n := n) (q := q) (R := R)
    (Set.mem_insert (tameRelatorGen n q) _)
  simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow] at h ⊢
  exact mul_inv_eq_one.mp h

/-- The wild word is a relator of `Γ_R`. -/
theorem gammaMarking_eval_R : (gammaMarking n q R).eval R = 1 := by
  rw [gammaMarking_eq_map, ← Marking.map_eval (gammaMk n q R) (freeMarking n) R]
  exact relator_gammaMk_eq_one (Set.mem_insert_of_mem _ rfl)

/-- **`W_R`**: the closed normal subgroup of `Γ_R` generated by the wild letters `x₀, …, x_n`. -/
noncomputable def wildPartR (n q : ℕ) (R : PWord (Generator n)) :
    Subgroup ((GammaR n q R) : Type) :=
  (Subgroup.normalClosure
    (Set.range fun i : Fin (n + 1) => gammaGen n q R (.wild i))).topologicalClosure

instance wildPartR_normal : (wildPartR n q R).Normal := Subgroup.is_normal_topologicalClosure _

instance wildPartR_isClosed : IsClosed ((wildPartR n q R) : Set ((GammaR n q R) : Type)) :=
  Subgroup.isClosed_topologicalClosure _

theorem gammaGen_wild_mem_wildPartR (i : Fin (n + 1)) :
    gammaGen n q R (.wild i) ∈ wildPartR n q R :=
  Subgroup.le_topologicalClosure _ (Subgroup.subset_normalClosure ⟨i, rfl⟩)

/-! ### Gate B: admissibility

Two predicates live here, and **the primary one is `TameSpec.TameSpecializes`**, further down
(it needs `tameMarking`, so it cannot be stated before Part (1) opens).

* `TameSpecializes n q R` — *"`R` dies under the tame marking of `T_q`"*, i.e. the ledger's
  `specializeTame R = 1`.  **Satisfiable**, satisfied by all five frozen branch words, and the
  hypothesis every construction below actually consumes.
* `KillsWild R` — the original, universally-quantified reading of the packet's prose.
  **Refuted** by all five frozen branch words; kept because the refutations are landed theorems
  and because it does imply the primary predicate (`TameSpec.tameSpecializes_of_killsWild`).

See the ⚠ warning on `KillsWild` itself before writing anything against it. -/

/-- **Gate B admissibility, universally quantified** (a literal reading of the first hypothesis
of packet Prop. 3.4): *killing all `x_i` makes the wild word `R` trivial*.  Stated semantically
— the value of `R` at any marking whose wild letters are trivial is `1` — which by F2's
`Marking.eval_killWild` is equivalent to the syntactic statement that `killWild R` evaluates to
`1` everywhere (`killsWild_iff_killWild`).

⚠ **Do not use this as a hypothesis.  It is refuted by every frozen branch word.**

`KillsWild` quantifies over *every* profinite group and *every* marking, with **no condition on
the `τ`-letter**.  But the tame-killed value of any word carrying an `(x_i τ)^{ω₂}`-shaped
`δ`-letter is `τ^{ω₂}` — see `Words/N0.lean`'s `eval_killWildLetters_nCompact` and its four
siblings — and `τ^{ω₂} ≠ 1` already in `Multiplicative (ZMod 8)`.  So `KillsWild` is not
merely mis-shaped; it is **false** for the words the campaign froze.  All five refutations are
landed theorems, and they must stay true:

* `GQ2.Dyadic.Words.not_killsWild` (compact `N`, `Words/N0.lean`),
* `GQ2.Dyadic.Words.Npc.not_killsWild` (`Words/Npc.lean`),
* `GQ2.Dyadic.Words.MCompact.not_killsWild` (compact `M`, `Words/M0.lean`),
* `GQ2.Dyadic.Words.Mpc.not_killsWild` (`Words/Mpc.lean`),
* `GQ2.Dyadic.Words.LSq.not_killsWild` (`Words/L.lean`).

This is **not** a defect in the words.  The packet's hypothesis lives where `τ` is pro-odd —
that is, in `T_q`, by Lemma 3.1 (§1) — and there the words *are* admissible.  The routes to use
instead, in decreasing order of preference:

1. `TameSpec.TameSpecializes n q R` (below) — the primary Gate-B predicate, and literally the
   ledger's `specializeTame R = 1`.  Every construction that used to take `KillsWild` has a
   `TameSpec` twin taking this instead, and the `KillsWild` versions are now thin wrappers
   around those twins.  A branch lane discharges it with
   `TameSpec.tameSpecializes_of_tau_pow`, fed its own `eval_killWildLetters_*` value theorem.
2. `Words/*.killsWild_of_tau` — the per-word `τ`-relativized statement.  ⚠ Note that *its*
   hypothesis is itself universally quantified over markings, so it is no more satisfiable than
   `KillsWild`; it records the shape of the argument, not a usable route.
3. `Words/*.eval_killWildLetters_*_eq_one_of_odd` — the finite-target form the F5 harnesses
   test (`Odd (orderOf t.τ)` at a finite discrete marking).

Recorded by ticket **F3b**; the original ruling is the WN0-a outcomes entry in
`docs/dyadic/tickets.md`. -/
def KillsWild {n : ℕ} (R : PWord (Generator n)) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [TotallyDisconnectedSpace G] (t : Marking n G), (Marking.killWildLetters t).eval R = 1

/-- Admissibility through F2's substitution operator: `KillsWild R` says exactly that the
kill-wild rewrite `killWild R` is a trivial word. -/
theorem killsWild_iff_killWild (R : PWord (Generator n)) :
    KillsWild R ↔ ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking n G), t.eval (killWild R) = 1 := by
  constructor
  · intro h G _ _ _ _ _ t; rw [Marking.eval_killWild]; exact h G t
  · intro h G _ _ _ _ _ t; rw [← Marking.eval_killWild]; exact h G t

/-! ### Part (1): the tame specialization `Γ_R/W_R ≅ T_q` -/

/-- The tame marking of `T_q`: `σ ↦ σ`, `τ ↦ τ`, `x_i ↦ 1`. -/
noncomputable def tameMarking (n q : ℕ) : Marking n ((Tq q) : Type) :=
  Marking.ofLetters (tqSigma q) (tqTau q) (fun _ => 1)

@[simp] theorem tameMarking_σ : (tameMarking n q).σ = tqSigma q := rfl

@[simp] theorem tameMarking_τ : (tameMarking n q).τ = tqTau q := rfl

@[simp] theorem tameMarking_x (i : Fin (n + 1)) : (tameMarking n q).x i = 1 := rfl

/-- **`ω₂` kills the tame marking's `τ`-letter** — `zpowHat_omega2_tqTau` (Lemma 3.1, §1) read
at `tameMarking`.  This is precisely the hypothesis the `_of_tau`-shaped branch-lane theorems
take (compact `M`'s `eval_killWildLetters_mCompact_of_tau`, `Mpc`'s
`eval_killWildLetters_mpcW_eq_one`), which is why Gate B is a one-liner for every lane: see
`TameSpec.tameSpecializes_of_tau`. -/
theorem tameMarking_tau_zpowHat_omega2 (hq0 : q ≠ 0) (hqe : Even q) :
    (tameMarking n q).τ ^ᶻ omega2 = 1 := by
  rw [tameMarking_τ]
  exact zpowHat_omega2_tqTau hq0 hqe

theorem killWildLetters_tameMarking :
    Marking.killWildLetters (tameMarking n q) = tameMarking n q := by
  ext g; cases g <;> rfl

/-- The classifying map `F(σ, τ, x₀, …, x_n) ⟶ T_q` of the tame marking. -/
noncomputable def tameBase (n q : ℕ) : FreeProfiniteGroup (Generator n) ⟶ Tq q :=
  (FreeProfiniteGroup.homEquiv (Generator n) (Tq q)).symm ⇑(tameMarking n q)

@[simp] theorem tameBase_of (n q : ℕ) (g : Generator n) :
    (tameBase n q).hom.toMonoidHom (FreeProfiniteGroup.of g) = tameMarking n q g :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem tameBase_tameRelatorGen : (tameBase n q).hom.toMonoidHom (tameRelatorGen n q) = 1 := by
  simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow, tameBase_of]
  have h := tame_relation_q q
  simp only [conjP] at h
  show (tqSigma q)⁻¹ * tqTau q * tqSigma q * ((tqTau q) ^ q)⁻¹ = 1
  rw [h, mul_inv_cancel]

/-! #### The primary Gate-B predicate and the construction over it

Everything the packet's Prop. 3.4(1) and Thm. 3.5 need is built here, over the **satisfiable**
hypothesis `TameSpecializes`.  The `KillsWild`-shaped declarations that follow each block are
one-line wrappers around these, so no statement stated against `KillsWild` is lost and no proof
is duplicated. -/

namespace TameSpec

/-- **Gate B, the primary predicate**: the wild word `R` dies under the tame marking of `T_q`
(`σ ↦ σ`, `τ ↦ τ`, `x_i ↦ 1`).  This is the ledger's `specializeTame R = 1` on the nose, and
the packet's Prop. 3.4 hypothesis read *where the packet reads it* — inside the tame quotient,
where Lemma 3.1 makes `τ` pro-odd.

Contrast `KillsWild`, which asks the same thing of **every** profinite group and **every**
marking and is therefore refuted by all five frozen branch words (see the ⚠ warning there).
`KillsWild R → TameSpecializes n q R` (`tameSpecializes_of_killsWild`); the converse is false.

Satisfied by all five branches: each `Words/*.lean` computes the tame boundary value as
`τ^{ω₂}` (`eval_killWildLetters_*`), and `τ^{ω₂} = 1` over `T_q` by `zpowHat_omega2_tqTau`.
`tameSpecializes_of_tau_pow` is that one-step route. -/
def TameSpecializes (n q : ℕ) (R : PWord (Generator n)) : Prop :=
  (tameMarking n q).eval R = 1

theorem tameSpecializes_iff : TameSpecializes n q R ↔ (tameMarking n q).eval R = 1 := Iff.rfl

/-- The kill-wild reading: over `T_q` the wild letters are already trivial, so `TameSpecializes`
is the value of `R` at the *kill-wild* tame marking — the shape the `Words/*` lanes state. -/
theorem tameSpecializes_iff_killWildLetters :
    TameSpecializes n q R ↔ (Marking.killWildLetters (tameMarking n q)).eval R = 1 := by
  rw [killWildLetters_tameMarking]
  exact tameSpecializes_iff

/-- **The implication that does hold.**  F3's universally-quantified Gate B implies the
primary predicate, by instantiating it at `G := T_q`, `t := tameMarking n q`.  So anything
stated against `KillsWild` still applies — which is why the `KillsWild` versions below are
wrappers rather than deletions.

⚠ The converse is **false**: `KillsWild` is refuted by all five frozen branch words while
`TameSpecializes` holds for them. -/
theorem tameSpecializes_of_killsWild (hadm : KillsWild R) : TameSpecializes n q R := by
  have h := hadm ((Tq q) : Type) (tameMarking n q)
  rwa [killWildLetters_tameMarking] at h

/-- **The branch lanes' route, form 1 — the bare value.**  Three of the five lanes prove their
word's tame boundary value is exactly `τ^{ω₂}` for an arbitrary marking:
`Words.eval_killWildLetters_nCompact`, `Words.Npc.eval_killWildLetters_npcW`,
`Words.LSq.eval_killWildLetters_lSq`.  Fed that theorem at `t := tameMarking n q`, this
discharges Gate B in one step, because `τ^{ω₂} = 1` in `T_q` (Lemma 3.1,
`zpowHat_omega2_tqTau`).

The other two lanes (compact `M`, `Mpc`) carry an `𝓔`-block and an orbit norm alongside the
`τ^{ω₂}`, so their bare value is *not* `τ^{ω₂}` — they take form 2 below. -/
theorem tameSpecializes_of_tau_pow (hq0 : q ≠ 0) (hqe : Even q)
    (h : (Marking.killWildLetters (tameMarking n q)).eval R = (tameMarking n q).τ ^ᶻ omega2) :
    TameSpecializes n q R := by
  rw [killWildLetters_tameMarking, tameMarking_τ, zpowHat_omega2_tqTau hq0 hqe] at h
  exact h

/-- **The branch lanes' route, form 2 — the `τ`-conditioned form**, and the one that covers
every word shape.  Compact `M` and `Mpc` state their tame boundary death as an *implication*
from `τ^{ω₂} = 1` (`Words.MCompact.eval_killWildLetters_mCompact_of_tau`,
`Words.Mpc.eval_killWildLetters_mpcW_eq_one`), because their kill-wild value carries an
`𝓔`-block (and, for `Mpc`, an orbit norm) that only collapses once `τ^{ω₂}` is trivial.  Hand
that implication here and Gate B is discharged: `T_q` supplies its antecedent by Lemma 3.1. -/
theorem tameSpecializes_of_tau (hq0 : q ≠ 0) (hqe : Even q)
    (h : (tameMarking n q).τ ^ᶻ omega2 = 1 →
      (Marking.killWildLetters (tameMarking n q)).eval R = 1) :
    TameSpecializes n q R :=
  tameSpecializes_iff_killWildLetters.mpr (h (tameMarking_tau_zpowHat_omega2 hq0 hqe))

/-- The route for a lane whose tame boundary value is already `1` with no side condition,
stated at the kill-wild marking the lanes use. -/
theorem tameSpecializes_of_killWildLetters
    (h : (Marking.killWildLetters (tameMarking n q)).eval R = 1) : TameSpecializes n q R :=
  tameSpecializes_iff_killWildLetters.mpr h

/-- The route through F2's *syntactic* substitution operator, via `Marking.eval_killWild`. -/
theorem tameSpecializes_of_evalKillWild (h : (tameMarking n q).eval (killWild R) = 1) :
    TameSpecializes n q R :=
  tameSpecializes_of_killWildLetters (by rwa [Marking.eval_killWild] at h)

/-- `tameBase_eval_R` at the primary hypothesis: the `R`-relator dies in `T_q`. -/
theorem tameBase_eval_R (hspec : TameSpecializes n q R) :
    (tameBase n q).hom.toMonoidHom ((freeMarking n).eval R) = 1 := by
  have h := Marking.map_eval (tameBase n q).hom (freeMarking n) R
  have hmark : (freeMarking n).map ⇑(tameBase n q).hom = tameMarking n q := by
    ext g; exact tameBase_of n q g
  show (tameBase n q).hom ((freeMarking n).eval R) = 1
  rw [h, hmark]
  exact hspec

/-- The tame base map kills every relator of `Γ_R` — the first half of GR1's admissibility
obligation for `tameOfSpec`. -/
theorem tameBase_gammaRelators (hspec : TameSpecializes n q R) :
    ∀ r ∈ gammaRelators n q R, (tameBase n q).hom r = 1 := by
  rintro r (rfl | rfl)
  · exact tameBase_tameRelatorGen
  · exact tameBase_eval_R hspec

/-- **The tame specialization** `Γ_R ↠ T_q` (`σ ↦ σ`, `τ ↦ τ`, `x_i ↦ 1`), well defined by the
primary Gate-B hypothesis.

Since ticket GR1 this goes through `gammaLift`, the **restricted** universal property of the
admissible limit, rather than `presentationLift`.  Its extra obligation — the wild-`2` clause —
is free here for the strongest possible reason: the tame marking sends every `x_i` to `1`, so the
normal closure of their images is trivial in every quotient (`wildMap_of_wild_eq_one`). -/
noncomputable def tameOfSpec (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) : ContinuousMonoidHom (GammaR n q R) (Tq q) :=
  gammaLift n q R (tameBase n q).hom (tameBase_gammaRelators hspec)
    (wildMap_of_wild_eq_one _ fun i => tameBase_of n q (.wild i))

@[simp] theorem tameOfSpec_gammaGen (hspec : TameSpecializes n q R) (g : Generator n) :
    tameOfSpec n q R hspec (gammaGen n q R g) = tameMarking n q g :=
  (gammaLift_gammaMk _ _ _ _ _ _ (FreeProfiniteGroup.of g)).trans (tameBase_of n q g)

theorem tameOfSpec_surjective (hspec : TameSpecializes n q R) :
    Function.Surjective (tameOfSpec n q R hspec) := by
  have hle : Subgroup.closure {tqSigma q, tqTau q}
      ≤ (tameOfSpec n q R hspec).toMonoidHom.range := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨gammaGen n q R .sigma, tameOfSpec_gammaGen hspec .sigma⟩
    · exact ⟨gammaGen n q R .tau, tameOfSpec_gammaGen hspec .tau⟩
  have hclosed :
      IsClosed (((tameOfSpec n q R hspec).toMonoidHom.range) : Set ((Tq q) : Type)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range (tameOfSpec n q R hspec).continuous_toFun).isClosed
  have htop : (tameOfSpec n q R hspec).toMonoidHom.range = ⊤ := by
    rw [eq_top_iff, ← topGen_tq q]
    exact Subgroup.topologicalClosure_minimal _ hle hclosed
  exact MonoidHom.range_eq_top.mp htop

theorem wildPartR_le_ker_tameOfSpec (hspec : TameSpecializes n q R) :
    wildPartR n q R ≤ (tameOfSpec n q R hspec).toMonoidHom.ker := by
  have hker_closed :
      IsClosed (((tameOfSpec n q R hspec).toMonoidHom.ker) : Set (GammaR n q R)) := by
    rw [MonoidHom.coe_ker]
    exact IsClosed.preimage (tameOfSpec n q R hspec).continuous_toFun isClosed_singleton
  refine Subgroup.topologicalClosure_minimal _ ?_ hker_closed
  refine Subgroup.normalClosure_le_normal ?_
  rintro z ⟨i, rfl⟩
  exact MonoidHom.mem_ker.mpr (tameOfSpec_gammaGen hspec (.wild i))

/-! #### The bare presentation's tame specialization

`GammaBare` (`AdmissibleR.lean` §6) is the pre-GR1 object: the same two relators, **without** the
pro-`2` clause.  It has the *plain* presentation property, so the tame marking descends over it
with no side condition — and that is exactly why it is the wrong group: `Count/Wild.lean` §4
descends the `ℤ/3` markings over it too, and concludes that the kernel below is never pro-`2`.
These two declarations exist only to carry CB-W's and CB-0's refutations, which remain theorems
about `GammaBare`. -/

/-- The tame specialization of the **bare** presentation, `Γ_R^bare ↠ T_q`. -/
noncomputable def tameOfSpecBare (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) : ContinuousMonoidHom (GammaBare n q R) (Tq q) :=
  presentationLift (gammaRelators n q R) (tameBase n q).hom (tameBase_gammaRelators hspec)

@[simp] theorem tameOfSpecBare_bareGen (hspec : TameSpecializes n q R) (g : Generator n) :
    tameOfSpecBare n q R hspec (bareGen n q R g) = tameMarking n q g :=
  (presentationLift_mk _ _ _ (FreeProfiniteGroup.of g)).trans (tameBase_of n q g)

theorem bareGen_wild_mem_ker_tameOfSpecBare (hspec : TameSpecializes n q R) (i : Fin (n + 1)) :
    bareGen n q R (.wild i) ∈ (tameOfSpecBare n q R hspec).toMonoidHom.ker :=
  MonoidHom.mem_ker.mpr (tameOfSpecBare_bareGen hspec (.wild i))

end TameSpec

/-! #### The `KillsWild`-shaped wrappers

Statement-for-statement the F3 originals; each is now the corresponding `TameSpec` declaration
composed with `TameSpec.tameSpecializes_of_killsWild`.  They are definitionally the old terms
(the hypothesis is a `Prop`), so every downstream `simp` set and `rfl` still fires.  ⚠ They are
**unusable at the frozen branch words** — see the warning on `KillsWild`. -/

theorem tameBase_eval_R (hadm : KillsWild R) :
    (tameBase n q).hom.toMonoidHom ((freeMarking n).eval R) = 1 :=
  TameSpec.tameBase_eval_R (TameSpec.tameSpecializes_of_killsWild hadm)

/-- **The tame specialization** `Γ_R ↠ T_q` (`σ ↦ σ`, `τ ↦ τ`, `x_i ↦ 1`), well defined by
admissibility.  ⚠ Prefer `TameSpec.tameOfSpec`: `KillsWild` is refuted by every frozen branch
word, so this form cannot be called at any of them. -/
noncomputable def tameR (n q : ℕ) (R : PWord (Generator n)) (hadm : KillsWild R) :
    ContinuousMonoidHom (GammaR n q R) (Tq q) :=
  TameSpec.tameOfSpec n q R (TameSpec.tameSpecializes_of_killsWild hadm)

theorem tameR_eq_tameOfSpec (hadm : KillsWild R) :
    tameR n q R hadm = TameSpec.tameOfSpec n q R (TameSpec.tameSpecializes_of_killsWild hadm) :=
  rfl

@[simp] theorem tameR_gammaGen (hadm : KillsWild R) (g : Generator n) :
    tameR n q R hadm (gammaGen n q R g) = tameMarking n q g :=
  TameSpec.tameOfSpec_gammaGen _ g

theorem tameR_surjective (hadm : KillsWild R) : Function.Surjective (tameR n q R hadm) :=
  TameSpec.tameOfSpec_surjective _

theorem wildPartR_le_ker_tameR (hadm : KillsWild R) :
    wildPartR n q R ≤ (tameR n q R hadm).toMonoidHom.ker :=
  TameSpec.wildPartR_le_ker_tameOfSpec _

/-- `Γ_R/W_R` as a profinite group. -/
noncomputable def TameGammaR (n q : ℕ) (R : PWord (Generator n)) : ProfiniteGrp :=
  profiniteQuotient (wildPartR n q R)

/-- The projection `Γ_R ↠ Γ_R/W_R`, typed at the bundled carrier. -/
noncomputable def tameGammaMk (n q : ℕ) (R : PWord (Generator n)) :
    ContinuousMonoidHom ((GammaR n q R) : Type) ((TameGammaR n q R) : Type) :=
  quotientMk (wildPartR n q R)

/-- The base map `F(σ, τ) ⟶ Γ_R/W_R`. -/
noncomputable def chiBaseR (n q : ℕ) (R : PWord (Generator n)) :
    FreeProfiniteGroup (Fin 2) ⟶ TameGammaR n q R :=
  (FreeProfiniteGroup.homEquiv (Fin 2) (TameGammaR n q R)).symm
    ![tameGammaMk n q R (gammaGen n q R .sigma), tameGammaMk n q R (gammaGen n q R .tau)]

@[simp] private theorem chiBaseR_of_zero : (chiBaseR n q R).hom.toMonoidHom
    (FreeProfiniteGroup.of 0) = tameGammaMk n q R (gammaGen n q R .sigma) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] private theorem chiBaseR_of_one : (chiBaseR n q R).hom.toMonoidHom
    (FreeProfiniteGroup.of 1) = tameGammaMk n q R (gammaGen n q R .tau) :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem chiBaseR_tameWordQ : (chiBaseR n q R).hom.toMonoidHom (tameWordQ q) = 1 := by
  simp only [tameWordQ, conjP, map_mul, map_inv, map_pow, chiBaseR_of_zero, chiBaseR_of_one]
  have h := congrArg (⇑(tameGammaMk n q R)) (gammaR_tame_relation (n := n) (q := q) (R := R))
  simp only [conjP, map_mul, map_inv, map_pow] at h
  rw [h, mul_inv_cancel]

/-- `χ : T_q → Γ_R/W_R`, by the universal property of the presentation of `T_q`. -/
noncomputable def chiR (n q : ℕ) (R : PWord (Generator n)) :
    ContinuousMonoidHom (Tq q) (TameGammaR n q R) :=
  presentationLift {tameWordQ q} (chiBaseR n q R).hom fun r hr => by
    rcases hr with rfl
    exact chiBaseR_tameWordQ

@[simp] private theorem chiR_tqSigma :
    chiR n q R (tqSigma q) = tameGammaMk n q R (gammaGen n q R .sigma) :=
  (presentationLift_mk _ _ _ _).trans chiBaseR_of_zero

@[simp] private theorem chiR_tqTau :
    chiR n q R (tqTau q) = tameGammaMk n q R (gammaGen n q R .tau) :=
  (presentationLift_mk _ _ _ _).trans chiBaseR_of_one

/-- `Γ_R/W_R` is topologically generated by the classes of the marked generators. -/
theorem topGen_tameGammaR :
    (Subgroup.closure (Set.range fun g : Generator n =>
      tameGammaMk n q R (gammaGen n q R g))).topologicalClosure = ⊤ := by
  have h := TopGen.map
    (f := ((tameGammaMk n q R).comp (gammaMk n q R)).toMonoidHom)
    ((tameGammaMk n q R).comp (gammaMk n q R)).continuous_toFun
    ((quotientMk_surjective _).comp (quotientMk_surjective _))
    (TopGen.freeProfiniteGroup (Generator n))
  rwa [← Set.range_comp] at h

namespace TameSpec

/-- `ψ : Γ_R/W_R → T_q`, the descent of the tame specialization. -/
noncomputable def psiOfSpec (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) :
    ContinuousMonoidHom ((TameGammaR n q R) : Type) (Tq q) :=
  quotientLift (wildPartR n q R) (tameOfSpec n q R hspec) (wildPartR_le_ker_tameOfSpec hspec)

@[simp] theorem psiOfSpec_mk (hspec : TameSpecializes n q R) (g : Generator n) :
    psiOfSpec n q R hspec (tameGammaMk n q R (gammaGen n q R g)) = tameMarking n q g :=
  (quotientLift_quotientMk _ _ _ _).trans (tameOfSpec_gammaGen hspec g)

theorem psiOfSpec_chiR (hspec : TameSpecializes n q R) (x : Tq q) :
    psiOfSpec n q R hspec (chiR n q R x) = x := by
  refine contMonoidHom_eq_of_gens (f := (psiOfSpec n q R hspec).comp (chiR n q R))
    (g := ContinuousMonoidHom.id (Tq q)) ?_ ?_ x
  · show psiOfSpec n q R hspec (chiR n q R (tqSigma q)) = tqSigma q
    rw [chiR_tqSigma, psiOfSpec_mk hspec .sigma]; rfl
  · show psiOfSpec n q R hspec (chiR n q R (tqTau q)) = tqTau q
    rw [chiR_tqTau, psiOfSpec_mk hspec .tau]; rfl

theorem chiR_psiOfSpec (hspec : TameSpecializes n q R) (x : ((TameGammaR n q R) : Type)) :
    chiR n q R (psiOfSpec n q R hspec x) = x := by
  have h := TopGen.monoidHom_eq
    (f := (chiR n q R).toMonoidHom.comp (psiOfSpec n q R hspec).toMonoidHom)
    (g := MonoidHom.id _)
    (by rw [MonoidHom.coe_comp]
        exact Continuous.comp (chiR n q R).continuous_toFun
          (psiOfSpec n q R hspec).continuous_toFun)
    continuous_id topGen_tameGammaR ?_
  · exact h x
  · rintro z ⟨g, rfl⟩
    show chiR n q R (psiOfSpec n q R hspec (tameGammaMk n q R (gammaGen n q R g)))
      = tameGammaMk n q R (gammaGen n q R g)
    rw [psiOfSpec_mk hspec g]
    cases g with
    | sigma => exact chiR_tqSigma
    | tau => exact chiR_tqTau
    | wild i =>
        have hx : tameGammaMk n q R (gammaGen n q R (.wild i)) = 1 :=
          (quotientMk_eq_one_iff _).mpr (gammaGen_wild_mem_wildPartR i)
        rw [hx]
        show chiR n q R (tameMarking n q (.wild i)) = 1
        show chiR n q R 1 = 1
        exact map_one _

/-- **Packet Prop. 3.4(1), first half**: `Γ_R/W_R ≅ T_{q_K}`, matching the marked generators. -/
noncomputable def gammaR_tame_equiv_of_spec (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) :
    ContinuousMulEquiv ((TameGammaR n q R) : Type) (Tq q) where
  toFun := psiOfSpec n q R hspec
  invFun := chiR n q R
  left_inv := chiR_psiOfSpec hspec
  right_inv := psiOfSpec_chiR hspec
  map_mul' := map_mul (psiOfSpec n q R hspec)
  continuous_toFun := (psiOfSpec n q R hspec).continuous_toFun
  continuous_invFun := (chiR n q R).continuous_toFun

/-- `ker(Γ_R ↠ T_q) = W_R`: the tame specialization has exactly the wild part as kernel. -/
theorem ker_tameOfSpec (hspec : TameSpecializes n q R) :
    (tameOfSpec n q R hspec).toMonoidHom.ker = wildPartR n q R := by
  refine le_antisymm ?_ (wildPartR_le_ker_tameOfSpec hspec)
  intro x hx
  have h1 : psiOfSpec n q R hspec (tameGammaMk n q R x) = 1 := by
    rw [show psiOfSpec n q R hspec (tameGammaMk n q R x) = tameOfSpec n q R hspec x from
      quotientLift_quotientMk _ _ _ _]
    exact hx
  have h2 : tameGammaMk n q R x = 1 :=
    (gammaR_tame_equiv_of_spec n q R hspec).injective (by rw [map_one]; exact h1)
  exact (quotientMk_eq_one_iff _).mp h2

/-- **Packet Prop. 3.4(1), second half**: `W_R = O₂(Γ_R)` — every closed normal pro-`2` subgroup
of `Γ_R` lies in `W_R`.  The proof is the `q = 2` pattern of `GQ2.SectionThree.tameData_maximal`
run on the general-`q` Lemma 3.3 (`o2_Tq_eq_bot`): the image of a competitor in `T_q` is normal
with `2`-group finite images, hence trivial. -/
theorem prop_3_4_one_of_spec (hq2 : 2 ≤ q) (hqe : Even q) (hspec : TameSpecializes n q R)
    (N : Subgroup ((GammaR n q R) : Type)) (hNn : N.Normal)
    (hNp : IsProP 2 N) : N ≤ wildPartR n q R := by
  haveI : Fact (2 ≤ q) := ⟨hq2⟩
  haveI := hNn
  set M : Subgroup ((Tq q) : Type) := N.map (tameOfSpec n q R hspec).toMonoidHom with hM
  haveI hMn : M.Normal := Subgroup.Normal.map hNn _ (tameOfSpec_surjective hspec)
  have hMbot : M = ⊥ := by
    refine o2_Tq_eq_bot hqe M ?_
    intro G _ _ _ _ f hf
    rw [hM, Subgroup.map_map]
    refine isPGroup_map_of_isProP hNp _ ?_
    rw [MonoidHom.coe_comp]
    exact hf.comp (tameOfSpec n q R hspec).continuous_toFun
  intro x hxN
  have h1 : tameOfSpec n q R hspec x ∈ M := Subgroup.mem_map.mpr ⟨x, hxN, rfl⟩
  rw [hMbot, Subgroup.mem_bot] at h1
  rw [← ker_tameOfSpec hspec]
  exact MonoidHom.mem_ker.mpr h1

end TameSpec

/-! #### The `KillsWild`-shaped wrappers, Prop. 3.4(1) -/

/-- `ψ : Γ_R/W_R → T_q`, the descent of the tame specialization. -/
noncomputable def psiR (n q : ℕ) (R : PWord (Generator n)) (hadm : KillsWild R) :
    ContinuousMonoidHom ((TameGammaR n q R) : Type) (Tq q) :=
  TameSpec.psiOfSpec n q R (TameSpec.tameSpecializes_of_killsWild hadm)

@[simp] private theorem psiR_mk (hadm : KillsWild R) (g : Generator n) :
    psiR n q R hadm (tameGammaMk n q R (gammaGen n q R g)) = tameMarking n q g :=
  TameSpec.psiOfSpec_mk _ g

theorem psiR_chiR (hadm : KillsWild R) (x : Tq q) : psiR n q R hadm (chiR n q R x) = x :=
  TameSpec.psiOfSpec_chiR _ x

theorem chiR_psiR (hadm : KillsWild R) (x : ((TameGammaR n q R) : Type)) :
    chiR n q R (psiR n q R hadm x) = x :=
  TameSpec.chiR_psiOfSpec _ x

/-- **Packet Prop. 3.4(1), first half**: `Γ_R/W_R ≅ T_{q_K}`, matching the marked generators. -/
noncomputable def gammaR_tame_equiv (n q : ℕ) (R : PWord (Generator n)) (hadm : KillsWild R) :
    ContinuousMulEquiv ((TameGammaR n q R) : Type) (Tq q) :=
  TameSpec.gammaR_tame_equiv_of_spec n q R (TameSpec.tameSpecializes_of_killsWild hadm)

/-- `ker(Γ_R ↠ T_q) = W_R`: the tame specialization has exactly the wild part as kernel. -/
theorem ker_tameR (hadm : KillsWild R) :
    (tameR n q R hadm).toMonoidHom.ker = wildPartR n q R :=
  TameSpec.ker_tameOfSpec _

/-- **Packet Prop. 3.4(1), second half**: `W_R = O₂(Γ_R)`. -/
theorem prop_3_4_one (hq2 : 2 ≤ q) (hqe : Even q) (hadm : KillsWild R)
    (N : Subgroup ((GammaR n q R) : Type)) (hNn : N.Normal)
    (hNp : IsProP 2 N) : N ≤ wildPartR n q R :=
  TameSpec.prop_3_4_one_of_spec hq2 hqe (TameSpec.tameSpecializes_of_killsWild hadm) N hNn hNp

/-! ### Part (2): the maximal pro-`2` specialization -/

/-- In a pro-`2` group the `ω₂`-power is the identity — the semantic content of Gate C's
*"replace every profinite exponent by its `2`-component"*. -/
theorem zpowHat_omega2_eq_self_of_isProP {Q : Type} [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    (hQ : IsProP 2 Q) (x : Q) : x ^ᶻ omega2 = x := by
  have hmul : (x ^ᶻ omega2) * x⁻¹ = 1 → x ^ᶻ omega2 = x := fun h => by
    rwa [mul_inv_eq_one] at h
  refine hmul (eq_one_of_forall_mem_openNormalSubgroup fun U => ?_)
  haveI : Finite (Q ⧸ U.toSubgroup) := inferInstance
  set mk : ContinuousMonoidHom Q (Q ⧸ U.toSubgroup) :=
    ⟨QuotientGroup.mk' U.toSubgroup, QuotientGroup.continuous_mk⟩ with hmk
  have hpush : mk (x ^ᶻ omega2) = (mk x) ^ᶻ omega2 := map_zpowHat _ x omega2
  have hfin : (mk x) ^ᶻ omega2 = powOmega2 (mk x) := zpowHat_omega2 (mk x)
  have hself : powOmega2 (mk x) = mk x := by
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (hQ U)) (mk x)
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pow_zero] at hk
      rw [orderOf_eq_one_iff.mp hk]
      simp only [powOmega2, one_pow]
    · have hlt : 1 < 2 ^ k := Nat.one_lt_two_pow_iff.mpr hpos.ne'
      have hexp : omega2Exp (orderOf (mk x)) = 1 := by
        rw [hk]
        show (if ((2 : ℕ) ^ k).factorization 2 = 0 then 0
          else ((2 : ℕ) ^ k / 2 ^ (((2 : ℕ) ^ k).factorization 2)) ^
            (2 ^ ((((2 : ℕ) ^ k).factorization 2) - 1)) % 2 ^ k) = 1
        rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same, if_neg hpos.ne',
          Nat.div_self (pow_pos two_pos k), one_pow, Nat.mod_eq_of_lt hlt]
      rw [powOmega2, hexp, pow_one]
  have : mk ((x ^ᶻ omega2) * x⁻¹) = 1 := by
    rw [map_mul, map_inv, hpush, hfin, hself, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).mp this

/-- **`τ` dies in every pro-`2` quotient of `Γ_R`** (packet: *"every map to a pro-`2` group kills
`τ`, because tame inertia is pro-odd"*). -/
theorem map_gammaGen_tau_eq_one_of_isProP (hq0 : q ≠ 0) (hqe : Even q) {Q : Type} [Group Q]
    [TopologicalSpace Q] [IsTopologicalGroup Q] [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] (hQ : IsProP 2 Q) (φ : ContinuousMonoidHom (GammaR n q R) Q) :
    φ (gammaGen n q R .tau) = 1 := by
  refine eq_one_of_forall_mem_openNormalSubgroup fun U => ?_
  haveI : Finite (Q ⧸ U.toSubgroup) := inferInstance
  set ψ : (GammaR n q R) →* (Q ⧸ U.toSubgroup) :=
    (QuotientGroup.mk' U.toSubgroup).comp φ.toMonoidHom with hψ
  have hrel : (ψ (gammaGen n q R .sigma))⁻¹ * ψ (gammaGen n q R .tau) * ψ (gammaGen n q R .sigma)
      = (ψ (gammaGen n q R .tau)) ^ q := by
    have h := congrArg ⇑ψ (gammaR_tame_relation (n := n) (q := q) (R := R))
    simpa only [conjP, map_mul, map_inv, map_pow] using h
  have hodd : Odd (orderOf (ψ (gammaGen n q R .tau))) :=
    TameQ.odd_order (orderOf_pos (ψ (gammaGen n q R .sigma))).ne' hq0 hqe hrel
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp (hQ U)) (ψ (gammaGen n q R .tau))
  rw [hk] at hodd
  have hone : ψ (gammaGen n q R .tau) = 1 := by
    rcases Nat.eq_zero_or_pos k with rfl | hpos
    · rw [pow_zero] at hk; exact orderOf_eq_one_iff.mp hk
    · exact absurd hodd (Nat.not_odd_iff_even.mpr (Nat.even_pow.mpr ⟨even_two, hpos.ne'⟩))
  exact (QuotientGroup.eq_one_iff _).mp hone

/-- **Packet Prop. 3.4(2)**: *the maximal pro-`2` quotient of `Γ_R` is
`D_P = ⟨σ, x₀, …, x_n ∣ P = 1⟩_{pro-2}`, `P = pro2 R`* — in universal-property form.

A marking `t` of the alphabet in a pro-`2` group `Q` extends to a continuous homomorphism out of
`Γ_R` **iff** `t` kills `τ` and kills the pro-`2` specialization `P = pro2 R` of the wild word.
That is exactly the universal property of `D_P` (whose generators are `σ, x₀, …, x_n` — `τ` is
absent — and whose single relator is `P`), so the maximal pro-`2` quotients of `Γ_R` and of `D_P`
have the same continuous homomorphisms into every pro-`2` group, hence agree.

Both hypotheses of the packet's proposition are used exactly once and only through F2:
`Marking.eval_pro2` converts `t.eval R` into `t.eval (pro2 R)`, and the `τ`-death half comes
from §1's Lemma 3.1. -/
theorem prop_3_4_two (hq0 : q ≠ 0) (hqe : Even q) (Q : ProfiniteGrp.{0}) (hQ : IsProP 2 Q)
    (t : Marking n ((Q : Type))) :
    (∃ φ : ContinuousMonoidHom (GammaR n q R) Q, ∀ g, φ (gammaGen n q R g) = t g)
      ↔ (t.τ = 1 ∧ t.eval (pro2 R) = 1) := by
  have hω : ∀ x : (Q : Type), x ^ᶻ omega2 = x := zpowHat_omega2_eq_self_of_isProP hQ
  constructor
  · rintro ⟨φ, hφ⟩
    have hτ : t.τ = 1 := by
      rw [show t.τ = t .tau from rfl, ← hφ .tau]
      exact map_gammaGen_tau_eq_one_of_isProP hq0 hqe hQ φ
    refine ⟨hτ, ?_⟩
    have hmark : (gammaMarking n q R).map ⇑φ = t := by ext g; exact hφ g
    have hR : t.eval R = 1 := by
      rw [← hmark, ← Marking.map_eval, gammaMarking_eval_R, map_one]
    rw [Marking.eval_pro2 t hτ hω R, hR]
  · rintro ⟨hτ, hP⟩
    have hR : t.eval R = 1 := by rw [← Marking.eval_pro2 t hτ hω R, hP]
    set base : FreeProfiniteGroup (Generator n) ⟶ Q :=
      (FreeProfiniteGroup.homEquiv (Generator n) Q).symm ⇑t with hbase
    have hbase_of : ∀ g, base.hom.toMonoidHom (FreeProfiniteGroup.of g) = t g := fun g =>
      FreeProfiniteGroup.homEquiv_symm_of _ _ _
    have hkill : ∀ r ∈ gammaRelators n q R, base.hom.toMonoidHom r = 1 := by
      rintro r (rfl | rfl)
      · simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow, hbase_of]
        rw [show t .tau = (1 : (Q : Type)) from hτ]
        group
      · have h := Marking.map_eval base.hom (freeMarking n) R
        have hmark : (freeMarking n).map ⇑base.hom = t := by ext g; exact hbase_of g
        show base.hom ((freeMarking n).eval R) = 1
        rw [h, hmark, hR]
    -- GR1: the wild-`2` clause of `gammaLift` is automatic in a pro-`2` target
    exact ⟨gammaLift n q R base.hom hkill fun V => wildMap_of_isProP hQ base.hom.toMonoidHom V,
      fun g => (gammaLift_gammaMk _ _ _ _ _ _ (FreeProfiniteGroup.of g)).trans (hbase_of g)⟩

/-! ### Part (3): the induced unramified character -/

/-- **Packet Prop. 3.4(3)**: the induced unramified character has `ν(σ) = 1` and `ν(x_i) = 0`
(and `ν(τ) = 0`), read through the tame specialization. -/
theorem TameSpec.prop_3_4_three_of_spec (hspec : TameSpec.TameSpecializes n q R) :
    nuTq q (TameSpec.tameOfSpec n q R hspec (gammaGen n q R .sigma)) = ztwoOne ∧
      nuTq q (TameSpec.tameOfSpec n q R hspec (gammaGen n q R .tau)) = 1 ∧
      ∀ i : Fin (n + 1),
        nuTq q (TameSpec.tameOfSpec n q R hspec (gammaGen n q R (.wild i))) = 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [TameSpec.tameOfSpec_gammaGen]; exact nuTq_tqSigma q
  · rw [TameSpec.tameOfSpec_gammaGen]; exact nuTq_tqTau q
  · intro i
    rw [TameSpec.tameOfSpec_gammaGen]
    show nuTq q 1 = 1
    exact map_one _

/-- **Packet Prop. 3.4(3)**, at F3's original `KillsWild` hypothesis. -/
theorem prop_3_4_three (hadm : KillsWild R) :
    nuTq q (tameR n q R hadm (gammaGen n q R .sigma)) = ztwoOne ∧
      nuTq q (tameR n q R hadm (gammaGen n q R .tau)) = 1 ∧
      ∀ i : Fin (n + 1), nuTq q (tameR n q R hadm (gammaGen n q R (.wild i))) = 1 :=
  TameSpec.prop_3_4_three_of_spec _

/-! ### The `Γ_R` side of Theorem 3.5, assembled -/

theorem ker_maxProPMk (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    (maxProPMk 2 G).toMonoidHom.ker = proPKernel 2 G := by
  ext x
  rw [MonoidHom.mem_ker]
  exact quotientMk_eq_one_iff _

namespace TameSpec

/-- The `2`-primary unramified character of the maximal pro-`2` quotient `Γ_R(2)`, obtained by
descending `ν₂ ∘ tame_R` (legitimate because `ℤ₂` is pro-`2`).  This is packet Prop. 3.4(3)'s
`ν` on the `D_P` side, and by construction it makes the `ν`-square of Theorem 3.5 commute. -/
noncomputable def nuTwoOfSpec (n q : ℕ) (R : PWord (Generator n))
    (hspec : TameSpecializes n q R) :
    ContinuousMonoidHom (maxProPQuotient 2 ((GammaR n q R) : Type)) Ztwo :=
  quotientLift (proPKernel 2 ((GammaR n q R) : Type)) ((nuTq q).comp (tameOfSpec n q R hspec))
    (proPKernel_le_ker isProP_maxProPQuotient _)

theorem nuTwoOfSpec_compat (hspec : TameSpecializes n q R) (g : (GammaR n q R : Type)) :
    nuTq q (tameOfSpec n q R hspec g) = nuTwoOfSpec n q R hspec (maxProPMk 2 _ g) :=
  (quotientLift_quotientMk (proPKernel 2 ((GammaR n q R) : Type))
    ((nuTq q).comp (tameOfSpec n q R hspec))
    (proPKernel_le_ker isProP_maxProPQuotient _) g).symm

/-- **Packet Theorem 3.5, the `Γ_R` side.**  For a `Γ_R` whose wild word tame-specializes, at an
even `q ≥ 2`, the natural map

  `Γ_R ⟶ ∂ = T_q ×_{ℤ₂} Γ_R(2)`

is **surjective**.  This is §3's relative-Goursat theorem instantiated at the two specializations
of Prop. 3.4: `tameOfSpec` (part 1) and the maximal pro-`2` quotient map (part 2), whose target
is `D_P` by `prop_3_4_two`.

⚠ This — not the `KillsWild`-shaped `gammaR_boundary_surjective` below — is the form the branch
lanes and `CertificateMain` can actually instantiate, because `KillsWild` is refuted by every
frozen branch word. -/
theorem gammaR_boundary_surjective_of_spec (hq2 : 2 ≤ q) (hqe : Even q)
    (hspec : TameSpecializes n q R) :
    Function.Surjective (fun g : ((GammaR n q R) : Type) =>
      (⟨(tameOfSpec n q R hspec g, maxProPMk 2 _ g), nuTwoOfSpec_compat hspec g⟩ :
        ↥(boundarySubgroupQ q (nuTwoOfSpec n q R hspec)))) :=
  boundary_jointly_surjective_of_maxProP (by omega) hqe (nuTwoOfSpec n q R hspec)
    (tameOfSpec n q R hspec) (maxProPMk 2 _) (tameOfSpec_surjective hspec)
    (quotientMk_surjective _) (ker_maxProPMk _) (nuTwoOfSpec_compat hspec)

end TameSpec

/-! #### The `KillsWild`-shaped wrappers, Theorem 3.5 -/

/-- The `2`-primary unramified character of `Γ_R(2)`, at F3's original `KillsWild` hypothesis. -/
noncomputable def nuTwoR (n q : ℕ) (R : PWord (Generator n)) (hadm : KillsWild R) :
    ContinuousMonoidHom (maxProPQuotient 2 ((GammaR n q R) : Type)) Ztwo :=
  TameSpec.nuTwoOfSpec n q R (TameSpec.tameSpecializes_of_killsWild hadm)

theorem nuTwoR_compat (hadm : KillsWild R) (g : (GammaR n q R : Type)) :
    nuTq q (tameR n q R hadm g) = nuTwoR n q R hadm (maxProPMk 2 _ g) :=
  TameSpec.nuTwoOfSpec_compat _ g

/-- **Packet Theorem 3.5, the `Γ_R` side**, at F3's original `KillsWild` hypothesis. -/
theorem gammaR_boundary_surjective (hq2 : 2 ≤ q) (hqe : Even q) (hadm : KillsWild R) :
    Function.Surjective (fun g : ((GammaR n q R) : Type) =>
      (⟨(tameR n q R hadm g, maxProPMk 2 _ g), nuTwoR_compat hadm g⟩ :
        ↥(boundarySubgroupQ q (nuTwoR n q R hadm)))) :=
  TameSpec.gammaR_boundary_surjective_of_spec hq2 hqe _

end PropThreeFour

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

@[simp] theorem tqClassify_tqSigma (q : ℕ) (P : ProfiniteGrp.{0}) {a b : P}
    (h : conjP b a = b ^ q) :
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
