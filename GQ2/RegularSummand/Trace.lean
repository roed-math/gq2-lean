/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.Algebra.Module.ZMod
public import Mathlib.GroupTheory.Sylow
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.RingTheory.UniqueFactorizationDomain.Finsupp
public import Mathlib.Algebra.Module.StablyFree.Basic
public import Mathlib.Analysis.Normed.Ring.Lemmas
public import GQ2.Words
public import GQ2.QuadraticFp2
public import GQ2.Tame
public import GQ2.TameQuotient

@[expose] public section

set_option backward.privateInPublic true
set_option backward.privateInPublic.warn false

/-!
# Relative trace and tame-kernel foundations for Lemma 6.11

The odd-index relative trace and the finite tame-group kernel facts used by the regular-summand
argument.  See `GQ2.RegularSummand` for the paper-facing overview and references.
-/

namespace GQ2

/-! ## The odd-index relative trace

`regular_summand_of_subgroup_summand` is the paper's "Sylow criterion for modular
projectivity" in the concrete split-pair shape: an equivariant split summand of a regular
module over an odd-index subgroup `P ≤ C` is one over `C`.  Everything is function-level —
no induced-module formalism: `ι v n g := j (g⁻¹ • v) n 1` and
`ρ F := ∑_{gP ∈ C/P} g • q (F n (g·—))` (the relative trace, well-defined on cosets by the
`P`-equivariance of `q`), with `ρ ∘ ι = [C : P] • id = id` because the index is odd and `V`
is 2-torsion.  This reduces `lemma_6_11` to its weight-orbit kernel
`sylow_split_pair_of_ramified` below (pp. 29–30, steps 1–2 of the plan). -/

section RelativeTrace

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V]

/-- The relative-trace coset summand: the class `g·P` contributes `g • q (F n (g·—))`,
independently of the representative by the `P`-equivariance of `q`. -/
private def cosetTrace (P : Subgroup C) {r : ℕ} (q : (Fin r → ↥P → ZMod 2) →+ V)
    (hq : ∀ (p : ↥P) (F : Fin r → ↥P → ZMod 2), q (fun n x => F n (p⁻¹ * x)) = (p : C) • q F)
    (F : Fin r → C → ZMod 2) : C ⧸ P → V :=
  Quotient.lift (fun g : C => g • q (fun n σ => F n (g * ↑σ))) (by
    intro g g' hgg'
    have hp : g⁻¹ * g' ∈ P := QuotientGroup.leftRel_apply.mp hgg'
    have hg' : g' = g * ((⟨g⁻¹ * g', hp⟩ : ↥P) : C) := by
      show g' = g * (g⁻¹ * g')
      rw [mul_inv_cancel_left]
    have step : q (fun (n : Fin r) (σ : ↥P) => F n (g * ↑σ))
        = ((⟨g⁻¹ * g', hp⟩ : ↥P) : C) • q (fun (n : Fin r) (σ : ↥P) => F n (g' * ↑σ)) := by
      refine (congrArg (⇑q) ?_).trans
        (hq ⟨g⁻¹ * g', hp⟩ (fun (n : Fin r) (σ : ↥P) => F n (g' * ↑σ)))
      funext n x
      show F n (g * ↑x) = F n (g' * ((g⁻¹ * g')⁻¹ * ↑x))
      refine congrArg (F n) ?_
      group
    show g • q (fun (n : Fin r) (σ : ↥P) => F n (g * ↑σ))
       = g' • q (fun (n : Fin r) (σ : ↥P) => F n (g' * ↑σ))
    rw [step, ← mul_smul, ← hg'])

omit [Finite C] in
private theorem cosetTrace_mk (P : Subgroup C) {r : ℕ} (q : (Fin r → ↥P → ZMod 2) →+ V)
    (hq : ∀ (p : ↥P) (F : Fin r → ↥P → ZMod 2), q (fun n x => F n (p⁻¹ * x)) = (p : C) • q F)
    (F : Fin r → C → ZMod 2) (g : C) :
    cosetTrace P q hq F (QuotientGroup.mk g) = g • q (fun n σ => F n (g * ↑σ)) := rfl

/-- **The odd-index relative trace** (the "Sylow criterion" step of Lemma 6.11): if `V` is an
equivariant split summand of a regular module over a subgroup `P ≤ C` of **odd index**, then
it is an equivariant split summand of a regular module over `C` (same rank). -/
theorem regular_summand_of_subgroup_summand (hV2 : ∀ v : V, v + v = 0)
    (P : Subgroup C) (hodd : Odd P.index) {r : ℕ}
    (j : V →+ (Fin r → ↥P → ZMod 2)) (q : (Fin r → ↥P → ZMod 2) →+ V)
    (hj : ∀ (p : ↥P) (v : V) (n : Fin r) (x : ↥P), j ((p : C) • v) n x = j v n (p⁻¹ * x))
    (hq : ∀ (p : ↥P) (F : Fin r → ↥P → ZMod 2), q (fun n x => F n (p⁻¹ * x)) = (p : C) • q F)
    (hqj : ∀ v, q (j v) = v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (ρ : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), ρ (fun n x => F n (h⁻¹ * x)) = h • ρ F) ∧
      ∀ v : V, ρ (ι v) = v := by
  haveI : Fintype (C ⧸ P) := Fintype.ofFinite _
  refine ⟨r,
    AddMonoidHom.mk' (fun v => fun n g => j (g⁻¹ • v) n 1) (by
      intro v w
      funext n g
      show j (g⁻¹ • (v + w)) n 1 = j (g⁻¹ • v) n 1 + j (g⁻¹ • w) n 1
      rw [smul_add, map_add]
      rfl),
    AddMonoidHom.mk' (fun F => ∑ᶠ x : C ⧸ P, cosetTrace P q hq F x) (by
      intro F F'
      have hpt : ∀ x : C ⧸ P,
          cosetTrace P q hq (F + F') x = cosetTrace P q hq F x + cosetTrace P q hq F' x := by
        intro x
        induction x using Quotient.ind with
        | _ g =>
          show cosetTrace P q hq (F + F') (QuotientGroup.mk g) = _
          rw [cosetTrace_mk, cosetTrace_mk, cosetTrace_mk]
          have hsp : (fun (n : Fin r) (σ : ↥P) => (F + F') n (g * ↑σ))
              = (fun (n : Fin r) (σ : ↥P) => F n (g * ↑σ))
                + fun (n : Fin r) (σ : ↥P) => F' n (g * ↑σ) := rfl
          rw [hsp, map_add, smul_add]
      rw [finsum_congr hpt]
      exact finsum_add_distrib (Set.toFinite _) (Set.toFinite _)),
    ?_, ?_, ?_⟩
  · intro h v n x
    show j (x⁻¹ • (h • v)) n 1 = j ((h⁻¹ * x)⁻¹ • v) n 1
    rw [← mul_smul, mul_inv_rev, inv_inv]
  · intro h F
    show ∑ᶠ x : C ⧸ P, cosetTrace P q hq (fun n y => F n (h⁻¹ * y)) x
       = h • ∑ᶠ x : C ⧸ P, cosetTrace P q hq F x
    have hpt : ∀ x : C ⧸ P, cosetTrace P q hq (fun n y => F n (h⁻¹ * y)) x
        = h • cosetTrace P q hq F (h⁻¹ • x) := by
      intro x
      induction x using Quotient.ind with
      | _ g =>
        rw [show (h⁻¹ • (QuotientGroup.mk g : C ⧸ P)) = QuotientGroup.mk (h⁻¹ * g) from
          MulAction.Quotient.smul_mk P h⁻¹ g]
        rw [cosetTrace_mk, cosetTrace_mk]
        have hfun : (fun (n : Fin r) (σ : ↥P) => F n (h⁻¹ * (g * ↑σ)))
            = fun (n : Fin r) (σ : ↥P) => F n ((h⁻¹ * g) * ↑σ) := by
          funext n σ
          rw [mul_assoc]
        rw [hfun, ← mul_smul, mul_inv_cancel_left]
    rw [finsum_congr hpt]
    have hre : ∑ᶠ x : C ⧸ P, h • cosetTrace P q hq F (h⁻¹ • x)
        = ∑ᶠ x : C ⧸ P, h • cosetTrace P q hq F x :=
      finsum_comp_equiv
        (⟨fun x => h⁻¹ • x, fun x => h • x, fun x => smul_inv_smul h x,
          fun x => inv_smul_smul h x⟩ : (C ⧸ P) ≃ (C ⧸ P))
        (f := fun y => h • cosetTrace P q hq F y)
    rw [hre, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.smul_sum]
  · intro v
    show ∑ᶠ x : C ⧸ P, cosetTrace P q hq (fun n g => j (g⁻¹ • v) n 1) x = v
    have hpt : ∀ x : C ⧸ P, cosetTrace P q hq (fun n g => j (g⁻¹ • v) n 1) x = v := by
      intro x
      induction x using Quotient.ind with
      | _ g =>
        rw [cosetTrace_mk]
        have hfun : (fun (n : Fin r) (σ : ↥P) => j ((g * ↑σ)⁻¹ • v) n 1)
            = j (g⁻¹ • v) := by
          funext n σ
          have h1 : (g * ↑σ)⁻¹ • v = ((σ⁻¹ : ↥P) : C) • (g⁻¹ • v) := by
            rw [← mul_smul, mul_inv_rev]
            push_cast
            rfl
          rw [h1, hj σ⁻¹ (g⁻¹ • v) n 1, inv_inv, mul_one]
        rw [hfun, hqj, smul_inv_smul]
    rw [finsum_congr hpt, finsum_eq_sum_of_fintype, Finset.sum_const, Finset.card_univ]
    have hcard : Fintype.card (C ⧸ P) = P.index := by
      rw [Subgroup.index, Nat.card_eq_fintype_card]
    rw [hcard]
    exact odd_nsmul_eq_self hV2 hodd v

end RelativeTrace

/-! ## Kernel toolbox: structure facts for the weight-orbit argument

Abstract `(s, t)`-forms (apply at `s := c tameSigma`, `t := c tameTau` via `tame_relation`,
the `odd_orderOf_tameInertia` pattern): the quotient by the odd normal inertia `⟨t⟩` is
cyclic, every 2-subgroup is cyclic (step 1 of the discharge plan), and on a ramified simple
module the inertia fixed space vanishes. -/

section KernelToolbox

variable {C : Type} [Group C] [Finite C]

omit [Finite C] in
/-- With `⟨t⟩` normal (supplied by `Tame.zpowers_normal_of_tame` at the call sites), the
quotient of a `{s, t}`-generated group by `⟨t⟩` is **cyclic**, generated by the image of `s`
(the image of `t` is trivial, and generation passes to the quotient). -/
theorem quotient_zpowers_isCyclic_of_tame {s t : C} [(Subgroup.zpowers t).Normal]
    (hgen : Subgroup.closure {s, t} = ⊤) :
    IsCyclic (C ⧸ Subgroup.zpowers t) := by
  refine ⟨⟨QuotientGroup.mk s, fun x => ?_⟩⟩
  have himg : Subgroup.closure
      ((QuotientGroup.mk' (Subgroup.zpowers t)) '' ({s, t} : Set C)) = ⊤ := by
    rw [← MonoidHom.map_closure, hgen]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have htop : Subgroup.zpowers (QuotientGroup.mk s : C ⧸ Subgroup.zpowers t) = ⊤ := by
    refine top_le_iff.mp ?_
    rw [← himg]
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨z, hz, rfl⟩
    rcases (hz : z = s ∨ z = t) with rfl | h2
    · exact Subgroup.mem_zpowers _
    · rw [h2, show (QuotientGroup.mk' (Subgroup.zpowers t)) t = 1 from
        (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_zpowers t)]
      exact Subgroup.one_mem _
  have hx : x ∈ (⊤ : Subgroup (C ⧸ Subgroup.zpowers t)) := Subgroup.mem_top x
  rwa [← htop] at hx

/-- **Every 2-subgroup of a finite tame-generated group is cyclic** (step 1 of the discharge
plan): its intersection with the odd inertia `⟨t⟩` is trivial by coprimality, so it embeds in
the cyclic quotient `C/⟨t⟩`.  In particular the Sylow 2-subgroup in
`sylow_split_pair_of_ramified` is cyclic. -/
theorem isCyclic_of_isPGroup_two_of_tame {s t : C}
    (hgen : Subgroup.closure {s, t} = ⊤) (hrel : s⁻¹ * t * s = t ^ 2)
    (Q : Subgroup C) (hQ : IsPGroup 2 Q) : IsCyclic ↥Q := by
  haveI : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  haveI := quotient_zpowers_isCyclic_of_tame hgen
  have hodd : Odd (orderOf t) := Tame.tame_odd_order (orderOf_pos s).ne' hrel
  have hbot : Q ⊓ Subgroup.zpowers t = ⊥ := by
    refine disjoint_iff.mp (Subgroup.disjoint_of_coprime_natCard ?_)
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    rw [hk, Nat.card_zpowers]
    refine Nat.Coprime.pow_left k ?_
    refine (Nat.prime_two.coprime_iff_not_dvd).mpr fun hdvd => ?_
    have h1 := Nat.odd_iff.mp hodd
    omega
  refine isCyclic_of_injective
    ((QuotientGroup.mk' (Subgroup.zpowers t)).comp Q.subtype) ?_
  rw [← MonoidHom.ker_eq_bot_iff]
  refine (Subgroup.eq_bot_iff_forall _).mpr fun x hx => ?_
  have hxt : (x : C) ∈ Subgroup.zpowers t := (QuotientGroup.eq_one_iff (x : C)).mp hx
  have hxQ : (x : C) ∈ Q ⊓ Subgroup.zpowers t := ⟨x.2, hxt⟩
  rw [hbot, Subgroup.mem_bot] at hxQ
  exact Subtype.ext hxQ

/-- **The inertia fixed space vanishes on a ramified simple module**: `{v | t • v = v}` is a
`C`-stable additive subgroup (conjugates of `t` lie in the normal `⟨t⟩`, and the stabilizer of
a fixed vector contains all of `⟨t⟩`), so simplicity forces it to be `⊥` — it is not `⊤`
because the module is ramified. -/
theorem fixedPoints_tame_inertia_eq_zero
    {V : Type} [AddCommGroup V] [DistribMulAction C V]
    {s t : C} (hgen : Subgroup.closure {s, t} = ⊤) (hrel : s⁻¹ * t * s = t ^ 2)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∀ v : V, t • v = v → v = 0 := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  set W : AddSubgroup V :=
    { carrier := {v | t • v = v}
      zero_mem' := smul_zero t
      add_mem' := fun ha hb => by
        show t • (_ + _) = _
        rw [smul_add, ha, hb]
      neg_mem' := fun ha => by
        show t • (-_) = -_
        rw [smul_neg, ha] } with hWdef
  have hstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    have hconj : h⁻¹ * t * h ∈ Subgroup.zpowers t := by
      have := hnorm.conj_mem t (Subgroup.mem_zpowers t) h⁻¹
      rwa [inv_inv] at this
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hconj
    have hfix : (h⁻¹ * t * h) • w = w := by
      rw [← hn]
      exact zpow_mem (show t ∈ MulAction.stabilizer C w from hw) n
    show t • (h • w) = h • w
    calc t • (h • w) = (t * h) • w := (mul_smul t h w).symm
      _ = (h * (h⁻¹ * t * h)) • w := by group
      _ = h • ((h⁻¹ * t * h) • w) := mul_smul _ _ _
      _ = h • w := by rw [hfix]
  rcases hsimple W hstable with hbot | htop
  · intro v hv
    have : v ∈ W := hv
    rwa [hbot, AddSubgroup.mem_bot] at this
  · obtain ⟨v, hv⟩ := hram
    exact absurd (htop ▸ AddSubgroup.mem_top v : v ∈ W) hv

end KernelToolbox

end GQ2
