/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import GQ2.TameQuotient
import GQ2.Tame

/-!
# Lemma 6.11: ramified simple modules are split summands of regular modules  (P-15f1)

The **paper node** Lemma 6.11 (§6.3, proof pp. 29–30): a ramified simple faithful module `V`
over the tame image `H_V` is a projective `𝔽₂[H_V]`-module — stated here in the equivalent
consumer shape *`V` is an equivariant split summand of a regular module `𝔽₂[H_V]^N`*.  The
regular module is carried as `Fin N → C → ZMod 2` with the **left-translation action spelled
inline** (`(h • F) n x = F n (h⁻¹x)`), so the statement needs no bespoke action instances.

## Status: PROVED (P-17e4, 2026-07-06) — std-3, no `sorry`, no B-axioms

`#print axioms GQ2.lemma_6_11 = [propext, Classical.choice, Quot.sound]`.  This is the
paper's **own** lemma — no single literature theorem states it (the paper assembles it from
Clifford, Ann. of Math. **38** (1937) 533–550, and Higman, Duke Math. J. **21** (1954)
369–376, plus elementary facts), so it was carried as a sorried allowlisted paper node
(P-15f1) until its discharge here.

## Proof architecture (self-contained finite representation theory, no arithmetic)

1. `P` a Sylow 2-subgroup of `C`: cyclic (`isCyclic_of_isPGroup_two_of_tame` — it meets the
   odd inertia `⟨c τ⟩` trivially and embeds in the cyclic quotient).
2. `V|_P` is free over `𝔽₂[P]` (`sylow_free_of_ramified`): the constructive counting
   criterion `free_of_card_fixedPoints_pow_le` (geometric-series retraction, no structure
   theorem) reduces freeness to the bound `#V^P ^ |P| ≤ #V`; Jordan-block concavity
   (`card_fixedPoints_pow_le_of_half`) reduces the bound to the single involution
   `ω = g₀^{2^{s−1}}`; and `involution_fixedPoints_sq_le` proves `#V^ω ^ 2 ≤ #V` by an
   explicit `𝔽₂`-rational **trace element** (see the `InvolutionKernel` section header) —
   a recorded deviation from the paper's `𝔽̄₂` weight-orbit argument.
3. Freeness over `P` ⟹ split summand over `C`: the odd-index relative trace
   `regular_summand_of_subgroup_summand` (the sibling of
   `LocalKummer.inflationVanishes_of_oddNormal`'s averaging — `odd_nsmul_eq_self`,
   no division).

Tickets: P-15f1 (statement, `docs/p15f1-dimcount-scoping.md` §2), P-17e4 (proof; the board
row has the full increment history).
-/

namespace GQ2

/-! ## Step 3 of the discharge plan: the odd-index relative trace  (P-17e4, proved)

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

/-- In a 2-torsion additive group, an odd multiple is the identity.  (Local copy of
`LocalKummer.odd_nsmul_eq_self`, which lives far higher in the import DAG.) -/
private theorem odd_nsmul_eq_self' (htor : ∀ a : V, a + a = 0)
    {n : ℕ} (hn : Odd n) (x : V) : n • x = x := by
  obtain ⟨k, rfl⟩ := hn
  rw [add_nsmul, one_nsmul, mul_nsmul', two_nsmul, htor, zero_add]

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
    exact odd_nsmul_eq_self' hV2 hodd v

end RelativeTrace

/-! ## Kernel toolbox  (P-17e4, proved): structure facts for the weight-orbit argument

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
    have hzz : z = s ∨ z = t := hz
    rcases hzz with rfl | h2
    · exact Subgroup.mem_zpowers _
    · rw [h2]
      have ht1 : (QuotientGroup.mk' (Subgroup.zpowers t)) t = 1 :=
        (QuotientGroup.eq_one_iff t).mpr (Subgroup.mem_zpowers t)
      rw [ht1]
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
  have hxt : (x : C) ∈ Subgroup.zpowers t := by
    have := (QuotientGroup.eq_one_iff (x : C)).mp hx
    exact this
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
      have htmem : t ∈ MulAction.stabilizer C w := hw
      have : t ^ n ∈ MulAction.stabilizer C w := zpow_mem htmem n
      exact this
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

/-! ## The counting criterion for `𝔽₂[P]`-freeness over a cyclic 2-group  (P-17e4, proved)

`free_of_card_fixedPoints_pow_le`: a finite 2-torsion module `V` over a **cyclic 2-group** `P`
satisfying the counting bound `#V^P ^ |P| ≤ #V` is equivariantly isomorphic to a regular
module `Fin r → P → ZMod 2`.  This is the 𝔽₂-rational endgame of the paper's Lemma 6.11
(pp. 29–30): the paper produces a regular `𝔽̄₂[P]`-basis from free weight orbits and descends
projectivity along the faithfully flat `𝔽₂ ⊆ 𝔽̄₂`; the counting criterion is the rational
shadow of that descent (the reverse bound `#V ≤ #V^P ^ |P|` always holds — Jordan filtration
of the nilpotent `ν := γ + 1`, `γ` the generator action — so the hypothesis pins every block
to full size `|P|`).

Proof shape: `ν^{2^s} = 0` and the group sum is `∑_{p ∈ P} p = ν^{2^s−1}` (freshman's dream
in characteristic 2 — no Lucas/Kummer needed).  If some `v₀` has `ν^{2^s−1} v₀ ≠ 0`, pick a
functional `λ` with `λ(ν^{2^s−1} v₀) = 1`; then the composite `T := φ ∘ j` of the orbit map
`j F := ∑_x F x • x•v₀` with the coefficient map `φ w := (x ↦ λ(x⁻¹•w))` is the convolution
by an augmentation-1 element, i.e. `T = 1 + (nilpotent)·B` — invertible by an **explicit
geometric series** — so `ρ := T⁻¹ ∘ φ` retracts `j` and one free rank-1 block splits off
equivariantly; recurse on the complement (the bound is inherited).  Otherwise
`ν^{2^s−1} = 0`, the kernel filtration gives `#V ≤ #V^P ^ (2^s−1)`, and the counting
hypothesis collapses `V = 0`. -/

section FreenessCriterion

private theorem zmod2_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide

private theorem two_zmod_two_eq_zero : (2 : ZMod 2) = 0 := by decide

/-- Freshman's dream for commuting elements in a ring with `2 = 0`:
`(A + B)^(2^k) = A^(2^k) + B^(2^k)`. -/
private theorem add_pow_two_pow_of_two_eq_zero {R : Type} [Ring R] (h2 : (2 : R) = 0)
    {A B : R} (hAB : Commute A B) (k : ℕ) :
    (A + B) ^ 2 ^ k = A ^ 2 ^ k + B ^ 2 ^ k := by
  have key : ∀ x y : R, Commute x y → (x + y) ^ 2 = x ^ 2 + y ^ 2 := by
    intro x y hxy
    rw [pow_two, pow_two, pow_two, add_mul, mul_add, mul_add, ← hxy.eq]
    rw [← add_assoc, add_assoc (x * x), ← two_mul, h2, zero_mul, add_zero]
  induction k with
  | zero => rw [pow_zero, pow_one, pow_one, pow_one]
  | succ k IH =>
    rw [pow_succ, pow_mul, pow_mul, pow_mul, IH,
      key (A ^ 2 ^ k) (B ^ 2 ^ k) (hAB.pow_pow _ _)]

/-- In a ring with `2 = 0`, the truncated geometric sum over a 2-power range is itself a
power: `∑_{j<2^k} A^j = (A + 1)^(2^k − 1)`.  (The binomial coefficients `C(2^k−1, i)` are
all odd, but no Lucas theorem is needed — squaring induction suffices.) -/
private theorem geom_sum_two_pow_of_two_eq_zero {R : Type} [Ring R] (h2 : (2 : R) = 0)
    (A : R) (k : ℕ) :
    ∑ j ∈ Finset.range (2 ^ k), A ^ j = (A + 1) ^ (2 ^ k - 1) := by
  induction k with
  | zero =>
    rw [pow_zero, Finset.range_one, Finset.sum_singleton, pow_zero, Nat.sub_self, pow_zero]
  | succ k IH =>
    have h1 : (1 : ℕ) ≤ 2 ^ k := Nat.one_le_two_pow
    have hsp : (2 : ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [pow_succ, mul_two]
    have hsplit : ∑ j ∈ Finset.range (2 ^ (k + 1)), A ^ j
        = ∑ j ∈ Finset.range (2 ^ k), A ^ j
          + ∑ j ∈ Finset.range (2 ^ k), A ^ (2 ^ k + j) := by
      rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive (fun j => A ^ j)
        (Nat.zero_le (2 ^ k)) (by omega : (2 : ℕ) ^ k ≤ 2 ^ (k + 1)), ← Finset.range_eq_Ico,
        Finset.sum_Ico_eq_sum_range, (by omega : 2 ^ (k + 1) - 2 ^ k = 2 ^ k)]
    rw [hsplit, Finset.sum_congr rfl (fun j _ => pow_add A (2 ^ k) j), ← Finset.mul_sum, IH,
      show (A + 1) ^ (2 ^ k - 1) + A ^ 2 ^ k * (A + 1) ^ (2 ^ k - 1)
          = (A + 1) ^ 2 ^ k * (A + 1) ^ (2 ^ k - 1) from by
        rw [add_pow_two_pow_of_two_eq_zero h2 (Commute.one_right A) k, one_pow,
          add_comm (A ^ 2 ^ k) 1, add_mul, one_mul],
      ← pow_add, (by omega : 2 ^ k + (2 ^ k - 1) = 2 ^ (k + 1) - 1)]

/-- Explicit two-sided inverse of `x + 1` for nilpotent `x` in a ring with `2 = 0`
(geometric series; note `x + 1 = x − 1` in characteristic 2). -/
private theorem geom_inverse_of_nilpotent {R : Type} [Ring R] (h2 : (2 : R) = 0)
    {x : R} {m : ℕ} (hm : x ^ m = 0) :
    (x + 1) * ∑ i ∈ Finset.range m, x ^ i = 1
      ∧ (∑ i ∈ Finset.range m, x ^ i) * (x + 1) = 1 := by
  have h11 : (1 : R) + 1 = 0 := by rw [one_add_one_eq_two, h2]
  have hneg : (-1 : R) = 1 := neg_eq_of_add_eq_zero_left h11
  constructor
  · have h := mul_geom_sum x m
    rwa [hm, zero_sub, sub_eq_add_neg, hneg] at h
  · have h := geom_sum_mul x m
    rwa [hm, zero_sub, sub_eq_add_neg, hneg] at h

/-- `Fin.cons` as an additive equivalence `M × (Fin n → M) ≃+ (Fin (n+1) → M)`. -/
private def finConsAddEquiv (M : Type) [AddCommMonoid M] (n : ℕ) :
    (M × (Fin n → M)) ≃+ (Fin (n + 1) → M) where
  toFun a := Fin.cons (α := fun _ => M) a.1 a.2
  invFun F := (F 0, fun i => F i.succ)
  left_inv a := by
    refine Prod.ext ?_ ?_
    · exact Fin.cons_zero (α := fun _ => M) a.1 a.2
    · funext i
      exact Fin.cons_succ (α := fun _ => M) a.1 a.2 i
  right_inv F := by
    funext i
    refine Fin.cases ?_ ?_ i
    · exact Fin.cons_zero (α := fun _ => M) _ _
    · intro j
      exact Fin.cons_succ (α := fun _ => M) _ _ j
  map_add' a b := by
    funext i
    refine Fin.cases ?_ ?_ i
    · show Fin.cons (α := fun _ => M) (a.1 + b.1) (a.2 + b.2) 0
        = Fin.cons (α := fun _ => M) a.1 a.2 0 + Fin.cons (α := fun _ => M) b.1 b.2 0
      rw [Fin.cons_zero, Fin.cons_zero, Fin.cons_zero]
    · intro j
      show Fin.cons (α := fun _ => M) (a.1 + b.1) (a.2 + b.2) j.succ
        = Fin.cons (α := fun _ => M) a.1 a.2 j.succ
          + Fin.cons (α := fun _ => M) b.1 b.2 j.succ
      rw [Fin.cons_succ, Fin.cons_succ, Fin.cons_succ]
      rfl

variable {P : Type} [Group P] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  [DistribMulAction P V] [SMulCommClass P (ZMod 2) V]

/-- The action of a fixed group element as a `ZMod 2`-linear endomorphism. -/
private def genOp (g₀ : P) : Module.End (ZMod 2) V where
  toFun v := g₀ • v
  map_add' a b := smul_add g₀ a b
  map_smul' c a := smul_comm g₀ c a

private theorem genOp_pow_apply (g₀ : P) (k : ℕ) (v : V) :
    ((genOp g₀ : Module.End (ZMod 2) V) ^ k) v = g₀ ^ k • v := by
  induction k generalizing v with
  | zero =>
    rw [pow_zero, pow_zero, one_smul]
    rfl
  | succ k IH =>
    rw [pow_succ, pow_succ, mul_smul]
    exact IH (g₀ • v)

/-- `genOp` turns a power of the group element into a power of the operator. -/
private theorem genOp_pow (g₀ : P) (k : ℕ) :
    (genOp (g₀ ^ k) : Module.End (ZMod 2) V) = (genOp g₀) ^ k := by
  apply LinearMap.ext
  intro v
  rw [genOp_pow_apply]
  rfl

/-- `ν := γ + 1`, the augmentation-style nilpotent attached to the generator action. -/
private def nuOp (g₀ : P) : Module.End (ZMod 2) V := genOp g₀ + 1

/-- The endomorphism ring of a `ZMod 2`-module has `2 = 0`. -/
private theorem end_two_eq_zero {M : Type} [AddCommGroup M] [Module (ZMod 2) M] :
    (2 : Module.End (ZMod 2) M) = 0 := by
  have h2 : (2 : Module.End (ZMod 2) M) = 1 + 1 := one_add_one_eq_two.symm
  ext m
  rw [h2]
  show m + m = (0 : Module.End (ZMod 2) M) m
  rw [← two_smul (ZMod 2) m, (by decide : (2 : ZMod 2) = 0), zero_smul]
  rfl

section WithFintype

variable [Fintype P]

/-- Reindex a sum over a cyclic group by powers of a generator. -/
private theorem sum_eq_sum_range_pow (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {M : Type} [AddCommMonoid M] (f : P → M) :
    ∑ x : P, f x = ∑ k ∈ Finset.range (orderOf g₀), f (g₀ ^ k) := by
  calc ∑ x : P, f x
      = ∑ y : ↥(Subgroup.zpowers g₀), f ↑y :=
        (Fintype.sum_equiv (Equiv.subtypeUnivEquiv hg) _ _ (fun y => rfl)).symm
    _ = ∑ k : Fin (orderOf g₀), f ↑(finEquivZPowers (isOfFinOrder_of_finite g₀) k) :=
        (Fintype.sum_equiv (finEquivZPowers (isOfFinOrder_of_finite g₀)) _ _
          (fun k => rfl)).symm
    _ = ∑ k : Fin (orderOf g₀), f (g₀ ^ (k : ℕ)) := by
        refine Fintype.sum_congr _ _ fun k => ?_
        rw [finEquivZPowers_apply]
    _ = ∑ k ∈ Finset.range (orderOf g₀), f (g₀ ^ k) :=
        Fin.sum_univ_eq_sum_range (fun k => f (g₀ ^ k)) (orderOf g₀)

private theorem orderOf_generator (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) : orderOf g₀ = 2 ^ s := by
  rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hs]

/-- `ν^(2^s) = 0`: the generator action is unipotent of index dividing `|P| = 2^s`. -/
private theorem nuOp_pow_card_eq_zero (g₀ : P) {s : ℕ} (hs : Fintype.card P = 2 ^ s) :
    (nuOp g₀ : Module.End (ZMod 2) V) ^ 2 ^ s = 0 := by
  have hγ : (genOp g₀ : Module.End (ZMod 2) V) ^ 2 ^ s = 1 := by
    apply LinearMap.ext
    intro v
    rw [genOp_pow_apply, ← hs, pow_card_eq_one, one_smul]
    rfl
  show (genOp g₀ + 1 : Module.End (ZMod 2) V) ^ 2 ^ s = 0
  rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero (Commute.one_right _) s, hγ, one_pow,
    one_add_one_eq_two, end_two_eq_zero]

/-- The group sum acts as `ν^(2^s − 1)` (the norm element in characteristic 2). -/
private theorem sum_smul_eq_nuOp_pow (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) (v : V) :
    ∑ x : P, x • v = ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v := by
  calc ∑ x : P, x • v
      = ∑ k ∈ Finset.range (orderOf g₀), g₀ ^ k • v :=
        sum_eq_sum_range_pow g₀ hg (fun x => x • v)
    _ = ∑ k ∈ Finset.range (2 ^ s), ((genOp g₀ : Module.End (ZMod 2) V) ^ k) v := by
        rw [orderOf_generator g₀ hg hs]
        exact Finset.sum_congr rfl fun k _ => (genOp_pow_apply g₀ k v).symm
    _ = (∑ k ∈ Finset.range (2 ^ s), (genOp g₀ : Module.End (ZMod 2) V) ^ k) v :=
        (LinearMap.sum_apply _ _ v).symm
    _ = ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v := by
        rw [geom_sum_two_pow_of_two_eq_zero end_two_eq_zero]
        rfl

/-- **Split off one free block.**  If `ν^(2^s−1) v₀ ≠ 0`, the sub-representation generated by
`v₀` is a free rank-1 block that splits off equivariantly: `V ≃+ (P → ZMod 2) × W` with a
`P`-stable complement `W` and both components equivariant.  The retraction is
`ρ := T⁻¹ ∘ φ` where `φ w := (x ↦ λ(x⁻¹ • w))` for a functional `λ` with
`λ(ν^(2^s−1) v₀) = 1`, `j F := ∑_x F x • x•v₀` is the orbit map, and `T := φ ∘ j` is
convolution by an augmentation-1 element — `T = 1 + (μ+1)·B` with `μ` the right-translation
by the generator, `(μ+1)^(2^s) = 0`, so `T` has an **explicit geometric-series inverse**
(no finiteness of `V` needed). -/
private theorem split_off_block (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    {s : ℕ} (hs : Fintype.card P = 2 ^ s) (v₀ : V)
    (hv₀ : ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ ≠ 0) :
    ∃ (W : Submodule (ZMod 2) V) (ψ : V ≃+ ((P → ZMod 2) × ↥W)),
      (∀ (p : P) (v : V), v ∈ W → p • v ∈ W) ∧
      (∀ (p : P) (v : V) (x : P), (ψ (p • v)).1 x = (ψ v).1 (p⁻¹ * x)) ∧
      (∀ (p : P) (v : V), ((ψ (p • v)).2 : V) = p • ((ψ v).2 : V)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, two_zmod_two_eq_zero, zero_smul]
  have hR2 : ∀ F : P → ZMod 2, F + F = 0 := fun F => by
    funext x
    exact CharTwo.add_self_eq_zero (F x)
  -- the functional detecting the deepest layer of the block
  set x₀ : V := ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ with hx₀def
  obtain ⟨pc, hpc⟩ := Submodule.exists_isCompl (Submodule.span (ZMod 2) {x₀})
  obtain ⟨lam, hlam⟩ : ∃ lam : V →ₗ[ZMod 2] ZMod 2, lam x₀ = 1 := by
    refine ⟨(LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x₀ hv₀).symm.toLinearMap.comp
      ((Submodule.span (ZMod 2) {x₀}).projectionOnto pc hpc), ?_⟩
    have h1 : ((Submodule.span (ZMod 2) {x₀}).projectionOnto pc hpc) x₀
        = ⟨x₀, Submodule.mem_span_singleton_self x₀⟩ :=
      Submodule.projectionOnto_apply_left hpc ⟨x₀, Submodule.mem_span_singleton_self x₀⟩
    show (LinearEquiv.toSpanNonzeroSingleton (ZMod 2) V x₀ hv₀).symm
        (((Submodule.span (ZMod 2) {x₀}).projectionOnto pc hpc) x₀) = 1
    rw [h1]
    refine (LinearEquiv.symm_apply_eq _).mpr ?_
    apply Subtype.ext
    rw [LinearEquiv.toSpanNonzeroSingleton_apply]
    exact (one_smul _ _).symm
  -- the orbit map and the coefficient map
  set jmap : (P → ZMod 2) →ₗ[ZMod 2] V :=
    { toFun := fun F => ∑ x : P, F x • (x • v₀)
      map_add' := fun F F' => by
        show ∑ x : P, (F x + F' x) • (x • v₀) = _
        rw [Finset.sum_congr rfl fun x _ => add_smul (F x) (F' x) (x • v₀),
          Finset.sum_add_distrib]
      map_smul' := fun c F => by
        show ∑ x : P, (c * F x) • (x • v₀) = c • ∑ x : P, F x • (x • v₀)
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun x _ => mul_smul c (F x) (x • v₀) } with hjdef
  set phim : V →ₗ[ZMod 2] (P → ZMod 2) :=
    { toFun := fun w x => lam (x⁻¹ • w)
      map_add' := fun a b => by
        funext x
        show lam (x⁻¹ • (a + b)) = lam (x⁻¹ • a) + lam (x⁻¹ • b)
        rw [smul_add, map_add]
      map_smul' := fun c a => by
        funext x
        show lam (x⁻¹ • c • a) = c * lam (x⁻¹ • a)
        rw [smul_comm, map_smul, smul_eq_mul] } with hphidef
  -- equivariance of both maps
  have hjeq : ∀ (p : P) (F : P → ZMod 2), jmap (fun x => F (p⁻¹ * x)) = p • jmap F := by
    intro p F
    show ∑ x : P, F (p⁻¹ * x) • (x • v₀) = p • ∑ x : P, F x • (x • v₀)
    rw [Finset.smul_sum]
    calc ∑ x : P, F (p⁻¹ * x) • (x • v₀)
        = ∑ x : P, F (p⁻¹ * (p * x)) • ((p * x) • v₀) :=
          (Equiv.sum_comp (Equiv.mulLeft p) (fun x : P => F (p⁻¹ * x) • (x • v₀))).symm
      _ = ∑ x : P, p • (F x • (x • v₀)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [inv_mul_cancel_left, mul_smul]
          exact (smul_comm p (F x) (x • v₀)).symm
  have hphieq : ∀ (p : P) (w : V) (x : P), phim (p • w) x = phim w (p⁻¹ * x) := by
    intro p w x
    show lam (x⁻¹ • p • w) = lam ((p⁻¹ * x)⁻¹ • w)
    rw [← mul_smul, mul_inv_rev, inv_inv]
  -- the right-translation operator and its unipotency
  set mu : Module.End (ZMod 2) (P → ZMod 2) :=
    { toFun := fun F x => F (x * g₀)
      map_add' := fun F F' => rfl
      map_smul' := fun c F => rfl } with hmudef
  have hmu_pow : ∀ (k : ℕ) (F : P → ZMod 2) (x : P), (mu ^ k) F x = F (x * g₀ ^ k) := by
    intro k
    induction k with
    | zero =>
      intro F x
      rw [pow_zero, pow_zero, mul_one]
      rfl
    | succ k IH =>
      intro F x
      rw [pow_succ, pow_succ, ← mul_assoc]
      exact IH (mu F) x
  have hmu_card : mu ^ 2 ^ s = 1 := by
    apply LinearMap.ext
    intro F
    funext x
    rw [hmu_pow, ← hs, pow_card_eq_one, mul_one]
    rfl
  have hnumu : (mu + 1) ^ 2 ^ s = 0 := by
    rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero (Commute.one_right mu) s, hmu_card,
      one_pow, one_add_one_eq_two, end_two_eq_zero]
  -- the convolution `T = φ ∘ j` and its expansion in powers of `μ`
  set T : Module.End (ZMod 2) (P → ZMod 2) := phim ∘ₗ jmap with hTdef
  have hTeq : ∀ (p : P) (F : P → ZMod 2),
      T (fun x => F (p⁻¹ * x)) = fun x => (T F) (p⁻¹ * x) := by
    intro p F
    show phim (jmap fun x => F (p⁻¹ * x)) = fun x => phim (jmap F) (p⁻¹ * x)
    rw [hjeq]
    funext x
    exact hphieq p (jmap F) x
  have hTform : T = ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k := by
    apply LinearMap.ext
    intro F
    funext x
    have hL : lam (x⁻¹ • jmap F) = ∑ y : P, F y * lam ((x⁻¹ * y) • v₀) := by
      show lam (x⁻¹ • ∑ y : P, F y • (y • v₀)) = _
      rw [Finset.smul_sum, map_sum]
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [smul_comm x⁻¹ (F y), map_smul, smul_eq_mul, ← mul_smul]
    have hre : ∑ y : P, F y * lam ((x⁻¹ * y) • v₀)
        = ∑ z : P, F (x * z) * lam (z • v₀) := by
      refine ((Equiv.sum_comp (Equiv.mulLeft x)
        (fun y : P => F y * lam ((x⁻¹ * y) • v₀))).symm).trans ?_
      refine Fintype.sum_congr _ _ fun z => ?_
      show F (x * z) * lam ((x⁻¹ * (x * z)) • v₀) = F (x * z) * lam (z • v₀)
      rw [inv_mul_cancel_left]
    have hpw : ∑ z : P, F (x * z) * lam (z • v₀)
        = ∑ k ∈ Finset.range (2 ^ s), F (x * g₀ ^ k) * lam (g₀ ^ k • v₀) := by
      rw [← orderOf_generator g₀ hg hs]
      exact sum_eq_sum_range_pow g₀ hg (fun z => F (x * z) * lam (z • v₀))
    have hR : (∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k) F x
        = ∑ k ∈ Finset.range (2 ^ s), F (x * g₀ ^ k) * lam (g₀ ^ k • v₀) := by
      rw [LinearMap.sum_apply, Finset.sum_apply]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [LinearMap.smul_apply, Pi.smul_apply, hmu_pow, smul_eq_mul, mul_comm]
    show lam (x⁻¹ • jmap F) = (∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k) F x
    rw [hL, hre, hpw, hR]
  -- the augmentation of the convolution kernel is 1
  have haug : ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) = 1 := by
    have h1 : ∑ x : P, lam (x • v₀) = ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) := by
      rw [← orderOf_generator g₀ hg hs]
      exact sum_eq_sum_range_pow g₀ hg (fun x => lam (x • v₀))
    rw [← h1, ← map_sum lam (fun x => x • v₀) Finset.univ,
      sum_smul_eq_nuOp_pow g₀ hg hs v₀]
    exact hlam
  -- decompose each `μ^k = 1 + (μ+1)·D_k`
  have hD : ∀ k : ℕ, ∃ D : Module.End (ZMod 2) (P → ZMod 2),
      mu ^ k = 1 + (mu + 1) * D ∧ Commute (mu + 1) D := by
    intro k
    induction k with
    | zero => exact ⟨0, by rw [pow_zero, mul_zero, add_zero], Commute.zero_right _⟩
    | succ k IH =>
      obtain ⟨D, hDeq, hDcomm⟩ := IH
      have hmu1 : mu = 1 + (mu + 1) := by
        rw [add_comm 1 (mu + 1), add_assoc, one_add_one_eq_two, end_two_eq_zero, add_zero]
      refine ⟨1 + D * mu, ?_, ?_⟩
      · rw [pow_succ, hDeq, add_mul, one_mul, mul_assoc, mul_add, mul_one, ← add_assoc,
          ← hmu1]
      · exact (Commute.one_right _).add_right
          (hDcomm.mul_right ((Commute.refl mu).add_left (Commute.one_left mu)))
  choose Dk hDk hDkcomm using hD
  set B : Module.End (ZMod 2) (P → ZMod 2) :=
    ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • Dk k with hBdef
  have hTB : T = 1 + (mu + 1) * B := by
    rw [hTform]
    calc ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • mu ^ k
        = ∑ k ∈ Finset.range (2 ^ s),
            (lam (g₀ ^ k • v₀) • (1 : Module.End (ZMod 2) (P → ZMod 2))
              + lam (g₀ ^ k • v₀) • ((mu + 1) * Dk k)) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [hDk k, smul_add]
      _ = (∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀))
            • (1 : Module.End (ZMod 2) (P → ZMod 2))
            + ∑ k ∈ Finset.range (2 ^ s), lam (g₀ ^ k • v₀) • ((mu + 1) * Dk k) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_smul]
      _ = 1 + (mu + 1) * B := by
          rw [haug, one_smul, hBdef, Finset.mul_sum]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [mul_smul_comm]
  -- the explicit inverse of `T`
  have hνB : Commute (mu + 1) B := by
    rw [hBdef]
    exact Commute.sum_right _ _ _ fun k _ => (hDkcomm k).smul_right _
  have hnilB : ((mu + 1) * B) ^ 2 ^ s = 0 := by
    rw [hνB.mul_pow, hnumu, zero_mul]
  set Tinv : Module.End (ZMod 2) (P → ZMod 2) :=
    ∑ i ∈ Finset.range (2 ^ s), ((mu + 1) * B) ^ i with hTinvdef
  have hTT1 : T * Tinv = 1 := by
    rw [hTB, add_comm 1 ((mu + 1) * B), hTinvdef]
    exact (geom_inverse_of_nilpotent end_two_eq_zero hnilB).1
  have hTT2 : Tinv * T = 1 := by
    rw [hTB, add_comm 1 ((mu + 1) * B), hTinvdef]
    exact (geom_inverse_of_nilpotent end_two_eq_zero hnilB).2
  -- the retraction and its equivariance
  set rho : V →ₗ[ZMod 2] (P → ZMod 2) := Tinv ∘ₗ phim with hrhodef
  have hrhoj : ∀ F : P → ZMod 2, rho (jmap F) = F := by
    intro F
    have h2 : (Tinv * T) F = (1 : Module.End (ZMod 2) (P → ZMod 2)) F := by rw [hTT2]
    exact h2
  have hTrho : ∀ u : V, T (rho u) = phim u := by
    intro u
    have h2 : (T * Tinv) (phim u) = (1 : Module.End (ZMod 2) (P → ZMod 2)) (phim u) := by
      rw [hTT1]
    exact h2
  have hTinj : Function.Injective T := by
    intro a b hab
    have ha : (Tinv * T) a = (Tinv * T) b := by
      show Tinv (T a) = Tinv (T b)
      rw [hab]
    rwa [hTT2] at ha
  have hrhoeq : ∀ (p : P) (w : V), rho (p • w) = fun x => rho w (p⁻¹ * x) := by
    intro p w
    apply hTinj
    rw [hTrho, hTeq p (rho w), hTrho]
    funext x
    exact hphieq p w x
  -- the complement and the splitting
  have hker_mem : ∀ v : V, v + jmap (rho v) ∈ LinearMap.ker rho := by
    intro v
    rw [LinearMap.mem_ker, map_add, hrhoj]
    exact hR2 (rho v)
  refine ⟨LinearMap.ker rho,
    { toFun := fun v => (rho v, ⟨v + jmap (rho v), hker_mem v⟩)
      invFun := fun a => jmap a.1 + ↑a.2
      left_inv := fun v => by
        show jmap (rho v) + (v + jmap (rho v)) = v
        rw [add_left_comm, hV2, add_zero]
      right_inv := fun a => by
        refine Prod.ext ?_ ?_
        · show rho (jmap a.1 + ↑a.2) = a.1
          rw [map_add, hrhoj, LinearMap.mem_ker.mp a.2.2, add_zero]
        · apply Subtype.ext
          show (jmap a.1 + ↑a.2) + jmap (rho (jmap a.1 + ↑a.2)) = (↑a.2 : V)
          rw [map_add, hrhoj, LinearMap.mem_ker.mp a.2.2, add_zero, add_right_comm, hV2,
            zero_add]
      map_add' := fun v v' => by
        refine Prod.ext ?_ ?_
        · exact map_add rho v v'
        · apply Subtype.ext
          show (v + v') + jmap (rho (v + v'))
              = (v + jmap (rho v)) + (v' + jmap (rho v'))
          rw [map_add, map_add]
          exact add_add_add_comm v v' (jmap (rho v)) (jmap (rho v')) },
    ?_, ?_, ?_⟩
  · intro p v hv
    rw [LinearMap.mem_ker] at hv ⊢
    rw [hrhoeq p v, hv]
    funext x
    rfl
  · intro p v x
    exact congrFun (hrhoeq p v) x
  · intro p v
    show (p • v) + jmap (rho (p • v)) = p • (v + jmap (rho v))
    rw [smul_add, hrhoeq p v, hjeq p (rho v)]

end WithFintype

/-- Kernel filtration bound: `#ker(f^k) ≤ #ker(f)^k`.  Each layer of the filtration
`ker f ⊆ ker f² ⊆ …` maps into the previous one with kernel inside `ker f`. -/
private theorem card_ker_pow_le {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Nat.card ↥(LinearMap.ker (f ^ k)) ≤ Nat.card ↥(LinearMap.ker f) ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    have h : LinearMap.ker (1 : Module.End (ZMod 2) V) = ⊥ := LinearMap.ker_id
    rw [h]
    exact le_of_eq Nat.card_unique
  | succ k IH =>
    have hmap : ∀ x ∈ LinearMap.ker (f ^ (k + 1)), f x ∈ LinearMap.ker (f ^ k) := by
      intro x hx
      rw [LinearMap.mem_ker] at hx ⊢
      calc (f ^ k) (f x) = (f ^ (k + 1)) x := by
            rw [pow_succ]
            rfl
        _ = 0 := hx
    set g := f.restrict hmap with hgdef
    have hdom : Nat.card ↥(LinearMap.ker (f ^ (k + 1)))
        = Nat.card (↥(LinearMap.ker (f ^ (k + 1))) ⧸ g.toAddMonoidHom.ker)
          * Nat.card ↥g.toAddMonoidHom.ker :=
      AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
    have hquot : Nat.card (↥(LinearMap.ker (f ^ (k + 1))) ⧸ g.toAddMonoidHom.ker)
        = Nat.card ↥g.toAddMonoidHom.range :=
      Nat.card_congr (QuotientAddGroup.quotientKerEquivRange g.toAddMonoidHom).toEquiv
    have hrange : Nat.card ↥g.toAddMonoidHom.range ≤ Nat.card ↥(LinearMap.ker (f ^ k)) :=
      Nat.card_le_card_of_injective
        (fun y => (y : ↥(LinearMap.ker (f ^ k)))) (fun y y' hyy => Subtype.ext hyy)
    have hkerg : Nat.card ↥g.toAddMonoidHom.ker ≤ Nat.card ↥(LinearMap.ker f) := by
      refine Nat.card_le_card_of_injective
        (fun y => (⟨((y : ↥(LinearMap.ker (f ^ (k + 1)))) : V), ?_⟩ : ↥(LinearMap.ker f)))
        ?_
      · rw [LinearMap.mem_ker]
        have h0 : g (y : ↥(LinearMap.ker (f ^ (k + 1)))) = 0 :=
          AddMonoidHom.mem_ker.mp y.2
        have h1 : ((g (y : ↥(LinearMap.ker (f ^ (k + 1))))) : V)
            = f ((y : ↥(LinearMap.ker (f ^ (k + 1)))) : V) := rfl
        rw [h0] at h1
        exact h1.symm.trans rfl
      · intro y y' hyy
        have h2 := congrArg (Subtype.val : ↥(LinearMap.ker f) → V) hyy
        apply Subtype.ext
        apply Subtype.ext
        exact h2
    calc Nat.card ↥(LinearMap.ker (f ^ (k + 1)))
        = Nat.card ↥g.toAddMonoidHom.range * Nat.card ↥g.toAddMonoidHom.ker := by
          rw [hdom, hquot]
      _ ≤ Nat.card ↥(LinearMap.ker (f ^ k)) * Nat.card ↥(LinearMap.ker f) :=
          Nat.mul_le_mul hrange hkerg
      _ ≤ Nat.card ↥(LinearMap.ker f) ^ k * Nat.card ↥(LinearMap.ker f) :=
          Nat.mul_le_mul_right _ IH
      _ = Nat.card ↥(LinearMap.ker f) ^ (k + 1) := (pow_succ _ _).symm

/-- **One Jordan-increment identity**: `dim ker f^{k+1} = dim ker f^k + dim(im f^k ⊓ ker f)`.
The map `f^k : ker f^{k+1} → im f^k ⊓ ker f` is onto with kernel `ker f^k`; rank-nullity. -/
theorem finrank_ker_pow_succ {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1)))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
        + Module.finrank (ZMod 2) ↥(LinearMap.range (f ^ k) ⊓ LinearMap.ker f) := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hfpow : ∀ w : V, f ((f ^ k) w) = (f ^ (k + 1)) w := fun w => by rw [pow_succ']; rfl
  have hmono : LinearMap.ker (f ^ k) ≤ LinearMap.ker (f ^ (k + 1)) := by
    intro x hx; rw [LinearMap.mem_ker] at hx ⊢; rw [← hfpow x, hx, map_zero]
  set g : ↥(LinearMap.ker (f ^ (k + 1))) →ₗ[ZMod 2] V :=
    (f ^ k).comp (LinearMap.ker (f ^ (k + 1))).subtype with hg
  have hgapp : ∀ x : ↥(LinearMap.ker (f ^ (k + 1))), g x = (f ^ k) (x : V) := fun _ => rfl
  have hrange : LinearMap.range g = LinearMap.range (f ^ k) ⊓ LinearMap.ker f := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      refine Submodule.mem_inf.mpr ⟨⟨x, rfl⟩, ?_⟩
      rw [LinearMap.mem_ker, hgapp, hfpow]; exact x.2
    · rintro y hy
      obtain ⟨⟨z, hz⟩, hy2⟩ := Submodule.mem_inf.mp hy
      rw [LinearMap.mem_ker] at hy2
      refine ⟨⟨z, ?_⟩, ?_⟩
      · rw [LinearMap.mem_ker, ← hfpow z, hz]; exact hy2
      · rw [hgapp]; exact hz
  have hker : LinearMap.ker g = Submodule.comap (LinearMap.ker (f ^ (k + 1))).subtype
      (LinearMap.ker (f ^ k)) := by
    ext x
    rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.subtype_apply, LinearMap.mem_ker, hgapp]
  have hrn := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange, hker] at hrn
  have hcomap : Module.finrank (ZMod 2)
      ↥(Submodule.comap (LinearMap.ker (f ^ (k + 1))).subtype (LinearMap.ker (f ^ k)))
      = Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k)) :=
    LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe hmono)
  rw [hcomap] at hrn
  omega

/-- **Concavity of the Jordan-increment sequence**: `k ↦ dim ker f^k` is concave, i.e.
`dim ker f^{k+2} + dim ker f^k ≤ 2·dim ker f^{k+1}`.  The increment `dim(im f^k ⊓ ker f)` is
non-increasing (`im f^{k+1} ≤ im f^k`, intersect with `ker f`, `finrank_mono`).  This is the
linear-algebra heart of the elementary-abelian reduction (see the section docstring). -/
theorem finrank_ker_pow_concave {V : Type} [AddCommGroup V] [Finite V] [Module (ZMod 2) V]
    (f : Module.End (ZMod 2) V) (k : ℕ) :
    Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 2)))
        + Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
      ≤ 2 * Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1))) := by
  have hrmono : LinearMap.range (f ^ (k + 1)) ≤ LinearMap.range (f ^ k) := by
    rintro _ ⟨w, rfl⟩; exact ⟨f w, by rw [pow_succ]; rfl⟩
  have hdmono := Submodule.finrank_mono
    (R := ZMod 2) (M := V) (inf_le_inf_right (LinearMap.ker f) hrmono)
  have hA1 := finrank_ker_pow_succ f k
  have hA2 := finrank_ker_pow_succ f (k + 1)
  rw [show k + 1 + 1 = k + 2 from rfl] at hA2
  omega

/-- The fixed points of the action are exactly the kernel of `ν = γ + 1` (as a count). -/
private theorem card_fixedPoints_eq_card_ker_nuOp (g₀ : P)
    (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀) :
    Nat.card {v : V // ∀ p : P, p • v = v}
      = Nat.card ↥(LinearMap.ker (nuOp g₀ : Module.End (ZMod 2) V)) := by
  have hV2 : ∀ v : V, v + v = 0 := fun v => by
    rw [← two_smul (ZMod 2) v, two_zmod_two_eq_zero, zero_smul]
  refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
  rw [LinearMap.mem_ker]
  constructor
  · intro hv
    show g₀ • v + v = 0
    rw [hv g₀]
    exact hV2 v
  · intro h
    have h' : g₀ • v + v = 0 := h
    have hfix : g₀ • v = v := by
      calc g₀ • v = g₀ • v + (v + v) := by rw [hV2, add_zero]
        _ = (g₀ • v + v) + v := (add_assoc _ _ _).symm
        _ = 0 + v := by rw [h']
        _ = v := zero_add v
    intro p
    have hg₀mem : g₀ ∈ MulAction.stabilizer P v := MulAction.mem_stabilizer_iff.mpr hfix
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg p)
    rw [← hn]
    exact MulAction.mem_stabilizer_iff.mp (zpow_mem hg₀mem n)

/-! ### Numeric core of the elementary-abelian reduction

For a concave monotone sequence `b` with `b 0 = 0` (the Jordan-kernel dimensions
`b k = dim ker ν^k`), the "midpoint is free" hypothesis `2·b m = b(2m)` forces **every**
increment to equal the first, hence `b(2m) = 2m·b 1`.  Concavity alone gives the reverse
`b(2m) ≤ 2·b m` (increments non-increasing), so a future rep-theory leaf only needs the
inequality `2·b m ≤ b(2m)` (the involution acts freely enough), not the full equality. -/

/-- Concavity's automatic half: `b(2m) ≤ 2·b m` for a concave monotone sequence with
`b 0 = 0` (the increments `e k = b(k+1) − b k` are non-increasing, so the second block of
`m` increments is dominated by the first). -/
private theorem seq_double_le (b : ℕ → ℕ) (hb0 : b 0 = 0) (hmono : ∀ k, b k ≤ b (k + 1))
    (hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1)) (m : ℕ) : b (2 * m) ≤ 2 * b m := by
  set e : ℕ → ℕ := fun k => b (k + 1) - b k with he
  have he_add : ∀ k, b (k + 1) = b k + e k := fun k => (Nat.add_sub_cancel' (hmono k)).symm
  have he_anti_succ : ∀ k, e (k + 1) ≤ e k := by
    intro k
    have h1 := he_add k
    have h2 := he_add (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h2
    have h3 := hconc k
    omega
  have he_anti : Antitone e := antitone_nat_of_succ_le he_anti_succ
  have hsum : ∀ n, b n = ∑ k ∈ Finset.range n, e k := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, hb0]
    | succ n IH => rw [Finset.sum_range_succ, ← IH, he_add n]
  have hsplit : b (2 * m) = b m + ∑ j ∈ Finset.range m, e (m + j) := by
    rw [show 2 * m = m + m from by ring, hsum (m + m), hsum m, Finset.sum_range_add]
  have hle2 : ∑ j ∈ Finset.range m, e (m + j) ≤ ∑ j ∈ Finset.range m, e j :=
    Finset.sum_le_sum (fun j _ => he_anti (by omega))
  rw [hsplit, hsum m, two_mul]
  exact Nat.add_le_add_left hle2 _

/-- Numeric core of the reduction: a concave monotone sequence with `b 0 = 0` and
`2·b m = b(2m)` (`m ≥ 1`) satisfies `2m·b 1 ≤ b(2m)` — indeed with equality, all increments
being forced equal to `b 1`.  (Two equal `m`-term sums with pairwise-dominating terms are
termwise equal; antitone squeeze then flattens the first block.) -/
private theorem seq_first_increment_le (b : ℕ → ℕ) (hb0 : b 0 = 0)
    (hmono : ∀ k, b k ≤ b (k + 1)) (hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1))
    (m : ℕ) (hm : 1 ≤ m) (hhalf : 2 * b m = b (2 * m)) : 2 * m * b 1 ≤ b (2 * m) := by
  set e : ℕ → ℕ := fun k => b (k + 1) - b k with he
  have he_add : ∀ k, b (k + 1) = b k + e k := fun k => (Nat.add_sub_cancel' (hmono k)).symm
  have he_anti_succ : ∀ k, e (k + 1) ≤ e k := by
    intro k
    have h1 := he_add k
    have h2 := he_add (k + 1)
    rw [show k + 1 + 1 = k + 2 from rfl] at h2
    have h3 := hconc k
    omega
  have he_anti : Antitone e := antitone_nat_of_succ_le he_anti_succ
  have hsum : ∀ n, b n = ∑ k ∈ Finset.range n, e k := by
    intro n
    induction n with
    | zero => rw [Finset.range_zero, Finset.sum_empty, hb0]
    | succ n IH => rw [Finset.sum_range_succ, ← IH, he_add n]
  have he0 : e 0 = b 1 := by show b 1 - b 0 = b 1; omega
  have hsplit : b (2 * m) = b m + ∑ j ∈ Finset.range m, e (m + j) := by
    rw [show 2 * m = m + m from by ring, hsum (m + m), hsum m, Finset.sum_range_add]
  have heq_sums : ∑ j ∈ Finset.range m, e j = ∑ j ∈ Finset.range m, e (m + j) := by
    have h := hsplit
    rw [← hhalf, two_mul] at h
    have hc := Nat.add_left_cancel h
    rw [hsum m] at hc
    exact hc
  have hle : ∀ j ∈ Finset.range m, e (m + j) ≤ e j := fun j _ => he_anti (by omega)
  have hterm := (Finset.sum_eq_sum_iff_of_le hle).mp heq_sums.symm
  have he0m : e m = e 0 := by have := hterm 0 (Finset.mem_range.mpr hm); simpa using this
  have hconst : ∀ j, j < m → e j = e 0 := by
    intro j hj
    have h1 : e j ≤ e 0 := he_anti (Nat.zero_le j)
    have h2 : e m ≤ e j := he_anti (by omega)
    omega
  have hbm_eq : b m = m * e 0 := by
    rw [hsum m, Finset.sum_congr rfl (fun j hj => hconst j (Finset.mem_range.mp hj)),
      Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hfinal : b (2 * m) = 2 * m * b 1 := by rw [← hhalf, hbm_eq, he0]; ring
  exact hfinal.ge

/-- The inductive engine behind the counting criterion: peel off one free block at a time.
Ordinary induction on a bound `n` for `#V` suffices, since the complement has strictly
smaller cardinality. -/
private theorem free_of_card_aux (P : Type) [Group P] [Finite P]
    (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀) (s : ℕ)
    (hs : Nat.card P = 2 ^ s) :
    ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Finite V] [DistribMulAction P V],
      Nat.card V ≤ n → (∀ v : V, v + v = 0) →
      Nat.card {v : V // ∀ p : P, p • v = v} ^ 2 ^ s ≤ Nat.card V →
      ∃ (r : ℕ) (φ : V ≃+ (Fin r → P → ZMod 2)),
        ∀ (p : P) (v : V) (m : Fin r) (x : P), φ (p • v) m x = φ v m (p⁻¹ * x) := by
  intro n
  induction n with
  | zero =>
    intro V _ _ _ hle _ _
    haveI : Nonempty V := ⟨0⟩
    have := Nat.card_pos (α := V)
    omega
  | succ n IH =>
    intro V _ _ _ hle hV2 hcount
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
      rw [two_nsmul]
      exact hV2 v)
    letI : SMulCommClass P (ZMod 2) V := ⟨fun p c v => by
      rcases zmod2_cases c with hc | hc <;> rw [hc]
      · rw [zero_smul, zero_smul, smul_zero]
      · rw [one_smul, one_smul]⟩
    haveI : Fintype P := Fintype.ofFinite P
    have hsF : Fintype.card P = 2 ^ s := by
      rw [← Nat.card_eq_fintype_card]
      exact hs
    have hfixker := card_fixedPoints_eq_card_ker_nuOp (V := V) g₀ hg
    by_cases hex : ∃ v₀ : V, ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ ≠ 0
    · -- a full-depth vector exists: split off one free block and recurse
      obtain ⟨v₀, hv₀⟩ := hex
      obtain ⟨W, ψ, hWstable, hψ1, hψ2⟩ := split_off_block g₀ hg hsF v₀ hv₀
      letI actW : DistribMulAction P ↥W :=
        { smul := fun p w => ⟨p • (w : V), hWstable p (w : V) w.2⟩
          one_smul := fun w => Subtype.ext (one_smul P (w : V))
          mul_smul := fun p q w => Subtype.ext (mul_smul p q (w : V))
          smul_zero := fun p => Subtype.ext (smul_zero p)
          smul_add := fun p w w' => Subtype.ext (smul_add p (w : V) (w' : V)) }
      have hcardR : Nat.card (P → ZMod 2) = 2 ^ 2 ^ s := by
        rw [Nat.card_fun, Nat.card_zmod, hs]
      have hcardV : Nat.card V = 2 ^ 2 ^ s * Nat.card ↥W := by
        rw [Nat.card_congr ψ.toEquiv, Nat.card_prod, hcardR]
      haveI : Nonempty ↥W := ⟨0⟩
      have hWpos : 0 < Nat.card ↥W := Nat.card_pos
      have h2pow : (2 : ℕ) ≤ 2 ^ 2 ^ s := by
        have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
        calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
          _ ≤ 2 ^ 2 ^ s := Nat.pow_le_pow_right (by omega) h1
      have hWle : Nat.card ↥W ≤ n := by
        have h3 : 2 * Nat.card ↥W ≤ 2 ^ 2 ^ s * Nat.card ↥W :=
          Nat.mul_le_mul_right _ h2pow
        omega
      have hV2W : ∀ w : ↥W, w + w = 0 := fun w => Subtype.ext (hV2 (w : V))
      -- fixed points inject: `ZMod 2 × Fix(W) ↪ Fix(V)` via `ψ⁻¹(const, ·)`
      have hfixsymm : ∀ (cc : ZMod 2) (w : {w : ↥W // ∀ p : P, p • w = w}) (p : P),
          p • ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))
            = ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W)) := by
        intro cc w p
        apply ψ.injective
        refine Prod.ext ?_ ?_
        · funext x
          rw [hψ1 p (ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))) x,
            AddEquiv.apply_symm_apply]
        · apply Subtype.ext
          rw [hψ2 p (ψ.symm ((fun _ => cc : P → ZMod 2), (w : ↥W))),
            AddEquiv.apply_symm_apply]
          exact congrArg (Subtype.val : ↥W → V) (w.2 p)
      have hfixinj : 2 * Nat.card {w : ↥W // ∀ p : P, p • w = w}
          ≤ Nat.card {v : V // ∀ p : P, p • v = v} := by
        have hcard2 : Nat.card (ZMod 2 × {w : ↥W // ∀ p : P, p • w = w})
            = 2 * Nat.card {w : ↥W // ∀ p : P, p • w = w} := by
          rw [Nat.card_prod, Nat.card_zmod]
        rw [← hcard2]
        refine Nat.card_le_card_of_injective
          (fun cw => ⟨ψ.symm ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W)),
            fun p => hfixsymm cw.1 cw.2 p⟩) ?_
        intro cw cw' hcc
        have h1 : ψ.symm ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W))
            = ψ.symm ((fun _ => cw'.1 : P → ZMod 2), (cw'.2 : ↥W)) :=
          congrArg (Subtype.val : {v : V // ∀ p : P, p • v = v} → V) hcc
        have h2 : ((fun _ => cw.1 : P → ZMod 2), (cw.2 : ↥W))
            = ((fun _ => cw'.1 : P → ZMod 2), (cw'.2 : ↥W)) := ψ.symm.injective h1
        refine Prod.ext ?_ ?_
        · exact congrFun (congrArg Prod.fst h2) (1 : P)
        · exact Subtype.ext (congrArg Prod.snd h2)
      have hcountW : Nat.card {w : ↥W // ∀ p : P, p • w = w} ^ 2 ^ s ≤ Nat.card ↥W := by
        have h4 : (2 * Nat.card {w : ↥W // ∀ p : P, p • w = w}) ^ 2 ^ s ≤ Nat.card V :=
          le_trans (Nat.pow_le_pow_left hfixinj _) hcount
        rw [mul_pow, hcardV] at h4
        exact Nat.le_of_mul_le_mul_left h4 (by omega)
      obtain ⟨r', φ', hφ'⟩ := IH ↥W hWle hV2W hcountW
      refine ⟨r' + 1,
        (ψ.trans ((AddEquiv.refl (P → ZMod 2)).prodCongr φ')).trans
          (finConsAddEquiv (P → ZMod 2) r'), ?_⟩
      have hunfold : ∀ u : V,
          ((ψ.trans ((AddEquiv.refl (P → ZMod 2)).prodCongr φ')).trans
            (finConsAddEquiv (P → ZMod 2) r')) u
            = Fin.cons (α := fun _ => P → ZMod 2) ((ψ u).1) (φ' ((ψ u).2)) :=
        fun u => rfl
      intro p v m x
      rw [hunfold, hunfold]
      refine Fin.cases ?_ (fun i => ?_) m
      · rw [Fin.cons_zero, Fin.cons_zero]
        exact hψ1 p v x
      · rw [Fin.cons_succ, Fin.cons_succ]
        have hw : (ψ (p • v)).2 = p • (ψ v).2 := Subtype.ext (hψ2 p v)
        rw [hw]
        exact hφ' p ((ψ v).2) i x
    · -- no full-depth vector: the filtration bound forces `V = 0`
      have hall : ∀ v₀ : V, ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1)) v₀ = 0 :=
        fun v₀ => not_not.mp fun h => hex ⟨v₀, h⟩
      have hzero : (nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1) = 0 :=
        LinearMap.ext hall
      have hVtop : Nat.card V
          = Nat.card ↥(LinearMap.ker
              ((nuOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ s - 1))) := by
        rw [hzero, LinearMap.ker_zero]
        exact (Nat.card_congr Submodule.topEquiv.toEquiv).symm
      have hbound : Nat.card V
          ≤ Nat.card {v : V // ∀ p : P, p • v = v} ^ (2 ^ s - 1) := by
        rw [hVtop, hfixker]
        exact card_ker_pow_le _ _
      haveI : Nonempty {v : V // ∀ p : P, p • v = v} := ⟨⟨0, fun p => smul_zero p⟩⟩
      have hfixpos : 0 < Nat.card {v : V // ∀ p : P, p • v = v} := Nat.card_pos
      have hple : Nat.card {v : V // ∀ p : P, p • v = v} ≤ 1 := by
        by_contra hgt
        have hgt' : 1 < Nat.card {v : V // ∀ p : P, p • v = v} := not_le.mp hgt
        have h1 : (1 : ℕ) ≤ 2 ^ s := Nat.one_le_two_pow
        have hlt : Nat.card {v : V // ∀ p : P, p • v = v} ^ (2 ^ s - 1)
            < Nat.card {v : V // ∀ p : P, p • v = v} ^ 2 ^ s :=
          Nat.pow_lt_pow_right hgt' (by omega)
        omega
      have hVone : Nat.card V ≤ 1 := by
        have h5 := Nat.pow_le_pow_left hple (2 ^ s - 1)
        rw [one_pow] at h5
        omega
      haveI : Nonempty V := ⟨0⟩
      have hVcard : Nat.card V = 1 := le_antisymm hVone Nat.card_pos
      obtain ⟨hsub, -⟩ := Nat.card_eq_one_iff_unique.mp hVcard
      exact ⟨0,
        { toFun := fun _ m => m.elim0
          invFun := fun _ => 0
          left_inv := fun v => Subsingleton.elim _ _
          right_inv := fun F => funext fun m => m.elim0
          map_add' := fun a b => funext fun m => m.elim0 },
        fun p v m x => m.elim0⟩

/-- **The counting criterion for `𝔽₂[P]`-freeness over a cyclic 2-group**: a finite
2-torsion `P`-module with `#V^P ^ |P| ≤ #V` is equivariantly isomorphic to a regular module
`Fin r → P → ZMod 2` (with the left-translation action spelled inline).  The reverse
inequality is automatic, so the hypothesis says exactly that the fixed space is as small as
freeness demands. -/
theorem free_of_card_fixedPoints_pow_le {P : Type} [Group P] [Finite P]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction P V]
    (hV2 : ∀ v : V, v + v = 0) (hcyc : IsCyclic P) (h2 : IsPGroup 2 P)
    (hcount : Nat.card {v : V // ∀ p : P, p • v = v} ^ Nat.card P ≤ Nat.card V) :
    ∃ (r : ℕ) (φ : V ≃+ (Fin r → P → ZMod 2)),
      ∀ (p : P) (v : V) (m : Fin r) (x : P), φ (p • v) m x = φ v m (p⁻¹ * x) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g₀, hg⟩ := hcyc.exists_generator
  obtain ⟨s, hs⟩ := h2.exists_card_eq
  rw [hs] at hcount
  exact free_of_card_aux P g₀ hg s hs (Nat.card V) V le_rfl hV2 hcount

/-- **Elementary-abelian reduction of the counting bound to the involution** `ω = g₀^{2^{s-1}}`.
Given the involution's own counting bound `#V^ω ^ 2 ≤ #V` (ω acts "freely enough"), the full
`𝔽₂[P]`-counting bound `#V^P ^ |P| ≤ #V` follows.  This is the standard reduction of freeness
over a cyclic `p`-group to freeness over its order-`p` subgroup, the `p = 2` case of
Chouinard's theorem, made elementary here: `b k := dim ker ν^k` is concave
(`finrank_ker_pow_concave`) with `b 0 = 0` and `b(2^s) = dim V`; the leaf gives
`2·b(2^{s-1}) ≤ dim V = b(2^s)` and concavity gives the reverse (`seq_double_le`), so
`2·b(2^{s-1}) = b(2^s)` and `seq_first_increment_le` forces `2^s·b 1 = b(2^s)`, whence
`#V^P ^ |P| = 2^{b 1·2^s} ≤ 2^{dim V} = #V`. -/
theorem card_fixedPoints_pow_le_of_half {P : Type} [Group P] [Finite P]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction P V]
    (hV2 : ∀ v : V, v + v = 0) (g₀ : P) (hg : ∀ x : P, x ∈ Subgroup.zpowers g₀)
    (s : ℕ) (hs : Nat.card P = 2 ^ s)
    (hleaf : Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2 ≤ Nat.card V) :
    Nat.card {v : V // ∀ p : P, p • v = v} ^ Nat.card P ≤ Nat.card V := by
  letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV2 v)
  letI : SMulCommClass P (ZMod 2) V := ⟨fun p c v => by
    rcases zmod2_cases c with hc | hc <;> rw [hc]
    · rw [zero_smul, zero_smul, smul_zero]
    · rw [one_smul, one_smul]⟩
  haveI : Fintype P := Fintype.ofFinite P
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hsF : Fintype.card P = 2 ^ s := by rw [← Nat.card_eq_fintype_card]; exact hs
  -- card ↔ finrank over 𝔽₂
  have hcardpow : ∀ (p : Submodule (ZMod 2) V),
      Nat.card ↥p = 2 ^ Module.finrank (ZMod 2) ↥p := by
    intro p
    haveI : Fintype ↥p := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := ↥p), ZMod.card]
  have hcardV : Nat.card V = 2 ^ Module.finrank (ZMod 2) V := by
    haveI : Fintype V := Fintype.ofFinite V
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]
  set f : Module.End (ZMod 2) V := nuOp g₀ with hf
  set b : ℕ → ℕ := fun k => Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k)) with hb
  have hb0 : b 0 = 0 := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ 0)) = 0
    rw [pow_zero, Module.End.one_eq_id, LinearMap.ker_id, finrank_bot]
  have hmono : ∀ k, b k ≤ b (k + 1) := by
    intro k; have := finrank_ker_pow_succ f k
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ k))
      ≤ Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (k + 1)))
    omega
  have hconc : ∀ k, b (k + 2) + b k ≤ 2 * b (k + 1) := fun k => finrank_ker_pow_concave f k
  have hbtop : b (2 ^ s) = Module.finrank (ZMod 2) V := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ (2 ^ s))) = _
    rw [hf, nuOp_pow_card_eq_zero g₀ hsF, LinearMap.ker_zero, finrank_top]
  -- fixed points of the whole group = 2^{b 1}
  have hb1 : b 1 = Module.finrank (ZMod 2)
      ↥(LinearMap.ker (nuOp g₀ : Module.End (ZMod 2) V)) := by
    show Module.finrank (ZMod 2) ↥(LinearMap.ker (f ^ 1)) = _
    rw [pow_one]
  have hVP : Nat.card {v : V // ∀ p : P, p • v = v} = 2 ^ b 1 := by
    rw [card_fixedPoints_eq_card_ker_nuOp g₀ hg, hcardpow, hb1]
  -- s = 0: P trivial, bound is #V^P ≤ #V
  rcases Nat.eq_zero_or_pos s with hs0 | hspos
  · subst hs0
    rw [hs, pow_zero, pow_one]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  set m : ℕ := 2 ^ (t + 1) / 2 with hmdef
  have hm_pow : m = 2 ^ t := by rw [hmdef, pow_succ, Nat.mul_div_cancel _ (by norm_num)]
  have h2m : 2 * m = 2 ^ (t + 1) := by rw [hm_pow, pow_succ]; ring
  have hm : 1 ≤ m := by rw [hm_pow]; exact Nat.one_le_two_pow
  -- ν^m = nuOp(g₀^m) (freshman, m = 2^t)
  have hnu_m : (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)
      = f ^ m := by
    have h1 : (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1 := by
      show (genOp (g₀ ^ m) + 1 : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1
      rw [genOp_pow]
    have h2 : (f ^ m : Module.End (ZMod 2) V)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ m + 1 := by
      rw [hf, hm_pow]
      show ((genOp g₀ + 1 : Module.End (ZMod 2) V)) ^ (2 ^ t)
        = (genOp g₀ : Module.End (ZMod 2) V) ^ (2 ^ t) + 1
      rw [add_pow_two_pow_of_two_eq_zero end_two_eq_zero
        (Commute.one_right (genOp g₀ : Module.End (ZMod 2) V)) t, one_pow]
    rw [h1, h2]
  -- the leaf count: #V^{g₀^m} = 2^{b m}
  have hleafcard : Nat.card {v : V // (g₀ ^ m) • v = v} = 2 ^ b m := by
    have hbridge : Nat.card {v : V // (g₀ ^ m) • v = v}
        = Nat.card ↥(LinearMap.ker (nuOp (g₀ ^ m) : Module.End (ZMod 2) V)) := by
      refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
      rw [LinearMap.mem_ker]
      constructor
      · intro hv
        show (genOp (g₀ ^ m) + 1) v = 0
        show (g₀ ^ m) • v + v = 0
        rw [hv]; exact hV2 v
      · intro h
        have h' : (g₀ ^ m) • v + v = 0 := h
        calc (g₀ ^ m) • v = (g₀ ^ m) • v + (v + v) := by rw [hV2, add_zero]
          _ = ((g₀ ^ m) • v + v) + v := (add_assoc _ _ _).symm
          _ = 0 + v := by rw [h']
          _ = v := zero_add v
    rw [hbridge, hnu_m, hcardpow]
  -- leaf ⟹ 2·b m ≤ dim V
  have hleafle : 2 * b m ≤ Module.finrank (ZMod 2) V := by
    have hl := hleaf
    rw [hleafcard, hcardV, ← pow_mul,
      Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)] at hl
    omega
  -- concavity's reverse ⟹ equality at the midpoint
  have hdouble : b (2 * m) ≤ 2 * b m := seq_double_le b hb0 hmono hconc m
  have hhalf : 2 * b m = b (2 * m) := by
    refine le_antisymm ?_ hdouble
    rw [h2m, hbtop]; exact hleafle
  have hkey := seq_first_increment_le b hb0 hmono hconc m hm hhalf
  rw [h2m, hbtop] at hkey
  -- assemble
  rw [hVP, hs, hcardV, ← pow_mul, Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), mul_comm]
  exact hkey

end FreenessCriterion

/-! ## The weight-orbit kernel: the involution counting bound  (P-17e4, PROVED)

`involution_fixedPoints_sq_le` was the last `sorry` of the `lemma_6_11` chain (the paper's
pp. 29–30 weight-orbit content).  It is proved here by an **explicit `𝔽₂`-rational trace
element** — a recorded deviation from the paper's `𝔽̄₂` weight-orbit argument: no base
change, no idempotent decomposition, no semilinear algebra.

Set `t := c τ`, of odd order `m` with `⟨t⟩ ⊴ C`, and let `ω = g₀^{2^{s-1}}` be the
involution of the cyclic Sylow-2 subgroup (`s ≥ 1`; the trivial-Sylow case is handled by
the consumer).  Conjugation gives `ω t ω⁻¹ = t^q` with `q² ≡ 1 (mod m)`.

* **`ω` centralizes `⟨t⟩` (`q ≡ 1`) — impossible** (`two_torsion_of_centralizer_eq_one`,
  the `O₂`-linchpin of Remark 6.12): the centralizer `D := C_C(⟨t⟩)` is abelian (`⟨t⟩` is
  central in it and `D/⟨t⟩` embeds in the cyclic `C/⟨t⟩`), hence its 2-torsion `S` is a
  normal 2-subgroup of `C` containing `ω`; a 2-group acting on the even-cardinality module
  `V` has a second fixed point beyond `0` (orbit counting), the `S`-fixed subgroup is
  `C`-stable by normality, so simplicity forces `S` to act trivially — against faithfulness
  and `ω ≠ 1`.

* **Otherwise, an explicit trace element.**  `g := gcd(q−1, m)` is a *unitary* divisor:
  `gcd(q−1, m/g) = 1` (`coprime_sub_one_div_gcd`, from `m ∣ (q−1)(q+1)` and `m` odd).  So on
  `u := t^g`, of order `r := m/g`, multiplication by `q` is a **fixed-point-free involution
  of `(ZMod r) ∖ {0}`**.  Every nontrivial power of `t` has zero fixed space
  (`fixedPoints_zpowers_tame_eq_zero`: its fixed subgroup is `C`-stable since `⟨t⟩ ⊴ C`, and
  faithfulness kills `⊤`), so the geometric sum `∑_{j<r} u^j • v` vanishes
  (`sum_range_orderOf_smul_eq_zero`).  For `ω`-fixed `v`, summing over the `val`-smaller
  half `Λ` of each pair `{k, qk}` gives `w := ∑_{k∈Λ} u^{k.val} • v` with
  `w + ω•w = ∑_{k≠0} u^{k.val} • v = v` — an explicit additive-Hilbert-90 trace.  Hence
  `ker(1+ω) ⊆ range(1+ω)`, and `#V^ω ^ 2 ≤ #ker·#range = #V` by first-isomorphism
  counting. -/

section InvolutionKernel

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V]

/-- **Every nontrivial element of the inertia `⟨t⟩` has zero fixed space** on a faithful
simple module — the "all isotypic factors are faithful" content of the weight-orbit plan, in
operator form.  The fixed space of `n = t^k` is `C`-stable (a conjugate `h⁻¹ n h = (h⁻¹th)^k`
is again a power of `n` since `h⁻¹th ∈ ⟨t⟩` by normality); simplicity leaves `⊥` or `⊤`, and
`⊤` makes `n` act trivially, so `n = 1` by faithfulness. -/
theorem fixedPoints_zpowers_tame_eq_zero {sg t : C}
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    {n : C} (hn : n ∈ Subgroup.zpowers t) (hn1 : n ≠ 1) :
    ∀ v : V, n • v = v → v = 0 := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hn
  set W : AddSubgroup V :=
    { carrier := {v | n • v = v}
      zero_mem' := smul_zero n
      add_mem' := fun ha hb => by
        show n • (_ + _) = _
        rw [smul_add, ha, hb]
      neg_mem' := fun ha => by
        show n • (-_) = -_
        rw [smul_neg, ha] } with hWdef
  have hstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    have hconjt : h⁻¹ * t * h ∈ Subgroup.zpowers t := by
      have h1 := hnorm.conj_mem t (Subgroup.mem_zpowers t) h⁻¹
      rwa [inv_inv] at h1
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.mp hconjt
    have hpow : h⁻¹ * n * h = n ^ a := by
      have e1 : (h⁻¹ * t * h) ^ k = h⁻¹ * t ^ k * h := by
        have e0 := conj_zpow (i := k) (a := h⁻¹) (b := t)
        rwa [inv_inv] at e0
      rw [← hk, ← e1, ← ha, ← zpow_mul, mul_comm, zpow_mul]
    have hfix : (h⁻¹ * n * h) • w = w := by
      rw [hpow]
      have hnst : n ∈ MulAction.stabilizer C w := hw
      have hmem : n ^ a ∈ MulAction.stabilizer C w := zpow_mem hnst a
      exact hmem
    show n • (h • w) = h • w
    calc n • (h • w) = (n * h) • w := (mul_smul n h w).symm
      _ = (h * (h⁻¹ * n * h)) • w := by group
      _ = h • ((h⁻¹ * n * h) • w) := mul_smul _ _ _
      _ = h • w := by rw [hfix]
  rcases hsimple W hstable with hbot | htop
  · intro v hv
    have hvW : v ∈ W := hv
    rwa [hbot, AddSubgroup.mem_bot] at hvW
  · exact absurd (hfaith n fun v => (htop ▸ AddSubgroup.mem_top v : v ∈ W)) hn1

omit [Finite C] in
/-- The **geometric sum** of a fixed-point-free finite-order action vanishes: the sum
`∑_{j < orderOf u} u^j • v` is `u`-invariant, so it lies in the zero fixed space. -/
theorem sum_range_orderOf_smul_eq_zero {u : C}
    (hfree : ∀ v : V, u • v = v → v = 0) (v : V) :
    ∑ j ∈ Finset.range (orderOf u), u ^ j • v = 0 := by
  refine hfree _ ?_
  rw [Finset.smul_sum]
  have hstep : ∀ j : ℕ, u • (u ^ j • v) = u ^ (j + 1) • v := fun j => by
    rw [← mul_smul, ← pow_succ']
  rw [Finset.sum_congr rfl fun j _ => hstep j]
  have h1 := Finset.sum_range_succ' (fun j => u ^ j • v) (orderOf u)
  have h2 := Finset.sum_range_succ (fun j => u ^ j • v) (orderOf u)
  have h3 : (∑ j ∈ Finset.range (orderOf u), u ^ (j + 1) • v) + u ^ 0 • v
      = (∑ j ∈ Finset.range (orderOf u), u ^ j • v) + u ^ orderOf u • v := h1.symm.trans h2
  rw [pow_zero, one_smul, pow_orderOf_eq_one, one_smul] at h3
  exact add_right_cancel h3

/-- Arithmetic core of the trace construction: for `m` odd with `m ∣ (q−1)(q+1)`, the gcd
`g := gcd(q−1, m)` is a *unitary* divisor — `gcd(q−1, m/g) = 1`.  (For any prime `p ∣ q−1`
dividing `m`, oddness forces `p ∤ q+1`, so the full `p`-part of `m` divides `q−1` and hence
`g`; nothing survives into `m/g`.) -/
private theorem coprime_sub_one_div_gcd {q m : ℕ} (hm : 0 < m) (hmodd : Odd m)
    (hq1 : 1 ≤ q) (hdvd : m ∣ (q - 1) * (q + 1)) :
    Nat.Coprime (q - 1) (m / Nat.gcd (q - 1) m) := by
  set g := Nat.gcd (q - 1) m with hg
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm
  have hr0 : 0 < m / g := Nat.div_pos (Nat.le_of_dvd hm hgm) hg0
  by_contra hcop
  obtain ⟨p, hp, hpq1, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpm : p ∣ m := hpr.trans (Nat.div_dvd_of_dvd hgm)
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr hpm)
  have hpq1' : ¬ p ∣ q + 1 := by
    intro hpq1p
    have h2 : p ∣ 2 := by
      have hsub := Nat.dvd_sub hpq1p hpq1
      have : q + 1 - (q - 1) = 2 := by omega
      rwa [this] at hsub
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  have hpe : p ^ m.factorization p ∣ m := Nat.ordProj_dvd m p
  have hpeq : p ^ m.factorization p ∣ q - 1 := by
    refine Nat.Coprime.dvd_of_dvd_mul_right ?_ (hpe.trans hdvd)
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq1')
  have hpeg : p ^ m.factorization p ∣ g := Nat.dvd_gcd hpeq hpe
  have hge : m.factorization p ≤ g.factorization p :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp hg0.ne').mp hpeg
  have hfe : (m / g).factorization p = m.factorization p - g.factorization p := by
    rw [Nat.factorization_div hgm, Finsupp.tsub_apply]
  have h1r : 1 ≤ (m / g).factorization p :=
    (Nat.Prime.dvd_iff_one_le_factorization hp hr0.ne').mp hpr
  omega

/-- **The `O₂`-linchpin (Remark 6.12)**: on a nonzero faithful simple 2-torsion module, an
element of order dividing 2 commuting with the inertia generator `t` is trivial.  The
centralizer `D := C_C(⟨t⟩)` is abelian (`⟨t⟩ ≤ Z(D)` and `D/⟨t⟩` embeds in the cyclic
`C/⟨t⟩`, so `commutative_of_cyclic_center_quotient` applies); its 2-torsion `S` is therefore
a subgroup, normal in `C`, and `IsPGroup 2`.  A 2-group acting on a module of even
cardinality with one fixed point has another
(`IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point`), so the `S`-fixed subgroup
is nonzero and `C`-stable, hence `⊤` by simplicity: `S` acts trivially and faithfulness
collapses it. -/
theorem two_torsion_of_centralizer_eq_one [Finite V] {sg t : C}
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV0 : ∃ v₀ : V, v₀ ≠ (0 : V))
    {x : C} (hx2 : x ^ 2 = 1) (hxt : x * t = t * x) : x = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  haveI hqcyc : IsCyclic (C ⧸ Subgroup.zpowers t) := quotient_zpowers_isCyclic_of_tame hgen
  set D : Subgroup C := Subgroup.centralizer (Subgroup.zpowers t : Set C) with hD
  have hDn : D.Normal := by rw [hD]; infer_instance
  have hxD : x ∈ D := by
    rw [hD]
    refine Subgroup.mem_centralizer_iff.mpr fun y hy => ?_
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (SetLike.mem_coe.mp hy)
    exact ((Commute.zpow_right hxt k).symm).eq
  -- `D` is abelian: `⟨t⟩ ≤ Z(D)` and `D/⟨t⟩` embeds in the cyclic quotient
  have hDcomm : IsMulCommutative ↥D := by
    refine MonoidHom.isMulCommutative_of_isCyclic_of_ker_le_center
      ((QuotientGroup.mk' (Subgroup.zpowers t)).comp D.subtype) ?_
    intro d hd
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hd
    have hdt : (d : C) ∈ Subgroup.zpowers t := (QuotientGroup.eq_one_iff _).mp hd
    refine Subgroup.mem_center_iff.mpr fun a => ?_
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp a.2 (d : C) hdt).symm
  have hDab : ∀ a b : ↥D, a * b = b * a := fun a b => hDcomm.is_comm.comm a b
  -- the 2-torsion of `D`: a normal 2-subgroup of `C` containing `x`
  set S : Subgroup C :=
    { carrier := {y : C | y ∈ D ∧ ∃ k : ℕ, y ^ 2 ^ k = 1}
      one_mem' := ⟨D.one_mem, 0, by norm_num⟩
      mul_mem' := by
        rintro a b ⟨haD, ka, hka⟩ ⟨hbD, kb, hkb⟩
        refine ⟨D.mul_mem haD hbD, ka + kb, ?_⟩
        have hcomm : Commute a b := congrArg Subtype.val (hDab ⟨a, haD⟩ ⟨b, hbD⟩)
        have ha' : a ^ 2 ^ (ka + kb) = 1 := by rw [pow_add, pow_mul, hka, one_pow]
        have hb' : b ^ 2 ^ (ka + kb) = 1 := by
          rw [pow_add, mul_comm (2 ^ ka), pow_mul, hkb, one_pow]
        rw [hcomm.mul_pow, ha', hb', one_mul]
      inv_mem' := by
        rintro a ⟨haD, ka, hka⟩
        exact ⟨D.inv_mem haD, ka, by rw [inv_pow, hka, inv_one]⟩ } with hS
  have hSn : S.Normal := by
    constructor
    rintro y ⟨hyD, k, hk⟩ g
    refine ⟨hDn.conj_mem y hyD g, k, ?_⟩
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  have hSp : IsPGroup 2 ↥S := by
    intro y
    obtain ⟨-, k, hk⟩ := y.2
    exact ⟨k, Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hk)⟩
  -- orbit counting: a second `S`-fixed point beyond `0`
  have h2V : (2 : ℕ) ∣ Nat.card V := by
    letI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact hV2 v)
    haveI : Fintype V := Fintype.ofFinite V
    haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
    obtain ⟨v₀, hv₀⟩ := hV0
    haveI : Nontrivial V := ⟨v₀, 0, hv₀⟩
    rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := V), ZMod.card]
    exact dvd_pow_self 2 Module.finrank_pos.ne'
  have hfix0 : (0 : V) ∈ MulAction.fixedPoints ↥S V := fun y => smul_zero y
  obtain ⟨w, hwfix, hw0⟩ :=
    hSp.exists_fixed_point_of_prime_dvd_card_of_fixed_point V h2V hfix0
  -- the `S`-fixed subgroup is `C`-stable and nonzero, hence `⊤`
  set W : AddSubgroup V :=
    { carrier := {v : V | ∀ y ∈ S, y • v = v}
      zero_mem' := fun y _ => smul_zero y
      add_mem' := fun ha hb y hy => by rw [smul_add, ha y hy, hb y hy]
      neg_mem' := fun ha y hy => by rw [smul_neg, ha y hy] } with hW
  have hstable : ∀ (h : C), ∀ w' ∈ W, h • w' ∈ W := by
    intro h w' hw' y hy
    have hyc : h⁻¹ * y * h ∈ S := by
      have h1 := hSn.conj_mem y hy h⁻¹
      rwa [inv_inv] at h1
    calc y • (h • w') = (y * h) • w' := (mul_smul y h w').symm
      _ = (h * (h⁻¹ * y * h)) • w' := by group
      _ = h • ((h⁻¹ * y * h) • w') := mul_smul _ _ _
      _ = h • w' := by rw [hw' _ hyc]
  have hwW : w ∈ W := fun y hy => hwfix ⟨y, hy⟩
  have hWtop : W = ⊤ := by
    rcases hsimple W hstable with hbot | htop
    · exfalso
      rw [hbot, AddSubgroup.mem_bot] at hwW
      exact hw0 hwW.symm
    · exact htop
  have hxS : x ∈ S := ⟨hxD, 1, by rw [pow_one]; exact hx2⟩
  refine hfaith x fun v => ?_
  have hvW : v ∈ W := hWtop ▸ AddSubgroup.mem_top v
  exact hvW x hxS

end InvolutionKernel

/-- **The involution counting bound** (the leaf of Lemma 6.11, P-17e4): the involution
`ω = g₀^{2^{s-1}}` of the cyclic Sylow-2 subgroup acts freely enough on the ramified simple
faithful module, `#V^ω ^ 2 ≤ #V`.  This is the `p = 2` elementary-abelian case of the
paper's pp. 29–30 weight-orbit argument.

**Statement amendment (P-17e4, documented in the board row): `hs1 : 1 ≤ s` added.**  The
bound is *false* for a trivial Sylow-2 subgroup (`s = 0` gives `ω = 1`, e.g. the Frobenius
group `C₇ ⋊ C₃` of order 21 acting on `𝔽₈` is ramified simple faithful with `#V^ω = #V`);
the sole consumer `card_fixedPoints_pow_le_of_ramified` needs no leaf there (`#V^P ^ 1 ≤ #V`
is subtype counting).

Proof: `t := c τ` has odd order `m` and `⟨t⟩ ⊴ C`; conjugation gives `ω t ω⁻¹ = t^q`,
`q² ≡ 1 (mod m)`.  If `t^q = t`, then `ω` lies in the 2-torsion of the abelian centralizer
`C_C(⟨t⟩)` — a normal 2-subgroup acting trivially by simplicity, against faithfulness
(`two_torsion_of_centralizer_eq_one`), impossible since `ω ≠ 1`.  Otherwise the trace element
`w := ∑_{k ∈ Λ} (t^g)^{k.val} • v` over a transversal `Λ` of the fixed-point-free involution
`k ↦ qk` of `(ZMod (m/g)) ∖ {0}` (`g := gcd(q−1, m)`, unitary by
`coprime_sub_one_div_gcd`) satisfies `w + ω•w = v` for every `ω`-fixed `v` (geometric-sum
vanishing `sum_range_orderOf_smul_eq_zero` + `fixedPoints_zpowers_tame_eq_zero`), so
`ker(1+ω) ⊆ range(1+ω)` and first-isomorphism counting gives the bound. -/
theorem involution_fixedPoints_sq_le_of_tame_pair {C : Type} [Group C]
    [Finite C] {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C)
    (g₀ : ↥(P : Subgroup C)) (hg : ∀ x : ↥(P : Subgroup C), x ∈ Subgroup.zpowers g₀)
    (s : ℕ) (hs1 : 1 ≤ s) (hs : Nat.card ↥(P : Subgroup C) = 2 ^ s) :
    Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2 ≤ Nat.card V := by
  haveI hnorm : (Subgroup.zpowers t).Normal := Tame.zpowers_normal_of_tame hgen hrel
  have hmodd : Odd (orderOf t) := Tame.tame_odd_order (orderOf_pos sg).ne' hrel
  set m : ℕ := orderOf t with hm
  have hm0 : 0 < m := orderOf_pos t
  -- ramification gives `t ≠ 1` and a nonzero vector
  obtain ⟨vr, hvr⟩ := hram
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, one_smul] at hvr
    exact hvr rfl
  have hV0 : ∃ v₀ : V, v₀ ≠ (0 : V) := by
    refine ⟨vr, fun h => hvr ?_⟩
    rw [h, smul_zero]
  -- the involution ω = g₀^{2^{s-1}}
  set ω : C := ((g₀ ^ (2 ^ s / 2) : ↥(P : Subgroup C)) : C) with hωdef
  have hsmul_def : ∀ v : V, (g₀ ^ (2 ^ s / 2)) • v = ω • v := fun v => rfl
  have hg₀ord : orderOf ((g₀ : C)) = 2 ^ s := by
    have h1 : orderOf g₀ = 2 ^ s := by
      rw [orderOf_eq_card_of_forall_mem_zpowers hg, hs]
    rw [← h1]
    exact orderOf_injective (P : Subgroup C).subtype Subtype.val_injective g₀
  have hs2 : 2 ^ s / 2 = 2 ^ (s - 1) := by
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ, Nat.mul_div_cancel _ (by norm_num : 0 < 2)]
  have hωcoe : ω = (g₀ : C) ^ (2 ^ s / 2) := by
    rw [hωdef, SubmonoidClass.coe_pow]
  have hωord : orderOf ω = 2 := by
    rw [hωcoe, hs2, orderOf_pow, hg₀ord]
    have hgcd : Nat.gcd (2 ^ s) (2 ^ (s - 1)) = 2 ^ (s - 1) :=
      Nat.gcd_eq_right (pow_dvd_pow 2 (by omega))
    rw [hgcd]
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    rw [Nat.add_sub_cancel, pow_succ,
      Nat.mul_div_cancel_left _ (by positivity : 0 < 2 ^ s')]
  have hω2 : ω * ω = 1 := by
    have h := pow_orderOf_eq_one ω
    rwa [hωord, pow_two] at h
  have hω1 : ω ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hωord
    omega
  -- conjugation by ω sends t to t^q, q² ≡ 1 (mod m)
  have hconjmem : ω * t * ω⁻¹ ∈ Subgroup.zpowers t :=
    hnorm.conj_mem t (Subgroup.mem_zpowers t) ω
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hconjmem
  set q : ℕ := (j % (m : ℤ)).toNat with hq
  have hjm0 : 0 ≤ j % (m : ℤ) := Int.emod_nonneg j (by exact_mod_cast hm0.ne')
  have hjm1 : j % (m : ℤ) < (m : ℤ) := Int.emod_lt_of_pos j (by exact_mod_cast hm0)
  have hqcast : (q : ℤ) = j % (m : ℤ) := Int.toNat_of_nonneg hjm0
  have hqm : q < m := by omega
  have htq : t ^ q = ω * t * ω⁻¹ := by
    have hm1 : t ^ (m : ℤ) = 1 := by
      rw [zpow_natCast, hm, pow_orderOf_eq_one]
    have h2 : t ^ j = t ^ (j % (m : ℤ)) := by
      conv_lhs => rw [← Int.emod_add_mul_ediv j (m : ℤ)]
      rw [zpow_add, zpow_mul, hm1, one_zpow, mul_one]
    calc t ^ q = t ^ (q : ℤ) := (zpow_natCast t q).symm
      _ = t ^ (j % (m : ℤ)) := by rw [hqcast]
      _ = t ^ j := h2.symm
      _ = ω * t * ω⁻¹ := hj
  have hq0 : q ≠ 0 := by
    intro h0
    rw [h0, pow_zero] at htq
    refine ht1 ?_
    calc t = ω⁻¹ * (ω * t * ω⁻¹) * ω := by group
      _ = ω⁻¹ * 1 * ω := by rw [← htq]
      _ = 1 := by group
  have htqq : t ^ (q * q) = t := by
    calc t ^ (q * q) = (t ^ q) ^ q := by rw [pow_mul]
      _ = (ω * t * ω⁻¹) ^ q := by rw [htq]
      _ = ω * t ^ q * ω⁻¹ := conj_pow
      _ = ω * (ω * t * ω⁻¹) * ω⁻¹ := by rw [htq]
      _ = (ω * ω) * t * (ω * ω)⁻¹ := by group
      _ = t := by rw [hω2, one_mul, inv_one, mul_one]
  have hqq : (q - 1) * (q + 1) = q * q - 1 := by
    obtain ⟨k, hk⟩ : ∃ k, q = k + 1 := ⟨q - 1, by omega⟩
    rw [hk]
    have h2 : (k + 1) * (k + 1) = k * (k + 1 + 1) + 1 := by ring
    rw [Nat.add_sub_cancel, h2, Nat.add_sub_cancel]
  have hdvd : m ∣ (q - 1) * (q + 1) := by
    have hqq0 : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    have ht1' : t ^ (q * q - 1) = 1 := by
      have h4 : t ^ (q * q - 1) * t = 1 * t := by
        rw [one_mul, ← pow_succ, Nat.sub_add_cancel hqq0, htqq]
      exact mul_right_cancel h4
    have h5 : t ^ ((q - 1) * (q + 1)) = 1 := by rw [hqq]; exact ht1'
    have h6 := orderOf_dvd_iff_pow_eq_one.mpr h5
    rwa [← hm] at h6
  -- dichotomy: ω centralizes t (impossible), or the trace element exists
  by_cases hcen : ω * t = t * ω
  · exact absurd
      (two_torsion_of_centralizer_eq_one hgen hrel hV2 hfaith hsimple hV0
        (by rw [pow_two]; exact hω2) hcen) hω1
  -- the ramified branch: q ≥ 2 and the unitary-gcd setup
  have hq2 : 2 ≤ q := by
    rcases Nat.lt_or_ge q 2 with h | h
    · exfalso
      have hq1 : q = 1 := by omega
      rw [hq1, pow_one] at htq
      refine hcen ?_
      calc ω * t = (ω * t * ω⁻¹) * ω := by group
        _ = t * ω := by rw [← htq]
    · exact h
  set g : ℕ := Nat.gcd (q - 1) m with hgdef
  have hgm : g ∣ m := Nat.gcd_dvd_right _ _
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hm0
  have hglt : g < m := by
    have h1 : g ∣ q - 1 := Nat.gcd_dvd_left _ _
    have h2 : g ≤ q - 1 := Nat.le_of_dvd (by omega) h1
    omega
  set r : ℕ := m / g with hrdef
  have hgr : g * r = m := by rw [hrdef]; exact Nat.mul_div_cancel' hgm
  have hr2 : 2 ≤ r := by
    rcases Nat.lt_or_ge r 2 with h | h
    · interval_cases r <;> omega
    · exact h
  haveI : NeZero r := ⟨by omega⟩
  have hcop' : Nat.Coprime (q - 1) r := by
    rw [hrdef, hgdef]
    exact coprime_sub_one_div_gcd hm0 hmodd (by omega) hdvd
  set u : C := t ^ g with hudef
  have humem : u ∈ Subgroup.zpowers t :=
    Subgroup.mem_zpowers_iff.mpr ⟨(g : ℤ), by rw [zpow_natCast, ← hudef]⟩
  have huord : orderOf u = r := by
    rw [hudef, orderOf_pow, ← hm, Nat.gcd_eq_right hgm, hrdef]
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, orderOf_one] at huord
    omega
  have hufree : ∀ v : V, u • v = v → v = 0 :=
    fixedPoints_zpowers_tame_eq_zero hgen hrel hfaith hsimple humem hu1
  have husum : ∀ v : V, ∑ k ∈ Finset.range r, u ^ k • v = 0 := by
    intro v
    have h := sum_range_orderOf_smul_eq_zero hufree v
    rwa [huord] at h
  have hconju : ∀ a : ℕ, ω * u ^ a * ω⁻¹ = u ^ (q * a) := by
    intro a
    calc ω * u ^ a * ω⁻¹ = ω * t ^ (g * a) * ω⁻¹ := by rw [hudef, ← pow_mul]
      _ = (ω * t * ω⁻¹) ^ (g * a) := by rw [conj_pow]
      _ = (t ^ q) ^ (g * a) := by rw [htq]
      _ = t ^ (q * (g * a)) := by rw [← pow_mul]
      _ = t ^ (g * (q * a)) := by rw [mul_left_comm]
      _ = (t ^ g) ^ (q * a) := by rw [pow_mul]
      _ = u ^ (q * a) := by rw [← hudef]
  -- mult-by-q is a fixed-point-free involution of (ZMod r) ∖ {0}
  have hrdvd : r ∣ q * q - 1 := by
    have hrm : r ∣ m := ⟨g, by rw [← hgr]; ring⟩
    rw [← hqq]
    exact hrm.trans hdvd
  have hcast : ((q : ZMod r) * (q : ZMod r)) = 1 := by
    have hqq0 : 0 < q * q := Nat.mul_pos (by omega) (by omega)
    have h0 : ((q * q - 1 : ℕ) : ZMod r) = 0 :=
      (CharP.cast_eq_zero_iff (ZMod r) r _).mpr hrdvd
    calc ((q : ZMod r) * (q : ZMod r)) = ((q * q : ℕ) : ZMod r) := by push_cast; ring
      _ = (((q * q - 1) + 1 : ℕ) : ZMod r) := by rw [Nat.sub_add_cancel hqq0]
      _ = ((q * q - 1 : ℕ) : ZMod r) + 1 := by push_cast; ring
      _ = 1 := by rw [h0, zero_add]
  have hinv2 : ∀ k : ZMod r, (q : ZMod r) * ((q : ZMod r) * k) = k := by
    intro k
    rw [← mul_assoc, hcast, one_mul]
  have hval_inj : ∀ a b : ZMod r, ZMod.val a = ZMod.val b → a = b := by
    intro a b h
    have ha := ZMod.natCast_rightInverse (n := r) a
    have hb := ZMod.natCast_rightInverse (n := r) b
    rw [← ha, ← hb, h]
  have hqfix : ∀ k : ZMod r, k ≠ 0 → (q : ZMod r) * k ≠ k := by
    intro k hk0 hfix
    have h1 : ((q - 1 : ℕ) : ZMod r) * k = 0 := by
      rw [Nat.cast_sub (by omega : 1 ≤ q), Nat.cast_one, sub_mul, one_mul, hfix, sub_self]
    have hunit : IsUnit ((q - 1 : ℕ) : ZMod r) := (ZMod.isUnit_iff_coprime _ _).mpr hcop'
    exact hk0 ((IsUnit.mul_right_eq_zero hunit).mp h1)
  -- the two half-transversals of the pairing k ↔ q·k
  set Λ₁ : Finset (ZMod r) :=
    Finset.univ.filter (fun k => k ≠ 0 ∧ ZMod.val k < ZMod.val ((q : ZMod r) * k)) with hΛ₁
  set Λ₂ : Finset (ZMod r) :=
    Finset.univ.filter (fun k => k ≠ 0 ∧ ZMod.val ((q : ZMod r) * k) < ZMod.val k) with hΛ₂
  have hdisj : Disjoint Λ₁ Λ₂ := by
    rw [Finset.disjoint_left]
    intro k h1 h2
    rw [hΛ₁, Finset.mem_filter] at h1
    rw [hΛ₂, Finset.mem_filter] at h2
    obtain ⟨-, -, hlt1⟩ := h1
    obtain ⟨-, -, hlt2⟩ := h2
    omega
  have hunion : Λ₁ ∪ Λ₂ = Finset.univ.erase (0 : ZMod r) := by
    ext k
    simp only [hΛ₁, hΛ₂, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_erase, and_true]
    constructor
    · rintro (⟨hk0, -⟩ | ⟨hk0, -⟩) <;> exact hk0
    · intro hk0
      have hne : ZMod.val ((q : ZMod r) * k) ≠ ZMod.val k := fun h =>
        hqfix k hk0 (hval_inj _ _ h)
      rcases Nat.lt_or_ge (ZMod.val k) (ZMod.val ((q : ZMod r) * k)) with h | h
      · exact Or.inl ⟨hk0, h⟩
      · exact Or.inr ⟨hk0, by omega⟩
  have hmapsto : ∀ k ∈ Λ₁, (q : ZMod r) * k ∈ Λ₂ := by
    intro k hk
    rw [hΛ₁, Finset.mem_filter] at hk
    rw [hΛ₂, Finset.mem_filter]
    obtain ⟨-, hk0, hlt⟩ := hk
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h0
      have h1 : (q : ZMod r) * ((q : ZMod r) * k) = (q : ZMod r) * 0 := by rw [h0]
      rw [hinv2 k, mul_zero] at h1
      exact hk0 h1
    · rw [hinv2 k]
      exact hlt
  have hmapsto' : ∀ k ∈ Λ₂, (q : ZMod r) * k ∈ Λ₁ := by
    intro k hk
    rw [hΛ₂, Finset.mem_filter] at hk
    rw [hΛ₁, Finset.mem_filter]
    obtain ⟨-, hk0, hlt⟩ := hk
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · intro h0
      have h1 : (q : ZMod r) * ((q : ZMod r) * k) = (q : ZMod r) * 0 := by rw [h0]
      rw [hinv2 k, mul_zero] at h1
      exact hk0 h1
    · rw [hinv2 k]
      exact hlt
  -- the trace element: every ω-fixed vector is in the range of 1 + ω
  have htrace : ∀ v : V, ω • v = v → ∃ w : V, v = w + ω • w := by
    intro v hv
    refine ⟨∑ k ∈ Λ₁, u ^ (ZMod.val k) • v, ?_⟩
    have hstep : ∀ k : ZMod r,
        ω • (u ^ (ZMod.val k) • v) = u ^ (ZMod.val ((q : ZMod r) * k)) • v := by
      intro k
      have h1 : ω * u ^ (ZMod.val k) = u ^ (q * ZMod.val k) * ω := by
        calc ω * u ^ (ZMod.val k) = (ω * u ^ (ZMod.val k) * ω⁻¹) * ω := by group
          _ = u ^ (q * ZMod.val k) * ω := by rw [hconju (ZMod.val k)]
      have h2 : u ^ (q * ZMod.val k) = u ^ (ZMod.val ((q : ZMod r) * k)) := by
        have hval : ZMod.val ((q : ZMod r) * k) = q * ZMod.val k % r := by
          rw [ZMod.val_mul, ZMod.val_natCast]
          exact (Nat.mod_modEq q r).mul_right (ZMod.val k)
        have hpm : u ^ (q * ZMod.val k % r) = u ^ (q * ZMod.val k) := by
          have h := pow_mod_orderOf u (q * ZMod.val k)
          rwa [huord] at h
        rw [hval]
        exact hpm.symm
      calc ω • (u ^ (ZMod.val k) • v) = (ω * u ^ (ZMod.val k)) • v := (mul_smul _ _ _).symm
        _ = (u ^ (q * ZMod.val k) * ω) • v := by rw [h1]
        _ = u ^ (q * ZMod.val k) • (ω • v) := mul_smul _ _ _
        _ = u ^ (q * ZMod.val k) • v := by rw [hv]
        _ = u ^ (ZMod.val ((q : ZMod r) * k)) • v := by rw [h2]
    have hωsum : ω • (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v) = ∑ k ∈ Λ₂, u ^ (ZMod.val k) • v := by
      calc ω • (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v)
          = ∑ k ∈ Λ₁, ω • (u ^ (ZMod.val k) • v) := Finset.smul_sum
        _ = ∑ k ∈ Λ₁, u ^ (ZMod.val ((q : ZMod r) * k)) • v :=
            Finset.sum_congr rfl fun k _ => hstep k
        _ = ∑ k ∈ Λ₂, u ^ (ZMod.val k) • v :=
            Finset.sum_nbij' (fun k => (q : ZMod r) * k) (fun k => (q : ZMod r) * k)
              hmapsto hmapsto' (fun k _ => hinv2 k) (fun k _ => hinv2 k) (fun k _ => rfl)
    have h2 : ∑ k : ZMod r, u ^ (ZMod.val k) • v = ∑ j ∈ Finset.range r, u ^ j • v :=
      Finset.sum_nbij' (fun k => ZMod.val k) (fun j => (j : ZMod r))
        (fun k _ => Finset.mem_range.mpr (ZMod.val_lt k))
        (fun j _ => Finset.mem_univ _)
        (fun k _ => ZMod.natCast_rightInverse k)
        (fun j hj => ZMod.val_cast_of_lt (Finset.mem_range.mp hj))
        (fun k _ => rfl)
    have hfull : ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v = v := by
      have h1 : (∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v)
          + u ^ (ZMod.val (0 : ZMod r)) • v = ∑ k : ZMod r, u ^ (ZMod.val k) • v :=
        Finset.sum_erase_add _ _ (Finset.mem_univ 0)
      rw [h2, husum v, ZMod.val_zero, pow_zero, one_smul] at h1
      calc ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v
          = ((∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v) + v) + v := by
            rw [add_assoc, hV2, add_zero]
        _ = 0 + v := by rw [h1]
        _ = v := zero_add v
    have hsplit : (∑ k ∈ Λ₁, u ^ (ZMod.val k) • v) + (∑ k ∈ Λ₂, u ^ (ZMod.val k) • v)
        = ∑ k ∈ Finset.univ.erase (0 : ZMod r), u ^ (ZMod.val k) • v := by
      rw [← Finset.sum_union hdisj, hunion]
    rw [hωsum, hsplit, hfull]
  -- counting: ker(1 + ω) ⊆ range(1 + ω) forces #ker² ≤ #V
  set A : V →+ V :=
    { toFun := fun w => w + ω • w
      map_zero' := by rw [smul_zero, add_zero]
      map_add' := fun a b => by rw [smul_add]; abel } with hA
  have hAfix : ∀ v : V, A v = 0 → ω • v = v := by
    intro v h
    have h1 : v + ω • v = 0 := h
    calc ω • v = ω • v + (v + v) := by rw [hV2, add_zero]
      _ = (v + ω • v) + v := by abel
      _ = 0 + v := by rw [h1]
      _ = v := zero_add v
  have hfixiff : ∀ v : V, ((g₀ ^ (2 ^ s / 2)) • v = v) ↔ v ∈ A.ker := by
    intro v
    rw [AddMonoidHom.mem_ker, hsmul_def v]
    constructor
    · intro h
      show v + ω • v = 0
      rw [h]
      exact hV2 v
    · intro h
      exact hAfix v h
  have hkerle : A.ker ≤ A.range := by
    intro v hv
    rw [AddMonoidHom.mem_ker] at hv
    obtain ⟨w, hw⟩ := htrace v (hAfix v hv)
    exact AddMonoidHom.mem_range.mpr ⟨w, hw.symm⟩
  have hcard1 : Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} = Nat.card ↥A.ker :=
    Nat.card_congr (Equiv.subtypeEquivRight hfixiff)
  have hcardle : Nat.card ↥A.ker ≤ Nat.card ↥A.range := by
    refine Nat.card_le_card_of_injective (fun x => ⟨x.1, hkerle x.2⟩) ?_
    intro a b hab
    have h1 := congrArg Subtype.val hab
    exact Subtype.ext h1
  have hiso : Nat.card (V ⧸ A.ker) = Nat.card ↥A.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange A).toEquiv
  have hprod : Nat.card V = Nat.card ↥A.range * Nat.card ↥A.ker := by
    rw [AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup A.ker, hiso]
  calc Nat.card {v : V // (g₀ ^ (2 ^ s / 2)) • v = v} ^ 2
      = Nat.card ↥A.ker * Nat.card ↥A.ker := by rw [hcard1, pow_two]
    _ ≤ Nat.card ↥A.range * Nat.card ↥A.ker :=
        Nat.mul_le_mul_right _ hcardle
    _ = Nat.card V := hprod.symm


/-- **The Sylow-2 fixed-space bound on a ramified simple faithful module.**  The full bound
`#V^P ^ |P| ≤ #V` follows (via `card_fixedPoints_pow_le_of_half`, the elementary-abelian
reduction) from the **involution counting bound** `#V^ω ^ 2 ≤ #V` for the involution
`ω = g₀^{2^{s-1}}` in the cyclic Sylow-2 subgroup (`involution_fixedPoints_sq_le` above,
which needs `1 ≤ s`); a trivial Sylow-2 subgroup gives the bound by subtype counting.

Faithfulness is genuinely needed (Remark 6.12: `C₃ ⋊ C₄` acting through `S₃` on `𝔽₄` is
ramified simple but its central `C₂` fixes everything, so `#V^ω = #V > #V^{1/2}`). -/
theorem card_fixedPoints_pow_le_of_ramified_of_tame_pair {C : Type} [Group C]
    [Finite C] {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    Nat.card {v : V // ∀ p : ↥(P : Subgroup C), p • v = v} ^ Nat.card ↥(P : Subgroup C)
      ≤ Nat.card V := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcyc : IsCyclic ↥(P : Subgroup C) :=
    isCyclic_of_isPGroup_two_of_tame hgen hrel (P : Subgroup C) P.isPGroup'
  obtain ⟨g₀, hg⟩ := hcyc.exists_generator
  obtain ⟨s, hs⟩ := P.isPGroup'.exists_card_eq
  -- trivial Sylow-2 subgroup: the bound is plain subtype counting
  rcases Nat.eq_zero_or_pos s with hs0 | hs1
  · subst hs0
    rw [hs, pow_zero, pow_one]
    exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
  -- Elementary-abelian reduction: it suffices that the involution `g₀^{2^{s-1}}` acts freely.
  refine card_fixedPoints_pow_le_of_half hV2 g₀ hg s hs ?_
  exact involution_fixedPoints_sq_le_of_tame_pair hgen hrel hV2 hfaith hsimple hram P g₀ hg
    s hs1 hs


/-- **`𝔽₂[P]`-freeness of the restriction to the Sylow 2-subgroup** (Lemma 6.11, steps 1–2):
a ramified simple faithful module is equivariantly additively isomorphic to a regular module
`𝔽₂[P]^r`.  **Proved** from the counting criterion `free_of_card_fixedPoints_pow_le` at the
cyclic Sylow 2-subgroup (`isCyclic_of_isPGroup_two_of_tame`, with the tame relation
transported from `tame_relation` along `c`) and the counting bound
`card_fixedPoints_pow_le_of_ramified` above.  Fully sorry-free, std-3. -/
theorem sylow_free_of_ramified_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    ∃ (r : ℕ) (φ : V ≃+ (Fin r → ↥(P : Subgroup C) → ZMod 2)),
      ∀ (p : ↥(P : Subgroup C)) (v : V) (n : Fin r) (x : ↥(P : Subgroup C)),
        φ ((p : C) • v) n x = φ v n (p⁻¹ * x) := by
  have hcyc : IsCyclic ↥(P : Subgroup C) :=
    isCyclic_of_isPGroup_two_of_tame hgen hrel (P : Subgroup C) P.isPGroup'
  have hcount :=
    card_fixedPoints_pow_le_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  obtain ⟨r, φ, hφ⟩ := free_of_card_fixedPoints_pow_le hV2 hcyc P.isPGroup' hcount
  exact ⟨r, φ, fun p v n x => hφ p v n x⟩


/-- **The weight-orbit kernel in split-pair form** (what `lemma_6_11` consumes): the equivariant
`𝔽₂[P]`-freeness `sylow_free_of_ramified` yields an equivariant split pair — take `j := φ`,
`q := φ⁻¹`.  Retraction equivariance is `φ`'s equivariance transported across the iso
(`φ⁻¹`-inject, then `φ`'s equivariance at `φ⁻¹ F`), and `q ∘ j = id` is `φ⁻¹ ∘ φ = id`. -/
theorem sylow_split_pair_of_ramified_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) (P : Sylow 2 C) :
    ∃ (r : ℕ) (j : V →+ (Fin r → ↥(P : Subgroup C) → ZMod 2))
      (q : (Fin r → ↥(P : Subgroup C) → ZMod 2) →+ V),
      (∀ (p : ↥(P : Subgroup C)) (v : V) (n : Fin r) (x : ↥(P : Subgroup C)),
        j ((p : C) • v) n x = j v n (p⁻¹ * x)) ∧
      (∀ (p : ↥(P : Subgroup C)) (F : Fin r → ↥(P : Subgroup C) → ZMod 2),
        q (fun n x => F n (p⁻¹ * x)) = (p : C) • q F) ∧
      ∀ v : V, q (j v) = v := by
  obtain ⟨r, φ, hφ⟩ := sylow_free_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  refine ⟨r, φ.toAddMonoidHom, φ.symm.toAddMonoidHom, ?_, ?_, ?_⟩
  · intro p v n x
    exact hφ p v n x
  · intro p F
    show φ.symm (fun n x => F n (p⁻¹ * x)) = (p : C) • φ.symm F
    refine φ.injective ?_
    rw [AddEquiv.apply_symm_apply]
    funext n x
    have hpx := hφ p (φ.symm F) n x
    rw [AddEquiv.apply_symm_apply] at hpx
    exact hpx.symm
  · intro v
    exact φ.symm_apply_apply v


/-- **Lemma 6.11, abstract tame-pair form** (P-17e5 statement alignment — resolves the banked
e5 design flag): the split-summand package from a generating pair `(sg, t)` with the tame
relation, rather than a `Ttame`-marking.  This is the form the κ⁰ assembly consumes
(`ActsThroughTame` supplies exactly such a pair); the `Ttame` form below is a wrapper. -/
theorem lemma_6_11_of_tame_pair {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    {sg t : C} (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ 2)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 C) := inferInstance
  haveI : (P : Subgroup C).FiniteIndex := ⟨Subgroup.index_ne_zero_of_finite⟩
  have hodd : Odd (P : Subgroup C).index := by
    have h2 : ¬ (2 : ℕ) ∣ (P : Subgroup C).index := Sylow.not_dvd_index P
    rcases Nat.even_or_odd (P : Subgroup C).index with he | ho
    · exact absurd he.two_dvd h2
    · exact ho
  obtain ⟨r, j, q, hj, hq, hqj⟩ :=
    sylow_split_pair_of_ramified_of_tame_pair hgen hrel hV2 hfaith hsimple hram P
  exact regular_summand_of_subgroup_summand hV2 (P : Subgroup C) hodd j q hj hq hqj

/-- **Lemma 6.11 (paper node, §6.3)**: a ramified simple faithful 2-torsion module over the
tame image is an equivariant split summand of a regular module.  The regular module `𝔽₂[C]^N`
is `Fin N → C → ZMod 2` with the left-translation action written inline; `ι` is the
equivariant embedding, `r` the equivariant retraction.

**Proved (P-17e4, std-3, no `sorry`)**: the odd-index relative trace
`regular_summand_of_subgroup_summand` at a Sylow 2-subgroup (`Sylow.not_dvd_index` gives the
odd index) composed with the weight-orbit kernel `sylow_split_pair_of_ramified` above.

From this the deep-count multiplicativity (`Hom(V^∨, −)`-exactness) follows —
`equivariant_lift_of_regular_summand` below — which is the sole remaining input to
`lemma_6_17_dim`'s lower bound `#X₊ ≥ 2^m`.  Applied at `V := V^∨` (also ramified simple
faithful) by the consumer. -/
theorem lemma_6_11 {C : Type} [Group C] [TopologicalSpace C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (c : ContinuousMonoidHom Ttame C)
    (hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v := by
  have hrel : (c tameSigma)⁻¹ * c tameTau * c tameSigma = c tameTau ^ 2 := by
    have h := congrArg (⇑c) tame_relation
    simpa only [conjP, map_mul, map_inv, map_pow] using h
  exact lemma_6_11_of_tame_pair hgen hrel hV2 hfaith hsimple hram

/-! ## The consequence: equivariant lifting (`Hom(V, −)`-exactness)

Proved from the summand package fields alone; consumers apply it to the `lemma_6_11` output
(now itself std-3, so the whole chain is `sorryAx`-free).  This is the "deep-count
multiplicativity" input of `docs/p15f1-dimcount-scoping.md` §2: every equivariant map out of
`V` lifts along equivariant surjections. -/

section EquivariantLift

variable {C : Type} [Group C]
variable {V W W' : Type} [AddCommGroup V] [AddCommGroup W] [AddCommGroup W']
  [DistribMulAction C V] [DistribMulAction C W] [DistribMulAction C W']

open scoped Classical

/-- The `(n, x)`-indicator basis vector of the regular module `Fin N → C → ZMod 2`. -/
noncomputable def regBasis (N : ℕ) (n : Fin N) (x : C) : Fin N → C → ZMod 2 :=
  fun m y => if m = n ∧ y = x then 1 else 0

omit [Group C] in
/-- Every element of the regular module is the sum of its coordinates against `regBasis`. -/
theorem regBasis_decomp [Fintype C] {N : ℕ} (F : Fin N → C → ZMod 2) :
    F = ∑ n : Fin N, ∑ x : C, F n x • regBasis N n x := by
  funext m y
  have happ : (∑ n : Fin N, ∑ x : C, F n x • regBasis N n x) m y
      = ∑ n : Fin N, ∑ x : C, (if m = n ∧ y = x then F n x else 0) := by
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    show F n x • (if m = n ∧ y = x then (1 : ZMod 2) else 0) = _
    by_cases h : m = n ∧ y = x
    · rw [if_pos h, if_pos h, smul_eq_mul, mul_one]
    · rw [if_neg h, if_neg h, smul_eq_mul, mul_zero]
  rw [happ]
  have hinner : ∀ n : Fin N,
      (∑ x : C, if m = n ∧ y = x then F n x else 0) = if m = n then F n y else 0 := by
    intro n
    by_cases hmn : m = n
    · simp only [hmn, true_and, if_true]
      rw [Finset.sum_ite_eq Finset.univ y (fun x => F n x), if_pos (Finset.mem_univ y)]
    · simp only [hmn, false_and, if_false]
      exact Finset.sum_const_zero
  rw [Finset.sum_congr rfl fun n _ => hinner n,
    Finset.sum_ite_eq Finset.univ m (fun n => F n y), if_pos (Finset.mem_univ m)]

/-- Left translation carries `regBasis N n x` to `regBasis N n (h·x)`. -/
theorem regBasis_translate {N : ℕ} (h : C) (n : Fin N) (x : C) :
    (fun (m : Fin N) (y : C) => regBasis N n x m (h⁻¹ * y)) = regBasis N n (h * x) := by
  funext m y
  show (if m = n ∧ h⁻¹ * y = x then (1 : ZMod 2) else 0)
    = if m = n ∧ y = h * x then 1 else 0
  refine if_congr (and_congr_right fun _ => ?_) rfl rfl
  exact inv_mul_eq_iff_eq_mul

/-- **Equivariant lifting along an equivariant surjection, from a regular-summand package**
(the `Hom(V, −)`-exactness consequence of Lemma 6.11; itself sorry-free — `sorryAx` enters a
consumer's audit only when the package is produced by `lemma_6_11`).  `W`, `W'` are 2-torsion
(all consumers are). -/
theorem equivariant_lift_of_regular_summand [Finite C]
    (h2W : ∀ w : W, w + w = 0) (h2W' : ∀ w : W', w + w = 0)
    {N : ℕ} (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V)
    (hι : ∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x))
    (hr : ∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F)
    (hri : ∀ v : V, r (ι v) = v)
    (π : W →+ W') (hπeq : ∀ (h : C) (w : W), π (h • w) = h • π w)
    (hπ : Function.Surjective ⇑π)
    (f : V →+ W') (hfeq : ∀ (h : C) (v : V), f (h • v) = h • f v) :
    ∃ g : V →+ W, (∀ (h : C) (v : V), g (h • v) = h • g v) ∧ ∀ v : V, π (g v) = f v := by
  have hz2 : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  haveI : Fintype C := Fintype.ofFinite C
  haveI : Module (ZMod 2) W := AddCommGroup.zmodModule (fun w => by
    rw [two_nsmul]; exact h2W w)
  haveI : Module (ZMod 2) W' := AddCommGroup.zmodModule (fun w => by
    rw [two_nsmul]; exact h2W' w)
  have hsmul_comm : ∀ (h : C) (z : ZMod 2) (u : W), h • (z • u) = z • (h • u) := by
    intro h z u
    rcases hz2 z with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, smul_zero]
    · rw [one_smul, one_smul]
  have hπz : ∀ (z : ZMod 2) (u : W), π (z • u) = z • π u := by
    intro z u
    rcases hz2 z with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
  -- `f` transported to the regular module.
  set f' : (Fin N → C → ZMod 2) →+ W' := f.comp r with hf'def
  have hf'eq : ∀ (h : C) (B : Fin N → C → ZMod 2),
      f' (fun n x => B n (h⁻¹ * x)) = h • f' B := by
    intro h B
    show f (r fun n x => B n (h⁻¹ * x)) = h • f (r B)
    rw [hr, hfeq]
  -- choose lifts of the values on the identity-based basis vectors.
  choose w hw using fun n : Fin N => hπ (f' (regBasis N n 1))
  -- the lifted map on the regular module: `G F = Σ_{n,x} F n x • (x • w n)`.
  set G : (Fin N → C → ZMod 2) →+ W := AddMonoidHom.mk'
    (fun F => ∑ n : Fin N, ∑ x : C, F n x • (x • w n))
    (fun F F' => by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun x _ => ?_
      show ((F + F') n x) • (x • w n) = _
      show (F n x + F' n x) • (x • w n) = _
      rw [add_smul]) with hGdef
  have hGval : ∀ F : Fin N → C → ZMod 2,
      G F = ∑ n : Fin N, ∑ x : C, F n x • (x • w n) := fun _ => rfl
  -- `G` is equivariant.
  have hGeq : ∀ (h : C) (F : Fin N → C → ZMod 2),
      G (fun n x => F n (h⁻¹ * x)) = h • G F := by
    intro h F
    rw [hGval, hGval, Finset.smul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    calc (∑ x : C, F n (h⁻¹ * x) • (x • w n))
        = ∑ x : C, F n (h⁻¹ * (h * x)) • ((h * x) • w n) :=
          (Equiv.sum_comp (Equiv.mulLeft h)
            (fun x : C => F n (h⁻¹ * x) • (x • w n))).symm
      _ = ∑ x : C, F n x • ((h * x) • w n) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [inv_mul_cancel_left]
      _ = ∑ x : C, h • (F n x • (x • w n)) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_smul, hsmul_comm]
      _ = h • ∑ x : C, F n x • (x • w n) := (Finset.smul_sum).symm
  -- `π ∘ G = f'` (via the basis decomposition).
  have hπG : ∀ F : Fin N → C → ZMod 2, π (G F) = f' F := by
    intro F
    have hval : π (G F) = ∑ n : Fin N, ∑ x : C, F n x • f' (regBasis N n x) := by
      rw [hGval, map_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [map_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hπz, hπeq, hw]
      congr 1
      have htr : (fun (m : Fin N) (y : C) => regBasis N n 1 m (x⁻¹ * y))
          = regBasis N n x := by
        have h1 := regBasis_translate (C := C) x n 1
        rwa [mul_one] at h1
      rw [← hf'eq x (regBasis N n 1), htr]
    rw [hval]
    conv_rhs => rw [regBasis_decomp (C := C) F]
    rw [map_sum]
    refine (Finset.sum_congr rfl fun n _ => ?_)
    rw [map_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rcases hz2 (F n x) with hz | hz <;> rw [hz]
    · rw [zero_smul, zero_smul, map_zero]
    · rw [one_smul, one_smul]
  -- assemble `g = G ∘ ι`.
  refine ⟨G.comp ι, fun h v => ?_, fun v => ?_⟩
  · show G (ι (h • v)) = h • G (ι v)
    have hιfun : ι (h • v) = fun n x => ι v n (h⁻¹ * x) := by
      funext n x
      exact hι h v n x
    rw [hιfun, hGeq]
  · show π (G (ι v)) = f v
    rw [hπG]
    show f (r (ι v)) = f v
    rw [hri]

end EquivariantLift

end GQ2
