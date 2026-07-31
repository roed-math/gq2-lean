/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionNine.Induction
import GQ2.Dyadic.Projectivity

/-!
# SEAM B: the κ⁰ base class at a general residue cardinality (ticket SD-R2)

**This file discharges SEAM B**, reported by SD-R1 in `GQ2/Dyadic/Recursion/Block.lean` and
threaded there as the six `hrel2`/`hrel2HV` binders of the Block productions (now removed).

The seam: `GQ2.SectionNine.ActsThroughTame` (`GQ2/SectionNine/Induction.lean:155`) puts the
tame relation `s⁻¹ * t * s = t ^ 2` **literally in its definition** (:160), and `kappa0_exists`
(:196) forwards it to `GQ2.kappa0_exists_tame` (`GQ2/KappaNormalForm.lean:1150`), whose
signature demands the same.  At a general residue cardinality the head's tame pair satisfies
`= t ^ q` (`GQ2.Dyadic.tame_rel_map_q`, and at the `H_V` level `GQ2.Dyadic.hv_relK`), so no
`K`-side head can meet the exponent-2 clause when `q ≠ 2`.

## The discharge

`ActsThroughTameQ q` (below) is the general-`q` predicate — the model's definition with `t ^ 2`
replaced by `t ^ q`; the frozen `ActsThroughTame` is **untouched**, and at `q = 2` the two are
*syntactically* identical (`actsThroughTameQ_two : ActsThroughTameQ 2 C V = ActsThroughTame C V`
is `rfl`).  `kappa0_exists_tameK` and `kappa0_existsK` are the corresponding clones.

The mathematics costs nothing, because PJ1 already de-fanged the deep half: the thousand lines
below `GQ2.lemma_6_11_of_tame_pair` consume the relation only through the two facts

* `(Subgroup.zpowers t).Normal` — the inertia is normal in the image, and
* `Odd (orderOf t)` — the inertia has odd order,

which `GQ2/Dyadic/Projectivity.lean` supplies at general `q` (`tame_zpowers_normal_pow`,
`tame_odd_order_pow`).  So `kappa0_exists_tameK` is `GQ2.kappa0_exists_tame` verbatim with
**exactly three changes** (SD-R1's assessment, confirmed): the `hrel'` exponent transport
(model :1204-1206) and the two callee swaps

| model call | `K`-side call |
|---|---|
| `lemma_6_11_of_tame_pair hgen' hrel' …` (:1218) | `lemma_6_11_of_tame_pairK hq0 hqe hgen' hrel' …` |
| `two_torsion_of_centralizer_eq_one hgen' hrel' …` (:1267) | `two_torsion_of_centralizer_eq_oneK hgen' hrel' …` |

⚠ Route note (the adopted depth assessment's caution, honored): the two `K`-side wrappers go
through `GQ2.lemma_6_11_of_odd_normal` / `GQ2.two_torsion_of_centralizer_eq_one_of_normal` plus
the two general-`q` leaves — **not** through `GQ2.Dyadic.lemma_6_11_of_tame_pair_pow`, which is
pinned at `q = 2 ^ f` with `1 ≤ f` rather than at `Even q ∧ q ≠ 0`.

Note the normality wrapper needs **no** hypothesis on `q` at all (`tame_zpowers_normal_pow` is
unconditional), so `two_torsion_of_centralizer_eq_oneK` is hypothesis-free in `q`; only the
odd-order leaf wants `q ≠ 0` and `Even q`.

## Copied `private` helpers

Four helpers of the model proof are `private` in `GQ2/KappaNormalForm.lean` and hence not
referenceable.  Two have public twins that are used instead — `datum_comapHom` (:302) is
`GQ2.SectionNine.IsEquivariantFactorSet.comapHom` and `datum_of_split` (:324) is three lines
over the public `GQ2.datum_comap` (:273).  The other two are copied verbatim below with a `K`
suffix: `two_torsion_of_nonsingular_simpleK` (:1080) and `datum_of_oddK` (:394), the latter
with its own private dependency `exists_biadditive_refinementK` (:354).  All four are
degree-blind — they never see the relation exponent.

Plain-import (memo §5).

Axioms: none beyond std-3.  Print check performed for every declaration in this file: each
prints `[propext, Classical.choice, Quot.sound]`, equal to its model's print
(`GQ2.kappa0_exists_tame`, `GQ2.SectionNine.kappa0_exists`) — hence a subset.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionNine QuadraticFp2

/-! ## The two exponent-carrying wrappers, at general `q`

`GQ2.lemma_6_11_of_tame_pair` (`GQ2/RegularSummand/Involution.lean:754`) and
`GQ2.two_torsion_of_centralizer_eq_one` (:265) are the only two places where
`kappa0_exists_tame` touches the relation.  Both are thin wrappers over exponent-free
`…_of_odd_normal` forms, so the general-`q` siblings are one application each. -/

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [DistribMulAction C V]

/-- **The `O₂`-linchpin at a general residue cardinality.**  General-`q` sibling of
`GQ2.two_torsion_of_centralizer_eq_one` (`GQ2/RegularSummand/Involution.lean:265`): an
involution centralizing the inertia of a tame pair acts trivially on a faithful simple
2-torsion module, hence is trivial.

No hypothesis on `q` is needed — `GQ2.Dyadic.tame_zpowers_normal_pow` is unconditional. -/
theorem two_torsion_of_centralizer_eq_oneK [Finite V] {sg t : C} {q : ℕ}
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ q)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV0 : ∃ v₀ : V, v₀ ≠ (0 : V))
    {x : C} (hx2 : x ^ 2 = 1) (hxt : x * t = t * x) : x = 1 :=
  two_torsion_of_centralizer_eq_one_of_normal hgen (tame_zpowers_normal_pow hgen hrel)
    hV2 hfaith hsimple hV0 hx2 hxt

/-- **Lemma 6.11 at a general residue cardinality**, tame-pair form.  General-`q` sibling of
`GQ2.lemma_6_11_of_tame_pair` (`GQ2/RegularSummand/Involution.lean:754`): a faithful ramified
simple 2-torsion module over a group generated by a tame pair at `sg⁻¹ t sg = t ^ q` is an
equivariant split summand of a regular module.

This is **not** `GQ2.Dyadic.lemma_6_11_of_tame_pair_pow`: that one is pinned at `q = 2 ^ f`
with `1 ≤ f`, whereas the `K`-side spine carries `Even q ∧ q ≠ 0`.  Both are two-leaf
corollaries of the same `GQ2.lemma_6_11_of_odd_normal`. -/
theorem lemma_6_11_of_tame_pairK [Finite V] {sg t : C} {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (hgen : Subgroup.closure {sg, t} = ⊤) (hrel : sg⁻¹ * t * sg = t ^ q)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, t • v ≠ v) :
    ∃ (N : ℕ) (ι : V →+ (Fin N → C → ZMod 2)) (r : (Fin N → C → ZMod 2) →+ V),
      (∀ (h : C) (v : V) (n : Fin N) (x : C), ι (h • v) n x = ι v n (h⁻¹ * x)) ∧
      (∀ (h : C) (F : Fin N → C → ZMod 2), r (fun n x => F n (h⁻¹ * x)) = h • r F) ∧
      ∀ v : V, r (ι v) = v :=
  lemma_6_11_of_odd_normal hgen (tame_zpowers_normal_pow hgen hrel)
    (tame_odd_order_pow (orderOf_pos sg).ne' hq0 hqe hrel) hV2 hfaith hsimple hram

/-! ## The two copied `private` helpers of the model proof

Both are degree-blind: they never mention the relation, let alone its exponent.  Copied
verbatim from `GQ2/KappaNormalForm.lean` because `private` puts them out of reach (the
`GQ2/Dyadic/Recursion/BlockHeadDat.lean` precedent). -/

/-- **2-torsion from simplicity + nonsingularity.**  Copy of the `private`
`two_torsion_of_nonsingular_simple` (`GQ2/KappaNormalForm.lean:1080`) — verbatim. -/
private theorem two_torsion_of_nonsingular_simpleK {H : Type} [Group H] {V : Type}
    [AddCommGroup V] [Finite V] [Nontrivial V] [DistribMulAction H V] {q : V → ZMod 2}
    (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∀ v : V, v + v = 0 := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype V := Fintype.ofFinite V
  set W₂ : AddSubgroup V :=
    { carrier := {v : V | v + v = 0}
      zero_mem' := by rw [Set.mem_setOf_eq, add_zero]
      add_mem' := fun {a b} ha hb => by
        rw [Set.mem_setOf_eq] at ha hb ⊢
        calc a + b + (a + b) = (a + a) + (b + b) := by abel
          _ = 0 := by rw [ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        rw [Set.mem_setOf_eq] at ha ⊢
        rw [← neg_add, ha, neg_zero] } with hW₂
  have hstable : ∀ (g : H) (w : V), w ∈ W₂ → g • w ∈ W₂ := by
    intro g w hw
    show g • w + g • w = 0
    rw [← smul_add, (hw : w + w = 0), smul_zero]
  rcases hsimple W₂ hstable with hbot | htop
  · -- no 2-torsion ⟹ |V| odd ⟹ all polar pairings vanish, against nonsingularity
    exfalso
    have hodd : Odd (Fintype.card V) := by
      rw [← Nat.not_even_iff_odd]
      intro heven
      obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card 2 heven.two_dvd
      have ha2 : a + a = 0 := by
        have h1 : (2 : ℕ) • a = 0 := by
          rw [← ha]
          exact addOrderOf_nsmul_eq_zero a
        rwa [two_nsmul] at h1
      have ha0 : a ≠ 0 := by
        intro h
        rw [h, addOrderOf_zero] at ha
        omega
      have : a ∈ W₂ := ha2
      rw [hbot, AddSubgroup.mem_bot] at this
      exact ha0 this
    obtain ⟨v₀, hv₀⟩ := exists_ne (0 : V)
    obtain ⟨w, hw⟩ := hns v₀ hv₀
    set ψ : V →+ ZMod 2 := AddMonoidHom.mk' (fun w' => polar q v₀ w')
      (fun w' w'' => hq.polar_add_right v₀ w' w'') with hψ
    have hcard : Fintype.card V • w = 0 := card_nsmul_eq_zero
    have h0 : ψ w = 0 := by
      have h1 : Fintype.card V • ψ w = ψ (Fintype.card V • w) := (map_nsmul ψ _ _).symm
      rw [hcard, map_zero] at h1
      have hc1 : (Fintype.card V : ZMod 2) = 1 := by
        obtain ⟨k, hk⟩ := hodd
        rw [hk]
        push_cast
        linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      rwa [nsmul_eq_mul, hc1, one_mul] at h1
    exact hw h0
  · intro v
    exact (htop ▸ AddSubgroup.mem_top v : v ∈ W₂)

/-- Copy of the `private` `exists_biadditive_refinement'` (`GQ2/KappaNormalForm.lean:354`) —
verbatim.  A 2-torsion `𝔽₂`-quadratic map has a biadditive refinement (a bilinear form whose
diagonal is the form), obtained from a basis via `QuadraticMap.toBilin`. -/
private theorem exists_biadditive_refinementK {V : Type*} [AddCommGroup V] [Finite V]
    (h2 : ∀ v : V, v + v = 0) (q : V → ZMod 2) (hq : IsQuadraticFp2 q) :
    ∃ f : V → V → ZMod 2, (∀ v v' w : V, f (v + v') w = f v w + f v' w)
      ∧ (∀ v w w' : V, f v (w + w') = f v w + f v w') ∧ (∀ v, f v v = q v) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by rw [two_nsmul]; exact h2 v)
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hsmul : ∀ (a : ZMod 2) (x : V), q (a • x) = (a * a) • q x := by
    intro a x
    rcases ZMod.eq_zero_or_eq_one a with rfl | rfl
    · simp [hq.map_zero]
    · simp
  have hcomp0 : ∀ x y : V, q (x + y) = q x + q y + polar q x y := by
    intro x y
    simp only [polar]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
  let Bil : LinearMap.BilinForm (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w')))
        (fun v v' => by
          ext w
          simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply,
            LinearMap.add_apply]
          exact hq.polar_add_left v v' w))
  have hBilapp : ∀ v w, Bil v w = polar q v w := fun v w => rfl
  let Qm : QuadraticMap (ZMod 2) V (ZMod 2) :=
    { toFun := q
      toFun_smul := hsmul
      exists_companion' := ⟨Bil, fun x y => by rw [hBilapp]; exact hcomp0 x y⟩ }
  let bm := Module.finBasis (ZMod 2) V
  refine ⟨fun v w => Qm.toBilin bm v w, fun v v' w => ?_, fun v w w' => ?_, fun v => ?_⟩
  · simp only [map_add, LinearMap.add_apply]
  · simp only [map_add]
  · show Qm.toBilin bm v v = q v
    exact DFunLike.congr_fun (QuadraticMap.toQuadraticMap_toBilin Qm bm) v

/-- The odd/unramified branch: copy of the `private` `datum_of_odd`
(`GQ2/KappaNormalForm.lean:394`) — verbatim.  Averaging a biadditive refinement over an
odd-order group produces an invariant biadditive factor set. -/
private theorem datum_of_oddK {H : Type*} [Group H] [Finite H] (hodd : Odd (Nat.card H))
    {V : Type*} [AddCommGroup V] [Finite V] [DistribMulAction H V] (h2 : ∀ v : V, v + v = 0)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant H q) :
    ∃ dat : FactorSet H V, IsEquivariantFactorSet q dat := by
  haveI : Fintype H := Fintype.ofFinite H
  obtain ⟨f₀, hl₀, hr₀, hdiag₀⟩ := exists_biadditive_refinementK h2 q hq
  have hinv' : ∀ (c : H) (x : V), q (c • x) = q x := hinv
  have oddsmul : ∀ x : ZMod 2, Fintype.card H • x = x := by
    intro x
    have hc1 : (Fintype.card H : ZMod 2) = 1 := by
      have hodd' : Odd (Fintype.card H) := by rwa [Nat.card_eq_fintype_card] at hodd
      obtain ⟨k, hk⟩ := hodd'
      rw [hk]
      push_cast
      rw [show (2 : ZMod 2) = 0 by decide]
      ring
    rw [nsmul_eq_mul, hc1, one_mul]
  refine ⟨⟨fun v w => ∑ h : H, f₀ (h • v) (h • w), fun _ _ => 0⟩,
    datum_of_biadditive_invariant ?_ ?_ ?_ ?_⟩
  · intro v v' w
    simp only [smul_add, hl₀]
    exact Finset.sum_add_distrib
  · intro v w w'
    simp only [smul_add, hr₀]
    exact Finset.sum_add_distrib
  · intro v
    have step : ∀ h : H, f₀ (h • v) (h • v) = q v := fun h => (hdiag₀ (h • v)).trans (hinv' h v)
    simp only [step, Finset.sum_const, Finset.card_univ]
    exact oddsmul (q v)
  · intro g v w
    simp only [← mul_smul]
    exact Fintype.sum_equiv (Equiv.mulRight g) _ _ (fun x => rfl)

/-! ## κ⁰ existence at a general residue cardinality -/

/-- **κ⁰ existence over a finite tame-generated group at a general residue cardinality**
(paper Lemma 6.3).  Clone of `GQ2.kappa0_exists_tame` (`GQ2/KappaNormalForm.lean:1150`) with
`hrel : s⁻¹ * t * s = t ^ q` in place of the exponent-2 clause, under `q ≠ 0`, `Even q`.

The proof is the model's verbatim except for the three changes tabulated in the module
docstring; the quadratic map is renamed `qf` because `q` is the residue cardinality in this
subtree's naming scheme. -/
theorem kappa0_exists_tameK {H : Type} [Group H] [Finite H]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction H V]
    {s t : H} {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    (hgen : Subgroup.closure {s, t} = ⊤) (hrel : s⁻¹ * t * s = t ^ q)
    (qf : V → ZMod 2) (hq : IsQuadraticFp2 qf) (hns : Nonsingular qf)
    (hinv : IsInvariant H qf) (hnt : Nontrivial V)
    (hsimple : ∀ W : AddSubgroup V, (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤) :
    ∃ dat : FactorSet H V, IsEquivariantFactorSet qf dat := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype V := Fintype.ofFinite V
  -- V is 2-torsion: the 2-torsion subgroup is stable, and `⊥` contradicts nonsingularity
  have hV2 : ∀ v : V, v + v = 0 := two_torsion_of_nonsingular_simpleK hq hns hsimple
  -- the faithful image Ĥ ≤ Perm V, with the tautological (distributive) action
  set α : H →* Equiv.Perm V := MulAction.toPermHom H V with hα
  haveI hfin : Finite ↥α.range := by
    have h1 : (Set.range ⇑α).Finite := Set.finite_range ⇑α
    exact h1.to_subtype
  letI actR : DistribMulAction ↥α.range V :=
    { smul := fun g v => (g : Equiv.Perm V) v
      one_smul := fun v => rfl
      mul_smul := fun g h v => rfl
      smul_zero := fun g => by
        obtain ⟨h, hh⟩ := g.2
        show (g : Equiv.Perm V) 0 = 0
        rw [← hh]
        exact smul_zero h
      smul_add := fun g v w => by
        obtain ⟨h, hh⟩ := g.2
        show (g : Equiv.Perm V) (v + w) = (g : Equiv.Perm V) v + (g : Equiv.Perm V) w
        rw [← hh]
        exact smul_add h v w }
  set πh : H →* ↥α.range := α.rangeRestrict with hπh
  have hπhsurj : Function.Surjective πh := α.rangeRestrict_surjective
  have hcompat : ∀ (h : H) (v : V), h • v = πh h • v := fun h v => rfl
  -- transported data over the faithful image
  have hinv' : IsInvariant ↥α.range qf := by
    intro c v
    obtain ⟨h, rfl⟩ := hπhsurj c
    rw [← hcompat, hinv]
  have hsimple' : ∀ W : AddSubgroup V,
      (∀ (g : ↥α.range), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hsimple W fun g w hw => ?_
    rw [hcompat]
    exact hW (πh g) w hw
  have hfaith' : ∀ g : ↥α.range, (∀ v : V, g • v = v) → g = 1 := by
    intro g hg
    have h1 : (g : Equiv.Perm V) = 1 := Equiv.ext fun v => hg v
    exact Subtype.ext h1
  have hgen' : Subgroup.closure {πh s, πh t} = ⊤ := by
    have himg : Subgroup.closure (⇑πh '' ({s, t} : Set H)) = ⊤ := by
      rw [← MonoidHom.map_closure, hgen]
      exact Subgroup.map_top_of_surjective _ hπhsurj
    rwa [Set.image_insert_eq, Set.image_singleton] at himg
  -- CHANGE 1 (model :1204-1206): the exponent transport is at `q`, not at `2`
  have hrel' : (πh s)⁻¹ * πh t * πh s = πh t ^ q := by
    rw [← map_inv, ← map_mul, ← map_mul, ← map_pow]
    exact congrArg πh hrel
  -- a datum over the faithful image pulls back along `πh`
  suffices hdat' : ∃ dat : FactorSet ↥α.range V, IsEquivariantFactorSet qf dat by
    obtain ⟨dat, hdat⟩ := hdat'
    exact ⟨_, IsEquivariantFactorSet.comapHom hdat πh hcompat⟩
  -- dichotomy on the inertia action
  by_cases hram : ∃ v : V, πh t • v ≠ v
  · -- ramified: split-embed into the permutation module and use the normal form
    have hsimple'' : ∀ W : AddSubgroup V,
        (∀ (h : ↥α.range), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
      hsimple' W fun g w hw => hW g w hw
    -- CHANGE 2 (model :1218): the general-`q` sibling of `lemma_6_11_of_tame_pair`
    obtain ⟨N, ι, ret, hι, hret, hretr⟩ :=
      lemma_6_11_of_tame_pairK hq0 hqe hgen' hrel' hV2 hfaith' hsimple'' hram
    -- the split pair lands in `PermW ↥α.range N` (definitionally)
    have hιinst : ∀ (c : ↥α.range) (v : V), ι (c • v) = c • ι v := by
      intro c v
      funext n x
      rw [hι c v n x]
      rfl
    set qW : PermW ↥α.range N → ZMod 2 := fun F => qf (ret F) with hqW
    have hqWquad : IsQuadraticFp2 qW := by
      constructor
      · show qf (ret 0) = 0
        rw [map_zero, hq.map_zero]
      · intro a b c
        show polar _ _ _ = polar _ _ _ + polar _ _ _
        simp only [hqW, polar, map_add]
        exact hq.polar_add_left (ret a) (ret b) (ret c)
      · intro a b c
        show polar _ _ _ = polar _ _ _ + polar _ _ _
        simp only [hqW, polar, map_add]
        exact hq.polar_add_right (ret a) (ret b) (ret c)
    have hqWinv : IsInvariant ↥α.range qW := by
      intro c F
      show qf (ret (c • F)) = qf (ret F)
      have h1 : ret (c • F) = c • ret F := hret c F
      rw [h1, hinv']
    obtain ⟨datW, hdatW⟩ := exists_datum_of_invariant_quadratic qW hqWquad hqWinv
    -- `datum_of_split` is `private`; this is its three-line body over the public `datum_comap`
    refine ⟨datW.comap ι, ?_⟩
    have hpb := datum_comap hdatW ι hιinst
    rwa [show (fun v => qW (ι v)) = qf from funext fun v => by
      show qf (ret (ι v)) = qf v
      rw [hretr v]] at hpb
  · -- unramified: `t̂ = 1`, the group has odd order, average
    have hram' : ∀ v : V, πh t • v = v := by
      intro v
      by_contra hv
      exact hram ⟨v, hv⟩
    have ht1 : πh t = 1 := hfaith' (πh t) hram'
    have hodd : Odd (Nat.card ↥α.range) := by
      haveI : Fintype ↥α.range := Fintype.ofFinite _
      rw [Nat.card_eq_fintype_card, ← Nat.not_even_iff_odd]
      intro heven
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card 2 heven.two_dvd
      have hz2 : z ^ 2 = 1 := by
        rw [← hz]
        exact pow_orderOf_eq_one z
      have hzt : z * πh t = πh t * z := by
        rw [ht1, mul_one, one_mul]
      have hsimple'' : ∀ W : AddSubgroup V,
          (∀ (h : ↥α.range), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤ := fun W hW =>
        hsimple' W fun g w hw => hW g w hw
      -- CHANGE 3 (model :1267): the general-`q` sibling of `two_torsion_of_centralizer_eq_one`
      have hz1 : z = 1 :=
        two_torsion_of_centralizer_eq_oneK hgen' hrel' hV2 hfaith' hsimple''
          (exists_ne (0 : V)) hz2 hzt
      rw [hz1, orderOf_one] at hz
      omega
    exact datum_of_oddK hodd hV2 qf hq hinv'

/-! ## The general-`q` `ActsThroughTame` predicate and the κ⁰ existential -/

/-- **The `C`-action on `V` factors through a finite tame group at residue cardinality `q`.**
Clone of `GQ2.SectionNine.ActsThroughTame` (`GQ2/SectionNine/Induction.lean:155`) with the
literal `t ^ 2` clause replaced by `t ^ q`; the frozen `ℚ₂` definition is untouched.

At `q = 2` this **is** the model's predicate, syntactically (`actsThroughTameQ_two`). -/
def ActsThroughTameQ (q : ℕ) (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (_ : DistribMulAction H V)
    (π : C →* H) (s t : H),
    Function.Surjective π ∧ (∀ (c : C) (v : V), c • v = π c • v) ∧
    Subgroup.closure {s, t} = ⊤ ∧ s⁻¹ * t * s = t ^ q

/-- The `n = 1` refl-bridge for the predicate: at `q = 2` the general clause `t ^ q` **is** the
model's `t ^ 2` — `rfl`.  This is what keeps the `q = 2` instances of the Block productions
elaborating after the SEAM-B binders are removed. -/
theorem actsThroughTameQ_two (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : ActsThroughTameQ 2 C V = ActsThroughTame C V := rfl

/-- **Existence of the equivariant factor-set datum** (the base determinant class `κ⁰_q`) at a
general residue cardinality — the paper's Lemma 6.3.  Clone of
`GQ2.SectionNine.kappa0_exists` (`GQ2/SectionNine/Induction.lean:196`): the proof is verbatim,
with `ActsThroughTameQ q` unpacked in place of `ActsThroughTame` and `kappa0_exists_tameK` in
place of `GQ2.kappa0_exists_tame`.  The quadratic map is renamed `qf` (`q` is the residue
cardinality here). -/
theorem kappa0_existsK {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V] {q : ℕ}
    (hq0 : q ≠ 0) (hqe : Even q)
    (qf : V → ZMod 2) (hq : IsQuadraticFp2 qf) (hns : Nonsingular qf)
    (hinv : IsInvariant C qf) (hsimple : FoxH.IsSimpleModTwo C V)
    (htame : ActsThroughTameQ q C V) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet qf dat := by
  obtain ⟨H, hG, hF, hA, π, s, t, hπsurj, hπcompat, hgen, hrel⟩ := htame
  letI := hG
  letI := hF
  letI := hA
  -- transport invariance and simplicity along the surjection `π`
  have hinvH : IsInvariant H qf := by
    intro h v
    obtain ⟨c, rfl⟩ := hπsurj h
    rw [← hπcompat, hinv]
  have hsimpleH : ∀ W : AddSubgroup V,
      (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hsimple.2 W fun g w hw => ?_
    rw [hπcompat]
    exact hW (π g) w hw
  obtain ⟨dat, hdat⟩ :=
    kappa0_exists_tameK hq0 hqe hgen hrel qf hq hns hinvH hsimple.1 hsimpleH
  exact ⟨_, IsEquivariantFactorSet.comapHom hdat π hπcompat⟩

end GQ2.Dyadic
