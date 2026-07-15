/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionSeven.Prop74Step1

/-!
# Module core of the `H_V` averaging: `(V∨)^C = 0`

Split off from `GQ2.SectionSeven`, building on `GQ2.SectionSeven.Prop74Step1`.  This file reduces
the block-module vanishing `(V∨)^C = 0` to pure group theory:

* the **(F1)** odd-order averaging core `avg_dual_zero` and its bridge, and the **(A)** simplicity
  lemma on the `Ctil`-fixed space;
* the **(P1)** normal-2-group counting lemmas on `V = P/S`;
* the **unramified** and **ramified** oddness lemmas feeding the `H_V` averaging.

See `GQ2.SectionSeven` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionSeven

open QuadraticFp2

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

variable {L : Subgroup Y}

/-! ### Module core of the `H_V` averaging (`(V∨)^C = 0`)

Two verified bricks that reduce the block-module vanishing to a pure group-theory statement:

* `avg_dual_zero` **(F1)** — the odd-order averaging: `V^C = 0 ⟹ (V∨)^C = 0`.
* `fixed_zero_of_moves` **(A)** — simplicity: a `Y`-normal `Ctil` that *moves* `V = P/S` has
  `V^C = 0`, since the `Ctil`-fixed space `fixSub` is `Y`-normal between `S` and `P`, so `chief`
  forces it to be `S`.

Together they reduce the block-module vanishing to producing an odd normal `Ctil` that moves `V`
(the tame construction, discharged by the case split in `hv_average_helper`). -/

/-- **(F1) averaging core** — for a finite odd-order group `C` acting on an `AddCommGroup V` via
`act : C → V →+ V` (anti-hom convention `act c' (act c v) = act (c*c') v`, matching `c⁻¹·k·c`
conjugation) with no nonzero fixed vector, every `C`-invariant functional `φ : V → 𝔽₂` vanishes.
The averaged vector `w = ∑_c act c v₀` is `C`-fixed and `φ w = |C| • φ v₀ = φ v₀` (odd), so a
nonzero `φ v₀` makes `w` a nonzero fixed vector — impossible.  (No Maschke needed.) -/
private theorem avg_dual_zero {C : Type*} [Group C] [Fintype C] {V : Type*} [AddCommGroup V]
    (act : C → V →+ V) (hactmul : ∀ (c c' : C) (v : V), act c' (act c v) = act (c * c') v)
    (hodd : Odd (Fintype.card C))
    (hfix : ∀ v : V, (∀ c : C, act c v = v) → v = 0)
    (φ : V →+ ZMod 2) (hφ : ∀ (c : C) (v : V), φ (act c v) = φ v)
    (v₀ : V) : φ v₀ = 0 := by
  classical
  set w := ∑ c : C, act c v₀ with hwdef
  have hwfix : ∀ c' : C, act c' w = w := by
    intro c'
    rw [hwdef, map_sum]
    have hstep : ∑ c : C, act c' (act c v₀) = ∑ c : C, act (c * c') v₀ :=
      Finset.sum_congr rfl (fun c _ => hactmul c c' v₀)
    rw [hstep]
    exact Equiv.sum_comp (Equiv.mulRight c') (fun c => act c v₀)
  have hw0 : w = 0 := hfix w hwfix
  have hcard : (Fintype.card C : ZMod 2) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]; push_cast
    rw [show (2 : ZMod 2) = 0 by decide, zero_mul, zero_add]
  have hφw : φ w = φ v₀ := by
    rw [hwdef, map_sum]
    have h1 : ∑ c : C, φ (act c v₀) = ∑ _c : C, φ v₀ :=
      Finset.sum_congr rfl (fun c _ => hφ c v₀)
    rw [h1, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard, one_mul]
  rw [hw0, map_zero] at hφw
  exact hφw.symm

/-- The `Ctil`-fixed space in `P/S`, pulled back to a subgroup of `Y` between `S` and `P`. -/
private def fixSub (S P Ctil : Subgroup Y) (hS : S.Normal) : Subgroup Y where
  carrier := {x | x ∈ P ∧ ∀ c, c ∈ Ctil → c⁻¹ * x * c * x⁻¹ ∈ S}
  one_mem' := by
    refine ⟨P.one_mem, fun c hc => ?_⟩
    simp
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    refine ⟨P.mul_mem haP hbP, fun c hc => ?_⟩
    have hsa := ha c hc
    have hsb := hb c hc
    have hrw : c⁻¹ * (a * b) * c * (a * b)⁻¹
        = (c⁻¹ * a * c * a⁻¹) * (a * (c⁻¹ * b * c * b⁻¹) * a⁻¹) := by group
    rw [hrw]
    exact S.mul_mem hsa (hS.conj_mem _ hsb a)
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨P.inv_mem haP, fun c hc => ?_⟩
    have hsa := ha c hc
    have hrw : c⁻¹ * a⁻¹ * c * (a⁻¹)⁻¹ = a⁻¹ * (c⁻¹ * a * c * a⁻¹)⁻¹ * a := by group
    rw [hrw]
    have := hS.conj_mem _ (S.inv_mem hsa) a⁻¹
    rwa [inv_inv] at this

omit [Finite Y] in
private theorem fixSub_normal (S P Ctil : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (hCtil : Ctil.Normal) : (fixSub S P Ctil hS).Normal := by
  constructor
  rintro a ⟨haP, ha⟩ y
  refine ⟨hP.conj_mem a haP y, fun c hc => ?_⟩
  have hc' : y⁻¹ * c * y ∈ Ctil := by
    have := hCtil.conj_mem c hc y⁻¹; rwa [inv_inv] at this
  have hrw : c⁻¹ * (y * a * y⁻¹) * c * (y * a * y⁻¹)⁻¹
      = y * ((y⁻¹ * c * y)⁻¹ * a * (y⁻¹ * c * y) * a⁻¹) * y⁻¹ := by group
  rw [hrw]
  exact hS.conj_mem _ (ha _ hc') y

omit [Finite Y] in
private theorem fixSub_S_le (S P Ctil : Subgroup Y) (hS : S.Normal) (hSP : S ≤ P) :
    S ≤ fixSub S P Ctil hS := by
  intro s hs
  refine ⟨hSP hs, fun c hc => ?_⟩
  have hcs : c⁻¹ * s * c ∈ S := by
    have := hS.conj_mem s hs c⁻¹; rwa [inv_inv] at this
  exact S.mul_mem hcs (S.inv_mem hs)

omit [Finite Y] in
/-- **(A)** simplicity: if `Ctil ◁ Y` moves `V = P/S` (some `c ∈ Ctil` moves some `p ∈ P` off
`S`), the chief condition forces `V^Ctil = 0` — any `k ∈ K` fixed by `Ctil` mod `S` lies in `S`. -/
theorem fixed_zero_of_moves (S P K Ctil : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (hCtil : Ctil.Normal) (hSP : S ≤ P) (hKP : K ≤ P)
    (chief : ∀ X : Subgroup Y, X.Normal → S ≤ X → X ≤ P → X = S ∨ X = P)
    (hmoves : ∃ p ∈ P, ∃ c ∈ Ctil, c⁻¹ * p * c * p⁻¹ ∉ S) :
    ∀ k, k ∈ K → (∀ c, c ∈ Ctil → c⁻¹ * k * c * k⁻¹ ∈ S) → k ∈ S := by
  set X := fixSub S P Ctil hS with hXdef
  have hXn : X.Normal := fixSub_normal S P Ctil hS hP hCtil
  have hSX : S ≤ X := fixSub_S_le S P Ctil hS hSP
  have hXP : X ≤ P := fun x hx => hx.1
  rcases chief X hXn hSX hXP with hXS | hXP'
  · intro k hk hkfix
    have hkX : k ∈ X := ⟨hKP hk, hkfix⟩
    rw [hXS] at hkX
    exact hkX
  · exfalso
    obtain ⟨p, hpP, c, hc, hmove⟩ := hmoves
    have hpX : p ∈ X := by rw [hXP']; exact hpP
    exact hmove (hpX.2 c hc)

/-- **(P1) count** — a normal 2-subgroup acting on `V = P/S` (nontrivial finite 2-group)
has a **nontrivial fixed coset**: `∃ p₁ ∈ P, p₁ ∉ S ∧ ∀ l ∈ L, l·p₁⁻¹·l⁻¹·p₁ ∈ S`.  The
same p-group fixed-point count (`IsPGroup.card_modEq_card_fixedPoints`) as
`exists_odd_moving_general`, but for the 2-group `L` directly. -/
private theorem exists_L_fixed_coset (S P L : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (hSP : S < P) (hP2 : IsPGroup 2 P) (hL2 : IsPGroup 2 L) :
    ∃ p₁ : Y, p₁ ∈ P ∧ p₁ ∉ S ∧ ∀ l, l ∈ L → l * p₁⁻¹ * l⁻¹ * p₁ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hSPn : (S.subgroupOf P).Normal := hS.subgroupOf P
  set Q := ↥P ⧸ S.subgroupOf P with hQdef
  set φ : Y →* Equiv.Perm Q := blockPerm S P hS hP with hφ
  have hval : ∀ (y : Y) (p : ↥P),
      (((conjHom P hP y p)⁻¹ * p : ↥P) : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y) := by
    intro y p
    show (y * (p : Y) * y⁻¹)⁻¹ * (p : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y)
    group
  have hfix_iff : ∀ (y : Y) (p : ↥P),
      φ y (QuotientGroup.mk p) = QuotientGroup.mk p ↔ y * (p : Y)⁻¹ * y⁻¹ * (p : Y) ∈ S := by
    intro y p
    rw [hφ, blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact Iff.of_eq (congrArg (· ∈ S) (hval y p))
  -- `V = P/S` is a nontrivial finite 2-group, so `2 ∣ card Q`
  haveI hQ2 : IsPGroup 2 Q := hP2.to_quotient (S.subgroupOf P)
  obtain ⟨p₀, hp₀P, hp₀S⟩ := SetLike.exists_of_lt hSP
  haveI hQnt : Nontrivial Q := by
    refine ⟨QuotientGroup.mk ⟨p₀, hp₀P⟩, 1, ?_⟩
    rw [ne_eq, QuotientGroup.eq_one_iff]
    exact fun hmem => hp₀S (Subgroup.mem_subgroupOf.mp hmem)
  have hcardQ : 2 ∣ Nat.card Q := by
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨k, hk⟩ := hQ2 q
    have hdvd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hne1 : orderOf q ≠ 1 := fun h => hq (orderOf_eq_one_iff.mp h)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := fun h0 => hne1 (by rw [hj, h0, pow_zero])
    exact (hj ▸ dvd_pow_self 2 hj0).trans (orderOf_dvd_natCard q)
  -- `L` acts on `Q` through `blockPerm`; it is a 2-group, so its fixed set is even
  letI : MulAction ↥L Q := MulAction.compHom Q (φ.comp L.subtype)
  have hmod := hL2.card_modEq_card_fixedPoints (α := Q)
  have hFPeven : 2 ∣ Nat.card (MulAction.fixedPoints ↥L Q) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hcardQ))
  -- `mk 1` is fixed
  have hFP1 : (QuotientGroup.mk 1 : Q) ∈ MulAction.fixedPoints ↥L Q := by
    intro l
    show φ (l : Y) (QuotientGroup.mk (1 : ↥P)) = QuotientGroup.mk 1
    rw [hfix_iff]
    simp
  have hFP2 : 2 ≤ Nat.card (MulAction.fixedPoints ↥L Q) :=
    Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨_, hFP1⟩, inferInstance⟩) hFPeven
  haveI : Nontrivial (MulAction.fixedPoints ↥L Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxne⟩ := exists_ne (⟨QuotientGroup.mk 1, hFP1⟩ : MulAction.fixedPoints ↥L Q)
  obtain ⟨p₁, hp₁⟩ := QuotientGroup.mk_surjective (x : Q)
  have hxfix : ∀ l, l ∈ L → (l : Y) * (p₁ : Y)⁻¹ * (l : Y)⁻¹ * (p₁ : Y) ∈ S := by
    intro l hl
    have := x.2 (⟨l, hl⟩ : ↥L)
    rw [← hp₁] at this
    exact (hfix_iff (l : Y) p₁).mp this
  have hp₁S : (p₁ : Y) ∉ S := by
    intro hmem
    apply hxne
    apply Subtype.ext
    show (x : Q) = QuotientGroup.mk 1
    rw [← hp₁]
    refine QuotientGroup.eq.mpr ?_
    rw [mul_one, Subgroup.mem_subgroupOf]
    simpa using inv_mem hmem
  exact ⟨(p₁ : Y), p₁.2, hp₁S, hxfix⟩

/-- (P1): a normal 2-group `L ⊇ P` acts trivially on `V = P/S` ⟹ `L ≤ ker(blockPerm)`. -/
theorem L_le_blockPerm_ker (S P Lm : Subgroup Y) (hS : S.Normal) (hP : P.Normal) (hL : Lm.Normal)
    (hSP : S < P) (hPL : P ≤ Lm) (h2L : IsPGroup 2 Lm)
    (chief : ∀ X : Subgroup Y, X.Normal → S ≤ X → X ≤ P → X = S ∨ X = P) :
    Lm ≤ (blockPerm S P hS hP).ker := by
  have hP2 : IsPGroup 2 P := fun g => by
    obtain ⟨n, hn⟩ := h2L ⟨g.1, hPL g.2⟩
    exact ⟨n, by ext; simpa using congrArg Subtype.val hn⟩
  obtain ⟨p₁, hp₁P, hp₁S, hp₁fix⟩ := exists_L_fixed_coset S P Lm hS hP hSP hP2 h2L
  have hp₁inv : p₁⁻¹ ∈ fixSub S P Lm hS := by
    refine ⟨P.inv_mem hp₁P, fun c hc => ?_⟩
    have h := hp₁fix c⁻¹ (inv_mem hc)
    have hgoal : c⁻¹ * p₁⁻¹ * c * (p₁⁻¹)⁻¹ = c⁻¹ * p₁⁻¹ * c⁻¹⁻¹ * p₁ := by group
    rw [hgoal]; exact h
  have hSlt : S < fixSub S P Lm hS :=
    (fixSub_S_le S P Lm hS hSP.le).lt_of_ne fun hEq => hp₁S (by
      have : p₁⁻¹ ∈ S := hEq ▸ hp₁inv; simpa using inv_mem this)
  have hfixP : fixSub S P Lm hS = P := by
    rcases chief _ (fixSub_normal S P Lm hS hP hL) (fixSub_S_le S P Lm hS hSP.le)
      (fun p hp => hp.1) with h | h
    · exact absurd h.symm hSlt.ne
    · exact h
  intro l hl
  rw [MonoidHom.mem_ker]
  refine Equiv.Perm.ext fun q => ?_
  refine QuotientGroup.induction_on q fun p => ?_
  show blockPerm S P hS hP l (QuotientGroup.mk p) = QuotientGroup.mk p
  rw [blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  have hcoe : (((conjHom P hP l p)⁻¹ * p : ↥P) : Y) = l * (p : Y)⁻¹ * l⁻¹ * (p : Y) := by
    show (l * (p : Y) * l⁻¹)⁻¹ * (p : Y) = l * (p : Y)⁻¹ * l⁻¹ * (p : Y)
    group
  rw [hcoe]
  have hpinvP : (p : Y)⁻¹ ∈ fixSub S P Lm hS := by rw [hfixP]; exact P.inv_mem p.2
  have h := hpinvP.2 l⁻¹ (inv_mem hl)
  have hgoal2 : l * (p : Y)⁻¹ * l⁻¹ * (p : Y)
      = (l⁻¹)⁻¹ * (p : Y)⁻¹ * l⁻¹ * ((p : Y)⁻¹)⁻¹ := by group
  rw [hgoal2]; exact h

/-- **(F1) bridge** `(V∨)^Ctil = 0 ⟸ V^Ctil = 0`: with `K/(K∩S)` abelian (`hcomm`), `YV`
acting trivially (`hYVtriv`), `Ctil/YV` odd, and `V^Ctil = 0` (`hfix0`), any `Ctil`-invariant
hom `φ : K → 𝔽₂` vanishing on `K∩S` vanishes on `K`.  Averages `φ` over `Ctil/YV` via
`avg_dual_zero`: the fixed vector it produces is nonzero unless `φ = 0`. -/
theorem dual_vanish_concrete (S K Ctil YV : Subgroup Y)
    (hS : S.Normal) (hK : K.Normal) (_hCtil : Ctil.Normal) (hYVn : YV.Normal)
    (hcomm : ∀ a ∈ K, ∀ b ∈ K, a * b * a⁻¹ * b⁻¹ ∈ S)
    (hYVtriv : ∀ z ∈ YV, ∀ k ∈ K, z * k * z⁻¹ * k⁻¹ ∈ S)
    (hodd : Odd (Nat.card (↥Ctil ⧸ (YV.subgroupOf Ctil))))
    (hfix0 : ∀ k, k ∈ K → (∀ c, c ∈ Ctil → c⁻¹ * k * c * k⁻¹ ∈ S) → k ∈ S)
    (φ : Y → ZMod 2) (hφhom : ∀ k, k ∈ K → ∀ l, l ∈ K → φ (k * l) = φ k + φ l)
    (hφS : ∀ k, k ∈ K → k ∈ S → φ k = 0)
    (hφCinv : ∀ c, c ∈ Ctil → ∀ k, k ∈ K → φ (c⁻¹ * k * c) = φ k) :
    ∀ k, k ∈ K → φ k = 0 := by
  classical
  haveI hMn : (S.subgroupOf K).Normal := hS.subgroupOf K
  letI icg : CommGroup (↥K ⧸ (S.subgroupOf K)) :=
    { (inferInstance : Group (↥K ⧸ (S.subgroupOf K))) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with | _ a =>
        induction y using QuotientGroup.induction_on with | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
          Subgroup.mem_subgroupOf]
        have hc : (((a * b)⁻¹ * (b * a) : ↥K) : Y)
            = (b : Y)⁻¹ * (a : Y)⁻¹ * ((b : Y)⁻¹)⁻¹ * ((a : Y)⁻¹)⁻¹ := by push_cast; group
        rw [hc]; exact hcomm _ (inv_mem b.2) _ (inv_mem a.2) }
  set V := Additive (↥K ⧸ (S.subgroupOf K)) with hVdef
  set N : Subgroup ↥Ctil := YV.subgroupOf Ctil with hNdef
  haveI hNn : N.Normal := hYVn.subgroupOf Ctil
  set Q := ↥Ctil ⧸ N with hQdef
  haveI : Fintype Q := Fintype.ofFinite _
  set qv : ↥K → V := fun k => Additive.ofMul (QuotientGroup.mk k) with hqv
  -- conjugation MonoidHom on ↥K by (↑c)⁻¹
  let kconjHom : ↥Ctil → (↥K →* ↥K) := fun c =>
    { toFun := fun k => ⟨(c:Y)⁻¹ * (k:Y) * (c:Y),
        by have := hK.conj_mem (k:Y) k.2 (c:Y)⁻¹; rwa [inv_inv] at this⟩
      map_one' := by apply Subtype.ext; push_cast; group
      map_mul' := fun a b => by apply Subtype.ext; push_cast; group }
  have hcompat : ∀ c : ↥Ctil, (S.subgroupOf K) ≤ (S.subgroupOf K).comap (kconjHom c) := by
    intro c x hx
    have hxS : (x:Y) ∈ S := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    have := hS.conj_mem (x:Y) hxS (c:Y)⁻¹
    rwa [inv_inv] at this
  -- E c : V →+ V
  let E : ↥Ctil → V →+ V := fun c =>
    AddMonoidHom.mk'
      (fun v => Additive.ofMul (QuotientGroup.map (S.subgroupOf K) (S.subgroupOf K)
        (kconjHom c) (hcompat c) (Additive.toMul v)))
      (fun a b => by
        show Additive.ofMul (QuotientGroup.map _ _ _ _ (Additive.toMul (a + b)))
          = Additive.ofMul _ + Additive.ofMul _
        rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl,
          map_mul, ofMul_mul])
  have hkcoe : ∀ (c : ↥Ctil) (k : ↥K), ((kconjHom c k : ↥K) : Y)
      = (c : Y)⁻¹ * (k : Y) * (c : Y) := fun _ _ => rfl
  -- value of E on a class
  have hEval : ∀ (c : ↥Ctil) (k : ↥K), E c (qv k) = qv (kconjHom c k) := by
    intro c k
    show Additive.ofMul (QuotientGroup.map _ _ _ _ (Additive.toMul (Additive.ofMul
      (QuotientGroup.mk k)))) = Additive.ofMul (QuotientGroup.mk _)
    rw [toMul_ofMul, QuotientGroup.map_mk]
  -- composition law
  have hEcomp : ∀ (a b : ↥Ctil) (v : V), E b (E a v) = E (a * b) v := by
    intro a b v
    induction v using Additive.rec with | _ x =>
    induction x using QuotientGroup.induction_on with | _ k =>
    rw [hEval, hEval, hEval]
    apply congrArg qv
    apply Subtype.ext
    rw [hkcoe, hkcoe, hkcoe]
    push_cast
    group
  -- well-definedness on Q
  have hE_wd : ∀ a b : ↥Ctil, a⁻¹ * b ∈ N → E a = E b := by
    intro a b hab
    have hv : ((a⁻¹ * b : ↥Ctil) : Y) ∈ YV := by
      rw [hNdef, Subgroup.mem_subgroupOf] at hab; exact hab
    apply AddMonoidHom.ext
    intro v
    induction v using Additive.rec with | _ x =>
    induction x using QuotientGroup.induction_on with | _ k =>
    rw [hEval, hEval]
    -- `qv (kconjHom a k) = qv (kconjHom b k)`: equal mod `S` via `YV`-conjugation
    have hmk : (QuotientGroup.mk (kconjHom a k) : ↥K ⧸ (S.subgroupOf K))
        = QuotientGroup.mk (kconjHom b k) := by
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
      have hcoe : (((kconjHom a k)⁻¹ * kconjHom b k : ↥K) : Y)
          = ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹ * ((b : Y)⁻¹ * (k : Y) * (b : Y)) := by
        rw [Subgroup.coe_mul, InvMemClass.coe_inv, hkcoe, hkcoe]
      rw [hcoe]
      have hk'K : (a : Y)⁻¹ * (k : Y) * (a : Y) ∈ K := by
        have := hK.conj_mem (k : Y) k.2 (a : Y)⁻¹; rwa [inv_inv] at this
      have hs : ((a⁻¹ * b : ↥Ctil) : Y)⁻¹ * ((a : Y)⁻¹ * (k : Y) * (a : Y))
          * ((a⁻¹ * b : ↥Ctil) : Y) * ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹ ∈ S := by
        have := hYVtriv (((a⁻¹ * b : ↥Ctil) : Y))⁻¹ (inv_mem hv) _ hk'K
        rwa [inv_inv] at this
      have hgoal : ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹ * ((b : Y)⁻¹ * (k : Y) * (b : Y))
          = ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹
            * (((a⁻¹ * b : ↥Ctil) : Y)⁻¹ * ((a : Y)⁻¹ * (k : Y) * (a : Y))
               * ((a⁻¹ * b : ↥Ctil) : Y) * ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹)
            * ((a : Y)⁻¹ * (k : Y) * (a : Y)) := by push_cast; group
      rw [hgoal]
      have := hS.conj_mem _ hs ((a : Y)⁻¹ * (k : Y) * (a : Y))⁻¹
      rwa [inv_inv] at this
    show Additive.ofMul (QuotientGroup.mk (kconjHom a k))
      = Additive.ofMul (QuotientGroup.mk (kconjHom b k))
    exact congrArg Additive.ofMul hmk
  -- === assemble: act on Q, then `avg_dual_zero` ===
  let act : Q → V →+ V := fun q => Quotient.liftOn q E (fun a b hab =>
    hE_wd a b (QuotientGroup.leftRel_apply.mp hab))
  have hact_mk : ∀ (c : ↥Ctil), act (QuotientGroup.mk c) = E c := fun _ => rfl
  have hactmul : ∀ (q q' : Q) (v : V), act q' (act q v) = act (q * q') v := by
    intro q q' v
    induction q using QuotientGroup.induction_on with | _ c =>
    induction q' using QuotientGroup.induction_on with | _ c' =>
    rw [hact_mk, hact_mk, ← QuotientGroup.mk_mul, hact_mk]
    exact hEcomp c c' v
  have hodd' : Odd (Fintype.card Q) := by rwa [Nat.card_eq_fintype_card] at hodd
  -- the descended functional `φbar : V →+ ZMod 2`
  let φMul : ↥K →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (φ (x : Y))
      map_one' := by
        show Multiplicative.ofAdd (φ ((1 : ↥K) : Y)) = 1
        rw [show ((1 : ↥K) : Y) = 1 from rfl]
        have hz : φ (1 : Y) = 0 := by simpa using hφhom 1 (one_mem _) 1 (one_mem _)
        rw [hz]; rfl
      map_mul' := fun x y => by
        show Multiplicative.ofAdd (φ ((x * y : ↥K) : Y)) = _
        rw [Subgroup.coe_mul, hφhom _ x.2 _ y.2]; rfl }
  have hφMulker : (S.subgroupOf K) ≤ φMul.ker := by
    intro x hx
    have hxS : (x : Y) ∈ S := Subgroup.mem_subgroupOf.mp hx
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (φ (x : Y)) = 1
    rw [hφS (x : Y) x.2 hxS]; rfl
  let φQ : (↥K ⧸ (S.subgroupOf K)) →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift _ φMul hφMulker
  let φbar : V →+ ZMod 2 := AddMonoidHom.mk'
    (fun v => Multiplicative.toAdd (φQ (Additive.toMul v)))
    (fun a b => by
      show Multiplicative.toAdd (φQ (Additive.toMul (a + b))) = _
      rw [show Additive.toMul (a + b) = Additive.toMul a * Additive.toMul b from rfl, map_mul]
      rfl)
  have hφbarval : ∀ (k : ↥K), φbar (qv k) = φ (k : Y) := by
    intro k
    show Multiplicative.toAdd (φQ (Additive.toMul (Additive.ofMul (QuotientGroup.mk k)))) = _
    rw [toMul_ofMul]
    show Multiplicative.toAdd (φMul k) = φ (k : Y)
    rfl
  have hφ : ∀ (q : Q) (v : V), φbar (act q v) = φbar v := by
    intro q v
    induction q using QuotientGroup.induction_on with | _ c =>
    induction v using Additive.rec with | _ x =>
    induction x using QuotientGroup.induction_on with | _ k =>
    rw [hact_mk, hEval, hφbarval, hφbarval, hkcoe]
    exact hφCinv (c : Y) c.2 (k : Y) k.2
  -- `V^Ctil = 0`  (from `hfix0`)
  have hfixV : ∀ v : V, (∀ q : Q, act q v = v) → v = 0 := by
    intro v hvfix
    induction v using Additive.rec with | _ x =>
    induction x using QuotientGroup.induction_on with | _ k =>
    have hk0 : (k : Y) ∈ S := by
      apply hfix0 (k : Y) k.2
      intro c hc
      have hq := hvfix (QuotientGroup.mk (⟨c, hc⟩ : ↥Ctil))
      rw [hact_mk, hEval] at hq
      have hmk : (QuotientGroup.mk (kconjHom (⟨c, hc⟩ : ↥Ctil) k) : ↥K ⧸ (S.subgroupOf K))
          = QuotientGroup.mk k := Additive.ofMul.injective hq
      rw [QuotientGroup.eq, Subgroup.mem_subgroupOf] at hmk
      have hcoe : (((kconjHom (⟨c, hc⟩ : ↥Ctil) k)⁻¹ * k : ↥K) : Y)
          = c⁻¹ * (k : Y)⁻¹ * c * (k : Y) := by
        rw [Subgroup.coe_mul, InvMemClass.coe_inv, hkcoe]; group
      rw [hcoe] at hmk
      -- `c⁻¹ k⁻¹ c k ∈ S ⟹ c⁻¹ k c k⁻¹ ∈ S` (inverse + conjugate by `k`)
      have hrw : c⁻¹ * (k : Y) * c * (k : Y)⁻¹
          = (k : Y) * (c⁻¹ * (k : Y)⁻¹ * c * (k : Y))⁻¹ * (k : Y)⁻¹ := by group
      rw [hrw]
      have := hS.conj_mem _ (S.inv_mem hmk) (k : Y)
      exact this
    show Additive.ofMul (QuotientGroup.mk k) = 0
    rw [show (0 : V) = Additive.ofMul (1 : ↥K ⧸ (S.subgroupOf K)) from rfl]
    apply congrArg Additive.ofMul
    rwa [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  -- conclude
  intro k hk
  have := avg_dual_zero act hactmul hodd' hfixV φbar hφ (qv ⟨k, hk⟩)
  rwa [hφbarval] at this

private theorem cyclic_quot {H : Type*} [Group H] (s t : H) (hgen : Subgroup.closure {s, t} = ⊤)
    (M : Subgroup H) [M.Normal] (htM : t ∈ M) : IsCyclic (H ⧸ M) := by
  classical
  refine ⟨⟨QuotientGroup.mk s, fun x => ?_⟩⟩
  induction x using QuotientGroup.induction_on with | _ h =>
  have hkey : Subgroup.closure {s, t}
      ≤ Subgroup.comap (QuotientGroup.mk' M) (Subgroup.zpowers (QuotientGroup.mk s)) := by
    rw [Subgroup.closure_le]
    intro y hy
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_comap]
    rcases hy with rfl | rfl
    · rw [QuotientGroup.mk'_apply]; exact Subgroup.mem_zpowers _
    · rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr htM]; exact one_mem _
  have hmem : h ∈ Subgroup.closure {s, t} := by rw [hgen]; exact Subgroup.mem_top h
  have : QuotientGroup.mk' M h ∈ Subgroup.zpowers (QuotientGroup.mk s) :=
    Subgroup.mem_comap.mp (hkey hmem)
  rwa [QuotientGroup.mk'_apply] at this

/-- **(unramified) image count** — if `G ≤ Y` acts on `V = P/S` through a 2-group image
(`blockPerm(G)` is `IsPGroup 2`), there is a nontrivial `G`-fixed coset. -/
private theorem exists_normal_fixed_coset (S P G : Subgroup Y) (hS : S.Normal) (hP : P.Normal)
    (hSP : S < P) (hP2 : IsPGroup 2 P)
    (hG2 : IsPGroup 2 (((blockPerm S P hS hP).comp G.subtype).range)) :
    ∃ p₁ : Y, p₁ ∈ P ∧ p₁ ∉ S ∧ ∀ g, g ∈ G → g * p₁⁻¹ * g⁻¹ * p₁ ∈ S := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hSPn : (S.subgroupOf P).Normal := hS.subgroupOf P
  set Q := ↥P ⧸ S.subgroupOf P with hQdef
  set φ : Y →* Equiv.Perm Q := blockPerm S P hS hP with hφ
  set R := ((blockPerm S P hS hP).comp G.subtype).range with hR
  have hval : ∀ (y : Y) (p : ↥P),
      (((conjHom P hP y p)⁻¹ * p : ↥P) : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y) := by
    intro y p
    show (y * (p : Y) * y⁻¹)⁻¹ * (p : Y) = y * (p : Y)⁻¹ * y⁻¹ * (p : Y)
    group
  have hfix_iff : ∀ (y : Y) (p : ↥P),
      φ y (QuotientGroup.mk p) = QuotientGroup.mk p ↔ y * (p : Y)⁻¹ * y⁻¹ * (p : Y) ∈ S := by
    intro y p
    rw [hφ, blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    exact Iff.of_eq (congrArg (· ∈ S) (hval y p))
  haveI hQ2 : IsPGroup 2 Q := hP2.to_quotient (S.subgroupOf P)
  obtain ⟨p₀, hp₀P, hp₀S⟩ := SetLike.exists_of_lt hSP
  haveI hQnt : Nontrivial Q := by
    refine ⟨QuotientGroup.mk ⟨p₀, hp₀P⟩, 1, ?_⟩
    rw [ne_eq, QuotientGroup.eq_one_iff]
    exact fun hmem => hp₀S (Subgroup.mem_subgroupOf.mp hmem)
  have hcardQ : 2 ∣ Nat.card Q := by
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨k, hk⟩ := hQ2 q
    have hdvd : orderOf q ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
    have hne1 : orderOf q ≠ 1 := fun h => hq (orderOf_eq_one_iff.mp h)
    obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
    have hj0 : j ≠ 0 := fun h0 => hne1 (by rw [hj, h0, pow_zero])
    exact (hj ▸ dvd_pow_self 2 hj0).trans (orderOf_dvd_natCard q)
  -- the 2-group `R = blockPerm(G) ≤ Perm Q` acts; fixed set is even
  letI : MulAction ↥R Q := MulAction.compHom Q R.subtype
  have hmod := hG2.card_modEq_card_fixedPoints (α := Q)
  have hFPeven : 2 ∣ Nat.card (MulAction.fixedPoints ↥R Q) :=
    (Nat.modEq_zero_iff_dvd).mp (hmod.symm.trans ((Nat.modEq_zero_iff_dvd).mpr hcardQ))
  have hFP1 : (QuotientGroup.mk 1 : Q) ∈ MulAction.fixedPoints ↥R Q := by
    rintro ⟨r, g, rfl⟩
    show φ (g : Y) (QuotientGroup.mk (1 : ↥P)) = QuotientGroup.mk 1
    rw [hfix_iff]
    simp
  have hFP2 : 2 ≤ Nat.card (MulAction.fixedPoints ↥R Q) :=
    Nat.le_of_dvd (Nat.card_pos_iff.mpr ⟨⟨_, hFP1⟩, inferInstance⟩) hFPeven
  haveI : Nontrivial (MulAction.fixedPoints ↥R Q) :=
    Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨x, hxne⟩ := exists_ne (⟨QuotientGroup.mk 1, hFP1⟩ : MulAction.fixedPoints ↥R Q)
  obtain ⟨p₁, hp₁⟩ := QuotientGroup.mk_surjective (x : Q)
  have hxfix : ∀ g, g ∈ G → (g : Y) * (p₁ : Y)⁻¹ * (g : Y)⁻¹ * (p₁ : Y) ∈ S := by
    intro g hg
    have hmemR : φ g ∈ R := ⟨⟨g, hg⟩, rfl⟩
    have := x.2 (⟨φ g, hmemR⟩ : ↥R)
    rw [← hp₁] at this
    exact (hfix_iff (g : Y) p₁).mp this
  have hp₁S : (p₁ : Y) ∉ S := by
    intro hmem
    apply hxne
    apply Subtype.ext
    show (x : Q) = QuotientGroup.mk 1
    rw [← hp₁]
    refine QuotientGroup.eq.mpr ?_
    rw [mul_one, Subgroup.mem_subgroupOf]
    simpa using inv_mem hmem
  exact ⟨(p₁ : Y), p₁.2, hp₁S, hxfix⟩

/-- **(unramified) oddness** — `Y/Y_V` (`Y_V = ker blockPerm`) is odd when it is cyclic and the
action on the simple `V = P/S` is faithful. -/
theorem unram_odd (S P : Subgroup Y) (hS : S.Normal) (hP : P.Normal) (hSP : S < P)
    (hP2 : IsPGroup 2 P) (chief : ∀ X : Subgroup Y, X.Normal → S ≤ X → X ≤ P → X = S ∨ X = P)
    (hcyc : IsCyclic (Y ⧸ (blockPerm S P hS hP).ker)) :
    Odd (Nat.card (Y ⧸ (blockPerm S P hS hP).ker)) := by
  classical
  set YV := (blockPerm S P hS hP).ker with hYV
  rw [Nat.odd_iff]
  by_contra hne
  have h2 : 2 ∣ Nat.card (Y ⧸ YV) := by omega
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fintype (Y ⧸ YV) := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card] at h2
  obtain ⟨gbar, hgbar⟩ := exists_prime_orderOf_dvd_card 2 h2
  -- `Y/Y_V` is commutative (cyclic); keep it as a plain fact to avoid an instance diamond.
  have hcomm : ∀ a b : Y ⧸ YV, a * b = b * a := by
    obtain ⟨gen, hgen⟩ := hcyc.exists_generator
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen a)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hgen b)
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  set Ctil : Subgroup Y := (Subgroup.zpowers gbar).comap (QuotientGroup.mk' YV) with hCtil
  have hCtilN : Ctil.Normal := by
    have hCN : (Subgroup.zpowers gbar).Normal :=
      ⟨fun n hn g => by rw [hcomm g n, mul_assoc, mul_inv_cancel, mul_one]; exact hn⟩
    exact hCN.comap _
  have hYVle : YV ≤ Ctil := by
    intro y hy
    rw [hCtil, Subgroup.mem_comap]
    have h1 : (QuotientGroup.mk' YV) y = 1 := by
      rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff y).mpr hy
    rw [h1]; exact one_mem _
  -- `blockPerm(Ctil)` is a 2-group: its range has card `= card(Ctil/Y_V) = orderOf gbar = 2`
  have hrange2 : IsPGroup 2 ((blockPerm S P hS hP).comp Ctil.subtype).range := by
    have hkr : ((blockPerm S P hS hP).comp Ctil.subtype).ker = YV.subgroupOf Ctil := by
      ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
        Subgroup.mem_subgroupOf, hYV]
    have hcard : Nat.card ((blockPerm S P hS hP).comp Ctil.subtype).range = 2 := by
      have e1 : (↥Ctil ⧸ ((blockPerm S P hS hP).comp Ctil.subtype).ker)
          ≃* ((blockPerm S P hS hP).comp Ctil.subtype).range :=
        QuotientGroup.quotientKerEquivRange _
      -- and `↥Ctil ⧸ (YV.subgroupOf Ctil) ≅ ⟨gbar⟩`
      have hker2 : ((QuotientGroup.mk' YV).comp Ctil.subtype).ker = YV.subgroupOf Ctil := by
        ext x
        simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype,
          QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hYV]
      have hrng2 : ((QuotientGroup.mk' YV).comp Ctil.subtype).range = Subgroup.zpowers gbar := by
        rw [MonoidHom.range_comp, Subgroup.range_subtype, hCtil,
          Subgroup.map_comap_eq_self (by
            rw [MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective YV)]; exact le_top)]
      have e2 : (↥Ctil ⧸ ((QuotientGroup.mk' YV).comp Ctil.subtype).ker)
          ≃* ((QuotientGroup.mk' YV).comp Ctil.subtype).range :=
        QuotientGroup.quotientKerEquivRange _
      have hc1 : Nat.card (↥Ctil ⧸ (YV.subgroupOf Ctil)) = 2 := by
        have e3 : (↥Ctil ⧸ (YV.subgroupOf Ctil))
            ≃* (↥Ctil ⧸ ((QuotientGroup.mk' YV).comp Ctil.subtype).ker) :=
          QuotientGroup.quotientMulEquivOfEq hker2.symm
        rw [Nat.card_congr (e3.trans e2).toEquiv, hrng2, Nat.card_zpowers, hgbar]
      have e4 : (↥Ctil ⧸ ((blockPerm S P hS hP).comp Ctil.subtype).ker)
          ≃* (↥Ctil ⧸ (YV.subgroupOf Ctil)) :=
        QuotientGroup.quotientMulEquivOfEq hkr
      rw [← Nat.card_congr e1.toEquiv, Nat.card_congr e4.toEquiv, hc1]
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [hcard, pow_one]⟩
  -- count: a nontrivial `Ctil`-fixed coset
  obtain ⟨p₁, hp₁P, hp₁S, hp₁fix⟩ := exists_normal_fixed_coset S P Ctil hS hP hSP hP2 hrange2
  -- `p₁⁻¹ ∈ fixSub`, `S < fixSub`, `chief` ⟹ `fixSub = P` ⟹ `Ctil ≤ Y_V`
  have hp₁inv : p₁⁻¹ ∈ fixSub S P Ctil hS := by
    refine ⟨P.inv_mem hp₁P, fun c hc => ?_⟩
    have h := hp₁fix c⁻¹ (inv_mem hc)
    have hgoal : c⁻¹ * p₁⁻¹ * c * (p₁⁻¹)⁻¹ = c⁻¹ * p₁⁻¹ * c⁻¹⁻¹ * p₁ := by group
    rw [hgoal]; exact h
  have hSlt : S < fixSub S P Ctil hS :=
    (fixSub_S_le S P Ctil hS hSP.le).lt_of_ne fun hEq => hp₁S (by
      have : p₁⁻¹ ∈ S := hEq ▸ hp₁inv; simpa using inv_mem this)
  have hfixP : fixSub S P Ctil hS = P := by
    rcases chief _ (fixSub_normal S P Ctil hS hP hCtilN) (fixSub_S_le S P Ctil hS hSP.le)
      (fun p hp => hp.1) with h | h
    · exact absurd h.symm hSlt.ne
    · exact h
  have hCtilYV : Ctil ≤ YV := by
    intro c hc
    rw [hYV, MonoidHom.mem_ker]
    refine Equiv.Perm.ext fun q => ?_
    refine QuotientGroup.induction_on q fun p => ?_
    show blockPerm S P hS hP c (QuotientGroup.mk p) = QuotientGroup.mk p
    rw [blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hcoe : (((conjHom P hP c p)⁻¹ * p : ↥P) : Y) = c * (p : Y)⁻¹ * c⁻¹ * (p : Y) := by
      show (c * (p : Y) * c⁻¹)⁻¹ * (p : Y) = c * (p : Y)⁻¹ * c⁻¹ * (p : Y); group
    rw [hcoe]
    have hpinvP : (p : Y)⁻¹ ∈ fixSub S P Ctil hS := by rw [hfixP]; exact P.inv_mem p.2
    have h := hpinvP.2 c⁻¹ (inv_mem hc)
    have hgoal2 : c * (p : Y)⁻¹ * c⁻¹ * (p : Y)
        = (c⁻¹)⁻¹ * (p : Y)⁻¹ * c⁻¹ * ((p : Y)⁻¹)⁻¹ := by group
    rw [hgoal2]; exact h
  -- contradiction: `gbar = 1` but `orderOf gbar = 2`
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective YV gbar
  have hgCtil : g ∈ Ctil := by rw [hCtil, Subgroup.mem_comap, hg]; exact Subgroup.mem_zpowers _
  have hg1 : gbar = 1 := by
    rw [← hg, QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).mpr (hCtilYV hgCtil)
  rw [hg1, orderOf_one] at hgbar
  exact absurd hgbar (by decide)

-- (a) IsCyclic(Y/YV) from tame gens + `t ∈ map π YV`
theorem cyc_YV {Y H : Type*} [Group Y] [Finite Y] [Group H] [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (YV : Subgroup Y) [YV.Normal]
    (hLYV : π.ker ≤ YV) (s t : H) (hgen : Subgroup.closure {s, t} = ⊤)
    (htYV : t ∈ YV.map π) : IsCyclic (Y ⧸ YV) := by
  classical
  set M := YV.map π with hM
  haveI hMn : M.Normal := (Subgroup.Normal.map (by infer_instance) π hπ)
  have hq : Function.Surjective ((QuotientGroup.mk' M).comp π) :=
    (QuotientGroup.mk'_surjective M).comp hπ
  have hqker : ((QuotientGroup.mk' M).comp π).ker = YV := by
    ext y
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hM]
    constructor
    · intro h
      obtain ⟨w, hw, hwy⟩ := Subgroup.mem_map.mp h
      have : w⁻¹ * y ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hwy, inv_mul_cancel]
      have := hLYV this
      simpa using mul_mem hw this
    · intro h; exact Subgroup.mem_map_of_mem π h
  haveI hcycM : IsCyclic (H ⧸ M) := cyclic_quot s t hgen M htYV
  let e : (Y ⧸ YV) ≃* (H ⧸ M) :=
    (QuotientGroup.quotientMulEquivOfEq hqker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective _ hq)
  exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective

-- (b) ⊤-quotient card conversion
theorem top_quot_card {Y : Type*} [Group Y] (YV : Subgroup Y) [YV.Normal] :
    Nat.card (↥(⊤ : Subgroup Y) ⧸ (YV.subgroupOf ⊤)) = Nat.card (Y ⧸ YV) := by
  rw [← Subgroup.index_eq_card, ← Subgroup.index_eq_card]
  exact Subgroup.index_comap_of_surjective YV (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)

/-- **(ramified) oddness** — if `π : Y ↠ H` has `ker π ≤ YV` and `t : H` has odd order,
the quotient `π⁻¹⟨t⟩ / (YV ∩ π⁻¹⟨t⟩)` is odd (a quotient of `π⁻¹⟨t⟩ / ker π ≅ ⟨t⟩`). -/
theorem odd_preimage_quot {Y H : Type*} [Group Y] [Finite Y] [Group H]
    (π : Y →* H) (hπ : Function.Surjective π) (YV : Subgroup Y) (hLYV : π.ker ≤ YV)
    (t : H) (ht : Odd (orderOf t)) :
    Odd (Nat.card (↥((Subgroup.zpowers t).comap π)
      ⧸ (YV.subgroupOf ((Subgroup.zpowers t).comap π)))) := by
  classical
  set C : Subgroup Y := (Subgroup.zpowers t).comap π with hC
  set N₁ : Subgroup ↥C := (π.ker).subgroupOf C with hN₁
  set N₂ : Subgroup ↥C := YV.subgroupOf C with hN₂
  -- `↥C ⧸ N₁ ≅ ⟨t⟩`, so `card (↥C ⧸ N₁) = orderOf t`
  have hker : (π.comp C.subtype).ker = N₁ := by
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.coe_subtype, hN₁,
      Subgroup.mem_subgroupOf]
  have hrange : (π.comp C.subtype).range = Subgroup.zpowers t := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hC,
      Subgroup.map_comap_eq_self (by rw [MonoidHom.range_eq_top.mpr hπ]; exact le_top)]
  have hcard1 : Nat.card (↥C ⧸ N₁) = orderOf t := by
    have e1 : (↥C ⧸ N₁) ≃* (↥C ⧸ (π.comp C.subtype).ker) :=
      QuotientGroup.quotientMulEquivOfEq hker.symm
    have e2 := QuotientGroup.quotientKerEquivRange (π.comp C.subtype)
    rw [Nat.card_congr (e1.trans e2).toEquiv, hrange, Nat.card_zpowers]
  -- `card (↥C ⧸ N₂) ∣ card (↥C ⧸ N₁)` since `N₁ ≤ N₂`
  have hN₁N₂ : N₁ ≤ N₂ := by
    rw [hN₁, hN₂]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    exact hLYV hx
  have hdvd : Nat.card (↥C ⧸ N₂) ∣ Nat.card (↥C ⧸ N₁) := by
    have := Subgroup.index_dvd_of_le hN₁N₂
    rwa [Subgroup.index_eq_card, Subgroup.index_eq_card] at this
  -- odd divides odd
  rw [Nat.odd_iff] at ht ⊢
  rw [hcard1] at hdvd
  by_contra hne
  have h2m : 2 ∣ Nat.card (↥C ⧸ N₂) := by omega
  have : 2 ∣ orderOf t := h2m.trans hdvd
  omega


end SectionSeven

end GQ2
