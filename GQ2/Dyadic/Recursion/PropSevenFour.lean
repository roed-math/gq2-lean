/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Recursion.Recursion
import GQ2.SectionSeven.Prop74

/-!
# §7 at a general residue cardinality — Proposition 7.4 over `T_q` (ticket SD-R1, SEAM A)

Clone of the `Ttame`-typed tier of §7, re-typed at F3's `Tq q`.  This discharges **SEAM A**,
reported by SD-R1's first pass and adopted as in-scope by the orchestrator: the SD1 memo listed
"all of §§5–7" as reused untouched, but `GQ2.SectionSeven.prop_7_4`
(`GQ2/SectionSeven/Prop74.lean:307`) takes `cH : ContinuousMonoidHom Ttame H`, so a `K`-frame's
`alpha : ContinuousMonoidHom (Tq q) H` is rejected outright.

## The seam is shallow — measured, not estimated

Of `GQ2/SectionSeven/` (2783 ln over five files), **only two files mention `cH`/`Ttame` at all**:

| file | ln | `cH`/`Ttame` hits | disposition |
|---|---|---|---|
| `Basic.lean` | 503 | 0 | consumed as-is, by import |
| `ModuleCore.lean` | 717 | 0 | consumed as-is, by import |
| `Prop74Step1.lean` | 734 | 0 | consumed as-is, by import |
| `Decorations.lean` | 371 | 2 | only `lemma_7_2`'s binder — see below |
| `Prop74.lean` | 458 | 27 | the four declarations cloned here |

So the module core, the averaging machinery (`dual_vanish_concrete`, `quotient_average`,
`fixed_zero_of_moves`, `sigma0_extends`, `invariant_hom_absurd`, `cyc_YV`, `unram_odd`,
`odd_preimage_quot`, `lam_comm_vanish`, …) is **degree-blind** and is reused unchanged.

## `lemma_7_2`'s head binders are decorative (a finding)

`GQ2.SectionSeven.lemma_7_2` (`Decorations.lean:136`) binds `π`, `Function.Surjective π`,
`π.ker = L`, `cH` and `Function.Surjective cH` — and its **body uses none of them**; the
conclusion mentions only `B`.  All five binders are decorative.  The honest content is
isolated here as `lemma_7_2_core`, and `lemma_7_2K` is the name-correspondent wrapper at the
retyped binder.  (The body could not be re-derived from the model: instantiating it would
require a surjection `Ttame ↠ Y/L` onto an arbitrary finite head, which does not exist.)

## The parameterization delta: four lemma names and two hypotheses

Every clone below gains `{q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)`.  Inside
`hv_average_helperK` — the **only** declaration doing real work — exactly four names change
(`Prop74.lean:102,103-105,107,108`):

| model | clone | note |
|---|---|---|
| `SectionThree.gen_ttame_quotient` | `GQ2.Dyadic.gen_tq_quotient` | no hypothesis on `q` |
| the inline `hrel` `by`-block (`congrArg cH tame_relation`) | `GQ2.Dyadic.tame_rel_map_q` | concludes `^ q`; term-mode, so the `simpa` disappears |
| `Tame.zpowers_normal_of_tame` | `GQ2.Dyadic.TameQ.zpowers_normal` | no hypothesis on `q` |
| `Tame.tame_odd_order` | `GQ2.Dyadic.TameQ.odd_order` | consumes `hq0`, `hqe` |

plus the elementwise `cH tameSigma/tameTau` → `cH (tqSigma q)/(tqTau q)`.  `key_extensionK`,
`lam_sq_vanishK` and `prop_7_4K` are **pure pass-through**: `cH` is threaded and never
inspected.

Everything else is byte-identical to the model.  In particular the ramified/unramified case
split at `Prop74.lean:109-151` — the mathematical heart of step 2 — is unchanged: it needs only
that `⟨cH τ⟩` is normal with odd order, both of which F3 supplies at general even `q`.

Axioms: none beyond std-3; each clone's print equals its model's.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.SectionSeven QuadraticFp2

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

variable {L : Subgroup Y}


/-! ## Three private helpers copied from the model

`comm_sq_eq_one_of_central` (`GQ2/SectionSeven/Decorations.lean:37`),
`mul_pow_four_of_central` (:60) and `frattini_sq_eq_one` (:112) are `private` in the model,
hence not referenceable from here.  They are copied verbatim — degree-blind class-2 group
theory with no tame input.  This duplication is the only cost SEAM A imposes beyond the
retyping itself. -/

omit [Finite Y] in
/-- With the squares and commutators of `K` central in `K` (`hcentral`), every commutator of
elements of `K` is an involution: `[k, l]² = 1`. -/
private theorem comm_sq_eq_one_of_central (K : Subgroup Y)
    (hcentral : ∀ r ∈ frattiniLike K, ∀ k ∈ K, r * k = k * r)
    {k l : Y} (hk : k ∈ K) (hl : l ∈ K) :
    (k * l * k⁻¹ * l⁻¹) * (k * l * k⁻¹ * l⁻¹) = 1 := by
  have hksq : ∀ m, m ∈ K → m * m ∈ frattiniLike K := fun m hm =>
    Subgroup.subset_closure (Or.inl ⟨m, hm, rfl⟩)
  have hcommR : ∀ m, m ∈ K → ∀ p, p ∈ K → m * p * m⁻¹ * p⁻¹ ∈ frattiniLike K := fun m hm p hp =>
    Subgroup.subset_closure (Or.inr ⟨m, hm, p, hp, rfl⟩)
  have hkkl : (k * k) * l * (k * k)⁻¹ * l⁻¹ = 1 := by
    have hc := hcentral (k * k) (hksq k hk) l hl
    rw [hc]; group
  have hexp : (k * k) * l * (k * k)⁻¹ * l⁻¹
      = k * (k * l * k⁻¹ * l⁻¹) * k⁻¹ * (k * l * k⁻¹ * l⁻¹) := by group
  have hkc : k * (k * l * k⁻¹ * l⁻¹) * k⁻¹ = k * l * k⁻¹ * l⁻¹ := by
    have hc := hcentral (k * l * k⁻¹ * l⁻¹) (hcommR k hk l hl) k hk
    rw [show k * (k * l * k⁻¹ * l⁻¹) = (k * l * k⁻¹ * l⁻¹) * k from hc.symm]
    group
  rw [hexp, hkc] at hkkl
  exact hkkl

omit [Finite Y] in
/-- Class-2 fourth-power law: with the squares and commutators of `K` central in `K` (`hcentral`),
`(k * l)^4 = k^4 * l^4` for `k, l ∈ K`. -/
private theorem mul_pow_four_of_central (K : Subgroup Y)
    (hcentral : ∀ r ∈ frattiniLike K, ∀ k ∈ K, r * k = k * r)
    {k l : Y} (hk : k ∈ K) (hl : l ∈ K) :
    (k * l) ^ 4 = k ^ 4 * l ^ 4 := by
  have hksq : ∀ m, m ∈ K → m * m ∈ frattiniLike K := fun m hm =>
    Subgroup.subset_closure (Or.inl ⟨m, hm, rfl⟩)
  have hcommR : ∀ m, m ∈ K → ∀ p, p ∈ K → m * p * m⁻¹ * p⁻¹ ∈ frattiniLike K := fun m hm p hp =>
    Subgroup.subset_closure (Or.inr ⟨m, hm, p, hp, rfl⟩)
  have hp4 : ∀ x : Y, x ^ 4 = x * x * x * x := fun x => by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  have hclk : l * k * l⁻¹ * k⁻¹ ∈ frattiniLike K := hcommR l hl k hk
  have hc' : k * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * k :=
    (hcentral (l * k * l⁻¹ * k⁻¹) hclk k hk).symm
  have hsq : (k * l) ^ 2 = (l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l) := by
    calc (k * l) ^ 2
        = k * (l * k * l⁻¹ * k⁻¹) * (k * l * l) := by rw [pow_two]; group
      _ = (l * k * l⁻¹ * k⁻¹) * k * (k * l * l) := by rw [hc']
      _ = (l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l) := by group
  have hlk2 : (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) = 1 :=
    comm_sq_eq_one_of_central K hcentral hl hk
  have s1 : (l * l) * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * (l * l) :=
    hcentral (l * l) (hksq l hl) _ (frattiniLike_le K hclk)
  have s2 : (k * k) * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * (k * k) :=
    hcentral (k * k) (hksq k hk) _ (frattiniLike_le K hclk)
  have s3 : (l * l) * (k * k) = (k * k) * (l * l) :=
    hcentral (l * l) (hksq l hl) _ (mul_mem hk hk)
  have h4 : (k * l) ^ 4 = ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l))
      * ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l)) := by
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hsq, pow_two]
  rw [h4]
  calc ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l)) * ((l * k * l⁻¹ * k⁻¹) * (k * k) * (l * l))
      = (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * l) * (l * k * l⁻¹ * k⁻¹)) * (k * k) * (l * l) := by
        group
    _ = (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * k * l⁻¹ * k⁻¹) * (l * l)) * (k * k) * (l * l) := by
        rw [s1]
    _ = (l * k * l⁻¹ * k⁻¹) * ((k * k) * (l * k * l⁻¹ * k⁻¹)) * (l * l) * (k * k) * (l * l) := by
        group
    _ = (l * k * l⁻¹ * k⁻¹) * ((l * k * l⁻¹ * k⁻¹) * (k * k)) * (l * l) * (k * k) * (l * l) := by
        rw [s2]
    _ = (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) * (k * k) * ((l * l) * (k * k)) * (l * l) := by
        group
    _ = (l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹) * (k * k) * ((k * k) * (l * l)) * (l * l) := by
        rw [s3]
    _ = ((l * k * l⁻¹ * k⁻¹) * (l * k * l⁻¹ * k⁻¹)) * ((k * k) * (k * k)) *
          ((l * l) * (l * l)) := by
        group
    _ = 1 * ((k * k) * (k * k)) * ((l * l) * (l * l)) := by rw [hlk2]
    _ = k ^ 4 * l ^ 4 := by rw [one_mul, hp4 k, hp4 l]; group

omit [Finite Y] in
/-- If every element of `K` satisfies `k^4 = 1` and the squares and commutators of `K` are central
in `K` (`hcentral`), then every element of `Φ(K)` is an involution. -/
private theorem frattini_sq_eq_one (K : Subgroup Y)
    (hcentral : ∀ r ∈ frattiniLike K, ∀ k ∈ K, r * k = k * r)
    (hk4 : ∀ k, k ∈ K → k ^ 4 = 1)
    {r : Y} (hr : r ∈ frattiniLike K) : r * r = 1 := by
  have hp4 : ∀ x : Y, x ^ 4 = x * x * x * x := fun x => by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  refine Subgroup.closure_induction (p := fun g _ => g * g = 1) ?_ ?_ ?_ ?_ hr
  · rintro g (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
    · rw [show (k * k) * (k * k) = k ^ 4 by rw [hp4 k]; group]; exact hk4 k hk
    · exact comm_sq_eq_one_of_central K hcentral hk hl
  · exact one_mul 1
  · intro a b ha_mem hb_mem ha hb
    have hbK : b ∈ K := frattiniLike_le K hb_mem
    have hab : a * b = b * a := hcentral a ha_mem b hbK
    calc (a * b) * (a * b) = a * (b * a) * b := by group
      _ = a * (a * b) * b := by rw [hab]
      _ = (a * a) * (b * b) := by group
      _ = 1 := by rw [ha, hb, mul_one]
  · intro a _ ha
    rw [show a⁻¹ * a⁻¹ = (a * a)⁻¹ by group, ha, inv_one]

/-- **Lemma 7.2's content**, with the five decorative binders of
`GQ2.SectionSeven.lemma_7_2` (`GQ2/SectionSeven/Decorations.lean:136`) removed: `R = Φ(K)` is
central elementary abelian in `K`, and `K⁴ = 1`.  Body copied verbatim from the model, which
uses neither `π` nor `cH`. -/
theorem lemma_7_2_core (B : MinimalBlock L) :
    (∀ r ∈ B.frattiniK, ∀ k ∈ B.K, r * k = k * r) ∧ (∀ r ∈ B.frattiniK, r * r = 1) ∧
      ∀ k ∈ B.K, k ^ 4 = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := B.hK
  have := B.hS
  have := B.hP
  have hRN : (B.frattiniK).Normal := frattiniLike_normal B.K B.hK
  -- `IsPGroup 2 P` and `IsPGroup 2 S`
  have hP2 : IsPGroup 2 B.P := B.h2L.to_le B.hPL
  have hS2 : IsPGroup 2 B.S := B.h2L.to_le (B.hSP.le.trans B.hPL)
  -- an odd-order element moving `V = P/S`
  obtain ⟨y, hyodd, pw, hpwP, hpwS⟩ :=
    GQ2.exists_odd_moving_general B.S B.P B.hS B.hP B.hSP hP2 B.chief B.nontrivial_action
  set Ñ := Subgroup.zpowers y with hÑ
  have hÑcard : Nat.card Ñ = orderOf y := Nat.card_zpowers y
  -- `#Ñ` (odd) is coprime to `#S` (a power of 2)
  have hcop : Nat.Coprime (Nat.card Ñ) (Nat.card B.S) := by
    obtain ⟨m, hm⟩ := (IsPGroup.iff_card (p := 2)).mp hS2
    rw [hÑcard, hm]
    exact (Nat.coprime_two_right.mpr hyodd).pow_right m
  -- `⁅Ñ, S⁆ = ⊥`
  obtain ⟨n, c, hc0, hcn, hmono, _hnorm, hccomm⟩ := B.scalar_below
  have hÑS : ⁅Ñ, B.S⁆ = ⊥ := by
    have := GQ2.comm_bot_of_scalarChain n Ñ c hc0 hmono hccomm (by rw [hcn]; exact hcop)
    rwa [hcn] at this
  -- `R ≤ S`, hence `⁅Ñ, R⁆ = ⊥`
  have hRS : B.frattiniK ≤ B.S := (lemma_7_1_head B).trans inf_le_right
  have hÑR : ⁅Ñ, B.frattiniK⁆ = ⊥ := le_bot_iff.mp (hÑS ▸ Subgroup.commutator_mono le_rfl hRS)
  have hÑcentR : Ñ ≤ Subgroup.centralizer (B.frattiniK : Set Y) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hÑR
  -- `D = K ⊓ C_Y(R)` is `Y`-normal
  set D := B.K ⊓ Subgroup.centralizer (B.frattiniK : Set Y) with hD
  have : D.Normal := by
    refine ⟨fun d hd g => Subgroup.mem_inf.mpr
      ⟨B.hK.conj_mem d (Subgroup.mem_inf.mp hd).1 g, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    have hdc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hd).2
    have hgr : g⁻¹ * r * g ∈ B.frattiniK := by simpa using hRN.conj_mem r hr g⁻¹
    have hcomm := hdc (g⁻¹ * r * g) hgr
    calc r * (g * d * g⁻¹) = g * ((g⁻¹ * r * g) * d) * g⁻¹ := by group
      _ = g * (d * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
      _ = (g * d * g⁻¹) * r := by group
  -- three-subgroup lemma: `⁅⁅K, Ñ⁆, R⁆ = ⊥`
  have hRK : ⁅B.frattiniK, B.K⁆ ≤ B.frattiniK := Subgroup.commutator_le_left B.frattiniK B.K
  have h3 : ⁅⁅B.K, Ñ⁆, B.frattiniK⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_
    · rw [hÑR, Subgroup.commutator_bot_left]
    · exact le_bot_iff.mp (hÑR ▸
        (Subgroup.commutator_mono hRK le_rfl).trans
          (le_of_eq (Subgroup.commutator_comm B.frattiniK Ñ)))
  -- `⁅K, Ñ⁆ ≤ D`
  have hKÑD : ⁅B.K, Ñ⁆ ≤ D :=
    le_inf (Subgroup.commutator_le_left B.K Ñ)
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h3)
  -- the `Y`-normal closure `K₁ = ⟪⁅K,Ñ⁆⟫` sits inside `D` and inside `K`
  set K₁ := Subgroup.normalClosure ((⁅B.K, Ñ⁆ : Subgroup Y) : Set Y) with hK₁
  have hCK₁ : ⁅B.K, Ñ⁆ ≤ K₁ := Subgroup.le_normalClosure
  have hK₁D : K₁ ≤ D := Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hKÑD)
  have hK₁K : K₁ ≤ B.K := Subgroup.normalClosure_le_normal
    (SetLike.coe_subset_coe.mpr (Subgroup.commutator_le_left B.K Ñ))
  have hK₁N : K₁.Normal := Subgroup.normalClosure_normal
  -- `K₁ ⊔ S = P` (the chief dichotomy: `= S` contradicts nontriviality)
  have hK₁gen : K₁ ⊔ B.S = B.P := by
    have hle : K₁ ⊔ B.S ≤ B.P := sup_le (hK₁K.trans B.hKP) B.hSP.le
    have hSle : B.S ≤ K₁ ⊔ B.S := le_sup_right
    rcases B.chief _ (Subgroup.sup_normal K₁ B.S) hSle hle with hEqS | hEqP
    · exfalso
      -- `K₁ ⊔ S = S ⟹ ⁅K,Ñ⁆ ≤ S`, so every `[y, p]` (`p ∈ P`) lands in `S`
      have hKÑS : ⁅B.K, Ñ⁆ ≤ B.S := hCK₁.trans (le_sup_left.trans hEqS.le)
      apply hpwS
      -- `pw = k * s`
      have hmem : pw ∈ (B.K : Set Y) * (B.S : Set Y) := by
        rw [← Subgroup.mul_normal, B.gen]; exact hpwP
      obtain ⟨k, hk, s, hs, rfl⟩ := hmem
      -- `[y, k] ∈ ⁅Ñ, K⁆ = ⁅K, Ñ⁆ ≤ S`
      have hyk : y * k * y⁻¹ * k⁻¹ ∈ B.S := by
        have : y * k * y⁻¹ * k⁻¹ ∈ ⁅Ñ, B.K⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) hk
        rw [Subgroup.commutator_comm] at this
        exact hKÑS this
      -- `[y, s] ∈ ⁅Ñ, S⁆ = ⊥`
      have hys : y * s * y⁻¹ * s⁻¹ = 1 := by
        have : y * s * y⁻¹ * s⁻¹ ∈ ⁅Ñ, B.S⁆ :=
          Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers y) hs
        rwa [hÑS, Subgroup.mem_bot] at this
      have hexp : y * (k * s) * y⁻¹ * (k * s)⁻¹
          = (y * k * y⁻¹ * k⁻¹) * (k * (y * s * y⁻¹ * s⁻¹) * k⁻¹) := by group
      rw [hexp, hys]
      simpa using hyk
    · exact hEqP
  -- minimality forces `K₁ = K`, hence `K ≤ D ≤ C_Y(R)`: conclusion (a)
  have hK₁eq : K₁ = B.K := B.minimal K₁ hK₁N hK₁K hK₁gen
  have hKcentR : B.K ≤ Subgroup.centralizer (B.frattiniK : Set Y) := by
    rw [← hK₁eq]; exact hK₁D.trans inf_le_right
  have hRcentral : ∀ r ∈ B.frattiniK, ∀ k ∈ B.K, r * k = k * r := fun r hr k hk =>
    (Subgroup.mem_centralizer_iff.mp (hKcentR hk) r hr)
  -- squares and commutators of `K` land in `R = Φ(K)`
  have hksq : ∀ k, k ∈ B.K → k * k ∈ B.frattiniK := fun k hk =>
    Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  -- `group` will not expand `x ^ (4 : ℕ)`; unfold it explicitly wherever it meets a product
  have hp4 : ∀ x : Y, x ^ 4 = x * x * x * x := fun x => by
    rw [pow_succ, pow_succ, pow_succ, pow_one]
  -- class-2 algebra: `(k*l)^4 = k^4 * l^4`, since `R = Φ(K)` is central in `K`
  have hf_hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → (k * l) ^ 4 = k ^ 4 * l ^ 4 :=
    fun k hk l hl => mul_pow_four_of_central B.K hRcentral hk hl
  -- `f k = k^4 ∈ R`
  have hf_mem : ∀ k, k ∈ B.K → k ^ 4 ∈ B.frattiniK := by
    intro k hk
    rw [show k ^ 4 = (k * k) * (k * k) by rw [hp4 k]; group]
    exact mul_mem (hksq k hk) (hksq k hk)
  -- the `Y`-normal subgroup `Kf = {k ∈ K | k^4 = 1}` contains `⁅K,Ñ⁆`, hence all of `K`
  have hf_ker : ∀ k, k ∈ B.K → k ^ 4 = 1 := by
    let Kf : Subgroup Y :=
      { carrier := {k | k ∈ B.K ∧ k ^ 4 = 1}
        one_mem' := ⟨one_mem _, one_pow 4⟩
        mul_mem' := by
          rintro a b ⟨haK, ha⟩ ⟨hbK, hb⟩
          exact ⟨mul_mem haK hbK, by rw [hf_hom a haK b hbK, ha, hb, one_mul]⟩
        inv_mem' := by
          rintro a ⟨haK, ha⟩
          exact ⟨inv_mem haK, by rw [show a⁻¹ ^ 4 = (a ^ 4)⁻¹ by group, ha, inv_one]⟩ }
    have : Kf.Normal := by
      refine ⟨fun a ha g => ⟨B.hK.conj_mem a ha.1 g, ?_⟩⟩
      rw [show (g * a * g⁻¹) ^ 4 = g * a ^ 4 * g⁻¹ by rw [hp4 (g * a * g⁻¹), hp4 a]; group,
        ha.2]; group
    have hKÑKf : ⁅B.K, Ñ⁆ ≤ Kf := by
      rw [Subgroup.commutator_le]
      intro k hk n hn
      refine ⟨?_, ?_⟩
      · rw [commutatorElement_def]
        simpa [mul_assoc] using mul_mem hk (B.hK.conj_mem k⁻¹ (inv_mem hk) n)
      · rw [commutatorElement_def]
        have hkn : k * n * k⁻¹ * n⁻¹ = k * (n * k⁻¹ * n⁻¹) := by group
        have hnkK : n * k⁻¹ * n⁻¹ ∈ B.K := B.hK.conj_mem k⁻¹ (inv_mem hk) n
        rw [hkn, hf_hom k hk _ hnkK,
          show (n * k⁻¹ * n⁻¹) ^ 4 = n * (k ^ 4)⁻¹ * n⁻¹ by
            rw [hp4 (n * k⁻¹ * n⁻¹), hp4 k]; group]
        have hn' : n ∈ Subgroup.centralizer (B.frattiniK : Set Y) := hÑcentR hn
        have hcomm := Subgroup.mem_centralizer_iff.mp hn' (k ^ 4) (hf_mem k hk)
        have hncent : n * (k ^ 4)⁻¹ * n⁻¹ = (k ^ 4)⁻¹ := by
          calc n * (k ^ 4)⁻¹ * n⁻¹ = (n * k ^ 4 * n⁻¹)⁻¹ := by group
            _ = (k ^ 4 * n * n⁻¹)⁻¹ := by rw [← hcomm]
            _ = (k ^ 4)⁻¹ := by group
        rw [hncent]; group
    have hKKf : B.K ≤ Kf := by
      rw [← hK₁eq]; exact Subgroup.normalClosure_le_normal (SetLike.coe_subset_coe.mpr hKÑKf)
    exact fun k hk => (hKKf hk).2
  refine ⟨hRcentral, ?_, hf_ker⟩
  -- `r^2 = 1`: `R = Φ(K)` is generated by squares (`k^4=1`) and commutators (`[k,l]^2=1`),
  -- and `R` is abelian (central in `K ⊇ R`), so the involution property closes under products.
  intro r hr
  exact frattini_sq_eq_one B.K hRcentral hf_ker hr

/-- **Lemma 7.2** at a general residue cardinality — the name-correspondent wrapper.  Clone of
`GQ2.SectionSeven.lemma_7_2` (`Decorations.lean:136`) with `cH` retyped to `Tq q`; the binders
are decorative, so this is `lemma_7_2_core`. -/
theorem lemma_7_2K {q : ℕ} {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (_ : Function.Surjective π) (_ : π.ker = L)
    (cH : ContinuousMonoidHom (Tq q) H) (_ : Function.Surjective cH)
    (B : MinimalBlock L) :
    (∀ r ∈ B.frattiniK, ∀ k ∈ B.K, r * k = k * r) ∧ (∀ r ∈ B.frattiniK, r * r = 1) ∧
      ∀ k ∈ B.K, k ^ 4 = 1 :=
  lemma_7_2_core B

/-- **H_V averaging (Prop. 7.4 step 2)** at a general residue cardinality.  Clone of
`GQ2.SectionSeven.hv_average_helper` (`GQ2/SectionSeven/Prop74.lean:43`).

This is the **only** declaration of the §7 seam that does real work: the four name swaps of the
module docstring all occur in the `Ctil`-construction block.  The ramified/unramified case
split is unchanged — it consumes only normality and oddness of `⟨cH τ⟩`. -/
private theorem hv_average_helperK {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom (Tq q) H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L)
    (σ₀ : Y → ZMod 2)
    (hσ₀hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → σ₀ (k * l) = σ₀ k + σ₀ l)
    (hσ₀KSinv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k)
    (hσ₀YV : ∀ (z : Y), (∀ k, k ∈ B.K → z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S) →
      ∀ k, k ∈ B.K → σ₀ (z * k * z⁻¹) = σ₀ k) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k) := by
  classical
  -- `Y_V := ker(blockPerm)` is the kernel of the `Y`-action on `V = P/S`, normal.  With the module
  -- core (`fixed_zero_of_moves` (A) + `dual_vanish_concrete` (F1)) the whole obligation reduces to
  -- the tame construction: an odd normal `Ctil` that **moves** `V`.
  have hYVn : ((blockPerm B.S B.P B.hS B.hP).ker).Normal :=
    (blockPerm B.S B.P B.hS B.hP).normal_ker
  -- `Y_V` acts trivially on `V = P/S`: `z` fixing `[k⁻¹]` (`k ∈ K ≤ P`) gives `[z,k] ∈ S`.
  have hYVtriv : ∀ z, z ∈ (blockPerm B.S B.P B.hS B.hP).ker → ∀ k, k ∈ B.K →
      z * k * z⁻¹ * k⁻¹ ∈ B.S := by
    intro z hz k hk
    have hkiP : k⁻¹ ∈ B.P := B.hKP (B.K.inv_mem hk)
    have hfix : (QuotientGroup.mk (conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)
          : ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k⁻¹, hkiP⟩ := by
      rw [← blockPerm_apply_mk B.S B.P B.hS B.hP z ⟨k⁻¹, hkiP⟩, MonoidHom.mem_ker.mp hz]
      rfl
    have h1 : (conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)⁻¹ * (⟨k⁻¹, hkiP⟩ : ↥B.P)
        ∈ B.S.subgroupOf B.P := QuotientGroup.eq.mp hfix
    have h2 := Subgroup.mem_subgroupOf.mp h1
    have hcoe : (((conjHom B.P B.hP z ⟨k⁻¹, hkiP⟩)⁻¹ * (⟨k⁻¹, hkiP⟩ : ↥B.P) : ↥B.P) : Y)
        = z * k * z⁻¹ * k⁻¹ := by
      show (z * k⁻¹ * z⁻¹)⁻¹ * k⁻¹ = z * k * z⁻¹ * k⁻¹
      group
    rwa [hcoe] at h2
  have hσ₀YV' : ∀ k, k ∈ B.K → ∀ z, z ∈ (blockPerm B.S B.P B.hS B.hP).ker →
      σ₀ (z * k * z⁻¹) = σ₀ k := by
    intro k hk z hz
    exact hσ₀YV z (fun k' hk' => Subgroup.mem_inf.mpr
      ⟨B.K.mul_mem (B.hK.conj_mem k' hk' z) (B.K.inv_mem hk'), hYVtriv z hz k' hk'⟩) k hk
  -- `K/(K∩S)` is abelian: commutators of `K` lie in `R ≤ K ∩ S ≤ S`.
  have hcomm : ∀ a, a ∈ B.K → ∀ b, b ∈ B.K → a * b * a⁻¹ * b⁻¹ ∈ B.S := by
    intro a ha b hb
    have hR : a * b * a⁻¹ * b⁻¹ ∈ B.frattiniK :=
      Subgroup.subset_closure (Or.inr ⟨a, ha, b, hb, rfl⟩)
    exact (Subgroup.mem_inf.mp (lemma_7_1_head B hR)).2
  -- **Remaining tame construction**: an odd normal `Ctil` that moves `V = P/S`.
  obtain ⟨Ctil, hCtiln, hodd, hmoves⟩ :
      ∃ Ctil : Subgroup Y, Ctil.Normal ∧
        Odd (Nat.card (↥Ctil ⧸ (((blockPerm B.S B.P B.hS B.hP).ker).subgroupOf Ctil))) ∧
        (∃ p, p ∈ B.P ∧ ∃ c, c ∈ Ctil ∧ c⁻¹ * p * c * p⁻¹ ∉ B.S) := by
    -- `L ≤ Y_V` (P1: `L` acts trivially on `V = P/S`), so `ker π = L ≤ Y_V`.
    have hLYV : L ≤ (blockPerm B.S B.P B.hS B.hP).ker :=
      L_le_blockPerm_ker B.S B.P L B.hS B.hP B.hL B.hSP B.hPL B.h2L B.chief
    have hkerYV : π.ker ≤ (blockPerm B.S B.P B.hS B.hP).ker := hkerπ.le.trans hLYV
    -- tame structure of `H = Y/L` via `cH`: `I_H = ⟨cH τ⟩` normal + odd.
    have hgen : Subgroup.closure {cH (tqSigma q), cH (tqTau q)} = ⊤ :=
      GQ2.Dyadic.gen_tq_quotient cH.toMonoidHom cH.continuous_toFun hcH
    have hrel : (cH (tqSigma q))⁻¹ * cH (tqTau q) * cH (tqSigma q) = (cH (tqTau q)) ^ q :=
      GQ2.Dyadic.tame_rel_map_q cH.toMonoidHom
    have hIH_normal : (Subgroup.zpowers (cH (tqTau q))).Normal :=
      GQ2.Dyadic.TameQ.zpowers_normal hgen hrel
    have hIH_odd : Odd (orderOf (cH (tqTau q))) :=
      GQ2.Dyadic.TameQ.odd_order (orderOf_pos _).ne' hq0 hqe hrel
    by_cases hram : ∃ p, p ∈ B.P ∧ ∃ c, c ∈ (Subgroup.zpowers (cH (tqTau q))).comap π ∧
        c⁻¹ * p * c * p⁻¹ ∉ B.S
    · -- **ramified**: `I_H` moves `V`, so `Ctil := π⁻¹⟨cH τ⟩` (odd over `Y_V`, moves `V`).
      exact ⟨(Subgroup.zpowers (cH (tqTau q))).comap π, hIH_normal.comap π,
        odd_preimage_quot π hπ (blockPerm B.S B.P B.hS B.hP).ker hkerYV (cH (tqTau q)) hIH_odd, hram⟩
    · -- **unramified**: `I_H` acts trivially, so `Ctil := ⊤` moves `V` (`nontrivial_action`),
      -- and `Y/Y_V = H_V` is odd (`O₂(H_V) = 1`, `H_V` cyclic).
      refine ⟨⊤, Subgroup.normal_top, ?_, ?_⟩
      · haveI hYVnorm : ((blockPerm B.S B.P B.hS B.hP).ker).Normal :=
          (blockPerm B.S B.P B.hS B.hP).normal_ker
        have hP2 : IsPGroup 2 B.P := fun g => by
          obtain ⟨n, hn⟩ := B.h2L ⟨g.1, B.hPL g.2⟩
          exact ⟨n, by ext; simpa using congrArg Subtype.val hn⟩
        push Not at hram
        -- `I_H`'s preimage acts trivially, so `π⁻¹⟨cH τ⟩ ≤ Y_V`
        have hIHYV : (Subgroup.zpowers (cH (tqTau q))).comap π
            ≤ (blockPerm B.S B.P B.hS B.hP).ker := by
          intro c hc
          rw [MonoidHom.mem_ker]
          refine Equiv.Perm.ext fun q => ?_
          refine QuotientGroup.induction_on q fun p => ?_
          show blockPerm B.S B.P B.hS B.hP c (QuotientGroup.mk p) = QuotientGroup.mk p
          rw [blockPerm_apply_mk, QuotientGroup.eq, Subgroup.mem_subgroupOf]
          have hcoe : (((conjHom B.P B.hP c p)⁻¹ * p : ↥B.P) : Y)
              = c * (p : Y)⁻¹ * c⁻¹ * (p : Y) := by
            show (c * (p : Y) * c⁻¹)⁻¹ * (p : Y) = c * (p : Y)⁻¹ * c⁻¹ * (p : Y); group
          rw [hcoe]
          have h := hram (p : Y)⁻¹ (B.P.inv_mem p.2) c⁻¹ (inv_mem hc)
          have hgoal : c * (p : Y)⁻¹ * c⁻¹ * (p : Y)
              = (c⁻¹)⁻¹ * (p : Y)⁻¹ * c⁻¹ * ((p : Y)⁻¹)⁻¹ := by group
          rw [hgoal]; exact h
        -- so `cH τ ∈ map π Y_V`, hence `Y/Y_V` is cyclic and odd (`unram_odd`)
        obtain ⟨yτ, hyτ⟩ := hπ (cH (tqTau q))
        have hyτIH : yτ ∈ (Subgroup.zpowers (cH (tqTau q))).comap π := by
          rw [Subgroup.mem_comap, hyτ]; exact Subgroup.mem_zpowers _
        have htYV : cH (tqTau q) ∈ ((blockPerm B.S B.P B.hS B.hP).ker).map π :=
          ⟨yτ, hIHYV hyτIH, hyτ⟩
        have hcyc : IsCyclic (Y ⧸ (blockPerm B.S B.P B.hS B.hP).ker) :=
          cyc_YV π hπ _ hkerYV (cH (tqSigma q)) (cH (tqTau q)) hgen htYV
        rw [top_quot_card]
        exact unram_odd B.S B.P B.hS B.hP B.hSP hP2 B.chief hcyc
      · obtain ⟨y, p, hpP, hmove⟩ := B.nontrivial_action
        exact ⟨p, hpP, y⁻¹, Subgroup.mem_top _, by rw [inv_inv]; exact hmove⟩
  -- module core: (A) simplicity `V^Ctil = 0`, then (F1) averaging `(V∨)^Ctil = 0`
  have hfix0 : ∀ k, k ∈ B.K → (∀ c, c ∈ Ctil → c⁻¹ * k * c * k⁻¹ ∈ B.S) → k ∈ B.S :=
    fixed_zero_of_moves B.S B.P B.K Ctil B.hS B.hP hCtiln B.hSP.le B.hKP B.chief hmoves
  have hVC : ∀ φ : Y → ZMod 2, (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → φ (k * l) = φ k + φ l) →
      (∀ k, k ∈ B.K ⊓ B.S → φ k = 0) →
      (∀ (c : Y), c ∈ Ctil → ∀ k, k ∈ B.K → φ (c⁻¹ * k * c) = φ k) →
      ∀ k, k ∈ B.K → φ k = 0 := by
    intro φ hφhom hφ0 hφCinv
    exact dual_vanish_concrete B.S B.K Ctil ((blockPerm B.S B.P B.hS B.hP).ker)
      B.hS B.hK hCtiln hYVn hcomm hYVtriv hodd hfix0 φ hφhom
      (fun k hk hkS => hφ0 k (Subgroup.mem_inf.mpr ⟨hk, hkS⟩)) hφCinv
  exact quotient_average B ((blockPerm B.S B.P B.hS B.hP).ker) Ctil hYVn hCtiln hodd σ₀
    hσ₀hom hσ₀KSinv hσ₀YV' hVC

/-- **Tame extension (Prop 7.4 step 2, front half)** at a general residue cardinality.  Clone of
`GQ2.SectionSeven.key_extension` (`GQ2/SectionSeven/Prop74.lean:171`) — pure pass-through of
`cH`. -/
private theorem key_extensionK {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom (Tq q) H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ∀ (hkk : k * k ∈ B.frattiniK), ψ k = lam ⟨k * k, hkk⟩) := by
  classical
  haveI := B.hK
  haveI := B.hS
  obtain ⟨hcentral, hr2, _hK4⟩ := lemma_7_2K π hπ hkerπ cH hcH B
  have hcomm_kill := lam_comm_vanish B hRN lam hlam_hom hlam_conj
  have lam_one : lam 1 = 0 := by simpa using hlam_hom 1 1
  have hsq : ∀ k, k ∈ B.K → k * k ∈ B.frattiniK := fun k hk =>
    Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)
  set σ : Y → ZMod 2 := fun y => if h : y * y ∈ B.frattiniK then lam ⟨y * y, h⟩ else 0 with hσdef
  -- reduction: `σ` is a hom on `K ∩ S`
  have hσhom : ∀ k, k ∈ B.K ⊓ B.S → ∀ l, l ∈ B.K ⊓ B.S → σ (k * l) = σ k + σ l := by
    intro k hk l hl
    have hkK := (Subgroup.mem_inf.mp hk).1
    have hlK := (Subgroup.mem_inf.mp hl).1
    have hklK : k * l ∈ B.K := mul_mem hkK hlK
    have hcomm : l * k * l⁻¹ * k⁻¹ ∈ B.frattiniK :=
      Subgroup.subset_closure (Or.inr ⟨l, hlK, k, hkK, rfl⟩)
    rw [hσdef]
    simp only [dif_pos (hsq _ hklK), dif_pos (hsq _ hkK), dif_pos (hsq _ hlK)]
    have e : (⟨(k * l) * (k * l), hsq _ hklK⟩ : ↥B.frattiniK)
        = (⟨l * k * l⁻¹ * k⁻¹, hcomm⟩ * ⟨k * k, hsq k hkK⟩) * ⟨l * l, hsq l hlK⟩ :=
      Subtype.ext (by
        show (k * l) * (k * l) = l * k * l⁻¹ * k⁻¹ * (k * k) * (l * l)
        have hc' : k * (l * k * l⁻¹ * k⁻¹) = (l * k * l⁻¹ * k⁻¹) * k :=
          (hcentral (l * k * l⁻¹ * k⁻¹) hcomm k hkK).symm
        calc (k * l) * (k * l)
            = k * (l * k * l⁻¹ * k⁻¹) * (k * l * l) := by group
          _ = (l * k * l⁻¹ * k⁻¹) * k * (k * l * l) := by rw [hc']
          _ = l * k * l⁻¹ * k⁻¹ * (k * k) * (l * l) := by group)
    rw [e, hlam_hom, hlam_hom, hcomm_kill l hlK k hk hcomm, zero_add]
  have hσR : ∀ r, r ∈ B.frattiniK → σ r = 0 := by
    intro r hr
    rw [hσdef]
    simp only [dif_pos (by rw [hr2 r hr]; exact one_mem _ : r * r ∈ B.frattiniK)]
    have : (⟨r * r, by rw [hr2 r hr]; exact one_mem _⟩ : ↥B.frattiniK) = 1 := Subtype.ext (hr2 r hr)
    rw [this, lam_one]
  -- hom extension `σ₀`
  obtain ⟨σ₀, hσ₀hom, hσ₀ext⟩ := sigma0_extends B σ hσhom hσR
  -- `σ₀|_{K∩S}` is `Y`-invariant (`q`-invariance)
  have hσ₀KSinv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k := by
    intro k hk y
    have hkK := (Subgroup.mem_inf.mp hk).1
    have hyk : y * k * y⁻¹ ∈ B.K ⊓ B.S := Subgroup.mem_inf.mpr
      ⟨B.hK.conj_mem k hkK y, B.hS.conj_mem k (Subgroup.mem_inf.mp hk).2 y⟩
    rw [hσ₀ext _ hyk, hσ₀ext _ hk, hσdef]
    simp only [dif_pos (hsq _ (B.hK.conj_mem k hkK y)), dif_pos (hsq k hkK)]
    have e : (⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ : ↥B.frattiniK)
        = ⟨y * (k * k) * y⁻¹, hRN.conj_mem _ (hsq k hkK) y⟩ := Subtype.ext (by group)
    rw [e, hlam_conj y (k * k) (hsq k hkK)]
  -- shear-vanishing: `σ₀` is `Y_V`-invariant
  have hσ₀YV : ∀ (z : Y), (∀ k, k ∈ B.K → z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S) →
      ∀ k, k ∈ B.K → σ₀ (z * k * z⁻¹) = σ₀ k := by
    intro z hz k hk
    have hs : z * k * z⁻¹ * k⁻¹ ∈ B.K ⊓ B.S := hz k hk
    set s := z * k * z⁻¹ * k⁻¹ with hsdef
    have hsK : s ∈ B.K := (Subgroup.mem_inf.mp hs).1
    have hzk : z * k * z⁻¹ = s * k := by rw [hsdef]; group
    have hσs : σ s = 0 := by
      have hqinv : σ (z * k * z⁻¹) = σ k := by
        rw [hσdef]
        simp only [dif_pos (hsq _ (B.hK.conj_mem k hk z)), dif_pos (hsq k hk)]
        have e : (⟨(z * k * z⁻¹) * (z * k * z⁻¹), hsq _ (B.hK.conj_mem k hk z)⟩ : ↥B.frattiniK)
            = ⟨z * (k * k) * z⁻¹, hRN.conj_mem _ (hsq k hk) z⟩ := Subtype.ext (by group)
        rw [e, hlam_conj z (k * k) (hsq k hk)]
      have hsplit : σ (s * k) = σ s + σ k := by
        have hskK : s * k ∈ B.K := mul_mem hsK hk
        have hcomm2 : k * s * k⁻¹ * s⁻¹ ∈ B.frattiniK :=
          Subgroup.subset_closure (Or.inr ⟨k, hk, s, hsK, rfl⟩)
        rw [hσdef]
        simp only [dif_pos (hsq _ hskK), dif_pos (hsq _ hsK), dif_pos (hsq k hk)]
        have e : (⟨(s * k) * (s * k), hsq _ hskK⟩ : ↥B.frattiniK)
            = (⟨k * s * k⁻¹ * s⁻¹, hcomm2⟩ * ⟨s * s, hsq s hsK⟩) * ⟨k * k, hsq k hk⟩ :=
          Subtype.ext (by
            show (s * k) * (s * k) = k * s * k⁻¹ * s⁻¹ * (s * s) * (k * k)
            have hc' : s * (k * s * k⁻¹ * s⁻¹) = (k * s * k⁻¹ * s⁻¹) * s :=
              (hcentral (k * s * k⁻¹ * s⁻¹) hcomm2 s hsK).symm
            calc (s * k) * (s * k)
                = s * (k * s * k⁻¹ * s⁻¹) * (s * k * k) := by group
              _ = (k * s * k⁻¹ * s⁻¹) * s * (s * k * k) := by rw [hc']
              _ = k * s * k⁻¹ * s⁻¹ * (s * s) * (k * k) := by group)
        rw [e, hlam_hom, hlam_hom, hcomm_kill k hk s hs hcomm2, zero_add]
      rw [hzk] at hqinv
      have h2 : σ s + σ k = 0 + σ k := by rw [zero_add]; exact hsplit.symm.trans hqinv
      exact add_right_cancel h2
    rw [hzk, hσ₀hom s hsK k hk, hσ₀ext s hs, hσs, zero_add]
  -- `H_V` averaging
  obtain ⟨ψ, hψhom, hψYinv, hψext⟩ :=
    hv_average_helperK hq0 hqe π hπ hkerπ cH hcH B σ₀ hσ₀hom hσ₀KSinv hσ₀YV
  refine ⟨ψ, hψhom, hψYinv, fun k hk hkk => ?_⟩
  rw [hψext k hk, hσ₀ext k hk]
  simp only [hσdef, dif_pos hkk]

/-- **Prop 7.4, step 2** (`q_λ|_{T₀} = 0`) at a general residue cardinality.  Clone of
`GQ2.SectionSeven.lam_sq_vanish` (`GQ2/SectionSeven/Prop74.lean:280`) — pure pass-through. -/
private theorem lam_sq_vanishK {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom (Tq q) H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩) :
    ∀ t, t ∈ B.K ⊓ B.S → ∀ (h : t * t ∈ B.frattiniK), lam ⟨t * t, h⟩ = 0 := by
  classical
  obtain ⟨ψ, hψhom, hψinv, hψext⟩ :=
    key_extensionK hq0 hqe π hπ hkerπ cH hcH B hRN lam hlam_hom hlam_conj
  intro t₀ ht₀ h
  by_contra hne
  exact invariant_hom_absurd B ψ hψhom hψinv t₀ (Subgroup.mem_inf.mp ht₀).1
    (by rw [hψext t₀ ht₀ h]; exact hne)

/-- **Proposition 7.4 at a general residue cardinality** — the SEAM A endpoint.  Clone of
`GQ2.SectionSeven.prop_7_4` (`GQ2/SectionSeven/Prop74.lean:307`) with the head datum retyped
from `Ttame` to `Tq q`; `cH` is threaded and never inspected, so the body is byte-identical.

This is what the `K`-side Block layer applies at `cH := F.alpha` for a
`F : BoundaryFrameK q P H E`. -/
theorem prop_7_4K {q : ℕ} (hq0 : q ≠ 0) (hqe : Even q)
    {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    (π : Y →* H) (hπ : Function.Surjective π) (hkerπ : π.ker = L)
    (cH : ContinuousMonoidHom (Tq q) H) (hcH : Function.Surjective cH)
    (B : MinimalBlock L)
    (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y : Y) (r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩)
    (hlam_ne : lam ≠ 0) :
    ∃ qbar : (↥B.P ⧸ (B.S.subgroupOf B.P)) → ZMod 2,
      (∀ (k : Y) (hk : k ∈ B.K), lam ⟨k * k, hsq k hk⟩
        = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩)) ∧
      qbar ≠ 0 ∧
      (∀ (y : Y) (p : Y) (hp : p ∈ B.P),
        qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
          = qbar (QuotientGroup.mk ⟨p, hp⟩)) := by
  classical
  haveI := B.hS
  have hB := lam_comm_vanish B hRN lam hlam_hom hlam_conj
  have hA := lam_sq_vanishK hq0 hqe π hπ hkerπ cH hcH B hRN lam hlam_hom hlam_conj
  -- master well-definedness: representatives in the same `S`-coset have equal square-values
  have hwd : ∀ (k k' : Y) (hk : k ∈ B.K) (hk' : k' ∈ B.K),
      (QuotientGroup.mk (⟨k, B.hKP hk⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = QuotientGroup.mk ⟨k', B.hKP hk'⟩ →
      lam ⟨k * k, hsq k hk⟩ = lam ⟨k' * k', hsq k' hk'⟩ := by
    intro k k' hk hk' hmk
    rw [QuotientGroup.eq] at hmk
    have htS : k⁻¹ * k' ∈ B.S := Subgroup.mem_subgroupOf.mp hmk
    have htK : k⁻¹ * k' ∈ B.K := B.K.mul_mem (B.K.inv_mem hk) hk'
    have hcm : k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹ ∈ B.frattiniK :=
      comm_mem_R B (B.K.inv_mem hk) htK
    have e : (⟨k' * k', hsq k' hk'⟩ : ↥B.frattiniK)
        = (⟨k * k, hsq k hk⟩ * ⟨k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹, hcm⟩)
            * ⟨(k⁻¹ * k') * (k⁻¹ * k'), hsq _ htK⟩ := Subtype.ext (by
      show k' * k'
        = k * k * (k⁻¹ * (k⁻¹ * k') * k⁻¹⁻¹ * (k⁻¹ * k')⁻¹) * ((k⁻¹ * k') * (k⁻¹ * k'))
      group)
    rw [e, hlam_hom, hlam_hom,
      hB k⁻¹ (B.K.inv_mem hk) (k⁻¹ * k') (Subgroup.mem_inf.mpr ⟨htK, htS⟩) hcm,
      hA (k⁻¹ * k') (Subgroup.mem_inf.mpr ⟨htK, htS⟩) (hsq _ htK), add_zero, add_zero]
  -- every class has a `K`-representative
  have hdec : ∀ v : ↥B.P ⧸ B.S.subgroupOf B.P,
      ∃ k, ∃ hk : k ∈ B.K, (QuotientGroup.mk (⟨k, B.hKP hk⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P) = v := by
    intro v
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective v
    have hp' : (p : Y) ∈ (B.K : Set Y) * (B.S : Set Y) := by
      rw [← Subgroup.mul_normal B.K B.S, B.gen]
      exact p.2
    obtain ⟨k, hk, s, hs, hks⟩ := hp'
    refine ⟨k, hk, ?_⟩
    rw [QuotientGroup.eq]
    refine Subgroup.mem_subgroupOf.mpr ?_
    show k⁻¹ * (p : Y) ∈ B.S
    have hkp : k⁻¹ * (p : Y) = s := by rw [← hks]; group
    rw [hkp]
    exact hs
  choose w hwK hwmk using hdec
  refine ⟨fun v => lam ⟨w v * w v, hsq (w v) (hwK v)⟩, ?_, ?_, ?_⟩
  · -- the square-map spec
    intro k hk
    exact (hwd (w _) k (hwK _) hk (hwmk _)).symm
  · -- nonzero
    intro h0
    have h0v : ∀ v, lam ⟨w v * w v, hsq (w v) (hwK v)⟩ = 0 := fun v => congrFun h0 v
    have lam_one : lam 1 = 0 := by simpa using hlam_hom 1 1
    -- squares vanish under λ
    have hsqv : ∀ (k : Y) (hk : k ∈ B.K), lam ⟨k * k, hsq k hk⟩ = 0 := by
      intro k hk
      rw [hwd k (w _) hk (hwK _) (hwmk _).symm]
      exact h0v _
    -- commutators vanish under λ
    have hcomm0 : ∀ (a b : Y), a ∈ B.K → b ∈ B.K →
        ∀ h : a * b * a⁻¹ * b⁻¹ ∈ B.frattiniK, lam ⟨a * b * a⁻¹ * b⁻¹, h⟩ = 0 := by
      intro a b ha hb h
      have hx : a⁻¹ ∈ B.K := B.K.inv_mem ha
      have hxy : a⁻¹ * b ∈ B.K := B.K.mul_mem hx hb
      have e : (⟨(a⁻¹ * b) * (a⁻¹ * b), hsq _ hxy⟩ : ↥B.frattiniK)
          = (⟨a⁻¹ * a⁻¹, hsq _ hx⟩ * ⟨a * b * a⁻¹ * b⁻¹, h⟩) * ⟨b * b, hsq b hb⟩ :=
        Subtype.ext (by
          show (a⁻¹ * b) * (a⁻¹ * b) = a⁻¹ * a⁻¹ * (a * b * a⁻¹ * b⁻¹) * (b * b)
          group)
      have h1 := hsqv (a⁻¹ * b) hxy
      rw [e, hlam_hom, hlam_hom, hsqv a⁻¹ hx, hsqv b hb, zero_add, add_zero] at h1
      exact h1
    -- so λ kills all of `R = Φ(K)`, contradicting `hlam_ne`
    let Z' : Subgroup Y :=
      { carrier := {x | ∃ hx : x ∈ B.frattiniK, lam ⟨x, hx⟩ = 0}
        one_mem' := ⟨one_mem _, lam_one⟩
        mul_mem' := by
          rintro a b ⟨ha, la⟩ ⟨hb, lb⟩
          refine ⟨mul_mem ha hb, ?_⟩
          have h := hlam_hom ⟨a, ha⟩ ⟨b, hb⟩
          rw [la, lb, add_zero] at h
          exact h
        inv_mem' := by
          rintro a ⟨ha, la⟩
          refine ⟨inv_mem ha, ?_⟩
          have h := hlam_hom ⟨a, ha⟩ ⟨a⁻¹, inv_mem ha⟩
          have e : (⟨a, ha⟩ * ⟨a⁻¹, inv_mem ha⟩ : ↥B.frattiniK) = 1 := Subtype.ext (by
            show a * a⁻¹ = 1
            group)
          rw [e, lam_one, la, zero_add] at h
          exact h.symm }
    have hRZ : B.frattiniK ≤ Z' := by
      refine (Subgroup.closure_le _).mpr ?_
      rintro x (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
      · exact ⟨sq_mem_R B hk, hsqv k hk⟩
      · exact ⟨comm_mem_R B hk hl, hcomm0 k l hk hl _⟩
    apply hlam_ne
    funext r
    obtain ⟨hr', h0'⟩ := hRZ r.2
    have hre : lam r = lam ⟨r.1, hr'⟩ := rfl
    rw [hre, h0']
    rfl
  · -- `Y`-invariance
    intro y p hp
    have hkK : w (QuotientGroup.mk ⟨p, hp⟩) ∈ B.K := hwK _
    set k := w (QuotientGroup.mk ⟨p, hp⟩) with hkdef
    have hkpS : k⁻¹ * p ∈ B.S := by
      have hkp := hwmk (QuotientGroup.mk (⟨p, hp⟩ : ↥B.P))
      rw [QuotientGroup.eq] at hkp
      exact Subgroup.mem_subgroupOf.mp hkp
    have hmk1 : (QuotientGroup.mk (⟨y * k * y⁻¹, B.hKP (B.hK.conj_mem k hkK y)⟩ : ↥B.P) :
        ↥B.P ⧸ B.S.subgroupOf B.P)
          = QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩ := by
      rw [QuotientGroup.eq]
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (y * k * y⁻¹)⁻¹ * (y * p * y⁻¹) ∈ B.S
      have e : (y * k * y⁻¹)⁻¹ * (y * p * y⁻¹) = y * (k⁻¹ * p) * y⁻¹ := by group
      rw [e]
      exact B.hS.conj_mem _ hkpS y
    have step1 : lam ⟨w (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
          * w (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩), hsq _ (hwK _)⟩
        = lam ⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ :=
      hwd (w _) (y * k * y⁻¹) (hwK _) (B.hK.conj_mem k hkK y) ((hwmk _).trans hmk1.symm)
    have step2 : lam ⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩
        = lam ⟨k * k, hsq k hkK⟩ := by
      have e : (⟨(y * k * y⁻¹) * (y * k * y⁻¹), hsq _ (B.hK.conj_mem k hkK y)⟩ : ↥B.frattiniK)
          = ⟨y * (k * k) * y⁻¹, hRN.conj_mem _ (hsq k hkK) y⟩ := Subtype.ext (by
        show (y * k * y⁻¹) * (y * k * y⁻¹) = y * (k * k) * y⁻¹
        group)
      rw [e]
      exact hlam_conj y (k * k) (hsq k hkK)
    exact step1.trans step2

end GQ2.Dyadic
