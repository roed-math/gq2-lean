/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.LocalGauss.Ramified
import GQ2.Dyadic.LocalGauss.VanishCloseK

/-!
# The general local Gauss theorem (LG5) — packet Thm. 6.15

The LG lane's final assembly.  For a finite extension `K/ℚ₂` of degree `n = [K : ℚ₂]`, presented
as an open subgroup `G_K = ↥U ≤ G_ℚ₂` of index `n`, and a simple faithful `𝔽₂[C]`-module `V`
with `#V = 2^{2m}` marked by a surjection `c : T_{q_K} ↠ C`:

  `#H¹(G_K, V) = 2^{2mn}`,   `arf (Q⁰_{K,V}) = if the marking is ramified then 0 else n mod 2`,

i.e. the Gauss sign of the base determinant form is `+2^{mn}` in the ramified case and
`(−1)^n 2^{mn}` in the unramified case (packet eq. (115)).

## What is assembled

* **the unramified half** — LG3's `prop_6_18_unramified_K` (`LocalGauss/Unramified.lean`), whose
  arf clause is `n mod 2`;
* **the ramified half** — LG4b's `prop_6_18_ramified_K_of_data` (`LocalGauss/Ramified.lean`),
  whose dimension core is already discharged, composed here with
* **the vanishing core** — LG4c's `lemma_6_17_vanish_final_K` (`LocalGauss/VanishCloseK.lean`),
  fed through the marking adapter of §1.

## Contents

* §1 **the marking adapter** `gen_of_markingK` / `rel_of_markingK` / `rho_surjective_of_marking`:
  LG3's marking interface (`c : T_{q_K} ↠ C`) → LG4c's abstract tame pair `(sg, t, f)`.
* §2 **the Euler clause** `card_H1_eq_of_markingK` — clause (a) of the theorem, shared by both
  halves (LG2a's Euler characteristic plus LG3's two collapse clauses).
* §3 **the vanish-discharge wrapper** `prop_6_18_ramified_K_of_package`: LG4c's endpoint plugged
  into the `hvanish` slot of `prop_6_18_ramified_K_of_data`, so the ramified half carries LG4c's
  field-package hypothesis surface rather than a bare `Q0locVanishesOnDeep` binder.
* §4 **the theorem** `local_gauss_K` (packet Thm. 6.15) and its ramification certificate
  `RamifiedCertificate`.
* §5 **zero-count corollaries** `local_gauss_K_zeroCount_add` / `local_gauss_K_zeroCount_sub`.
* §6 **regressions**: the `ℚ₂` (`n = 1`) assembled statement `local_gauss_q2` — whose two
  branches are *literally* the two models' conclusions, pinned by `rfl` against
  `GQ2.DetRamified.prop_6_18_ramified` and `GQ2.UnramifiedModel.prop_6_18_unramified` — the
  `n = 2` unramified `+` sign, and the ramified `+` sign at every `n`.

## The AX3/AX4 surface (the G-AX flip will replace exactly these binders)

Nothing here is an axiom and the census is unchanged.  The field-side interfaces enter as explicit
binders, in the two shapes fixed by LG3 and LG4c:

* `tameFK` / `htameFK` / `hfac` — the tame quotient `G_K ↠ T_{q_K}` factoring `ρ` (AX4's
  normalization; LG3's convention);
* `RamifiedCertificate.k₀` / `.hker₀` / `.htriv` and `.hpkg : InvolutionFieldPackage anc ρ k₀` —
  the splitting field of `ρ` and the per-involution tower (AX3's field-side interface; LG4c's
  `InvolutionFieldPackage` is the single entry point), together with the residue-trivial tame
  lift `.g₀` / `.hg₀` / `.hg₀rt` that LG4b's dimension lane threads.

## Axiom hygiene

Every declaration is parametrized over the duality bundles `D`, `Dker`, so the axiom set is the
union of the two endpoints': the standard three plus `B6`/`B7`/`B9`/`B11a` exactly as inherited
from LG3/LG4b/LG4c.  Nothing new; census unchanged.
-/

namespace GQ2.Dyadic

open GQ2 GQ2.ContCoh GQ2.QuadraticFp2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

/-- The `AlgEquiv`-flavoured spelling of `G_ℚ₂` (LG4a's anchoring convention, binding here). -/
local notation "GalQ2" => Kummer.GaloisGroup ℚ_[2]

/-! ## §1 The marking adapter

LG3 and LG4b present the acting group `C` by a **marking** — a surjection `c : T_{q_K} ↠ C` from
the tame quotient at residue cardinality `q_K = 2^f`.  LG4c's vanishing endpoint instead takes the
**abstract tame pair** `(sg, t)` of PJ1 (`hgen : ⟨sg, t⟩ = ⊤`, `hrel : sg⁻¹ t sg = t^{2^f}`).  The
translation is `sg := c σ`, `t := c τ`, and it is exactly F3's `gen_tq_quotient` plus the image of
the defining relation `tame_rel_map_q`. -/

section Adapter

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C]

/-- **Adapter, generation half**: the images of `σ, τ` generate a discrete quotient `C` of `T_q`
(F3's `gen_tq_quotient`), which is LG4c's `hgen`. -/
theorem gen_of_markingK {q : ℕ} (c : ContinuousMonoidHom (Tq q) C) (hc : Function.Surjective ⇑c) :
    Subgroup.closure {c (tqSigma q), c (tqTau q)} = ⊤ :=
  gen_tq_quotient c.toMonoidHom c.continuous_toFun hc

omit [DiscreteTopology C] in
/-- **Adapter, relation half**: the tame relation `τ^σ = τ^{q}` pushed through the marking, with
`q = 2^f` substituted — LG4c's `hrel`. -/
theorem rel_of_markingK {q f : ℕ} (hqf : q = 2 ^ f) (c : ContinuousMonoidHom (Tq q) C) :
    (c (tqSigma q))⁻¹ * c (tqTau q) * c (tqSigma q) = c (tqTau q) ^ (2 ^ f) := by
  rw [← hqf]
  exact tame_rel_map_q c.toMonoidHom

omit [DiscreteTopology C] in
/-- **Adapter, surjectivity**: a marking `c` of a surjective tame quotient `tameF` makes the
factored representation `ρ = c ∘ tameF` surjective.  (The three copies inlined in LG3's and LG4b's
endpoints are this lemma.) -/
theorem rho_surjective_of_marking {Γ : Type} [Group Γ] [TopologicalSpace Γ] {q : ℕ}
    {tameF : ContinuousMonoidHom Γ (Tq q)} (htameF : Function.Surjective ⇑tameF)
    {c : ContinuousMonoidHom (Tq q) C} (hc : Function.Surjective ⇑c)
    {ρ : ContinuousMonoidHom Γ C} (hfac : ∀ g, ρ g = c (tameF g)) :
    Function.Surjective ⇑ρ := by
  intro y
  obtain ⟨t, ht⟩ := hc y
  obtain ⟨g, hg⟩ := htameF t
  exact ⟨g, by rw [hfac, hg, ht]⟩

end Adapter

/-! ## §2 The Euler clause

Clause (a) of packet Thm. 6.15, `#H¹(G_K, V) = 2^{2mn}`.  Both halves of the theorem derive it the
same way — LG2a's Euler characteristic (`localEulerCharacteristic_open`) together with LG3's two
collapse clauses `#H⁰ = #H² = 1` — so it is factored out here. -/

section Euler

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

omit [DiscreteTopology C] [Finite C] in
/-- **Packet Thm. 6.15(a)**: `#H¹(G_K, V) = 2^{2mn}` for a simple faithful marked module `V` with
`#V = 2^{2m}` over `G_K = ↥U` of index `n = P.n`.  This is the shared Euler input of the two
halves; it does not see the ramification of the marking. -/
theorem card_H1_eq_of_markingK (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hindex : U.index = P.n)
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) := by
  classical
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hqG : ∀ (g : ↥U) (v : V), q (g • v) = q v := fun g v => by rw [hρ]; exact hinv _ v
  haveI hVnt : Nontrivial V := by
    rw [← Finite.one_lt_card_iff_nontrivial, hcard]
    calc (1 : ℕ) < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective_of_marking htameFK hc hfac
  obtain ⟨h₀, hmoves⟩ := exists_smul_neK hsimple (exists_ne (0 : V)) hV2 m hm hcard
  have hH0 : Nat.card (H0 ↥U V) = 1 :=
    card_H0_eq_one_of_surjectiveK ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves
  have hH2 : Nat.card (H2 ↥U V) = 1 :=
    card_H2_eq_one_of_card_H0_eq_oneK V D q hq hns hV2 hqG
      (localEulerCharacteristic_open U hU V).2.2.1 hH0
  exact card_H1_eq_two_pow_of_euler U hU V hH0 hH2 m P.n hindex hcard

end Euler

/-! ## §3 The vanish-discharge wrapper

LG4b's `prop_6_18_ramified_K_of_data` leaves the vanishing core of packet Lemma 6.17 as a bare
`hvanish : Q0locVanishesOnDeep D dat anc ρ` binder; LG4c's `lemma_6_17_vanish_final_K` produces
exactly that proposition.  Composing them (through §1's adapter, which is all the two interfaces
differ by) gives the ramified half of the theorem with **both** §6.3 Kummer cores discharged: what
remains of the ramified hypothesis surface is the field-side data `(k₀, hker₀, htriv, hpkg)`, the
residue-trivial tame lift `(g₀, hg₀, hg₀rt)`, the anchor conditions `(hancinj, hancind)` and the
kernel duality bundle `Dker` — all free at the campaign's instantiation `anc = U.subtype` except
the two AX3-interface entries `hker₀`/`hpkg`. -/

section Wrapper

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **Packet Prop. 6.18 / eq. (115), ramified case, with both §6.3 cores discharged.**

`GQ2.Dyadic.prop_6_18_ramified_K_of_data` (dimension core discharged) composed with
`GQ2.Dyadic.lemma_6_17_vanish_final_K` (vanishing core), the marking translated to LG4c's abstract
tame pair by §1.  The conclusion is the **positive** Gauss sign at every degree,
`#(Q⁰)⁻¹(0) = 2^{2mn−1} + 2^{mn−1}`. -/
theorem prop_6_18_ramified_K_of_package (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hindex : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (anc : ContinuousMonoidHom ↥U GalQ2)
    (hancinj : Function.Injective ⇑anc) (hancind : Topology.IsInducing ⇑anc)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c (tqTau P.qK) • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (Dker : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup ↥U) 2)
    (g₀ : ↥U) (hg₀ : ρ g₀ = c (tqTau P.qK))
    (hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g₀))
    (k₀ : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k₀]
    (htriv : ∀ (g : k₀.fixingSubgroup) (y : ZMod 2), g • y = y)
    (hker₀ : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k₀.fixingSubgroup)
    (hpkg : InvolutionFieldPackage anc ρ k₀)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card {x : H1 ↥U V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * (m * P.n) - 1) + 2 ^ (m * P.n - 1) := by
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective_of_marking htameFK hc hfac
  have hvanish : Q0locVanishesOnDeep D dat anc ρ :=
    lemma_6_17_vanish_final_K D anc hancinj ρ hρsurj P.one_le_f
      (gen_of_markingK c hc) (rel_of_markingK P.qK_eq c) hρ hV2 hfaith hsimple hram
      q hq hinv dat hdat k₀ hker₀ hpkg
  exact prop_6_18_ramified_K_of_data P U hU hindex D tameFK htameFK c hc anc hancinj hancind
    ρ hfac hρ hfaith hsimple hram q hq hns hinv dat hdat Dker g₀ hg₀ hg₀rt k₀ htriv hker₀
    hvanish m hm hcard

end Wrapper

/-! ## §4 The theorem

Packet Thm. 6.15.  The ramified half needs strictly more data than the unramified half (the
anchored splitting field, the involution tower, the residue-trivial tame lift), and that data has
no unramified counterpart, so it enters as a **conditional certificate**: the hypothesis is
"*if* the marking is ramified, here is its certificate".  The unramified alternative needs no
extra data at all — LG3's `hunram` is exactly the negation of the ramification condition — so the
conclusion is uniform: the `ite` of the memo skeleton, whose condition is the ramification of the
marking. -/

section Certificate

variable (P : FieldParameters) (U : Subgroup AbsGalQ2)
  [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
  {C : Type} [Group C] [TopologicalSpace C]
  (V : Type) [AddCommGroup V] [DistribMulAction C V]

/-- **The ramified certificate**: everything the ramified half of packet Thm. 6.15 needs beyond
the marking data shared with the unramified half.  It is the union of the extra binders of LG4b's
`prop_6_18_ramified_K_of_data` and LG4c's `lemma_6_17_vanish_final_K`, with the two files'
splitting fields identified (they carry the *same* hypothesis `hker₀`, so one field serves both).

At the campaign's instantiation `Γ = ↥U`, `anc = U.subtype` the fields `anc`, `hancinj`,
`hancind`, `Dker` are free (`Subtype.val_injective`, `Topology.IsInducing.subtypeVal`, LG2's
`tateDualityKer`); `k₀`, `fd`, `htriv`, `hker₀`, `g₀`, `hg₀`, `hg₀rt` are the `ℚ₂`-side
`GQ2.ResidueLift` data at the open subgroup `ancSubgroup (kerAnc U.subtype ρ) ≤ G_ℚ₂`; and `hpkg`
is **the AX3 field-side interface** — the single entry point the G-AX flip will replace. -/
structure RamifiedCertificate (c : ContinuousMonoidHom (Tq P.qK) C)
    (ρ : ContinuousMonoidHom ↥U C) where
  /-- The marking is ramified: the tame generator `τ` acts nontrivially on `V`. -/
  ram : ∃ v : V, c (tqTau P.qK) • v ≠ v
  /-- The anchor `G_K → G_ℚ₂` of LG4a's anchoring convention (`U.subtype` in the campaign). -/
  anc : ContinuousMonoidHom ↥U GalQ2
  /-- The anchor is injective (LG4c's involution carrier needs the pointwise membership test). -/
  hancinj : Function.Injective ⇑anc
  /-- The anchor is a topological embedding (LG4b's dimension lane). -/
  hancind : Topology.IsInducing ⇑anc
  /-- Tate duality at the splitting group `N_K = ker ρ` (LG2's `tateDualityKer` supplies it). -/
  Dker : TateDualityG ↥(ρ.toMonoidHom.ker : Subgroup ↥U) 2
  /-- A lift of the tame generator `c τ` to `G_K`. -/
  g₀ : ↥U
  /-- `g₀` lifts `c τ`. -/
  hg₀ : ρ g₀ = c (tqTau P.qK)
  /-- `g₀` acts residue-trivially on the anchored splitting group (the `ℚ₂` `ResidueLift` input). -/
  hg₀rt : IsResidueTrivial (ancSubgroup (kerAnc anc ρ)) (anc g₀)
  /-- The finite subfield of `ℚ̄₂` cutting out the anchored splitting group. -/
  k₀ : IntermediateField ℚ_[2] ℚ̄₂
  /-- `k₀/ℚ₂` is finite. -/
  fd : FiniteDimensional ℚ_[2] k₀
  /-- The `𝔽₂`-action of `Gal(ℚ̄₂/k₀)` is trivial. -/
  htriv : ∀ (g : k₀.fixingSubgroup) (y : ZMod 2), g • y = y
  /-- `k₀` cuts out the anchored splitting group `anc(ker ρ) ≤ G_ℚ₂`. -/
  hker₀ : ∀ x : GalQ2, x ∈ ancSubgroup (kerAnc anc ρ) ↔ x ∈ k₀.fixingSubgroup
  /-- **The AX3 field-side interface**: the per-involution tower over `k₀` with its
  norm-matching clause (LG4c's `InvolutionFieldPackage`). -/
  hpkg : InvolutionFieldPackage anc ρ k₀

end Certificate

section Theorem

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- **The ramified Gauss sign is `+` at every degree**: `arf (Q⁰_{K,V}) = 0` whenever the marking
is ramified (packet Prop. 6.12/6.14).  Both §6.3 Kummer cores are discharged from the certificate:
the dimension core by LG4b's `lemma_6_17_dim_final_K`, the vanishing core by LG4c's
`lemma_6_17_vanish_final_K` through §1's adapter. -/
theorem arf_zero_of_ramified_K (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hindex : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (cert : RamifiedCertificate P U V c ρ) :
    arf (Q0loc D dat ρ (V := V)) = 0 := by
  haveI := cert.fd
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective_of_marking htameFK hc hfac
  have hEuler : Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) :=
    card_H1_eq_of_markingK P U hU hindex D tameFK htameFK c hc ρ hfac hρ hsimple q hq hns hinv
      m hm hcard
  haveI hfin : Finite (H1 ↥U V) := (Nat.card_ne_zero.mp (by rw [hEuler]; positivity)).2
  have hdim := lemma_6_17_dim_final_K (V := V) P.qK_eq P.one_le_f cert.anc c hc ρ cert.Dker
    hρsurj hρ hV2 hfaith hsimple cert.ram q hq hns hinv cert.g₀ cert.hg₀ cert.hg₀rt
    cert.k₀ cert.htriv cert.hker₀ cert.hancinj cert.hancind
  have hvanish : Q0locVanishesOnDeep D dat cert.anc ρ :=
    lemma_6_17_vanish_final_K D cert.anc cert.hancinj ρ hρsurj P.one_le_f
      (gen_of_markingK c hc) (rel_of_markingK P.qK_eq c) hρ hV2 hfaith hsimple cert.ram
      q hq hinv dat hdat cert.k₀ cert.hker₀ cert.hpkg
  exact arf_Q0loc_zero_of_deep D q hq hns dat hdat cert.anc ρ hρ (fun cc v => hinv cc v) hV2
    hfin hdim hvanish

open scoped Classical in
/-- **Packet Thm. 6.15 — the local Gauss theorem over a finite extension `K/ℚ₂`.**

Let `K/ℚ₂` have degree `n = [K : ℚ₂]` and residue cardinality `q_K = 2^f` (F1's
`GQ2.Dyadic.FieldParameters`), realised as an open subgroup `G_K = ↥U ≤ G_ℚ₂` of index `n`.  Let
`V` be a simple faithful `𝔽₂[C]`-module with `#V = 2^{2m}`, carrying a nonsingular
`C`-invariant quadratic form `q` and an equivariant factor set `dat`, and let the `G_K`-action
factor as `ρ = c ∘ tameF_K` through a marking `c : T_{q_K} ↠ C` of the tame quotient.  Then

  `#H¹(G_K, V) = 2^{2mn}`  and  `arf (Q⁰_{K,V}) = if the marking is ramified then 0 else n mod 2`.

Equivalently (§5) the Gauss sign of the base determinant form is `+2^{mn}` in the ramified case
and `(−1)^n 2^{mn}` in the unramified case — packet eq. (115).

The `hcert` binder carries the case split: *if* the marking is ramified then a
`RamifiedCertificate` is supplied (unramified markings need nothing beyond the shared data — LG3's
`hunram` is the negation of the `ite` condition).  The AX3/AX4 field-side interfaces are the
binders `tameFK`/`htameFK`/`hfac` and the certificate's `hker₀`/`hpkg`. -/
theorem local_gauss_K (P : FieldParameters) (U : Subgroup AbsGalQ2)
    (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] (hn : U.index = P.n)
    [DistribMulAction ↥U (ZMod 2)] [ContinuousSMul ↥U (ZMod 2)]
    [DistribMulAction ↥U (MuN 2)] [ContinuousSMul ↥U (MuN 2)]
    {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
    [DistribMulAction ↥U V] [ContinuousSMul ↥U V] [DistribMulAction C V]
    (D : TateDualityG ↥U 2)
    (tameFK : ContinuousMonoidHom ↥U (Tq P.qK)) (htameFK : Function.Surjective ⇑tameFK)
    (c : ContinuousMonoidHom (Tq P.qK) C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom ↥U C) (hfac : ∀ g, ρ g = c (tameFK g))
    (hρ : ∀ (g : ↥U) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m))
    (hcert : (∃ v : V, c (tqTau P.qK) • v ≠ v) → Nonempty (RamifiedCertificate P U V c ρ)) :
    Nat.card (H1 ↥U V) = 2 ^ (2 * m * P.n) ∧
      arf (Q0loc D dat ρ (V := V))
        = if ∃ v : V, c (tqTau P.qK) • v ≠ v then 0 else (P.n : ZMod 2) := by
  have hEuler : Nat.card (H1 ↥U V) = 2 ^ (2 * (m * P.n)) :=
    card_H1_eq_of_markingK P U hU hn D tameFK htameFK c hc ρ hfac hρ hsimple q hq hns hinv
      m hm hcard
  refine ⟨by rw [mul_assoc]; exact hEuler, ?_⟩
  by_cases hr : ∃ v : V, c (tqTau P.qK) • v ≠ v
  · rw [if_pos hr]
    obtain ⟨cert⟩ := hcert hr
    exact arf_zero_of_ramified_K P U hU hn D tameFK htameFK c hc ρ hfac hρ hfaith hsimple
      q hq hns hinv dat hdat m hm hcard cert
  · rw [if_neg hr]
    have hunram : ∀ v : V, c (tqTau P.qK) • v = v := fun v => not_not.mp fun hv => hr ⟨v, hv⟩
    exact (prop_6_18_unramified_K P U hU hn D tameFK htameFK c hc ρ hfac hρ hfaith hsimple
      hunram q hq hns hinv dat hdat m hm hcard).1

end Theorem

end GQ2.Dyadic
