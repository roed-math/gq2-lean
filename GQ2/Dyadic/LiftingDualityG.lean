/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
module

public import GQ2.LocalLiftingDuality
public import GQ2.Dyadic.LocalGauss.EulerShapiro
public import GQ2.Dyadic.LocalGauss.Q0
public import GQ2.Dyadic.MarkedRecipBundle

@[expose] public section

/-!
# Prop 5.16 (local lifting duality) over a general local source  (dyadic campaign, ticket CB-SG)

`GQ2/LocalLiftingDuality.lean` proves the paper's `prop_5_16` at `Γ = G_ℚ₂`, hard-wired to the
ambient through its two inputs: **B6** (`GQ2.tateDuality`, the local Tate duality bundle) and
**B7** (`GQ2.Foundations.absGalQ2_localEulerCharacteristic`).  ASK's report recommended making the
proposition `Γ`-generic over a `TateDualityG Γ 2` bundle plus an Euler-characteristic hypothesis
rather than cloning it to `K`; this file does that, and instantiates the result at `G_K`.

## The one place the statement genuinely changes

Clause (ii) is **degree-sensitive**, and the naive `Γ`-generic transcription of it is **false**.
At `ℚ₂` the local Euler characteristic reads `#H¹ = #H⁰ · #H² · 2^{v₂(#A)}`; at `G_K` it reads
`#H¹ = #H⁰ · #H² · 2^{d · v₂(#A)}` with `d = [G_ℚ₂ : G_K] = [K : ℚ₂]`
(`GQ2.Dyadic.absGalK_localEulerCharacteristic`).  Running the `ℚ₂` computation

  `#Z¹ = #H¹ · #B¹ = (#H⁰ · #H² · #Aᵈ) · #B¹ = (#B¹ · #H⁰) · #H² · #Aᵈ = #A^{d+1} · #H²`

therefore gives `#Z¹(A) = #A^{d+1} · #fixedPts C (A′)`, not `#A² · #fixedPts C (A′)`.  The two
agree exactly at `d = 1`, i.e. at `Γ = G_ℚ₂`; for `[K : ℚ₂] > 1` the `ℚ₂` shape is wrong at `K`.
So the generic statement carries a **degree parameter** `d`, and `LocalEulerChar Γ d` below is the
hypothesis, matching `absGalK_localEulerCharacteristic` on the nose at `d = G_K.index`.

The refutation is Lean-checked, not just asserted: `card_Z1_zmod2G_eq_eight_iff` evaluates clause
(ii) at the trivial module `A = 𝔽₂` (where the `ℚ₂` shape predicts `4 · 2 = 8`) and shows the true
value `2^{d+2}` equals `8` **iff** `d = 1`; `card_Z1_zmod2_galK_eq_eight_iff` is the same statement
at `G_K`, i.e. iff `[K : ℚ₂] = 1`.

This is the same `n`-dependence the recursion layer already anticipated: `SourceDataN.hZcard` is
stated as `#Z¹(V) = #V · SN.h1Mult #V` with `(standardNumerics n).h1Mult V = Vⁿ`
(`GQ2/Dyadic/Recursion/Numerics.lean`), i.e. `#V^{n+1}` — SD-R3's "outer/inner" shape rule.  The
generic clause (ii) is that rule's provenance.

## What had to be retyped, and what did not

Of the `ℚ₂` file's declarations, the following are already ambient-free and are **imported and
used verbatim**, not cloned: `card_muN_two`, `muNTwoEquiv`, `card_addHom_zmod2`,
`exists_addHom_ne_zero`, `bijective_cup`, `pow_padicValNat_card`, `dualMap`, `dualMapInv`,
`dualAddEquiv` (+ their `simp` lemmas) and `elemDual_fixed_pointwise`.  Their signatures mention
no group at all — `MuDual n M = M →+ MuN n` and `ElemDual A = A →+ ZMod 2` are group-free.

The remainder is retyped here with `AbsGalQ2 ⇝ Γ`, `tateDuality 2 ⇝ D` and
`absGalQ2_localEulerCharacteristic ⇝ hE`.  Only two proofs needed real thought:
`card_Z1_eqG` (the degree above) and `smul_muN_two_trivialG`.

## `μ₂`-triviality is automatic, at every group

The `ℚ₂` file's `smul_muN_two_trivial` is stated as an arithmetic fact ("`{±1} ⊆ ℚ₂` is fixed by
every `ℚ₂`-algebra automorphism"), but its *proof* uses only `#μ₂ = 2`: a distributive action
fixes `0`, and a bijection of a two-element group fixing `0` fixes the other point.  So it holds
for **any** group acting on `MuN 2`, and no anchoring map `Γ →ₜ* G_ℚ₂` is needed here (LG4a's
convention is satisfied vacuously — no `AbsGalQ2` appears in any anchor type in §1–§7).

## Axiom state

§1–§7 are parametrized over the bundle `D` and the hypothesis `hE`, so they print the standard
three.  §8 is the `G_K` instantiation and is where **B6** (`tateDualityAt`) and **B7** (through
LG2a's *derived* `absGalK_localEulerCharacteristic` — AX2 stays closed) enter.  No new axiom, no
`sorry`; the census stays at eleven.

## Scope

This file is the **substrate** ASK identified, not the four `Phase140/Local.lean` residues
themselves (`tcocycle_card_local`, `hsep_local`, `hpartial_local`, `hZcard_local`).  Those consume
`prop_5_16` and remain owed; what changes is that their `K` versions can now be *generic* proofs
over `prop_5_16_gen` instead of `AbsGalQ2`-clones.  See the ticket report for the accounting.
-/

namespace GQ2.Dyadic.LiftingDualityG

open ContCoh GQ2 FoxH GQ2.LocalLiftingDuality

/-! ## §1 `μ₂`-triviality at an arbitrary group

`MuN 2` has exactly two elements, so every distributive action on it is trivial.  This replaces
the `ℚ₂` file's `smul_muN_two_trivial`, whose statement (though not whose proof) is about
`ℚ₂`-algebra automorphisms. -/

/-- **Any group acts trivially on `μ₂`** — the `Γ`-generic form of
`GQ2.LocalLiftingDuality.smul_muN_two_trivial`.  Only `#μ₂ = 2` is used: `g • ·` is a bijection
fixing `0` of a two-element group, hence the identity. -/
theorem smul_muN_two_trivialG {Γ : Type*} [Group Γ] [DistribMulAction Γ (MuN 2)]
    (g : Γ) (x : MuN 2) : g • x = x := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact smul_zero g
  · have hgx : g • x ≠ 0 := fun h => hx (by rw [← inv_smul_smul g x, h, smul_zero])
    apply muNTwoEquiv.injective
    have key : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    rw [key _ (fun h => hgx (EmbeddingLike.map_eq_zero_iff.mp h)),
      key _ (fun h => hx (EmbeddingLike.map_eq_zero_iff.mp h))]

/-! ## §2 The Euler-characteristic hypothesis

The `Γ`-generic stand-in for **B7**.  `d` is the local degree: `d = 1` recovers the `ℚ₂` shape
(`GQ2.Foundations.absGalQ2_localEulerCharacteristic`, after `one_mul`), and `d = G_K.index`
is `GQ2.Dyadic.absGalK_localEulerCharacteristic` verbatim (§8). -/

/-- **The local Euler–Poincaré characteristic at `Γ`, of degree `d`**: for every finite discrete
`Γ`-module `M`, the groups `Hⁱ(Γ, M)` are finite for `i = 0, 1, 2` and

  `#H¹(Γ, M) = #H⁰(Γ, M) · #H²(Γ, M) · 2 ^ (d · v₂(#M))`.

Stated as a `Prop` over `Γ` rather than assumed of a Galois group: the `ℚ₂` instance is B7 at
`d = 1`, the `K` instance is LG2a's Shapiro-derived theorem at `d = [K : ℚ₂]`. -/
def LocalEulerChar (Γ : Type) [Group Γ] [TopologicalSpace Γ] (d : ℕ) : Prop :=
  ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction Γ M] [ContinuousSMul Γ M] [Finite M],
    Finite (H0 Γ M) ∧ Finite (H1 Γ M) ∧ Finite (H2 Γ M) ∧
      Nat.card (H1 Γ M)
        = Nat.card (H0 Γ M) * Nat.card (H2 Γ M) * 2 ^ (d * padicValNat 2 (Nat.card M))

section Generic

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)]

/-! ## §3 Two-torsion of `H¹` and `H²`

Verbatim retypes of `H1_two_torsion_gen` / `H2_two_torsion_gen` (only the group name changes). -/

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
/-- **Two-torsion of `H¹`** for a `2`-torsion coefficient module, at a general `Γ`. -/
theorem H1_two_torsionG {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction Γ M] [ContinuousSMul Γ M]
    (hM₂ : ∀ m : M, m + m = 0) (z : H1 Γ M) : z + z = 0 := by
  obtain ⟨w, rfl⟩ := H1mk_surjective (G := Γ) (M := M) z
  rw [← map_add, show (w + w : ↥(Z1 Γ M)) = 0 from Subtype.ext (funext fun g => hM₂ _), map_zero]

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] in
/-- **Two-torsion of `H²`** for a `2`-torsion coefficient module, at a general `Γ`. -/
theorem H2_two_torsionG {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
    [DistribMulAction Γ M] [ContinuousSMul Γ M]
    (hM₂ : ∀ m : M, m + m = 0) (z : H2 Γ M) : z + z = 0 := by
  obtain ⟨w, rfl⟩ := H2mk_surjective (G := Γ) (M := M) z
  rw [← map_add, show (w + w : ↥(Z2 Γ M)) = 0 from Subtype.ext (funext fun p => hM₂ _), map_zero]

/-! ## §4 Degree-`0` transport

`#H⁰(Γ, MuDual 2 A) = #fixedPts C (ElemDual A)`.  The transport map itself (`dualAddEquiv`) is
imported: it is group-free.  What is retyped is the equivariance bookkeeping. -/

section Bridge

variable {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  {ρ : ContinuousMonoidHom Γ C} (hρ : Function.Surjective ρ)
  {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction C A] [DistribMulAction Γ A] [ContinuousSMul Γ A]
  (hcomp : ∀ (γ : Γ) (a : A), γ • a = ρ γ • a)

/-- `dualMapInv` computes pointwise (`rfl`; the `ℚ₂` file's twin is `private`). -/
private theorem dualMapInv_applyG {A : Type} [AddCommGroup A] (lam : ElemDual A) (a : A) :
    dualMapInv lam a = muNTwoEquiv.symm (lam a) := rfl

/-- `dualAddEquiv` computes pointwise (`rfl`; the `ℚ₂` file's twin is `private`). -/
private theorem dualAddEquiv_applyG {A : Type} [AddCommGroup A] (φ : MuDual 2 A) (a : A) :
    dualAddEquiv φ a = muNTwoEquiv (φ a) := rfl

include hρ hcomp in
omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (MuN 2)] [DiscreteTopology C] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [ContinuousSMul Γ A] in
/-- The `Γ`-invariance of a `μ₂`-dual `φ`, transported to `C`-orbits through `ρ`. -/
theorem muDual_inv_pointwiseG {φ : MuDual 2 A} (hφ : ∀ γ : Γ, γ • φ = φ) (c : C) (a : A) :
    φ (c • a) = φ a := by
  obtain ⟨γ, hγ⟩ := hρ c
  have h := DFunLike.congr_fun (hφ γ) (c • a)
  rw [muDual_smul_apply, smul_muN_two_trivialG] at h
  have hid : γ⁻¹ • (c • a) = a := by rw [hcomp, ← hγ, map_inv, inv_smul_smul]
  rw [hid] at h
  exact h.symm

include hρ hcomp in
omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (MuN 2)] [DiscreteTopology C] [Finite C]
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [ContinuousSMul Γ A] in
/-- **Degree-0 transport at a general `Γ`**: the `Γ`-invariants of the `μ₂`-dual biject with the
`C`-invariants of the `𝔽₂`-dual. -/
theorem card_H0_muDual_eq_fixedPtsG :
    Nat.card (H0 Γ (MuDual 2 A)) = Nat.card (fixedPts C (ElemDual A)) := by
  refine Nat.card_congr ⟨fun φ => ⟨dualMap φ.1, fun c => ?_⟩,
    fun lam => ⟨dualMapInv lam.1, fun γ => ?_⟩, fun φ => ?_, fun lam => ?_⟩
  · refine DFunLike.ext _ _ fun a => ?_
    rw [ElemDual.smul_apply, LocalLiftingDuality.dualMap_apply,
      LocalLiftingDuality.dualMap_apply, muDual_inv_pointwiseG hρ hcomp φ.2 c⁻¹ a]
  · refine DFunLike.ext _ _ fun a => ?_
    rw [muDual_smul_apply, smul_muN_two_trivialG, dualMapInv_applyG, dualMapInv_applyG]
    congr 1
    rw [hcomp, elemDual_fixed_pointwise lam.2 (ρ γ⁻¹) a]
  · exact Subtype.ext (DFunLike.ext _ _ fun a => muNTwoEquiv.symm_apply_apply _)
  · exact Subtype.ext (DFunLike.ext _ _ fun a => muNTwoEquiv.apply_symm_apply _)

/-! ## §5 Clauses (i) and (ii): the numeric content -/

include hρ hcomp in
omit [DiscreteTopology C] [Finite C] in
/-- **Clause (i)** at a general `Γ`: `#H²(A) = #fixedPts C (A′)`.  B6's `(0,2)` perfectness, the
self-dual count `#Hom(H²(A), 𝔽₂) = #H²(A)`, and §4.  The Euler hypothesis is used only for the
finiteness of `H²`. -/
theorem card_H2_eq_fixedPtsG (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (H2 Γ A) = Nat.card (fixedPts C (ElemDual A)) := by
  haveI : Finite (H2 Γ A) := (hE A).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  calc Nat.card (H2 Γ A)
      = Nat.card (H2 Γ A →+ ZMod 2) :=
        (card_addHom_zmod2 (H2_two_torsionG (Γ := Γ) hA₂)).symm
    _ = Nat.card (H0 Γ (MuDual 2 A)) :=
        (TateDualityG.card_H0_dual D A htor).symm
    _ = Nat.card (fixedPts C (ElemDual A)) := card_H0_muDual_eq_fixedPtsG hρ hcomp

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [ContinuousSMul Γ A] in
/-- `ker(d⁰) = H⁰`, at a general `Γ`. -/
theorem dZero_ker_eq_H0G : (dZero Γ A).ker = H0 Γ A := by
  ext m
  rw [AddMonoidHom.mem_ker]
  constructor
  · intro h g
    have hg : (dZero Γ A) m g = 0 := by rw [h]; rfl
    rwa [show (dZero Γ A) m g = g • m - m from rfl, sub_eq_zero] at hg
  · intro h
    ext g
    rw [show (dZero Γ A) m g = g • m - m from rfl, h g, sub_self]; rfl

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)]
  [ContinuousSMul Γ (MuN 2)] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [ContinuousSMul Γ A] in
/-- `#A = #B¹ · #H⁰` (first isomorphism theorem for `d⁰`), at a general `Γ`. -/
theorem card_A_eq_B1_mul_H0G : Nat.card A = Nat.card (B1 Γ A) * Nat.card (H0 Γ A) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup (H0 Γ A)
  rw [show Nat.card (A ⧸ H0 Γ A) = Nat.card (B1 Γ A) from ?_] at h
  · exact h
  · rw [← dZero_ker_eq_H0G]
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivRange (dZero Γ A)).toEquiv

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (MuN 2)] [ContinuousSMul Γ (MuN 2)] [Finite A] in
/-- `#Z¹ = #H¹ · #B¹` (Lagrange on `H¹ = Z¹/B¹`), at a general `Γ`. -/
theorem card_Z1_eq_H1_mul_B1G : Nat.card (Z1 Γ A) = Nat.card (H1 Γ A) * Nat.card (B1 Γ A) := by
  have h := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    ((B1 Γ A).addSubgroupOf (Z1 Γ A))
  rwa [Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe (B1_le_Z1 (G := Γ) (M := A))).toEquiv]
    at h

include hρ hcomp in
omit [DiscreteTopology C] [Finite C] in
/-- **Clause (ii) at a general `Γ` of degree `d`**: `#Z¹(A) = #A^{d+1} · #fixedPts C (A′)`.

⚠ **This is where the `ℚ₂` statement is degree-sensitive.**  The `ℚ₂` clause reads `#A²`; the
correct generic exponent is `d + 1`, with `d` the degree in the Euler characteristic
(`d = 1` at `G_ℚ₂`, `d = [K : ℚ₂]` at `G_K`).  A verbatim `K`-clone of the `ℚ₂` clause would be
false for `[K : ℚ₂] > 1`. -/
theorem card_Z1_eqG (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0) :
    Nat.card (Z1 Γ A) = Nat.card A ^ (d + 1) * Nat.card (fixedPts C (ElemDual A)) := by
  have hEuler := (hE A).2.2.2
  rw [card_Z1_eq_H1_mul_B1G, hEuler, pow_mul', pow_padicValNat_card hA₂,
    card_H2_eq_fixedPtsG hρ hcomp D hE hA₂, pow_succ,
    show Nat.card (H0 Γ A) * Nat.card (fixedPts C (ElemDual A)) * Nat.card A ^ d
        * Nat.card (B1 Γ A)
      = Nat.card A ^ d * Nat.card (fixedPts C (ElemDual A))
          * (Nat.card (B1 Γ A) * Nat.card (H0 Γ A)) from by ring,
    ← card_A_eq_B1_mul_H0G]
  ring

end Bridge

/-! ## §6 Clause (iii): `#H²(Γ, 𝔽₂) = 2`

Shorter than the `ℚ₂` route (which counts through `MuDual`): B6's invariant map `H²(Γ, μ₂) ≃+ ℤ/2`
composed with the trivial-action coefficient transport `𝔽₂ ≃+ μ₂` already *is* an isomorphism
`H²(Γ, 𝔽₂) ≃+ 𝔽₂`.  No Euler input. -/

section ScalarH2

variable [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [ContinuousSMul Γ (MuN 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- The coefficient transport `𝔽₂ ≃+ μ₂` is `Γ`-equivariant (both actions are trivial). -/
theorem muNTwoEquiv_symm_equivariantG (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    ∀ (g : Γ) (m : ZMod 2), muNTwoEquiv.symm (g • m) = g • muNTwoEquiv.symm m :=
  fun g m => by rw [smul_muN_two_trivialG, htriv]

/-- **The invariant map in `𝔽₂`-coefficients at a general `Γ`**: `H²(Γ, 𝔽₂) ≃+ 𝔽₂`. -/
noncomputable def invG (D : TateDualityG Γ 2) (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    H2 Γ (ZMod 2) ≃+ ZMod 2 :=
  (H2congr muNTwoEquiv.symm (muNTwoEquiv_symm_equivariantG htriv)).trans D.inv

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Clause (iii)** at a general `Γ`: `#H²(Γ, 𝔽₂) = 2`. -/
theorem card_H2_zmod2_eq_twoG (D : TateDualityG Γ 2)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) : Nat.card (H2 Γ (ZMod 2)) = 2 := by
  rw [Nat.card_congr (invG D htriv).toEquiv, Nat.card_zmod]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- `H²(Γ, 𝔽₂)` is finite — from clause (iii), so this too is Euler-free. -/
theorem finite_H2_zmod2G (D : TateDualityG Γ 2)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) : Finite (H2 Γ (ZMod 2)) :=
  Finite.of_equiv _ (invG D htriv).symm.toEquiv

/-! ### The witness that clause (ii) is degree-sensitive

Evaluated at the trivial module `A = 𝔽₂` (and the trivial `C`, where
`fixedPts C (ElemDual 𝔽₂) = ElemDual 𝔽₂` has two elements), clause (ii) predicts
`#Z¹(Γ, 𝔽₂) = #𝔽₂^{d+1} · 2 = 2^{d+2}`, whereas a verbatim `ℚ₂`-clone predicting `#A² · #fixedPts`
would say `4 · 2 = 8`.  The next two theorems compute the true value and show the `ℚ₂` value is
attained **exactly** at `d = 1`.  Independent cross-check: at `Γ = G_K` the true value `2^{n+2}`
is `GQ2.Dyadic.card_hom_zmodTwo_galK` (`#Hom_c(G_K, 𝔽₂) = 2^{[K:ℚ₂]+2}`, proved from B7 by a
different route in `GQ2/Dyadic/Instances/KSupply.lean`). -/

/-- `#Z¹(Γ, 𝔽₂) = 2^{d+2}` for a trivial `𝔽₂`-action — clause (ii) at `A = 𝔽₂`, computed. -/
theorem card_Z1_zmod2G (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) : Nat.card (Z1 Γ (ZMod 2)) = 2 ^ (d + 2) := by
  have hH0 : Nat.card (H0 Γ (ZMod 2)) = 2 := by
    rw [show H0 Γ (ZMod 2) = ⊤ from eq_top_iff.mpr fun m _ g => htriv g m,
      Nat.card_congr (AddSubgroup.topEquiv (G := ZMod 2)).toEquiv, Nat.card_zmod]
  have hB1 : Nat.card (B1 Γ (ZMod 2)) = 1 := by
    have h := card_A_eq_B1_mul_H0G (Γ := Γ) (A := ZMod 2)
    rw [Nat.card_zmod, hH0] at h
    omega
  rw [card_Z1_eq_H1_mul_B1G, (hE (ZMod 2)).2.2.2, hH0, card_H2_zmod2_eq_twoG D htriv, hB1,
    Nat.card_zmod, show padicValNat 2 2 = 1 from padicValNat.self one_lt_two, mul_one, mul_one,
    pow_add]
  ring

/-- **The refutation.**  The `ℚ₂` clause-(ii) value `#A² · #fixedPts = 8` at `A = 𝔽₂` holds
**iff** `d = 1`.  So a verbatim `K`-clone of `GQ2.FoxH.prop_5_16`'s clause (ii) is *false* for
every `K/ℚ₂` of degree `> 1`, and the degree parameter is not optional. -/
theorem card_Z1_zmod2G_eq_eight_iff (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    Nat.card (Z1 Γ (ZMod 2)) = 2 ^ 2 * 2 ↔ d = 1 := by
  rw [card_Z1_zmod2G D hE htriv, show (2 : ℕ) ^ 2 * 2 = 2 ^ 3 by norm_num]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := Nat.pow_right_injective (le_refl 2) h
  omega

end ScalarH2

/-! ## §7 Clauses (iv)–(vi): perfectness of the evaluation cup pairings

The `ℚ₂` argument is structurally ambient-free: graded-commutativity in characteristic two carries
B6's `μ₂`-side perfectness to the `𝔽₂`-side transpose, and `bijective_cup` (imported) closes by
counting.  Only the `AbsGalQ2` occurrences and the two axiom appeals change. -/

section CupClauses

variable {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
  [DistribMulAction Γ A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [DistribMulAction Γ (ElemDual A)] [ContinuousSMul Γ (ElemDual A)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [ContinuousSMul Γ (MuN 2)]
  [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- `muNTwoEquiv : μ₂ ≃+ 𝔽₂` is `Γ`-equivariant (both actions are trivial). -/
theorem muNTwoEquiv_equivariantG (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    ∀ (g : Γ) (m : MuN 2), muNTwoEquiv (g • m) = g • muNTwoEquiv m :=
  fun g m => by rw [smul_muN_two_trivialG]; exact (htriv g (muNTwoEquiv m)).symm

omit [TopologicalSpace Γ] [IsTopologicalGroup Γ] [ContinuousSMul Γ (MuN 2)]
  [TopologicalSpace A] [DiscreteTopology A] [Finite A] [ContinuousSMul Γ A]
  [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
  [ContinuousSMul Γ (ElemDual A)] [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
/-- `dualAddEquiv : MuDual 2 A ≃+ ElemDual A` is `Γ`-equivariant. -/
theorem edEquivariantG
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) :
    ∀ (g : Γ) (φ : MuDual 2 A), dualAddEquiv (g • φ) = g • dualAddEquiv φ := by
  intro g φ
  refine DFunLike.ext _ _ fun a => ?_
  have hEDsmul : (g • dualAddEquiv φ) a = (dualAddEquiv φ) (g⁻¹ • a) := by
    have h := hpair g (g⁻¹ • a) (dualAddEquiv φ)
    rwa [smul_inv_smul, dualEval_apply, dualEval_apply, htriv] at h
  rw [hEDsmul]
  simp only [dualAddEquiv_applyG, muDual_smul_apply, smul_muN_two_trivialG]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The shared cup-clause skeleton** at a general `Γ` — `bijective_cup` applied to the
`τ`-transported opposite currying, where `τ = invG D htriv`. -/
private theorem bijective_cup_of_commG {V W Y : Type*} [AddCommGroup V] [AddCommGroup W]
    [AddCommGroup Y] [Finite V] [Finite W] (D : TateDualityG Γ 2)
    (hV₂ : ∀ v : V, v + v = 0) (hW₂ : ∀ w : W, w + w = 0) (hcardVW : Nat.card V = Nat.card W)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (Φ : V →+ W →+ H2 Γ (ZMod 2)) (Ψ : Y →+ V →+ H2 Γ (MuN 2)) (e : Y ≃+ W)
    (hP : Function.Surjective fun d'' : Y => D.inv.toAddMonoidHom.comp (Ψ d''))
    (hcomm : ∀ (c : V) (d'' : Y),
      Φ c (e d'') = H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv) (Ψ d'' c)) :
    Function.Bijective ⇑Φ := by
  haveI : Finite (H2 Γ (ZMod 2)) := finite_H2_zmod2G D htriv
  let τ : H2 Γ (ZMod 2) ≃+ ZMod 2 :=
    (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv)).symm.trans D.inv
  have hτapp : ∀ X, τ (H2congr muNTwoEquiv (muNTwoEquiv_equivariantG htriv) X) = D.inv X :=
    fun X => by simp [τ]
  have hsurj : ∀ f : V →+ ZMod 2, ∃ w : W, ∀ c : V, τ (Φ c w) = f c := by
    intro f
    obtain ⟨d'', hd''⟩ := hP f
    refine ⟨e d'', fun c => ?_⟩
    rw [hcomm c d'', hτapp]
    exact DFunLike.congr_fun hd'' c
  exact bijective_cup hV₂ hW₂ hcardVW τ Φ hsurj

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Clause (iv)** at a general `Γ`: the `(1,1)` evaluation cup is bijective. -/
theorem bijective_cup11_dualEvalG (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : H1 Γ A => cup11 (dualEval A) hpair c) := by
  haveI : Finite (H1 Γ A) := (hE A).2.1
  haveI : Finite (H1 Γ (ElemDual A)) := (hE (ElemDual A)).2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have heD := edEquivariantG hpair htriv
  refine bijective_cup_of_commG D (H1_two_torsionG hA₂)
    (H1_two_torsionG ElemDual.add_self_eq_zero)
    (by rw [← Nat.card_congr (H1congr dualAddEquiv heD).toEquiv,
      TateDualityG.card_H1_dual D A htor,
      card_addHom_zmod2 (H1_two_torsionG (Γ := Γ) hA₂)])
    htriv (cup11 (dualEval A) hpair)
    (cup11 (muDualPairing 2 A) (muDualPairing_equivariant 2 A)) (H1congr dualAddEquiv heD)
    ((D.perfect11 A htor).2) (fun c d'' => ?_)
  rw [cup11_comm (dualEval A) hpair (fun p => CharTwo.add_self_eq_zero p) c
    (H1congr dualAddEquiv heD d'')]
  obtain ⟨a', rfl⟩ := H1mk_surjective (G := Γ) (M := MuDual 2 A) d''
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := Γ) (M := A) c
  rw [H1congr_mk, cup11_mk_mk, cup11_mk_mk, H2congr_mk]
  congr 1

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Clause (v)** at a general `Γ`: the `(0,2)` evaluation cup is bijective. -/
theorem bijective_cup02_dualEvalG (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : ↥(H0 Γ A) => cup02 (dualEval A) hpair c) := by
  haveI : Finite (H2 Γ (ElemDual A)) := (hE (ElemDual A)).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have h0₂ : ∀ v : ↥(H0 Γ A), v + v = 0 := fun v => Subtype.ext (by simpa using hA₂ v.1)
  have heD := edEquivariantG hpair htriv
  refine bijective_cup_of_commG D h0₂ (H2_two_torsionG ElemDual.add_self_eq_zero)
    (by rw [← Nat.card_congr (H2congr dualAddEquiv heD).toEquiv,
      TateDualityG.card_H2_dual D A htor, card_addHom_zmod2 h0₂])
    htriv (cup02 (dualEval A) hpair)
    (cup20 (muDualPairing 2 A) (muDualPairing_equivariant 2 A)) (H2congr dualAddEquiv heD)
    ((D.perfect20 A htor).2) (fun c d'' => ?_)
  rw [cup02_eq_cup20_flip (dualEval A) hpair c (H2congr dualAddEquiv heD d'')]
  obtain ⟨a', rfl⟩ := H2mk_surjective (G := Γ) (M := MuDual 2 A) d''
  rw [H2congr_mk, cup20_mk_mk, cup20_mk_mk, H2congr_mk]
  congr 1

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Clause (vi)** at a general `Γ`: the `(2,0)` evaluation cup is bijective. -/
theorem bijective_cup20_dualEvalG (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (hA₂ : ∀ a : A, a + a = 0)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    Function.Bijective (fun c : H2 Γ A => cup20 (dualEval A) hpair c) := by
  haveI : Finite (H2 Γ A) := (hE A).2.2.1
  have htor : ∀ x : A, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact hA₂ x
  have hED0₂ : ∀ w : ↥(H0 Γ (ElemDual A)), w + w = 0 :=
    fun w => Subtype.ext (by simpa using ElemDual.add_self_eq_zero w.1)
  have heD := edEquivariantG hpair htriv
  refine bijective_cup_of_commG D (H2_two_torsionG hA₂) hED0₂
    (by rw [← Nat.card_congr (H0congr dualAddEquiv heD).toEquiv,
      TateDualityG.card_H0_dual D A htor,
      card_addHom_zmod2 (H2_two_torsionG (Γ := Γ) hA₂)])
    htriv (cup20 (dualEval A) hpair)
    (cup02 (muDualPairing 2 A) (muDualPairing_equivariant 2 A)) (H0congr dualAddEquiv heD)
    ((D.perfect02 A htor).2) (fun c d'' => ?_)
  rw [cup20_eq_cup02_flip (dualEval A) hpair c (H0congr dualAddEquiv heD d'')]
  obtain ⟨b, rfl⟩ := H2mk_surjective (G := Γ) (M := A) c
  rw [cup02_mk_mk, cup02_mk_mk, H2congr_mk]
  congr 1

end CupClauses

/-! ## §8 Assembly -/

/-- **Prop 5.16 (local lifting duality) at a general local source `Γ` of degree `d`** — the
`Γ`-generic form of `GQ2.FoxH.prop_5_16`, over a Tate-duality bundle `D : TateDualityG Γ 2` and
an Euler-characteristic hypothesis `hE : LocalEulerChar Γ d`.  No `AbsGalQ2`, no `G_K`.

Clauses (i), (iii)–(vi) are the `ℚ₂` statements verbatim with `G_ℚ₂ ⇝ Γ`.  **Clause (ii) is
`#A^{d+1}`, not `#A²`** — see the module docstring; the `ℚ₂` reading is the `d = 1` case. -/
theorem prop_5_16_gen {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (D : TateDualityG Γ 2) {d : ℕ} (hE : LocalEulerChar Γ d)
    (ρ : ContinuousMonoidHom Γ C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction Γ A] [ContinuousSMul Γ A]
    (hcomp : ∀ (γ : Γ) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction Γ (ElemDual A)] [ContinuousSMul Γ (ElemDual A)]
    (_hcompD : ∀ (γ : Γ) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : Γ) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 Γ A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 Γ A) = Nat.card A ^ (d + 1) * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 Γ (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 Γ A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : ↥(H0 Γ A) => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 Γ A => cup20 (dualEval A) hpair c) :=
  ⟨card_H2_eq_fixedPtsG hρ hcomp D hE hA₂, card_Z1_eqG hρ hcomp D hE hA₂,
    card_H2_zmod2_eq_twoG D htriv, bijective_cup11_dualEvalG D hE hA₂ htriv hpair,
    bijective_cup02_dualEvalG D hE hA₂ htriv hpair, bijective_cup20_dualEvalG D hE hA₂ htriv hpair⟩

end Generic

/-! ## §9 Faithfulness: the generic statement re-derives the `ℚ₂` original

A generalization is only worth the retype if it is not weaker.  `LocalEulerChar AbsGalQ2 1` **is**
B7 (after `one_mul`), and `prop_5_16_gen` at `(Γ, d) = (G_ℚ₂, 1)` gives back `GQ2.FoxH.prop_5_16`'s
six clauses on the nose — including `#Z¹ = #A²`, since `d + 1 = 2` there.  So the degree parameter
is a genuine generalization of the `ℚ₂` clause, not a divergence from it. -/

section Faithfulness

/-- **B7 is `LocalEulerChar` at degree `1`.** -/
theorem localEulerChar_absGalQ2 : LocalEulerChar AbsGalQ2 1 := by
  intro M _ _ _ _ _ _
  obtain ⟨h0, h1, h2, hc⟩ := Foundations.absGalQ2_localEulerCharacteristic M
  exact ⟨h0, h1, h2, by rw [hc, one_mul]⟩

/-- **The `ℚ₂` `prop_5_16`, re-derived from the generic one** — literally
`GQ2.FoxH.prop_5_16`'s conclusion, obtained from `prop_5_16_gen` at `Γ = G_ℚ₂`, `d = 1`.
Parametrized over the bundle, so it consumes B7 but not B6. -/
theorem prop_5_16_of_gen {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (D : TateDuality 2) (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    (hcomp : ∀ (γ : AbsGalQ2) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction AbsGalQ2 (ElemDual A)] [ContinuousSMul AbsGalQ2 (ElemDual A)]
    (hcompD : ∀ (γ : AbsGalQ2) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction AbsGalQ2 (ZMod 2)] [ContinuousSMul AbsGalQ2 (ZMod 2)]
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : AbsGalQ2) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 AbsGalQ2 A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 AbsGalQ2 A) = Nat.card A ^ 2 * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 AbsGalQ2 A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : ↥(H0 AbsGalQ2 A) => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 AbsGalQ2 A => cup20 (dualEval A) hpair c) :=
  prop_5_16_gen D localEulerChar_absGalQ2 ρ hρ hcomp hA₂ hcompD htriv hpair

end Faithfulness

/-! ## §10 The instantiation at `G_K`

The two `ℚ₂` inputs of `prop_5_16` are both available at `G_K` for `K/ℚ₂` finite, which is what
made the generic route cheaper than a clone:

* **B6** — `tateDualityAt` applies because `G_K` is an open finite-index subgroup of `G_ℚ₂`
  (LG2's `subgroup_isLocalDualizingGroup`);
* **B7** — LG2a's `absGalK_localEulerCharacteristic`, a *theorem* (Shapiro at the coinduced
  module), so `AX2` stays closed and the census is unchanged.

Everything is spelled at `GalK K = ↥(GalKsub K)`, the `MarkedRecipBundle` R6 instance pin that
`KSupply`'s carrier `galKProfinite K` unfolds to by `rfl`.  Consumers holding an
`AS1 DyadicLocalInput` should use `prop_5_16_galK_of` with the record's own `duality` field, so
that the bundle is the record's; `prop_5_16_galK` builds one from B6 when there is no record. -/

section GalKInstance

variable (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]

/-- **The Euler-characteristic hypothesis holds at `G_K`, at degree `[G_ℚ₂ : G_K]`** — LG2a's
Shapiro-derived Euler characteristic, read as a `LocalEulerChar`.  B7 (derived), no new axiom.

Routed through `localEulerCharacteristic_open` at the subgroup `GalKsub K` rather than through
`absGalK_localEulerCharacteristic`: the latter is spelled at `↥K.fixingSubgroup`, which is the
*same type* as `GalK K` through a different instance path (`MarkedRecipBundle`'s R6 trap), so its
`DistribMulAction` argument does not synthesize here.  The open-subgroup form is already at the
`Subgroup AbsGalQ2` spelling `GalKsub` pins, and applies directly. -/
theorem localEulerChar_galK : LocalEulerChar (GalK K) (GalKsub K).index := by
  intro M _ _ _ _ _ _
  haveI := finite_quotient_of_isOpen (GalKsub K) (isOpen_fixingSubgroup K)
  exact localEulerCharacteristic_open (GalKsub K) (isOpen_fixingSubgroup K) M

/-- **The B6 bundle at `G_K`**, at the `GalK` spelling.  Same axiom application as
`GQ2.Dyadic.FieldData.tateDualityGalK`; restated here only because that file is plain-import and
this one is `module`-style. -/
noncomputable def tateDualityGalK : TateDualityG (GalK K) 2 :=
  haveI : (GalKsub K).FiniteIndex :=
    @Subgroup.finiteIndex_of_finite_quotient _ _ _
      (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))
  tateDualityAt (GalK K) 2 (subgroup_isLocalDualizingGroup 2 (GalKsub K) (isOpen_fixingSubgroup K))

/-- **Prop 5.16 at `G_K`, over a supplied duality bundle** — the form a consumer holding AS1's
`DyadicLocalInput` uses (pass the record's `duality` field).  Consumes **B7** only.

Clause (ii) reads `#Z¹(A) = #A^{n+1} · #fixedPts C (A′)` with `n = [K : ℚ₂]`: this is the `#V`
(outer) times `SN.h1Mult #V = #V^n` (inner) shape of `SourceDataN.hZcard`, and it is where a
verbatim `ℚ₂`-clone would have been wrong. -/
theorem prop_5_16_galK_of {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C]
    [Finite C] (D : TateDualityG (GalK K) 2)
    (ρ : ContinuousMonoidHom (GalK K) C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction (GalK K) A] [ContinuousSMul (GalK K) A]
    (hcomp : ∀ (γ : GalK K) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction (GalK K) (ElemDual A)] [ContinuousSMul (GalK K) (ElemDual A)]
    (hcompD : ∀ (γ : GalK K) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (GalK K) (ZMod 2)] [ContinuousSMul (GalK K) (ZMod 2)]
    (htriv : ∀ (γ : GalK K) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : GalK K) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 (GalK K) A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 (GalK K) A)
      = Nat.card A ^ (Module.finrank ℚ_[2] K + 1) * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 (GalK K) (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 (GalK K) A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : ↥(H0 (GalK K) A) => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 (GalK K) A => cup20 (dualEval A) hpair c) := by
  have h := prop_5_16_gen D (localEulerChar_galK K) ρ hρ hcomp hA₂ hcompD htriv hpair
  -- `GalKsub K` and `K.fixingSubgroup` are the same subgroup through two instance paths, so the
  -- degree identity is `exact`-elaborated into the `GalKsub` spelling before being rewritten.
  have hidx : (GalKsub K).index = Module.finrank ℚ_[2] K :=
    (IntermediateField.finrank_eq_fixingSubgroup_index K).symm
  rwa [hidx] at h

/-- **Prop 5.16 at `G_K`** — the full instantiation, building the duality bundle from **B6**.
Consumes B6 + B7; this is ASK's `stokes`-side substrate at the arithmetic carrier. -/
theorem prop_5_16_galK {C : Type*} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
    (ρ : ContinuousMonoidHom (GalK K) C) (hρ : Function.Surjective ρ)
    {A : Type} [AddCommGroup A] [TopologicalSpace A] [DiscreteTopology A] [Finite A]
    [DistribMulAction C A]
    [DistribMulAction (GalK K) A] [ContinuousSMul (GalK K) A]
    (hcomp : ∀ (γ : GalK K) (a : A), γ • a = ρ γ • a)
    (hA₂ : ∀ a : A, a + a = 0)
    [TopologicalSpace (ElemDual A)] [DiscreteTopology (ElemDual A)]
    [DistribMulAction (GalK K) (ElemDual A)] [ContinuousSMul (GalK K) (ElemDual A)]
    (hcompD : ∀ (γ : GalK K) (lam : ElemDual A), γ • lam = ρ γ • lam)
    [TopologicalSpace (ZMod 2)] [DiscreteTopology (ZMod 2)]
    [DistribMulAction (GalK K) (ZMod 2)] [ContinuousSMul (GalK K) (ZMod 2)]
    (htriv : ∀ (γ : GalK K) (m : ZMod 2), γ • m = m)
    (hpair : ∀ (γ : GalK K) (a : A) (lam : ElemDual A),
      dualEval A (γ • a) (γ • lam) = γ • dualEval A a lam) :
    (Nat.card (H2 (GalK K) A) = Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (Z1 (GalK K) A)
      = Nat.card A ^ (Module.finrank ℚ_[2] K + 1) * Nat.card (fixedPts C (ElemDual A))) ∧
    (Nat.card (H2 (GalK K) (ZMod 2)) = 2) ∧
    Function.Bijective (fun c : H1 (GalK K) A => cup11 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : ↥(H0 (GalK K) A) => cup02 (dualEval A) hpair c) ∧
    Function.Bijective (fun c : H2 (GalK K) A => cup20 (dualEval A) hpair c) :=
  prop_5_16_galK_of K (tateDualityGalK K) ρ hρ hcomp hA₂ hcompD htriv hpair

/-! ### The refutation, at the arithmetic carrier

`card_Z1_zmod2G` evaluated at `Γ = G_K` says `#Z¹(G_K, 𝔽₂) = 2^{n+2}`, `n = [K : ℚ₂]`.  That
number is the `ℚ₂` clause-(ii) value `8` **only** when `n = 1`.  So the `K`-clone ASK's ticket was
originally scoped to write would have shipped a false clause for every `K ≠ ℚ₂`.

The value also matches `GQ2.Dyadic.card_hom_zmodTwo_galK` (`#Hom_c(G_K,𝔽₂) = 2^{n+2}`, proved in
`KSupply.lean` from `Count.card_hom_eq_card_Z1` + FD1's `card_H1_zmodTwo`), which is an
independent derivation of the same number — so the degree-shifted clause (ii) is corroborated at
`K` by already-landed mathematics, not only by the Euler bookkeeping here. -/

/-- `#Z¹(G_K, 𝔽₂) = 2^{[K:ℚ₂]+2}` — the generic clause (ii) at the trivial module, at `G_K`. -/
theorem card_Z1_zmod2_galK :
    Nat.card (Z1 (GalK K) (ZMod 2)) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
  have h := card_Z1_zmod2G (tateDualityGalK K) (localEulerChar_galK K) (fun _ _ => rfl)
  have hidx : (GalKsub K).index = Module.finrank ℚ_[2] K :=
    (IntermediateField.finrank_eq_fixingSubgroup_index K).symm
  rwa [hidx] at h

/-- **A `ℚ₂`-clone of clause (ii) would be false at `K`.**  The `ℚ₂` value `#A² · #fixedPts = 8`
at `A = 𝔽₂` is attained exactly when `[K : ℚ₂] = 1`. -/
theorem card_Z1_zmod2_galK_eq_eight_iff :
    Nat.card (Z1 (GalK K) (ZMod 2)) = 2 ^ 2 * 2 ↔ Module.finrank ℚ_[2] K = 1 := by
  rw [card_Z1_zmod2_galK K, show (2 : ℕ) ^ 2 * 2 = 2 ^ 3 by norm_num]
  refine ⟨fun h => ?_, fun h => by rw [h]⟩
  have := Nat.pow_right_injective (le_refl 2) h
  omega

end GalKInstance

end GQ2.Dyadic.LiftingDualityG
