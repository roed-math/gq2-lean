/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Compare

/-!
# Dyadic campaign, ticket CB-2: the scalar block

The two `SourceDataN` clauses whose coefficient module is the **scalars** `𝔽₂` with no action:

* `homCard : #Hom_c(Γ, 𝔽₂) = SN.homScalar`  (`GQ2/Dyadic/SourceDataN.lean:181`);
* `cardH2  : #H²(Γ, 𝔽₂) = 2`                (`GQ2/Dyadic/SourceDataN.lean:184`).

CB-S's sizing note said the lane's real content moved here.  It was right about *where* the
content is and wrong about *which clause*: the scalar block has exactly **one** mathematical
input, the word-level `#H²w(𝔽₂) = 2` (§4), and both clauses are consumers of it.  `homCard`
consumes it and closes; `cardH2` consumes it and is left one *structural* theorem short — see
§7, which is this ticket's API finding.

## The one input, and why the block is one theorem

At scalar coefficients the marking cannot act (§1: **every** `DistribMulAction C (ZMod 2)` is
trivial, because `𝔽₂` has no nonzero additive automorphism but the identity — so
`SourceDataN`'s `smulZmod2`/`htriv` pair carries no information at this coefficient module).
Hence `d⁰ = 0` on both `𝔽₂` and `(𝔽₂)^∨`, and

* `#H⁰w(𝔽₂) = 2` and `#H⁰w((𝔽₂)^∨) = 2` are free (§2–§3);
* CB-S's clause 2 collapses to `#Z¹w(𝔽₂) = 2^{n+1} · 2 = 2^{n+2}`, which is
  `standardNumerics n`'s `homScalar` **on the nose** (§5);
* CB-S's clause 1 collapses to `#H²w(𝔽₂) = 2` (§4) — the block's whole duality content, and the
  *only* place a `StokesDuality` payload is consumed.

Two routes to the count are given because they cost different things:

* `card_wordZ1_zmod2_of_cardH2` is **duality-free** — it is CB-S's §2 rank–nullity plus the
  degree bookkeeping, and takes `#H²w(𝔽₂) = 2` as an input.  At scalar coefficients that
  hypothesis is a statement about the **rank of the mod-`2` exponent matrix of the relator
  family** (for a two-relator family: "exactly one row is nonzero"), i.e. a finite linear-algebra
  fact a branch can compute without any duality certificate at the trivial marking.
* `card_wordZ1_zmod2` takes the `StokesDuality` payload instead and derives that input through
  WW3b's `card_wordH2` — CB-S's "one theorem" route.

Both land the same value.  The first is recommended for branch instantiation; the second is what
makes the block a *derivation* from `IsSelfDualN` rather than a separate development.

## What is reused, and what is new

Reused verbatim, not re-derived: WW3b's `card_wordH2` (the universal-coefficient step — the
lane's only genuine duality), CB-S's `card_wordZ1_mul_pow` (rank–nullity), `mem_ker_heisD0_iff`
and `IsSelfDualN`, CB-1's `card_Z1_eq_card_wordZ1` (the comparison) and `lower_rel`.  **No count
and no duality is re-proved here.**

New: §1 (scalars carry no action), §2–§3 (the trivial-action evaluation of `H⁰w`), §6's
`homEquivZ1` — the `Hom_c(Γ, 𝔽₂) ≃ Z¹(Γ, 𝔽₂)` bridge, which is the scalar analogue of CB-1's
`tcocycleEquivZ1`/`vcocycleEquivZ1` and did not exist in any form (the `ℚ₂` `lemma_8_2_*` count
characters by hand off a `FreeProfiniteGroup` presentation, `GQ2/SectionEight/ScalarCount.lean`,
and never meet `Z¹`).

## Import discipline

Plain-import: the single import `GQ2.Dyadic.Count.Compare` is plain, and nothing is added to its
closure — every ingredient above is already in it.

Axioms: no new axioms, no `sorry`.  `decide` is used only at kernel-decidable `ZMod 2`
statements (`∀ a : ZMod 2, a + a = 0` and the two-element case split).  Every headline prints
exactly the standard three (`propext`, `Classical.choice`, `Quot.sound`) — recorded in the
report.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh

/-! ## §1. Scalars carry no action

`𝔽₂` has exactly one additive automorphism, so a group acting on it by additive automorphisms
acts trivially — **no hypothesis needed**.  This is what makes the block "scalar", and it is
also the observation that `SourceDataN.htriv` (`GQ2/Dyadic/SourceDataN.lean:174`) is not an
assumption at all at this coefficient module but a theorem about `ZMod 2`. -/

section NoAction

variable {C : Type*} [Group C]

/-- **Every action on the scalars is trivial.**  If `g • m ≠ m` for some `m : 𝔽₂` then `g` would
be a nonidentity additive automorphism of a two-element group. -/
theorem smul_zmod2 [DistribMulAction C (ZMod 2)] (g : C) (m : ZMod 2) : g • m = m := by
  have hone : g • (1 : ZMod 2) = 1 := by
    have hne : g • (1 : ZMod 2) ≠ 0 := by
      intro h0
      have : (1 : ZMod 2) = 0 := by
        have := congrArg (fun z : ZMod 2 => g⁻¹ • z) h0
        rwa [inv_smul_smul, smul_zero] at this
      exact one_ne_zero this
    revert hne
    generalize g • (1 : ZMod 2) = z
    revert z
    decide
  rcases (show m = 0 ∨ m = 1 by revert m; decide) with rfl | rfl
  · exact smul_zero g
  · exact hone

/-- **The trivial action on the scalars**, as a bundled instance for the places that need one
(the comparison isomorphism is stated over a `DistribMulAction Γ A`).  By `smul_zmod2` it is the
*only* one, so no diamond can arise: any other instance is propositionally equal on values. -/
@[reducible] def scalarAction (Γ : Type*) [Group Γ] : DistribMulAction Γ (ZMod 2) where
  smul _ m := m
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

theorem scalarAction_continuousSMul (Γ : Type*) [Group Γ] [TopologicalSpace Γ] :
    letI := scalarAction Γ
    ContinuousSMul Γ (ZMod 2) :=
  letI := scalarAction Γ
  ⟨continuous_snd⟩

/-- **The contragredient of a trivial action is trivial.**  Applied at `A = 𝔽₂`, this says the
marking acts trivially on `(𝔽₂)^∨` as well — which is what `#H⁰w((𝔽₂)^∨) = 2` needs. -/
theorem smul_elemDual_of_trivial {A : Type*} [AddCommGroup A] [DistribMulAction C A]
    (htriv : ∀ (g : C) (a : A), g • a = a) (g : C) (lam : ElemDual A) : g • lam = lam :=
  ElemDual.ext fun a => by rw [ElemDual.smul_apply, htriv]

/-- The scalar dual carries no action either. -/
theorem smul_elemDual_zmod2 [DistribMulAction C (ZMod 2)] (g : C) (lam : ElemDual (ZMod 2)) :
    g • lam = lam :=
  smul_elemDual_of_trivial smul_zmod2 g lam

/-- `𝔽₂` is elementary — the `hA₂` input of the comparison isomorphism, at the scalars. -/
theorem zmod2_add_self (a : ZMod 2) : a + a = 0 := by revert a; decide

end NoAction

/-! ## §2. `H⁰w` at a trivial action

`d⁰v = ((cᵢ − 1)v)ᵢ`, so a trivial marking action makes `d⁰` the zero map and `H⁰w` the whole
module.  Two lines off CB-S's `mem_ker_heisD0_iff`; no generation hypothesis is involved, which
is the scalar block's dispensation from WW3b's second record-design caution (the `fixedPts`
bridge of `Count/Spike.lean` §4 is not needed here — at a trivial action `ker d⁰` and the
invariants are both everything). -/

section TrivialH0

variable {ι : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- With a trivial action `ker d⁰ = ⊤`. -/
theorem ker_heisD0_eq_top_of_trivial (htriv : ∀ (g : C) (a : A), g • a = a) (c : ι → C) :
    (heisD0 (A := A) c).ker = ⊤ :=
  eq_top_iff.mpr fun v _ => (mem_ker_heisD0_iff c v).mpr fun i => htriv (c i) v

/-- The cardinality form: `#H⁰w(A) = #A`. -/
theorem card_ker_heisD0_of_trivial (htriv : ∀ (g : C) (a : A), g • a = a) (c : ι → C) :
    Nat.card ↥(heisD0 (A := A) c).ker = Nat.card A := by
  rw [ker_heisD0_eq_top_of_trivial htriv c]
  exact Nat.card_congr (AddSubgroup.topEquiv (G := A)).toEquiv

end TrivialH0

/-! ## §3. The scalar `H⁰`s

Both are `2`, with no input at all. -/

section ScalarH0

variable {ι : Type*} {C : Type*} [Group C] [DistribMulAction C (ZMod 2)] (c : ι → C)

/-- `#H⁰w(𝔽₂) = 2`. -/
theorem card_ker_heisD0_zmod2 :
    Nat.card ↥(heisD0 (A := ZMod 2) c).ker = 2 := by
  rw [card_ker_heisD0_of_trivial smul_zmod2 c, Nat.card_zmod]

/-- `#H⁰w((𝔽₂)^∨) = 2` — the right-hand side of CB-S's clause 1 and clause 2 at the scalars. -/
theorem card_ker_heisD0_elemDual_zmod2 :
    Nat.card ↥(heisD0 (A := ElemDual (ZMod 2)) c).ker = 2 := by
  rw [card_ker_heisD0_of_trivial smul_elemDual_zmod2 c,
    card_elemDual (A := ZMod 2) zmod2_add_self, Nat.card_zmod]

end ScalarH0

/-! ## §4. The block's single input: `#H²w(𝔽₂) = 2`

CB-S's clause 1 (`IsSelfDualN.cardH2`, i.e. WW3b's `card_wordH2`) evaluated at the scalars.
**This is the only place in the file a duality payload is consumed**, and the only genuine
mathematics the scalar block needs — everything in §5–§6 is bookkeeping on top of it.

Read the other way round: at scalar coefficients WW3b's universal-coefficient theorem says the
mod-`2` exponent matrix of the relator family has corank exactly one in the relator direction.
A branch that can compute that rank does not need the duality payload at all (§5's first
route). -/

section ScalarH2

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]
  [DistribMulAction C (ZMod 2)] {c : ι → C} {w : ρ → FreeGroup ι}

/-- **`#H²w(𝔽₂) = 2`**, from one `StokesDuality` payload. -/
theorem card_wordH2_zmod2 (hd : StokesDuality c w (ZMod 2))
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card (WordH2 c w (ZMod 2)) = 2 :=
  (card_wordH2 hd hr hend).trans (card_ker_heisD0_elemDual_zmod2 c)

omit [Fintype ι] [DecidableEq ι] in
/-- The same, read off CB-S's package instead of the raw payload. -/
theorem card_wordH2_zmod2_of_selfDual {n : ℕ}
    (S : IsSelfDualN n c w (ZMod 2)) : Nat.card (WordH2 c w (ZMod 2)) = 2 :=
  S.cardH2.trans (card_ker_heisD0_elemDual_zmod2 c)

end ScalarH2

/-! ## §5. The scalar count `#Z¹w(𝔽₂) = 2^{n+2}`

The value `standardNumerics n` calls `homScalar`.  Two routes; the first consumes no duality. -/

section ScalarCount

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]
  [DistribMulAction C (ZMod 2)] {c : ι → C} {w : ρ → FreeGroup ι}

omit [DecidableEq ι] in
/-- **The scalar count, duality-free.**  CB-S's §2 rank–nullity `#Z¹w · #A^{|ρ|} = #A^{|ι|} ·
#H²w(A)` at `A = 𝔽₂`, with the deficiency-`n` bookkeeping `|ι| = |ρ| + (n + 1)` and the single
input `#H²w(𝔽₂) = 2`.  The `2^{|ρ|}` cancels; nothing else is used.

At `n = 1` this is the frozen `#Hom_c(Γ, 𝔽₂) = 8` of `GQ2/SourceData.lean:131`, and the `8` is
`2^{|ι| − |ρ| + 1} = 2^{4 − 2 + 1}` — the same deficiency CB-S identified behind the `ℚ₂`
literal `²`. -/
theorem card_wordZ1_zmod2_of_cardH2 {n : ℕ} (hdeg : Nat.card ι = Nat.card ρ + (n + 1))
    (hH2 : Nat.card (WordH2 c w (ZMod 2)) = 2) :
    Nat.card ↥(heisD1 (A := ZMod 2) c w).ker = 2 ^ (n + 2) := by
  have h := card_wordZ1_mul_pow (A := ZMod 2) c w
  rw [hH2, hdeg, Nat.card_zmod] at h
  have hpos : 0 < 2 ^ Nat.card ρ := Nat.two_pow_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [h]
  ring

/-- **The scalar count**, through CB-S's clause 1 — the "one theorem" route. -/
theorem card_wordZ1_zmod2 {n : ℕ} (hdeg : Nat.card ι = Nat.card ρ + (n + 1))
    (hd : StokesDuality c w (ZMod 2)) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    Nat.card ↥(heisD1 (A := ZMod 2) c w).ker = 2 ^ (n + 2) :=
  card_wordZ1_zmod2_of_cardH2 hdeg (card_wordH2_zmod2 hd hr hend)

omit [Fintype ι] [DecidableEq ι] in
/-- The same off CB-S's package, in the `standardNumerics` spelling the record uses. -/
theorem card_wordZ1_zmod2_of_selfDual {n : ℕ} (S : IsSelfDualN n c w (ZMod 2)) :
    Nat.card ↥(heisD1 (A := ZMod 2) c w).ker = (standardNumerics n).homScalar := by
  rw [S.cardZ1, card_ker_heisD0_elemDual_zmod2 c, Nat.card_zmod]
  show 2 ^ (n + 1) * 2 = 2 ^ (n + 2)
  ring

end ScalarCount

/-! ## §6. The scalar comparison bridge `Hom_c(Γ, 𝔽₂) ≃ Z¹(Γ, 𝔽₂)`

The scalar analogue of CB-1's `tcocycleEquivZ1`/`vcocycleEquivZ1`, and the piece that lets the
`homCard` clause reach the word lane at all.  With no action a continuous crossed homomorphism
*is* a continuous homomorphism into `Multiplicative 𝔽₂`: the cocycle law
`z(γδ) = z γ + γ • z δ` loses its twist by §1, and `Multiplicative`'s multiplication is `𝔽₂`'s
addition, so the two sides are the same function under `toAdd`/`ofAdd`.

The `ℚ₂` ancestors never meet `Z¹`: `lemma_8_2_gammaA`/`lemma_8_2_R`/`lemma_8_2_local`
(`GQ2/SectionEight/ScalarCount.lean:245,339`, `GQ2/Roe/Supply.lean:202`) count characters by hand
against a `FreeProfiniteGroup (Fin 4)` presentation and a hand-built `vecEquiv`.  That route is
not degree-generic — the `Fin 4` and the `8` are both hard-coded — which is why this bridge is
new rather than transported. -/

section HomBridge

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [DistribMulAction Γ (ZMod 2)]

/-- **`Hom_c(Γ, 𝔽₂) ≃ Z¹(Γ, 𝔽₂)`** — continuous characters are continuous `1`-cocycles, for the
(unique, §1) action of `Γ` on the scalars.  Both directions are the identity on underlying
functions, so both round trips are `rfl`. -/
def homEquivZ1 : ContinuousMonoidHom Γ (Multiplicative (ZMod 2)) ≃ ↥(Z1 Γ (ZMod 2)) where
  toFun f :=
    ⟨fun γ => Multiplicative.toAdd (f γ), (mem_Z1_iff_of_trivial smul_zmod2).mpr
      ⟨f.continuous_toFun, fun g h => congrArg Multiplicative.toAdd (map_mul f g h)⟩⟩
  invFun z :=
    { toFun := fun γ => Multiplicative.ofAdd (z.1 γ)
      map_one' := congrArg Multiplicative.ofAdd (Z1_apply_one z)
      map_mul' := fun g h =>
        congrArg Multiplicative.ofAdd (((mem_Z1_iff_of_trivial smul_zmod2).mp z.2).2 g h)
      continuous_toFun := ((mem_Z1_iff_of_trivial smul_zmod2).mp z.2).1 }
  left_inv _ := rfl
  right_inv _ := Subtype.ext rfl

@[simp] theorem homEquivZ1_coe (f : ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) (γ : Γ) :
    (homEquivZ1 f).1 γ = Multiplicative.toAdd (f γ) := rfl

/-- The cardinality form — the equation `homCard` transports along. -/
theorem card_hom_eq_card_Z1 :
    Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = Nat.card ↥(Z1 Γ (ZMod 2)) :=
  Nat.card_congr homEquivZ1

end HomBridge

/-! ## §7. `SourceDataN.homCard`, over the abstract carrier

The first field value.  Three rewrites and no cohomology: §6 moves into `Z¹`, CB-1's
`card_Z1_eq_card_wordZ1` moves into the word complex, §5 reads off the value, and
`(standardNumerics n).homScalar = 2^{n+2}` is `rfl`.

⚠ The `DistribMulAction Γ (ZMod 2)` the comparison needs is supplied **internally** by
`scalarAction` and never appears in the statement, so the clause composes with `SourceDataN`
without a `letI` at the call site — unlike `tcocycle_card`/`hZcard`, whose field goals mention
their actions.  By §1 this is not a choice: any action a branch might supply agrees with it on
values. -/

section HomCard

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  {gen : ι → Γ} {W : κ → PWord ι} {w : κ → FreeGroup ι} {c : ι → C} {J : Set ι}
  (rho : ContinuousMonoidHom Γ C) (hc : ∀ i, rho (gen i) = c i)

omit [DecidableEq ι] in
include hc in
/-- **The `SourceDataN.homCard` value, degree-generically, duality-free.**

`#Hom_c(Γ, 𝔽₂) = SN.homScalar` for `SN = standardNumerics n`, at a degree-`n` marked
presentation, from the single scalar input `#H²w(𝔽₂) = 2`.  This is the shape
`GQ2/Dyadic/SourceDataN.lean:181` asks for; at `n = 1` it is the frozen `8`
(`GQ2/SourceData.lean:131`), and the `8` is `2^{|ι| − |ρ| + 1}`. -/
theorem homCardN {n : ℕ} (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (hwild2 : IsWildTwo J c)
    (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hH2 : Nat.card (WordH2 c w (ZMod 2)) = 2) :
    Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2)))
      = (standardNumerics n).homScalar := by
  letI := scalarAction Γ
  haveI := scalarAction_continuousSMul Γ
  rw [card_hom_eq_card_Z1,
    card_Z1_eq_card_wordZ1 rho (fun γ a => (smul_zmod2 (rho γ) a).symm) hc hpres hres
      zmod2_add_self hwild2,
    card_wordZ1_zmod2_of_cardH2 hdeg hH2]
  rfl

include hc in
/-- **The same through CB-S's "one theorem"**: the scalar input comes from the branch's
`StokesDuality` payload at the scalars, and the relator hypothesis `hr` is supplied by the
presentation (CB-1's `lower_rel`) rather than re-verified. -/
theorem homCardN_of_stokes {n : ℕ} (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (hwild2 : IsWildTwo J c)
    (hdeg : Nat.card ι = Nat.card κ + (n + 1)) (hd : StokesDuality c w (ZMod 2))
    (hend : IsStokesEndpoint w) :
    Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2)))
      = (standardNumerics n).homScalar := by
  letI := scalarAction Γ
  haveI := scalarAction_continuousSMul Γ
  exact homCardN rho hc hpres hres hwild2 hdeg
    (card_wordH2_zmod2 hd (lower_rel (A := ZMod 2) rho hc hpres hres) hend)

end HomCard

end GQ2.Dyadic.Count
