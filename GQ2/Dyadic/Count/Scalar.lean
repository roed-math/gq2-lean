/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Count.Compare
import GQ2.Dyadic.Count.Presentation
import GQ2.Dyadic.GammaRHom

/-!
# Dyadic campaign, ticket CB-2: the scalar block

The two `SourceDataN` clauses whose coefficient module is the **scalars** `𝔽₂` with no action:

* `homCard : #Hom_c(Γ, 𝔽₂) = SN.homScalar`  (`GQ2/Dyadic/SourceDataN.lean:181`);
* `cardH2  : #H²(Γ, 𝔽₂) = 2`                (`GQ2/Dyadic/SourceDataN.lean:184`).

CB-S's sizing note said the lane's real content moved here.  It was right about *where* the
content is and wrong about *which clause*: the scalar block has exactly **one** mathematical
input, the word-level `#H²w(𝔽₂) = 2` (§4), and both clauses are consumers of it.  `homCard`
consumes it and closes; `cardH2` consumes it and is left one *structural* theorem short — see
§8, which is this ticket's API finding.

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
and never meet `Z¹`).  `GQ2/Dyadic/CertificateMain.lean:264-272` records the consequence of that
absence in so many words — the candidate side's scalar rows "are not yet a `#Hom` count" — and
`homEquivZ1` is what closes it.

## Section map

| § | content | status |
|---|---|---|
| 1 | every action on `𝔽₂` (and on `(𝔽₂)^∨`) is trivial | new, free |
| 2–3 | `H⁰w` at a trivial action; both scalar `H⁰`s are `2` | new, free |
| 4 | **`#H²w(𝔽₂) = 2`** — the block's single input | one line off WW3b |
| 5 | `#Z¹w(𝔽₂) = 2^{n+2}` (duality-free route + `IsSelfDualN` route) | closed |
| 6 | `Hom_c(Γ, 𝔽₂) ≃ Z¹(Γ, 𝔽₂)` | new bridge |
| 7 | **`SourceDataN.homCard` over the abstract carrier** | **CLOSED** |
| 8 | `SourceDataN.cardH2`, reduced to the missing H² rung | **OPEN** (one named argument) |
| 9 | `SourceDataN.lem86` is a scalar-block consumer, not an `exactLifting` one | reduction landed |
| 10–11 | the N0 / `√−2` pilot, and the pilot over `Γ_R` itself | closed |
| 12 | the two verbatim `SourceDataN` field goals | `homCard` closed |

`hsep` and `hpartial` are **not** here and do not belong here: neither factors through the scalar
block.  `hsep` has two disjoint `ℚ₂` proofs (the `Γ_A` marking route and the local `cup20` route,
with no common generic core), and `hpartial` is generic except for one stage — the right-slot
separation, which forks `prop_5_15` against B6's `bijective_cup11/02_dualEval`.  Both stay with
CB-4's `stokes` bundle, where CB1's memo already puts them.

## Import discipline

Plain-import: `GQ2.Dyadic.Count.Compare` is plain, and nothing is added to its closure — every
ingredient above is already in it.  Ticket CB-DD added `GQ2.Dyadic.GammaRHom`, also plain and
sitting directly above `AdmissibleR.lean`, for the shared trivial `ZMod 2`-action (§1); it brings
in no new mathematics.

Axioms: no new axioms, no `sorry`.  `decide` is used only at kernel-decidable `ZMod 2`
statements (`∀ a : ZMod 2, a + a = 0` and the two-element case split).  Every headline prints
exactly the standard three (`propext`, `Classical.choice`, `Quot.sound`) — recorded in the
report.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic ContCoh
open GQ2.SectionEight GQ2.SectionEight.CentralObstruction

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

/-! **The trivial action on the scalars**, as a bundled instance for the places that need one
(the comparison isomorphism is stated over a `DistribMulAction Γ A`).  By `smul_zmod2` it is the
*only* one, so no diamond can arise: any other instance is propositionally equal on values.

⚠ **De-duplicated (ticket CB-DD).**  This section used to declare its own `scalarAction` (over
`Group`) and `scalarAction_continuousSMul`; the merge the note here reserved for "whichever
ticket first has both in scope" has now happened.  Both are `GQ2.Dyadic.scalarActionZmodTwo`
and `.scalarActionZmodTwo_continuousSMul` (`GQ2/Dyadic/GammaRHom.lean` §3), stated over
`Monoid` — the same five-line trivial action, one typeclass weaker, so every `Group Γ` use site
below is unchanged.  The import that made this affordable is `GQ2.Dyadic.GammaRHom`, upstream of
`AdmissibleR.lean` — **not** the `Count/Routine.lean` route the old note priced and rejected
(that one would have dragged in `GQ2.Dyadic.CertificateMain` and the five `Words/` files). -/

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
`scalarActionZmodTwo` and never appears in the statement, so the clause composes with
`SourceDataN`
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
  letI := scalarActionZmodTwo Γ
  haveI := scalarActionZmodTwo_continuousSMul Γ
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
  letI := scalarActionZmodTwo Γ
  haveI := scalarActionZmodTwo_continuousSMul Γ
  exact homCardN rho hc hpres hres hwild2 hdeg
    (card_wordH2_zmod2 hd (lower_rel (A := ZMod 2) rho hc hpres hres) hend)

end HomCard

/-! ## §8. `SourceDataN.cardH2` — the reduction, and the rung that is missing

**This clause does not close here, and the reason is structural, not arithmetic.**

The scalar block's single input already gives the *word-level* value: `#H²w(𝔽₂) = 2` (§4). What
`SourceDataN.cardH2` asks for is the *group-level* `#H²(Γ, 𝔽₂) = 2`, and the two are joined by a
theorem that does not exist anywhere in the repository:

> **The H² rung of the comparison ladder.**  CB-1's `Count/Compare.lean` builds `z1Equiv` (degree
> `1` cocycles) and `h1Equiv` (degree `1` cohomology) and stops there — its own section map lists
> no H² item.  Nothing in `GQ2/` relates `ContCoh.H2 Γ _` to `WordH2`/`StokesH2`: the only two
> files naming `WordH2`/`StokesH2` are `Word/StokesDual.lean` and `Count/Spike.lean`, and neither
> mentions group cohomology.  The `ℚ₂` ancestors do the comparison *numerically* and only at
> `AbsGalQ2` — `cor_5_17_card` (`GQ2/LocalLiftingDuality.lean:571`) and `cor_5_17_card_R`
> (`GQ2/Roe/DualityAssembly.lean:509`) get `#H²w = #H²(G_ℚ₂)` by routing **both** sides through
> `#fixedPts C (ElemDual A)`, i.e. through B6 on the local side.  There is no `Γ`-generic form.

So `cardH2N` below takes that comparison as its hypothesis.  That is the honest statement of
where the clause stands: the scalar arithmetic is discharged, and exactly one structural theorem
— the degree-`2` analogue of `h1Equiv` — is owed.  Its expected shape is the injection
`H²(Γ, A) ↪ WordH²(A)` coming from the five-term sequence of `1 → R → F → Γ → 1` (the relators
span `R/[R,F]R²`, so `Hom(R/[R,F]R², A) ↪ (ρ → A)`, and cokernels of a composite with an
injective second factor inject); with `#H²w = 2` that gives `≤ 2`, and `cardH2_of_le_two` closes
from nontriviality.

Neither `WordCoh.card_H2_le_two` nor the `ℚ₂` `obsH2` route substitutes for it: the former needs
`IsProP 2 G` (the source group is not pro-`2`) and a **single** relator, and the latter is
hard-wired to `Fin 4` with exactly two relators inside `F₄ ⧸ N_A`. -/

section CardH2

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The sandwich.**  `#H² ≤ 2` plus nontriviality pins the value; finiteness is what rules out
the `Nat.card = 0` reading of the bound. -/
theorem cardH2_of_le_two [Finite (H2 Γ (ZMod 2))] (hle : Nat.card (H2 Γ (ZMod 2)) ≤ 2)
    (hnt : Nontrivial (H2 Γ (ZMod 2))) : Nat.card (H2 Γ (ZMod 2)) = 2 := by
  have h1 : 1 < Nat.card (H2 Γ (ZMod 2)) := Finite.one_lt_card_iff_nontrivial.mpr hnt
  omega

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **`SourceDataN.cardH2`, reduced to the missing rung.**  Everything but `hcomp` is discharged:
`hcomp` is the degree-`2` comparison, and the `2` on its right is §4's `#H²w(𝔽₂) = 2`.

Stated so that a future H²-rung ticket closes the clause by supplying one argument. -/
theorem cardH2N {ι ρ' : Type*} [Fintype ι] [Fintype ρ'] [DecidableEq ι] {C : Type*} [Group C]
    [DistribMulAction C (ZMod 2)] {c : ι → C} {w : ρ' → FreeGroup ι}
    (hcomp : Nat.card (H2 Γ (ZMod 2)) = Nat.card (WordH2 c w (ZMod 2)))
    (hd : StokesDuality c w (ZMod 2)) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) : Nat.card (H2 Γ (ZMod 2)) = 2 :=
  hcomp.trans (card_wordH2_zmod2 hd hr hend)

end CardH2

/-! ## §9. `SourceDataN.lem86` is a **scalar-block consumer**, not an `exactLifting` one

CB1's memo groups `lem86` with `liftsOver_card`/`stageR136` in the `exactLifting` bundle
(`docs/dyadic/cb-design.md:113`).  The mathematics puts it here: the half-torsor count is already
`Γ`-generic in the repository — `CentralObstruction.half_count` (`GQ2/CentralObstruction.lean:1074`)
takes an abstract `Γ` and consumes **`Nat.card (H2 Γ (ZMod 2)) = 2` directly as a hypothesis**.
So `lem86` needs no new counting at all; it needs `cardH2`, `tfg`, and a nonzero variation class.

The ticket said to follow the mathematics rather than the memo's grouping where they diverge.
They diverge here, and the consequence is concrete: **`lem86` cannot be closed before `cardH2`
is**, so CB-3 should not be scheduled as if it were independent of the scalar block.

`hvar` is the one genuinely per-source residue (at `ℚ₂` it is `exists_nonzero_varCoc_gammaA`,
which routes through `prop_5_15`; on the local side `RadicalEdgeLocal.exists_good_twist`, which
routes through B6).  The `NoDescent` witness is already source-free — `RadicalCoverData Bg` binds
no `Γ`, which is why `Γ_R` reuses `Γ_A`'s `D₈` datum verbatim. -/

section Lem86

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [TotallyDisconnectedSpace Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The `SourceDataN.lem86` value, over the abstract carrier**, from `cardH2` plus the record's
own `tfg` plus a nonzero variation class.  The `htriv` input of `half_count` is not a hypothesis:
by §1 it is a theorem. -/
theorem lem86N (tfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hcardH2 : Nat.card (H2 Γ (ZMod 2)) = 2) (D : RadicalCoverData Bg)
    (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)) (S : TComplement D) (u : TCocycle D ρ)
    (hvar : H2mk Γ (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S smul_zmod2 u⟩ ≠ 0) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  haveI : Finite (ContinuousMonoidHom Γ Bg) := finite_continuousMonoidHom tfg Bg
  haveI : Finite (MLifts D ρ) := by unfold MLifts; exact Subtype.finite
  exact half_count D ρ S smul_zmod2 u hvar hcardH2

end Lem86

/-! ## §10. The N0 / `√−2` pilot

CB-S's degree bookkeeping (`nCompact_degree`: the compact-`N` family has deficiency `2h + 2`) and
N0's own endpoint certificate, at the scalar coefficient module.  At `h = 0` the degree is
`n = 2 = [ℚ₂(√−2) : ℚ₂]`, so the pilot's character count is `2^4 = 16` — the degree-`2`
replacement for the frozen `ℚ₂` `8`.  Nothing is fudged: `standardNumerics 2`'s
`homScalar = 2^{2+2}` **is** `2^{|ι| − |ρ| + 1} = 2^{5 − 2 + 1}` for the two-relator compact-`N`
presentation on `Generator 2`. -/

section N0

open GQ2.Dyadic.Certificates

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]

/-- **The character count at branch N0**: `#Hom_c(Γ, 𝔽₂) = SN.homScalar` for
`SN = standardNumerics (2h + 2)`. -/
theorem nCompact_homCard {α h q e : ℕ} {gen : Generator (2 + 2 * h) → Γ}
    {W : Fin 2 → PWord (Generator (2 + 2 * h))} {J : Set (Generator (2 + 2 * h))}
    {t : Marking (2 + 2 * h) C} (rho : ContinuousMonoidHom Γ C)
    (hc : ∀ i, rho (gen i) = t i) (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W (nCompactFam α h q e) (WordLift (ZMod 2) C))
    (hwild2 : IsWildTwo J (⇑t)) (hd : StokesDuality (⇑t) (nCompactFam α h q e) (ZMod 2))
    (hend : IsStokesEndpoint (nCompactFam α h q e)) :
    Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2)))
      = (standardNumerics (2 * h + 2)).homScalar :=
  homCardN_of_stokes rho hc hpres hres hwild2 (nCompact_degree h) hd hend

/-- **The `√−2` pilot** (`(α, h, q, e) = (2, 0, 2, 3)`, `n = 2`): the `SourceDataN.homCard` field
value for AS2's branch, with N0's own `sqrtNegTwo_isStokesEndpoint` composed in — the scalar twin
of CB-1's `sqrtNegTwo_tcocycle_card`/`sqrtNegTwo_hZcard`. -/
theorem sqrtNegTwo_homCard {gen : Generator 2 → Γ} {W : Fin 2 → PWord (Generator 2)}
    {J : Set (Generator 2)} {t : Marking 2 C} (rho : ContinuousMonoidHom Γ C)
    (hc : ∀ i, rho (gen i) = t i) (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres : ResolvesAt W (nCompactFam 2 0 2 3) (WordLift (ZMod 2) C))
    (hwild2 : IsWildTwo J (⇑t)) (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) (ZMod 2)) :
    Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2)))
      = (standardNumerics 2).homScalar :=
  nCompact_homCard (h := 0) rho hc hpres hres hwild2 hd sqrtNegTwo_isStokesEndpoint

end N0

/-! ## §11. The pilot over `Γ_R` itself

CB-P's §8 shape, at the scalar clause: the presentation is `isAdmissibleMarkedPresentation_gammaR`,
the admissibility of the lower marking is `isWildTwo_of_gammaGen`, the module's `2`-torsion is
`zmod2_add_self` (§1), and — in the `_nCompact` form — the resolution is discharged by CB-FR's
`resolvesAt_nCompactFam_three` from the single condition that the counting target has exponent
dividing `6`.

Note what is **not** needed here and is needed by CB-1's twins: no `hcomp`/`hround`/`hact`
compatibility, because §1 makes every scalar action the same one. -/

section PilotGammaR

open GQ2.Dyadic.Certificates

variable {q : ℕ} {R : PWord (Generator 2)}
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]

/-- **The `√−2` pilot's `homCard` field value, over `Γ_R`.** -/
theorem sqrtNegTwo_homCard_gammaR {t : Marking 2 C}
    (rho : ContinuousMonoidHom ((GammaR 2 q R) : Type) C)
    (hc : ∀ g, rho (gammaGen 2 q R g) = t g)
    (hres : ResolvesAt (gammaFam 2 q R) (nCompactFam 2 0 2 3) (WordLift (ZMod 2) C))
    (hsurj : Function.Surjective rho)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) (ZMod 2)) :
    Nat.card (ContinuousMonoidHom ((GammaR 2 q R) : Type) (Multiplicative (ZMod 2)))
      = (standardNumerics 2).homScalar :=
  sqrtNegTwo_homCard rho hc (isAdmissibleMarkedPresentation_gammaR 2 q R) hres
    (isWildTwo_of_gammaGen rho hsurj hc) hd

/-- **The `√−2` pilot's `homCard` field value at the intrinsic branch word**, with no resolution
hypothesis: `e = 3` is `omega2Exp 6`, so a scalar counting target of exponent dividing `6`
resolves itself (CB-FR/CB-P's `resolvesAt_nCompactFam_three`). -/
theorem sqrtNegTwo_homCard_gammaR_nCompact {t : Marking 2 C}
    (rho : ContinuousMonoidHom ((GammaR 2 2 (Words.nCompactW 2 0)) : Type) C)
    (hc : ∀ g, rho (gammaGen 2 2 (Words.nCompactW 2 0) g) = t g)
    (hord : ∀ x : WordLift (ZMod 2) C, orderOf x ∣ 6)
    (hsurj : Function.Surjective rho)
    (hd : StokesDuality (⇑t) (nCompactFam 2 0 2 3) (ZMod 2)) :
    Nat.card (ContinuousMonoidHom ((GammaR 2 2 (Words.nCompactW 2 0)) : Type)
        (Multiplicative (ZMod 2)))
      = (standardNumerics 2).homScalar :=
  sqrtNegTwo_homCard_gammaR rho hc (resolvesAt_nCompactFam_three hord 2 0 2) hsurj hd

end PilotGammaR

/-! ## §12. The verbatim `SourceDataN` field goals

CB-1's standard of evidence: state the goal **in the record's own vocabulary** — `Γ : ProfiniteGrp`,
`SN := standardNumerics n`, and for `cardH2` the record's `letI := smulZmod2` shape — and close it.

`homCard` closes.  `cardH2` closes only against the missing rung (§8), which is exactly the point
of stating it: the residue is one argument, and it is named. -/

section FieldGoals

variable {n : ℕ} {Gam : ProfiniteGrp} {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι]
  {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [DistribMulAction C (ZMod 2)]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)]
  {gen : ι → (Gam : Type)} {W : κ → PWord ι} {w : κ → FreeGroup ι} {c : ι → C} {J : Set ι}

/-- **`SourceDataN.homCard`, verbatim** (`GQ2/Dyadic/SourceDataN.lean:181`), at
`SN := standardNumerics n`.  No `letI` is needed at the call site: the field goal mentions no
action, and §7 supplies the one its proof needs. -/
theorem homCard_field_goal (rho : ContinuousMonoidHom (Gam : Type) C)
    (hc : ∀ i, rho (gen i) = c i) (hpres : IsAdmissibleMarkedPresentation (Gam : Type) gen W J)
    (hres : ResolvesAt W w (WordLift (ZMod 2) C)) (hwild2 : IsWildTwo J c)
    (hdeg : Nat.card ι = Nat.card κ + (n + 1)) (hd : StokesDuality c w (ZMod 2))
    (hend : IsStokesEndpoint w) :
    Nat.card (ContinuousMonoidHom Gam (Multiplicative (ZMod 2)))
      = (standardNumerics n).homScalar :=
  homCardN_of_stokes rho hc hpres hres hwild2 hdeg hd hend

omit [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (WordLift (ZMod 2) C)] [DiscreteTopology (WordLift (ZMod 2) C)] in
/-- **`SourceDataN.cardH2`, verbatim** (`GQ2/Dyadic/SourceDataN.lean:184`), including the record's
`letI := smulZmod2` — with the missing rung `hcomp` as the single open argument (§8).

`smulZmod2` is the record's own field, passed positionally.  Two of the record's neighbouring
fields are *not* needed: `contSMulZmod2`, because `ContCoh.H2` does not consume `ContinuousSMul`
(only `Z2`'s differential does, through `DistribMulAction`), and `htriv`, because §1 proves it. -/
theorem cardH2_field_goal (smulZmod2 : DistribMulAction (Gam : Type) (ZMod 2))
    (hcomp : letI := smulZmod2
      Nat.card (H2 (Gam : Type) (ZMod 2)) = Nat.card (WordH2 c w (ZMod 2)))
    (hd : StokesDuality c w (ZMod 2)) (hr : ∀ k, FreeGroup.lift c (w k) = 1)
    (hend : IsStokesEndpoint w) :
    letI := smulZmod2
    Nat.card (H2 Gam (ZMod 2)) = 2 := by
  letI := smulZmod2
  exact cardH2N hcomp hd hr hend

end FieldGoals

end GQ2.Dyadic.Count
