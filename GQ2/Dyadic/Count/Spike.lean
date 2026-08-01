/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Word.StokesDual
import GQ2.Dyadic.Recursion.Numerics
import GQ2.Dyadic.Certificates.N0
import GQ2.DualityAssembly

/-!
# Dyadic campaign, ticket CB-S: the degree-generic count clause (spike)

**This is a spike, not a production file.**  It exists to answer one question before the CB
lane (CB1 memo `docs/dyadic/cb-design.md`, ~10–13k lines) is committed:

> WW3b warned that `IsSelfDual`'s second numeric clause
> `#Z¹w = #A² · #(A^∨)^C` is **NOT** degree-generic.  Is there an honest degree-generic
> statement of it over the abstract carrier, and do the `SourceDataN` count clauses factor
> through *one* theorem rather than eleven?

**Verdict: GREEN.**  The clause is degree-generic in the division-free form

  `#Z¹w · #A^{|ρ|} = #A^{|ι|} · #H²w(A)`   (§1–§2, pure counting, no duality)

and the literal `²` of the `ℚ₂` ancestor is exactly `|ι| − |ρ| = 4 − 2`.  Under the degree-`n`
marking convention `|ι| = |ρ| + n + 1` (deficiency `n`) this reads
`#Z¹w = #A^{n+1} · #H⁰w(A^∨)`, which is `standardNumerics n`'s `tMult T = T^(n+1)` on the nose
(§6), and `#A · h1Mult #A` with `h1Mult V = V^n` once the dual has no invariants (§6).

## What is proved here

* **§1** `card_ker_mul_card_cod` — rank–nullity for a three-term complex, division-free and
  degree-free.  The generic form of the `ℚ₂` ancestor `card_Z1w_eq_sq_mul_card_H2w_R`
  (`GQ2/Roe/Devissage/Naturality.lean:116`), which hard-codes `#A^4` and `#A^2`.
* **§2** `card_wordZ1_mul_pow` — the same at the generic word complex
  `A → (ι → A) → (ρ → A)`.  **No duality input**: the count is bookkeeping, exactly as the
  `ℚ₂` dévissage says by discarding clause 2 (`isSelfDualW_iff_R` does
  `rintro ⟨hc1, -, hpair⟩`, `GQ2/Roe/Devissage/SelfDual.lean:58`).
* **§3** `card_wordZ1_of_degree` — **the degree-generic clause 2**.  Duality enters exactly
  once, through WW3b's `card_wordH2`.
* **§4** `ker_heisD0_eq_fixedPts` — WW3b's *second* caution: `card_wordH0/H2` are phrased
  against `(heisD0 c).ker`, and the `fixedPts`-phrased clause needs a generation hypothesis.
  It costs 20 lines, not a ticket.
* **§5** `IsSelfDualN` + `isSelfDualN_of_stokesDuality` — the degree-generic `IsSelfDual`
  package (all three clauses) from one `StokesDuality` payload: **the "one theorem".**
* **§6** the factoring demonstration: `tcocycle_card_shape` and `hZcard_shape_of_simple`, two
  *different* `SourceDataN` clause shapes read off the *same* `IsSelfDualN`, valued in
  `standardNumerics n`'s moving leaves.  Derivation 2's side condition (the dual has no
  invariants) is discharged from `hZcard`'s own `hsimple`/`hnt` binders by the already-generic
  `card_fixedPts_elemDual_eq_one_of_nontrivial`, so **neither derivation needs any input the
  record does not already carry.**
* **§7** the N0 instantiation: `ι = Generator (2 + 2h)`, `ρ = Fin 2`, so the deficiency is
  `2h + 2` and the `standardNumerics` value bridge closes; at `h = 0` (the `√−2` pilot)
  `n = 2 = [ℚ₂(√−2) : ℚ₂]`.

## Import discipline

Plain-import: `GQ2.Dyadic.Recursion.Numerics` and `GQ2.Dyadic.Certificates.N0` are plain, so
this file cannot be `module`-style; `GQ2.Dyadic.Word.StokesDual` and `GQ2.DualityAssembly` are
`module`-style and are imported by a plain file, which is the permitted direction.

The `GQ2.DualityAssembly` import is for **one** already-generic, word-free leaf
(`card_fixedPts_elemDual_eq_one_of_nontrivial`).  A production CB file should hoist that leaf
rather than depend on the `ℚ₂` assembly stack; noted for CB-4.

Axioms: no new axioms, no `sorry`, no `decide`.  Every headline prints exactly the standard
three (`propext`, `Classical.choice`, `Quot.sound`) — recorded in the report.
-/

namespace GQ2.Dyadic.Count

open GQ2.FoxH GQ2.Dyadic

/-! ## §1. Rank–nullity for a three-term complex

`K₁ --d₁--> K₂`.  Lagrange twice plus the first isomorphism theorem eliminate `#(im d₁)`:

  `#K₁ = #(im d₁) · #(ker d₁)`,   `#K₂ = #H² · #(im d₁)`.

The `ℚ₂` ancestor (`card_Z1w_eq_sq_mul_card_H2w_R`) is this argument with `K₁ = Fin 4 → A`
and `K₂ = A × A` substituted *before* the elimination, which is where the literal `²` is
introduced.  Keeping the elimination abstract costs nothing and removes the exponent. -/

section ThreeTerm

variable {K₁ K₂ : Type*} [AddCommGroup K₁] [AddCommGroup K₂]

/-- **Rank–nullity, division-free and degree-free**: `#(ker d₁) · #K₂ = #K₁ · #H²`.

This is the entire mathematical content of `IsSelfDual`'s count clause.  It has no
hypotheses beyond finiteness — in particular no relator, no marking, no duality. -/
theorem card_ker_mul_card_cod [Finite K₁] [Finite K₂] (d₁ : K₁ →+ K₂) :
    Nat.card ↥d₁.ker * Nat.card K₂ = Nat.card K₁ * Nat.card (StokesH2 d₁) := by
  have e1 : Nat.card (K₁ ⧸ d₁.ker) = Nat.card ↥d₁.range :=
    Nat.card_congr (QuotientAddGroup.quotientKerEquivRange d₁).toEquiv
  have e2 : Nat.card K₁ = Nat.card (K₁ ⧸ d₁.ker) * Nat.card ↥d₁.ker :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  have e3 : Nat.card K₂ = Nat.card (StokesH2 d₁) * Nat.card ↥d₁.range :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup _
  rw [e2, e1, e3]
  ring

end ThreeTerm

/-! ## §2. The count at the generic word complex

`A --heisD0--> (ι → A) --heisD1--> (ρ → A)`, so `#C¹ = #A^{|ι|}` and `#C² = #A^{|ρ|}`, and §1
reads

  `#Z¹w · #A^{|ρ|} = #A^{|ι|} · #H²w(A)`.

**Still no duality.**  This is the honest degree-generic replacement for the `ℚ₂` lemma's
`#Z¹w = #A² · #H²w`; the `²` was `|ι| − |ρ|`. -/

section WordCount

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The degree-generic count, duality-free**: `#Z¹w · #A^{|ρ|} = #A^{|ι|} · #H²w(A)`. -/
theorem card_wordZ1_mul_pow [Finite A] (c : ι → C) (w : ρ → FreeGroup ι) :
    Nat.card ↥(heisD1 (A := A) c w).ker * Nat.card A ^ Nat.card ρ
      = Nat.card A ^ Nat.card ι * Nat.card (WordH2 c w A) := by
  have h := card_ker_mul_card_cod (heisD1 (A := A) c w)
  rwa [Nat.card_fun, Nat.card_fun] at h

end WordCount

/-! ## §3. The degree-generic clause 2

Duality enters exactly once, through WW3b's `card_wordH2 : #H²w(A) = #H⁰w(A^∨)`.  Everything
else was §2.  This is the theorem WW3b's warning said should not be expected; the warning was
right about the literal `²` and wrong about the statement. -/

section ClauseTwo

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]

/-- **Clause 2, degree-generic, division-free**:
`#Z¹w(A) · #A^{|ρ|} = #A^{|ι|} · #H⁰w(A^∨)`. -/
theorem card_wordZ1_mul_pow_dual {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card ↥(heisD1 (A := A) c w).ker * Nat.card A ^ Nat.card ρ
      = Nat.card A ^ Nat.card ι * Nat.card ↥(heisD0 (A := ElemDual A) c).ker := by
  rw [card_wordZ1_mul_pow c w, card_wordH2 hd hr hend]

/-- **Clause 2 at a degree-`n` marking**: under the deficiency-`n` condition
`|ι| = |ρ| + n + 1`, the count is `#Z¹w = #A^{n+1} · #H⁰w(A^∨)`.

At `ℚ₂` (`|ι| = 4`, `|ρ| = 2`, `n = 1`) this is the frozen literal
`#Z¹w = #A² · #(A^∨)^C`.  The deficiency convention is the campaign's own: `cor_5_17_card`
reads the `ℚ₂` presentation's `4 − 2 − 1 = 1` against the local Euler characteristic. -/
theorem card_wordZ1_of_degree {n : ℕ} {c : ι → C} {w : ρ → FreeGroup ι}
    (hdeg : Nat.card ι = Nat.card ρ + (n + 1)) (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    Nat.card ↥(heisD1 (A := A) c w).ker
      = Nat.card A ^ (n + 1) * Nat.card ↥(heisD0 (A := ElemDual A) c).ker := by
  have hpos : 0 < Nat.card A ^ Nat.card ρ := pow_pos Nat.card_pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [card_wordZ1_mul_pow_dual hd hr hend, hdeg, pow_add]
  ring

end ClauseTwo

/-! ## §4. The `fixedPts` bridge — WW3b's second caution

`card_wordH0/H2` are phrased against `(heisD0 c).ker`, but `SourceDataN`'s `tcocycle_card` is
phrased against `fixedPts`.  The two agree exactly when the marking generates, which is the
degree-generic form of the `ℚ₂` `H0w_eq_fixedPts` (`GQ2/Devissage/GeneratesBridge.lean:36`) —
the sole role of `hgen` in `isSelfDual_iff_W_R`.  Twenty lines, not a ticket. -/

section Generation

variable {ι : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- `ker d⁰` is the set of vectors fixed by every *marked* generator. -/
theorem mem_ker_heisD0_iff (c : ι → C) (v : A) :
    v ∈ (heisD0 (A := A) c).ker ↔ ∀ i, c i • v = v := by
  rw [AddMonoidHom.mem_ker, funext_iff]
  exact forall_congr' fun i => by rw [heisD0_apply, Pi.zero_apply, sub_eq_zero]

/-- **The generation bridge**: for a marking whose letters generate `C`, `ker d⁰` *is* the
set of `C`-invariants.  Degree-generic form of `GQ2.FoxH.H0w_eq_fixedPts`. -/
theorem ker_heisD0_eq_fixedPts {c : ι → C} (hgen : Subgroup.closure (Set.range c) = ⊤) :
    ((heisD0 (A := A) c).ker : Set A) = fixedPts C A := by
  ext v
  rw [SetLike.mem_coe, mem_ker_heisD0_iff]
  refine ⟨fun h g => ?_, fun h i => h (c i)⟩
  have hle : Subgroup.closure (Set.range c) ≤ MulAction.stabilizer C v :=
    (Subgroup.closure_le _).mpr (by rintro _ ⟨i, rfl⟩; exact h i)
  rw [hgen] at hle
  exact hle (Subgroup.mem_top g)

/-- The cardinality form of the bridge. -/
theorem card_ker_heisD0_eq_card_fixedPts {c : ι → C}
    (hgen : Subgroup.closure (Set.range c) = ⊤) :
    Nat.card ↥(heisD0 (A := A) c).ker = Nat.card (fixedPts C A) :=
  Nat.card_congr (Equiv.setCongr (ker_heisD0_eq_fixedPts hgen))

end Generation

/-! ## §5. The "one theorem"

CB1 memo §1.5's central design instruction: the eleven `SourceDataN` clauses are one theorem,
not eleven, because at `ℚ₂` they all factor through `prop_5_15_R`'s `IsSelfDual_R`.  Here is
the degree-generic package and the single theorem producing it.  All three clauses come from
**one** `StokesDuality` payload plus the endpoint/relator conditions the branch already has;
nothing else is consumed. -/

section OneTheorem

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]

/-- **The degree-generic `IsSelfDual` package** (`GQ2.FoxH.IsSelfDual`'s three clauses at the
degree-generic marking, phrased word-internally as `IsSelfDualW` is — §4 converts to
`fixedPts` where a branch has generation). -/
structure IsSelfDualN (n : ℕ) (c : ι → C) (w : ρ → FreeGroup ι) (A : Type*) [AddCommGroup A]
    [DistribMulAction C A] [Finite A] : Prop where
  /-- Clause 1 — the real content: `#H²w(A) = #H⁰w(A^∨)`. -/
  cardH2 : Nat.card (WordH2 c w A) = Nat.card ↥(heisD0 (A := ElemDual A) c).ker
  /-- Clause 2 — the count, degree-generic: `#Z¹w(A) = #A^{n+1} · #H⁰w(A^∨)`. -/
  cardZ1 : Nat.card ↥(heisD1 (A := A) c w).ker
    = Nat.card A ^ (n + 1) * Nat.card ↥(heisD0 (A := ElemDual A) c).ker
  /-- Clause 3 — the perfect degree-one pairing descending the traced Stokes pairing. -/
  pairing : ∃ P : WordH1 c w A → WordH1 c w (ElemDual A) → ZMod 2,
    (∀ (x : ↥(heisD1 (A := A) c w).ker) (y : ↥(heisD1 (A := ElemDual A) c w).ker),
        P (stokesH1Mk _ _ x) (stokesH1Mk _ _ y) = heisEta1 c w x.1 y.1) ∧
    (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧ (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0)

variable {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]

/-- Clause 3, extracted: `stokesChi1` is the pairing, `stokesChi1_injective` gives the left
half of nondegeneracy and `stokesChi1_separating` the right half. -/
theorem pairing_clause {c : ι → C} {w : ρ → FreeGroup ι} (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    ∃ P : WordH1 c w A → WordH1 c w (ElemDual A) → ZMod 2,
      (∀ (x : ↥(heisD1 (A := A) c w).ker) (y : ↥(heisD1 (A := ElemDual A) c w).ker),
          P (stokesH1Mk _ _ x) (stokesH1Mk _ _ y) = heisEta1 c w x.1 y.1) ∧
      (∀ h, h ≠ 0 → ∃ h', P h h' ≠ 0) ∧ (∀ h', h' ≠ 0 → ∃ h, P h h' ≠ 0) := by
  refine ⟨fun h h' => stokesChi1 (A := A) c w hr hend h h', fun x y => rfl, fun h hne => ?_,
    fun h' hne => stokesChi1_separating hd hr hend h' hne⟩
  by_contra hno
  push Not at hno
  exact hne ((injective_iff_map_eq_zero _).mp (stokesChi1_injective hd hr hend) h
    (ElemDual.ext hno))

/-- **The one theorem.**  A single `StokesDuality` payload at a degree-`n` marking yields all
three `IsSelfDual` clauses over the abstract carrier.

This is the statement CB-1 owns.  CB-2…CB-4 are meant to be short derivations from it (memo
§5's design instruction); §6 demonstrates two such derivations. -/
theorem isSelfDualN_of_stokesDuality {n : ℕ} {c : ι → C} {w : ρ → FreeGroup ι}
    (hdeg : Nat.card ι = Nat.card ρ + (n + 1)) (hd : StokesDuality c w A)
    (hr : ∀ k, FreeGroup.lift c (w k) = 1) (hend : IsStokesEndpoint w) :
    IsSelfDualN n c w A where
  cardH2 := card_wordH2 hd hr hend
  cardZ1 := card_wordZ1_of_degree hdeg hd hr hend
  pairing := pairing_clause hd hr hend

end OneTheorem

/-! ## §6. The factoring demonstration

Two *different* `SourceDataN` count clauses, read off the *same* `IsSelfDualN` with no further
cohomological input.  This is the miniature of memo §1.5's claim.

`SourceDataN`'s shapes (`GQ2/Dyadic/SourceDataN.lean:229,274`):

* `tcocycle_card : #TCocycle = SN.tMult #T * #fixedPts …(ElemDual T)`
* `hZcard        : #VCocycle = #V * SN.h1Mult #V`

and `standardNumerics n` (`GQ2/Dyadic/Recursion/Numerics.lean:82,83`) has
`tMult T = T^(n+1)`, `h1Mult V = V^n`.  Both fall out of clause 2 alone. -/

section Factoring

variable {ι ρ : Type*} [Fintype ι] [Fintype ρ] [DecidableEq ι] {C : Type*} [Group C]
  {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
  {n : ℕ} {c : ι → C} {w : ρ → FreeGroup ι}

omit [Fintype ι] [DecidableEq ι] in
/-- **Derivation 1 — the `tcocycle_card` shape.**  Clause 2 *is* `SN.tMult #A · #H⁰w(A^∨)` for
`SN = standardNumerics n`: the moving leaf `tMult T = T^{n+1}` absorbs the exponent
`|ι| − |ρ|` exactly. -/
theorem tcocycle_card_shape (S : IsSelfDualN n c w A) :
    Nat.card ↥(heisD1 (A := A) c w).ker
      = (standardNumerics n).tMult (Nat.card A)
        * Nat.card ↥(heisD0 (A := ElemDual A) c).ker :=
  S.cardZ1

omit [Fintype ι] [DecidableEq ι] in
/-- The same in `SourceDataN`'s own `fixedPts` spelling, for a generating marking (§4). -/
theorem tcocycle_card_shape_fixedPts (S : IsSelfDualN n c w A)
    (hgen : Subgroup.closure (Set.range c) = ⊤) :
    Nat.card ↥(heisD1 (A := A) c w).ker
      = (standardNumerics n).tMult (Nat.card A)
        * Nat.card (fixedPts C (ElemDual A)) := by
  rw [tcocycle_card_shape S, card_ker_heisD0_eq_card_fixedPts hgen]

omit [Fintype ι] [DecidableEq ι] in
/-- **Derivation 2 — the `hZcard` shape.**  For a module whose dual has no nonzero invariants
(what `hZcard`'s `hsimple`/`hnt` binders exist to supply), the *same* clause 2 reads
`#Z¹w = #V · SN.h1Mult #V`, with the **outer** `#V` literal and the **inner** factor
`h1Mult V = V^n` moving — SD-R3's shape rule (`SourceDataN.lean:260-263`) confirmed. -/
theorem hZcard_shape (S : IsSelfDualN n c w A)
    (hinv : Nat.card ↥(heisD0 (A := ElemDual A) c).ker = 1) :
    Nat.card ↥(heisD1 (A := A) c w).ker
      = Nat.card A * (standardNumerics n).h1Mult (Nat.card A) := by
  rw [S.cardZ1, hinv, mul_one]
  show Nat.card A ^ (n + 1) = Nat.card A * Nat.card A ^ n
  rw [pow_succ]
  ring

omit [Fintype ι] [DecidableEq ι] in
/-- **Derivation 2, with its side condition discharged.**  `hZcard`'s own binders — simplicity
of the module and nontriviality of the action — are exactly what forces the dual to have no
invariants, by the *already generic, word-free* `card_fixedPts_elemDual_eq_one_of_nontrivial`
(`GQ2/DualityAssembly.lean:112`).  So the `hZcard` shape needs no input beyond what
`SourceDataN` already carries plus generation. -/
theorem hZcard_shape_of_simple (S : IsSelfDualN n c w A)
    (hgen : Subgroup.closure (Set.range c) = ⊤) (hsimple : IsSimpleModTwo C A)
    (hnt : ∃ (g : C) (a : A), g • a ≠ a) :
    Nat.card ↥(heisD1 (A := A) c w).ker
      = Nat.card A * (standardNumerics n).h1Mult (Nat.card A) :=
  hZcard_shape S (by
    rw [card_ker_heisD0_eq_card_fixedPts hgen,
      card_fixedPts_elemDual_eq_one_of_nontrivial hsimple hnt])

omit [Fintype ι] [DecidableEq ι] in
/-- Sanity pin at `n = 1`: the two derivations reproduce the frozen `ℚ₂` literals
`#A² · #(A^∨)^C` and `#V · #V`. -/
theorem shape_pin_one (S : IsSelfDualN 1 c w A) :
    Nat.card ↥(heisD1 (A := A) c w).ker
        = Nat.card A ^ 2 * Nat.card ↥(heisD0 (A := ElemDual A) c).ker
      ∧ ((standardNumerics 1).h1Mult (Nat.card A) = Nat.card A) :=
  ⟨S.cardZ1, standardNumerics_one_h1Mult _⟩

end Factoring

/-! ## §7. The N0 instantiation and the `standardNumerics` value bridge

The compact-`N` branch: `ι = Generator (2 + 2h)` (so `|ι| = 2h + 5` by
`Parameters.card_generator`) and `ρ = Fin 2` (`nCompactFam` is a two-relator family:
tame + wild).  Deficiency `= (2h + 5) − 2 − 1 = 2h + 2`, so **N0 sits at degree `n = 2h + 2`**,
and at `h = 0` — the `√−2` pilot `nCompactFam 2 0 2 3` — at `n = 2`, which is
`[ℚ₂(√−2) : ℚ₂]`.  The `standardNumerics` value bridge therefore closes with no fudge. -/

section N0

open GQ2.Dyadic.Certificates

variable {C : Type*} [Group C]

/-- The N0 degree bookkeeping: `|ι| = |ρ| + (n + 1)` with `n = 2h + 2`. -/
theorem nCompact_degree (h : ℕ) :
    Nat.card (Generator (2 + 2 * h)) = Nat.card (Fin 2) + ((2 * h + 2) + 1) := by
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Generator.card_generator,
    Fintype.card_fin]
  omega

/-- **The count clause at N0**, from the branch's own Stokes payload.  `hd` is what
`nCompact_stokesDuality` returns and `hr` is its relator input in the form
`stokesDuality_of_simple` already uses. -/
theorem nCompact_cardZ1 {α h q e : ℕ} (t : Marking (2 + 2 * h) C)
    {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hd : StokesDuality ⇑t (nCompactFam α h q e) A)
    (hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam α h q e k) = 1)
    (hend : IsStokesEndpoint (nCompactFam α h q e)) :
    Nat.card ↥(heisD1 (A := A) ⇑t (nCompactFam α h q e)).ker
      = Nat.card A ^ (2 * h + 2 + 1)
        * Nat.card ↥(heisD0 (A := ElemDual A) ⇑t).ker :=
  card_wordZ1_of_degree (nCompact_degree h) hd hr hend

/-- **The N0 `IsSelfDualN` payload** at degree `n = 2h + 2` — the object CB-2…CB-4 would
consume at this branch. -/
theorem nCompact_isSelfDualN {α h q e : ℕ} (t : Marking (2 + 2 * h) C)
    {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hd : StokesDuality ⇑t (nCompactFam α h q e) A)
    (hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam α h q e k) = 1)
    (hend : IsStokesEndpoint (nCompactFam α h q e)) :
    IsSelfDualN (2 * h + 2) (⇑t) (nCompactFam α h q e) A :=
  isSelfDualN_of_stokesDuality (nCompact_degree h) hd hr hend

/-- **The `√−2` pilot value bridge**: at `(α, h, q, e) = (2, 0, 2, 3)` the degree is `n = 2`,
the endpoint condition is N0's own `sqrtNegTwo_isStokesEndpoint`, and the count is
`#Z¹w = #A³ · #H⁰w(A^∨)` — i.e. `standardNumerics 2`'s `tMult T = T³`, on the nose. -/
theorem sqrtNegTwo_cardZ1 (t : Marking 2 C)
    {A : Type*} [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hd : StokesDuality ⇑t (nCompactFam 2 0 2 3) A)
    (hr : ∀ k, FreeGroup.lift ⇑t (nCompactFam 2 0 2 3 k) = 1) :
    Nat.card ↥(heisD1 (A := A) ⇑t (nCompactFam 2 0 2 3)).ker
      = (standardNumerics 2).tMult (Nat.card A)
        * Nat.card ↥(heisD0 (A := ElemDual A) ⇑t).ker :=
  tcocycle_card_shape (nCompact_isSelfDualN t hd hr sqrtNegTwo_isStokesEndpoint)

end N0

end GQ2.Dyadic.Count
