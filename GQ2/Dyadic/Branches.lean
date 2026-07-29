/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.Algebra.Group.TypeTags.Hom
public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import GQ2.Dyadic.Parameters

@[expose] public section

/-!
# Dyadic campaign, layer F4: the marked cyclotomic datum and the arithmetic branches

The marked datum `(C, I, λ, γ)` of draft §2 (eqs. 2.1–2.3) and the **arithmetic branch
correction** of packet §8: Prop. 8.1 (the excluded branch) and Cor. 8.2 (`ℚ₂(√-10)`).

Everything here is *data-level*: `C` is an abstract group and `λ` an abstract surjection onto
`ℤ/2^r`.  No Galois theory, no field, no reciprocity map enters — the one statement that does
mention fields (Prop. 8.1's "hence `K(i)/K` is unramified") takes the field content as an
explicit hypothesis binder, in the exact shape of the AX3 `MarkedRecip` clause
(`docs/dyadic/ax3-proposal.md` §2.2 `ki_unramified`, §4.1 F4 row).  **No axiom is declared or
consumed here**; the census stays at 9.

References (all vendored under `docs/dyadic/refs/`, packet **overrides** drafts):

* **packet** = `dyadic-presentations-formalization-proof.tex`
  §8: Prop. 8.1 (`prop:sign-excluded`, line 774) and Cor. 8.2 (`cor:minus10`, line 801).
* **draft** = `dyadic-presentations.tex`
  §2 eqs. 2.1–2.3 (`eq:CI`, `eq:lambda`, `eq:gamma`) and the Warning after them; §10.2
  (line 1310) for the `CyclotomicFrobeniusDatum` shape; §7.3 for `ℚ₂(√10)`.
* **F1** = `GQ2/Dyadic/Parameters.lean` (the five-row `BranchData`, `epsVal`, `etaUnit`).
* **AX3 memo** = `docs/dyadic/ax3-proposal.md` (§2.2 the bundle, §4 the consumer binders,
  §7 R2/R3/R4 the risks this file is built against).

## Main definitions

* `GQ2.Dyadic.CyclotomicFrobeniusDatum` — draft §10.2's record: the level `r`, the surjection
  `λ : C →* Multiplicative (ZMod (2 ^ r))`, with `inertiaImage = ker λ` (draft eq. 2.1's `I`)
  and `gammaCoset` (draft eq. 2.3's `γ`, the coset of λ-value `1`).
* `GQ2.Dyadic.CyclotomicFrobeniusDatum.lambdaAdd` — the **additive** spelling of `λ`
  (AX3 memo §7 R3: the branch equations `λ(-1) = ε·2^{r-1}`, `λ(u) = η` are additive; every
  statement below is stated through `lambdaAdd`, never by mixing `ofAdd`-values into a row).
* `GQ2.Dyadic.etaValue` / `GQ2.Dyadic.IsEtaFor` — the one adapter between F1's `η : ℤ_[2]ˣ`
  (through `etaUnit`) and the draft's `Multiplicative (ZMod (2 ^ r))` λ-target.
* `GQ2.Dyadic.MarkedSplitting` — the marked pair `C = ⟨-1⟩ × ⟨u⟩` of packet §8, in the weakest
  form Prop. 8.1's proof consumes.

## Main results

* `GQ2.Dyadic.level_eq_one_of_even_of_spanning` — the ℤ/2^r arithmetic of packet Prop. 8.1,
  isolated from all group theory (this is where a sign or parity slip would live).
* `GQ2.Dyadic.MarkedSplitting.classification_of_even` — **packet Prop. 8.1, data level**:
  `η` even forces `r = 1`, `ε = 1` and `ker λ = ⟨u⟩`.
* `GQ2.Dyadic.MarkedSplitting.unramified_of_even` — its field-interpretation clause, as a
  hypothesis-shaped corollary; `MarkedSplitting.not_even_eta_of_not_unramified` and
  `MarkedSplitting.level_zero_or_not_even_eta` are the forms the branch table consumes.
* `GQ2.Dyadic.not_even_lambdaAdd_of_isEtaFor` — a row carrying `η : ℤ_[2]ˣ` is automatically
  outside the excluded branch (F1's design decision, cashed) — and conversely
  `GQ2.Dyadic.exists_isEtaFor_of_not_even`, so the procyclic rows are *exactly* the marked data
  with odd `λ(u)`.
* `GQ2.Dyadic.branchSqrtNegTen` and `GQ2.Dyadic.toZModPow_three_eq_five_of_inv_neg_three`,
  `GQ2.Dyadic.isSquare_neg_two_div_five_iff` — **packet Cor. 8.2**.
* `GQ2.Dyadic.branchData_five_rows`, `GQ2.Dyadic.exists_M_row`, `GQ2.Dyadic.exists_N_row`,
  `GQ2.Dyadic.exists_L_row`, `GQ2.Dyadic.eps_both_occur` — the exhaustiveness package.
* `GQ2.Dyadic.mockDatum` / `GQ2.Dyadic.mockSplitting` and the `mock_*` pins — the **mandated
  synthetic `r = 2` regression** of AX3 memo §7 R2 (final section).

## The excluded branch, stated positively

Packet Prop. 8.1 *removes* a row from the ramified-`i` assembly: if `λ(u)` is even then
`K(i)/K` is unramified, which is outside the standing hypothesis of this campaign.  A removed
row is not a Lean object — nothing in `GQ2/Dyadic/` may *declare* it (this is what
`scripts/check_dyadic.sh` check D3 enforces).  The positive content is therefore stated as
the exhaustiveness of F1's five rows (`branchData_five_rows` and the three realizability
lemmas) plus the dichotomy `level_zero_or_not_even_eta`: under ramified `i` a type-`M` field is
on the compact row `r = 0` or on the procyclic row `r ≥ 1` with `λ(u)` odd.

## How the AX3 binder is threaded

`MarkedSplitting.unramified_of_even` takes

* `chi : C →* ℤ_[2]ˣ`, the cyclotomic coordinate of the marked datum (`C ⊆ ℤ₂ˣ` in the
  arithmetic model, so `chi` is the inclusion);
* `bridge`, an implication `(∀ c ∈ ker λ, chi c ≡ 1 mod 4) → Unramified`, and
* `Unramified : Prop`, the field-side conclusion, opaque here.

`bridge` is the AX3 bundle's `ki_unramified` clause (memo §2.2) in marked-datum coordinates:
when `GQ2/Dyadic/MarkedRecipBundle.lean` lands, a consumer holding
`(B : MarkedRecip localReciprocity K)` takes `C := (chiCycKAb K).range`, `chi := C.subtype`,
`Unramified := ∀ δi, δi ^ 2 = -1 → HasEqualNormValueGroups K δi`, and obtains `bridge` from
`B.ki_unramified` through the derived identification `ker λ = I = χ(ker ν)` (memo §1.5) — every
`c ∈ ker λ` is `χ g` for some `g` with `ν g = 1`, which is exactly that clause's premise.  Until
the bundle lands — and, for the data-level lemmas, forever after — nothing here depends on it,
so this layer compiles and is auditable before the G-AX gate.  MC5 and the boundary lane consume
the same shape: they bind `B` and feed `B`'s derived `(C, I, λ, γ)` into these lemmas.

## Implementation notes

* **Dependent-type discipline.**  `ZMod (2 ^ d.r)` depends on the datum, so `d.r = 1` can never
  be rewritten inside a type.  All arithmetic that needs the value of `r` is therefore proved in
  `eq_zero_of_even_of_level_one`, `eq_zero_or_eq_two_pow_pred` and
  `level_eq_one_of_even_of_spanning`, where `r` is a *free variable* and `subst`/`decide` are
  available; the datum-level theorems only ever consume the element equations `b = 0`, `a ≠ 0`
  that the last of these returns.
* **`r = 0` (AX3 memo §7 R4).**  `ε · 2^{r-1}` is meaningless at `r = 0` (`ZMod (2 ^ 0)` is
  trivial and ℕ-subtraction truncates), so every statement whose conclusion reads `ε`, or
  excludes a branch, carries `1 ≤ r`; the compact rows are the `r = 0` fact itself.
* **The compact-`M` change of variables is not needed here.**  MC1's memo (`mc-design.md` §7.2,
  owner question Q4) records that the compact-`M` (`r = 0`) marked change of variables is missing
  from the vendored sources.  Nothing in this file uses it: the `r = 0` row enters only as the
  *level* fact `d.r = 0` (`level_zero_or_not_even_eta`, `exists_M_row`), never through a
  coordinate substitution.  The gap therefore does not block F4; it still blocks MC5/WM0.
* This file is `module`-style; all four imports are `module`-style, so plan §3 A5 is satisfied.
-/

namespace GQ2.Dyadic

/-! ## Parity in `ZMod (2 ^ r)`

The excluded branch is a parity statement, so the whole of packet Prop. 8.1 factors through the
reduction `ℤ/2^r → ℤ/2`.  Keeping it as a ring hom (rather than juggling `Even`) is what makes
the `ℤ`-linear-combination step of the proof one `map_zsmul`. -/

section Parity

variable {r : ℕ}

theorem two_dvd_two_pow (hr : 1 ≤ r) : 2 ∣ 2 ^ r := dvd_pow_self 2 (by omega)

/-- The parity homomorphism `ℤ/2^r → ℤ/2`, defined for `r ≥ 1`. -/
def parity (hr : 1 ≤ r) : ZMod (2 ^ r) →+* ZMod 2 := ZMod.castHom (two_dvd_two_pow hr) (ZMod 2)

@[simp] theorem parity_natCast (hr : 1 ≤ r) (k : ℕ) :
    parity hr (k : ZMod (2 ^ r)) = (k : ZMod 2) := map_natCast (parity hr) k

theorem parity_eq_zero_of_even (hr : 1 ≤ r) {x : ZMod (2 ^ r)} (hx : Even x) :
    parity hr x = 0 := by
  obtain ⟨y, rfl⟩ := hx
  have h : ∀ z : ZMod 2, z + z = 0 := by decide
  rw [map_add]
  exact h _

/-- A unit of `ℤ/2^r` is odd (`r ≥ 1`).  This is the abstract form of F1's
`toZMod_units_eq_one`, and the reason a row carrying `η : ℤ_[2]ˣ` can never be the branch that
packet Prop. 8.1 excludes. -/
theorem not_even_of_isUnit (hr : 1 ≤ r) {x : ZMod (2 ^ r)} (hx : IsUnit x) : ¬ Even x := by
  intro h
  have h1 : IsUnit (parity hr x) := hx.map (parity hr)
  rw [parity_eq_zero_of_even hr h] at h1
  exact not_isUnit_zero h1

/-- At level `r = 1` an even element vanishes: `ℤ/2` has no room. -/
theorem eq_zero_of_even_of_level_one (hr : r = 1) {x : ZMod (2 ^ r)} (hx : Even x) : x = 0 := by
  subst hr
  obtain ⟨y, rfl⟩ := hx
  revert y
  decide

/-- `2^n ∣ 2k` and `k < 2^n` (`n ≥ 1`) leave only `k = 0` and `k = 2^{n-1}`: the two-torsion of
`ℤ/2^n`, in ℕ.  Kept free of `ZMod` so that no dependent type is rewritten. -/
theorem eq_zero_or_eq_two_pow_pred {n k : ℕ} (hn : 1 ≤ n) (hdvd : 2 ^ n ∣ 2 * k)
    (hlt : k < 2 ^ n) : k = 0 ∨ k = 2 ^ (n - 1) := by
  have hpow : (2 : ℕ) ^ n = 2 * 2 ^ (n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  rw [hpow, Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 2)] at hdvd
  obtain ⟨m, rfl⟩ := hdvd
  rw [hpow] at hlt
  have hp : 0 < 2 ^ (n - 1) := pow_pos (by norm_num) _
  have hm2 : m < 2 := by
    rcases Nat.lt_or_ge m 2 with hcon | hcon
    · exact hcon
    · exact absurd (Nat.mul_le_mul_left (2 ^ (n - 1)) hcon) (by omega)
  interval_cases m
  · exact Or.inl (by simp)
  · exact Or.inr (by simp)

end Parity

/-! ## The cyclotomic Frobenius datum (draft §2 eqs. 2.1–2.3, §10.2) -/

/-- The **cyclotomic Frobenius datum** of draft §10.2: the marked level `r`, together with the
canonical quotient `λ : C ↠ ℤ/2^r` of draft eq. 2.2.

`C` is the cyclotomic image `χ(D_K)` of draft eq. 2.1 and `λ(χ g) = ν_ur(g) mod 2^r`; both are
abstract here — see the module docstring.  Following draft §10.2 the target is written
multiplicatively, `Multiplicative (ZMod (2 ^ r))`, so that `λ` is a `MonoidHom` out of the
multiplicative group `C`; every *value* statement uses the additive spelling `lambdaAdd`
(AX3 memo §7 R3).  In particular draft eq. 2.3's `λ(γ) = 1` is the additive `1`, i.e.
`lambdaAdd γ = 1` — **not** the identity of the target, which would say `γ ∈ I`. -/
structure CyclotomicFrobeniusDatum (C : Type*) [Group C] where
  /-- The marked level `r`, i.e. `A = ν_ur(ker χ) = 2^r ℤ₂` (draft eq. 2.1). -/
  r : ℕ
  /-- The marked quotient `λ : C ↠ ℤ/2^r` of draft eq. 2.2, written multiplicatively. -/
  lambda : C →* Multiplicative (ZMod (2 ^ r))
  /-- `λ` is surjective (draft eq. 2.2). -/
  lambda_surjective : Function.Surjective lambda

namespace CyclotomicFrobeniusDatum

variable {C : Type*} [Group C] (d : CyclotomicFrobeniusDatum C)

/-- The additive spelling of `λ`: `lambdaAdd c ∈ ℤ/2^r` is the unramified degree of `c`.  All
branch equations (`λ(-1) = ε·2^{r-1}`, `λ(u) = η`, `λ(γ) = 1`) are stated through this. -/
def lambdaAdd (c : C) : ZMod (2 ^ d.r) := Multiplicative.toAdd (d.lambda c)

@[simp] theorem lambdaAdd_mul (c c' : C) :
    d.lambdaAdd (c * c') = d.lambdaAdd c + d.lambdaAdd c' := by
  simp [lambdaAdd]

@[simp] theorem lambdaAdd_one : d.lambdaAdd 1 = 0 := by simp [lambdaAdd]

@[simp] theorem lambdaAdd_inv (c : C) : d.lambdaAdd c⁻¹ = -d.lambdaAdd c := by
  simp [lambdaAdd]

theorem lambdaAdd_zpow (c : C) (k : ℤ) : d.lambdaAdd (c ^ k) = k • d.lambdaAdd c := by
  simp [lambdaAdd]

theorem lambdaAdd_surjective : Function.Surjective d.lambdaAdd := fun z => by
  obtain ⟨c, hc⟩ := d.lambda_surjective (Multiplicative.ofAdd z)
  exact ⟨c, by simp [lambdaAdd, hc]⟩

/-- The inertia image `I = χ(ker ν_ur) = ker λ` of draft eq. 2.1.  The two descriptions agree by
the AX3 memo §1.5 derivation `I = ker λ`; on the data level `ker λ` is the definition. -/
abbrev inertiaImage : Subgroup C := d.lambda.ker

theorem mem_inertiaImage_iff {c : C} : c ∈ d.inertiaImage ↔ d.lambdaAdd c = 0 :=
  MonoidHom.mem_ker

/-- `C/I ≃ ℤ/2^r`, the canonical isomorphism induced by `λ` (draft eq. 2.2). -/
noncomputable def quotientEquiv : C ⧸ d.inertiaImage ≃* Multiplicative (ZMod (2 ^ d.r)) :=
  QuotientGroup.quotientKerEquivOfSurjective d.lambda d.lambda_surjective

@[simp] theorem quotientEquiv_mk (c : C) :
    d.quotientEquiv (QuotientGroup.mk c) = d.lambda c := rfl

/-- The Frobenius coset `γ ∈ C/I` of draft eq. 2.3: the unique coset of λ-value `1`.

Choosing it as a *coset* rather than a representative is draft §10.2's instruction ("a
representative should be chosen only when a concrete word requires a Frobenius lift"). -/
noncomputable def gammaCoset : C ⧸ d.inertiaImage :=
  d.quotientEquiv.symm (Multiplicative.ofAdd 1)

/-- Draft eq. 2.3, `λ(γ) = 1`: a representative of `γ` is exactly an element of unramified
degree `1`.  ⚠ The `1` is the additive one of `ℤ/2^r`, not the identity of the λ-target. -/
theorem mk_eq_gammaCoset_iff {g : C} :
    (QuotientGroup.mk g : C ⧸ d.inertiaImage) = d.gammaCoset ↔ d.lambdaAdd g = 1 := by
  constructor
  · intro h
    have h' := congrArg d.quotientEquiv h
    rwa [quotientEquiv_mk, gammaCoset, MulEquiv.apply_symm_apply] at h'
  · intro h
    refine d.quotientEquiv.injective ?_
    rw [quotientEquiv_mk, gammaCoset, MulEquiv.apply_symm_apply]
    exact h

theorem exists_rep_gammaCoset :
    ∃ g : C, (QuotientGroup.mk g : C ⧸ d.inertiaImage) = d.gammaCoset ∧ d.lambdaAdd g = 1 := by
  obtain ⟨g, hg⟩ := d.lambdaAdd_surjective 1
  exact ⟨g, d.mk_eq_gammaCoset_iff.2 hg, hg⟩

end CyclotomicFrobeniusDatum

/-! ## The `η` adapter (F1 `etaUnit` ↔ draft §10.2 λ-target)

F1 carries the Frobenius unit as `η : ℤ_[2]ˣ` and exports `etaUnit r η : (ZMod (2 ^ r))ˣ` as
"the λ(u)-comparison hook"; draft §10.2 spells λ-values in `Multiplicative (ZMod (2 ^ r))`.  The
two are related by *one* adapter, below — the units are units of the **ring** `ZMod (2 ^ r)`
while the λ-target is its **additive** group written multiplicatively, so the bridge is the
underlying-element coercion, and nothing else in the campaign may re-spell it. -/

section Eta

variable {C : Type*} [Group C]

/-- F1's `η : ℤ_[2]ˣ` as an element of the draft's λ-target `Multiplicative (ZMod (2 ^ r))`. -/
noncomputable def etaValue (r : ℕ) (η : ℤ_[2]ˣ) : Multiplicative (ZMod (2 ^ r)) :=
  Multiplicative.ofAdd ((etaUnit r η : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r))

@[simp] theorem toAdd_etaValue (r : ℕ) (η : ℤ_[2]ˣ) :
    Multiplicative.toAdd (etaValue r η) = ((etaUnit r η : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) := rfl

@[simp] theorem toAdd_etaValue_eq_toZModPow (r : ℕ) (η : ℤ_[2]ˣ) :
    Multiplicative.toAdd (etaValue r η) = PadicInt.toZModPow r (η : ℤ_[2]) := rfl

/-- `η : ℤ_[2]ˣ` **represents** the marked value `λ(u)`: F1's compatibility `etaUnit r η = λ(u)`.
Two lifts of the same `λ(u)` differ by `1 + 2^r ℤ₂`, so this is the whole content of F1's
"`η` lives as a `2`-adic unit" design decision. -/
def IsEtaFor (d : CyclotomicFrobeniusDatum C) (u : C) (η : ℤ_[2]ˣ) : Prop :=
  d.lambdaAdd u = ((etaUnit d.r η : (ZMod (2 ^ d.r))ˣ) : ZMod (2 ^ d.r))

theorem isEtaFor_iff {d : CyclotomicFrobeniusDatum C} {u : C} {η : ℤ_[2]ˣ} :
    IsEtaFor d u η ↔ d.lambda u = etaValue d.r η := Iff.rfl

/-- **A row carrying `η : ℤ_[2]ˣ` is never the excluded branch.**  Packet Prop. 8.1 excludes the
case "`λ(u)` even"; if `λ(u)` is represented by a `2`-adic *unit* then it is odd, so the excluded
case cannot arise on F1's two procyclic rows.  (F1's `BranchData` carries `η : ℤ_[2]ˣ` precisely
so that this is a typing fact rather than a side condition.) -/
theorem not_even_lambdaAdd_of_isEtaFor {d : CyclotomicFrobeniusDatum C} {u : C} {η : ℤ_[2]ˣ}
    (hr : 1 ≤ d.r) (h : IsEtaFor d u η) : ¬ Even (d.lambdaAdd u) := by
  rw [IsEtaFor] at h
  rw [h]
  exact not_even_of_isUnit hr (etaUnit d.r η).isUnit

/-- **Conversely, every odd marked value comes from a `2`-adic unit**: `η : ℤ_[2]ˣ` loses nothing
against a `(ZMod (2 ^ r))ˣ`-valued datum.  Together with `not_even_lambdaAdd_of_isEtaFor` this
says that F1's procyclic rows are *exactly* the marked data with odd `λ(u)` — the half of
exhaustiveness that the choice of `η`'s type could have broken.  No `1 ≤ r` is needed: at `r = 0`
every element of the trivial group `ℤ/1` is even, so the hypothesis is vacuous. -/
theorem exists_etaUnit_of_not_even {r : ℕ} {x : ZMod (2 ^ r)} (hx : ¬ Even x) :
    ∃ η : ℤ_[2]ˣ, ((etaUnit r η : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) = x := by
  haveI : NeZero (2 ^ r) := ⟨by positivity⟩
  obtain ⟨k, hk⟩ := ZMod.natCast_zmod_surjective x
  have hkodd : ¬ Even k := by
    rintro ⟨m, rfl⟩
    exact hx (hk ▸ ⟨(m : ZMod (2 ^ r)), by push_cast; ring⟩)
  have hunit : IsUnit ((k : ℤ_[2])) := by
    rw [PadicInt.isUnit_iff]
    rcases eq_or_lt_of_le (PadicInt.norm_le_one ((k : ℤ_[2]))) with h | h
    · exact h
    · refine absurd ?_ hkodd
      rw [PadicInt.norm_lt_one_iff_dvd] at h
      obtain ⟨c, hc⟩ := h
      have h0 : ((k : ℕ) : ZMod 2) = 0 := by
        have h2 := congrArg PadicInt.toZMod hc
        rwa [map_natCast, map_mul, map_natCast, ZMod.natCast_self, zero_mul] at h2
      exact ZMod.natCast_eq_zero_iff_even.1 h0
  refine ⟨hunit.unit, ?_⟩
  rw [etaUnit_coe, IsUnit.unit_spec, map_natCast, hk]

/-- Datum form of `exists_etaUnit_of_not_even`: a procyclic row with odd `λ(u)` really is an F1
row, i.e. some `η : ℤ_[2]ˣ` represents its marked value. -/
theorem exists_isEtaFor_of_not_even {d : CyclotomicFrobeniusDatum C} {u : C}
    (hx : ¬ Even (d.lambdaAdd u)) : ∃ η : ℤ_[2]ˣ, IsEtaFor d u η := by
  obtain ⟨η, hη⟩ := exists_etaUnit_of_not_even hx
  exact ⟨η, hη.symm⟩

end Eta

/-! ## Packet Prop. 8.1: the arithmetic branch correction

The proposition has two halves.  The **arithmetic** half is `level_eq_one_of_even_of_spanning`:
pure `ZMod (2 ^ r)` bookkeeping, no group and no field, which is where the `ε`/`η` signs live.
The **structural** half is `MarkedSplitting.classification_of_even`, which adds `ker λ = ⟨u⟩`. -/

section Arithmetic

/-- **Packet Prop. 8.1, arithmetic core.**  Let `a = ε·2^{r-1}` and `b` be an even element of
`ℤ/2^r` (`r ≥ 1`) whose `ℤ`-span is everything.  Then `r = 1`, `ε = 1`, `b = 0` and `a ≠ 0`.

`a` and `b` are `λ(-1)` and `λ(u) = η`; the spanning hypothesis is surjectivity of `λ` together
with `C = ⟨-1⟩ × ⟨u⟩`.  The last two conclusions are the element equations the group-level
statement needs, returned here because `r` is a *free variable* in this lemma and so `r = 1`
may be substituted — inside a datum it cannot (module docstring, dependent-type discipline). -/
theorem level_eq_one_of_even_of_spanning {r : ℕ} (hr : 1 ≤ r) (ε : Bool) {a b : ZMod (2 ^ r)}
    (ha : a = ((epsVal ε * 2 ^ (r - 1) : ℕ) : ZMod (2 ^ r))) (hb : Even b)
    (hspan : ∀ z : ZMod (2 ^ r), ∃ i j : ℤ, z = i • a + j • b) :
    r = 1 ∧ ε = true ∧ b = 0 ∧ a ≠ 0 := by
  -- The parity of `a` is `1`: otherwise the span of `{a, b}` misses `1`.
  have hpb : parity hr b = 0 := parity_eq_zero_of_even hr hb
  have hpa : parity hr a ≠ 0 := by
    intro h0
    obtain ⟨i, j, hij⟩ := hspan 1
    have : (1 : ZMod 2) = 0 := by
      have := congrArg (parity hr) hij
      rwa [map_one, map_add, map_zsmul, map_zsmul, h0, hpb, smul_zero, smul_zero,
        add_zero] at this
    exact one_ne_zero this
  -- `ε = 1`, since `ε = 0` would make `a = 0`.
  have hε : ε = true := by
    cases ε with
    | false => exact absurd (by rw [ha]; simp [epsVal]) hpa
    | true => rfl
  -- `r = 1`, since `2 ∣ 2^{r-1}` for `r ≥ 2` would make `a` even.
  have hr1 : r = 1 := by
    by_contra hne
    have hr2 : 2 ≤ r := by omega
    refine hpa ?_
    rw [ha, parity_natCast, ZMod.natCast_eq_zero_iff_even]
    exact even_iff_two_dvd.2 (Dvd.dvd.mul_left (dvd_pow_self 2 (by omega)) _)
  refine ⟨hr1, hε, eq_zero_of_even_of_level_one hr1 hb, ?_⟩
  intro h0
  exact hpa (by rw [h0, map_zero])

end Arithmetic

/-! ### The marked splitting `C = ⟨-1⟩ × ⟨u⟩` -/

/-- The marked pair of packet §8: `C = ⟨-1⟩ × ⟨u⟩` with `u = (1 - 2^α)⁻¹ ∈ 1 + 4ℤ₂`.

The fields are the *weakest* form of that splitting which Prop. 8.1's proof consumes, chosen so
that the arithmetic model can supply them: in the model `procyclic` is the **topological**
closure of `u ^ ℤ` inside `ℤ₂ˣ`, which is strictly larger than the abstract subgroup generated
by `u`, so neither `procyclic = Subgroup.closure {u}` nor `Subgroup.closure {negOne, u} = ⊤`
may be assumed.  What survives, and is all that is used, is:

* the λ-image of `procyclic` is generated by `η = λ(u)` (`lambdaAdd_procyclic` — true in the
  model because `λ` is continuous with finite target), and
* `C` is covered by the two cosets of `procyclic` (`exists_decomp`).

`negOne_sq` (the packet's "the element `-1` has order two") is what makes `λ(-1)` two-torsion,
hence of the form `ε·2^{r-1}` — see `MarkedSplitting.exists_eps`. -/
structure MarkedSplitting {C : Type*} [Group C] (d : CyclotomicFrobeniusDatum C) where
  /-- The torsion generator `-1 ∈ C`. -/
  negOne : C
  /-- The topological generator `u = (1 - 2^α)⁻¹` of the procyclic factor. -/
  u : C
  /-- The procyclic factor `⟨u⟩ ≤ C`. -/
  procyclic : Subgroup C
  /-- `-1` has order dividing two. -/
  negOne_sq : negOne ^ 2 = 1
  /-- `u ∈ ⟨u⟩`. -/
  u_mem : u ∈ procyclic
  /-- `λ(⟨u⟩) = ⟨λ(u)⟩`: the λ-image of the procyclic factor is generated by `η`. -/
  lambdaAdd_procyclic : ∀ w ∈ procyclic, ∃ j : ℤ, d.lambdaAdd w = j • d.lambdaAdd u
  /-- `C = ⟨-1⟩ · ⟨u⟩`: every element of `C` is `w` or `-w` for some `w` in the procyclic
  factor. -/
  exists_decomp : ∀ c : C, ∃ w ∈ procyclic, c = w ∨ c = negOne * w

namespace MarkedSplitting

variable {C : Type*} [Group C] {d : CyclotomicFrobeniusDatum C} (S : MarkedSplitting d)

/-- `η = λ(u)`, the Frobenius value of the row (draft §5.3, packet §8). -/
def eta : ZMod (2 ^ d.r) := d.lambdaAdd S.u

/-- `λ(-1)`, which packet §8 writes as `ε·2^{r-1}`. -/
def negOneVal : ZMod (2 ^ d.r) := d.lambdaAdd S.negOne

theorem eta_def : S.eta = d.lambdaAdd S.u := rfl

theorem negOneVal_def : S.negOneVal = d.lambdaAdd S.negOne := rfl

theorem two_nsmul_negOneVal : (2 : ℕ) • S.negOneVal = 0 := by
  have h := congrArg d.lambdaAdd S.negOne_sq
  rw [pow_two, d.lambdaAdd_mul, d.lambdaAdd_one, ← two_nsmul] at h
  exact h

/-- Surjectivity of `λ` plus `C = ⟨-1⟩ · ⟨u⟩` says that `λ(-1)` and `η` span `ℤ/2^r`. -/
theorem spanning (z : ZMod (2 ^ d.r)) : ∃ i j : ℤ, z = i • S.negOneVal + j • S.eta := by
  obtain ⟨c, hc⟩ := d.lambdaAdd_surjective z
  obtain ⟨w, hw, hcw | hcw⟩ := S.exists_decomp c
  · obtain ⟨j, hj⟩ := S.lambdaAdd_procyclic w hw
    exact ⟨0, j, by rw [← hc, hcw, hj]; simp [eta]⟩
  · obtain ⟨j, hj⟩ := S.lambdaAdd_procyclic w hw
    exact ⟨1, j, by rw [← hc, hcw, d.lambdaAdd_mul, hj]; simp [eta, negOneVal]⟩

/-- `λ(-1) = ε·2^{r-1}` for a **unique Boolean** `ε` (`r ≥ 1`): the two-torsion of `ℤ/2^r` is
`{0, 2^{r-1}}`.  This is F1's `epsVal` design decision (`ε : Bool`, not `ZMod 2` or `Fin 2`)
as a theorem, and it shows that the `hε` hypothesis of the classification below is free. -/
theorem exists_eps (hr : 1 ≤ d.r) :
    ∃ ε : Bool, S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r)) := by
  haveI : NeZero (2 ^ d.r) := ⟨by positivity⟩
  have hval : ((2 * S.negOneVal.val : ℕ) : ZMod (2 ^ d.r)) = 0 := by
    push_cast
    rw [ZMod.natCast_zmod_val, two_mul, ← two_nsmul]
    exact S.two_nsmul_negOneVal
  have hdvd : (2 : ℕ) ^ d.r ∣ 2 * S.negOneVal.val := (ZMod.natCast_eq_zero_iff _ _).1 hval
  rcases eq_zero_or_eq_two_pow_pred hr hdvd (ZMod.val_lt _) with h | h
  · exact ⟨false, by rw [← ZMod.natCast_zmod_val S.negOneVal, h]; simp [epsVal]⟩
  · exact ⟨true, by rw [← ZMod.natCast_zmod_val S.negOneVal, h]; simp [epsVal]⟩

/-- **Packet Prop. 8.1, data level.**  If the Frobenius value `η = λ(u)` is even then the marked
level is `r = 1`, the sign parameter is `ε = 1`, and the inertia image is the procyclic factor:
`ker λ = ⟨u⟩`.

`1 ≤ d.r` is not decoration: at `r = 0` the target `ℤ/2^0` is trivial, `λ(u) = 0` is even for
free, and `ker λ = C`, which need not be `⟨u⟩` — that is the compact row, which the proposition
is not about (AX3 memo §7 R4).  `hε` is free by `exists_eps`. -/
theorem classification_of_even (hr : 1 ≤ d.r) (ε : Bool)
    (hε : S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r))) (hη : Even S.eta) :
    d.r = 1 ∧ ε = true ∧ d.inertiaImage = S.procyclic := by
  obtain ⟨hr1, hεt, hb, ha⟩ :=
    level_eq_one_of_even_of_spanning hr ε hε hη (fun z => S.spanning z)
  refine ⟨hr1, hεt, le_antisymm ?_ ?_⟩
  · intro c hc
    rw [d.mem_inertiaImage_iff] at hc
    obtain ⟨w, hw, hcw | hcw⟩ := S.exists_decomp c
    · rwa [hcw]
    · obtain ⟨j, hj⟩ := S.lambdaAdd_procyclic w hw
      rw [hcw, d.lambdaAdd_mul, hj, ← S.eta_def, hb, smul_zero, add_zero,
        ← S.negOneVal_def] at hc
      exact absurd hc ha
  · intro w hw
    obtain ⟨j, hj⟩ := S.lambdaAdd_procyclic w hw
    rw [d.mem_inertiaImage_iff, hj, ← S.eta_def, hb, smul_zero]

/-- Packet Prop. 8.1 as the campaign consumes it: `r = 1 ∧ ε = 1`. -/
theorem level_eq_one_of_even (hr : 1 ≤ d.r) (ε : Bool)
    (hε : S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r))) (hη : Even S.eta) :
    d.r = 1 := (S.classification_of_even hr ε hε hη).1

/-- Packet Prop. 8.1's `I = ker λ = ⟨u⟩`. -/
theorem inertiaImage_eq_of_even (hr : 1 ≤ d.r) (ε : Bool)
    (hε : S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r))) (hη : Even S.eta) :
    d.inertiaImage = S.procyclic := (S.classification_of_even hr ε hε hη).2.2

/-! ### The field-interpretation clause (AX3 `MarkedRecip` binder)

Packet Prop. 8.1's last sentence — "hence `K(i)/K` is unramified" — is the only field statement
of §8.  It is *not* proved here and no axiom is added for it: the field content enters as the
`bridge` binder, whose shape is the AX3 bundle's `ki_unramified` clause (memo §2.2), and the
conclusion `Unramified` is an opaque `Prop`.  See the module docstring for the instantiation. -/

/-- **Packet Prop. 8.1, field clause** (hypothesis-shaped).  If the Frobenius value `η = λ(u)`
is even, and the procyclic factor acts trivially on `μ₄` (`chi w ≡ 1 mod 4` for `w ∈ ⟨u⟩`, true
in the model because `u ∈ 1 + 4ℤ₂` and `1 + 4ℤ₂` is closed), then the inertia image acts
trivially on `μ₄`, which is the premise of the AX3 bridge; so `K(i)/K` is unramified. -/
theorem unramified_of_even {Unramified : Prop} (hr : 1 ≤ d.r) (ε : Bool)
    (hε : S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r))) (hη : Even S.eta)
    (chi : C →* ℤ_[2]ˣ)
    (hproc : ∀ w ∈ S.procyclic, PadicInt.toZModPow 2 ((chi w : ℤ_[2])) = 1)
    (bridge : (∀ c ∈ d.inertiaImage, PadicInt.toZModPow 2 ((chi c : ℤ_[2])) = 1) → Unramified) :
    Unramified := by
  refine bridge fun c hc => hproc c ?_
  rwa [S.inertiaImage_eq_of_even hr ε hε hη] at hc

/-- **Under the standing ramified-`i` hypothesis, `η` is odd** — the contrapositive of
`unramified_of_even`, and the exhaustiveness input for F1's five-row branch datum. -/
theorem not_even_eta_of_not_unramified {Unramified : Prop} (hr : 1 ≤ d.r) (ε : Bool)
    (hε : S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r)))
    (chi : C →* ℤ_[2]ˣ)
    (hproc : ∀ w ∈ S.procyclic, PadicInt.toZModPow 2 ((chi w : ℤ_[2])) = 1)
    (bridge : (∀ c ∈ d.inertiaImage, PadicInt.toZModPow 2 ((chi c : ℤ_[2])) = 1) → Unramified)
    (hram : ¬ Unramified) : ¬ Even S.eta := fun hη =>
  hram (S.unramified_of_even hr ε hε hη chi hproc bridge)

/-- **The surviving `M_α` rows, stated positively** (packet Prop. 8.1's last sentence): under
ramified `i` a marked datum is on the compact row `r = 0`, or on the procyclic row `r ≥ 1` with
`η = λ(u)` odd.  There is no third possibility — which is exactly the content of the row that
packet §8 removed from the draft's assembly. -/
theorem level_zero_or_not_even_eta {Unramified : Prop}
    (hε : 1 ≤ d.r → ∃ ε : Bool,
      S.negOneVal = ((epsVal ε * 2 ^ (d.r - 1) : ℕ) : ZMod (2 ^ d.r)))
    (chi : C →* ℤ_[2]ˣ)
    (hproc : ∀ w ∈ S.procyclic, PadicInt.toZModPow 2 ((chi w : ℤ_[2])) = 1)
    (bridge : (∀ c ∈ d.inertiaImage, PadicInt.toZModPow 2 ((chi c : ℤ_[2])) = 1) → Unramified)
    (hram : ¬ Unramified) :
    d.r = 0 ∨ (1 ≤ d.r ∧ ¬ Even S.eta) := by
  rcases Nat.eq_zero_or_pos d.r with h | h
  · exact Or.inl h
  · obtain ⟨ε, hεv⟩ := hε h
    exact Or.inr ⟨h, S.not_even_eta_of_not_unramified h ε hεv chi hproc bridge hram⟩

end MarkedSplitting

/-! ## Packet Cor. 8.2: the `ℚ₂(√-10)` parameters `(r, ε, η) = (1, 1, 1)`

Two arithmetic facts carry the corollary, and both are elementary:

* the type-`M₂` unit is `u = (1 - 2²)⁻¹ = (-3)⁻¹`, and `(-3)⁻¹ ≡ 5 (mod 8)`;
* `(-2)/5 = (-10)/5²`, so `-2/5` is a square in `K = ℚ₂(√-10)` and the unramified quadratic
  extension `K(√5)` is also `K(√-2)`, a subextension of the `2`-power cyclotomic tower.

The identification of the resulting marked datum with the branch row is the AS-lane's instance
work (it needs the norm computations of AX3 memo §5); what belongs here is the row itself and
the two computations. -/

section SqrtNegTen

/-- The type-`M₂` recipe `u = (1 - 2^α)⁻¹` at `α = 2` is `u = (-3)⁻¹`. -/
theorem one_sub_two_pow_two : (1 : ℤ_[2]) - 2 ^ 2 = -3 := by norm_num

/-- **Packet Cor. 8.2, first computation**: `u = (-3)⁻¹ ≡ 5 (mod 8)`.

Stated through the defining equation `u · (-3) = 1` rather than through an inverse, so that no
`ℤ_[2]`-invertibility API is needed; `PadicInt.toZModPow 3 : ℤ_[2] →+* ZMod 8` is the reduction
mod `8`. -/
theorem toZModPow_three_eq_five_of_inv_neg_three {u : ℤ_[2]} (hu : u * (-3) = 1) :
    PadicInt.toZModPow 3 u = 5 := by
  have h : PadicInt.toZModPow 3 u * (-3 : ZMod (2 ^ 3)) = 1 := by
    have h' := congrArg (PadicInt.toZModPow 3) hu
    rwa [map_mul, map_one, map_neg, map_ofNat] at h'
  revert h
  generalize PadicInt.toZModPow 3 u = x
  revert x
  decide

/-- The same computation in the `α`-spelling: `u · (1 - 2²) = 1` forces `u ≡ 5 (mod 8)`. -/
theorem toZModPow_three_eq_five_of_uM_two {u : ℤ_[2]} (hu : u * (1 - 2 ^ 2) = 1) :
    PadicInt.toZModPow 3 u = 5 :=
  toZModPow_three_eq_five_of_inv_neg_three (by rwa [one_sub_two_pow_two] at hu)

/-- `u ≡ 5 (mod 8)` is odd, so its marked value at level `r = 1` is `η = 1` — packet Cor. 8.2's
`η = 1`. -/
theorem toZModPow_one_eq_one_of_inv_neg_three {u : ℤ_[2]} (hu : u * (-3) = 1) :
    PadicInt.toZModPow 1 u = 1 := by
  have h : PadicInt.toZModPow 1 u * (-3 : ZMod (2 ^ 1)) = 1 := by
    have h' := congrArg (PadicInt.toZModPow 1) hu
    rwa [map_mul, map_one, map_neg, map_ofNat] at h'
  revert h
  generalize PadicInt.toZModPow 1 u = x
  revert x
  decide

/-- **Packet Cor. 8.2, second computation**: `(-2)/5 = (-10)/5²`.  Over any field in which `5`
is invertible, `-2/5` and `-10` differ by the square `(1/5)²`. -/
theorem neg_two_div_five_eq_neg_ten_div_sq {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) :
    (-2 : F) / 5 = (-10 : F) / 5 ^ 2 := by
  field_simp
  ring

/-- Consequently `-2/5` is a square exactly when `-10` is: in `K = ℚ₂(√-10)` the unramified
quadratic extension `K(√5)` is also `K(√-2)`, a quadratic subextension of the `2`-power
cyclotomic tower (packet Cor. 8.2). -/
theorem isSquare_neg_two_div_five_iff {F : Type*} [Field F] (h5 : (5 : F) ≠ 0) :
    IsSquare ((-2 : F) / 5) ↔ IsSquare (-10 : F) := by
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨5 * c, ?_⟩
    have hc' : (-2 : F) = 5 * (c * c) := by
      field_simp at hc
      linear_combination hc
    linear_combination 5 * hc'
  · rintro ⟨c, hc⟩
    refine ⟨c / 5, ?_⟩
    field_simp
    linear_combination hc

/-- **Packet Cor. 8.2**: `ℚ₂(√-10)` is the procyclic `M₂` row with `(r, ε, η) = (1, 1, 1)`.

The draft's field-specific relative-norm word for this field survives only as a regression
target (F5), never as a specialization of the row packet §8 removed. -/
noncomputable def branchSqrtNegTen : BranchData := .Mpc 2 1 true 1

@[simp] theorem branchSqrtNegTen_labuteType : branchSqrtNegTen.labuteType = .M 2 := rfl
@[simp] theorem branchSqrtNegTen_level : branchSqrtNegTen.level = 1 := rfl
@[simp] theorem branchSqrtNegTen_eps : branchSqrtNegTen.eps = true := rfl
@[simp] theorem branchSqrtNegTen_eta : branchSqrtNegTen.eta? = some 1 := rfl
@[simp] theorem branchSqrtNegTen_sVal : branchSqrtNegTen.sVal = 2 := rfl
@[simp] theorem branchSqrtNegTen_pVal : branchSqrtNegTen.pVal = 1 := rfl

theorem branchSqrtNegTen_valid : branchSqrtNegTen.Valid := ⟨le_refl 2, le_refl 1⟩

theorem branchSqrtNegTen_isProcyclicRow : branchSqrtNegTen.IsProcyclicRow := le_refl 1

/-- `ℚ₂(√-10)` is a ramified quadratic field (`n = 2`, `f = 1`, `q_K = 2`), and the row is
degree-compatible with it. -/
theorem branchSqrtNegTen_compatible : Compatible paramsRamifiedQuadratic branchSqrtNegTen :=
  compatible_of_isEven rfl (by decide)

/-- The row's marked value: `etaUnit 1 1 = 1`, i.e. `λ(u) = 1 ∈ ℤ/2` — packet Cor. 8.2's `η = 1`
in the spelling the datum uses. -/
theorem etaUnit_one_branchSqrtNegTen :
    ((etaUnit 1 (1 : ℤ_[2]ˣ) : (ZMod (2 ^ 1))ˣ) : ZMod (2 ^ 1)) = 1 := by
  rw [etaUnit, map_one]
  rfl

end SqrtNegTen

/-! ## Exhaustiveness of the five rows

F1's `BranchData` has five constructors; packet Prop. 8.1 says that this is the complete list
for ramified `i`.  The Lean content is (i) the case analysis `branchData_five_rows`, (ii) the
three realizability lemmas, which show that *every* admissible parameter tuple is on a row —
in particular both values of `ε` on the procyclic `M` row (`eps_both_occur`; draft §7.3's
`ℚ₂(√10)` has `B = x₁`, i.e. `p = 0`, i.e. `ε = false`, while packet Cor. 8.2's `ℚ₂(√-10)` has
`ε = true`) — and (iii) `MarkedSplitting.level_zero_or_not_even_eta` above, which says a
ramified-`i` marked datum lands on one of them. -/

section Exhaustiveness

/-- The branch datum has exactly the five rows of plan §1. -/
theorem branchData_five_rows (B : BranchData) :
    B = .L ∨ (∃ α, B = .N0 α) ∨ (∃ α r η, B = .Npc α r η) ∨ (∃ α, B = .M0 α) ∨
      (∃ α r ε η, B = .Mpc α r ε η) := by
  cases B with
  | L => exact Or.inl rfl
  | N0 α => exact Or.inr (Or.inl ⟨α, rfl⟩)
  | Npc α r η => exact Or.inr (Or.inr (Or.inl ⟨α, r, η, rfl⟩))
  | M0 α => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨α, rfl⟩)))
  | Mpc α r ε η => exact Or.inr (Or.inr (Or.inr (Or.inr ⟨α, r, ε, η, rfl⟩)))

/-- **Type `M` is covered for every `(α, r, ε, η)`**: the compact row at `r = 0` and the
procyclic row at `r ≥ 1`, with *both* sign values `ε` and every Frobenius unit `η : ℤ_[2]ˣ`
(which is automatically odd, F1's `toZMod_units_eq_one`).  No further row is needed — packet
Prop. 8.1. -/
theorem exists_M_row (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (ε : Bool) (η : ℤ_[2]ˣ) :
    ∃ B : BranchData, B.Valid ∧ B.labuteType = .M α ∧ B.level = r ∧
      (1 ≤ r → B.eps = ε ∧ B.eta? = some η) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨.M0 α, hα, rfl, rfl, fun h => absurd h (by omega)⟩
  · exact ⟨.Mpc α r ε η, ⟨hα, hr⟩, rfl, rfl, fun _ => ⟨rfl, rfl⟩⟩

/-- Type `N` is covered for every `(α, r, η)` (the `N` rows carry no sign parameter). -/
theorem exists_N_row (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (η : ℤ_[2]ˣ) :
    ∃ B : BranchData, B.Valid ∧ B.labuteType = .N α ∧ B.level = r ∧
      (1 ≤ r → B.eta? = some η) := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact ⟨.N0 α, hα, rfl, rfl, fun h => absurd h (by omega)⟩
  · exact ⟨.Npc α r η, ⟨hα, hr⟩, rfl, rfl, fun _ => rfl⟩

/-- Type `L` is the single row `r = 0`, `I = C` (draft §2.2). -/
theorem exists_L_row : ∃ B : BranchData, B.Valid ∧ B.labuteType = .L ∧ B.level = 0 :=
  ⟨.L, trivial, rfl, rfl⟩

/-- **Both sign values occur on the procyclic `M` row** (F1's discovery): draft §7.3's
`ℚ₂(√10)` has `B = x₁`, i.e. `p = 0`, i.e. `ε = false`, while packet Cor. 8.2's `ℚ₂(√-10)` has
`ε = true`.  An exhaustiveness statement that fixed `ε` would therefore be wrong. -/
theorem eps_both_occur :
    ∃ B₁ B₂ : BranchData, B₁.Valid ∧ B₂.Valid ∧ B₁.labuteType = B₂.labuteType ∧
      B₁.level = B₂.level ∧ B₁.eps = false ∧ B₂.eps = true ∧ B₁.pVal = 0 ∧ B₂.pVal = 1 :=
  ⟨.Mpc 2 1 false 1, .Mpc 2 1 true 1, ⟨le_refl 2, le_refl 1⟩, ⟨le_refl 2, le_refl 1⟩,
    rfl, rfl, rfl, rfl, rfl, rfl⟩

end Exhaustiveness

/-! ## Regression: the synthetic `r = 2` mock bundle

**Mandated by AX3 memo §7 R2.**  All five quadratic instances have `r ≤ 1`, where the λ-sign is
invisible: `ℤ/2` has no signs, and `λ(-1) = ε·2^{r-1}` is two-torsion, hence sign-blind at every
level (`2 = -2` in `ℤ/4`).  The λ-value that *does* carry a sign is `η = λ(u)`, and the smallest
level where `1 ≠ -1` is `r = 2`.  The mock datum below is the smallest one that exercises it:

`C = ℤ/2 × ℤ/4` written multiplicatively, `λ(a, b) = 2a + b`, `-1 = (1, 0)`, `u = (0, 1)`.
Then `r = 2`, `λ(-1) = 2 = ε·2^{r-1}` with `ε = 1`, and `η = λ(u) = 1`.

The sign-bearing pins are `mock_isEtaFor_one` / `mock_not_isEtaFor_neg_one` (the `η` adapter:
`1 ≠ 3` in `ℤ/4`), their swap on `u⁻¹` (`mock_isEtaFor_inv_neg_one` /
`mock_not_isEtaFor_inv_one`, which shows the test discriminates rather than failing both ways),
and `mock_gammaCoset` (the Frobenius coset: geometric `+1`, not arithmetic `-1` — AX3 memo
§7 R1).  `mock_even_eta_absurd` runs packet Prop. 8.1 itself at `r = 2`.  Note that `λ(-1)` is
two-torsion, hence sign-blind at *every* level (`2 = -2` in `ℤ/4`), so `ε` cannot be pinned this
way — that is a fact about `ε`, not a gap in the regression.

The section doubles as the **non-vacuity witness** for the two interfaces of this file: it
constructs a `CyclotomicFrobeniusDatum` and a `MarkedSplitting` outright, so neither structure
can be silently unsatisfiable (the failure mode of AX3 memo §7 R8). -/

section MockBundle

/-- The mock carrier `C = ℤ/2 × ℤ/4`, written multiplicatively. -/
abbrev MockC : Type := Multiplicative (ZMod 2 × ZMod 4)

/-- The mock marked quotient `λ(a, b) = 2a + b : ℤ/4`, additively. -/
def mockLambdaAdd : (ZMod 2 × ZMod 4) →+ ZMod (2 ^ 2) where
  toFun p := 2 * (p.1.val : ZMod 4) + p.2
  map_zero' := by decide
  map_add' := by decide

/-- The synthetic level-`2` datum. -/
def mockDatum : CyclotomicFrobeniusDatum MockC where
  r := 2
  lambda := AddMonoidHom.toMultiplicative mockLambdaAdd
  lambda_surjective := fun z => ⟨Multiplicative.ofAdd (0, Multiplicative.toAdd z), by
    show Multiplicative.ofAdd (mockLambdaAdd _) = z
    simp [mockLambdaAdd]⟩

/-- The first-coordinate projection, whose kernel is the mock procyclic factor. -/
def mockFst : MockC →* Multiplicative (ZMod 2) :=
  AddMonoidHom.toMultiplicative (AddMonoidHom.fst (ZMod 2) (ZMod 4))

/-- The mock marked splitting `C = ⟨-1⟩ × ⟨u⟩` with `-1 = (1, 0)` and `u = (0, 1)`. -/
def mockSplitting : MarkedSplitting mockDatum where
  negOne := Multiplicative.ofAdd (1, 0)
  u := Multiplicative.ofAdd (0, 1)
  procyclic := mockFst.ker
  negOne_sq := by decide
  u_mem := by decide
  lambdaAdd_procyclic := by
    intro w hw
    have hw0 : (Multiplicative.toAdd w).1 = 0 := congrArg Multiplicative.toAdd hw
    have hcast : ∀ b : ZMod 4, ((b.val : ℤ) : ZMod (2 ^ 2)) = b := by decide
    have hu : mockDatum.lambdaAdd (Multiplicative.ofAdd ((0 : ZMod 2), (1 : ZMod 4))) = 1 := by
      decide
    have hwv : mockDatum.lambdaAdd w = (Multiplicative.toAdd w).2 := by
      show mockLambdaAdd (Multiplicative.toAdd w) = _
      simp [mockLambdaAdd, hw0]
    refine ⟨((Multiplicative.toAdd w).2.val : ℤ), ?_⟩
    rw [hwv, hu, zsmul_eq_mul, mul_one]
    exact (hcast _).symm
  exists_decomp := by
    intro c
    refine ⟨Multiplicative.ofAdd (0, (Multiplicative.toAdd c).2), ?_, ?_⟩
    · show Multiplicative.ofAdd (0 : ZMod 2) = 1
      rfl
    · revert c
      decide

/-- `λ(-1) = 2 = ε·2^{r-1}` with `ε = 1` and `r = 2`. -/
theorem mock_negOneVal : mockSplitting.negOneVal = ((epsVal true * 2 ^ (2 - 1) : ℕ) : ZMod 4) := by
  decide

/-- `η = λ(u) = 1`.  **This is the sign-bearing value**: at `r = 2` the wrong sign would be
`3 = -1`, and `mock_not_isEtaFor_neg_one` rejects it. -/
theorem mock_eta : mockSplitting.eta = 1 := by decide

/-- `η = 1` represents `λ(u)` — the `η` adapter with the correct sign. -/
theorem mock_isEtaFor_one : IsEtaFor mockDatum mockSplitting.u 1 := by
  show mockSplitting.eta = _
  rw [mock_eta, etaUnit, map_one]
  rfl

/-- `η = -1` does **not** represent `λ(u)`: `1 ≠ 3` in `ℤ/4`.  A sign flip anywhere in the
`etaUnit` ↔ λ-target adapter (or in the value pipeline that feeds it) fails here, and at
`r ≤ 1` — every quadratic instance — it would not. -/
theorem mock_not_isEtaFor_neg_one : ¬ IsEtaFor mockDatum mockSplitting.u (-1) := by
  rw [IsEtaFor, etaUnit_coe]
  show mockSplitting.eta ≠ _
  rw [mock_eta, Units.val_neg, Units.val_one, map_neg, map_one]
  decide

/-- `λ(u⁻¹) = 3 = -1`: the inverse element is where `η = -1` *is* the representative. -/
theorem mock_lambdaAdd_inv_u : mockDatum.lambdaAdd mockSplitting.u⁻¹ = 3 := by
  rw [mockDatum.lambdaAdd_inv, show mockDatum.lambdaAdd mockSplitting.u = 1 from mock_eta]
  decide

/-- The two `η` pins above are a genuine **discriminator**, not a pair of vacuous failures: on
`u⁻¹` the verdicts swap.  So a pipeline that inverted `u` (or flipped the `ν`-sign feeding `λ`)
anywhere between the field computation and the branch row is caught at `r = 2`. -/
theorem mock_isEtaFor_inv_neg_one : IsEtaFor mockDatum mockSplitting.u⁻¹ (-1) := by
  rw [IsEtaFor, etaUnit_coe, mock_lambdaAdd_inv_u, Units.val_neg, Units.val_one, map_neg,
    map_one]
  decide

theorem mock_not_isEtaFor_inv_one : ¬ IsEtaFor mockDatum mockSplitting.u⁻¹ 1 := by
  rw [IsEtaFor, etaUnit_coe, mock_lambdaAdd_inv_u, Units.val_one, map_one]
  decide

/-- The Frobenius coset is the coset of `u`, whose λ-value is `+1`: geometric normalization.
At `r = 2` the arithmetic convention would give `-1 = 3` and this pin would fail
(AX3 memo §7 R1). -/
theorem mock_gammaCoset :
    mockDatum.gammaCoset = (QuotientGroup.mk mockSplitting.u : MockC ⧸ mockDatum.inertiaImage) :=
  (mockDatum.mk_eq_gammaCoset_iff.2 mock_eta).symm

/-- `η` is odd, so the mock row is a genuine procyclic row. -/
theorem mock_not_even_eta : ¬ Even mockSplitting.eta := by
  rw [mock_eta]
  rintro ⟨y, hy⟩
  revert y
  decide

/-- **Packet Prop. 8.1 at `r = 2`.**  If the mock datum's `η` were even, the classification
would force `r = 1`, contradicting `r = 2`.  The proof runs the real theorem, so a parity or
sign error in `level_eq_one_of_even_of_spanning` fails here. -/
theorem mock_even_eta_absurd (h : Even mockSplitting.eta) : False := by
  have := mockSplitting.level_eq_one_of_even (by decide) true mock_negOneVal h
  exact absurd this (by decide)

end MockBundle

end GQ2.Dyadic
