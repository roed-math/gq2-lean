/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Parameters
public import GQ2.Zhat

@[expose] public section

/-!
# Dyadic campaign, layer F2 (syntax): the reflected word type `PWord`

The word-level backbone of the general-`2`-adic campaign (plan §3, decision **A1**): a single
reflected syntax for the relator words, mirroring the frozen Python grammar of the presentation
*simplification* campaign (`dyadic_search/words/ast.py`, ticket S1.1) constructor-for-constructor
on the shared node set, so that the two sides can be compared and generated from one expression
tree.

## The grammar

`PWord Gen` has exactly the constructors of plan §3 A1:

```
one | gen | mul | inv | conj | comm | zpow (ℤ) | z2pow (ℤ_[2]) | profPow (ℤ̂)
```

Correspondence with the Python grammar (`ast.py`, "Constructors (exactly campaign doc
section 5)"):

* `Identity()` ↦ `PWord.one`; `Inverse(w)` ↦ `PWord.inv`.
* `Generator(name)` ↦ `PWord.gen g`: Python's generator *names* become the *semantic* alphabet
  `Generator n` of `GQ2/Dyadic/Parameters.lean`.
* `Multiply(children)` ↦ `PWord.mul`, binary; the `n`-ary Python product is `PWord.prodList`.
* `IntegerPower(w, e)` ↦ `PWord.zpow w k`.  Python's `e` may be symbolic, but "concrete finite
  backends must only ever receive fully evaluated ints", so the Lean exponent is a plain `ℤ`.
* `ZhatPower(w, spec)` ↦ `PWord.profPow w γ`: the three Python specs `Int n` / `Omega2` /
  `EtaHat` are the `ℤ̂`-elements `Zhat.ofInt n`, `GQ2.omega2` and `etaHatZ`.
* `Omega2Power(w)` ↦ `PWord.omega2Pow w`, *sugar* for `profPow w omega2` — matching Python's
  "semantically equal to `ZhatPower(word, Omega2())`".
* `Conjugate(w, g)` ↦ `PWord.conj w g` (`w^g = g⁻¹ w g`);
  `Commutator(x, y)` ↦ `PWord.comm x y` (`[x,y] = x⁻¹y⁻¹xy`).
* `OrbitNorm`, `HyperbolicHandles`: **no constructor** — S1.9 landed these as group-level blocks
  (`GQ2/Dyadic/Word/Blocks.lean`: `orbitNorm`, `handlesProd`).
* `Shadow`: **no constructor**, semantics owned by S4.2.  `Auxiliary`: **no constructor**, a
  display/sharing device rather than a group operation.
* `PWord.z2pow w z` is Lean-only, per packet Rem. 2.3 ("a word syntax should distinguish
  integral powers, `ℤ₂`-powers, and `ℤ̂`-powers").

`x^{-g}` is **sugar** (`PWord.invConj`), never an exponent — packet Rem. 2.3 is explicit that it
must not be parsed as a `-g` exponent.

## `2`-adic exponents

`GQ2/Zhat.lean` provides `ℤ̂` and its idempotent `ω₂` but no ring structure, so the profinite
exponent `η̂` of the branch words ("let `η̂ ∈ ℤ̂ˣ` have `2`-component `η` and odd-primary
components `1`", draft §5.2/§5.3) is not available from that API alone.  This file builds it:

* `padicOmega2Exp z N` — the integer representative modulo `N` of the profinite exponent `z·ω₂`;
* `padicOmega2 : ℤ_[2] → ℤ̂` — `z ↦ z·ω₂`, the canonical splitting `ℤ₂ ↪ ℤ̂` of the projection,
  built as a compatible family exactly like `GQ2.omega2` (its congruence is
  `padicOmega2Exp_modEq`, the `ω₂` argument of `GQ2.omega2Exp_modEq` with a `2`-adic factor);
* `etaHatZ η = 1 + (η − 1)·ω₂` — the `ℤ̂`-element with `2`-component `η` and odd components `1`;
* `zpowHat_padicOmega2` / `zpowHat_etaHatZ` — their finite evaluations (packet Lem. 2.2).

`EtaData` is the *syntactic* `(num, den)` pair of the Python `EtaHat` node, with
`canonicalEtaHat` reproducing the ticket-S1.M constructor-level canonicalization (`den > 0`,
gcd-reduced) so that printed Lean terms and Python content hashes agree.

## Specializations

`killWild` (Gate B step 0) and `pro2` (Gate C) are the two boundary substitutions of
`dyadic_search/semantics/specialization.py`, transcribed as syntactic transformations.  Their
*soundness* lemmas — evaluating the substituted word equals evaluating in the specialized
marking — live in `GQ2/Dyadic/Word/Eval.lean` together with the semantic content of Gate B's
rules T1/T2.

## Implementation notes

This file is `module`-style: both of its in-repo imports (`GQ2.Dyadic.Parameters`, `GQ2.Zhat`)
are `module`-style, so the one-directional rule of plan §3 A5 is satisfied.
-/

namespace GQ2.Dyadic

/-! ## The `2`-adic exponent embedding `ℤ₂ ↪ ℤ̂` -/

section PadicExponent

open PadicInt

/-- The integer representative modulo `N` of the profinite exponent `z · ω₂` for `z : ℤ₂`:
the unique residue that is `≡ z` on the `2`-part of `N` and `≡ 0` on its odd part.

This is `GQ2.omega2Exp` scaled by (a lift of) `z`: `ω₂` is `≡ 1` on the `2`-part and `≡ 0` on the
odd part, so multiplying by an integer congruent to `z` modulo `2^{v₂ N}` produces exactly the
required residue, and only the `2`-part of the lift matters. -/
noncomputable def padicOmega2Exp (z : ℤ_[2]) (N : ℕ) : ℕ :=
  (toZModPow (N.factorization 2) z).val * omega2Exp N

/-- The `2`-adic lift used by `padicOmega2Exp` is coherent across levels. -/
private theorem val_toZModPow_modEq {α β : ℕ} (h : α ≤ β) (z : ℤ_[2]) :
    (toZModPow β z).val ≡ (toZModPow α z).val [MOD 2 ^ α] := by
  rw [← ZMod.natCast_eq_natCast_iff, ZMod.natCast_zmod_val, ZMod.natCast_val]
  have := congrArg (fun f => (f : ℤ_[2] →+* ZMod (2 ^ α)) z)
    (zmod_cast_comp_toZModPow (p := 2) α β h)
  simpa [ZMod.castHom_apply] using this

/-- **Compatibility of the `z·ω₂` exponents across levels** — the exact analogue of
`GQ2.omega2Exp_modEq`, and what makes `padicOmega2` a well-defined element of `ℤ̂`. -/
theorem padicOmega2Exp_modEq {N M : ℕ} (hdvd : N ∣ M) (hM : M ≠ 0) (z : ℤ_[2]) :
    padicOmega2Exp z M ≡ padicOmega2Exp z N [MOD N] := by
  have hN : N ≠ 0 := ne_zero_of_dvd_ne_zero hM hdvd
  have hle : N.factorization 2 ≤ M.factorization 2 :=
    (Nat.factorization_le_iff_dvd hN hM).mpr hdvd 2
  -- Congruent modulo the `2`-part `2 ^ v₂(N)`: there `ω₂ ≡ 1` at both levels.
  have h2 : padicOmega2Exp z M ≡ padicOmega2Exp z N [MOD 2 ^ N.factorization 2] := by
    by_cases hα : N.factorization 2 = 0
    · rw [hα, pow_zero]; exact Nat.modEq_one
    · have hoM : omega2Exp M ≡ 1 [MOD 2 ^ N.factorization 2] :=
        (omega2Exp_modEq_one hM (by lia)).of_dvd (pow_dvd_pow 2 hle)
      have hoN : omega2Exp N ≡ 1 [MOD 2 ^ N.factorization 2] := omega2Exp_modEq_one hN hα
      calc padicOmega2Exp z M
          ≡ (toZModPow (N.factorization 2) z).val * 1 [MOD 2 ^ N.factorization 2] :=
            Nat.ModEq.mul (val_toZModPow_modEq hle z) hoM
        _ ≡ (toZModPow (N.factorization 2) z).val * omega2Exp N [MOD 2 ^ N.factorization 2] :=
            Nat.ModEq.mul_left _ hoN.symm
  -- Congruent modulo the odd part `N / 2 ^ v₂(N)`: there both sides are `≡ 0`.
  have hodd : padicOmega2Exp z M ≡ padicOmega2Exp z N [MOD N / 2 ^ N.factorization 2] := by
    have e1 : (N / 2 ^ N.factorization 2) ∣ padicOmega2Exp z N :=
      Dvd.dvd.mul_left (oddPart_dvd_omega2Exp N) _
    have e2 : (N / 2 ^ N.factorization 2) ∣ padicOmega2Exp z M :=
      Dvd.dvd.mul_left
        ((Nat.ordCompl_dvd_ordCompl_of_dvd hdvd 2).trans (oddPart_dvd_omega2Exp M)) _
    exact (Nat.modEq_zero_iff_dvd.mpr e2).trans (Nat.modEq_zero_iff_dvd.mpr e1).symm
  -- CRT over the coprime factorisation `N = 2^{v₂ N} · (N / 2^{v₂ N})`.
  have hcop : Nat.Coprime (2 ^ N.factorization 2) (N / 2 ^ N.factorization 2) :=
    Nat.Coprime.pow_left _
      ((Nat.prime_two.coprime_iff_not_dvd).mpr (Nat.not_dvd_ordCompl Nat.prime_two hN))
  have hcrt := (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp ⟨h2, hodd⟩
  rwa [Nat.ordProj_mul_ordCompl_eq_self N 2] at hcrt

/-- `1 · ω₂ = ω₂`: the embedding is normalized so that the `2`-adic unit `1` recovers the
idempotent of `GQ2/Zhat.lean`. -/
theorem padicOmega2Exp_one (N : ℕ) : padicOmega2Exp 1 N = omega2Exp N := by
  unfold padicOmega2Exp
  by_cases hα : N.factorization 2 = 0
  · have : omega2Exp N = 0 := by simp [omega2Exp, hα]
    simp [this]
  · have h1 : (1 : ℕ) < 2 ^ N.factorization 2 :=
      Nat.one_lt_two_pow_iff.mpr hα
    rw [map_one, ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt h1, one_mul]

/-- **The canonical splitting `ℤ₂ ↪ ℤ̂`**, `z ↦ z·ω₂`: the element of `ℤ̂` whose `2`-component is
`z` and whose odd-primary components vanish.  Constructed componentwise from `padicOmega2Exp`,
exactly as `GQ2.omega2 = padicOmega2 1` is constructed from `GQ2.omega2Exp`; compatibility of the
family is `padicOmega2Exp_modEq`. -/
noncomputable def padicOmega2 (z : ℤ_[2]) : Zhat :=
  ⟨fun H => QuotientGroup.mk (Multiplicative.ofAdd (padicOmega2Exp z H.toSubgroup.index : ℤ)),
   fun H K π => by
    show QuotientGroup.map H.toSubgroup K.toSubgroup (MonoidHom.id _) π.le
        (QuotientGroup.mk (Multiplicative.ofAdd (padicOmega2Exp z H.toSubgroup.index : ℤ)))
      = QuotientGroup.mk (Multiplicative.ofAdd (padicOmega2Exp z K.toSubgroup.index : ℤ))
    rw [QuotientGroup.map_mk, MonoidHom.id_apply]
    exact mk_ofAdd_eq_mk_ofAdd_iff.mpr
      ((padicOmega2Exp_modEq (Subgroup.index_dvd_of_le π.le)
        Subgroup.FiniteIndex.index_ne_zero z).dvd)⟩

/-- The zero `2`-adic exponent embeds as the zero exponent in `Zhat` (whose multiplicative
identity represents additive zero). -/
@[simp] theorem padicOmega2_zero : padicOmega2 (0 : ℤ_[2]) = 1 := by
  apply Subtype.ext
  funext H
  simp [padicOmega2, padicOmega2Exp]
  rfl

section Eval

variable {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **Finite evaluation of a `2`-adic exponent** (packet Lem. 2.2 for `z·ω₂`): in a finite
(discrete) group, `x ^ᶻ (z·ω₂) = x ^ padicOmega2Exp z (orderOf x)`.  Same proof shape as
`GQ2.zpowHat_omega2`. -/
theorem zpowHat_padicOmega2 (z : ℤ_[2]) (x : P) :
    x ^ᶻ padicOmega2 z = x ^ padicOmega2Exp z (orderOf x) := by
  have hU : IsOpen ((x ^ᶻ ·) ⁻¹' {x ^ᶻ padicOmega2 z}) :=
    (continuous_zpowHat x).isOpen_preimage _ (isOpen_discrete _)
  have hmem : padicOmega2 z ∈ (x ^ᶻ ·) ⁻¹' {x ^ᶻ padicOmega2 z} := rfl
  obtain ⟨H₀, hH₀⟩ := completion_exists_level hU hmem
  have hN₀ : H₀.toSubgroup.index ≠ 0 := Subgroup.FiniteIndex.index_ne_zero
  have hord : orderOf x ≠ 0 := (orderOf_pos x).ne'
  have hM : Nat.lcm H₀.toSubgroup.index (orderOf x) ≠ 0 := Nat.lcm_ne_zero hN₀ hord
  have hcomp : (Zhat.ofInt (padicOmega2Exp z (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ)).1 H₀
      = (padicOmega2 z).1 H₀ := by
    show ((Multiplicative.ofAdd
        (padicOmega2Exp z (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ) :
        Multiplicative ℤ) : Multiplicative ℤ ⧸ H₀.toSubgroup)
      = ((Multiplicative.ofAdd (padicOmega2Exp z H₀.toSubgroup.index : ℤ) :
        Multiplicative ℤ) : Multiplicative ℤ ⧸ H₀.toSubgroup)
    rw [mk_ofAdd_eq_mk_ofAdd_iff]
    exact (padicOmega2Exp_modEq (Nat.dvd_lcm_left _ _) hM z).dvd
  have hev : x ^ᶻ Zhat.ofInt (padicOmega2Exp z (Nat.lcm H₀.toSubgroup.index (orderOf x)) : ℤ)
      = x ^ᶻ padicOmega2 z := hH₀ _ hcomp
  rw [zpowHat_ofInt, zpow_natCast,
    pow_eq_pow_iff_modEq.mpr (padicOmega2Exp_modEq (Nat.dvd_lcm_right _ _) hM z)] at hev
  exact hev.symm

/-- The embedding is normalized: at `z = 1` it computes the `ω₂`-power. -/
theorem zpowHat_padicOmega2_one (x : P) : x ^ᶻ padicOmega2 1 = x ^ᶻ omega2 := by
  rw [zpowHat_padicOmega2, padicOmega2Exp_one, zpowHat_omega2, powOmega2]

/-- `padicOmega2` kills pro-odd elements: if `orderOf x` is odd then `x ^ᶻ (z·ω₂) = 1`.  This is
the semantic core of Gate B's rule **T1** for `ℤ₂`-exponents. -/
theorem zpowHat_padicOmega2_eq_one_of_odd {z : ℤ_[2]} {x : P} (h : Odd (orderOf x)) :
    x ^ᶻ padicOmega2 z = 1 := by
  have hfac : (orderOf x).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using h)
  have : omega2Exp (orderOf x) = 0 := by simp [omega2Exp, hfac]
  rw [zpowHat_padicOmega2, padicOmega2Exp, this, Nat.mul_zero, pow_zero]

end Eval

/-! ### `η̂`: the `ℤ̂`-exponent with `2`-component `η` and odd components `1` -/

/-- **`η̂ ∈ ℤ̂`**: the profinite exponent with `2`-component `η` and *all* odd-primary components
equal to `1` (draft §5.2/§5.3; Python `EtaHat`).  Written additively, `η̂ = 1 + (η − 1)·ω₂`:
on the `2`-part `ω₂ ≡ 1` so the value is `η`, on every odd part `ω₂ ≡ 0` so the value is `1`. -/
noncomputable def etaHatZ (η : ℤ_[2]) : Zhat := Zhat.ofInt 1 * padicOmega2 (η - 1)

/-- The profinite lift of the `2`-adic unit `1` is the ordinary exponent `1`. -/
@[simp] theorem etaHatZ_one : etaHatZ (1 : ℤ_[2]) = Zhat.ofInt 1 := by
  rw [etaHatZ, sub_self, padicOmega2_zero, mul_one]

section EtaEval

variable {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **Finite evaluation of `η̂`** (packet Lem. 2.2). -/
theorem zpowHat_etaHatZ (η : ℤ_[2]) (x : P) :
    x ^ᶻ etaHatZ η = x * x ^ padicOmega2Exp (η - 1) (orderOf x) := by
  rw [etaHatZ, zpowHat_mul, zpowHat_padicOmega2, zpowHat_ofInt, zpow_one]

/-- **Gate B, rule T2**: `η̂` acts as the identity on pro-odd elements — "`η̂` does *not* kill
tau-words" (`specialization.py`, rule T2), it fixes them.  Only `ω₂` kills. -/
theorem zpowHat_etaHatZ_of_odd {η : ℤ_[2]} {x : P} (h : Odd (orderOf x)) :
    x ^ᶻ etaHatZ η = x := by
  rw [etaHatZ, zpowHat_mul, zpowHat_padicOmega2_eq_one_of_odd h, zpowHat_ofInt, zpow_one, mul_one]

end EtaEval

end PadicExponent

/-! ## The syntactic `η̂` datum and its canonical form -/

/-- The syntactic data of a Python `EtaHat(num, den)` node: the pair of (intended odd) integers
with `η = num · den⁻¹` read `2`-adically.  Kept as raw integers — oddness is a side condition
of the *use*, exactly as `LabuteType.Valid` is a predicate rather than a constructor argument
(`GQ2/Dyadic/Parameters.lean`). -/
structure EtaData where
  /-- The numerator of `η = num / den`. -/
  num : ℤ
  /-- The denominator of `η = num / den`; odd, hence a `2`-adic unit. -/
  den : ℤ
  deriving DecidableEq, Repr

namespace EtaData

/-- The canonical form of a Python `EtaHat` pair since ticket S1.M: positive denominator,
gcd-reduced. -/
def IsCanonical (e : EtaData) : Prop := 0 < e.den ∧ Int.gcd e.num e.den = 1

instance (e : EtaData) : Decidable e.IsCanonical := by unfold IsCanonical; infer_instance

/-- Divide both entries of the pair `(a, b)` by `gcd(a, b)` — the reduction half of the S1.M
canonicalization. -/
def reduce (a b : ℤ) : EtaData := ⟨a / (Int.gcd a b : ℤ), b / (Int.gcd a b : ℤ)⟩

/-- The `2`-adic unit denoted by an `EtaData` pair, `η = num · den⁻¹`. -/
noncomputable def toPadic (e : EtaData) : ℤ_[2] := (e.num : ℤ_[2]) * PadicInt.inv (e.den : ℤ_[2])

/-- The canonical syntactic pair `<1,1>` denotes the `2`-adic unit `1`. -/
@[simp] theorem one_toPadic : (EtaData.mk 1 1).toPadic = 1 := by
  rw [toPadic]
  have hinv : PadicInt.inv (1 : ℤ_[2]) = 1 := by
    simpa using PadicInt.mul_inv (z := (1 : ℤ_[2])) (norm_one : ‖(1 : ℤ_[2])‖ = 1)
  simp only [Int.cast_one, hinv, mul_one]

/-- The `ℤ̂`-exponent denoted by an `EtaData` pair. -/
noncomputable def toZhat (e : EtaData) : Zhat := etaHatZ e.toPadic

/-- The canonical syntactic pair `<1,1>` denotes the ordinary profinite exponent `1`. -/
@[simp] theorem one_toZhat : (EtaData.mk 1 1).toZhat = Zhat.ofInt 1 := by
  rw [toZhat, one_toPadic, etaHatZ_one]

end EtaData

/-- **The S1.M canonicalization of a Python `EtaHat` pair**: make the denominator positive, then
divide out `gcd(|num|, den)`.  Byte-for-byte the normalization performed by
`dyadic_search.words.ast.EtaHat.__post_init__` (and by
`dyadic_search.semantics.specialization.canonical_etahat`), so Lean terms and Python content
hashes name the same representative.

The gcd of two odd integers is odd, hence a `2`-adic unit, so the denoted `2`-adic value is
unchanged (`canonicalEtaHat_cross`). -/
def canonicalEtaHat (e : EtaData) : EtaData :=
  if e.den < 0 then EtaData.reduce (-e.num) (-e.den) else EtaData.reduce e.num e.den

namespace EtaData

/-- Divide both entries of a pair by their gcd. -/
private theorem cross_of_dvd {a b g : ℤ} (hg : g ≠ 0) (ha : g ∣ a) (hb : g ∣ b) :
    a * (b / g) = (a / g) * b := by
  refine mul_right_cancel₀ hg ?_
  rw [mul_assoc, Int.ediv_mul_cancel hb, mul_right_comm, Int.ediv_mul_cancel ha]

private theorem reduce_den_pos {a b : ℤ} (h : 0 < b) : 0 < (reduce a b).den := by
  have hg : 0 < (Int.gcd a b : ℤ) := by
    refine Int.natCast_pos.mpr (Nat.pos_of_ne_zero fun hc => ?_)
    exact absurd (Int.gcd_eq_zero_iff.mp hc).2 h.ne'
  exact Int.ediv_pos_of_pos_of_dvd h hg.le (Int.gcd_dvd_right _ _)

private theorem reduce_gcd {a b : ℤ} (h : b ≠ 0) :
    Int.gcd (reduce a b).num (reduce a b).den = 1 :=
  Int.gcd_div_gcd_div_gcd (Nat.pos_of_ne_zero fun hc => h (Int.gcd_eq_zero_iff.mp hc).2)

private theorem reduce_cross (a b : ℤ) : a * (reduce a b).den = (reduce a b).num * b := by
  rcases eq_or_ne ((Int.gcd a b : ℤ)) 0 with hg | hg
  · have h := Int.gcd_eq_zero_iff.mp (Int.natCast_eq_zero.mp hg)
    simp [reduce, h.1, h.2]
  · exact cross_of_dvd hg (Int.gcd_dvd_left _ _) (Int.gcd_dvd_right _ _)

private theorem reduce_eq_self {a b : ℤ} (h : Int.gcd a b = 1) : reduce a b = ⟨a, b⟩ := by
  simp [reduce, h]

/-- The canonicalized denominator is positive (given `den ≠ 0`, which oddness supplies). -/
theorem canonicalEtaHat_den_pos {e : EtaData} (h : e.den ≠ 0) : 0 < (canonicalEtaHat e).den := by
  unfold canonicalEtaHat
  split
  · exact reduce_den_pos (by lia)
  · exact reduce_den_pos (by lia)

/-- The canonicalized pair is coprime (given `den ≠ 0`). -/
theorem canonicalEtaHat_gcd {e : EtaData} (h : e.den ≠ 0) :
    Int.gcd (canonicalEtaHat e).num (canonicalEtaHat e).den = 1 := by
  unfold canonicalEtaHat
  split
  · exact reduce_gcd (by lia)
  · exact reduce_gcd h

/-- The canonicalization output is canonical (given `den ≠ 0`). -/
theorem isCanonical_canonicalEtaHat {e : EtaData} (h : e.den ≠ 0) :
    (canonicalEtaHat e).IsCanonical :=
  ⟨canonicalEtaHat_den_pos h, canonicalEtaHat_gcd h⟩

/-- **The canonicalization preserves the denoted fraction**: `num · den' = num' · den`.  Together
with invertibility of the (odd) denominators this is the statement that `canonicalEtaHat` is a
no-op on `η`, i.e. that Python's constructor-level normalization is convention-independent. -/
theorem canonicalEtaHat_cross (e : EtaData) :
    e.num * (canonicalEtaHat e).den = (canonicalEtaHat e).num * e.den := by
  unfold canonicalEtaHat
  split
  · have := reduce_cross (-e.num) (-e.den)
    lia
  · exact reduce_cross e.num e.den

/-- A canonical pair is a fixed point of the canonicalization. -/
theorem canonicalEtaHat_eq_self {e : EtaData} (h : e.IsCanonical) : canonicalEtaHat e = e := by
  obtain ⟨hpos, hgcd⟩ := h
  rw [canonicalEtaHat, if_neg (not_lt.mpr hpos.le), reduce_eq_self hgcd]

/-- The canonicalization is idempotent (given `den ≠ 0`), as in Python. -/
theorem canonicalEtaHat_idem {e : EtaData} (h : e.den ≠ 0) :
    canonicalEtaHat (canonicalEtaHat e) = canonicalEtaHat e :=
  canonicalEtaHat_eq_self (isCanonical_canonicalEtaHat h)

/-- The cross-multiplication identity, read in `ℤ₂`. -/
theorem canonicalEtaHat_cross_padic (e : EtaData) :
    (e.num : ℤ_[2]) * ((canonicalEtaHat e).den : ℤ_[2])
      = ((canonicalEtaHat e).num : ℤ_[2]) * (e.den : ℤ_[2]) := by
  exact_mod_cast congrArg (fun k : ℤ => (k : ℤ_[2])) (canonicalEtaHat_cross e)

/-! ### Oddness, units, and invariance of the denoted `2`-adic unit -/

private theorem odd_ediv_of_odd {a g : ℤ} (hg : g ∣ a) (ha : Odd a) : Odd (a / g) := by
  obtain ⟨p, hp⟩ := hg
  have hg0 : g ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hp
    rw [hp, Int.odd_iff] at ha
    lia
  have hpodd : Odd p := by
    rcases Int.even_or_odd p with he | ho
    · refine absurd ha ?_
      rw [Int.not_odd_iff_even, hp]
      exact he.mul_left g
    · exact ho
  rwa [hp, Int.mul_ediv_cancel_left _ hg0]

/-- Canonicalization preserves oddness of the numerator ("negation and division by an odd
divisor preserve oddness", `ast.py`). -/
theorem canonicalEtaHat_odd_num {e : EtaData} (hn : Odd e.num) : Odd (canonicalEtaHat e).num := by
  unfold canonicalEtaHat
  split
  · exact odd_ediv_of_odd (Int.gcd_dvd_left _ _) hn.neg
  · exact odd_ediv_of_odd (Int.gcd_dvd_left _ _) hn

/-- Canonicalization preserves oddness of the denominator, so the canonical denominator is again
a `2`-adic unit. -/
theorem canonicalEtaHat_odd_den {e : EtaData} (hd : Odd e.den) : Odd (canonicalEtaHat e).den := by
  unfold canonicalEtaHat
  split
  · exact odd_ediv_of_odd (Int.gcd_dvd_right _ _) hd.neg
  · exact odd_ediv_of_odd (Int.gcd_dvd_right _ _) hd

/-- An odd integer is a unit in `ℤ₂` — the typing fact behind the `EtaHat` grammar's
"`den` odd makes it a `2`-adic unit". -/
theorem isUnit_intCast_of_odd {k : ℤ} (h : Odd k) : IsUnit ((k : ℤ_[2])) := by
  rw [PadicInt.isUnit_iff]
  rcases lt_or_eq_of_le (PadicInt.norm_le_one ((k : ℤ_[2]))) with hlt | heq
  · obtain ⟨c, hc⟩ : ((2 : ℕ) : ℤ) ∣ k := (PadicInt.norm_int_lt_one_iff_dvd k).mp hlt
    obtain ⟨m, hm⟩ := h
    exfalso; lia
  · exact heq

private theorem inv_cancel_of_cross {a b a' b' : ℤ_[2]} (hb : b * PadicInt.inv b = 1)
    (hb' : b' * PadicInt.inv b' = 1) (h : a * b' = a' * b) :
    a' * PadicInt.inv b' = a * PadicInt.inv b := by
  have hbne : b * b' ≠ 0 := by
    intro hc
    rcases mul_eq_zero.mp hc with h0 | h0
    · rw [h0, zero_mul] at hb; exact zero_ne_one hb
    · rw [h0, zero_mul] at hb'; exact zero_ne_one hb'
  refine mul_right_cancel₀ hbne ?_
  calc a' * PadicInt.inv b' * (b * b')
      = a' * b * (b' * PadicInt.inv b') := by ring
    _ = a * b' * (b' * PadicInt.inv b') := by rw [← h]
    _ = a * b' := by rw [hb', mul_one]
    _ = a * (b * PadicInt.inv b) * b' := by rw [hb, mul_one]
    _ = a * PadicInt.inv b * (b * b') := by ring

/-- **The canonicalization is a no-op on the denoted `2`-adic unit.**  Together with
`isCanonical_canonicalEtaHat` and `canonicalEtaHat_idem` this is the Lean side of ticket S1.M's
conclusion that "content hashes are convention-independent: how a caller spelled the fraction can
no longer change a word's identity". -/
theorem canonicalEtaHat_toPadic {e : EtaData} (hd : Odd e.den) :
    (canonicalEtaHat e).toPadic = e.toPadic :=
  inv_cancel_of_cross
    (PadicInt.mul_inv (PadicInt.isUnit_iff.mp (isUnit_intCast_of_odd hd)))
    (PadicInt.mul_inv (PadicInt.isUnit_iff.mp (isUnit_intCast_of_odd (canonicalEtaHat_odd_den hd))))
    (canonicalEtaHat_cross_padic e)

/-- Consequently the `ℤ̂`-exponent denoted by an `EtaData` pair is canonicalization-invariant. -/
theorem canonicalEtaHat_toZhat {e : EtaData} (hd : Odd e.den) :
    (canonicalEtaHat e).toZhat = e.toZhat := by
  rw [toZhat, toZhat, canonicalEtaHat_toPadic hd]

end EtaData

/-! ## The reflected word syntax -/

/-- **The reflected word syntax** of plan §3 A1 over an alphabet `Gen`.

`conj u g` is the paper's right conjugation `u^g = g⁻¹ u g` and `comm u v` the paper's commutator
`[u,v] = u⁻¹v⁻¹uv` (campaign §3, `GQ2/Dyadic/Word/Blocks.lean`); they are primitive constructors
rather than sugar because the Fox/Stokes/Hessian evaluators of the `WW` lane read them
structurally.

The three exponent constructors are kept apart on purpose (packet Rem. 2.3): `zpow` for genuine
integers, `z2pow` for `ℤ₂`-exponents, `profPow` for `ℤ̂`-exponents.  There is deliberately **no**
`x^{-g}` constructor — see `PWord.invConj`. -/
inductive PWord (Gen : Type*) where
  /-- The empty word. -/
  | one : PWord Gen
  /-- A generator letter. -/
  | gen (g : Gen) : PWord Gen
  /-- An ordered product `u · v`. -/
  | mul (u v : PWord Gen) : PWord Gen
  /-- The inverse `u⁻¹`. -/
  | inv (u : PWord Gen) : PWord Gen
  /-- Right conjugation `u ^ g = g⁻¹ u g`. -/
  | conj (u g : PWord Gen) : PWord Gen
  /-- The commutator `[u, v] = u⁻¹ v⁻¹ u v`. -/
  | comm (u v : PWord Gen) : PWord Gen
  /-- An integer power `u ^ k`. -/
  | zpow (u : PWord Gen) (k : ℤ) : PWord Gen
  /-- A `2`-adic power `u ^ z` (interpreted through `padicOmega2`, i.e. on the `2`-primary
  part; on a pro-`2` element this is the honest `ℤ₂`-power). -/
  | z2pow (u : PWord Gen) (z : ℤ_[2]) : PWord Gen
  /-- A profinite power `u ^ γ`, `γ ∈ ℤ̂`. -/
  | profPow (u : PWord Gen) (γ : Zhat) : PWord Gen

namespace PWord

variable {Gen Gen' : Type*}

/-- **`x^{-g}` is sugar** — packet Rem. 2.3: "the expression `x^{-g}` should be a defined syntax
constructor or expanded to `(x⁻¹)^g`, **never** parsed as an exponent `-g`". -/
def invConj (u g : PWord Gen) : PWord Gen := .conj (.inv u) g

@[inherit_doc] scoped notation:max u " ^⁻ " g => PWord.invConj u g

/-- `u ^ ω₂`, the Python `Omega2Power` node ("semantically equal to `ZhatPower(word, Omega2())`;
normalization canonicalizes the latter to this node"). -/
noncomputable def omega2Pow (u : PWord Gen) : PWord Gen := .profPow u omega2

/-- `u ^ η̂` for a `2`-adic unit `η`: the Python `ZhatPower(w, EtaHat(...))` node. -/
noncomputable def etaPow (u : PWord Gen) (η : ℤ_[2]) : PWord Gen := .profPow u (etaHatZ η)

/-- The `n`-ary product of the Python `Multiply` node, folded to the right. -/
def prodList : List (PWord Gen) → PWord Gen
  | [] => .one
  | w :: ws => .mul w (prodList ws)

@[simp] theorem prodList_nil : prodList ([] : List (PWord Gen)) = .one := rfl

@[simp] theorem prodList_cons (w : PWord Gen) (ws : List (PWord Gen)) :
    prodList (w :: ws) = .mul w (prodList ws) := rfl

/-! ### Substitution -/

/-- Substitution of generators by words — the Lean form of
`dyadic_search.semantics.specialization.substitute_generators`.  Purely structural; profinite and
`ℤ₂` exponents ride along untouched. -/
def subst (f : Gen → PWord Gen') : PWord Gen → PWord Gen'
  | .one => .one
  | .gen g => f g
  | .mul u v => .mul (subst f u) (subst f v)
  | .inv u => .inv (subst f u)
  | .conj u g => .conj (subst f u) (subst f g)
  | .comm u v => .comm (subst f u) (subst f v)
  | .zpow u k => .zpow (subst f u) k
  | .z2pow u z => .z2pow (subst f u) z
  | .profPow u γ => .profPow (subst f u) γ

@[simp] theorem subst_one (f : Gen → PWord Gen') : subst f .one = .one := rfl
@[simp] theorem subst_gen (f : Gen → PWord Gen') (g : Gen) : subst f (.gen g) = f g := rfl
@[simp] theorem subst_mul (f : Gen → PWord Gen') (u v : PWord Gen) :
    subst f (.mul u v) = .mul (subst f u) (subst f v) := rfl
@[simp] theorem subst_inv (f : Gen → PWord Gen') (u : PWord Gen) :
    subst f (.inv u) = .inv (subst f u) := rfl
@[simp] theorem subst_conj (f : Gen → PWord Gen') (u g : PWord Gen) :
    subst f (.conj u g) = .conj (subst f u) (subst f g) := rfl
@[simp] theorem subst_comm (f : Gen → PWord Gen') (u v : PWord Gen) :
    subst f (.comm u v) = .comm (subst f u) (subst f v) := rfl
@[simp] theorem subst_zpow (f : Gen → PWord Gen') (u : PWord Gen) (k : ℤ) :
    subst f (.zpow u k) = .zpow (subst f u) k := rfl
@[simp] theorem subst_z2pow (f : Gen → PWord Gen') (u : PWord Gen) (z : ℤ_[2]) :
    subst f (.z2pow u z) = .z2pow (subst f u) z := rfl
@[simp] theorem subst_profPow (f : Gen → PWord Gen') (u : PWord Gen) (γ : Zhat) :
    subst f (.profPow u γ) = .profPow (subst f u) γ := rfl

/-! ### `ω₂`-only words -/

/-- `w` uses no `ℤ₂`-exponent and no profinite exponent other than `ω₂`.

This is the fragment on which the `ℕ`-exponent form of packet Lem. 2.2 is available with a single
global exponent — i.e. exactly the `wildValueExp`/`wildValueExpR` situation of the `ℚ₂`
development (`GQ2/FoxHeisenberg/Traced.lean`, `GQ2/Roe/Words.lean`). -/
def IsOmega2Only : PWord Gen → Prop
  | .one => True
  | .gen _ => True
  | .mul u v => IsOmega2Only u ∧ IsOmega2Only v
  | .inv u => IsOmega2Only u
  | .conj u g => IsOmega2Only u ∧ IsOmega2Only g
  | .comm u v => IsOmega2Only u ∧ IsOmega2Only v
  | .zpow u _ => IsOmega2Only u
  | .z2pow _ _ => False
  | .profPow u γ => γ = omega2 ∧ IsOmega2Only u

@[simp] theorem isOmega2Only_one : IsOmega2Only (.one : PWord Gen) := trivial
@[simp] theorem isOmega2Only_gen (g : Gen) : IsOmega2Only (.gen g) := trivial
@[simp] theorem isOmega2Only_mul {u v : PWord Gen} :
    IsOmega2Only (.mul u v) ↔ IsOmega2Only u ∧ IsOmega2Only v := Iff.rfl
@[simp] theorem isOmega2Only_inv {u : PWord Gen} :
    IsOmega2Only (.inv u) ↔ IsOmega2Only u := Iff.rfl
@[simp] theorem isOmega2Only_conj {u g : PWord Gen} :
    IsOmega2Only (.conj u g) ↔ IsOmega2Only u ∧ IsOmega2Only g := Iff.rfl
@[simp] theorem isOmega2Only_comm {u v : PWord Gen} :
    IsOmega2Only (.comm u v) ↔ IsOmega2Only u ∧ IsOmega2Only v := Iff.rfl
@[simp] theorem isOmega2Only_zpow {u : PWord Gen} {k : ℤ} :
    IsOmega2Only (.zpow u k) ↔ IsOmega2Only u := Iff.rfl
@[simp] theorem isOmega2Only_profPow {u : PWord Gen} {γ : Zhat} :
    IsOmega2Only (.profPow u γ) ↔ γ = omega2 ∧ IsOmega2Only u := Iff.rfl
@[simp] theorem isOmega2Only_omega2Pow {u : PWord Gen} :
    IsOmega2Only (omega2Pow u) ↔ IsOmega2Only u := by
  simp [omega2Pow]

end PWord

/-! ## Derived letters over the semantic alphabet -/

section Letters

variable {n : ℕ}

/-- The letter **`σ₂ = σ^{ω₂}`** (packet Def. 2.1). -/
noncomputable def sigma2W : PWord (Generator n) := (PWord.gen .sigma).omega2Pow

/-- The **`δ`-letter `δ_i = (x_i τ)^{ω₂} x_i⁻¹`** (packet §10, `\delta_i` of Prop. 10.2), the
degree-`n` generalisation of the `ℚ₂` ledger letter `d₀` of `GQ2/Words.lean`. -/
noncomputable def deltaW (i : Fin (n + 1)) : PWord (Generator n) :=
  .mul (PWord.omega2Pow (.mul (.gen (.wild i)) (.gen .tau))) (.inv (.gen (.wild i)))

@[simp] theorem isOmega2Only_sigma2W : (sigma2W (n := n)).IsOmega2Only := by
  simp [sigma2W, PWord.omega2Pow]

@[simp] theorem isOmega2Only_deltaW (i : Fin (n + 1)) : (deltaW i).IsOmega2Only := by
  simp [deltaW, PWord.omega2Pow]

end Letters

/-! ## The two boundary specializations

Transcriptions of `dyadic_search/semantics/specialization.py`.  Only the *substitution* halves
live here; the semantic content (Gate B's rules T1/T2, and the fact that the rewrites do not
change the evaluated element) is proved in `GQ2/Dyadic/Word/Eval.lean`. -/

section Specialization

variable {n : ℕ}

/-- The Gate-B substitution: every wild generator goes to `1`, `σ` and `τ` are untouched
(`specialize_tame`, step 0). -/
def killWildSubst : Generator n → PWord (Generator n)
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild _ => .one

@[simp] theorem killWildSubst_sigma : killWildSubst (n := n) .sigma = .gen .sigma := rfl
@[simp] theorem killWildSubst_tau : killWildSubst (n := n) .tau = .gen .tau := rfl
@[simp] theorem killWildSubst_wild (i : Fin (n + 1)) :
    killWildSubst (.wild i) = (.one : PWord (Generator n)) := rfl

/-- **Gate B, step 0** (`specialize_tame`): kill the wild generators `x₀, …, x_n`.

Hyperbolic-handle blocks are not a constructor of `PWord`, so the Python discussion of
`handle_generators_wild` does not arise: a handle product is written out with genuine `wild`
letters and dies with them. -/
def killWild : PWord (Generator n) → PWord (Generator n) := PWord.subst killWildSubst

/-- **Gate C** (`specialize_pro2`): the maximal pro-`2` specialization as an exact rewrite —
`τ ↦ 1`, `w^{ω₂} ↦ w` (this *is* `σ₂ ↦ σ`), every other exponent kept.

The `η̂`-contract of `specialization.py` is reproduced verbatim: an `η̂`-power is **not**
collapsed, its base is rewritten and the letter kept, because "in the maximal pro-`2` quotient
the profinite exponent `η̂` becomes the genuine `ℤ₂`-power `η`" and the marked cores are written
with the same letters.  Likewise a `ℤ₂`-power survives untouched. -/
noncomputable def pro2 : PWord (Generator n) → PWord (Generator n)
  | .one => .one
  | .gen .tau => .one
  | .gen g => .gen g
  | .mul u v => .mul (pro2 u) (pro2 v)
  | .inv u => .inv (pro2 u)
  | .conj u g => .conj (pro2 u) (pro2 g)
  | .comm u v => .comm (pro2 u) (pro2 v)
  | .zpow u k => .zpow (pro2 u) k
  | .z2pow u z => .z2pow (pro2 u) z
  | .profPow u γ =>
      @ite _ (γ = omega2) (Classical.propDecidable _) (pro2 u) (.profPow (pro2 u) γ)

@[simp] theorem pro2_one : pro2 (n := n) .one = .one := rfl
@[simp] theorem pro2_gen_tau : pro2 (n := n) (.gen .tau) = .one := rfl
@[simp] theorem pro2_gen_sigma : pro2 (n := n) (.gen .sigma) = .gen .sigma := rfl
@[simp] theorem pro2_gen_wild (i : Fin (n + 1)) :
    pro2 (.gen (.wild i)) = (.gen (.wild i) : PWord (Generator n)) := rfl
@[simp] theorem pro2_mul (u v : PWord (Generator n)) :
    pro2 (.mul u v) = .mul (pro2 u) (pro2 v) := rfl
@[simp] theorem pro2_inv (u : PWord (Generator n)) : pro2 (.inv u) = .inv (pro2 u) := rfl
@[simp] theorem pro2_conj (u g : PWord (Generator n)) :
    pro2 (.conj u g) = .conj (pro2 u) (pro2 g) := rfl
@[simp] theorem pro2_comm (u v : PWord (Generator n)) :
    pro2 (.comm u v) = .comm (pro2 u) (pro2 v) := rfl
@[simp] theorem pro2_zpow (u : PWord (Generator n)) (k : ℤ) :
    pro2 (.zpow u k) = .zpow (pro2 u) k := rfl
@[simp] theorem pro2_z2pow (u : PWord (Generator n)) (z : ℤ_[2]) :
    pro2 (.z2pow u z) = .z2pow (pro2 u) z := rfl

/-- Gate C collapses an `ω₂`-power. -/
@[simp] theorem pro2_profPow_omega2 (u : PWord (Generator n)) :
    pro2 (.profPow u omega2) = pro2 u := by
  show @ite _ (omega2 = omega2) (Classical.propDecidable _) (pro2 u) _ = pro2 u
  rw [if_pos rfl]

/-- Gate C keeps every profinite exponent other than `ω₂` — in particular the `η̂`-letters, per
the pinned `η̂`-contract of `specialization.py`. -/
theorem pro2_profPow_of_ne (u : PWord (Generator n)) {γ : Zhat} (h : γ ≠ omega2) :
    pro2 (.profPow u γ) = .profPow (pro2 u) γ := by
  show @ite _ (γ = omega2) (Classical.propDecidable _) (pro2 u) _ = _
  rw [if_neg h]

@[simp] theorem pro2_omega2Pow (u : PWord (Generator n)) : pro2 (PWord.omega2Pow u) = pro2 u := by
  rw [PWord.omega2Pow, pro2_profPow_omega2]

/-- `σ₂ ↦ σ` — the headline instance of Gate C's rewrite. -/
@[simp] theorem pro2_sigma2W : pro2 (sigma2W (n := n)) = .gen .sigma := by
  simp [sigma2W]

/-- `δ_i ↦ x_i x_i⁻¹` — the syntactic half of "every `δ_i = 1`" (`specialization.py`, Gate C). -/
@[simp] theorem pro2_deltaW (i : Fin (n + 1)) :
    pro2 (deltaW i) = .mul (.mul (.gen (.wild i)) .one) (.inv (.gen (.wild i))) := by
  simp [deltaW]

end Specialization

end GQ2.Dyadic
