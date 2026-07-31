/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Eval
public import GQ2.FoxHeisenberg.WildRow
public import GQ2.Roe.WildRow
public import Mathlib.GroupTheory.PGroup

@[expose] public section

/-!
# Dyadic campaign, layer WW1: the generic Fox evaluator and the literal defect formula

The word-certificate lane's foundation (plan §3 A1, board WW1): a **structural-recursion Fox
evaluator** on the reflected syntax `PWord` of `GQ2/Dyadic/Word/Syntax.lean`, valued in the lift
group `A ⋊ C` (`GQ2.FoxH.WordLift`, `GQ2/FoxHeisenberg/Basic.lean`), together with the packet's
§4 lifting theory: the literal defect formula (packet Prop. 4.1), the no-extra-equation
statement for admissibility (packet Prop. 4.2), and coefficient exactness (packet Lem. 4.3).

## The evaluator: nothing but `evalFin` in the lift group

The paper convention `(u, g)(v, h) = (u + g•v, gh)` makes the `A`-offset of a product obey the
Fox rule `D(uv) = D(u) + ū·D(v)` and the offset of an inverse obey `D(u⁻¹) = −ū⁻¹·D(u)` — the
two displays of packet Prop. 4.1's proof.  So the generic Fox evaluator is **literally F2's
finite denotation `PWord.evalFin` applied at a lifted marking** `g ↦ (a g, t g)`:

* `foxLift t a` — the lifted marking `X → WordLift A C`;
* `foxEval t a E E₂ w` — `evalFin` at the lifted marking (profinite `ω₂`-powers via the
  intrinsic `powOmega2`, i.e. packet Lem. 2.2 finite evaluation; other profinite exponents via
  the resolvers `E`, `E₂`, exactly as in F2);
* `foxD t a E E₂ w` — the **Fox derivative**: the `A`-offset of `foxEval`; `foxDHom` bundles it
  additively in the offsets;
* `foxD0 t` — the coboundary `v ↦ (g ↦ t g • v − v)` (display `d⁰`);
* `foxJacobian t E E₂ R₁ R₂ : (X → A) →+ A × A` — the **evaluated two-relator Jacobian**
  `d¹_{R,ρ}`; at `X = Generator n` this is the packet's `A^{n+3} → A²`, one coordinate per
  marked generator `σ, τ, x₀, …, x_n` (the packet's column order).

This mirrors the Sage reference implementation
(`~/claude/general_2adic/dyadic_search/semantics/fox.py`, section 5 "Numeric
cross-validation"): its `SemidirectGroup` realizes exactly `WordLift A C`, and lifting the
marked generator `g` to `(a_g, ρ(g))` gives the exact identity `α(w) = Σ_g (∂w/∂g)(a_g)`
"for arbitrary `a_g` (not merely to first order: `A` is abelian)".  The Lean twin of its
`word_lift_derivative` is `foxD`; the identity is exact here for the same reason.

## The lift level (the one delicate point — `fox.py` §2, mirrored, not rediscovered)

An `ω₂`-power is differentiated **at the order of the lifted element**, not at the order of its
lower value.  If the base `p.g` has order `e`, the lift `p` has order dividing `2e`
(`WordLift.orderOf_dvd_two_mul_orderOf_base` — the Lean form of `fox.py`'s "Lemma (lift
level)"), and the two levels genuinely differ on the first jet: for a *pro-odd* base (odd `e`)
the naive level-`e` reading of `ω₂` gives the Fox coefficient `0`, while the truth at level
`2e` is the norm projector `P = 1 + T + ⋯ + T^{e−1}`.  `foxEval` is immune by construction —
`powOmega2` reads the order of the lifted element itself (the same reason `fox.py` §5's numeric
cross-validation is exact) — but every *resolver* argument `E`/`E₂` for a non-`ω₂` profinite
exponent must be chosen correct **at the lift level**; a resolver correct only in the lower
group silently halves the level and produces the falsely-zero derivative.  With a `ℤ/4` centre
(class-two extensions, WW3/WW4 territory) the constant is `4`, not `2` — `fox.py`'s
`LIFT_LEVEL_FACTOR`; the statements below are the exponent-`2` (elementary `A`) case only.

Two corollaries, both engine lemmas here (`fox.py` §2's "Two corollaries"):

* **`η̂` differentiates to `1` on pro-odd bases** (the jet-level shadow of Gate B's rule T2):
  the `η̂`-residue at level `2e`, `e` odd, is `1`, so the `η̂`-power of the lift *is* the lift
  (`WordLift.zpowHat_etaHatZ_of_odd_orderOf_base`), whence `D(u^{η̂}) = D(u)` with no
  correction term.
* **Every profinite geometric sum has augmentation `1`**: the profinite exponents produced at
  the lift level are odd, so the scalar (`𝔽₂`-augmentation) specialization of every
  `Proj`/geometric-sum operator is `1` — `sum_pow_smul_of_trivial_odd` is the module form
  (trivial action + char 2 + odd length ⇒ the sum is the identity operator).

The split/ramified collapses of the `ω₂`-geometric sum are **already** the engine lemmas
`WordLift.powOmega2_u_of_trivial` (split: `P = 1`; on a simple *unramified* module the wild
bases and — by the marked hypothesis `hU` of the `Γ_A` row — `σ₂ = S₂` act as the identity,
which is why the projector collapses there) and `WordLift.powOmega2_u_of_oddFixedPointFree`
(ramified: `P = 0`) of `GQ2/FoxHeisenberg/Basic.lean`; this file adds no duplicate.

## Packet §4, formalized

* **Prop. 4.1** (`prop:defect`).  For an extension `1 → A → B → C → 1` with `A` abelian
  (interface: `ι : A → B` multiplicative-on-additive, conjugation-compatible with the
  `B`-action on the coefficients), `foxGlue` is the homomorphism `WordLift A B →* B`,
  `(u, b) ↦ ι u · b`, and naturality of `evalFin` through it gives the **literal defect
  formula** `foxDefect_eq`: evaluating any word at the shifted lifts `g ↦ ι (a g) · b g`
  multiplies the evaluation at `b` by `ι` of the Fox derivative — the packet display
  `e ↦ e + d¹_{R,ρ}(a)` is `foxDefect_shift`.  Consequences: `foxLifts_iff` /
  `foxLifts_iff_coker` (a lift exists iff the defect dies in `coker d¹`),
  `foxSolution_sub_mem_ker` + `foxSolution_add_ker` (the solution set is a `ker d¹`-torsor),
  and `foxJacobian_comp_foxD0` (simultaneous conjugation gives the three-term complex
  `0 → A → A^X → A² → 0`).  The descent lemmas `foxD_comp_hom`/`foxJacobian_comp_hom` move the
  Jacobian between `B`- and `C`-coefficients (the conjugation action factors through `C`
  because `A` is abelian), so `d¹` may be computed through `ρ` exactly as the packet writes it.
* **Prop. 4.2** (`prop:no-extra`).  `comap_isPGroup_of_elementaryKer`: the preimage of a
  normal `2`-subgroup under an elementary `2`-extension is a `2`-group (`comap_normal`,
  `lift_mem_comap` complete the statement) — pro-`2` admissibility adds **no equation** to the
  elementary lifting problem.
* **Lem. 4.3** (`lem:coeff-exact`).  Coefficient functoriality of the whole complex
  (`foxD_map_coeff`, `foxD0_map_coeff`, `foxJacobian_map_coeff`) and the coordinatewise
  transfer of exactness to the terms (`pi_map_*`, `prodMap_*`): a short exact sequence of
  finite `𝔽₂[C]`-modules induces a termwise short exact sequence of Fox complexes, naturally.

## Regression (mandatory, plan §3 A1): the `n = 1` hand rows

`gammaAWildWord` and `gammaRWildWord` are the `Γ_A`/`Γ_R` wild relators as `PWord (Generator 1)`
trees, mirroring `GQ2/Words.lean` and `GQ2/Roe/Words.lean` **letter for letter** (same
association, same exponent spellings — `(x₀³)⁻¹` not `x₀⁻³`, `d₀²` as `zpow 2`, matching the
machine-readable App. B block).  The evaluator reproduces the ledger values at **every** marking
(`evalFin_gammaAWildWord`, `evalFin_gammaRWildWord`), in particular at every lifted marking
(`foxEval_gammaAWildWord`/`foxEval_gammaRWildWord`), and the generic rows therefore equal the
hand rows `GQ2.FoxH.liftMarking_wildValue_u` (`GQ2/FoxHeisenberg/WildRow.lean`) and
`GQ2.FoxH.liftMarking_wildValueR_u` (`GQ2/Roe/WildRow.lean`): `foxD_gammaAWildWord_split` and
`foxD_gammaRWildWord_split`.  Note `Γ_R`'s row needs no `σ₂`-tameness hypothesis `hU`, exactly
as the hand row.  Per the frozen selection (`selection-freeze.md` row 1, SQ1), the `n = 1`
specialization of the primary `L_sq` word *is* `Γ_R`'s relator, so the `Γ_R` pin is also the
`L_sq` base-case pin for lane WL.

## Axiom state (recorded per WW1 instructions; `#print axioms` run in a scratch section, not
committed)

All headline declarations of this file print exactly the standard axioms
`[propext, Classical.choice, Quot.sound]` (std-3): checked for `foxD`, `foxJacobian`,
`foxDefect_eq`, `foxLifts_iff`, `foxLifts_iff_coker`, `foxSolution_sub_mem_ker`,
`foxSolution_add_ker`, `foxJacobian_comp_foxD0`, `comap_isPGroup_of_elementaryKer`,
`foxD_map_coeff`, `foxJacobian_map_coeff`, `WordLift.orderOf_dvd_two_mul_orderOf_base`,
`WordLift.zpowHat_etaHatZ_of_odd_orderOf_base`, `foxD_gammaAWildWord_split`,
`foxD_gammaRWildWord_split`, `foxD_gammaRWildWord_ramified`.  No sorries; no new axioms;
kernel `decide` only (no `native_decide`).

## Implementation notes

`module`-style: all four imports are `module`-style (`GQ2.Dyadic.Word.Eval`,
`GQ2.FoxHeisenberg.WildRow`, `GQ2.Roe.WildRow`, Mathlib).  The file deliberately does **not**
import `GQ2/Dyadic/NpcJet/*` (plain-import; module-system rule, plan §3 A5) and needs none of
its seams: everything here goes through `evalFin`-naturality, not the `κ⁰`-extension slice.
`nc3_orderOf_dvd_two_mul` of `GQ2/Dyadic/NpcJet/Omega.lean` proves the same `2·ord`
divisibility on the `CentExt` carrier; `WordLift.orderOf_dvd_two_mul_orderOf_base` below is the
`WordLift` carrier's copy under a distinct name (dedup note: a joint hoist to a carrier-generic
lemma is a mechanical follow-up for the orchestrator).  Likewise `conjR_eq_conjP`/
`commR_eq_commP` are the one-line crossovers `GQ2/Dyadic/Word/Blocks.lean` promised, local and
`private` here.
-/

namespace GQ2.Dyadic

/-! ## The `η̂`-exponent at low `2`-valuation

Preparation for the `η̂` lift-level corollary: the `2`-part of the `η̂`-exponent dies at any
level of `2`-valuation `≤ 1`. -/

/-- For `η` an odd `2`-adic integer (`η = 1 + 2z`), the finite `z·ω₂`-exponent of `η − 1`
vanishes at every level `N` with `v₂(N) ≤ 1`: the `2`-part contributes `(η−1 mod 2) = 0` and
the odd part is killed by `ω₂`.  This is the computation behind "the `η̂`-residue at level
`2e`, `e` odd, is `1`". -/
theorem padicOmega2Exp_eta_eq_zero {η : ℤ_[2]} (z : ℤ_[2]) (hη : η = 1 + 2 * z)
    {N : ℕ} (hN : N.factorization 2 ≤ 1) : padicOmega2Exp (η - 1) N = 0 := by
  have h2 : (η - 1 : ℤ_[2]) = 2 * z := by rw [hη]; ring
  rw [padicOmega2Exp, h2]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hN with h | h
  · exact mul_eq_zero_of_right _ (by simp [omega2Exp, h])
  · rw [h]
    refine mul_eq_zero_of_left ?_ _
    have hmap : (PadicInt.toZModPow 1 (2 * z) : ZMod (2 ^ 1)) = 0 := by
      rw [map_mul, map_ofNat]
      exact mul_eq_zero_of_left (by decide) _
    rw [hmap, ZMod.val_zero]

end GQ2.Dyadic

namespace GQ2.FoxH.WordLift

/-! ## Lift-group additions: the base projection and the lift-level lemmas

New `WordLift` API consumed by the Fox layer below (and by WW2's certificates): the bundled
base projection and the lift-level engine lemmas of `fox.py` §2. -/

section BaseProj

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The base projection `A ⋊ C →* C`, `(u, g) ↦ g` — `.g` bundled as a homomorphism (the `π` of
the split model). -/
def baseProj : WordLift A C →* C where
  toFun p := p.g
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem baseProj_apply (p : WordLift A C) : baseProj p = p.g := rfl

/-- The base coordinate of an integer power is the integer power of the base (`pow_g` for `ℤ`,
via `baseProj`). -/
theorem zpow_g (p : WordLift A C) (m : ℤ) : (p ^ m).g = p.g ^ m :=
  map_zpow baseProj p m

/-- **The lift-level lemma** (`fox.py` §2, "Lemma (lift level)"), split-model form: over an
elementary (2-torsion) coefficient module, the order of a lift divides **twice** the order of
its base — `p^e` has trivial base for `e = ord(p.g)`, and its offset kills itself.  The factor
`2` is essential: differentiating an `ω₂`-power at the naive level `e` instead of `2e` silently
produces the Fox coefficient `0` where the truth is the norm projector `P`.  (No finiteness:
if the base has infinite order the statement is `∣ 0`, trivially true.) -/
theorem orderOf_dvd_two_mul_orderOf_base (hA₂ : ∀ a : A, a + a = 0) (p : WordLift A C) :
    orderOf p ∣ 2 * orderOf p.g := by
  refine orderOf_dvd_of_pow_eq_one ?_
  have hg : (p ^ orderOf p.g).g = 1 := by rw [pow_g, pow_orderOf_eq_one]
  have hsq : (p ^ orderOf p.g) * (p ^ orderOf p.g) = 1 := by
    ext
    · rw [mul_u, hg, one_smul, hA₂, one_u]
    · rw [mul_g, hg, one_mul, one_g]
  calc p ^ (2 * orderOf p.g) = (p ^ orderOf p.g) * (p ^ orderOf p.g) := by
        rw [two_mul, pow_add]
    _ = 1 := hsq

/-- Powers of a lift see exponents only modulo `2·ord(base)`: the exponent-level consequence of
the lift-level lemma — the form WW2's resolver-correctness conditions quote. -/
theorem pow_eq_pow_of_modEq_two_mul (hA₂ : ∀ a : A, a + a = 0) (p : WordLift A C) {k l : ℕ}
    (hkl : k ≡ l [MOD 2 * orderOf p.g]) : p ^ k = p ^ l :=
  pow_eq_pow_iff_modEq.mpr (hkl.of_dvd (orderOf_dvd_two_mul_orderOf_base hA₂ p))

end BaseProj

section EtaLift

open GQ2.Dyadic

/-- **`η̂` fixes lifts of pro-odd bases** — the jet-level shadow of Gate B's rule T2 (`fox.py`
§2, first corollary): if the base `p.g` has odd order and the coefficients are elementary, the
`η̂`-power of the lift `p` is `p` itself, for every odd `η = 1 + 2z`.  Consequently
`D(u^{η̂}) = D(u)`: an `η̂`-power on a pro-odd base contributes the identity operator to the
Fox row, not a geometric sum.  (The content is that the **lift** is fixed, offset included:
`v₂(ord p) ≤ v₂(2e) = 1` by the lift-level lemma, and the `η̂`-residue there is `1`.) -/
theorem zpowHat_etaHatZ_of_odd_orderOf_base {C : Type} [Group C] {A : Type} [AddCommGroup A]
    [DistribMulAction C A] [TopologicalSpace (WordLift A C)] [DiscreteTopology (WordLift A C)]
    [Finite A] [Finite C] (hA₂ : ∀ a : A, a + a = 0) {p : WordLift A C}
    (hodd : Odd (orderOf p.g)) {η : ℤ_[2]} (z : ℤ_[2]) (hη : η = 1 + 2 * z) :
    p ^ᶻ etaHatZ η = p := by
  have hval : (orderOf p).factorization 2 ≤ 1 := by
    have hdvd := orderOf_dvd_two_mul_orderOf_base hA₂ p
    have hne : 2 * orderOf p.g ≠ 0 :=
      mul_ne_zero (by norm_num) (orderOf_pos p.g).ne'
    have hle := (Nat.factorization_le_iff_dvd (orderOf_pos p).ne' hne).mpr hdvd 2
    have h2m : (2 * orderOf p.g).factorization 2 = 1 := by
      have hodd' : (orderOf p.g).factorization 2 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd
          (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using hodd)
      rw [Nat.factorization_mul (by norm_num) (orderOf_pos p.g).ne']
      simp [Nat.Prime.factorization_self Nat.prime_two, hodd']
    exact h2m ▸ hle
  rw [zpowHat_etaHatZ, padicOmega2Exp_eta_eq_zero z hη hval, pow_zero, mul_one]

end EtaLift

section Augmentation

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- A geometric sum over a trivially-acting base is scalar: `Σ_{i<k} g^i • u = k • u`. -/
theorem sum_pow_smul_of_trivial {g : C} (hg : ∀ a : A, g • a = a) (u : A) (k : ℕ) :
    ∑ i ∈ Finset.range k, g ^ i • u = k • u := by
  have hc : ∀ i, g ^ i • u = u := (MulAction.stabilizer C u).pow_mem (hg u)
  simp only [hc, Finset.sum_const, Finset.card_range]

/-- **Every profinite geometric sum has augmentation `1`** (`fox.py` §2, second corollary): the
profinite exponents produced at the lift level are odd, and over elementary coefficients with a
trivially-acting base an odd-length geometric sum is the identity operator.  This is the scalar
(`𝔽₂`-augmentation) specialization pin: every profinite geometric-sum operator augments to
`1`, never `0`. -/
theorem sum_pow_smul_of_trivial_odd (hA₂ : ∀ a : A, a + a = 0) {g : C}
    (hg : ∀ a : A, g • a = a) (u : A) {k : ℕ} (hk : Odd k) :
    ∑ i ∈ Finset.range k, g ^ i • u = u := by
  obtain ⟨m, hm⟩ := hk
  rw [sum_pow_smul_of_trivial hg, hm, add_nsmul, mul_nsmul, two_nsmul, hA₂, nsmul_zero,
    zero_add, one_nsmul]

end Augmentation

end GQ2.FoxH.WordLift

namespace GQ2.Dyadic

open GQ2.FoxH

/-! ## The Fox evaluator -/

section FoxEval

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- The **lifted marking**: each generator `g` goes to the pair `(a g, t g)` in the lift group
`A ⋊ C` — the Lean twin of `fox.py` §5's "lifting the marked generator `g` to
`(a_g, rho(g))`". -/
def foxLift (t : X → C) (a : X → A) : X → WordLift A C := fun g => ⟨a g, t g⟩

omit [Group C] [AddCommGroup A] [DistribMulAction C A] in
@[simp] theorem foxLift_u (t : X → C) (a : X → A) (g : X) : (foxLift t a g).u = a g := rfl

omit [Group C] [AddCommGroup A] [DistribMulAction C A] in
@[simp] theorem foxLift_g (t : X → C) (a : X → A) (g : X) : (foxLift t a g).g = t g := rfl

/-- Zero offsets lift along the base embedding. -/
theorem foxLift_zero (t : X → C) :
    foxLift t (0 : X → A) = fun g => WordLift.baseEmbed (t g) := rfl

/-- **The generic Fox evaluator** (board WW1; plan §3 A1): F2's finite denotation `evalFin` at
the lifted marking.  Profinite `ω₂`-powers are evaluated intrinsically by `powOmega2` **at the
order of the lifted element** — the lift-level discipline of the module docstring — and any
other profinite/`ℤ₂` exponent through the resolvers `E`/`E₂`, which must therefore be correct
at the lift level (orders may double: `WordLift.orderOf_dvd_two_mul_orderOf_base`). -/
noncomputable def foxEval (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord X) : WordLift A C :=
  PWord.evalFin (foxLift t a) E E₂ w

/-- **The Fox derivative** `D_{t,a}(w)`: the `A`-offset of the Fox evaluation.  By exactness of
the split model (`fox.py` §5's `WordLift` identity) this is `Σ_g (∂w/∂g)|_t (a g)` — the Fox
row of `w` evaluated through the marking `t` and applied to the offsets `a`, exactly, not
merely to first order. -/
noncomputable def foxD (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord X) : A :=
  (foxEval t a E E₂ w).u

variable (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

theorem foxEval_def (w : PWord X) :
    foxEval t a E E₂ w = PWord.evalFin (foxLift t a) E E₂ w := rfl

theorem foxD_def (w : PWord X) : foxD t a E E₂ w = (foxEval t a E E₂ w).u := rfl

/-! ### Structural equations (`rfl`-level, no finiteness)

The raw recursion: `foxEval` is `evalFin`, so each constructor's equation is definitional; the
`.u`-coordinates are the Fox rules with the base still spelled inside the lift group.  The
finite "textbook" forms with the base identified as `evalFin t` follow the base lemma
`foxEval_g` below. -/

@[simp] theorem foxEval_one : foxEval t a E E₂ .one = 1 := rfl
@[simp] theorem foxEval_gen (g : X) : foxEval t a E E₂ (.gen g) = ⟨a g, t g⟩ := rfl
@[simp] theorem foxEval_mul (u v : PWord X) :
    foxEval t a E E₂ (.mul u v) = foxEval t a E E₂ u * foxEval t a E E₂ v := rfl
@[simp] theorem foxEval_inv (u : PWord X) :
    foxEval t a E E₂ (.inv u) = (foxEval t a E E₂ u)⁻¹ := rfl
@[simp] theorem foxEval_conj (u g : PWord X) :
    foxEval t a E E₂ (.conj u g) = conjR (foxEval t a E E₂ u) (foxEval t a E E₂ g) := rfl
@[simp] theorem foxEval_comm (u v : PWord X) :
    foxEval t a E E₂ (.comm u v) = commR (foxEval t a E E₂ u) (foxEval t a E E₂ v) := rfl
@[simp] theorem foxEval_zpow (u : PWord X) (k : ℤ) :
    foxEval t a E E₂ (.zpow u k) = foxEval t a E E₂ u ^ k := rfl
@[simp] theorem foxEval_z2pow (u : PWord X) (z : ℤ_[2]) :
    foxEval t a E E₂ (.z2pow u z) = foxEval t a E E₂ u ^ E₂ z := rfl

@[simp] theorem foxEval_profPow_omega2 (u : PWord X) :
    foxEval t a E E₂ (.profPow u omega2) = powOmega2 (foxEval t a E E₂ u) :=
  PWord.evalFin_profPow_omega2 _ E E₂ u

theorem foxEval_profPow_of_ne (u : PWord X) {γ : Zhat} (h : γ ≠ omega2) :
    foxEval t a E E₂ (.profPow u γ) = foxEval t a E E₂ u ^ E γ :=
  PWord.evalFin_profPow_of_ne _ E E₂ u h

@[simp] theorem foxEval_omega2Pow (u : PWord X) :
    foxEval t a E E₂ u.omega2Pow = powOmega2 (foxEval t a E E₂ u) :=
  PWord.evalFin_omega2Pow _ E E₂ u

/-- `D(1) = 0`. -/
@[simp] theorem foxD_one : foxD t a E E₂ .one = 0 := rfl

/-- `D(g) = a g`: a generator letter differentiates to its offset. -/
@[simp] theorem foxD_gen (g : X) : foxD t a E E₂ (.gen g) = a g := rfl

/-- **`D(uv) = D(u) + ū·D(v)`**, raw form (the base `ū` spelled inside the lift group): the
multiplication law of `WordLift` itself, hence `rfl`. -/
theorem foxD_mul' (u v : PWord X) :
    foxD t a E E₂ (.mul u v)
      = foxD t a E E₂ u + (foxEval t a E E₂ u).g • foxD t a E E₂ v := rfl

/-- **`D(u⁻¹) = −ū⁻¹·D(u)`**, raw form. -/
theorem foxD_inv' (u : PWord X) :
    foxD t a E E₂ (.inv u) = -((foxEval t a E E₂ u).g⁻¹ • foxD t a E E₂ u) := rfl

/-- `D(u^k) = (1 + ū + ⋯ + ū^{k−1})·D(u)` for a natural exponent, raw form: the norm-of-power
formula `WordLift.pow_u`. -/
theorem foxD_zpow_natCast' (u : PWord X) (k : ℕ) :
    foxD t a E E₂ (.zpow u (k : ℤ))
      = ∑ i ∈ Finset.range k, (foxEval t a E E₂ u).g ^ i • foxD t a E E₂ u := by
  show (foxEval t a E E₂ u ^ (k : ℤ)).u = _
  rw [zpow_natCast, WordLift.pow_u]
  rfl

/-- `D(u^{−k}) = −ū^{−k}·D(u^k)`: the negative half of the integer-power rule, reduced to the
natural case through the inverse rule. -/
theorem foxD_zpow_neg' (u : PWord X) (k : ℕ) :
    foxD t a E E₂ (.zpow u (-(k : ℤ)))
      = -(((foxEval t a E E₂ u).g ^ k)⁻¹ • foxD t a E E₂ (.zpow u (k : ℤ))) := by
  show (foxEval t a E E₂ u ^ (-(k : ℤ))).u
      = -(((foxEval t a E E₂ u).g ^ k)⁻¹ • (foxEval t a E E₂ u ^ (k : ℤ)).u)
  rw [zpow_neg, WordLift.inv_u, WordLift.zpow_g, zpow_natCast]

/-- The `ω₂`-power differentiates to the geometric sum **at the lift level**: the exponent is
`omega2Exp` of the order of the *lifted* evaluation, which may be twice the base order (module
docstring).  The split (`P = 1`) and ramified (`P = 0`) collapses of this sum are
`WordLift.powOmega2_u_of_trivial` and `WordLift.powOmega2_u_of_oddFixedPointFree`. -/
theorem foxD_profPow_omega2' (u : PWord X) :
    foxD t a E E₂ (.profPow u omega2)
      = ∑ i ∈ Finset.range (omega2Exp (orderOf (foxEval t a E E₂ u))),
          (foxEval t a E E₂ u).g ^ i • foxD t a E E₂ u := by
  show (foxEval t a E E₂ (.profPow u omega2)).u = _
  rw [foxEval_profPow_omega2, powOmega2, WordLift.pow_u]
  rfl

end FoxEval

/-! ### The base lemma and the textbook Fox rules -/

section FoxBase

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  [Finite A] [Finite C]

variable (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The base of the Fox evaluation is the evaluation of the base**: pushing `foxEval` through
the base projection recovers `evalFin` at the underlying marking.  (Finiteness because `ω₂`
computes `2`-primary parts only in finite groups — `powOmega2_map`.) -/
theorem foxEval_g (w : PWord X) : (foxEval t a E E₂ w).g = PWord.evalFin t E E₂ w := by
  have h := PWord.map_evalFin (WordLift.baseProj (C := C) (A := A)) (foxLift t a) E E₂ w
  simpa [foxEval_def] using h

/-- **`D(uv) = D(u) + ū·D(v)`** (packet Prop. 4.1's first display), textbook form. -/
theorem foxD_mul (u v : PWord X) :
    foxD t a E E₂ (.mul u v)
      = foxD t a E E₂ u + PWord.evalFin t E E₂ u • foxD t a E E₂ v := by
  rw [foxD_mul', foxEval_g]

/-- **`D(u⁻¹) = −ū⁻¹·D(u)`** (packet Prop. 4.1's second display), textbook form. -/
theorem foxD_inv (u : PWord X) :
    foxD t a E E₂ (.inv u) = -((PWord.evalFin t E E₂ u)⁻¹ • foxD t a E E₂ u) := by
  rw [foxD_inv', foxEval_g]

/-- `D(u^k)` as the evaluated geometric sum `(1 + ū + ⋯ + ū^{k−1})·D(u)`, textbook form. -/
theorem foxD_zpow_natCast (u : PWord X) (k : ℕ) :
    foxD t a E E₂ (.zpow u (k : ℤ))
      = ∑ i ∈ Finset.range k, PWord.evalFin t E E₂ u ^ i • foxD t a E E₂ u := by
  rw [foxD_zpow_natCast']
  simp only [foxEval_g]

omit [Finite A] [Finite C] in
/-- `D(u^g) = ḡ⁻¹·(D(u) + ū·D(g) − D(g))`, raw form — the conjugation rule in closed form
(`fox.py` §3 expands `Conjugate` and recurses; the closed form is what row assemblies quote). -/
theorem foxD_conj' {X' : Type*} (t' : X' → C) (a' : X' → A) (u g : PWord X') :
    foxD t' a' E E₂ (.conj u g)
      = (foxEval t' a' E E₂ g).g⁻¹ • (foxD t' a' E E₂ u
          + (foxEval t' a' E E₂ u).g • foxD t' a' E E₂ g - foxD t' a' E E₂ g) := by
  show ((foxEval t' a' E E₂ g)⁻¹ * foxEval t' a' E E₂ u * foxEval t' a' E E₂ g).u = _
  simp only [WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, smul_add,
    smul_sub, mul_smul, foxD_def]
  abel

/-- The conjugation rule, textbook form. -/
theorem foxD_conj (u g : PWord X) :
    foxD t a E E₂ (.conj u g)
      = (PWord.evalFin t E E₂ g)⁻¹ • (foxD t a E E₂ u
          + PWord.evalFin t E E₂ u • foxD t a E E₂ g - foxD t a E E₂ g) := by
  rw [foxD_conj', foxEval_g, foxEval_g]

end FoxBase

/-! ## Additivity in the offsets and the two-relator Jacobian -/

section Jacobian

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  [Finite A] [Finite C]

variable (t : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

omit [Finite A] [Finite C] in
private theorem fst_equivariant :
    ∀ (g : C) (v : A × A), (AddMonoidHom.fst A A) (g • v) = g • (AddMonoidHom.fst A A) v :=
  fun _ _ => rfl

omit [Finite A] [Finite C] in
private theorem snd_equivariant :
    ∀ (g : C) (v : A × A), (AddMonoidHom.snd A A) (g • v) = g • (AddMonoidHom.snd A A) v :=
  fun _ _ => rfl

omit [Finite A] [Finite C] in
private theorem sum_equivariant : ∀ (g : C) (v : A × A),
    (AddMonoidHom.fst A A + AddMonoidHom.snd A A) (g • v)
      = g • (AddMonoidHom.fst A A + AddMonoidHom.snd A A) v := by
  intro g v
  show (g • v).1 + (g • v).2 = g • (v.1 + v.2)
  rw [Prod.smul_fst, Prod.smul_snd, smul_add]

omit [Finite A] in
/-- Zero offsets have zero derivative: the zero-offset lift is the base embedding, a
homomorphic image of the base marking. -/
@[simp] theorem foxD_zero (w : PWord X) : foxD t (0 : X → A) E E₂ w = 0 := by
  have h := PWord.map_evalFin (WordLift.baseEmbed (A := A) (C := C)) t E E₂ w
  rw [foxD_def, foxEval_def, foxLift_zero, ← h]
  rfl

/-- **The Fox derivative is additive in the offsets** — the paper's "finite Fox rules"
linearity, proved once and generically by coefficient functoriality (the `d1Fun_add` argument
of `GQ2/FoxHeisenberg/Basic.lean`): evaluate over `A × A`, then push through the three
equivariant coefficient maps `fst`, `snd`, `fst + snd`. -/
theorem foxD_add (a b : X → A) (w : PWord X) :
    foxD t (a + b) E E₂ w = foxD t a E E₂ w + foxD t b E E₂ w := by
  set φ1 := WordLift.map (C := C) (AddMonoidHom.fst A A) fst_equivariant
  set φ2 := WordLift.map (C := C) (AddMonoidHom.snd A A) snd_equivariant
  set φs := WordLift.map (C := C) (AddMonoidHom.fst A A + AddMonoidHom.snd A A) sum_equivariant
  have h1 : (fun g => φ1 (foxLift t (fun g => (a g, b g)) g)) = foxLift t a := rfl
  have h2 : (fun g => φ2 (foxLift t (fun g => (a g, b g)) g)) = foxLift t b := rfl
  have hs : (fun g => φs (foxLift t (fun g => (a g, b g)) g)) = foxLift t (a + b) := rfl
  have e1 := PWord.map_evalFin φ1 (foxLift t (fun g => (a g, b g))) E E₂ w
  have e2 := PWord.map_evalFin φ2 (foxLift t (fun g => (a g, b g))) E E₂ w
  have es := PWord.map_evalFin φs (foxLift t (fun g => (a g, b g))) E E₂ w
  rw [h1] at e1
  rw [h2] at e2
  rw [hs] at es
  rw [foxD_def, foxD_def, foxD_def, foxEval_def, foxEval_def, foxEval_def, ← e1, ← e2, ← es]
  rfl

/-- The Fox derivative of a fixed word, bundled additively in the offsets: one **row** of the
evaluated Fox Jacobian. -/
noncomputable def foxDHom (w : PWord X) : (X → A) →+ A :=
  AddMonoidHom.mk' (fun a => foxD t a E E₂ w) fun a b => foxD_add t E E₂ a b w

@[simp] theorem foxDHom_apply (w : PWord X) (a : X → A) :
    foxDHom t E E₂ w a = foxD t a E E₂ w := rfl

/-- **The evaluated two-relator Jacobian** `d¹_{R,ρ}` (packet Prop. 4.1): the pair of Fox
derivatives of the two relator words, bundled additively.  At `X = Generator n` this is the
packet's `A^{n+3} → A²` (domain `Generator n → A`, one coordinate per marked generator
`σ, τ, x₀, …, x_n` — the packet's column order; `fox.py` §3's `columns` note). -/
noncomputable def foxJacobian (R₁ R₂ : PWord X) : (X → A) →+ A × A :=
  (foxDHom t E E₂ R₁).prod (foxDHom t E E₂ R₂)

@[simp] theorem foxJacobian_apply (R₁ R₂ : PWord X) (a : X → A) :
    foxJacobian t E E₂ R₁ R₂ a = (foxD t a E E₂ R₁, foxD t a E E₂ R₂) := rfl

end Jacobian

/-! ## The coboundary and the three-term complex (packet Prop. 4.1(3)) -/

section Coboundary

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The coboundary `d⁰`**: simultaneous infinitesimal conjugation, `v ↦ (g ↦ t g • v − v)` —
the generic form of `GQ2.FoxH.d0` (display (31)). -/
def foxD0 (t : X → C) : A →+ (X → A) :=
  AddMonoidHom.mk' (fun v => fun g => t g • v - v) <| by
    intro v w
    funext g
    show t g • (v + w) - (v + w) = (t g • v - v) + (t g • w - w)
    rw [smul_add]
    abel

@[simp] theorem foxD0_apply (t : X → C) (v : A) (g : X) : foxD0 t v g = t g • v - v := rfl

variable [Finite C]

/-- **Simultaneous conjugation is Fox-exact** (packet Prop. 4.1(3), the complex property): at
coboundary offsets `d⁰(v)` the Fox derivative of any word *killed by the marking* vanishes.
Proof: the coboundary lift is the base marking pushed through the inner-twisted base embedding
`g ↦ ⟨v,1⟩⁻¹·(0, g)·⟨v,1⟩` (`WordLift.conj_baseEmbed`), so its evaluation is a conjugate of an
offset-zero element — offset-zero as soon as the word dies below.  (Only `C` finite is needed:
naturality runs through `C →* WordLift A C`.) -/
theorem foxD_coboundary (t : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (v : A) {w : PWord X}
    (hw : PWord.evalFin t E E₂ w = 1) : foxD t (foxD0 t v) E E₂ w = 0 := by
  set ψ : C →* WordLift A C :=
    (MulAut.conj (⟨v, 1⟩ : WordLift A C)).symm.toMonoidHom.comp WordLift.baseEmbed
  have hψ_apply : ∀ g : C, ψ g = ⟨g • v - v, g⟩ := WordLift.conj_baseEmbed v
  have hlift : foxLift t (foxD0 t v) = fun g => ψ (t g) := by
    funext g
    rw [hψ_apply]
    rfl
  have h := PWord.map_evalFin ψ t E E₂ w
  rw [foxD_def, foxEval_def, hlift, ← h, hw, map_one]
  rfl

/-- **The three-term complex** `0 → A →^{d⁰} A^X →^{d¹} A² → 0` (packet Prop. 4.1(3)):
`d¹ ∘ d⁰ = 0` at any marking killing both relators. -/
theorem foxJacobian_comp_foxD0 [Finite A] (t : X → C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    {R₁ R₂ : PWord X} (hR₁ : PWord.evalFin t E E₂ R₁ = 1)
    (hR₂ : PWord.evalFin t E E₂ R₂ = 1) :
    (foxJacobian (A := A) t E E₂ R₁ R₂).comp (foxD0 t) = 0 :=
  AddMonoidHom.ext fun v =>
    Prod.ext (foxD_coboundary t E E₂ v hR₁) (foxD_coboundary t E E₂ v hR₂)

end Coboundary

/-! ## The literal defect formula (packet Prop. 4.1)

The extension interface: `1 → A → B → C → 1` with `A` abelian is carried as a
multiplicative-on-additive map `ι : A → B` (`hι`), with the `B`-action on the coefficients
realized by conjugation in `B` (`hconj`) — packet §4's preamble action, which factors through
`C` because `A` is abelian (descend along `π` with `foxD_comp_hom` to compute `d¹` through `ρ`
as the packet writes it).  Elementarity (`2`-torsion) enters only in Prop. 4.2; the defect
formula itself needs none of it. -/

section Defect

variable {X : Type*} {B : Type*} [Group B] {A : Type*} [AddCommGroup A] [DistribMulAction B A]

omit [DistribMulAction B A] in
private theorem iota_zero {ι : A → B} (hι : ∀ v w : A, ι (v + w) = ι v * ι w) :
    ι 0 = 1 := by
  have h : ι 0 * 1 = ι 0 * ι 0 := by
    rw [mul_one]
    simpa using hι 0 0
  exact (mul_left_cancel h).symm

/-- **The glue homomorphism** `A ⋊ B →* B` of an extension with abelian kernel:
`(u, b) ↦ ι u · b`.  The paper convention `(u, g)(v, h) = (u + g•v, gh)` is exactly what makes
this multiplicative when the coefficient action is conjugation (`hconj`). -/
def foxGlue (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) : WordLift A B →* B where
  toFun p := ι p.u * p.g
  map_one' := by
    show ι (0 : A) * 1 = 1
    rw [iota_zero hι, mul_one]
  map_mul' p q := by
    show ι (p.u + p.g • q.u) * (p.g * q.g) = (ι p.u * p.g) * (ι q.u * q.g)
    rw [hι, ← hconj p.g q.u]
    group

@[simp] theorem foxGlue_apply (ι : A → B) (hι) (hconj) (p : WordLift A B) :
    foxGlue ι hι hconj p = ι p.u * p.g := rfl

variable [Finite A] [Finite B]

/-- **The literal defect formula** (packet Prop. 4.1, main display): evaluating any word at the
shifted generator lifts `g ↦ ι (a g) · b g` multiplies the evaluation at the base lifts `b` on
the left by `ι` of the Fox derivative.  This is exact for arbitrary offsets — `A` is abelian —
and holds for *every* word, relator or not; the packet's `e ↦ e + d¹_{R,ρ}(a)` is the
specialization `foxDefect_shift`. -/
theorem foxDefect_eq (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B) (a : X → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    PWord.evalFin (fun g => ι (a g) * b g) E E₂ w
      = ι (foxD b a E E₂ w) * PWord.evalFin b E E₂ w := by
  have h := PWord.map_evalFin (foxGlue ι hι hconj) (foxLift b a) E E₂ w
  have hcomp : (fun g => foxGlue ι hι hconj (foxLift b a g)) = fun g => ι (a g) * b g := rfl
  rw [hcomp] at h
  rw [← h, foxGlue_apply]
  show ι (foxEval b a E E₂ w).u * (foxEval b a E E₂ w).g = _
  rw [foxEval_g]
  rfl

/-- **The defect shifts by `d¹(a)`** (packet Prop. 4.1): if the base lifts have defect `ι e` at
a relator `R`, the shifted lifts have defect `ι (foxD(a) + e)`. -/
theorem foxDefect_shift (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B) (a : X → A)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {R : PWord X} {e : A}
    (he : PWord.evalFin b E E₂ R = ι e) :
    PWord.evalFin (fun g => ι (a g) * b g) E E₂ R = ι (foxD b a E E₂ R + e) := by
  rw [foxDefect_eq ι hι hconj, he, hι]

omit [AddCommGroup A] [DistribMulAction B A] [Finite A] in
/-- **Defect witnesses exist**: if the marking below (through `π`) kills a relator, the relator
value at any generator lifts lies in the kernel of `π`, hence in the image of `ι`
(surjectivity of `ι` onto the kernel supplied as `hrange`).  This is where "`ρ` is a
homomorphism" enters the packet's setup. -/
theorem exists_foxDefect {C : Type*} [Group C] (π : B →* C) (ι : A → B)
    (hrange : ∀ x : B, π x = 1 → ∃ v : A, ι v = x) (b : X → B) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) {R : PWord X} (hR : PWord.evalFin (fun g => π (b g)) E E₂ R = 1) :
    ∃ e : A, ι e = PWord.evalFin b E E₂ R := by
  refine hrange _ ?_
  rw [PWord.map_evalFin π b E E₂ R, hR]

omit [DistribMulAction B A] [Finite A] [Finite B] in
private theorem iota_eq_one_iff {ι : A → B} (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hinj : Function.Injective ι) {v : A} : ι v = 1 ↔ v = 0 := by
  constructor
  · intro h
    exact hinj (h.trans (iota_zero hι).symm)
  · rintro rfl
    exact iota_zero hι

/-- **The lifting criterion** (packet Prop. 4.1(1), range form): the two relations hold at some
shifted lift of `b` if and only if the defect `(e₁, e₂)` lies in the range of the evaluated
Jacobian.  ("An affine equation `d¹(a) = −e` is solvable exactly when `[e] = 0` in the
cokernel"; the sign disappears because the range is a subgroup.) -/
theorem foxLifts_iff (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hinj : Function.Injective ι)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {R₁ R₂ : PWord X} {e₁ e₂ : A}
    (he₁ : PWord.evalFin b E E₂ R₁ = ι e₁) (he₂ : PWord.evalFin b E E₂ R₂ = ι e₂) :
    (∃ a : X → A, PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₁ = 1
        ∧ PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₂ = 1)
      ↔ (e₁, e₂) ∈ (foxJacobian b E E₂ R₁ R₂).range := by
  have key : ∀ a : X → A,
      (PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₁ = 1
        ∧ PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₂ = 1)
      ↔ foxJacobian b E E₂ R₁ R₂ a = -(e₁, e₂) := by
    intro a
    rw [foxDefect_shift ι hι hconj b a E E₂ he₁, foxDefect_shift ι hι hconj b a E E₂ he₂,
      iota_eq_one_iff hι hinj, iota_eq_one_iff hι hinj, foxJacobian_apply, Prod.neg_mk,
      Prod.mk.injEq]
    constructor
    · rintro ⟨h₁, h₂⟩
      exact ⟨eq_neg_of_add_eq_zero_left h₁, eq_neg_of_add_eq_zero_left h₂⟩
    · rintro ⟨h₁, h₂⟩
      constructor
      · rw [h₁]
        abel
      · rw [h₂]
        abel
  constructor
  · rintro ⟨a, ha⟩
    have hmem : -(e₁, e₂) ∈ (foxJacobian b E E₂ R₁ R₂).range :=
      AddMonoidHom.mem_range.mpr ⟨a, (key a).mp ha⟩
    simpa using neg_mem hmem
  · intro h
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp h
    exact ⟨-a, (key (-a)).mpr (by rw [map_neg, ha])⟩

/-- **The lifting criterion, cokernel form** (packet Prop. 4.1(1) verbatim): a lift exists iff
the defect class vanishes in `coker d¹_{R,ρ} = (A × A) ⧸ im d¹`. -/
theorem foxLifts_iff_coker (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hinj : Function.Injective ι)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {R₁ R₂ : PWord X} {e₁ e₂ : A}
    (he₁ : PWord.evalFin b E E₂ R₁ = ι e₁) (he₂ : PWord.evalFin b E E₂ R₂ = ι e₂) :
    (∃ a : X → A, PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₁ = 1
        ∧ PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₂ = 1)
      ↔ (QuotientAddGroup.mk (e₁, e₂)
          : (A × A) ⧸ (foxJacobian b E E₂ R₁ R₂).range) = 0 :=
  (foxLifts_iff ι hι hinj hconj b E E₂ he₁ he₂).trans
    (QuotientAddGroup.eq_zero_iff _).symm

/-- **The torsor, half 1** (packet Prop. 4.1(2)): two offset solutions of the two relations
differ by an element of `ker d¹_{R,ρ}`. -/
theorem foxSolution_sub_mem_ker (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hinj : Function.Injective ι)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {R₁ R₂ : PWord X} {a a' : X → A}
    (ha₁ : PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₁ = 1)
    (ha₂ : PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₂ = 1)
    (ha'₁ : PWord.evalFin (fun g => ι (a' g) * b g) E E₂ R₁ = 1)
    (ha'₂ : PWord.evalFin (fun g => ι (a' g) * b g) E E₂ R₂ = 1) :
    a - a' ∈ (foxJacobian b E E₂ R₁ R₂).ker := by
  have cancel : ∀ {R : PWord X},
      PWord.evalFin (fun g => ι (a g) * b g) E E₂ R = 1 →
      PWord.evalFin (fun g => ι (a' g) * b g) E E₂ R = 1 →
      foxD b a E E₂ R - foxD b a' E E₂ R = 0 := by
    intro R h h'
    rw [foxDefect_eq ι hι hconj] at h h'
    have hval : ι (foxD b a E E₂ R) = ι (foxD b a' E E₂ R) :=
      mul_right_cancel (h.trans h'.symm)
    rw [hinj hval, sub_self]
  rw [AddMonoidHom.mem_ker, map_sub, foxJacobian_apply, foxJacobian_apply, Prod.mk_sub_mk,
    Prod.mk_eq_zero]
  exact ⟨cancel ha₁ ha'₁, cancel ha₂ ha'₂⟩

/-- **The torsor, half 2** (packet Prop. 4.1(2)): translating an offset solution by an element
of `ker d¹_{R,ρ}` yields an offset solution; with `foxSolution_sub_mem_ker`, the nonempty
solution set is a torsor under `ker d¹_{R,ρ}`. -/
theorem foxSolution_add_ker (ι : A → B) (hι : ∀ v w : A, ι (v + w) = ι v * ι w)
    (hconj : ∀ (b : B) (v : A), b * ι v * b⁻¹ = ι (b • v)) (b : X → B)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {R₁ R₂ : PWord X} {a c : X → A}
    (ha₁ : PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₁ = 1)
    (ha₂ : PWord.evalFin (fun g => ι (a g) * b g) E E₂ R₂ = 1)
    (hc : c ∈ (foxJacobian b E E₂ R₁ R₂).ker) :
    PWord.evalFin (fun g => ι ((a + c) g) * b g) E E₂ R₁ = 1
      ∧ PWord.evalFin (fun g => ι ((a + c) g) * b g) E E₂ R₂ = 1 := by
  rw [AddMonoidHom.mem_ker, foxJacobian_apply, Prod.mk_eq_zero] at hc
  constructor
  · rw [foxDefect_eq ι hι hconj, foxD_add, hc.1, add_zero, ← foxDefect_eq ι hι hconj]
    exact ha₁
  · rw [foxDefect_eq ι hι hconj, foxD_add, hc.2, add_zero, ← foxDefect_eq ι hι hconj]
    exact ha₂

end Defect

/-! ### Descent: computing `d¹` through `ρ`

The conjugation action of `B` on the abelian kernel factors through `C`; the packet's
`d¹_{R,ρ}` is the Jacobian with coefficients read through `ρ`.  `foxD_comp_hom` is the
change of base along any action-compatible homomorphism — apply it to `π : B →* C`. -/

section Descent

variable {X : Type*} {B C : Type*} [Group B] [Group C] {A : Type*} [AddCommGroup A]
  [DistribMulAction B A] [DistribMulAction C A]

/-- The base-change homomorphism `A ⋊ B →* A ⋊ C` along an action-compatible `f : B →* C`. -/
def wordLiftMapBase (f : B →* C) (hf : ∀ (x : B) (v : A), x • v = f x • v) :
    WordLift A B →* WordLift A C where
  toFun p := ⟨p.u, f p.g⟩
  map_one' := by
    show (⟨(1 : WordLift A B).u, f (1 : WordLift A B).g⟩ : WordLift A C) = 1
    rw [WordLift.one_u, WordLift.one_g, map_one]
    rfl
  map_mul' p q := by
    show (⟨(p * q).u, f (p * q).g⟩ : WordLift A C)
        = (⟨p.u, f p.g⟩ : WordLift A C) * ⟨q.u, f q.g⟩
    rw [WordLift.mul_u, WordLift.mul_g, map_mul]
    exact WordLift.ext (by rw [WordLift.mul_u, hf]) rfl

@[simp] theorem wordLiftMapBase_u (f : B →* C) (hf) (p : WordLift A B) :
    (wordLiftMapBase f hf p).u = p.u := rfl

@[simp] theorem wordLiftMapBase_g (f : B →* C) (hf) (p : WordLift A B) :
    (wordLiftMapBase f hf p).g = f p.g := rfl

variable [Finite A] [Finite B] [Finite C]

omit [Finite C] in
/-- **Descent of the Fox derivative along the extension map**: the derivative with coefficients
acted on through `B` equals the derivative through the image marking whenever the action
factors (the abelian-kernel situation of packet §4).  Consequently `d¹` can be evaluated
through `ρ`, as the packet writes it. -/
theorem foxD_comp_hom (f : B →* C) (hf : ∀ (x : B) (v : A), x • v = f x • v) (b : X → B)
    (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    foxD b a E E₂ w = foxD (fun g => f (b g)) a E E₂ w := by
  have h := PWord.map_evalFin (wordLiftMapBase f hf) (foxLift b a) E E₂ w
  have hcomp : (fun g => wordLiftMapBase f hf (foxLift b a g))
      = foxLift (fun g => f (b g)) a := rfl
  rw [hcomp] at h
  rw [foxD_def, foxD_def, foxEval_def, foxEval_def, ← h]
  rfl

/-- Descent of the whole Jacobian: `d¹` computed over `B` is `d¹` computed through the image
marking. -/
theorem foxJacobian_comp_hom (f : B →* C) (hf : ∀ (x : B) (v : A), x • v = f x • v)
    (b : X → B) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (R₁ R₂ : PWord X) :
    foxJacobian (A := A) b E E₂ R₁ R₂ = foxJacobian (A := A) (fun g => f (b g)) E E₂ R₁ R₂ := by
  refine AddMonoidHom.ext fun a => ?_
  show (foxD b a E E₂ R₁, foxD b a E E₂ R₂)
      = (foxD (fun g => f (b g)) a E E₂ R₁, foxD (fun g => f (b g)) a E E₂ R₂)
  rw [foxD_comp_hom f hf b a E E₂ R₁, foxD_comp_hom f hf b a E E₂ R₂]

end Descent

/-! ## Packet Prop. 4.2: admissibility adds no equation -/

section Admissibility

variable {B C : Type*} [Group B] [Group C]

/-- **Preimages of `2`-subgroups under elementary `2`-extensions are `2`-groups** (packet
Prop. 4.2): if the kernel of `π` is elementary (`x² = 1` on the kernel) and `N ≤ C` is a
`2`-group, then `π⁻¹(N)` is a `2`-group — an extension of a `2`-group by an elementary
abelian `2`-group.  No finiteness is needed for the group-theoretic statement. -/
theorem comap_isPGroup_of_elementaryKer (π : B →* C)
    (hker2 : ∀ x : B, π x = 1 → x * x = 1) {N : Subgroup C} (hN : IsPGroup 2 N) :
    IsPGroup 2 (N.comap π) := by
  rintro ⟨x, hx⟩
  obtain ⟨k, hk⟩ := hN ⟨π x, hx⟩
  have hπ : π (x ^ 2 ^ k) = 1 := by
    have h1 : ((⟨π x, hx⟩ : N) : C) ^ 2 ^ k = 1 := by
      rw [← SubmonoidClass.coe_pow, hk, OneMemClass.coe_one]
    rw [map_pow]
    exact h1
  refine ⟨k + 1, ?_⟩
  have hsq : x ^ 2 ^ (k + 1) = 1 := by
    calc x ^ 2 ^ (k + 1) = (x ^ 2 ^ k) * (x ^ 2 ^ k) := by
          rw [pow_succ, pow_mul, pow_two]
      _ = 1 := hker2 _ hπ
  exact Subtype.ext (by rw [SubmonoidClass.coe_pow, OneMemClass.coe_one]; exact hsq)

/-- The preimage of a normal subgroup is normal — the normality half of packet Prop. 4.2
(recorded; it is mathlib's `Subgroup.Normal.comap`). -/
theorem comap_normal (π : B →* C) {N : Subgroup C} (hN : N.Normal) : (N.comap π).Normal :=
  hN.comap π

/-- The preimage contains every lift of every element of `N` — "it is normal in `B` and
contains every lift of every `x_i`" (packet Prop. 4.2).  With
`comap_isPGroup_of_elementaryKer` and `comap_normal` this is the packet's conclusion: the
pro-`2` admissibility condition ("the wild letters land in a pro-`2` normal subgroup") holds
automatically for every choice of lifts, hence **adds no equation** to the elementary lifting
problem of Prop. 4.1. -/
theorem lift_mem_comap (π : B →* C) {N : Subgroup C} {b : B} (hb : π b ∈ N) :
    b ∈ N.comap π :=
  Subgroup.mem_comap.mpr hb

end Admissibility

/-! ## Packet Lem. 4.3: exactness in coefficients, coordinatewise -/

section CoeffExact

variable {X : Type*} {C : Type*} [Group C] {A A' : Type*} [AddCommGroup A] [AddCommGroup A']
  [DistribMulAction C A] [DistribMulAction C A']

/-- **Coefficient naturality of the Fox derivative** (packet Lem. 4.3, the chain-map half): a
`C`-equivariant coefficient map transports the derivative — the differentials of the Fox
complex "are finite sums of action operators", so they commute with equivariant maps.  Proved
by `WordLift` functoriality, once, for all words. -/
theorem foxD_map_coeff [Finite A] [Finite C] (f : A →+ A')
    (hf : ∀ (g : C) (v : A), f (g • v) = g • f v) (t : X → C) (a : X → A) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    foxD t (fun g => f (a g)) E E₂ w = f (foxD t a E E₂ w) := by
  have h := PWord.map_evalFin (WordLift.map f hf) (foxLift t a) E E₂ w
  have hcomp : (fun g => WordLift.map f hf (foxLift t a g))
      = foxLift t (fun g => f (a g)) := rfl
  rw [hcomp] at h
  rw [foxD_def, foxD_def, foxEval_def, foxEval_def, ← h]
  rfl

/-- Coefficient naturality of the coboundary `d⁰` (no finiteness needed). -/
theorem foxD0_map_coeff (f : A →+ A') (hf : ∀ (g : C) (v : A), f (g • v) = g • f v)
    (t : X → C) (v : A) : foxD0 t (f v) = fun g => f (foxD0 t v g) := by
  funext g
  show t g • f v - f v = f (t g • v - v)
  rw [map_sub, hf]

/-- **Coefficient naturality of the Jacobian** (packet Lem. 4.3): the square
`d¹ ∘ (f ∘ ·) = (f × f) ∘ d¹` commutes for every equivariant `f` — naturality of the defect
construction in the coefficient module. -/
theorem foxJacobian_map_coeff [Finite A] [Finite A'] [Finite C] (f : A →+ A')
    (hf : ∀ (g : C) (v : A), f (g • v) = g • f v) (t : X → C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (R₁ R₂ : PWord X) (a : X → A) :
    foxJacobian t E E₂ R₁ R₂ (fun g => f (a g))
      = Prod.map f f (foxJacobian t E E₂ R₁ R₂ a) := by
  refine Prod.ext ?_ ?_
  · show foxD t (fun g => f (a g)) E E₂ R₁ = f (foxD t a E E₂ R₁)
    exact foxD_map_coeff f hf t a E E₂ R₁
  · show foxD t (fun g => f (a g)) E E₂ R₂ = f (foxD t a E E₂ R₂)
    exact foxD_map_coeff f hf t a E E₂ R₂

/-! ### Coordinatewise transfer of exactness (the terms are direct powers)

The Fox complex's terms are `A`, `X → A`, and `A × A`; a short exact sequence of coefficient
modules transfers to each term coordinatewise ("Exactness and naturality therefore follow
coordinatewise", packet Lem. 4.3's proof).  These are the generic transfer facts for the middle
term (`X → A`) and the end term (`A × A`); the degree-zero term is the sequence itself. -/

variable {A'' : Type*} [AddCommGroup A'']

/-- Injectivity transfers to the degree-one term coordinatewise. -/
theorem pi_map_injective {f : A' →+ A} (hf : Function.Injective f) :
    Function.Injective (fun (a : X → A') (g : X) => f (a g)) := by
  intro a b hab
  funext g
  exact hf (congrFun hab g)

/-- Surjectivity transfers to the degree-one term coordinatewise. -/
theorem pi_map_surjective {f : A →+ A''} (hf : Function.Surjective f) :
    Function.Surjective (fun (a : X → A) (g : X) => f (a g)) := by
  intro b
  choose s hs using fun g => hf (b g)
  exact ⟨s, funext hs⟩

/-- Exactness at the middle transfers to the degree-one term coordinatewise: a family killed by
the quotient map lifts pointwise along the inclusion. -/
theorem pi_map_exact {f : A' →+ A} {p : A →+ A''}
    (hexact : ∀ v : A, p v = 0 → ∃ w : A', f w = v) (a : X → A) (ha : ∀ g, p (a g) = 0) :
    ∃ a' : X → A', ∀ g, f (a' g) = a g := by
  choose s hs using fun g => hexact (a g) (ha g)
  exact ⟨s, hs⟩

/-- Injectivity transfers to the degree-two term `A × A`. -/
theorem prodMap_injective {f : A' →+ A} (hf : Function.Injective f) :
    Function.Injective (Prod.map f f : A' × A' → A × A) :=
  hf.prodMap hf

/-- Surjectivity transfers to the degree-two term `A × A`. -/
theorem prodMap_surjective {f : A →+ A''} (hf : Function.Surjective f) :
    Function.Surjective (Prod.map f f : A × A → A'' × A'') :=
  hf.prodMap hf

/-- Exactness at the middle transfers to the degree-two term `A × A`. -/
theorem prodMap_exact {f : A' →+ A} {p : A →+ A''}
    (hexact : ∀ v : A, p v = 0 → ∃ w : A', f w = v) (e : A × A)
    (he : Prod.map p p e = 0) : ∃ e' : A' × A', Prod.map f f e' = e := by
  obtain ⟨w₁, hw₁⟩ := hexact e.1 (congrArg Prod.fst he)
  obtain ⟨w₂, hw₂⟩ := hexact e.2 (congrArg Prod.snd he)
  exact ⟨(w₁, w₂), Prod.ext hw₁ hw₂⟩

end CoeffExact

/-! ## Regression: the `n = 1` hand rows (mandatory; plan §3 A1)

The `Γ_A` and `Γ_R` wild relators as `PWord (Generator 1)` trees, mirroring the ledgers of
`GQ2/Words.lean` and `GQ2/Roe/Words.lean` **letter for letter** (same association, same
exponent spellings — `(x₀³)⁻¹` not `x₀⁻³`, `d₀²` as `zpow 2`, matching the machine-readable
App. B block).  Everything below is a regression pin in the sense of plan §3 A1 ("adapters at
`n = 1` cross-check the generic rows against the existing `Γ_A`/`Γ_R` hand rows — regression,
not replacement"); nothing below is cited by a proof. -/

section Regression

/-- `conjR` agrees verbatim with the `ℚ₂` ledger's `conjP` (the one-line crossover promised by
`GQ2/Dyadic/Word/Blocks.lean`'s conventions note; local to the regression). -/
private theorem conjR_eq_conjP {G : Type*} [Group G] (x g : G) :
    conjR x g = _root_.GQ2.conjP x g := rfl

/-- `commR` agrees verbatim with the ledger's `commP`. -/
private theorem commR_eq_commP {G : Type*} [Group G] (x y : G) :
    commR x y = _root_.GQ2.commP x y := rfl

/-- The aux letter `u_i = (x_i τ)^{ω₂}` as a tree (the first factor of `deltaW`). -/
noncomputable def uWordQ2 (i : Fin 2) : PWord (Generator 1) :=
  PWord.omega2Pow (.mul (.gen (.wild i)) (.gen .tau))

/-- `d₀ = u₀ x₀⁻¹` as a tree — definitionally `deltaW 0` of `GQ2/Dyadic/Word/Syntax.lean`. -/
noncomputable def d0WordQ2 : PWord (Generator 1) := deltaW 0

/-- `z₀ = x₀^{σ₂}` as a tree. -/
noncomputable def z0WordQ2 : PWord (Generator 1) := .conj (.gen (.wild 0)) sigma2W

/-- `c₀ = [d₀, z₀]` as a tree. -/
noncomputable def c0WordQ2 : PWord (Generator 1) := .comm d0WordQ2 z0WordQ2

/-- `g₀ = σ₂²` as a tree. -/
noncomputable def g0WordQ2 : PWord (Generator 1) := .zpow sigma2W 2

/-- `d_g = d₀^{g₀}` as a tree. -/
noncomputable def dgWordQ2 : PWord (Generator 1) := .conj d0WordQ2 g0WordQ2

/-- `h_c = [d_g, d₀]` as a tree. -/
noncomputable def hcWordQ2 : PWord (Generator 1) := .comm dgWordQ2 d0WordQ2

/-- `h₀ = (x₀^{g₀})·x₀·d_g·d₀·d₀²·h_c` as a tree (note the bare `d₀` — the App. B block's
`dg*d0*d0^2`; see the erratum note at `GQ2.Marking.h0`). -/
noncomputable def h0WordQ2 : PWord (Generator 1) :=
  .mul (.mul (.mul (.mul (.mul (.conj (.gen (.wild 0)) g0WordQ2) (.gen (.wild 0))) dgWordQ2)
    d0WordQ2) (.zpow d0WordQ2 2)) hcWordQ2

/-- **The `Γ_A` wild relator** `h₀·u₁⁻¹·x₁^σ·c₀` (relation (6)) as a reflected tree. -/
noncomputable def gammaAWildWord : PWord (Generator 1) :=
  .mul (.mul (.mul h0WordQ2 (.inv (uWordQ2 1))) (.conj (.gen (.wild 1)) (.gen .sigma)))
    c0WordQ2

/-- The `Γ_R` aux letter `a = ((x₀³)⁻¹ τ)^{ω₂}` as a tree (the ledger's spelling
`(t.x₀ ^ 3)⁻¹ * t.τ`, not `x₀⁻³`). -/
noncomputable def aRWordQ2 : PWord (Generator 1) :=
  PWord.omega2Pow (.mul (.inv (.zpow (.gen (.wild 0)) 3)) (.gen .tau))

/-- The `Γ_R` letter `y₁ = x₁^{σ₂}` as a tree. -/
noncomputable def y1RWordQ2 : PWord (Generator 1) := .conj (.gen (.wild 1)) sigma2W

/-- The `Γ_R` letter `c = [x₁, y₁]` as a tree. -/
noncomputable def cRWordQ2 : PWord (Generator 1) := .comm (.gen (.wild 1)) y1RWordQ2

/-- **The `Γ_R` wild relator** `(x₀^σ)⁻¹·a·x₁²·c` as a reflected tree.  Per the frozen
selection (`selection-freeze.md` row 1, SQ1) this is also the `n = 1` specialization of the
primary `L_sq` word `R_sq(L,n)` — the base case of lane WL's cross-identification. -/
noncomputable def gammaRWildWord : PWord (Generator 1) :=
  .mul (.mul (.mul (.inv (.conj (.gen (.wild 0)) (.gen .sigma))) aRWordQ2)
    (.zpow (.gen (.wild 1)) 2)) cRWordQ2

variable {G : Type*} [Group G]

/-- **The evaluator computes the `Γ_A` ledger at every marking**: `evalFin` of the reflected
tree at (the `n = 1` adapter of) any `GQ2.Marking` is the ledger's `wildValue`.  Applied at a
lifted marking this is the statement that the generic Fox evaluator reproduces the `Γ_A` wild
row (`foxEval_gammaAWildWord`). -/
theorem evalFin_gammaAWildWord (s : _root_.GQ2.Marking G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (⇑(Marking.ofQ2 s)) E E₂ gammaAWildWord = s.wildValue := by
  simp only [gammaAWildWord, h0WordQ2, hcWordQ2, dgWordQ2, g0WordQ2, c0WordQ2, z0WordQ2,
    d0WordQ2, deltaW, uWordQ2, sigma2W, PWord.evalFin_mul, PWord.evalFin_inv,
    PWord.evalFin_conj, PWord.evalFin_comm, PWord.evalFin_zpow, PWord.evalFin_omega2Pow,
    PWord.evalFin_gen, Marking.apply_sigma, Marking.apply_tau, Marking.apply_wild,
    Marking.ofQ2_σ, Marking.ofQ2_τ, Marking.ofQ2_x_zero, Marking.ofQ2_x_one, zpow_ofNat]
  simp only [_root_.GQ2.Marking.wildValue, _root_.GQ2.Marking.h0, _root_.GQ2.Marking.u1,
    _root_.GQ2.Marking.u0, _root_.GQ2.Marking.u, _root_.GQ2.Marking.d0, _root_.GQ2.Marking.z0,
    _root_.GQ2.Marking.c0, _root_.GQ2.Marking.g0, _root_.GQ2.Marking.dg,
    _root_.GQ2.Marking.hc, _root_.GQ2.Marking.sigma2, conjR_eq_conjP, commR_eq_commP]

/-- **The evaluator computes the `Γ_R` ledger at every marking.**  Per SQ1, this is also the
`L_sq` base-case pin. -/
theorem evalFin_gammaRWildWord (s : _root_.GQ2.Marking G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalFin (⇑(Marking.ofQ2 s)) E E₂ gammaRWildWord = s.wildValueR := by
  simp only [gammaRWildWord, cRWordQ2, y1RWordQ2, aRWordQ2, sigma2W, PWord.evalFin_mul,
    PWord.evalFin_inv, PWord.evalFin_conj, PWord.evalFin_comm, PWord.evalFin_zpow,
    PWord.evalFin_omega2Pow, PWord.evalFin_gen, Marking.apply_sigma, Marking.apply_tau,
    Marking.apply_wild, Marking.ofQ2_σ, Marking.ofQ2_τ, Marking.ofQ2_x_zero,
    Marking.ofQ2_x_one, zpow_ofNat]
  simp only [_root_.GQ2.Marking.wildValueR, _root_.GQ2.Marking.aR, _root_.GQ2.Marking.y1R,
    _root_.GQ2.Marking.cR, _root_.GQ2.Marking.sigma2, conjR_eq_conjP, commR_eq_commP]

/-- The `n = 1` offsets adapter: a `Fin 4` offset vector as a `Generator 1`-indexed family
(`(σ, τ, x₀, x₁) ↦ (x 0, x 1, x 2, x 3)`, matching `GQ2.FoxH.liftMarking`'s slot order). -/
def q2Offsets {V : Type*} (x : Fin 4 → V) : Generator 1 → V :=
  ⇑(Marking.ofQ2 (G := V) ⟨x 0, x 1, x 2, x 3⟩)

variable {C : Type*} [Group C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

omit [Group C] [AddCommGroup V] [DistribMulAction C V] in
/-- The generic lift of the `n = 1` adapter marking **is** the `ℚ₂` development's
`liftMarking` (through the adapter again): `rfl`-level per generator. -/
theorem foxLift_ofQ2 (t : _root_.GQ2.Marking C) (x : Fin 4 → V) :
    foxLift (⇑(Marking.ofQ2 t)) (q2Offsets x) = ⇑(Marking.ofQ2 (FoxH.liftMarking t x)) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | (k + 2), h => exact absurd h (by omega)

/-- **Regression, evaluator level (`Γ_A`)**: the generic Fox evaluation of the reflected `Γ_A`
wild relator at a lifted `n = 1` marking is the hand ledger's `wildValue` at the `ℚ₂`
development's `liftMarking` — offsets and base together, before any triviality hypothesis. -/
theorem foxEval_gammaAWildWord (t : _root_.GQ2.Marking C) (x : Fin 4 → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxEval (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaAWildWord
      = (FoxH.liftMarking t x).wildValue := by
  rw [foxEval_def, foxLift_ofQ2, evalFin_gammaAWildWord]

/-- **Regression, evaluator level (`Γ_R`)**. -/
theorem foxEval_gammaRWildWord (t : _root_.GQ2.Marking C) (x : Fin 4 → V) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxEval (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaRWildWord
      = (FoxH.liftMarking t x).wildValueR := by
  rw [foxEval_def, foxLift_ofQ2, evalFin_gammaRWildWord]

variable [Finite C] [Finite V]

/-- **REGRESSION (mandatory, board WW1): the generic `Γ_A` wild row equals the hand row**
`GQ2.FoxH.liftMarking_wildValue_u` (`GQ2/FoxHeisenberg/WildRow.lean:277`): at a split simple
tame module (`hx0`/`hx1`/`htau` wild-and-inertia triviality, `hU` the `σ₂ = S₂`-identity of a
simple *unramified* module, `hV₂` char 2), the generic Fox derivative of the reflected `Γ_A`
relator is `x₁ + (1 + S⁻¹)·x₃`. -/
theorem foxD_gammaAWildWord_split (t : _root_.GQ2.Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) :
    foxD (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaAWildWord
      = x 1 + x 3 + t.σ⁻¹ • x 3 := by
  rw [foxD_def, foxEval_gammaAWildWord]
  exact FoxH.liftMarking_wildValue_u t x hV₂ hx0 hx1 htau hU

/-- **REGRESSION (mandatory, board WW1): the generic `Γ_R` wild row equals the hand row**
`GQ2.FoxH.liftMarking_wildValueR_u` (`GQ2/Roe/WildRow.lean:219`): at a split simple tame
module the generic Fox derivative of the reflected `Γ_R` relator is `x₁ + (1 + S⁻¹)·x₂` — and,
exactly as in the hand row, **no `σ₂`-tameness hypothesis `hU`** is needed (`σ₂` enters `r_R`
only as a conjugator).  Per SQ1 this is the `L_sq` base-case row for lane WL. -/
theorem foxD_gammaRWildWord_split (t : _root_.GQ2.Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    foxD (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaRWildWord
      = x 1 + x 2 + t.σ⁻¹ • x 2 := by
  rw [foxD_def, foxEval_gammaRWildWord]
  exact FoxH.liftMarking_wildValueR_u t x hV₂ hx0 hx1 htau

/-- **Regression bonus (the ramified `Γ_R` row)**: at a ramified simple module (`V^T = 0`,
`powOmega2 T` trivial) the generic row collapses to `S⁻¹·x₂` — the hand row
`GQ2.FoxH.liftMarking_wildValueR_u_ramified` (display (53)'s `P = 0` reading). -/
theorem foxD_gammaRWildWord_ramified (t : _root_.GQ2.Marking C) (x : Fin 4 → V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    foxD (⇑(Marking.ofQ2 t)) (q2Offsets x) E E₂ gammaRWildWord = t.σ⁻¹ • x 2 := by
  rw [foxD_def, foxEval_gammaRWildWord]
  exact FoxH.liftMarking_wildValueR_u_ramified t x hV₂ hx0 hx1 htau hTodd

end Regression

end GQ2.Dyadic
