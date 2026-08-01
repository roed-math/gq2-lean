/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Count.Presentation
import GQ2.Dyadic.Certificates.N0
import GQ2.Dyadic.Certificates.Npc
import GQ2.Dyadic.Certificates.M0
import GQ2.Dyadic.Certificates.MpcStokes
import GQ2.Dyadic.Certificates.L

/-!
# Discharging `ResolvesGammaRelators` at the five frozen branch families (ticket CB-RES)

CB-MP built the restricted class `Count.IsAdmissibleMarkedPresentation` and its instance
`Count.isAdmissibleMarkedPresentation_gammaR` for `GammaR n q R`, leaving exactly one hypothesis
undischarged: `Count.ResolvesGammaRelators n q R w`, the seam CB-1 first flagged.  This file is
the word-lane work that hypothesis asks for, for the five frozen branch families.

## The reduction (§1–§2)

`heisToFree` **is** `PWord.evalZ FreeGroup.of`, and `PWord.evalZ` is natural for every monoid
hom (`PWord.map_evalZ`, no topology and no finiteness).  So

```
freeToProf (heisToFree E E₂ w) = PWord.evalZ ⇑(freeMarking n) E E₂ w
```

on the nose (`freeToProf_heisToFree`), while `(freeMarking n).eval R` is `PWord.eval` — the
*profinite* denotation.  Both of CB-MP's two equations are therefore one and the same statement:
**the integer-resolved denotation agrees with the profinite denotation, at the free profinite
marking**.  `PWord.eval_eq_evalZ` reduces that to F2's `PWord.ResolvedAt`.

* the **tame** equation is generic and needs no resolver at all: `tameRelW` carries no profinite
  exponent, so `ResolvedAt` holds by `trivial` and the equation is
  `freeToProf_heisToFree_tameRelWord`, proved **once** for all five branches (§2);
* the **wild** equation is `ResolvedAt ⇑(freeMarking n) (const e) (const e) R`, i.e. it asks for
  `Y ^ᶻ ω₂ = Y ^ e` **in the free profinite group** at the bases `Y` of the word's `ω₂`-nodes.

## The verdict (§4–§6): the wild equation is false at every one of the five

§4 builds the finite cyclic characters `degHom n m g₀ : F →  ℤ/m` (letter `g₀ ↦ 1`, every other
letter `↦ 0`) and computes both denotations through them.  §5 is the obstruction:

> `zpowHat_omega2_ne_zpow`: for `Y ∈ F` of degree `1` in some letter, `Y ^ᶻ ω₂ ≠ Y ^ k` for
> **every** integer `k`.

The proof is two congruences on `omega2Exp` and no case analysis: `omega2Exp (2 ^ a) = 1` forces
`k ≡ 1 mod 2 ^ a` for every `a`, hence `k = 1`; `omega2Exp 3 = 0` then forces `3 ∣ 1`.  Both are
kernel computations from the definition of `omega2Exp`.

Each of the five frozen words has such a node — `(x₂τ)^{ω₂}` for the two `N` rows,
`σ₂ = σ^{ω₂}` for `L_sq` and the two `M` rows — so §6 refutes `ResolvedAt` at all five, for
**every** resolver `e`, not just the frozen `e = 3`.  §7 upgrades this from "the sufficient
condition fails" to "the equation itself fails", and indeed to the failure of
`ResolvesGammaRelators.fam_mem`, at the compact-`N` pilot: the character into `ℤ/4` kills both
relators and does not kill `freeToProf (nCompactFam α h q e 1)` whenever `e ≢ 1 mod 4`.

⚠ The refuting character lands in a **`2`-group**.  Unlike CB-W's `ℤ/3` counterexamples to the
plain clause (iii), this obstruction is *not* removed by CB-MP's admissibility restriction.

## What is provable instead (§3)

`GammaR n q R` is parametric in `R`, and the count lane gets to choose it.  `resolveWord E E₂ R`
is `R` with every profinite exponent replaced by its integer resolver, and

```
freeToProf (heisToFree E E₂ w) = (freeMarking n).eval (resolveWord E E₂ w)
```

holds unconditionally (`freeToProf_heisToFree_resolveWord`).  So all five families **do** resolve
the relators of `Γ_{resolveWord e R}` — §3's five theorems — the group presented by the *resolved*
relator, which is the object the Fox/Stokes certificate lane has been computing with throughout.
Whether that group is the intended `Γ_R` is a mathematical question about the presentation, not a
Lean one, and it is the count lane's remaining open item.

## Axiom posture

`sorry`-free, **no new axiom**; every headline `#print axioms` is the standard three.  The
`decide`s are kernel `decide`s on `omega2Exp` at the literal moduli `3` and `4` and in `ℤ/4`.
-/

namespace GQ2.Dyadic

namespace Count

open GQ2 GQ2.Dyadic

/-! ## §1 The reduction: both equations are one denotational agreement

`heisToFree` resolves the exponents *before* reading the word in `FreeGroup`; `freeToProf` then
carries it into `F`.  Because `PWord.evalZ` is natural, the composite is the integer-resolved
denotation read directly in `F`. -/

section Reduction

variable {n : ℕ}

/-- **`freeToProf` of a resolved word is the integer-exponent denotation at the free marking.**
The word lane's `FreeGroup` detour is invisible: `PWord.map_evalZ` needs no topology and no
finiteness, so this holds for every resolver pair. -/
theorem freeToProf_heisToFree (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord (Generator n)) :
    freeToProf (Generator n) (heisToFree E E₂ w)
      = PWord.evalZ (⇑(freeMarking n)) E E₂ w := by
  rw [heisToFree, PWord.map_evalZ (freeToProf (Generator n)) FreeGroup.of E E₂ w]
  rfl

/-- **The seam, reduced to `ResolvedAt`.**  CB-MP's two equations differ only in which word they
are applied to; each is exactly "the integer resolvers compute this word's profinite exponents,
at the free profinite marking". -/
theorem freeToProf_heisToFree_eq_eval {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
    {w : PWord (Generator n)} (hw : PWord.ResolvedAt (⇑(freeMarking n)) E E₂ w) :
    freeToProf (Generator n) (heisToFree E E₂ w) = (freeMarking n).eval w := by
  rw [freeToProf_heisToFree, Marking.eval_def, PWord.eval_eq_evalZ _ E E₂ w hw]

end Reduction

/-! ## §2 The tame equation, once for all five branches

`tameRelW` is `τ^σ · (τ^q)⁻¹`: `mul`, `conj`, `inv`, `zpow`, and no profinite exponent anywhere.
So `ResolvedAt` is `trivial` at every node and the equation holds for **every** resolver pair, at
every degree and every `q`.  Both certificate lanes spell the same body — `Certificates.tameRelW`
and `Certificates.Npc.tameRelW` are distinct constants with identical definitions — so the
statement is made about the body and the two lanes are `rfl`-corollaries. -/

section Tame

variable {n : ℕ}

/-- The tame relator word, spelled out.  Definitionally both lanes' `tameRelW`. -/
def tameRelWord (n q : ℕ) : PWord (Generator n) :=
  .mul (.conj (.gen .tau) (.gen .sigma)) (.inv (.zpow (.gen .tau) (q : ℤ)))

theorem tameRelWord_eq (n q : ℕ) : tameRelWord n q = Certificates.tameRelW n q := rfl

theorem tameRelWord_eq_npc (n q : ℕ) : tameRelWord n q = Certificates.Npc.tameRelW n q := rfl

/-- The tame relator carries no profinite exponent, so every resolver pair resolves it. -/
theorem resolvedAt_tameRelWord {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (μ : Generator n → G) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (q : ℕ) : PWord.ResolvedAt μ E E₂ (tameRelWord n q) :=
  ⟨⟨trivial, trivial⟩, trivial⟩

/-- **The tame equation** — `h0` of CB-MP's `ResolvesGammaRelators.of_two`, generically. -/
theorem freeToProf_heisToFree_tameRelWord (n q : ℕ) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    freeToProf (Generator n) (heisToFree E E₂ (tameRelWord n q)) = tameRelatorGen n q :=
  (freeToProf_heisToFree_eq_eval (resolvedAt_tameRelWord _ E E₂ q)).trans
    (Certificates.freeMarking_eval_tameRelW n q)

end Tame

/-! ## §3 The wild equation at the resolved relator

`resolveWord E E₂ R` replaces every `profPow`/`z2pow` node of `R` by the `zpow` at its resolver.
Its profinite denotation *is* the integer-resolved denotation of `R` — no hypothesis at all — so
the wild equation holds at `resolveWord E E₂ R` for every word and every resolver pair. -/

section Resolved

variable {n : ℕ}

/-- **The resolved word**: every profinite and `2`-adic exponent replaced by its integer
resolver. -/
def resolveWord (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord (Generator n) → PWord (Generator n)
  | .one => .one
  | .gen g => .gen g
  | .mul u v => .mul (resolveWord E E₂ u) (resolveWord E E₂ v)
  | .inv u => .inv (resolveWord E E₂ u)
  | .conj u g => .conj (resolveWord E E₂ u) (resolveWord E E₂ g)
  | .comm u v => .comm (resolveWord E E₂ u) (resolveWord E E₂ v)
  | .zpow u k => .zpow (resolveWord E E₂ u) k
  | .z2pow u z => .zpow (resolveWord E E₂ u) (E₂ z)
  | .profPow u γ => .zpow (resolveWord E E₂ u) (E γ)

/-- The profinite denotation of the resolved word is the integer-exponent denotation of the
original.  No topology hypothesis beyond the ambient profinite target, and no `ResolvedAt`. -/
theorem eval_resolveWord {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (μ : Generator n → G) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord (Generator n)) :
    PWord.eval μ (resolveWord E E₂ w) = PWord.evalZ μ E E₂ w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [resolveWord, PWord.eval_mul, PWord.evalZ_mul, ihu, ihv]
  | inv u ih => rw [resolveWord, PWord.eval_inv, PWord.evalZ_inv, ih]
  | conj u g ihu ihg => rw [resolveWord, PWord.eval_conj, PWord.evalZ_conj, ihu, ihg]
  | comm u v ihu ihv => rw [resolveWord, PWord.eval_comm, PWord.evalZ_comm, ihu, ihv]
  | zpow u k ih => rw [resolveWord, PWord.eval_zpow, PWord.evalZ_zpow, ih]
  | z2pow u z ih => rw [resolveWord, PWord.eval_zpow, PWord.evalZ_z2pow, ih]
  | profPow u γ ih => rw [resolveWord, PWord.eval_zpow, PWord.evalZ_profPow, ih]

/-- **The wild equation, at the resolved relator** — `h1` of `ResolvesGammaRelators.of_two`,
unconditionally. -/
theorem freeToProf_heisToFree_resolveWord (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (w : PWord (Generator n)) :
    freeToProf (Generator n) (heisToFree E E₂ w)
      = (freeMarking n).eval (resolveWord E E₂ w) := by
  rw [freeToProf_heisToFree, Marking.eval_def, eval_resolveWord]

end Resolved

/-! ### The five frozen families, discharged at the resolved relator

Each family is `![heisToFree (const e) (const e) (tameRelW …), heisToFree (const e) (const e) R]`,
so §2 gives the tame half and §3 the wild half with `R` read as `resolveWord (const e) (const e)`
of the frozen branch word.  Nothing here is conditional: these are the count lane's five
`ResolvesGammaRelators` values, at the presentation whose wild relator is the resolved word. -/

section FrozenResolved

/-- The constant resolver at `e`, the one every frozen family uses. -/
def constRes (e : ℕ) : Zhat → ℤ := fun _ => (e : ℤ)

/-- Its `ℤ₂` twin. -/
def constRes₂ (e : ℕ) : ℤ_[2] → ℤ := fun _ => (e : ℤ)

/-- The resolved wild relator of a branch word at the constant resolver `e`. -/
def resolvedRelator (e : ℕ) {n : ℕ} (R : PWord (Generator n)) : PWord (Generator n) :=
  resolveWord (constRes e) (constRes₂ e) R

/-- **Compact `N` resolves the relators of the resolved presentation.** -/
theorem resolves_nCompactFam (α h q e : ℕ) :
    ResolvesGammaRelators (2 + 2 * h) q (resolvedRelator e (Words.nCompactW α h))
      (Certificates.nCompactFam α h q e) :=
  ResolvesGammaRelators.of_two (freeToProf_heisToFree_tameRelWord _ q _ _)
    (freeToProf_heisToFree_resolveWord _ _ _)

/-- **Procyclic `N`.** -/
theorem resolves_npcFam (α r h q e : ℕ) (d : EtaData) :
    ResolvesGammaRelators (2 + 2 * h) q (resolvedRelator e (Words.Npc.npcW α r h d))
      (Certificates.Npc.npcFam α r h q e d) :=
  ResolvesGammaRelators.of_two (freeToProf_heisToFree_tameRelWord _ q _ _)
    (freeToProf_heisToFree_resolveWord _ _ _)

/-- **Compact `M`.** -/
theorem resolves_mCompactFam (α h q e : ℕ) :
    ResolvesGammaRelators (2 + 2 * h) q (resolvedRelator e (Words.MCompact.mCompactW α h))
      (Certificates.MCompact.mCompactFam α h q e) :=
  ResolvesGammaRelators.of_two (freeToProf_heisToFree_tameRelWord _ q _ _)
    (freeToProf_heisToFree_resolveWord _ _ _)

/-- **Procyclic `M`.** -/
theorem resolves_mpcFam (α r pp h q e : ℕ) (η : Words.Mpc.EtaDisplay) :
    ResolvesGammaRelators (2 + 2 * h) q (resolvedRelator e (Words.Mpc.mpcW α r pp η h))
      (Certificates.MProcyclic.mpcFam α r pp h q e η) :=
  ResolvesGammaRelators.of_two (freeToProf_heisToFree_tameRelWord _ q _ _)
    (freeToProf_heisToFree_resolveWord _ _ _)

/-- **`L_sq`.** -/
theorem resolves_lSqFam (h q e : ℕ) :
    ResolvesGammaRelators (2 * h + 1) q (resolvedRelator e (Words.LSq.lSqW h))
      (Certificates.LSqStokes.lSqFam h q e) :=
  ResolvesGammaRelators.of_two (freeToProf_heisToFree_tameRelWord _ q _ _)
    (freeToProf_heisToFree_resolveWord _ _ _)

end FrozenResolved

/-! ## §4 Cyclic characters of the free profinite group

`degHom n m g₀` is the classifying map of the marking "`g₀ ↦ 1`, every other letter `↦ 0`" into
`ℤ/m` written multiplicatively.  It is the only external device §5 needs: `zpowHat` is natural for
continuous homomorphisms (`GQ2.map_zpowHat`) and computable in a finite group
(`PWord.zpowHat_omega2_zpow`), so a `ℤ̂`-exponent upstairs becomes an ordinary residue
downstairs. -/

section Characters

/-- The cyclic test target `ℤ/m`, multiplicatively and discretely — a finite discrete group, so
`ProfiniteGrp.of` accepts it and `PWord.eval` is available. -/
def CycTest (m : ℕ) : Type := Multiplicative (ZMod m)

namespace CycTest

instance (m : ℕ) : CommGroup (CycTest m) :=
  inferInstanceAs (CommGroup (Multiplicative (ZMod m)))

instance (m : ℕ) : TopologicalSpace (CycTest m) := ⊥

instance (m : ℕ) : DiscreteTopology (CycTest m) := ⟨rfl⟩

instance (m : ℕ) [NeZero m] : Finite (CycTest m) :=
  inferInstanceAs (Finite (Multiplicative (ZMod m)))

instance (m : ℕ) : DecidableEq (CycTest m) :=
  inferInstanceAs (DecidableEq (Multiplicative (ZMod m)))

/-- The chosen generator `1 ∈ ℤ/m`. -/
def gen (m : ℕ) : CycTest m := Multiplicative.ofAdd 1

/-- Integer powers of the generator are the residues. -/
theorem gen_zpow (m : ℕ) (j : ℤ) :
    gen m ^ j = (Multiplicative.ofAdd (j : ZMod m) : CycTest m) := by
  show (Multiplicative.ofAdd (1 : ZMod m)) ^ j = _
  rw [← ofAdd_zsmul, zsmul_eq_mul, mul_one]

/-- Two integer powers of the generator agree exactly on residues. -/
theorem gen_zpow_inj {m : ℕ} {j l : ℤ} (h : gen m ^ j = gen m ^ l) :
    (j : ZMod m) = (l : ZMod m) := by
  rw [gen_zpow, gen_zpow] at h
  exact Multiplicative.ofAdd.injective h

/-- The generator is killed by `m`, so its order divides `m`. -/
theorem orderOf_gen_dvd (m : ℕ) : orderOf (gen m) ∣ m := by
  refine orderOf_dvd_of_pow_eq_one ?_
  have h : gen m ^ (m : ℤ) = (Multiplicative.ofAdd ((m : ℕ) : ZMod m) : CycTest m) := by
    rw [gen_zpow]; norm_cast
  rw [← zpow_natCast, h, ZMod.natCast_self]
  rfl

end CycTest

variable {n : ℕ}

/-- The **degree marking** in the letter `g₀`: `g₀ ↦ 1`, every other letter `↦ 0`. -/
def degMark (n m : ℕ) (g₀ : Generator n) : Generator n → CycTest m :=
  fun g => if g = g₀ then CycTest.gen m else 1

@[simp] theorem degMark_self (m : ℕ) (g₀ : Generator n) :
    degMark n m g₀ g₀ = CycTest.gen m := if_pos rfl

@[simp] theorem degMark_of_ne {m : ℕ} {g g₀ : Generator n} (h : g ≠ g₀) :
    degMark n m g₀ g = 1 := if_neg h

/-- The classifying continuous hom of the degree marking, at the plain carrier instances (the
type ascription is load-bearing, exactly as for `Count.testBaseHom`). -/
noncomputable def degHom (n m : ℕ) [NeZero m] (g₀ : Generator n) :
    ContinuousMonoidHom ((FreeProfiniteGroup (Generator n)) : Type) (CycTest m) :=
  ((FreeProfiniteGroup.homEquiv (Generator n) (ProfiniteGrp.of (CycTest m))).symm
    (degMark n m g₀)).hom

@[simp] theorem degHom_of (m : ℕ) [NeZero m] (g₀ g : Generator n) :
    degHom n m g₀ (FreeProfiniteGroup.of g) = degMark n m g₀ g :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem freeMarking_map_degHom (m : ℕ) [NeZero m] (g₀ : Generator n) :
    (freeMarking n).map ⇑(degHom n m g₀) = ⟨degMark n m g₀⟩ := by
  ext g
  exact degHom_of m g₀ g

end Characters

/-! ## §5 The obstruction: no integer resolves `ω₂` in the free profinite group

`ω₂ ∈ ℤ̂` is the idempotent that is `1` on the `2`-part and `0` on the odd part.  An integer that
agreed with it would have to be `≡ 1` modulo every power of `2` — hence be `1` — and `≡ 0` modulo
`3`.  Both halves are read off `omega2Exp` through the characters of §4, and the conclusion holds
for **every** integer, so no choice of resolver `e` can repair it. -/

section Obstruction

variable {n : ℕ}

/-- An element of `F` is **degree one in `g₀`** if every cyclic character in `g₀` sends it to the
generator.  The value of an `ω₂`-node base of every frozen branch word is of this shape. -/
def IsDegOne (g₀ : Generator n) (Y : ((FreeProfiniteGroup (Generator n)) : Type)) : Prop :=
  ∀ (m : ℕ) [NeZero m], degHom n m g₀ Y = CycTest.gen m

/-- `ω₂` is `≡ 1` on every power of `2`. -/
theorem omega2Exp_two_pow_modEq_one {a : ℕ} (ha : a ≠ 0) :
    omega2Exp (2 ^ a) ≡ 1 [MOD 2 ^ a] := by
  have hfac : (2 ^ a).factorization 2 = a := by
    rw [Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same]
  have h := omega2Exp_modEq_one (n := 2 ^ a) (by positivity) (by rw [hfac]; exact ha)
  rwa [hfac] at h

/-- `ω₂` is `≡ 0` on the odd part — at the modulus `3`, `3 ∣ omega2Exp 3`. -/
theorem three_dvd_omega2Exp_three : 3 ∣ omega2Exp 3 := by
  have hfac : (3 : ℕ).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by norm_num)
  have h := oddPart_dvd_omega2Exp 3
  rwa [hfac, pow_zero, Nat.div_one] at h

/-- The residue of `ω₂` at a character, read off the character's own modulus. -/
theorem degHom_zpowHat_omega2 (m : ℕ) [NeZero m] (g₀ : Generator n)
    {Y : ((FreeProfiniteGroup (Generator n)) : Type)} (hY : IsDegOne g₀ Y) :
    degHom n m g₀ (Y ^ᶻ omega2) = CycTest.gen m ^ (omega2Exp m : ℤ) := by
  rw [map_zpowHat, hY m,
    PWord.zpowHat_omega2_zpow (NeZero.ne m) (CycTest.orderOf_gen_dvd m)]

/-- **No integer resolves `ω₂`.**  For a degree-one element of the free profinite group,
`Y ^ᶻ ω₂ ≠ Y ^ k` for every integer `k` — so `PWord.ResolvedAt` can never hold at an `ω₂`-node
whose base is degree one, at *any* resolver.

The two congruences are `omega2Exp (2 ^ a) ≡ 1` and `3 ∣ omega2Exp 3`; nothing else enters. -/
theorem zpowHat_omega2_ne_zpow {g₀ : Generator n}
    {Y : ((FreeProfiniteGroup (Generator n)) : Type)} (hY : IsDegOne g₀ Y) (k : ℤ) :
    Y ^ᶻ omega2 ≠ Y ^ k := by
  intro hres
  -- every character equates the residue of `ω₂` with that of `k`
  have key : ∀ (m : ℕ) [NeZero m], ((omega2Exp m : ℤ) : ZMod m) = (k : ZMod m) := by
    intro m _
    have h1 : degHom n m g₀ (Y ^ᶻ omega2) = degHom n m g₀ (Y ^ k) := congrArg _ hres
    rw [degHom_zpowHat_omega2 m g₀ hY, map_zpow, hY m] at h1
    exact CycTest.gen_zpow_inj h1
  -- the `2`-part: `k ≡ 1` modulo every power of `2`, so `k = 1`
  have h2 : ∀ a : ℕ, a ≠ 0 → (2 ^ a : ℤ) ∣ k - 1 := by
    intro a ha
    haveI : NeZero (2 ^ a) := ⟨by positivity⟩
    have h := key (2 ^ a)
    have hone : ((omega2Exp (2 ^ a) : ℤ) : ZMod (2 ^ a)) = ((1 : ℤ) : ZMod (2 ^ a)) := by
      have := omega2Exp_two_pow_modEq_one ha
      exact_mod_cast (ZMod.natCast_eq_natCast_iff _ _ _).mpr this
    rw [hone] at h
    exact Int.modEq_iff_dvd.mp ((ZMod.intCast_eq_intCast_iff _ _ _).mp h)
  have hk1 : k = 1 := by
    have hdvd := h2 ((k - 1).natAbs + 1) (Nat.succ_ne_zero _)
    have hlt : |k - 1| < (2 : ℤ) ^ ((k - 1).natAbs + 1) := by
      have h1 : |k - 1| = ((k - 1).natAbs : ℤ) := (Int.abs_eq_natAbs _)
      have h2' : (k - 1).natAbs < 2 ^ ((k - 1).natAbs + 1) :=
        lt_of_lt_of_le (Nat.lt_two_pow_self) (Nat.pow_le_pow_right (by norm_num) (by omega))
      rw [h1]
      exact_mod_cast h2'
    have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
    omega
  -- the odd part: `k ≡ 0` modulo `3`, contradicting `k = 1`
  have h3 := key 3
  rw [hk1] at h3
  have hzero : ((omega2Exp 3 : ℤ) : ZMod 3) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr
      (Int.natCast_dvd_natCast.mpr three_dvd_omega2Exp_three)
  rw [hzero] at h3
  exact absurd h3.symm (by decide)

end Obstruction

/-! ## §6 The refutation template

A cyclic character that kills **both** relators but not the resolved family member witnesses
`freeToProf (v 1) ∉ relatorSubgroup (gammaRelators n q R)` — i.e. the failure of
`ResolvesGammaRelators.fam_mem` itself, not merely of the `of_two` route.

The character used below is `degHom n m g₀` at a *wild* letter `g₀`, so `τ ↦ 1` and the tame
relator dies for free, at every `q`. -/

section Refute

variable {n : ℕ}

/-- Every element of `ℤ/m` is killed by `m`. -/
theorem CycTest.pow_self (m : ℕ) (x : CycTest m) : x ^ m = 1 := by
  have h : ∀ a : ZMod m, (Multiplicative.ofAdd a : Multiplicative (ZMod m)) ^ m = 1 := by
    intro a
    rw [← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
    rfl
  exact h (Multiplicative.toAdd (x : Multiplicative (ZMod m)))

theorem CycTest.orderOf_dvd (m : ℕ) (x : CycTest m) : orderOf x ∣ m :=
  orderOf_dvd_of_pow_eq_one (CycTest.pow_self m x)

/-- The degree character at a letter other than `τ` kills the tame relator, at every `q`. -/
theorem degHom_tameRelatorGen (m : ℕ) [NeZero m] {g₀ : Generator n}
    (hg : Generator.tau ≠ g₀) (q : ℕ) : degHom n m g₀ (tameRelatorGen n q) = 1 := by
  simp only [tameRelatorGen, conjP, map_mul, map_inv, map_pow, degHom_of, degMark_of_ne hg]
  group

/-- The degree character of the **intrinsic** wild relator, on the `ω₂`-only fragment: packet
Lem. 2.2 turns `^ᶻ ω₂` into the `ℕ`-power at `omega2Exp m`. -/
theorem degHom_freeMarking_eval (m : ℕ) [NeZero m] (g₀ : Generator n) {w : PWord (Generator n)}
    (hw : w.IsOmega2Only) :
    degHom n m g₀ ((freeMarking n).eval w)
      = PWord.evalNat (degMark n m g₀) (omega2Exp m) w := by
  rw [Marking.map_eval (degHom n m g₀) (freeMarking n) w, freeMarking_map_degHom]
  exact PWord.eval_eq_evalNat_of_dvd (NeZero.ne m) (CycTest.orderOf_dvd m) _ hw

/-- The degree character of the **resolved** relator: the integer-exponent denotation, with no
hypothesis at all. -/
theorem degHom_freeToProf_heisToFree (m : ℕ) [NeZero m] (g₀ : Generator n)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord (Generator n)) :
    degHom n m g₀ (freeToProf (Generator n) (heisToFree E E₂ w))
      = PWord.evalZ (degMark n m g₀) E E₂ w := by
  have hfun : (fun x => (degHom n m g₀).toMonoidHom (FreeProfiniteGroup.of x)) = degMark n m g₀ :=
    funext fun x => degHom_of m g₀ x
  have h := comp_freeToProf (degHom n m g₀).toMonoidHom (heisToFree E E₂ w)
  rw [hfun] at h
  rw [evalZ_eq_lift_heisToFree (degMark n m g₀) E E₂ w]
  exact h

/-- **The refutation template.**  Both relators die at the character and the resolved family
member does not, so it is outside the closed normal closure of the relators. -/
theorem not_resolvesGammaRelators {m : ℕ} [NeZero m] {g₀ : Generator n}
    (hg : Generator.tau ≠ g₀) (q : ℕ) {R : PWord (Generator n)}
    {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ} {v : Fin 2 → FreeGroup (Generator n)}
    (hv : v 1 = heisToFree E E₂ R)
    (hkill : degHom n m g₀ ((freeMarking n).eval R) = 1)
    (hlive : PWord.evalZ (degMark n m g₀) E E₂ R ≠ 1) :
    ¬ ResolvesGammaRelators n q R v := by
  intro hres
  have hker : relatorSubgroup (gammaRelators n q R) ≤ (degHom n m g₀).toMonoidHom.ker := by
    refine Subgroup.topologicalClosure_minimal _ (Subgroup.normalClosure_le_normal ?_)
      (IsClosed.preimage (degHom n m g₀).continuous_toFun isClosed_singleton)
    intro r hr
    simp only [gammaRelators, Set.mem_insert_iff, Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact MonoidHom.mem_ker.mpr (degHom_tameRelatorGen m hg q)
    · exact MonoidHom.mem_ker.mpr hkill
  have h1 := hker (hres.fam_mem 1)
  rw [hv] at h1
  refine hlive ?_
  rw [← degHom_freeToProf_heisToFree m g₀ E E₂ R]
  exact MonoidHom.mem_ker.mp h1

/-- The `ω₂`-only form: `hkill` becomes a computation at the resolver `omega2Exp m`. -/
theorem not_resolvesGammaRelators_of_isOmega2Only {m : ℕ} [NeZero m] {g₀ : Generator n}
    (hg : Generator.tau ≠ g₀) (q : ℕ) {R : PWord (Generator n)} (hR : R.IsOmega2Only)
    {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ} {v : Fin 2 → FreeGroup (Generator n)}
    (hv : v 1 = heisToFree E E₂ R)
    (hkill : PWord.evalNat (degMark n m g₀) (omega2Exp m) R = 1)
    (hlive : PWord.evalZ (degMark n m g₀) E E₂ R ≠ 1) :
    ¬ ResolvesGammaRelators n q R v :=
  not_resolvesGammaRelators hg q hv
    ((degHom_freeMarking_eval m g₀ hR).trans hkill) hlive

end Refute

/-! ## §7 The five frozen families, refuted at the intrinsic branch word

Each theorem below says: at the frozen instance, the family does **not** resolve the relators of
`Γ_R` when `R` is the branch word itself.  The witness is one cyclic character in the letter `x₂`
(`x₀` for `L_sq`) into `ℤ/8` (`ℤ/4` for `L_sq`) — a **`2`-group**, so CB-MP's admissibility
restriction does not exclude it.  All of `q` is covered: the tame relator dies at the character
for every `q`, because the character kills `τ`.

The arithmetic in every case is `omega2Exp (2 ^ a) = 1` against the frozen resolver `e = 3`: the
intrinsic relator's traced exponent is `ω₂ − 1 ↦ 0`, the resolved one's is `e − 1 ↦ 2 ≠ 0`. -/

section Frozen

/-- `omega2Exp 4 = 1`, the `L_sq` modulus (companion of `omega2Exp_eight`). -/
theorem omega2Exp_four : omega2Exp 4 = 1 := by
  have hfac : (4 : ℕ).factorization 2 = 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  norm_num [omega2Exp, hfac]

/-- **Compact `N` (the `√−2` pilot) does not resolve the relators of the intrinsic branch
word**, at any `q`. -/
theorem not_resolves_nCompactFam (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.nCompactW 2 0)
      (Certificates.nCompactFam 2 0 q 3) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 8) (g₀ := Words.coreLetter 0 2)
    (by decide) q (Words.isOmega2Only_nCompact 2 0) rfl
    (by rw [omega2Exp_eight]; decide) (by decide)

/-- **Compact `M` (the `√2` pilot).** -/
theorem not_resolves_mCompactFam (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.MCompact.mCompactW 3 0)
      (Certificates.MCompact.mCompactFam 3 0 q 3) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 8) (g₀ := Words.coreLetter 0 2)
    (by decide) q (Words.MCompact.isOmega2Only_mCompact 3 0) rfl
    (by rw [omega2Exp_eight]; decide) (by decide)

/-- **Compact `M` (the `√5` pilot).** -/
theorem not_resolves_mCompactFam_five (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.MCompact.mCompactW 2 0)
      (Certificates.MCompact.mCompactFam 2 0 q 3) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 8) (g₀ := Words.coreLetter 0 2)
    (by decide) q (Words.MCompact.isOmega2Only_mCompact 2 0) rfl
    (by rw [omega2Exp_eight]; decide) (by decide)

/-- **Procyclic `M` (the `√−10` pilot).**  `η̂ = .one` is an `ω₂`-only display, so the packet
Lem. 2.2 route is available (`Words.Mpc.isOmega2Only_mpcW`). -/
theorem not_resolves_mpcFam (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.Mpc.mpcW 2 1 1 .one 0)
      (Certificates.MProcyclic.mpcFam 2 1 1 0 q 3 .one) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 8) (g₀ := Words.coreLetter 0 2)
    (by decide) q (Words.Mpc.isOmega2Only_mpcW 2 1 1 (η := .one) trivial 0) rfl
    (by rw [omega2Exp_eight]; decide) (by decide)

/-- **Procyclic `M` (the `√10` pilot).** -/
theorem not_resolves_mpcFam_ten (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.Mpc.mpcW 2 1 0 .one 0)
      (Certificates.MProcyclic.mpcFam 2 1 0 0 q 3 .one) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 8) (g₀ := Words.coreLetter 0 2)
    (by decide) q (Words.Mpc.isOmega2Only_mpcW 2 1 0 (η := .one) trivial 0) rfl
    (by rw [omega2Exp_eight]; decide) (by decide)

/-- **`L_sq` (the `q = 2` pilot).**  The `L_sq` character is in `x₀` and lands in `ℤ/4`: the
traced `x₀`-exponent is `−1 − 3ω₂`, which is `−4 ↦ 0` intrinsically and `−10 ↦ 2` at `e = 3`. -/
theorem not_resolves_lSqFam (q : ℕ) :
    ¬ ResolvesGammaRelators (2 * 0 + 1) q (Words.LSq.lSqW 0)
      (Certificates.LSqStokes.lSqFam 0 q 3) :=
  not_resolvesGammaRelators_of_isOmega2Only (m := 4) (g₀ := Words.LSq.coreLetter 0 0)
    (by decide) q (Words.LSq.isOmega2Only_lSq 0) rfl
    (by rw [omega2Exp_four]; decide) (by decide)

/-- **Procyclic `N` (the `npcPin` instance).**  This word is *not* `ω₂`-only (WNP-a's
`not_isOmega2Only_npcW`), so the intrinsic side goes through WNP-a's abelian normal form
`eval_npcW_of_comm` instead: on a commutative target the `η̂`-twist, the correction block and the
handles are all invisible, and what survives is exactly the compact row's `x₂⁻¹ (x₂τ)^{ω₂}`. -/
theorem not_resolves_npcFam (q : ℕ) :
    ¬ ResolvesGammaRelators (2 + 2 * 0) q (Words.Npc.npcW 2 1 0 ⟨1, 1⟩)
      (Certificates.Npc.npcFam 2 1 0 q 3 ⟨1, 1⟩) := by
  refine not_resolvesGammaRelators (m := 8) (g₀ := Words.coreLetter 0 2) (by decide) q rfl ?_
    (by decide)
  rw [Marking.map_eval (degHom (2 + 2 * 0) 8 (Words.coreLetter 0 2)) (freeMarking _) _,
    freeMarking_map_degHom, Words.Npc.eval_npcW_of_comm]
  show (degMark (2 + 2 * 0) 8 (Words.coreLetter 0 2) (Words.coreLetter 0 0)) ^ ((2 : ℤ) + 2 ^ 2) *
      (degMark (2 + 2 * 0) 8 (Words.coreLetter 0 2) (Words.coreLetter 0 2))⁻¹ *
      (degMark (2 + 2 * 0) 8 (Words.coreLetter 0 2) (Words.coreLetter 0 2) *
        degMark (2 + 2 * 0) 8 (Words.coreLetter 0 2) Generator.tau) ^ᶻ omega2 = 1
  rw [degMark_of_ne (by decide), degMark_self, degMark_of_ne (by decide), one_zpow, one_mul,
    mul_one]
  rw [PWord.zpowHat_omega2_zpow (N := 8) (by norm_num) (CycTest.orderOf_dvd 8 _),
    omega2Exp_eight, Nat.cast_one, zpow_one, inv_mul_cancel]

end Frozen

end Count

end GQ2.Dyadic
