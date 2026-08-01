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

end Count

end GQ2.Dyadic
