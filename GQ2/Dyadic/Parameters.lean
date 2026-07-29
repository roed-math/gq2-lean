/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Tactic.DeriveFintype
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fin.VecNotation
public import GQ2.Words

@[expose] public section

/-!
# Dyadic campaign, layer F1: parameters, semantic generators, markings, branch data

This is the bottom layer of the general-`2`-adic (ramified-`i`) extension of the `G_{ℚ₂}`
formalization: the *parameter*, *semantic generator*, *marking* and *branch datum* types that
every later dyadic lane consumes.  Nothing here is a theorem about fields; the file is a
vocabulary, frozen at campaign gate `G1`.

References (all vendored under `docs/dyadic/refs/`, packet **overrides** drafts):

* **packet** = `dyadic-presentations-formalization-proof.tex`
  (§8 Prop. 8.1 + Cor. 8.2 = the arithmetic branch correction; §13 module graph).
* **draft** = `dyadic-presentations.tex`
  (§2 marked datum `(C, I, λ, γ)`, eqs. 2.1–2.3; §5 the relator families; §10.2 the paper's own
  suggested Lean parameter layer, which this file follows and sharpens).
* **plan** = `docs/dyadic/plan.md` (§1 five-row branch table, §3 A5 file layout).

## Main definitions

* `GQ2.Dyadic.FieldParameters` — `n = [K : ℚ₂]`, residue degree `f`, `q_K = 2 ^ f`, with
  `f ∣ n` and the derived ramification index `e = n / f`.
* `GQ2.Dyadic.LabuteType` — `L | M α | N α`, with validity `2 ≤ α` for the even types.
* `GQ2.Dyadic.Generator n` — the *semantic* generator alphabet `σ | τ | x₀, …, x_n`
  (draft §10.2: preferable to a bare `Fin (n + 3)`, which invites coordinate-order mistakes,
  while carrying the same cardinality `n + 3`).
* `GQ2.Dyadic.Marking n G` — a `Generator n`-indexed tuple in `G`, with letters `σ`, `τ`,
  `x i`, functorial `Marking.map`, and an explicit `n = 1` adapter to the existing four-field
  `GQ2.Marking` of `GQ2/Words.lean`.
* `GQ2.Dyadic.BranchData` — the **five-row** branch datum `L | N0 | Npc | M0 | Mpc`
  (plan §1; packet Prop. 8.1 deleted the draft's sign-Frobenius row), with `BranchData.Valid`,
  `BranchData.labuteType`, and the well-formedness predicate `Compatible`.
* Numeric conventions `m`, `pAlpha`, `s`, `p` of draft §5.

## Design decisions recorded for the `G1` API review

1. **`η : ℤ_[2]ˣ`, not `(ZMod (2 ^ r))ˣ`** — see the docstring of `BranchData`.
2. **`ε : Bool`** with `false ↦ λ(-1) = 0`, `true ↦ λ(-1) = 2^{r-1}` — see `epsVal`.
3. **Side conditions live in `Valid`/`Compatible` predicates, not in constructors** — see the
   docstrings of `LabuteType.Valid` and `BranchData.Valid`.
4. **`Marking.map` acts on bare functions**, not on `MonoidHom`s — see `Marking.map`.

## Implementation notes

This file is `module`-style.  `GQ2/Words.lean` (its only in-repo import) is `module`-style, and
so is every Mathlib file used here, so the one-directional rule of plan §3 A5 ("a `module` file
cannot import a plain-import file") is satisfied.  Later dyadic files that reach the §8/§9 stack
must still be plain-import; importing *this* file from a plain-import file is fine.
-/

namespace GQ2.Dyadic

/-! ## Field parameters -/

/-- The numerical parameters of a finite extension `K/ℚ₂` that the presentation sees:
the degree `n = [K : ℚ₂]`, the residue degree `f`, and the residue cardinality `q_K = 2 ^ f`.

`q_K` is carried as a field together with `qK_eq` rather than being defined as `2 ^ f`, so that
concrete instances can be written with a literal (`qK := 4`) and definitional unfolding in the
tame relation `τ^σ = τ^{q_K}` stays under the author's control.

Only `q_K` enters the tame relation; the Demuškin invariant of the branch cores is always `2`
(draft §2, remark after eq. 2.3), and the cyclotomic depth of the `L` core uses `σ₂²`, not
`σ₂^{q_K}` (draft §5.1 remark).  So `f` is *not* redundant data about the branch: it is exactly
the tame parameter. -/
structure FieldParameters where
  /-- `n = [K : ℚ₂]`, the number of wild generators minus one (`x₀, …, x_n`). -/
  n : ℕ
  /-- `f`, the residue degree of `K/ℚ₂`. -/
  f : ℕ
  /-- `q_K`, the residue cardinality. -/
  qK : ℕ
  /-- `q_K = 2 ^ f`: the residue field is `𝔽_{2^f}`. -/
  qK_eq : qK = 2 ^ f
  /-- `K` is a field, so `1 ≤ n`. -/
  one_le_n : 1 ≤ n
  /-- `1 ≤ f`. -/
  one_le_f : 1 ≤ f
  /-- The residue degree divides the degree, `n = e * f`. -/
  f_dvd_n : f ∣ n

namespace FieldParameters

variable (P : FieldParameters)

/-- The ramification index `e = n / f` of `K/ℚ₂`.  Characterised by `FieldParameters.n_eq`. -/
def e : ℕ := P.n / P.f

/-- The fundamental identity `n = e * f`. -/
theorem n_eq : P.n = P.e * P.f := (Nat.div_mul_cancel P.f_dvd_n).symm

@[simp] theorem e_mul_f : P.e * P.f = P.n := (n_eq P).symm

theorem f_pos : 0 < P.f := P.one_le_f

theorem n_pos : 0 < P.n := P.one_le_n

theorem e_pos : 0 < P.e := by
  rcases Nat.eq_zero_or_pos P.e with h | h
  · have h0 : P.n = 0 := by rw [n_eq, h, Nat.zero_mul]
    have := P.one_le_n
    omega
  · exact h

theorem one_le_e : 1 ≤ P.e := P.e_pos

theorem f_le_n : P.f ≤ P.n := Nat.le_of_dvd P.n_pos P.f_dvd_n

theorem two_le_qK : 2 ≤ P.qK := by
  rw [P.qK_eq]
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ P.f := Nat.pow_le_pow_right (by norm_num) P.one_le_f

theorem qK_pos : 0 < P.qK := lt_of_lt_of_le (by norm_num) P.two_le_qK

/-- The number of generators of the candidate presentation `Γ_R`, namely
`σ, τ, x₀, …, x_n`.  This depends only on `P.n`, never on the branch — see the docstring of
`GQ2.Dyadic.Compatible`, which is the actual branch/degree compatibility hook. -/
def generatorCount : ℕ := P.n + 3

end FieldParameters

/-! ## Labute types -/

/-- The abstract Demuškin (Labute) type of the maximal pro-`2` quotient: `L` in odd degree, and
the two even families `M α`, `N α` (draft §2.2, relators `r_M = a²[a,b]c^{2^α}[c,d]⋯` and
`r_N = a^{2+2^α}[a,b][c,d]⋯`).

⚠ The abstract type does **not** determine the marked pair `(D_K, ν_ur)`; the necessary datum is
`(C, I, λ, γ)` (draft §2 warning: `ℚ₂(√5)`, `ℚ₂(√10)`, `ℚ₂(√-10)` all have type `M₂`).  The
Lean-side refinement of `LabuteType` that *does* determine the word is `BranchData`. -/
inductive LabuteType
  /-- Odd degree. -/
  | L
  /-- Even type `M_α`, core relator `a²[a,b]c^{2^α}[c,d]⋯`. -/
  | M (α : ℕ)
  /-- Even type `N_α`, core relator `a^{2+2^α}[a,b][c,d]⋯`. -/
  | N (α : ℕ)
  deriving DecidableEq, Repr

namespace LabuteType

/-- Validity of a Labute type: `2 ≤ α` for the even families.

The bound is not decorative.  The `M_α` branch is built from `u = (1 - 2^α)⁻¹ ∈ 1 + 4ℤ₂`
(packet §8) and the `N_α` branch from `v = -(1 + 2^α)⁻¹` (draft §2.2); membership in the
procyclic factor `1 + 4ℤ₂` of `ℤ₂ˣ = ⟨-1⟩ × (1 + 4ℤ₂)` is exactly `2 ≤ α`, and at `α = 1` the
`M` recipe degenerates (`u = -1`, the torsion factor).

**Design note (predicate, not subtype).**  Validity is a `Prop`-valued predicate on the plain
inductive rather than a constructor argument or a subtype because (i) every downstream consumer
pattern-matches on the constructor and never inspects the proof, so proof-carrying constructors
would only add `Subsingleton`/`DecidableEq` boilerplate at each match; (ii) the condition is
decidable, so concrete instances discharge it by `decide`; (iii) a lane that genuinely needs a
bundled type can still form `{t : LabuteType // t.Valid}` without a change here. -/
def Valid : LabuteType → Prop
  | .L => True
  | .M α => 2 ≤ α
  | .N α => 2 ≤ α

@[simp] theorem valid_L : Valid .L := trivial

@[simp] theorem valid_M_iff {α : ℕ} : Valid (.M α) ↔ 2 ≤ α := Iff.rfl

@[simp] theorem valid_N_iff {α : ℕ} : Valid (.N α) ↔ 2 ≤ α := Iff.rfl

instance (t : LabuteType) : Decidable (Valid t) := by
  cases t
  · exact isTrue trivial
  · exact decidable_of_iff _ valid_M_iff.symm
  · exact decidable_of_iff _ valid_N_iff.symm

/-- `true` for the two even families `M α`, `N α`; `false` for `L`.  The even types are exactly
the ones whose marked core has rank four and which therefore force `n` to be even
(draft §5: `n = 2 + 2h` for the even families, `n = 2m + 1` for `L`). -/
def isEven : LabuteType → Bool
  | .L => false
  | .M _ => true
  | .N _ => true

@[simp] theorem isEven_L : isEven .L = false := rfl
@[simp] theorem isEven_M {α : ℕ} : isEven (.M α) = true := rfl
@[simp] theorem isEven_N {α : ℕ} : isEven (.N α) = true := rfl

end LabuteType

/-! ## Semantic generators -/

/-- The generator alphabet of the candidate presentation over a field of degree `n`:
`σ` (Frobenius lift), `τ` (tame generator), and the wild generators `x₀, …, x_n`
(draft eq. 1.1 / plan §1: `Γ_R = ⟨σ, τ, x₀, …, x_n | τ^σ = τ^{q_K}, R = 1, ⋯⟩`).

Draft §10.2: this *semantic* alphabet is preferred to a bare `Fin (n + 3)` because it prevents
coordinate-order mistakes in the Fox complex while retaining the correct cardinality
(`card_generator`).  When a linear index really is wanted (matrix rows/columns), use
`Generator.equivFin`, whose ordering is `σ, τ, x₀, …, x_n`. -/
inductive Generator (n : ℕ)
  /-- The Frobenius-lift generator `σ`. -/
  | sigma
  /-- The tame generator `τ`. -/
  | tau
  /-- The wild generator `x i`, `0 ≤ i ≤ n`. -/
  | wild (i : Fin (n + 1))
  deriving DecidableEq, Fintype, Repr

namespace Generator

variable {n : ℕ}

/-- `Generator n` split into its two "boundary" letters and its `n + 1` wild letters.
`σ ↦ inl false`, `τ ↦ inl true`, `x i ↦ inr i`. -/
def equivSum (n : ℕ) : Generator n ≃ Bool ⊕ Fin (n + 1) where
  toFun
    | .sigma => .inl false
    | .tau => .inl true
    | .wild i => .inr i
  invFun
    | .inl false => .sigma
    | .inl true => .tau
    | .inr i => .wild i
  left_inv g := by cases g <;> rfl
  right_inv g := by rcases g with (_ | _) | i <;> rfl

/-- The canonical linear indexing of the generator alphabet: `σ ↦ 0`, `τ ↦ 1`, `x i ↦ i + 2`.

Provided for matrix/vector code (Fox complexes, evaluation matrices) only.  Words are always
built from the semantic constructors; this equivalence exists so that a lane never has to invent
its own generator ordering. -/
def equivFin (n : ℕ) : Generator n ≃ Fin (n + 3) where
  toFun
    | .sigma => ⟨0, by omega⟩
    | .tau => ⟨1, by omega⟩
    | .wild i => ⟨(i : ℕ) + 2, by have := i.isLt; omega⟩
  invFun j :=
    if (j : ℕ) = 0 then .sigma
    else if (j : ℕ) = 1 then .tau
    else .wild ⟨(j : ℕ) - 2, by have := j.isLt; omega⟩
  left_inv g := by
    cases g with
    | sigma => rfl
    | tau => rfl
    | wild i =>
        have h0 : ¬ ((i : ℕ) + 2 = 0) := by omega
        have h1 : ¬ ((i : ℕ) + 2 = 1) := by omega
        simp only [h0, h1, if_false, Nat.add_sub_cancel]
  right_inv j := by
    rcases j with ⟨v, hv⟩
    by_cases h0 : v = 0
    · subst h0; rfl
    · by_cases h1 : v = 1
      · subst h1; rfl
      · simp only [h0, h1, if_false]
        refine Fin.ext ?_
        show v - 2 + 2 = v
        omega

@[simp] theorem equivFin_sigma : (equivFin n .sigma : ℕ) = 0 := rfl
@[simp] theorem equivFin_tau : (equivFin n .tau : ℕ) = 1 := rfl
@[simp] theorem equivFin_wild (i : Fin (n + 1)) :
    (equivFin n (.wild i) : ℕ) = (i : ℕ) + 2 := rfl

/-- The alphabet has `n + 3` letters: `σ`, `τ` and `x₀, …, x_n`. -/
@[simp] theorem card_generator (n : ℕ) : Fintype.card (Generator n) = n + 3 := by
  rw [Fintype.card_congr (equivFin n), Fintype.card_fin]

theorem card_generator_eq (P : FieldParameters) :
    Fintype.card (Generator P.n) = P.generatorCount := card_generator P.n

end Generator

/-! ## Markings -/

/-- A **marking** of `Generator n` in `G`: an ordered `(n + 3)`-tuple `(σ, τ, x₀, …, x_n)` of
elements of `G`, packaged as a single function so that word evaluation is literally
"substitute the marking" (draft §10.2, where the layer is a three-field record; bundling the one
function instead makes `Marking.map` and the F2 denotation lemmas uniform in the letter).

`G` carries no algebraic structure here: markings are used for profinite groups, finite groups
and (in the Fox layer) modules alike. -/
structure Marking (n : ℕ) (G : Type*) where
  /-- The underlying assignment of a group element to each generator letter. -/
  toFun : Generator n → G

namespace Marking

variable {n : ℕ} {G H K : Type*}

instance instFunLike : FunLike (Marking n G) (Generator n) G where
  coe := Marking.toFun
  coe_injective := by rintro ⟨f⟩ ⟨g⟩ h; exact congrArg Marking.mk h

@[simp] theorem coe_mk (f : Generator n → G) : ⇑(Marking.mk f : Marking n G) = f := rfl

@[simp] theorem toFun_eq_coe (t : Marking n G) : t.toFun = ⇑t := rfl

@[ext] theorem ext {t u : Marking n G} (h : ∀ g, t g = u g) : t = u :=
  DFunLike.ext _ _ h

/-! ### Letters -/

variable (t : Marking n G)

/-- The letter `σ` of a marking. -/
def σ : G := t .sigma

/-- The letter `τ` of a marking. -/
def τ : G := t .tau

/-- The wild letter `x i` of a marking, `0 ≤ i ≤ n`. -/
def x (i : Fin (n + 1)) : G := t (.wild i)

@[simp] theorem apply_sigma : t .sigma = t.σ := rfl
@[simp] theorem apply_tau : t .tau = t.τ := rfl
@[simp] theorem apply_wild (i : Fin (n + 1)) : t (.wild i) = t.x i := rfl

/-- Build a marking from its letters. -/
def ofLetters (σ τ : G) (x : Fin (n + 1) → G) : Marking n G :=
  ⟨fun | .sigma => σ | .tau => τ | .wild i => x i⟩

@[simp] theorem ofLetters_σ (σ τ : G) (x : Fin (n + 1) → G) :
    (ofLetters σ τ x).σ = σ := rfl
@[simp] theorem ofLetters_τ (σ τ : G) (x : Fin (n + 1) → G) :
    (ofLetters σ τ x).τ = τ := rfl
@[simp] theorem ofLetters_x (σ τ : G) (x : Fin (n + 1) → G) (i : Fin (n + 1)) :
    (ofLetters σ τ x).x i = x i := rfl

@[simp] theorem ofLetters_letters : ofLetters t.σ t.τ t.x = t := by
  ext g; cases g <;> rfl

/-! ### Functoriality -/

/-- Push a marking forward along a map of the ambient types.

**Design note.**  `map` takes a *bare function* `G → H`, not a `MonoidHom`: a marking carries no
algebraic structure, so this is the most general functoriality, and it specialises to every
morphism class the campaign needs (`t.map ⇑φ` for `φ : G →* H`, a `ContinuousMonoidHom`, a
`MulEquiv`, a quotient map, …) with no coercion lemmas per class.  The two bridge lemmas
`map_monoidHom_comp` and `map_monoidHom_id` recover the `MonoidHom`-functor statements. -/
def map (f : G → H) (t : Marking n G) : Marking n H := ⟨fun g => f (t g)⟩

@[simp] theorem map_apply (f : G → H) (t : Marking n G) (g : Generator n) :
    t.map f g = f (t g) := rfl

@[simp] theorem map_σ (f : G → H) (t : Marking n G) : (t.map f).σ = f t.σ := rfl
@[simp] theorem map_τ (f : G → H) (t : Marking n G) : (t.map f).τ = f t.τ := rfl
@[simp] theorem map_x (f : G → H) (t : Marking n G) (i : Fin (n + 1)) :
    (t.map f).x i = f (t.x i) := rfl

@[simp] theorem map_id (t : Marking n G) : t.map id = t := rfl

@[simp] theorem map_map (f : G → H) (g : H → K) (t : Marking n G) :
    (t.map f).map g = t.map (g ∘ f) := rfl

theorem map_comp (f : G → H) (g : H → K) (t : Marking n G) :
    t.map (g ∘ f) = (t.map f).map g := rfl

theorem map_monoidHom_id {G : Type*} [Monoid G] (t : Marking n G) :
    t.map ⇑(MonoidHom.id G) = t := rfl

theorem map_monoidHom_comp {G H K : Type*} [Monoid G] [Monoid H] [Monoid K]
    (f : G →* H) (g : H →* K) (t : Marking n G) :
    (t.map ⇑f).map ⇑g = t.map ⇑(g.comp f) := rfl

/-! ### The `n = 1` adapter

At `n = 1` the alphabet is `(σ, τ, x₀, x₁)`, which is exactly the four-field record
`GQ2.Marking` of `GQ2/Words.lean` used by the frozen `G_{ℚ₂}` development (plan §3 A6).  The
adapter below is an `Equiv`, so every ℚ₂ statement can be transported without touching the ℚ₂
files. -/

/-- The `n = 1` marking `(σ, τ, x 0, x 1)` as the legacy four-field `GQ2.Marking`. -/
def toQ2 (t : Marking 1 G) : _root_.GQ2.Marking G := ⟨t.σ, t.τ, t.x 0, t.x 1⟩

/-- A legacy four-field `GQ2.Marking` as an `n = 1` marking. -/
def ofQ2 (t : _root_.GQ2.Marking G) : Marking 1 G := ofLetters t.σ t.τ ![t.x₀, t.x₁]

@[simp] theorem toQ2_σ (t : Marking 1 G) : (toQ2 t).σ = t.σ := rfl
@[simp] theorem toQ2_τ (t : Marking 1 G) : (toQ2 t).τ = t.τ := rfl
@[simp] theorem toQ2_x₀ (t : Marking 1 G) : (toQ2 t).x₀ = t.x 0 := rfl
@[simp] theorem toQ2_x₁ (t : Marking 1 G) : (toQ2 t).x₁ = t.x 1 := rfl

@[simp] theorem ofQ2_σ (t : _root_.GQ2.Marking G) : (ofQ2 t).σ = t.σ := rfl
@[simp] theorem ofQ2_τ (t : _root_.GQ2.Marking G) : (ofQ2 t).τ = t.τ := rfl
@[simp] theorem ofQ2_x_zero (t : _root_.GQ2.Marking G) : (ofQ2 t).x 0 = t.x₀ := rfl
@[simp] theorem ofQ2_x_one (t : _root_.GQ2.Marking G) : (ofQ2 t).x 1 = t.x₁ := rfl

@[simp] theorem toQ2_ofQ2 (t : _root_.GQ2.Marking G) : toQ2 (ofQ2 t) = t := rfl

@[simp] theorem ofQ2_toQ2 (t : Marking 1 G) : ofQ2 (toQ2 t) = t := by
  ext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | (k + 2), h => exact absurd h (by omega)

/-- The `n = 1` markings are exactly the legacy four-field markings. -/
def equivQ2 : Marking 1 G ≃ _root_.GQ2.Marking G where
  toFun := toQ2
  invFun := ofQ2
  left_inv := ofQ2_toQ2
  right_inv := toQ2_ofQ2

@[simp] theorem equivQ2_apply (t : Marking 1 G) : equivQ2 t = toQ2 t := rfl
@[simp] theorem equivQ2_symm_apply (t : _root_.GQ2.Marking G) : equivQ2.symm t = ofQ2 t := rfl

end Marking

/-! ## Numeric conventions

The exponents that occur in the branch words and cores (draft §5): `m = 2^{α-1}`,
`p_α = 2 + 2^α`, `s = 2^r`, `p = ε·2^{r-1}`. -/

/-- `m = 2^{α-1}`, the half-power occurring in the `M_α` coordinates
`x₀ = c^{-m} a^{-1}` and in `E_m^{rev}` (draft §2.2, §5.3). -/
def m (α : ℕ) : ℕ := 2 ^ (α - 1)

/-- `p_α = 2 + 2^α`, the exponent of `x₀` in the `N_α` core `x₀^{p_α}[x₀,x₁][σ,x₂]`
(draft §2.2 eq. `Ncompact-core`, §5.2). -/
def pAlpha (α : ℕ) : ℕ := 2 + 2 ^ α

/-- `s = 2^r`, the unramified level of the marked datum: `A = ν_ur(ker χ) = 2^r ℤ₂`
(draft eq. 2.1), appearing in `C₀ = x₂ σ₂^s` (draft §5.3). -/
def s (r : ℕ) : ℕ := 2 ^ r

/-- The numeric value of the sign parameter `ε`: `λ(-1) = ε · 2^{r-1}` (packet §8).

`ε` is `Bool`-valued because `λ(-1)` has only two possible values: `-1` has order two in
`C = ⟨-1⟩ × ⟨u⟩`, so its image in `ℤ/2^r` is either `0` (`ε = false`, i.e. `-1 ∈ I = ker λ`) or
the unique element of order two, `2^{r-1}` (`ε = true`).  Both occur under the standing
ramified-`i` hypothesis: draft §7.3 computes `ℚ₂(√10)` with `B = x₁` (`ε = false`) while packet
Cor. 8.2 gives `ℚ₂(√-10)` with `ε = 1` (`ε = true`).

Alternative considered: `ε : ZMod 2` or `ε : Fin 2`.  `Bool` was chosen because `ε` is never
added to anything — it only selects between two exponents — and `Bool` gives `decide`-ability
and `Repr` for free. -/
def epsVal (ε : Bool) : ℕ := cond ε 1 0

/-- `p = ε · 2^{r-1}`, the exponent of `σ₂` in `B = x₁ σ₂^p` (draft §5.3).

Only meaningful for `r ≥ 1`, i.e. on the procyclic rows; the truncated `r - 1` makes
`p ε 0 = epsVal ε`, a value no word reads (on the compact rows `BranchData.eps` is `false`, so
`BranchData.pVal` is `0` there anyway). -/
def p (ε : Bool) (r : ℕ) : ℕ := epsVal ε * 2 ^ (r - 1)

@[simp] theorem m_zero : m 0 = 1 := rfl
@[simp] theorem m_one : m 1 = 1 := rfl
@[simp] theorem m_two : m 2 = 2 := rfl

theorem m_pos (α : ℕ) : 0 < m α := pow_pos (by norm_num) _

theorem two_mul_m {α : ℕ} (h : 1 ≤ α) : 2 * m α = 2 ^ α := by
  unfold m
  rw [← pow_succ']
  congr 1
  omega

theorem two_le_m {α : ℕ} (h : 2 ≤ α) : 2 ≤ m α := by
  unfold m
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ (α - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

@[simp] theorem pAlpha_two : pAlpha 2 = 6 := rfl

theorem pAlpha_eq_two_add_two_mul_m {α : ℕ} (h : 1 ≤ α) : pAlpha α = 2 + 2 * m α := by
  rw [pAlpha, two_mul_m h]

theorem six_le_pAlpha {α : ℕ} (h : 2 ≤ α) : 6 ≤ pAlpha α := by
  rw [pAlpha_eq_two_add_two_mul_m (by omega)]
  have := two_le_m h
  omega

@[simp] theorem s_zero : s 0 = 1 := rfl

@[simp] theorem s_succ (r : ℕ) : s (r + 1) = 2 * s r := by
  simp [s, pow_succ']

theorem s_pos (r : ℕ) : 0 < s r := pow_pos (by norm_num) _

theorem two_le_s {r : ℕ} (h : 1 ≤ r) : 2 ≤ s r := by
  unfold s
  calc (2 : ℕ) = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) h

@[simp] theorem epsVal_false : epsVal false = 0 := rfl
@[simp] theorem epsVal_true : epsVal true = 1 := rfl

@[simp] theorem p_false (r : ℕ) : p false r = 0 := by simp [p]

@[simp] theorem p_true (r : ℕ) : p true r = 2 ^ (r - 1) := by simp [p]

/-- `λ(-1) = 2^{r-1}` is the unique element of order two of `ℤ/2^r` (`r ≥ 1`). -/
theorem two_mul_p_true {r : ℕ} (h : 1 ≤ r) : 2 * p true r = s r := by
  rw [p_true, s, ← pow_succ']
  congr 1
  omega

theorem p_lt_s {ε : Bool} {r : ℕ} (h : 1 ≤ r) : p ε r < s r := by
  cases ε
  · simpa using s_pos r
  · have h2 := two_mul_p_true h
    have h1 : 0 < p true r := by rw [p_true]; exact pow_pos (by norm_num) _
    omega

/-! ## `2`-adic units and their residues

`η` is a `2`-adic unit throughout (see `BranchData`); the two lemmas below are the bridge to the
mod-`2^r` values `λ(u) ∈ ℤ/2^r` of the marked datum (draft eq. 2.2), which is what F4's
`CyclotomicFrobeniusDatum` produces. -/

/-- The reduction `ℤ_[2]ˣ → (ZMod (2 ^ r))ˣ`.  If `η` is the chosen `2`-adic lift of the marked
value `λ(u) ∈ ℤ/2^r`, then `etaUnit r η = λ(u)` is the compatibility that F4 states. -/
noncomputable def etaUnit (r : ℕ) (η : ℤ_[2]ˣ) : (ZMod (2 ^ r))ˣ :=
  Units.map (PadicInt.toZModPow r : ℤ_[2] →+* ZMod (2 ^ r)).toMonoidHom η

@[simp] theorem etaUnit_coe (r : ℕ) (η : ℤ_[2]ˣ) :
    ((etaUnit r η : (ZMod (2 ^ r))ˣ) : ZMod (2 ^ r)) = PadicInt.toZModPow r (η : ℤ_[2]) := rfl

/-- **Every `2`-adic unit is odd.**  This is why the `η`-oddness side condition of the
procyclic rows (packet Prop. 8.1) carries no proof obligation once `η : ℤ_[2]ˣ`:
the residue of a unit in `ZMod 2` is `1`. -/
theorem toZMod_units_eq_one (η : ℤ_[2]ˣ) : PadicInt.toZMod (η : ℤ_[2]) = 1 := by
  have h : PadicInt.toZMod (η : ℤ_[2]) * PadicInt.toZMod ((η⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
    rw [← map_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one, map_one]
  revert h
  generalize PadicInt.toZMod (η : ℤ_[2]) = a
  generalize PadicInt.toZMod ((η⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) = b
  revert a b
  decide

/-! ## The five-row branch datum -/

/-- The **branch datum**: which of the five relator families of plan §1 applies, together with
its parameters.  This is the Lean form of the marked arithmetic datum `(C, I, λ, γ)` of
draft §2 *as it is consumed by the words*: the abstract Labute type plus the unramified level
`r`, the sign parameter `ε`, and the Frobenius unit `η`.

**There is no sign-Frobenius row** (packet Prop. 8.1, `prop:sign-excluded`): if `η = λ(u)` is
even then surjectivity of `λ : C = ⟨-1⟩ × ⟨u⟩ ↠ ℤ/2^r` forces `r = 1`, `ε = 1`,
`I = ker λ = ⟨u⟩`, and hence `K(i)/K` *unramified* — which is outside the standing hypothesis of
this campaign (Diekert 1984 covers that case).  So under ramified `i`, `η` is necessarily odd and
the `M_α` families are exactly the compact row `r = 0` and the procyclic row `r ≥ 1`,
`η ∈ ℤ₂ˣ`.  The draft's `R_{M,sgn}` (draft eq. `Msign-word`) and its §7.4 use for `ℚ₂(√-10)`
are superseded; packet Cor. 8.2 puts `ℚ₂(√-10)` on the procyclic row with `(r, ε, η) = (1,1,1)`.

**Design decision — `η : ℤ_[2]ˣ`.**  The marked datum of draft eq. 2.2 produces
`λ(u) ∈ ℤ/2^r`, and one could take `η : (ZMod (2 ^ r))ˣ`, which is canonical (no choice of
lift).  We take the `2`-adic unit instead, for three reasons.
(i) *The words need it.*  Draft §5.2/§5.3 read: "let `η̂ ∈ Ẑˣ` have `2`-component `η` and
odd-primary components `1`", and the relators contain the letter `σ^{η̂}` (eqs. `Npc-word`,
`Mpc-word`) *alongside* the letter `σ^{2^r}` (in `C₀ = x₂ σ₂^s`, `g = x₁ σ^{2^r}`).  Since
`σ^{2^r} ≠ 1` in `Γ_R`, the exponent is not reducible mod `2^r`: a `(ZMod (2 ^ r))ˣ` datum could
not be exponentiated at all, and the branch datum would have to carry a lift anyway.
(ii) *Fidelity to the governing source.*  Packet Prop. 8.1 states the surviving rows literally as
"`r = 0`" and "`r ≥ 1`, `η ∈ ℤ₂ˣ`"; draft §5.3 likewise writes `η = λ(u) ∈ ℤ₂ˣ`.
(iii) *Oddness becomes automatic.*  The packet's conclusion "`η` is necessarily odd" is then a
typing fact, not a side condition to re-prove per row (`toZMod_units_eq_one`), and the inverse
`ρ = η⁻¹` used by the core coordinates (draft §2.2) is available with no `r`-dependent
invertibility hypothesis.
The discarded alternative is recovered by `etaUnit r η : (ZMod (2 ^ r))ˣ`, which is exactly the
value `λ(u)`; F4 states the compatibility `etaUnit r η = λ(u)` against its
`CyclotomicFrobeniusDatum`, and any two lifts of the same `λ(u)` differ by `1 + 2^r ℤ₂`.

**Design decision — side conditions.**  `2 ≤ α` and `1 ≤ r` are collected in `BranchData.Valid`
rather than carried in the constructors, for the reasons given at `LabuteType.Valid`.  The
degree conditions (`n` odd for `L`, `n` even otherwise) cannot live here at all: `n` is a
`FieldParameters` field, independent of the branch, so they live in `Compatible`. -/
inductive BranchData
  /-- Odd degree, type `L`: `r = 0` and `I = C` (draft §2.2). -/
  | L
  /-- Compact `N_α`: `r = 0` (draft eq. `Ncompact-word`). -/
  | N0 (α : ℕ)
  /-- Procyclic `N_α`: `r ≥ 1`, `η = λ(-(1 + 2^α)⁻¹) ∈ ℤ₂ˣ` (draft eq. `Npc-word`). -/
  | Npc (α : ℕ) (r : ℕ) (η : ℤ_[2]ˣ)
  /-- Compact `M_α`: `r = 0` (draft eq. `Mcompact-word`). -/
  | M0 (α : ℕ)
  /-- Procyclic `M_α`: `r ≥ 1`, `ε` the sign parameter `λ(-1) = ε·2^{r-1}`, and
  `η = λ((1 - 2^α)⁻¹) ∈ ℤ₂ˣ` — odd automatically, packet Prop. 8.1
  (draft eq. `Mpc-word`). -/
  | Mpc (α : ℕ) (r : ℕ) (ε : Bool) (η : ℤ_[2]ˣ)

namespace BranchData

variable (B : BranchData)

/-- The abstract Labute type underlying a branch row. -/
def labuteType : BranchData → LabuteType
  | .L => .L
  | .N0 α => .N α
  | .Npc α _ _ => .N α
  | .M0 α => .M α
  | .Mpc α _ _ _ => .M α

@[simp] theorem labuteType_L : labuteType .L = .L := rfl
@[simp] theorem labuteType_N0 {α : ℕ} : labuteType (.N0 α) = .N α := rfl
@[simp] theorem labuteType_Npc {α r : ℕ} {η : ℤ_[2]ˣ} :
    labuteType (.Npc α r η) = .N α := rfl
@[simp] theorem labuteType_M0 {α : ℕ} : labuteType (.M0 α) = .M α := rfl
@[simp] theorem labuteType_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    labuteType (.Mpc α r ε η) = .M α := rfl

/-- The unramified level `r` with `A = ν_ur(ker χ) = 2^r ℤ₂` (draft eq. 2.1).
`r = 0` on the compact rows and on `L` (draft §2.2: "when `n` is odd, `r = 0`, `I = C`"). -/
def level : BranchData → ℕ
  | .L => 0
  | .N0 _ => 0
  | .Npc _ r _ => r
  | .M0 _ => 0
  | .Mpc _ r _ _ => r

@[simp] theorem level_L : level .L = 0 := rfl
@[simp] theorem level_N0 {α : ℕ} : level (.N0 α) = 0 := rfl
@[simp] theorem level_Npc {α r : ℕ} {η : ℤ_[2]ˣ} : level (.Npc α r η) = r := rfl
@[simp] theorem level_M0 {α : ℕ} : level (.M0 α) = 0 := rfl
@[simp] theorem level_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    level (.Mpc α r ε η) = r := rfl

/-- The sign parameter `ε` of `λ(-1) = ε·2^{r-1}`.  It is `false` on every row except the
procyclic `M` row, where it is genuine data (draft §7.3 vs. packet Cor. 8.2). -/
def eps : BranchData → Bool
  | .Mpc _ _ ε _ => ε
  | _ => false

@[simp] theorem eps_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} : eps (.Mpc α r ε η) = ε := rfl
@[simp] theorem eps_L : eps .L = false := rfl
@[simp] theorem eps_N0 {α : ℕ} : eps (.N0 α) = false := rfl
@[simp] theorem eps_Npc {α r : ℕ} {η : ℤ_[2]ˣ} : eps (.Npc α r η) = false := rfl
@[simp] theorem eps_M0 {α : ℕ} : eps (.M0 α) = false := rfl

/-- The Demuškin parameter `α`, where it exists (`none` on the `L` row). -/
def alpha? : BranchData → Option ℕ
  | .L => none
  | .N0 α => some α
  | .Npc α _ _ => some α
  | .M0 α => some α
  | .Mpc α _ _ _ => some α

@[simp] theorem alpha?_L : alpha? .L = none := rfl
@[simp] theorem alpha?_N0 {α : ℕ} : alpha? (.N0 α) = some α := rfl
@[simp] theorem alpha?_Npc {α r : ℕ} {η : ℤ_[2]ˣ} : alpha? (.Npc α r η) = some α := rfl
@[simp] theorem alpha?_M0 {α : ℕ} : alpha? (.M0 α) = some α := rfl
@[simp] theorem alpha?_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    alpha? (.Mpc α r ε η) = some α := rfl

/-- The Frobenius unit `η`, where it exists (`none` on the compact rows and on `L`). -/
def eta? : BranchData → Option ℤ_[2]ˣ
  | .Npc _ _ η => some η
  | .Mpc _ _ _ η => some η
  | _ => none

@[simp] theorem eta?_Npc {α r : ℕ} {η : ℤ_[2]ˣ} : eta? (.Npc α r η) = some η := rfl
@[simp] theorem eta?_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    eta? (.Mpc α r ε η) = some η := rfl
@[simp] theorem eta?_L : eta? .L = none := rfl
@[simp] theorem eta?_N0 {α : ℕ} : eta? (.N0 α) = none := rfl
@[simp] theorem eta?_M0 {α : ℕ} : eta? (.M0 α) = none := rfl

/-- `s = 2^r` for this row. -/
def sVal : ℕ := s B.level

/-- `p = ε·2^{r-1}` for this row. -/
def pVal : ℕ := p B.eps B.level

@[simp] theorem sVal_eq : B.sVal = s B.level := rfl
@[simp] theorem pVal_eq : B.pVal = p B.eps B.level := rfl

/-- The compact rows: `r = 0`, i.e. the unramified marking is trivial on `ker χ`. -/
def IsCompactRow : Prop := B.level = 0

/-- The procyclic-Frobenius rows: `r ≥ 1`. -/
def IsProcyclicRow : Prop := 1 ≤ B.level

instance : Decidable B.IsCompactRow := by unfold IsCompactRow; infer_instance
instance : Decidable B.IsProcyclicRow := by unfold IsProcyclicRow; infer_instance

theorem isCompactRow_or_isProcyclicRow : B.IsCompactRow ∨ B.IsProcyclicRow := by
  unfold IsCompactRow IsProcyclicRow; omega

/-- Validity of a branch datum: `2 ≤ α` on the even rows (see `LabuteType.Valid`) and `1 ≤ r`
on the two procyclic rows.  `η`-oddness is *not* listed: it is automatic for `η : ℤ_[2]ˣ`
(`toZMod_units_eq_one`), which is the point of the design decision recorded on `BranchData`. -/
def Valid : BranchData → Prop
  | .L => True
  | .N0 α => 2 ≤ α
  | .Npc α r _ => 2 ≤ α ∧ 1 ≤ r
  | .M0 α => 2 ≤ α
  | .Mpc α r _ _ => 2 ≤ α ∧ 1 ≤ r

@[simp] theorem valid_L : Valid .L := trivial
@[simp] theorem valid_N0_iff {α : ℕ} : Valid (.N0 α) ↔ 2 ≤ α := Iff.rfl
@[simp] theorem valid_Npc_iff {α r : ℕ} {η : ℤ_[2]ˣ} :
    Valid (.Npc α r η) ↔ 2 ≤ α ∧ 1 ≤ r := Iff.rfl
@[simp] theorem valid_M0_iff {α : ℕ} : Valid (.M0 α) ↔ 2 ≤ α := Iff.rfl
@[simp] theorem valid_Mpc_iff {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    Valid (.Mpc α r ε η) ↔ 2 ≤ α ∧ 1 ≤ r := Iff.rfl

instance (B : BranchData) : Decidable B.Valid := by
  cases B
  · exact isTrue trivial
  · exact decidable_of_iff _ valid_N0_iff.symm
  · exact decidable_of_iff _ valid_Npc_iff.symm
  · exact decidable_of_iff _ valid_M0_iff.symm
  · exact decidable_of_iff _ valid_Mpc_iff.symm

/-- A valid branch datum has a valid Labute type. -/
theorem valid_labuteType (h : B.Valid) : B.labuteType.Valid := by
  cases B
  · trivial
  · exact h
  · exact h.1
  · exact h
  · exact h.1

/-- On a valid procyclic row, `r ≥ 1`. -/
theorem one_le_level_of_isProcyclicRow (h : B.IsProcyclicRow) : 1 ≤ B.level := h

/-- `true` for the four even rows, `false` for `L`. -/
def isEven : Bool := B.labuteType.isEven

@[simp] theorem isEven_L : isEven .L = false := rfl
@[simp] theorem isEven_N0 {α : ℕ} : isEven (.N0 α) = true := rfl
@[simp] theorem isEven_Npc {α r : ℕ} {η : ℤ_[2]ˣ} : isEven (.Npc α r η) = true := rfl
@[simp] theorem isEven_M0 {α : ℕ} : isEven (.M0 α) = true := rfl
@[simp] theorem isEven_Mpc {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    isEven (.Mpc α r ε η) = true := rfl

end BranchData

/-! ## Degree compatibility -/

/-- Well-formedness of a `(FieldParameters, BranchData)` pair.

There is no function `n ↦ branch` or `branch ↦ n`: the degree `n` and the branch row are
independent data (the same `n` occurs with several rows, and the same row with several `n`), so
the *only* link between them is the parity condition of draft §5 — `n = 2m + 1` odd for `L`, and
`n = 2 + 2h` even for the four even rows, `h` being the number of hyperbolic handles appended to
the rank-four core.  That link is this predicate; it is the "degree-compatibility hook" of the
F1 specification, and the generator count itself is `FieldParameters.generatorCount`,
a function of `P.n` alone. -/
def Compatible (P : FieldParameters) (B : BranchData) : Prop :=
  if B.isEven then Even P.n else Odd P.n

instance (P : FieldParameters) (B : BranchData) : Decidable (Compatible P B) := by
  unfold Compatible; split <;> infer_instance

@[simp] theorem compatible_L {P : FieldParameters} : Compatible P .L ↔ Odd P.n := Iff.rfl
@[simp] theorem compatible_N0 {P : FieldParameters} {α : ℕ} :
    Compatible P (.N0 α) ↔ Even P.n := Iff.rfl
@[simp] theorem compatible_Npc {P : FieldParameters} {α r : ℕ} {η : ℤ_[2]ˣ} :
    Compatible P (.Npc α r η) ↔ Even P.n := Iff.rfl
@[simp] theorem compatible_M0 {P : FieldParameters} {α : ℕ} :
    Compatible P (.M0 α) ↔ Even P.n := Iff.rfl
@[simp] theorem compatible_Mpc {P : FieldParameters} {α r : ℕ} {ε : Bool} {η : ℤ_[2]ˣ} :
    Compatible P (.Mpc α r ε η) ↔ Even P.n := Iff.rfl

theorem compatible_of_isEven {P : FieldParameters} {B : BranchData}
    (hB : B.isEven = true) (h : Even P.n) : Compatible P B := by
  unfold Compatible; rw [hB]; exact h

theorem compatible_of_not_isEven {P : FieldParameters} {B : BranchData}
    (hB : B.isEven = false) (h : Odd P.n) : Compatible P B := by
  unfold Compatible; rw [hB]; exact h

/-- An even-type branch forces `2 ≤ n`: the rank-four core already needs `x₀, x₁, x₂`. -/
theorem Compatible.two_le_n {P : FieldParameters} {B : BranchData}
    (h : Compatible P B) (hB : B.isEven = true) : 2 ≤ P.n := by
  unfold Compatible at h
  rw [hB, if_pos rfl, Nat.even_iff] at h
  have := P.one_le_n
  omega

/-- The number of hyperbolic handles `[x_{2j}, x_{2j+1}]` appended to the core: `h` with
`n = 2 + 2h` on the even rows, `m` with `n = 2m + 1` on the `L` row (draft §5). -/
def handleCount (P : FieldParameters) (B : BranchData) : ℕ :=
  if B.isEven then (P.n - 2) / 2 else (P.n - 1) / 2

/-- On an even row, `n = 2 + 2h` (draft §5: `n = 2 + 2h`). -/
theorem two_add_two_mul_handleCount {P : FieldParameters} {B : BranchData}
    (h : Compatible P B) (hB : B.isEven = true) : 2 + 2 * handleCount P B = P.n := by
  unfold Compatible at h
  rw [hB, if_pos rfl, Nat.even_iff] at h
  have hn := P.one_le_n
  unfold handleCount
  rw [hB, if_pos rfl]
  omega

/-- On the `L` row, `n = 2m + 1` (draft §5.1). -/
theorem two_mul_handleCount_add_one {P : FieldParameters} {B : BranchData}
    (h : Compatible P B) (hB : B.isEven = false) : 2 * handleCount P B + 1 = P.n := by
  unfold Compatible at h
  rw [hB, if_neg (by simp), Nat.odd_iff] at h
  unfold handleCount
  rw [hB, if_neg (by simp)]
  omega

/-! ## Stress section

Typechecking pins only.  Nothing below is cited by a proof; the field-theoretic content of the
branch assignments is the business of F4 and the `AS` instance lane. -/

section Stress

/-- The alphabet of a degree-`3` field has six letters `σ, τ, x₀, x₁, x₂, x₃`. -/
example : Fintype.card (Generator 3) = 6 := by decide

example : Fintype.card (Generator 0) = 3 := by decide

/-- The `n = 1` adapter round-trips, both ways, definitionally on letters. -/
example {G : Type} (t : Marking 1 G) : (Marking.toQ2 t).σ = t.σ := rfl
example {G : Type} (t : Marking 1 G) : (Marking.toQ2 t).x₀ = t.x 0 := rfl
example {G : Type} (t : Marking 1 G) : (Marking.toQ2 t).x₁ = t.x 1 := rfl
example {G : Type} (t : _root_.GQ2.Marking G) : Marking.toQ2 (Marking.ofQ2 t) = t := rfl
example {G : Type} (t : Marking 1 G) : Marking.ofQ2 (Marking.toQ2 t) = t := by
  ext g; cases g <;> [rfl; rfl; skip]
  · exact (Marking.ofQ2_toQ2 t) ▸ rfl

/-- `Marking.map` composes through `MonoidHom.comp`. -/
example {G H K : Type} [Monoid G] [Monoid H] [Monoid K] (f : G →* H) (g : H →* K)
    (t : Marking 2 G) : (t.map ⇑f).map ⇑g = t.map ⇑(g.comp f) := rfl

/-- A `FunLike` morphism may be passed to `Marking.map` without writing the coercion. -/
example {G H : Type} [Monoid G] [Monoid H] (f : G →* H) (t : Marking 2 G) (g : Generator 2) :
    t.map f g = f (t g) := rfl

/-- `ℚ₂` itself: `n = f = 1`, `q = 2`, branch `L`. -/
def paramsQ2 : FieldParameters :=
  { n := 1, f := 1, qK := 2, qK_eq := rfl, one_le_n := le_refl 1, one_le_f := le_refl 1,
    f_dvd_n := dvd_refl 1 }

example : Compatible paramsQ2 .L := by decide
example : (BranchData.L).Valid := by decide
example : paramsQ2.e = 1 := rfl
example : paramsQ2.generatorCount = 4 := rfl

/-- Shape of a ramified quadratic field: `n = 2`, `f = 1`, `q_K = 2`. -/
def paramsRamifiedQuadratic : FieldParameters :=
  { n := 2, f := 1, qK := 2, qK_eq := rfl, one_le_n := by norm_num, one_le_f := le_refl 1,
    f_dvd_n := one_dvd 2 }

/-- Shape of the unramified quadratic field `ℚ₂(√5)`: `n = 2`, `f = 2`, `q_K = 4`. -/
def paramsUnramifiedQuadratic : FieldParameters :=
  { n := 2, f := 2, qK := 4, qK_eq := rfl, one_le_n := by norm_num, one_le_f := by norm_num,
    f_dvd_n := dvd_refl 2 }

example : paramsRamifiedQuadratic.e = 2 := rfl
example : paramsUnramifiedQuadratic.e = 1 := rfl

/-! The five quadratic endpoints of plan §1 / ledger §7, as *shapes* only — the field-theoretic
identification of each branch is F4/AS work and is not proved here.  `η` is left as a variable
precisely because no row's compatibility or validity depends on it:

| field | branch row | source |
|---|---|---|
| `ℚ₂(√-2)` | `N0 2` (compact `N₂`, `r = 0`, `q_K = 2`) | draft §7.1 |
| `ℚ₂(√2)` | `M0 3` (compact `M₃`, `m = 4`) | draft §7.2 |
| `ℚ₂(√5)` | `M0 2` (compact `M₂`, `m = 2`; `f = 2`, `q_K = 4`) | draft §7.2 |
| `ℚ₂(√10)` | `Mpc 2 1 false η` (`B = x₁`, i.e. `p = 0`, so `ε = false`) | draft §7.3 |
| `ℚ₂(√-10)` | `Mpc 2 1 true η` (`(r, ε, η) = (1, 1, 1)`) | packet Cor. 8.2 (not the sign row) |
-/

example : Compatible paramsRamifiedQuadratic (.N0 2) := by decide
example : Compatible paramsRamifiedQuadratic (.M0 3) := by decide
example : Compatible paramsUnramifiedQuadratic (.M0 2) := by decide
example (η : ℤ_[2]ˣ) : Compatible paramsRamifiedQuadratic (.Mpc 2 1 false η) :=
  compatible_of_isEven rfl (by decide)
example (η : ℤ_[2]ˣ) : Compatible paramsRamifiedQuadratic (.Mpc 2 1 true η) :=
  compatible_of_isEven rfl (by decide)

example : (BranchData.N0 2).Valid := by decide
example : (BranchData.M0 3).Valid := by decide
example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 true η).Valid := ⟨le_refl 2, le_refl 1⟩
example (η : ℤ_[2]ˣ) : (BranchData.Npc 2 1 η).Valid := ⟨le_refl 2, le_refl 1⟩

example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 true η).labuteType = .M 2 := rfl
example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 true η).pVal = 1 := rfl
example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 false η).pVal = 0 := rfl
example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 true η).sVal = 2 := rfl
example : m 3 = 4 := rfl
example : m 2 = 2 := rfl
example : (BranchData.N0 2).IsCompactRow := rfl
example (η : ℤ_[2]ˣ) : (BranchData.Mpc 2 1 true η).IsProcyclicRow := le_refl 1

example : handleCount paramsRamifiedQuadratic (.N0 2) = 0 := rfl
example : handleCount paramsQ2 .L = 0 := rfl

end Stress

end GQ2.Dyadic
