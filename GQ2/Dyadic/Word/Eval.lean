/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Syntax
public import GQ2.Dyadic.Word.Blocks
public import GQ2.GammaA

@[expose] public section

/-!
# Dyadic campaign, layer F2 (semantics): denotations of `PWord` and the generic word quadruple

Two denotations of the reflected syntax of `GQ2/Dyadic/Word/Syntax.lean`, and — once and
generically — the four lemmas that the `ℚ₂` development hand-writes for *every* relator word
(recon survey `docs/dyadic/recon/wc-survey.md` §1c: "profinite form / `ℕ`-exponent form / `_eq_`
bridge / `_map` naturality, ~4 hand-written lemmas per word").

## The two denotations

* `PWord.eval μ` — the **profinite denotation**, into any compact totally disconnected
  topological group, with `GQ2.zpowHat` (`^ᶻ`) for `profPow` and `padicOmega2` for `z2pow`.
  This is the honest reading of a word: `ω₂` is the genuine element of `ℤ̂`.
* `PWord.evalFin μ E E₂` — the **finite denotation** of packet Lem. 2.2, into *any* group (no
  topology): an `ω₂`-power is the `2`-primary component `GQ2.powOmega2` of its base, so no global
  integer representative is selected (packet Rem. 2.3: "finite evaluation should reduce the last
  kind by Lem. 2.2; this avoids selecting global integer representatives").  Over a finite group
  it agrees with `eval` on every `ω₂`-only word with **no** side condition (`eval_eq_evalFin`).
* `PWord.evalZ μ E E₂` — the auxiliary **integer-exponent denotation**, where *every* profinite
  exponent is resolved to an ordinary integer by `E`, `E₂`.  `PWord.evalNat μ e` is the
  single-exponent case `E = E₂ = e`, which is exactly the `wildValueExp`/`wildValueExpR` pattern
  of the `ℚ₂` files (`GQ2/FoxHeisenberg/Traced.lean:75`, `GQ2/Roe/Words.lean:165`) — the form
  that survives into `FreeGroup`, where `ω₂` cannot be applied.

## The quadruple (`wc-survey` §1c), proved once

1. **profinite/finite agreement** — `PWord.eval_eq_evalFin`, `PWord.eval_omega2Pow` (`w^{ω₂}`
   evaluates to the `2`-primary part `powOmega2` in a finite group) and
   `PWord.map_eval_omega2Pow` (the literal `GQ2.map_zpowHat_omega2` pattern);
2. **`ℕ`-exponent form and the `_of_dvd` bridge** — `PWord.eval_eq_evalZ`,
   `PWord.eval_eq_evalNat_of_dvd`, `PWord.eval_eq_evalNat_exponent`,
   `PWord.evalFin_eq_evalNat_of_dvd`;
3. **naturality** — `PWord.map_eval` (`ContinuousMonoidHom`), `PWord.map_evalFin` and
   `PWord.map_evalZ` (any `MonoidHomClass`, no topology), `Marking.map_eval`;
4. **evaluation through a quotient** — `PWord.eval_map_eq_one_iff`,
   `Marking.eval_map_eq_one_iff`: the generic form of `GQ2.map_wildRelator_eq_one_iff`.

## Specialization soundness

* `PWord.eval_subst` — evaluation of a substituted word is evaluation at the substituted marking;
* `Marking.eval_killWild` — Gate B step 0 (`specialize_tame`): killing the wild letters
  syntactically is evaluating in the wild-trivialized marking;
* `PWord.eval_pro2` / `Marking.eval_pro2` — Gate C (`specialize_pro2`): in a pro-`2` marking
  (`τ = 1` and `x^{ω₂} = x`) the rewritten word evaluates to the same element;
* `PWord.eval_omega2Pow_eq_one_of_odd`, `zpowHat_etaHatZ_of_odd` (in `Syntax.lean`) — the
  semantic content of Gate B's audited rules **T1** ("`ω₂` kills pro-odd elements") and **T2**
  ("`η̂` fixes them; only `ω₂` kills").

## Stress tests

`GQ2/Dyadic/Word/Syntax.lean`'s `deltaW 0` and `sigma2W` at `n = 1` are, definitionally, the
`Γ_A` ledger letters `d₀` and `σ₂` of `GQ2/GammaA.lean`; the `private` bridge lemmas of
`GQ2/GammaA.lean:107-139` are re-derived here from the generic theorems through F1's `equivQ2`
adapter (`stress_map_d0`, `stress_map_sigma2`).  A `ZMod 8` evaluation with a *genuine* `ℤ̂`
exponent (`eval_zmod8`, `eval_zmod8_delta`) pins the finite evaluation numerically, in the style
of `GQ2.wildValueExpR_zmod8`.

## Implementation notes

`module`-style: all three in-repo imports are `module`-style.  Following `GQ2/Zhat.lean`, the
profinite carrier is `Type` (universe `0`) because `GQ2.zpowHat` is; the alphabet `X` is
universe-polymorphic, and `evalZ` — which needs no topology — is universe-polymorphic in the
target too.
-/

namespace GQ2.Dyadic

/-! ## The integer-exponent denotation -/

namespace PWord

section ConjHelpers

variable {G H : Type*} [Group G] [Group H]

private theorem map_conjR' {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (x g : G) :
    f (conjR x g) = conjR (f x) (f g) := by simp [conjR]

private theorem map_commR' {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (x y : G) :
    f (commR x y) = commR (f x) (f y) := by simp [commR]

end ConjHelpers

section EvalZ

variable {X : Type*} {G : Type*} [Group G]

/-- The **integer-exponent denotation**: a word is evaluated in an arbitrary group after the
profinite exponents have been replaced by ordinary integers supplied by the *resolvers* `E`
(for `ℤ̂`) and `E₂` (for `ℤ₂`).

No topology is involved, so this denotation is available in `FreeGroup`, in module lifts, and in
every other target where `^ᶻ` is meaningless.  Packet Lem. 2.2 is what makes it agree with the
profinite denotation over a finite group; the agreement is `eval_eq_evalZ`. -/
def evalZ (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord X → G
  | .one => 1
  | .gen g => μ g
  | .mul u v => evalZ μ E E₂ u * evalZ μ E E₂ v
  | .inv u => (evalZ μ E E₂ u)⁻¹
  | .conj u g => conjR (evalZ μ E E₂ u) (evalZ μ E E₂ g)
  | .comm u v => commR (evalZ μ E E₂ u) (evalZ μ E E₂ v)
  | .zpow u k => evalZ μ E E₂ u ^ k
  | .z2pow u z => evalZ μ E E₂ u ^ E₂ z
  | .profPow u γ => evalZ μ E E₂ u ^ E γ

variable (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

@[simp] theorem evalZ_one : evalZ μ E E₂ .one = 1 := rfl
@[simp] theorem evalZ_gen (g : X) : evalZ μ E E₂ (.gen g) = μ g := rfl
@[simp] theorem evalZ_mul (u v : PWord X) :
    evalZ μ E E₂ (.mul u v) = evalZ μ E E₂ u * evalZ μ E E₂ v := rfl
@[simp] theorem evalZ_inv (u : PWord X) : evalZ μ E E₂ (.inv u) = (evalZ μ E E₂ u)⁻¹ := rfl
@[simp] theorem evalZ_conj (u g : PWord X) :
    evalZ μ E E₂ (.conj u g) = conjR (evalZ μ E E₂ u) (evalZ μ E E₂ g) := rfl
@[simp] theorem evalZ_comm (u v : PWord X) :
    evalZ μ E E₂ (.comm u v) = commR (evalZ μ E E₂ u) (evalZ μ E E₂ v) := rfl
@[simp] theorem evalZ_zpow (u : PWord X) (k : ℤ) :
    evalZ μ E E₂ (.zpow u k) = evalZ μ E E₂ u ^ k := rfl
@[simp] theorem evalZ_z2pow (u : PWord X) (z : ℤ_[2]) :
    evalZ μ E E₂ (.z2pow u z) = evalZ μ E E₂ u ^ E₂ z := rfl
@[simp] theorem evalZ_profPow (u : PWord X) (γ : Zhat) :
    evalZ μ E E₂ (.profPow u γ) = evalZ μ E E₂ u ^ E γ := rfl

@[simp] theorem evalZ_invConj (u g : PWord X) :
    evalZ μ E E₂ (u ^⁻ g) = conjR (evalZ μ E E₂ u)⁻¹ (evalZ μ E E₂ g) := rfl

theorem evalZ_prodList : ∀ ws : List (PWord X),
    evalZ μ E E₂ (prodList ws) = (ws.map (evalZ μ E E₂)).prod
  | [] => rfl
  | w :: ws => by rw [prodList_cons, evalZ_mul, evalZ_prodList ws, List.map_cons, List.prod_cons]

/-- **The `ℕ`-exponent form**: every profinite exponent is replaced by one and the same integer
`e`.  This is the shape of `GQ2.FoxH.wildValueExp` and `GQ2.wildValueExpR`, generated here rather
than hand-written per word. -/
def evalNat (μ : X → G) (e : ℕ) : PWord X → G :=
  evalZ μ (fun _ ↦ (e : ℤ)) (fun _ ↦ (e : ℤ))

variable (e : ℕ)

@[simp] theorem evalNat_one : evalNat μ e .one = 1 := rfl
@[simp] theorem evalNat_gen (g : X) : evalNat μ e (.gen g) = μ g := rfl
@[simp] theorem evalNat_mul (u v : PWord X) :
    evalNat μ e (.mul u v) = evalNat μ e u * evalNat μ e v := rfl
@[simp] theorem evalNat_inv (u : PWord X) : evalNat μ e (.inv u) = (evalNat μ e u)⁻¹ := rfl
@[simp] theorem evalNat_conj (u g : PWord X) :
    evalNat μ e (.conj u g) = conjR (evalNat μ e u) (evalNat μ e g) := rfl
@[simp] theorem evalNat_comm (u v : PWord X) :
    evalNat μ e (.comm u v) = commR (evalNat μ e u) (evalNat μ e v) := rfl
@[simp] theorem evalNat_zpow (u : PWord X) (k : ℤ) :
    evalNat μ e (.zpow u k) = evalNat μ e u ^ k := rfl
@[simp] theorem evalNat_z2pow (u : PWord X) (z : ℤ_[2]) :
    evalNat μ e (.z2pow u z) = evalNat μ e u ^ e := zpow_natCast _ _
@[simp] theorem evalNat_profPow (u : PWord X) (γ : Zhat) :
    evalNat μ e (.profPow u γ) = evalNat μ e u ^ e := zpow_natCast _ _
@[simp] theorem evalNat_omega2Pow (u : PWord X) :
    evalNat μ e (omega2Pow u) = evalNat μ e u ^ e := zpow_natCast _ _

/-! ### The finite denotation of packet Lem. 2.2 -/

/-- The **finite denotation** of packet Lem. 2.2: an `ω₂`-power is evaluated as the `2`-primary
component `GQ2.powOmega2` of its base — *no* global integer representative is selected, which is
exactly what the packet's "Lean encoding" remark asks for — while any other profinite or `ℤ₂`
exponent is resolved to an ordinary integer by `E`/`E₂`.

Like `evalZ`, and unlike `eval`, this denotation needs no topology; over a finite group it agrees
with the profinite denotation on every `ω₂`-only word with **no side condition at all**
(`eval_eq_evalFin`). -/
noncomputable def evalFin (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord X → G
  | .one => 1
  | .gen g => μ g
  | .mul u v => evalFin μ E E₂ u * evalFin μ E E₂ v
  | .inv u => (evalFin μ E E₂ u)⁻¹
  | .conj u g => conjR (evalFin μ E E₂ u) (evalFin μ E E₂ g)
  | .comm u v => commR (evalFin μ E E₂ u) (evalFin μ E E₂ v)
  | .zpow u k => evalFin μ E E₂ u ^ k
  | .z2pow u z => evalFin μ E E₂ u ^ E₂ z
  | .profPow u γ => @ite _ (γ = omega2) (Classical.propDecidable _)
      (powOmega2 (evalFin μ E E₂ u)) (evalFin μ E E₂ u ^ E γ)

@[simp] theorem evalFin_one : evalFin μ E E₂ .one = 1 := rfl
@[simp] theorem evalFin_gen (g : X) : evalFin μ E E₂ (.gen g) = μ g := rfl
@[simp] theorem evalFin_mul (u v : PWord X) :
    evalFin μ E E₂ (.mul u v) = evalFin μ E E₂ u * evalFin μ E E₂ v := rfl
@[simp] theorem evalFin_inv (u : PWord X) :
    evalFin μ E E₂ (.inv u) = (evalFin μ E E₂ u)⁻¹ := rfl
@[simp] theorem evalFin_conj (u g : PWord X) :
    evalFin μ E E₂ (.conj u g) = conjR (evalFin μ E E₂ u) (evalFin μ E E₂ g) := rfl
@[simp] theorem evalFin_comm (u v : PWord X) :
    evalFin μ E E₂ (.comm u v) = commR (evalFin μ E E₂ u) (evalFin μ E E₂ v) := rfl
@[simp] theorem evalFin_zpow (u : PWord X) (k : ℤ) :
    evalFin μ E E₂ (.zpow u k) = evalFin μ E E₂ u ^ k := rfl
@[simp] theorem evalFin_z2pow (u : PWord X) (z : ℤ_[2]) :
    evalFin μ E E₂ (.z2pow u z) = evalFin μ E E₂ u ^ E₂ z := rfl

@[simp] theorem evalFin_profPow_omega2 (u : PWord X) :
    evalFin μ E E₂ (.profPow u omega2) = powOmega2 (evalFin μ E E₂ u) := by
  show @ite _ (omega2 = omega2) (Classical.propDecidable _) _ _ = _
  rw [if_pos rfl]

theorem evalFin_profPow_of_ne (u : PWord X) {γ : Zhat} (h : γ ≠ omega2) :
    evalFin μ E E₂ (.profPow u γ) = evalFin μ E E₂ u ^ E γ := by
  show @ite _ (γ = omega2) (Classical.propDecidable _) _ _ = _
  rw [if_neg h]

@[simp] theorem evalFin_omega2Pow (u : PWord X) :
    evalFin μ E E₂ (omega2Pow u) = powOmega2 (evalFin μ E E₂ u) :=
  evalFin_profPow_omega2 μ E E₂ u

end EvalZ

section MapEvalFin

variable {X : Type*} {G H : Type*} [Group G] [Group H] [Finite G]

/-- **Naturality of the finite denotation**: the `powOmega2` calculus is natural
(`GQ2.powOmega2_map`), so the finite form transports along every group homomorphism. -/
theorem map_evalFin (f : G →* H) (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    f (evalFin μ E E₂ w) = evalFin (fun g ↦ f (μ g)) E E₂ w := by
  induction w with
  | one => exact map_one f
  | gen g => rfl
  | mul u v ihu ihv => rw [evalFin_mul, evalFin_mul, map_mul, ihu, ihv]
  | inv u ih => rw [evalFin_inv, evalFin_inv, map_inv, ih]
  | conj u g ihu ihg => rw [evalFin_conj, evalFin_conj, map_conjR', ihu, ihg]
  | comm u v ihu ihv => rw [evalFin_comm, evalFin_comm, map_commR', ihu, ihv]
  | zpow u k ih => rw [evalFin_zpow, evalFin_zpow, map_zpow, ih]
  | z2pow u z ih => rw [evalFin_z2pow, evalFin_z2pow, map_zpow, ih]
  | profPow u γ ih =>
      by_cases h : γ = omega2
      · subst h
        rw [evalFin_profPow_omega2, evalFin_profPow_omega2, powOmega2_map, ih]
      · rw [evalFin_profPow_of_ne _ _ _ _ h, evalFin_profPow_of_ne _ _ _ _ h, map_zpow, ih]

end MapEvalFin

/-! ### Naturality of the integer-exponent denotation -/

section MapEvalZ

variable {X : Type*} {G H : Type*} [Group G] [Group H]

/-- **Naturality of the integer-exponent denotation**, for any monoid homomorphism and with no
finiteness or topology: `evalZ` uses only `mul`, `inv`, `zpow`, `conjR`, `commR`. -/
theorem map_evalZ {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (μ : X → G)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) :
    f (evalZ μ E E₂ w) = evalZ (fun g ↦ f (μ g)) E E₂ w := by
  induction w with
  | one => exact map_one f
  | gen g => rfl
  | mul u v ihu ihv => rw [evalZ_mul, evalZ_mul, map_mul, ihu, ihv]
  | inv u ih => rw [evalZ_inv, evalZ_inv, map_inv, ih]
  | conj u g ihu ihg => rw [evalZ_conj, evalZ_conj, map_conjR', ihu, ihg]
  | comm u v ihu ihv => rw [evalZ_comm, evalZ_comm, map_commR', ihu, ihv]
  | zpow u k ih => rw [evalZ_zpow, evalZ_zpow, map_zpow, ih]
  | z2pow u z ih => rw [evalZ_z2pow, evalZ_z2pow, map_zpow, ih]
  | profPow u γ ih => rw [evalZ_profPow, evalZ_profPow, map_zpow, ih]

theorem map_evalNat {F : Type*} [FunLike F G H] [MonoidHomClass F G H] (f : F) (μ : X → G)
    (e : ℕ) (w : PWord X) : f (evalNat μ e w) = evalNat (fun g ↦ f (μ g)) e w :=
  map_evalZ f μ _ _ w

/-- Substitution is composition of denotations (the `substitute_generators` half of
`specialization.py`). -/
theorem evalZ_subst {Y : Type*} (μ : Y → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (φ : X → PWord Y) (w : PWord X) :
    evalZ μ E E₂ (subst φ w) = evalZ (fun g ↦ evalZ μ E E₂ (φ g)) E E₂ w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [subst_mul, evalZ_mul, evalZ_mul, ihu, ihv]
  | inv u ih => rw [subst_inv, evalZ_inv, evalZ_inv, ih]
  | conj u g ihu ihg => rw [subst_conj, evalZ_conj, evalZ_conj, ihu, ihg]
  | comm u v ihu ihv => rw [subst_comm, evalZ_comm, evalZ_comm, ihu, ihv]
  | zpow u k ih => rw [subst_zpow, evalZ_zpow, evalZ_zpow, ih]
  | z2pow u z ih => rw [subst_z2pow, evalZ_z2pow, evalZ_z2pow, ih]
  | profPow u γ ih => rw [subst_profPow, evalZ_profPow, evalZ_profPow, ih]

end MapEvalZ

/-! ## The profinite denotation -/

section Eval

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The **profinite denotation** of a reflected word: `ℤ̂`-exponents are evaluated by
`GQ2.zpowHat`, and a `ℤ₂`-exponent `z` through the canonical splitting `padicOmega2 : ℤ₂ ↪ ℤ̂`
(so `z2pow u z` is the honest `ℤ₂`-power whenever the value of `u` is a pro-`2` element, and its
`2`-primary truncation in general). -/
noncomputable def eval (μ : X → G) : PWord X → G
  | .one => 1
  | .gen g => μ g
  | .mul u v => eval μ u * eval μ v
  | .inv u => (eval μ u)⁻¹
  | .conj u g => conjR (eval μ u) (eval μ g)
  | .comm u v => commR (eval μ u) (eval μ v)
  | .zpow u k => eval μ u ^ k
  | .z2pow u z => eval μ u ^ᶻ padicOmega2 z
  | .profPow u γ => eval μ u ^ᶻ γ

variable (μ : X → G)

@[simp] theorem eval_one : eval μ .one = 1 := rfl
@[simp] theorem eval_gen (g : X) : eval μ (.gen g) = μ g := rfl
@[simp] theorem eval_mul (u v : PWord X) : eval μ (.mul u v) = eval μ u * eval μ v := rfl
@[simp] theorem eval_inv (u : PWord X) : eval μ (.inv u) = (eval μ u)⁻¹ := rfl
@[simp] theorem eval_conj (u g : PWord X) :
    eval μ (.conj u g) = conjR (eval μ u) (eval μ g) := rfl
@[simp] theorem eval_comm (u v : PWord X) :
    eval μ (.comm u v) = commR (eval μ u) (eval μ v) := rfl
@[simp] theorem eval_zpow (u : PWord X) (k : ℤ) : eval μ (.zpow u k) = eval μ u ^ k := rfl
@[simp] theorem eval_z2pow (u : PWord X) (z : ℤ_[2]) :
    eval μ (.z2pow u z) = eval μ u ^ᶻ padicOmega2 z := rfl
@[simp] theorem eval_profPow (u : PWord X) (γ : Zhat) : eval μ (.profPow u γ) = eval μ u ^ᶻ γ :=
  rfl
@[simp] theorem eval_omega2PowHat (u : PWord X) : eval μ (omega2Pow u) = eval μ u ^ᶻ omega2 := rfl
@[simp] theorem eval_etaPow (u : PWord X) (η : ℤ_[2]) :
    eval μ (u.etaPow η) = eval μ u ^ᶻ etaHatZ η := rfl

@[simp] theorem eval_invConj (u g : PWord X) :
    eval μ (u ^⁻ g) = conjR (eval μ u)⁻¹ (eval μ g) := rfl

theorem eval_prodList : ∀ ws : List (PWord X),
    eval μ (prodList ws) = (ws.map (eval μ)).prod
  | [] => rfl
  | w :: ws => by rw [prodList_cons, eval_mul, eval_prodList ws, List.map_cons, List.prod_cons]

/-- **Substitution soundness**: evaluating a substituted word is evaluating the original word at
the substituted marking. -/
theorem eval_subst {Y : Type*} (μ : Y → G) (φ : X → PWord Y) (w : PWord X) :
    eval μ (subst φ w) = eval (fun g ↦ eval μ (φ g)) w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [subst_mul, eval_mul, eval_mul, ihu, ihv]
  | inv u ih => rw [subst_inv, eval_inv, eval_inv, ih]
  | conj u g ihu ihg => rw [subst_conj, eval_conj, eval_conj, ihu, ihg]
  | comm u v ihu ihv => rw [subst_comm, eval_comm, eval_comm, ihu, ihv]
  | zpow u k ih => rw [subst_zpow, eval_zpow, eval_zpow, ih]
  | z2pow u z ih => rw [subst_z2pow, eval_z2pow, eval_z2pow, ih]
  | profPow u γ ih => rw [subst_profPow, eval_profPow, eval_profPow, ih]

end Eval

/-! ### Quadruple, part 3: naturality of the profinite denotation -/

section MapEval

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [TotallyDisconnectedSpace H]

/-- **Naturality of the profinite denotation** under continuous homomorphisms of profinite
groups — the generic replacement for the per-letter `_map` lemmas of the `ℚ₂` ledgers
(`GQ2/GammaA.lean:107-139` and its `Γ_R` twin). -/
theorem map_eval (f : ContinuousMonoidHom G H) (μ : X → G) (w : PWord X) :
    f (eval μ w) = eval (fun g ↦ f (μ g)) w := by
  induction w with
  | one => exact map_one f
  | gen g => rfl
  | mul u v ihu ihv => rw [eval_mul, eval_mul, map_mul, ihu, ihv]
  | inv u ih => rw [eval_inv, eval_inv, map_inv, ih]
  | conj u g ihu ihg => rw [eval_conj, eval_conj, map_conjR', ihu, ihg]
  | comm u v ihu ihv => rw [eval_comm, eval_comm, map_commR', ihu, ihv]
  | zpow u k ih => rw [eval_zpow, eval_zpow, map_zpow, ih]
  | z2pow u z ih => rw [eval_z2pow, eval_z2pow, map_zpowHat, ih]
  | profPow u γ ih => rw [eval_profPow, eval_profPow, map_zpowHat, ih]

/-! ### Quadruple, part 4: evaluation through a quotient -/

/-- **Evaluation through a quotient**: a word dies in the image marking exactly when its value
lies in the kernel.  This is the generic form of `GQ2.map_wildRelator_eq_one_iff`. -/
theorem eval_map_eq_one_iff (f : ContinuousMonoidHom G H) (μ : X → G) (w : PWord X) :
    eval (fun g ↦ f (μ g)) w = 1 ↔ eval μ w ∈ f.toMonoidHom.ker := by
  rw [← map_eval f μ w, MonoidHom.mem_ker]
  exact Iff.rfl

end MapEval

/-! ## Quadruple, parts 1–2: finite evaluation (packet Lem. 2.2) -/

section Finite

variable {X : Type*} {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **Profinite/finite agreement** (packet Lem. 2.2): in a finite group, `w^{ω₂}` evaluates to
the `2`-primary component of the value of `w`. -/
@[simp] theorem eval_omega2Pow (μ : X → P) (u : PWord X) :
    eval μ (omega2Pow u) = powOmega2 (eval μ u) := by
  rw [eval_omega2PowHat, zpowHat_omega2]

/-- **The `map_zpowHat_omega2` pattern, once**: pushing an `ω₂`-power into a finite quotient
computes the finite `ω₂`-calculus of `GQ2/Words.lean`. -/
theorem map_eval_omega2Pow {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G] (f : ContinuousMonoidHom G P) (μ : X → G)
    (u : PWord X) : f (eval μ (omega2Pow u)) = powOmega2 (f (eval μ u)) := by
  rw [eval_omega2PowHat, map_zpowHat_omega2]

/-- **Gate B, rule T1**: `ω₂` kills a subword whose value has odd order — "tame inertia is
pro-odd, so `τ^{ω₂} = 1`" (packet Prop. 10.2, `specialization.py` rule T1). -/
theorem eval_omega2Pow_eq_one_of_odd (μ : X → P) (u : PWord X) (h : Odd (orderOf (eval μ u))) :
    eval μ (omega2Pow u) = 1 := by
  have hfac : (orderOf (eval μ u)).factorization 2 = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (by simpa [Nat.odd_iff, Nat.two_dvd_ne_zero] using h)
  rw [eval_omega2Pow, powOmega2, show omega2Exp (orderOf (eval μ u)) = 0 by simp [omega2Exp, hfac],
    pow_zero]

/-- **Gate B, rule T2**: an `η̂`-power fixes a subword whose value has odd order.  `η̂` does
*not* kill tame words — only `ω₂` does (`specialization.py`, rule T2). -/
theorem eval_etaPow_of_odd (μ : X → P) (u : PWord X) (η : ℤ_[2])
    (h : Odd (orderOf (eval μ u))) : eval μ (u.etaPow η) = eval μ u := by
  rw [eval_etaPow, zpowHat_etaHatZ_of_odd h]

/-- The `ω₂`-resolver at a level `N` killed by `x`: `x ^ᶻ ω₂ = x ^ omega2Exp N`. -/
theorem zpowHat_omega2_zpow {N : ℕ} (hN : N ≠ 0) {x : P} (hx : orderOf x ∣ N) :
    x ^ᶻ omega2 = x ^ (omega2Exp N : ℤ) := by
  rw [zpowHat_omega2, zpow_natCast, powOmega2_pow_eq x hx hN]

end Finite

/-! ### The resolver predicate and the two-form bridge -/

section Bridge

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- `ResolvedAt μ E E₂ w`: the integer resolvers `E`, `E₂` compute the profinite exponents of `w`
*at the elements actually reached* while evaluating `w` under `μ`.

This is the generic form of the per-subword order hypotheses of the `ℚ₂` `_of_dvd` bridges
(`GQ2.wildValueExpR_eq_wildValueR_of_dvd`, `GQ2.FoxH.wildValueExp_eq_wildValue_of_dvd`). -/
def ResolvedAt (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : PWord X → Prop
  | .one => True
  | .gen _ => True
  | .mul u v => ResolvedAt μ E E₂ u ∧ ResolvedAt μ E E₂ v
  | .inv u => ResolvedAt μ E E₂ u
  | .conj u g => ResolvedAt μ E E₂ u ∧ ResolvedAt μ E E₂ g
  | .comm u v => ResolvedAt μ E E₂ u ∧ ResolvedAt μ E E₂ v
  | .zpow u _ => ResolvedAt μ E E₂ u
  | .z2pow u z => ResolvedAt μ E E₂ u ∧ eval μ u ^ᶻ padicOmega2 z = eval μ u ^ E₂ z
  | .profPow u γ => ResolvedAt μ E E₂ u ∧ eval μ u ^ᶻ γ = eval μ u ^ E γ

/-- **The two-form bridge**: on a word whose profinite exponents are resolved, the profinite and
integer-exponent denotations agree. -/
theorem eval_eq_evalZ (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X)
    (hw : ResolvedAt μ E E₂ w) : eval μ w = evalZ μ E E₂ w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [eval_mul, evalZ_mul, ihu hw.1, ihv hw.2]
  | inv u ih => rw [eval_inv, evalZ_inv, ih hw]
  | conj u g ihu ihg => rw [eval_conj, evalZ_conj, ihu hw.1, ihg hw.2]
  | comm u v ihu ihv => rw [eval_comm, evalZ_comm, ihu hw.1, ihv hw.2]
  | zpow u k ih => rw [eval_zpow, evalZ_zpow, ih hw]
  | z2pow u z ih => rw [eval_z2pow, evalZ_z2pow, hw.2, ih hw.1]
  | profPow u γ ih => rw [eval_profPow, evalZ_profPow, hw.2, ih hw.1]

/-- On an `ω₂`-only word, a resolver correct for `ω₂` on all of `G` resolves everything. -/
theorem resolvedAt_of_isOmega2Only (μ : X → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hE : ∀ x : G, x ^ᶻ omega2 = x ^ E omega2) (w : PWord X) :
    w.IsOmega2Only → ResolvedAt μ E E₂ w := by
  induction w with
  | one => exact fun _ => trivial
  | gen g => exact fun _ => trivial
  | mul u v ihu ihv => exact fun h => ⟨ihu h.1, ihv h.2⟩
  | inv u ih => exact fun h => ih h
  | conj u g ihu ihg => exact fun h => ⟨ihu h.1, ihg h.2⟩
  | comm u v ihu ihv => exact fun h => ⟨ihu h.1, ihv h.2⟩
  | zpow u k ih => exact fun h => ih h
  | z2pow u z ih => exact fun h => h.elim
  | profPow u γ ih => exact fun h => ⟨ih h.2, by rw [h.1]; exact hE _⟩

end Bridge

section BridgeFinite

variable {X : Type*} {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]

/-- **The `_of_dvd` bridge** (packet Lem. 2.2, generic form): in a finite group an `ω₂`-only
word evaluates to its `ℕ`-exponent form at `omega2Exp N`, for any nonzero `N` killing every
element.  The `ℚ₂` development writes this out per word
(`GQ2.wildValueExpR_eq_wildValueR_of_dvd`, `GQ2.FoxH.wildValueExp_eq_wildValue_of_dvd`). -/
theorem eval_eq_evalNat_of_dvd {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : P, orderOf x ∣ N)
    (μ : X → P) {w : PWord X} (hw : w.IsOmega2Only) :
    eval μ w = evalNat μ (omega2Exp N) w :=
  eval_eq_evalZ μ _ _ w
    (resolvedAt_of_isOmega2Only μ _ _ (fun x ↦ zpowHat_omega2_zpow hN (hord x)) w hw)

/-- The `_of_dvd` bridge at the canonical level `N = Monoid.exponent P`. -/
theorem eval_eq_evalNat_exponent (μ : X → P) {w : PWord X} (hw : w.IsOmega2Only) :
    eval μ w = evalNat μ (omega2Exp (Monoid.exponent P)) w :=
  eval_eq_evalNat_of_dvd Monoid.exponent_ne_zero_of_finite
    (fun x ↦ Monoid.order_dvd_exponent x) μ hw

/-- **Quadruple, part 1 in its sharpest form** (packet Lem. 2.2): over a finite group the
profinite denotation *is* the `powOmega2` denotation, on every `ω₂`-only word, with no exponent
level, no divisibility hypothesis and no choice of integer representative. -/
theorem eval_eq_evalFin (μ : X → P) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X)
    (hw : w.IsOmega2Only) : eval μ w = evalFin μ E E₂ w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [eval_mul, evalFin_mul, ihu hw.1, ihv hw.2]
  | inv u ih => rw [eval_inv, evalFin_inv, ih hw]
  | conj u g ihu ihg => rw [eval_conj, evalFin_conj, ihu hw.1, ihg hw.2]
  | comm u v ihu ihv => rw [eval_comm, evalFin_comm, ihu hw.1, ihv hw.2]
  | zpow u k ih => rw [eval_zpow, evalFin_zpow, ih hw]
  | z2pow u z ih => exact hw.elim
  | profPow u γ ih =>
      obtain ⟨rfl, hu⟩ := hw
      rw [eval_profPow, zpowHat_omega2, evalFin_profPow_omega2, ih hu]

/-- The two finite forms agree on the `ω₂`-only fragment: choosing the global representative
`omega2Exp N` computes the `2`-primary components. -/
theorem evalFin_eq_evalNat_of_dvd {N : ℕ} (hN : N ≠ 0) (hord : ∀ x : P, orderOf x ∣ N)
    (μ : X → P) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {w : PWord X} (hw : w.IsOmega2Only) :
    evalFin μ E E₂ w = evalNat μ (omega2Exp N) w :=
  (eval_eq_evalFin μ E E₂ w hw).symm.trans (eval_eq_evalNat_of_dvd hN hord μ hw)

end BridgeFinite

/-! ## Gate C soundness -/

section Pro2

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- **Gate C soundness** (`specialize_pro2`): in a marking that is already pro-`2` on the nose —
`τ ↦ 1` and `x^{ω₂} = x` for every `x` — the rewritten word evaluates to the same element as the
original.  The two hypotheses are exactly the two facts `specialization.py` records for the
maximal pro-`2` quotient. -/
theorem eval_pro2 (μ : Generator n → G) (hτ : μ .tau = 1) (hω : ∀ x : G, x ^ᶻ omega2 = x)
    (w : PWord (Generator n)) : eval μ (pro2 w) = eval μ w := by
  induction w with
  | one => rfl
  | gen g =>
      cases g with
      | sigma => rfl
      | tau => rw [pro2_gen_tau, eval_one, eval_gen, hτ]
      | wild i => rfl
  | mul u v ihu ihv => rw [pro2_mul, eval_mul, eval_mul, ihu, ihv]
  | inv u ih => rw [pro2_inv, eval_inv, eval_inv, ih]
  | conj u g ihu ihg => rw [pro2_conj, eval_conj, eval_conj, ihu, ihg]
  | comm u v ihu ihv => rw [pro2_comm, eval_comm, eval_comm, ihu, ihv]
  | zpow u k ih => rw [pro2_zpow, eval_zpow, eval_zpow, ih]
  | z2pow u z ih => rw [pro2_z2pow, eval_z2pow, eval_z2pow, ih]
  | profPow u γ ih =>
      by_cases h : γ = omega2
      · subst h
        rw [pro2_profPow_omega2, ih, eval_profPow, hω]
      · rw [pro2_profPow_of_ne _ h, eval_profPow, eval_profPow, ih]

end Pro2

end PWord

/-! ## Marking-level API -/

namespace Marking

section Plain

variable {n : ℕ} {G H : Type*} [Group G] [Group H]

/-- The marking with every wild letter set to `1` — the semantic side of Gate B's step 0. -/
def killWildLetters (t : Marking n G) : Marking n G := ofLetters t.σ t.τ (fun _ ↦ 1)

@[simp] theorem killWildLetters_σ (t : Marking n G) : (killWildLetters t).σ = t.σ := rfl
@[simp] theorem killWildLetters_τ (t : Marking n G) : (killWildLetters t).τ = t.τ := rfl
@[simp] theorem killWildLetters_x (t : Marking n G) (i : Fin (n + 1)) :
    (killWildLetters t).x i = 1 := rfl

/-- The `n = 1` adapter of `GQ2/Dyadic/Parameters.lean` commutes with pushforward. -/
theorem ofQ2_map (f : G →* H) (t : _root_.GQ2.Marking G) :
    (ofQ2 t).map ⇑f = ofQ2 (t.map f) := by
  ext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      obtain ⟨v, hv⟩ := i
      match v, hv with
      | 0, _ => rfl
      | 1, _ => rfl
      | (k + 2), h => exact absurd h (by lia)

end Plain

variable {n : ℕ} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- The profinite denotation at a marking. -/
noncomputable def eval (t : Marking n G) (w : PWord (Generator n)) : G := PWord.eval ⇑t w

theorem eval_def (t : Marking n G) (w : PWord (Generator n)) : t.eval w = PWord.eval ⇑t w := rfl

@[simp] theorem eval_gen (t : Marking n G) (g : Generator n) : t.eval (.gen g) = t g := rfl
@[simp] theorem eval_one (t : Marking n G) : t.eval .one = 1 := rfl
@[simp] theorem eval_mul (t : Marking n G) (u v : PWord (Generator n)) :
    t.eval (.mul u v) = t.eval u * t.eval v := rfl
@[simp] theorem eval_inv (t : Marking n G) (u : PWord (Generator n)) :
    t.eval (.inv u) = (t.eval u)⁻¹ := rfl

/-- `σ₂` evaluates to the `ω₂`-power of the `σ`-letter. -/
@[simp] theorem eval_sigma2W (t : Marking n G) : t.eval sigma2W = t.σ ^ᶻ omega2 := rfl

/-- `δ_i` evaluates to `(x_i τ)^{ω₂} x_i⁻¹`. -/
@[simp] theorem eval_deltaW (t : Marking n G) (i : Fin (n + 1)) :
    t.eval (deltaW i) = ((t.x i * t.τ) ^ᶻ omega2) * (t.x i)⁻¹ := rfl

/-- **Naturality at the marking level**: the generic replacement for the per-letter bridges of
`GQ2/GammaA.lean`. -/
theorem map_eval {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] (f : ContinuousMonoidHom G H)
    (t : Marking n G) (w : PWord (Generator n)) : f (t.eval w) = (t.map ⇑f).eval w :=
  PWord.map_eval f _ w

/-- **Evaluation through a quotient at the marking level** — the generic form of
`GQ2.map_wildRelator_eq_one_iff`: a relator dies in the pushed marking iff its value lies in the
kernel. -/
theorem eval_map_eq_one_iff {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [TotallyDisconnectedSpace H] (f : ContinuousMonoidHom G H)
    (t : Marking n G) (w : PWord (Generator n)) :
    (t.map ⇑f).eval w = 1 ↔ t.eval w ∈ f.toMonoidHom.ker :=
  PWord.eval_map_eq_one_iff f _ w

/-! ### Gate B: killing the wild letters -/

/-- **Gate B soundness** (`specialize_tame`, step 0): killing the wild generators syntactically
is the same as evaluating in the marking whose wild letters are trivial. -/
theorem eval_killWild (t : Marking n G) (w : PWord (Generator n)) :
    t.eval (killWild w) = (killWildLetters t).eval w := by
  rw [eval_def, killWild, PWord.eval_subst, eval_def]
  congr 1
  funext g
  cases g <;> rfl

/-- **Gate C soundness** at the marking level. -/
theorem eval_pro2 (t : Marking n G) (hτ : t.τ = 1) (hω : ∀ x : G, x ^ᶻ omega2 = x)
    (w : PWord (Generator n)) : t.eval (pro2 w) = t.eval w :=
  PWord.eval_pro2 _ hτ hω w

end Marking

/-! ## Stress tests

Nothing below is cited by a proof: these are regression pins in the sense of plan §3 A1
("adapters at `n = 1` cross-check the generic rows against the existing `Γ_A`/`Γ_R` hand rows"). -/

section StressGammaA

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P]
  [Finite P]

/-- The `n = 1` `δ₀`-letter **is**, definitionally, the `Γ_A` ledger letter `d₀` of
`GQ2/GammaA.lean` (through F1's `equivQ2` adapter). -/
theorem eval_deltaW_zero_eq_d0Hat (t : _root_.GQ2.Marking G) :
    (Marking.ofQ2 t).eval (deltaW 0) = t.d0Hat := rfl

/-- The `n = 1` `σ₂`-letter **is**, definitionally, the `Γ_A` ledger letter `σ₂`. -/
theorem eval_sigma2W_eq_sigma2Hat (t : _root_.GQ2.Marking G) :
    (Marking.ofQ2 t).eval sigma2W = t.sigma2Hat := rfl

/-- The same two pins spelled through F1's adapter `Marking.equivQ2` itself, rather than through
its `ofQ2` component. -/
theorem eval_deltaW_zero_equivQ2 (t : _root_.GQ2.Marking G) :
    (Marking.equivQ2.symm t).eval (deltaW 0) = t.d0Hat := rfl

theorem eval_sigma2W_equivQ2 (t : _root_.GQ2.Marking G) :
    (Marking.equivQ2.symm t).eval sigma2W = t.sigma2Hat := rfl

/-- In a finite group the profinite `δ₀`-letter computes the finite ledger letter `d₀` of
`GQ2/Words.lean`. -/
theorem eval_deltaW_zero_eq_d0 (s : _root_.GQ2.Marking P) :
    (Marking.ofQ2 s).eval (deltaW 0) = s.d0 := by
  rw [eval_deltaW_zero_eq_d0Hat]
  simp only [_root_.GQ2.Marking.d0Hat, _root_.GQ2.Marking.u0Hat, _root_.GQ2.Marking.uHat,
    _root_.GQ2.Marking.d0, _root_.GQ2.Marking.u0, _root_.GQ2.Marking.u, zpowHat_omega2]

/-- **Stress (`Γ_A` ledger at `n = 1`)**: the `private` bridge lemma `map_d0Hat` of
`GQ2/GammaA.lean:107-139` re-derived from the generic F2 theorems — naturality of the profinite
denotation plus packet Lem. 2.2, with no hand-written per-letter algebra. -/
theorem stress_map_d0 (f : ContinuousMonoidHom G P) (t : _root_.GQ2.Marking G) :
    (t.map f.toMonoidHom).d0 = f.toMonoidHom t.d0Hat := by
  have hc : (⇑f.toMonoidHom : G → P) = ⇑f := rfl
  have h2 : Marking.ofQ2 (t.map f.toMonoidHom) = (Marking.ofQ2 t).map ⇑f := by
    rw [← Marking.ofQ2_map, hc]
  rw [← eval_deltaW_zero_eq_d0, h2, ← Marking.map_eval, eval_deltaW_zero_eq_d0Hat]
  exact congrFun hc.symm _

/-- **Stress (`Γ_A` ledger at `n = 1`)**: the twin for `σ₂` (`map_sigma2Hat`). -/
theorem stress_map_sigma2 (f : ContinuousMonoidHom G P) (t : _root_.GQ2.Marking G) :
    (t.map f.toMonoidHom).sigma2 = f.toMonoidHom t.sigma2Hat := by
  have hc : (⇑f.toMonoidHom : G → P) = ⇑f := rfl
  have h1 : ∀ s : _root_.GQ2.Marking P, (Marking.ofQ2 s).eval sigma2W = s.sigma2 := fun s => by
    rw [eval_sigma2W_eq_sigma2Hat]
    simp only [_root_.GQ2.Marking.sigma2Hat, _root_.GQ2.Marking.sigma2, zpowHat_omega2]
  have h2 : Marking.ofQ2 (t.map f.toMonoidHom) = (Marking.ofQ2 t).map ⇑f := by
    rw [← Marking.ofQ2_map, hc]
  rw [← h1, h2, ← Marking.map_eval, eval_sigma2W_eq_sigma2Hat]
  exact congrFun hc.symm _

end StressGammaA

section StressZMod8

local instance : TopologicalSpace (Multiplicative (ZMod 8)) := ⊥
local instance : DiscreteTopology (Multiplicative (ZMod 8)) := ⟨rfl⟩

/-- A concrete `n = 1` marking `(σ, τ, x₀, x₁) = (5, 1, 1, 1)` (written additively) in
`Multiplicative (ZMod 8)`, in the style of `GQ2.zmod8MarkingR`. -/
def zmod8Marking : Marking 1 (Multiplicative (ZMod 8)) :=
  Marking.ofLetters (Multiplicative.ofAdd 5) (Multiplicative.ofAdd 1)
    ![Multiplicative.ofAdd 1, Multiplicative.ofAdd 1]

/-- `omega2Exp 8 = 1`: on a group of exponent `8` the concrete `ω₂`-representative is `1`. -/
theorem omega2Exp_eight : omega2Exp 8 = 1 := by
  have hfac : (8 : ℕ).factorization 2 = 3 := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  norm_num [omega2Exp, hfac]

private theorem zmod8_orderOf_dvd (x : Multiplicative (ZMod 8)) : orderOf x ∣ 8 := by
  have h : ∀ y : Multiplicative (ZMod 8), y ^ 8 = 1 := by decide
  exact orderOf_dvd_of_pow_eq_one (h x)

/-- The test word `δ₀ · σ₂`, carrying two genuine `ℤ̂`-exponents. -/
noncomputable def zmod8Word : PWord (Generator 1) := .mul (deltaW 0) sigma2W

/-- **Stress (genuine `ω₂`)**: the *profinite* denotation — real `x ^ᶻ ω₂` powers, not a
hand-chosen integer exponent — of `δ₀ σ₂` at `zmod8Marking` is `ofAdd 6`.

Additively: `δ₀ = (x₀ + τ) − x₀ = 1` and `σ₂ = σ = 5`, so the product is `6`.  Pins the
placement of the `ω₂`-exponent on the `(x₀ τ)`-subword (a bare `x₀^{ω₂}` would give `5`) and the
trailing `x₀⁻¹` of `δ₀` (dropping it would give `7`). -/
theorem eval_zmod8 : zmod8Marking.eval zmod8Word = Multiplicative.ofAdd (6 : ZMod 8) := by
  rw [Marking.eval_def, PWord.eval_eq_evalNat_of_dvd (by norm_num) zmod8_orderOf_dvd,
    omega2Exp_eight]
  · decide
  · exact ⟨isOmega2Only_deltaW 0, isOmega2Only_sigma2W⟩

/-- **Stress (`ω₂` is not vacuous)**: the same evaluation with the exponent forced to `3` — an
odd non-`ω₂` representative — gives a *different* value (`3·2 − 1 + 3·5 = 4`), so the `ω₂`-slot
genuinely carries information at this marking. -/
theorem eval_zmod8_exponent_three :
    PWord.evalNat ⇑zmod8Marking 3 zmod8Word = Multiplicative.ofAdd (4 : ZMod 8) := by decide

end StressZMod8

end GQ2.Dyadic
