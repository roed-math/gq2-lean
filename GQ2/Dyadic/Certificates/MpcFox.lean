/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Words.Mpc
import GQ2.Dyadic.Certificates.M0Fox
import GQ2.Dyadic.Word.Stokes

/-!
# Dyadic campaign, ticket WMP-b: the Fox certificate of the procyclic `M_α` branch word

The certificate layer of the hardest branch lane, sitting on WMP-a's word
(`GQ2/Dyadic/Words/Mpc.lean`), WW1's Fox evaluator (`GQ2/Dyadic/Word/Fox.lean`), WW2's
certificate grammar (`GQ2/Dyadic/Word/FoxCert.lean`) and WW3's `heisJetZero` family
(`GQ2/Dyadic/Word/Stokes.lean`).  It carries packet Def. 9.1 items (3)–(4) for **row 5 of the
R5 selection freeze**, the procyclic-`M` relator

```
R_{M,pc} = R_lin^pc · R̂^pc · D₀²[D₀,D₁] · H_h,     R̂^pc = Sh_M(R_lin^pc)
R_lin^pc = A²[A,B] · C₀^{2^α}[C₀,D] · E₀₁^pc · E₂^pc
```

Two copies, one substitution.  The three deliverables are the **`Sh_M` operator** (§2), the
**σ-column coincidence lemma** (§4) and the **hat copy's vanishing first Fox derivative** (§5).

## `Sh_M` (§2) — the design decision, and why it is not on `Generator n`

S4.2's frozen substitution is

```
x₀ ↦ δ₀,  x₁ ↦ δ₁,  x₂ ↦ 1,  δ₀ ↦ δ₀,  δ₁ ↦ δ₁,  δ₂ ↦ 1,  τ ↦ 1,  σ ↦ σ,  σ₂ ↦ σ₂
```

with **the δ-letters atomic** — the memo is explicit that descending into them would send
`δ₀ ↦ (δ₀τ)^{ω₂}δ₀⁻¹`, which is *not* the draft's word.

`Sh_M` is therefore **not** definable as a `PWord (Generator n) → PWord (Generator n)`
substitution.  `PWord (Generator n)` is the *denotation* layer: `Export.denote` has already
inlined every `Auxiliary` wrapper, so in `Words.Mpc.dW h 0` the letter `δ₀` is literally the
word `(x₀τ)^{ω₂}x₀⁻¹`, and any generator-level substitution descends into it and produces
exactly the rejected reading.  The atomicity clause is not a side condition one can bolt on:
it is a statement about which letters *exist*.

So `Sh_M` is a genuine `PWord → PWord` transform on the **displayed alphabet**, which is the
memo's own formulation ("`Sh_M` is an endomorphism of the free profinite group on the
*displayed* alphabet"; "defined on displayed spellings only"):

```
shM : PWord MLetter → PWord MLetter := PWord.subst shLetter
```

`MLetter` reifies that alphabet, and δ-atomicity holds **by construction**.  Two further
letters are atoms because they are *displayed definitions* (`Auxiliary` nodes, charged once —
memo §1, §9.3 rule 3): `σ₂ = σ^{ω₂}` and the Tietze display `D = σ^{η̂}` (freeze row 5: "η is
immovable in this grammar; only the Tietze display is available").  Atomizing them is not an
extra assumption — `shM_omega2Pow_sigma` and `shM_profPow_sigma` prove that the expanded
readings are fixed *because* `σ ↦ σ`, so `σ₂ ↦ σ₂` and `D ↦ D` are **derived**, not postulated.
It also has a technical payoff: with them atomic, every displayed factor of the procyclic row
lies in the profinite-power-free fragment `PWord.NoProf`, which is what makes §3's transport
theorem a plain structural induction.

`inlineM h η : PWord MLetter → PWord (Generator (2 + 2*h))` is the bridge back to WMP-a's
words (`δ_i ↦ dW h i`, `σ₂ ↦ sigma2W`, `D ↦ η.toPWord`); the bridges
`inlineM_linFactorsM`/`inlineM_hatFactorsM` are `rfl`, so the displayed layer is a faithful
re-spelling of the emitted trees, not a parallel definition.

## The certificate shrink (§2) — `hatFactors` IS the `Sh_M`-image of `linFactors`

Stated at the **`foxEval` layer**, which is the register the memo's "up to a final
`normalize`" forces and the one both consumers need at once:

```
foxEval t a E E₂ (inlineM h η (shM (mpcLinM α r p)))  =  foxEval t a E E₂ (mpcHatW α r p η h)
```

`foxEval` values in `WordLift V C` carry the base value in `.g` and the Fox derivative in `.u`,
so this single equality delivers **both** halves of what the freeze asks for: the hat copy's
gates B and C are WMP-a's balance pair (`.g`), and its `d¹` is the raw word's under transport
(`.u`).  Syntactic equality is *not* available and the memo says so — three named obstructions,
all of them the substitution's own created units, none visible to `foxEval`:

1. `Sh_M(C₀) = 1·Ĉ₀` — the `x₂ ↦ 1` clause fires *inside* `C₀ = x₂σ₂^s`, where the emitted hat
   display writes the bare `Ĉ₀ = σ₂^s` (`shM_c0M`, an exact `rfl`);
2. `Sh_M(E₂^pc)` keeps its tree shape while every letter in it dies (`δ₂ ↦ 1`), so `Ê₂ = 1` is a
   *value* statement — which is precisely why the emitted hat display has **five** factors and
   no `Ê₂` (`foxEval_shM_e2M`);
3. `prodList`'s trailing `PWord.one`s (WMP-a authoring rule 4).

What *is* exactly syntactic is recorded as such, and those are the informative cases: `Ê₀₁ =
E₀₁` verbatim, `B ↦ B̂` on the nose, `D ↦ D`, and — memo §4 item 2 — **the whole tail of
eq. `Mpc-word` is shadow-stable**, `Sh_M(D₀²[D₀,D₁]) = D₀²[D₀,D₁]` and `Sh_M ∘ Sh_M = Sh_M`.

## The transport theorem (§3)

S4.2's P3 is an operator identity between the shadow's row and the *core*'s row, and the memo
**refutes the naive chain rule** for `w ↦ Sh_M(w)` (a Fox derivative of a profinite power is
not a fixed group-ring element — its finite representative is read at `2·ord(lower value)`, so
pushing `ρ` through the substitution turns `P` into `1`).  That refutation is not rediscovered
here.  What is formalized is the transport statement itself, in WW1's operator algebra:

> `foxD_subst_congr` — two inlinings of one displayed word have the same Fox row as soon as,
> letter by letter, their evaluations act equally on the coefficient module and their Fox
> derivatives agree.

The naive rule is exactly what this lemma does *not* say: it never pushes an operator through a
power node, which is why it survives on the fragment where the memo's counterexample lives —
and the `NoProf` hypothesis is where that discipline is visible.

## The σ-column coincidence lemma (§4)

Freeze row 5, binding: the Lean side needs **the σ-column coincidence lemma, not the
geometric-sum identity** `(1+S^a)[b] = (1+S^b)[a]`.  The statement is

> the two copies' σ-column entries are the **same operator**, so the product's σ-column
> vanishes **without either factor's vanishing**.

Formally, with `foxColumn` the `g`-entry of a Fox row read as an additive operator
(`v ↦ D(w)` at the offset vector supported on `g` alone):

```
foxColumn ⇑t E E₂ (mpcHatW α r p η h) .sigma = foxColumn ⇑t E E₂ (mpcLinW α r p η h) .sigma
```

and then `D(R_lin·R̂)`'s σ-column is `Φ + Φ = 0` in characteristic 2.  The proof is the
transport theorem applied to the two inlinings, whose only disagreements are at `τ, x₀, x₁, x₂,
δ₂` — letters that carry **no σ** (so their σ-columns are `0` on both sides) and act trivially
(so no prefix weight can tell the copies apart).  `D(σ₂)` — the Sage engine's opaque atom
`G[S;ω₂]` — is never computed; it cancels, exactly as on the compact row.

**Contrast with WM0-b's compact-M analogue**, which is instructive and *different*: there the
σ-column cancels **over ℤ**, because the balancing `σ₂^{2m}` sits behind the `A₀`-prefix, so the
differentiated Prop. 9.2 balance does the work and no characteristic hypothesis is spent
(`MCompact.foxD_mWordWith_core`).  Here the two σ-columns do **not** individually vanish, and
what kills the sum is `hV₂`.  Both facts are the same power balance seen from two sides; only
the compact one is a ℤ-statement, and conflating them would be an error.

The WW3 form is stated too, as mandated: `heisJetZero` is the "copies cancel" consumable, and
`sigmaColumn_heisJetZero` puts the coincidence where the second-order shadow enters.

## The hat copy's zero first Fox derivative (§5) — the headline

Draft Rem. 5.4: on ramified simples `R̂^pc` has zero first Fox derivative.  Proved here as
`foxD_mpcHatW_ram`, at general `(α, r, p)` and **every `η̂` display**, from the ramified
readings of the δ-row (`P = 0`: `D(δ_i) = −a(x_i)`) — and the two vanishing conditions the memo
names are visible in the proof as themselves: the free `δ₀/δ₁` row of the core cancels (`Â²`
against `[Â,B̂]` and `E₀₁`'s four δ-occurrences in pairs), and the σ-balance `bal = 0` is
WMP-a's `s_mul_two_pow`.

⚠ **The `E₀₁^pc` asymmetry is stated honestly and not hidden.**  Freeze row 5: `E₂^pc` is
first-order essential, **`E₀₁^pc` is first-order redundant** — the hat copy reproduces its
entire first-order contribution operator-for-operator, its justification is second-order only,
and **gate D cannot justify it**.  So the linear row is stated *with* `E₀₁^pc`'s first-order
contribution present and named (`foxD_e01W_ram`, a genuine nonzero `(1+S₂^a)`-type entry), and
next to it the theorem that the shadow reproduces exactly that contribution
(`foxD_e01_reproduced_by_shadow`).  **The two together are the finding**; either alone
misrepresents the row.  Nothing here rejects or justifies `E₀₁^pc` — that is a gate-D/second-
order statement and belongs to WMP-c.

## Certificates (§6)

WW2 normal forms at the classes the row supports, plus the `(1,1,1)` `√−10` instance — packet
Cor. 8.2, **merge gate 9**.  The handle columns are zero at first order at every `h`.

## Gotchas honoured (relayed with the ticket; all of them bit)

* the word is **not** `IsOmega2Only` (WMP-a's `not_isOmega2Only_mpcW_hat`) — every statement is
  quantified over the honest resolvers `E`, `E₂`, never over a numeric ω₂-exponent;
* `deltaC` silently collides with the frozen peripheral `GQ2.deltaC` (`GQ2/PeripheralAction.lean`)
  — WM0-b's `open … renaming deltaC → deltaCert` is reused verbatim;
* `S₂ = 1` is a **hypothesis** (`hS₂`), not an interpretation (WW2's binding rule);
* nested namespace `GQ2.Dyadic.Certificates.MProcyclic`, following WM0-a deviation 2 / WM0-b:
  `Certificates`, `Certificates.MCompact` and this file would otherwise collide.

## Dedup (recorded, not duplicated)

`Words.MCompact.deltaC h i` and `Words.Mpc.dW h i` are the **same `PWord`** — checked `rfl`
(`dW_eq_deltaCert`).  So WM0-b's δ-row lemmas `MCompact.foxD_deltaC_unram`,
`MCompact.foxD_deltaC_ram`, `MCompact.trivAct_deltaC`, `MCompact.trivAct_deltaBlock_unram`,
`MCompact.trivAct_deltaBlock_ram` are **cited, not re-derived**, as are its lane-generic
`foxD_prodList_pair`, `evalFin_prodList_pair`, `foxD_conj_of_trivial`,
`foxD_comm_of_trivial_right`, `trivAct_commR_right`, `sigmaGeom` + `foxD_sigma2Pow_natCast` +
`foxD_sigma2Pow_neg` and `sum_generator_quad`.  Genuinely new and lane-generic here (hoist
candidates for the WWH queue, beside WM0-b's seven): `foxColumn`, `PWord.NoProf`,
`evalFin_subst`, `foxEval_subst` and `foxD_subst_congr`.

## Implementation notes

**Not `module`-style, and forced**: `GQ2.Dyadic.Words.Mpc` is not `module`-style (it imports
F3's `TameBoundary`), and a `module` file may not import a non-`module` one — the WN0-a ruling
that `Words/` and `Certificates/` are plain-import layers.

**Audited axiom state**: every named declaration of this file depends on a subset of
`[propext, Classical.choice, Quot.sound]` (scratch audit over the full declaration list; not
committed).  Zero `sorryAx`, zero `native_decide` — kernel `decide` only — so the census is
untouched at eleven.
-/

namespace GQ2.Dyadic.Certificates.MProcyclic

open GQ2.FoxH GQ2.Dyadic.Words.Mpc

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## §1 Generic Fox toolkit

Lane-generic material the WMP row needs and no earlier lane produced.  All of it belongs beside
WWH's hoists in `GQ2/Dyadic/Word/Fox.lean`; it sits here because this ticket owns one file. -/

section Generic

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **The `g`-column of a Fox row**, as an additive operator.

`foxD` is additive in the offset vector (`foxD_add`), so a row *is* the sum of its columns and
a column is the row evaluated at an offset vector supported on one letter.  This is the Lean
form of "the σ-entry of the Fox row", the object freeze row 5's coincidence lemma is about. -/
noncomputable def foxColumn [DecidableEq X] [Finite A] [Finite C] (t : X → C) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) (g : X) : A →+ A :=
  (foxDHom t E E₂ w).comp (AddMonoidHom.single (fun _ : X => A) g)

@[simp] theorem foxColumn_apply [DecidableEq X] [Finite A] [Finite C] (t : X → C)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (w : PWord X) (g : X) (v : A) :
    foxColumn t E E₂ w g v = foxD t (Pi.single g v) E E₂ w := rfl

/-- **The displayed fragment over a letter set `P`**: `w` uses only letters satisfying `P`, and
no profinite or `ℤ₂`-power node.

Both restrictions are load-bearing in §3.

*No `profPow`*: every displayed factor of the procyclic row avoids it, because `σ₂` and
`D = σ^{η̂}` are displayed *definitions* — `Auxiliary` nodes — hence atoms of the displayed
alphabet.  This is what makes the transport theorem a plain structural induction: a `profPow`
node reads its finite representative at `2·ord(lower value)`, so two words with *equally acting*
evaluations need not have equally acting `ω₂`-powers.  That is the same phenomenon the shadow
memo's refutation of the naive chain rule turns on, and this predicate is where the discipline
is visible rather than assumed away.

*Only `P`-letters*: transport compares two inlinings, and they need only agree on the letters
that actually occur.  On this row that matters concretely — `τ` occurs in **no** displayed
factor (it lives inside the `δ`-atoms), and it is the one letter where the two inlinings
disagree beyond first order: `Sh_M` sends `τ ↦ 1` while `τ` itself acts nontrivially on every
ramified module.  Without the restriction the transport hypothesis would be false. -/
def _root_.GQ2.Dyadic.PWord.Displayed {Gen : Type*} (P : Gen → Prop) : PWord Gen → Prop
  | .one => True
  | .gen g => P g
  | .mul u v => u.Displayed P ∧ v.Displayed P
  | .inv u => u.Displayed P
  | .conj u g => u.Displayed P ∧ g.Displayed P
  | .comm u v => u.Displayed P ∧ v.Displayed P
  | .zpow u _ => u.Displayed P
  | .z2pow _ _ => False
  | .profPow _ _ => False

theorem displayed_prodList {Gen : Type*} {P : Gen → Prop} :
    ∀ {l : List (PWord Gen)}, (∀ w ∈ l, w.Displayed P) → (PWord.prodList l).Displayed P
  | [], _ => trivial
  | w :: _ws, hw =>
      ⟨hw w (List.mem_cons_self ..),
       displayed_prodList fun u hu => hw u (List.mem_cons_of_mem _ hu)⟩

/-- Substitution commutes with evaluation: evaluating a substituted word is evaluating the
original at the substituted marking.  ("`Sh_M` is **a substitution**, so it commutes with
evaluation.  Every theorem below is that one fact plus one hypothesis about the image." —
shadow memo §1.) -/
theorem evalFin_subst {Y : Type*} {G : Type*} [Group G] (μ : X → G) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (f : Y → PWord X) :
    ∀ w : PWord Y,
      PWord.evalFin μ E E₂ (PWord.subst f w)
        = PWord.evalFin (fun ℓ => PWord.evalFin μ E E₂ (f ℓ)) E E₂ w
  | .one => rfl
  | .gen _ => rfl
  | .mul u v => by
      simp only [PWord.subst_mul, PWord.evalFin_mul, evalFin_subst μ E E₂ f u,
        evalFin_subst μ E E₂ f v]
  | .inv u => by simp only [PWord.subst_inv, PWord.evalFin_inv, evalFin_subst μ E E₂ f u]
  | .conj u g => by
      simp only [PWord.subst_conj, PWord.evalFin_conj, evalFin_subst μ E E₂ f u,
        evalFin_subst μ E E₂ f g]
  | .comm u v => by
      simp only [PWord.subst_comm, PWord.evalFin_comm, evalFin_subst μ E E₂ f u,
        evalFin_subst μ E E₂ f v]
  | .zpow u k => by simp only [PWord.subst_zpow, PWord.evalFin_zpow, evalFin_subst μ E E₂ f u]
  | .z2pow u z => by simp only [PWord.subst_z2pow, PWord.evalFin_z2pow, evalFin_subst μ E E₂ f u]
  | .profPow u γ => by
      rcases eq_or_ne γ omega2 with rfl | hγ
      · simp only [PWord.subst_profPow, PWord.evalFin_profPow_omega2, evalFin_subst μ E E₂ f u]
      · simp only [PWord.subst_profPow, PWord.evalFin_profPow_of_ne _ _ _ _ hγ,
          evalFin_subst μ E E₂ f u]

/-- The same fact one level up, at the **Fox** evaluation: the Fox evaluation of a substituted
word is the Fox evaluation at the substituted *lift* marking.  This is the engine behind every
`Sh_M` statement in this file — it delivers the base value (`.g`) and the Fox derivative (`.u`)
in one stroke. -/
theorem foxEval_subst {Y : Type*} (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (f : Y → PWord X) (w : PWord Y) :
    foxEval t a E E₂ (PWord.subst f w)
      = PWord.evalFin (fun ℓ => foxEval t a E E₂ (f ℓ)) E E₂ w :=
  evalFin_subst (foxLift t a) E E₂ f w

end Generic

/-! ### The transport theorem

The Lean shape of S4.2's P3.  Two inlinings of one displayed word have the same Fox row as soon
as their letters agree "to first order": equal offsets, equally acting base values. -/

section Transport

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **First-order agreement of two Fox lift values**: the same `A`-offset (the Fox derivative)
and base values that act equally on the coefficient module.

This is the exact register the shadow substitution preserves.  It is *not* equality: the two
copies' base values are genuinely different group elements (`x₀` versus `δ₀`), and the whole
content of P4's jet clause is that they act the same.  Being a congruence for the `WordLift`
group operations, it propagates through a word for free. -/
def LiftActEq (p q : WordLift A C) : Prop :=
  p.u = q.u ∧ ∀ v : A, p.g • v = q.g • v

namespace LiftActEq

theorem refl (p : WordLift A C) : LiftActEq p p := ⟨rfl, fun _ => rfl⟩

theorem one : LiftActEq (1 : WordLift A C) 1 := refl 1

theorem mul {p q p' q' : WordLift A C} (hp : LiftActEq p p') (hq : LiftActEq q q') :
    LiftActEq (p * q) (p' * q') :=
  ⟨by rw [WordLift.mul_u, WordLift.mul_u, hp.1, hq.1, hp.2],
   fun v => by rw [WordLift.mul_g, WordLift.mul_g, mul_smul, mul_smul, hq.2, hp.2]⟩

theorem inv {p p' : WordLift A C} (hp : LiftActEq p p') : LiftActEq p⁻¹ p'⁻¹ := by
  have hg : ∀ v : A, p.g⁻¹ • v = p'.g⁻¹ • v := fun v => by
    rw [inv_smul_eq_iff, hp.2, smul_inv_smul]
  exact ⟨by rw [WordLift.inv_u, WordLift.inv_u, hp.1, hg], fun v => by
    rw [WordLift.inv_g, WordLift.inv_g]; exact hg v⟩

theorem conjR {p q p' q' : WordLift A C} (hp : LiftActEq p p') (hq : LiftActEq q q') :
    LiftActEq (conjR p q) (conjR p' q') :=
  mul (mul (inv hq) hp) hq

theorem commR {p q p' q' : WordLift A C} (hp : LiftActEq p p') (hq : LiftActEq q q') :
    LiftActEq (commR p q) (commR p' q') :=
  mul (mul (mul (inv hp) (inv hq)) hp) hq

theorem pow {p p' : WordLift A C} (hp : LiftActEq p p') : ∀ k : ℕ, LiftActEq (p ^ k) (p' ^ k)
  | 0 => by simpa using one
  | k + 1 => by rw [_root_.pow_succ, _root_.pow_succ]; exact mul (pow hp k) hp

theorem zpow {p p' : WordLift A C} (hp : LiftActEq p p') : ∀ k : ℤ, LiftActEq (p ^ k) (p' ^ k)
  | .ofNat k => by simpa using pow hp k
  | .negSucc k => by
      rw [zpow_negSucc, zpow_negSucc]
      exact inv (pow hp (k + 1))

end LiftActEq

variable [Finite A] [Finite C] (t : X → C) (a : X → A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The transport theorem** (S4.2 P3, Lean shape), at the `foxEval` layer.

If two letter maps `f`, `f'` agree to first order — equal Fox derivatives, equally acting
evaluations — then the two substituted words agree to first order too, throughout the
displayed fragment.  Because `foxEval` carries the Fox derivative in `.u` and the base value in `.g`, one
statement transports **both** the certificate's `d¹` and its gate-B/C values.

This is *not* the naive chain rule, and deliberately so: it never pushes an operator through a
power node.  The shadow memo refutes the naive rule (a Fox derivative of a profinite power is
not a fixed group-ring element — its finite representative is read at `2·ord(lower value)`, so
pushing `ρ` through the substitution turns `P` into `1`), and `Displayed` is the fence around that
refutation, not a convenience. -/
theorem liftActEq_foxEval_subst {Y : Type*} {P : Y → Prop} (f f' : Y → PWord X)
    (hf : ∀ ℓ, P ℓ → LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ))) :
    ∀ w : PWord Y, w.Displayed P →
      LiftActEq (foxEval t a E E₂ (PWord.subst f w)) (foxEval t a E E₂ (PWord.subst f' w)) := by
  intro w
  induction w with
  | one => intro _; exact LiftActEq.one
  | gen ℓ => intro hw; exact hf ℓ hw
  | mul u v ihu ihv =>
      intro hw
      simpa only [PWord.subst_mul, foxEval_mul] using LiftActEq.mul (ihu hw.1) (ihv hw.2)
  | inv u ihu => intro hw; simpa only [PWord.subst_inv, foxEval_inv] using LiftActEq.inv (ihu hw)
  | conj u g ihu ihg =>
      intro hw
      simpa only [PWord.subst_conj, foxEval_conj] using LiftActEq.conjR (ihu hw.1) (ihg hw.2)
  | comm u v ihu ihv =>
      intro hw
      simpa only [PWord.subst_comm, foxEval_comm] using LiftActEq.commR (ihu hw.1) (ihv hw.2)
  | zpow u k ihu =>
      intro hw
      simpa only [PWord.subst_zpow, foxEval_zpow] using LiftActEq.zpow (ihu hw) k
  | z2pow u z _ => intro hw; exact hw.elim
  | profPow u γ _ => intro hw; exact hw.elim

/-- **The Fox half of transport**: the substituted words have the same Fox derivative.  This is
the operator identity the σ-column coincidence lemma runs on. -/
theorem foxD_subst_congr {Y : Type*} {P : Y → Prop} (f f' : Y → PWord X)
    (hf : ∀ ℓ, P ℓ → LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ)))
    (w : PWord Y) (hw : w.Displayed P) :
    foxD t a E E₂ (PWord.subst f w) = foxD t a E E₂ (PWord.subst f' w) :=
  (liftActEq_foxEval_subst t a E E₂ f f' hf w hw).1

/-- **The value half of transport**: the substituted words' base values act equally.  This is
what makes the hat copy's gates B and C WMP-a's balance pair rather than a second ledger. -/
theorem evalFin_subst_act_congr {Y : Type*} {P : Y → Prop} (f f' : Y → PWord X)
    (hf : ∀ ℓ, P ℓ → LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ)))
    (w : PWord Y) (hw : w.Displayed P) (v : A) :
    PWord.evalFin t E E₂ (PWord.subst f w) • v = PWord.evalFin t E E₂ (PWord.subst f' w) • v := by
  have h := (liftActEq_foxEval_subst t a E E₂ f f' hf w hw).2 v
  rwa [foxEval_g, foxEval_g] at h

/-- The first-order agreement criterion at a single letter, in the shape the applications
supply it: equal Fox derivatives and both evaluations acting trivially. -/
theorem liftActEq_of_trivAct {u u' : PWord X} (hD : foxD t a E E₂ u = foxD t a E E₂ u')
    (hu : PWord.evalFin t E E₂ u ∈ trivAct C A)
    (hu' : PWord.evalFin t E E₂ u' ∈ trivAct C A) :
    LiftActEq (foxEval t a E E₂ u) (foxEval t a E E₂ u') := by
  refine ⟨hD, fun v => ?_⟩
  rw [foxEval_g, foxEval_g, mem_trivAct.mp hu, mem_trivAct.mp hu']

end Transport

/-! ## §2 The `Sh_M` operator

S4.2's frozen substitution, as a `PWord → PWord` transform on the **displayed** alphabet.  See
the module docstring for why it cannot live on `Generator n`: there the `δ`-letters are already
inlined, so a generator-level substitution descends into them and produces the memo's explicitly
rejected `δ₀ ↦ (δ₀τ)^{ω₂}δ₀⁻¹`.  Here δ-atomicity is a property of the *type*. -/

/-- **The displayed alphabet** of the procyclic-`M` row (shadow memo §1).

`σ, τ, x₀, x₁, x₂, δ₀, δ₁, δ₂` are the memo's own eight letters; `σ₂` and `D` are the two
further *displayed definitions* (`Auxiliary` nodes, each charged once — §9.3 rule 3) that the
frozen tree spells as units: `σ₂ = σ^{ω₂}`, and the Tietze display `D = σ^{η̂}` which freeze
row 5 makes the only available spelling of `η`.  Carrying them as atoms is faithful to the
display and puts every factor of the row in the `NoProf` fragment. -/
inductive MLetter
  /-- The Frobenius lift `σ`. -/
  | sigma : MLetter
  /-- The displayed definition `σ₂ = σ^{ω₂}`. -/
  | sigma2 : MLetter
  /-- The Tietze display `D = σ^{η̂}` (freeze row 5: `η` is immovable in this grammar). -/
  | dee : MLetter
  /-- The tame letter `τ`. -/
  | tau : MLetter
  /-- The wild letter `x_i`. -/
  | x (i : Fin 3) : MLetter
  /-- The `δ`-letter `δ_i = (x_iτ)^{ω₂}x_i⁻¹`, **atomic**. -/
  | delta (i : Fin 3) : MLetter
  deriving DecidableEq, Repr

namespace MLetter

/-- **The frozen substitution table** (S4.2, shadow memo §0):

```
x₀ ↦ δ₀   x₁ ↦ δ₁   x₂ ↦ 1      δ₀ ↦ δ₀   δ₁ ↦ δ₁   δ₂ ↦ 1      τ ↦ 1   σ ↦ σ   σ₂ ↦ σ₂
```

The `σ₂ ↦ σ₂` and `D ↦ D` clauses are *forced* by `σ ↦ σ` rather than chosen — see
`shM_omega2Pow_sigma` and `shM_profPow_sigma`, which run the substitution over the expanded
readings and get the same answer.  The `τ ↦ 1` clause is the one the memo flags as a *verified*
reading of the draft rather than a hand argument (without it the sign row's boundary block would
leave `τ^{ω₂}` standing in the hat copy). -/
def shLetter : MLetter → PWord MLetter
  | .sigma => .gen .sigma
  | .sigma2 => .gen .sigma2
  | .dee => .gen .dee
  | .tau => .one
  | .x ⟨0, _⟩ => .gen (.delta 0)
  | .x ⟨1, _⟩ => .gen (.delta 1)
  | .x _ => .one
  | .delta ⟨0, _⟩ => .gen (.delta 0)
  | .delta ⟨1, _⟩ => .gen (.delta 1)
  | .delta _ => .one

end MLetter

/-- **`Sh_M`** — the frozen shadow operator, as a `PWord → PWord` transform on the displayed
alphabet.  It is `PWord.subst` at S4.2's table, so it commutes with evaluation by construction:
"a substitution, so it commutes with evaluation.  Every theorem below is that one fact plus one
hypothesis about the image" (shadow memo §1). -/
def shM : PWord MLetter → PWord MLetter := PWord.subst MLetter.shLetter

@[simp] theorem shM_one : shM .one = .one := rfl
@[simp] theorem shM_gen (l : MLetter) : shM (.gen l) = MLetter.shLetter l := rfl
@[simp] theorem shM_mul (u v : PWord MLetter) : shM (.mul u v) = .mul (shM u) (shM v) := rfl
@[simp] theorem shM_inv (u : PWord MLetter) : shM (.inv u) = .inv (shM u) := rfl
@[simp] theorem shM_conj (u g : PWord MLetter) : shM (.conj u g) = .conj (shM u) (shM g) := rfl
@[simp] theorem shM_comm (u v : PWord MLetter) : shM (.comm u v) = .comm (shM u) (shM v) := rfl
@[simp] theorem shM_zpow (u : PWord MLetter) (k : ℤ) : shM (.zpow u k) = .zpow (shM u) k := rfl
@[simp] theorem shM_z2pow (u : PWord MLetter) (z : ℤ_[2]) :
    shM (.z2pow u z) = .z2pow (shM u) z := rfl
@[simp] theorem shM_profPow (u : PWord MLetter) (γ : Zhat) :
    shM (.profPow u γ) = .profPow (shM u) γ := rfl

/-- `σ₂ ↦ σ₂` is **derived**, not postulated: running `Sh_M` over the expanded reading
`σ₂ = σ^{ω₂}` returns it unchanged, because `σ ↦ σ`. -/
theorem shM_omega2Pow_sigma :
    shM (PWord.omega2Pow (.gen .sigma)) = PWord.omega2Pow (.gen .sigma) := rfl

/-- Likewise `D = σ^{η̂} ↦ D`, at every profinite exponent. -/
theorem shM_profPow_sigma (γ : Zhat) :
    shM (.profPow (.gen .sigma) γ) = .profPow (.gen .sigma) γ := rfl

/-- `Sh_M` fixes every letter of its own image (`⟨σ, σ₂, D, δ₀, δ₁⟩`, the shadow-stable
subgroup)… -/
theorem shM_shLetter (ℓ : MLetter) : shM (MLetter.shLetter ℓ) = MLetter.shLetter ℓ := by
  rcases ℓ with - | - | - | - | ⟨i, hi⟩ | ⟨i, hi⟩ <;>
    first
      | rfl
      | (interval_cases i <;> rfl)

/-- …hence **`Sh_M` is idempotent** (shadow memo §1: "its image is the shadow-stable subgroup
`⟨σ, δ₀, δ₁⟩`"). -/
theorem shM_idem : ∀ w : PWord MLetter, shM (shM w) = shM w
  | .one => rfl
  | .gen ℓ => shM_shLetter ℓ
  | .mul u v => by rw [shM_mul, shM_mul, shM_idem u, shM_idem v]
  | .inv u => by rw [shM_inv, shM_inv, shM_idem u]
  | .conj u g => by rw [shM_conj, shM_conj, shM_idem u, shM_idem g]
  | .comm u v => by rw [shM_comm, shM_comm, shM_idem u, shM_idem v]
  | .zpow u k => by rw [shM_zpow, shM_zpow, shM_idem u]
  | .z2pow u z => by rw [shM_z2pow, shM_z2pow, shM_idem u]
  | .profPow u γ => by rw [shM_profPow, shM_profPow, shM_idem u]

theorem shM_prodList : ∀ l : List (PWord MLetter),
    shM (PWord.prodList l) = PWord.prodList (l.map shM)
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, shM_mul, shM_prodList ws, List.map_cons, PWord.prodList_cons]

/-! ### The inlining back to WMP-a's words -/

/-- The displayed letters, inlined into WMP-a's alphabet: `δ_i ↦ dW h i` (the point at which
atomicity is spent, once, deliberately), `σ₂ ↦ sigma2W`, `D ↦ η.toPWord` at the instance's
display. -/
noncomputable def inlineLetter (h : ℕ) (η : EtaDisplay) :
    MLetter → PWord (Generator (2 + 2 * h))
  | .sigma => .gen .sigma
  | .sigma2 => sigma2W
  | .dee => η.toPWord
  | .tau => .gen .tau
  | .x i => .gen (coreLetter h i)
  | .delta i => dW h i

/-- The inlining `PWord MLetter → PWord (Generator (2+2h))`. -/
noncomputable def inlineM (h : ℕ) (η : EtaDisplay) :
    PWord MLetter → PWord (Generator (2 + 2 * h)) :=
  PWord.subst (inlineLetter h η)

section InlineSimp
variable (h : ℕ) (η : EtaDisplay)

@[simp] theorem inlineM_one : inlineM h η .one = .one := rfl
@[simp] theorem inlineM_gen (l : MLetter) : inlineM h η (.gen l) = inlineLetter h η l := rfl
@[simp] theorem inlineM_mul (u v : PWord MLetter) :
    inlineM h η (.mul u v) = .mul (inlineM h η u) (inlineM h η v) := rfl
@[simp] theorem inlineM_inv (u : PWord MLetter) :
    inlineM h η (.inv u) = .inv (inlineM h η u) := rfl
@[simp] theorem inlineM_conj (u g : PWord MLetter) :
    inlineM h η (.conj u g) = .conj (inlineM h η u) (inlineM h η g) := rfl
@[simp] theorem inlineM_comm (u v : PWord MLetter) :
    inlineM h η (.comm u v) = .comm (inlineM h η u) (inlineM h η v) := rfl
@[simp] theorem inlineM_zpow (u : PWord MLetter) (k : ℤ) :
    inlineM h η (.zpow u k) = .zpow (inlineM h η u) k := rfl

end InlineSimp

theorem inlineM_prodList (h : ℕ) (η : EtaDisplay) : ∀ l : List (PWord MLetter),
    inlineM h η (PWord.prodList l) = PWord.prodList (l.map (inlineM h η))
  | [] => rfl
  | w :: ws => by
      rw [PWord.prodList_cons, inlineM_mul, inlineM_prodList h η ws, List.map_cons,
        PWord.prodList_cons]

theorem inlineM_orbitNormFactors (h : ℕ) (η : EtaDisplay) (z u : PWord MLetter) (k : ℕ) :
    (Export.orbitNormFactors z u k).map (inlineM h η)
      = Export.orbitNormFactors (inlineM h η z) (inlineM h η u) k := by
  simp [Export.orbitNormFactors, List.map_map]

/-- `dW` and WM0-a's certificate `δ`-letter are the **same `PWord`** — the dedup the module
docstring records, checked in the kernel.  It is what lets this file cite WM0-b's δ-row lemmas
instead of re-deriving them. -/
theorem dW_eq_deltaCert (h : ℕ) (i : Fin 3) : dW h i = deltaCert h i := rfl

/-! ### The displayed spellings

Mirror images of WMP-a's `Words/Mpc.lean` definitions, letter for letter, including the
emitter's display collapses at trivial exponents.  Each `inlineM_*` bridge is `rfl`, so this
layer is a faithful re-spelling of the emitted trees and not a parallel definition. -/

section Spellings

/-- `σ₂^k` as displayed (bare at `k = 1`). -/
def sig2PowM : ℕ → PWord MLetter
  | 1 => .gen .sigma2
  | k => .zpow (.gen .sigma2) (k : ℤ)

/-- `C₀ = x₂σ₂^s`. -/
def c0M (s : ℕ) : PWord MLetter :=
  PWord.prodList [.gen (.x 2), .zpow (.gen .sigma2) (s : ℤ)]

/-- `A = x₀⁻¹C₀⁻ᵐ`. -/
def aM (s mm : ℕ) : PWord MLetter :=
  PWord.prodList [.inv (.gen (.x 0)), .zpow (c0M s) (-(mm : ℤ))]

/-- `B = x₁σ₂^p`, bare `x₁` at `p = 0`. -/
def bM : ℕ → PWord MLetter
  | 0 => .gen (.x 1)
  | p => PWord.prodList [.gen (.x 1), sig2PowM p]

/-- `E₀₁^pc = 𝓔(σ₂^a, σ₂^b; δ₀, δ₁)` — a word in `δ₀, δ₁, σ₂` alone, hence `Sh_M`-fixed. -/
def e01M (a b : ℕ) : PWord MLetter :=
  PWord.prodList
    [.conj (PWord.prodList [.conj (.gen (.delta 1)) (.zpow (.gen .sigma2) (b : ℤ)),
      .gen (.delta 1), .gen (.delta 0)]) (.zpow (.gen .sigma2) (a : ℤ)),
     .gen (.delta 0)]

/-- The orbit-norm base `z = δ₂δ₂^{σ₂^p}` (`δ₂²` at `p = 0`). -/
def zM : ℕ → PWord MLetter
  | 0 => .zpow (.gen (.delta 2)) ((2 : ℕ) : ℤ)
  | p => PWord.prodList [.gen (.delta 2), .conj (.gen (.delta 2)) (sig2PowM p)]

/-- `E₂^pc = δ₂^U·𝒩_{U,m}(z)^{U^m}` — every letter a `δ₂`, hence killed whole by `Sh_M`. -/
def e2M (s mm p : ℕ) : PWord MLetter :=
  PWord.prodList
    [.conj (.gen (.delta 2)) (.zpow (.gen .sigma2) (s : ℤ)),
     .conj (PWord.prodList (Export.orbitNormFactors (zM p) (.zpow (.gen .sigma2) (s : ℤ)) mm))
       (.zpow (.gen .sigma2) ((s * mm : ℕ) : ℤ))]

/-- `Ĉ₀ = σ₂^s`. -/
def c0HatM (s : ℕ) : PWord MLetter := .zpow (.gen .sigma2) (s : ℤ)

/-- `Â = δ₀⁻¹Ĉ₀⁻ᵐ`. -/
def aHatM (s mm : ℕ) : PWord MLetter :=
  PWord.prodList [.inv (.gen (.delta 0)), .zpow (c0HatM s) (-(mm : ℤ))]

/-- `B̂ = δ₁σ₂^p`, bare `δ₁` at `p = 0`. -/
def bHatM : ℕ → PWord MLetter
  | 0 => .gen (.delta 1)
  | p => PWord.prodList [.gen (.delta 1), sig2PowM p]

/-- The plus block `D₀²[D₀,D₁]`. -/
def plusM : PWord MLetter :=
  PWord.prodList [.zpow (.gen (.delta 0)) ((2 : ℕ) : ℤ),
    .comm (.gen (.delta 0)) (.gen (.delta 1))]

/-- The linear copy's displayed factor list. -/
def linFactorsM (α r p : ℕ) : List (PWord MLetter) :=
  [.zpow (aM (s r) (m α)) ((2 : ℕ) : ℤ),
   .comm (aM (s r) (m α)) (bM p),
   .zpow (c0M (s r)) ((2 ^ α : ℕ) : ℤ),
   .comm (c0M (s r)) (.gen .dee),
   e01M (p + s r * m α) (s r * m α),
   e2M (s r) (m α) p]

/-- The hat copy's displayed factor list — **five** factors, as emitted. -/
def hatFactorsM (α r p : ℕ) : List (PWord MLetter) :=
  [.zpow (aHatM (s r) (m α)) ((2 : ℕ) : ℤ),
   .comm (aHatM (s r) (m α)) (bHatM p),
   .zpow (c0HatM (s r)) ((2 ^ α : ℕ) : ℤ),
   .comm (c0HatM (s r)) (.gen .dee),
   e01M (p + s r * m α) (s r * m α)]

/-- `R_lin^pc` at the displayed layer. -/
def mpcLinM (α r p : ℕ) : PWord MLetter := PWord.prodList (linFactorsM α r p)

/-- `R̂^pc` at the displayed layer. -/
def mpcHatM (α r p : ℕ) : PWord MLetter := PWord.prodList (hatFactorsM α r p)

end Spellings

/-! ### The bridges to WMP-a

All `rfl` except `e2M`, whose `OrbitNorm` expansion is a `List.map` over `List.range` and so
needs the one map lemma (the same friction WMP-a recorded one level down). -/

section Bridges

variable (h : ℕ) (η : EtaDisplay)

theorem inlineM_sig2PowM : ∀ k : ℕ, inlineM h η (sig2PowM k) = sig2PowW h k
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

theorem inlineM_c0M (s' : ℕ) : inlineM h η (c0M s') = c0W h s' := rfl

theorem inlineM_aM (s' mm : ℕ) : inlineM h η (aM s' mm) = aW h s' mm := rfl

theorem inlineM_bM : ∀ p : ℕ, inlineM h η (bM p) = bW h p
  | 0 => rfl
  | p + 1 => by
      rw [show bM (p + 1) = PWord.prodList [.gen (.x 1), sig2PowM (p + 1)] from rfl,
        show bW h (p + 1) = PWord.prodList [.gen (coreLetter h 1), sig2PowW h (p + 1)] from rfl,
        inlineM_prodList]
      simp only [List.map_cons, List.map_nil, inlineM_sig2PowM]
      rfl

theorem inlineM_e01M (a b : ℕ) : inlineM h η (e01M a b) = e01W h a b := rfl

theorem inlineM_zM : ∀ p : ℕ, inlineM h η (zM p) = zW h p
  | 0 => rfl
  | p + 1 => by
      rw [show zM (p + 1)
            = PWord.prodList [.gen (.delta 2), .conj (.gen (.delta 2)) (sig2PowM (p + 1))]
          from rfl,
        show zW h (p + 1)
            = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (p + 1))] from rfl,
        inlineM_prodList]
      simp only [List.map_cons, List.map_nil, inlineM_conj, inlineM_sig2PowM]
      rfl

theorem inlineM_e2M (s' mm p : ℕ) : inlineM h η (e2M s' mm p) = e2W h s' mm p := by
  rw [e2M, e2W, inlineM_prodList]
  simp only [List.map_cons, List.map_nil, inlineM_conj, inlineM_zpow, inlineM_gen,
    inlineM_prodList, inlineM_orbitNormFactors, inlineM_zM]
  rfl

theorem inlineM_c0HatM (s' : ℕ) : inlineM h η (c0HatM s') = c0HatW h s' := rfl

theorem inlineM_aHatM (s' mm : ℕ) : inlineM h η (aHatM s' mm) = aHatW h s' mm := rfl

theorem inlineM_bHatM : ∀ p : ℕ, inlineM h η (bHatM p) = bHatW h p
  | 0 => rfl
  | p + 1 => by
      rw [show bHatM (p + 1) = PWord.prodList [.gen (.delta 1), sig2PowM (p + 1)] from rfl,
        show bHatW h (p + 1) = PWord.prodList [dW h 1, sig2PowW h (p + 1)] from rfl,
        inlineM_prodList]
      simp only [List.map_cons, List.map_nil, inlineM_sig2PowM]
      rfl

theorem inlineM_plusM : inlineM h η plusM = plusW h := rfl

/-- **The displayed layer is WMP-a's layer**: inlining the linear factor list returns
`Words.Mpc.linFactors` on the nose. -/
theorem inlineM_linFactorsM (α r p : ℕ) :
    (linFactorsM α r p).map (inlineM h η) = linFactors α r p η h := by
  simp only [linFactorsM, linFactors, List.map_cons, List.map_nil, inlineM_zpow, inlineM_comm,
    inlineM_aM, inlineM_bM, inlineM_c0M, inlineM_e01M, inlineM_e2M]
  rfl

@[inherit_doc inlineM_linFactorsM]
theorem inlineM_hatFactorsM (α r p : ℕ) :
    (hatFactorsM α r p).map (inlineM h η) = hatFactors α r p η h := by
  simp only [hatFactorsM, hatFactors, List.map_cons, List.map_nil, inlineM_zpow, inlineM_comm,
    inlineM_aHatM, inlineM_bHatM, inlineM_c0HatM]
  rfl

theorem inlineM_mpcLinM (α r p : ℕ) : inlineM h η (mpcLinM α r p) = mpcLinW α r p η h := by
  rw [mpcLinM, inlineM_prodList, inlineM_linFactorsM, mpcLinW]

theorem inlineM_mpcHatM (α r p : ℕ) : inlineM h η (mpcHatM α r p) = mpcHatW α r p η h := by
  rw [mpcHatM, inlineM_prodList, inlineM_hatFactorsM, mpcHatW]

end Bridges

/-! ### The certificate shrink: `hatFactors` IS the `Sh_M`-image of `linFactors`

The S4.2 statement WMP-b owes.  First the cases that are **exactly syntactic** — they are the
informative ones — then the headline at the `foxEval` layer, where the substitution's own
created units are invisible. -/

section Shrink

open MLetter in
/-! The frozen table, letter by letter, as `rfl`-lemmas (the `Fin 3` patterns do not reduce
under `simp` on their own). -/

@[simp] theorem shLetter_sigma : MLetter.shLetter .sigma = .gen .sigma := rfl
@[simp] theorem shLetter_sigma2 : MLetter.shLetter .sigma2 = .gen .sigma2 := rfl
@[simp] theorem shLetter_dee : MLetter.shLetter .dee = .gen .dee := rfl
@[simp] theorem shLetter_tau : MLetter.shLetter .tau = .one := rfl
@[simp] theorem shLetter_x_zero : MLetter.shLetter (.x 0) = .gen (.delta 0) := rfl
@[simp] theorem shLetter_x_one : MLetter.shLetter (.x 1) = .gen (.delta 1) := rfl
@[simp] theorem shLetter_x_two : MLetter.shLetter (.x 2) = .one := rfl
@[simp] theorem shLetter_delta_zero : MLetter.shLetter (.delta 0) = .gen (.delta 0) := rfl
@[simp] theorem shLetter_delta_one : MLetter.shLetter (.delta 1) = .gen (.delta 1) := rfl
@[simp] theorem shLetter_delta_two : MLetter.shLetter (.delta 2) = .one := rfl

/-- `Ê₀₁ = E₀₁` **verbatim**: the block is a word in `δ₀, δ₁, σ₂` alone, every one of them
`Sh_M`-fixed.  This is why the emitted hat display repeats the *same* subtree (`E01` occurs
twice in the tree, shared) rather than a hatted copy. -/
@[simp] theorem shM_e01M (a b : ℕ) : shM (e01M a b) = e01M a b := rfl

/-- `σ₂^k ↦ σ₂^k`. -/
@[simp] theorem shM_sig2PowM : ∀ k : ℕ, shM (sig2PowM k) = sig2PowM k
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- `B ↦ B̂` on the nose (`x₁ ↦ δ₁`, `σ₂` fixed). -/
@[simp] theorem shM_bM : ∀ p : ℕ, shM (bM p) = bHatM p
  | 0 => rfl
  | 1 => rfl
  | _ + 2 => rfl

/-- `D ↦ D`: the Tietze display is `Sh_M`-fixed, which is why the two copies' `[C₀,D]` and
`[Ĉ₀,D]` commutators share a conjugand at every `η̂` display. -/
@[simp] theorem shM_dee : shM (.gen .dee) = .gen .dee := rfl

/-- **The plus block is its own shadow** — shadow memo §1: `D₀²[D₀,D₁]` is shadow-stable, so
"the tail of eq. `Mpc-word` is shadow-stable" is a theorem, not a convention. -/
@[simp] theorem shM_plusM : shM plusM = plusM := rfl

/-- **The substitution's single created unit.**  The `x₂ ↦ 1` clause fires *inside*
`C₀ = x₂σ₂^s`, so `Sh_M(C₀) = 1·Ĉ₀` where the emitted hat display writes the bare `Ĉ₀ = σ₂^s`.
This is the memo's "the substitution can create cancellations (`x₂σ ↦ σ`) but never destroy
one", and on this row it is the *only* place a final normalization is needed. -/
theorem shM_c0M (s' : ℕ) : shM (c0M s') = PWord.prodList [.one, c0HatM s'] := rfl

/-- The same unit, transported through `A = x₀⁻¹C₀⁻ᵐ`. -/
theorem shM_aM (s' mm : ℕ) :
    shM (aM s' mm)
      = PWord.prodList [.inv (.gen (.delta 0)),
          .zpow (PWord.prodList [.one, c0HatM s']) (-(mm : ℤ))] := rfl

/-- **The shrink, syntactically**: applying `Sh_M` to the six displayed factors of the linear
copy returns, factor for factor, the five displayed hat factors — up to the created unit in the
two `C₀`-derived slots — with the sixth, `E₂^pc`, collapsing (every letter is a `δ₂`).  That
collapse is exactly why the emitted hat display carries **five** factors and no `Ê₂`. -/
theorem shM_linFactorsM (α r p : ℕ) :
    (linFactorsM α r p).map shM
      = [.zpow (shM (aM (s r) (m α))) ((2 : ℕ) : ℤ),
         .comm (shM (aM (s r) (m α))) (bHatM p),
         .zpow (shM (c0M (s r))) ((2 ^ α : ℕ) : ℤ),
         .comm (shM (c0M (s r))) (.gen .dee),
         e01M (p + s r * m α) (s r * m α),
         shM (e2M (s r) (m α) p)] := by
  simp only [linFactorsM, List.map_cons, List.map_nil, shM_zpow, shM_comm, shM_bM, shM_e01M,
    shM_dee]

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  {h : ℕ} (t : Generator (2 + 2 * h) → C) (a : Generator (2 + 2 * h) → A) (E : Zhat → ℤ)
  (E₂ : ℤ_[2] → ℤ) (η : EtaDisplay)

theorem foxEval_prodListF (l : List (PWord (Generator (2 + 2 * h)))) :
    foxEval t a E E₂ (PWord.prodList l) = (l.map (foxEval t a E E₂)).prod :=
  evalFin_prodList (foxLift t a) E E₂ l

/-- The created unit is invisible to the Fox evaluation. -/
theorem foxEval_inlineM_oneCons (y : PWord MLetter) :
    foxEval t a E E₂ (inlineM h η (PWord.prodList [.one, y]))
      = foxEval t a E E₂ (inlineM h η y) := by
  rw [inlineM_prodList]
  simp only [List.map_cons, List.map_nil, inlineM_one, foxEval_prodListF]
  simp

theorem foxEval_inlineM_shM_c0M (s' : ℕ) :
    foxEval t a E E₂ (inlineM h η (shM (c0M s'))) = foxEval t a E E₂ (c0HatW h s') := by
  rw [shM_c0M, foxEval_inlineM_oneCons, inlineM_c0HatM]

theorem foxEval_inlineM_shM_aM (s' mm : ℕ) :
    foxEval t a E E₂ (inlineM h η (shM (aM s' mm))) = foxEval t a E E₂ (aHatW h s' mm) := by
  rw [shM_aM, aHatW, inlineM_prodList, foxEval_prodListF, foxEval_prodListF]
  simp only [List.map_cons, List.map_nil, inlineM_inv, inlineM_zpow, foxEval_inv,
    foxEval_zpow, foxEval_inlineM_oneCons, inlineM_c0HatM]
  rfl

theorem foxEval_inlineM_shM_zM (pp : ℕ) :
    foxEval t a E E₂ (inlineM h η (shM (zM pp))) = 1 := by
  match pp with
  | 0 =>
      show foxEval t a E E₂ (inlineM h η (shM (.zpow (.gen (.delta 2)) ((2 : ℕ) : ℤ)))) = 1
      simp
  | q + 1 =>
      rw [show zM (q + 1)
            = PWord.prodList [.gen (.delta 2), .conj (.gen (.delta 2)) (sig2PowM (q + 1))]
          from rfl, shM_prodList, inlineM_prodList, foxEval_prodListF]
      simp

/-- **`Ê₂ = 1`.**  Every letter of `E₂^pc` is a `δ₂`, and `Sh_M` kills `δ₂`; the tree shape
survives the substitution (so this is a *value* statement, not a syntactic one), but the value
is the identity — the honest form of "`Ê₂` is dropped from the display". -/
theorem foxEval_inlineM_shM_e2M (s' mm pp : ℕ) :
    foxEval t a E E₂ (inlineM h η (shM (e2M s' mm pp))) = 1 := by
  have horb : foxEval t a E E₂
      (inlineM h η (shM (PWord.prodList
        (Export.orbitNormFactors (zM pp) (PWord.zpow (.gen .sigma2) (s' : ℤ)) mm)))) = 1 := by
    rw [shM_prodList, inlineM_prodList, foxEval_prodListF, List.map_map, List.map_map]
    refine List.prod_eq_one fun y hy => ?_
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hy
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
    simp only [Function.comp_apply, shM_conj, inlineM_conj, foxEval_conj,
      foxEval_inlineM_shM_zM t a E E₂ η pp, one_conjR]
  rw [e2M, shM_prodList, inlineM_prodList, foxEval_prodListF]
  simp only [List.map_cons, List.map_nil, shM_conj, shM_gen, shM_zpow, inlineM_conj,
    foxEval_conj, List.prod_cons, List.prod_nil, mul_one, shLetter_delta_two, inlineM_one,
    foxEval_one, one_conjR, horb]

/-- **The certificate shrink (S4.2), at the `foxEval` layer** — the theorem WMP-b owes.

`R̂^pc` **is** `Sh_M(R_lin^pc)`: the hat copy is not a second word to certify, it is the image of
the first under one frozen substitution.  Because `foxEval` carries the base value in `.g` and
the Fox derivative in `.u`, this single equality delivers both halves at once — the hat copy's
gate-B and gate-C values are WMP-a's balance pair (`foxEval_shM_mpcLinM_g`) and its `d¹` is the
raw word's under transport (`foxD_shM_mpcLinM`).

Hypothesis-free: no module condition, no ramification, no `α ≥ 1`.  The three obstructions to a
*syntactic* statement — `Sh_M(C₀) = 1·Ĉ₀`, `Ê₂`'s surviving tree shape, and `prodList`'s
trailing units — are precisely the memo's "commutes with normalization up to a final
`normalize`", and none of them is visible here. -/
theorem foxEval_inlineM_shM_mpcLinM (α r p : ℕ) :
    foxEval t a E E₂ (inlineM h η (shM (mpcLinM α r p)))
      = foxEval t a E E₂ (mpcHatW α r p η h) := by
  rw [mpcLinM, shM_prodList, shM_linFactorsM, inlineM_prodList, foxEval_prodListF, mpcHatW,
    hatFactors, foxEval_prodListF]
  simp only [List.map_cons, List.map_nil, inlineM_zpow, inlineM_comm, foxEval_zpow,
    foxEval_comm, foxEval_inlineM_shM_aM, foxEval_inlineM_shM_c0M, foxEval_inlineM_shM_e2M,
    List.prod_cons, List.prod_nil, mul_one, inlineM_bHatM, inlineM_e01M]
  rfl

include a in
/-- **Gate B and gate C for the hat copy are WMP-a's balance pair** (`.g` of the shrink): the
shadow's boundary values are the raw word's, transported — not a second ledger.  (The offsets
`a` are inert here — the statement is about base values only — but they pin the coefficient
module the shrink is read in; pass `0`.) -/
theorem foxEval_shM_mpcLinM_g [Finite A] [Finite C] (α r p : ℕ) :
    PWord.evalFin t E E₂ (inlineM h η (shM (mpcLinM α r p)))
      = PWord.evalFin t E E₂ (mpcHatW α r p η h) := by
  have hh := congrArg WordLift.g (foxEval_inlineM_shM_mpcLinM t a E E₂ η α r p)
  rwa [foxEval_g, foxEval_g] at hh

/-- **The hat copy's `d¹` is the raw word's under transport** (`.u` of the shrink). -/
theorem foxD_shM_mpcLinM (α r p : ℕ) :
    foxD t a E E₂ (inlineM h η (shM (mpcLinM α r p)))
      = foxD t a E E₂ (mpcHatW α r p η h) :=
  congrArg WordLift.u (foxEval_inlineM_shM_mpcLinM t a E E₂ η α r p)

end Shrink

/-! ## §4 The σ-column coincidence lemma

Freeze row 5, binding on this ticket: *"The Lean side needs the **σ-column coincidence lemma**
(the two copies' σ entries are the same operator, so the product's column vanishes without
either factor vanishing) — **NOT** the geometric-sum identity."*  Both halves are delivered
here, and the geometric-sum identity `(1+S^a)[b] = (1+S^b)[a]` is never used or stated. -/

section SigmaColumn

theorem subst_subst {G₀ G₁ G₂ : Type*} (g : G₁ → PWord G₂) (f : G₀ → PWord G₁) :
    ∀ w : PWord G₀,
      PWord.subst g (PWord.subst f w) = PWord.subst (fun x => PWord.subst g (f x)) w
  | .one => rfl
  | .gen _ => rfl
  | .mul u v => by
      simp only [PWord.subst_mul, subst_subst g f u, subst_subst g f v]
  | .inv u => by simp only [PWord.subst_inv, subst_subst g f u]
  | .conj u x => by simp only [PWord.subst_conj, subst_subst g f u, subst_subst g f x]
  | .comm u v => by simp only [PWord.subst_comm, subst_subst g f u, subst_subst g f v]
  | .zpow u k => by simp only [PWord.subst_zpow, subst_subst g f u]
  | .z2pow u z => by simp only [PWord.subst_z2pow, subst_subst g f u]
  | .profPow u γ => by simp only [PWord.subst_profPow, subst_subst g f u]

/-- **The shadow-inlining**: inlining the `Sh_M`-image is substituting the composed letter map.
This is what puts the two copies side by side as two inlinings of *one* displayed word — the
form the transport theorem consumes. -/
theorem inlineM_shM (h : ℕ) (η : EtaDisplay) (w : PWord MLetter) :
    inlineM h η (shM w) = PWord.subst (fun ℓ => inlineM h η (MLetter.shLetter ℓ)) w :=
  subst_subst _ _ w

/-! ### The displayed row uses no bare `τ`

`τ` occurs in the frozen procyclic word **only inside the `δ`-atoms**.  That is not a
convenience: `τ` is the one letter at which the two inlinings disagree beyond first order
(`Sh_M` sends it to `1`, and it acts nontrivially on every ramified module), so the transport
hypothesis would be false without this. -/

theorem displayed_sig2PowM : ∀ k : ℕ, (sig2PowM k).Displayed (fun ℓ => ℓ ≠ MLetter.tau)
  | 0 => by simp [sig2PowM, PWord.Displayed]
  | 1 => by simp [sig2PowM, PWord.Displayed]
  | _ + 2 => by simp [sig2PowM, PWord.Displayed]

theorem displayed_c0M (s' : ℕ) : (c0M s').Displayed (fun ℓ => ℓ ≠ MLetter.tau) := by
  simp [c0M, PWord.Displayed]

theorem displayed_aM (s' mm : ℕ) : (aM s' mm).Displayed (fun ℓ => ℓ ≠ MLetter.tau) := by
  refine ⟨?_, ?_, trivial⟩
  · simp [PWord.Displayed]
  · exact displayed_c0M s'

theorem displayed_bM : ∀ pp : ℕ, (bM pp).Displayed (fun ℓ => ℓ ≠ MLetter.tau)
  | 0 => by simp [bM, PWord.Displayed]
  | q + 1 => by
      rw [show bM (q + 1) = PWord.prodList [.gen (.x 1), sig2PowM (q + 1)] from rfl]
      exact ⟨by simp [PWord.Displayed], displayed_sig2PowM (q + 1), trivial⟩

theorem displayed_e01M (a b : ℕ) : (e01M a b).Displayed (fun ℓ => ℓ ≠ MLetter.tau) := by
  simp [e01M, PWord.Displayed]

theorem displayed_zM : ∀ pp : ℕ, (zM pp).Displayed (fun ℓ => ℓ ≠ MLetter.tau)
  | 0 => by simp [zM, PWord.Displayed]
  | q + 1 => by
      rw [show zM (q + 1)
            = PWord.prodList [.gen (.delta 2), .conj (.gen (.delta 2)) (sig2PowM (q + 1))]
          from rfl]
      exact ⟨by simp [PWord.Displayed],
        ⟨by simp [PWord.Displayed], displayed_sig2PowM (q + 1)⟩, trivial⟩

theorem displayed_e2M (s' mm pp : ℕ) : (e2M s' mm pp).Displayed (fun ℓ => ℓ ≠ MLetter.tau) := by
  refine ⟨⟨by simp [PWord.Displayed], by simp [PWord.Displayed]⟩, ⟨?_, by simp [PWord.Displayed]⟩,
    trivial⟩
  refine displayed_prodList fun w hw => ?_
  rw [Export.orbitNormFactors] at hw
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp hw
  exact ⟨displayed_zM pp, by simp [PWord.Displayed]⟩

/-- **No displayed factor of the procyclic row carries a bare `τ`.** -/
theorem displayed_mpcLinM (α r p : ℕ) :
    (mpcLinM α r p).Displayed (fun ℓ => ℓ ≠ MLetter.tau) := by
  refine displayed_prodList fun w hw => ?_
  simp only [linFactorsM, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl | rfl
  · exact displayed_aM _ _
  · exact ⟨displayed_aM _ _, displayed_bM p⟩
  · exact displayed_c0M _
  · exact ⟨displayed_c0M _, by simp [PWord.Displayed]⟩
  · exact displayed_e01M _ _
  · exact displayed_e2M _ _ _

/-! ### The coincidence -/

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- `x_i` is not the `σ`-letter (so the σ-column offsets vanish on it). -/
theorem coreLetter_ne_sigma (hh : ℕ) (i : Fin 3) :
    coreLetter hh i ≠ (Generator.sigma : Generator (2 + 2 * hh)) := by
  intro hc
  simp [coreLetter] at hc

/-- The two inlinings agree to first order at every letter but `τ`.

Letter by letter this is exactly what the shadow substitution is: `σ`, `σ₂` and `D` are fixed
(*equal*, not merely equally acting), `δ₀` and `δ₁` are fixed, and the four letters that move —
`x₀ ↦ δ₀`, `x₁ ↦ δ₁`, `x₂ ↦ 1`, `δ₂ ↦ 1` — carry **no `σ`** (so both Fox derivatives vanish on
the σ-column) and act trivially (so no prefix weight can tell the copies apart).  The `x₂` and
`δ₂` clauses are the reason `E₂^pc` has no shadow at all. -/
theorem liftActEq_shInline_inline (η : EtaDisplay) (v : V)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hδtriv : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V)
    (hδD : ∀ i : Fin 3, foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) = 0) :
    ∀ ℓ : MLetter, ℓ ≠ MLetter.tau →
      LiftActEq (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (inlineM h η (MLetter.shLetter ℓ)))
        (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (inlineLetter h η ℓ)) := by
  have hxa : ∀ i : Fin 3, (Pi.single Generator.sigma v : Generator (2 + 2 * h) → V)
      (coreLetter h i) = 0 := fun i => Pi.single_eq_of_ne (coreLetter_ne_sigma h i) v
  have hxact : ∀ (i : Fin 3) (w : V), t (coreLetter h i) • w = w := fun i w => hwild _ w
  have hone : ∀ i : Fin 3,
      LiftActEq (foxEval ⇑t (Pi.single Generator.sigma v) E E₂
          (PWord.one : PWord (Generator (2 + 2 * h))))
        (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (.gen (coreLetter h i))) :=
    fun i => ⟨(hxa i).symm, fun w => by simpa using (hxact i w).symm⟩
  have hδ : ∀ i : Fin 3,
      LiftActEq (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i))
        (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (.gen (coreLetter h i))) := by
    refine fun i => ⟨?_, fun w => ?_⟩
    · rw [show (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i)).u
          = foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) from rfl, hδD i]
      simpa using (hxa i).symm
    · simp only [foxEval_g]
      rw [mem_trivAct.mp (hδtriv i)]
      simpa using (hxact i w).symm
  have hδone : ∀ i : Fin 3,
      LiftActEq (foxEval ⇑t (Pi.single Generator.sigma v) E E₂
          (PWord.one : PWord (Generator (2 + 2 * h))))
        (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i)) := by
    refine fun i => ⟨?_, fun w => ?_⟩
    · rw [show (foxEval ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i)).u
          = foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) from rfl, hδD i]
      rfl
    · simp only [foxEval_g]
      rw [mem_trivAct.mp (hδtriv i)]
      simp
  rintro (- | - | - | - | ⟨i, hi⟩ | ⟨i, hi⟩) hτ
  · exact LiftActEq.refl _
  · exact LiftActEq.refl _
  · exact LiftActEq.refl _
  · exact absurd rfl hτ
  · interval_cases i
    · exact hδ 0
    · exact hδ 1
    · exact hone 2
  · interval_cases i
    · exact LiftActEq.refl _
    · exact LiftActEq.refl _
    · exact hδone 2

/-- **The σ-column coincidence lemma** (freeze row 5).

> The two copies' σ-column entries are the **same operator**.

The proof is §3's transport theorem applied to the two inlinings of the *one* displayed word
`mpcLinM`.  `D(σ₂)` — the Sage engine's opaque atom `G[S;ω₂]` — is never computed; it does not
have to be, because nothing in the argument evaluates it.  Neither copy's σ-column is claimed
to vanish, and neither does: `[Â,B̂]` has a `σ₂`-carrying right entry, so it contributes to the
column on both sides.

⚠ **Contrast with WM0-b's compact-`M` analogue**, which is a genuinely different mechanism:
there the σ-column cancels **over `ℤ`**, because the balancing `σ₂^{2m}` sits behind the
`A₀`-prefix and the differentiated Prop. 9.2 balance does the work with no characteristic
hypothesis (`MCompact.foxD_mWordWith_core`, via `MCompact.sigmaGeom_two_mul`).  There it works
because the compact `B`-letter is the *bare* `x₁`, which acts trivially; here `B = x₁σ₂^p` does
not.  Conflating the two would be an error. -/
theorem foxColumn_sigma_mpcHatW_eq_mpcLinW (α r p : ℕ) (η : EtaDisplay)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hδtriv : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V)
    (hδD : ∀ (v : V) (i : Fin 3), foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) = 0) :
    foxColumn (A := V) ⇑t E E₂ (mpcHatW α r p η h) Generator.sigma
      = foxColumn (A := V) ⇑t E E₂ (mpcLinW α r p η h) Generator.sigma := by
  refine AddMonoidHom.ext fun v => ?_
  rw [foxColumn_apply, foxColumn_apply, ← foxD_shM_mpcLinM, inlineM_shM, ← inlineM_mpcLinM h η,
    inlineM]
  exact foxD_subst_congr (P := fun ℓ => ℓ ≠ MLetter.tau) _ _ _ _ _ _
    (liftActEq_shInline_inline t E E₂ η v hwild hδtriv (hδD v)) _ (displayed_mpcLinM α r p)

/-- **The product's σ-column vanishes without either factor vanishing** — the second half of the
freeze's mandate, and the reason the coincidence lemma is the right statement.

`D(uv) = D(u) + ū·D(v)`; the linear copy's value acts trivially (`hlin` — the Prop. 9.2 balance
read at the value level: `A²` contributes `S₂^{−2sm}`, `C₀^{2^α}` contributes `S₂^{s·2^α}`, and
those cancel), so the two σ-entries add rather than compose, and by the coincidence they are the
*same* entry.  Over a characteristic-`2` module `Φ + Φ = 0`.

This is where characteristic `2` genuinely enters, and it enters **here and not earlier**. -/
theorem foxColumn_sigma_mul_eq_zero (α r p : ℕ) (η : EtaDisplay) (hV₂ : ∀ w : V, w + w = 0)
    (hlin : PWord.evalFin ⇑t E E₂ (mpcLinW α r p η h) ∈ trivAct C V)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hδtriv : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V)
    (hδD : ∀ (v : V) (i : Fin 3), foxD ⇑t (Pi.single Generator.sigma v) E E₂ (dW h i) = 0) :
    foxColumn (A := V) ⇑t E E₂ (.mul (mpcLinW α r p η h) (mpcHatW α r p η h)) Generator.sigma
      = 0 := by
  refine AddMonoidHom.ext fun v => ?_
  have hcol := congrArg (fun f : V →+ V => f v)
    (foxColumn_sigma_mpcHatW_eq_mpcLinW t E E₂ α r p η hwild hδtriv hδD)
  simp only [foxColumn_apply] at hcol ⊢
  rw [foxD_mul, mem_trivAct.mp hlin, hcol]
  exact hV₂ _

end SigmaColumn

/-! ### The WW3 form: where the second-order shadow enters

The mandate is to state the coincidence *against* WW3's `heisJetZero` family, which is the
"copies cancel" consumable.  `heisJetZero` is the subgroup of lift values with **both** first
derivatives zero (`p.a = 0` and `p.l = 0`), and `heisEvalZ_mul_z` is the second-order product
rule `β(uv) = β(u) + β(v) + D^∨(u)(ū·D(v))`.  Once the hat copy's first jet vanishes — §5's
headline, of which the σ-column is the last entry — the cross term dies and the two copies'
central values simply add, which is the step WMP-c turns into the char-`2` cancellation. -/

section HeisForm

variable {X : Type*} {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]
  (μ : X → C) (x : X → A) (y : X → ElemDual A) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The copies-cancel step, at the second order** (WW3's `heisMul_z_of_jetZero`, wired to this
lane).  If the hat copy's first jet vanishes then the pair's central value is the sum of the two
copies' central values — no cross term.  This needs *only* the vanishing first derivative
(S1.5's banked lemma (iii)(a)); no module, no lift, no characteristic hypothesis. -/
theorem heisEvalZ_pair_z_of_hat_jetZero (lin hat : PWord X)
    (hjet : heisEvalZ μ x y E E₂ hat ∈ heisJetZero A C) :
    (heisEvalZ μ x y E E₂ (.mul lin hat)).z
      = (heisEvalZ μ x y E E₂ lin).z + (heisEvalZ μ x y E E₂ hat).z := by
  rw [heisEvalZ_mul_z, hjet.1, smul_zero, map_zero, add_zero]

end HeisForm

/-! ## §5 The hat copy's first Fox derivative

Draft Rem. 5.4: on ramified simples `R̂^pc` has **zero first Fox derivative**.

The shadow memo's P3 vanishing criterion has two clauses, and they are discharged by two
different routes — that is not an artefact, it is the structure of the statement:

1. **the free `δ₀`/`δ₁` row of the core vanishes** (the *self-replication* clause: the raw
   word's `x_i` occurrences and its `δ_i` occurrences carry the same prefix sum, so once the
   substitution merges them they cancel over `F₂`).  That is this section, and it is where
   `hV₂` is spent;
2. **`bal(w) = 0`** — the σ-column.  The memo closes it with S1.3's procyclic collector, *not*
   with the Fox engine; the freeze re-points the Lean side at §4's coincidence lemma.  So §5
   states its row at **σ-free offsets** and §4 supplies the σ-entry.  Splitting the statement
   this way is the honest reading of the freeze, not a weakening: the memo's own criterion is a
   conjunction of two separately-checked conditions ("both are exactly checkable, by different
   engines").

Everything below is quantified over the honest resolvers `E`, `E₂` — the word is **not**
`IsOmega2Only` (WMP-a's `not_isOmega2Only_mpcW_hat`), so no numeric ω₂-exponent route exists on
the `η̂` row and none is used. -/

section HatRow

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The general commutator Fox row** — the one engine lemma the hat copy needs that WWH's
`foxD_comm_of_trivial` (both entries trivial) and WM0-b's `foxD_comm_of_trivial_right` (right
entry trivial) do not cover: on this row `B̂ = δ₁σ₂^p` acts by `S₂^p`, so *neither* entry of
`[Â,B̂]` acts trivially.  Hoist candidate. -/
theorem foxD_comm_general (u v : PWord (Generator (2 + 2 * h))) :
    foxD ⇑t a E E₂ (.comm u v)
      = -((PWord.evalFin ⇑t E E₂ u)⁻¹ • foxD ⇑t a E E₂ u)
        - ((PWord.evalFin ⇑t E E₂ u)⁻¹ * (PWord.evalFin ⇑t E E₂ v)⁻¹) • foxD ⇑t a E E₂ v
        + ((PWord.evalFin ⇑t E E₂ u)⁻¹ * (PWord.evalFin ⇑t E E₂ v)⁻¹) • foxD ⇑t a E E₂ u
        + ((PWord.evalFin ⇑t E E₂ u)⁻¹ * (PWord.evalFin ⇑t E E₂ v)⁻¹ * PWord.evalFin ⇑t E E₂ u)
            • foxD ⇑t a E E₂ v := by
  show (commR (foxEval ⇑t a E E₂ u) (foxEval ⇑t a E E₂ v)).u = _
  simp only [commR, WordLift.mul_u, WordLift.mul_g, WordLift.inv_u, WordLift.inv_g, smul_add,
    smul_neg, mul_smul, foxEval_g]
  rw [show foxD ⇑t a E E₂ u = (foxEval ⇑t a E E₂ u).u from rfl,
    show foxD ⇑t a E E₂ v = (foxEval ⇑t a E E₂ v).u from rfl]
  abel

/-! ### `σ`-free offsets kill every `σ₂`-carrying entry

`D(σ₂)` is the Sage engine's opaque atom `G[S;ω₂]`; on the σ-free part of the offset space it is
`0` because it is a multiple of `a(σ)`, and the whole `σ₂`-tower goes with it. -/

/-- `D(σ₂) = 0` at `σ`-free offsets. -/
theorem foxD_sigma2W_of_sigma_free (hσ : a Generator.sigma = 0) :
    foxD ⇑t a E E₂ (sigma2W : PWord (Generator (2 + 2 * h))) = 0 := by
  rw [sigma2W, PWord.omega2Pow, foxD_profPow_omega2']
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [show foxD ⇑t a E E₂ (PWord.gen (Generator.sigma : Generator (2 + 2 * h)))
      = a Generator.sigma from rfl, hσ, smul_zero]

/-- The whole `σ₂`-tower dies with it: `D(σ₂^k) = 0` at every integer exponent. -/
theorem foxD_sigma2Pow_of_sigma_free (hσ : a Generator.sigma = 0) (k : ℤ) :
    foxD ⇑t a E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) k) = 0 := by
  have hnat : ∀ j : ℕ,
      foxD ⇑t a E E₂ (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (j : ℤ)) = 0 := by
    intro j
    rw [foxD_zpow_natCast]
    exact Finset.sum_eq_zero fun i _ => by
      rw [foxD_sigma2W_of_sigma_free t E E₂ a hσ, smul_zero]
  rcases k with j | j
  · simpa using hnat j
  · rw [Int.negSucc_eq, show -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
      foxD_zpow_neg', hnat (j + 1), smul_zero, neg_zero]

/-- `Ĉ₀ = σ₂^s` has no first-order content off the σ-column. -/
theorem foxD_c0HatW_of_sigma_free (hσ : a Generator.sigma = 0) (s' : ℕ) :
    foxD ⇑t a E E₂ (c0HatW h s') = 0 :=
  foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _

/-- …and so does `D = σ^{η̂}`, at **every** `η̂` display — the bare `σ`, a literal power, and the
genuine `ZhatPower` node alike.  This is what keeps the `[Ĉ₀,D]` factor silent at first order
without any hypothesis on `η`. -/
theorem foxD_etaDisplay_of_sigma_free (hσ : a Generator.sigma = 0) (η : EtaDisplay) :
    foxD ⇑t a E E₂ (η.toPWord (n := 2 + 2 * h)) = 0 := by
  have hgen : foxD ⇑t a E E₂ (PWord.gen (Generator.sigma : Generator (2 + 2 * h))) = 0 := hσ
  cases η with
  | one => exact hgen
  | lit k =>
      rw [show (EtaDisplay.lit k).toPWord (n := 2 + 2 * h)
          = .zpow (.gen Generator.sigma) k from rfl]
      rcases k with j | j
      · rw [show (Int.ofNat j) = ((j : ℕ) : ℤ) from rfl, foxD_zpow_natCast]
        exact Finset.sum_eq_zero fun i _ => by rw [hgen, smul_zero]
      · rw [Int.negSucc_eq, show -((j : ℤ) + 1) = -((j + 1 : ℕ) : ℤ) by push_cast; ring,
          foxD_zpow_neg', foxD_zpow_natCast,
          Finset.sum_eq_zero fun i _ => by rw [hgen, smul_zero], smul_zero, neg_zero]
  | hat num den =>
      rw [show (EtaDisplay.hat num den).toPWord (n := 2 + 2 * h)
          = .profPow (.gen Generator.sigma) (Export.RawSpec.toZhat (.etahat num den)) from rfl]
      rcases eq_or_ne (Export.RawSpec.toZhat (.etahat num den)) omega2 with hω | hω
      · rw [hω, foxD_profPow_omega2']
        exact Finset.sum_eq_zero fun i _ => by rw [hgen, smul_zero]
      · rw [show foxD ⇑t a E E₂
              (PWord.profPow (.gen (Generator.sigma : Generator (2 + 2 * h)))
                (Export.RawSpec.toZhat (.etahat num den)))
            = (foxEval ⇑t a E E₂ (.gen (Generator.sigma : Generator (2 + 2 * h)))
                ^ E (Export.RawSpec.toZhat (.etahat num den))).u by
            rw [show foxD ⇑t a E E₂ _ = (foxEval ⇑t a E E₂ _).u from rfl,
              foxEval_profPow_of_ne _ _ _ _ _ hω]]
        have hzero : foxEval ⇑t a E E₂ (PWord.gen (Generator.sigma : Generator (2 + 2 * h)))
            = ⟨0, t.σ⟩ := by
          rw [foxEval_gen]
          exact congrArg (WordLift.mk · _) hσ
        rw [hzero]
        rcases E (Export.RawSpec.toZhat (.etahat num den)) with j | j
        · rw [show (Int.ofNat j) = ((j : ℕ) : ℤ) from rfl, zpow_natCast]
          induction j with
          | zero => rfl
          | succ j ih => rw [pow_succ, WordLift.mul_u, ih, smul_zero, add_zero]
        · rw [Int.negSucc_eq, zpow_neg, show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring,
            zpow_natCast, WordLift.inv_u]
          have : ∀ k : ℕ, ((⟨0, t.σ⟩ : WordLift V C) ^ k).u = 0 := by
            intro k
            induction k with
            | zero => rfl
            | succ k ih => rw [pow_succ, WordLift.mul_u, ih, smul_zero, add_zero]
          rw [this (j + 1), smul_zero, neg_zero]

/-! ### The δ-letter rows, at the ramified reading

`P = 0`: `D(δ_i) = −a(x_i)`.  **Cited from WM0-b, not re-derived** — `dW h i` and
`Words.MCompact.deltaC h i` are the same `PWord` (`dW_eq_deltaCert`). -/

/-- The ramified δ-row, transported to this lane's spelling. -/
theorem foxD_dW_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (i : Fin 3) :
    foxD ⇑t a E E₂ (dW h i) = -a (coreLetter h i) :=
  MCompact.foxD_deltaC_ram t E E₂ hwild hτfpf hTodd i a

/-- The δ-letters act trivially at the ramified reading. -/
theorem trivAct_dW_ram (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (i : Fin 3) :
    PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V :=
  MCompact.trivAct_deltaC t E E₂ hwild i (MCompact.trivAct_deltaBlock_ram t E E₂ hwild hTodd i)

/-! ### The factor rows

Standing hypotheses of this block, the ramified reading (`P = 0`) at σ-free offsets.  `U` below
is `powOmega2 t.σ = S₂`; every prefix weight on this row is a power of it, which is the whole
reason the balance is visible at first order. -/

section Factors

variable (hσ : a Generator.sigma = 0)
  (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
  (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)

include hσ hwild hτfpf hTodd

/-- `D(Â) = a(x₀)`: the `Ĉ₀⁻ᵐ` tail is σ-only, so the whole first-order content of `Â` is its
`δ₀`-head — and at the ramified reading `D(δ₀⁻¹) = a(x₀)` on the nose. -/
theorem foxD_aHatW (s' mm : ℕ) : foxD ⇑t a E E₂ (aHatW h s' mm) = a (coreLetter h 0) := by
  rw [aHatW, MCompact.foxD_prodList_pair, foxD_inv,
    mem_trivAct.mp (inv_mem (trivAct_dW_ram t E E₂ hwild hTodd 0)),
    foxD_dW_ram t E E₂ a hwild hτfpf hTodd 0]
  have hz : foxD ⇑t a E E₂ (.zpow (c0HatW h s') (-(mm : ℤ))) = 0 := by
    rw [foxD_zpow_neg', foxD_zpow_natCast,
      Finset.sum_eq_zero fun i _ => by
        rw [foxD_c0HatW_of_sigma_free t E E₂ a hσ s', smul_zero], smul_zero, neg_zero]
  rw [hz, smul_zero, add_zero, neg_neg]

/-- `D(B̂) = −a(x₁)`: the `σ₂^p` tail is σ-only. -/
theorem foxD_bHatW : ∀ pp : ℕ, foxD ⇑t a E E₂ (bHatW h pp) = -a (coreLetter h 1)
  | 0 => foxD_dW_ram t E E₂ a hwild hτfpf hTodd 1
  | q + 1 => by
      rw [show bHatW h (q + 1) = PWord.prodList [dW h 1, sig2PowW h (q + 1)] from rfl,
        MCompact.foxD_prodList_pair, foxD_dW_ram t E E₂ a hwild hτfpf hTodd 1]
      have hs : foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 := by
        match q with
        | 0 => exact foxD_sigma2W_of_sigma_free t E E₂ a hσ
        | j + 1 =>
            rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
            exact foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
      rw [hs, smul_zero, add_zero]

/-- **`E₀₁^pc`'s first-order contribution — stated, not hidden.**

```
D(E₀₁^pc) = −S₂^{−a−b}·a(x₁) − S₂^{−a}·a(x₁) − S₂^{−a}·a(x₀) − a(x₀)
```

a genuinely **nonzero** row: the block's four `δ`-occurrences each contribute, weighted by their
`σ₂`-conjugators.

⚠ Freeze row 5 (binding, paper-relevant): `E₂^pc` is first-order *essential* while `E₀₁^pc` is
first-order *redundant* — the shadow copy reproduces this entire contribution
operator-for-operator, so **gate D cannot justify `E₀₁^pc`**, and `E₀₁^pc` and the shadow
substitution are *not independently choosable*.  The justification of `E₀₁^pc` is second-order
only (the exact gate-F refutation on the fifth-root module), which is WMP-c's business, not
this file's.  This row and `foxD_e01_reproduced_by_shadow` below are the two halves of that
finding; **either one alone misrepresents the row**. -/
theorem foxD_e01W_ram (aa bb : ℕ) :
    foxD ⇑t a E E₂ (e01W h aa bb)
      = -((((powOmega2 t.σ) ^ aa)⁻¹ * ((powOmega2 t.σ) ^ bb)⁻¹) • a (coreLetter h 1))
        - (((powOmega2 t.σ) ^ aa)⁻¹) • a (coreLetter h 1)
        - (((powOmega2 t.σ) ^ aa)⁻¹) • a (coreLetter h 0)
        - a (coreLetter h 0) := by
  have hd0 := foxD_dW_ram t E E₂ a hwild hτfpf hTodd 0
  have hd1 := foxD_dW_ram t E E₂ a hwild hτfpf hTodd 1
  have ht0 := trivAct_dW_ram t E E₂ hwild hTodd 0
  have ht1 := trivAct_dW_ram t E E₂ hwild hTodd 1
  have hpow : ∀ k : ℕ, foxD ⇑t a E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (k : ℤ)) = 0 := fun k =>
    foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
  have hev : ∀ k : ℕ, PWord.evalFin ⇑t E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (k : ℤ)) = (powOmega2 t.σ) ^ k := by
    intro k
    rw [PWord.evalFin_zpow, MCompact.evalFin_sigma2W, zpow_natCast]
  -- the inner conjugate `δ₁^{σ₂^b}`
  have hconj : foxD ⇑t a E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ)))
      = (((powOmega2 t.σ) ^ bb)⁻¹) • (-a (coreLetter h 1)) := by
    rw [foxD_conj, hd1, hpow, smul_zero, add_zero, sub_zero, hev]
  have htconj : PWord.evalFin ⇑t E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ))) ∈ trivAct C V := by
    rw [PWord.evalFin_conj]
    exact trivAct_conjR ht1 _
  -- the inner three-factor product
  have hinner : foxD ⇑t a E E₂
      (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (bb : ℤ)), dW h 1, dW h 0])
      = (((powOmega2 t.σ) ^ bb)⁻¹) • (-a (coreLetter h 1)) + -a (coreLetter h 1)
          + -a (coreLetter h 0) := by
    rw [PWord.prodList_cons, foxD_mul, MCompact.foxD_prodList_pair, hconj, hd0, hd1,
      mem_trivAct.mp ht1, mem_trivAct.mp htconj, add_assoc]
  have htinner : PWord.evalFin ⇑t E E₂
      (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (bb : ℤ)), dW h 1, dW h 0])
      ∈ trivAct C V := by
    refine trivAct_evalFin_prodList fun w hw => ?_
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl | rfl
    · exact htconj
    · exact ht1
    · exact ht0
  rw [e01W, MCompact.foxD_prodList_pair, foxD_conj, hinner, hpow, smul_zero, add_zero, sub_zero,
    hev, hd0, PWord.evalFin_conj, mem_trivAct.mp (trivAct_conjR htinner _)]
  simp only [smul_add, smul_neg, mul_smul]
  abel

end Factors

end HatRow

end GQ2.Dyadic.Certificates.MProcyclic
