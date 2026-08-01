/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Words.Mpc
import GQ2.Dyadic.Certificates.M0Fox

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

/-- **The profinite-power-free fragment.**

Every displayed factor of the procyclic row is in it, because `σ₂` and `D = σ^{η̂}` are
displayed *definitions* — `Auxiliary` nodes — hence atoms of the displayed alphabet.  It is the
fragment on which §3's transport theorem is a plain structural induction: a `profPow` node
reads its finite representative at `2·ord(lower value)`, so two words with *equally acting*
evaluations need not have equally acting `ω₂`-powers.  That is the same phenomenon the shadow
memo's refutation of the naive chain rule turns on, and `NoProf` is where the discipline is
visible rather than assumed away. -/
def _root_.GQ2.Dyadic.PWord.NoProf {Gen : Type*} : PWord Gen → Prop
  | .one => True
  | .gen _ => True
  | .mul u v => u.NoProf ∧ v.NoProf
  | .inv u => u.NoProf
  | .conj u g => u.NoProf ∧ g.NoProf
  | .comm u v => u.NoProf ∧ v.NoProf
  | .zpow u _ => u.NoProf
  | .z2pow _ _ => False
  | .profPow _ _ => False

open PWord in
theorem noProf_prodList {Gen : Type*} :
    ∀ {l : List (PWord Gen)}, (∀ w ∈ l, w.NoProf) → (PWord.prodList l).NoProf
  | [], _ => trivial
  | w :: _ws, hw =>
      ⟨hw w (List.mem_cons_self ..), noProf_prodList fun u hu => hw u (List.mem_cons_of_mem _ hu)⟩

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
evaluations — then the two substituted words agree to first order too, throughout the `NoProf`
fragment.  Because `foxEval` carries the Fox derivative in `.u` and the base value in `.g`, one
statement transports **both** the certificate's `d¹` and its gate-B/C values.

This is *not* the naive chain rule, and deliberately so: it never pushes an operator through a
power node.  The shadow memo refutes the naive rule (a Fox derivative of a profinite power is
not a fixed group-ring element — its finite representative is read at `2·ord(lower value)`, so
pushing `ρ` through the substitution turns `P` into `1`), and `NoProf` is the fence around that
refutation, not a convenience. -/
theorem liftActEq_foxEval_subst {Y : Type*} (f f' : Y → PWord X)
    (hf : ∀ ℓ, LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ))) :
    ∀ w : PWord Y, w.NoProf →
      LiftActEq (foxEval t a E E₂ (PWord.subst f w)) (foxEval t a E E₂ (PWord.subst f' w)) := by
  intro w
  induction w with
  | one => intro _; exact LiftActEq.one
  | gen ℓ => intro _; exact hf ℓ
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
theorem foxD_subst_congr {Y : Type*} (f f' : Y → PWord X)
    (hf : ∀ ℓ, LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ)))
    (w : PWord Y) (hw : w.NoProf) :
    foxD t a E E₂ (PWord.subst f w) = foxD t a E E₂ (PWord.subst f' w) :=
  (liftActEq_foxEval_subst t a E E₂ f f' hf w hw).1

/-- **The value half of transport**: the substituted words' base values act equally.  This is
what makes the hat copy's gates B and C WMP-a's balance pair rather than a second ledger. -/
theorem evalFin_subst_act_congr {Y : Type*} (f f' : Y → PWord X)
    (hf : ∀ ℓ, LiftActEq (foxEval t a E E₂ (f ℓ)) (foxEval t a E E₂ (f' ℓ)))
    (w : PWord Y) (hw : w.NoProf) (v : A) :
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

end GQ2.Dyadic.Certificates.MProcyclic
