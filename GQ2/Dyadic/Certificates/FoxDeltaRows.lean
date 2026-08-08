/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Certificates.NpcFox
import GQ2.Dyadic.Certificates.MpcFox

/-!
# W51-HOIST: the Fox factor rows, parameterised by the δ-row

The origin note (W44-MPCUNRAM, campaign record, quoted verbatim):

> The `include hτfpf hTodd` hoist is NOT a hypothesis swap and NOT cheap (23 decls / ~660 ln
> across two unowned files; hTodd is derivable, only hτfpf is false unramified; the δ-rows are
> genuinely different statements) — own ticket, phrase as 'parameterise the factor rows by the
> δ-row'.

That is what this file does, additively.  Nothing committed is edited; the layer is new
declarations that the committed ramified statements are then re-derived through, and that the
unramified reading instantiates for the first time.

## What the δ-row is

Every `hτfpf`-carrying declaration of the four Fox files reaches `hτfpf` through **exactly one**
statement, the `ω₂`-block row

```
D((x_iτ)^{ω₂})  =  P·(a(x_i) + a(τ)),        i : Fin 3,
```

with `P` the `ω₂`-norm projector: `P = 1` unramified (`Npc.foxD_omega2Block_unram`,
`Certificates.foxD_deltaBlock_unram`) and `P = 0` ramified (`Npc.foxD_omega2Block_ram`,
`MCompact.foxD_deltaC_ram`'s inner step).  The certificate `δ`-letter is
`δ_i = (x_iτ)^{ω₂} x_i⁻¹`, so its row is the ω₂-block row minus `a(x_i)`:

```
D(δ_i)  =  P·(a(x_i) + a(τ)) − a(x_i)      =  a(τ)   at P = 1,   −a(x_i)   at P = 0.
```

Those two values are the *"genuinely different statements"* of the origin note.  `FoxDeltaRow`
below carries the row **as data**, a free vector `block a : Fin 3 → V` together with the two
facts the downstream layer actually consumes (the Fox value and the trivial action of the
block), so the factor rows are stated once, for an arbitrary δ-row, and the two readings are
two terms of the structure rather than two copies of the chain.

## Why the row and not the projector

The parameter is deliberately the **row value**, not an `AddMonoid.End V`.  Every consumer below
is linear in the row and never inspects it; taking the value keeps the layer free of any
commitment to the projector's shape, and lets a future third reading (a genuinely partial `P`)
instantiate the same theorems.  The two instances supplied here do have `block a i = P (a(x_i) +
a(τ))`, which is recorded as `deltaRowUnram_block` / `deltaRowRam_block`.

## `hTodd` is a theorem here, not a hypothesis

The origin note's *"hTodd is derivable"* is discharged as `FoxDeltaRow.todd`: from the block's
trivial action plus the uniform wild hypothesis, `ω₂`-naturality
(`GQ2.powOmega2_map`) recovers `∀ v, powOmega2 t.τ • v = v`.  So the parameterised layer carries
`hTodd` in **no** signature and supplies it to the committed lemmas that still want it.  The
committed declarations are untouched and keep their hypothesis.

## Staleness found, and what changed because of it

The origin note is **partly stale**, and the residual is stated precisely rather than assumed:

1. The Npc lane is *not* blocked at all: `Npc.foxD_npc_unram`, `foxDHom_npc_unram_column_eq_zero`
   and the unramified certificates were always there, alongside the ramified ones.  Same for the
   two h=0 twins: `N0Fox` and `M0Fox` carry a full `_unram` copy of every `_ram` row.
2. The Mpc lane's `section Factors` (`MpcFox.lean` 1333–1642, `include hσ hwild hτfpf hTodd`) is
   the real ramified-only region, and `GQ2/Dyadic/Instances/MpcUnramifiedBranch.lean` has since
   *duplicated by hand* its shallow half at the unramified reading (`foxD_dW_unram`,
   `foxD_aHatW_unram`, `foxD_bHatW_unram`, `foxD_e01W_unram`).
3. What no file has, at any reading other than the ramified one, is the section's **headline**:
   `MpcFox.foxD_mpcHatW_ram`, the hat copy's first Fox derivative.  That is the one genuinely
   unreachable consumer-facing theorem, and `foxDelta_mpcHatW_unram` (§6) is it.

So the layer's value is two things at once: the unreachable endpoint becomes reachable, and the
hand-duplicated shallow rows become instantiations of one statement (§4 subsumes both the
committed ramified rows and `MpcUnramifiedBranch`'s copies; rewiring those consumers is
deliberately **not** in this wave's scope).

## Scope decisions

* **`N0Fox` / `M0Fox` are in scope only through their δ-row constructors.**  Both files already
  carry the complete unramified twin of every ramified row, so a parameterised restatement of
  their chains would buy nothing this wave; what they do supply is `MCompact.trivAct_deltaC`,
  already parameterised by the block's trivial action ("the class-neutral hinge"), and
  `MCompact.trivAct_deltaBlock_unram` / `_ram`, which are the two δ-row constructors of §2.
* **The certificate layer is out of scope**, and for a structural reason rather than budget: a
  `FoxCertificate` is stated over the *formal* alphabet at a fixed interpretation
  (`NpcSym.ramifiedEnd` vs `splitEnd`) and the ramified branch carries two column operations
  where the unramified branch carries none (`npcRamOps` vs `[]`).  Those are different data, not
  a common statement with a parameter, so the certificates are not δ-row-parameterisable and the
  ticket's "full consumer rewiring is not in scope" is the right ruling for them.

## Sections

0. The one micro-lemma the layer needs: `ω₂`-transparency, read backwards.
1. `FoxDeltaRow`: the structure, and everything derived from it (`todd`, the δ-letter row).
2. The two instances: `deltaRowRam` and `deltaRowUnram`.
3. The parameterised noncompact-`N` factor rows.
4. The parameterised procyclic-`M` factor rows, up to the hat copy.
5. The ramified pins: committed statements re-derived through the layer.
6. The unramified instantiation, including the previously unreachable hat row.
7. Axiom pins.

## Implementation notes

Not `module`-style, and forced: `Certificates/NpcFox.lean` and `Certificates/MpcFox.lean` are
plain-import files (WN0-a's ruling that `Words/` and `Certificates/` are plain-import layers), so
a `module` file could not import them.

The two lanes cannot both be `open`ed at file scope: `Words.Npc.aW` (the η̂-conjugator, one
`EtaData` argument) and `Words.Mpc.aW` (the Labute letter, two `ℕ` arguments) collide, as do
`bW` and `coreLetter`'s neighbours.  §3 and §4 are therefore separate sections with their own
`open` lines.  `Words.MCompact.deltaC` is opened under the rename `deltaCert`, as `MpcFox.lean`
does, because the frozen peripheral `GQ2.deltaC` wins the resolution race silently.
-/

namespace GQ2.Dyadic.Certificates.FoxDelta

open GQ2.FoxH GQ2.Dyadic.Words

/-! ## §0. The `ω₂`-transparency lemma

One micro-lemma the layer needs and no file has: the converse half of
`WordLift.powOmega2_smul_of_trivial_mul`.  Both directions are the same two-line naturality
argument; only the forward one was ever needed before. -/

section Transparent

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]

/-- **A trivially-acting left factor is `ω₂`-transparent, backwards.**  If `g` acts trivially on
`V` and `powOmega2 (g * y)` acts trivially, then `powOmega2 y` does.

`WordLift.powOmega2_smul_of_trivial_mul` is the forward reading of the same fact; the proof is
`GQ2.powOmega2_map` at `MulAction.toPermHom C V`, under which `g ↦ 1`, so `powOmega2 (g * y)`
and `powOmega2 y` induce the **same permutation** of `V`.  This is the step that turns the
δ-row's own trivial-action field into `hTodd`, which is why the parameterised layer never has to
carry `hTodd`. -/
theorem powOmega2_trivAct_of_trivial_mul {g y : C} (hg : g ∈ trivAct C V)
    (hgy : powOmega2 (g * y) ∈ trivAct C V) : powOmega2 y ∈ trivAct C V := by
  have hperm : MulAction.toPermHom C V g = 1 := MonoidHom.mem_ker.mp hg
  have hnat := powOmega2_map (MulAction.toPermHom C V) (g * y)
  rw [map_mul, hperm, one_mul, ← powOmega2_map] at hnat
  exact MonoidHom.mem_ker.mpr (hnat ▸ MonoidHom.mem_ker.mp hgy)

end Transparent

/-! ## §1. The δ-row

The parameter of the whole layer.  Three fields plus the uniform wild hypothesis; everything the
`hτfpf`-carrying chain consumes is one of them, or derived from them here. -/

section Row

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The δ-row at a marking, a resolver pair and an offset vector.**

The datum the factor rows of both lanes are parameterised by:

* `wild`, the uniform class hypothesis, true at every reading (the wild letters act trivially);
* `block`, the row itself: the value of `D((x_iτ)^{ω₂})` per core letter;
* `foxD_block`, that this *is* that value;
* `trivAct_block`, that the `ω₂`-block evaluates into the trivially-acting subgroup.

`τ` appears in no field.  The ramified branch's `hτfpf` and the unramified branch's `hτ` are
spent **once**, in the two constructors of §2, and never again: this is the whole point of the
parameterisation, since `hτfpf` is false at unramified parameters and so is `hτ` at ramified
ones, while every consumer below holds at both.

`hTodd` is not a field either.  It is `FoxDeltaRow.todd`, a theorem.

The row is a function **of the offset vector**, not a value at one offset.  It has to be: a
*column* of an evaluated row is the row at the single-slot offset `Pi.single g v`
(`Npc.foxDHom_npc_ram_column_eq_zero` and its handle corollaries are exactly that), so a δ-row
pinned to one offset could not state them.  Both instances of §2 are uniform in the offset
anyway. -/
structure FoxDeltaRow where
  /-- The uniform wild hypothesis: the wild letters `x_i` act trivially on `V`. -/
  wild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v
  /-- The row: the first-order value of the `ω₂`-block `(x_iτ)^{ω₂}`, per offset and core
  letter. -/
  block : (Generator (2 + 2 * h) → V) → Fin 3 → V
  /-- The `ω₂`-block's Fox derivative is the row. -/
  foxD_block : ∀ (a : Generator (2 + 2 * h) → V) (i : Fin 3), foxD ⇑t a E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) = block a i
  /-- The `ω₂`-block acts trivially.  Uniform in the reading and in the offset, and the field
  that replaces `hTodd` everywhere downstream. -/
  trivAct_block : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V

namespace FoxDeltaRow

variable {t E E₂} (dr : FoxDeltaRow (V := V) t E E₂) (a : Generator (2 + 2 * h) → V)

include dr

omit [Finite C] [Finite V] in
/-- The core letters act trivially: `wild`, in subgroup form. -/
theorem trivAct_coreLetter (i : Fin 3) : t (coreLetter h i) ∈ trivAct C V :=
  mem_trivAct.mpr (dr.wild _)

omit [Finite V] in
/-- **`hTodd` is derivable from the δ-row**: the origin note's *"hTodd is derivable"*, made a
theorem.

`trivAct_block 0` says `powOmega2 (x₀ · τ)` acts trivially; `x₀` acts trivially by `wild`; so
`powOmega2 τ` acts trivially by `ω₂`-transparency.  No hypothesis of either branch is used, so
the parameterised layer can hand `hTodd` to every committed lemma that still asks for it without
ever binding it. -/
theorem toddMem : powOmega2 t.τ ∈ trivAct C V := by
  refine powOmega2_trivAct_of_trivial_mul (dr.trivAct_coreLetter 0) ?_
  have h0 := dr.trivAct_block 0
  rwa [PWord.evalFin_omega2Pow, Npc.evalFin_deltaInner t E E₂ 0] at h0

omit [Finite V] in
@[inherit_doc toddMem]
theorem todd : ∀ v : V, powOmega2 t.τ • v = v := mem_trivAct.mp dr.toddMem

omit [Finite C] [Finite V] in
/-- The certificate `δ`-letter `δ_i = (x_iτ)^{ω₂}x_i⁻¹` acts trivially.  `MCompact.trivAct_deltaC`
is already parameterised by the block's trivial action (the house's own class-neutral hinge),
so this is that lemma fed the structure's field. -/
theorem trivAct_delta (i : Fin 3) :
    PWord.evalFin ⇑t E E₂ (Words.MCompact.deltaC h i) ∈ trivAct C V :=
  MCompact.trivAct_deltaC t E E₂ dr.wild i (dr.trivAct_block i)

/-- **The δ-row proper**: the value `D(δ_i)` of the certificate `δ`-letter's Fox derivative,
`block a i − a(x_i)`.

This is the vector the origin note names, and the one every procyclic-`M` factor row of §4 is
stated in.  It is `a(τ)` unramified and `−a(x_i)` ramified: two genuinely different rows, one
definition. -/
def deltaVal (i : Fin 3) : V := dr.block a i - a (coreLetter h i)

/-- **The δ-letter row: `D(δ_i) = deltaVal a i`.**

At `block a i = a(x_i) + a(τ)` (unramified) this is `MCompact.foxD_deltaC_unram`'s `a(τ)`; at
`block a i = 0` (ramified) it is `MCompact.foxD_deltaC_ram`'s `−a(x_i)`; here it is one
theorem. -/
theorem foxD_delta (i : Fin 3) :
    foxD ⇑t a E E₂ (Words.MCompact.deltaC h i) = dr.deltaVal a i := by
  rw [Words.MCompact.deltaC, MCompact.foxD_prodList_pair, dr.foxD_block a i,
    mem_trivAct.mp (dr.trivAct_block i), foxD_inv, PWord.evalFin_gen, foxD_gen,
    mem_trivAct.mp (inv_mem (dr.trivAct_coreLetter i)), deltaVal]
  abel

end FoxDeltaRow

end Row

/-! ## §2. The two readings

Both branch hypotheses are spent here and nowhere else.  `deltaRowRam` is the only place `hτfpf`
appears in this file; `deltaRowUnram` is the only place `hτ` does. -/

section Instances

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **The ramified δ-row** (`P = 0`): the `ω₂`-block dies, `block a i = 0`.

This is the single point of the file at which `hτfpf` is consumed.  Everything the committed
ramified chain proves from `hτfpf` is proved below from *this term*, so the branch hypothesis
never reaches a factor-row statement again. -/
def deltaRowRam (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    FoxDeltaRow (V := V) t E E₂ where
  wild := hwild
  block _ _ := 0
  foxD_block a i := Npc.foxD_omega2Block_ram t E E₂ i hwild hτfpf hTodd a
  trivAct_block i := MCompact.trivAct_deltaBlock_ram t E E₂ hwild hTodd i

/-- **The unramified δ-row** (`P = 1`): the `ω₂`-block is transparent,
`block a i = a(x_i) + a(τ)`.

The row the origin note asks for.  It is *not* the ramified row with a hypothesis swapped: the
two are different vectors, and that is exactly why the chain had to be parameterised rather than
re-hypothesised.  Reading it off the unramified branch is immediate once the block is isolated,
since `τ` acts trivially there and `WordLift.powOmega2_u_of_trivial` differentiates the
`ω₂`-power of a trivially-acting base as the base's own row `a(x_i) + a(τ)`
(`Npc.foxD_omega2Block_unram`).

`hTodd` is not an argument: on this branch it follows from `hτ`, and the layer derives it from
the row itself (`FoxDeltaRow.todd`) in any case. -/
def deltaRowUnram (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v) :
    FoxDeltaRow (V := V) t E E₂ where
  wild := hwild
  block a i := a (coreLetter h i) + a .tau
  foxD_block a i := Npc.foxD_omega2Block_unram t E E₂ i hV₂ hwild hτ a
  trivAct_block i := MCompact.trivAct_deltaBlock_unram t E E₂ hwild hτ i

@[simp] theorem deltaRowRam_block (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) (i : Fin 3) :
    (deltaRowRam t E E₂ hwild hτfpf hTodd).block a i = 0 := rfl

@[simp] theorem deltaRowUnram_block (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (a : Generator (2 + 2 * h) → V) (i : Fin 3) :
    (deltaRowUnram t E E₂ hV₂ hwild hτ).block a i = a (coreLetter h i) + a .tau := rfl

end Instances

/-! ## §3. The noncompact-`N` factor rows, parameterised

The `hτfpf`-carrying half of `NpcFox.lean`'s `section Rows`, restated once.  Four of the word's
six factors (`x₀^{p_α}`, `[x₀,A]`, `x₂^{-g}`, `H_h`) never see the δ-row and are cited
unchanged; the `ω₂`-block is the row itself; the correction block `E_{r,η}` sees it only through
`hTodd`, which is `FoxDeltaRow.todd`.

The committed `Npc.foxD_npc_ram` and `Npc.foxD_npc_unram` are the two specialisations, pinned in
§5 and §6. -/

section NpcRows

open GQ2.Dyadic.Words.Npc

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] {t : Marking (2 + 2 * h) C} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
  (dr : FoxDeltaRow (V := V) t E E₂)

include dr

/-- **The noncompact-`N` wild row at an arbitrary δ-row.**

```
D(R_{N,α,r,η}) = (A⁻¹ − 1)·a(x₀) + (block(a)₂ − B⁻¹·a(x₂)),   A = S^{E(η̂)}, B = S^{2^r}
```

One statement for both module classes.  The δ-row enters in exactly one slot, the `ω₂`-block's,
which is the honest content of "the `τ`- and `x₂`-halves of the `ω₂`-block die" (ramified,
`block = 0`) versus "the row carries the `τ`-pivot" (unramified, `block a 2 = a(x₂) + a(τ)`):
the *rest* of the row is class-independent and always was.

`hα : 1 ≤ α` is spent on the leading power's parity and `hV₂` with it; neither touches the
δ-row. -/
theorem foxDelta_npc (hV₂ : ∀ v : V, v + v = 0) (hα : 1 ≤ α) (e : EtaData)
    (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e)
      = ((t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0))
        + (dr.block a 2 - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2)) := by
  rw [npcW, foxD_prodList_of_trivial _ _ _ _ _
    (Npc.trivAct_npc_factors t E E₂ dr.wild dr.todd e)]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [Npc.foxD_leadingPow t E E₂ hV₂ dr.wild hα, Npc.foxD_commX0A t E E₂ dr.wild e,
    Npc.foxD_invConjX2G t E E₂ dr.wild, dr.foxD_block a 2,
    Npc.foxD_eBlockW t E E₂ dr.wild dr.todd e, Npc.foxD_handlesW t E E₂ dr.wild]
  abel

/-- **Every column off `x₀`, `x₂` is the δ-row's own entry.**

A column of the evaluated row is the row at a single-slot offset `Pi.single g v`, so this is
`foxDelta_npc` read at that offset with the two surviving letters missed.  At the ramified row
the right-hand side is `0` and this is `Npc.foxDHom_npc_ram_column_eq_zero`; at the unramified
row it is `Pi.single g v (x₂) + Pi.single g v (τ)`, which is `0` unless `g = τ` and reproduces
`Npc.foxDHom_npc_unram_column_eq_zero`'s extra `g ≠ τ` hypothesis as an output rather than an
input.

This is the statement that forces the δ-row to be a function of the offset. -/
theorem foxDelta_npcHom_column (hV₂ : ∀ v : V, v + v = 0) (hα : 1 ≤ α) (e : EtaData)
    {g : Generator (2 + 2 * h)} (hg0 : g ≠ coreLetter h 0) (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single g v) = dr.block (Pi.single g v) 2 := by
  rw [foxDHom_apply, foxDelta_npc dr hV₂ hα e, Pi.single_eq_of_ne (Ne.symm hg0),
    Pi.single_eq_of_ne (Ne.symm hg2)]
  simp

/-- The `2h` handle columns, at an arbitrary δ-row: the `u`-half. -/
theorem foxDelta_npcHom_handleU_column (hV₂ : ∀ v : V, v + v = 0) (hα : 1 ≤ α) (e : EtaData)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single (handleU j) v)
      = dr.block (Pi.single (handleU j) v) 2 :=
  foxDelta_npcHom_column dr hV₂ hα e (Npc.handleU_ne_coreLetter j 0)
    (Npc.handleU_ne_coreLetter j 2) v

/-- The `2h` handle columns, at an arbitrary δ-row: the `v`-half. -/
theorem foxDelta_npcHom_handleV_column (hV₂ : ∀ v : V, v + v = 0) (hα : 1 ≤ α) (e : EtaData)
    (j : Fin h) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single (handleV j) v)
      = dr.block (Pi.single (handleV j) v) 2 :=
  foxDelta_npcHom_column dr hV₂ hα e (Npc.handleV_ne_coreLetter j 0)
    (Npc.handleV_ne_coreLetter j 2) v

/-- **Gate-D blindness at an arbitrary δ-row**: the corrected and the uncorrected words have the
same Fox row.  The committed statement is already class-uniform (`hTodd` only); it is restated
here only so the layer is closed under the section's own consumers, with `hTodd` supplied by the
row rather than bound. -/
theorem foxDelta_npcW_eq_uncorrected (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e) = foxD ⇑t a E E₂ (Npc.npcUncorrectedW α r h e) :=
  Npc.foxD_npcW_eq_uncorrected t E E₂ dr.wild dr.todd e a

/-- **The `D`-block's row at an arbitrary δ-row**: the corrected cross operator applied to
`D(δ₀)`, which the layer now writes as the δ-row itself.  `Npc.foxD_dBlockW` states it with
`D(δ₀)` opaque and `hTodd` bound; here `D(δ₀)` is `dr.deltaVal a 0`
(`FoxDeltaRow.foxD_delta`) and `hTodd` is derived. -/
theorem foxDelta_dBlockW (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (dBlockW h r e)
      = (t.σ ^ E e.toZhat)⁻¹ • dr.deltaVal a 0
        + (t.σ ^ ((2 : ℤ) ^ r) • dr.deltaVal a 0
          + t.σ ^ ((2 : ℤ) ^ r) • (t.σ ^ E e.toZhat)⁻¹ • dr.deltaVal a 0) := by
  have hδ : foxD ⇑t a E E₂ (deltaZeroW h) = dr.deltaVal a 0 := dr.foxD_delta a 0
  rw [Npc.foxD_dBlockW t E E₂ dr.wild dr.todd e a, hδ]

end NpcRows

/-! ## §4. The procyclic-`M` factor rows, parameterised

`MpcFox.lean`'s `section Factors` is the file's ramified-only region: `include hσ hwild hτfpf
hTodd`, eight declarations, and no unramified twin anywhere in the tree for its headline.  This
section is that block restated with the δ-row as the parameter.

Every row here is **linear in the δ-row** and never inspects it, which is what makes the
parameterisation exact rather than a weakening: the ramified reading substitutes
`deltaVal a i = −a(x_i)` and reproduces the committed statements on the nose (§5), the
unramified reading substitutes `deltaVal a i = a(τ)` (§6).

`hσ : a σ = 0` stays a hypothesis.  It is not a class condition at all (it says the offset
vector is `σ`-free) and it is uniform across readings; the freeze's own splitting of the hat-row
statement into "σ-free offsets here, the σ-column at §4's coincidence lemma" is untouched. -/

section MpcRows

open GQ2.Dyadic.Words.Mpc

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] {t : Marking (2 + 2 * h) C} {E : Zhat → ℤ} {E₂ : ℤ_[2] → ℤ}
  (dr : FoxDeltaRow (V := V) t E E₂) (a : Generator (2 + 2 * h) → V)

include dr

/-- **The δ-letter row in this lane's spelling.**  `dW h i` and `Words.MCompact.deltaC h i` are
the same `PWord` (`MProcyclic.dW_eq_deltaCert`), so this is `FoxDeltaRow.foxD_delta` transported,
and it is the δ-row-parameterised replacement for `MProcyclic.foxD_dW_ram`. -/
theorem foxDelta_dW (i : Fin 3) : foxD ⇑t a E E₂ (dW h i) = dr.deltaVal a i :=
  dr.foxD_delta a i

omit [Finite C] [Finite V] in
/-- The δ-letters act trivially, at every reading. -/
theorem foxDelta_trivAct_dW (i : Fin 3) : PWord.evalFin ⇑t E E₂ (dW h i) ∈ trivAct C V :=
  dr.trivAct_delta i

/-- **`D(Â) = −D(δ₀)`**: the `Ĉ₀⁻ᵐ` tail is `σ`-only, so the whole first-order content of `Â` is
its `δ₀`-head, inverted.  At the ramified row this is `a(x₀)`
(`MProcyclic.foxD_aHatW`); at the unramified row it is `−a(τ)`, which is
`MpcUnramifiedBranch.foxD_aHatW_unram`'s `a(τ)` up to the char-2 sign that lemma spends `hV₂`
on.  The parameterised statement needs no `hV₂`. -/
theorem foxDelta_aHatW (hσ : a Generator.sigma = 0) (s' mm : ℕ) :
    foxD ⇑t a E E₂ (aHatW h s' mm) = -dr.deltaVal a 0 := by
  rw [aHatW, MCompact.foxD_prodList_pair, foxD_inv,
    mem_trivAct.mp (inv_mem (foxDelta_trivAct_dW dr 0)), foxDelta_dW dr a 0]
  have hz : foxD ⇑t a E E₂ (.zpow (c0HatW h s') (-(mm : ℤ))) = 0 := by
    rw [foxD_zpow_neg', foxD_zpow_natCast,
      Finset.sum_eq_zero fun i _ => by
        rw [MProcyclic.foxD_c0HatW_of_sigma_free t E E₂ a hσ s', smul_zero], smul_zero, neg_zero]
  rw [hz, smul_zero, add_zero]

/-- **`D(B̂) = D(δ₁)`**: the `σ₂^p` tail is `σ`-only.  `−a(x₁)` ramified
(`MProcyclic.foxD_bHatW`), `a(τ)` unramified (`MpcUnramifiedBranch.foxD_bHatW_unram`), and here
neither reading is built in. -/
theorem foxDelta_bHatW (hσ : a Generator.sigma = 0) :
    ∀ pp : ℕ, foxD ⇑t a E E₂ (bHatW h pp) = dr.deltaVal a 1
  | 0 => foxDelta_dW dr a 1
  | q + 1 => by
      rw [show bHatW h (q + 1) = PWord.prodList [dW h 1, sig2PowW h (q + 1)] from rfl,
        MCompact.foxD_prodList_pair, foxDelta_dW dr a 1]
      have hs : foxD ⇑t a E E₂ (sig2PowW h (q + 1)) = 0 := by
        match q with
        | 0 => exact MProcyclic.foxD_sigma2W_of_sigma_free t E E₂ a hσ
        | j + 1 =>
            rw [show sig2PowW h (j + 2) = .zpow sigma2W ((j + 2 : ℕ) : ℤ) from rfl]
            exact MProcyclic.foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
      rw [hs, smul_zero, add_zero]

/-- **`E₀₁^pc`'s first-order contribution at an arbitrary δ-row**:

```
D(E₀₁^pc) = (S₂^{−a−b} + S₂^{−a})·D(δ₁) + (S₂^{−a} + 1)·D(δ₀).
```

The block's four `δ`-occurrences, each weighted by its `σ₂`-conjugator, and nothing else: the
statement is *manifestly* linear in the δ-row, which is the structural reason freeze row 5's
finding (`E₀₁^pc` is first-order redundant, gate D cannot justify it) is class-independent.
Ramified this is `MProcyclic.foxD_e01W_ram`; unramified all four weights hit the same `a(τ)` and
the sum dies over `F₂` once `S₂` acts trivially, which is
`MpcUnramifiedBranch.foxD_e01W_unram`. -/
theorem foxDelta_e01W (hσ : a Generator.sigma = 0) (aa bb : ℕ) :
    foxD ⇑t a E E₂ (e01W h aa bb)
      = (((powOmega2 t.σ) ^ aa)⁻¹ * ((powOmega2 t.σ) ^ bb)⁻¹) • dr.deltaVal a 1
        + (((powOmega2 t.σ) ^ aa)⁻¹) • dr.deltaVal a 1
        + (((powOmega2 t.σ) ^ aa)⁻¹) • dr.deltaVal a 0
        + dr.deltaVal a 0 := by
  have hd0 := foxDelta_dW dr a 0
  have hd1 := foxDelta_dW dr a 1
  have ht0 := foxDelta_trivAct_dW dr 0
  have ht1 := foxDelta_trivAct_dW dr 1
  have hpow : ∀ k : ℕ, foxD ⇑t a E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (k : ℤ)) = 0 := fun k =>
    MProcyclic.foxD_sigma2Pow_of_sigma_free t E E₂ a hσ _
  have hev : ∀ k : ℕ, PWord.evalFin ⇑t E E₂
      (.zpow (sigma2W : PWord (Generator (2 + 2 * h))) (k : ℤ)) = (powOmega2 t.σ) ^ k := by
    intro k
    rw [PWord.evalFin_zpow, MCompact.evalFin_sigma2W, zpow_natCast]
  have hconj : foxD ⇑t a E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ)))
      = (((powOmega2 t.σ) ^ bb)⁻¹) • dr.deltaVal a 1 := by
    rw [foxD_conj, hd1, hpow, smul_zero, add_zero, sub_zero, hev]
  have htconj : PWord.evalFin ⇑t E E₂ (.conj (dW h 1) (.zpow sigma2W (bb : ℤ))) ∈ trivAct C V := by
    rw [PWord.evalFin_conj]
    exact trivAct_conjR ht1 _
  have hinner : foxD ⇑t a E E₂
      (PWord.prodList [.conj (dW h 1) (.zpow sigma2W (bb : ℤ)), dW h 1, dW h 0])
      = (((powOmega2 t.σ) ^ bb)⁻¹) • dr.deltaVal a 1 + dr.deltaVal a 1
          + dr.deltaVal a 0 := by
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
  simp only [smul_add, mul_smul]

/-! ### The assembled hat row: the headline

`MpcFox.foxD_mpcHatW_ram` is draft Rem. 5.4's first-order half, and the deepest declaration of
the ramified-only region.  Its whole proof is arithmetic in the one procyclic letter
`U = S₂ = σ^{ω₂}` applied to the **two** vectors `D(Â)` and `D(B̂)`, and those are `∓D(δ_i)`.
So the theorem is not ramified at all: it holds at every δ-row, and the two `δ`-columns cancel
for the reason the memo gives (the `x_i`- and `δ_i`-occurrences carry the same prefix sum, and
`hV₂` finishes the doubled `x₁`-column) whatever the row's value.

The `obtain` pair below is the honest way to say that: `X₀` and `X₁` are introduced as *opaque*
vectors with `D(δ_i) = −X_i`, so nothing after them can depend on which reading is in force. -/

/-- **The hat copy has zero first Fox derivative, at every δ-row.**

At `σ`-free offsets, `D(R̂^pc) = 0` for every `(α, r, p)` with `α ≥ 1`, every `η̂` display, and
**every** reading of the `ω₂`-block.  The committed `MProcyclic.foxD_mpcHatW_ram` is the
`deltaVal a i = −a(x_i)` case (pinned in §5); `foxDelta_mpcHatW_unram` (§6) is the
`deltaVal a i = a(τ)` case, which no file could state before.

`α ≥ 1` enters in exactly one place and it is the packet's own balance:
`−2m·2^r + 2^α·2^r = 0` (`s_mul_two_pow`).  Nothing else on the row uses it, and nothing at all
uses the reading. -/
theorem foxDelta_mpcHatW (hσ : a Generator.sigma = 0) {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ)
    (η : EtaDisplay) (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcHatW α r pp η h) = 0 := by
  set U := powOmega2 t.σ with hUdef
  set k : ℕ := s r * m α with hkdef
  obtain ⟨X₀, hX0⟩ : ∃ X : V, dr.deltaVal a 0 = -X := ⟨-dr.deltaVal a 0, (neg_neg _).symm⟩
  obtain ⟨X₁, hX1⟩ : ∃ X : V, dr.deltaVal a 1 = -X := ⟨-dr.deltaVal a 1, (neg_neg _).symm⟩
  have hmerge : ∀ (i j : ℤ) (w : V), (U ^ i) • ((U ^ j) • w) = (U ^ (i + j)) • w := by
    intro i j w; rw [← mul_smul, ← zpow_add]
  have hA : foxD ⇑t a E E₂ (aHatW h (s r) (m α)) = X₀ := by
    rw [foxDelta_aHatW dr a hσ, hX0, neg_neg]
  have hB : foxD ⇑t a E E₂ (bHatW h pp) = -X₁ := by
    rw [foxDelta_bHatW dr a hσ pp, hX1]
  have hAact : ∀ w : V,
      PWord.evalFin ⇑t E E₂ (aHatW h (s r) (m α)) • w = (U ^ (-(k : ℕ) : ℤ)) • w :=
    MProcyclic.evalFin_aHatW_act t E E₂ dr.wild dr.todd _ _
  have hBact : ∀ w : V, PWord.evalFin ⇑t E E₂ (bHatW h pp) • w = (U ^ ((pp : ℕ) : ℤ)) • w :=
    MProcyclic.evalFin_bHatW_act t E E₂ dr.wild dr.todd pp
  have hAinv : ∀ w : V,
      (PWord.evalFin ⇑t E E₂ (aHatW h (s r) (m α)))⁻¹ • w = (U ^ ((k : ℕ) : ℤ)) • w := by
    intro w; rw [inv_smul_eq_iff, hAact, hmerge]; simp
  have hBinv : ∀ w : V,
      (PWord.evalFin ⇑t E E₂ (bHatW h pp))⁻¹ • w = (U ^ (-(pp : ℕ) : ℤ)) • w := by
    intro w; rw [inv_smul_eq_iff, hBact, hmerge]; simp
  -- factor 1: `Â²`
  have hf1 : foxD ⇑t a E E₂ (.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ))
      = X₀ + (U ^ (-(k : ℕ) : ℤ)) • X₀ := by
    rw [foxD_zpow_natCast, Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero,
      pow_zero, pow_one, one_smul, zero_add, hA, hAact]
  -- factor 2: `[Â,B̂]`, where neither entry acts trivially
  have hf2 : foxD ⇑t a E E₂ (.comm (aHatW h (s r) (m α)) (bHatW h pp))
      = -((U ^ ((k : ℕ) : ℤ)) • X₀) - (U ^ (((k : ℕ) : ℤ) + (-(pp : ℕ) : ℤ))) • (-X₁)
        + (U ^ (((k : ℕ) : ℤ) + (-(pp : ℕ) : ℤ))) • X₀
        + (U ^ (-(pp : ℕ) : ℤ)) • (-X₁) := by
    rw [MProcyclic.foxD_comm_general, hA, hB]
    simp only [mul_smul, hAinv, hBinv, hAact, hmerge]
    rw [show ((k : ℕ) : ℤ) + ((-(pp : ℕ) : ℤ) + (-(k : ℕ) : ℤ)) = (-(pp : ℕ) : ℤ) by ring]
  -- factors 3 and 4 are silent off the σ-column
  have hf3 : foxD ⇑t a E E₂ (.zpow (c0HatW h (s r)) ((2 ^ α : ℕ) : ℤ)) = 0 := by
    rw [foxD_zpow_natCast]
    exact Finset.sum_eq_zero fun i _ => by
      rw [MProcyclic.foxD_c0HatW_of_sigma_free t E E₂ a hσ, smul_zero]
  have hf4 : foxD ⇑t a E E₂ (.comm (c0HatW h (s r)) (η.toPWord (n := 2 + 2 * h))) = 0 := by
    rw [MProcyclic.foxD_comm_general, MProcyclic.foxD_c0HatW_of_sigma_free t E E₂ a hσ,
      MProcyclic.foxD_etaDisplay_of_sigma_free t E E₂ a hσ]
    simp
  -- factor 5: `E₀₁^pc`
  have hpowinv : ∀ (j : ℕ) (w : V), ((U ^ j)⁻¹ : C) • w = (U ^ (-(j : ℕ) : ℤ)) • w := by
    intro j w; rw [zpow_neg, zpow_natCast]
  have hf5 : foxD ⇑t a E E₂ (e01W h (pp + k) k)
      = -((U ^ ((-(pp + k : ℕ) : ℤ) + (-(k : ℕ) : ℤ))) • X₁)
        - (U ^ (-(pp + k : ℕ) : ℤ)) • X₁ - (U ^ (-(pp + k : ℕ) : ℤ)) • X₀ - X₀ := by
    rw [foxDelta_e01W dr a hσ, hX0, hX1]
    simp only [← hUdef, mul_smul, hpowinv, hmerge, smul_neg]
    abel
  -- prefix weights
  have hw1 : ∀ w : V,
      PWord.evalFin ⇑t E E₂ (.zpow (aHatW h (s r) (m α)) ((2 : ℕ) : ℤ)) • w
        = (U ^ ((-(k : ℕ) : ℤ) + (-(k : ℕ) : ℤ))) • w := by
    intro w
    rw [PWord.evalFin_zpow, zpow_natCast, pow_two, mul_smul, hAact, hAact, hmerge]
  have hcommTriv : ∀ (u v : PWord (Generator (2 + 2 * h))) (i j : ℤ),
      (∀ w : V, PWord.evalFin ⇑t E E₂ u • w = (U ^ i) • w) →
      (∀ w : V, PWord.evalFin ⇑t E E₂ v • w = (U ^ j) • w) →
      ∀ w : V, PWord.evalFin ⇑t E E₂ (.comm u v) • w = w := by
    intro u v i j hu hv w
    have hiu : ∀ w : V, (PWord.evalFin ⇑t E E₂ u)⁻¹ • w = (U ^ (-i)) • w := by
      intro w; rw [inv_smul_eq_iff, hu, hmerge]; simp
    have hiv : ∀ w : V, (PWord.evalFin ⇑t E E₂ v)⁻¹ • w = (U ^ (-j)) • w := by
      intro w; rw [inv_smul_eq_iff, hv, hmerge]; simp
    rw [PWord.evalFin_comm, commR]
    simp only [mul_smul, hv, hu, hiv, hiu, hmerge]
    rw [show -i + (-j + (i + j)) = (0 : ℤ) by ring, zpow_zero, one_smul]
  have hw2 : ∀ w : V,
      PWord.evalFin ⇑t E E₂ (.comm (aHatW h (s r) (m α)) (bHatW h pp)) • w = w :=
    hcommTriv _ _ _ _ hAact hBact
  have hknat : s r * 2 ^ α = k + k := by
    have := s_mul_two_pow (α := α) hα r
    rw [hkdef]; omega
  have hw3 : ∀ w : V,
      PWord.evalFin ⇑t E E₂ (.zpow (c0HatW h (s r)) ((2 ^ α : ℕ) : ℤ)) • w
        = (U ^ (((k : ℕ) : ℤ) + ((k : ℕ) : ℤ))) • w := by
    intro w
    rw [PWord.evalFin_zpow, MProcyclic.evalFin_c0HatW_eq, ← zpow_mul]
    congr 2
    rw [← Nat.cast_mul, hknat]
    push_cast
    ring
  -- `[Ĉ₀,D]` is trivial because both entries are `ℤ`-powers of `σ`
  have hw4 : ∀ w : V,
      PWord.evalFin ⇑t E E₂ (.comm (c0HatW h (s r)) (η.toPWord (n := 2 + 2 * h))) • w = w := by
    obtain ⟨n, hn⟩ := MProcyclic.exists_zpow_evalFin_etaDisplay t E E₂ η
    have hc0 : PWord.evalFin ⇑t E E₂ (c0HatW h (s r))
        = t.σ ^ ((omega2Exp (orderOf t.σ) * s r : ℕ) : ℤ) := by
      rw [MProcyclic.evalFin_c0HatW_eq, powOmega2, ← zpow_natCast t.σ, ← zpow_mul]
      push_cast
      ring_nf
    intro w
    rw [PWord.evalFin_comm, hn, hc0,
      commR_eq_one_iff.mpr ((Commute.refl t.σ).zpow_zpow _ _), one_smul]
  -- assemble
  rw [mpcHatW, hatFactors]
  simp only [PWord.prodList_cons, PWord.prodList_nil, foxD_mul, foxD_one, smul_zero, add_zero]
  rw [hf1, hf2, hf3, hf4, hf5, hw1, hw2, hw3, hw4]
  simp only [smul_add, smul_sub, smul_neg, hmerge, zero_add]
  rw [show ((-(k : ℕ) : ℤ) + (-(k : ℕ) : ℤ)) + ((k : ℕ) : ℤ) = (-(k : ℕ) : ℤ) by ring,
    show ((-(k : ℕ) : ℤ) + (-(k : ℕ) : ℤ)) + (((k : ℕ) : ℤ) + (-(pp : ℕ) : ℤ))
      = (-(pp + k : ℕ) : ℤ) by push_cast; ring,
    show ((-(k : ℕ) : ℤ) + (-(k : ℕ) : ℤ)) + (-(pp : ℕ) : ℤ)
      = (-(pp + k : ℕ) : ℤ) + (-(k : ℕ) : ℤ) by push_cast; ring,
    show ((-(k : ℕ) : ℤ) + (-(k : ℕ) : ℤ)) + (((k : ℕ) : ℤ) + ((k : ℕ) : ℤ)) = (0 : ℤ) by ring,
    zpow_zero, one_smul]
  -- the `x₀` column cancels over `ℤ`; the `x₁` column is a doubled term, killed by `hV₂`
  have h2z : ∀ w : V, (-2 : ℤ) • w = 0 := fun w => by
    rw [show (-2 : ℤ) = -(2 : ℤ) by norm_num, neg_zsmul, two_zsmul, hV₂, neg_zero]
  abel_nf
  exact h2z _

end MpcRows

/-! ## §5. The ramified pins: no loss

Five committed statements, re-derived through the parameterised layer and pinned.

The pins are **statement-identical** in a machine-checked sense, not by eyeball: each is followed
by an equation `@..._pin = @<committed name> := rfl`, which typechecks exactly when the two
declarations have the same type (proof irrelevance is definitional in Lean 4, so the *proofs*
never enter, only the statements).  A drift in any binder, implicitness or hypothesis order
would break it.

Together with the axiom prints of §7 this is the ticket's "no loss": every statement the
committed ramified chain makes is reachable from the δ-row layer with the same hypotheses and
the same axioms. -/

section RamPinsNpc

open GQ2.Dyadic.Words.Npc

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Pin 1**: the ramified noncompact-`N` wild row, through the layer.  Statement-identical to
`Npc.foxD_npc_ram`. -/
theorem foxDelta_npc_ram_pin (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e)
      = ((t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0))
        - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2) := by
  rw [foxDelta_npc (deltaRowRam t E E₂ hwild hτfpf hTodd) hV₂ hα e a,
    deltaRowRam_block t E E₂ hwild hτfpf hTodd a 2, zero_sub]
  abel

@[inherit_doc foxDelta_npc_ram_pin]
theorem foxDelta_npc_ram_pin_eq : @foxDelta_npc_ram_pin = @Npc.foxD_npc_ram := rfl

/-- **Pin 2**: every ramified column off `x₀`, `x₂` vanishes, through the layer.
Statement-identical to `Npc.foxDHom_npc_ram_column_eq_zero`.  Note what the layer does here: the
committed statement's `= 0` is the δ-row's own entry at the ramified reading, so the pin is
`foxDelta_npcHom_column` plus `deltaRowRam_block`, with no separate argument. -/
theorem foxDelta_npcHom_ram_column_pin (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v)
    (hτfpf : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) {g : Generator (2 + 2 * h)} (hg0 : g ≠ coreLetter h 0)
    (hg2 : g ≠ coreLetter h 2) (v : V) :
    foxDHom ⇑t E E₂ (npcW α r h e) (Pi.single g v) = 0 := by
  rw [foxDelta_npcHom_column (deltaRowRam t E E₂ hwild hτfpf hTodd) hV₂ hα e hg0 hg2 v,
    deltaRowRam_block t E E₂ hwild hτfpf hTodd _ 2]

@[inherit_doc foxDelta_npcHom_ram_column_pin]
theorem foxDelta_npcHom_ram_column_pin_eq :
    @foxDelta_npcHom_ram_column_pin = @Npc.foxDHom_npc_ram_column_eq_zero := rfl

end RamPinsNpc

section RamPinsMpc

open GQ2.Dyadic.Words.Mpc

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **Pin 3**: the ramified δ-letter row, through the layer.  Statement-identical to
`MProcyclic.foxD_dW_ram`, which is the single cross-lane citation of the `hτfpf`-carrying
δ-row and therefore the hinge the whole `section Factors` turned on. -/
theorem foxDelta_dW_ram_pin (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (i : Fin 3) :
    foxD ⇑t a E E₂ (dW h i) = -a (coreLetter h i) := by
  rw [foxDelta_dW (deltaRowRam t E E₂ hwild hτfpf hTodd) a i, FoxDeltaRow.deltaVal,
    deltaRowRam_block t E E₂ hwild hτfpf hTodd a i, zero_sub]

@[inherit_doc foxDelta_dW_ram_pin]
theorem foxDelta_dW_ram_pin_eq : @foxDelta_dW_ram_pin = @MProcyclic.foxD_dW_ram := rfl

/-- **Pin 4**: `E₀₁^pc`'s ramified row, through the layer.  Statement-identical to
`MProcyclic.foxD_e01W_ram`, the row freeze row 5 is about. -/
theorem foxDelta_e01W_ram_pin (hσ : a Generator.sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w) (aa bb : ℕ) :
    foxD ⇑t a E E₂ (e01W h aa bb)
      = -((((powOmega2 t.σ) ^ aa)⁻¹ * ((powOmega2 t.σ) ^ bb)⁻¹) • a (coreLetter h 1))
        - (((powOmega2 t.σ) ^ aa)⁻¹) • a (coreLetter h 1)
        - (((powOmega2 t.σ) ^ aa)⁻¹) • a (coreLetter h 0)
        - a (coreLetter h 0) := by
  rw [foxDelta_e01W (deltaRowRam t E E₂ hwild hτfpf hTodd) a hσ aa bb, FoxDeltaRow.deltaVal,
    FoxDeltaRow.deltaVal, deltaRowRam_block t E E₂ hwild hτfpf hTodd a 0,
    deltaRowRam_block t E E₂ hwild hτfpf hTodd a 1, zero_sub, zero_sub]
  simp only [smul_neg]
  abel

@[inherit_doc foxDelta_e01W_ram_pin]
theorem foxDelta_e01W_ram_pin_eq : @foxDelta_e01W_ram_pin = @MProcyclic.foxD_e01W_ram := rfl

/-- **Pin 5, the deep endpoint**: the hat copy's ramified row, through the layer.
Statement-identical to `MProcyclic.foxD_mpcHatW_ram`, the deepest declaration of the
ramified-only region and the one the ticket names. -/
theorem foxDelta_mpcHatW_ram_pin (hσ : a Generator.sigma = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w)
    (hτfpf : ∀ w : V, t.τ • w = w → w = 0) (hTodd : ∀ w : V, powOmega2 t.τ • w = w)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) (hV₂ : ∀ w : V, w + w = 0) :
    foxD ⇑t a E E₂ (mpcHatW α r pp η h) = 0 :=
  foxDelta_mpcHatW (deltaRowRam t E E₂ hwild hτfpf hTodd) a hσ hα r pp η hV₂

@[inherit_doc foxDelta_mpcHatW_ram_pin]
theorem foxDelta_mpcHatW_ram_pin_eq :
    @foxDelta_mpcHatW_ram_pin = @MProcyclic.foxD_mpcHatW_ram := rfl

end RamPinsMpc

/-! ## §6. The unramified instantiation

The other reading of the same theorems.  The first of these is a sixth pin (the committed
unramified noncompact-`N` row, showing the parameterisation is genuinely two-sided and not a
ramified layer with a hole); the rest are the procyclic-`M` factor rows at the unramified δ-row,
ending with the one the tree could not state.

`GQ2/Dyadic/Instances/MpcUnramifiedBranch.lean` currently proves the shallow three by hand.
Those are now corollaries of §4 and this section subsumes them, but that file is downstream of
`Certificates/` and rewiring it is a separate ticket, deliberately out of this wave's scope. -/

section UnramPinNpc

open GQ2.Dyadic.Words.Npc

variable {h α r : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

/-- **Pin 6**: the *unramified* noncompact-`N` wild row, through the same layer.
Statement-identical to `Npc.foxD_npc_unram`.

This pin is the evidence that `foxDelta_npc` is a parameterisation and not a ramified statement
in disguise: one theorem, two readings, both committed statements recovered on the nose. -/
theorem foxDelta_npc_unram_pin (hV₂ : ∀ v : V, v + v = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v) (hτ : ∀ v : V, t.τ • v = v)
    (hα : 1 ≤ α) (e : EtaData) (a : Generator (2 + 2 * h) → V) :
    foxD ⇑t a E E₂ (npcW α r h e)
      = ((t.σ ^ E e.toZhat)⁻¹ • a (coreLetter h 0) - a (coreLetter h 0))
        + (a .tau + (a (coreLetter h 2) - (t.σ ^ ((2 : ℤ) ^ r))⁻¹ • a (coreLetter h 2))) := by
  rw [foxDelta_npc (deltaRowUnram t E E₂ hV₂ hwild hτ) hV₂ hα e a,
    deltaRowUnram_block t E E₂ hV₂ hwild hτ a 2]
  abel

@[inherit_doc foxDelta_npc_unram_pin]
theorem foxDelta_npc_unram_pin_eq : @foxDelta_npc_unram_pin = @Npc.foxD_npc_unram := rfl

end UnramPinNpc

section UnramMpc

open GQ2.Dyadic.Words.Mpc

variable {h : ℕ} {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2 + 2 * h) C) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
  (a : Generator (2 + 2 * h) → V)

/-- **The unramified δ-letter row**: `D(δ_i) = a(τ)`, the same entry for every `i`.

The row the origin note asks for, read off the layer rather than re-derived.  It is *not* the
ramified row `−a(x_i)` with a hypothesis swapped: the entry no longer depends on `i` at all, and
it lands on a column (`τ`) that the ramified row does not touch.  That is what "the δ-rows are
genuinely different statements" means. -/
theorem foxDelta_dW_unram (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (i : Fin 3) : foxD ⇑t a E E₂ (dW h i) = a .tau := by
  rw [foxDelta_dW (deltaRowUnram t E E₂ hV₂ hwild hτ) a i, FoxDeltaRow.deltaVal,
    deltaRowUnram_block t E E₂ hV₂ hwild hτ a i]
  abel

/-- `D(Â) = a(τ)` at the unramified reading.  The layer gives `−a(τ)` with no characteristic
hypothesis; `hV₂` is spent only on the sign. -/
theorem foxDelta_aHatW_unram (hσ : a Generator.sigma = 0) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (s' mm : ℕ) : foxD ⇑t a E E₂ (aHatW h s' mm) = a .tau := by
  rw [foxDelta_aHatW (deltaRowUnram t E E₂ hV₂ hwild hτ) a hσ s' mm, FoxDeltaRow.deltaVal,
    deltaRowUnram_block t E E₂ hV₂ hwild hτ a 0, add_sub_cancel_left, neg_eq_self hV₂]

/-- `D(B̂) = a(τ)` at the unramified reading, exactly and with no characteristic hypothesis. -/
theorem foxDelta_bHatW_unram (hσ : a Generator.sigma = 0) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (pp : ℕ) : foxD ⇑t a E E₂ (bHatW h pp) = a .tau := by
  rw [foxDelta_bHatW (deltaRowUnram t E E₂ hV₂ hwild hτ) a hσ pp, FoxDeltaRow.deltaVal,
    deltaRowUnram_block t E E₂ hV₂ hwild hτ a 1, add_sub_cancel_left]

/-- **`D(E₀₁^pc) = 0` at the unramified reading.**  All four `δ`-occurrences contribute the same
`a(τ)`, every weight is a power of `S₂` and acts trivially on a simple unramified coefficient,
and four copies die over `F₂`.  The ramified twin `MProcyclic.foxD_e01W_ram` is *nonzero*; both
are the one row of §4 read at the two δ-rows. -/
theorem foxDelta_e01W_unram (hσ : a Generator.sigma = 0) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    (hS₂ : ∀ w : V, powOmega2 t.σ • w = w) (aa bb : ℕ) :
    foxD ⇑t a E E₂ (e01W h aa bb) = 0 := by
  have hU : ∀ (j : ℕ) (w : V), (((powOmega2 t.σ) ^ j)⁻¹ : C) • w = w := fun j w =>
    mem_trivAct.mp (inv_mem (pow_mem (mem_trivAct.mpr hS₂) j)) w
  have h4 : ∀ w : V, w + w + w + w = 0 := fun w => by rw [hV₂, zero_add, hV₂]
  rw [foxDelta_e01W (deltaRowUnram t E E₂ hV₂ hwild hτ) a hσ aa bb, FoxDeltaRow.deltaVal,
    FoxDeltaRow.deltaVal, deltaRowUnram_block t E E₂ hV₂ hwild hτ a 0,
    deltaRowUnram_block t E E₂ hV₂ hwild hτ a 1, add_sub_cancel_left, add_sub_cancel_left,
    mul_smul, hU, hU, hU]
  exact h4 _

/-- **The previously unreachable theorem: `D(R̂^pc) = 0` at the unramified reading.**

The hat copy has zero first Fox derivative at `σ`-free offsets on an *unramified* simple module
too, at every `(α, r, p)` with `α ≥ 1` and every `η̂` display.  No file in the tree could state
this before: `MProcyclic.foxD_mpcHatW_ram` is the only version and it sits inside
`include hσ hwild hτfpf hTodd`, whose `hτfpf` is false at unramified parameters, while
`Instances/MpcUnramifiedBranch.lean` redid only the shallow rows by hand and stopped short of the
hat copy.

It costs one line here, and that is the point of the wave: the hat row never needed the
ramification hypothesis, it needed the δ-row.  Note also that no `hS₂` appears, unlike the
unramified `E₀₁^pc` row above: the assembled statement is exact at every `σ`-action. -/
theorem foxDelta_mpcHatW_unram (hσ : a Generator.sigma = 0) (hV₂ : ∀ w : V, w + w = 0)
    (hwild : ∀ (i : Fin (2 + 2 * h + 1)) (w : V), t.x i • w = w) (hτ : ∀ w : V, t.τ • w = w)
    {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    foxD ⇑t a E E₂ (mpcHatW α r pp η h) = 0 :=
  foxDelta_mpcHatW (deltaRowUnram t E E₂ hV₂ hwild hτ) a hσ hα r pp η hV₂

end UnramMpc

/-! ## §7. Axiom pins

`#print axioms` on every public declaration of this file, in source order.  The layer is a
restatement of committed material, so the standard requirement applies: every print must be a
subset of the standard three, `[propext, Classical.choice, Quot.sound]`, and no axiom of the
dyadic census may appear.  It is not merely a subset of what the committed originals print, it
is exactly the standard set or less, matching `NpcFox.lean`'s and `MpcFox.lean`'s own audited
states.  Zero `sorryAx`, zero `Lean.ofReduceBool` (no `native_decide`, and no `decide` at all in
this file).  The census stays at eleven. -/

#print axioms GQ2.Dyadic.Certificates.FoxDelta.powOmega2_trivAct_of_trivial_mul
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.mk
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.wild
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.block
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.foxD_block
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.trivAct_block
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.trivAct_coreLetter
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.toddMem
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.todd
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.trivAct_delta
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.deltaVal
#print axioms GQ2.Dyadic.Certificates.FoxDelta.FoxDeltaRow.foxD_delta
#print axioms GQ2.Dyadic.Certificates.FoxDelta.deltaRowRam
#print axioms GQ2.Dyadic.Certificates.FoxDelta.deltaRowUnram
#print axioms GQ2.Dyadic.Certificates.FoxDelta.deltaRowRam_block
#print axioms GQ2.Dyadic.Certificates.FoxDelta.deltaRowUnram_block
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npc
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcHom_column
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcHom_handleU_column
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcHom_handleV_column
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcW_eq_uncorrected
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_dBlockW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_dW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_trivAct_dW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_aHatW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_bHatW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_e01W
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_mpcHatW
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npc_ram_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npc_ram_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcHom_ram_column_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npcHom_ram_column_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_dW_ram_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_dW_ram_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_e01W_ram_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_e01W_ram_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_mpcHatW_ram_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_mpcHatW_ram_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npc_unram_pin
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_npc_unram_pin_eq
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_dW_unram
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_aHatW_unram
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_bHatW_unram
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_e01W_unram
#print axioms GQ2.Dyadic.Certificates.FoxDelta.foxDelta_mpcHatW_unram

end GQ2.Dyadic.Certificates.FoxDelta
