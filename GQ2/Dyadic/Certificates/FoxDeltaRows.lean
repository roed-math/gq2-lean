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
below carries the row **as data**, a free vector `block : Fin 3 → V` together with the two
facts the downstream layer actually consumes (the Fox value and the trivial action of the
block), so the factor rows are stated once, for an arbitrary δ-row, and the two readings are
two terms of the structure rather than two copies of the chain.

## Why the row and not the projector

The parameter is deliberately the **row value**, not an `AddMonoid.End V`.  Every consumer below
is linear in the row and never inspects it; taking the value keeps the layer free of any
commitment to the projector's shape, and lets a future third reading (a genuinely partial `P`)
instantiate the same theorems.  The two instances supplied here do have `block i = P (a(x_i) +
a(τ))`, which is recorded as `FoxDeltaRow.unram_block` / `FoxDeltaRow.ram_block`.

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

0. Notation and the two micro-lemmas the layer needs.
1. `FoxDeltaRow`: the structure, and everything derived from it (`todd`, the δ-letter row).
2. The two instances: `FoxDeltaRow.ram` and `FoxDeltaRow.unram`.
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

`hTodd` is not a field either.  It is `FoxDeltaRow.todd`, a theorem. -/
structure FoxDeltaRow (a : Generator (2 + 2 * h) → V) where
  /-- The uniform wild hypothesis: the wild letters `x_i` act trivially on `V`. -/
  wild : ∀ (i : Fin (2 + 2 * h + 1)) (v : V), t.x i • v = v
  /-- The row: the first-order value of the `ω₂`-block `(x_iτ)^{ω₂}` at the offset `a`. -/
  block : Fin 3 → V
  /-- The `ω₂`-block's Fox derivative is the row. -/
  foxD_block : ∀ i : Fin 3, foxD ⇑t a E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) = block i
  /-- The `ω₂`-block acts trivially.  Uniform in the reading, and the field that replaces
  `hTodd` everywhere downstream. -/
  trivAct_block : ∀ i : Fin 3, PWord.evalFin ⇑t E E₂
    (PWord.omega2Pow (PWord.prodList [.gen (coreLetter h i), .gen .tau])) ∈ trivAct C V

namespace FoxDeltaRow

variable {t E E₂} {a : Generator (2 + 2 * h) → V} (dr : FoxDeltaRow t E E₂ a)

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

/-- **The δ-letter row: `D(δ_i) = block i − a(x_i)`.**

The statement the origin note calls "the δ-row".  At `block i = a(x_i) + a(τ)` (unramified) it
is `MCompact.foxD_deltaC_unram`'s `a(τ)`; at `block i = 0` (ramified) it is
`MCompact.foxD_deltaC_ram`'s `−a(x_i)`; here it is one theorem. -/
theorem foxD_delta (i : Fin 3) :
    foxD ⇑t a E E₂ (Words.MCompact.deltaC h i) = dr.block i - a (coreLetter h i) := by
  rw [Words.MCompact.deltaC, MCompact.foxD_prodList_pair, dr.foxD_block i,
    mem_trivAct.mp (dr.trivAct_block i), foxD_inv, PWord.evalFin_gen, foxD_gen,
    mem_trivAct.mp (inv_mem (dr.trivAct_coreLetter i))]
  abel

end FoxDeltaRow

end Row
