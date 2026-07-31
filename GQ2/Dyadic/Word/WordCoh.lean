/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Eval
public import GQ2.Cohomology
public import GQ2.Roe.DRWordCoh

@[expose] public section

/-!
# Dyadic campaign, layer F2 (cohomology): rank-generic relator obstructions

**Ticket MC-OB** of the dyadic campaign, closing the infra gap recorded in the MC2 outcomes log
(2026-07-29, item (v)): *"`DRWordCoh`'s `relZ`/`obsH2` layer is hard-wired to `drWord`/`Fin 3` —
a relator-generic `obsH2` port is a separate ticket, needed before MC5/branch-word cohomology."*

This file is that port.  Where `GQ2/Roe/DRWordCoh.lean` fixes one word (`drWord`) on one alphabet
(`Fin 3`) inside one group (`D_R`), everything here is stated for

* an **arbitrary alphabet** `X` (in particular `Generator n` of `GQ2/Dyadic/Parameters.lean`,
  so every rank `n` at once — that is the "rank-generic" of the ticket name),
* an **arbitrary relator word** `w : PWord X` of the F2 syntax
  (`GQ2/Dyadic/Word/Syntax.lean`), evaluated by the F2 integer-exponent denotation
  `PWord.evalZ` (`GQ2/Dyadic/Word/Eval.lean`),
* an **arbitrary marking** `μ : X → G` — equivalently a `Marking n G` — of an arbitrary
  profinite group,
* and an **arbitrary finite family of relators** `R : ρ → PWord X`, so that the one-relator
  `D_R` shape and the two-relator `Γ_A` shape are both instances.

## What a consumer gets (MC5's `MarkedCoreCertificate`, the branch-word lanes)

The three entry points, in the order a consumer meets them.

1. **`relZ W μ c : ZMod 2`** — the *relator obstruction at a finite level*.  Given a natural
   word `W` (see `NatWord`, which carries the relator and its exponent resolvers), a
   `ZMod 2`-valued 2-cocycle `c` on a group `L` and a marking `μ : X → L`, lift each letter to
   the central extension `CentExt c` with **zero fibre** and read off the fibre coordinate of the
   relator.  This is the number a Gram-matrix computation actually evaluates.  Its laws:
   `relZ_comap` (level change), `relZ_add` (additivity in `c`), `relZ_zero` (the split cocycle),
   `relZ_coboundary` (a coboundary sees only the base relator value).
   Multi-relator form: `relZFam R μ c : ρ → ZMod 2`, with the same four laws pointwise.

2. **`obsH2 htriv W μ hW : H2 G (ZMod 2) →+ ZMod 2`** — the *`H²` obstruction class* of a
   marking against a relator, and `obsH2_injective`, the `#H² ≤ 2` half.  This is the generic
   analogue of `GQ2.obsH2_DR`.  Beyond the marking `μ` and the word `W` it needs:
   * `htriv` — the `G`-action on `ZMod 2` is trivial (as everywhere in this development);
   * `hW : MarkedRelator` — the word lies in the Frattini subgroup (`NatWord.IsFrattini`) *and*
     dies at the marking (`holds`).  `IsFrattini` has a `Decidable` instance, so for a concrete
     word on a `Fintype` alphabet it falls to kernel `decide` — at computable exponent resolvers,
     which `isFrattini_ofPWord_of_parity` supplies from the honest (noncomputable) ones;
   * `hpres : PresentedBy` — required by `obsH2_injective`, not by `obsH2` itself: the universal
     property of the marking, saying that every marking of a pro-`2` group killing the relator
     extends to a continuous hom out of `G`, and that homs out of `G` are determined by the
     marking.  This is the *only* place the presentation enters, and it is threaded as an
     explicit hypothesis bundle rather than an axiom or a typeclass — MC2's documented
     general-`K` hypothesis-threading pattern.

   The form the Demushkin lane actually consumes is the corollary `card_H2_le_two`:
   `#H²(G, 𝔽₂) ≤ 2`.  Paired with a nonzero cup value from MC2's Gram (through (3) below) it
   pins `#H² = 2`, the Demushkin condition behind MC5's `MarkedCoreCertificate`.

3. **`obsH2_eq_of_factor`** — the bridge a Gram computation consumes: for a continuous 2-cocycle
   `φ` that factors through a *finite* quotient `ρ : G →* L` as `φ (g, h) = c.κ (ρ g) (ρ h)`,
   the class of `φ` has obstruction exactly `relZ W (ρ ∘ μ) c`.  Together with (1) this
   reduces an `H²` question to a finite computation in `CentExt c`.

**Division of labour with MC2.**  This file *packages*; it does not re-prove.  The mathematical
content of a marked-core cup computation — the cup-cocycle layer `IsCupCocycle`, the mod-`4`
`diagCoeff` rule and the `α`-independent cup Gram of `GQ2/Dyadic/MarkedCore/Cores.lean` §6 —
stays where MC2 put it.  In particular the cup Gram is **not** `decide`-able at `2^α`: MC2's
exponent/normal-form lemma is the asset that computes it, and this file's job is only to say
*which* number a cup cocycle must be fed to, namely `relZ`.

## Deduplication

The generic central-extension algebra (`TwoCocycle`, `CentExt`, `FiberProd`, `zeroCocycle`,
`coboundaryCocycle`, `Psi`, `TwoCocycle.comap`/`projExt`, `exists_openNormalSubgroup_factor_two`)
exists twice already in the repository:

* `GQ2/WordCoh2.lean`, namespace `GQ2.WordCoh2` — the original, in a **non-`module`** file, and
  therefore not importable here at all (plan §3 A5: a `module` file may not import a plain-import
  file).  *That impossibility is the entire reason this ticket exists.*
* `GQ2/Roe/DRWordCoh.lean`, namespace `GQ2.DRCoh` — a verbatim re-derivation, `module`-style,
  made for exactly the same reason.

`## The central-extension algebra` below is the third copy, in the fresh namespace
`GQ2.Dyadic.WordCoh`, so that the dyadic word layer does not inherit the `ℚ₂` `D_R` vocabulary
through its own definitions.  `GQ2.Roe.DRWordCoh` *is* imported, but only so that
`## Regression pins against `DRWordCoh`` can state that the `drWord`/`Fin 3` instantiation of this
file reproduces the `ℚ₂` values; nothing in §§1–5 depends on it.  `ofDRCoh` translates a
`GQ2.DRCoh.TwoCocycle` into the local one (the two structures have identical fields, so the
translation is definitional and the pins are `rfl` up to `zpow_natCast`).

Name-by-name, the local re-derivations shadow: `GQ2.WordCoh2.TwoCocycle` / `GQ2.DRCoh.TwoCocycle`,
`.CentExt`, `.FiberProd`, `.zeroCocycle`, `.coboundaryCocycle`, `.Psi`, `.fibHom0`,
`.TwoCocycle.comap`, `.projExt`, `.exists_openNormalSubgroup_factor_two`.  The relator layer
shadows `GQ2.drLift`/`drRelZ`/`DRLevelFactor`/`obsFun_DR`/`obs_DR`/`obsH2_DR` under the
un-prefixed names `lift`/`relZ`/`LevelFactor`/`obsFun`/`obs`/`obsH2`, and `GQ2.WordCoh2.relZPair`
under `relZFam`.

## Verification record (MC-OB)

`lake build GQ2.Dyadic.Word.WordCoh` is green with **no warnings**.  The file contains no `sorry`,
no `axiom`, and no `native_decide`; its single `decide` (`isFrattini_drNatWord`) is a kernel
decision over the `2³` markings of `Multiplicative (ZMod 2)`.  145 declarations.

Every headline prints **std-3** — `[propext, Classical.choice, Quot.sound]` — so the file adds
nothing to the census:

* relator layer: `relZ`, `relZ_base`, `relZ_comap`, `relZ_add`, `relZ_zero`, `relZ_coboundary`,
  `relZFam_add`, `relZFam_coboundary`;
* profinite layer: `exists_openNormalSubgroup_factor_two`, `exists_twoCocycle_factor`,
  `LevelFactor.obs_congr`, `isProP_CentExt`;
* `H²` layer: `obs`, `obs_B2_eq_zero`, `obs_ker_le`, `obsH2`, `obsH2_injective`,
  `finite_H2`, `card_H2_le_two`, `obsH2_eq_of_factor`;
* Frattini checkability: `evalZ_congr_of_parity`, `isFrattini_ofPWord_of_parity`;
* `Marking` interface: `Marking.relZ_map`;
* pins 1–8: `evalZ_drWordP`, `ofPWord_drWordP`, `relZ_ofDRCoh`, `relZ_drNatWord_eq_drRelZ`,
  `relZ_ofPWord_drWordP_eq_drRelZ`, `relZ_base_drNatWord`, `isFrattini_drNatWord`,
  `markedRelator_DR`, `presentedBy_DR`, `obsFun_eq_obsFun_DR`, `obsH2_eq_obsH2_DR`,
  `obsH2_DR_injective_via_generic`.

`PresentedBy` and `MarkedRelator` are ordinary structures threaded at every use, never axioms and
never instances, so no consumer can acquire them silently.

## Implementation notes

All three in-repo imports (`GQ2.Dyadic.Word.Eval`, `GQ2.Cohomology`, `GQ2.Roe.DRWordCoh`) are
`module`-style, so this file is `module`-style too and the one-directional rule of plan §3 A5 is
satisfied.  `GQ2/WordCoh2.lean` is deliberately *not* among them.

The relator layer is built on `PWord.evalZ` — the *integer-exponent* denotation — rather than on
the profinite `PWord.eval`.  This is what makes the whole file topology-free below §4: `evalZ`
needs only `[Group L]`, so it evaluates in `CentExt c`, in `FiberProd c₁ c₂` and in
`Multiplicative (ZMod 2)` without any of those having to be given a topological group structure,
and its naturality `PWord.map_evalZ` holds for an arbitrary `MonoidHomClass` — exactly the four
homs (`CentExt.proj`, `projExt`, the `FiberProd` projections, `fibHom0`) the `D_R` proofs push the
relator through.  `evalZ_eq_one_of_eval` bridges back to the profinite denotation.
-/

namespace GQ2.Dyadic.WordCoh

/-! ## The central-extension algebra

Re-derivation of the generic-in-`L` declarations of the non-`module` `GQ2/WordCoh2.lean`, in the
fresh namespace `GQ2.Dyadic.WordCoh`; see `## Deduplication` in the module docstring for why the
third copy exists and which names it shadows. -/

variable {L : Type*} [Group L]

/-- A `ZMod 2`-valued 2-cocycle on `L`, normalized at `(1,1)`.

Dedup: `GQ2.WordCoh2.TwoCocycle` (non-`module`), `GQ2.DRCoh.TwoCocycle` (`module`); this copy is
the one the dyadic word layer is stated over.  `ofDRCoh` converts. -/
structure TwoCocycle (L : Type*) [Group L] where
  /-- The underlying 2-cochain. -/
  κ : L → L → ZMod 2
  /-- Normalization at the identity. -/
  norm : κ 1 1 = 0
  /-- The 2-cocycle identity (trivial coefficients). -/
  cocyc : ∀ a b c : L, κ a b + κ (a * b) c = κ a (b * c) + κ b c

namespace TwoCocycle

variable (c : TwoCocycle L)

theorem κ_one_left (l : L) : c.κ 1 l = 0 := by simpa [c.norm] using c.cocyc 1 1 l

theorem κ_one_right (l : L) : c.κ l 1 = 0 := by simpa [c.norm] using c.cocyc l 1 1

theorem κ_inv (l : L) : c.κ l l⁻¹ = c.κ l⁻¹ l := by
  simpa [c.κ_one_left, c.κ_one_right] using c.cocyc l l⁻¹ l

end TwoCocycle

/-- Two `TwoCocycle`s with equal cochain are equal. -/
theorem TwoCocycle.ext' {c d : TwoCocycle L} (h : c.κ = d.κ) : c = d := by
  cases c; cases d; subst h; rfl

/-- The central extension `L ×_κ ZMod 2`: carrier `L × ZMod 2`, product
`(l, z) · (l', z') = (l·l', z + z' + κ l l')`.

Dedup: `GQ2.WordCoh2.CentExt`, `GQ2.DRCoh.CentExt`. -/
def CentExt (_c : TwoCocycle L) : Type _ := L × ZMod 2

namespace CentExt

variable {c : TwoCocycle L}

/-- Base coordinate. -/
def base (p : CentExt c) : L := p.1
/-- Fibre coordinate. -/
def fib (p : CentExt c) : ZMod 2 := p.2

@[ext] theorem ext {p q : CentExt c} (h1 : p.base = q.base) (h2 : p.fib = q.fib) : p = q :=
  Prod.ext h1 h2

instance : Group (CentExt c) where
  mul p q := (p.1 * q.1, p.2 + q.2 + c.κ p.1 q.1)
  one := (1, 0)
  inv p := (p.1⁻¹, p.2 + c.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply Prod.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2 + q.2 + c.κ p.1 q.1 + r.2 + c.κ (p.1 * q.1) r.1
        = p.2 + (q.2 + r.2 + c.κ q.1 r.1) + c.κ p.1 (q.1 * r.1)
      linear_combination c.cocyc p.1 q.1 r.1
  one_mul p := by
    apply Prod.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2 + c.κ 1 p.1 = p.2
      rw [c.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply Prod.ext
    · exact mul_one p.1
    · show p.2 + 0 + c.κ p.1 1 = p.2
      rw [c.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply Prod.ext
    · exact inv_mul_cancel p.1
    · show p.2 + c.κ p.1 p.1⁻¹ + p.2 + c.κ p.1⁻¹ p.1 = 0
      rw [c.κ_inv]
      exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] theorem mul_base (p q : CentExt c) : (p * q).base = p.base * q.base := rfl
@[simp] theorem mul_fib (p q : CentExt c) : (p * q).fib = p.fib + q.fib + c.κ p.base q.base := rfl
@[simp] theorem one_base : (1 : CentExt c).base = 1 := rfl
@[simp] theorem one_fib : (1 : CentExt c).fib = 0 := rfl

/-- The base projection `CentExt c →* L`. -/
def proj (c : TwoCocycle L) : CentExt c →* L where
  toFun := CentExt.base
  map_one' := rfl
  map_mul' := mul_base

@[simp] theorem proj_apply (c : TwoCocycle L) (p : CentExt c) : proj c p = p.base := rfl

/-- The central inclusion `ZMod 2 → CentExt c`. -/
def incl (c : TwoCocycle L) : ZMod 2 → CentExt c := fun z => (1, z)

@[simp] theorem incl_base (z : ZMod 2) : (incl c z).base = 1 := rfl
@[simp] theorem incl_fib (z : ZMod 2) : (incl c z).fib = z := rfl

theorem base_eq_one_iff (p : CentExt c) : p.base = 1 ↔ p = incl c p.fib :=
  ⟨fun h => CentExt.ext h rfl, fun h => by rw [h]; rfl⟩

@[simp] theorem incl_zero : incl c (0 : ZMod 2) = 1 := rfl

@[simp] theorem incl_mul_fib (z : ZMod 2) (p : CentExt c) : (incl c z * p).fib = z + p.fib := by
  show z + p.fib + c.κ 1 p.base = z + p.fib
  rw [c.κ_one_left, add_zero]

instance : TopologicalSpace (CentExt c) := ⊥
instance : DiscreteTopology (CentExt c) := ⟨rfl⟩
instance [Finite L] : Finite (CentExt c) := inferInstanceAs (Finite (L × ZMod 2))

end CentExt

/-! ### Level change: pulling a cocycle back along a group hom -/

section LevelChange

variable {L L' : Type*} [Group L] [Group L']

/-- Pull back a 2-cocycle along `φ : L' →* L`.  Dedup: `GQ2.DRCoh.TwoCocycle.comap`. -/
def TwoCocycle.comap (c : TwoCocycle L) (φ : L' →* L) : TwoCocycle L' where
  κ a b := c.κ (φ a) (φ b)
  norm := by simp only [map_one]; exact c.norm
  cocyc a b d := by simp only [map_mul]; exact c.cocyc (φ a) (φ b) (φ d)

@[simp] theorem TwoCocycle.comap_κ (c : TwoCocycle L) (φ : L' →* L) (a b : L') :
    (c.comap φ).κ a b = c.κ (φ a) (φ b) := rfl

/-- The base hom `φ` lifts to `CentExt (c.comap φ) →* CentExt c`.  Dedup: `GQ2.DRCoh.projExt`. -/
def projExt (c : TwoCocycle L) (φ : L' →* L) : CentExt (c.comap φ) →* CentExt c where
  toFun p := ((φ p.base, p.fib) : CentExt c)
  map_one' := CentExt.ext (map_one φ) rfl
  map_mul' p q := CentExt.ext (map_mul φ p.base q.base) rfl

@[simp] theorem projExt_fib (c : TwoCocycle L) (φ : L' →* L) (p : CentExt (c.comap φ)) :
    (projExt c φ p).fib = p.fib := rfl

@[simp] theorem projExt_base (c : TwoCocycle L) (φ : L' →* L) (p : CentExt (c.comap φ)) :
    (projExt c φ p).base = φ p.base := rfl

end LevelChange

/-! ### Additivity infrastructure: sum cocycle and fibre product -/

section Additivity

variable {L : Type*} [Group L]

/-- Pointwise sum of 2-cocycles. -/
instance : Add (TwoCocycle L) where
  add c₁ c₂ :=
    { κ := fun a b => c₁.κ a b + c₂.κ a b
      norm := by rw [c₁.norm, c₂.norm, add_zero]
      cocyc := fun a b d => by
        have h1 := c₁.cocyc a b d; have h2 := c₂.cocyc a b d; linear_combination h1 + h2 }

@[simp] theorem TwoCocycle.add_κ (c₁ c₂ : TwoCocycle L) (a b : L) :
    (c₁ + c₂).κ a b = c₁.κ a b + c₂.κ a b := rfl

/-- The fibre product `CentExt c₁ ×_L CentExt c₂`.  Dedup: `GQ2.DRCoh.FiberProd`. -/
def FiberProd (_c₁ _c₂ : TwoCocycle L) : Type _ := L × ZMod 2 × ZMod 2

namespace FiberProd

variable {c₁ c₂ : TwoCocycle L}

/-- Base coordinate. -/
def base (p : FiberProd c₁ c₂) : L := p.1
/-- First fibre coordinate. -/
def fibA (p : FiberProd c₁ c₂) : ZMod 2 := p.2.1
/-- Second fibre coordinate. -/
def fibB (p : FiberProd c₁ c₂) : ZMod 2 := p.2.2

@[ext] theorem ext {p q : FiberProd c₁ c₂} (h1 : p.base = q.base) (h2 : p.fibA = q.fibA)
    (h3 : p.fibB = q.fibB) : p = q :=
  Prod.ext h1 (Prod.ext h2 h3)

instance : Group (FiberProd c₁ c₂) where
  mul p q := (p.1 * q.1, p.2.1 + q.2.1 + c₁.κ p.1 q.1, p.2.2 + q.2.2 + c₂.κ p.1 q.1)
  one := (1, 0, 0)
  inv p := (p.1⁻¹, p.2.1 + c₁.κ p.1 p.1⁻¹, p.2.2 + c₂.κ p.1 p.1⁻¹)
  mul_assoc p q r := by
    apply FiberProd.ext
    · exact mul_assoc p.1 q.1 r.1
    · show p.2.1 + q.2.1 + c₁.κ p.1 q.1 + r.2.1 + c₁.κ (p.1 * q.1) r.1
        = p.2.1 + (q.2.1 + r.2.1 + c₁.κ q.1 r.1) + c₁.κ p.1 (q.1 * r.1)
      linear_combination c₁.cocyc p.1 q.1 r.1
    · show p.2.2 + q.2.2 + c₂.κ p.1 q.1 + r.2.2 + c₂.κ (p.1 * q.1) r.1
        = p.2.2 + (q.2.2 + r.2.2 + c₂.κ q.1 r.1) + c₂.κ p.1 (q.1 * r.1)
      linear_combination c₂.cocyc p.1 q.1 r.1
  one_mul p := by
    apply FiberProd.ext
    · exact one_mul p.1
    · show (0 : ZMod 2) + p.2.1 + c₁.κ 1 p.1 = p.2.1; rw [c₁.κ_one_left, add_zero, zero_add]
    · show (0 : ZMod 2) + p.2.2 + c₂.κ 1 p.1 = p.2.2; rw [c₂.κ_one_left, add_zero, zero_add]
  mul_one p := by
    apply FiberProd.ext
    · exact mul_one p.1
    · show p.2.1 + 0 + c₁.κ p.1 1 = p.2.1; rw [c₁.κ_one_right, add_zero, add_zero]
    · show p.2.2 + 0 + c₂.κ p.1 1 = p.2.2; rw [c₂.κ_one_right, add_zero, add_zero]
  inv_mul_cancel p := by
    apply FiberProd.ext
    · exact inv_mul_cancel p.1
    · show p.2.1 + c₁.κ p.1 p.1⁻¹ + p.2.1 + c₁.κ p.1⁻¹ p.1 = 0
      rw [c₁.κ_inv]; exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _
    · show p.2.2 + c₂.κ p.1 p.1⁻¹ + p.2.2 + c₂.κ p.1⁻¹ p.1 = 0
      rw [c₂.κ_inv]; exact (by decide : ∀ x y : ZMod 2, x + y + x + y = 0) _ _

@[simp] theorem mul_base (p q : FiberProd c₁ c₂) : (p * q).base = p.base * q.base := rfl

/-- Projection to the first central extension. -/
def pr1 : FiberProd c₁ c₂ →* CentExt c₁ where
  toFun p := ((p.base, p.fibA) : CentExt c₁)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection to the second central extension. -/
def pr2 : FiberProd c₁ c₂ →* CentExt c₂ where
  toFun p := ((p.base, p.fibB) : CentExt c₂)
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The fibre-sum hom to the sum extension. -/
def prSum : FiberProd c₁ c₂ →* CentExt (c₁ + c₂) where
  toFun p := ((p.base, p.fibA + p.fibB) : CentExt (c₁ + c₂))
  map_one' := CentExt.ext rfl (add_zero (0 : ZMod 2))
  map_mul' p q := CentExt.ext rfl <| by
    show (p.fibA + q.fibA + c₁.κ p.base q.base) + (p.fibB + q.fibB + c₂.κ p.base q.base)
        = (p.fibA + p.fibB) + (q.fibA + q.fibB) + (c₁.κ p.base q.base + c₂.κ p.base q.base)
    ring

@[simp] theorem pr1_fib (p : FiberProd c₁ c₂) : (pr1 p).fib = p.fibA := rfl
@[simp] theorem pr2_fib (p : FiberProd c₁ c₂) : (pr2 p).fib = p.fibB := rfl
@[simp] theorem prSum_fib (p : FiberProd c₁ c₂) : (prSum p).fib = p.fibA + p.fibB := rfl

instance [Finite L] : Finite (FiberProd c₁ c₂) := inferInstanceAs (Finite (L × ZMod 2 × ZMod 2))

end FiberProd

end Additivity

/-! ### The split and coboundary cocycles -/

section SplitCoboundary

variable {L : Type*} [Group L]

/-- The trivial (split) 2-cocycle `κ ≡ 0`.  Dedup: `GQ2.DRCoh.zeroCocycle`. -/
def zeroCocycle : TwoCocycle L where
  κ _ _ := 0
  norm := rfl
  cocyc _ _ _ := rfl

@[simp] theorem zeroCocycle_κ (a b : L) : (zeroCocycle : TwoCocycle L).κ a b = 0 := rfl

/-- The fibre projection `CentExt zeroCocycle →* Multiplicative 𝔽₂`. -/
def fibHom0 : CentExt (zeroCocycle : TwoCocycle L) →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd p.fib
  map_one' := rfl
  map_mul' p q := by
    show Multiplicative.ofAdd (p * q).fib = Multiplicative.ofAdd p.fib * Multiplicative.ofAdd q.fib
    rw [CentExt.mul_fib, zeroCocycle_κ, add_zero, ofAdd_add]

@[simp] theorem fibHom0_apply (p : CentExt (zeroCocycle : TwoCocycle L)) :
    fibHom0 p = Multiplicative.ofAdd p.fib := rfl

/-- The coboundary 2-cocycle `δ¹λ`.  Dedup: `GQ2.DRCoh.coboundaryCocycle`. -/
def coboundaryCocycle (lam : L → ZMod 2) (hlam1 : lam 1 = 0) : TwoCocycle L where
  κ a b := lam a + lam b + lam (a * b)
  norm := by simp [hlam1]
  cocyc a b c := by
    show lam a + lam b + lam (a * b) + (lam (a * b) + lam c + lam (a * b * c))
      = lam a + lam (b * c) + lam (a * (b * c)) + (lam b + lam c + lam (b * c))
    rw [mul_assoc a b c]
    abel_nf
    simp [CharTwo.two_eq_zero]

@[simp] theorem coboundaryCocycle_κ (lam : L → ZMod 2) (hlam1 : lam 1 = 0) (a b : L) :
    (coboundaryCocycle lam hlam1).κ a b = lam a + lam b + lam (a * b) := rfl

/-- The trivialization hom `Ψ_λ : (l, z) ↦ (l, z + λ l)`.  Dedup: `GQ2.DRCoh.Psi`. -/
def Psi (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    CentExt (coboundaryCocycle lam hlam1) →* CentExt (zeroCocycle : TwoCocycle L) where
  toFun p := ((p.base, p.fib + lam p.base) : CentExt (zeroCocycle : TwoCocycle L))
  map_one' := CentExt.ext rfl (by show (0 : ZMod 2) + lam 1 = 0; simp [hlam1])
  map_mul' p q := by
    refine CentExt.ext rfl ?_
    · show (p * q).fib + lam (p * q).base
          = (p.fib + lam p.base) + (q.fib + lam q.base)
            + (zeroCocycle : TwoCocycle L).κ p.base q.base
      rw [CentExt.mul_fib, CentExt.mul_base, zeroCocycle_κ, coboundaryCocycle_κ]
      abel_nf
      simp [CharTwo.two_eq_zero]

@[simp] theorem Psi_fib (lam : L → ZMod 2) (hlam1 : lam 1 = 0)
    (p : CentExt (coboundaryCocycle lam hlam1)) : (Psi lam hlam1 p).fib = p.fib + lam p.base := rfl

@[simp] theorem Psi_base (lam : L → ZMod 2) (hlam1 : lam 1 = 0)
    (p : CentExt (coboundaryCocycle lam hlam1)) : (Psi lam hlam1 p).base = p.base := rfl

end SplitCoboundary

/-! ### Factoring a continuous 2-variable map through a finite quotient -/

/-- **Uniform local constancy** (2-variable form), generic in the profinite group `G`: a
continuous map `G × G → M` into a discrete space is constant on `V`-cosets in both slots for one
open normal `V`.  Dedup: `GQ2.WordCoh2.exists_openNormalSubgroup_factor_two`,
`GQ2.DRCoh.exists_openNormalSubgroup_factor_two`. -/
theorem exists_openNormalSubgroup_factor_two
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {M : Type*} [TopologicalSpace M] [DiscreteTopology M]
    (f : G × G → M) (hf : Continuous f) :
    ∃ V : OpenNormalSubgroup G, ∀ x y : G, ∀ u ∈ V, ∀ v ∈ V, f (x * u, y * v) = f (x, y) := by
  have hbox : ∀ p : G × G, ∃ W : OpenNormalSubgroup G,
      ∀ u ∈ W, ∀ v ∈ W, f (p.1 * u, p.2 * v) = f p := by
    intro p
    have hop : IsOpen (f ⁻¹' {f p}) := (isOpen_discrete _).preimage hf
    obtain ⟨A, B, hA, hB, hpA, hpB, hAB⟩ := isOpen_prod_iff.mp hop p.1 p.2 rfl
    have hOA : IsOpen ((fun w => p.1 * w) ⁻¹' A) := hA.preimage (continuous_const.mul continuous_id)
    have hOB : IsOpen ((fun w => p.2 * w) ⁻¹' B) := hB.preimage (continuous_const.mul continuous_id)
    have h1A : (1 : G) ∈ (fun w => p.1 * w) ⁻¹' A := by simpa using hpA
    have h1B : (1 : G) ∈ (fun w => p.2 * w) ⁻¹' B := by simpa using hpB
    obtain ⟨WA, hWA⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOA h1A
    obtain ⟨WB, hWB⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOB h1B
    refine ⟨WA ⊓ WB, fun u hu v hv => ?_⟩
    have huA : p.1 * u ∈ A := hWA (SetLike.le_def.mp inf_le_left hu)
    have hvB : p.2 * v ∈ B := hWB (SetLike.le_def.mp inf_le_right hv)
    have hmem : (p.1 * u, p.2 * v) ∈ f ⁻¹' {f p} := hAB (Set.mk_mem_prod huA hvB)
    simpa using hmem
  choose W hW using hbox
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun p : G × G => (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)))
    (fun p => (((W p).toOpenSubgroup.isOpen.prod (W p).toOpenSubgroup.isOpen)).preimage
      (by fun_prop))
    (fun q _ => Set.mem_iUnion.mpr ⟨q, by
      rw [Set.mem_preimage, Set.mem_prod, inv_mul_cancel, inv_mul_cancel]
      exact ⟨one_mem _, one_mem _⟩⟩)
  have hne : t.Nonempty := by
    obtain ⟨i, hi, _⟩ := Set.mem_iUnion₂.mp (ht (Set.mem_univ ((1, 1) : G × G)))
    exact ⟨i, hi⟩
  refine ⟨t.inf' hne W, fun x y u hu v hv => ?_⟩
  have hxy : (x, y) ∈ ⋃ p ∈ t,
      (fun q : G × G => (p.1⁻¹ * q.1, p.2⁻¹ * q.2)) ⁻¹' (↑(W p) ×ˢ ↑(W p)) := ht (Set.mem_univ _)
  rw [Set.mem_iUnion₂] at hxy
  obtain ⟨p, hpt, hp⟩ := hxy
  rw [Set.mem_preimage, Set.mem_prod] at hp
  obtain ⟨hx, hy⟩ := hp
  have hVle : t.inf' hne W ≤ W p := Finset.inf'_le _ hpt
  have huWp : u ∈ W p := SetLike.le_def.mp hVle hu
  have hvWp : v ∈ W p := SetLike.le_def.mp hVle hv
  have hfxy : f (x, y) = f p := by
    have h := hW p (p.1⁻¹ * x) hx (p.2⁻¹ * y) hy
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  have hfxuyv : f (x * u, y * v) = f p := by
    have hxu : p.1⁻¹ * (x * u) ∈ W p := by rw [← mul_assoc]; exact mul_mem hx huWp
    have hyv : p.2⁻¹ * (y * v) ∈ W p := by rw [← mul_assoc]; exact mul_mem hy hvWp
    have h := hW p (p.1⁻¹ * (x * u)) hxu (p.2⁻¹ * (y * v)) hyv
    rwa [mul_inv_cancel_left, mul_inv_cancel_left] at h
  rw [hfxuyv, hfxy]

/-! ## Natural words

The relator layer below is stated over an **abstract natural word** rather than over `PWord`
directly.  The reason is that the campaign already carries relators in two shapes:

* reflected syntax — `w : PWord X` of `GQ2/Dyadic/Word/Syntax.lean`, evaluated by `PWord.evalZ`,
  with naturality `PWord.map_evalZ`;
* bare word *shapes* — `drWord s x y` (`GQ2/Roe/DRPresentation.lean`), and MC2's `mWord`,
  `nWord`, `handleWord`, `mRelWord`, `nRelWord` (`GQ2/Dyadic/MarkedCore/Cores.lean` §1), each a
  plain function of its letters with a hand-written naturality lemma `map_mWord`, `map_nWord`, ….

Both shapes are *exactly* a function `(X → G) → G` natural in `G`, and naturality is the *only*
property the obstruction proofs use: the relator has to be pushed through `CentExt.proj`,
`projExt`, the three `FiberProd` projections and `fibHom0`.  Bundling that is what lets this file
be written once and consumed by both the `PWord` branch-word lanes and MC2's existing core words —
`NatWord.ofPWord` for the former, `drNatWord`-style anonymous constructors (shape paired with its
`map_…` lemma) for the latter.

Universe note: `ev` quantifies over `G : Type`.  Every group the layer needs is there — finite
quotients `G ⧸ V`, `CentExt c`, `FiberProd c₁ c₂`, `Multiplicative (ZMod 2)` — and pinning the
universe keeps `IsFrattini`, whose test group is the `Type`-valued `Multiplicative (ZMod 2)`,
statable.  The central-extension algebra above stays `Type*`-generic. -/

/-- A **natural word** on the alphabet `X`: an evaluation of a relator at a marking, defined in
every group and commuting with every group hom.

This is the interface the relator obstruction consumes.  `NatWord.ofPWord` builds one from the
reflected syntax; `drNatWord` below is the template for a bare word shape — an anonymous
constructor pairing the shape with its naturality lemma. -/
structure NatWord (X : Type*) where
  /-- Evaluate the word at a marking of an arbitrary group. -/
  ev : ∀ {G : Type} [Group G], (X → G) → G
  /-- Naturality: the word commutes with every group homomorphism. -/
  nat : ∀ {G H : Type} [Group G] [Group H] (f : G →* H) (μ : X → G),
    f (ev μ) = ev fun k => f (μ k)

namespace NatWord

variable {X : Type*}

/-- Naturality for an arbitrary monoid-hom-like map (`MonoidHomClass`), obtained from the
`MonoidHom` field by coercion. -/
theorem nat' (W : NatWord X) {G H : Type} [Group G] [Group H] {F : Type*} [FunLike F G H]
    [MonoidHomClass F G H] (f : F) (μ : X → G) : f (W.ev μ) = W.ev fun k => f (μ k) :=
  W.nat (MonoidHomClass.toMonoidHom f) μ

/-- **Every word dies at the trivial marking.**  Unlike `IsFrattini` this needs no hypothesis: it
is naturality applied to the unique hom out of the trivial group. -/
theorem ev_one (W : NatWord X) {G : Type} [Group G] : W.ev (fun _ : X => (1 : G)) = 1 := by
  have h := W.nat (1 : PUnit →* G) (fun _ : X => (1 : PUnit))
  have h1 : W.ev (fun _ : X => (1 : PUnit)) = 1 := Subsingleton.elim _ _
  rw [h1, map_one] at h
  exact h.symm

/-- The natural word given by a reflected `PWord` under the integer-exponent denotation. -/
def ofPWord (w : PWord X) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) : NatWord X where
  ev := fun {_} _ μ => PWord.evalZ μ E E₂ w
  nat := fun f μ => PWord.map_evalZ f μ E E₂ w

@[simp] theorem ofPWord_ev (w : PWord X) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) {G : Type} [Group G]
    (μ : X → G) : (ofPWord w E E₂).ev μ = PWord.evalZ μ E E₂ w := rfl

/-! ### The Frattini condition -/

/-- **`W` lies in the Frattini subgroup**: it dies under *every* `𝔽₂`-marking.

Equivalently, the relator lies in `F² · [F, F]` — the standard requirement that a presentation be
*minimal* (no relator may consume a generator).  It is what makes the obstruction well defined on
coboundaries: `relZ_coboundary` and, through it, `obs_B2_eq_zero`.

`ev_one` is the special case of the trivial marking and holds unconditionally; the content here is
the *general* `𝔽₂`-marking, and it genuinely fails for a non-minimal word (e.g. `PWord.gen k`). -/
def IsFrattini (W : NatWord X) : Prop :=
  ∀ ν : X → Multiplicative (ZMod 2), W.ev ν = 1

instance (W : NatWord X) [Fintype X] [DecidableEq X]
    [DecidablePred fun ν : X → Multiplicative (ZMod 2) => W.ev ν = 1] :
    Decidable (IsFrattini W) :=
  inferInstanceAs (Decidable (∀ _, _))

/-- The Frattini condition for a reflected word, spelled out: it is a statement about a *finite*
group, so for a concrete word on a `Fintype` alphabet it is closed by kernel `decide`. -/
theorem isFrattini_ofPWord_iff (w : PWord X) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    IsFrattini (ofPWord w E E₂) ↔
      ∀ ν : X → Multiplicative (ZMod 2), PWord.evalZ ν E E₂ w = 1 := Iff.rfl

end NatWord

/-! ## The relator obstruction at a finite level

The rank-generic port of `GQ2.drLift` / `GQ2.drRelZ` and their four laws
(`GQ2/Roe/DRWordCoh.lean`, `drRelZ_base` / `drRelZ_comap` / `drRelZ_add` / `drRelZ_zero` /
`drRelZ_coboundary`).  Dedup: `GQ2.WordCoh2.relZPair` is the two-relator `Γ_A` version; `relZFam`
below is the `ρ`-indexed generalisation of both. -/

section RelZ

variable {X : Type*} {L : Type} [Group L]

/-- The **zero-fibre lift** of a marking into a central extension: each letter `μ k` is lifted to
`(μ k, 0)`.  Dedup: `GQ2.drLift` (`Fin 3`), `GQ2.centLift` (`Cores.lean` §6, one element). -/
def lift (μ : X → L) (c : TwoCocycle L) : X → CentExt c := fun k => ((μ k, 0) : CentExt c)

@[simp] theorem lift_base (μ : X → L) (c : TwoCocycle L) (k : X) : (lift μ c k).base = μ k := rfl

@[simp] theorem lift_fib (μ : X → L) (c : TwoCocycle L) (k : X) : (lift μ c k).fib = 0 := rfl

/-- The **relator obstruction** of a 2-cocycle `c` relative to the marking `μ`: the fibre
coordinate of the relator evaluated at the zero-fibre lift.

This is the number a Gram-matrix computation evaluates.  MC2's `IsCupCocycle` layer computes
exactly such fibres for the marked-core words (`mRelWord_centLift_fib`, `nRelWord_centLift_fib`);
this definition is the slot those values fill. -/
def relZ (W : NatWord X) (μ : X → L) (c : TwoCocycle L) : ZMod 2 := (W.ev (lift μ c)).fib

/-- The base of the lifted relator value is the base relator value: the obstruction really does
measure the *failure* of a relation that already holds downstairs. -/
theorem relZ_base (W : NatWord X) (μ : X → L) (c : TwoCocycle L) :
    (W.ev (lift μ c)).base = W.ev μ := by
  have h := W.nat (CentExt.proj c) (lift μ c)
  simpa only [CentExt.proj_apply, lift_base] using h

/-- If the relation holds at the marking, the lifted relator lies in the central `ZMod 2`. -/
theorem relZ_eq_iff (W : NatWord X) (μ : X → L) (c : TwoCocycle L) (hrel : W.ev μ = 1) :
    W.ev (lift μ c) = 1 ↔ relZ W μ c = 0 := by
  constructor
  · intro h; rw [relZ, h]; rfl
  · intro h
    refine CentExt.ext ?_ h
    rw [relZ_base, hrel, CentExt.one_base]

end RelZ

section RelZComap

variable {X : Type*} {L L' : Type} [Group L] [Group L']

/-- **Level-independence.**  Pulling `c` back along `φ` and pushing the marking forward by `φ`
give the same obstruction.  Port of `GQ2.drRelZ_comap`. -/
theorem relZ_comap (W : NatWord X) (μ : X → L') (c : TwoCocycle L) (φ : L' →* L) :
    relZ W (fun k => φ (μ k)) c = relZ W μ (c.comap φ) := by
  have h := W.nat (projExt c φ) (lift μ (c.comap φ))
  have hlift : (fun k => projExt c φ (lift μ (c.comap φ) k)) = lift (fun k => φ (μ k)) c := rfl
  rw [hlift] at h
  show (W.ev (lift (fun k => φ (μ k)) c)).fib = (W.ev (lift μ (c.comap φ))).fib
  rw [← h, projExt_fib]

end RelZComap

section RelZAdd

variable {X : Type*} {L : Type} [Group L]

/-- The fibre-product lift of a marking (both fibres zero). -/
def liftFP (μ : X → L) (c₁ c₂ : TwoCocycle L) : X → FiberProd c₁ c₂ :=
  fun k => ((μ k, 0, 0) : FiberProd c₁ c₂)

private theorem pr1_liftFP (μ : X → L) (c₁ c₂ : TwoCocycle L) :
    (fun k => FiberProd.pr1 (liftFP μ c₁ c₂ k)) = lift μ c₁ := rfl

private theorem pr2_liftFP (μ : X → L) (c₁ c₂ : TwoCocycle L) :
    (fun k => FiberProd.pr2 (liftFP μ c₁ c₂ k)) = lift μ c₂ := rfl

private theorem prSum_liftFP (μ : X → L) (c₁ c₂ : TwoCocycle L) :
    (fun k => FiberProd.prSum (liftFP μ c₁ c₂ k)) = lift μ (c₁ + c₂) := by
  funext k; exact CentExt.ext rfl (add_zero (0 : ZMod 2))

/-- **Additivity of the relator obstruction** in the cocycle.  Port of `GQ2.drRelZ_add`. -/
theorem relZ_add (W : NatWord X) (μ : X → L) (c₁ c₂ : TwoCocycle L) :
    relZ W μ (c₁ + c₂) = relZ W μ c₁ + relZ W μ c₂ := by
  have h1 := W.nat FiberProd.pr1 (liftFP μ c₁ c₂)
  have h2 := W.nat FiberProd.pr2 (liftFP μ c₁ c₂)
  have hs := W.nat FiberProd.prSum (liftFP μ c₁ c₂)
  rw [pr1_liftFP] at h1
  rw [pr2_liftFP] at h2
  rw [prSum_liftFP] at hs
  show (W.ev (lift μ (c₁ + c₂))).fib = (W.ev (lift μ c₁)).fib + (W.ev (lift μ c₂)).fib
  rw [← hs, ← h1, ← h2, FiberProd.prSum_fib, FiberProd.pr1_fib, FiberProd.pr2_fib]

end RelZAdd

section RelZCoboundary

variable {X : Type*} {L : Type} [Group L]

/-- **The obstruction of the split cocycle vanishes.**  Port of `GQ2.drRelZ_zero`; note that no
Frattini hypothesis is needed, because the zero-fibre lift of *any* marking maps to the trivial
marking of `Multiplicative (ZMod 2)` and `NatWord.ev_one` handles that unconditionally. -/
theorem relZ_zero (W : NatWord X) (μ : X → L) : relZ W μ (zeroCocycle : TwoCocycle L) = 0 := by
  have h := W.nat (fibHom0 (L := L)) (lift μ zeroCocycle)
  have hgen : (fun k => fibHom0 (lift μ (zeroCocycle : TwoCocycle L) k))
      = fun _ : X => (1 : Multiplicative (ZMod 2)) := rfl
  rw [hgen, W.ev_one] at h
  have hval : Multiplicative.ofAdd (relZ W μ (zeroCocycle : TwoCocycle L))
      = (1 : Multiplicative (ZMod 2)) := h
  simpa using Multiplicative.ofAdd.injective hval

/-- **The obstruction of a coboundary** is `lam` of the base relator value.  In particular it
vanishes when the marking satisfies the relation.  Port of `GQ2.drRelZ_coboundary`; this is where
the Frattini hypothesis is genuinely used, since here the induced `𝔽₂`-marking is
`k ↦ lam (μ k)`, an arbitrary one. -/
theorem relZ_coboundary (W : NatWord X) (hW : W.IsFrattini) (μ : X → L) (lam : L → ZMod 2)
    (hlam1 : lam 1 = 0) : relZ W μ (coboundaryCocycle lam hlam1) = lam (W.ev μ) := by
  set θ : CentExt (coboundaryCocycle lam hlam1) →* Multiplicative (ZMod 2) :=
    (fibHom0 (L := L)).comp (Psi lam hlam1) with hθ
  have h := W.nat θ (lift μ (coboundaryCocycle lam hlam1))
  have hgen : (fun k => θ (lift μ (coboundaryCocycle lam hlam1) k))
      = fun k => Multiplicative.ofAdd (lam (μ k)) := by
    funext k
    show Multiplicative.ofAdd ((Psi lam hlam1 (lift μ (coboundaryCocycle lam hlam1) k)).fib) = _
    rw [Psi_fib, lift_fib, lift_base, zero_add]
  rw [hgen, hW _] at h
  have hval : Multiplicative.ofAdd
      ((W.ev (lift μ (coboundaryCocycle lam hlam1))).fib + lam (W.ev μ))
      = (1 : Multiplicative (ZMod 2)) := by
    rw [← h]
    show _ = Multiplicative.ofAdd ((Psi lam hlam1 (W.ev (lift μ (coboundaryCocycle lam hlam1)))).fib)
    rw [Psi_fib, relZ_base]
  have hsum : relZ W μ (coboundaryCocycle lam hlam1) + lam (W.ev μ) = 0 :=
    Multiplicative.ofAdd.injective (hval.trans ofAdd_zero.symm)
  rw [eq_neg_of_add_eq_zero_left hsum, CharTwo.neg_eq]

end RelZCoboundary

/-! ### The multi-relator family

`D_R` has one relator, `Γ_A` has two (`GQ2.WordCoh2.relZPair`), and a branch word may have any
finite number; indexing by `ρ` covers all of them, and every law is pointwise. -/

section RelZFam

variable {X ρ : Type*} {L L' : Type} [Group L] [Group L']

/-- The obstruction vector of a **family** of relators. -/
def relZFam (R : ρ → NatWord X) (μ : X → L) (c : TwoCocycle L) : ρ → ZMod 2 :=
  fun r => relZ (R r) μ c

@[simp] theorem relZFam_apply (R : ρ → NatWord X) (μ : X → L) (c : TwoCocycle L) (r : ρ) :
    relZFam R μ c r = relZ (R r) μ c := rfl

/-- The family is `IsFrattini` when each member is. -/
def IsFrattiniFam (R : ρ → NatWord X) : Prop := ∀ r, (R r).IsFrattini

theorem relZFam_comap (R : ρ → NatWord X) (μ : X → L') (c : TwoCocycle L) (φ : L' →* L) :
    relZFam R (fun k => φ (μ k)) c = relZFam R μ (c.comap φ) :=
  funext fun r => relZ_comap (R r) μ c φ

theorem relZFam_add (R : ρ → NatWord X) (μ : X → L) (c₁ c₂ : TwoCocycle L) :
    relZFam R μ (c₁ + c₂) = relZFam R μ c₁ + relZFam R μ c₂ :=
  funext fun r => relZ_add (R r) μ c₁ c₂

theorem relZFam_zero (R : ρ → NatWord X) (μ : X → L) :
    relZFam R μ (zeroCocycle : TwoCocycle L) = 0 :=
  funext fun r => relZ_zero (R r) μ

theorem relZFam_coboundary (R : ρ → NatWord X) (hR : IsFrattiniFam R) (μ : X → L)
    (lam : L → ZMod 2) (hlam1 : lam 1 = 0) :
    relZFam R μ (coboundaryCocycle lam hlam1) = fun r => lam ((R r).ev μ) :=
  funext fun r => relZ_coboundary (R r) (hR r) μ lam hlam1

end RelZFam

/-! ## Factoring a continuous cochain through a finite quotient

Generic in the profinite group `G`: `GQ2.exists_twoCocycle_factor_DR` and
`GQ2.exists_oneCochain_factor_DR` with `D_R` replaced by an arbitrary profinite group. -/

section Factoring

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Every open normal subgroup of a profinite group has finite quotient. -/
instance quotient_finite_openNormal (V : OpenNormalSubgroup G) : Finite (G ⧸ V.toSubgroup) :=
  Subgroup.quotient_finite_of_isOpen V.toSubgroup V.isOpen'

/-- **Factoring a normalized continuous 2-cocycle** through a finite quotient. -/
theorem exists_twoCocycle_factor (κ : G × G → ZMod 2)
    (hκc : Continuous κ) (hκ1 : κ (1, 1) = 0)
    (hκcoc : ∀ a b c : G, κ (a, b) + κ (a * b, c) = κ (a, b * c) + κ (b, c)) :
    ∃ (V : OpenNormalSubgroup G) (c : TwoCocycle (G ⧸ V.toSubgroup)),
      ∀ x y : G,
        κ (x, y) = c.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y) := by
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two κ hκc
  refine ⟨V, ?_, ?_⟩
  · refine { κ := fun p q => Quotient.liftOn₂ p q (fun x y => κ (x, y)) ?_, norm := ?_, cocyc := ?_ }
    · intro x₁ y₁ x₂ y₂ hx hy
      have hxv : x₁⁻¹ * x₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hx
      have hyv : y₁⁻¹ * y₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hy
      have h := hV x₁ y₁ _ hxv _ hyv
      rw [mul_inv_cancel_left, mul_inv_cancel_left] at h
      exact h.symm
    · show κ (1, 1) = 0; exact hκ1
    · intro a b c
      induction a using QuotientGroup.induction_on with | H x =>
      induction b using QuotientGroup.induction_on with | H y =>
      induction c using QuotientGroup.induction_on with | H z =>
      show κ (x, y) + κ (x * y, z) = κ (x, y * z) + κ (y, z)
      exact hκcoc x y z
  · intro x y; rfl

/-- **Factoring a continuous 1-cochain** through a finite quotient. -/
theorem exists_oneCochain_factor (ψ : G → ZMod 2) (hψc : Continuous ψ) :
    ∃ (V : OpenNormalSubgroup G) (lam : G ⧸ V.toSubgroup → ZMod 2),
      ∀ x : G, ψ x = lam (QuotientGroup.mk' V.toSubgroup x) := by
  obtain ⟨V, hV⟩ := exists_openNormalSubgroup_factor_two (fun p => ψ p.1)
    (hψc.comp continuous_fst)
  refine ⟨V, fun p => Quotient.liftOn p (fun x => ψ x) ?_, ?_⟩
  · intro x₁ x₂ hx
    have hxv : x₁⁻¹ * x₂ ∈ V.toSubgroup := QuotientGroup.leftRel_apply.mp hx
    have h := hV x₁ x₁ _ hxv 1 (one_mem _)
    rw [mul_inv_cancel_left, mul_one] at h
    exact h.symm
  · intro x; rfl

end Factoring

/-! ## The level-independent obstruction

Port of `GQ2.DRLevelFactor` / `.obs` / `.obs_eq_comap` / `.obs_congr`. -/

section LevelFactor

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]

/-- A factorization of a `G`-2-cochain `κ` through a finite quotient `G ⧸ V`. -/
structure LevelFactor (κ : G × G → ZMod 2) where
  /-- The finite level `G ⧸ V`. -/
  V : OpenNormalSubgroup G
  /-- The finite-level 2-cocycle whose inflation is `κ`. -/
  c : TwoCocycle (G ⧸ V.toSubgroup)
  /-- `κ` is the inflation of `c`. -/
  hfact : ∀ x y : G,
    κ (x, y) = c.κ (QuotientGroup.mk' V.toSubgroup x) (QuotientGroup.mk' V.toSubgroup y)

/-- The relator obstruction of a factorization: the obstruction of the finite-level cocycle at the
projected marking. -/
noncomputable def LevelFactor.obs (W : NatWord X) (μ : X → G) {κ : G × G → ZMod 2}
    (F : LevelFactor κ) : ZMod 2 :=
  relZ W (fun k => QuotientGroup.mk' F.V.toSubgroup (μ k)) F.c

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **Level-independence.**  `F.obs` may be computed at any finer level `W'` through the
pulled-back cocycle. -/
theorem LevelFactor.obs_eq_comap (W : NatWord X) (μ : X → G) {κ : G × G → ZMod 2}
    (F : LevelFactor κ) (W' : OpenNormalSubgroup G)
    (proj : (G ⧸ W'.toSubgroup) →* (G ⧸ F.V.toSubgroup))
    (hproj : proj.comp (QuotientGroup.mk' W'.toSubgroup) = QuotientGroup.mk' F.V.toSubgroup) :
    F.obs W μ = relZ W (fun k => QuotientGroup.mk' W'.toSubgroup (μ k)) (F.c.comap proj) := by
  rw [← relZ_comap W (fun k => QuotientGroup.mk' W'.toSubgroup (μ k)) F.c proj]
  show relZ W (fun k => QuotientGroup.mk' F.V.toSubgroup (μ k)) F.c
    = relZ W (fun k => proj (QuotientGroup.mk' W'.toSubgroup (μ k))) F.c
  congr 1
  funext k
  rw [← MonoidHom.comp_apply, hproj]

/-- The canonical projection between two finite levels, one refining the other. -/
private noncomputable def levelProj {V W' : OpenNormalSubgroup G} (h : W'.toSubgroup ≤ V.toSubgroup) :
    (G ⧸ W'.toSubgroup) →* (G ⧸ V.toSubgroup) :=
  QuotientGroup.map W'.toSubgroup V.toSubgroup (MonoidHom.id _) (by rw [Subgroup.comap_id]; exact h)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem levelProj_comp {V W' : OpenNormalSubgroup G} (h : W'.toSubgroup ≤ V.toSubgroup) :
    (levelProj h).comp (QuotientGroup.mk' W'.toSubgroup) = QuotientGroup.mk' V.toSubgroup := by
  ext g; rw [levelProj, MonoidHom.comp_apply, QuotientGroup.map_mk']; rfl

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
private theorem levelProj_mk {V W' : OpenNormalSubgroup G} (h : W'.toSubgroup ≤ V.toSubgroup)
    (g : G) : levelProj h (QuotientGroup.mk' W'.toSubgroup g) = QuotientGroup.mk' V.toSubgroup g := by
  rw [← MonoidHom.comp_apply, levelProj_comp]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- **Well-definedness.**  `F.obs` depends only on `κ`, not on the chosen factorization. -/
theorem LevelFactor.obs_congr (W : NatWord X) (μ : X → G) {κ : G × G → ZMod 2}
    (F₁ F₂ : LevelFactor κ) : F₁.obs W μ = F₂.obs W μ := by
  set W' : OpenNormalSubgroup G := F₁.V ⊓ F₂.V with hWdef
  have hW1 : W'.toSubgroup ≤ F₁.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have hW2 : W'.toSubgroup ≤ F₂.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  rw [F₁.obs_eq_comap W μ W' (levelProj hW1) (levelProj_comp hW1),
    F₂.obs_eq_comap W μ W' (levelProj hW2) (levelProj_comp hW2)]
  have hcc : F₁.c.comap (levelProj hW1) = F₂.c.comap (levelProj hW2) := by
    apply TwoCocycle.ext'
    funext a b
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective W'.toSubgroup a
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective W'.toSubgroup b
    rw [TwoCocycle.comap_κ, TwoCocycle.comap_κ, levelProj_mk, levelProj_mk, levelProj_mk,
      levelProj_mk, ← F₁.hfact g h, ← F₂.hfact g h]
  rw [hcc]

end LevelFactor

/-! ## `CentExt` over a finite pro-`2` level is pro-`2` -/

/-- `CentExt c` over a finite `2`-group is a finite `2`-group, hence pro-`2` — the target
hypothesis of a presentation lift.  Port of `GQ2.isProP_CentExt`. -/
theorem isProP_CentExt {L : Type} [Group L] [Finite L] (hL : IsPGroup 2 L) (c : TwoCocycle L) :
    IsProP 2 (CentExt c) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hL
  refine isProP_of_isPGroup ((IsPGroup.iff_card (p := 2)).mpr ⟨k + 1, ?_⟩)
  have hcard : Nat.card (CentExt c) = Nat.card L * Nat.card (ZMod 2) := Nat.card_prod _ _
  rw [hcard, hk, Nat.card_zmod, pow_succ]

/-! ## Marked relators and marked presentations

The two hypothesis bundles the `H²` layer consumes.  Neither is an axiom and neither is a
typeclass: both are ordinary structures, threaded explicitly at every use — MC2's documented
general-`K` pattern, and the reason this file introduces no new census entries. -/

section Bundles

variable {X : Type*} (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A **marked relator**: a natural word that lies in the Frattini subgroup and dies at the
marking.  These are exactly the two facts the obstruction needs about the relator itself, and both
are checkable — `IsFrattini` by `decide` for a concrete word on a `Fintype` alphabet, `holds` from
the presentation. -/
structure MarkedRelator (W : NatWord X) (μ : X → G) : Prop where
  /-- The relator lies in the Frattini subgroup: it dies under every `𝔽₂`-marking. -/
  frattini : W.IsFrattini
  /-- The relation holds at the marking. -/
  holds : W.ev μ = 1

/-- The **universal property of a marked presentation**, as an explicit hypothesis bundle: every
marking of a pro-`2` group that kills the relator extends over `G`, and a continuous hom out of
`G` is determined by its values on the marking.

Instantiated for `D_R` by `GQ2.drLiftHom` + `GQ2.drLiftHom_S/X/Y` + `GQ2.dr_hom_ext` (see
`presentedBy_DR` in the regression-pin section), and for MC2's marked cores by
`GQ2.presLiftHom` + `GQ2.presLiftHom_gen` + `GQ2.presPro2_hom_ext`
(`GQ2/Dyadic/MarkedCore/Cores.lean` §3.1) — which is why this file does *not* import the
`MarkedCore` layer: `Word/` sits below `MarkedCore/`, and threading the property keeps it that
way. -/
structure PresentedBy (W : NatWord X) (μ : X → G) where
  /-- Extend a relator-killing marking of a pro-`2` group over `G`. -/
  liftHom : ∀ {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
    [T2Space P] [TotallyDisconnectedSpace P], IsProP 2 P → ∀ ν : X → P, W.ev ν = 1 →
    ContinuousMonoidHom G P
  /-- The extension restricts to the given marking. -/
  liftHom_mark : ∀ {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P] (hP : IsProP 2 P) (ν : X → P)
    (hν : W.ev ν = 1) (k : X), liftHom hP ν hν (μ k) = ν k
  /-- Continuous homs out of `G` are determined by the marking. -/
  hom_ext : ∀ {A : Type} [Group A] [TopologicalSpace A] [IsTopologicalGroup A] [T2Space A]
    (φ ψ : ContinuousMonoidHom G A), (∀ k, φ (μ k) = ψ (μ k)) → φ = ψ

end Bundles

/-! ## The `H²` obstruction homomorphism and its injectivity

Port of `GQ2.normalizeCochain` / `obsFun_DR` / `obs_DR` / `obs_DR_B2_eq_zero` / `obs_DR_ker_le` /
`obsH2_DR` / `obsH2_DR_injective` / `obsH2_DR_eq_of_factor`, with `D_R` replaced by an arbitrary
profinite group carrying a marked presentation. -/

open ContCoh

section Normalize

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Normalize a 2-cochain at `(1,1)` by subtracting the constant `κ (1,1)`. -/
noncomputable def normalizeCochain (κ : G × G → ZMod 2) : G × G → ZMod 2 :=
  κ - fun _ => κ (1, 1)

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem normalizeCochain_add (κ κ' : G × G → ZMod 2) :
    normalizeCochain (κ + κ') = normalizeCochain κ + normalizeCochain κ' := by
  funext p; simp only [normalizeCochain, Pi.add_apply, Pi.sub_apply]; abel

end Normalize

section Obstruction

variable {X : Type*} {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

variable (htriv : ∀ (x : G) (m : ZMod 2), x • m = m)
include htriv

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [ContinuousSMul G (ZMod 2)] in
/-- A constant 2-cochain is a continuous coboundary. -/
theorem const2_mem_B2 (v : ZMod 2) : (fun _ : G × G => v) ∈ B2 G (ZMod 2) := by
  rw [B2, AddSubgroup.mem_map]
  refine ⟨fun _ => v, continuous_const, ?_⟩
  funext p
  simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, htriv]
  abel

omit [ContinuousSMul G (ZMod 2)] in
/-- The normalization of a continuous 2-cocycle factors through a finite quotient. -/
theorem nonempty_levelFactor_normalize (φ : Z2 G (ZMod 2)) :
    Nonempty (LevelFactor (normalizeCochain φ.1)) := by
  have hφcont : Continuous φ.1 := (mem_Z2_iff.mp φ.2).1
  have hφcoc := (mem_Z2_iff.mp φ.2).2
  have hcont : Continuous (normalizeCochain φ.1) := hφcont.sub continuous_const
  have hnorm : normalizeCochain φ.1 (1, 1) = 0 := by
    simp only [normalizeCochain, Pi.sub_apply, sub_self]
  have hcoc : ∀ a b c, normalizeCochain φ.1 (a, b) + normalizeCochain φ.1 (a * b, c)
      = normalizeCochain φ.1 (a, b * c) + normalizeCochain φ.1 (b, c) := by
    intro a b c
    have hz := hφcoc a b c
    rw [htriv] at hz
    simp only [normalizeCochain, Pi.sub_apply]
    linear_combination -hz
  obtain ⟨V, c, hfact⟩ := exists_twoCocycle_factor (normalizeCochain φ.1) hcont hnorm hcoc
  exact ⟨V, c, hfact⟩

/-- The per-cocycle obstruction of a marking against a relator. -/
noncomputable def obsFun (W : NatWord X) (μ : X → G) (φ : Z2 G (ZMod 2)) : ZMod 2 :=
  (nonempty_levelFactor_normalize htriv φ).some.obs W μ

omit [ContinuousSMul G (ZMod 2)] in
/-- `obsFun` may be computed at *any* factorization of the normalization. -/
theorem obsFun_eq (W : NatWord X) (μ : X → G) (φ : Z2 G (ZMod 2))
    (F : LevelFactor (normalizeCochain φ.1)) : obsFun htriv W μ φ = F.obs W μ :=
  LevelFactor.obs_congr W μ _ F

omit [ContinuousSMul G (ZMod 2)] in
/-- **Additivity of the obstruction.** -/
theorem obsFun_add (W : NatWord X) (μ : X → G) (φ ψ : Z2 G (ZMod 2)) :
    obsFun htriv W μ (φ + ψ) = obsFun htriv W μ φ + obsFun htriv W μ ψ := by
  set Fφ := (nonempty_levelFactor_normalize htriv φ).some with hFφ
  set Fψ := (nonempty_levelFactor_normalize htriv ψ).some with hFψ
  set W' : OpenNormalSubgroup G := Fφ.V ⊓ Fψ.V with hWdef
  have hW1 : W'.toSubgroup ≤ Fφ.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_left hx
  have hW2 : W'.toSubgroup ≤ Fψ.V.toSubgroup := fun x hx => SetLike.le_def.mp inf_le_right hx
  have hFsum : obsFun htriv W μ (φ + ψ)
      = relZ W (fun k => QuotientGroup.mk' W'.toSubgroup (μ k))
          (Fφ.c.comap (levelProj hW1) + Fψ.c.comap (levelProj hW2)) := by
    refine obsFun_eq htriv W μ (φ + ψ)
      ⟨W', Fφ.c.comap (levelProj hW1) + Fψ.c.comap (levelProj hW2), ?_⟩
    intro x y
    rw [TwoCocycle.add_κ, TwoCocycle.comap_κ, TwoCocycle.comap_κ, levelProj_mk, levelProj_mk,
      levelProj_mk, levelProj_mk, ← Fφ.hfact x y, ← Fψ.hfact x y]
    show normalizeCochain (φ.1 + ψ.1) (x, y)
      = normalizeCochain φ.1 (x, y) + normalizeCochain ψ.1 (x, y)
    rw [normalizeCochain_add, Pi.add_apply]
  rw [obsFun_eq htriv W μ φ Fφ, obsFun_eq htriv W μ ψ Fψ, hFsum,
    Fφ.obs_eq_comap W μ W' (levelProj hW1) (levelProj_comp hW1),
    Fψ.obs_eq_comap W μ W' (levelProj hW2) (levelProj_comp hW2), relZ_add]

/-- The **obstruction homomorphism** `Z²_cont(G, 𝔽₂) →+ 𝔽₂`. -/
noncomputable def obs (W : NatWord X) (μ : X → G) : Z2 G (ZMod 2) →+ ZMod 2 :=
  AddMonoidHom.mk' (obsFun htriv W μ) (obsFun_add htriv W μ)

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)] htriv in
/-- The relation is inherited by every finite quotient. -/
theorem ev_mk_eq_one (W : NatWord X) (μ : X → G) (hrel : W.ev μ = 1) (V : OpenNormalSubgroup G) :
    W.ev (fun k => QuotientGroup.mk' V.toSubgroup (μ k)) = 1 := by
  have h := W.nat (QuotientGroup.mk' V.toSubgroup) μ
  rw [hrel, map_one] at h
  exact h.symm

omit [ContinuousSMul G (ZMod 2)] in
/-- **`obs` kills `B²`.**  A continuous coboundary normalizes to `δ¹ψ'` (`ψ' 1 = 0`), which factors
as `coboundaryCocycle λ`; its obstruction is `λ (relator) = λ 1 = 0`, the relation dying at the
level.  This is the step that consumes the Frattini hypothesis (through `relZ_coboundary`). -/
theorem obs_B2_eq_zero (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ) :
    (B2 G (ZMod 2)).addSubgroupOf (Z2 G (ZMod 2)) ≤ (obs htriv W μ).ker := by
  intro x hx
  rw [AddMonoidHom.mem_ker]
  rw [AddSubgroup.mem_addSubgroupOf, B2, AddSubgroup.mem_map] at hx
  obtain ⟨ψ, hψc, hψeq⟩ := hx
  have hψcont : Continuous ψ := mem_C1_iff.mp hψc
  have hx1 : x.1 = dOne G (ZMod 2) ψ := hψeq.symm
  set ψ' : G → ZMod 2 := ψ - fun _ => ψ 1 with hψ'def
  obtain ⟨V, lam, hlamfact⟩ := exists_oneCochain_factor ψ' (hψcont.sub continuous_const)
  have hlam1 : lam 1 = 0 := by
    have h := hlamfact 1
    rw [show QuotientGroup.mk' V.toSubgroup (1 : G) = 1 from map_one _] at h
    rw [← h]; simp [hψ'def]
  have hfact : ∀ p q : G, normalizeCochain x.1 (p, q)
      = (coboundaryCocycle lam hlam1).κ (QuotientGroup.mk' V.toSubgroup p)
          (QuotientGroup.mk' V.toSubgroup q) := by
    intro p q
    show normalizeCochain x.1 (p, q)
      = lam (QuotientGroup.mk' V.toSubgroup p) + lam (QuotientGroup.mk' V.toSubgroup q)
        + lam (QuotientGroup.mk' V.toSubgroup p * QuotientGroup.mk' V.toSubgroup q)
    rw [← map_mul (QuotientGroup.mk' V.toSubgroup) p q, ← hlamfact p, ← hlamfact q,
      ← hlamfact (p * q), hx1]
    simp only [normalizeCochain, Pi.sub_apply, hψ'def, dOne, AddMonoidHom.coe_mk,
      ZeroHom.coe_mk, htriv, mul_one, CharTwo.sub_eq_add]
    abel
  show obsFun htriv W μ x = 0
  rw [obsFun_eq htriv W μ x ⟨V, coboundaryCocycle lam hlam1, hfact⟩]
  show relZ W (fun k => QuotientGroup.mk' V.toSubgroup (μ k)) (coboundaryCocycle lam hlam1) = 0
  rw [relZ_coboundary W hW.frattini, ev_mk_eq_one W μ hW.holds V, hlam1]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [ContinuousSMul G (ZMod 2)] in
/-- **Coboundary extraction.**  A continuous hom `sect : G → CentExt c` splitting the level
projection makes the level cocycle a continuous coboundary `δ¹ (fib ∘ sect)`. -/
theorem cocycle_mem_B2 {V : OpenNormalSubgroup G} {c : TwoCocycle (G ⧸ V.toSubgroup)}
    (sect : ContinuousMonoidHom G (CentExt c)) :
    (fun p : G × G => c.κ (sect p.1).base (sect p.2).base) ∈ B2 G (ZMod 2) := by
  have key : ∀ x y z : ZMod 2, y - (x + y + z) + x = z := by decide
  refine ⟨fun g => (sect g).fib, ?_, ?_⟩
  · rw [SetLike.mem_coe, mem_C1_iff]
    exact (continuous_of_discreteTopology (f := CentExt.fib)).comp sect.continuous_toFun
  · funext p
    obtain ⟨g, h⟩ := p
    show g • (sect h).fib - (sect (g * h)).fib + (sect g).fib = c.κ (sect g).base (sect h).base
    rw [htriv, map_mul sect, CentExt.mul_fib]
    exact key (sect g).fib (sect h).fib (c.κ (sect g).base (sect h).base)

omit [ContinuousSMul G (ZMod 2)] in
/-- **Injectivity keystone.**  A continuous 2-cocycle with `obs = 0` is a continuous coboundary:
the relator dies exactly at the factoring level, so the presentation's universal property builds a
splitting section and the level cocycle is `δ¹ (fib ∘ section)`.

This is the only statement of the file that consumes `PresentedBy`. -/
theorem obs_ker_le (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ)
    (hpres : PresentedBy G W μ) (hG : IsProP 2 G) :
    (obs htriv W μ).ker ≤ (B2 G (ZMod 2)).addSubgroupOf (Z2 G (ZMod 2)) := by
  intro φ hφ
  rw [AddMonoidHom.mem_ker] at hφ
  rw [AddSubgroup.mem_addSubgroupOf]
  set F := (nonempty_levelFactor_normalize htriv φ).some with hF
  have hobs0 : F.obs W μ = 0 := by rw [← obsFun_eq htriv W μ φ F]; exact hφ
  set V := F.V with hV
  set c := F.c with hc
  haveI : DiscreteTopology (G ⧸ V.toSubgroup) :=
    Subgroup.instDiscreteTopologyQuotientOfSeparatelyContinuousMul V.toOpenSubgroup
  -- the zero-fibre lift of the projected marking kills the relator, by `hobs0`
  set m : X → CentExt c := lift (fun k => QuotientGroup.mk' V.toSubgroup (μ k)) c with hm
  have hrel : W.ev m = 1 := by
    refine CentExt.ext ?_ ?_
    · rw [relZ_base]; exact ev_mk_eq_one W μ hW.holds V
    · exact hobs0
  set sect : ContinuousMonoidHom G (CentExt c) :=
    hpres.liftHom (isProP_CentExt (hG V) c) m hrel with hsect
  -- `sect` splits the level projection
  have hbase : ∀ g : G, (sect g).base = QuotientGroup.mk' V.toSubgroup g := by
    have hcomp : (⟨CentExt.proj c, continuous_of_discreteTopology⟩ :
        ContinuousMonoidHom (CentExt c) (G ⧸ V.toSubgroup)).comp sect
          = quotientMk V.toSubgroup := by
      refine hpres.hom_ext _ _ fun k => ?_
      show CentExt.proj c (sect (μ k)) = quotientMk V.toSubgroup (μ k)
      rw [hsect, hpres.liftHom_mark]
      rfl
    intro g
    exact DFunLike.congr_fun hcomp g
  -- the normalization is the level cocycle pulled back through the section
  have hnB2 : normalizeCochain φ.1 ∈ B2 G (ZMod 2) := by
    have heq : normalizeCochain φ.1 = fun p : G × G => c.κ (sect p.1).base (sect p.2).base := by
      funext p
      rw [hbase, hbase]
      exact F.hfact p.1 p.2
    rw [heq]
    exact cocycle_mem_B2 htriv sect
  have hconst : φ.1 = normalizeCochain φ.1 + fun _ => φ.1 (1, 1) := by
    funext p; simp only [normalizeCochain, Pi.sub_apply, Pi.add_apply]; abel
  rw [hconst]
  exact AddSubgroup.add_mem _ hnB2 (const2_mem_B2 htriv (φ.1 (1, 1)))

/-! ### Assembly -/

/-- The **descended obstruction** `H²(G, 𝔽₂) →+ 𝔽₂` of a marking against a relator.

The headline of this file: `GQ2.obsH2_DR` with `D_R`/`drWord`/`Fin 3` replaced by an arbitrary
profinite group, natural word and alphabet. -/
noncomputable def obsH2 (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ) :
    H2 G (ZMod 2) →+ ZMod 2 :=
  QuotientAddGroup.lift _ (obs htriv W μ) (fun _ h => obs_B2_eq_zero htriv W μ hW h)

omit [ContinuousSMul G (ZMod 2)] in
@[simp] theorem obsH2_mk (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ)
    (φ : Z2 G (ZMod 2)) : obsH2 htriv W μ hW (H2mk G (ZMod 2) φ) = obsFun htriv W μ φ := rfl

omit [ContinuousSMul G (ZMod 2)] in
/-- **`obsH2` is injective** — the `#H² ≤ 2` half. -/
theorem obsH2_injective (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ)
    (hpres : PresentedBy G W μ) (hG : IsProP 2 G) :
    Function.Injective (obsH2 htriv W μ hW) := by
  rw [injective_iff_map_eq_zero]
  intro a
  induction a using QuotientAddGroup.induction_on with | H φ =>
  intro ha
  exact (QuotientAddGroup.eq_zero_iff φ).mpr
    (obs_ker_le htriv W μ hW hpres hG (AddMonoidHom.mem_ker.mpr ha))

omit [ContinuousSMul G (ZMod 2)] in
/-- **`H²(G, 𝔽₂)` is finite**, being embedded in `𝔽₂`. -/
theorem finite_H2 (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ)
    (hpres : PresentedBy G W μ) (hG : IsProP 2 G) : Finite (H2 G (ZMod 2)) :=
  Finite.of_injective _ (obsH2_injective htriv W μ hW hpres hG)

omit [ContinuousSMul G (ZMod 2)] in
/-- **`#H²(G, 𝔽₂) ≤ 2`** — the form in which the Demushkin lane consumes this file.

A pro-`2` group with a *single* Frattini relator has at most a two-element `H²`; combined with the
matching lower bound (a nonzero cup value, which is what MC2's `IsCupCocycle` Gram supplies via
`obsH2_eq_of_factor`) this pins `#H² = 2`, the Demushkin condition.  Compare
`GQ2.card_H2_DR` (`GQ2/Roe/DRDemushkin.lean`), which is this argument run by hand for `D_R`. -/
theorem card_H2_le_two (W : NatWord X) (μ : X → G) (hW : MarkedRelator G W μ)
    (hpres : PresentedBy G W μ) (hG : IsProP 2 G) : Nat.card (H2 G (ZMod 2)) ≤ 2 := by
  have h := Nat.card_le_card_of_injective _ (obsH2_injective htriv W μ hW hpres hG)
  rwa [Nat.card_zmod] at h

omit [ContinuousSMul G (ZMod 2)] in
/-- **The obstruction at an explicit factoring** — the hook a Gram-matrix computation consumes.

For a continuous 2-cocycle `φ` factoring through a *finite* quotient `L` as
`φ (g, h) = c.κ (ρ g) (ρ h)`, the obstruction of its class is the finite-level relator obstruction
`relZ W (ρ ∘ μ) c`.  This is where MC2's `IsCupCocycle` values (`mRelWord_centLift_fib`,
`nRelWord_centLift_fib`, `handleWord_centLift_fib` of `GQ2/Dyadic/MarkedCore/Cores.lean` §6) enter:
they compute the right-hand side, and this theorem says that number *is* the `H²` obstruction.
Note that no continuity of `ρ` is needed — the two factorizations agree pointwise through
`hfact`. -/
theorem obsH2_eq_of_factor {L : Type} [Group L] [Finite L] (W : NatWord X) (μ : X → G)
    (hW : MarkedRelator G W μ) (φ : Z2 G (ZMod 2)) (ρ : G →* L) (c : TwoCocycle L)
    (hfact : ∀ g h : G, φ.1 (g, h) = c.κ (ρ g) (ρ h)) :
    obsH2 htriv W μ hW (H2mk G (ZMod 2) φ) = relZ W (fun k => ρ (μ k)) c := by
  have hone : φ.1 (1, 1) = 0 := by rw [hfact, map_one, c.norm]
  have hnorm : normalizeCochain φ.1 = φ.1 := by
    funext p; simp only [normalizeCochain, Pi.sub_apply, hone, sub_zero]
  set F := (nonempty_levelFactor_normalize htriv φ).some with hF
  have h1 : obsH2 htriv W μ hW (H2mk G (ZMod 2) φ) = F.obs W μ := rfl
  have hcc : F.c.comap (QuotientGroup.mk' F.V.toSubgroup) = c.comap ρ := by
    refine TwoCocycle.ext' ?_
    funext g h
    rw [TwoCocycle.comap_κ, TwoCocycle.comap_κ, ← F.hfact g h, hnorm, hfact]
  rw [h1]
  show relZ W (fun k => QuotientGroup.mk' F.V.toSubgroup (μ k)) F.c = _
  rw [relZ_comap W μ F.c (QuotientGroup.mk' F.V.toSubgroup), relZ_comap W μ c ρ, hcc]

end Obstruction

/-! ## Checking the Frattini condition

`IsFrattini` is a statement about markings in `Multiplicative (ZMod 2)`, a group of exponent `2`,
so it depends on the exponent resolvers `E`, `E₂` only through the **parities** of their values.
That is what makes it `decide`-able for a real branch word: the honest resolvers send `ω₂` and `η̂`
to noncomputable integers, but `isFrattini_ofPWord_of_parity` replaces them by any computable
resolver of the same parity — typically the constant `1`, since `ω₂` and `η̂` act as odd exponents
on a pro-`2` element. -/

section FrattiniCheck

variable {X : Type*} {G : Type} [Group G]

/-- In a group of exponent `2` a `ℤ`-power depends only on the parity of the exponent. -/
private theorem zpow_eq_of_sq_eq_one (hG : ∀ g : G, g ^ (2 : ℤ) = 1) (g : G) {k l : ℤ}
    (h : k % 2 = l % 2) : g ^ k = g ^ l := by
  have hmod : k ≡ l [ZMOD 2] := h
  obtain ⟨m, hm⟩ := hmod.dvd
  have hkl : k = l + 2 * (-m) := by omega
  rw [hkl, zpow_add, zpow_mul, hG, one_zpow, mul_one]

/-- **The parity reduction.**  Two exponent resolvers with the same parities give the same
denotation in a group of exponent `2`. -/
theorem evalZ_congr_of_parity (hG : ∀ g : G, g ^ (2 : ℤ) = 1) (μ : X → G)
    {E E' : Zhat → ℤ} {E₂ E₂' : ℤ_[2] → ℤ} (hE : ∀ γ, E γ % 2 = E' γ % 2)
    (hE₂ : ∀ z, E₂ z % 2 = E₂' z % 2) (w : PWord X) :
    PWord.evalZ μ E E₂ w = PWord.evalZ μ E' E₂' w := by
  induction w with
  | one => rfl
  | gen g => rfl
  | mul u v ihu ihv => rw [PWord.evalZ_mul, PWord.evalZ_mul, ihu, ihv]
  | inv u ih => rw [PWord.evalZ_inv, PWord.evalZ_inv, ih]
  | conj u g ihu ihg => rw [PWord.evalZ_conj, PWord.evalZ_conj, ihu, ihg]
  | comm u v ihu ihv => rw [PWord.evalZ_comm, PWord.evalZ_comm, ihu, ihv]
  | zpow u k ih => rw [PWord.evalZ_zpow, PWord.evalZ_zpow, ih]
  | z2pow u z ih =>
      rw [PWord.evalZ_z2pow, PWord.evalZ_z2pow, ih, zpow_eq_of_sq_eq_one hG _ (hE₂ z)]
  | profPow u γ ih =>
      rw [PWord.evalZ_profPow, PWord.evalZ_profPow, ih, zpow_eq_of_sq_eq_one hG _ (hE γ)]

/-- Every element of `Multiplicative (ZMod 2)` has exponent `2`. -/
theorem sq_eq_one_multZMod2 (g : Multiplicative (ZMod 2)) : g ^ (2 : ℤ) = 1 := by
  revert g; decide

/-- **The Frattini condition may be checked with any resolvers of the right parity.**  Combined
with the `Decidable` instance on `NatWord.IsFrattini` this closes the condition by kernel
`decide` for a concrete word, at computable resolvers such as `fun _ => 1`. -/
theorem isFrattini_ofPWord_of_parity {E E' : Zhat → ℤ} {E₂ E₂' : ℤ_[2] → ℤ}
    (hE : ∀ γ, E γ % 2 = E' γ % 2) (hE₂ : ∀ z, E₂ z % 2 = E₂' z % 2) (w : PWord X)
    (h : (NatWord.ofPWord w E' E₂').IsFrattini) : (NatWord.ofPWord w E E₂).IsFrattini := by
  intro ν
  rw [NatWord.ofPWord_ev,
    evalZ_congr_of_parity sq_eq_one_multZMod2 ν hE hE₂ w, ← NatWord.ofPWord_ev w E' E₂']
  exact h ν

end FrattiniCheck

/-! ## The `Marking` interface

Thin wrappers presenting the layer over `Marking n G` and `Generator n`, the vocabulary the
branch-word lanes and the marked-core lanes are written in.  `Marking n G` is `FunLike`, so these
are pure notation — `relZ W ⇑t c` already typechecks — but naming them keeps consumer statements
readable. -/

namespace Marking

variable {n : ℕ}

/-- The relator obstruction of a cocycle against a `Marking`. -/
def relZ {L : Type} [Group L] (W : NatWord (Generator n)) (t : GQ2.Dyadic.Marking n L)
    (c : TwoCocycle L) : ZMod 2 :=
  WordCoh.relZ W ⇑t c

@[simp] theorem relZ_def {L : Type} [Group L] (W : NatWord (Generator n))
    (t : GQ2.Dyadic.Marking n L) (c : TwoCocycle L) : relZ W t c = WordCoh.relZ W ⇑t c := rfl

/-- Pushing a marking forward along a group hom is a level change of the obstruction — the
`Marking.map` form of `relZ_comap`. -/
theorem relZ_map {L L' : Type} [Group L] [Group L'] (W : NatWord (Generator n))
    (t : GQ2.Dyadic.Marking n L') (c : TwoCocycle L) (φ : L' →* L) :
    relZ W (t.map φ) c = relZ W t (c.comap φ) :=
  WordCoh.relZ_comap W ⇑t c φ

end Marking

/-! ## Regression pins against `GQ2/Roe/DRWordCoh.lean`

The `drWord`/`Fin 3` instantiation of this file reproduces the `ℚ₂` development's values.  These
are the ticket's acceptance pins; each names the exact `DRWordCoh` declaration it is pinned
against.  Nothing above depends on this section — it is the only place `GQ2.Roe.DRWordCoh` is
used, and it exists so that a future edit to the generic layer cannot silently drift from the
`D_R` values that `GQ2/Roe/DRH2.lean` and `GQ2/Roe/DRDemushkin.lean` consume. -/

section Pins

/-! ### Translating a `GQ2.DRCoh` cocycle

`GQ2.DRCoh.TwoCocycle` and the local `TwoCocycle` have identical fields, so the translation is
definitional in both directions and `CentExt` agrees on the nose.  This is also the bridge MC2's
`IsCupCocycle` layer crosses: its cup-Gram theorems (`mRelWord_centLift_fib`,
`nRelWord_centLift_fib`, `handleWord_centLift_fib`) compute fibres in `GQ2.DRCoh.CentExt`, and
`relZ_ofDRCoh` says those fibres *are* this file's `relZ`. -/

variable {L : Type} [Group L]

/-- Read a `GQ2.DRCoh` 2-cocycle as a local one. -/
def ofDRCoh (c : GQ2.DRCoh.TwoCocycle L) : TwoCocycle L := ⟨c.κ, c.norm, c.cocyc⟩

/-- Read a local 2-cocycle as a `GQ2.DRCoh` one. -/
def toDRCoh (c : TwoCocycle L) : GQ2.DRCoh.TwoCocycle L := ⟨c.κ, c.norm, c.cocyc⟩

@[simp] theorem ofDRCoh_κ (c : GQ2.DRCoh.TwoCocycle L) : (ofDRCoh c).κ = c.κ := rfl
@[simp] theorem toDRCoh_κ (c : TwoCocycle L) : (toDRCoh c).κ = c.κ := rfl
@[simp] theorem ofDRCoh_toDRCoh (c : TwoCocycle L) : ofDRCoh (toDRCoh c) = c := rfl
@[simp] theorem toDRCoh_ofDRCoh (c : GQ2.DRCoh.TwoCocycle L) : toDRCoh (ofDRCoh c) = c := rfl

/-- **The packaging statement.**  `relZ` against a translated cocycle is the fibre of the relator
at the zero-offset lift in `GQ2.DRCoh.CentExt` — the shape MC2's cup-Gram theorems compute.  So
this file's job really is only to *name* the number those theorems produce. -/
theorem relZ_ofDRCoh {X : Type*} (W : NatWord X) (μ : X → L) (c : GQ2.DRCoh.TwoCocycle L) :
    relZ W μ (ofDRCoh c)
      = GQ2.DRCoh.CentExt.fib
          (W.ev (G := GQ2.DRCoh.CentExt c) fun k => ((μ k, 0) : L × ZMod 2)) := rfl

/-! ### The `D_R` relator as a natural word and as a `PWord` -/

/-- `GQ2.drWord` packaged as a `NatWord (Fin 3)`, via `GQ2.map_drWord`. -/
def drNatWord : NatWord (Fin 3) where
  ev := fun {_} _ μ => GQ2.drWord (μ 0) (μ 1) (μ 2)
  nat := fun f μ => GQ2.map_drWord f (μ 0) (μ 1) (μ 2)

@[simp] theorem drNatWord_ev {G : Type} [Group G] (μ : Fin 3 → G) :
    drNatWord.ev μ = GQ2.drWord (μ 0) (μ 1) (μ 2) := rfl

/-- The Roe relator `r₂ = (x^s)⁻¹ x⁻³ y² [y, y^s]` written in the **F2 reflected syntax**
(`GQ2/Dyadic/Word/Syntax.lean`), with `s = gen 0`, `x = gen 1`, `y = gen 2`.  This is the object
that makes the `D_R` pin a pin *over the dyadic word vocabulary* rather than over the bare word
shape. -/
def drWordP : PWord (Fin 3) :=
  .mul (.mul (.mul (.inv (.conj (.gen 1) (.gen 0))) (.inv (.zpow (.gen 1) 3))) (.zpow (.gen 2) 2))
    (.comm (.gen 2) (.conj (.gen 2) (.gen 0)))

/-- **`drWordP` denotes `GQ2.drWord`.**  `PWord.conj`/`PWord.comm` denote `conjR`/`commR`, which
are `GQ2.conjP`/`GQ2.commP` on the nose; the only gap is `ℕ`- versus `ℤ`-powers, closed by
`zpow_natCast`.  Pinned against `GQ2.drWord` (`GQ2/Roe/DRPresentation.lean`). -/
theorem evalZ_drWordP {G : Type*} [Group G] (μ : Fin 3 → G) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    PWord.evalZ μ E E₂ drWordP = GQ2.drWord (μ 0) (μ 1) (μ 2) := by
  rw [GQ2.drWord, ← zpow_natCast (μ 1) 3, ← zpow_natCast (μ 2) 2]
  rfl

/-- The reflected `D_R` relator and the bare word shape give the same natural word. -/
theorem ofPWord_drWordP (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    NatWord.ofPWord drWordP E E₂ = drNatWord := by
  have h : ∀ {G : Type} [Group G] (μ : Fin 3 → G),
      (NatWord.ofPWord drWordP E E₂).ev μ = drNatWord.ev μ := fun μ => evalZ_drWordP μ E E₂
  cases hW : NatWord.ofPWord drWordP E E₂ with | mk ev nat =>
  cases hD : drNatWord with | mk ev' nat' =>
  have hev : @ev = @ev' := by
    funext G inst μ
    have := h (G := G) μ
    rw [hW, hD] at this
    exact this
  subst hev
  rfl

/-! ### The pins -/

/-- **Pin 1 — the finite-level obstruction.**  `relZ` at `drNatWord` is `GQ2.drRelZ`
(`GQ2/Roe/DRWordCoh.lean`, `drRelZ`).  Definitional: the two zero-fibre lifts `lift` and
`GQ2.drLift` are the same term, and the two `CentExt` group structures have identical fields. -/
theorem relZ_drNatWord_eq_drRelZ (μ : Fin 3 → L) (c : GQ2.DRCoh.TwoCocycle L) :
    relZ drNatWord μ (ofDRCoh c) = GQ2.drRelZ μ c := rfl

/-- **Pin 1' — the same, over the reflected syntax.**  The `PWord` form of the relator reproduces
`GQ2.drRelZ` for every choice of exponent resolvers (the word has no profinite exponent, so the
resolvers are irrelevant). -/
theorem relZ_ofPWord_drWordP_eq_drRelZ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (μ : Fin 3 → L)
    (c : GQ2.DRCoh.TwoCocycle L) :
    relZ (NatWord.ofPWord drWordP E E₂) μ (ofDRCoh c) = GQ2.drRelZ μ c := by
  rw [ofPWord_drWordP, relZ_drNatWord_eq_drRelZ]

/-- **Pin 2 — the base value.**  `relZ_base` at `drNatWord` is `GQ2.drRelZ_base`. -/
theorem relZ_base_drNatWord (μ : Fin 3 → L) (c : GQ2.DRCoh.TwoCocycle L) :
    (drNatWord.ev (lift μ (ofDRCoh c))).base = GQ2.drWord (μ 0) (μ 1) (μ 2) :=
  relZ_base drNatWord μ (ofDRCoh c)

/-- **Pin 3 — the Frattini condition.**  `GQ2.drWord` lies in the Frattini subgroup: this is
`DRWordCoh`'s (private) `drWord_multZMod2_eq_one`, the abelian collapse `−4x + 2y ≡ 0 (mod 2)`,
re-derived here by the same kernel `decide` over the `2³` markings of `Multiplicative (ZMod 2)`. -/
theorem isFrattini_drNatWord : drNatWord.IsFrattini := by decide

/-- The reflected form is Frattini too, for any resolvers. -/
theorem isFrattini_ofPWord_drWordP (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) :
    (NatWord.ofPWord drWordP E E₂).IsFrattini := by
  rw [ofPWord_drWordP]; exact isFrattini_drNatWord

/-- **Pin 4 — the marked relator.**  `D_R` with its marked generators satisfies both hypotheses of
`MarkedRelator`: Frattini by `decide`, and `holds` is `GQ2.dr_relation`. -/
theorem markedRelator_DR : MarkedRelator GQ2.DRT drNatWord GQ2.drGens where
  frattini := isFrattini_drNatWord
  holds := GQ2.dr_relation

/-- **Pin 5 — the universal property.**  `D_R` instantiates `PresentedBy` from `GQ2.drLiftHom`,
`GQ2.drLiftHom_S/X/Y` and `GQ2.dr_hom_ext`, confirming that the hypothesis bundle asks for exactly
what a real profinite presentation supplies. -/
noncomputable def presentedBy_DR : PresentedBy GQ2.DRT drNatWord GQ2.drGens where
  liftHom := fun hP ν hν => GQ2.drLiftHom hP ν hν
  liftHom_mark := by
    intro P _ _ _ _ _ _ hP ν hν k
    fin_cases k
    · exact GQ2.drLiftHom_S hP ν hν
    · exact GQ2.drLiftHom_X hP ν hν
    · exact GQ2.drLiftHom_Y hP ν hν
  hom_ext := fun φ ψ h => GQ2.dr_hom_ext φ ψ (h 0) (h 1) (h 2)

/-! ### The end-to-end pin

The strongest regression pin available: the *generic* `H²` obstruction of this file, instantiated
at `D_R` with its marked generators, is literally `GQ2.obsH2_DR`.  Everything the `ℚ₂` development
proves about `obsH2_DR` — injectivity (`GQ2.obsH2_DR_injective`), the factoring bridge
(`GQ2.obsH2_DR_eq_of_factor`), and the `#H²(D_R) ≤ 2` conclusion that `GQ2/Roe/DRH2.lean` and
`GQ2/Roe/DRDemushkin.lean` consume — therefore transfers, and a drift in the generic layer cannot
go unnoticed. -/

section DRPin

variable [DistribMulAction GQ2.DRT (ZMod 2)] [ContinuousSMul GQ2.DRT (ZMod 2)]
variable (htriv : ∀ (x : GQ2.DRT) (m : ZMod 2), x • m = m)
include htriv

omit [ContinuousSMul GQ2.DRT (ZMod 2)] in
/-- **Pin 6 (cocycle level).**  The generic per-cocycle obstruction at `D_R` is `GQ2.obsFun_DR`.
Both sides are computed at some choice of factoring level; `GQ2.obsFun_DR_eq` moves the `ℚ₂` side
onto *this* file's choice, after which the two agree by `relZ_drNatWord_eq_drRelZ`. -/
theorem obsFun_eq_obsFun_DR (φ : ContCoh.Z2 GQ2.DRT (ZMod 2)) :
    obsFun htriv drNatWord GQ2.drGens φ = GQ2.obsFun_DR htriv φ := by
  set F := (nonempty_levelFactor_normalize htriv φ).some with hF
  rw [GQ2.obsFun_DR_eq htriv φ ⟨F.V, toDRCoh F.c, F.hfact⟩]
  rfl

omit [ContinuousSMul GQ2.DRT (ZMod 2)] in
/-- **Pin 7 (`H²` level).**  `obsH2` at `D_R` is `GQ2.obsH2_DR`
(`GQ2/Roe/DRWordCoh.lean`, `obsH2_DR`). -/
theorem obsH2_eq_obsH2_DR (x : ContCoh.H2 GQ2.DRT (ZMod 2)) :
    obsH2 htriv drNatWord GQ2.drGens markedRelator_DR x = GQ2.obsH2_DR htriv x := by
  induction x using QuotientAddGroup.induction_on with | H φ => exact obsFun_eq_obsFun_DR htriv φ

omit [ContinuousSMul GQ2.DRT (ZMod 2)] in
/-- **Pin 8 (the consequence).**  Injectivity of the generic obstruction, proved from the generic
`PresentedBy` bundle, reproduces `GQ2.obsH2_DR_injective`. -/
theorem obsH2_DR_injective_via_generic : Function.Injective (GQ2.obsH2_DR htriv) := by
  have h : (GQ2.obsH2_DR htriv : ContCoh.H2 GQ2.DRT (ZMod 2) → ZMod 2)
      = obsH2 htriv drNatWord GQ2.drGens markedRelator_DR :=
    funext fun x => (obsH2_eq_obsH2_DR htriv x).symm
  rw [h]
  exact obsH2_injective htriv drNatWord GQ2.drGens markedRelator_DR presentedBy_DR GQ2.isProP_DR

end DRPin

end Pins

end GQ2.Dyadic.WordCoh
