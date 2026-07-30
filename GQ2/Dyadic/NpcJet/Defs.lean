/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Dyadic.Word.Eval
import GQ2.GaussZ.RelatorGammaA

/-!
# The corrected noncompact-`N` jet: word, marking, operators, and the slice calculus

Ticket **NC2** of the NC lane (R3(a) commission).  Binding design memo:
`docs/dyadic/nc-design.md` — every declaration below carries a pointer to the memo section it
implements.  The lane proves the **S3.2-corrected** cross-operator identity

```
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),        L_c = A⁻¹ + B + B·A⁻¹,
A = σ^{η̂},  B = σ^{2^r}
```

for the noncompact `N_α` relator — replacing the draft display eq:Ncross's `L_c = A⁻¹`
(machine-refuted; errata item 5).

This file is NC2's deliverable: the **statement-level definitions** (memo §2.2) and the two
pieces of missing machinery the memo's §5.1 leaves to NC2 — the Heisenberg-slice simp kit as
*named* lemmas (memo §3.0(b), friction note §5.3(3)) and the `y^k` power law with its `y^m`
reduction for `δ₀` (memo §3.1).  The headline theorem `npc_cross_operators` (memo §2.3) is
NC5's, in `NpcJet/Main.lean`; the `ω₂`-power bridge and the norm-vanishing lemma (memo §3.0(c),
(d)) are NC3's, in `NpcJet/Omega.lean`; the `δ₀`/D/E block evaluations (memo §3.1–§3.3) are
NC4's, in `NpcJet/Delta.lean`.  Nothing here is sorried and nothing here cites an axiom.

## Contents

* **§1 the word** — `npcDBlock`, `npcEBlock`, `npcWord`: the eq:Npc-word as a `PWord` tree over
  F2's syntax, in the *compressed* D-block spelling `δ₀^A (δ₀ δ₀^A)^{B⁻¹}`.  Per the memo's Q3
  (adopted), this is *the* eq:Npc tree: WNP-a consumes it rather than building its own.
* **§2 the slice vocabulary** — `elt` (typed elements `((v,c),z)` of `CentExt κ⁰`), `sliceElt`
  (the Heisenberg slice `((v,1),z)`), `cLine` (the κ-free `C`-line `((0,c),0)`), and the slice
  simp kit: product, inversion, square, conjugation and commutator laws.
* **§3 the power law** — `normSum`, `powCharge`, `elt_pow`, and the `δ₀` reduction
  `elt_pow_eq_sliceElt` together with `orderOf_elt_dvd_two_mul` (the divisibility hypothesis
  NC3's `ω₂`-bridge consumes).
* **§4 the marking and the operators** — `npcMarking` (Gate-E), `lcOp` (the corrected `L_c`),
  `npcQ0` (the diagonal part).

## Two elaboration frictions (memo §5.3), and their mitigations

1. **Raw `Prod` literals shadow the extension's algebra.**  `CentExt` is a plain `def` for
   `L × ZMod 2`, so a raw pair `(Sd.mk v c, z)` — even with a type ascription — lets Lean find
   `Prod`'s component-wise `Mul`, which is the *wrong* multiplication, after which
   `CentExt.mul_fib` does not fire (and an unascribed literal can even default `C := ℕ`).
   *Mitigation*: every element in this development is routed through the typed constructor
   `elt` (or its specializations `sliceElt`/`cLine`), and the slice kit below is stated in
   those terms only.  `Marking.ofLetters`'s binder types protect `npcMarking`, and
   `Marking.eval` multiplies through the `[Group G]` instance, so evaluation itself is safe.
2. **`CentExt.fib` needs its cocycle.**  On a term whose type is an expression rather than a
   binder type, dot-notation `x.fib` can fail to elaborate; pass the cocycle explicitly as
   `CentExt.fib (c := kappa0Cocycle dat hdat) x` — see `elt_injective` for the pattern.
   Inside this file the `elt`-typed terms otherwise make dot-notation safe; downstream
   (NC4/NC5) the ascription is occasionally needed.

## Naming

Everything lives in `GQ2.Dyadic.NpcJet` — one namespace deeper than the memo's spike, which
sits in `GQ2.Dyadic`.  The nesting is deliberate: NC3 develops the generic `ω₂`/norm lemmas
(`sum_pow_smul_eq_zero`, `zpowHat_omega2_eq_pow_of_dvd_two_mul`) in `GQ2.Dyadic`, and the extra
segment keeps the two files' name spaces disjoint by construction.  Declaration *names* are the
memo's verbatim.

`IsEquivariantFactorSet.m_zero` is *not* a structure field — it is a theorem of
`GQ2.SectionEight.AffineTLift`, so it is spelled `IsEquivariantFactorSet.m_zero dat hdat` rather
than `hdat.m_zero` throughout.
-/

namespace GQ2.Dyadic.NpcJet

open WordCoh2 SectionEight.AffineTLift QuadraticFp2

/-! ## §1. The word (memo §1.1, §2.2)

`g = x₁σ^{2^r}`, `p_α = 2 + 2^α`, and

```
R_{N,α,r,η} = x₀^{p_α} [x₀, σ^{η̂}] · x₂^{-g} (x₂τ)^{ω₂} · E_{r,η}          (h = 0 core)
D_{r,η}     = δ₀^A (δ₀ δ₀^A)^{B⁻¹}        (compressed; A = σ^{η̂}, B = σ^{2^r})
E_{r,η}     = [D_{r,η}, x₁],   δ₀ = (x₀τ)^{ω₂} x₀⁻¹
```

Two AST decisions are mirrored from F2 (memo §1.1): `x^{-g}` is sugar (`PWord.invConj`, packet
Rem. 2.3), and the sum exponent `η̂ − 2^r` **has no node** — the third conjugator of the
expanded D-block is the *product* `A·B⁻¹` of two σ-powers, which is what the compressed
spelling below writes as a single conjugation of `δ₀ δ₀^A` by `B⁻¹`. -/

/-- The **compressed D-block** `D_{r,η} = δ₀^A (δ₀ δ₀^A)^{B⁻¹}` with `A = σ^{η̂}`,
`B = σ^{2^r}` (memo §1.1; `N.py` `d_block_noncompact`, compressed spelling).  Expanded, this is
`δ₀^{σ^{η̂}} δ₀^{σ^{−2^r}} δ₀^{σ^{η̂−2^r}}`; the compressed form is the one the AST uses, since
`η̂ − 2^r` is not an exponent node. -/
noncomputable def npcDBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .mul (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η))
    (.conj (.mul (deltaW 0) (.conj (deltaW 0) ((PWord.gen .sigma).etaPow η)))
      (.zpow (.gen .sigma) (-(2 ^ r : ℤ))))

/-- The **correction block** `E_{r,η} = [D_{r,η}, x₁]` (memo §1.1).  Its jet is the entire
cross term: `E_{r,η}` evaluates to the *central* element with fibre `b_q(L_c c₀, c₁)`
(memo §3.3), which is why the corrected `L_c` is visible in the proof's shape. -/
noncomputable def npcEBlock (η : ℤ_[2]) (r : ℕ) : PWord (Generator 2) :=
  .comm (npcDBlock η r) (.gen (.wild 1))

/-- The **noncompact `N_α` relator** `R_{N,α,r,η}` (draft eq:Npc-word), `h = 0` core: the front
block `x₀^{2+2^α} [x₀, σ^{η̂}]`, the boundary block `x₂^{-g} (x₂τ)^{ω₂}` with `g = x₁σ^{2^r}`,
and the correction `E_{r,η}`.  The handle tail `H_h` (memo §2.5) is appended by NC6; the
`h = 0` core is what the commissioned identity is about. -/
noncomputable def npcWord (α r : ℕ) (η : ℤ_[2]) : PWord (Generator 2) :=
  .mul (.zpow (.gen (.wild 0)) ((2 : ℤ) + 2 ^ α))
    (.mul (.comm (.gen (.wild 0)) ((PWord.gen .sigma).etaPow η))
      (.mul (PWord.invConj (.gen (.wild 2))
              (.mul (.gen (.wild 1)) (.zpow (.gen .sigma) ((2 : ℤ) ^ r))))
        (.mul (PWord.omega2Pow (.mul (.gen (.wild 2)) (.gen .tau)))
          (npcEBlock η r))))

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-! ## §2. The slice vocabulary and its simp kit (memo §3.0(b))

The evaluation group is `E = CentExt (kappa0Cocycle dat hdat)`, whose elements are written
`((v, c), z)` with `v ∈ V`, `c ∈ C`, `z ∈ 𝔽₂` and multiplied by

```
((v,c),z) · ((w,d),z') = ((v + c•w, cd), z + z' + f(v, c•w) + m_c(w)).
```

At the Gate-E marking the whole computation lives in two subsets: the **Heisenberg slice**
`{((v,1),z)}`, where the κ-correction degenerates to `f(v,w)`, and the **κ-free `C`-line**
`{((0,c),0)}`, where it vanishes altogether.  The lemmas of this section are the memo's
§3.0(b) mechanism, packaged as named rewrites (memo §5.3(3): the spike's `show`-style
definitional steps must not survive into the lane, since they are toolchain-fragile). -/

/-- **The typed constructor** for elements `((v,c),z)` of the `κ⁰`-extension.  Everything in the
NC lane is built from this rather than from raw pairs — see friction 1 in the module docstring:
raw `Prod` literals let the component-wise `Prod.mul` be found in place of the extension's
multiplication. -/
def elt (v : V) (c : C) (z : ZMod 2) : CentExt (kappa0Cocycle dat hdat) := (Sd.mk v c, z)

@[simp] theorem elt_base (v : V) (c : C) (z : ZMod 2) :
    (elt dat hdat v c z).base = Sd.mk v c := rfl

@[simp] theorem elt_fib (v : V) (c : C) (z : ZMod 2) : (elt dat hdat v c z).fib = z := rfl

/-- Components of an `elt` are recoverable — the injectivity that lets a block value be read off
coordinatewise.  The proof also exhibits friction 2's mitigation: on a term whose type is the
expression `CentExt (kappa0Cocycle dat hdat)`, the projections take the cocycle explicitly, as
`CentExt.fib (c := kappa0Cocycle dat hdat)`. -/
theorem elt_injective {v w : V} {c d : C} {z z' : ZMod 2}
    (h : elt dat hdat v c z = elt dat hdat w d z') : v = w ∧ c = d ∧ z = z' :=
  ⟨congrArg (fun x => (CentExt.base (c := kappa0Cocycle dat hdat) x).v) h,
    congrArg (fun x => (CentExt.base (c := kappa0Cocycle dat hdat) x).cc) h,
    congrArg (CentExt.fib (c := kappa0Cocycle dat hdat)) h⟩

/-- The identity of the extension in `elt`-form. -/
theorem elt_one : elt dat hdat 0 1 0 = 1 := rfl

/-- **The product law of the extension**, in `elt`-form: the `V`-parts twist, the `C`-parts
multiply, and the fibres pick up `κ⁰ = f(v, c·w) + m_c(w)`.  Definitional — every other law of
this section is a rewrite of this one. -/
theorem elt_mul (v w : V) (c d : C) (z z' : ZMod 2) :
    elt dat hdat v c z * elt dat hdat w d z'
      = elt dat hdat (v + c • w) (c * d) (z + z' + (dat.f v (c • w) + dat.m c w)) := rfl

/-- **The inversion law of the extension**, in `elt`-form.  Definitional; the usable forms are
`sliceElt_inv` (char 2, the `q`-charge of inversion) and `cLine_inv`. -/
theorem elt_inv (v : V) (c : C) (z : ZMod 2) :
    (elt dat hdat v c z)⁻¹ = elt dat hdat (-(c⁻¹ • v)) c⁻¹
      (z + (dat.f v (c • -(c⁻¹ • v)) + dat.m c (-(c⁻¹ • v)))) := rfl

/-- **Slice elements** `((v,1),z)` — the Heisenberg slice of the extension (memo §3.0(b)).  The
wild letters of the Gate-E marking, `δ₀`, and every block value except the conjugators live
here. -/
def sliceElt (v : V) (z : ZMod 2) : CentExt (kappa0Cocycle dat hdat) := elt dat hdat v 1 z

/-- **`C`-line elements** `((0,c),0)` — the κ-free copy of `C` in the extension (memo §3.0(a)).
The conjugators `A = σ^{η̂}`, `B = σ^{2^r}` and the `τ`-letter evaluate here. -/
def cLine (c : C) : CentExt (kappa0Cocycle dat hdat) := elt dat hdat 0 c 0

theorem sliceElt_def (v : V) (z : ZMod 2) : sliceElt dat hdat v z = elt dat hdat v 1 z := rfl

theorem cLine_def (c : C) : cLine dat hdat c = elt dat hdat 0 c 0 := rfl

@[simp] theorem sliceElt_base (v : V) (z : ZMod 2) :
    (sliceElt dat hdat v z).base = Sd.mk v 1 := rfl

@[simp] theorem sliceElt_fib (v : V) (z : ZMod 2) : (sliceElt dat hdat v z).fib = z := rfl

@[simp] theorem cLine_base (c : C) : (cLine dat hdat c).base = Sd.mk 0 c := rfl

@[simp] theorem cLine_fib (c : C) : (cLine dat hdat c).fib = 0 := rfl

@[simp] theorem sliceElt_zero_zero : sliceElt dat hdat (0 : V) 0 = 1 := rfl

@[simp] theorem cLine_one : cLine dat hdat (1 : C) = 1 := rfl

/-- **The slice product law** (memo §3.0(b)): on `{((v,1),z)}` the κ-correction is `f(v,w)` —
the Heisenberg group of `(V, f)` sits inside the extension. -/
theorem sliceElt_mul (v w : V) (z z' : ZMod 2) :
    sliceElt dat hdat v z * sliceElt dat hdat w z'
      = sliceElt dat hdat (v + w) (z + z' + dat.f v w) := by
  simp only [sliceElt_def, elt_mul, one_smul, one_mul, hdat.m_one, add_zero]

/-- **The `C`-line product law** (memo §3.0(a)): `c ↦ ((0,c),0)` is multiplicative — the κ⁰
correction `f(0, c·0) + m_c(0)` vanishes by `f_zero_left` and `m_zero`.  Together with
`cLine_one` and `cLine_inv` this is the content of NC3's `C`-line homomorphism. -/
theorem cLine_mul (c d : C) : cLine dat hdat c * cLine dat hdat d = cLine dat hdat (c * d) := by
  simp only [cLine_def, elt_mul, smul_zero, add_zero, hdat.f_zero_left,
    IsEquivariantFactorSet.m_zero dat hdat]

/-- **The `C`-line inversion law** (memo §3.0(a)). -/
theorem cLine_inv (c : C) : (cLine dat hdat c)⁻¹ = cLine dat hdat c⁻¹ := by
  simp only [cLine_def, elt_inv, smul_zero, neg_zero, hdat.f_zero_left,
    IsEquivariantFactorSet.m_zero dat hdat, add_zero]

/-- Slice times `C`-line: `((v,1),z)·((0,c),0) = ((v,c),z)`.  This is how the `δ₀`-base
`x₀τ ↦ ((c₀,u),0)` is assembled from the Gate-E marking's letters (memo §3.1). -/
theorem sliceElt_mul_cLine (v : V) (z : ZMod 2) (c : C) :
    sliceElt dat hdat v z * cLine dat hdat c = elt dat hdat v c z := by
  simp only [sliceElt_def, cLine_def, elt_mul, smul_zero, add_zero, one_mul,
    hdat.f_zero_right, hdat.m_one]

/-- `C`-line times slice: `((0,c),0)·((w,1),z') = ((c•w, c), z' + m_c(w))`. -/
theorem cLine_mul_sliceElt (c : C) (w : V) (z' : ZMod 2) :
    cLine dat hdat c * sliceElt dat hdat w z' = elt dat hdat (c • w) c (z' + dat.m c w) := by
  simp only [cLine_def, sliceElt_def, elt_mul, zero_add, mul_one, hdat.f_zero_left]

/-- **The slice inversion law** (memo §3.0(b)): in characteristic 2, `((v,1),z)⁻¹` has the same
`V`-part and fibre `z + q v` — the `q`-charge of inversion, the second ingredient of the
commutator mechanism. -/
theorem sliceElt_inv (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    (sliceElt dat hdat v z)⁻¹ = sliceElt dat hdat v (z + q v) := by
  have hneg : ∀ x : V, -x = x := fun x => neg_eq_of_add_eq_zero_left (hV2 x)
  simp only [sliceElt_def, elt_inv, inv_one, one_smul, hneg, hdat.m_one, add_zero, hdat.f_diag]

/-- **The slice square law**: `((v,1),z)² = ((0,1), q v)` in characteristic 2.  This is the
`x₀²`-step of the front block (memo §3.4). -/
theorem sliceElt_sq (hV2 : ∀ v : V, v + v = 0) (v : V) (z : ZMod 2) :
    sliceElt dat hdat v z ^ 2 = sliceElt dat hdat 0 (q v) := by
  rw [sq, sliceElt_mul dat hdat, hV2, hdat.f_diag, CharTwo.add_self_eq_zero, zero_add]

/-- **The slice conjugation law** (memo §3.0(b)): right conjugation by a `C`-line element
applies the **inverse** operator, `((v,1),z)^{((0,g),0)} = ((g⁻¹•v, 1), z + m_{g⁻¹}(v))`.

*This is where the inverse conjugators of the corrected `L_c = A⁻¹ + B + B·A⁻¹` come from*:
`conjR x g = g⁻¹ x g` applies `g⁻¹`, so the D-block's three conjugators `â`, `b⁻¹`, `âb⁻¹`
contribute the three operators `A⁻¹`, `B`, `B A⁻¹` (memo §3.2).  The draft's `L_c = A⁻¹` is the
first summand alone. -/
theorem sliceElt_conj (v : V) (z : ZMod 2) (g : C) :
    conjR (sliceElt dat hdat v z) (cLine dat hdat g)
      = sliceElt dat hdat (g⁻¹ • v) (z + dat.m g⁻¹ v) := by
  rw [conjR, cLine_inv dat hdat, cLine_mul_sliceElt dat hdat, cLine_def, elt_mul, sliceElt_def]
  simp only [smul_zero, add_zero, inv_mul_cancel, hdat.f_zero_right,
    IsEquivariantFactorSet.m_zero dat hdat]

/-- **The slice commutator law** (memo §3.0(b)) — *the entire cross-term mechanism*:
`[((d,1),ζ), ((w,1),ξ)] = ((0,1), b_q(d,w))`.  Both fibres cancel, so the value is independent
of the charges `ζ, ξ`; this is why the E-block's jet needs no normalization of the D-block's
fibre `ζ_D` (memo §3.3, risk 2). -/
theorem sliceElt_comm (hV2 : ∀ v : V, v + v = 0) (d w : V) (ζ ξ : ZMod 2) :
    commR (sliceElt dat hdat d ζ) (sliceElt dat hdat w ξ)
      = sliceElt dat hdat 0 (polar q d w) := by
  -- `f(d, d + w) = q d + f(d, w)`, from the factor-set cocycle identity at `(d, d, w)`.
  have hcross : dat.f d (d + w) = q d + dat.f d w := by
    have h := hdat.f_cocycle d d w
    rw [hV2, hdat.f_zero_left, hdat.f_diag, zero_add] at h
    rw [h, add_assoc, CharTwo.add_self_eq_zero, add_zero]
  -- `f(d + w, d) = q d + f(w, d)`, from the same identity at `(d, w, d)` plus `hcross`.
  have hkey : dat.f (d + w) d = q d + dat.f w d := by
    have h := hdat.f_cocycle d w d
    rw [add_comm w d, hcross] at h
    linear_combination h
  have hV2' : d + w + d = w := by rw [add_comm d w, add_assoc, hV2, add_zero]
  rw [commR, sliceElt_inv dat hdat hV2, sliceElt_inv dat hdat hV2, sliceElt_mul dat hdat,
    sliceElt_mul dat hdat, sliceElt_mul dat hdat, hV2', hV2, hkey, hdat.f_diag]
  congr 1
  -- Pure `𝔽₂` bookkeeping: the two `ζ`'s, the two `ξ`'s, the two `q d`'s and the two `q w`'s
  -- cancel, and what remains is `f(d,w) + f(w,d) = b_q(d,w)`, i.e. `f_polar`.
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hdat.f_polar d w

/-! ## §3. The `y^k` power law and the `y^m` reduction for `δ₀` (memo §3.1)

`δ₀ = (x₀τ)^{ω₂} x₀⁻¹` is the one block whose evaluation leaves the slice: its base
`y := eval(x₀τ) = ((c₀, u), 0)` is a genuinely mixed element.  Its powers are

```
y^k = ((N_k c₀, u^k), z_k),  N_k = ∑_{i<k} uⁱ•,  z_k = ∑_{j<k} [f(N_j c₀, uʲ•c₀) + m_{uʲ}(c₀)]
```

(`elt_pow`).  At `k = m := orderOf u` the norm `N_m` vanishes — that is NC3's
`sum_pow_smul_eq_zero`, rule 2 of the memo's §1.3 table, which needs `V^u = 0` and *no*
semisimplicity — so `y^m` is the slice element `((0,1), z_m)` (`elt_pow_eq_sliceElt`), hence
`y^{2m} = 1` and `orderOf y ∣ 2m` (`orderOf_elt_dvd_two_mul`).  That divisibility is exactly the
hypothesis of NC3's `ω₂`-bridge, which then evaluates `(x₀τ)^{ω₂}` as `y^m`.

The `y^m`-reduction lemma takes the vanishing of the norm as a **hypothesis**, spelled with the
raw `∑ i ∈ Finset.range m, u ^ i • v` of NC3's statement, so that the two files compose with no
bridging lemma. -/

/-- The **`c`-orbit norm** `N_k v = ∑_{i<k} c^i • v` (memo §3.1). -/
def normSum (c : C) (k : ℕ) (v : V) : V := ∑ i ∈ Finset.range k, c ^ i • v

@[simp] theorem normSum_zero (c : C) (v : V) : normSum c 0 v = 0 := Finset.sum_range_zero _

theorem normSum_succ (c : C) (k : ℕ) (v : V) :
    normSum c (k + 1) v = normSum c k v + c ^ k • v := Finset.sum_range_succ _ _

/-- The **accumulated fibre charge** `z_k = ∑_{j<k} [f(N_j v, cʲ•v) + m_{cʲ}(v)]` of the `k`-th
power of `((v,c),0)` (memo §3.1).  It is deliberately never normalized: the E-block's value is
charge-independent (memo §3.3), and `δ₀` needs `z_m` only as "some element of `𝔽₂` depending on
`c₀` alone" (memo risk 2). -/
def powCharge (c : C) (v : V) (k : ℕ) : ZMod 2 :=
  ∑ j ∈ Finset.range k, (dat.f (normSum c j v) (c ^ j • v) + dat.m (c ^ j) v)

@[simp] theorem powCharge_zero (c : C) (v : V) : powCharge dat c v 0 = 0 :=
  Finset.sum_range_zero _

theorem powCharge_succ (c : C) (v : V) (k : ℕ) :
    powCharge dat c v (k + 1)
      = powCharge dat c v k + (dat.f (normSum c k v) (c ^ k • v) + dat.m (c ^ k) v) :=
  Finset.sum_range_succ _ _

/-- **The `y^k` power law** (memo §3.1): the `k`-th power of `((v,c),0)` is
`((N_k v, c^k), z_k)`.  A finite induction on `k` through the definitional product law. -/
theorem elt_pow (v : V) (c : C) (k : ℕ) :
    elt dat hdat v c 0 ^ k = elt dat hdat (normSum c k v) (c ^ k) (powCharge dat c v k) := by
  induction k with
  | zero => rw [pow_zero, pow_zero, normSum_zero, powCharge_zero, elt_one]
  | succ k ih =>
      rw [pow_succ, ih, elt_mul, add_zero, normSum_succ, powCharge_succ, ← pow_succ]

/-- **The `y^m` reduction for `δ₀`** (memo §3.1): once the `c`-norm of `v` vanishes and
`c^m = 1`, the `m`-th power of `((v,c),0)` is the *slice* element `((0,1), z_m)`.

The norm hypothesis is NC3's `sum_pow_smul_eq_zero` — rule 2 of the memo's §1.3 table — applied
at `m = orderOf u`; it is taken as a hypothesis here so that NC2 and NC3 stay independent. -/
theorem elt_pow_eq_sliceElt {c : C} {m : ℕ} (hm : c ^ m = 1) {v : V}
    (hN : ∑ i ∈ Finset.range m, c ^ i • v = 0) :
    elt dat hdat v c 0 ^ m = sliceElt dat hdat 0 (powCharge dat c v m) := by
  rw [elt_pow, show normSum c m v = 0 from hN, hm, sliceElt_def]

/-- Under the hypotheses of `elt_pow_eq_sliceElt`, the `2m`-th power is trivial: the slice
element `((0,1), z_m)` squares to `1` because `f(0,0) = 0` and `𝔽₂` has characteristic 2. -/
theorem elt_pow_two_mul_eq_one {c : C} {m : ℕ} (hm : c ^ m = 1) {v : V}
    (hN : ∑ i ∈ Finset.range m, c ^ i • v = 0) : elt dat hdat v c 0 ^ (2 * m) = 1 := by
  rw [mul_comm, pow_mul, elt_pow_eq_sliceElt dat hdat hm hN, sq, sliceElt_mul dat hdat,
    hdat.f_zero_left, add_zero, add_zero, CharTwo.add_self_eq_zero, sliceElt_zero_zero]

/-- **The order bound feeding NC3's `ω₂`-bridge** (memo §3.1): `orderOf y ∣ 2m` for
`y = ((v,c),0)` with `c^m = 1` and vanishing `c`-norm of `v`.  With `m` odd this is exactly the
hypothesis of `zpowHat_omega2_eq_pow_of_dvd_two_mul`, which then rewrites `(x₀τ)^{ω₂}` to
`y^m`. -/
theorem orderOf_elt_dvd_two_mul {c : C} {m : ℕ} (hm : c ^ m = 1) {v : V}
    (hN : ∑ i ∈ Finset.range m, c ^ i • v = 0) : orderOf (elt dat hdat v c 0) ∣ 2 * m :=
  orderOf_dvd_of_pow_eq_one (elt_pow_two_mul_eq_one dat hdat hm hN)

/-! ## §4. The Gate-E marking (memo §2.2, §2.4) -/

/-- **The Gate-E marking** (`N.py` `symbolic_marking`): `σ ↦ s`, `τ ↦ u` free on the `C`-line,
the wild letters **trivial-lower** (`N.py:891`) with offsets `c₀` on `x₀` and `c₁` on `x₁`.

The boundary letter `x₂` carries lower value `1` and offset `0`: it is *deliberately absent*
from the marking data (`N.py` `primal_names`, memo §2.4).  Giving it an offset computes the
three-variable Gate-D diagnostic form, which is not the commissioned identity. -/
def npcMarking (s u : C) (c₀ c₁ : V) : Marking 2 (CentExt (kappa0Cocycle dat hdat)) :=
  Marking.ofLetters (cLine dat hdat s) (cLine dat hdat u)
    ![sliceElt dat hdat c₀ 0, sliceElt dat hdat c₁ 0, sliceElt dat hdat 0 0]

@[simp] theorem npcMarking_σ (s u : C) (c₀ c₁ : V) :
    (npcMarking dat hdat s u c₀ c₁).σ = cLine dat hdat s := rfl

@[simp] theorem npcMarking_τ (s u : C) (c₀ c₁ : V) :
    (npcMarking dat hdat s u c₀ c₁).τ = cLine dat hdat u := rfl

@[simp] theorem npcMarking_x_zero (s u : C) (c₀ c₁ : V) :
    (npcMarking dat hdat s u c₀ c₁).x 0 = sliceElt dat hdat c₀ 0 := rfl

@[simp] theorem npcMarking_x_one (s u : C) (c₀ c₁ : V) :
    (npcMarking dat hdat s u c₀ c₁).x 1 = sliceElt dat hdat c₁ 0 := rfl

/-- The boundary letter is `1` — `x₂` carries no offset (memo §2.4, §3.5). -/
@[simp] theorem npcMarking_x_two (s u : C) (c₀ c₁ : V) :
    (npcMarking dat hdat s u c₀ c₁).x 2 = 1 := rfl

section Profinite

variable [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-! ### The corrected operators (memo §1.2, §2.2)

`A = s ^ᶻ η̂` and `B = s ^ (2^r)` are the two conjugator *elements*; the operators of the jet
are their actions on `V`.  Both `lcOp` and `npcQ0` are stated over an arbitrary `C`-module,
with no side condition on `r` or `η` — the identity holds for **all** `r : ℕ` and **all**
`η : ℤ_[2]`, which is strictly stronger than the commissioned `r ≥ 1`, `η ∈ ℤ₂ˣ` (memo §2.4).
The draft-validity side conditions belong on the word row, not on the jet identity. -/

/-- **The corrected cross operator** `L_c = A⁻¹ + B + B·A⁻¹` as the module action
(memo §1.2, §2.2) — the S3.2 machine value replacing draft eq:Ncross's `L_c = A⁻¹`.

`polar` is symmetric, so `polar q c₁ (lcOp s η r c₀)` *is* the pairing `b_q(c₁, L_c c₀)`; the
adjoint `M_c = adj(L_c) = A + B⁻¹ + A·B⁻¹` therefore needs no separate Lean object — it is the
same datum read in the other slot of the symmetric pairing (memo §2.4, owner Q6: docstring
reading, no second definition). -/
noncomputable def lcOp (s : C) (η : ℤ_[2]) (r : ℕ) (v : V) : V :=
  (s ^ᶻ etaHatZ η)⁻¹ • v + s ^ (2 ^ r) • v + (s ^ (2 ^ r) * (s ^ᶻ etaHatZ η)⁻¹) • v

/-- The **diagonal part** `Q₀(c₀) = β_A(c₀, A⁻¹c₀) + c_{A⁻¹}(c₀)` in factor-set vocabulary
(memo §1.2, §3.4): the `PLUS_FORM_TEXT_NONCOMPACT` display, with the twisted-lift term
`c_{A⁻¹}` landing as the factor-set correction `dat.m`.  It carries no diagonal `q`-term — the
`q(c₀)` of `x₀^{2+2^α}` cancels against the one from `[x₀, σ^{η̂}]`, which is exactly the
`α ≥ 2` condition `LabuteType.Valid (.N α)` (memo §3.4). -/
noncomputable def npcQ0 (s : C) (η : ℤ_[2]) (c₀ : V) : ZMod 2 :=
  dat.f c₀ ((s ^ᶻ etaHatZ η)⁻¹ • c₀) + dat.m ((s ^ᶻ etaHatZ η)⁻¹) c₀

end Profinite

end Module

end GQ2.Dyadic.NpcJet
