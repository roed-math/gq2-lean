/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.MarkedCore.NFrameExists

/-!
# W70-NFRAME4: the `ℤ/4` frame at `α = 1`, and `demushkinQ (D_N 1 h) = 4`

Wave 70 proved both `α = 1` even cores Demushkin at every handle count
(`GQ2/Dyadic/Instances/EvenAlphaOne.lean`: `evenAlphaOne_isDemushkin_DN` on the `N` row and
`evenAlphaOne_isDemushkin_DM` on the `M` row).  It did **not**
compute the `q`-invariant there, and it could not: `demushkinQ` is a torsion count on the
abelianization, logically independent of `IsDemushkin`, and the committed route to a `q`-value
on the `N` row runs through `NFrame`, which is **provably empty** at `α = 1`
(`nFrameExists_isEmpty_one`).

The emptiness is not an accident of the proof.  `NFrame` hardcodes a `ℤ/2` torsion slot twice
over: in the type of its coordinate isomorphism (`NFrameModel h` carries `ZMod 2` in the first
factor) and in the field `map_t`, which pins the marked generator `x̄₀` into that slot.  At
`α = 1` the relation vector is `4·x̄₀`, so `x̄₀` has order `4` on the nose and no `ℤ/2`-slotted
frame can receive it.

This file builds the `ℤ/4` twin (`NFrameModel4`, `NFrame4`, `nFrame4Exists_phiEquiv`,
`nonempty_nFrame4`) and reads the invariant off it: `demushkinQ (D_N 1 h) = 4` at every handle
count, with **no** frame hypothesis (§7).  Together with `evenAlphaOne_isDemushkin_DN` and the
committed `demushkinRank_DN` this closes the `α = 1` `N`-row invariant package
`(rank, q) = (4 + 2h, 4)`, but **not here**: composing them needs `Instances/`, so the package is
assembled in `GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean` (§8 says why, and this file's
§8 carries only the cross-check).

## Why `q = 4` rather than "`x̄₀` has order 4"

The order of the marked generator is *not* the invariant.  `demushkinQ` counts the whole torsion
subgroup of `D_N^{ab}`, so a proof that `x̄₀` has order `4` (which is already committed, in the
contrapositive form `dnX0_sq_ne_one_one`) bounds `q` from below and says nothing from above.
What forces `q = 4` is the full coordinate isomorphism

  `D_N^{ab} ≅ ℤ/4 ⊕ ℤ₂³ ⊕ ℤ₂^{2h}`   (`nFrame4Exists_phiEquiv`),

whose right side is torsion-free off the first factor (`nFourFinOrder_model`), so its torsion
subgroup is exactly `ℤ/4` and has exactly four elements.  The computation is therefore an
identification of the torsion, not a lower bound on it.

## The `α = 1` construction is shorter than the `α ≥ 2` one

`NFrameExists.lean` needs `dn_torsionGen_sq`, whose proof cancels an odd `ℤ₂`-unit power to get
from `x̄₀^{2+2^α} = 1` to `x̄₀² = 1`.  At `α = 1` the relator reads `x̄₀^4 = 1` on the nose
(`dn_abRel 1 h`), which is already the statement needed, so that apparatus is skipped entirely.
What replaces it is one level shift: the `ℤ₂`-powering seam has to be read modulo `2²` rather
than modulo `2`, which is §2's `zpowZtwo_eq_pow_toZModPow`.

## Reuse, and the duplication this file does *not* remove

Everything α-free in `NFrameExists.lean` is reused verbatim: `nCoordHom`/`nCoordHom_gen`,
`nAbWord`/`nAbWordHom`, the coordinate surjectivity `nDNab_coord`, `nCoordHom_word`, the four
non-torsion coordinate homs `nBHom`/`nCHom`/`nDHom`/`nHHom` with their word formulas, the handle
index lemmas, and `nSurjVec` together with its four non-torsion evaluation lemmas (§6.2 wraps it
rather than cloning it).

Three helper lemmas could not be reused because they are `private` in their home files and are
therefore restated here, each in the *generic* form that a later dedup ticket can hoist; a fourth
private construction is replaced rather than restated:

* `nFourPadicInt_nsmul_eq_zero` and `nFourFinOrder_model` restate `N.lean`'s private
  `nPadicInt_nsmul_eq_zero`/`nFinOrder_model` (the latter is `ZMod 2`-typed, so it needed a new
  statement in any case);
* `zpowZtwo_eq_pow_toZModPow` (§2) restates the private lemma of the same name in
  `GQ2/Dyadic/Instances/NpcCore.lean`, which is itself the all-level form of the public
  `SectionThree.zpowZtwo_of_sq_eq_one`;
* `NFrameExists.lean`'s private `nZ4Hom` is **not** restated at all.  §4 builds its own `ℤ/4`
  target from the α-free `nCoordHom` builder instead, as `nFourIsProP_two_multZMod4` and
  `nFourTHom`.  No declaration named `nFourZ4Hom` exists here, and none is intended.

§1's `demushkinQ_of_torsionEquivZMod` is the **generic** counting step this file was asked to
produce instead of a fourth specialized clone.  It is stated for an arbitrary `MulEquiv` onto an
arbitrary model with an arbitrary `ZMod q` torsion, so it subsumes all four committed
torsion-counting equivalences (`Roe/DRAbelianization.lean`, `MarkedCore/Cores.lean`,
`MarkedCore/MFrame.lean`, `MarkedCore/N.lean`) and the three `private demushkinQ_of_frame`
wrappers that wrap them.  Retro-fitting those four call sites is **not** done here: they live in
files outside this lane, and each of the two candidate homes for the hoisted lemma
(`GQ2/Demushkin.lean`, `GQ2/ZtwoPowering.lean`) carries over 740 transitive importers, so the
move is a dedup ticket of its own rather than a side effect of this one.

## What this settles for the third stratum's surviving point, and what it does not

`Instances/EvenUnramified.lean` isolates the one point at which an `N`-row image is a
principal-unit group, `imChiN 1 = evenRangePrin 2` (`evenUnram_imChiN_one_eq_prin_two`), with
`evenUnram_imChiN_eq_prin_iff` showing that point is unique.  Two things recorded there and in
`Instances/EvenAlphaOne.lean` as prose readings become statements here:

* `EvenAlphaOne.lean` §10 point 3 reads the emptiness of `NFrame 1 h` as being "because the
  invariant it would record is not `2`".  §8's `nFrame4_isEmpty_nFrame_one` derives that
  emptiness from the computed invariant, in the direction the reading was stated.
* The same section records that "the identification of the invariant as `q = 4` is **not** proved
  here", and `Instances/EvenDemushkin.lean`'s residual R1 **recorded** the `α = 1` `q`-invariant
  as uncomputed.  §7 computes it, so both records are discharged rather than inherited.
  (`EvenDemushkin.lean` has since been corrected and now cites `nFrame4_demushkinQ_DN_one`
  directly; `EvenAlphaOne.lean` §10 has not, and its sentence stays literally true of that file.)

What this buys at the surviving point is one matching invariant and nothing beyond it.  The
stratum at depth `α` carries `demushkinQ = 2^α` (the abelianization torsion count, not the
residue cardinality `qOf K FF`), so depth `2` demands `demushkinQ = 4`, and
`evenUnram_head_eq_two_pow_iff` already showed that `2 + 2^a = 2^b` has the single solution
`(a, b) = (1, 2)`; §7 supplies the group-side value that the arithmetic side demands.
`nFrame4_survivingPoint_invariants`, in the companion file
`GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean`, states that agreement as a conjunction, so
that the range identity and the core invariants are read together.

What is **not** proved, here or anywhere in the tree, is that `G_{ℚ₂(i)}(2)` is isomorphic to any
`DN 1 h`: no declaration asserts that in either direction.  An invariant match is not an
isomorphism, and the classification at that point still needs the marked and oriented inputs the
`α = 1` regime lacks.  Of the three replacements the wave-69 note prices for this stratum (a
`q = 4` frame, a Gram at head exponent `4`, and a substitute for the relator-shift factorization
at an even half-exponent) this file supplies the first and does not touch the other two.

## Layering

This file imports `MarkedCore/NFrameExists.lean` and nothing else, so every import stays inside
`MarkedCore/` and the `q`-invariant is available above `Instances/`.  The composites that
genuinely need `Instances/` material, the invariant package and the surviving-point statement,
are in `GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean`, which imports this file and
`Instances/EvenAlphaOne.lean`.  Splitting them off is what keeps a `MarkedCore/ -> Instances/`
edge, which would have been the first of its kind, out of the tree; it follows the owner decision
of 2026-08-12 (owner memo, decisions block, item 5) on the `SqCore`/`Count` boundary.

## Variance (MC-VAR discipline)

As in `NFrameExists.lean`, and for the same reason: everything here happens in the
**abelianization layer**.  No cup form, no Gram matrix and no bilinear pairing occurs in any
statement or proof in this file, so the `M`/`N` row-vs-column dictionary
(`GQ2/Dyadic/MarkedCore/Variance.lean`) is not invoked and no transposition arises.  The
`Finset.prod` inherited from `nAbWord` is a product in an abelian group, not a matrix product.
Nothing from the `H¹`/`H²` layer is cited anywhere in this file; the two statements that do cite
it are in the companion `Instances/` file, which consumes them as black-box conjuncts.

## Contents

* **§1** The generic torsion count `demushkinQ_of_torsionEquivZMod`.
* **§2** The level-`k` powering seam `zpowZtwo_eq_pow_toZModPow`.
* **§3** The `ℤ/4` model `NFrameModel4`, its torsion, and the structure `NFrame4`.
* **§4** The `ℤ/4` torsion coordinate hom `nFourTHom` and its word formula.
* **§5** The combined hom `nFourPhiHom` and its word formula.
* **§6** Injectivity and surjectivity.
* **§7** `nFrame4Exists_phiEquiv`, `nonempty_nFrame4`, and `demushkinQ (D_N 1 h) = 4`.
* **§8** The cross-check against `nFrameExists_isEmpty_one`.
* **§9** Axiom pins.

The invariant package `(rank, q) = (4 + 2h, 4)` and the surviving-point statement are in
`GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean`; see the layering section above.

## Axiom scope (measured)

Every declaration in this file prints at most `[propext, Classical.choice, Quot.sound]` (std-3);
see §9.  This matches the `α ≥ 2` analogues `nonempty_nFrame` and `nFrameExists_demushkinQ_DN`.
The companion file's package is std-3 as well, since the two inputs it adds are.
-/

open Multiplicative

namespace GQ2

open SectionThree

namespace Dyadic

namespace MarkedCore

open scoped GQ2.SectionThree.TopAbInstances

/-! ## §1 The generic torsion count

Four torsion equivalences in the tree hardcode a `ZMod 2` codomain (`Roe/DRAbelianization.lean`
`torsionEquivZMod2`, `MarkedCore/Cores.lean` `torsionEquivZMod2Four`, `MarkedCore/MFrame.lean`
`mTorsionEquivZMod2`, `MarkedCore/N.lean` `nTorsionEquivZMod2`), and three `private`
`demushkinQ_of_frame` wrappers carry `= 2` in their statements.  Nothing in that pattern depends
on the `2`: the transport of the finite-order subtype along the coordinate isomorphism is
generic, and the final count is `Nat.card_zmod`, which is already stated for every modulus.  The
two lemmas below are that observation, and §7 uses them instead of adding a fifth clone. -/

/-- Transport of the finite-order subtype along a multiplicative equivalence.  This is the step
that the four committed torsion equivalences each re-prove inline. -/
def mulEquivSubtypeIsOfFinOrder {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    {x : A // IsOfFinOrder x} ≃ {z : B // IsOfFinOrder z} :=
  Equiv.subtypeEquiv e.toEquiv fun x => by
    show IsOfFinOrder x ↔ IsOfFinOrder (e x)
    rw [isOfFinOrder_iff_pow_eq_one, isOfFinOrder_iff_pow_eq_one]
    exact ⟨fun ⟨n, hn, hp⟩ => ⟨n, hn, by rw [← map_pow, hp, map_one]⟩,
      fun ⟨n, hn, hp⟩ => ⟨n, hn, e.injective (by rw [map_pow, map_one]; exact hp)⟩⟩

/-- **The generic `q`-count**: if the topological abelianization of `G` is isomorphic to a model
whose finite-order elements form a `ZMod q`, then `demushkinQ G = q`.

The hypothesis is a bare `MulEquiv`, not a `ContinuousMulEquiv`: continuity is irrelevant to a
cardinality of a subtype, so consumers holding a coordinate isomorphism pass `F.e.toMulEquiv`.
`q = 0` is permitted and reports `0`, since `Nat.card (ZMod 0) = Nat.card ℤ = 0`. -/
theorem demushkinQ_of_torsionEquivZMod {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] {M : Type*} [Group M] {q : ℕ}
    (e : topAbelianization G ≃* M) (t : {z : M // IsOfFinOrder z} ≃ ZMod q) :
    demushkinQ G = q := by
  rw [demushkinQ, Nat.card_congr (mulEquivSubtypeIsOfFinOrder e), Nat.card_congr t, Nat.card_zmod]

/-! ## §2 The level-`k` powering seam

`SectionThree.zpowZtwo_of_sq_eq_one` reads `ℤ₂`-powering of a square-trivial element modulo `2`.
At `α = 1` the torsion generator is killed by `4`, not by `2`, so the same statement is needed
one level up.  The all-level form already exists in the tree but is `private`
(`GQ2/Dyadic/Instances/NpcCore.lean`), so it is restated here from public ingredients only
(`powZModTwoHom`, `continuous_powZModTwoHom`, `zpowZtwoHom_unique`, all of
`GQ2/ZtwoPowering.lean`).  A dedup ticket should keep one public copy and delete the other two
specializations. -/

/-- On an element killed by `2^k`, `ℤ₂`-powering is evaluation at the standard residue modulo
`2^k`.  The all-level form of `SectionThree.zpowZtwo_of_sq_eq_one`, which is the case `k = 1`. -/
theorem zpowZtwo_eq_pow_toZModPow {P : Type} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) (k : ℕ) (hx : x ^ 2 ^ k = 1) (u : ℤ_[2]) :
    zpowZtwo hP x u = x ^ (PadicInt.toZModPow k u).val := by
  have h := zpowZtwoHom_unique hP (φ := powZModTwoHom x k hx)
    (continuous_powZModTwoHom x k hx) u
  have hone : powZModTwoHom x k hx (ofAdd (1 : ℤ_[2])) = x := by
    show x ^ (PadicInt.toZModPow k (ofAdd (1 : ℤ_[2])).toAdd).val = x
    rw [show (ofAdd (1 : ℤ_[2])).toAdd = (1 : ℤ_[2]) from rfl, map_one]
    by_cases hk : k = 0
    · have hx1 : x = 1 := by simpa [hk] using hx
      simp [hx1]
    · rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (Nat.one_lt_two_pow_iff.mpr hk), pow_one]
  rw [hone] at h
  exact h.symm

/-! ## §3 The `ℤ/4` model and the `α = 1` frame

The only change from `NFrameModel`/`NFrame` is the first factor, `ZMod 2 ⇝ ZMod 4`; the three
core `ℤ₂`-coordinates and the `2h` handle coordinates are untouched, since the handles never
interact with the relation vector and the relation vector only ever constrains `x̄₀`.  The
structure is indexed by `h` alone: `α` is pinned to `1`, because that is the unique exponent at
which `v₂(2 + 2^α) = 2`. -/

/-- The `α = 1` coordinate model of the rank-`(4+2h)` `N`-frame: `ℤ/4 × ℤ₂³ × ℤ₂^{2h}`.  The
`ZMod 4` in the first slot is the entire difference from `NFrameModel`. -/
abbrev NFrameModel4 (h : ℕ) : Type :=
  Multiplicative (ZMod 4 × ℤ_[2] × ℤ_[2] × ℤ_[2] × (Fin (2 * h) → ℤ_[2]))

/-- **The `α = 1` `N`-frame**: a continuous coordinate isomorphism
`D_N^{ab} ≅ ℤ/4 ⊕ ℤ₂^{3+2h}` in which the torsion coordinate is the marked generator `x̄₀`.
The six field values are the same six as `NFrame`'s; only the ambient model differs. -/
structure NFrame4 (h : ℕ) where
  /-- The coordinate isomorphism. -/
  e : ContinuousMulEquiv (topAbelianization (DN 1 h : Type)) (NFrameModel4 h)
  /-- The torsion coordinate: the *marked* generator `x̄₀ ↦ (1, 0, 0, 0, 0)`, now of order 4. -/
  map_t : e (abMk (dnX0 1 h)) = ofAdd (1, 0, 0, 0, 0)
  /-- `x̄₁ ↦ (0, 1, 0, 0, 0)`. -/
  map_B : e (abMk (dnX1 1 h)) = ofAdd (0, 1, 0, 0, 0)
  /-- `σ̄ ↦ (0, 0, 1, 0, 0)`. -/
  map_C : e (abMk (dnSigma 1 h)) = ofAdd (0, 0, 1, 0, 0)
  /-- `x̄₂ ↦ (0, 0, 0, 1, 0)`. -/
  map_D : e (abMk (dnX2 1 h)) = ofAdd (0, 0, 0, 1, 0)
  /-- `ū_j ↦` the `2j`-th handle coordinate. -/
  map_U : ∀ j : Fin h, e (abMk (dnGen 1 h (handleIdxU j)))
    = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordU j) 1)
  /-- `v̄_j ↦` the `(2j+1)`-st handle coordinate. -/
  map_V : ∀ j : Fin h, e (abMk (dnGen 1 h (handleIdxV j)))
    = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordV j) 1)

section ModelTorsion

/-- A `ℤ₂` killed by a positive natural number is zero.  Restatement of `N.lean`'s private
`nPadicInt_nsmul_eq_zero`. -/
private lemma nFourPadicInt_nsmul_eq_zero {n : ℕ} (hn : 0 < n) {b : ℤ_[2]} (h : n • b = 0) :
    b = 0 := by
  rw [nsmul_eq_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr hn.ne')
  · exact h1

/-- A finite-order element of the `ℤ/4` model has zero `ℤ₂`-components, core and handle alike.
This is what makes the torsion subgroup exactly the first factor, and it is the step that turns
"`x̄₀` has order 4" into "`q = 4`". -/
private lemma nFourFinOrder_model {h : ℕ} {a : ZMod 4} {b c d : ℤ_[2]}
    {f : Fin (2 * h) → ℤ_[2]} (hfin : IsOfFinOrder (ofAdd (a, b, c, d, f) : NFrameModel4 h)) :
    b = 0 ∧ c = 0 ∧ d = 0 ∧ f = 0 := by
  rw [isOfFinOrder_iff_pow_eq_one] at hfin
  obtain ⟨n, hn, hpow⟩ := hfin
  rw [← ofAdd_nsmul, ← ofAdd_zero] at hpow
  have hz := Multiplicative.ofAdd.injective hpow
  have hb : n • b = 0 := congrArg (fun p => p.2.1) hz
  have hc : n • c = 0 := congrArg (fun p => p.2.2.1) hz
  have hd : n • d = 0 := congrArg (fun p => p.2.2.2.1) hz
  have hf : n • f = 0 := congrArg (fun p => p.2.2.2.2) hz
  refine ⟨nFourPadicInt_nsmul_eq_zero hn hb, nFourPadicInt_nsmul_eq_zero hn hc,
    nFourPadicInt_nsmul_eq_zero hn hd, funext fun i => ?_⟩
  have hfi : n • f i = 0 := by
    have hfi' := congrFun hf i
    rwa [Pi.smul_apply] at hfi'
  exact nFourPadicInt_nsmul_eq_zero hn hfi

/-- **Torsion of the `ℤ/4` model**: the finite-order subtype of `ℤ/4 × ℤ₂^{3+2h}` is `ℤ/4`, at
every handle count.  The `ZMod 4` twin of `N.lean`'s `nTorsionEquivZMod2`. -/
noncomputable def nTorsionEquivZMod4 (h : ℕ) :
    {z : NFrameModel4 h // IsOfFinOrder z} ≃ ZMod 4 where
  toFun z := z.1.toAdd.1
  invFun a := ⟨ofAdd (a, 0, 0, 0, 0), by
    rw [isOfFinOrder_iff_pow_eq_one]
    refine ⟨4, by norm_num, ?_⟩
    rw [← ofAdd_nsmul, ← ofAdd_zero]
    congr 1
    refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_)))
    · show (4 : ℕ) • a = 0
      exact (by decide : ∀ b : ZMod 4, (4 : ℕ) • b = 0) a
    all_goals simp⟩
  left_inv := by
    rintro ⟨z, hz⟩
    apply Subtype.ext
    have hz' : IsOfFinOrder (ofAdd
        (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
          : NFrameModel4 h) := by
      rw [show (z.toAdd.1, z.toAdd.2.1, z.toAdd.2.2.1, z.toAdd.2.2.2.1, z.toAdd.2.2.2.2)
        = z.toAdd from rfl, ofAdd_toAdd]
      exact hz
    obtain ⟨hb, hc, hd, hf⟩ := nFourFinOrder_model hz'
    show (ofAdd (z.toAdd.1, (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2])) : NFrameModel4 h) = z
    conv_rhs => rw [← ofAdd_toAdd z]
    exact congrArg ofAdd
      (Prod.ext rfl (Prod.ext hb.symm (Prod.ext hc.symm (Prod.ext hd.symm hf.symm))))
  right_inv a := rfl

end ModelTorsion

/-! ## §4 The `ℤ/4` torsion coordinate hom

`nCoordHom` is α-free, so the builder is reused unchanged; only the relator obligation has to be
discharged in the new target, and at `α = 1` it reads `4·1 = 0` in `ℤ/4`.  This is exactly the
check that fails at every other `α`: at `α = 0` the exponent `3` is odd, and at `α ≥ 2` the
exponent `2 + 2^α` is `2 mod 4`, not `0 mod 4`. -/

/-- `Multiplicative (ZMod 4)` is pro-2, being a finite 2-group of order `4`. -/
theorem nFourIsProP_two_multZMod4 : IsProP 2 (Multiplicative (ZMod 4)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 2)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-- **The `α = 1` torsion coordinate** `x̄₀ ↦ 1` into `ZMod 4`, every other marked generator
`↦ 0`.  Its relator check is `(2 + 2^1)·1 = 4·1 = 0` in `ℤ/4`. -/
noncomputable def nFourTHom (h : ℕ) :
    ContinuousMonoidHom (topAbelianization (DN 1 h : Type)) (Multiplicative (ZMod 4)) :=
  nCoordHom 1 h nFourIsProP_two_multZMod4 (coreMark (ofAdd (1 : ZMod 4)) 1 1 1) (by
    rw [coreMark_zero, ← ofAdd_nsmul, ← ofAdd_zero]
    congr 1)

/-- The torsion coordinate of a `ℤ₂`-power word is its `x̄₀`-exponent, read in `ℤ/4`.  The
`ZMod 4` twin of `nTHom_word`. -/
theorem nFourTHom_word (h : ℕ) (c : Fin (coreRank h) → ℤ_[2]) :
    nFourTHom h (nAbWord 1 h c)
      = zpowZtwo nFourIsProP_two_multZMod4 (ofAdd (1 : ZMod 4)) (c 0) := by
  rw [nFourTHom, nCoordHom_word, mProd_single _ _ _ 0 (fun i hi => by
    rw [coreMark_apply]
    have hv := mCoreVal_ne_zero hi
    split_ifs <;> first | rfl | omega), coreMark_zero]

/-- The `ZMod 4` powering hits every class: `(ofAdd 1)^(c.val) = ofAdd c`.  The `ZMod 4` twin of
`zpowZtwo_ofAdd_one_zmod2`. -/
theorem nFourZpowZtwo_ofAdd_one_zmod4 (c : ZMod 4) :
    zpowZtwo nFourIsProP_two_multZMod4 (ofAdd (1 : ZMod 4)) ((c.val : ℤ_[2])) = ofAdd c := by
  rw [zpowZtwo_natCast, ← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul, mul_one]
  exact ZMod.natCast_rightInverse c

/-! ## §5 The combined coordinate hom `φ_N^{(4)}`

Identical in shape to `nPhiHom`, with `nFourTHom` in the torsion slot and `α` pinned to `1`.
The four non-torsion components are the committed `nBHom`, `nCHom`, `nDHom`, `nHHom`. -/

section Phi

variable (h : ℕ)

/-- **The combined coordinate hom** `φ_N^{(4)} : D_N^{ab} → ℤ/4 ⊕ ℤ₂³ ⊕ ℤ₂^{2h}` at `α = 1`. -/
noncomputable def nFourPhiHom : topAbelianization (DN 1 h : Type) →* NFrameModel4 h where
  toFun z := ofAdd ((nFourTHom h z).toAdd, (nBHom 1 h z).toAdd,
    (nCHom 1 h z).toAdd, (nDHom 1 h z).toAdd, fun k => (nHHom 1 k z).toAdd)
  map_one' := by
    simp only [map_one, toAdd_one]
    rfl
  map_mul' x y := by
    simp only [map_mul, toAdd_mul]
    rw [← ofAdd_add]
    rfl

theorem continuous_nFourPhiHom : Continuous (nFourPhiHom h) := by
  show Continuous fun z => ofAdd ((nFourTHom h z).toAdd, (nBHom 1 h z).toAdd,
    (nCHom 1 h z).toAdd, (nDHom 1 h z).toAdd, fun k => (nHHom 1 k z).toAdd)
  exact continuous_ofAdd.comp
    ((continuous_toAdd.comp (nFourTHom h).continuous_toFun).prodMk
      ((continuous_toAdd.comp (nBHom 1 h).continuous_toFun).prodMk
        ((continuous_toAdd.comp (nCHom 1 h).continuous_toFun).prodMk
          ((continuous_toAdd.comp (nDHom 1 h).continuous_toFun).prodMk
            (continuous_pi fun k => continuous_toAdd.comp (nHHom 1 k).continuous_toFun)))))

/-- `φ_N^{(4)}` on a `ℤ₂`-power word, all five coordinates at once. -/
theorem nFourPhiHom_word (c : Fin (coreRank h) → ℤ_[2]) :
    nFourPhiHom h (nAbWord 1 h c)
      = ofAdd ((zpowZtwo nFourIsProP_two_multZMod4 (ofAdd (1 : ZMod 4)) (c 0)).toAdd,
          c 1, c 2, c 3, fun k => c (mHandleIdx k)) := by
  show ofAdd (_, _, _, _, _) = _
  rw [nFourTHom_word, nBHom_word, nCHom_word, nDHom_word]
  simp only [toAdd_ofAdd]
  congr 1
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _
    (funext fun k => by rw [nHHom_word, toAdd_ofAdd]))))

/-! ### §6.1 Injectivity

The `α ≥ 2` proof kills the four non-torsion exponents and then uses `x̄₀² = 1` to collapse the
survivor.  Here the survivor is collapsed by `x̄₀⁴ = 1` instead, which is `dn_abRel 1 h` verbatim
with no unit cancellation, and the residue is read modulo `4` rather than modulo `2`. -/

/-- The marked generator is killed by `2² = 4` at `α = 1`: the relation vector `(2 + 2^1)·x̄₀`
*is* `4·x̄₀`.  Contrast `α ≥ 2`, where extracting `x̄₀² = 1` from `x̄₀^{2+2^α} = 1` costs an odd
`ℤ₂`-unit cancellation (`dn_torsionGen_sq`). -/
theorem nFourX0_pow_four (h : ℕ) : (abMk (dnX0 1 h)) ^ 2 ^ 2 = 1 := by
  have h4 : (2 : ℕ) ^ 2 = 2 + 2 ^ 1 := by norm_num
  rw [h4]
  exact dn_abRel 1 h

/-- The generator of `Multiplicative (ZMod 4)` is killed by `2² = 4`, in the shape §2's seam
consumes. -/
theorem nFourGen_pow_four : (ofAdd (1 : ZMod 4)) ^ 2 ^ 2 = 1 := by
  rw [← ofAdd_nsmul, ← ofAdd_zero]
  congr 1

theorem nFourPhiHom_injective : Function.Injective (nFourPhiHom h) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨c, rfl⟩ := nDNab_coord 1 h z
  rw [nFourPhiHom_word] at hz
  have hv := Multiplicative.ofAdd.injective (hz.trans
    (show (1 : NFrameModel4 h) = ofAdd ((0 : ZMod 4), (0 : ℤ_[2]), (0 : ℤ_[2]), (0 : ℤ_[2]),
      (0 : Fin (2 * h) → ℤ_[2])) from rfl))
  rw [Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq, Prod.mk.injEq] at hv
  obtain ⟨hvt, hv1, hv2, hv3, hvh⟩ := hv
  -- every exponent off the torsion slot vanishes
  have hc0 : ∀ i, i ≠ 0 → c i = 0 := by
    intro i hi0
    rcases mIdx_cases i with rfl | rfl | rfl | rfl | ⟨k, rfl⟩
    · exact absurd rfl hi0
    · exact hv1
    · exact hv2
    · exact hv3
    · exact congrFun hvh k
  -- the `ℤ/4` torsion coordinate says the surviving exponent is `0 mod 4`
  have hval0 : (PadicInt.toZModPow 2 (c 0)).val = 0 := by
    rw [zpowZtwo_eq_pow_toZModPow nFourIsProP_two_multZMod4 (ofAdd (1 : ZMod 4)) 2
      nFourGen_pow_four (c 0), ← ofAdd_nsmul, toAdd_ofAdd, nsmul_eq_mul, mul_one] at hvt
    have hlt : (PadicInt.toZModPow (p := 2) 2 (c 0)).val < 4 := by
      have := ZMod.val_lt (PadicInt.toZModPow (p := 2) 2 (c 0)); simpa using this
    rcases (by omega : (PadicInt.toZModPow 2 (c 0)).val = 0
        ∨ (PadicInt.toZModPow 2 (c 0)).val = 1
        ∨ (PadicInt.toZModPow 2 (c 0)).val = 2
        ∨ (PadicInt.toZModPow 2 (c 0)).val = 3) with h0 | h1 | h2 | h3
    · exact h0
    · rw [h1] at hvt; exact absurd hvt (by decide)
    · rw [h2] at hvt; exact absurd hvt (by decide)
    · rw [h3] at hvt; exact absurd hvt (by decide)
  rw [nAbWord_single 1 h c hc0, ← dnX0,
    zpowZtwo_eq_pow_toZModPow (nIsProP_two_topAb_DN 1 h) _ 2 (nFourX0_pow_four h) (c 0),
    hval0, pow_zero]

/-! ### §6.2 Surjectivity

`nSurjVec` is committed and α-free, but its torsion slot is typed at `ZMod 2`.  Rather than clone
it and its five evaluation lemmas, `nFourSurjVec` overrides the zero slot and delegates every
other slot to `nSurjVec`, so the four committed non-torsion evaluation lemmas are reused as they
stand. -/

/-- The exponent vector realizing a prescribed `ℤ/4`-torsion coordinate tuple: the zero slot
carries the `ZMod 4` residue, every other slot is `nSurjVec`'s. -/
noncomputable def nFourSurjVec {h : ℕ} (a : ZMod 4) (b cc d : ℤ_[2])
    (f : Fin (2 * h) → ℤ_[2]) : Fin (coreRank h) → ℤ_[2] := fun i =>
  if (i : ℕ) = 0 then ((a.val : ℤ_[2])) else nSurjVec (0 : ZMod 2) b cc d f i

section SurjVec

variable {h : ℕ} (a : ZMod 4) (b cc d : ℤ_[2]) (f : Fin (2 * h) → ℤ_[2])

@[simp] theorem nFourSurjVec_zero : nFourSurjVec a b cc d f 0 = ((a.val : ℤ_[2])) := by
  rw [nFourSurjVec, if_pos (coreVal_zero h)]

@[simp] theorem nFourSurjVec_one : nFourSurjVec a b cc d f 1 = b := by
  rw [nFourSurjVec, if_neg (by rw [coreVal_one]; omega)]
  exact nSurjVec_one 0 b cc d f

@[simp] theorem nFourSurjVec_two : nFourSurjVec a b cc d f 2 = cc := by
  rw [nFourSurjVec, if_neg (by rw [coreVal_two]; omega)]
  exact nSurjVec_two 0 b cc d f

@[simp] theorem nFourSurjVec_three : nFourSurjVec a b cc d f 3 = d := by
  rw [nFourSurjVec, if_neg (by rw [coreVal_three]; omega)]
  exact nSurjVec_three 0 b cc d f

@[simp] theorem nFourSurjVec_handle (k : Fin (2 * h)) :
    nFourSurjVec a b cc d f (mHandleIdx k) = f k := by
  rw [nFourSurjVec, if_neg (by rw [mHandleIdx_val]; omega)]
  exact nSurjVec_handle 0 b cc d f k

end SurjVec

theorem nFourPhiHom_surjective : Function.Surjective (nFourPhiHom h) := by
  intro w
  rw [← ofAdd_toAdd w]
  obtain ⟨a, b, cc, d, f⟩ := w.toAdd
  refine ⟨nAbWord 1 h (nFourSurjVec a b cc d f), ?_⟩
  rw [nFourPhiHom_word, nFourSurjVec_zero, nFourSurjVec_one, nFourSurjVec_two,
    nFourSurjVec_three]
  congr 1
  refine Prod.ext ?_ (Prod.ext rfl (Prod.ext rfl (Prod.ext rfl (funext fun k => ?_))))
  · show (zpowZtwo nFourIsProP_two_multZMod4 (ofAdd (1 : ZMod 4)) ((a.val : ℤ_[2]))).toAdd = a
    rw [nFourZpowZtwo_ofAdd_one_zmod4, toAdd_ofAdd]
  · exact nFourSurjVec_handle a b cc d f k

/-! ### §6.3 `φ_N^{(4)}` on the marked generators

The six values are the six fields of `NFrame4`.  All four core rows are standard basis vectors,
as on the `α ≥ 2` side: there is no forced row to reconcile. -/

/-- `φ_N^{(4)}` at a marked generator: each slot reads its own marking. -/
theorem nFourPhiHom_gen (i : Fin (coreRank h)) :
    nFourPhiHom h (abMk (dnGen 1 h i))
      = ofAdd ((coreMark (ofAdd (1 : ZMod 4)) 1 1 1 i).toAdd,
          (coreMark 1 (ofAdd (1 : ℤ_[2])) 1 1 i).toAdd,
          (coreMark 1 1 (ofAdd (1 : ℤ_[2])) 1 i).toAdd,
          (coreMark 1 1 1 (ofAdd (1 : ℤ_[2])) i).toAdd,
          fun k => (mHandleMark k (ofAdd (1 : ℤ_[2])) i).toAdd) := by
  show ofAdd (_, _, _, _, _) = _
  rw [nFourTHom, nBHom, nCHom, nDHom, nCoordHom_gen, nCoordHom_gen, nCoordHom_gen,
    nCoordHom_gen]
  exact congrArg _ (congrArg _ (congrArg _ (congrArg _ (congrArg _
    (funext fun k => by rw [nHHom, nCoordHom_gen])))))

/-- The torsion coordinate is the marked generator: `x̄₀ ↦ (1, 0, 0, 0, 0)`, now in `ℤ/4`. -/
theorem nFourPhiHom_X0 : nFourPhiHom h (abMk (dnX0 1 h)) = ofAdd (1, 0, 0, 0, 0) := by
  rw [dnX0, nFourPhiHom_gen]
  simp only [coreMark_zero, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (0 : Fin (coreRank h)) (by rw [coreVal_zero]; omega)]
  rfl

theorem nFourPhiHom_X1 : nFourPhiHom h (abMk (dnX1 1 h)) = ofAdd (0, 1, 0, 0, 0) := by
  rw [dnX1, nFourPhiHom_gen]
  simp only [coreMark_one, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (1 : Fin (coreRank h)) (by rw [coreVal_one]; omega)]
  rfl

theorem nFourPhiHom_Sigma : nFourPhiHom h (abMk (dnSigma 1 h)) = ofAdd (0, 0, 1, 0, 0) := by
  rw [dnSigma, nFourPhiHom_gen]
  simp only [coreMark_two, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (2 : Fin (coreRank h)) (by rw [coreVal_two]; omega)]
  rfl

theorem nFourPhiHom_X2 : nFourPhiHom h (abMk (dnX2 1 h)) = ofAdd (0, 0, 0, 1, 0) := by
  rw [dnX2, nFourPhiHom_gen]
  simp only [coreMark_three, toAdd_ofAdd, toAdd_one,
    mHandleMark_toAdd_core (3 : Fin (coreRank h)) (by rw [coreVal_three]; omega)]
  rfl

/-- `ū_j ↦` the `2j`-th handle coordinate. -/
theorem nFourPhiHom_U {h : ℕ} (j : Fin h) :
    nFourPhiHom h (abMk (dnGen 1 h (handleIdxU j)))
      = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordU j) 1) := by
  rw [← nHandleIdx_coordU j, nFourPhiHom_gen]
  simp only [coreMark_mHandleIdx, toAdd_one, mHandleMark_toAdd_single]

/-- `v̄_j ↦` the `(2j+1)`-st handle coordinate. -/
theorem nFourPhiHom_V {h : ℕ} (j : Fin h) :
    nFourPhiHom h (abMk (dnGen 1 h (handleIdxV j)))
      = ofAdd (0, 0, 0, 0, Pi.single (nHandleCoordV j) 1) := by
  rw [← nHandleIdx_coordV j, nFourPhiHom_gen]
  simp only [coreMark_mHandleIdx, toAdd_one, mHandleMark_toAdd_single]

end Phi

/-! ## §7 The frame, its existence, and the `q`-invariant -/

set_option synthInstance.maxSize 256 in
/-- **The `α = 1` coordinate isomorphism** `φ_N^{(4)} : D_N^{ab} ≃ₜ* ℤ/4 × ℤ₂³ × ℤ₂^{2h}`. -/
noncomputable def nFrame4Exists_phiEquiv (h : ℕ) :
    ContinuousMulEquiv (topAbelianization (DN 1 h : Type)) (NFrameModel4 h) :=
  continuousMulEquivOfBijective ⟨nFourPhiHom h, continuous_nFourPhiHom h⟩
    ⟨nFourPhiHom_injective h, nFourPhiHom_surjective h⟩

@[simp] theorem nFrame4Exists_phiEquiv_apply (h : ℕ)
    (z : topAbelianization (DN 1 h : Type)) :
    nFrame4Exists_phiEquiv h z = nFourPhiHom h z := rfl

/-- **Existence of the `α = 1` `N`-frame**, at every handle count.  This is the statement that
makes the `α = 1` `q`-invariant non-vacuous: `NFrame 1 h` is empty (`nFrameExists_isEmpty_one`),
so without a `ℤ/4`-slotted replacement there would be no frame at `α = 1` at all. -/
theorem nonempty_nFrame4 (h : ℕ) : Nonempty (NFrame4 h) :=
  ⟨{ e := nFrame4Exists_phiEquiv h
     map_t := nFourPhiHom_X0 h
     map_B := nFourPhiHom_X1 h
     map_C := nFourPhiHom_Sigma h
     map_D := nFourPhiHom_X2 h
     map_U := fun j => nFourPhiHom_U j
     map_V := fun j => nFourPhiHom_V j }⟩

/-- **`demushkinQ D_N = 4` at `α = 1` from a frame**: the `ZMod 4` twin of `demushkinQ_DN_nFrame`,
routed through §1's generic count rather than through a fourth bespoke wrapper. -/
theorem demushkinQ_DN_one_nFrame4 {h : ℕ} (F : NFrame4 h) : demushkinQ (DN 1 h : Type) = 4 :=
  demushkinQ_of_torsionEquivZMod F.e.toMulEquiv (nTorsionEquivZMod4 h)

/-- **The unlock**: `demushkinQ D_N = 4` at `α = 1` with **no** frame hypothesis, at every handle
count.  The `α = 1` counterpart of `nFrameExists_demushkinQ_DN`, which proves `= 2` for `α ≥ 2`.

So the `N`-row `q`-invariant is not uniform in `α`: it is `4` at `α = 1` and `2` at `α ≥ 2`. -/
theorem nFrame4_demushkinQ_DN_one (h : ℕ) : demushkinQ (DN 1 h : Type) = 4 :=
  (nonempty_nFrame4 h).elim demushkinQ_DN_one_nFrame4

/-! ## §8 The cross-check against the committed emptiness theorem

The invariant package that composes §7 with `evenAlphaOne_isDemushkin_DN` and
`EvenModel.demushkinRank_DN` is **not** here: both of those live under `Instances/`, and citing
them would put a `MarkedCore/ -> Instances/` edge in the tree.  They are composed in
`GQ2/Dyadic/Instances/NFrameAlphaOneInvariants.lean` instead, which keeps this file's imports
inside `MarkedCore/`.  The cross-check below needs nothing outside `MarkedCore/` and stays. -/

/-- **Cross-check against the committed emptiness theorem.**  `nFrameExists_isEmpty_one` is
proved in `NFrameExists.lean` by exhibiting a `ℤ/4`-valued character separating `x̄₀²` from `1`.
It is re-derived here from the `q`-invariant instead: a `ℤ/2`-slotted frame would force
`demushkinQ (D_N 1 h) = 2`, and §7 computes `4`.

The two proofs share more than `dn_abRel`: both run through the same coordinate homomorphism
`abLiftG (nLiftHom 1 h _ (coreMark (ofAdd (1 : ZMod 4)) 1 1 1) _)` with the same `ℤ/4` marking,
`NFrameExists.lean`'s private `nZ4Hom` writing it out and §4's `nFourTHom` reaching it through
the `nCoordHom` builder (which is *defined* as `abLiftG (nLiftHom …)`).  The duplication is
recorded in the layering note above.  So this is a consistency check on §7's *reading* of that
hom, not an independent second route to the emptiness.  It is still the sharpest form of the
reason `NFrame` had to be replaced rather than repaired at `α = 1`. -/
theorem nFrame4_isEmpty_nFrame_one (h : ℕ) : IsEmpty (NFrame 1 h) := by
  refine ⟨fun F => ?_⟩
  have h2 : demushkinQ (DN 1 h : Type) = 2 := demushkinQ_DN_nFrame F
  rw [nFrame4_demushkinQ_DN_one h] at h2
  exact absurd h2 (by decide)

/-! ## §9 Axiom pins

The measured scope is the **std-3** set `[propext, Classical.choice, Quot.sound]`, matching the
`α ≥ 2` analogues `nonempty_nFrame` and `nFrameExists_demushkinQ_DN`.  No census axiom appears,
and none of the cited inputs contributes one. -/

section AxiomPins

#print axioms mulEquivSubtypeIsOfFinOrder
#print axioms demushkinQ_of_torsionEquivZMod
#print axioms zpowZtwo_eq_pow_toZModPow
#print axioms nTorsionEquivZMod4
#print axioms nFourIsProP_two_multZMod4
#print axioms nFourTHom
#print axioms nFourTHom_word
#print axioms nFourZpowZtwo_ofAdd_one_zmod4
#print axioms nFourPhiHom
#print axioms continuous_nFourPhiHom
#print axioms nFourPhiHom_word
#print axioms nFourX0_pow_four
#print axioms nFourGen_pow_four
#print axioms nFourPhiHom_injective
#print axioms nFourSurjVec
#print axioms nFourSurjVec_zero
#print axioms nFourSurjVec_one
#print axioms nFourSurjVec_two
#print axioms nFourSurjVec_three
#print axioms nFourSurjVec_handle
#print axioms nFourPhiHom_surjective
#print axioms nFourPhiHom_gen
#print axioms nFourPhiHom_X0
#print axioms nFourPhiHom_X1
#print axioms nFourPhiHom_Sigma
#print axioms nFourPhiHom_X2
#print axioms nFourPhiHom_U
#print axioms nFourPhiHom_V
#print axioms nFrame4Exists_phiEquiv
#print axioms nFrame4Exists_phiEquiv_apply
#print axioms nonempty_nFrame4
#print axioms demushkinQ_DN_one_nFrame4
#print axioms nFrame4_demushkinQ_DN_one
#print axioms nFrame4_isEmpty_nFrame_one

-- the private model-torsion lemmas, printed because §7 rests on them
#print axioms nFourPadicInt_nsmul_eq_zero
#print axioms nFourFinOrder_model

end AxiomPins

end MarkedCore

end Dyadic

end GQ2
