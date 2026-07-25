/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Roe.FoxBasic
public import GQ2.Roe.NormalForms
public import GQ2.TameSimple

@[expose] public section

/-!
# Proposition 5.2: the mixed Hessian of the Roe relator  (⟦prop:hessian⟧, ⟦eq:pairingoperator⟧)

The `Γ_R` counterpart of `GQ2.FoxHeisenberg.HessianRow`: the degree-one Fox–Heisenberg pairing
induced by the traced mixed central coordinate `mixedB_R` (`GQ2.Roe.FoxBasic`) on the simple
normal forms of ⟦lem:normalforms⟧.  On a nontrivial simple tame module `V`, a degree-one class is
represented by `(0,0,0,d)` (`x₁`-supported — the note's normal form, the `x₀ ↔ x₁` swap of the
`Γ_A` `x₀`-supported rep) and the dual class by `λ ∈ V^∨` in the matching `x₁`-supported form.
The Roe wild relator (note eq. (1.2) ⟦eq:relators⟧, `GQ2.Roe.Words`)

  `r_R = (x₀^σ)⁻¹ · aR · x₁² · cR`,   `aR = (x₀⁻³τ)^{ω₂}`,   `cR = [x₁, x₁^{σ₂}]`

evaluates at the Heisenberg lift `heisMarking t (x1Supported d) (x1Supported lam)` to the central
scalar of ⟦eq:pairingoperator⟧:

  `(d, λ) ↦ λ(d)`                       if `T = 1`   (unramified/split, `U = 1`),
  `(d, λ) ↦ λ((1 + U + U⁻¹) d)`         if `V^T = 0` (ramified),   `U = σ₂ = Marking.sigma2`.

Per-factor central (`z`) ledger (the note's proof of ⟦prop:hessian⟧, quoted) — this is the
`z`-analogue of R21's `u`-ledger (`GQ2.Roe.WildRow`), one class-two degree up, on the
`x₁`-supported rep:

* "the factors `(x₀^σ)⁻¹` and `(x₀⁻³τ)^{ω₂}` have no varying coordinate" — both lie in the base
  slice `secHom '' C` (their `σ, τ, x₀` inputs are `x₁`-supported-free): `heisMarking_aR_secHom`
  and `heisMarking_conjP_x0_sigma_secHom`/`heisMarking_conjP_x0_sigma_inv_z` give `.z = .a = .l = 0`;
* "The square `x₁²` contributes the usual Heisenberg diagonal `λ(d)`" — `heisMarking_x1_sq_z`,
  a single `HeisLift.mul_z_of_trivial` (no `d₀²`-inside-`h₀` apparatus: `x₁.a = d` is structural,
  no `ω₂`-norm collapse, so `Γ_R`'s diagonal is shorter than `Γ_A`'s `h₀`-shadow);
* "The class-two commutator identity applied to `[x₁, x₁^{σ₂}]` contributes `λ(Ud) + λ(U⁻¹d)`" —
  `heisMarking_cR_z`, via `HeisLift.commP_z_of_trivial` + the base-slice conjugation
  `HeisLift.conjP_a_of_slice`/`conjP_l_of_slice` on `y1R = x₁^{σ₂}` (mirrors `Γ_A`'s
  `heisMarking_c0_z_ramified`, with the commutator entries `x₁, x₁^{σ₂}` in place of `d₀, x₀^{σ₂}`).

Assembled wild summand (the exact shape `Γ_A`'s `heisMarking_wildValue_z(_ramified)` uses, so
R25/R26/R27 mirror consumption 1:1): `heisMarking_wildValueR_z` (split, `= λ(d)`; the two
commutator terms cancel in char 2 once `U = 1`) and `heisMarking_wildValueR_z_ramified`
(`= λ(d + U d + U⁻¹ d)`).  The `.z` is additive across the four-factor peel because every right
factor has `.a = 0` (base slice, char-2 square, commutator), so the `HeisLift.mul_z` cross-terms
`prefix.l(factor.a)` vanish.

Assembled pairing (⟦prop:hessian⟧ proper, ⟦eq:pairingoperator⟧): `mixedB_R_pairing_split`
(`= λ(d)`) and `mixedB_R_pairing_ramified` (`= λ((1+U+U⁻¹)d)`) — the tame relator's central
coordinate vanishes on the `x₁`-supported rep (`heisMarking_tameValue_z_eq_zero`, shared with
`Γ_A`), so the pairing is carried entirely by the wild summand.  Nondegeneracy of the ramified
operator `1 + U + U⁻¹` (`Both operators are invertible.`) is `sigma2_pairing_operator_injective`,
reused **verbatim** — the operator is the presentation-independent tame datum `U = σ₂`, not a
`Γ_A`/`Γ_R`-specific relator — and re-exported here under the Roe name
`pairingR_operator_injective` for R27's quadratic seam.

Organisation mirrors `GQ2/FoxHeisenberg/HessianRow.lean`'s `section HessianRow` 1:1 (per-factor
`z`-ledger, then the assembled wild summand, then the `mixedB_R` pairing); it is far shorter — no
`h₀` class-two apparatus, and two of the four factors are pure base slice.  The scalar-Gram
cocycle closed form (the note's `⟨(a,c,d),(a',c',d')⟩ = ac' + ca' + dd'`, ⟦eq:scalarform⟧, the
honest diagonal `dd'` this diagonal `λ(d)` feeds) is ticket R25's `mixedB_cocycle_R`; the
quadratic refinement ⟦prop:quadratic⟧/⟦eq:QR⟧ (`q(d)` and `q(d) + b_q(d, U⁻¹d)`) is R27's.
-/

namespace GQ2

namespace FoxH

section HessianRowR

variable {C : Type*} [Group C] [Finite C] {V : Type*} [AddCommGroup V] [DistribMulAction C V]
  [Finite V]

/-! ### The base generators land in the base slice on the `x₁`-supported rep

The `x₁`-supported tuple `x1Supported` (⟦lem:normalforms⟧'s normal form `(0,0,0,d)`) is
`GQ2.Roe.NormalForms`'s — imported, not redeclared.

`σ, τ, x₀` (indices `0,1,2`) have zero primal/dual offsets on `x1Supported`, so they are pure
`secHom` base elements; only `x₁` (index `3`) carries the varying coordinate `d`. -/

omit [Finite C] [Finite V] in
/-- `σ` is a base-slice element on the `x₁`-supported rep. -/
theorem heisMarking_sigma_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).σ = secHom t.σ := rfl

omit [Finite C] [Finite V] in
/-- `τ` is a base-slice element on the `x₁`-supported rep. -/
theorem heisMarking_tau_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).τ = secHom t.τ := rfl

omit [Finite C] [Finite V] in
/-- `x₀` is a base-slice element on the `x₁`-supported rep. -/
theorem heisMarking_x0_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).x₀ = secHom t.x₀ := rfl

omit [Finite V] in
/-- `σ₂ = σ^{ω₂}` is a base-slice element on the `x₁`-supported rep (`ω₂` of a base element is
base, `powOmega2_map` along `secHom`): `σ₂ = secHom t.σ₂`, so `.a = .l = .z = 0` and `.g = σ₂`. -/
theorem heisMarking_sigma2_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).sigma2 = secHom t.sigma2 := by
  show powOmega2 (heisMarking t (x1Supported d) (x1Supported lam)).σ = secHom t.sigma2
  rw [heisMarking_sigma_secHom, ← powOmega2_map secHom]
  rfl

omit [Finite V] in
/-- `aR = (x₀⁻³τ)^{ω₂}` is a base-slice element on the `x₁`-supported rep — the note's "the factor
`(x₀⁻³τ)^{ω₂}` has no varying coordinate": its `σ, τ, x₀` inputs are all `x₁`-supported-free, so
`aR = secHom t.aR` and `.z = .a = .l = 0` (`.g = t.aR`). -/
theorem heisMarking_aR_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).aR = secHom t.aR := by
  show powOmega2 (((heisMarking t (x1Supported d) (x1Supported lam)).x₀ ^ 3)⁻¹
      * (heisMarking t (x1Supported d) (x1Supported lam)).τ) = secHom t.aR
  rw [heisMarking_x0_secHom, heisMarking_tau_secHom, ← map_pow, ← map_inv, ← map_mul,
    ← powOmega2_map secHom]
  rfl

/-! ### Per-factor central (`z`) ledger (⟦prop:hessian⟧ proof, quoted) -/

omit [Finite C] [Finite V] in
/-- **`(x₀^σ)⁻¹` has no varying coordinate** — the note's "the factor `(x₀^σ)⁻¹` has no varying
coordinate": `conjP x₀ σ` is a base-slice element (both `x₀, σ` are).  The `Γ_R` analogue of
`Γ_A`'s `heisMarking_conjP_x1_sigma_z`. -/
theorem heisMarking_conjP_x0_sigma_secHom (t : Marking C) (d : V) (lam : ElemDual V) :
    conjP (heisMarking t (x1Supported d) (x1Supported lam)).x₀
      (heisMarking t (x1Supported d) (x1Supported lam)).σ = secHom (conjP t.x₀ t.σ) := by
  simp only [conjP, map_mul, map_inv]; rfl

omit [Finite C] [Finite V] in
/-- **`(x₀^σ)⁻¹` has no central contribution** (`heisMarking_conjP_x0_sigma_secHom`, `.z` of the
inverse — both the factor and its inverse are base slice). -/
theorem heisMarking_conjP_x0_sigma_inv_z (t : Marking C) (d : V) (lam : ElemDual V) :
    ((conjP (heisMarking t (x1Supported d) (x1Supported lam)).x₀
      (heisMarking t (x1Supported d) (x1Supported lam)).σ)⁻¹).z = 0 := by
  rw [heisMarking_conjP_x0_sigma_secHom, ← map_inv]; rfl

omit [Finite V] in
/-- **`aR` has no central contribution** (`heisMarking_aR_secHom`, `.z`-projection). -/
theorem heisMarking_aR_z (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).aR.z = 0 := by
  rw [heisMarking_aR_secHom]; rfl

omit [Finite V] in
/-- **`aR` has no primal offset** (`heisMarking_aR_secHom`, `.a`-projection) — needed to kill the
`HeisLift.mul_z` cross-term in the assembled peel. -/
theorem heisMarking_aR_a (t : Marking C) (d : V) (lam : ElemDual V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).aR.a = 0 := by
  rw [heisMarking_aR_secHom]; rfl

omit [Finite V] in
/-- **Split base-triviality of `aR`**: with `x₀, τ` acting trivially on `V`, the base of
`aR = (x₀⁻³τ)^{ω₂}` acts trivially (`WordLift.powOmega2_smul_of_trivial_mul`: `(x₀⁻³)` trivial, `τ`
trivial ⇒ `powOmega2 τ` trivial).  Mirrors R21's `liftMarking_aR_g_smul`. -/
theorem heisMarking_aR_g_smul (t : Marking C) (d : V) (lam : ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (htau : ∀ v : V, t.τ • v = v) (v : V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).aR.g • v = v := by
  rw [heisMarking_aR_secHom]
  show powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ) • v = v
  refine WordLift.powOmega2_smul_of_trivial_mul _ _ (fun w => ?_) (fun w => ?_) v
  · exact inv_smul_eq_iff.mpr ((MulAction.stabilizer C w).pow_mem (hx0 w) 3).symm
  · rw [powOmega2]; exact (MulAction.stabilizer C w).pow_mem (htau w) _

omit [Finite V] in
/-- **Ramified base-triviality of `aR`**: with `x₀` acting trivially and `τ` acting with *odd*
order (`powOmega2 t.τ` trivial, `hTodd`), the base of `aR` still acts trivially — its action is
the 2-part of the `τ`-action (`WordLift.powOmega2_smul_of_trivial_mul`).  Mirrors R21's
`liftMarking_aR_g_ramified`; no `htau` fixed-point-freeness enters. -/
theorem heisMarking_aR_g_ramified (t : Marking C) (d : V) (lam : ElemDual V)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) (v : V) :
    (heisMarking t (x1Supported d) (x1Supported lam)).aR.g • v = v := by
  rw [heisMarking_aR_secHom]
  show powOmega2 ((t.x₀ ^ 3)⁻¹ * t.τ) • v = v
  exact WordLift.powOmega2_smul_of_trivial_mul _ _
    (fun w => inv_smul_eq_iff.mpr ((MulAction.stabilizer C w).pow_mem (hx0 w) 3).symm) hTodd v

omit [Finite C] [Finite V] in
/-- **`x₁²` contributes the Heisenberg diagonal `λ(d)`** — the note's "The square `x₁²` contributes
the usual Heisenberg diagonal `λ(d)`".  A single `HeisLift.mul_z_of_trivial`: `x₁.a = d`,
`x₁.l = λ`, `x₁.z = 0`, so `(x₁·x₁).z = 0 + 0 + λ(d)` (the two `z`'s cancel in char 2 anyway).
No `d₀²`-inside-`h₀` apparatus — the varying coordinate is `x₁.a = d` directly. -/
theorem heisMarking_x1_sq_z (t : Marking C) (d : V) (lam : ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) :
    ((heisMarking t (x1Supported d) (x1Supported lam)).x₁ ^ 2).z = lam d := by
  rw [pow_two, HeisLift.mul_z_of_trivial _ _ (fun v => hx1 v)]
  show (0 : ZMod 2) + 0 + lam d = lam d
  simp

omit [Finite C] [Finite V] in
/-- **`x₁²` has no primal offset**: `(x₁·x₁).a = d + d = 0` (char 2) — the note's `D(x₁²) = 0`,
here one class-two degree up.  Kills the `HeisLift.mul_z` cross-term in the assembled peel. -/
theorem heisMarking_x1_sq_a (t : Marking C) (d : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx1 : ∀ v : V, t.x₁ • v = v) :
    ((heisMarking t (x1Supported d) (x1Supported lam)).x₁ ^ 2).a = 0 := by
  rw [pow_two, HeisLift.mul_a_of_trivial _ _ (fun v => hx1 v)]
  show d + d = 0
  exact hV₂ d

omit [Finite V] in
/-- **`cR = [x₁, x₁^{σ₂}]` contributes `λ(U⁻¹d) + λ(Ud)`** — the note's "The class-two commutator
identity applied to `[x₁, x₁^{σ₂}]` contributes `λ(Ud) + λ(U⁻¹d)`", `U = σ₂`.  Via the Heisenberg
commutator symplectic form `HeisLift.commP_z_of_trivial`:
`[x₁, y₁].z = x₁.l(y₁.a) + y₁.l(x₁.a)`, with `y₁ = x₁^{σ₂}` a base-slice conjugate of `x₁`
(`conjP_a_of_slice`/`conjP_l_of_slice`, `σ₂` base): `y₁.a = U⁻¹d`, `y₁.l = U⁻¹λ`, so
`= λ(U⁻¹d) + (U⁻¹λ)(d) = λ(U⁻¹d) + λ(Ud)`.  Mirrors `Γ_A`'s `heisMarking_c0_z_ramified`. -/
theorem heisMarking_cR_z (t : Marking C) (d : V) (lam : ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) :
    (heisMarking t (x1Supported d) (x1Supported lam)).cR.z
      = lam (t.sigma2⁻¹ • d) + lam (t.sigma2 • d) := by
  set M := heisMarking t (x1Supported d) (x1Supported lam) with hM
  have hX_a : M.x₁.a = d := rfl
  have hX_l : M.x₁.l = lam := rfl
  have hX_g : ∀ v : V, M.x₁.g • v = v := fun v => hx1 v
  have hsig_a : M.sigma2.a = 0 := by rw [heisMarking_sigma2_secHom]; rfl
  have hsig_l : M.sigma2.l = 0 := by rw [heisMarking_sigma2_secHom]; rfl
  have hsig_g : M.sigma2.g = t.sigma2 := by rw [heisMarking_sigma2_secHom]; rfl
  have hy_a : M.y1R.a = t.sigma2⁻¹ • d := by
    show (conjP M.x₁ M.sigma2).a = _
    rw [HeisLift.conjP_a_of_slice M.x₁ M.sigma2 hsig_a, hX_a, hsig_g]
  have hy_l : M.y1R.l = t.sigma2⁻¹ • lam := by
    show (conjP M.x₁ M.sigma2).l = _
    rw [HeisLift.conjP_l_of_slice M.x₁ M.sigma2 hsig_l, hX_l, hsig_g]
  have hy_g : ∀ v : V, M.y1R.g • v = v := HeisLift.conjP_g_trivial M.x₁ M.sigma2 hX_g
  show (commP M.x₁ M.y1R).z = _
  rw [HeisLift.commP_z_of_trivial M.x₁ M.y1R hX_g hy_g, hX_l, hy_a, hy_l, hX_a,
    ElemDual.smul_apply, inv_inv]

omit [Finite C] [Finite V] in
/-- **`cR` has no primal offset**: a commutator of trivially-based elements
(`HeisLift.commP_a_of_trivial`).  Kills the outermost `HeisLift.mul_z` cross-term. -/
theorem heisMarking_cR_a (t : Marking C) (d : V) (lam : ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) :
    (heisMarking t (x1Supported d) (x1Supported lam)).cR.a = 0 := by
  set M := heisMarking t (x1Supported d) (x1Supported lam) with hM
  have hX_g : ∀ v : V, M.x₁.g • v = v := fun v => hx1 v
  show (commP M.x₁ M.y1R).a = 0
  exact HeisLift.commP_a_of_trivial M.x₁ M.y1R hX_g
    (HeisLift.conjP_g_trivial M.x₁ M.sigma2 hX_g)

/-! ### The assembled wild summand (⟦eq:pairingoperator⟧, shapes matching `Γ_A`)

The four-factor peel of `wildValueR = (x₀^σ)⁻¹ · aR · x₁² · cR`: `.z` is additive because every
right factor has `.a = 0` (`aR` base slice, `x₁²` char-2 square, `cR` commutator), so the
`HeisLift.mul_z` cross-terms `prefix.l(factor.a)` vanish; only `x₁².z = λ(d)` and `cR.z` survive
(`(x₀^σ)⁻¹.z = aR.z = 0`). -/

omit [Finite V] in
/-- **The split wild summand** (⟦eq:pairingoperator⟧, `T = 1`, so `U = 1` on a nontrivial simple
module): `wildValueR.z = λ(d)`.  Peel: `(x₀^σ)⁻¹.z + aR.z + x₁².z + cR.z = 0 + 0 + λ(d) + (λ(d) +
λ(d)) = λ(d)` — the two commutator terms cancel in char 2 once `U = 1` (`hU`).  Exact shape of
`Γ_A`'s `heisMarking_wildValue_z`; **no `σ₂`-conjugator-tameness beyond `hU`** and no `htau`
fixed-point-freeness. -/
theorem heisMarking_wildValueR_z (t : Marking C) (d : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x1Supported d) (x1Supported lam)).wildValueR.z = lam d := by
  set M := heisMarking t (x1Supported d) (x1Supported lam) with hM
  have hA_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹).g • v = v := fun v =>
    HeisLift.inv_g_trivial _ (HeisLift.conjP_g_trivial M.x₀ M.σ (fun w => hx0 w)) v
  have hB_g : ∀ v : V, M.aR.g • v = v := heisMarking_aR_g_smul t d lam hx0 htau
  have hC_g : ∀ v : V, (M.x₁ ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ (fun w => hx1 w) (fun w => hx1 w) v
  have hAB_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹ * M.aR).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hA_g hB_g v
  have hABC_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hAB_g hC_g v
  show ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2 * M.cR).z = lam d
  rw [HeisLift.mul_z_of_trivial _ _ hABC_g, heisMarking_cR_a t d lam hx1, map_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hAB_g, heisMarking_x1_sq_a t d lam hV₂ hx1, map_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hA_g, heisMarking_aR_a t d lam, map_zero, add_zero,
    heisMarking_conjP_x0_sigma_inv_z t d lam, heisMarking_aR_z t d lam,
    heisMarking_x1_sq_z t d lam hx1, heisMarking_cR_z t d lam hx1,
    show t.sigma2⁻¹ • d = d from inv_smul_eq_iff.mpr (hU d).symm, hU d]
  rw [CharTwo.add_self_eq_zero (lam d)]
  simp

omit [Finite V] in
/-- **The ramified wild summand** (⟦eq:pairingoperator⟧, `V^T = 0`):
`wildValueR.z = λ(d + Ud + U⁻¹d) = λ((1 + U + U⁻¹)d)`.  Same peel as the split case, but the two
commutator terms `λ(U⁻¹d) + λ(Ud)` no longer cancel.  Exact shape of `Γ_A`'s
`heisMarking_wildValue_z_ramified`; the fixed-point-free hypothesis is carried for
signature-parity with `Γ_A` (consumed by R26's duality assembly) but is *not needed* here — the
`Γ_R` diagonal comes from `x₁.a = d` structurally, not from an `ω₂`-norm collapse. -/
theorem heisMarking_wildValueR_z_ramified (t : Marking C) (d : V) (lam : ElemDual V)
    (hV₂ : ∀ v : V, v + v = 0) (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (_ : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v) :
    (heisMarking t (x1Supported d) (x1Supported lam)).wildValueR.z
      = lam (d + t.sigma2 • d + t.sigma2⁻¹ • d) := by
  set M := heisMarking t (x1Supported d) (x1Supported lam) with hM
  have hA_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹).g • v = v := fun v =>
    HeisLift.inv_g_trivial _ (HeisLift.conjP_g_trivial M.x₀ M.σ (fun w => hx0 w)) v
  have hB_g : ∀ v : V, M.aR.g • v = v := heisMarking_aR_g_ramified t d lam hx0 hTodd
  have hC_g : ∀ v : V, (M.x₁ ^ 2).g • v = v := fun v => by
    rw [pow_two]; exact HeisLift.mul_g_trivial _ _ (fun w => hx1 w) (fun w => hx1 w) v
  have hAB_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹ * M.aR).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hA_g hB_g v
  have hABC_g : ∀ v : V, ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2).g • v = v := fun v =>
    HeisLift.mul_g_trivial _ _ hAB_g hC_g v
  show ((conjP M.x₀ M.σ)⁻¹ * M.aR * M.x₁ ^ 2 * M.cR).z = lam (d + t.sigma2 • d + t.sigma2⁻¹ • d)
  rw [HeisLift.mul_z_of_trivial _ _ hABC_g, heisMarking_cR_a t d lam hx1, map_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hAB_g, heisMarking_x1_sq_a t d lam hV₂ hx1, map_zero, add_zero,
    HeisLift.mul_z_of_trivial _ _ hA_g, heisMarking_aR_a t d lam, map_zero, add_zero,
    heisMarking_conjP_x0_sigma_inv_z t d lam, heisMarking_aR_z t d lam,
    heisMarking_x1_sq_z t d lam hx1, heisMarking_cR_z t d lam hx1, map_add, map_add]
  abel

/-! ### The assembled degree-one pairing (⟦prop:hessian⟧, ⟦eq:pairingoperator⟧)

The tame relator's central coordinate vanishes on the `x₁`-supported rep
(`heisMarking_tameValue_z_eq_zero`, `σ, τ` inputs offset-free), so the `mixedB_R` pairing is
carried entirely by the wild summand above. -/

omit [Finite V] in
/-- **⟦prop:hessian⟧, ⟦eq:pairingoperator⟧, split case**: on the `x₁`-supported representatives the
degree-one pairing is `(d, λ) ↦ λ(d)` when `T = 1`.  Exact `Γ_R` twin of `lemma_5_13_pairing_split`
(consumed by R26). -/
theorem mixedB_R_pairing_split (t : Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v) (htau : ∀ v : V, t.τ • v = v)
    (hU : ∀ v : V, t.sigma2 • v = v) (d : V) (lam : ElemDual V) :
    mixedB_R t (x1Supported d) (x1Supported (V := ElemDual V) lam) = lam d := by
  show (heisMarking t (x1Supported d) (x1Supported lam)).tameValue.z
      + (heisMarking t (x1Supported d) (x1Supported lam)).wildValueR.z = lam d
  rw [heisMarking_tameValue_z_eq_zero t (x1Supported d) (x1Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValueR_z t d lam hV₂ hx0 hx1 htau hU, zero_add]

omit [Finite V] in
/-- **⟦prop:hessian⟧, ⟦eq:pairingoperator⟧, ramified case**: when `V^T = 0` the pairing on the
`x₁`-supported representatives is `(d, λ) ↦ λ((1 + U + U⁻¹)d)` for `U = σ₂ = Marking.sigma2`.
Exact `Γ_R` twin of `lemma_5_13_pairing_ramified` (consumed by R26). -/
theorem mixedB_R_pairing_ramified (t : Marking C) (hV₂ : ∀ v : V, v + v = 0)
    (hx0 : ∀ v : V, t.x₀ • v = v) (hx1 : ∀ v : V, t.x₁ • v = v)
    (htau : ∀ v : V, t.τ • v = v → v = 0) (hTodd : ∀ v : V, powOmega2 t.τ • v = v)
    (d : V) (lam : ElemDual V) :
    mixedB_R t (x1Supported d) (x1Supported (V := ElemDual V) lam)
      = lam (d + t.sigma2 • d + t.sigma2⁻¹ • d) := by
  show (heisMarking t (x1Supported d) (x1Supported lam)).tameValue.z
      + (heisMarking t (x1Supported d) (x1Supported lam)).wildValueR.z = _
  rw [heisMarking_tameValue_z_eq_zero t (x1Supported d) (x1Supported lam) rfl rfl rfl rfl,
    heisMarking_wildValueR_z_ramified t d lam hV₂ hx0 hx1 htau hTodd, zero_add]

/-! ### Invertibility (⟦prop:hessian⟧: "Both operators are invertible.") -/

omit [Finite V] in
/-- **The ramified Roe pairing operator `1 + U + U⁻¹` is injective** (`U = σ₂`) — the
`Both operators are invertible.` clause of ⟦prop:hessian⟧, feeding perfectness of the ramified
pairing `λ((1+U+U⁻¹)d)` (`mixedB_R_pairing_ramified`).  A thin re-export of the shared
`sigma2_pairing_operator_injective`: the operator is the presentation-independent tame datum
`U = σ₂`, identical for `Γ_A` and `Γ_R`, so the `Γ_A`-side nondegeneracy engine is reused verbatim
(no `Γ_R`-specific proof).  The unramified operator of ⟦eq:pairingoperator⟧ is the identity. -/
theorem pairingR_operator_injective (t : Marking C) (hV₂ : ∀ v : V, v + v = 0) :
    Function.Injective (fun v : V => v + t.sigma2 • v + t.sigma2⁻¹ • v) :=
  sigma2_pairing_operator_injective t hV₂

/-! ### Stress test: the commutator cancellation (the note's `U = 1` collapse)

Evaluate the `cR` central ledger entry `heisMarking_cR_z` in the split regime (`σ₂` acts
trivially, e.g. any tame marking whose `σ` acts through an odd-order quotient — R5's split Sanity
markings): the two commutator terms `λ(U⁻¹d) + λ(Ud)` collapse to `λ(d) + λ(d) = 0`, exactly the
note's "these two commutator terms cancel".  This isolates why the split pairing is the honest
diagonal `λ(d)` and the ramified one is not. -/
omit [Finite V] in
theorem heisMarking_cR_z_split_cancels (t : Marking C) (d : V) (lam : ElemDual V)
    (hx1 : ∀ v : V, t.x₁ • v = v) (hU : ∀ v : V, t.sigma2 • v = v) :
    (heisMarking t (x1Supported d) (x1Supported lam)).cR.z = 0 := by
  rw [heisMarking_cR_z t d lam hx1, show t.sigma2⁻¹ • d = d from inv_smul_eq_iff.mpr (hU d).symm,
    hU d]
  exact CharTwo.add_self_eq_zero (lam d)

end HessianRowR

end FoxH

end GQ2

/-! ### Paper-tag ledger (Roe note `paper/roe-presentation-verification.tex`; hand-maintained)

  * Proposition 5.2 (Mixed Hessian) = ⟦prop:hessian⟧ — the assembled pairing
    `mixedB_R_pairing_split`/`mixedB_R_pairing_ramified` (display ⟦eq:pairingoperator⟧
    `(d,λ) ↦ λ(d)` resp. `λ((1+U+U⁻¹)d)`); the wild summands are
    `heisMarking_wildValueR_z`/`heisMarking_wildValueR_z_ramified`; the per-factor ledger is
    `heisMarking_conjP_x0_sigma_inv_z` (`(x₀^σ)⁻¹`), `heisMarking_aR_z` (`aR`), `heisMarking_x1_sq_z`
    (`x₁²`, the diagonal `λ(d)`), `heisMarking_cR_z` (`[x₁,x₁^{σ₂}]`, `λ(Ud)+λ(U⁻¹d)`).
  * "Both operators are invertible." = `pairingR_operator_injective`
    (`= sigma2_pairing_operator_injective`, reused verbatim — `U = σ₂` is presentation-independent).
  * Lemma 4.3 scalar Gram ⟦eq:scalarform⟧ (`⟨…⟩ = ac' + ca' + dd'`, the honest diagonal `dd'` this
    `λ(d)` feeds) = ticket R25's `mixedB_cocycle_R` (on `mixedB_R`, `GQ2.Roe.FoxBasic`).
  * Proposition 6.1 (Base word expansion) = ⟦prop:quadratic⟧/⟦eq:QR⟧ (`q(d)`,
    `q(d) + b_q(d, U⁻¹d)`, polar `b_R(d,d') = b_q(d,(1+U+U⁻¹)d')`) = ticket R27's, building on the
    `heisMarking_cR_z` symplectic entry and `pairingR_operator_injective` here.
-/
