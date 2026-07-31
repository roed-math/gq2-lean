/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.Dyadic.Word.Stokes
public import GQ2.Dyadic.Word.WordCoh
public import GQ2.SectionSix
public import GQ2.OrbitData

@[expose] public section

/-!
# Dyadic campaign, ticket WW4 (Hessian half): `PWord` extraspecial evaluation

The word-side half of the affine-phase interface (board WW4 spec; SD1 memo §6 is the ratified
baseline; packet §§6–7 and `lem:extraspecialconnecting`):

1. **The extraspecial (`CentExt κ⁰`-route) denotation** of a reflected word (`hessEvalZ`):
   `PWord.evalZ` at the **zero-fibre lifted marking** `WordCoh.lift μ c` into the central
   extension `CentExt c` of an arbitrary finite level `L` by a normalized 2-cocycle.  This
   follows WW3's pattern exactly — **no new recursion**: the `CentExt` product law *is* the
   packet's central product rule, so the rules hold definitionally (`hessEvalZ_mul_fib`,
   `hessEvalZ_inv_fib`) and every F2 naturality theorem applies verbatim.  The transport
   mechanism is WW3's free-group bridge (`hessEvalZ_eq_lift` via `heisToFree` /
   `evalZ_eq_lift_heisToFree`), and the fibre value is literally MC-OB's relator obstruction
   (`hessRelZ_eq_relZ`), so the four `relZ` laws (base/comap/add/zero) apply unchanged.

2. **The base central cocycle `κ⁰_q` module-side** (`kappa0Cocycle`): `GQ2.kappa0` of an
   equivariant factor-set datum, as a `GQ2.Dyadic.WordCoh.TwoCocycle` on the semidirect
   carrier `GQ2.SectionSix.SemiProd C V` — the generalization of the `Γ_A` evaluation route
   `GQ2/GaussZ/RelatorGammaA.lean:223` (`QZero_eq_relZPair_kappa0`): the base determinant
   form `Q⁰` is a relator value in the concrete extension `CentExt κ⁰`.  Wave-2 branch lanes
   evaluate their words here at graph-type markings; the certificate layer (Phase.lean /
   the `HessianCertificate` section below, milestone 3) records the resulting quadratic.

3. **The κ_q⁰ normalization laws** — `class2.py`'s warning made formal: *"the polarization
   alone cannot see the Bockstein diagonal."*  The polar/cross data of the extension is
   normalization-independent, but the **diagonal** is pinned by the factor set:
   `kappa0Cocycle_diag_fibre` (`κ⁰((v,1),(v,1)) = q v`, from `f_diag`) and the extraspecial
   square law `hessSq_of_fibre` (`p² = incl (q p.base.1)` over the fibre).  This is the seam
   through which `stokesGram` diagonals must be matched (WW3's Bockstein-diagonal caveat,
   `GQ2/Dyadic/Word/Stokes.lean` scalar hooks): the `β(u⁻¹)`-rule on this side is
   `hessEvalZ_inv_fib`.

4. **The ℤ/4-centre lift-level boundary (ticket S1.T; "It is 4, not 2")**: one central
   `𝔽₂`-step doubles the lift level (`centExt_pow_eq_one_of_base_pow`, constant 2), but on
   the twisted path the kernel over the lower group `C` is the whole extraspecial group,
   which has exponent 4 — `kappa0_pow_eq_one_of_snd_pow` proves the constant-4 law
   `p.base.2 ^ n = 1 → p ^ (4·n) = 1`, and `stress_lift_level_four_sharp` pins sharpness
   (an element with lower order 1 and genuine order 4).  Stated and **proved**, not left as
   a hypothesis.

5. **The WMP no-affine-shift corollary** (`heisJetZero_mul_right_jet`), stated against
   WW3's `heisJetZero` family as the board log mandates: a jet-zero (shadow) right factor
   contributes no primal offset, no dual offset and no cross term — hence no affine shift
   (the shift vector of packet Lem 6.1 is computed from the first jet, so the unique polar
   representative is unchanged; the central values then cancel in char 2 by WW3's
   `heisJetZero_sq_z`).  This is the corollary the shadow-theorem memo (§4, "the shadow
   contributes no primal or dual offset when P3 holds, so it contributes no affine shift")
   notes "nobody has written down".

## Design notes

* **Dedup ledger**: `kappa0Cocycle` is the `WordCoh`-typed sibling of
  `GQ2.SectionEight.AffineTLift.kappa0Cocycle` (`GQ2/GaussZ/RelatorGammaA.lean`, a
  `WordCoh2.TwoCocycle` in a non-`module` file — not importable here; the module rule).
  Same underlying function `GQ2.kappa0` (`GQ2/OrbitData.lean`, module-style), same Lemma 6.1
  associativity proof.  This mirrors MC-OB's ratified third-copy discipline for the
  central-extension algebra itself (`GQ2/Dyadic/Word/WordCoh.lean`, `## Deduplication`).
* The carrier is `GQ2.SectionSix.SemiProd C V` (module-style), not `AffineTLift.Sd`
  (non-module twin); the two have definitionally equal group laws.
* Only the fibre coordinate of `hessEvalZ` is new information: the base coordinate is the
  plain `PWord.evalZ` denotation (`hessEvalZ_base`, one `map_evalZ` line — the recorded
  WW1↔WW3 bridge pattern).
* Milestone plan (commit-early): this file lands in two milestones — (M1) the evaluation
  route + κ⁰ laws above; (M3, after `Phase.lean`) the `HessianCertificate` layer and the
  frozen-row worked examples.

## Axiom prints (recorded at commit time)

Every headline prints **exactly the standard three** (`propext`, `Classical.choice`,
`Quot.sound`) — verified via `#print axioms` for `hessEvalZ_eq_lift`, `hessRelZ_eq_relZ`,
`kappa0Cocycle`, `kappa0Cocycle_diag_fibre`, `hessSq_of_fibre`,
`centExt_pow_eq_one_of_base_pow`, `kappa0_pow_eq_one_of_snd_pow`,
`heisJetZero_mul_right_jet`, `stress_lift_level_four_sharp`.  No sorries, no new axioms;
the only `decide`s are kernel `decide`s in `𝔽₂` case splits and the stress pins.  The
`local instance`s live in the stress section only (WW3's doesn't-export idiom).

Module-style: all four imports are module-style.
-/

namespace GQ2.Dyadic

open GQ2.FoxH GQ2.SectionSix

/-! ## The extraspecial denotation of a reflected word

`PWord.evalZ` at the zero-fibre lifted marking `WordCoh.lift μ c : X → CentExt c`.  No new
recursion: the `CentExt` group law is the second-order central rule, so the per-constructor
equations are `rfl` and F2 naturality (`PWord.map_evalZ`) applies verbatim. -/

section ExtraspecialEval

variable {X : Type*} {L : Type} [Group L]

/-- **The extraspecial evaluation** of a reflected word: `PWord.evalZ` at the zero-fibre
lifted marking into `CentExt c`.  The `PWord` twin of the `relZPair`-evaluation of
`GQ2/GaussZ/RelatorGammaA.lean:223`, over an arbitrary finite level `L` and normalized
2-cocycle `c`. -/
noncomputable def hessEvalZ (μ : X → L) (c : WordCoh.TwoCocycle L) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) : PWord X → WordCoh.CentExt c :=
  PWord.evalZ (WordCoh.lift μ c) E E₂

variable (μ : X → L) (c : WordCoh.TwoCocycle L) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

@[simp] theorem hessEvalZ_gen (i : X) :
    hessEvalZ μ c E E₂ (.gen i) = ((μ i, 0) : WordCoh.CentExt c) := rfl

@[simp] theorem hessEvalZ_mul (u v : PWord X) :
    hessEvalZ μ c E E₂ (.mul u v) = hessEvalZ μ c E E₂ u * hessEvalZ μ c E E₂ v := rfl

@[simp] theorem hessEvalZ_inv (u : PWord X) :
    hessEvalZ μ c E E₂ (.inv u) = (hessEvalZ μ c E E₂ u)⁻¹ := rfl

/-- **The central product rule** (the κ-side of WW3's `heisEvalZ_mul_z`): the fibre of a
product denotation is the sum of the fibres plus the cocycle value at the bases. -/
theorem hessEvalZ_mul_fib (u v : PWord X) :
    (hessEvalZ μ c E E₂ (.mul u v)).fib
      = (hessEvalZ μ c E E₂ u).fib + (hessEvalZ μ c E E₂ v).fib
        + c.κ (hessEvalZ μ c E E₂ u).base (hessEvalZ μ c E E₂ v).base := rfl

/-- **The central inverse rule** — the κ-side Bockstein seam (WW3's `heisEvalZ_inv_z`):
`β(u⁻¹) = β(u) + κ(ū, ū⁻¹)`.  This is the rule through which `stokesGram` diagonal
comparisons must pass (the Bockstein-diagonal caveat of the Stokes scalar hooks). -/
theorem hessEvalZ_inv_fib (u : PWord X) :
    (hessEvalZ μ c E E₂ (.inv u)).fib
      = (hessEvalZ μ c E E₂ u).fib
        + c.κ (hessEvalZ μ c E E₂ u).base (hessEvalZ μ c E E₂ u).base⁻¹ := rfl

/-- The base coordinate is the plain denotation: one `map_evalZ` line under the
`CentExt.proj` projection (the recorded WW1↔WW3 bridge pattern, κ-side). -/
theorem hessEvalZ_base (w : PWord X) :
    (hessEvalZ μ c E E₂ w).base = PWord.evalZ μ E E₂ w :=
  PWord.map_evalZ (WordCoh.CentExt.proj c) (WordCoh.lift μ c) E E₂ w

/-- **The free-group transport** (WW3's mechanism, reused verbatim): the extraspecial
denotation is `FreeGroup.lift` of the lifted marking at the resolved free word.  This is
what lets the frozen `Fin n`-generic layers act on `hessEvalZ`-values. -/
theorem hessEvalZ_eq_lift (w : PWord X) :
    hessEvalZ μ c E E₂ w = FreeGroup.lift (WordCoh.lift μ c) (heisToFree E E₂ w) :=
  evalZ_eq_lift_heisToFree _ E E₂ w

/-- **The evaluated Hessian** of a reflected word: the fibre coordinate of the extraspecial
denotation.  At a graph-type marking of a branch word this is the base determinant quadratic
`Q⁰` — the generalization of `QZero_eq_relZPair_kappa0`'s right-hand side. -/
noncomputable def hessRelZ (μ : X → L) (c : WordCoh.TwoCocycle L) (E : Zhat → ℤ)
    (E₂ : ℤ_[2] → ℤ) (w : PWord X) : ZMod 2 :=
  (hessEvalZ μ c E E₂ w).fib

/-- The evaluated Hessian **is** MC-OB's relator obstruction of the reflected natural word —
definitionally.  All four `relZ` laws (`relZ_base`, `relZ_comap`, `relZ_add`, `relZ_zero`)
apply to `hessRelZ` through this identification. -/
theorem hessRelZ_eq_relZ (w : PWord X) :
    hessRelZ μ c E E₂ w = WordCoh.relZ (WordCoh.NatWord.ofPWord w E E₂) μ c := rfl

/-- Level-change naturality for the evaluated Hessian (the `relZPair_comap` step of the
`Γ_A` route, rank-generically). -/
theorem hessRelZ_comap {L' : Type} [Group L'] (μ' : X → L') (φ : L' →* L) (w : PWord X) :
    hessRelZ (fun k ↦ φ (μ' k)) c E E₂ w = hessRelZ μ' (c.comap φ) E E₂ w := by
  rw [hessRelZ_eq_relZ, hessRelZ_eq_relZ]
  exact WordCoh.relZ_comap _ _ _ _

/-- Additivity of the evaluated Hessian in the cocycle. -/
theorem hessRelZ_add (c₁ c₂ : WordCoh.TwoCocycle L) (w : PWord X) :
    hessRelZ μ (c₁ + c₂) E E₂ w = hessRelZ μ c₁ E E₂ w + hessRelZ μ c₂ E E₂ w := by
  rw [hessRelZ_eq_relZ, hessRelZ_eq_relZ, hessRelZ_eq_relZ]
  exact WordCoh.relZ_add _ _ _ _

/-- The evaluated Hessian of the split cocycle vanishes. -/
theorem hessRelZ_zero (w : PWord X) :
    hessRelZ μ (WordCoh.zeroCocycle : WordCoh.TwoCocycle L) E E₂ w = 0 := by
  rw [hessRelZ_eq_relZ]
  exact WordCoh.relZ_zero _ _

end ExtraspecialEval

/-! ## The base central cocycle `κ⁰_q` on `V ⋊ C`, module-side

`GQ2.kappa0` of an equivariant factor-set datum, packaged as a `WordCoh.TwoCocycle` on
`GQ2.SectionSix.SemiProd C V`.  The cocycle identity is Lemma 6.1's "associativity of `E_f`"
(`lem:extraspecialconnecting`), assembled from `f_cocycle`, `m_quad`, `m_mul` exactly as in
the non-module twin `GQ2.SectionEight.AffineTLift.kappa0Cocycle`. -/

section Kappa0

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]

/-- First component of a `SemiProd` product (component form of `SemiProd.mul_def`). -/
@[simp] theorem semiProd_mul_fst (a b : SemiProd C V) : (a * b).1 = a.1 + a.2 • b.1 := rfl

/-- Second component of a `SemiProd` product. -/
@[simp] theorem semiProd_mul_snd (a b : SemiProd C V) : (a * b).2 = a.2 * b.2 := rfl

/-- The lower projection `V ⋊ C →* C`. -/
def sdSnd : SemiProd C V →* C where
  toFun p := p.2
  map_one' := rfl
  map_mul' _ _ := rfl

@[simp] theorem sdSnd_apply (p : SemiProd C V) : sdSnd p = p.2 := rfl

variable {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

/-- **The base central cocycle `κ⁰_q` as a normalized `WordCoh.TwoCocycle` on `V ⋊ C`**
(eq. (61); Lemma 6.1's associativity from the `IsEquivariantFactorSet` clauses).  The
module-side generalization of the `Γ_A` route's `kappa0Cocycle`
(`GQ2/GaussZ/RelatorGammaA.lean`, dedup note in the module docstring). -/
noncomputable def kappa0Cocycle : WordCoh.TwoCocycle (SemiProd C V) where
  κ p r := dat.f p.1 (p.2 • r.1) + dat.m p.2 r.1
  norm := by
    show dat.f (0 : V) ((1 : C) • (0 : V)) + dat.m (1 : C) (0 : V) = 0
    rw [smul_zero, hdat.f_zero_left, hdat.m_one, add_zero]
  cocyc := by
    intro p r s
    show dat.f p.1 (p.2 • r.1) + dat.m p.2 r.1
        + (dat.f (p * r).1 ((p * r).2 • s.1) + dat.m (p * r).2 s.1)
      = dat.f p.1 (p.2 • (r * s).1) + dat.m p.2 (r * s).1
        + (dat.f r.1 (r.2 • s.1) + dat.m r.2 s.1)
    simp only [semiProd_mul_fst, semiProd_mul_snd]
    have h1 := hdat.f_cocycle p.1 (p.2 • r.1) ((p.2 * r.2) • s.1)
    have h2 := hdat.m_quad p.2 r.1 (r.2 • s.1)
    have h3 := hdat.m_mul p.2 r.2 s.1
    have hsm : p.2 • (r.1 + r.2 • s.1) = p.2 • r.1 + (p.2 * r.2) • s.1 := by
      rw [smul_add, mul_smul]
    have hsm2 : p.2 • (r.2 • s.1) = (p.2 * r.2) • s.1 := (mul_smul p.2 r.2 s.1).symm
    rw [hsm]
    rw [hsm2] at h2
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1 + h2 + h3

@[simp] theorem kappa0Cocycle_κ (p r : SemiProd C V) :
    (kappa0Cocycle dat hdat).κ p r = dat.f p.1 (p.2 • r.1) + dat.m p.2 r.1 := rfl

/-- The packaged cocycle is `GQ2.kappa0` of the datum, on the nose. -/
theorem kappa0Cocycle_κ_eq_kappa0 (p r : SemiProd C V) :
    (kappa0Cocycle dat hdat).κ p r = kappa0 dat (p.1, p.2) (r.1, r.2) := rfl

/-- **The κ_q⁰ diagonal normalization** (`class2.py`: "the polarization alone cannot see the
Bockstein diagonal"): on the `V`-fibre the diagonal of the cocycle **is** the quadratic form
`q` — this is `f_diag`, the datum the polar form cannot recover. -/
theorem kappa0Cocycle_diag_fibre (v : V) :
    (kappa0Cocycle dat hdat).κ ((v, 1) : SemiProd C V) ((v, 1) : SemiProd C V) = q v := by
  show dat.f v ((1 : C) • v) + dat.m (1 : C) v = q v
  rw [one_smul, hdat.m_one, add_zero, hdat.f_diag]

/-- **The extraspecial square law**: over the `V`-fibre of the base, squaring lands in the
centre with value the quadratic form — `x² = ι(q(x̄))`.  This is the evaluation-route form
of the κ_q⁰ normalization: the diagonal of any Gram comparison must pass through it. -/
theorem hessSq_of_fibre (hV2 : ∀ v : V, v + v = 0)
    (p : WordCoh.CentExt (kappa0Cocycle dat hdat)) (hp : p.base.2 = 1) :
    p * p = WordCoh.CentExt.incl _ (q p.base.1) := by
  refine WordCoh.CentExt.ext ?_ ?_
  · show p.base * p.base = 1
    refine Prod.ext ?_ ?_
    · show p.base.1 + p.base.2 • p.base.1 = 0
      rw [hp, one_smul]
      exact hV2 _
    · show p.base.2 * p.base.2 = 1
      rw [hp, one_mul]
  · show p.fib + p.fib + (dat.f p.base.1 (p.base.2 • p.base.1) + dat.m p.base.2 p.base.1)
      = q p.base.1
    rw [hp, one_smul, hdat.m_one, add_zero, hdat.f_diag, CharTwo.add_self_eq_zero, zero_add]

/-- A central `𝔽₂`-inclusion squares to `1` in any `CentExt`. -/
theorem centExt_incl_mul_self {L : Type*} [Group L] {c : WordCoh.TwoCocycle L} (z : ZMod 2) :
    WordCoh.CentExt.incl c z * WordCoh.CentExt.incl c z = 1 := by
  refine WordCoh.CentExt.ext ?_ ?_
  · show (1 : L) * 1 = 1
    rw [one_mul]
  · show z + z + c.κ 1 1 = 0
    rw [c.norm, add_zero, CharTwo.add_self_eq_zero]

/-- **The untwisted lift-level constant is 2** (S1.4's board rule): one central `𝔽₂`-step
doubles the lift level — `x̄ⁿ = 1` forces `x^{2n} = 1` in any `CentExt`. -/
theorem centExt_pow_eq_one_of_base_pow {L : Type*} [Group L] {c : WordCoh.TwoCocycle L}
    (p : WordCoh.CentExt c) {n : ℕ} (hn : p.base ^ n = 1) : p ^ (2 * n) = 1 := by
  have hbase : (p ^ n).base = 1 := by
    calc (p ^ n).base = WordCoh.CentExt.proj c (p ^ n) := rfl
      _ = (WordCoh.CentExt.proj c p) ^ n := map_pow _ _ _
      _ = 1 := hn
  have hincl := (WordCoh.CentExt.base_eq_one_iff (p ^ n)).mp hbase
  rw [mul_comm 2 n, pow_mul, sq, hincl]
  exact centExt_incl_mul_self _

/-- **The ℤ/4-centre lift-level constant is 4 on the twisted path** (ticket S1.T; `class2.py`:
*"It is 4, not 2."*).  In the κ⁰-extension the kernel over the lower group `C` is the whole
extraspecial group, whose exponent is 4 (`hessSq_of_fibre`: fibre squares hit the centre with
value `q`), so a lower-order bound only gives `p^{4n} = 1`.  Sharpness is
`stress_lift_level_four_sharp`. -/
theorem kappa0_pow_eq_one_of_snd_pow (hV2 : ∀ v : V, v + v = 0)
    (p : WordCoh.CentExt (kappa0Cocycle dat hdat)) {n : ℕ} (hn : p.base.2 ^ n = 1) :
    p ^ (4 * n) = 1 := by
  have hfib2 : (p ^ n).base.2 = 1 := by
    calc (p ^ n).base.2
        = sdSnd (WordCoh.CentExt.proj (kappa0Cocycle dat hdat) (p ^ n)) := rfl
      _ = sdSnd ((WordCoh.CentExt.proj (kappa0Cocycle dat hdat) p) ^ n) := by rw [map_pow]
      _ = (sdSnd (WordCoh.CentExt.proj (kappa0Cocycle dat hdat) p)) ^ n := map_pow _ _ _
      _ = 1 := hn
  have hsq := hessSq_of_fibre dat hdat hV2 (p ^ n) hfib2
  have h4 : (p ^ n) ^ 4 = 1 := by
    have h2 : (p ^ n) ^ 2 = WordCoh.CentExt.incl _ (q (p ^ n).base.1) := by
      rw [sq]
      exact hsq
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, h2, sq]
    exact centExt_incl_mul_self _
  calc p ^ (4 * n) = (p ^ n) ^ 4 := by rw [mul_comm, pow_mul]
    _ = 1 := h4

end Kappa0

/-! ## The WMP no-affine-shift corollary

Stated against WW3's `heisJetZero` family, as the board log mandates.  The shadow-theorem
memo (§4) notes: *"The shadow contributes no primal or dual offset when P3 holds, so it
contributes no affine shift — but that is a corollary nobody has written down."*  Here it
is: a jet-zero right factor leaves the entire first jet — hence the linear form `ℓ` of the
affine Gauss translation, hence packet Lem 6.1's unique polar representative `y` — unchanged,
and adds only its own central value (which cancels against its twin in char 2 by WW3's
`heisJetZero_sq_z`). -/

section ShadowJet

variable {C : Type*} [Group C] {A : Type*} [AddCommGroup A] [DistribMulAction C A]

/-- **No affine shift from a shadow factor**: multiplying by a jet-zero factor on the right
changes neither the primal offset nor the dual offset, and is centrally additive.  The
affine-phase data of the product is that of the left factor. -/
theorem heisJetZero_mul_right_jet (p r : HeisLift A C) (hr : r ∈ heisJetZero A C) :
    (p * r).a = p.a ∧ (p * r).l = p.l ∧ (p * r).z = p.z + r.z :=
  ⟨by rw [HeisLift.mul_a, hr.1, smul_zero, add_zero],
   by rw [HeisLift.mul_l, hr.2, smul_zero, add_zero],
   heisMul_z_of_a_eq_zero p r hr.1⟩

end ShadowJet

/-! ## Stress tests

Regression pins in the sense of plan §3 A1; nothing below is cited by a proof.  The `local`
instances do not export (WW3's idiom). -/

section StressTests

/-- The trivial action of `Multiplicative (ZMod 2)` on `ZMod 2`, for the pins below only. -/
local instance : DistribMulAction (Multiplicative (ZMod 2)) (ZMod 2) where
  smul _ a := a
  one_smul _ := rfl
  mul_smul _ _ _ := rfl
  smul_zero _ := rfl
  smul_add _ _ _ := rfl

local instance : DecidableEq (SemiProd (Multiplicative (ZMod 2)) (ZMod 2)) :=
  inferInstanceAs (DecidableEq (ZMod 2 × Multiplicative (ZMod 2)))

/-- The multiplication factor set on `𝔽₂`: the bilinear refinement of `q(v) = v` (= `v²`). -/
def stressDat : FactorSet (Multiplicative (ZMod 2)) (ZMod 2) where
  f v w := v * w
  m _ _ := 0

theorem stressDat_equivariant : IsEquivariantFactorSet (fun v : ZMod 2 ↦ v) stressDat := by
  constructor <;> decide

local instance :
    DecidableEq (WordCoh.CentExt (kappa0Cocycle stressDat stressDat_equivariant)) :=
  inferInstanceAs (DecidableEq ((ZMod 2 × Multiplicative (ZMod 2)) × ZMod 2))

/-- **Sharpness of the S1.T constant** (`class2.py`: the ratio genuinely attains 4): the
fibre element over `v = 1` has lower `C`-order 1, yet its square is the nontrivial central
element — order exactly 4, so the untwisted constant 2 is insufficient on the twisted path
and `kappa0_pow_eq_one_of_snd_pow`'s constant 4 is sharp. -/
theorem stress_lift_level_four_sharp :
    ∃ p : WordCoh.CentExt (kappa0Cocycle stressDat stressDat_equivariant),
      p.base.2 = 1 ∧ p * p ≠ 1 ∧ p ^ 4 = 1 := by
  refine ⟨(((1 : ZMod 2), (1 : Multiplicative (ZMod 2))), (0 : ZMod 2)), rfl, ?_, ?_⟩ <;>
    decide

/-- The constant fibre-generator marking for the pin below. -/
def stressMark (_ : Fin 2) : SemiProd (Multiplicative (ZMod 2)) (ZMod 2) :=
  ((1 : ZMod 2), (1 : Multiplicative (ZMod 2)))

/-- **Second-order rule pin**: the central product rule of `hessEvalZ` is the cocycle value
at the bases — at the stress datum, the product of the two fibre generators over `1` has
fibre `κ((1,1),(1,1)) = 1·1 = 1`. -/
theorem stress_hessEvalZ_mul_fib :
    (hessEvalZ stressMark (kappa0Cocycle stressDat stressDat_equivariant)
        (fun _ ↦ 0) (fun _ ↦ 0) (.mul (.gen 0) (.gen 1))).fib = 1 := by
  decide

end StressTests

end GQ2.Dyadic
