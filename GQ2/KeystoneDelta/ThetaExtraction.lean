/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.KeystoneDelta.AtomCalculus

/-!
# The splitting lemma, `ξ`-calculus and the `Θ`-extraction

Split off from `GQ2.KeystoneDelta` (design §§3–5).  This file provides:

* **Stage B** — the `V`-splitting lemma `exists_splitting_of_symm_zero_diag` (a symmetric
  zero-diagonal normalized 2-cocycle on a finite elementary-abelian 2-group is a coboundary);
* **Stage C.1** — the `ξ`-normalization lemmas and the cover-commutator = polar lemma
  (`xi_polar`);
* **Stage C.2** — the descended-cover cocycle `κfull` and the `Θ`-facts (`theta_facts`);
* **Stage C.3** — `Θ'`, the four-chase extraction (`theta'_decomp`) and the dual-crossed law
  for the edge `γκ` (`gammakap_dual_crossed`).

See `GQ2.KeystoneDelta` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

/-! ## Stage B: the `V`-splitting lemma (design §3)

A symmetric, zero-diagonal, normalized 2-cocycle on a finite elementary-abelian 2-group is a
coboundary: the twisted extension it classifies is an `𝔽₂`-vector space, so the projection has
a linear section, whose first coordinate is the splitting cochain. -/

section Splitting

/-- Carrier of the twisted extension `𝔽₂ ×_φ V` (`φ` a phantom parameter). -/
private structure TwExt {V : Type} (φ : V → V → ZMod 2) where
  /-- The central `𝔽₂`-coordinate. -/
  z : ZMod 2
  /-- The base `V`-coordinate. -/
  v : V

namespace TwExt

variable {V : Type} [AddCommGroup V] {φ : V → V → ZMod 2}

private instance : Zero (TwExt φ) := ⟨⟨0, 0⟩⟩
private instance : Add (TwExt φ) := ⟨fun p q => ⟨p.z + q.z + φ p.v q.v, p.v + q.v⟩⟩
private instance : Neg (TwExt φ) := ⟨fun p => p⟩

end TwExt

/-- **The splitting lemma** (design §3): a symmetric zero-diagonal normalized 2-cocycle on a
finite elementary-abelian 2-group is `∂g` for a normalized `g`. -/
theorem exists_splitting_of_symm_zero_diag {V : Type} [AddCommGroup V] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (φ : V → V → ZMod 2)
    (hcoc : ∀ v w x : V, φ (v + w) x + φ v w = φ v (w + x) + φ w x)
    (hsymm : ∀ v w : V, φ v w = φ w v) (hdiag : ∀ v : V, φ v v = 0)
    (hzl : ∀ v : V, φ 0 v = 0) :
    ∃ g : V → ZMod 2, g 0 = 0 ∧ ∀ v w : V, φ v w = g (v + w) + g v + g w := by
  classical
  have hzr : ∀ v : V, φ v 0 = 0 := fun v => (hsymm v 0).trans (hzl v)
  have hE2 : ∀ p : TwExt φ, p + p = (0 : TwExt φ) := by
    intro p
    show TwExt.mk (p.z + p.z + φ p.v p.v) (p.v + p.v) = TwExt.mk 0 0
    rw [hdiag, hV2, add_zero, CharTwo.add_self_eq_zero]
  letI : AddCommGroup (TwExt φ) :=
    { add_assoc := fun p q r => by
        show TwExt.mk (p.z + q.z + φ p.v q.v + r.z + φ (p.v + q.v) r.v) (p.v + q.v + r.v)
          = TwExt.mk (p.z + (q.z + r.z + φ q.v r.v) + φ p.v (q.v + r.v)) (p.v + (q.v + r.v))
        refine congrArg₂ TwExt.mk ?_ (add_assoc _ _ _)
        linear_combination hcoc p.v q.v r.v
      zero_add := fun p => by
        show TwExt.mk (0 + p.z + φ 0 p.v) (0 + p.v) = p
        rw [hzl, add_zero, zero_add, zero_add]
      add_zero := fun p => by
        show TwExt.mk (p.z + 0 + φ p.v 0) (p.v + 0) = p
        rw [hzr, add_zero, add_zero, add_zero]
      add_comm := fun p q => by
        show TwExt.mk (p.z + q.z + φ p.v q.v) (p.v + q.v)
          = TwExt.mk (q.z + p.z + φ q.v p.v) (q.v + p.v)
        rw [hsymm, add_comm p.z q.z, add_comm p.v q.v]
      neg_add_cancel := fun p => hE2 p
      nsmul := nsmulRec
      zsmul := zsmulRec }
  haveI : Module (ZMod 2) (TwExt φ) := AddCommGroup.zmodModule (fun p => by
    rw [two_nsmul]; exact hE2 p)
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact hV2 v)
  -- the projection is linear and surjective, so it splits over the field `𝔽₂`
  let π : TwExt φ →ₗ[ZMod 2] V :=
    { toFun := fun p => p.v
      map_add' := fun p q => rfl
      map_smul' := fun c p => by
        show (c • p).v = (RingHom.id (ZMod 2)) c • p.v
        rw [RingHom.id_apply]
        rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
        · rw [zero_smul, zero_smul]
          rfl
        · rw [one_smul, one_smul] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun v => ⟨⟨0, v⟩, rfl⟩
  obtain ⟨sec, hsec⟩ := π.exists_rightInverse_of_surjective hsurj
  have hsecv : ∀ v : V, (sec v).v = v := fun v => LinearMap.congr_fun hsec v
  refine ⟨fun v => (sec v).z, ?_, ?_⟩
  · exact congrArg TwExt.z (map_zero sec)
  · intro v w
    show φ v w = (sec (v + w)).z + (sec v).z + (sec w).z
    have hz : (sec (v + w)).z = (sec v).z + (sec w).z + φ (sec v).v (sec w).v :=
      congrArg TwExt.z (map_add sec v w)
    rw [hsecv, hsecv] at hz
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hz

end Splitting

/-! ## Stage C, part 1: `ξ`-normalization and the cover-commutator = polar lemma (design §5) -/

section XiCalculus

variable {DD : DescData D} (Dsc : Descent D)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem xi_one_left (x : Bg ⧸ D.T) : xi Dsc (1, x) = 0 := by
  show ccZsign Dsc (s0 Dsc 1 * s0 Dsc x * (s0 Dsc (1 * x))⁻¹) = 0
  rw [s0_one, one_mul, one_mul, mul_inv_cancel, ccZsign_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem xi_one_right (x : Bg ⧸ D.T) : xi Dsc (x, 1) = 0 := by
  show ccZsign Dsc (s0 Dsc x * s0 Dsc 1 * (s0 Dsc (x * 1))⁻¹) = 0
  rw [s0_one, mul_one, mul_one, mul_inv_cancel, ccZsign_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Kernel elements of `descP` are involutions. -/
theorem ker_sq_one {x : covQ Dsc} (hx : x ∈ (descP Dsc).ker) : x * x = 1 := by
  rcases descKerCases Dsc hx with rfl | rfl
  · rw [one_mul]
  · exact zbar_sq Dsc

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The diagonal of `ξ` at an involution is the section-square sign. -/
theorem xi_diag_sq {x : Bg ⧸ D.T} (hx : x * x = 1) :
    xi Dsc (x, x) = ccZsign Dsc (s0 Dsc x * s0 Dsc x) := by
  show ccZsign Dsc (s0 Dsc x * s0 Dsc x * (s0 Dsc (x * x))⁻¹) = _
  rw [hx, s0_one, inv_one, mul_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The cover-commutator = polar lemma** (design §5): the symmetry defect of `ξ` on the
`V`-fibre is the polar form of the descended square map `q̄`. -/
theorem xi_polar (v w : DD.Vmod) :
    xi Dsc (iV DD (Multiplicative.ofAdd v), iV DD (Multiplicative.ofAdd w))
      + xi Dsc (iV DD (Multiplicative.ofAdd w), iV DD (Multiplicative.ofAdd v))
      = polar DD.qbar v w := by
  classical
  set a := iV DD (Multiplicative.ofAdd v) with ha_def
  set b := iV DD (Multiplicative.ofAdd w) with hb_def
  -- the `iV`-image is elementary abelian
  have hmul : ∀ x y : DD.Vmod, iV DD (Multiplicative.ofAdd x) * iV DD (Multiplicative.ofAdd y)
      = iV DD (Multiplicative.ofAdd (x + y)) := fun x y => (iV_ofAdd_add DD x y).symm
  have hcomm : a * b = b * a := by
    rw [ha_def, hb_def, hmul, hmul, add_comm]
  have hsq : ∀ x : DD.Vmod,
      iV DD (Multiplicative.ofAdd x) * iV DD (Multiplicative.ofAdd x) = 1 := by
    intro x
    rw [hmul, Vmod_exp2 DD x, ofAdd_zero, map_one]
  have hab : a * b = iV DD (Multiplicative.ofAdd (v + w)) := by rw [ha_def, hb_def, hmul]
  have hab2 : (a * b) * (a * b) = 1 := by rw [hab]; exact hsq (v + w)
  -- kernel elements
  have hX : s0 Dsc a * s0 Dsc b * (s0 Dsc (a * b))⁻¹ ∈ (descP Dsc).ker :=
    defect_mem_ker Dsc a b
  set X := s0 Dsc a * s0 Dsc b * (s0 Dsc (a * b))⁻¹ with hX_def
  have hcomm' : s0 Dsc b * s0 Dsc a * (s0 Dsc b)⁻¹ * (s0 Dsc a)⁻¹ ∈ (descP Dsc).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, s0_sect, s0_sect]
    rw [← hcomm]
    group
  set C' := s0 Dsc b * s0 Dsc a * (s0 Dsc b)⁻¹ * (s0 Dsc a)⁻¹ with hC'_def
  -- step 1: the symmetry defect is `ccZsign C'`
  have hstep1 : xi Dsc (a, b) + xi Dsc (b, a) = ccZsign Dsc C' := by
    have hY : s0 Dsc b * s0 Dsc a * (s0 Dsc (b * a))⁻¹ = C' * X := by
      rw [← hcomm, hC'_def, hX_def]
      group
    show ccZsign Dsc X + ccZsign Dsc (s0 Dsc b * s0 Dsc a * (s0 Dsc (b * a))⁻¹) = _
    rw [hY, ccZsign_mul Dsc hcomm' hX]
    have hchar : ∀ x y : ZMod 2, x + (y + x) = y := by decide
    exact hchar _ _
  -- step 2: the square relation `s0(ab)² = C' · s0a² · s0b²`
  have hsq_ker : ∀ (x : Bg ⧸ D.T), x * x = 1 → s0 Dsc x * s0 Dsc x ∈ (descP Dsc).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, map_mul, s0_sect, hx]
  have hstep2 : s0 Dsc (a * b) * s0 Dsc (a * b)
      = C' * (s0 Dsc a * s0 Dsc a) * (s0 Dsc b * s0 Dsc b) := by
    have hs0ab : s0 Dsc (a * b) = X⁻¹ * (s0 Dsc a * s0 Dsc b) := by rw [hX_def]; group
    have hX2 : X * X = 1 := ker_sq_one Dsc hX
    have hC'c : ∀ y : covQ Dsc, C' * y = y * C' := fun y => ker_central Dsc hcomm' y
    calc s0 Dsc (a * b) * s0 Dsc (a * b)
        = X⁻¹ * (s0 Dsc a * s0 Dsc b) * (X⁻¹ * (s0 Dsc a * s0 Dsc b)) := by rw [hs0ab]
      _ = X⁻¹ * X⁻¹ * (s0 Dsc a * s0 Dsc b * (s0 Dsc a * s0 Dsc b)) := by
          rw [show X⁻¹ * (s0 Dsc a * s0 Dsc b) * (X⁻¹ * (s0 Dsc a * s0 Dsc b))
              = X⁻¹ * ((s0 Dsc a * s0 Dsc b) * X⁻¹) * (s0 Dsc a * s0 Dsc b) from by group,
            ← ker_central Dsc (inv_mem hX) (s0 Dsc a * s0 Dsc b)]
          group
      _ = s0 Dsc a * s0 Dsc b * (s0 Dsc a * s0 Dsc b) := by
          rw [show X⁻¹ * X⁻¹ = (X * X)⁻¹ from by group, hX2, inv_one, one_mul]
      _ = s0 Dsc a * (s0 Dsc b * s0 Dsc a) * s0 Dsc b := by group
      _ = s0 Dsc a * (C' * (s0 Dsc a * s0 Dsc b)) * s0 Dsc b := by
          rw [show s0 Dsc b * s0 Dsc a = C' * (s0 Dsc a * s0 Dsc b) from by
            rw [hC'_def]; group]
      _ = (s0 Dsc a * C') * (s0 Dsc a * s0 Dsc b) * s0 Dsc b := by group
      _ = (C' * s0 Dsc a) * (s0 Dsc a * s0 Dsc b) * s0 Dsc b := by rw [← hC'c (s0 Dsc a)]
      _ = C' * (s0 Dsc a * s0 Dsc a) * (s0 Dsc b * s0 Dsc b) := by group
  -- step 3: apply signs and `xi_diag`
  have hdva : xi Dsc (a, a) = ccZsign Dsc (s0 Dsc a * s0 Dsc a) := xi_diag_sq Dsc (hsq v)
  have hdvb : xi Dsc (b, b) = ccZsign Dsc (s0 Dsc b * s0 Dsc b) := xi_diag_sq Dsc (hsq w)
  have hdab : xi Dsc (a * b, a * b) = ccZsign Dsc (s0 Dsc (a * b) * s0 Dsc (a * b)) :=
    xi_diag_sq Dsc hab2
  have hsign2 : ccZsign Dsc (s0 Dsc (a * b) * s0 Dsc (a * b))
      = ccZsign Dsc C' + ccZsign Dsc (s0 Dsc a * s0 Dsc a)
        + ccZsign Dsc (s0 Dsc b * s0 Dsc b) := by
    rw [hstep2, ccZsign_mul Dsc (mul_mem hcomm' (hsq_ker a (by rw [ha_def]; exact hsq v)))
      (hsq_ker b (by rw [hb_def]; exact hsq w)),
      ccZsign_mul Dsc hcomm' (hsq_ker a (by rw [ha_def]; exact hsq v))]
  -- assemble: `q̄`-values via `xi_diag`
  have hqa : xi Dsc (a, a) = DD.qbar v := by rw [ha_def]; exact xi_diag DD Dsc v
  have hqb : xi Dsc (b, b) = DD.qbar w := by rw [hb_def]; exact xi_diag DD Dsc w
  have hqab : xi Dsc (a * b, a * b) = DD.qbar (v + w) := by
    rw [hab]; exact xi_diag DD Dsc (v + w)
  have hCval : ccZsign Dsc C' = DD.qbar (v + w) + DD.qbar v + DD.qbar w := by
    have h1 : DD.qbar (v + w) = ccZsign Dsc C' + DD.qbar v + DD.qbar w := by
      rw [← hqab, hdab, hsign2, ← hdva, ← hdvb, hqa, hqb]
    linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1
  rw [hstep1, hCval]
  rfl

end XiCalculus

/-! ## Stage C, part 2: the descended-cover cocycle and the `Θ`-extraction (design §4) -/

section Theta

variable {DD : DescData D} (σ : DD.C0 →* Bg ⧸ D.T) (Dsc : Descent D)

/-- The descended central class `κfull`, transported to the raw semidirect pairs. -/
noncomputable def kfull (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  xi Dsc (jmap DD σ p, jmap DD σ q)

variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `κfull` satisfies the raw Serre identity for `pmul`. -/
theorem kfull_serre (p q r : DD.Vmod × DD.C0) :
    kfull σ Dsc q r + kfull σ Dsc p (pmul q r)
      = kfull σ Dsc (pmul p q) r + kfull σ Dsc p q := by
  unfold kfull
  rw [← jmap_mul hσ q r, ← jmap_mul hσ p q]
  exact xi_cocycle Dsc (jmap DD σ p) (jmap DD σ q) (jmap DD σ r)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
omit hσ in
private theorem kfull_pone_left (q : DD.Vmod × DD.C0) : kfull σ Dsc pone q = 0 := by
  unfold kfull
  rw [jmap_pone]
  exact xi_one_left Dsc _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
omit hσ in
private theorem kfull_pone_right (p : DD.Vmod × DD.C0) : kfull σ Dsc p pone = 0 := by
  unfold kfull
  rw [jmap_pone]
  exact xi_one_right Dsc _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `m_c(0) = 0` for an equivariant factor-set datum. -/
theorem m_zero {q : DD.Vmod → ZMod 2} {dat : FactorSet DD.C0 DD.Vmod}
    (hdat : IsEquivariantFactorSet q dat) (cc : DD.C0) : dat.m cc 0 = 0 := by
  have h := hdat.m_quad cc 0 0
  rw [add_zero, smul_zero, hdat.f_zero_left] at h
  have hchar : ∀ a : ZMod 2, a + a + a = 0 + 0 → a = 0 := by decide
  exact hchar _ h

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The raw Serre identity for `kappa0` of any equivariant factor-set datum. -/
theorem kappa0_serre {q : DD.Vmod → ZMod 2} {dat : FactorSet DD.C0 DD.Vmod}
    (hdat : IsEquivariantFactorSet q dat) (p q' r : DD.Vmod × DD.C0) :
    kappa0 dat q' r + kappa0 dat p (pmul q' r)
      = kappa0 dat (pmul p q') r + kappa0 dat p q' := by
  show (dat.f q'.1 (q'.2 • r.1) + dat.m q'.2 r.1)
      + (dat.f p.1 (p.2 • (q'.1 + q'.2 • r.1)) + dat.m p.2 (q'.1 + q'.2 • r.1))
    = (dat.f (p.1 + p.2 • q'.1) ((p.2 * q'.2) • r.1) + dat.m (p.2 * q'.2) r.1)
      + (dat.f p.1 (p.2 • q'.1) + dat.m p.2 q'.1)
  rw [mul_smul, smul_add]
  have hf := hdat.f_cocycle p.1 (p.2 • q'.1) (p.2 • (q'.2 • r.1))
  have hmm := hdat.m_mul p.2 q'.2 r.1
  have hmq := hdat.m_quad p.2 q'.1 (q'.2 • r.1)
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hf + hmm + hmq

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `pmul`-coboundary of a 1-cochain satisfies the raw Serre identity. -/
theorem pcob_serre (G : DD.Vmod × DD.C0 → ZMod 2) (p q r : DD.Vmod × DD.C0) :
    (G (pmul q r) + G q + G r) + (G (pmul p (pmul q r)) + G p + G (pmul q r))
      = (G (pmul (pmul p q) r) + G (pmul p q) + G r)
        + (G (pmul p q) + G p + G q) := by
  rw [pmul_assoc]
  have hchar : ∀ a b c d e f : ZMod 2,
      (a + b + c) + (d + e + a) = (d + f + c) + (f + e + b) := by decide
  exact hchar _ _ _ _ _ _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **`Θ := κfull + κ⁰`** has zero diagonal and symmetric `V×V`-part. -/
theorem theta_facts :
    (∀ v : DD.Vmod, kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (v, 1)
        + kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (v, 1) = 0) ∧
      (∀ v w : DD.Vmod,
        (kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
            + kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (w, 1))
          = (kfull σ Dsc ((w, 1) : DD.Vmod × DD.C0) (v, 1)
            + kappa0 DD.dat ((w, 1) : DD.Vmod × DD.C0) (v, 1))) := by
  have hjV : ∀ v : DD.Vmod, jmap DD σ ((v, 1) : DD.Vmod × DD.C0)
      = iV DD (Multiplicative.ofAdd v) := by
    intro v
    show iV DD (Multiplicative.ofAdd v) * σ 1 = iV DD (Multiplicative.ofAdd v)
    rw [map_one, mul_one]
  constructor
  · intro v
    have h1 : kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (v, 1) = DD.qbar v := by
      unfold kfull
      rw [hjV]
      exact xi_diag DD Dsc v
    have h2 : kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (v, 1) = DD.qbar v := by
      show DD.dat.f v ((1 : DD.C0) • v) + DD.dat.m 1 v = DD.qbar v
      rw [one_smul, DD.hdat.f_diag, DD.hdat.m_one, add_zero]
    rw [h1, h2]
    exact CharTwo.add_self_eq_zero _
  · intro v w
    have hk : kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
        + kfull σ Dsc ((w, 1) : DD.Vmod × DD.C0) (v, 1) = polar DD.qbar v w := by
      unfold kfull
      rw [hjV, hjV]
      exact xi_polar Dsc v w
    have hp : kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (w, 1)
        + kappa0 DD.dat ((w, 1) : DD.Vmod × DD.C0) (v, 1) = polar DD.qbar v w := by
      show (DD.dat.f v ((1 : DD.C0) • w) + DD.dat.m 1 w)
          + (DD.dat.f w ((1 : DD.C0) • v) + DD.dat.m 1 v) = polar DD.qbar v w
      rw [one_smul, one_smul, DD.hdat.m_one, DD.hdat.m_one, add_zero, add_zero]
      exact DD.hdat.f_polar v w
    have hchar : ∀ a b c d P : ZMod 2, a + b = P → c + d = P → a + c = b + d := by decide
    exact hchar _ _ _ _ _ hk hp

end Theta

/-! ## Stage C, part 3: `Θ'` and the four-chase extraction (design §4) -/

section ThetaPrime

variable {DD : DescData D} (σ : DD.C0 →* Bg ⧸ D.T) (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

/-- `Θ := κfull + κ⁰`. -/
noncomputable def theta (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  kfull σ Dsc p q + kappa0 DD.dat p q

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem theta_serre (p q r : DD.Vmod × DD.C0) :
    theta σ Dsc q r + theta σ Dsc p (pmul q r)
      = theta σ Dsc (pmul p q) r + theta σ Dsc p q := by
  have h1 := kfull_serre σ Dsc hσ p q r
  have h2 := kappa0_serre (DD := DD) DD.hdat p q r
  unfold theta
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta_pone_left (q : DD.Vmod × DD.C0) : theta σ Dsc pone q = 0 := by
  unfold theta
  rw [kfull_pone_left]
  show 0 + (DD.dat.f 0 ((1 : DD.C0) • q.1) + DD.dat.m 1 q.1) = 0
  rw [DD.hdat.f_zero_left, DD.hdat.m_one, add_zero, add_zero]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta_pone_right (p : DD.Vmod × DD.C0) : theta σ Dsc p pone = 0 := by
  unfold theta
  rw [kfull_pone_right]
  show 0 + (DD.dat.f p.1 (p.2 • (0 : DD.Vmod)) + DD.dat.m p.2 0) = 0
  rw [smul_zero, DD.hdat.f_zero_right, m_zero (DD := DD) DD.hdat, add_zero, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The splitting data for `Θ|_{V×V}` exists. -/
theorem gkappa_exists : ∃ g : DD.Vmod → ZMod 2, g 0 = 0 ∧
    ∀ v w : DD.Vmod, theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
      = g (v + w) + g v + g w := by
  refine exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)) ?_ ?_ ?_ ?_
  · -- cocycle: the Serre identity at `V`-triples
    intro v w x
    have hs := theta_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (w, 1) (x, 1)
    have pm1 : pmul ((w, 1) : DD.Vmod × DD.C0) (x, 1) = (w + x, 1) := by
      unfold pmul
      rw [one_smul, one_mul]
    have pm2 : pmul ((v, 1) : DD.Vmod × DD.C0) (w, 1) = (v + w, 1) := by
      unfold pmul
      rw [one_smul, one_mul]
    rw [pm1, pm2] at hs
    linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs
  · -- symmetric
    exact (theta_facts σ Dsc).2
  · -- zero diagonal
    exact (theta_facts σ Dsc).1
  · -- left-normalized
    exact fun v => theta_pone_left σ Dsc ((v, 1) : DD.Vmod × DD.C0)

/-- The `V×V`-splitting cochain `gκ`. -/
noncomputable def gkappa : DD.Vmod → ZMod 2 :=
  Classical.choose (gkappa_exists σ Dsc hσ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gkappa_zero : gkappa σ Dsc hσ 0 = 0 :=
  (Classical.choose_spec (gkappa_exists σ Dsc hσ)).1

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem gkappa_split (v w : DD.Vmod) :
    theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
      = gkappa σ Dsc hσ (v + w) + gkappa σ Dsc hσ v + gkappa σ Dsc hσ w :=
  (Classical.choose_spec (gkappa_exists σ Dsc hσ)).2 v w

/-- **`Θ'`** — `Θ` with the `V×V`-part killed by the `gκ`-coboundary. -/
noncomputable def theta' (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  theta σ Dsc p q
    + (gkappa σ Dsc hσ (pmul p q).1 + gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ q.1)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem theta'_serre (p q r : DD.Vmod × DD.C0) :
    theta' σ Dsc hσ q r + theta' σ Dsc hσ p (pmul q r)
      = theta' σ Dsc hσ (pmul p q) r + theta' σ Dsc hσ p q := by
  have h1 := theta_serre σ Dsc hσ p q r
  have h2 := pcob_serre (DD := DD) (fun x => gkappa σ Dsc hσ x.1) p q r
  unfold theta'
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta'_VV (v w : DD.Vmod) :
    theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (w, 1) = 0 := by
  unfold theta'
  have pm : pmul ((v, 1) : DD.Vmod × DD.C0) (w, 1) = (v + w, 1) := by
    unfold pmul
    rw [one_smul, one_mul]
  rw [pm, gkappa_split σ Dsc hσ v w]
  exact CharTwo.add_self_eq_zero _

/-! ### The extraction data -/

/-- `uκ(v, cc) := Θ'((v,1),(0,cc))`. -/
noncomputable def ukap (v : DD.Vmod) (cc : DD.C0) : ZMod 2 :=
  theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (0, cc)

/-- `δκ(cc, dd) := Θ'((0,cc),(0,dd))` — the scalar part of the descended class. -/
noncomputable def dkap (cc dd : DD.C0) : ZMod 2 :=
  theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (0, dd)

/-- `γκ`-raw: `Θ'((0,cc),(w,1))`. -/
noncomputable def gkraw (cc : DD.C0) (w : DD.Vmod) : ZMod 2 :=
  theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, 1)

/-- **The edge `γκ`** of the descended class (`gammaEdge`-calibrated). -/
noncomputable def gammakap (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  gkraw σ Dsc hσ cc (cc⁻¹ • x) + ukap σ Dsc hσ (x) (cc)

/- `pmul`-evaluations used in the chases. -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem pm_v1_0c (v : DD.Vmod) (cc : DD.C0) :
    pmul ((v, 1) : DD.Vmod × DD.C0) (0, cc) = (v, cc) := by
  unfold pmul
  rw [smul_zero, add_zero, one_mul]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem pm_0c_wd (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    pmul ((0, cc) : DD.Vmod × DD.C0) (w, dd) = (cc • w, cc * dd) := by
  unfold pmul
  rw [zero_add]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
private theorem pm_v1_x1 (v x : DD.Vmod) (ee : DD.C0) :
    pmul ((v, 1) : DD.Vmod × DD.C0) (x, ee) = (v + x, ee) := by
  unfold pmul
  rw [one_smul, one_mul]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E2: `Θ'` on a `V`-row. -/
theorem chaseE2 (v x : DD.Vmod) (ee : DD.C0) :
    theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (x, ee)
      = ukap σ Dsc hσ (v + x) (ee) + ukap σ Dsc hσ (x) (ee) := by
  have hs := theta'_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (x, 1) (0, ee)
  rw [pm_v1_0c, pm_v1_x1] at hs
  have hVV := theta'_VV σ Dsc hσ v x
  unfold ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs + hVV

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E1: peel the `V`-coordinate off the first argument. -/
theorem chaseE1 (v : DD.Vmod) (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, dd)
        + theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (cc • w, cc * dd)
        + ukap σ Dsc hσ (v) (cc) := by
  have hs := theta'_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (0, cc) (w, dd)
  rw [pm_v1_0c, pm_0c_wd] at hs
  unfold ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E3: peel the `V`-coordinate off the second argument. -/
theorem chaseE3 (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, dd)
      = ukap σ Dsc hσ (w) (dd)
        + theta' σ Dsc hσ ((cc • w, cc) : DD.Vmod × DD.C0) (0, dd)
        + gkraw σ Dsc hσ cc w := by
  have hs := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, 1) (0, dd)
  have pmA : pmul ((0, cc) : DD.Vmod × DD.C0) (w, 1) = (cc • w, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  have pmB : pmul ((w, 1) : DD.Vmod × DD.C0) (0, dd) = (w, dd) := pm_v1_0c w dd
  rw [pmA, pmB] at hs
  unfold ukap gkraw
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E4: reduce the mixed corner to `δκ` and `uκ`. -/
theorem chaseE4 (cc dd : DD.C0) (y : DD.Vmod) :
    theta' σ Dsc hσ ((y, cc) : DD.Vmod × DD.C0) (0, dd)
      = dkap σ Dsc hσ cc dd + ukap σ Dsc hσ (y) (cc * dd) + ukap σ Dsc hσ (y) (cc) := by
  have hs := theta'_serre σ Dsc hσ ((y, 1) : DD.Vmod × DD.C0) (0, cc) (0, dd)
  have pmA : pmul ((0, cc) : DD.Vmod × DD.C0) (0, dd) = (0, cc * dd) := by
    unfold pmul
    rw [smul_zero, add_zero]
  rw [pm_v1_0c, pmA] at hs
  unfold dkap ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The extraction** (design §4): `Θ'` in `Γγκ + inf δκ + ∂uκ` normal form (raw values). -/
theorem theta'_decomp (v : DD.Vmod) (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = (gkraw σ Dsc hσ cc w + ukap σ Dsc hσ (cc • w) (cc))
        + dkap σ Dsc hσ cc dd
        + (ukap σ Dsc hσ (v + cc • w) (cc * dd) + ukap σ Dsc hσ (v) (cc)
            + ukap σ Dsc hσ (w) (dd)) := by
  have h1 := chaseE1 σ Dsc hσ v cc w dd
  have h3 := chaseE3 σ Dsc hσ cc w dd
  have h4 := chaseE4 σ Dsc hσ cc dd (cc • w)
  have h2 := chaseE2 σ Dsc hσ v (cc • w) (cc * dd)
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h3 + h4 + h2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E5: `gkraw` additivity up to `uκ`-corrections. -/
theorem chaseE5 (cc : DD.C0) (a b : DD.Vmod) :
    gkraw σ Dsc hσ cc (a + b)
      = gkraw σ Dsc hσ cc a + gkraw σ Dsc hσ cc b
        + ukap σ Dsc hσ (cc • (a + b)) (cc) + ukap σ Dsc hσ (cc • b) (cc)
        + ukap σ Dsc hσ (cc • a) (cc) := by
  -- E5a
  have hsA := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (a, 1) (b, 1)
  have pmA : pmul ((a, 1) : DD.Vmod × DD.C0) (b, 1) = (a + b, 1) := pm_v1_x1 a b 1
  have pmB : pmul ((0, cc) : DD.Vmod × DD.C0) (a, 1) = (cc • a, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  rw [pmA, pmB] at hsA
  have hVV := theta'_VV σ Dsc hσ a b
  -- E5b
  have hsB := theta'_serre σ Dsc hσ ((cc • a, 1) : DD.Vmod × DD.C0) (0, cc) (b, 1)
  have pmC : pmul ((0, cc) : DD.Vmod × DD.C0) (b, 1) = (cc • b, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  rw [pm_v1_0c, pmC] at hsB
  -- E5c
  have hsC := chaseE2 σ Dsc hσ (cc • a) (cc • b) cc
  unfold gkraw ukap at *
  rw [show cc • (a + b) = cc • a + cc • b from smul_add cc a b]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero]))
    hsA + hVV + hsB + hsC

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γκ` is additive. -/
theorem gammakap_add (cc : DD.C0) (x y : DD.Vmod) :
    gammakap σ Dsc hσ cc (x + y)
      = gammakap σ Dsc hσ cc x + gammakap σ Dsc hσ cc y := by
  unfold gammakap
  have h5 := chaseE5 σ Dsc hσ cc (cc⁻¹ • x) (cc⁻¹ • y)
  rw [show cc • (cc⁻¹ • x + cc⁻¹ • y) = x + y from by
      rw [smul_add, smul_inv_smul, smul_inv_smul],
    smul_inv_smul, smul_inv_smul] at h5
  rw [show cc⁻¹ • (x + y) = cc⁻¹ • x + cc⁻¹ • y from smul_add cc⁻¹ x y]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h5

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E6: the `gkraw`-composition law. -/
theorem chaseE6 (cc dd : DD.C0) (w : DD.Vmod) :
    gkraw σ Dsc hσ (cc * dd) w
      = gkraw σ Dsc hσ dd w + gkraw σ Dsc hσ cc (dd • w)
        + ukap σ Dsc hσ (dd • w) (dd) + ukap σ Dsc hσ (cc • dd • w) (cc * dd)
        + ukap σ Dsc hσ (cc • dd • w) (cc) := by
  -- E6a
  have hsA := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (0, dd) (w, 1)
  have pmA : pmul ((0, dd) : DD.Vmod × DD.C0) (w, 1) = (dd • w, dd) := by
    unfold pmul
    rw [zero_add, mul_one]
  have pmB : pmul ((0, cc) : DD.Vmod × DD.C0) (0, dd) = (0, cc * dd) := by
    unfold pmul
    rw [smul_zero, add_zero]
  rw [pmA, pmB] at hsA
  -- E6b
  have hsB := chaseE3 σ Dsc hσ cc (dd • w) dd
  -- E6c
  have hsC := chaseE4 σ Dsc hσ cc dd (cc • dd • w)
  unfold gkraw dkap ukap at *
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hsA + hsB + hsC

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The dual-crossed law for `γκ`** (design §6): `γκ(cc·dd)(x) = γκ(cc)(x) + γκ(dd)(cc⁻¹•x)`. -/
theorem gammakap_dual_crossed (cc dd : DD.C0) (x : DD.Vmod) :
    gammakap σ Dsc hσ (cc * dd) x
      = gammakap σ Dsc hσ cc x + gammakap σ Dsc hσ dd (cc⁻¹ • x) := by
  unfold gammakap
  have h6 := chaseE6 σ Dsc hσ cc dd ((cc * dd)⁻¹ • x)
  have harg1 : dd • (cc * dd)⁻¹ • x = cc⁻¹ • x := by
    rw [mul_inv_rev, mul_smul, smul_inv_smul]
  rw [harg1, smul_inv_smul] at h6
  rw [show (cc * dd)⁻¹ • x = dd⁻¹ • cc⁻¹ • x from by rw [mul_inv_rev, mul_smul]] at h6 ⊢
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h6

end ThetaPrime

end AffineTLift

end SectionEight

end GQ2
