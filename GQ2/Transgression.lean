import GQ2.QuadraticFp2

/-!
# Transgression splitting for Lemma 6.21  (ticket P-15i — F-design)

Proof layer for `GQ2.SectionSix.lemma_6_21`: an extension `1 → V → B → C → 1` carrying a
global `𝔽₂`-valued 2-cocycle `ξ` whose fibre diagonal is a **nonsingular** quadratic form `q`
splits.  The paper's mechanism is the transgression formula `d₂(q) = B_q^♭ ∘ η` (eq. (116));
this file fixes a **direct cochain-level design** with no spectral sequences:

## The design

Fix a set-section `σ : C → B` with `σ 1 = 1` (`Function.surjInv` patched at `1`) and its
factor set `f c d := i⁻¹(σ c · σ d · σ (c·d)⁻¹) ∈ V` (values in `i.range = ker p`).  Define
the explicit **mixed cochain**

  `A : C → V → ZMod 2,  A c v := ξ (σ c, i (c⁻¹ • v)) + ξ (i v, σ c)`.

The **key transgression identity** (`key_transgression`, the cochain-level (116)) is

  `polar q (f c d) v = A c v + A d (c⁻¹ • v) + A (c*d) v`  —  i.e. `B_q^♭ ∘ f = δA` in the
  `C`-module `V^∨ = (V → 𝔽₂)` with `(c • φ) v = φ (c⁻¹ • v)`,

proved by expanding `hcocycle` on mixed triples from `{σ c, σ d, i v}` (the grind is
`lemma_6_22`-flavoured: `linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))`
over the cocycle instances, after normalizing arguments with `hconj`/`hσ`).

Since `B_q^♭ : V → (V → 𝔽₂)` is **bijective** (nonsingular + finiteness: `#Hom(V,𝔽₂) = #V`
for the elementary abelian `V`) and **`C`-equivariant** (polar conjugation-invariance), the
1-cochain `g := B_q^♭⁻¹ ∘ A c` satisfies `f = δg`, and `s c := i (g c)⁻¹ · σ c` is the
splitting homomorphism.

## Facts derived, not assumed

* `V` has exponent 2: `polar q (v+v) w = 2·polar q v w = 0` for all `w`, so `hns` forces
  `v + v = 0` (`exponent_two_of_nonsingular`, proved below).
* `ξ` is normalized at `1`: cocycle instances give `ξ(g,1) = ξ(1,k) = ξ(1,1)`, and
  `hξq` at `v = 0` gives `ξ(1,1) = q 0 = 0`.
* `q (c • v) = q v` and `polar q (c•v) (c•w) = polar q v w`: conjugating a 2-cocycle changes
  it by an explicit coboundary `δ(k_b)`; diagonals and antisymmetrizations of coboundaries
  vanish (`δa` is symmetric with zero diagonal), so both are conjugation-invariant.

## O-finish list (sorried below, routes in docstrings)

`bflat_bijective`, `polar_conj`, `factorSet_cocycle`, `key_transgression`, and the assembly
`splitting_of_global_cocycle` (= `lemma_6_21`'s statement; splice `:= by exact` when closed).
-/

namespace GQ2

namespace Transgression

open QuadraticFp2

variable {C : Type} [Group C] [Finite C]
variable {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
variable {B : Type} [Group B] [Finite B]

omit [Finite V] in
/-- Exponent 2 of the fibre is forced by nonsingularity (no `h2` hypothesis needed):
`polar q (v+v) w = 2·polar q v w = 0` for every `w`. -/
theorem exponent_two_of_nonsingular {q : V → ZMod 2} (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (v : V) : v + v = 0 := by
  by_contra hne
  obtain ⟨w, hw⟩ := hns (v + v) hne
  apply hw
  rw [hq.polar_add_left]
  exact CharTwo.add_self_eq_zero _

section Design

variable (p : B →* C) (hp : Function.Surjective p)
  (i : Multiplicative V →* B) (hi : Function.Injective i)
  (hrange : i.range = p.ker)
  (hconj : ∀ (b : B) (v : V), b * i (Multiplicative.ofAdd v) * b⁻¹
    = i (Multiplicative.ofAdd (p b • v)))
  (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
  (ξ : B × B → ZMod 2)
  (hcocycle : ∀ g h k : B, ξ (h, k) + ξ (g, h * k) = ξ (g * h, k) + ξ (g, h))
  (hξq : ∀ v : V, ξ (i (Multiplicative.ofAdd v), i (Multiplicative.ofAdd v)) = q v)

include hq hns in
/-- The polar adjoint `B_q^♭ : V → (V → 𝔽₂)` is bijective onto the additive functionals:
for every additive `φ : V → 𝔽₂` there is a unique `v` with `polar q v · = φ`.  The polar of a
nonsingular `q` on the finite elementary abelian `V` is a nondegenerate `𝔽₂`-bilinear form, so
`V ≃ₗ Module.Dual (ZMod 2) V` (`LinearMap.BilinForm.toDual`); additivity ⟹ `𝔽₂`-linearity via
`AddMonoidHom.toZModLinearMap`. -/
theorem bflat_bijective :
    ∀ φ : V → ZMod 2, (∀ x y, φ (x + y) = φ x + φ y) →
      ∃! v : V, ∀ w, polar q v w = φ w := by
  intro φ hφ
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact exponent_two_of_nonsingular hq hns v)
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  -- The polar form as a genuine `𝔽₂`-bilinear form (biadditivity ⟹ `ZMod 2`-linearity).
  let Bil : LinearMap.BilinForm (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2
      (AddMonoidHom.mk'
        (fun v => AddMonoidHom.toZModLinearMap 2
          (AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w')))
        (fun v v' => by
          ext w
          simp only [AddMonoidHom.coe_toZModLinearMap, AddMonoidHom.mk'_apply, LinearMap.add_apply]
          exact hq.polar_add_left v v' w))
  have hBilapp : ∀ v w, Bil v w = polar q v w := fun v w => rfl
  have hnd : Bil.Nondegenerate := by
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · by_contra hvne
      obtain ⟨w, hw⟩ := hns v hvne
      exact hw (by rw [← hBilapp]; exact hv w)
    · by_contra hvne
      obtain ⟨w, hw⟩ := hns v hvne
      exact hw (by rw [polar_comm, ← hBilapp]; exact hv w)
  let e := Bil.toDual hnd
  let φlin : Module.Dual (ZMod 2) V :=
    AddMonoidHom.toZModLinearMap 2 (AddMonoidHom.mk' φ hφ)
  have hφlinapp : ∀ w, φlin w = φ w := fun w => rfl
  refine ⟨e.symm φlin, ?_, ?_⟩
  · intro w
    rw [← hBilapp]
    show Bil ((Bil.toDual hnd).symm φlin) w = φ w
    rw [LinearMap.BilinForm.apply_toDual_symm_apply, hφlinapp]
  · intro v' hv'
    have hev' : e v' = φlin := by
      ext w
      show Bil v' w = φlin w
      rw [hBilapp, hv' w, hφlinapp]
    calc v' = e.symm (e v') := (e.symm_apply_apply v').symm
      _ = e.symm φlin := by rw [hev']

include hcocycle hξq hq hns in
/-- **The fibre antisymmetrization computes the polar**: for `u w : V`,
`polar q u w = ξ(iu, iw) + ξ(iw, iu)`.  Proof: expand `q(u+w) = ξ(iu·iw, iu·iw)` by the
cocycle on the (commuting, involutive) fibre elements `iu, iw`, using normalization
`ξ(1, ·) = 0`. -/
theorem polar_fibre (u w : V) :
    polar q u w = ξ (i (Multiplicative.ofAdd u), i (Multiplicative.ofAdd w))
                + ξ (i (Multiplicative.ofAdd w), i (Multiplicative.ofAdd u)) := by
  -- normalization `ξ(1, ·) = 0`
  have hone : ξ ((1 : B), (1 : B)) = 0 := by
    have h := hξq 0; rw [ofAdd_zero, map_one] at h; rw [h]; exact hq.map_zero
  have h1L : ∀ x : B, ξ ((1 : B), x) = 0 := by
    intro x
    have h := hcocycle 1 1 x
    rw [one_mul, one_mul, hone, add_zero, CharTwo.add_self_eq_zero] at h
    exact h.symm
  set a := i (Multiplicative.ofAdd u) with ha
  set b := i (Multiplicative.ofAdd w) with hb
  have hab : a * b = i (Multiplicative.ofAdd (u + w)) := by rw [ha, hb, ← map_mul, ← ofAdd_add]
  have hba : b * a = i (Multiplicative.ofAdd (u + w)) := by
    rw [ha, hb, ← map_mul, ← ofAdd_add, add_comm w u]
  have hcomm : a * b = b * a := by rw [hab, hba]
  have hbb : b * b = 1 := by
    rw [hb, ← map_mul, ← ofAdd_add, exponent_two_of_nonsingular hq hns w, ofAdd_zero, map_one]
  have hqu : q u = ξ (a, a) := (hξq u).symm
  have hqw : q w = ξ (b, b) := (hξq w).symm
  have hquw : q (u + w) = ξ (a * b, a * b) := by rw [hab]; exact (hξq (u + w)).symm
  have hbab : b * (a * b) = a := by rw [← mul_assoc, ← hcomm, mul_assoc, hbb, mul_one]
  have hc1 := hcocycle a b (a * b)
  rw [hbab] at hc1
  have hc2 := hcocycle b b a
  rw [hbb, ← hcomm, h1L] at hc2
  unfold polar
  rw [hquw, hqu, hqw]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc1 + hc2

include hcocycle in
/-- **Conjugation is a coboundary**: for a trivial-coefficient 2-cocycle `ξ`, conjugation by a
fixed `s` changes `ξ` by the coboundary of the 1-cochain `β_s(z) = ξ(s, z) + ξ(szs⁻¹, s)`:
`ξ(sxs⁻¹, sys⁻¹) + ξ(x, y) = β_s(x) + β_s(y) + β_s(xy)`.  (Three cocycle instances, char 2.) -/
theorem xi_conj_cobound (s x y : B) :
    ξ (s * x * s⁻¹, s * y * s⁻¹) + ξ (x, y)
      = (ξ (s, x) + ξ (s * x * s⁻¹, s)) + (ξ (s, y) + ξ (s * y * s⁻¹, s))
        + (ξ (s, x * y) + ξ (s * (x * y) * s⁻¹, s)) := by
  have hYs : s * y * s⁻¹ * s = s * y := by group
  have hXs : s * x * s⁻¹ * s = s * x := by group
  have hXY : s * x * s⁻¹ * (s * y * s⁻¹) = s * (x * y) * s⁻¹ := by group
  have hc1 := hcocycle (s * x * s⁻¹) (s * y * s⁻¹) s
  rw [hYs, hXY] at hc1
  have hc2 := hcocycle (s * x * s⁻¹) s y
  rw [hXs] at hc2
  have hc3 := hcocycle s x y
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hc1 + hc2 + hc3

include hp hconj hcocycle hξq hq hns in
/-- Conjugation-invariance of the polar form: `polar q (c•v) (c•w) = polar q v w`.  The polar is
the fibre antisymmetrization (`polar_fibre`), and by `xi_conj_cobound` conjugation changes `ξ`
by a coboundary; the antisymmetrization of a coboundary vanishes on the commuting fibre
elements, so the polar is `C`-invariant. -/
theorem polar_conj (c : C) (v w : V) :
    polar q (c • v) (c • w) = polar q v w := by
  obtain ⟨s, hs⟩ := hp c
  have hcv : ∀ z : V, i (Multiplicative.ofAdd (c • z))
      = s * i (Multiplicative.ofAdd z) * s⁻¹ := by
    intro z; have h := hconj s z; rw [hs] at h; exact h.symm
  rw [polar_fibre i q hq hns ξ hcocycle hξq (c • v) (c • w),
      polar_fibre i q hq hns ξ hcocycle hξq v w, hcv v, hcv w]
  set av := i (Multiplicative.ofAdd v) with hav
  set bw := i (Multiplicative.ofAdd w) with hbw
  have hcomm : av * bw = bw * av := by
    rw [hav, hbw]
    exact (Commute.all (Multiplicative.ofAdd v) (Multiplicative.ofAdd w)).map i
  have hAB := xi_conj_cobound ξ hcocycle s av bw
  have hBA := xi_conj_cobound ξ hcocycle s bw av
  rw [← hcomm] at hBA
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hAB + hBA

/-- The normalized section: `Function.surjInv hp` patched to send `1 ↦ 1`. -/
noncomputable def sigma : C → B := fun c =>
  letI := Classical.dec (c = 1)
  if c = 1 then 1 else Function.surjInv hp c

theorem sigma_spec (c : C) : p (sigma p hp c) = c := by
  unfold sigma
  split
  · rename_i h; rw [map_one, h]
  · exact Function.surjInv_eq hp c

/-- The factor set of `sigma`, valued in `V` through `i⁻¹` (well-defined:
`σc·σd·σ(cd)⁻¹ ∈ ker p = i.range`).  [O: define via `Function.invFun i` + `hrange`;
prove `i (ofAdd (factorSet c d)) = sigma c * sigma d * (sigma (c*d))⁻¹`.] -/
noncomputable def factorSet (c d : C) : V :=
  Multiplicative.toAdd (Function.invFun i
    (sigma p hp c * sigma p hp d * (sigma p hp (c * d))⁻¹))

include hp hrange in
/-- Defining property of the factor set: `i (ofAdd (f c d)) = σc · σd · σ(cd)⁻¹`
(well-defined since `σc·σd·σ(cd)⁻¹ ∈ ker p = i.range`). -/
theorem factorSet_spec (c d : C) :
    i (Multiplicative.ofAdd (factorSet p hp i c d))
      = sigma p hp c * sigma p hp d * (sigma p hp (c * d))⁻¹ := by
  unfold factorSet
  rw [ofAdd_toAdd]
  apply Function.invFun_eq
  rw [← MonoidHom.mem_range, hrange, MonoidHom.mem_ker]
  simp only [map_mul, map_inv, sigma_spec]
  group

include hp hi hrange hconj in
/-- The nonabelian 2-cocycle identity of the factor set:
`f c d + f (c*d) e = c • f d e + f c (d*e)`.  [associativity of `B` + `hconj` + `hi`.] -/
theorem factorSet_cocycle (c d e : C) :
    factorSet p hp i c d + factorSet p hp i (c * d) e
      = c • factorSet p hp i d e + factorSet p hp i c (d * e) := by
  -- conjugation form of the `C`-action after transporting through `i ∘ ofAdd`
  have hsmul : ∀ (cc : C) (X : V), i (Multiplicative.ofAdd (cc • X))
      = sigma p hp cc * i (Multiplicative.ofAdd X) * (sigma p hp cc)⁻¹ := fun cc X => by
    have h := hconj (sigma p hp cc) X
    rw [sigma_spec] at h
    exact h.symm
  have e1 := factorSet_spec p hp i hrange c d
  have e2 := factorSet_spec p hp i hrange (c * d) e
  have e3 := factorSet_spec p hp i hrange d e
  have e4 := factorSet_spec p hp i hrange c (d * e)
  -- prove the identity after applying the injection `i ∘ ofAdd`
  have key : i (Multiplicative.ofAdd (factorSet p hp i c d + factorSet p hp i (c * d) e))
      = i (Multiplicative.ofAdd (c • factorSet p hp i d e + factorSet p hp i c (d * e))) := by
    rw [ofAdd_add, map_mul, ofAdd_add, map_mul, e1, e2, hsmul, e3, e4, mul_assoc c d e]
    group
  simpa using congrArg Multiplicative.toAdd (hi key)

/-- The mixed transgression cochain `A c v = ξ(σc, i(c⁻¹•v)) + ξ(iv, σc)`. -/
noncomputable def mixedA (c : C) (v : V) : ZMod 2 :=
  ξ (sigma p hp c, i (Multiplicative.ofAdd (c⁻¹ • v)))
    + ξ (i (Multiplicative.ofAdd v), sigma p hp c)

include hp hrange hconj hcocycle hξq hq hns in
/-- **The key transgression identity** — the cochain-level eq. (116): `B_q^♭(f c d) = (δA)(c,d)`
as functionals on `V`, i.e. `polar q (f c d) v = A c v + A d (c⁻¹•v) + A (c*d) v`.  Proof: rewrite
the polar as a fibre antisymmetrization (`polar_fibre`), the factor set through `factorSet_spec`,
then close with a single char-2 `linear_combination` of nine `hcocycle` instances whose group
arguments are normalized by three `hconj`-conjugation moves (`m1`/`m2`/`m3`). -/
theorem key_transgression (c d : C) (v : V) :
    polar q (factorSet p hp i c d) v
      = mixedA p hp i ξ c v + mixedA p hp i ξ d (c⁻¹ • v) + mixedA p hp i ξ (c * d) v := by
  rw [polar_fibre i q hq hns ξ hcocycle hξq (factorSet p hp i c d) v,
      factorSet_spec p hp i hrange c d]
  simp only [mixedA, ← mul_smul, ← mul_inv_rev]
  -- normalization `ξ(1, ·) = 0 = ξ(·, 1)`
  have hone : ξ ((1 : B), (1 : B)) = 0 := by
    have h := hξq 0; rw [ofAdd_zero, map_one] at h; rw [h]; exact hq.map_zero
  have hone_left : ∀ x : B, ξ ((1 : B), x) = 0 := by
    intro x
    have h := hcocycle 1 1 x
    rw [one_mul, one_mul, hone, add_zero, CharTwo.add_self_eq_zero] at h
    exact h.symm
  have hone_right : ∀ y : B, ξ (y, (1 : B)) = 0 := by
    intro y
    have h := hcocycle y 1 1
    rw [mul_one, mul_one, hone, zero_add, CharTwo.add_self_eq_zero] at h
    exact h
  -- conjugation-move relations (`hconj` + `sigma_spec`), raw form
  have m1 : i (Multiplicative.ofAdd v) * sigma p hp c
      = sigma p hp c * i (Multiplicative.ofAdd (c⁻¹ • v)) := by
    have h := hconj (sigma p hp c) (c⁻¹ • v)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  have m2 : i (Multiplicative.ofAdd (c⁻¹ • v)) * sigma p hp d
      = sigma p hp d * i (Multiplicative.ofAdd ((c * d)⁻¹ • v)) := by
    have h := hconj (sigma p hp d) ((c * d)⁻¹ • v)
    rw [sigma_spec, mul_inv_rev, ← mul_smul, ← mul_assoc, mul_inv_cancel, one_mul] at h
    rw [← h]; group
  have m3 : sigma p hp (c * d) * i (Multiplicative.ofAdd ((c * d)⁻¹ • v))
      = i (Multiplicative.ofAdd v) * sigma p hp (c * d) := by
    have h := hconj (sigma p hp (c * d)) ((c * d)⁻¹ • v)
    rw [sigma_spec, ← mul_smul, mul_inv_cancel, one_smul] at h
    rw [← h]; group
  set a := sigma p hp c with ha
  set b := sigma p hp d with hb
  set m := sigma p hp (c * d) with hm
  set X := i (Multiplicative.ofAdd v) with hX
  set Xc := i (Multiplicative.ofAdd (c⁻¹ • v)) with hXc
  set Xcd := i (Multiplicative.ofAdd ((c * d)⁻¹ • v)) with hXcd
  -- derived moves
  have m4 : Xcd * m⁻¹ = m⁻¹ * X := by
    have h5 : Xcd = m⁻¹ * (X * m) := by rw [← m3]; group
    rw [h5]; group
  have m6 : X * (a * b) = a * b * Xcd := by
    rw [← mul_assoc, m1, mul_assoc, m2, ← mul_assoc]
  -- the nine cocycle instances, group arguments normalized by the moves
  have hA := hcocycle X (a * b) m⁻¹
  rw [m6] at hA
  have hB := hcocycle X a b
  rw [m1] at hB
  have hC := hcocycle a Xc b
  rw [m2] at hC
  have hD := hcocycle a b Xcd
  have hE := hcocycle (a * b) Xcd m⁻¹
  rw [m4] at hE
  have hF := hcocycle (a * b) m⁻¹ X
  have hG := hcocycle m Xcd m⁻¹
  rw [m4, m3] at hG
  have hH := hcocycle m m⁻¹ X
  rw [mul_inv_cancel, hone_left] at hH
  have hI := hcocycle X m m⁻¹
  rw [mul_inv_cancel, hone_right] at hI
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    hA + hB + hC + hD + hE + hF + hG + hH + hI

include hp hrange hconj hcocycle hξq hq hns in
/-- **The assembled splitting** (= `lemma_6_21`).  Structure of the proof:

* **Descent** (proved): from a `B_q^♭`-representable transgression primitive `g : C → V` — i.e.
  `polar q (f c d) v = polar q (g c) v + polar q (g d) (c⁻¹•v) + polar q (g (c*d)) v` — the
  polar-adjoint injectivity (`bflat_bijective`) together with `polar_conj` (equivariance) yields
  the `H²(C,V)`-coboundary equation `f c d = g c + c • g d + g (c*d)`.
* **Section** (proved): from that coboundary equation, `s c := i(ofAdd (g c))⁻¹ · σ c` is a
  monoid homomorphism sectioning `p` (`hconj` + `factorSet_spec` + fibre 2-torsion).

* **The remaining gap** (`sorry`, the transgression vanishing `d₂ q = 0`): that such a
  `B_q^♭`-representable `g` exists.  `key_transgression` proves `δ(mixedA) = B_q^♭ f` at cochain
  level, but `mixedA c` is **not additive** in `v` (defect `ξ(i(c⁻¹v),i(c⁻¹v')) + ξ(iv,iv')`, a
  nonzero symmetric zero-diagonal 2-cocycle on the fibre), so upgrading `mixedA` to a `V`-valued
  `g` is the genuine cohomological content — equivalent to the splitting, forced by the *global*
  lift `ξ` (its base cochain `ξ(σ·,σ·)`) rather than the cochain identity alone.  See the
  P-15i note in `docs/section67-extraction.md`. -/
theorem splitting_of_global_cocycle :
    ∃ s : C →* B, ∀ cc : C, p (s cc) = cc := by
  -- injectivity of the polar adjoint `B_q^♭`, from `bflat_bijective`
  have hinj : ∀ x y : V, (∀ w, polar q x w = polar q y w) → x = y := by
    intro x y hxy
    obtain ⟨z, _, hz⟩ := bflat_bijective q hq hns (fun w => polar q x w)
      (fun w w' => hq.polar_add_right x w w')
    rw [hz x fun w => rfl]
    exact (hz y fun w => (hxy w).symm).symm
  -- GAP: existence of a `B_q^♭`-representable transgression primitive (see docstring).
  obtain ⟨g, hg⟩ : ∃ g : C → V, ∀ (cc dd : C) (v : V),
      polar q (factorSet p hp i cc dd) v
        = polar q (g cc) v + polar q (g dd) (cc⁻¹ • v) + polar q (g (cc * dd)) v := by
    sorry
  -- descent: `f = δ g` in `H²(C, V)`
  have hcob : ∀ cc dd : C, factorSet p hp i cc dd = g cc + cc • g dd + g (cc * dd) := by
    intro cc dd
    apply hinj
    intro w
    have hmid : polar q (g dd) (cc⁻¹ • w) = polar q (cc • g dd) w := by
      have hpc := polar_conj p hp i hconj q hq hns ξ hcocycle hξq cc (g dd) (cc⁻¹ • w)
      rw [smul_smul, mul_inv_cancel, one_smul] at hpc
      exact hpc.symm
    rw [hg cc dd w, hmid, ← hq.polar_add_left, ← hq.polar_add_left]
  -- the splitting homomorphism `s cc = i(ofAdd (g cc))⁻¹ · σ cc`
  refine ⟨MonoidHom.mk' (fun cc => (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc) ?_, ?_⟩
  · intro cc dd
    have hmove : sigma p hp cc * (i (Multiplicative.ofAdd (g dd)))⁻¹
               = (i (Multiplicative.ofAdd (cc • g dd)))⁻¹ * sigma p hp cc := by
      have h := hconj (sigma p hp cc) (g dd)
      rw [sigma_spec] at h
      rw [← h]; group
    have hfs : sigma p hp cc * sigma p hp dd
             = i (Multiplicative.ofAdd (factorSet p hp i cc dd)) * sigma p hp (cc * dd) := by
      rw [factorSet_spec p hp i hrange cc dd]; group
    have hiprod : (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
                * i (Multiplicative.ofAdd (factorSet p hp i cc dd))
                = i (Multiplicative.ofAdd (g (cc * dd))) := by
      rw [hcob cc dd]
      simp only [← map_inv, ← map_mul]
      congr 1
      simp only [← ofAdd_neg, ← ofAdd_add]
      congr 1
      abel
    have htors : (i (Multiplicative.ofAdd (g (cc * dd))))⁻¹
               = i (Multiplicative.ofAdd (g (cc * dd))) := by
      have h2 : g (cc * dd) + g (cc * dd) = 0 := exponent_two_of_nonsingular hq hns _
      rw [← map_inv, ← ofAdd_neg, neg_eq_of_add_eq_zero_left h2]
    have key : (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
             * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
             = i (Multiplicative.ofAdd (g (cc * dd))) * sigma p hp (cc * dd) := by
      calc (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
              * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
          = (i (Multiplicative.ofAdd (g cc)))⁻¹
              * (sigma p hp cc * (i (Multiplicative.ofAdd (g dd)))⁻¹) * sigma p hp dd := by group
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹
              * ((i (Multiplicative.ofAdd (cc • g dd)))⁻¹ * sigma p hp cc) * sigma p hp dd := by
              rw [hmove]
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * (sigma p hp cc * sigma p hp dd) := by group
        _ = (i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * (i (Multiplicative.ofAdd (factorSet p hp i cc dd)) * sigma p hp (cc * dd)) := by
              rw [hfs]
        _ = ((i (Multiplicative.ofAdd (g cc)))⁻¹ * (i (Multiplicative.ofAdd (cc • g dd)))⁻¹
              * i (Multiplicative.ofAdd (factorSet p hp i cc dd))) * sigma p hp (cc * dd) := by group
        _ = i (Multiplicative.ofAdd (g (cc * dd))) * sigma p hp (cc * dd) := by rw [hiprod]
    show (i (Multiplicative.ofAdd (g (cc * dd))))⁻¹ * sigma p hp (cc * dd)
       = (i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc
         * ((i (Multiplicative.ofAdd (g dd)))⁻¹ * sigma p hp dd)
    rw [htors, key]
  · intro cc
    show p ((i (Multiplicative.ofAdd (g cc)))⁻¹ * sigma p hp cc) = cc
    rw [map_mul, map_inv, sigma_spec]
    have hker : i (Multiplicative.ofAdd (g cc)) ∈ p.ker := by
      rw [← hrange]; exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rw [MonoidHom.mem_ker] at hker
    rw [hker, inv_one, one_mul]

end Design

end Transgression

end GQ2
