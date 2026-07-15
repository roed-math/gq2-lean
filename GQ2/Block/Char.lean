/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionSeven
import GQ2.EvensKahn

/-!
# The index-2 character `blockLam` (scratch)

The `lam` input to `prop_7_4` / `mForm_of_qbar`: for a `Y`-normal `l ≤ R` of relative index 2,
the character `λ_l : ↥R → 𝔽₂` cutting `R ↠ R/l ≅ 𝔽₂`.  Additive (`blockLam_hom`), `Y`-conjugation
invariant (`blockLam_conj`), and nonzero (`blockLam_ne`).  Self-contained (no `prop_7_4`).
-/

namespace GQ2

open SectionSeven

open scoped Classical

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y}

/-- The index-2 character `λ_l : ↥R → 𝔽₂` cutting out `l ≤ R` (`R ↠ R/l ≅ 𝔽₂`):
`r ↦ 0` if `r ∈ l`, else `1`. -/
noncomputable def blockLam (B : MinimalBlock L) (l : Subgroup Y) : ↥B.frattiniK → ZMod 2 :=
  fun r => if (r : Y) ∈ l then 0 else 1

omit [Finite Y] in
theorem blockLam_eq_zero_iff (B : MinimalBlock L) (l : Subgroup Y) (r : ↥B.frattiniK) :
    blockLam B l r = 0 ↔ (r : Y) ∈ l := by
  unfold blockLam; split <;> simp_all

omit [Finite Y] in
/-- **Additivity**: `λ_l(r·r') = λ_l(r) + λ_l(r')` — from index-2 product membership
(`mul_mem_iff_of_index_two`). -/
theorem blockLam_hom (B : MinimalBlock L) (l : Subgroup Y)
    (hidx : (l.subgroupOf B.frattiniK).index = 2) (r r' : ↥B.frattiniK) :
    blockLam B l (r * r') = blockLam B l r + blockLam B l r' := by
  have hkey := mul_mem_iff_of_index_two hidx r r'
  simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul] at hkey
  unfold blockLam
  by_cases h1 : (r : Y) ∈ l <;> by_cases h2 : (r' : Y) ∈ l <;>
    simp only [Subgroup.coe_mul, hkey, h1, h2, iff_true, iff_false, iff_self,
      if_true, if_false] <;> decide

omit [Finite Y] in
/-- **`Y`-conjugation invariance**: `λ_l(y r y⁻¹) = λ_l(r)` — because `l` is `Y`-normal. -/
theorem blockLam_conj (B : MinimalBlock L) (l : Subgroup Y) (hlN : l.Normal)
    (hRN : B.frattiniK.Normal) (y : Y) (r : Y) (hr : r ∈ B.frattiniK) :
    blockLam B l ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = blockLam B l ⟨r, hr⟩ := by
  unfold blockLam
  by_cases hrl : r ∈ l
  · rw [if_pos (hlN.conj_mem r hrl y), if_pos hrl]
  · have hnot : y * r * y⁻¹ ∉ l := fun h => hrl (by
      have := hlN.conj_mem _ h y⁻¹
      rwa [show y⁻¹ * (y * r * y⁻¹) * y⁻¹⁻¹ = r from by group] at this)
    rw [if_neg hnot, if_neg hrl]

omit [Finite Y] in
/-- **Nonzero**: since `l < R`, some `r ∈ R∖l` has `λ_l(r) = 1`. -/
theorem blockLam_ne (B : MinimalBlock L) (l : Subgroup Y) (hlt : l < B.frattiniK) :
    blockLam B l ≠ 0 := by
  obtain ⟨r, hrR, hrl⟩ := SetLike.exists_of_lt hlt
  intro hcon
  have h0 := congrFun hcon ⟨r, hrR⟩
  rw [blockLam, if_neg hrl] at h0
  exact one_ne_zero h0

/-- Relative index is exactly 2 for a proper `l < R` with `relIndex ≤ 2` (the `DR` shape). -/
theorem relIndex_two_of_le (B : MinimalBlock L) (l : Subgroup Y)
    (hlR : l ≤ B.frattiniK) (hle2 : l.relIndex B.frattiniK ≤ 2) (hne : l ≠ B.frattiniK) :
    l.relIndex B.frattiniK = 2 := by
  have hne1 : l.relIndex B.frattiniK ≠ 1 := fun hcon =>
    absurd (le_antisymm hlR (Subgroup.relIndex_eq_one.mp hcon)) (ne_of_lt (hlR.lt_of_ne hne))
  have hne0 : l.relIndex B.frattiniK ≠ 0 := Subgroup.index_ne_zero_of_finite
  omega

/-! ## `hquad`: the descended form `qbar` is quadratic (biadditive polar) -/
omit [Finite Y] in
/-- Commutators of `K` land in `R = Φ(K)`: `[b,a] = b a b⁻¹ a⁻¹ ∈ R` — via
`a[b,a]a⁻¹ = (ab)²(a²b²)⁻¹ ∈ R` (squares, `hsq`) and `R`-normality. -/
theorem comm_mem_R_of_K (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK) {a b : Y} (ha : a ∈ B.K) (hb : b ∈ B.K) :
    b * a * b⁻¹ * a⁻¹ ∈ B.frattiniK := by
  have hconj : a * (b * a * b⁻¹ * a⁻¹) * a⁻¹
      = (a * b) * (a * b) * ((a * a) * (b * b))⁻¹ := by group
  have hmem : (a * b) * (a * b) * ((a * a) * (b * b))⁻¹ ∈ B.frattiniK :=
    B.frattiniK.mul_mem (hsq _ (B.K.mul_mem ha hb))
      (B.frattiniK.inv_mem (B.frattiniK.mul_mem (hsq a ha) (hsq b hb)))
  have hback := hRN.conj_mem _ (hconj ▸ hmem) a⁻¹
  rwa [show a⁻¹ * (a * (b * a * b⁻¹ * a⁻¹) * a⁻¹) * a⁻¹⁻¹ = b * a * b⁻¹ * a⁻¹ from by group]
    at hback

/-- **Packaging**: a `ZMod 2`-form on a `CommGroup` `G` that is normalized (`qm 1 = 0`) and has a
biadditive multiplicative polar form gives an `IsQuadraticFp2` form on `Additive G`. -/
theorem isQuadraticFp2_of_mul {G : Type*} [CommGroup G] (qm : G → ZMod 2)
    (h0 : qm 1 = 0)
    (hbiadd : ∀ u v w : G, qm (u * v * w) + qm (u * v) + qm w
      = (qm (u * w) + qm u + qm w) + (qm (v * w) + qm v + qm w)) :
    QuadraticFp2.IsQuadraticFp2 (fun v : Additive G => qm (Additive.toMul v)) := by
  have hpolar : ∀ a b : Additive G,
      QuadraticFp2.polar (fun v => qm (Additive.toMul v)) a b
        = qm (Additive.toMul a * Additive.toMul b) + qm (Additive.toMul a)
          + qm (Additive.toMul b) := fun _ _ => rfl
  refine ⟨h0, ?_, ?_⟩
  · intro u v w
    rw [hpolar, hpolar, hpolar]
    exact hbiadd (Additive.toMul u) (Additive.toMul v) (Additive.toMul w)
  · intro u v w
    rw [QuadraticFp2.polar_comm _ u (v + w), QuadraticFp2.polar_comm _ u v,
        QuadraticFp2.polar_comm _ u w, hpolar, hpolar, hpolar]
    exact hbiadd (Additive.toMul v) (Additive.toMul w) (Additive.toMul u)

section Quad

variable (B : MinimalBlock L) [(B.S.subgroupOf B.P).Normal]

omit [Finite Y] in
/-- `⟦a⟧·⟦b⟧ = ⟦ab⟧` on `P/S`, in the `K`-membership form (proof term `B.hKP (mul_mem …)`
matches `hspec`/`blockQbar_beta`). -/
theorem mkK_mul {a b : Y} (ha : a ∈ B.K) (hb : b ∈ B.K) :
    (QuotientGroup.mk ⟨a, B.hKP ha⟩ : ↥B.P ⧸ B.S.subgroupOf B.P) * QuotientGroup.mk ⟨b, B.hKP hb⟩
      = QuotientGroup.mk ⟨a * b, B.hKP (B.K.mul_mem ha hb)⟩ := by
  rw [← QuotientGroup.mk_mul]
  rfl

omit [Finite Y] in
/-- **The polar form is a conjugated commutator character**:
`β(⟦a⟧,⟦b⟧) = qbar(⟦a⟧⟦b⟧) + qbar⟦a⟧ + qbar⟦b⟧ = λ([b,a])` — the linchpin of biadditivity. -/
theorem blockQbar_beta (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩)
    (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hspec : ∀ (k : Y) (hk : k ∈ B.K),
      lam ⟨k * k, hsq k hk⟩ = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩))
    {a b : Y} (ha : a ∈ B.K) (hb : b ∈ B.K) :
    qbar (QuotientGroup.mk ⟨a, B.hKP ha⟩ * QuotientGroup.mk ⟨b, B.hKP hb⟩)
        + qbar (QuotientGroup.mk ⟨a, B.hKP ha⟩) + qbar (QuotientGroup.mk ⟨b, B.hKP hb⟩)
      = lam ⟨b * a * b⁻¹ * a⁻¹, comm_mem_R_of_K B hRN hsq ha hb⟩ := by
  rw [mkK_mul B ha hb, ← hspec _ (B.K.mul_mem ha hb), ← hspec a ha, ← hspec b hb]
  have hcomm_conj : a * (b * a * b⁻¹ * a⁻¹) * a⁻¹ ∈ B.frattiniK :=
    hRN.conj_mem _ (comm_mem_R_of_K B hRN hsq ha hb) a
  have edecomp : (⟨(a * b) * (a * b), hsq _ (B.K.mul_mem ha hb)⟩ : ↥B.frattiniK)
      = ⟨a * (b * a * b⁻¹ * a⁻¹) * a⁻¹, hcomm_conj⟩ * ⟨a * a, hsq a ha⟩ * ⟨b * b, hsq b hb⟩ :=
    Subtype.ext (by push_cast; group)
  rw [edecomp, hlam_hom, hlam_hom]
  rw [hlam_conj a (b * a * b⁻¹ * a⁻¹) (comm_mem_R_of_K B hRN hsq ha hb)]
  have hz : ∀ x p q : ZMod 2, x + p + q + p + q = x := by decide
  exact hz _ _ _

omit [Finite Y] in
/-- **`qbar 1 = 0`** (`map_zero`): from `λ 1 = 0`. -/
theorem blockQbar_map_zero (_ : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hspec : ∀ (k : Y) (hk : k ∈ B.K),
      lam ⟨k * k, hsq k hk⟩ = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩)) :
    qbar 1 = 0 := by
  have lam_one : lam 1 = 0 := by
    have h := hlam_hom 1 1
    rw [one_mul] at h
    have h2 : (0 : ZMod 2) + lam 1 = lam 1 + lam 1 := by rw [zero_add]; exact h
    exact (add_right_cancel h2).symm
  have h := hspec 1 (one_mem _)
  rw [show (⟨1, B.hKP (one_mem _)⟩ : ↥B.P) = 1 from rfl, QuotientGroup.mk_one] at h
  rw [← h, show (⟨(1 : Y) * 1, hsq 1 (one_mem _)⟩ : ↥B.frattiniK) = 1 from Subtype.ext (one_mul 1),
    lam_one]

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] in
/-- Every class of `V = P/S` has a `K`-representative (from `KS = P`, `Blk.gen`). -/
theorem exists_K_rep (v : ↥B.P ⧸ B.S.subgroupOf B.P) :
    ∃ k : Y, ∃ hk : k ∈ B.K,
      (QuotientGroup.mk ⟨k, B.hKP hk⟩ : ↥B.P ⧸ B.S.subgroupOf B.P) = v := by
  haveI := B.hS
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective v
  have hp' : (p : Y) ∈ (B.K : Set Y) * (B.S : Set Y) := by
    rw [← Subgroup.mul_normal B.K B.S, B.gen]; exact p.2
  obtain ⟨k, hk, s, hs, hks⟩ := hp'
  refine ⟨k, hk, ?_⟩
  rw [QuotientGroup.eq]
  refine Subgroup.mem_subgroupOf.mpr ?_
  show k⁻¹ * (p : Y) ∈ B.S
  rw [show k⁻¹ * (p : Y) = s from by rw [← hks]; group]
  exact hs

omit [Finite Y] in
/-- **The multiplicative polar form is biadditive** (`hquad`'s core `polar_add_left`):
`β(u·v, w) = β(u,w) + β(v,w)`.  Via `blockQbar_beta` (`β = λ(commutator)`) + the commutator
identity `[w, uv] = [w,u]·u[w,v]u⁻¹` + `λ`'s additivity/conj-invariance. -/
theorem blockQbar_polar_add (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩)
    (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hspec : ∀ (k : Y) (hk : k ∈ B.K),
      lam ⟨k * k, hsq k hk⟩ = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩))
    (u v w : ↥B.P ⧸ B.S.subgroupOf B.P) :
    qbar (u * v * w) + qbar (u * v) + qbar w
      = (qbar (u * w) + qbar u + qbar w) + (qbar (v * w) + qbar v + qbar w) := by
  obtain ⟨ku, hku, rfl⟩ := exists_K_rep B u
  obtain ⟨kv, hkv, rfl⟩ := exists_K_rep B v
  obtain ⟨kw, hkw, rfl⟩ := exists_K_rep B w
  rw [mkK_mul B hku hkv,
    blockQbar_beta B hRN hsq lam hlam_hom hlam_conj qbar hspec (B.K.mul_mem hku hkv) hkw,
    blockQbar_beta B hRN hsq lam hlam_hom hlam_conj qbar hspec hku hkw,
    blockQbar_beta B hRN hsq lam hlam_hom hlam_conj qbar hspec hkv hkw]
  -- goal: λ⟨[kw, ku·kv]⟩ = λ⟨[kw,ku]⟩ + λ⟨[kw,kv]⟩
  have hcid : (⟨kw * (ku * kv) * kw⁻¹ * (ku * kv)⁻¹,
        comm_mem_R_of_K B hRN hsq (B.K.mul_mem hku hkv) hkw⟩ : ↥B.frattiniK)
      = ⟨kw * ku * kw⁻¹ * ku⁻¹, comm_mem_R_of_K B hRN hsq hku hkw⟩
        * ⟨ku * (kw * kv * kw⁻¹ * kv⁻¹) * ku⁻¹,
            hRN.conj_mem _ (comm_mem_R_of_K B hRN hsq hkv hkw) ku⟩ :=
    Subtype.ext (by push_cast; group)
  rw [hcid, hlam_hom, hlam_conj ku (kw * kv * kw⁻¹ * kv⁻¹) (comm_mem_R_of_K B hRN hsq hkv hkw)]

/-! ## `hns`: the descended form `qbar` is nonsingular -/

/-- Total extension of `qbar` to `Y`: `qbP y = qbar⟦y⟧` for `y ∈ P`, else `0`. -/
noncomputable def qbP (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) (y : Y) : ZMod 2 :=
  if h : y ∈ B.P then qbar (QuotientGroup.mk ⟨y, h⟩) else 0

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] in
private theorem qbP_mem (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) {y : Y} (hy : y ∈ B.P) :
    qbP B qbar y = qbar (QuotientGroup.mk ⟨y, hy⟩) := dif_pos hy

omit [Finite Y] in
/-- `⟦p⟧·⟦q⟧ = ⟦pq⟧` on `P/S` (the `P`-membership form). -/
theorem mkP_mul {a b : Y} (ha : a ∈ B.P) (hb : b ∈ B.P) :
    (QuotientGroup.mk ⟨a, ha⟩ : ↥B.P ⧸ B.S.subgroupOf B.P) * QuotientGroup.mk ⟨b, hb⟩
      = QuotientGroup.mk ⟨a * b, mul_mem ha hb⟩ := by
  rw [← QuotientGroup.mk_mul]
  rfl

omit [Finite Y] [(B.S.subgroupOf B.P).Normal] in
/-- **`Y`-conjugation invariance of the polar form** `β(g•a, g•b) = β(a,b)` (in `qbP` terms),
from `qbar`'s `Y`-invariance `hinv`. -/
theorem beta_conj (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hinv : ∀ (y p : Y) (hp : p ∈ B.P),
      qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
        = qbar (QuotientGroup.mk ⟨p, hp⟩))
    (g y q : Y) (hy : y ∈ B.P) (hq : q ∈ B.P) :
    qbP B qbar (g * y * g⁻¹ * (g * q * g⁻¹)) + qbP B qbar (g * y * g⁻¹)
        + qbP B qbar (g * q * g⁻¹)
      = qbP B qbar (y * q) + qbP B qbar y + qbP B qbar q := by
  have hyq : y * q ∈ B.P := mul_mem hy hq
  rw [show g * y * g⁻¹ * (g * q * g⁻¹) = g * (y * q) * g⁻¹ from by group,
    qbP_mem B qbar (B.hP.conj_mem _ hyq g), qbP_mem B qbar (B.hP.conj_mem _ hy g),
    qbP_mem B qbar (B.hP.conj_mem _ hq g), qbP_mem B qbar hyq, qbP_mem B qbar hy,
    qbP_mem B qbar hq, hinv g (y * q) hyq, hinv g y hy, hinv g q hq]

/-- The polar form as a `Y`-function via `qbP` (meaningful for `y, q ∈ P`). -/
noncomputable def betaP (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) (y q : Y) : ZMod 2 :=
  qbP B qbar (y * q) + qbP B qbar y + qbP B qbar q

omit [Finite Y] in
/-- `betaP` is additive in its first argument (from `qbar`'s polar biadditivity). -/
theorem betaP_biadd (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hbiadd : ∀ u v w : ↥B.P ⧸ B.S.subgroupOf B.P,
      qbar (u * v * w) + qbar (u * v) + qbar w
        = (qbar (u * w) + qbar u + qbar w) + (qbar (v * w) + qbar v + qbar w))
    {y y' q : Y} (hy : y ∈ B.P) (hy' : y' ∈ B.P) (hq : q ∈ B.P) :
    betaP B qbar (y * y') q = betaP B qbar y q + betaP B qbar y' q := by
  have key := hbiadd (QuotientGroup.mk ⟨y, hy⟩) (QuotientGroup.mk ⟨y', hy'⟩)
    (QuotientGroup.mk ⟨q, hq⟩)
  rw [mkP_mul B hy hy', mkP_mul B (mul_mem hy hy') hq, mkP_mul B hy hq, mkP_mul B hy' hq] at key
  unfold betaP
  rw [qbP_mem B qbar (mul_mem (mul_mem hy hy') hq), qbP_mem B qbar (mul_mem hy hy'),
    qbP_mem B qbar hq, qbP_mem B qbar (mul_mem hy hq), qbP_mem B qbar hy,
    qbP_mem B qbar (mul_mem hy' hq), qbP_mem B qbar hy']
  exact key

omit [Finite Y] in
/-- `betaP 1 q = 0` (`⟦1⟧ = 0` in the polar form). -/
theorem betaP_one (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) (h0 : qbar 1 = 0) (q : Y) :
    betaP B qbar 1 q = 0 := by
  unfold betaP
  have h1 : qbP B qbar 1 = 0 := by
    rw [qbP_mem B qbar (one_mem _), show (⟨1, one_mem _⟩ : ↥B.P) = 1 from rfl,
      QuotientGroup.mk_one, h0]
  rw [one_mul, h1, add_zero, CharTwo.add_self_eq_zero]

/-- **The polar radical** as a subgroup of `Y` (contained in `P`): `{y ∈ P | ∀ q ∈ P, β(y,q)=0}`.
A subgroup by biadditivity/normalization of `β`. -/
def radSub (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hbiadd : ∀ u v w : ↥B.P ⧸ B.S.subgroupOf B.P,
      qbar (u * v * w) + qbar (u * v) + qbar w
        = (qbar (u * w) + qbar u + qbar w) + (qbar (v * w) + qbar v + qbar w))
    (h0 : qbar 1 = 0) : Subgroup Y where
  carrier := {y | y ∈ B.P ∧ ∀ q : Y, q ∈ B.P → betaP B qbar y q = 0}
  one_mem' := ⟨one_mem _, fun q _ => betaP_one B qbar h0 q⟩
  mul_mem' := by
    rintro a b ⟨haP, ha⟩ ⟨hbP, hb⟩
    exact ⟨mul_mem haP hbP, fun q hq => by
      rw [betaP_biadd B qbar hbiadd haP hbP hq, ha q hq, hb q hq, add_zero]⟩
  inv_mem' := by
    rintro a ⟨haP, ha⟩
    refine ⟨inv_mem haP, fun q hq => ?_⟩
    have hbi := betaP_biadd B qbar hbiadd haP (inv_mem haP) hq
    rw [mul_inv_cancel, betaP_one B qbar h0 q, ha q hq, zero_add] at hbi
    exact hbi.symm

omit [Finite Y] in
private theorem radSub_le_P (qbar) (hbiadd) (h0) : radSub B qbar hbiadd h0 ≤ B.P := fun _ hy => hy.1

omit [Finite Y] in
private theorem S_le_radSub (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) (hbiadd) (h0 : qbar 1 = 0) :
    B.S ≤ radSub B qbar hbiadd h0 := by
  intro s hs
  have hsP : s ∈ B.P := B.hSP.le hs
  refine ⟨hsP, fun q hq => ?_⟩
  have hs1 : (QuotientGroup.mk ⟨s, hsP⟩ : ↥B.P ⧸ B.S.subgroupOf B.P) = 1 := by
    rw [QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr hs
  unfold betaP
  rw [qbP_mem B qbar (mul_mem hsP hq), qbP_mem B qbar hsP, qbP_mem B qbar hq,
    ← mkP_mul B hsP hq, hs1, one_mul, h0, add_zero, CharTwo.add_self_eq_zero]

omit [Finite Y] in
private theorem radSub_normal (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2) (hbiadd) (h0)
    (hinv : ∀ (y p : Y) (hp : p ∈ B.P),
      qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
        = qbar (QuotientGroup.mk ⟨p, hp⟩)) :
    (radSub B qbar hbiadd h0).Normal := by
  refine ⟨fun a ha g => ?_⟩
  obtain ⟨haP, ha⟩ := ha
  refine ⟨B.hP.conj_mem a haP g, fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g ∈ B.P := by
    have h := B.hP.conj_mem q hq g⁻¹; rwa [inv_inv] at h
  have hbc := beta_conj B qbar hinv g a (g⁻¹ * q * g) haP hq'
  rw [show g * (g⁻¹ * q * g) * g⁻¹ = q from by group] at hbc
  unfold betaP
  rw [hbc]
  exact ha (g⁻¹ * q * g) hq'

/-- **Endgame**: an additive nonzero `Y`-invariant `qbar : V → 𝔽₂` yields a `Y`-normal index-2
subgroup of `K` above `R` (`ker` of the character `k ↦ qbar⟦k⟧`), contradicting `lemma_7_1_dual`. -/
theorem additive_qbar_absurd (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (h0 : qbar 1 = 0)
    (hadd : ∀ a b : ↥B.P ⧸ B.S.subgroupOf B.P, qbar (a * b) = qbar a + qbar b)
    (hqbar_ne : ∃ a, qbar a ≠ 0)
    (hinv : ∀ (y p : Y) (hp : p ∈ B.P),
      qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
        = qbar (QuotientGroup.mk ⟨p, hp⟩)) : False := by
  have qbar_inv : ∀ a : ↥B.P ⧸ B.S.subgroupOf B.P, qbar a⁻¹ = qbar a := fun a => by
    have h := hadd a a⁻¹
    rw [mul_inv_cancel, h0] at h
    have hz : ∀ x y : ZMod 2, 0 = x + y → y = x := by decide
    exact hz _ _ h
  -- the invariant character subgroup `Xk = {k ∈ K | qbar⟦k⟧ = 0}`
  set Xk : Subgroup Y :=
    { carrier := {y | y ∈ B.K ∧ qbP B qbar y = 0}
      one_mem' := ⟨one_mem _, by
        rw [qbP_mem B qbar (one_mem _), show (⟨1, one_mem _⟩ : ↥B.P) = 1 from rfl,
          QuotientGroup.mk_one, h0]⟩
      mul_mem' := by
        rintro x y ⟨hxK, hx0⟩ ⟨hyK, hy0⟩
        refine ⟨mul_mem hxK hyK, ?_⟩
        rw [qbP_mem B qbar (B.hKP (mul_mem hxK hyK)), ← mkP_mul B (B.hKP hxK) (B.hKP hyK), hadd]
        rw [qbP_mem B qbar (B.hKP hxK)] at hx0
        rw [qbP_mem B qbar (B.hKP hyK)] at hy0
        rw [hx0, hy0, add_zero]
      inv_mem' := by
        rintro y ⟨hyK, hy0⟩
        refine ⟨inv_mem hyK, ?_⟩
        rw [qbP_mem B qbar (B.hKP (inv_mem hyK))]
        rw [qbP_mem B qbar (B.hKP hyK)] at hy0
        rw [show (⟨y⁻¹, B.hKP (inv_mem hyK)⟩ : ↥B.P) = (⟨y, B.hKP hyK⟩)⁻¹ from rfl,
          QuotientGroup.mk_inv, qbar_inv, hy0] } with hXkdef
  have hXkK : Xk ≤ B.K := fun _ hy => hy.1
  have hXkN : Xk.Normal := ⟨fun n hn g => by
    obtain ⟨hnK, hn0⟩ := hn
    refine ⟨B.hK.conj_mem n hnK g, ?_⟩
    rw [qbP_mem B qbar (B.hP.conj_mem n (B.hKP hnK) g)]
    rw [qbP_mem B qbar (B.hKP hnK)] at hn0
    rw [hinv g n (B.hKP hnK), hn0]⟩
  have hRXk : B.frattiniK ≤ Xk := by
    intro r hr
    have hrK : r ∈ B.K := frattiniLike_le B.K hr
    refine ⟨hrK, ?_⟩
    rw [qbP_mem B qbar (B.hKP hrK)]
    rw [show (QuotientGroup.mk ⟨r, B.hKP hrK⟩ : ↥B.P ⧸ B.S.subgroupOf B.P) = 1 from by
      rw [QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (((lemma_7_1_head B).trans inf_le_right) hr), h0]
  -- index 2, via a witness `k₁` with `qbar⟦k₁⟧ = 1`
  obtain ⟨a₁, ha₁⟩ := hqbar_ne
  obtain ⟨k₁, hk₁, hk₁eq⟩ := exists_K_rep B a₁
  have hzmod : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hk1v : qbar (QuotientGroup.mk ⟨k₁, B.hKP hk₁⟩) = 1 := by
    rw [hk₁eq]; exact hzmod _ ha₁
  have hidx : (Xk.subgroupOf B.K).index = 2 := by
    rw [Subgroup.index_eq_two_iff]
    refine ⟨⟨k₁, hk₁⟩, fun b => ?_⟩
    have hmem : ∀ c : ↥B.K, (c ∈ Xk.subgroupOf B.K)
        ↔ qbar (QuotientGroup.mk ⟨(c : Y), B.hKP c.2⟩) = 0 := by
      intro c
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun h => by rw [← qbP_mem B qbar (B.hKP c.2)]; exact h.2,
        fun h => ⟨c.2, by rw [qbP_mem B qbar (B.hKP c.2)]; exact h⟩⟩
    have hbk : qbar (QuotientGroup.mk ⟨(↑(b * ⟨k₁, hk₁⟩) : Y), B.hKP (b * ⟨k₁, hk₁⟩).2⟩)
        = qbar (QuotientGroup.mk ⟨(b : Y), B.hKP b.2⟩) + 1 := by
      have he : (QuotientGroup.mk ⟨(↑(b * ⟨k₁, hk₁⟩) : Y), B.hKP (b * ⟨k₁, hk₁⟩).2⟩ :
            ↥B.P ⧸ B.S.subgroupOf B.P)
          = QuotientGroup.mk ⟨(b : Y), B.hKP b.2⟩ * QuotientGroup.mk ⟨k₁, B.hKP hk₁⟩ := by
        rw [mkP_mul B (B.hKP b.2) (B.hKP hk₁)]; rfl
      rw [he, hadd, hk1v]
    rw [hmem, hmem, hbk]
    rcases eq_or_ne (qbar (QuotientGroup.mk ⟨(b : Y), B.hKP b.2⟩)) 0 with h | h
    · rw [h]; right; exact ⟨rfl, by decide⟩
    · left
      exact ⟨by rw [hzmod _ h]; decide, h⟩
  exact lemma_7_1_dual B ⟨Xk, hXkN, hRXk, hXkK, hidx⟩

/-- **`hns` core (multiplicative)**: the polar form is non-degenerate — every `a ≠ 1` in `V=P/S`
pairs nontrivially.  If not, `radSub` is a nonzero `Y`-normal subgroup between `S` and `P`, so
`= P` by `chief`; then `qbar` is additive, contradicting `lemma_7_1_dual`
(`additive_qbar_absurd`). -/
theorem blockQbar_nonsingular_mul (hRN : B.frattiniK.Normal)
    (hsq : ∀ k ∈ B.K, k * k ∈ B.frattiniK)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩)
    (qbar : (↥B.P ⧸ B.S.subgroupOf B.P) → ZMod 2)
    (hspec : ∀ (k : Y) (hk : k ∈ B.K),
      lam ⟨k * k, hsq k hk⟩ = qbar (QuotientGroup.mk ⟨k, B.hKP hk⟩))
    (hqbar_ne : ∃ a, qbar a ≠ 0)
    (hinv : ∀ (y p : Y) (hp : p ∈ B.P),
      qbar (QuotientGroup.mk ⟨y * p * y⁻¹, B.hP.conj_mem p hp y⟩)
        = qbar (QuotientGroup.mk ⟨p, hp⟩)) :
    ∀ a : ↥B.P ⧸ B.S.subgroupOf B.P, a ≠ 1 → ∃ b, qbar (a * b) + qbar a + qbar b ≠ 0 := by
  have h0 : qbar 1 = 0 := blockQbar_map_zero B hRN hsq lam hlam_hom qbar hspec
  have hbiadd : ∀ u v w : ↥B.P ⧸ B.S.subgroupOf B.P,
      qbar (u * v * w) + qbar (u * v) + qbar w
        = (qbar (u * w) + qbar u + qbar w) + (qbar (v * w) + qbar v + qbar w) :=
    blockQbar_polar_add B hRN hsq lam hlam_hom hlam_conj qbar hspec
  intro a ha
  by_contra! hcon
  obtain ⟨p₀, hp₀⟩ := QuotientGroup.mk_surjective a
  have hp₀S : (↑p₀ : Y) ∉ B.S := by
    intro hmem
    exact ha (by rw [← hp₀, QuotientGroup.eq_one_iff]; exact Subgroup.mem_subgroupOf.mpr hmem)
  have hp₀rad : (↑p₀ : Y) ∈ radSub B qbar hbiadd h0 := by
    refine ⟨p₀.2, fun q hq => ?_⟩
    have hb := hcon (QuotientGroup.mk ⟨q, hq⟩)
    rw [← hp₀] at hb
    unfold betaP
    rw [qbP_mem B qbar (mul_mem p₀.2 hq), qbP_mem B qbar p₀.2, qbP_mem B qbar hq,
      ← mkP_mul B p₀.2 hq]
    exact hb
  have hne : radSub B qbar hbiadd h0 ≠ B.S := fun heq => hp₀S (by rw [← heq]; exact hp₀rad)
  rcases B.chief (radSub B qbar hbiadd h0) (radSub_normal B qbar hbiadd h0 hinv)
      (S_le_radSub B qbar hbiadd h0) (radSub_le_P B qbar hbiadd h0) with hS | hPeq
  · exact hne hS
  have hadd : ∀ a b : ↥B.P ⧸ B.S.subgroupOf B.P, qbar (a * b) = qbar a + qbar b := by
    intro a b
    obtain ⟨pa, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨pb, rfl⟩ := QuotientGroup.mk_surjective b
    have hpa : (↑pa : Y) ∈ radSub B qbar hbiadd h0 := by rw [hPeq]; exact pa.2
    have hb0 := hpa.2 ↑pb pb.2
    unfold betaP at hb0
    rw [qbP_mem B qbar (mul_mem pa.2 pb.2), qbP_mem B qbar pa.2, qbP_mem B qbar pb.2,
      ← mkP_mul B pa.2 pb.2] at hb0
    have hz : ∀ a x y : ZMod 2, a + x + y = 0 → a = x + y := by decide
    exact hz _ _ _ hb0
  exact additive_qbar_absurd B qbar h0 hadd hqbar_ne hinv

end Quad

/-- **Packaging**: multiplicative non-degeneracy of `qm` on a `CommGroup` gives `Nonsingular` on
`Additive`. -/
theorem nonsingular_of_mul {G : Type*} [CommGroup G] (qm : G → ZMod 2)
    (hns : ∀ a : G, a ≠ 1 → ∃ b, qm (a * b) + qm a + qm b ≠ 0) :
    QuadraticFp2.Nonsingular (fun v : Additive G => qm (Additive.toMul v)) := by
  intro v hv
  obtain ⟨b, hb⟩ := hns (Additive.toMul v) (fun h => hv (by
    rw [show v = Additive.ofMul (Additive.toMul v) from rfl, h]; rfl))
  exact ⟨Additive.ofMul b, hb⟩

end GQ2
