import GQ2.FrameEnrichment
import GQ2.CentralObstruction
import GQ2.SectionSix

/-!
# §8 zero-edge engines: Lemma 8.7 (affine `T`-lifting) + Prop 8.8, target side  (P-16d4)

When the radical edge of the scalar cover `p_λ` vanishes — the `∃ N`-branch of the (140)
case split, i.e. `¬ D.NoDescent` — the paper (pp. 40–43) runs three steps to evaluate the
constrained Gauss sum.  This file provides the **source-generic, target-side** halves:

1. **`descended_splitting`** (Lemma 6.21 application): the descent datum `N` makes
   `Q = Bg/T` a split extension of `C₀` by `V`, i.e. `∃ σ : C₀ →* Q` sectioning `piQbar`.
   Consumes the `κ⁰_q` datum (the `Enrichment` fields of P-16d1) exactly as the paper's
   "fix the base determinant class" clause requires.
2. **`lemma_8_7_count`** (Lemma 8.7, (131)/(132), count form): the central `M`-lifts over a
   lower map `ρ` fibre over their `V`-coordinates with constant multiplicity `#Z¹_{Γ,ρ}(T)`.
   The torsor structure is the P-16a `twist` involution; `Central`-invariance under a
   `T`-twist is `ob_twist` with the **vanishing** variation class (the `N`-complement has
   `edge ≡ 0`).
3. **`prop_8_8_target`** (Prop 8.8, (133)/(134), target side): the edge-killing shear, an
   instance of the proved `lemma_6_22`, produces the total scalar phase `DeltaScalar`.
   The Γ-level completed-square (135) — which consumes cor. 5.17 — is **out of scope**
   (P-16d6, behind the P-13f firewall).

Plus **`exists_polar_inverse`**, the finite-linear-algebra supplier of the shift vectors
`a_{χ,κ}` of (133) (cf. `lemma_8_5`'s `a`-data-with-spec).

Design decisions D1–D6 and the full work order: `docs/p16d4-plan.md`.  Deviation-ledger
entries D1 (cocycle-level 8.7) and D3 (6.22-normalized `Δ`): `docs/section8-extraction.md`.
Everything is finite-group / generic-`Γ`; **no B6/B7, no P-13f material**; all std-3.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2

/-! ## The `N`-section and the vanishing edge

In the zero-edge regime we are handed a normal complement `N ◁ B̃` with `p(N) = T` and
`z ∉ N` (the negation of `NoDescent`).  Since `p|_N : N ≅ T` is a bijection, its inverse
`sectN` is a homomorphic section of `p` over `T` whose image `N` is normal — so the edge
cocycle of the resulting `TComplement` vanishes identically. -/

variable {Bg : Type} [Group Bg] [Finite Bg] {D : RadicalCoverData Bg}

/-- **A descent datum** for the scalar cover: a normal complement `N ◁ B̃` to `⟨z⟩` over `T`
(`p(N) = T`, `z ∉ N`).  This is the negation of `D.NoDescent` unpacked; d6 obtains it from
`radData_noDescent_iff`.  Its existence is the zero-edge case of the (140) split. -/
structure Descent (D : RadicalCoverData Bg) where
  /-- The normal complement. -/
  N : Subgroup D.C.cover
  hN : N.Normal
  /-- `N` covers `T`. -/
  hNT : N.map D.C.p = D.T
  /-- `N` misses the central `z`. -/
  hNz : D.C.z ∉ N

variable (Dsc : Descent D)

/-- Every element of `N` covers a `T`-element (`p(N) = T`). -/
theorem pN_mem_T (n : ↥Dsc.N) : D.C.p n.1 ∈ D.T := by
  rw [← Dsc.hNT]; exact Subgroup.mem_map_of_mem _ n.2

/-- `p|_N : N → T` as a homomorphism. -/
noncomputable def pN : ↥Dsc.N →* ↥D.T :=
  (D.C.p.comp Dsc.N.subtype).codRestrict D.T (fun n => pN_mem_T Dsc n)

@[simp] theorem pN_coe (n : ↥Dsc.N) : ((pN Dsc n : ↥D.T) : Bg) = D.C.p n.1 := rfl

theorem pN_injective : Function.Injective (pN Dsc) := by
  rw [injective_iff_map_eq_one]
  intro n hn
  have hker : n.1 ∈ D.C.p.ker := by
    rw [MonoidHom.mem_ker]; simpa [pN] using congrArg Subtype.val hn
  rcases ker_cases D hker with h1 | hz
  · exact Subtype.ext h1
  · exact absurd (hz ▸ n.2) Dsc.hNz

theorem pN_surjective : Function.Surjective (pN Dsc) := by
  intro t
  have ht : t.1 ∈ Dsc.N.map D.C.p := by rw [Dsc.hNT]; exact t.2
  obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp ht
  exact ⟨⟨n, hnN⟩, Subtype.ext hn⟩

/-- `p|_N : N ≅ T` as a group isomorphism. -/
noncomputable def eN : ↥Dsc.N ≃* ↥D.T :=
  MulEquiv.ofBijective (pN Dsc) ⟨pN_injective Dsc, pN_surjective Dsc⟩

/-- **The `N`-section** `T → B̃`: the inverse of `p|_N`, landing in the normal complement. -/
noncomputable def sectN : ↥D.T →* D.C.cover :=
  Dsc.N.subtype.comp (eN Dsc).symm.toMonoidHom

theorem sectN_mem (t : ↥D.T) : sectN Dsc t ∈ Dsc.N :=
  ((eN Dsc).symm t).2

@[simp] theorem sectN_sect (t : ↥D.T) : D.C.p (sectN Dsc t) = t.1 := by
  have h : pN Dsc ((eN Dsc).symm t) = t := (eN Dsc).apply_symm_apply t
  simpa [sectN, pN] using congrArg Subtype.val h

/-- The `N`-section, packaged as a `TComplement`. -/
noncomputable def SN : TComplement D :=
  ⟨sectN Dsc, sectN_sect Dsc⟩

/-- **The edge vanishes on the `N`-complement**: conjugation preserves the normal `N`, so
the section's conjugation defect is trivial.  This is what makes the (129) variation class
zero in the zero-edge regime. -/
theorem edge_zero (b : Bg) (t : ↥D.T) : edge D (SN Dsc) b t = 0 := by
  classical
  set x := Function.surjInv D.C.surj b with hx
  have hpx : D.C.p x = b := Function.surjInv_eq D.C.surj b
  refine edge_eq_of_spec D (SN Dsc) hpx t 0 ?_
  -- both sides lie in `N` and cover `b t b⁻¹`, hence are equal
  have hsN : sectN Dsc t ∈ Dsc.N := sectN_mem Dsc t
  have hwN : x * sectN Dsc t * x⁻¹ ∈ Dsc.N := Dsc.hN.conj_mem _ hsN x
  have hrN : sectN Dsc ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ ∈ Dsc.N :=
    sectN_mem Dsc _
  have hwp : D.C.p (x * sectN Dsc t * x⁻¹) = b * t.1 * b⁻¹ := by
    rw [map_mul, map_mul, map_inv, hpx, sectN_sect]
  have hrp : D.C.p (sectN Dsc ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩) = b * t.1 * b⁻¹ := by
    rw [sectN_sect]
  have heq : (⟨x * sectN Dsc t * x⁻¹, hwN⟩ : ↥Dsc.N)
      = ⟨sectN Dsc ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩, hrN⟩ := by
    apply pN_injective Dsc
    apply Subtype.ext
    rw [pN_coe, pN_coe, hwp, hrp]
  have hval : x * sectN Dsc t * x⁻¹
      = sectN Dsc ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ := congrArg Subtype.val heq
  show x * (SN Dsc).s t * x⁻¹
    = (SN Dsc).s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ (0 : ZMod 2).val
  rw [show ((0 : ZMod 2)).val = 0 from by decide, pow_zero, mul_one]
  exact hval

/-! ## The descended semidirect structure on `Q = Bg/T`

`T` is normal (it is `D.hT`), so `Q := Bg ⧸ T` is a group and the projection `piT` sits over
`piQbar : Q ↠ C₀` (the lift of `piC₀`, which kills `T ≤ M`).  Its kernel is `V = M/T`, and
the descent iso `descend : M ↠ V` gives the inclusion `iV : V ↪ Q` characterized by
`iV (descend m) = piT m`.  All the extension data of `1 → V → Q → C₀ → 1` reads off `iV`. -/

instance instNormalT (D : RadicalCoverData Bg) : D.T.Normal := D.hT

/-- **The descended `κ⁰_q` datum** for the zero-edge regime (the P-16d1 `Enrichment` fields at
a fixed nonzero `λ`, in the source-generic `RadicalCoverData` vocabulary).  The `C`-stage
group `C₀` (with `piC₀ : Bg ↠ C₀`, `ker = M`), the descended module `V = M/T` with its
`C₀`-action and the descent surjection `descend : M ↠ V`, the descended nonsingular form
`q̄`, and its fixed equivariant factor-set datum (Lemma 6.1's `κ⁰_{q̄}` — the relative
hypothesis of `lemma_6_21`).  d6 builds one `DescData` from `E : RF.Enrichment` at `(l,h)`
via `E.radData l h`, `RF.piBC`, `RF.ker_piBC`, and the descended-module fields. -/
structure DescData (D : RadicalCoverData Bg) where
  /-- The `C`-stage group `C₀ = B/M`. -/
  C0 : Type
  [gC0 : Group C0]
  [fC0 : Finite C0]
  /-- The projection `piC₀ : B ↠ C₀`. -/
  piC0 : Bg →* C0
  hpiC0 : Function.Surjective piC0
  hkerC0 : piC0.ker = D.M
  /-- The descended module `V = M/T`. -/
  Vmod : Type
  [aVmod : AddCommGroup Vmod]
  [fVmod : Finite Vmod]
  [actVmod : DistribMulAction C0 Vmod]
  /-- The descent surjection `M ↠ V`. -/
  descend : ↥D.M →* Multiplicative Vmod
  hdesc_surj : Function.Surjective descend
  hdesc_ker : ∀ m : ↥D.M, descend m = 1 ↔ (m : Bg) ∈ D.T
  /-- `descend` intertwines `B`-conjugation with the `C₀`-action through `piC₀`. -/
  hdesc_conj : ∀ (bb : Bg) (m : ↥D.M) (hm : bb * (m : Bg) * bb⁻¹ ∈ D.M),
    descend ⟨bb * (m : Bg) * bb⁻¹, hm⟩
      = Multiplicative.ofAdd (piC0 bb • Multiplicative.toAdd (descend m))
  /-- The descended form `q̄` on `V`. -/
  qbar : Vmod → ZMod 2
  hquad : IsQuadraticFp2 qbar
  hns : Nonsingular qbar
  /-- The fixed equivariant factor-set datum for `q̄` (Lemma 6.1's `κ⁰_{q̄}`). -/
  dat : FactorSet C0 Vmod
  hdat : IsEquivariantFactorSet qbar dat
  /-- `q_λ = q̄ ∘ descend` on `M`. -/
  hqbar : ∀ m : ↥D.M, D.q m = qbar (Multiplicative.toAdd (descend m))

attribute [instance] DescData.gC0 DescData.fC0 DescData.aVmod DescData.fVmod DescData.actVmod

section Descended

variable (DD : DescData D)

/-- The `T`-projection `Bg ↠ Q`. -/
abbrev piT : Bg →* Bg ⧸ D.T := QuotientGroup.mk' D.T

/-- `T ≤ ker piC₀` (`= M`), so `piC₀` descends to `Q`. -/
theorem T_le_kerC0 : D.T ≤ DD.piC0.ker := by rw [DD.hkerC0]; exact D.hTM

/-- **The connecting map** `piQbar : Q ↠ C₀`, the descent of `piC₀` through `T ≤ M`. -/
noncomputable def piQbar : (Bg ⧸ D.T) →* DD.C0 :=
  QuotientGroup.lift D.T DD.piC0 (T_le_kerC0 DD)

@[simp] theorem piQbar_mk (b : Bg) : piQbar DD (piT (D := D) b) = DD.piC0 b :=
  QuotientGroup.lift_mk' _ _ b

theorem piQbar_surj : Function.Surjective (piQbar DD) := by
  intro c
  obtain ⟨b, rfl⟩ := DD.hpiC0 c
  exact ⟨piT (D := D) b, piQbar_mk DD b⟩

/-- `descend` and the `M`-into-`Q` map have the same kernel `T ∩ M`. -/
theorem descend_ker_eq_mMap_ker :
    DD.descend.ker = ((piT (D := D)).comp D.M.subtype).ker := by
  ext m
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact DD.hdesc_ker m

/-- **The `V`-inclusion** `iV : V ↪ Q`, the descent of `M ↪ Bg ↠ Q` through `descend`. -/
noncomputable def iV : Multiplicative DD.Vmod →* Bg ⧸ D.T :=
  (QuotientGroup.lift DD.descend.ker ((piT (D := D)).comp D.M.subtype)
      (le_of_eq (descend_ker_eq_mMap_ker DD))).comp
    (QuotientGroup.quotientKerEquivOfSurjective DD.descend DD.hdesc_surj).symm.toMonoidHom

/-- **The characterizing identity**: `iV (descend m) = piT m` for `m ∈ M`.  Everything about
`iV` (injectivity, range, conjugation) is derived from this. -/
@[simp] theorem iV_spec (m : ↥D.M) :
    iV DD (DD.descend m) = piT (D := D) (m : Bg) := by
  set e := QuotientGroup.quotientKerEquivOfSurjective DD.descend DD.hdesc_surj with he_def
  have he : e (QuotientGroup.mk m) = DD.descend m := QuotientGroup.kerLift_mk _ m
  have hsymm : e.symm (DD.descend m) = QuotientGroup.mk m := e.symm_apply_eq.mpr he.symm
  show (QuotientGroup.lift DD.descend.ker _ _).comp e.symm.toMonoidHom (DD.descend m) = _
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hsymm, QuotientGroup.lift_mk]
  rfl

theorem iV_injective : Function.Injective (iV DD) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  obtain ⟨m, rfl⟩ := DD.hdesc_surj x
  rw [iV_spec, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  exact (DD.hdesc_ker m).mpr hx

/-- **`range iV = ker piQbar`** (`= V`): the extension `1 → V → Q → C₀ → 1` in `lemma_6_21`
form. -/
theorem iV_range : (iV DD).range = (piQbar DD).ker := by
  ext qq
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨m, rfl⟩ := DD.hdesc_surj x
    rw [MonoidHom.mem_ker, iV_spec, piQbar_mk]
    have hm : (m : Bg) ∈ DD.piC0.ker := by rw [DD.hkerC0]; exact m.2
    exact hm
  · intro hqq
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D.T qq
    rw [MonoidHom.mem_ker, piQbar_mk] at hqq
    have hbM : b ∈ D.M := by rw [← DD.hkerC0]; exact hqq
    exact ⟨DD.descend ⟨b, hbM⟩, by rw [iV_spec]⟩

/-- **The conjugation law** for the extension (`lemma_6_21`'s `hconj`): `iV` intertwines
`Q`-conjugation with the `C₀`-action through `piQbar`. -/
theorem iV_conj (qq : Bg ⧸ D.T) (v : DD.Vmod) :
    qq * iV DD (Multiplicative.ofAdd v) * qq⁻¹
      = iV DD (Multiplicative.ofAdd (piQbar DD qq • v)) := by
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D.T qq
  obtain ⟨mv, hmv⟩ := DD.hdesc_surj (Multiplicative.ofAdd v)
  have hiv : iV DD (Multiplicative.ofAdd v) = piT (D := D) (mv : Bg) := by rw [← hmv, iV_spec]
  have hbmv : b * (mv : Bg) * b⁻¹ ∈ D.M := D.hM.conj_mem _ mv.2 b
  rw [hiv]
  calc piT (D := D) b * piT (D := D) (mv : Bg) * (piT (D := D) b)⁻¹
      = piT (D := D) (b * (mv : Bg) * b⁻¹) := by rw [← map_inv, ← map_mul, ← map_mul]
    _ = iV DD (DD.descend ⟨b * (mv : Bg) * b⁻¹, hbmv⟩) :=
          (iV_spec DD ⟨b * (mv : Bg) * b⁻¹, hbmv⟩).symm
    _ = iV DD (Multiplicative.ofAdd (DD.piC0 b • v)) := by
          rw [DD.hdesc_conj b mv hbmv, hmv, toAdd_ofAdd]
    _ = iV DD (Multiplicative.ofAdd (piQbar DD (QuotientGroup.mk' D.T b) • v)) := by
          rw [piQbar_mk]

end Descended

/-! ## The descended central double cover and its defect cocycle `ξ`

`Q̃ := B̃/N ↠ Q = B/T` is a central double cover (its kernel is `⟨z̄⟩`, `z̄ = mk z`, missing
`1` since `z ∉ N`).  Its **defect cocycle** `ξ` — the `z̄`-sign of the associativity defect of
a set-section — is the `𝔽₂`-class of the extension, with `ξ(iv, iv) = q̄(v)` on the fibre
`V`.  This is the class `lemma_6_21` consumes; `ξ` avoids bundling `Q̃` as a `CentralCover`
(hence no quotient-topology diamond) by reusing only the kernel-sign calculus. -/

instance instDescentNormal (Dsc : Descent D) : Dsc.N.Normal := Dsc.hN

section Cover

variable (Dsc : Descent D)

/-- The covering group `Q̃ = B̃/N`. -/
abbrev covQ : Type := D.C.cover ⧸ Dsc.N

/-- `N ≤ ker(piT ∘ p)`: elements of `N` cover `T`, which dies in `Q`. -/
theorem N_le_ker : Dsc.N ≤ ((piT (D := D)).comp D.C.p).ker := by
  intro n hn
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  exact pN_mem_T Dsc ⟨n, hn⟩

/-- The descended cover map `descP : Q̃ ↠ Q`. -/
noncomputable def descP : covQ Dsc →* Bg ⧸ D.T :=
  QuotientGroup.lift Dsc.N ((piT (D := D)).comp D.C.p) (N_le_ker Dsc)

@[simp] theorem descP_mk (x : D.C.cover) :
    descP Dsc (QuotientGroup.mk' Dsc.N x) = piT (D := D) (D.C.p x) :=
  QuotientGroup.lift_mk' _ _ x

theorem descP_surj : Function.Surjective (descP Dsc) := by
  intro q
  obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective D.T q
  obtain ⟨x, rfl⟩ := D.C.surj b
  exact ⟨QuotientGroup.mk' Dsc.N x, descP_mk Dsc x⟩

/-- The central involution `z̄ = mk z` of the descended cover. -/
noncomputable def zbar : covQ Dsc := QuotientGroup.mk' Dsc.N D.C.z

theorem zbar_ne_one : zbar Dsc ≠ 1 := by
  rw [zbar, QuotientGroup.mk'_apply, Ne, QuotientGroup.eq_one_iff]
  exact Dsc.hNz

theorem zbar_sq : zbar Dsc * zbar Dsc = 1 := by
  rw [zbar, ← map_mul, D.C.z_sq, map_one]

theorem zbar_central (x : covQ Dsc) : zbar Dsc * x = x * zbar Dsc := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Dsc.N x
  rw [zbar, ← map_mul, ← map_mul, D.C.central]

/-- Kernel elements of `descP` are `1` or `z̄`. -/
theorem descKerCases {x : covQ Dsc} (hx : x ∈ (descP Dsc).ker) :
    x = 1 ∨ x = zbar Dsc := by
  obtain ⟨w, rfl⟩ := QuotientGroup.mk'_surjective Dsc.N x
  rw [MonoidHom.mem_ker, descP_mk, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx
  -- `p w ∈ T`, so some `n ∈ N` has `p n = p w`; then `w n⁻¹ ∈ ⟨z⟩`
  have hpwT : D.C.p w ∈ D.T := hx
  obtain ⟨n, hnN, hpn⟩ := Subgroup.mem_map.mp (Dsc.hNT ▸ hpwT)
  have hker : w * n⁻¹ ∈ D.C.p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hpn, mul_inv_cancel]
  have hmkn : (QuotientGroup.mk' Dsc.N n : covQ Dsc) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr hnN
  rcases ker_cases D hker with h1 | hz
  · left
    have : w = n := by rw [← mul_inv_cancel_right w n⁻¹, h1, one_mul, inv_inv]
    rw [this]; exact hmkn
  · right
    have hw : w = D.C.z * n := by
      rw [← mul_inv_cancel_right w n⁻¹, hz, inv_inv]
    rw [hw, map_mul, hmkn, mul_one, zbar]

/-- The `z̄`-sign on the descended cover (meaningful on `ker descP = {1, z̄}`). -/
noncomputable def ccZsign (x : covQ Dsc) : ZMod 2 :=
  letI := Classical.dec (x = 1)
  if x = 1 then 0 else 1

theorem ccZsign_one : ccZsign Dsc (1 : covQ Dsc) = 0 := by simp [ccZsign]

theorem ccZsign_zbar : ccZsign Dsc (zbar Dsc) = 1 := by
  simp [ccZsign, zbar_ne_one Dsc]


/-- `ccZsign` is additive on the kernel. -/
theorem ccZsign_mul {x y : covQ Dsc} (hx : x ∈ (descP Dsc).ker) (hy : y ∈ (descP Dsc).ker) :
    ccZsign Dsc (x * y) = ccZsign Dsc x + ccZsign Dsc y := by
  rcases descKerCases Dsc hx with rfl | rfl <;> rcases descKerCases Dsc hy with rfl | rfl
  · simp [ccZsign_one]
  · rw [one_mul, ccZsign_one, zero_add]
  · rw [mul_one, ccZsign_one, add_zero]
  · rw [zbar_sq, ccZsign_one, ccZsign_zbar]; decide

/-- `ccZsign` of a `z̄`-power. -/
theorem ccZsign_zbar_pow (a : ZMod 2) : ccZsign Dsc (zbar Dsc ^ a.val) = a := by
  have key : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide
  rcases key a with rfl | rfl
  · rw [show ((0 : ZMod 2)).val = 0 from by decide, pow_zero, ccZsign_one]
  · rw [show ((1 : ZMod 2)).val = 1 from by decide, pow_one, ccZsign_zbar]

/-- A normalized set-section `s₀ : Q → Q̃` of `descP` (`s₀ 1 = 1`). -/
noncomputable def s0 (q : Bg ⧸ D.T) : covQ Dsc :=
  letI := Classical.dec (q = 1)
  if q = 1 then 1 else Function.surjInv (descP_surj Dsc) q

theorem s0_sect (q : Bg ⧸ D.T) : descP Dsc (s0 Dsc q) = q := by
  rw [s0]
  split
  · next h => rw [h, map_one]
  · exact Function.surjInv_eq (descP_surj Dsc) q

theorem s0_one : s0 Dsc (1 : Bg ⧸ D.T) = 1 := by rw [s0]; simp

/-- **The defect `𝔽₂`-cocycle** `ξ` of the descended cover: the `z̄`-sign of the associativity
defect of `s₀`.  This is the class `lemma_6_21` consumes. -/
noncomputable def xi (p : (Bg ⧸ D.T) × (Bg ⧸ D.T)) : ZMod 2 :=
  ccZsign Dsc (s0 Dsc p.1 * s0 Dsc p.2 * (s0 Dsc (p.1 * p.2))⁻¹)

theorem defect_mem_ker (a b : Bg ⧸ D.T) :
    s0 Dsc a * s0 Dsc b * (s0 Dsc (a * b))⁻¹ ∈ (descP Dsc).ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, s0_sect, s0_sect, s0_sect, mul_inv_cancel]

theorem ker_central {d : covQ Dsc} (hd : d ∈ (descP Dsc).ker) (w : covQ Dsc) :
    d * w = w * d := by
  rcases descKerCases Dsc hd with rfl | rfl
  · rw [one_mul, mul_one]
  · exact zbar_central Dsc w

/-- **The `ξ` cocycle identity** (`lemma_6_21`'s `hcocycle`): from associativity of
`s₀ g · s₀ h · s₀ k`, computed via the two central defects. -/
theorem xi_cocycle (g h k : Bg ⧸ D.T) :
    xi Dsc (h, k) + xi Dsc (g, h * k) = xi Dsc (g * h, k) + xi Dsc (g, h) := by
  have hassoc : g * (h * k) = g * h * k := (mul_assoc g h k).symm
  have hWmem : s0 Dsc g * s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹ ∈ (descP Dsc).ker := by
    rw [← hassoc]; exact defect_mem_ker Dsc g (h * k)
  have hcentral := ker_central Dsc (defect_mem_ker Dsc h k) (s0 Dsc g)
  -- the pure-group defect identity: `def(g,h)·def(gh,k) = def(h,k)·def(g,hk)`
  have hAB : (s0 Dsc g * s0 Dsc h * (s0 Dsc (g * h))⁻¹)
        * (s0 Dsc (g * h) * s0 Dsc k * (s0 Dsc (g * h * k))⁻¹)
      = (s0 Dsc h * s0 Dsc k * (s0 Dsc (h * k))⁻¹)
        * (s0 Dsc g * s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹) := by
    calc (s0 Dsc g * s0 Dsc h * (s0 Dsc (g * h))⁻¹)
          * (s0 Dsc (g * h) * s0 Dsc k * (s0 Dsc (g * h * k))⁻¹)
        = s0 Dsc g * (s0 Dsc h * s0 Dsc k * (s0 Dsc (h * k))⁻¹)
          * (s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹) := by group
      _ = (s0 Dsc h * s0 Dsc k * (s0 Dsc (h * k))⁻¹) * s0 Dsc g
          * (s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹) := by rw [← hcentral]
      _ = (s0 Dsc h * s0 Dsc k * (s0 Dsc (h * k))⁻¹)
          * (s0 Dsc g * s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹) := by group
  -- read off signs, then compare via `hAB`
  have hRHS : xi Dsc (g * h, k) + xi Dsc (g, h)
      = ccZsign Dsc ((s0 Dsc g * s0 Dsc h * (s0 Dsc (g * h))⁻¹)
          * (s0 Dsc (g * h) * s0 Dsc k * (s0 Dsc (g * h * k))⁻¹)) := by
    rw [ccZsign_mul Dsc (defect_mem_ker Dsc g h) (defect_mem_ker Dsc (g * h) k)]
    exact add_comm _ _
  have hLHS : xi Dsc (h, k) + xi Dsc (g, h * k)
      = ccZsign Dsc ((s0 Dsc h * s0 Dsc k * (s0 Dsc (h * k))⁻¹)
          * (s0 Dsc g * s0 Dsc (h * k) * (s0 Dsc (g * h * k))⁻¹)) := by
    rw [ccZsign_mul Dsc (defect_mem_ker Dsc h k) hWmem]
    simp only [xi]
    rw [hassoc]
  rw [hLHS, hRHS, hAB]

end Cover

/-! ## `descended_splitting`: the Lemma 6.21 application

With `ξ` in hand, the extension `1 → V → Q → C₀ → 1` splits.  `hξq` reads the fibre square
map of `ξ` off `q̄` (via `D.hq`/`hqbar`); `lemma_6_21` (P-15i, proved) then delivers the
group-theoretic section `σ : C₀ →* Q`. -/

section Splitting

variable (DD : DescData D) (Dsc : Descent D)

/-- `V` has exponent 2 (it is `M/T`, and `M` is elementary abelian). -/
theorem Vmod_exp2 (v : DD.Vmod) : v + v = 0 := by
  obtain ⟨m, hm⟩ := DD.hdesc_surj (Multiplicative.ofAdd v)
  have hmm : (m * m : ↥D.M) = 1 := Subtype.ext (D.helem m.1 m.2)
  exact Multiplicative.ofAdd.injective <| by
    rw [ofAdd_add, ofAdd_zero, ← hm, ← map_mul, hmm, map_one]

/-- **The fibre square identity** `ξ(iv, iv) = q̄(v)` (`lemma_6_21`'s `hξq`): the descended
cover's square map on `V` is the descended form.  Uses `D.hq` (cover square relation) pushed
down through `hqbar`. -/
theorem xi_diag (v : DD.Vmod) :
    xi Dsc (iV DD (Multiplicative.ofAdd v), iV DD (Multiplicative.ofAdd v)) = DD.qbar v := by
  set iv := iV DD (Multiplicative.ofAdd v) with hiv_def
  have hexp2 : Multiplicative.ofAdd v * Multiplicative.ofAdd v = 1 := by
    rw [← ofAdd_add, Vmod_exp2 DD v, ofAdd_zero]
  have hiv2 : iv * iv = 1 := by rw [hiv_def, ← map_mul, hexp2, map_one]
  have hxi : xi Dsc (iv, iv) = ccZsign Dsc (s0 Dsc iv * s0 Dsc iv) := by
    show ccZsign Dsc (s0 Dsc iv * s0 Dsc iv * (s0 Dsc (iv * iv))⁻¹) = _
    rw [hiv2, s0_one, inv_one, mul_one]
  rw [hxi]
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Dsc.N (s0 Dsc iv)
  have hdescP : descP Dsc (s0 Dsc iv) = iv := s0_sect Dsc iv
  rw [← hx, descP_mk] at hdescP
  have hpxM : D.C.p x ∈ D.M := by
    have hmem : iv ∈ (piQbar DD).ker := by
      rw [← iV_range]; exact ⟨Multiplicative.ofAdd v, rfl⟩
    rw [MonoidHom.mem_ker, ← hdescP, piQbar_mk] at hmem
    rw [← DD.hkerC0]; exact hmem
  have hdesc_eq : DD.descend ⟨D.C.p x, hpxM⟩ = Multiplicative.ofAdd v := by
    apply iV_injective DD
    rw [iV_spec, hdescP, hiv_def]
  rw [← hx, ← map_mul, D.hq x hpxM, map_pow]
  show ccZsign Dsc ((QuotientGroup.mk' Dsc.N D.C.z) ^ (D.q ⟨D.C.p x, hpxM⟩).val) = DD.qbar v
  rw [show (QuotientGroup.mk' Dsc.N D.C.z) = zbar Dsc from rfl, ccZsign_zbar_pow,
    DD.hqbar ⟨D.C.p x, hpxM⟩, hdesc_eq, toAdd_ofAdd]

include Dsc in
/-- **`descended_splitting`** (P-16d4, 2.2): in the zero-edge regime the extension
`1 → V → Q → C₀ → 1` splits — `∃ σ : C₀ →* Q` sectioning `piQbar`.  This is Lemma 6.21 at the
descended data, the paper's "`B/T ≅ V ⋊ C`".  d6 provides `DD`/`Dsc` from the `Enrichment`. -/
theorem descended_splitting :
    ∃ σ : DD.C0 →* Bg ⧸ D.T, ∀ cc : DD.C0, piQbar DD (σ cc) = cc :=
  SectionSix.lemma_6_21 (piQbar DD) (piQbar_surj DD) (iV DD) (iV_injective DD)
    (iV_range DD) (iV_conj DD) DD.qbar DD.hquad DD.hns DD.dat DD.hdat (xi Dsc)
    (xi_cocycle Dsc) (xi_diag DD Dsc)

end Splitting

/-! ## Prop 8.8, target side: the edge-killing shear

The completed-square identity (135), C-level half.  Given an **edge-killing shear** `a`
(`B_q̄(a c, ·) = γ c`, i.e. `hkill`), the general determinant class `κ⁰ + Γ_γ + inf δ`
shears to `κ⁰ + inf(Δ)` up to coboundary, where `Δ = δ + Θ⁰_q̄(a) + (γ ⌣ a)` is the total
scalar phase.  Direct instance of the proved `lemma_6_22` with the `γ + B♭a = 0` collapse.
The Γ-level (135) (which pulls this back along cor. 5.17) is d6, behind the P-13f firewall. -/

section Phase

variable {C : Type} [Group C] [Finite C]
  {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]

open SectionSix

/-- **The total scalar phase** `Δ = δ + Θ⁰_q̄(a) + (γ ⌣ a)` (the (134)-analog; the `γ⌣a`
cup term is the `lemma_6_22`-normalized form, D3 — the family is `∃`-bound in `prop_8_9`). -/
noncomputable def DeltaScalar (dat : FactorSet C V) (γ : C → V →+ ZMod 2)
    (δ : C × C → ZMod 2) (a : C → V) : C × C → ZMod 2 :=
  fun cd => δ cd + thetaPhase dat a cd + gammaCupA γ a cd

omit [Finite C] [Finite V] in
/-- **Prop 8.8, target side** (P-16d4, 2.6): the edge-killing shear collapses the general
determinant class to `κ⁰ + inf Δ` up to an explicit coboundary. -/
theorem prop_8_8_target (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (γ : C → V →+ ZMod 2) (δ : C × C → ZMod 2)
    (a : C → V) (ha : ∀ c d : C, a (c * d) = a c + c • a d)
    (hkill : ∀ (c : C) (v : V), polar q (a c) v + γ c v = 0) :
    ∃ w : V × C → ZMod 2, ∀ p q' : V × C,
      (kappa0 dat (shear a p) (shear a q') + gammaEdge γ (shear a p) (shear a q')
          + inflScalar δ (shear a p) (shear a q'))
        = (kappa0 dat p q' + inflScalar (DeltaScalar dat γ δ a) p q')
          + (w (p.1 + p.2 • q'.1, p.2 * q'.2) + w p + w q') := by
  obtain ⟨w, hw⟩ := lemma_6_22 q hq dat hdat γ δ a ha
  refine ⟨w, fun p q' => ?_⟩
  have hzero : (fun c ↦ γ c
      + AddMonoidHom.mk' (polar q (a c)) (fun v v' ↦ hq.polar_add_right (a c) v v'))
      = (fun _ : C => (0 : V →+ ZMod 2)) := by
    funext c
    ext v
    simp only [AddMonoidHom.add_apply, AddMonoidHom.mk'_apply, AddMonoidHom.zero_apply]
    rw [add_comm]; exact hkill c v
  have hge : gammaEdge (fun _ : C => (0 : V →+ ZMod 2)) = fun _ _ => (0 : ZMod 2) := by
    funext p1 q1; simp [gammaEdge]
  rw [hw p q', hzero, hge]
  unfold DeltaScalar
  ring

end Phase

/-! ## The polar-inverse supplier (`a_{χ,κ}`)

Finite `𝔽₂`-linear algebra: a nonsingular quadratic form's polar map `B♭ : V ↪ V∨` is
bijective, so every functional `φ` has a unique polar-preimage `a`.  d5 uses this to define
the (133) shift vectors `a_{χ,κ}` from `γ_χ + γ_κ` (cf. `lemma_8_5`'s `a`-data-with-spec). -/

section Polar

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

/-- **`exists_polar_inverse`** (P-16d4, 2.5): for nonsingular `q` on a finite `𝔽₂`-space,
every functional `φ` is `B_q(a, ·)` for some `a`. -/
theorem exists_polar_inverse (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (φ : Module.Dual (ZMod 2) V) : ∃ a : V, ∀ v : V, polar q a v = φ v := by
  haveI : FiniteDimensional (ZMod 2) V := Module.Finite.of_finite
  have hzl : ∀ w : V, polar q 0 w = 0 := by
    intro w; unfold polar; rw [zero_add, hq.map_zero, add_zero]; exact CharTwo.add_self_eq_zero _
  have hsmul : ∀ (c : ZMod 2) (u w : V), polar q (c • u) w = c • polar q u w := by
    intro c u w
    rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
    · rw [zero_smul, zero_smul, hzl]
    · rw [one_smul, one_smul]
  have hsmulr : ∀ (c : ZMod 2) (u w : V), polar q u (c • w) = c • polar q u w := by
    intro c u w; rw [polar_comm, hsmul, polar_comm]
  let Bflat : V →ₗ[ZMod 2] Module.Dual (ZMod 2) V :=
    LinearMap.mk₂ (ZMod 2) (polar q) hq.polar_add_left hsmul hq.polar_add_right hsmulr
  have hBapp : ∀ a v, Bflat a v = polar q a v := fun a v => rfl
  have hinj : Function.Injective Bflat := by
    rw [injective_iff_map_eq_zero]
    intro a ha
    by_contra hane
    obtain ⟨w, hw⟩ := hns a hane
    exact hw (by rw [← hBapp a w, ha]; rfl)
  obtain ⟨a, ha⟩ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      Subspace.dual_finrank_eq.symm).mp hinj φ
  exact ⟨a, fun v => by rw [← hBapp a v, ha]⟩

end Polar

/-! ## Lemma 8.7, count form: the `T`-twist torsor

In the zero-edge regime the `N`-complement has `edge ≡ 0`, so the (129) variation class of
every `T`-cocycle vanishes.  Hence twisting by a `T`-cocycle preserves the central relation
(`central_twist_iff`), and the fibres of the `T`-reduction map on `M`-lifts are free
`T`-cocycle torsors on which `Central` is constant.  This is the multiplicity `μ = #Z¹(T)`
of Lemma 8.7 (131)/(132) — the `V`-coordinate factorization.  The Γ-machinery is P-16a's
`twist`/`ob`/`central_iff_ob_eq_zero`, reused verbatim. -/

section Count

open CentralObstruction ContCoh

variable [TopologicalSpace Bg] [DiscreteTopology Bg]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M))
variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `N`-complement's variation cochain vanishes (`edge ≡ 0`). -/
theorem edgeQ_zero (Dsc : Descent D) (c : Bg ⧸ D.M) (t : ↥D.T) :
    edgeQ D (SN Dsc) c t = 0 :=
  edge_zero Dsc (Quotient.out c) t

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **`central_twist_iff`** (P-16d4, 2.4b): in the zero-edge regime, twisting an `M`-lift by
a `T`-cocycle preserves the central relation — the (129) variation class is zero because the
normal `N`-complement has vanishing edge.  This is what makes `Central` constant on the
`T`-cocycle torsors. -/
theorem central_twist_iff (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (u : TCocycle D ρ) (f : MLifts D ρ) :
    (twist D ρ u f).Central ↔ f.Central := by
  have hvfun : varCoc D ρ (SN Dsc) u = 0 := by
    funext gd; exact edgeQ_zero Dsc (ρ gd.1) ⟨u.u gd.2, u.mem gd.2⟩
  have hvz : (⟨varCoc D ρ (SN Dsc) u, varCoc_mem_Z2 D ρ (SN Dsc) htriv u⟩ : Z2 Γ (ZMod 2))
      = 0 := Subtype.ext hvfun
  rw [central_iff_ob_eq_zero D ρ htriv (twist D ρ u f), central_iff_ob_eq_zero D ρ htriv f,
    ob_twist D ρ (SN Dsc) htriv u f, hvz, map_zero, add_zero]

/-- The `T`-reduction of an `M`-lift: `red_T f = piT ∘ f : Γ → B/T`.  Its fibres are the
`T`-cocycle torsors of Lemma 8.7. -/
def redT (f : MLifts D ρ) : Γ → Bg ⧸ D.T := fun γ => QuotientGroup.mk (f.1 γ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `M` centralizes `T` (`T ≤ M`, `M` abelian) — makes the crossed condition rep-independent. -/
theorem M_cent_T {m : Bg} (hm : m ∈ D.M) {t : Bg} (ht : t ∈ D.T) : m * t * m⁻¹ = t := by
  rw [D.hcomm m hm t (D.hTM ht), mul_assoc, mul_inv_cancel, mul_one]

omit [DiscreteTopology Bg] [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)]
  [ContinuousSMul Γ (ZMod 2)] in
/-- Extensionality for `T`-cocycles (only the underlying function matters). -/
theorem tcocycle_ext {u v : TCocycle D ρ} (h : u.u = v.u) : u = v := by
  cases u with
  | mk uu um uc ucr => cases v with
    | mk vu vm vc vcr => simp only [] at h; subst h; rfl

/-- **The `T`-cocycle torsor** (P-16d4, 2.4a): fixing an `M`-lift `f₀`, the fibre of `red_T`
through `f₀` is a torsor under `Z¹_{Γ,ρ}(T)` — every `M`-lift with the same `T`-reduction is a
unique `T`-twist of `f₀`.  (Combined with `central_twist_iff`, this is the constant `μ`
multiplicity of (132).) -/
noncomputable def tcocycle_torsor_equiv (f₀ : MLifts D ρ) :
    TCocycle D ρ ≃ {f : MLifts D ρ // redT ρ f = redT ρ f₀} where
  toFun u := ⟨twist D ρ u f₀, by
    funext γ
    show QuotientGroup.mk (u.u γ * f₀.1 γ) = QuotientGroup.mk (f₀.1 γ)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (u.u γ)).mpr (u.mem γ), one_mul]⟩
  invFun f :=
    { u := fun γ => f.1.1 γ * (f₀.1 γ)⁻¹
      mem := fun γ => by
        have hred : (QuotientGroup.mk (f.1.1 γ) : Bg ⧸ D.T) = QuotientGroup.mk (f₀.1 γ) :=
          congrFun f.2 γ
        rw [← div_eq_mul_inv]; exact QuotientGroup.eq_iff_div_mem.mp hred
      cont := (continuous_of_discreteTopology (f := fun p : Bg × Bg => p.1 * p.2⁻¹)).comp
        (f.1.1.continuous_toFun.prodMk f₀.1.continuous_toFun)
      crossed := fun γ δ b hb => by
        -- rep-independence: `b = m · f₀ γ` with `m ∈ M`, and `M` centralizes `T`
        have hmM : b * (f₀.1 γ)⁻¹ ∈ D.M := by
          have heq : (QuotientGroup.mk b : Bg ⧸ D.M) = QuotientGroup.mk (f₀.1 γ) :=
            hb.trans (f₀.2 γ).symm
          rw [← div_eq_mul_inv]; exact QuotientGroup.eq_iff_div_mem.mp heq
        have htδ : f.1.1 δ * (f₀.1 δ)⁻¹ ∈ D.T := by
          have hred : (QuotientGroup.mk (f.1.1 δ) : Bg ⧸ D.T) = QuotientGroup.mk (f₀.1 δ) :=
            congrFun f.2 δ
          rw [← div_eq_mul_inv]; exact QuotientGroup.eq_iff_div_mem.mp hred
        have hconjT : f₀.1 γ * (f.1.1 δ * (f₀.1 δ)⁻¹) * (f₀.1 γ)⁻¹ ∈ D.T :=
          D.hT.conj_mem _ htδ _
        -- `b · (uδ) · b⁻¹ = f₀γ · uδ · f₀γ⁻¹` (the `M`-part cancels)
        have hbconj : b * (f.1.1 δ * (f₀.1 δ)⁻¹) * b⁻¹
            = f₀.1 γ * (f.1.1 δ * (f₀.1 δ)⁻¹) * (f₀.1 γ)⁻¹ := by
          obtain ⟨m, hmMset, hmeq⟩ : ∃ m ∈ D.M, b = m * f₀.1 γ :=
            ⟨b * (f₀.1 γ)⁻¹, hmM, by group⟩
          rw [hmeq]
          calc m * f₀.1 γ * (f.1.1 δ * (f₀.1 δ)⁻¹) * (m * f₀.1 γ)⁻¹
              = m * (f₀.1 γ * (f.1.1 δ * (f₀.1 δ)⁻¹) * (f₀.1 γ)⁻¹) * m⁻¹ := by group
            _ = f₀.1 γ * (f.1.1 δ * (f₀.1 δ)⁻¹) * (f₀.1 γ)⁻¹ := M_cent_T hmMset hconjT
        -- assemble via the homomorphism property of `f`, `f₀`
        show f.1.1 (γ * δ) * (f₀.1 (γ * δ))⁻¹
          = f.1.1 γ * (f₀.1 γ)⁻¹ * (b * (f.1.1 δ * (f₀.1 δ)⁻¹) * b⁻¹)
        rw [hbconj, map_mul, map_mul]
        group }
  left_inv u := by
    apply tcocycle_ext
    funext γ
    show u.u γ * f₀.1 γ * (f₀.1 γ)⁻¹ = u.u γ
    group
  right_inv f := by
    apply Subtype.ext
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    intro γ
    show f.1.1 γ * (f₀.1 γ)⁻¹ * f₀.1 γ = f.1.1 γ
    group

omit [ContinuousSMul Γ (ZMod 2)] in
/-- **Lemma 8.7, count form** (P-16d4, 2.4c): the central `M`-lifts sharing the `T`-reduction
of a fixed central lift `f₀` number exactly `#Z¹_{Γ,ρ}(T)` — the multiplicity `μ` of (132),
constant over the `V`-coordinate.  (`Central` is automatic on the torsor once `f₀` is central,
by `central_twist_iff`.)  d6 sums this over the liftable `V`-coordinates to reach `zBC`. -/
theorem lemma_8_7_count (Dsc : Descent D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (f₀ : MLifts D ρ) (hf₀ : f₀.Central) :
    Nat.card {f : MLifts D ρ // f.Central ∧ redT ρ f = redT ρ f₀}
      = Nat.card (TCocycle D ρ) := by
  -- `Central` is automatic on the `red_T`-fibre through the central `f₀`
  have hauto : ∀ f : MLifts D ρ, redT ρ f = redT ρ f₀ → f.Central := by
    intro f hf
    have hf_eq : f = twist D ρ ((tcocycle_torsor_equiv ρ f₀).symm ⟨f, hf⟩) f₀ :=
      congrArg Subtype.val ((tcocycle_torsor_equiv ρ f₀).apply_symm_apply ⟨f, hf⟩).symm
    rw [hf_eq]
    exact (central_twist_iff ρ Dsc htriv _ f₀).mpr hf₀
  rw [Nat.card_congr
      (Equiv.subtypeEquivRight (fun f => ⟨fun h => h.2, fun h => ⟨hauto f h, h⟩⟩)),
    Nat.card_congr (tcocycle_torsor_equiv ρ f₀).symm]

end Count

/-! ## The phase covers: `centralCoverOfCocycle`  (P-16d5)

The twisted product `𝔽₂ ×_δ C₀` of a **normalized** `𝔽₂`-valued 2-cocycle `δ` on a finite
group `C₀` — a central double cover of `C₀`.  This is the (133)/(134) phase-cover
constructor: d6's `prop_8_9` phase family is `ζ ↦ centralCoverOfCocycle (Δ_{χ,κ})`, with the
scalar `Δ` produced by `prop_8_8_target`/`DeltaScalar`.  Multiplicative analog of P-15i's
additive `Transgression.Twisted`. -/

/-- Carrier of the twisted product `𝔽₂ ×_δ C₀` (`δ` a phantom parameter). -/
private structure TwistCov {C0 : Type} (δ : C0 × C0 → ZMod 2) where
  /-- The central `𝔽₂`-coordinate. -/
  z : ZMod 2
  /-- The base `C₀`-coordinate. -/
  c : C0

namespace TwistCov

variable {C0 : Type} [Group C0] {δ : C0 × C0 → ZMod 2}

private instance : One (TwistCov δ) := ⟨⟨0, 1⟩⟩
private instance : Mul (TwistCov δ) := ⟨fun p q => ⟨p.z + q.z + δ (p.c, q.c), p.c * q.c⟩⟩
private instance : Inv (TwistCov δ) := ⟨fun p => ⟨p.z + δ (p.c⁻¹, p.c), p.c⁻¹⟩⟩

/-- `TwistCov δ ≃ ZMod 2 × C₀` (for the finiteness instance). -/
private def equivProd : TwistCov δ ≃ ZMod 2 × C0 where
  toFun p := (p.z, p.c)
  invFun q := ⟨q.1, q.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end TwistCov

/-- **The phase cover** (P-16d5): the central double cover `𝔽₂ ×_δ C₀ ↠ C₀` of a normalized
`𝔽₂`-2-cocycle `δ` — multiplication `(s,c)(t,d) = (s+t+δ(c,d), cd)`, kernel `⟨z⟩` with
`z = (1,1)`.  d6 instantiates `δ := DeltaScalar …` (the (134) total phase). -/
noncomputable def centralCoverOfCocycle {C0 : Type} [Group C0] [Finite C0]
    (δ : C0 × C0 → ZMod 2)
    (hcoc : ∀ g h k : C0, δ (h, k) + δ (g, h * k) = δ (g * h, k) + δ (g, h))
    (hone_l : ∀ c : C0, δ (1, c) = 0) (hone_r : ∀ c : C0, δ (c, 1) = 0) :
    CentralCover C0 :=
  letI grp : Group (TwistCov δ) :=
    { mul := (· * ·), one := 1, inv := Inv.inv, npow := npowRec, zpow := zpowRec
      mul_assoc := fun p q r => by
        show TwistCov.mk (p.z + q.z + δ (p.c, q.c) + r.z + δ (p.c * q.c, r.c))
            (p.c * q.c * r.c)
          = TwistCov.mk (p.z + (q.z + r.z + δ (q.c, r.c)) + δ (p.c, q.c * r.c))
            (p.c * (q.c * r.c))
        congr 1
        · linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
            hcoc p.c q.c r.c
        · exact mul_assoc p.c q.c r.c
      one_mul := fun p => by
        show TwistCov.mk (0 + p.z + δ (1, p.c)) (1 * p.c) = p
        rw [hone_l p.c, add_zero, zero_add, one_mul]
      mul_one := fun p => by
        show TwistCov.mk (p.z + 0 + δ (p.c, 1)) (p.c * 1) = p
        rw [hone_r p.c, add_zero, add_zero, mul_one]
      inv_mul_cancel := fun p => by
        show TwistCov.mk (p.z + δ (p.c⁻¹, p.c) + p.z + δ (p.c⁻¹, p.c)) (p.c⁻¹ * p.c)
          = TwistCov.mk 0 1
        rw [inv_mul_cancel]
        exact congrArg₂ TwistCov.mk
          ((by decide : ∀ a b : ZMod 2, a + b + a + b = 0) p.z (δ (p.c⁻¹, p.c))) rfl }
  letI : Finite (TwistCov δ) := Finite.of_equiv _ TwistCov.equivProd.symm
  letI : TopologicalSpace (TwistCov δ) := ⊥
  haveI : DiscreteTopology (TwistCov δ) := ⟨rfl⟩
  let pc : TwistCov δ →* C0 :=
    { toFun := fun p => p.c, map_one' := rfl, map_mul' := fun _ _ => rfl }
  { cover := TwistCov δ
    group := grp
    p := pc
    surj := fun c => ⟨⟨0, c⟩, rfl⟩
    z := ⟨1, 1⟩
    z_ne := fun h => absurd (congrArg TwistCov.z h : (1 : ZMod 2) = 0) one_ne_zero
    z_sq := by
      show TwistCov.mk (1 + 1 + δ (1, 1)) (1 * 1) = TwistCov.mk 0 1
      rw [hone_l 1]; exact congrArg₂ TwistCov.mk (by decide) (one_mul 1)
    central := fun x => by
      show TwistCov.mk (1 + x.z + δ (1, x.c)) (1 * x.c)
        = TwistCov.mk (x.z + 1 + δ (x.c, 1)) (x.c * 1)
      rw [hone_l x.c, hone_r x.c]
      exact congrArg₂ TwistCov.mk (by ring) (by rw [one_mul, mul_one])
    ker_eq := by
      ext x
      obtain ⟨xz, xc⟩ := x
      rw [MonoidHom.mem_ker, Subgroup.mem_zpowers_iff]
      constructor
      · intro hx
        have hc : xc = 1 := hx
        subst hc
        refine ⟨(xz.val : ℤ), ?_⟩
        rw [zpow_natCast]
        rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) xz with hz | hz
        · subst hz; rfl
        · subst hz; rw [show ((1 : ZMod 2).val) = 1 from rfl, pow_one]
      · rintro ⟨n, hn⟩
        show xc = 1
        have hpc := congrArg pc hn
        rw [map_zpow, show pc (⟨1, 1⟩ : TwistCov δ) = 1 from rfl, one_zpow] at hpc
        exact hpc.symm
    }

/-- **The phase family** (P-16d5): the `prop_8_9`-shaped phase-cover family
`DT → CentralCover C₀` from a family of normalized 2-cocycles.  d6 supplies
`Δ ζ := DeltaScalar …` (the (134) total phase `Δ_{χ,κ}`), giving `prop_8_9`'s `phase`
component directly; the shared `(μ, G⁰, DT)` are `lemma_8_7_count`'s `#Z¹(T)`, `gaussSum`
of the enrichment form, and the `(T^∨)^C` index. -/
noncomputable def phaseFamily {C0 : Type} [Group C0] [Finite C0] {DT : Type}
    (Δ : DT → C0 × C0 → ZMod 2)
    (hcoc : ∀ ζ (g h k : C0), Δ ζ (h, k) + Δ ζ (g, h * k) = Δ ζ (g * h, k) + Δ ζ (g, h))
    (hl : ∀ ζ (c : C0), Δ ζ (1, c) = 0) (hr : ∀ ζ (c : C0), Δ ζ (c, 1) = 0) :
    DT → CentralCover C0 :=
  fun ζ => centralCoverOfCocycle (Δ ζ) (hcoc ζ) (hl ζ) (hr ζ)

/-- **The canonical section of the twisted-product cover** (P-16d6c2 export): the phase cover
`𝔽₂ ×_δ C₀` admits a normalized set-section `s` with multiplication defect exactly `δ`
(`s c · s d = z^{δ(c,d)} · s(cd)`).  This is the (only) internals fact the phase-obstruction
layer needs: a lift of `ρ` through the cover exists iff `ρ^*δ` is a continuous coboundary
(`GQ2/PhaseObstruction.lean`). -/
theorem centralCoverOfCocycle_exists_section {C0 : Type} [Group C0] [Finite C0]
    (δ : C0 × C0 → ZMod 2)
    (hcoc : ∀ g h k : C0, δ (h, k) + δ (g, h * k) = δ (g * h, k) + δ (g, h))
    (hone_l : ∀ c : C0, δ (1, c) = 0) (hone_r : ∀ c : C0, δ (c, 1) = 0) :
    ∃ s : C0 → (centralCoverOfCocycle δ hcoc hone_l hone_r).cover,
      (∀ c, (centralCoverOfCocycle δ hcoc hone_l hone_r).p (s c) = c) ∧ s 1 = 1 ∧
        ∀ c d, s c * s d
          = (centralCoverOfCocycle δ hcoc hone_l hone_r).z ^ (δ (c, d)).val * s (c * d) := by
  refine ⟨fun c => ⟨0, c⟩, fun c => rfl, rfl, fun c d => ?_⟩
  rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) (δ (c, d)) with hδ | hδ
  · -- `z^0 = 1`: both sides are explicit `TwistCov.mk` terms
    rw [hδ]
    show TwistCov.mk (0 + 0 + δ (c, d)) (c * d)
      = TwistCov.mk (0 + 0 + δ (1, c * d)) (1 * (c * d))
    rw [hδ, hone_l, one_mul]
  · -- `z^1 = 1 * z` (`npowRec`); unfold both multiplications
    rw [hδ]
    show TwistCov.mk (0 + 0 + δ (c, d)) (c * d)
      = TwistCov.mk ((0 + 1 + δ (1, 1)) + 0 + δ (1 * 1, c * d)) ((1 * 1) * (c * d))
    rw [hδ, one_mul, one_mul, hone_l, hone_l]
    norm_num

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * cor 5.17 = ⟦cor-adjointboundary⟧
  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 6.21 = ⟦lem-transgression⟧
  * Lemma 8.7 = ⟦lem-affinelifting⟧
  * Prop 8.8 = ⟦prop-phaseidentity⟧
-/
