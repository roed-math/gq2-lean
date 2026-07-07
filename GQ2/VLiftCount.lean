import GQ2.VCocycle
import GQ2.PhaseObstruction

/-!
# P-16d6c1b: the affine `T`-lifting obstruction over the `V`-cocycle layer (Lemma 8.7, (131))

For a `V`-coordinate `c ∈ Z¹_{Γ,ρ}(V)` (c1a's `VCocycle`), when is `g_c = qOfCocycle c` the
`T`-reduction of an actual — and central — `M`-lift?  Following the paper's Lemma 8.7 (p. 41)
at cocycle level:

* **`tDef`** — the `T`-valued defect of the pointwise lift `γ ↦ mV(c γ)·uσ(ρ'γ)` of `g_c`
  (the paper's "`∂c + ρ^*e`" in one piece; `CountSections` fixes the normalized set-sections).
* **`TCharC`** — the `C`-invariant `𝔽₂`-character group `D = (T^∨)^C` (the paper's phase index).
* **`chiDef`** — the `χ`-pushforward `χ_*(tDef c) ∈ Z²(Γ,𝔽₂)` (`chiDef_mem_Z2`: `C`-invariance
  of `χ` kills the crossed twist), and **`betaChi χ c := ι_Γ(χ_* tDef c)`** — the `χ`-component
  of the `T`-lifting obstruction.
* **`TLiftable`** (131): `c` is the `V`-coordinate of an `M`-lift; `tliftable_iff` characterizes
  it — the easy direction (`betaChi ≡ 0`) is generic (`betaChi_of_tliftable`), the converse is
  the source-specific **separation** `hsep` (the `(T^∨)^C ≅ H²_{Γ,ρ}(T)^∨` perfectness of
  cor. 5.17/5.16, threaded to the d6e residue list — the d6a `hsep_hom` idiom).
* **`betaXi`** — the scalar obstruction `ι_Γ(g_c^*ξ)` through the descended cover `Q̃ = B̃/N`
  (`xi` of P-16d4), with **`central_iff_betaXi`**: an `M`-lift over `g_c` is central iff
  `betaXi c = 0` (the bridge from `CentralObstruction.ob` through `mk_N`).
* **`mem_centralImage_iff`**: `c` is the `V`-coordinate of a **central** `M`-lift iff
  `TLiftable c ∧ betaXi c = 0` — the complete (131)-characterization the master count consumes.

Everything is source-generic std-3; the Γ-specific inputs (`hsep`, and the counting facts) are
threaded as hypotheses.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-! ## The `C`-invariant character group `D = (T^∨)^C` -/

variable (D) in
/-- **The `C`-invariant `𝔽₂`-characters of `T`** (the paper's `D = (T^∨)^C`, p. 42):
additive characters `T → 𝔽₂` invariant under the full `B`-conjugation (which factors through
`C` since `M` centralizes `T`).  An additive subgroup of the function space. -/
def TCharC : AddSubgroup (↥D.T → ZMod 2) where
  carrier := {χ | (∀ t t' : ↥D.T, χ (t * t') = χ t + χ t') ∧
    ∀ (bb : Bg) (t : ↥D.T), χ ⟨bb * t * bb⁻¹, D.hT.conj_mem t.1 t.2 bb⟩ = χ t}
  zero_mem' := ⟨fun _ _ => by simp, fun _ _ => rfl⟩
  add_mem' := fun {χ ψ} hχ hψ =>
    ⟨fun t t' => by
      show χ (t * t') + ψ (t * t') = (χ t + ψ t) + (χ t' + ψ t')
      rw [hχ.1 t t', hψ.1 t t']; ring,
     fun bb t => by
      show χ _ + ψ _ = χ t + ψ t
      rw [hχ.2 bb t, hψ.2 bb t]⟩
  neg_mem' := fun {χ} hχ =>
    ⟨fun t t' => by
      show -χ (t * t') = -χ t + -χ t'
      rw [hχ.1 t t']; ring,
     fun bb t => by
      show -χ _ = -χ t
      rw [hχ.2 bb t]⟩

instance : Finite ↥(TCharC D) := by
  haveI : Finite (↥D.T → ZMod 2) := Pi.finite
  exact Subtype.finite

namespace TCharC

variable {χ : ↥(TCharC D)}

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem map_mul (χ : ↥(TCharC D)) (t t' : ↥D.T) : χ.1 (t * t') = χ.1 t + χ.1 t' :=
  χ.2.1 t t'

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem map_one (χ : ↥(TCharC D)) : χ.1 1 = 0 := by
  have h : χ.1 (1 * 1) = χ.1 1 + χ.1 1 := χ.2.1 1 1
  rw [one_mul] at h
  have hchar : ∀ a : ZMod 2, a = a + a → a = 0 := by decide
  exact hchar _ h

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem map_inv (χ : ↥(TCharC D)) (t : ↥D.T) : χ.1 t⁻¹ = χ.1 t := by
  have h := χ.2.1 t t⁻¹
  rw [mul_inv_cancel, map_one] at h
  have : χ.1 t + χ.1 t⁻¹ = 0 := h.symm
  have hchar : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact hchar _ _ this

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem conj_invariant (χ : ↥(TCharC D)) (bb : Bg) (t : ↥D.T)
    (h : bb * ↑t * bb⁻¹ ∈ D.T) : χ.1 ⟨bb * ↑t * bb⁻¹, h⟩ = χ.1 t :=
  χ.2.2 bb t

end TCharC

/-! ## The section data and the pointwise `B`-lift -/

variable (DD : DescData D)

/-- **The section pair for the master count**: normalized set-sections `mV` of `descend` and
`uσ` of `piT` over the splitting `σ`. -/
structure CountSections (σ : DD.C0 →* Bg ⧸ D.T) where
  /-- A set-section of `descend : M ↠ V`. -/
  mV : DD.Vmod → ↥D.M
  descend_mV : ∀ v, DD.descend (mV v) = Multiplicative.ofAdd v
  mV_zero : mV 0 = 1
  /-- A set-lift of `σ : C₀ → Q` through `piT : B ↠ Q`. -/
  uσ : DD.C0 → Bg
  piT_uσ : ∀ cc, piT (D := D) (uσ cc) = σ cc
  uσ_one : uσ 1 = 1

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Section pairs exist (finite surjections; normalize at the identity). -/
theorem countSections_exist (σ : DD.C0 →* Bg ⧸ D.T) : Nonempty (CountSections DD σ) := by
  classical
  -- `mV`: a section of `descend`, shifted to be normalized
  have hdesc := DD.hdesc_surj
  set m0 : DD.Vmod → ↥D.M :=
    fun v => Function.surjInv hdesc (Multiplicative.ofAdd v) with hm0
  have hm0spec : ∀ v, DD.descend (m0 v) = Multiplicative.ofAdd v :=
    fun v => Function.surjInv_eq hdesc _
  set mV : DD.Vmod → ↥D.M := fun v => m0 v * (m0 0)⁻¹ with hmV
  have hmVspec : ∀ v, DD.descend (mV v) = Multiplicative.ofAdd v := by
    intro v
    rw [hmV]
    show DD.descend (m0 v * (m0 0)⁻¹) = Multiplicative.ofAdd v
    rw [map_mul, map_inv, hm0spec, hm0spec, ofAdd_zero, inv_one, mul_one]
  -- `uσ`: a set-lift of `σ` through `piT`, shifted to be normalized
  have hsurj : Function.Surjective (piT (D := D)) := QuotientGroup.mk'_surjective D.T
  set u0 : DD.C0 → Bg := fun cc => Function.surjInv hsurj (σ cc) with hu0
  have hu0spec : ∀ cc, piT (D := D) (u0 cc) = σ cc := fun cc => Function.surjInv_eq hsurj _
  set uσ : DD.C0 → Bg := fun cc => u0 cc * (u0 1)⁻¹ with huσ
  have huσspec : ∀ cc, piT (D := D) (uσ cc) = σ cc := by
    intro cc
    rw [huσ]
    show piT (D := D) (u0 cc * (u0 1)⁻¹) = σ cc
    rw [map_mul, map_inv, hu0spec, hu0spec, map_one, inv_one, mul_one]
  exact ⟨⟨mV, hmVspec, by rw [hmV]; show m0 0 * (m0 0)⁻¹ = 1; group,
    uσ, huσspec, by rw [huσ]; show u0 1 * (u0 1)⁻¹ = 1; group⟩⟩

variable {DD}
variable {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}

/-- The pointwise `B`-lift `γ ↦ mV(c γ) · uσ(ρ'γ)` of `g_c = qOfCocycle c`. -/
noncomputable def fLift (c : VCocycle DD ρ) : Γ → Bg :=
  fun γ => (S.mV (c.c γ) : Bg) * S.uσ (rho0 DD ρ γ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `mV` covers `iV` through `piT`. -/
theorem piT_mV (v : DD.Vmod) :
    piT (D := D) ((S.mV v : Bg)) = iV DD (Multiplicative.ofAdd v) := by
  rw [← S.descend_mV v, iV_spec]

variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

include hσ in
/-- The pointwise lift lies over `g_c` through `piT`. -/
theorem fLift_mk (c : VCocycle DD ρ) (γ : Γ) :
    piT (D := D) (fLift S c γ) = (qOfCocycle DD ρ σ hσ c).1 γ := by
  rw [fLift, map_mul, piT_mV, S.piT_uσ, qOfCocycle_apply]

include hσ in
/-- The defect of the pointwise lift lies in `T`. -/
theorem fLift_defect_mem (c : VCocycle DD ρ) (γ δ : Γ) :
    fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹ ∈ D.T := by
  have h : piT (D := D) (fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, fLift_mk S hσ, fLift_mk S hσ, fLift_mk S hσ,
      ← map_mul (qOfCocycle DD ρ σ hσ c).1 γ δ, mul_inv_cancel]
  rwa [piT, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

/-- **The `T`-valued defect** of the pointwise lift — the paper's `∂c + ρ^*e` in one piece
(Lemma 8.7's normalized-cocycle representative, pulled back along the graph of `c`). -/
noncomputable def tDef (c : VCocycle DD ρ) (p : Γ × Γ) : ↥D.T :=
  ⟨fLift S c p.1 * fLift S c p.2 * (fLift S c (p.1 * p.2))⁻¹, fLift_defect_mem S hσ c p.1 p.2⟩

/-- The `χ`-pushforward of the defect. -/
noncomputable def chiDef (χ : ↥(TCharC D)) (c : VCocycle DD ρ) : Γ × Γ → ZMod 2 :=
  fun p => χ.1 (tDef S hσ c p)

/-- The pointwise lift is continuous (through the discrete `Q × B/M`, since `V` carries no
topology — the `iV`-embedded continuity of `c` is inverted by injectivity). -/
theorem fLift_continuous (c : VCocycle DD ρ) : Continuous (fLift S c) := by
  classical
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
    fun a b h => iV_ofAdd_inj DD h
  have heq : fLift S c = (fun q : (Bg ⧸ D.T) × (Bg ⧸ D.M) =>
      (S.mV (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) q.1) : Bg)
        * S.uσ (liftC0 DD q.2))
      ∘ (fun γ => (iV DD (Multiplicative.ofAdd (c.c γ)), ρ γ)) := by
    funext γ
    show (S.mV (c.c γ) : Bg) * S.uσ (rho0 DD ρ γ)
      = (S.mV (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
          (iV DD (Multiplicative.ofAdd (c.c γ)))) : Bg) * S.uσ (liftC0 DD (ρ γ))
    rw [Function.leftInverse_invFun hinj (c.c γ)]
    rfl
  rw [heq]
  exact continuous_of_discreteTopology.comp (c.cont.prodMk ρ.continuous_toFun)

variable [IsTopologicalGroup Γ]

include hσ in
/-- The `T`-defect is continuous. -/
theorem tDef_continuous (c : VCocycle DD ρ) : Continuous (tDef S hσ c) := by
  apply Continuous.subtype_mk
  have h3 : Continuous (fun p : Γ × Γ => (fLift S c p.1, fLift S c p.2, fLift S c (p.1 * p.2))) :=
    ((fLift_continuous S c).comp continuous_fst).prodMk
      (((fLift_continuous S c).comp continuous_snd).prodMk
        ((fLift_continuous S c).comp continuous_mul))
  exact (continuous_of_discreteTopology
    (f := fun x : Bg × Bg × Bg => x.1 * x.2.1 * x.2.2⁻¹)).comp h3

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

include hσ in
omit [ContinuousSMul Γ (ZMod 2)] in
/-- **The `χ`-pushforward of the defect is a continuous 2-cocycle**: the nonabelian defect
identity conjugates by `fLift`, and `C`-invariance of `χ` kills the conjugation. -/
theorem chiDef_mem_Z2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (χ : ↥(TCharC D)) (c : VCocycle DD ρ) : chiDef S hσ χ c ∈ Z2 Γ (ZMod 2) := by
  refine mem_Z2_iff.mpr ⟨?_, ?_⟩
  · exact (continuous_of_discreteTopology (f := fun t : ↥D.T => χ.1 t)).comp
      (tDef_continuous S hσ c)
  · intro γ δ ε
    rw [htriv]
    -- the nonabelian defect identity, raw
    have hraw : (tDef S hσ c (γ, δ) : Bg) * (tDef S hσ c (γ * δ, ε) : Bg)
        = fLift S c γ * (tDef S hσ c (δ, ε) : Bg) * (fLift S c γ)⁻¹
            * (tDef S hσ c (γ, δ * ε) : Bg) := by
      show fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹
            * (fLift S c (γ * δ) * fLift S c ε * (fLift S c (γ * δ * ε))⁻¹)
          = fLift S c γ * (fLift S c δ * fLift S c ε * (fLift S c (δ * ε))⁻¹)
              * (fLift S c γ)⁻¹
            * (fLift S c γ * fLift S c (δ * ε) * (fLift S c (γ * (δ * ε)))⁻¹)
      rw [show γ * δ * ε = γ * (δ * ε) from mul_assoc γ δ ε]
      group
    -- lift to the subtype and push through `χ`
    have hsub : tDef S hσ c (γ, δ) * tDef S hσ c (γ * δ, ε)
        = (⟨fLift S c γ * ↑(tDef S hσ c (δ, ε)) * (fLift S c γ)⁻¹,
            D.hT.conj_mem _ (tDef S hσ c (δ, ε)).2 _⟩ : ↥D.T)
          * tDef S hσ c (γ, δ * ε) := by
      apply Subtype.ext
      show (tDef S hσ c (γ, δ) : Bg) * (tDef S hσ c (γ * δ, ε) : Bg)
        = fLift S c γ * ↑(tDef S hσ c (δ, ε)) * (fLift S c γ)⁻¹ * ↑(tDef S hσ c (γ, δ * ε))
      exact hraw
    have hkey : χ.1 (tDef S hσ c (γ, δ)) + χ.1 (tDef S hσ c (γ * δ, ε))
        = χ.1 (tDef S hσ c (δ, ε)) + χ.1 (tDef S hσ c (γ, δ * ε)) := by
      calc χ.1 (tDef S hσ c (γ, δ)) + χ.1 (tDef S hσ c (γ * δ, ε))
          = χ.1 (tDef S hσ c (γ, δ) * tDef S hσ c (γ * δ, ε)) :=
            (TCharC.map_mul χ _ _).symm
        _ = χ.1 ((⟨fLift S c γ * ↑(tDef S hσ c (δ, ε)) * (fLift S c γ)⁻¹,
              D.hT.conj_mem _ (tDef S hσ c (δ, ε)).2 _⟩ : ↥D.T)
            * tDef S hσ c (γ, δ * ε)) := by rw [hsub]
        _ = χ.1 (⟨fLift S c γ * ↑(tDef S hσ c (δ, ε)) * (fLift S c γ)⁻¹,
              D.hT.conj_mem _ (tDef S hσ c (δ, ε)).2 _⟩ : ↥D.T)
            + χ.1 (tDef S hσ c (γ, δ * ε)) := TCharC.map_mul χ _ _
        _ = χ.1 (tDef S hσ c (δ, ε)) + χ.1 (tDef S hσ c (γ, δ * ε)) := by
            rw [TCharC.conj_invariant χ (fLift S c γ) (tDef S hσ c (δ, ε))]
    show chiDef S hσ χ c (δ, ε) + chiDef S hσ χ c (γ, δ * ε)
      = chiDef S hσ χ c (γ * δ, ε) + chiDef S hσ χ c (γ, δ)
    unfold chiDef
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hkey

/-- **The `χ`-component of the `T`-lifting obstruction**: `β_χ(c) := ι_Γ(χ_* tDef c)`. -/
noncomputable def betaChi (χ : ↥(TCharC D)) (c : VCocycle DD ρ) : ZMod 2 :=
  iotaB (chiDef S hσ χ c)

/-! ## (131): the `T`-liftability characterization -/

/-- **`T`-liftability** of a `V`-coordinate: `c` is the `T`-reduction of an actual `M`-lift. -/
def TLiftable (c : VCocycle DD ρ) : Prop :=
  ∃ f : MLifts D ρ, redTLift DD f = qOfCocycle DD ρ σ hσ c

include hσ in
omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **The generic direction of (131)**: a liftable `V`-coordinate has vanishing `χ`-obstruction
for every `χ` — the defect of the pointwise lift is a crossed coboundary, and `χ` (being
`C`-invariant) sends it to a plain continuous coboundary. -/
theorem betaChi_of_tliftable (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    {c : VCocycle DD ρ} (hc : TLiftable hσ c) (χ : ↥(TCharC D)) :
    betaChi S hσ χ c = 0 := by
  obtain ⟨f, hf⟩ := hc
  -- the discrepancy `s γ = fLift γ · (f γ)⁻¹` lands in `T`
  have hmemT : ∀ γ : Γ, fLift S c γ * (f.1 γ)⁻¹ ∈ D.T := by
    intro γ
    have h1 : piT (D := D) (fLift S c γ * (f.1 γ)⁻¹) = 1 := by
      have hfγ : piT (D := D) (f.1 γ) = (qOfCocycle DD ρ σ hσ c).1 γ := by
        have := congrArg (fun g : QLiftsOver DD ρ => g.1 γ) hf
        simpa [redTLift_apply] using this
      rw [map_mul, map_inv, fLift_mk S hσ, hfγ, mul_inv_cancel]
    rwa [piT, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set s : Γ → ↥D.T := fun γ => ⟨fLift S c γ * (f.1 γ)⁻¹, hmemT γ⟩ with hs
  -- the defect is the crossed coboundary of `s`
  have hdef : ∀ γ δ : Γ, (tDef S hσ c (γ, δ) : Bg)
      = ↑(s γ) * (f.1 γ * ↑(s δ) * (f.1 γ)⁻¹) * (↑(s (γ * δ)))⁻¹ := by
    intro γ δ
    show fLift S c γ * fLift S c δ * (fLift S c (γ * δ))⁻¹ = _
    have h1 : fLift S c γ = ↑(s γ) * f.1 γ := by rw [hs]; group
    have h2 : fLift S c δ = ↑(s δ) * f.1 δ := by rw [hs]; group
    have h3 : fLift S c (γ * δ) = ↑(s (γ * δ)) * f.1 (γ * δ) := by rw [hs]; group
    rw [h1, h2, h3, map_mul]
    group
  -- push through `χ`: a plain coboundary
  refine iotaB_of_mem_B2 ?_
  refine ⟨fun γ => χ.1 (s γ), ?_, ?_⟩
  · have hscont : Continuous s := by
      apply Continuous.subtype_mk
      exact ((fLift_continuous S c).mul (f.1.continuous_toFun.inv))
    exact (continuous_of_discreteTopology (f := fun t : ↥D.T => χ.1 t)).comp hscont
  · funext p
    obtain ⟨γ, δ⟩ := p
    show γ • χ.1 (s δ) - χ.1 (s (γ * δ)) + χ.1 (s γ) = chiDef S hσ χ c (γ, δ)
    rw [htriv]
    have hsub : tDef S hσ c (γ, δ)
        = s γ * (⟨f.1 γ * ↑(s δ) * (f.1 γ)⁻¹, D.hT.conj_mem _ (s δ).2 _⟩ : ↥D.T)
          * (s (γ * δ))⁻¹ := by
      apply Subtype.ext
      show (tDef S hσ c (γ, δ) : Bg) = ↑(s γ) * (f.1 γ * ↑(s δ) * (f.1 γ)⁻¹) * (↑(s (γ * δ)))⁻¹
      exact hdef γ δ
    have hval : chiDef S hσ χ c (γ, δ) = χ.1 (s γ) + χ.1 (s δ) + χ.1 (s (γ * δ)) := by
      show χ.1 (tDef S hσ c (γ, δ)) = _
      rw [hsub, TCharC.map_mul, TCharC.map_mul, TCharC.map_inv,
        TCharC.conj_invariant χ (f.1 γ) (s δ)]
    rw [hval]
    have hchar : ∀ a b cc : ZMod 2, a - cc + b = b + a + cc := by decide
    exact hchar _ _ _

/-! ## The scalar obstruction through the descended cover -/

variable (Dsc : Descent D)

/-- **The scalar obstruction** of a `V`-coordinate: `ι_Γ(g_c^* ξ)`, the lifting obstruction of
`g_c` through the descended central double cover `Q̃ = B̃/N ↠ Q` (defect cocycle `ξ`). -/
noncomputable def betaXi (c : VCocycle DD ρ) : ZMod 2 :=
  iotaB (pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc))

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `ccZsign` of an inverse kernel element. -/
theorem ccZsign_inv {x : covQ Dsc} (hx : x ∈ (descP Dsc).ker) :
    ccZsign Dsc x⁻¹ = ccZsign Dsc x := by
  rcases descKerCases Dsc hx with rfl | rfl
  · rw [inv_one]
  · rw [show (zbar Dsc)⁻¹ = zbar Dsc from inv_eq_of_mul_eq_one_left (zbar_sq Dsc)]

omit [TopologicalSpace Bg] in
/-- The descended cover is discrete (quotient of the discrete cover). -/
theorem discreteTopology_covQ : DiscreteTopology (covQ Dsc) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  have h1 : IsOpen (QuotientGroup.mk ⁻¹' {c} : Set D.C.cover) := isOpen_discrete _
  have h2 : QuotientGroup.mk '' (QuotientGroup.mk ⁻¹' {c} : Set D.C.cover) = {c} :=
    Set.image_preimage_eq _ QuotientGroup.mk_surjective
  rw [← h2]
  exact QuotientGroup.isOpenMap_coe _ h1

omit [TopologicalSpace Bg] [DiscreteTopology Bg] [IsTopologicalGroup Γ]
  [ContinuousSMul Γ (ZMod 2)] in
/-- **Sign-defect well-definedness**: two continuous pointwise lifts of the same continuous
homomorphic map through `descP` have `z̄`-sign defect cochains differing by a continuous
coboundary — hence the same `B²`-membership. -/
theorem descP_lift_sign_mem_B2_iff (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    {L1 L2 : Γ → covQ Dsc} (hL1 : Continuous L1) (hL2 : Continuous L2)
    (hover : ∀ γ, descP Dsc (L1 γ) = descP Dsc (L2 γ))
    (hmul : ∀ γ δ : Γ, descP Dsc (L2 (γ * δ)) = descP Dsc (L2 γ) * descP Dsc (L2 δ)) :
    ((fun p : Γ × Γ => ccZsign Dsc (L1 p.1 * L1 p.2 * (L1 (p.1 * p.2))⁻¹))
        ∈ B2 Γ (ZMod 2)) ↔
      (fun p : Γ × Γ => ccZsign Dsc (L2 p.1 * L2 p.2 * (L2 (p.1 * p.2))⁻¹))
        ∈ B2 Γ (ZMod 2) := by
  haveI : DiscreteTopology (covQ Dsc) := discreteTopology_covQ Dsc
  -- the kernel discrepancy and the defect kernel-memberships
  set n : Γ → covQ Dsc := fun γ => L1 γ * (L2 γ)⁻¹ with hn
  have hnker : ∀ γ, n γ ∈ (descP Dsc).ker := by
    intro γ
    rw [MonoidHom.mem_ker]
    show descP Dsc (L1 γ * (L2 γ)⁻¹) = 1
    rw [map_mul, map_inv, hover, mul_inv_cancel]
  have hd2ker : ∀ γ δ : Γ, L2 γ * L2 δ * (L2 (γ * δ))⁻¹ ∈ (descP Dsc).ker := by
    intro γ δ
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hmul, mul_inv_cancel]
  -- the defect comparison: `d1 = nγ · nδ · n(γδ)⁻¹ · d2` (kernel elements are central)
  have hcomp : ∀ γ δ : Γ, L1 γ * L1 δ * (L1 (γ * δ))⁻¹
      = n γ * n δ * (n (γ * δ))⁻¹ * (L2 γ * L2 δ * (L2 (γ * δ))⁻¹) := by
    intro γ δ
    have h1 : L1 γ = n γ * L2 γ := by rw [hn]; group
    have h2 : L1 δ = n δ * L2 δ := by rw [hn]; group
    have h3 : L1 (γ * δ) = n (γ * δ) * L2 (γ * δ) := by rw [hn]; group
    rw [h1, h2, h3]
    -- shuffle the central kernel factors to the front
    calc n γ * L2 γ * (n δ * L2 δ) * (n (γ * δ) * L2 (γ * δ))⁻¹
        = n γ * (L2 γ * n δ) * L2 δ * ((L2 (γ * δ))⁻¹ * (n (γ * δ))⁻¹) := by group
      _ = n γ * (n δ * L2 γ) * L2 δ * ((L2 (γ * δ))⁻¹ * (n (γ * δ))⁻¹) := by
          rw [ker_central Dsc (hnker δ) (L2 γ)]
      _ = n γ * n δ * (L2 γ * L2 δ * (L2 (γ * δ))⁻¹) * (n (γ * δ))⁻¹ := by group
      _ = n γ * n δ * ((n (γ * δ))⁻¹ * (L2 γ * L2 δ * (L2 (γ * δ))⁻¹)) := by
          rw [ker_central Dsc (inv_mem (hnker (γ * δ))) (L2 γ * L2 δ * (L2 (γ * δ))⁻¹)]
          group
      _ = _ := by group
  -- the sign difference is the coboundary of `w = ccZsign ∘ n`
  set w : Γ → ZMod 2 := fun γ => ccZsign Dsc (n γ) with hw
  have hwc : Continuous w := by
    have hnc : Continuous n :=
      (continuous_of_discreteTopology (f := fun q : covQ Dsc × covQ Dsc => q.1 * q.2⁻¹)).comp
        (hL1.prodMk hL2)
    exact (continuous_of_discreteTopology (f := fun q : covQ Dsc => ccZsign Dsc q)).comp hnc
  have hsigns : ∀ γ δ : Γ, ccZsign Dsc (L1 γ * L1 δ * (L1 (γ * δ))⁻¹)
      = w γ + w δ + w (γ * δ) + ccZsign Dsc (L2 γ * L2 δ * (L2 (γ * δ))⁻¹) := by
    intro γ δ
    rw [hcomp γ δ,
      ccZsign_mul Dsc (mul_mem (mul_mem (hnker γ) (hnker δ)) (inv_mem (hnker (γ * δ))))
        (hd2ker γ δ),
      ccZsign_mul Dsc (mul_mem (hnker γ) (hnker δ)) (inv_mem (hnker (γ * δ))),
      ccZsign_mul Dsc (hnker γ) (hnker δ), ccZsign_inv Dsc (hnker (γ * δ))]
  -- the coboundary cochain
  have hDmem : (fun p : Γ × Γ => w p.1 + w p.2 + w (p.1 * p.2)) ∈ B2 Γ (ZMod 2) := by
    refine ⟨w, hwc, ?_⟩
    funext p
    show p.1 • w p.2 - w (p.1 * p.2) + w p.1 = w p.1 + w p.2 + w (p.1 * p.2)
    rw [htriv]
    have hchar : ∀ a b cc : ZMod 2, a - cc + b = b + a + cc := by decide
    exact hchar _ _ _
  have hfun : (fun p : Γ × Γ => ccZsign Dsc (L1 p.1 * L1 p.2 * (L1 (p.1 * p.2))⁻¹))
      = (fun p : Γ × Γ => w p.1 + w p.2 + w (p.1 * p.2))
        + (fun p : Γ × Γ => ccZsign Dsc (L2 p.1 * L2 p.2 * (L2 (p.1 * p.2))⁻¹)) := by
    funext p
    exact hsigns p.1 p.2
  constructor
  · intro h1
    have := AddSubgroup.sub_mem _ h1 hDmem
    rw [hfun] at this
    simpa using this
  · intro h2
    rw [hfun]
    exact AddSubgroup.add_mem _ hDmem h2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `zsign` on the cover kernel matches `ccZsign` after `mk_N`. -/
theorem ccZsign_mk_of_ker {x : D.C.cover} (hx : x ∈ D.C.p.ker) :
    ccZsign Dsc (QuotientGroup.mk' Dsc.N x) = CentralObstruction.zsign D x := by
  rcases CentralObstruction.ker_cases D hx with rfl | rfl
  · rw [map_one, ccZsign_one, CentralObstruction.zsign_one]
  · rw [show (QuotientGroup.mk' Dsc.N D.C.z : covQ Dsc) = zbar Dsc from rfl, ccZsign_zbar,
      CentralObstruction.zsign_z]

include hσ in
/-- **The scalar-obstruction bridge**: an `M`-lift with `T`-reduction `g_c` is central iff the
`ξ`-obstruction of `g_c` vanishes — `CentralObstruction.ob` computed through `mk_N` and
transported to the `s₀`-section by sign-defect well-definedness. -/
theorem central_iff_betaXi (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    {c : VCocycle DD ρ} {f : MLifts D ρ} (hf : redTLift DD f = qOfCocycle DD ρ σ hσ c) :
    f.Central ↔ betaXi hσ Dsc c = 0 := by
  classical
  haveI : DiscreteTopology (covQ Dsc) := discreteTopology_covQ Dsc
  set gc := (qOfCocycle DD ρ σ hσ c).1 with hgc
  have hfγ : ∀ γ, piT (D := D) (f.1 γ) = gc γ := by
    intro γ
    exact congrArg (fun g : QLiftsOver DD ρ => g.1 γ) hf
  set L1 : Γ → covQ Dsc := fun γ => QuotientGroup.mk' Dsc.N (liftFam D ρ f γ) with hL1def
  set L2 : Γ → covQ Dsc := fun γ => s0 Dsc (gc γ) with hL2def
  have hL1c : Continuous L1 :=
    (continuous_of_discreteTopology
      (f := fun x : D.C.cover => (QuotientGroup.mk' Dsc.N x : covQ Dsc))).comp
      (liftFam_cont D ρ f)
  have hL2c : Continuous L2 :=
    (continuous_of_discreteTopology (f := fun q : Bg ⧸ D.T => s0 Dsc q)).comp
      gc.continuous_toFun
  have hover : ∀ γ, descP Dsc (L1 γ) = descP Dsc (L2 γ) := by
    intro γ
    rw [hL1def, hL2def]
    show descP Dsc (QuotientGroup.mk' Dsc.N (liftFam D ρ f γ)) = descP Dsc (s0 Dsc (gc γ))
    rw [descP_mk, liftFam_p, s0_sect, hfγ]
  have hmul : ∀ γ δ : Γ, descP Dsc (L2 (γ * δ)) = descP Dsc (L2 γ) * descP Dsc (L2 δ) := by
    intro γ δ
    show descP Dsc (s0 Dsc (gc (γ * δ))) = descP Dsc (s0 Dsc (gc γ)) * descP Dsc (s0 Dsc (gc δ))
    rw [s0_sect, s0_sect, s0_sect, map_mul]
  -- Lift 1's sign defect is `obCocOf (liftFam f)`
  have hsign1 : (fun p : Γ × Γ => ccZsign Dsc (L1 p.1 * L1 p.2 * (L1 (p.1 * p.2))⁻¹))
      = obCocOf D (liftFam D ρ f) := by
    funext p
    show ccZsign Dsc (L1 p.1 * L1 p.2 * (L1 (p.1 * p.2))⁻¹) = _
    rw [hL1def]
    show ccZsign Dsc (QuotientGroup.mk' Dsc.N (liftFam D ρ f p.1)
        * QuotientGroup.mk' Dsc.N (liftFam D ρ f p.2)
        * (QuotientGroup.mk' Dsc.N (liftFam D ρ f (p.1 * p.2)))⁻¹) = _
    rw [← map_inv, ← map_mul, ← map_mul,
      ccZsign_mk_of_ker Dsc (obDefect_mem_ker D ρ (liftFam_p D ρ f) p.1 p.2)]
    rfl
  -- Lift 2's sign defect is the `ξ`-pullback
  have hsign2 : (fun p : Γ × Γ => ccZsign Dsc (L2 p.1 * L2 p.2 * (L2 (p.1 * p.2))⁻¹))
      = pullCoc (⇑gc) (xi Dsc) := by
    funext p
    show ccZsign Dsc (s0 Dsc (gc p.1) * s0 Dsc (gc p.2) * (s0 Dsc (gc (p.1 * p.2)))⁻¹)
      = xi Dsc (gc p.1, gc p.2)
    rw [map_mul gc]
    rfl
  -- assemble the chain
  rw [central_iff_ob_eq_zero D ρ htriv f]
  have hob : ob D ρ htriv f = 0 ↔ obCocOf D (liftFam D ρ f) ∈ B2 Γ (ZMod 2) :=
    H2mk_eq_zero_iff _
  rw [hob, ← hsign1,
    descP_lift_sign_mem_B2_iff Dsc htriv hL1c hL2c hover hmul, hsign2,
    show betaXi hσ Dsc c = iotaB (pullCoc (⇑gc) (xi Dsc)) from rfl,
    iotaB_eq_zero_iff]

include hσ in
/-- **The complete (131)-characterization** (P-16d6c1b): `c` is the `V`-coordinate of a
**central** `M`-lift iff it is `T`-liftable and its scalar `ξ`-obstruction vanishes. -/
theorem mem_centralImage_iff (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (c : VCocycle DD ρ) :
    (∃ f : {f : MLifts D ρ // f.Central}, cocycleOfQ DD ρ σ hσ (redTLift DD f.1) = c)
      ↔ TLiftable hσ c ∧ betaXi hσ Dsc c = 0 := by
  constructor
  · rintro ⟨⟨f, hcen⟩, hfc⟩
    have hf : redTLift DD f = qOfCocycle DD ρ σ hσ c := by
      rw [← hfc]
      exact ((vcocycleEquivLifts DD ρ σ hσ).right_inv (redTLift DD f)).symm
    exact ⟨⟨f, hf⟩, (central_iff_betaXi hσ Dsc htriv hf).mp hcen⟩
  · rintro ⟨⟨f, hf⟩, hxi⟩
    refine ⟨⟨f, (central_iff_betaXi hσ Dsc htriv hf).mpr hxi⟩, ?_⟩
    show cocycleOfQ DD ρ σ hσ (redTLift DD f) = c
    rw [hf]
    exact (vcocycleEquivLifts DD ρ σ hσ).left_inv c

/-! ## Group structure and finiteness of `Z¹_{Γ,ρ}(V)` -/

section GroupStructure

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- Negation on `Z¹_{Γ,ρ}(V)` is the identity (`V` has exponent 2). -/
noncomputable instance : Neg (VCocycle DD ρ) := ⟨fun a => a⟩

/-- `Z¹_{Γ,ρ}(V)` is an elementary abelian 2-group. -/
noncomputable instance : AddCommGroup (VCocycle DD ρ) where
  add_assoc a b c := VCocycle.ext (funext fun γ => add_assoc _ _ _)
  zero_add a := VCocycle.ext (funext fun γ => zero_add _)
  add_zero a := VCocycle.ext (funext fun γ => add_zero _)
  add_comm a b := VCocycle.ext (funext fun γ => add_comm _ _)
  neg a := a
  neg_add_cancel a := VCocycle.ext (funext fun γ => Vmod_exp2 DD (a.c γ))
  nsmul := nsmulRec
  zsmul := zsmulRec

theorem finite_vcocycle (σ : DD.C0 →* Bg ⧸ D.T) (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Finite (VCocycle DD ρ) := by
  haveI : Finite (ContinuousMonoidHom Γ (Bg ⧸ D.T)) :=
    finite_continuousMonoidHom hfg (Bg ⧸ D.T)
  haveI : Finite (QLiftsOver DD ρ) := Subtype.finite
  exact Finite.of_injective (qOfCocycle DD ρ σ hσ)
    (vcocycleEquivLifts DD ρ σ hσ).injective

end GroupStructure

/-! ## The `χ`-additivity of the `T`-obstruction and the base form `Q⁰` -/

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- `β_χ` vanishes at the zero character. -/
theorem betaChi_zero_char (c : VCocycle DD ρ) : betaChi S hσ (0 : ↥(TCharC D)) c = 0 := by
  have h : chiDef S hσ (0 : ↥(TCharC D)) c = 0 := by
    funext p
    show ((0 : ↥(TCharC D)) : ↥D.T → ZMod 2) (tDef S hσ c p) = 0
    rfl
  rw [betaChi, h]
  exact iotaB_of_mem_B2 (AddSubgroup.zero_mem _)

omit [ContinuousSMul Γ (ZMod 2)] in
/-- `β_χ` is additive in the character (`ι_Γ`-additivity, `#H²(Γ,𝔽₂) = 2`). -/
theorem betaChi_add_char (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (χ ψ : ↥(TCharC D)) (c : VCocycle DD ρ) :
    betaChi S hσ (χ + ψ) c = betaChi S hσ χ c + betaChi S hσ ψ c := by
  have h : chiDef S hσ (χ + ψ) c = chiDef S hσ χ c + chiDef S hσ ψ c := by
    funext p
    show ((χ + ψ : ↥(TCharC D)) : ↥D.T → ZMod 2) (tDef S hσ c p) = _
    rfl
  rw [betaChi, h]
  exact iotaB_add hH2 (chiDef_mem_Z2 S hσ htriv χ c) (chiDef_mem_Z2 S hσ htriv ψ c)

variable (DD ρ) in
/-- **The base determinant form `Q⁰_{Γ,ρ}`** on `Z¹_{Γ,ρ}(V)`: `ι_Γ` of the graph pullback of
the fixed equivariant base class `κ⁰` (eq. (62)/(133)-side). -/
noncomputable def QZero (c : VCocycle DD ρ) : ZMod 2 :=
  iotaB (graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c)

/-! ## The master count -/

omit [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- Transporting the central `red_T`-image count to the `V`-cocycle layer. -/
theorem card_range_redT_eq :
    Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1))
      = Nat.card {c : VCocycle DD ρ //
          ∃ f : {f : MLifts D ρ // f.Central}, cocycleOfQ DD ρ σ hσ (redTLift DD f.1) = c} := by
  classical
  -- factor `redT = (raw coercion) ∘ redTLift`, both injective transports
  have h1 : (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1)
      = (fun g : QLiftsOver DD ρ => (⇑g.1 : Γ → Bg ⧸ D.T))
        ∘ (fun f : {f : MLifts D ρ // f.Central} => redTLift DD f.1) := by
    funext f
    rfl
  have hinj1 : Function.Injective (fun g : QLiftsOver DD ρ => (⇑g.1 : Γ → Bg ⧸ D.T)) := by
    intro g g' h
    apply Subtype.ext
    apply ContinuousMonoidHom.ext
    exact fun γ => congrFun h γ
  have hinj2 : Function.Injective (cocycleOfQ DD ρ σ hσ) :=
    (vcocycleEquivLifts DD ρ σ hσ).symm.injective
  rw [h1, Set.range_comp, Nat.card_image_of_injective hinj1]
  have h2 : Set.range (fun f : {f : MLifts D ρ // f.Central} =>
        cocycleOfQ DD ρ σ hσ (redTLift DD f.1))
      = cocycleOfQ DD ρ σ hσ '' Set.range (fun f : {f : MLifts D ρ // f.Central} =>
          redTLift DD f.1) := by
    rw [← Set.range_comp]
    rfl
  calc Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redTLift DD f.1))
      = Nat.card ↥(cocycleOfQ DD ρ σ hσ '' Set.range
          (fun f : {f : MLifts D ρ // f.Central} => redTLift DD f.1)) :=
        (Nat.card_image_of_injective hinj2 _).symm
    _ = Nat.card {c : VCocycle DD ρ // ∃ f : {f : MLifts D ρ // f.Central},
          cocycleOfQ DD ρ σ hσ (redTLift DD f.1) = c} := by rw [← h2]; rfl

open scoped Classical in
/-- **The master count** (P-16d6c1b/c1c interface): the per-`ρ` phase-obstruction identity of
the paper's Prop 8.9 proof, derived from the (131)-characterization by double Fourier
expansion.  The source-specific inputs are threaded: `hH2` (`#H²(Γ,𝔽₂) = 2`), `hsep` (the
`(T^∨)^C`-separation of the `T`-obstruction), `haff`/`hpartial` (affineness and nontriviality
of the `χ`-components — `∂`-surjectivity), `hkey` (the (135) completed square, from the
keystone file), `hZcard` (`#Z¹(V) = #V²`) and `hGaussZ` (`G(Q⁰) = #V·G0` — the source-Gauss
transport). -/
theorem two_mul_card_centralImage
    [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (hsep : ∀ c : VCocycle DD ρ, (∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0) → TLiftable hσ c)
    (haff : ∀ (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ),
      betaChi S hσ χ (c + c')
        = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ))
    (hpartial : ∀ χ : ↥(TCharC D), χ ≠ 0 →
      ∃ c : VCocycle DD ρ, betaChi S hσ χ c ≠ betaChi S hσ χ (0 : VCocycle DD ρ))
    (Δ : ↥(TCharC D) → DD.C0 × DD.C0 → ZMod 2) (sh : ↥(TCharC D) → VCocycle DD ρ)
    (hkey : ∀ (χ : ↥(TCharC D)) (c : VCocycle DD ρ),
      betaChi S hσ χ c + betaXi hσ Dsc c
        = QZero DD ρ (c + sh χ) + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))
    (G0 : ℤ)
    (hZcard : Nat.card (VCocycle DD ρ) = Nat.card DD.Vmod * Nat.card DD.Vmod)
    (hGaussZ : ∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c) = (Nat.card DD.Vmod : ℤ) * G0) :
    2 * (Nat.card ↥(TCharC D) : ℤ)
        * (Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1)) : ℤ)
      = (Nat.card DD.Vmod : ℤ) * ((Nat.card DD.Vmod : ℤ)
          + G0 * ∑ᶠ χ : ↥(TCharC D),
              sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ)))) := by
  classical
  haveI : Finite (VCocycle DD ρ) := finite_vcocycle σ hσ hfg
  haveI : Fintype (VCocycle DD ρ) := Fintype.ofFinite _
  haveI : Fintype ↥(TCharC D) := Fintype.ofFinite _
  -- Step 0: transport the count to the cocycle layer and the (131)-characterization
  have hbridge : Nat.card ↥(Set.range (fun f : {f : MLifts D ρ // f.Central} => redT ρ f.1))
      = Nat.card {c : VCocycle DD ρ // TLiftable hσ c ∧ betaXi hσ Dsc c = 0} := by
    rw [card_range_redT_eq hσ]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun c =>
      mem_centralImage_iff hσ Dsc htriv c)
  -- Step 1: the per-`c` character sum is the `TLiftable`-indicator
  have hA : ∀ c : VCocycle DD ρ,
      (∑ χ : ↥(TCharC D), sign (betaChi S hσ χ c))
        = if TLiftable hσ c then (Nat.card ↥(TCharC D) : ℤ) else 0 := by
    intro c
    by_cases hc : TLiftable hσ c
    · rw [if_pos hc]
      rw [Finset.sum_congr rfl fun χ _ => by
        rw [betaChi_of_tliftable S hσ htriv hc χ, sign_zero]]
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
        Nat.card_eq_fintype_card]
    · rw [if_neg hc]
      have hnz : ¬∀ χ : ↥(TCharC D), betaChi S hσ χ c = 0 := fun hall => hc (hsep c hall)
      have hadd : ∀ χ ψ : ↥(TCharC D),
          betaChi S hσ (χ + ψ) c = betaChi S hσ χ c + betaChi S hσ ψ c :=
        fun χ ψ => betaChi_add_char S hσ htriv hH2 χ ψ c
      have := sum_sign_eq_zero (fun χ : ↥(TCharC D) => betaChi S hσ χ c) hadd hnz
      rwa [finsum_eq_sum_of_fintype] at this
  -- Step 2: the master double sum, evaluated two ways
  set Tsum : ℤ := ∑ c : VCocycle DD ρ, ∑ χ : ↥(TCharC D),
    sign (betaChi S hσ χ c) * (1 + sign (betaXi hσ Dsc c)) with hTsum
  -- Way 1: `2·#D · #{central image}`
  have hway1 : Tsum = 2 * (Nat.card ↥(TCharC D) : ℤ)
      * (Nat.card {c : VCocycle DD ρ // TLiftable hσ c ∧ betaXi hσ Dsc c = 0} : ℤ) := by
    have hc : ∀ c : VCocycle DD ρ, (∑ χ : ↥(TCharC D),
        sign (betaChi S hσ χ c) * (1 + sign (betaXi hσ Dsc c)))
        = if TLiftable hσ c ∧ betaXi hσ Dsc c = 0
          then 2 * (Nat.card ↥(TCharC D) : ℤ) else 0 := by
      intro c
      rw [← Finset.sum_mul, hA c, one_add_sign]
      by_cases h1 : TLiftable hσ c <;> by_cases h2 : betaXi hσ Dsc c = 0
      · rw [if_pos h1, if_pos h2, if_pos ⟨h1, h2⟩]; ring
      · rw [if_pos h1, if_neg h2, if_neg (fun h => h2 h.2)]; ring
      · rw [if_neg h1, if_pos h2, if_neg (fun h => h1 h.1)]; ring
      · rw [if_neg h1, if_neg h2, if_neg (fun h => h1 h.1)]; ring
    rw [hTsum, Finset.sum_congr rfl fun c _ => hc c, ← Finset.sum_filter,
      Finset.sum_const, Nat.card_eq_fintype_card (α := {c : VCocycle DD ρ //
        TLiftable hσ c ∧ betaXi hσ Dsc c = 0}), Fintype.card_subtype]
    ring
  -- Way 2: expand, swap, evaluate the two `χ`-sums
  have hway2 : Tsum = (Nat.card (VCocycle DD ρ) : ℤ)
      + (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
        * ∑ χ : ↥(TCharC D), sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
    have hsplit : Tsum = (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c))
        + ∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ,
            sign (betaChi S hσ χ c + betaXi hσ Dsc c) := by
      rw [hTsum, Finset.sum_comm, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun χ _ => ?_
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [sign_add]
      ring
    -- first double sum: only `χ = 0` survives
    have hfirst : (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c))
        = (Nat.card (VCocycle DD ρ) : ℤ) := by
      rw [Finset.sum_eq_single (0 : ↥(TCharC D))]
      · rw [Finset.sum_congr rfl fun c _ => by rw [betaChi_zero_char S hσ c, sign_zero],
          Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          Nat.card_eq_fintype_card]
      · intro χ _ hχ
        -- affine with nonzero linear part: balanced signs
        have hadd : ∀ a b : VCocycle DD ρ,
            (betaChi S hσ χ (a + b) + betaChi S hσ χ (0 : VCocycle DD ρ))
              = (betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ))
                + (betaChi S hσ χ b + betaChi S hσ χ (0 : VCocycle DD ρ)) := by
          intro a b
          rw [haff χ a b]
          ring
        have hnz : ¬∀ a : VCocycle DD ρ, betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ) = 0 := by
          intro hall
          obtain ⟨c₀, hc₀⟩ := hpartial χ hχ
          have := hall c₀
          have hchar : ∀ x y : ZMod 2, x + y = 0 → x = y := by decide
          exact hc₀ (hchar _ _ this)
        have hzero := sum_sign_eq_zero
          (fun a : VCocycle DD ρ => betaChi S hσ χ a + betaChi S hσ χ (0 : VCocycle DD ρ)) hadd hnz
        rw [finsum_eq_sum_of_fintype] at hzero
        calc ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c)
            = ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ (0 : VCocycle DD ρ))
                * sign (betaChi S hσ χ c + betaChi S hσ χ (0 : VCocycle DD ρ)) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [← sign_add]
              congr 1
              have hchar : ∀ x y : ZMod 2, x = y + (x + y) := by decide
              exact hchar _ _
          _ = sign (betaChi S hσ χ (0 : VCocycle DD ρ)) * ∑ c : VCocycle DD ρ,
                sign (betaChi S hσ χ c + betaChi S hσ χ (0 : VCocycle DD ρ)) := by rw [Finset.mul_sum]
          _ = 0 := by rw [hzero, mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    -- second double sum: the keystone + translation-invariance of the `Q⁰`-Gauss sum
    have hsecond : (∑ χ : ↥(TCharC D), ∑ c : VCocycle DD ρ,
          sign (betaChi S hσ χ c + betaXi hσ Dsc c))
        = (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
          * ∑ χ : ↥(TCharC D), sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun χ _ => ?_
      calc ∑ c : VCocycle DD ρ, sign (betaChi S hσ χ c + betaXi hσ Dsc c)
          = ∑ c : VCocycle DD ρ, sign (QZero DD ρ (c + sh χ))
              * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
            refine Finset.sum_congr rfl fun c _ => ?_
            rw [← sign_add, hkey χ c]
        _ = (∑ c : VCocycle DD ρ, sign (QZero DD ρ (c + sh χ)))
              * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
            rw [← Finset.sum_mul]
        _ = (∑ᶠ c : VCocycle DD ρ, sign (QZero DD ρ c))
              * sign (iotaB (pullCoc (fun γ => rho0 DD ρ γ) (Δ χ))) := by
            congr 1
            rw [finsum_eq_sum_of_fintype]
            exact Fintype.sum_equiv (Equiv.addRight (sh χ))
              (fun c => sign (QZero DD ρ (c + sh χ))) (fun c => sign (QZero DD ρ c))
              (fun c => rfl)
    rw [hsplit, hfirst, hsecond]
  -- assemble
  rw [hbridge, ← hway1, hway2, hZcard, hGaussZ, finsum_eq_sum_of_fintype,
    Nat.cast_mul]
  ring

end AffineTLift

end SectionEight

end GQ2
