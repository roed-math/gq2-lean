import GQ2.CentralObstruction
import GQ2.LocalLiftingDuality
import GQ2.WordCohBridge
import GQ2.DualityAssembly
import GQ2.RadicalEdgeLocal

/-!
# Lemma 8.6, `Γ_A` source: the duality half via `prop_5_15`  (ticket P-16c3)

The `Γ_A`-side analogue of `RadicalEdgeLocal.exists_good_twist`: from `NoDescent`, the
Fox–Heisenberg self-duality `prop_5_15` produces a nonzero *traced mixed pairing*
`mixedB t_ρ x_w y_φ ≠ 0`, where `y_φ` is the shifted-edge dual class and `x_w` its
`prop_5_15`-pairing partner.  This is the c3 deliverable; the Θ–mixedB comparison
(`mixedB ≠ 0 ⟹ [varCoc u_w] ≠ 0`, using c2's `θ`) is P-16c4.

**Structural pivot (docs/p16c3-recon.md):** `MuDual`'s `DistribMulAction` is hardcoded to
`AbsGalQ2` (`GQ2/TateDuality.lean`), so the local proof's `φf : Γ → MuDual 2 (Additive ↥T)`
does not port to `Γ = GA`.  The shifted-edge cocycle is built directly in
`ElemDual (Additive ↥T)` (generic `DistribMulAction C (ElemDual A)`, `FoxHeisenberg`;
`(g•λ)a = λ(g⁻¹•a)`), which also removes `dualAddEquiv` from the bridge.

Source group is the **raw** `GA = F₄ ⧸ N_A` (matching `WordCohBridge`; the `GammaA` transport
is P-16c5).  The `C = Bg ⧸ D.M`-conjugation action on `T` is the primary module structure
(what `mixedB`/`Z1w`/`markC` consume); the `GA`-action is its pullback `DistribMulAction.compHom
ρ` (so `hcompat` for `h1Equiv` is `rfl`).

Axioms (target): std-3 only — the pairing comes from `prop_5_15` (P-13f), not B6.
-/

namespace GQ2

namespace SectionEight

namespace RadicalEdgeGammaA

open CentralObstruction ContCoh LocalLiftingDuality WordCohBridge FoxH RadicalEdgeLocal

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  (D : RadicalCoverData Bg)

/-! ## The `C = Bg ⧸ D.M`-conjugation module on `T`

`M` centralizes `T` (`D.hcomm` + `D.hTM`), so `c • t := b t b⁻¹` (any `b` over `c`) is a
well-defined action of the finite discrete group `C = Bg ⧸ D.M` on the abelian 2-group `T`. -/

/-- `↥D.T` is commutative (`T ≤ M` abelian) — additive form for the word complex.  Built on
top of the existing `AddGroup (Additive ↥D.T)` (from the subgroup `Group`), so no diamond. -/
noncomputable instance instACGaddT : AddCommGroup (Additive ↥D.T) :=
  { (inferInstance : AddGroup (Additive ↥D.T)) with
    add_comm := fun a b => by
      apply Additive.toMul.injective
      show Additive.toMul a * Additive.toMul b = Additive.toMul b * Additive.toMul a
      exact Subtype.ext
        (D.hcomm _ (D.hTM (Additive.toMul a).2) _ (D.hTM (Additive.toMul b).2)) }

/-- The conjugation action of `C = Bg ⧸ D.M` on `T`, at the canonical representative. -/
noncomputable def cactFun (c : Bg ⧸ D.M) (t : ↥D.T) : ↥D.T :=
  ⟨Quotient.out c * t.1 * (Quotient.out c)⁻¹, conj_mem_T D (Quotient.out c) t⟩

theorem cactFun_eq (c : Bg ⧸ D.M) {b : Bg} (hb : QuotientGroup.mk b = c) (t : ↥D.T) :
    (cactFun D c t).1 = b * t.1 * b⁻¹ :=
  conj_eq_of_mk_eq D (by rw [QuotientGroup.out_eq' c, hb]) t

theorem cactFun_one (t : ↥D.T) : cactFun D 1 t = t := by
  apply Subtype.ext
  rw [cactFun_eq D 1 (by rw [QuotientGroup.mk_one]) t]; group

theorem cactFun_mul (c c' : Bg ⧸ D.M) (t : ↥D.T) :
    cactFun D (c * c') t = cactFun D c (cactFun D c' t) := by
  apply Subtype.ext
  have hcc' : (QuotientGroup.mk (Quotient.out c * Quotient.out c') : Bg ⧸ D.M) = c * c' := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq', QuotientGroup.out_eq']
  rw [cactFun_eq D (c * c') hcc' t]
  show _ = Quotient.out c * (cactFun D c' t).1 * (Quotient.out c)⁻¹
  show Quotient.out c * Quotient.out c' * t.1 * (Quotient.out c * Quotient.out c')⁻¹
    = Quotient.out c
      * (Quotient.out c' * t.1 * (Quotient.out c')⁻¹) * (Quotient.out c)⁻¹
  group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem cactFun_mul' (c : Bg ⧸ D.M) (t t' : ↥D.T) :
    cactFun D c (t * t') = cactFun D c t * cactFun D c t' := by
  apply Subtype.ext
  show Quotient.out c * (t.1 * t'.1) * (Quotient.out c)⁻¹
    = (Quotient.out c * t.1 * (Quotient.out c)⁻¹)
      * (Quotient.out c * t'.1 * (Quotient.out c)⁻¹)
  group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem cactFun_one_elt (c : Bg ⧸ D.M) : cactFun D c 1 = 1 := by
  apply Subtype.ext
  show Quotient.out c * (1 : Bg) * (Quotient.out c)⁻¹ = 1; group

/-- The `C = Bg ⧸ D.M`-conjugation action on `Additive ↥D.T`. -/
noncomputable instance cActT : DistribMulAction (Bg ⧸ D.M) (Additive ↥D.T) :=
  { smul := fun c t => Additive.ofMul (cactFun D c (Additive.toMul t))
    one_smul := fun t => cactFun_one D (Additive.toMul t)
    mul_smul := fun c c' t => cactFun_mul D c c' (Additive.toMul t)
    smul_zero := fun c => cactFun_one_elt D c
    smul_add := fun c t t' => cactFun_mul' D c (Additive.toMul t) (Additive.toMul t') }

theorem cActT_toMul (c : Bg ⧸ D.M) (t : Additive ↥D.T) :
    Additive.toMul (c • t) = cactFun D c (Additive.toMul t) := rfl

/-- The discrete topology on the `𝔽₂`-dual (a valid coefficient module). -/
instance instTopElemDualT : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
instance instDiscElemDualT : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The `Γ_A` twist, duality half** (Lemma 8.6, `Γ_A` source; ticket P-16c3): from
`NoDescent`, `prop_5_15`'s perfect pairing yields word cocycles `x` (primal) and `y` (the
shifted-edge dual) with nonzero traced mixed pairing.  Consumed by P-16c4 (Θ–mixedB). -/
theorem exists_good_pairing_gammaA (S : TComplement D)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GA (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    ∃ (x : Z1w (A := Additive ↥D.T) (markC ρ))
      (y : Z1w (A := ElemDual (Additive ↥D.T)) (markC ρ)),
      mixedB (markC ρ) x.val y.val ≠ 0 := by
  classical
  haveI := discreteTopology_quotient D
  letI : TopologicalSpace (Additive ↥D.T) := (inferInstance : TopologicalSpace ↥D.T)
  haveI : DiscreteTopology (Additive ↥D.T) :=
    ⟨(inferInstance : DiscreteTopology ↥D.T).eq_bot⟩
  haveI : Finite (Additive ↥D.T) := (inferInstance : Finite ↥D.T)
  haveI : IsTopologicalAddGroup (Additive ↥D.T) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  -- ===== `T`/`T^∨` as `GA`-modules via the `ρ`-pullback of the `C`-conjugation action =====
  letI actGA : DistribMulAction GA (Additive ↥D.T) :=
    DistribMulAction.compHom (Additive ↥D.T) ρ.toMonoidHom
  have hcompat : ∀ (γ : GA) (a : Additive ↥D.T), γ • a = ρ γ • a := fun _ _ => rfl
  have hactGA : ∀ (γ : GA) (s : Additive ↥D.T),
      Additive.toMul (γ • s) = cactFun D (ρ γ) (Additive.toMul s) := fun _ _ => rfl
  haveI : ContinuousSMul GA (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : GA × Additive ↥D.T => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × Additive ↥D.T => cq.1 • cq.2)
          ∘ (fun p : GA × Additive ↥D.T => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  letI actGAD : DistribMulAction GA (ElemDual (Additive ↥D.T)) :=
    DistribMulAction.compHom (ElemDual (Additive ↥D.T)) ρ.toMonoidHom
  have hcompatD : ∀ (γ : GA) (l : ElemDual (Additive ↥D.T)), γ • l = ρ γ • l := fun _ _ => rfl
  haveI : ContinuousSMul GA (ElemDual (Additive ↥D.T)) := by
    constructor
    have hfac : (fun p : GA × ElemDual (Additive ↥D.T) => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × ElemDual (Additive ↥D.T) => cq.1 • cq.2)
          ∘ (fun p : GA × ElemDual (Additive ↥D.T) => ((ρ p.1 : Bg ⧸ D.M), p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  -- the `GA`-contragredient on `ElemDual`, expressed through the `GA`-action on `A`
  have hsmulD : ∀ (γ : GA) (l : ElemDual (Additive ↥D.T)) (a : Additive ↥D.T),
      (γ • l) a = l (γ⁻¹ • a) := by
    intro γ l a
    rw [hcompatD, ElemDual.smul_apply, hcompat γ⁻¹ a, map_inv]
  have hA₂ : ∀ a : Additive ↥D.T, a + a = 0 := fun a =>
    Additive.toMul.injective (Subtype.ext (D.helem _ (D.hTM (Additive.toMul a).2)))
  have hA₂D : ∀ l : ElemDual (Additive ↥D.T), l + l = 0 := fun l => by
    ext a; simp only [ElemDual.add_apply, ElemDual.zero_apply]
    exact CharTwo.add_self_eq_zero (l a)
  -- ===== the shifted-edge dual 1-cocycle `φf` (valued in `ElemDual`, no `MuDual`) =====
  have hφadd : ∀ (γ : GA) (s s' : Additive ↥D.T),
      edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • (s + s')))
        = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • s))
          + edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • s')) := by
    intro γ s s'
    have hmulcast : Additive.toMul ((γ⁻¹ : GA) • (s + s'))
        = Additive.toMul ((γ⁻¹ : GA) • s) * Additive.toMul ((γ⁻¹ : GA) • s') := by
      rw [smul_add]; rfl
    rw [hmulcast]
    exact edge_add D S (Quotient.out (ρ γ)) _ _
  set φf : GA → ElemDual (Additive ↥D.T) := fun γ =>
    (AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • s))) (hφadd γ)
      : Additive ↥D.T →+ ZMod 2) with hφfdef
  have hφapp : ∀ (γ : GA) (s : Additive ↥D.T),
      (φf γ) s = edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • s)) := fun _ _ => rfl
  -- the ZMod₂-level crossed law of the shifted edge (edgeQ-only, `MuDual`-free)
  have hcrossZ : ∀ (γ δ : GA) (s : Additive ↥D.T),
      edgeQ D S (ρ (γ * δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
        = edgeQ D S (ρ γ) (Additive.toMul (γ⁻¹ • s))
          + edgeQ D S (ρ δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : GA) • s)) := by
    intro γ δ s
    have hγ : (QuotientGroup.mk (Quotient.out (ρ γ)) : Bg ⧸ D.M) = ρ γ :=
      QuotientGroup.out_eq' _
    have hδ : (QuotientGroup.mk (Quotient.out (ρ δ)) : Bg ⧸ D.M) = ρ δ :=
      QuotientGroup.out_eq' _
    have hγδrep : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
        = ρ (γ * δ) := by rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
    rw [edgeQ_eq D S (ρ (γ * δ)) hγδrep, edge_mul]
    have h2 : edge D S (Quotient.out (ρ γ))
          ⟨Quotient.out (ρ δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (ρ δ))⁻¹,
            conj_mem_T D (Quotient.out (ρ δ)) (Additive.toMul ((γ * δ)⁻¹ • s))⟩
        = edgeQ D S (ρ γ) (Additive.toMul (γ⁻¹ • s)) := by
      rw [edgeQ_eq D S (ρ γ) hγ]
      congr 1
      apply Subtype.ext
      show Quotient.out (ρ δ) * (Additive.toMul ((γ * δ)⁻¹ • s)).1 * (Quotient.out (ρ δ))⁻¹
          = (Additive.toMul (γ⁻¹ • s)).1
      have hsplit : Additive.toMul ((γ * δ)⁻¹ • s)
          = cactFun D (ρ δ⁻¹) (Additive.toMul (γ⁻¹ • s)) := by
        rw [hactGA, show ((γ * δ)⁻¹ : GA) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ, map_mul,
          cactFun_mul, ← hactGA]
      rw [hsplit]
      have hδinv : (QuotientGroup.mk ((Quotient.out (ρ δ))⁻¹) : Bg ⧸ D.M) = ρ δ⁻¹ := by
        rw [QuotientGroup.mk_inv, hδ, map_inv]
      rw [cactFun_eq D (ρ δ⁻¹) hδinv]
      group
    have h1 : edge D S (Quotient.out (ρ δ)) (Additive.toMul ((γ * δ)⁻¹ • s))
        = edgeQ D S (ρ δ) (Additive.toMul (δ⁻¹ • (γ⁻¹ : GA) • s)) := by
      rw [edgeQ_eq D S (ρ δ) hδ]
      congr 1
      rw [mul_inv_rev, mul_smul]
    rw [h1, h2]
  have hφZ1 : φf ∈ Z1 GA (ElemDual (Additive ↥D.T)) := by
    rw [mem_Z1_iff]
    refine ⟨?_, ?_⟩
    · -- continuity: `φf` factors through the discrete quotient
      have hΦadd : ∀ (c : Bg ⧸ D.M) (s s' : Additive ↥D.T),
          edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩
            = edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
              + edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                  * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                  conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
        intro c s s'
        have hsplit : (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul (s + s')).1
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul (s + s'))⟩ : ↥D.T)
            = (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩ : ↥D.T)
              * ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                  * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                  conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
          apply Subtype.ext
          show Quotient.out (c⁻¹ : Bg ⧸ D.M)
              * ((Additive.toMul s).1 * (Additive.toMul s').1)
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹
            = (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
          group
        rw [hsplit]
        exact edge_add D S (Quotient.out c) _ _
      have hfac : φf = (fun c : Bg ⧸ D.M =>
          (AddMonoidHom.mk' (fun s : Additive ↥D.T =>
            edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
                * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩) (hΦadd c)
            : ElemDual (Additive ↥D.T))) ∘ (fun γ : GA => (ρ γ : Bg ⧸ D.M)) := by
        funext γ
        refine DFunLike.ext _ _ fun s => ?_
        rw [hφapp]
        show edgeQ D S (ρ γ) (Additive.toMul ((γ⁻¹ : GA) • s))
          = edgeQ D S (ρ γ) ⟨Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
              * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹,
              conj_mem_T D (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩
        refine congrArg (edgeQ D S (ρ γ)) (Subtype.ext ?_)
        rw [hactGA]
        show Quotient.out (ρ γ⁻¹) * (Additive.toMul s).1 * (Quotient.out (ρ γ⁻¹))⁻¹
          = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
            * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹
        rw [map_inv]
      rw [hfac]
      exact continuous_of_discreteTopology.comp ρ.continuous_toFun
    · intro γ δ
      refine DFunLike.ext _ _ fun s => ?_
      have hz := hcrossZ γ δ s
      show (φf (γ * δ)) s = (φf γ + γ • φf δ) s
      rw [ElemDual.add_apply, hsmulD]
      simp only [hφapp]
      exact hz
  -- ===== `[φf] ≠ 0` (else the edge trivializes and the cover descends) =====
  have hφne : H1mk GA (ElemDual (Additive ↥D.T)) ⟨φf, hφZ1⟩ ≠ 0 := by
    intro h0
    have hmem : φf ∈ B1 GA (ElemDual (Additive ↥D.T)) := by
      have h1 := (QuotientAddGroup.eq_zero_iff _).mp h0
      rwa [AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨lam, hlam⟩ := hmem
    set ℓ : ↥D.T → ZMod 2 :=
      fun t => (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul t) with hℓdef
    have hℓadd : ∀ t t' : ↥D.T, ℓ (t * t') = ℓ t + ℓ t' := by
      intro t t'
      show (lam : ElemDual (Additive ↥D.T)) (Additive.ofMul (t * t')) = _
      rw [show Additive.ofMul (t * t')
          = Additive.ofMul t + Additive.ofMul t' from rfl, map_add]
    refine (not_noDescent_of_edge_trivial D S ℓ hℓadd ?_) hedge
    intro b t
    obtain ⟨γ, hγ⟩ := hρ (QuotientGroup.mk b)
    have hlamγ := congrFun hlam γ
    have hval := congrArg
      (fun ψ : ElemDual (Additive ↥D.T) => ψ ((γ : GA) • Additive.ofMul t)) hlamγ
    have hL : (dZero GA (ElemDual (Additive ↥D.T)) lam γ) ((γ : GA) • Additive.ofMul t)
        = lam (Additive.ofMul t) - lam ((γ : GA) • Additive.ofMul t) := by
      show ((γ • lam - lam : ElemDual (Additive ↥D.T))) ((γ : GA) • Additive.ofMul t) = _
      rw [ElemDual.sub_apply, hsmulD, inv_smul_smul]
    have hR : (φf γ) ((γ : GA) • Additive.ofMul t) = edge D S b t := by
      rw [hφapp, ← edgeQ_eq D S (ρ γ) hγ.symm t]
      refine congrArg (edgeQ D S (ρ γ)) ?_
      exact inv_smul_smul γ (Additive.ofMul t)
    rw [hL, hR] at hval
    have hbt : Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)
        = (γ : GA) • Additive.ofMul t := by
      rw [show ((γ : GA) • Additive.ofMul t) = Additive.ofMul (cactFun D (ρ γ) t) from rfl]
      exact congrArg Additive.ofMul (Subtype.ext (cactFun_eq D (ρ γ) hγ.symm t).symm)
    show edge D S b t = ℓ (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T) + ℓ t
    rw [hℓdef]
    show edge D S b t
      = lam (Additive.ofMul (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T)) + lam (Additive.ofMul t)
    rw [hbt, ← hval]
    have harith : ∀ a e : ZMod 2, a - e = e + a := by decide
    exact harith _ _
  -- ===== `prop_5_15`: the perfect pairing detects the nonzero shifted-edge dual class =====
  have adm := markC_admissible ρ hρ
  obtain ⟨P, hP, _hleft, hright⟩ :=
    (FoxH.prop_5_15 (markC ρ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2).2.2
  set yφ : H1w (A := ElemDual (Additive ↥D.T)) (markC ρ) :=
    h1Equiv ρ hcompatD hρ hA₂D (H1mk GA (ElemDual (Additive ↥D.T)) ⟨φf, hφZ1⟩) with hyφdef
  have hyφne : yφ ≠ 0 := by
    intro h
    apply hφne
    apply (h1Equiv ρ hcompatD hρ hA₂D).injective
    rw [map_zero]
    exact h
  obtain ⟨hx, hPne⟩ := hright yφ hyφne
  obtain ⟨x, hx_eq0⟩ := QuotientAddGroup.mk_surjective hx
  obtain ⟨y, hy_eq0⟩ := QuotientAddGroup.mk_surjective yφ
  have hx_eq : h1wMk (markC ρ) x = hx := hx_eq0
  have hy_eq : h1wMk (markC ρ) y = yφ := hy_eq0
  refine ⟨x, y, fun hmix => hPne ?_⟩
  rw [← hx_eq, ← hy_eq, hP x y]
  exact hmix

end RadicalEdgeGammaA

end SectionEight

end GQ2
