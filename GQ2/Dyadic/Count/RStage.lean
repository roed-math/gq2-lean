/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex
-/
import GQ2.Dyadic.Count.Marking
import GQ2.Dyadic.Recursion.BlockRStage
import GQ2.RStage.Local

/-!
# The degree-generic R-stage cocycle count

The frozen `R`-stage files prove `#RCocycle = #R^2 * #D_R` separately for `AbsGalQ2`,
`GammaA`, and `GammaR`.  The source-free part of those proofs is uniform: an `RCocycle` is a
continuous additive `1`-cocycle with coefficients in `R = Phi(K)`, and the invariant dual of
`R` has cardinality `#D_R`.

For a degree-`n` admissibly marked presentation, however, the word-complex count contributes
`(standardNumerics n).tMult #R = #R^(n+1)`, not the frozen exponent `2`.  This file records that
actual generic theorem.  Consequently it also isolates the exact obstruction to reusing the
old `RecursionFrame.zR` unchanged at higher degree: only the `n = 1` specialization reduces to
the frame's present `zR` definition.
-/

namespace GQ2.Dyadic.Count

open GQ2.ContCoh GQ2.FoxH GQ2.SectionEight GQ2.SectionSeven

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : MinimalBlock T.LY}

/-! ## Candidate-side separation by the marking route -/

section Separation

variable {ι κ : Type*} {Γ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]
  {gen : ι → Γ} {W : κ → PWord ι} {w : κ → FreeGroup ι} {J : Set ι}

/-- **Candidate-side `R`-separation, degree-generically.**

Let `g : Γ → Y/R` be onto.  If its scalar obstruction vanishes for every
`Y`-invariant character of `R`, then a Stokes-dual admissible presentation of `Γ` corrects a
set-lift of the marked generators to a relator-killing marking in `Y`.  Admissible extension and
marking rigidity then produce a continuous homomorphism `Γ → Y` over `g`.

This is the generic core shared by all candidate presentations.  It does not assume its
conclusion or an `R`-valued splitting cochain.  The two structural hypotheses `hRK` and `hR2`
are essential: they make `R = Φ(K)` an elementary abelian `Y/K`-module and make the corrected
marking admissible.  The proof uses only the presentation, its matched resolver, Stokes duality,
and the already-proved scalar-cover characterization of `obs`. -/
theorem homLift_of_obs_zero_markingN
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (g : ContinuousMonoidHom Γ (blockFrameImpl T Blk hE2).YB)
    (hgsurj : Function.Surjective g)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwild2 : IsWildTwo J (fun i => g (gen i)))
    (hres2 :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      letI := scalarActionZmodTwo (Y ⧸ Blk.K)
      ResolvesAt W w (WordLift (ZMod 2) (Y ⧸ Blk.K)))
    (hresR :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality
        (fun i =>
          QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
            (by rw [Subgroup.comap_id]; exact SectionSeven.frattiniLike_le Blk.K)
            (g (gen i)))
        w (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
      htriv hcard g = 0) :
    ∃ φ : ContinuousMonoidHom Γ Y,
      ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g γ := by
  classical
  let RF := blockFrameImpl T Blk hE2
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  letI actC2 : DistribMulAction (Y ⧸ Blk.K) (ZMod 2) :=
    scalarActionZmodTwo (Y ⧸ Blk.K)
  have htrivC : ∀ (c : Y ⧸ Blk.K) (m : ZMod 2), c • m = m :=
    scalarActionZmodTwo_triv _
  have hRleK : Blk.frattiniK ≤ Blk.K := SectionSeven.frattiniLike_le Blk.K
  set qKR : RF.YB →* (Y ⧸ Blk.K) :=
    QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
      (by rw [Subgroup.comap_id]; exact hRleK) with hqKR
  set θ : ContinuousMonoidHom Γ (Y ⧸ Blk.K) :=
    ⟨qKR.comp g.toMonoidHom,
      (continuous_of_discreteTopology (f := qKR)).comp g.continuous_toFun⟩ with hθ
  have hθsurj : Function.Surjective θ := by
    intro c
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨γ, hγ⟩ := hgsurj (RF.piB y)
    refine ⟨γ, ?_⟩
    show qKR (g γ) = QuotientGroup.mk' Blk.K y
    rw [hγ]
    rfl
  set c : ι → (Y ⧸ Blk.K) := fun i => θ (gen i) with hc
  have hdc : StokesDuality c w (Additive ↥Blk.frattiniK) := by
    change StokesDuality (fun i => qKR (g (gen i))) w (Additive ↥Blk.frattiniK)
    change StokesDuality (fun i => qKR (g (gen i))) w (Additive ↥Blk.frattiniK) at hd
    exact hd
  choose f₀ hf₀ using fun i => RF.piB_surj (g (gen i))
  have hf₀C : ∀ i, QuotientGroup.mk' Blk.K (f₀ i) = c i := by
    intro i
    show QuotientGroup.mk' Blk.K (f₀ i) = qKR (g (gen i))
    rw [← hf₀ i]
    rfl
  have hvmem : ∀ k, PWord.eval f₀ (W k) ∈ Blk.frattiniK := by
    intro k
    rw [← RF.ker_piB]
    refine MonoidHom.mem_ker.mpr ?_
    have hmap := PWord.map_eval
      (⟨RF.piB, continuous_of_discreteTopology⟩ : ContinuousMonoidHom Y RF.YB) f₀ (W k)
    rw [show RF.piB (PWord.eval f₀ (W k)) =
        PWord.eval (fun i => RF.piB (f₀ i)) (W k) from hmap,
      show (fun i => RF.piB (f₀ i)) = fun i => g (gen i) from funext hf₀,
      hpres.rel g k]
  set v : κ → Additive ↥Blk.frattiniK :=
    fun k => Additive.ofMul ⟨PWord.eval f₀ (W k), hvmem k⟩ with hvdef
  have hgen : Subgroup.closure (Set.range c) = ⊤ :=
    closure_range_lower_eq_top θ (fun _ => rfl) hpres hθsurj
  have hv : ∀ lam : ElemDual (Additive ↥Blk.frattiniK),
      heisD0 (A := ElemDual (Additive ↥Blk.frattiniK)) c lam = 0 →
        lam (∑ k, v k) = 0 := by
    intro lam hlam
    have hfix : lam ∈ fixedPts (Y ⧸ Blk.K) (ElemDual (Additive ↥Blk.frattiniK)) := by
      have hmem : lam ∈
          ((heisD0 (A := ElemDual (Additive ↥Blk.frattiniK)) c).ker : Set _) :=
        AddMonoidHom.mem_ker.mpr hlam
      rwa [ker_heisD0_eq_fixedPts hgen] at hmem
    set dc : ↥(RCharSub Blk) :=
      ⟨lam, fun y r => RStageLocal.elemDual_fixed_apply_conj hRK lam hfix y r⟩ with hdc
    by_cases hdc0 : dc = 0
    · have hlam0 : lam = 0 := congrArg Subtype.val hdc0
      rw [hlam0]
      rfl
    · have hne : (blockRObstructionData T Blk hE2).toDR dc ≠ RF.zeroDR := by
        intro heq
        apply hdc0
        rw [← Equiv.symm_apply_apply (blockRObstructionData T Blk hE2).toDR dc, heq]
        exact (blockRObstructionData T Blk hE2).h0
      let Q := RF.scalarCover ((blockRObstructionData T Blk hE2).toDR dc) hne
      obtain ⟨gc, hgc⟩ := (obs_zero_iff_lifts RF (blockRObstructionData T Blk hE2)
        htriv hcard g dc hne).mp (LinearMap.congr_fun hg dc)
      have hgcC : ∀ i, qKR (Q.p (gc (gen i))) = c i := by
        intro i
        rw [hgc]
        rfl
      have hcov : ∀ i, Q.p
          ((blockRObstructionData T Blk hE2).coverMap
            ((blockRObstructionData T Blk hE2).toDR dc) hne (f₀ i))
          = Q.p (gc (gen i)) := by
        intro i
        rw [← MonoidHom.comp_apply,
          (blockRObstructionData T Blk hE2).coverMap_lifts, hf₀ i, hgc]
      obtain ⟨x, hx⟩ := exists_kernel_offset Q.p (coverJ Q)
        (fun z hz => exists_coverJ_of_mem_ker Q hz)
        (fun i => (blockRObstructionData T Blk hE2).coverMap
          ((blockRObstructionData T Blk hE2).toDR dc) hne (f₀ i))
        (fun i => gc (gen i)) hcov
      have hker : ∀ k, Q.p
          ((blockRObstructionData T Blk hE2).coverMap
            ((blockRObstructionData T Blk hE2).toDR dc) hne (PWord.eval f₀ (W k))) = 1 := by
        intro k
        rw [← MonoidHom.comp_apply,
          (blockRObstructionData T Blk hE2).coverMap_lifts]
        exact MonoidHom.mem_ker.mp (by rw [RF.ker_piB]; exact hvmem k)
      choose ζ hζ using fun k => exists_coverJ_of_mem_ker Q (hker k)
      have hζeval : ∀ k, PWord.eval (fun i => coverJ Q (x i) * gc (gen i)) (W k)
          = coverJ Q (ζ k) := by
        intro k
        rw [show (fun i => coverJ Q (x i) * gc (gen i)) =
            fun i => (blockRObstructionData T Blk hE2).coverMap
              ((blockRObstructionData T Blk hE2).toDR dc) hne (f₀ i) from
                funext fun i => (hx i).symm]
        change PWord.eval
            (fun i => discreteCMH ((blockRObstructionData T Blk hE2).coverMap
              ((blockRObstructionData T Blk hE2).toDR dc) hne) (f₀ i)) (W k) = _
        exact (PWord.map_eval
          (discreteCMH ((blockRObstructionData T Blk hE2).coverMap
            ((blockRObstructionData T Blk hE2).toDR dc) hne)) f₀ (W k)).symm.trans (hζ k)
      have hsum : ∑ k, ζ k = 0 :=
        sum_relatorFib_eq_zero (qKR.comp Q.p) (coverJ Q) htrivC
          (coverJ_add Q) (coverJ_comm Q) (coverJ_injective Q) hpres hres2
          (lower_rel θ (fun _ => rfl) hpres hres2) hend gc hgcC x ζ hζeval
      rw [map_sum]
      calc
        ∑ k, lam (v k) = ∑ k, ζ k := by
          apply Finset.sum_congr rfl
          intro k _
          rw [hvdef]
          change (blockRObstructionData T Blk hE2).pair dc
              (Additive.ofMul (⟨PWord.eval f₀ (W k), hvmem k⟩ : ↥Blk.frattiniK)) = ζ k
          rw [(blockRObstructionData T Blk hE2).pair_coverMap dc hne,
            hζ k, show coverJ Q (ζ k) = Q.z ^ (ζ k).val from rfl]
          change CentralObstruction.zsign (trivialRCD Q) (Q.z ^ (ζ k).val) = ζ k
          exact CentralObstruction.zsign_z_pow (trivialRCD Q) (ζ k)
        _ = 0 := hsum
  obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp (sepWordN hdc v hv)
  letI actY : DistribMulAction Y (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ (QuotientGroup.mk' Blk.K)
  set j : Additive ↥Blk.frattiniK → Y :=
    fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y) with hj
  have hact : ∀ (y : Y) (a : Additive ↥Blk.frattiniK),
      y • a = QuotientGroup.mk' Blk.K y • a := fun _ _ => rfl
  have hjmul : ∀ a b : Additive ↥Blk.frattiniK, j (a + b) = j a * j b := fun _ _ => rfl
  have hjconj : ∀ (y : Y) (a : Additive ↥Blk.frattiniK),
      j (y • a) = y * j a * y⁻¹ := by
    intro y a
    rw [hact y a]
    have hs := RStageLocal.conjC_smul_of_mk hRK y (Additive.toMul a)
    exact congrArg
      (fun z : Additive ↥Blk.frattiniK => ((Additive.toMul z : ↥Blk.frattiniK) : Y)) hs
  have hjker : ∀ a : Additive ↥Blk.frattiniK, RF.piB (j a) = 1 := fun a =>
    MonoidHom.mem_ker.mp (by rw [RF.ker_piB]; exact (Additive.toMul a).2)
  have hker2 : ∀ y : Y, RF.piB y = 1 → y * y = 1 := by
    intro y hy
    apply hR2 y
    rw [← RF.ker_piB]
    exact MonoidHom.mem_ker.mpr hy
  have hkill : ∀ k, PWord.eval (fun i => j (x i) * f₀ i) (W k) = 1 := by
    intro k
    rw [eval_corrected_heisD1 (QuotientGroup.mk' Blk.K) j hact hjmul hjconj hf₀C hresR x k,
      show heisD1 (A := Additive ↥Blk.frattiniK) c w x k = v k from congrFun hx k,
      hvdef]
    exact hR2 _ (hvmem k)
  obtain ⟨φ, hφ⟩ := hpres.extend (fun i => j (x i) * f₀ i) hkill
    (isWildTwo_corrected RF.piB j hjker hf₀ hwild2 hker2 x)
  have hpin : (⟨RF.piB.comp φ.toMonoidHom,
      (continuous_of_discreteTopology (f := ⇑RF.piB)).comp φ.continuous_toFun⟩ :
        ContinuousMonoidHom Γ RF.YB) = g := by
    refine eq_of_eqOn_gen hpres.gen_top fun i => ?_
    show RF.piB (φ (gen i)) = g (gen i)
    rw [hφ i]
    exact pi_corrected RF.piB j hjker hf₀ x i
  exact ⟨φ, fun γ => congrArg (fun ψ : ContinuousMonoidHom Γ RF.YB => ψ γ) hpin⟩

/-- **Boundary-lift regression for candidate-side `R`-separation.**

This is `homLift_of_obs_zero_markingN` in exactly the `BoundaryLiftsK` shape consumed by
`stageR136_ofRSepDataK`.  In particular, the bundled surjectivity is used as an input; the
boundary equation itself is irrelevant to the marking correction.  Unlike the old `StageSep`
residuals, the theorem keeps the necessary block hypotheses `hRK` and `hR2` explicit. -/
theorem homLift_of_obs_zero_boundaryLiftK_markingN
    {q : ℕ} {P : ProfiniteGrp} {nuP : ContinuousMonoidHom P Ztwo}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2)
    (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ q nuP))
    (F : BoundaryFrameK q P H E)
    (g : BoundaryLiftsK b F (blockFrameImpl T Blk hE2).TB)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hwild2 : IsWildTwo J (fun i => g.1.1 (gen i)))
    (hres2 :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      letI := scalarActionZmodTwo (Y ⧸ Blk.K)
      ResolvesAt W w (WordLift (ZMod 2) (Y ⧸ Blk.K)))
    (hresR :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality
        (fun i =>
          QuotientGroup.map Blk.frattiniK Blk.K (MonoidHom.id Y)
            (by rw [Subgroup.comap_id]; exact SectionSeven.frattiniLike_le Blk.K)
            (g.1.1 (gen i)))
        w (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w)
    (hg : obs (blockFrameImpl T Blk hE2) (blockRObstructionData T Blk hE2)
      htriv hcard g.1.1 = 0) :
    ∃ φ : ContinuousMonoidHom Γ Y,
      ∀ γ, (blockFrameImpl T Blk hE2).piB (φ γ) = g.1.1 γ := by
  exact homLift_of_obs_zero_markingN hE2 hRK hR2 htriv hcard g.1.1 g.1.2 hpres
    hwild2 hres2 hresR hd hend hg

end Separation

section Count

variable {ι κ : Type*} {Γ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι]
  [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  {gen : ι → Γ} {W : κ → PWord ι} {w : κ → FreeGroup ι} {J : Set ι}

/-- **The honest degree-`n` cardinality of the R-stage torsor.**

This is generic in the source presentation and the marked target.  The proof factors the count
as

`RCocycle ~= Z1(Gamma, R) ~= ker(d1_word)`

and then applies the degree-`n` Stokes count.  In particular, the target data alone do not imply
the result: `hpres`, `hres`, `hwild2`, `hd`, and `hend` are genuinely source-cohomological inputs.
-/
theorem rCocycle_cardN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
        * Nat.card (blockFrameImpl T Blk hE2).DR := by
  classical
  letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
  letI actC : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
    RStageLocal.conjC Blk hRK
  let theta : ContinuousMonoidHom Γ (Y ⧸ Blk.K) :=
    ⟨(QuotientGroup.mk' Blk.K).comp f.toMonoidHom, by
      show Continuous fun gamma => QuotientGroup.mk' Blk.K (f gamma)
      exact Continuous.comp continuous_of_discreteTopology f.continuous_toFun⟩
  have htheta_surj : Function.Surjective theta := by
    intro c
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective Blk.K c
    obtain ⟨gamma, hgamma⟩ := hf y
    exact ⟨gamma, by show QuotientGroup.mk' Blk.K (f gamma) = c; rw [hgamma, hy]⟩
  letI actG : DistribMulAction Γ (Additive ↥Blk.frattiniK) :=
    DistribMulAction.compHom _ theta.toMonoidHom
  letI : TopologicalSpace (Additive ↥Blk.frattiniK) :=
    (inferInstance : TopologicalSpace ↥Blk.frattiniK)
  haveI : DiscreteTopology (Additive ↥Blk.frattiniK) :=
    ⟨(inferInstance : DiscreteTopology ↥Blk.frattiniK).eq_bot⟩
  haveI : Finite (Additive ↥Blk.frattiniK) := inferInstance
  haveI : ContinuousSMul Γ (Additive ↥Blk.frattiniK) := by
    refine ⟨?_⟩
    have hfac : (fun p : Γ × Additive ↥Blk.frattiniK => p.1 • p.2)
        = (fun q : (Y ⧸ Blk.K) × Additive ↥Blk.frattiniK => q.1 • q.2)
          ∘ (fun p : Γ × Additive ↥Blk.frattiniK => (theta p.1, p.2)) := rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((theta.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have hcomp : ∀ (gamma : Γ) (a : Additive ↥Blk.frattiniK),
      gamma • a = theta gamma • a := fun _ _ => rfl
  have hA2 : ∀ a : Additive ↥Blk.frattiniK, a + a = 0 :=
    RStageLocal.frattiniK_add_self hRK hR2
  have htheta_apply (gamma : Γ) :
      theta gamma = QuotientGroup.mk' Blk.K (f gamma) := rfl
  have hwild2_theta : IsWildTwo J (fun i => theta (gen i)) := by
    simpa only [htheta_apply] using hwild2
  have hd_theta : StokesDuality (fun i => theta (gen i)) w
      (Additive ↥Blk.frattiniK) := by
    simpa only [htheta_apply] using hd
  have hsmul : ∀ (gamma : Γ) (a : Additive ↥Blk.frattiniK),
      gamma • a = Additive.ofMul
        (⟨f gamma * ((Additive.toMul a : ↥Blk.frattiniK) : Y) * (f gamma)⁻¹,
          RStageLocal.conj_mem_R (f gamma) (Additive.toMul a)⟩ : ↥Blk.frattiniK) := by
    intro gamma a
    have h1 : gamma • a
        = (QuotientGroup.mk' Blk.K (f gamma) : Y ⧸ Blk.K) •
          Additive.ofMul (Additive.toMul a) := rfl
    rw [h1]
    exact RStageLocal.conjC_smul_of_mk hRK (f gamma) (Additive.toMul a)
  have hequiv : RCocycle (blockFrameImpl T Blk hE2) f
      ≃ ↥(Z1 Γ (Additive ↥Blk.frattiniK)) :=
    { toFun := fun c =>
        ⟨fun gamma => Additive.ofMul ⟨c.u gamma, c.mem gamma⟩, by
          refine mem_Z1_iff.mpr ⟨?_, ?_⟩
          · show Continuous fun gamma =>
              (⟨c.u gamma, c.mem gamma⟩ : ↥Blk.frattiniK)
            exact Continuous.subtype_mk c.cont _
          · intro gamma delta
            rw [hsmul gamma (Additive.ofMul ⟨c.u delta, c.mem delta⟩)]
            refine Additive.toMul.injective (Subtype.ext ?_)
            exact c.crossed gamma delta⟩
      invFun := fun z =>
        { u := fun gamma => ((Additive.toMul (z.1 gamma) : ↥Blk.frattiniK) : Y)
          mem := fun gamma => (Additive.toMul (z.1 gamma)).2
          cont := continuous_subtype_val.comp (mem_Z1_iff.mp z.2).1
          crossed := by
            intro gamma delta
            have hz := (mem_Z1_iff.mp z.2).2 gamma delta
            rw [hsmul gamma (z.1 delta)] at hz
            simpa using congrArg
              (fun a => ((Additive.toMul a : ↥Blk.frattiniK) : Y)) hz }
      left_inv := fun c => RCocycle.ext rfl
      right_inv := fun z => Subtype.ext (funext fun gamma => rfl) }
  rw [Nat.card_congr hequiv,
    card_Z1_eq_card_wordZ1 theta hcomp (fun _ => rfl) hpres hres hA2 hwild2_theta,
    tcocycle_card_shape_fixedPts
      (isSelfDualN_of_stokesDuality hdeg hd_theta
        (lower_rel theta (fun _ => rfl) hpres hres) hend)
      (closure_range_lower_eq_top theta (fun _ => rfl) hpres htheta_surj),
    RStageLocal.card_fixedPts_eq_card_RCharSub hRK,
    blockRChar_card T Blk hE2]

/-- `rCocycle_cardN` in the corrected recursion's own coefficient vocabulary. -/
theorem rCocycle_card_standard_zRN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (n + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = zRN (blockFrameImpl T Blk hE2) (standardNumerics n) := by
  rw [rCocycle_cardN hE2 hRK hR2 f hf hpres hres hwild2 hdeg hd hend, zRN,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]

/-- Above degree one, the generic `tMult` coefficient is strictly larger than the frozen square
as soon as the coefficient group and the remaining factor are nontrivial. -/
theorem standardNumerics_tMult_ne_sq {n r d : ℕ} (hn : 2 ≤ n) (hr : 1 < r) (hd : 0 < d) :
    (standardNumerics n).tMult r * d ≠ r ^ 2 * d := by
  have hexp : 2 < n + 1 := Nat.lt_succ_of_le hn
  have hp : r ^ 2 < r ^ (n + 1) := Nat.pow_lt_pow_right hr hexp
  have hm : r ^ 2 * d < r ^ (n + 1) * d := Nat.mul_lt_mul_of_pos_right hp hd
  intro h
  exact (Nat.ne_of_lt hm) (by simpa [standardNumerics] using h.symm)

/-- **No-go for the rank-one-calibrated `zR`.**  If the degree-`n` Stokes calculation has been
performed, `n >= 2`, and `R` is nontrivial, its result cannot equal the current
`RecursionFrame.zR`.  The `D_R` factor needs no hypothesis: the frame supplies `zeroDR`, so its
finite carrier is automatically nonempty.

This theorem deliberately does not alter `zR`; it makes the specification mismatch explicit for
the degree-indexed recursion lane to resolve. -/
theorem rCocycle_card_ne_zR_of_cardN {n : ℕ}
    (hE2 : ∀ e : E, e ^ 2 = 1) (f : ContinuousMonoidHom Γ Y)
    (hcard : Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
        * Nat.card (blockFrameImpl T Blk hE2).DR)
    (hn : 2 ≤ n) (hR : 1 < Nat.card (Additive ↥Blk.frattiniK)) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      ≠ (blockFrameImpl T Blk hE2).zR := by
  rw [hcard]
  change (standardNumerics n).tMult (Nat.card (Additive ↥Blk.frattiniK))
      * Nat.card (blockFrameImpl T Blk hE2).DR
    ≠ Nat.card ↥Blk.frattiniK ^ 2 * Nat.card (blockFrameImpl T Blk hE2).DR
  rw [← Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  letI : Nonempty (blockFrameImpl T Blk hE2).DR :=
    ⟨(blockFrameImpl T Blk hE2).zeroDR⟩
  exact standardNumerics_tMult_ne_sq hn hR Nat.card_pos

/-- At degree one, `rCocycle_cardN` specializes definitionally to the frozen block frame's
`zR = #R^2 * #D_R`.  This is the precise regression theorem for the old Q2 count. -/
theorem rCocycle_card_one
    (hE2 : ∀ e : E, e ^ 2 = 1)
    (hRK : ∀ r ∈ Blk.frattiniK, ∀ k ∈ Blk.K, r * k = k * r)
    (hR2 : ∀ r ∈ Blk.frattiniK, r * r = 1)
    (f : ContinuousMonoidHom Γ Y) (hf : Function.Surjective f)
    (hpres : IsAdmissibleMarkedPresentation Γ gen W J)
    (hres :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      ResolvesAt W w (WordLift (Additive ↥Blk.frattiniK) (Y ⧸ Blk.K)))
    (hwild2 : IsWildTwo J
      (fun i => QuotientGroup.mk' Blk.K (f (gen i))))
    (hdeg : Nat.card ι = Nat.card κ + (1 + 1))
    (hd :
      letI : CommGroup ↥Blk.frattiniK := RStageLocal.rCommGroup Blk hRK
      letI : DistribMulAction (Y ⧸ Blk.K) (Additive ↥Blk.frattiniK) :=
        RStageLocal.conjC Blk hRK
      StokesDuality (fun i => QuotientGroup.mk' Blk.K (f (gen i))) w
        (Additive ↥Blk.frattiniK))
    (hend : IsStokesEndpoint w) :
    Nat.card (RCocycle (blockFrameImpl T Blk hE2) f)
      = (blockFrameImpl T Blk hE2).zR := by
  rw [rCocycle_cardN hE2 hRK hR2 f hf hpres hres hwild2 hdeg hd hend,
    standardNumerics_one_tMult,
    Nat.card_congr (Additive.toMul (α := ↥Blk.frattiniK))]
  rfl

end Count

end GQ2.Dyadic.Count
