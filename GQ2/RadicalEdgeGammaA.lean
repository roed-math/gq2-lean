import GQ2.CentralObstruction
import GQ2.LocalLiftingDuality
import GQ2.WordCohBridge
import GQ2.DualityAssembly
import GQ2.RadicalEdgeLocal

/-!
# Lemma 8.6, `Γ_A` source: the duality half via `prop_5_15`  (ticket P-16c3)

Port of `RadicalEdgeLocal.exists_good_twist`'s **source-generic prefix** (`CentralObstruction`
is generic over the source group `Γ`, so the `act`/`φf`/`hφZ1`/`hφne` blocks port verbatim by
`AbsGalQ2 → GA`), with the B6 tail replaced by the word-complex bridge: the nonzero shifted-edge
class `[φf]` transports through `WordCohBridge.h1Equiv` + `dualAddEquiv` to a nonzero `H1w`-dual
class, and `FoxH.prop_5_15`'s perfect pairing yields the crossed `T`-cocycle whose variation is
not a coboundary.  Source group is the **raw** `GA = F₄ ⧸ N_A` (matching `WordCohBridge`; the
`GammaA` transport is P-16c5).  See `docs/p16c3-recon.md`.

Axioms (target): std-3 only — the pairing comes from `prop_5_15` (P-13f), not B6.
-/

namespace GQ2

namespace SectionEight

namespace RadicalEdgeGammaA

open CentralObstruction ContCoh LocalLiftingDuality WordCohBridge FoxH RadicalEdgeLocal

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  (D : RadicalCoverData Bg)

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
/-- **The `Γ_A` twist construction** (Lemma 8.6, `Γ_A` source, duality step): from `NoDescent`,
a crossed `T`-cocycle whose variation cochain is not a (trivial-action) coboundary — same
action-free conclusion as the local `exists_good_twist`, but proved through the word complex.
**Currently: prefix ported, bridge tail sorried (P-16c3 in progress).** -/
theorem exists_good_twist_gammaA (S : TComplement D)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GA (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    ∃ u : TCocycle D ρ,
      ¬ ∃ c : GA → ZMod 2, Continuous c ∧
        ∀ γ δ : GA, varCoc D ρ S u (γ, δ) = c δ - c (γ * δ) + c γ := by
  classical
  -- `GA` is not a Galois group: give `μ₂` the trivial `GA`-action (μ₂ = {±1} is acted on
  -- trivially anyway; `smulMuN_triv` replaces the `AbsGalQ2`-specific `smulMuN_triv`).
  letI actMuN : DistribMulAction GA (MuN 2) :=
    { smul := fun _ x => x, one_smul := fun _ => rfl, mul_smul := fun _ _ _ => rfl,
      smul_zero := fun _ => rfl, smul_add := fun _ _ _ => rfl }
  haveI : ContinuousSMul GA (MuN 2) := ⟨continuous_snd⟩
  have smulMuN_triv : ∀ (g : GA) (x : MuN 2), g • x = x := fun _ _ => rfl
  haveI := discreteTopology_quotient D
  -- ===== `T` as a `G_ℚ₂`-module through `ρ`-conjugation =====
  letI : CommGroup ↥D.T := tCommGroup D
  letI : TopologicalSpace (Additive ↥D.T) := (inferInstance : TopologicalSpace ↥D.T)
  haveI : DiscreteTopology (Additive ↥D.T) :=
    ⟨(inferInstance : DiscreteTopology ↥D.T).eq_bot⟩
  haveI : Finite (Additive ↥D.T) := (inferInstance : Finite ↥D.T)
  haveI : IsTopologicalAddGroup (Additive ↥D.T) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  set act : GA → ↥D.T → ↥D.T := fun γ t =>
    ⟨Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹,
      conj_mem_T D (Quotient.out (ρ γ)) t⟩ with hactdef
  have hact_eq : ∀ (γ : GA) (b : Bg), QuotientGroup.mk b = ρ γ →
      ∀ t : ↥D.T, (act γ t).1 = b * t.1 * b⁻¹ := by
    intro γ b hb t
    show Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹ = b * t.1 * b⁻¹
    exact conj_eq_of_mk_eq D (by rw [QuotientGroup.out_eq' (ρ γ), hb]) t
  have hact_one : ∀ t : ↥D.T, act 1 t = t := by
    intro t
    apply Subtype.ext
    rw [hact_eq 1 1 (by rw [QuotientGroup.mk_one, map_one]) t]
    group
  have hact_mul : ∀ (γ δ : GA) (t : ↥D.T), act (γ * δ) t = act γ (act δ t) := by
    intro γ δ t
    apply Subtype.ext
    have hγ : (QuotientGroup.mk (Quotient.out (ρ γ)) : Bg ⧸ D.M) = ρ γ :=
      QuotientGroup.out_eq' _
    have hδ : (QuotientGroup.mk (Quotient.out (ρ δ)) : Bg ⧸ D.M) = ρ δ :=
      QuotientGroup.out_eq' _
    have hγδ : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
        = ρ (γ * δ) := by
      rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
    rw [hact_eq (γ * δ) _ hγδ t]
    show _ = Quotient.out (ρ γ) * (act δ t).1 * (Quotient.out (ρ γ))⁻¹
    show Quotient.out (ρ γ) * Quotient.out (ρ δ) * t.1
        * (Quotient.out (ρ γ) * Quotient.out (ρ δ))⁻¹
      = Quotient.out (ρ γ)
        * (Quotient.out (ρ δ) * t.1 * (Quotient.out (ρ δ))⁻¹) * (Quotient.out (ρ γ))⁻¹
    group
  have hact_mul' : ∀ (γ : GA) (t t' : ↥D.T),
      act γ (t * t') = act γ t * act γ t' := by
    intro γ t t'
    apply Subtype.ext
    show Quotient.out (ρ γ) * (t.1 * t'.1) * (Quotient.out (ρ γ))⁻¹
      = (Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹)
        * (Quotient.out (ρ γ) * t'.1 * (Quotient.out (ρ γ))⁻¹)
    group
  have hact_one_elt : ∀ γ : GA, act γ 1 = 1 := by
    intro γ
    apply Subtype.ext
    show Quotient.out (ρ γ) * (1 : Bg) * (Quotient.out (ρ γ))⁻¹ = 1
    group
  have hact_inv : ∀ (γ : GA) (t : ↥D.T), act γ⁻¹ (act γ t) = t := by
    intro γ t
    rw [← hact_mul, inv_mul_cancel, hact_one]
  letI actT : DistribMulAction GA (Additive ↥D.T) :=
    { smul := fun γ t => Additive.ofMul (act γ (Additive.toMul t))
      one_smul := fun t => hact_one _
      mul_smul := fun γ δ t => hact_mul γ δ _
      smul_zero := fun γ => hact_one_elt γ
      smul_add := fun γ t t' => hact_mul' γ _ _ }
  have hsmulT : ∀ (γ : GA) (t : Additive ↥D.T),
      γ • t = Additive.ofMul (act γ (Additive.toMul t)) := fun _ _ => rfl
  haveI : ContinuousSMul GA (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : GA × Additive ↥D.T => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × ↥D.T =>
            Additive.ofMul (⟨Quotient.out cq.1 * cq.2.1 * (Quotient.out cq.1)⁻¹,
              conj_mem_T D (Quotient.out cq.1) cq.2⟩ : ↥D.T))
          ∘ (fun p : GA × Additive ↥D.T =>
              ((ρ p.1 : Bg ⧸ D.M), Additive.toMul p.2)) := by
      funext p
      rfl
    rw [hfac]
    exact continuous_of_discreteTopology.comp
      ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)
  have htorT : ∀ x : Additive ↥D.T, (2 : ℕ) • x = 0 := by
    intro x
    rw [two_nsmul]
    show Additive.toMul x * Additive.toMul x = 1
    exact Subtype.ext (D.helem _ (D.hTM (Additive.toMul x).2))
  -- ===== φf / hφZ1 / hφne + the prop_5_15 bridge  (P-16c3 — WIP) =====
  -- STRUCTURAL PIVOT (docs/p16c3-recon.md): `MuDual`'s `DistribMulAction` is hardcoded to
  -- `AbsGalQ2` (TateDuality.lean:60,101) — there is NO `DistribMulAction GA (MuDual n M)`.  So
  -- the Γ_A shifted-edge cocycle must be built directly in `ElemDual (Additive ↥D.T)` (generic
  -- `DistribMulAction C (ElemDual A)`, FoxHeisenberg:568; `(g•λ)a = λ(g⁻¹•a)`), which also makes
  -- `dualAddEquiv` unnecessary.  Recipe: `φf γ := AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ)
  -- (act γ⁻¹ (Additive.toMul s))) (hφadd γ) : ElemDual (Additive ↥D.T)` (drop `muNTwoEquiv`);
  -- the cocycle law is `hcrossZ` + `ElemDual.smul_apply` (no `smul_muN_two_trivial`); `hφne` via
  -- `not_noDescent_of_edge_trivial` with `ℓ t := (lam : ElemDual _) (Additive.ofMul t)`.  Then
  -- `h1Equiv`/`z1Equiv` (A = `Additive ↥D.T`) + `prop_5_15` right-nondegeneracy ⟹ the crossed
  -- cocycle `u` with `varCoc` not a coboundary.  The module foundation above (act/actT/
  -- ContinuousSMul) is ported and builds.
  sorry

end RadicalEdgeGammaA

end SectionEight

end GQ2
