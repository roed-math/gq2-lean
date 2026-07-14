import GQ2.CentralObstruction
import GQ2.LocalLiftingDuality
import GQ2.WordCohBridge
import GQ2.DualityAssembly
import GQ2.RadicalEdge.Local

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
    add_comm := fun a b => Additive.toMul.injective <| Subtype.ext
      (D.hcomm _ (D.hTM (Additive.toMul a).2) _ (D.hTM (Additive.toMul b).2)) }

/-- The conjugation action of `C = Bg ⧸ D.M` on `T`, at the canonical representative. -/
noncomputable def cactFun (c : Bg ⧸ D.M) (t : ↥D.T) : ↥D.T :=
  ⟨Quotient.out c * t.1 * (Quotient.out c)⁻¹, conj_mem_T D (Quotient.out c) t⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem cactFun_eq (c : Bg ⧸ D.M) {b : Bg} (hb : QuotientGroup.mk b = c) (t : ↥D.T) :
    (cactFun D c t).1 = b * t.1 * b⁻¹ :=
  conj_eq_of_mk_eq D (by rw [QuotientGroup.out_eq' c, hb]) t

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem cactFun_one (t : ↥D.T) : cactFun D 1 t = t := by
  apply Subtype.ext
  rw [cactFun_eq D 1 (by rw [QuotientGroup.mk_one]) t]; group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
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

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem cActT_toMul (c : Bg ⧸ D.M) (t : Additive ↥D.T) :
    Additive.toMul (c • t) = cactFun D c (Additive.toMul t) := rfl

/-- The discrete topology on the `𝔽₂`-dual (a valid coefficient module). -/
instance instTopElemDualT : TopologicalSpace (ElemDual (Additive ↥D.T)) := ⊥
instance instDiscElemDualT : DiscreteTopology (ElemDual (Additive ↥D.T)) := ⟨rfl⟩


end RadicalEdgeGammaA

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 8.6 = ⟦lem-radicaledge⟧
-/
