import GQ2.CentralObstruction
import GQ2.LocalLiftingDuality

/-!
# Lemma 8.6, local source: the B6 half-torsor count  (ticket P-16b)

Closes `SectionEight.lemma_8_6_local` through the P-16a engine
(`GQ2/CentralObstruction.lean`): given `NoDescent`, the twist producing the flip involution is
manufactured from **B6's perfect `(1,1)` pairing** (`GQ2.tateDuality 2 |>.perfect11`) applied
to the `T`-conjugation module.

The bridge (`docs/p16-ticket-split.md`, P-16b): the shifted edge
`φ(γ)(s) := ε̄(ρ(γ))(γ⁻¹•s)` is an exact `Z¹(G_ℚ₂, (A_T)^{μ₂∨})`-cocycle, and on the nose
`cup11Fun (muDualPairing) φ w = muNTwoEquiv.symm ∘ varCoc u_w` for the crossed `T`-cocycle
`u_w` corresponding to `w ∈ Z¹(A_T)`.  `NoDescent` forbids `[φ] = 0` (a coboundary constant
`λ` would trivialize the edge by `ρ`-surjectivity — `not_noDescent_of_edge_trivial`), so
perfectness yields `w` with nonzero cup class, hence nonzero variation class, and the
engine's `half_count` finishes with `#H²(G_ℚ₂, 𝔽₂) = 2` (`card_H2_zmod2_eq_two`).

**Hypotheses** (per the `lemma_8_2_local`/`lemma_8_3` amendment precedents): `G_ℚ₂` compact +
totally disconnected (instance binders) and topologically finitely generated (`hfg`, the
B1-shaped input supplied upstream) — these finitize `MLifts`.

Axioms: **B6** (`tateDuality`) and **B7** (through `card_H2_zmod2_eq_two`'s finiteness).
-/

namespace GQ2

namespace SectionEight

namespace RadicalEdgeLocal

open CentralObstruction ContCoh LocalLiftingDuality

variable {Bg : Type} [Group Bg] [TopologicalSpace Bg] [DiscreteTopology Bg] [Finite Bg]
  (D : RadicalCoverData Bg)

/-- Conjugation of `T`-elements only depends on the `M`-coset of the conjugator
(`M` centralizes `T`). -/
theorem conj_eq_of_mk_eq {b b' : Bg}
    (h : (QuotientGroup.mk b : Bg ⧸ D.M) = QuotientGroup.mk b') (t : ↥D.T) :
    b * t.1 * b⁻¹ = b' * t.1 * b'⁻¹ := by
  have hm : b⁻¹ * b' ∈ D.M := (QuotientGroup.eq (s := D.M)).mp h
  have hcomm := D.hcomm _ hm _ (D.hTM t.2)
  calc b * t.1 * b⁻¹
      = b * (t.1 * (b⁻¹ * b') * (b⁻¹ * b')⁻¹) * b⁻¹ := by group
    _ = b * ((b⁻¹ * b') * t.1 * (b⁻¹ * b')⁻¹) * b⁻¹ := by rw [← hcomm]
    _ = b' * t.1 * b'⁻¹ := by group

/-- The commutative group structure on `↥T` (`T ≤ M` abelian). -/
@[reducible] def tCommGroup : CommGroup ↥D.T :=
  { (inferInstance : Group ↥D.T) with
    mul_comm := fun a b => Subtype.ext (D.hcomm _ (D.hTM a.2) _ (D.hTM b.2)) }

section GoodTwist

/-! ### The B6 twist construction, staged

`exists_good_twist` below is assembled from private helpers, one per stage: the
`ρ`-conjugation module (`outConj`/`rhoConj`/`conjModule`), the shifted-edge dual cocycle
(`shiftedEdge*`), its class nonvanishing (`shiftedEdge_class_ne_zero`), the B6 pairing
partner (`exists_pairing_partner`), and the crossed-cocycle packaging (`twistCocycle`)
with its cup ↔ variation bridge (`cup11Fun_shiftedEdge_eq_varCoc`). -/

attribute [local instance] tCommGroup discreteTopology_quotient

/-- Conjugation of `T`-elements by the canonical representative of a `Bg ⧸ M`-class. -/
private noncomputable def outConj (c : Bg ⧸ D.M) (t : ↥D.T) : ↥D.T :=
  ⟨Quotient.out c * t.1 * (Quotient.out c)⁻¹, conj_mem_T D (Quotient.out c) t⟩

/-- `outConj` computes as conjugation by any representative of the class. -/
private theorem outConj_coe (c : Bg ⧸ D.M) (b : Bg) (hb : QuotientGroup.mk b = c)
    (t : ↥D.T) : (outConj D c t).1 = b * t.1 * b⁻¹ :=
  conj_eq_of_mk_eq D (by rw [QuotientGroup.out_eq' c, hb]) t

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `outConj c` is multiplicative in the `T`-slot. -/
private theorem outConj_map_mul (c : Bg ⧸ D.M) (t t' : ↥D.T) :
    outConj D c (t * t') = outConj D c t * outConj D c t' := by
  apply Subtype.ext
  show Quotient.out c * (t.1 * t'.1) * (Quotient.out c)⁻¹
    = Quotient.out c * t.1 * (Quotient.out c)⁻¹ * (Quotient.out c * t'.1 * (Quotient.out c)⁻¹)
  group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `outConj c` fixes the identity. -/
private theorem outConj_map_one (c : Bg ⧸ D.M) : outConj D c 1 = 1 := by
  apply Subtype.ext
  show Quotient.out c * (1 : Bg) * (Quotient.out c)⁻¹ = 1
  group

/-- The `ρ`-conjugation of `T`-elements — the raw action underlying the B6 twist module. -/
private noncomputable def rhoConj (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (γ : AbsGalQ2) (t : ↥D.T) : ↥D.T :=
  outConj D (ρ γ) t

/-- `rhoConj` computes as conjugation by any representative of `ρ γ`. -/
private theorem rhoConj_coe (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) (γ : AbsGalQ2)
    (b : Bg) (hb : QuotientGroup.mk b = ρ γ) (t : ↥D.T) :
    (rhoConj D ρ γ t).1 = b * t.1 * b⁻¹ :=
  outConj_coe D (ρ γ) b hb t

omit [DiscreteTopology Bg] in
/-- `rhoConj γ` is multiplicative in the `T`-slot. -/
private theorem rhoConj_map_mul (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) (γ : AbsGalQ2)
    (t t' : ↥D.T) : rhoConj D ρ γ (t * t') = rhoConj D ρ γ t * rhoConj D ρ γ t' :=
  outConj_map_mul D (ρ γ) t t'

omit [DiscreteTopology Bg] in
/-- `rhoConj γ` fixes the identity. -/
private theorem rhoConj_map_one (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (γ : AbsGalQ2) : rhoConj D ρ γ 1 = 1 :=
  outConj_map_one D (ρ γ)

/-- `rhoConj` at `γ = 1` is the identity. -/
private theorem rhoConj_one (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) (t : ↥D.T) :
    rhoConj D ρ 1 t = t := by
  apply Subtype.ext
  rw [rhoConj_coe D ρ 1 1 (by rw [QuotientGroup.mk_one, map_one]) t]
  group

/-- `rhoConj` is an action: it composes along multiplication in `G_ℚ₂`. -/
private theorem rhoConj_mul (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) (γ δ : AbsGalQ2)
    (t : ↥D.T) : rhoConj D ρ (γ * δ) t = rhoConj D ρ γ (rhoConj D ρ δ t) := by
  have hγδ : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
      = ρ (γ * δ) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.out_eq' (ρ γ), QuotientGroup.out_eq' (ρ δ),
      map_mul]
  apply Subtype.ext
  rw [rhoConj_coe D ρ (γ * δ) _ hγδ t]
  show Quotient.out (ρ γ) * Quotient.out (ρ δ) * t.1
      * (Quotient.out (ρ γ) * Quotient.out (ρ δ))⁻¹
    = Quotient.out (ρ γ)
      * (Quotient.out (ρ δ) * t.1 * (Quotient.out (ρ δ))⁻¹) * (Quotient.out (ρ γ))⁻¹
  group

/-- `rhoConj γ⁻¹` undoes `rhoConj γ`. -/
private theorem rhoConj_inv_rhoConj (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (γ : AbsGalQ2) (t : ↥D.T) : rhoConj D ρ γ⁻¹ (rhoConj D ρ γ t) = t := by
  rw [← rhoConj_mul, inv_mul_cancel, rhoConj_one]

/-- **The `ρ`-conjugation module**: `Additive ↥T` as a `G_ℚ₂`-module via `rhoConj` (the
coefficient module of the B6 `(1,1)` pairing). -/
@[reducible] private noncomputable def conjModule (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) :
    DistribMulAction AbsGalQ2 (Additive ↥D.T) :=
  { smul := fun γ t => Additive.ofMul (rhoConj D ρ γ (Additive.toMul t))
    one_smul := fun t => rhoConj_one D ρ (Additive.toMul t)
    mul_smul := fun γ δ t => rhoConj_mul D ρ γ δ (Additive.toMul t)
    smul_zero := fun γ => rhoConj_map_one D ρ γ
    smul_add := fun γ t t' => rhoConj_map_mul D ρ γ (Additive.toMul t) (Additive.toMul t') }

/-- Continuity of the `ρ`-conjugation action: it factors through the discrete quotient. -/
private theorem conjModule_continuousSMul (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)) :
    letI := conjModule D ρ
    ContinuousSMul AbsGalQ2 (Additive ↥D.T) := by
  letI := conjModule D ρ
  constructor
  have hfac : (fun p : AbsGalQ2 × Additive ↥D.T => p.1 • p.2)
      = (fun cq : (Bg ⧸ D.M) × ↥D.T => Additive.ofMul (outConj D cq.1 cq.2))
        ∘ (fun p : AbsGalQ2 × Additive ↥D.T => ((ρ p.1 : Bg ⧸ D.M), Additive.toMul p.2)) := by
    funext p
    rfl
  rw [hfac]
  exact continuous_of_discreteTopology.comp
    ((ρ.continuous_toFun.comp continuous_fst).prodMk continuous_snd)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `Additive ↥T` is `2`-torsion (`T` is elementary abelian). -/
private theorem two_nsmul_additiveT_eq_zero (x : Additive ↥D.T) : (2 : ℕ) • x = 0 := by
  rw [two_nsmul]
  show Additive.toMul x * Additive.toMul x = 1
  exact Subtype.ext (D.helem _ (D.hTM (Additive.toMul x).2))

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Additivity in the `T`-slot of the quotient-level shifted edge. -/
private theorem edgeQ_outConj_add (S : TComplement D) (c : Bg ⧸ D.M)
    (s s' : Additive ↥D.T) :
    edgeQ D S c (outConj D c⁻¹ (Additive.toMul (s + s')))
      = edgeQ D S c (outConj D c⁻¹ (Additive.toMul s))
        + edgeQ D S c (outConj D c⁻¹ (Additive.toMul s')) := by
  rw [show Additive.toMul (s + s') = Additive.toMul s * Additive.toMul s' from rfl,
    outConj_map_mul D c⁻¹]
  exact edge_add D S (Quotient.out c) _ _

/-- The quotient-level shifted-edge functional through which `shiftedEdge` factors
(discrete source ⇒ continuity). -/
private noncomputable def shiftedEdgeQ (S : TComplement D) (c : Bg ⧸ D.M) :
    MuDual 2 (Additive ↥D.T) :=
  (muNTwoEquiv.symm.toAddMonoidHom.comp
    (AddMonoidHom.mk' (fun s => edgeQ D S c (outConj D c⁻¹ (Additive.toMul s)))
      (edgeQ_outConj_add D S c))
    : Additive ↥D.T →+ MuN 2)

/-- Additivity in the `T`-slot of the shifted edge. -/
private theorem edgeQ_rhoConj_add (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (γ : AbsGalQ2) (s s' : Additive ↥D.T) :
    edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul (s + s')))
      = edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul s))
        + edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul s')) := by
  rw [show rhoConj D ρ γ⁻¹ (Additive.toMul (s + s'))
      = rhoConj D ρ γ⁻¹ (Additive.toMul s) * rhoConj D ρ γ⁻¹ (Additive.toMul s') from
    rhoConj_map_mul D ρ γ⁻¹ (Additive.toMul s) (Additive.toMul s')]
  exact edge_add D S (Quotient.out (ρ γ)) _ _

/-- **The shifted-edge dual cochain** `φ(γ) = ε̄(ρ(γ))(γ⁻¹ • ·)`, valued in the `μ₂`-dual of
the `ρ`-conjugation module. -/
private noncomputable def shiftedEdge (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (γ : AbsGalQ2) : MuDual 2 (Additive ↥D.T) :=
  (muNTwoEquiv.symm.toAddMonoidHom.comp
    (AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul s)))
      (edgeQ_rhoConj_add D ρ S γ))
    : Additive ↥D.T →+ MuN 2)

/-- Evaluation of the shifted edge. -/
private theorem shiftedEdge_apply (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (γ : AbsGalQ2) (s : Additive ↥D.T) :
    (shiftedEdge D ρ S γ : Additive ↥D.T →+ MuN 2) s
      = muNTwoEquiv.symm (edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul s))) :=
  rfl

/-- `shiftedEdge` factors through the discrete quotient. -/
private theorem shiftedEdge_eq_comp (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) :
    shiftedEdge D ρ S = shiftedEdgeQ D S ∘ (fun γ : AbsGalQ2 => (ρ γ : Bg ⧸ D.M)) := by
  funext γ
  refine DFunLike.ext _ _ fun s => ?_
  rw [shiftedEdge_apply]
  show muNTwoEquiv.symm (edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ (Additive.toMul s)))
    = muNTwoEquiv.symm (edgeQ D S (ρ γ) (outConj D (ρ γ)⁻¹ (Additive.toMul s)))
  refine congrArg muNTwoEquiv.symm (congrArg (edgeQ D S (ρ γ)) (Subtype.ext ?_))
  show Quotient.out (ρ γ⁻¹) * (Additive.toMul s).1 * (Quotient.out (ρ γ⁻¹))⁻¹
    = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
      * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹
  rw [show Quotient.out (ρ γ⁻¹) = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) from by rw [map_inv]]

/-- Continuity of the shifted edge (through the discrete quotient). -/
private theorem continuous_shiftedEdge (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) : Continuous (shiftedEdge D ρ S) := by
  rw [shiftedEdge_eq_comp]
  exact continuous_of_discreteTopology.comp ρ.continuous_toFun

/-- The `ℤ/2`-level crossed law of the shifted edge (the `Z¹`-identity before dualizing). -/
private theorem edgeQ_rhoConj_crossed (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (γ δ : AbsGalQ2) (t : ↥D.T) :
    edgeQ D S (ρ (γ * δ)) (rhoConj D ρ (γ * δ)⁻¹ t)
      = edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ t)
        + edgeQ D S (ρ δ) (rhoConj D ρ δ⁻¹ (rhoConj D ρ γ⁻¹ t)) := by
  have hγ : (QuotientGroup.mk (Quotient.out (ρ γ)) : Bg ⧸ D.M) = ρ γ :=
    QuotientGroup.out_eq' _
  have hδ : (QuotientGroup.mk (Quotient.out (ρ δ)) : Bg ⧸ D.M) = ρ δ :=
    QuotientGroup.out_eq' _
  have hγδrep : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
      = ρ (γ * δ) := by
    rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
  rw [edgeQ_eq D S (ρ (γ * δ)) hγδrep, edge_mul]
  have h2 : edge D S (Quotient.out (ρ γ))
        ⟨Quotient.out (ρ δ) * (rhoConj D ρ (γ * δ)⁻¹ t).1 * (Quotient.out (ρ δ))⁻¹,
          conj_mem_T D (Quotient.out (ρ δ)) (rhoConj D ρ (γ * δ)⁻¹ t)⟩
      = edgeQ D S (ρ γ) (rhoConj D ρ γ⁻¹ t) := by
    rw [edgeQ_eq D S (ρ γ) hγ]
    congr 1
    apply Subtype.ext
    show Quotient.out (ρ δ) * (rhoConj D ρ (γ * δ)⁻¹ t).1 * (Quotient.out (ρ δ))⁻¹
      = (rhoConj D ρ γ⁻¹ t).1
    have hsplit : rhoConj D ρ (γ * δ)⁻¹ t = rhoConj D ρ δ⁻¹ (rhoConj D ρ γ⁻¹ t) := by
      rw [show ((γ * δ)⁻¹ : AbsGalQ2) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ,
        rhoConj_mul D ρ δ⁻¹ γ⁻¹]
    rw [hsplit]
    have hδinv : (QuotientGroup.mk ((Quotient.out (ρ δ))⁻¹) : Bg ⧸ D.M) = ρ δ⁻¹ := by
      rw [QuotientGroup.mk_inv, hδ, map_inv]
    rw [rhoConj_coe D ρ δ⁻¹ _ hδinv]
    group
  have h1 : edge D S (Quotient.out (ρ δ)) (rhoConj D ρ (γ * δ)⁻¹ t)
      = edgeQ D S (ρ δ) (rhoConj D ρ δ⁻¹ (rhoConj D ρ γ⁻¹ t)) := by
    rw [edgeQ_eq D S (ρ δ) hδ]
    congr 1
    rw [show ((γ * δ)⁻¹ : AbsGalQ2) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ,
      rhoConj_mul D ρ δ⁻¹ γ⁻¹]
  rw [h1, h2]

/-- The shifted edge is an exact `Z¹(G_ℚ₂, (A_T)^{μ₂∨})`-cocycle. -/
private theorem shiftedEdge_mem_Z1 (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) :
    letI := conjModule D ρ
    haveI := conjModule_continuousSMul D ρ
    shiftedEdge D ρ S ∈ Z1 AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := by
  letI := conjModule D ρ
  haveI := conjModule_continuousSMul D ρ
  rw [mem_Z1_iff]
  refine ⟨continuous_shiftedEdge D ρ S, fun γ δ => ?_⟩
  refine DFunLike.ext _ _ fun s => ?_
  show (shiftedEdge D ρ S (γ * δ) : Additive ↥D.T →+ MuN 2) s
    = ((shiftedEdge D ρ S γ + γ • shiftedEdge D ρ S δ : MuDual 2 (Additive ↥D.T))
        : Additive ↥D.T →+ MuN 2) s
  have hsmul : ((γ • shiftedEdge D ρ S δ : MuDual 2 (Additive ↥D.T))
      : Additive ↥D.T →+ MuN 2) s
      = muNTwoEquiv.symm
          (edgeQ D S (ρ δ) (rhoConj D ρ δ⁻¹ (rhoConj D ρ γ⁻¹ (Additive.toMul s)))) := by
    rw [show ((γ • shiftedEdge D ρ S δ : MuDual 2 (Additive ↥D.T))
          : Additive ↥D.T →+ MuN 2) s
        = γ • (shiftedEdge D ρ S δ : Additive ↥D.T →+ MuN 2) ((γ⁻¹ : AbsGalQ2) • s) from rfl,
      smul_muN_two_trivial, shiftedEdge_apply]
    rfl
  rw [show ((shiftedEdge D ρ S γ + γ • shiftedEdge D ρ S δ : MuDual 2 (Additive ↥D.T))
        : Additive ↥D.T →+ MuN 2) s
      = (shiftedEdge D ρ S γ : Additive ↥D.T →+ MuN 2) s
        + ((γ • shiftedEdge D ρ S δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s
      from rfl,
    hsmul, shiftedEdge_apply D ρ S (γ * δ), shiftedEdge_apply D ρ S γ,
    edgeQ_rhoConj_crossed D ρ S γ δ (Additive.toMul s), map_add]

/-- **`[φ] ≠ 0`**: were the shifted edge a coboundary, the constant `λ` would trivialize the
edge through `ρ`-surjectivity (`not_noDescent_of_edge_trivial`), contradicting `NoDescent`. -/
private theorem shiftedEdge_class_ne_zero (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (hedge : D.NoDescent) (hρ : Function.Surjective ρ) :
    letI := conjModule D ρ
    haveI := conjModule_continuousSMul D ρ
    H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T))
      ⟨shiftedEdge D ρ S, shiftedEdge_mem_Z1 D ρ S⟩ ≠ 0 := by
  letI := conjModule D ρ
  haveI := conjModule_continuousSMul D ρ
  intro h0
  have hmem : shiftedEdge D ρ S ∈ B1 AbsGalQ2 (MuDual 2 (Additive ↥D.T)) :=
    AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
  obtain ⟨lam, hlam⟩ := hmem
  set ℓ : ↥D.T → ZMod 2 :=
    fun t => muNTwoEquiv ((lam : Additive ↥D.T →+ MuN 2) (Additive.ofMul t)) with hℓdef
  have hℓadd : ∀ t t' : ↥D.T, ℓ (t * t') = ℓ t + ℓ t' := by
    intro t t'
    show muNTwoEquiv ((lam : Additive ↥D.T →+ MuN 2) (Additive.ofMul (t * t'))) = _
    rw [show Additive.ofMul (t * t')
        = Additive.ofMul t + Additive.ofMul t' from rfl, map_add, map_add]
  refine (not_noDescent_of_edge_trivial D S ℓ hℓadd ?_) hedge
  intro b t
  obtain ⟨γ, hγ⟩ := hρ (QuotientGroup.mk b)
  have hlamγ := congrFun hlam γ
  have hval := congrArg (fun ψ : MuDual 2 (Additive ↥D.T) =>
    (ψ : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t)) hlamγ
  -- LHS of `hval`: the coboundary value
  have hL : ((dZero AbsGalQ2 (MuDual 2 (Additive ↥D.T)) lam)
        γ : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t)
      = (lam : Additive ↥D.T →+ MuN 2) (Additive.ofMul t)
        - (lam : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t) := by
    show ((γ • lam - lam : MuDual 2 (Additive ↥D.T))
        : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t) = _
    rw [show ((γ • lam - lam : MuDual 2 (Additive ↥D.T))
        : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t)
      = γ • (lam : Additive ↥D.T →+ MuN 2)
          ((γ⁻¹ : AbsGalQ2) • (γ : AbsGalQ2) • Additive.ofMul t)
        - (lam : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t) from rfl,
      smul_muN_two_trivial, inv_smul_smul]
  -- RHS of `hval`: the shifted edge at the shifted point
  have hR : (shiftedEdge D ρ S γ : Additive ↥D.T →+ MuN 2)
        ((γ : AbsGalQ2) • Additive.ofMul t)
      = muNTwoEquiv.symm (edgeQ D S (ρ γ) t) := by
    rw [shiftedEdge_apply]
    congr 2
    rw [show Additive.toMul ((γ : AbsGalQ2) • Additive.ofMul t) = rhoConj D ρ γ t from rfl]
    exact rhoConj_inv_rhoConj D ρ γ t
  rw [hL, hR] at hval
  -- convert to the `𝔽₂`-shadow
  have h2 := congrArg muNTwoEquiv hval
  rw [map_sub, AddEquiv.apply_symm_apply] at h2
  have hedgeval : edge D S b t = ℓ t - ℓ (rhoConj D ρ γ t) := by
    rw [← edgeQ_eq D S (ρ γ) hγ.symm t, ← h2]
    rfl
  have hconj : (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T) = rhoConj D ρ γ t :=
    Subtype.ext (rhoConj_coe D ρ γ b hγ.symm t).symm
  rw [hedgeval, hconj]
  exact (by decide : ∀ a e : ZMod 2, a - e = e + a) _ _

/-- **The B6 step**: perfectness of the `(1,1)` pairing plus `[φ] ≠ 0` produce a class
pairing nontrivially with the shifted edge. -/
private theorem exists_pairing_partner (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (hedge : D.NoDescent) (hρ : Function.Surjective ρ) :
    letI := conjModule D ρ
    haveI := conjModule_continuousSMul D ρ
    ∃ ξ : H1 AbsGalQ2 (Additive ↥D.T),
      (GQ2.tateDuality 2).inv
        (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
          (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T))
            ⟨shiftedEdge D ρ S, shiftedEdge_mem_Z1 D ρ S⟩) ξ) ≠ 0 := by
  letI := conjModule D ρ
  haveI := conjModule_continuousSMul D ρ
  have hperf := (GQ2.tateDuality 2).perfect11 (Additive ↥D.T) (two_nsmul_additiveT_eq_zero D)
  by_contra hall
  rw [not_exists] at hall
  apply shiftedEdge_class_ne_zero D ρ S hedge hρ
  apply hperf.injective
  show (GQ2.tateDuality 2).inv.toAddMonoidHom.comp
      (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
        (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T))
          ⟨shiftedEdge D ρ S, shiftedEdge_mem_Z1 D ρ S⟩))
    = (GQ2.tateDuality 2).inv.toAddMonoidHom.comp
      (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
        0)
  refine AddMonoidHom.ext fun ξ' => ?_
  have h1 := not_not.mp (hall ξ')
  show (GQ2.tateDuality 2).inv
      (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
        (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T))
          ⟨shiftedEdge D ρ S, shiftedEdge_mem_Z1 D ρ S⟩) ξ')
    = (GQ2.tateDuality 2).inv
      (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
        0 ξ')
  rw [map_zero]
  rw [show ((0 : H1 AbsGalQ2 (Additive ↥D.T) →+ H2 AbsGalQ2 (MuN 2))) ξ' = 0 from rfl,
    map_zero]
  exact h1

/-- The crossed `T`-cocycle packaging a `rhoConj`-crossed additive cocycle `w`. -/
private noncomputable def twistCocycle (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (w : AbsGalQ2 → Additive ↥D.T) (hcont : Continuous w)
    (hcross : ∀ γ δ : AbsGalQ2,
      w (γ * δ) = w γ + Additive.ofMul (rhoConj D ρ γ (Additive.toMul (w δ)))) :
    TCocycle D ρ where
  u γ := ((Additive.toMul (w γ) : ↥D.T) : Bg)
  mem γ := (Additive.toMul (w γ)).2
  cont := continuous_subtype_val.comp hcont
  crossed := by
    intro γ δ b hb
    have hval := congrArg (fun x : Additive ↥D.T => ((Additive.toMul x : ↥D.T) : Bg))
      (hcross γ δ)
    rw [hval]
    show ((Additive.toMul (w γ) * rhoConj D ρ γ (Additive.toMul (w δ)) : ↥D.T) : Bg) = _
    rw [show ((Additive.toMul (w γ) * rhoConj D ρ γ (Additive.toMul (w δ)) : ↥D.T) : Bg)
        = ((Additive.toMul (w γ) : ↥D.T) : Bg)
          * ((rhoConj D ρ γ (Additive.toMul (w δ)) : ↥D.T) : Bg) from rfl,
      rhoConj_coe D ρ γ b hb]

/-- **The exact bridge**: the cup-product cochain of the shifted edge against `w` is the
`μ₂`-shadow of the variation cochain of the packaged twist. -/
private theorem cup11Fun_shiftedEdge_eq_varCoc (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (S : TComplement D) (w : AbsGalQ2 → Additive ↥D.T) (hcont : Continuous w)
    (hcross : ∀ γ δ : AbsGalQ2,
      w (γ * δ) = w γ + Additive.ofMul (rhoConj D ρ γ (Additive.toMul (w δ)))) :
    letI := conjModule D ρ
    ∀ gd : AbsGalQ2 × AbsGalQ2,
      cup11Fun (muDualPairing 2 (Additive ↥D.T)) (shiftedEdge D ρ S) w gd
        = muNTwoEquiv.symm (varCoc D ρ S (twistCocycle D ρ w hcont hcross) gd) := by
  letI := conjModule D ρ
  intro gd
  obtain ⟨γ, δ⟩ := gd
  show muDualPairing 2 (Additive ↥D.T) (shiftedEdge D ρ S γ) ((γ : AbsGalQ2) • w δ)
    = muNTwoEquiv.symm (varCoc D ρ S (twistCocycle D ρ w hcont hcross) (γ, δ))
  rw [muDualPairing_apply, shiftedEdge_apply]
  refine congrArg muNTwoEquiv.symm (congrArg (edgeQ D S (ρ γ)) ?_)
  rw [show Additive.toMul ((γ : AbsGalQ2) • w δ)
      = rhoConj D ρ γ (Additive.toMul (w δ)) from rfl,
    rhoConj_inv_rhoConj D ρ γ (Additive.toMul (w δ))]
  rfl

/-- **The B6 twist construction** (Lemma 8.6, local source, duality step): from `NoDescent`,
a crossed `T`-cocycle whose variation cochain is not a (trivial-action) coboundary.  The
statement is action-free (raw cochain level) so the consumer can bridge it to the
`H²(Γ,𝔽₂)`-class with its own coefficient instances; the *proof* runs B6's perfect `(1,1)`
pairing on the `ρ`-conjugation module — deliberately in a **minimal context** (no
compactness, no finiteness), keeping the `μ₂`-dual instance searches tame. -/
private theorem exists_good_twist (S : TComplement D)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    ∃ u : TCocycle D ρ,
      ¬ ∃ c : AbsGalQ2 → ZMod 2, Continuous c ∧
        ∀ γ δ : AbsGalQ2, varCoc D ρ S u (γ, δ) = c δ - c (γ * δ) + c γ := by
  classical
  letI := conjModule D ρ
  haveI := conjModule_continuousSMul D ρ
  -- resolve the `μ₂`-dual instance bundle once, early (large-context synthesis shortcut)
  letI : DistribMulAction AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := inferInstance
  haveI : ContinuousSMul AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := inferInstance
  -- ===== B6: perfectness pairs the shifted edge nontrivially with some class `[w]` =====
  obtain ⟨ξ, hξ⟩ := exists_pairing_partner D ρ S hedge hρ
  obtain ⟨w, rfl⟩ := H1mk_surjective (G := AbsGalQ2) (M := Additive ↥D.T) ξ
  rw [cup11_mk_mk] at hξ
  have hwZ := mem_Z1_iff.mp w.2
  -- ===== the crossed `T`-cocycle from `w`; a trivializing cochain would kill the cup class
  refine ⟨twistCocycle D ρ w.1 hwZ.1 hwZ.2, ?_⟩
  rintro ⟨c, hcC1, hceq⟩
  have hcupB2 : cup11Fun (muDualPairing 2 (Additive ↥D.T)) (shiftedEdge D ρ S) w.1
      ∈ B2 AbsGalQ2 (MuN 2) := by
    refine AddSubgroup.mem_map.mpr
      ⟨fun γ => muNTwoEquiv.symm (c γ), ?_, ?_⟩
    · exact (continuous_of_discreteTopology
        (f := fun a : ZMod 2 => muNTwoEquiv.symm a)).comp hcC1
    · funext gd
      obtain ⟨γ, δ⟩ := gd
      show γ • muNTwoEquiv.symm (c δ) - muNTwoEquiv.symm (c (γ * δ))
          + muNTwoEquiv.symm (c γ) = _
      rw [smul_muN_two_trivial, ← map_sub, ← map_add,
        cup11Fun_shiftedEdge_eq_varCoc D ρ S w.1 hwZ.1 hwZ.2 (γ, δ)]
      congr 1
      exact (hceq γ δ).symm
  have hcup0 : H2mk AbsGalQ2 (MuN 2)
      ⟨cup11Fun (muDualPairing 2 (Additive ↥D.T)) (shiftedEdge D ρ S) w.1,
        cup11_mem_Z2 (muDualPairing 2 (Additive ↥D.T))
          (muDualPairing_equivariant 2 (Additive ↥D.T))
          ⟨shiftedEdge D ρ S, shiftedEdge_mem_Z1 D ρ S⟩ w⟩ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hcupB2)
  rw [hcup0, map_zero] at hξ
  exact hξ rfl

end GoodTwist

/-- **Lemma 8.6, local source, engine form** — the half-torsor count for `G_ℚ₂` from
`NoDescent`, via B6.  Consumed by `SectionEight.lemma_8_6_local`. -/
theorem half_torsor_local
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (hfg : ∃ s : Finset AbsGalQ2,
      (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤)
    (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M))
    (hρ : Function.Surjective ρ) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  classical
  -- finiteness of the lift set (B1-shaped input `hfg`)
  haveI : Finite (ContinuousMonoidHom AbsGalQ2 Bg) := finite_continuousMonoidHom hfg Bg
  haveI : Finite (MLifts D ρ) := by
    unfold MLifts
    exact Subtype.finite
  -- the complement and the B6 twist
  obtain ⟨S⟩ := tComplement_nonempty D
  obtain ⟨u, hraw⟩ := exists_good_twist D S hedge ρ hρ
  -- the trivial 𝔽₂-action
  letI actZ : DistribMulAction AbsGalQ2 (ZMod 2) :=
    { smul := fun _ m => m
      one_smul := fun _ => rfl
      mul_smul := fun _ _ _ => rfl
      smul_zero := fun _ => rfl
      smul_add := fun _ _ _ => rfl }
  haveI : ContinuousSMul AbsGalQ2 (ZMod 2) := ⟨continuous_snd⟩
  have htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m := fun _ _ => rfl
  have hcard : Nat.card (H2 AbsGalQ2 (ZMod 2)) = 2 := card_H2_zmod2_eq_two htriv
  -- the variation class is nonzero (bridge the raw form)
  have hvar : H2mk AbsGalQ2 (ZMod 2)
      ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ ≠ 0 := by
    intro h0
    have hmem : varCoc D ρ S u ∈ B2 AbsGalQ2 (ZMod 2) :=
      AddSubgroup.mem_addSubgroupOf.mp ((QuotientAddGroup.eq_zero_iff _).mp h0)
    obtain ⟨c, hcC1, hceq⟩ := AddSubgroup.mem_map.mp hmem
    refine hraw ⟨c, hcC1, fun γ δ => ?_⟩
    have hpt := congrFun hceq (γ, δ)
    rw [← hpt]
    show γ • c δ - c (γ * δ) + c γ = c δ - c (γ * δ) + c γ
    rw [htriv]
  exact half_count D ρ S htriv u hvar hcard

end RadicalEdgeLocal

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 8.6 = ⟦lem-radicaledge⟧
-/
