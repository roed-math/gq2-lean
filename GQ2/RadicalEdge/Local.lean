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
  set act : AbsGalQ2 → ↥D.T → ↥D.T := fun γ t =>
    ⟨Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹,
      conj_mem_T D (Quotient.out (ρ γ)) t⟩ with hactdef
  have hact_eq : ∀ (γ : AbsGalQ2) (b : Bg), QuotientGroup.mk b = ρ γ →
      ∀ t : ↥D.T, (act γ t).1 = b * t.1 * b⁻¹ := by
    intro γ b hb t
    show Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹ = b * t.1 * b⁻¹
    exact conj_eq_of_mk_eq D (by rw [QuotientGroup.out_eq' (ρ γ), hb]) t
  have hact_one : ∀ t : ↥D.T, act 1 t = t := by
    intro t
    apply Subtype.ext
    rw [hact_eq 1 1 (by rw [QuotientGroup.mk_one, map_one]) t]
    group
  have hact_mul : ∀ (γ δ : AbsGalQ2) (t : ↥D.T), act (γ * δ) t = act γ (act δ t) := by
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
  have hact_mul' : ∀ (γ : AbsGalQ2) (t t' : ↥D.T),
      act γ (t * t') = act γ t * act γ t' := by
    intro γ t t'
    apply Subtype.ext
    show Quotient.out (ρ γ) * (t.1 * t'.1) * (Quotient.out (ρ γ))⁻¹
      = (Quotient.out (ρ γ) * t.1 * (Quotient.out (ρ γ))⁻¹)
        * (Quotient.out (ρ γ) * t'.1 * (Quotient.out (ρ γ))⁻¹)
    group
  have hact_one_elt : ∀ γ : AbsGalQ2, act γ 1 = 1 := by
    intro γ
    apply Subtype.ext
    show Quotient.out (ρ γ) * (1 : Bg) * (Quotient.out (ρ γ))⁻¹ = 1
    group
  have hact_inv : ∀ (γ : AbsGalQ2) (t : ↥D.T), act γ⁻¹ (act γ t) = t := by
    intro γ t
    rw [← hact_mul, inv_mul_cancel, hact_one]
  letI actT : DistribMulAction AbsGalQ2 (Additive ↥D.T) :=
    { smul := fun γ t => Additive.ofMul (act γ (Additive.toMul t))
      one_smul := fun t => hact_one _
      mul_smul := fun γ δ t => hact_mul γ δ _
      smul_zero := fun γ => hact_one_elt γ
      smul_add := fun γ t t' => hact_mul' γ _ _ }
  have hsmulT : ∀ (γ : AbsGalQ2) (t : Additive ↥D.T),
      γ • t = Additive.ofMul (act γ (Additive.toMul t)) := fun _ _ => rfl
  haveI : ContinuousSMul AbsGalQ2 (Additive ↥D.T) := by
    constructor
    have hfac : (fun p : AbsGalQ2 × Additive ↥D.T => p.1 • p.2)
        = (fun cq : (Bg ⧸ D.M) × ↥D.T =>
            Additive.ofMul (⟨Quotient.out cq.1 * cq.2.1 * (Quotient.out cq.1)⁻¹,
              conj_mem_T D (Quotient.out cq.1) cq.2⟩ : ↥D.T))
          ∘ (fun p : AbsGalQ2 × Additive ↥D.T =>
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
  -- resolve the `μ₂`-dual instance bundle once, early (large-context synthesis shortcut)
  letI : DistribMulAction AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := inferInstance
  haveI : ContinuousSMul AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := inferInstance
  -- ===== the shifted-edge dual 1-cocycle `φ` =====
  have hφadd : ∀ (γ : AbsGalQ2) (s s' : Additive ↥D.T),
      edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul (s + s')))
        = edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s))
          + edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s')) := by
    intro γ s s'
    have hmulcast : Additive.toMul (s + s')
        = Additive.toMul s * Additive.toMul s' := rfl
    rw [hmulcast, hact_mul' γ⁻¹]
    exact edge_add D S (Quotient.out (ρ γ)) _ _
  set φf : AbsGalQ2 → MuDual 2 (Additive ↥D.T) := fun γ =>
    (muNTwoEquiv.symm.toAddMonoidHom.comp
      (AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s))) (hφadd γ))
      : Additive ↥D.T →+ MuN 2) with hφfdef
  have hφapp : ∀ (γ : AbsGalQ2) (s : Additive ↥D.T),
      (φf γ : Additive ↥D.T →+ MuN 2) s
        = muNTwoEquiv.symm (edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s))) :=
    fun _ _ => rfl
  -- the ZMod₂-level crossed law of the shifted edge
  have hcrossZ : ∀ (γ δ : AbsGalQ2) (s : Additive ↥D.T),
      edgeQ D S (ρ (γ * δ)) (act (γ * δ)⁻¹ (Additive.toMul s))
        = edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s))
          + edgeQ D S (ρ δ) (act δ⁻¹ (Additive.toMul ((γ⁻¹ : AbsGalQ2) • s))) := by
    intro γ δ s
    have hγ : (QuotientGroup.mk (Quotient.out (ρ γ)) : Bg ⧸ D.M) = ρ γ :=
      QuotientGroup.out_eq' _
    have hδ : (QuotientGroup.mk (Quotient.out (ρ δ)) : Bg ⧸ D.M) = ρ δ :=
      QuotientGroup.out_eq' _
    have hγδrep : (QuotientGroup.mk (Quotient.out (ρ γ) * Quotient.out (ρ δ)) : Bg ⧸ D.M)
        = ρ (γ * δ) := by
      rw [QuotientGroup.mk_mul, hγ, hδ, map_mul]
    rw [edgeQ_eq D S (ρ (γ * δ)) hγδrep, edge_mul]
    have h2 : edge D S (Quotient.out (ρ γ))
          ⟨Quotient.out (ρ δ) * (act (γ * δ)⁻¹ (Additive.toMul s)).1
            * (Quotient.out (ρ δ))⁻¹,
            conj_mem_T D (Quotient.out (ρ δ)) (act (γ * δ)⁻¹ (Additive.toMul s))⟩
        = edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s)) := by
      rw [edgeQ_eq D S (ρ γ) hγ]
      congr 1
      apply Subtype.ext
      show Quotient.out (ρ δ) * (act (γ * δ)⁻¹ (Additive.toMul s)).1
          * (Quotient.out (ρ δ))⁻¹ = (act γ⁻¹ (Additive.toMul s)).1
      have hsplit : act (γ * δ)⁻¹ (Additive.toMul s)
          = act δ⁻¹ (act γ⁻¹ (Additive.toMul s)) := by
        rw [show ((γ * δ)⁻¹ : AbsGalQ2) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ,
          hact_mul δ⁻¹ γ⁻¹]
      rw [hsplit]
      have hδinv : (QuotientGroup.mk ((Quotient.out (ρ δ))⁻¹) : Bg ⧸ D.M) = ρ δ⁻¹ := by
        rw [QuotientGroup.mk_inv, hδ, map_inv]
      rw [hact_eq δ⁻¹ ((Quotient.out (ρ δ))⁻¹) hδinv]
      group
    have h1 : edge D S (Quotient.out (ρ δ)) (act (γ * δ)⁻¹ (Additive.toMul s))
        = edgeQ D S (ρ δ) (act δ⁻¹ (Additive.toMul ((γ⁻¹ : AbsGalQ2) • s))) := by
      rw [edgeQ_eq D S (ρ δ) hδ]
      congr 1
      rw [show Additive.toMul ((γ⁻¹ : AbsGalQ2) • s) = act γ⁻¹ (Additive.toMul s) from rfl]
      rw [show ((γ * δ)⁻¹ : AbsGalQ2) = δ⁻¹ * γ⁻¹ from mul_inv_rev γ δ, hact_mul δ⁻¹ γ⁻¹]
    rw [h1, h2]
  have hφZ1 : φf ∈ Z1 AbsGalQ2 (MuDual 2 (Additive ↥D.T)) := by
    rw [mem_Z1_iff]
    constructor
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
            = (⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1 * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩ : ↥D.T)
              * ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1 * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s')⟩ := by
          apply Subtype.ext
          show Quotient.out (c⁻¹ : Bg ⧸ D.M)
              * ((Additive.toMul s).1 * (Additive.toMul s').1)
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹
            = (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1 * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
              * (Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s').1 * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹)
          group
        rw [hsplit]
        exact edge_add D S (Quotient.out c) _ _
      have hfac : φf = (fun c : Bg ⧸ D.M =>
          (muNTwoEquiv.symm.toAddMonoidHom.comp
            (AddMonoidHom.mk' (fun s : Additive ↥D.T =>
              edgeQ D S c ⟨Quotient.out (c⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1 * (Quotient.out (c⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out (c⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩) (hΦadd c))
            : Additive ↥D.T →+ MuN 2)) ∘ (fun γ : AbsGalQ2 => (ρ γ : Bg ⧸ D.M)) := by
        funext γ
        refine DFunLike.ext _ _ fun s => ?_
        rw [hφapp]
        show muNTwoEquiv.symm (edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s)))
          = muNTwoEquiv.symm (edgeQ D S (ρ γ)
              ⟨Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1 * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹,
                conj_mem_T D (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M)) (Additive.toMul s)⟩)
        refine congrArg muNTwoEquiv.symm (congrArg (edgeQ D S (ρ γ)) (Subtype.ext ?_))
        have hrep : Quotient.out (ρ γ⁻¹) = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) := by
          rw [map_inv]
        show Quotient.out (ρ γ⁻¹) * (Additive.toMul s).1 * (Quotient.out (ρ γ⁻¹))⁻¹
          = Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M) * (Additive.toMul s).1
            * (Quotient.out ((ρ γ)⁻¹ : Bg ⧸ D.M))⁻¹
        rw [hrep]
      rw [hfac]
      exact continuous_of_discreteTopology.comp ρ.continuous_toFun
    · intro γ δ
      refine DFunLike.ext _ _ fun s => ?_
      have hz := hcrossZ γ δ s
      show (φf (γ * δ) : Additive ↥D.T →+ MuN 2) s
        = ((φf γ + γ • φf δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s
      have hsmul : ((γ • φf δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s
          = (φf δ : Additive ↥D.T →+ MuN 2) ((γ⁻¹ : AbsGalQ2) • s) := by
        rw [show ((γ • φf δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s
            = γ • (φf δ : Additive ↥D.T →+ MuN 2) ((γ⁻¹ : AbsGalQ2) • s) from rfl,
          smul_muN_two_trivial]
      rw [show ((φf γ + γ • φf δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s
          = (φf γ : Additive ↥D.T →+ MuN 2) s
            + ((γ • φf δ : MuDual 2 (Additive ↥D.T)) : Additive ↥D.T →+ MuN 2) s from rfl,
        hsmul, hφapp, hφapp, hφapp, hz, map_add]
  -- ===== `[φ] ≠ 0` (else the edge trivializes and the cover descends) =====
  have hφne : H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T)) ⟨φf, hφZ1⟩ ≠ 0 := by
    intro h0
    have hmem : φf ∈ B1 AbsGalQ2 (MuDual 2 (Additive ↥D.T)) :=
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
    have hR : (φf γ : Additive ↥D.T →+ MuN 2) ((γ : AbsGalQ2) • Additive.ofMul t)
        = muNTwoEquiv.symm (edgeQ D S (ρ γ) t) := by
      rw [hφapp]
      congr 2
      rw [show Additive.toMul ((γ : AbsGalQ2) • Additive.ofMul t) = act γ t from rfl]
      exact hact_inv γ t
    rw [hL, hR] at hval
    -- convert to the `𝔽₂`-shadow
    have h2 := congrArg muNTwoEquiv hval
    rw [map_sub, AddEquiv.apply_symm_apply] at h2
    have hedgeval : edge D S b t = ℓ t - ℓ (act γ t) := by
      rw [← edgeQ_eq D S (ρ γ) hγ.symm t, ← h2]
      rfl
    have hconj : (⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ : ↥D.T) = act γ t :=
      Subtype.ext (hact_eq γ b hγ.symm t).symm
    rw [hedgeval, hconj]
    exact (by decide : ∀ a e : ZMod 2, a - e = e + a) _ _
  -- ===== B6: perfectness produces the nonzero pairing partner =====
  have hperf := (GQ2.tateDuality 2).perfect11 (Additive ↥D.T) htorT
  obtain ⟨ξ, hξ⟩ : ∃ ξ : H1 AbsGalQ2 (Additive ↥D.T),
      (GQ2.tateDuality 2).inv
        (cup11 (muDualPairing 2 (Additive ↥D.T))
          (muDualPairing_equivariant 2 (Additive ↥D.T))
          (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T)) ⟨φf, hφZ1⟩) ξ) ≠ 0 := by
    by_contra hall
    rw [not_exists] at hall
    apply hφne
    apply hperf.injective
    show (GQ2.tateDuality 2).inv.toAddMonoidHom.comp
        (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
          (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T)) ⟨φf, hφZ1⟩))
      = (GQ2.tateDuality 2).inv.toAddMonoidHom.comp
        (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
          0)
    refine AddMonoidHom.ext fun ξ' => ?_
    have h1 := not_not.mp (hall ξ')
    show (GQ2.tateDuality 2).inv
        (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
          (H1mk AbsGalQ2 (MuDual 2 (Additive ↥D.T)) ⟨φf, hφZ1⟩) ξ')
      = (GQ2.tateDuality 2).inv
        (cup11 (muDualPairing 2 (Additive ↥D.T)) (muDualPairing_equivariant 2 (Additive ↥D.T))
          0 ξ')
    rw [map_zero]
    rw [show ((0 : H1 AbsGalQ2 (Additive ↥D.T) →+ H2 AbsGalQ2 (MuN 2))) ξ' = 0 from rfl,
      map_zero]
    exact h1
  obtain ⟨w, rfl⟩ := H1mk_surjective (G := AbsGalQ2) (M := Additive ↥D.T) ξ
  rw [cup11_mk_mk] at hξ
  -- ===== the crossed `T`-cocycle from `w` =====
  have hwZ := mem_Z1_iff.mp w.2
  set u : TCocycle D ρ :=
    { u := fun γ => ((Additive.toMul (w.1 γ) : ↥D.T) : Bg)
      mem := fun γ => (Additive.toMul (w.1 γ)).2
      cont := continuous_subtype_val.comp hwZ.1
      crossed := by
        intro γ δ b hb
        have hw := hwZ.2 γ δ
        have hval := congrArg (fun x : Additive ↥D.T => ((Additive.toMul x : ↥D.T) : Bg)) hw
        rw [hval]
        show ((Additive.toMul (w.1 γ) * act γ (Additive.toMul (w.1 δ)) : ↥D.T) : Bg) = _
        rw [show ((Additive.toMul (w.1 γ) * act γ (Additive.toMul (w.1 δ)) : ↥D.T) : Bg)
            = ((Additive.toMul (w.1 γ) : ↥D.T) : Bg)
              * ((act γ (Additive.toMul (w.1 δ)) : ↥D.T) : Bg) from rfl,
          hact_eq γ b hb] } with hudef
  -- ===== the exact bridge: `varCoc u = μ₂-shadow of the cup cocycle` =====
  have hbridge : ∀ gd : AbsGalQ2 × AbsGalQ2,
      cup11Fun (muDualPairing 2 (Additive ↥D.T)) φf w.1 gd
        = muNTwoEquiv.symm (varCoc D ρ S u gd) := by
    intro gd
    obtain ⟨γ, δ⟩ := gd
    show muDualPairing 2 (Additive ↥D.T) (φf γ) ((γ : AbsGalQ2) • w.1 δ)
      = muNTwoEquiv.symm (varCoc D ρ S u (γ, δ))
    rw [muDualPairing_apply, hφapp]
    refine congrArg muNTwoEquiv.symm (congrArg (edgeQ D S (ρ γ)) ?_)
    rw [show Additive.toMul ((γ : AbsGalQ2) • w.1 δ)
        = act γ (Additive.toMul (w.1 δ)) from rfl, hact_inv]
  -- ===== the raw nonvanishing: a trivializing cochain would kill the cup class =====
  refine ⟨u, ?_⟩
  rintro ⟨c, hcC1, hceq⟩
  have hcupB2 : cup11Fun (muDualPairing 2 (Additive ↥D.T)) φf w.1
      ∈ B2 AbsGalQ2 (MuN 2) := by
    refine AddSubgroup.mem_map.mpr
      ⟨fun γ => muNTwoEquiv.symm (c γ), ?_, ?_⟩
    · exact (continuous_of_discreteTopology
        (f := fun a : ZMod 2 => muNTwoEquiv.symm a)).comp hcC1
    · funext gd
      obtain ⟨γ, δ⟩ := gd
      show γ • muNTwoEquiv.symm (c δ) - muNTwoEquiv.symm (c (γ * δ))
          + muNTwoEquiv.symm (c γ) = _
      rw [smul_muN_two_trivial, ← map_sub, ← map_add, hbridge (γ, δ)]
      congr 1
      exact (hceq γ δ).symm
  have hcup0 : H2mk AbsGalQ2 (MuN 2)
      ⟨cup11Fun (muDualPairing 2 (Additive ↥D.T)) φf w.1,
        cup11_mem_Z2 (muDualPairing 2 (Additive ↥D.T))
          (muDualPairing_equivariant 2 (Additive ↥D.T)) ⟨φf, hφZ1⟩ w⟩ = 0 :=
    (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hcupB2)
  rw [hcup0, map_zero] at hξ
  exact hξ rfl

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
