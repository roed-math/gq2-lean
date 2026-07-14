import GQ2.Shapiro.Deepness
import GQ2.RegularIsometry
import GQ2.OrbitDecomp
import GQ2.DimAssembly
import GQ2.Shapiro.Read
import GQ2.InvolutionSplice
import GQ2.AdmissibleCount

/-!
# P-15f2d: final assembly of `lemma_6_17_vanish` — wiring bricks

The capstone composing f2a (datum-independence) + Lemma 6.14 (`RepIndependence.lemma_6_14`) + f2b
(the orbit decomposition `regular_isometric_embedding_orbit`) + f2c (`hcoh`/`hvanish`) through
`OrbitVanish.Q0loc_vanish_of_datum_decomp`, then the SectionSix statement-move.

This file begins with the **mechanical wiring bricks** — independent of the open f2a/f2c1/f2c2
mathematics, buildable now.  f2b's orbit datum lives over `G ⧸ N` while the ambient `Q0loc` /
Lemma-6.14 transport is over `C`; the assembly reindexes the datum along `e : C ≃* G ⧸ N` (the
`FactorSet.reindexHom`/`Q0loc_reindexHom` bridge landed in `ShapiroDeepness`).  These two bricks
say `reindexHom` distributes over `sumDatum` and preserves equivariance under the `φ`-pullback
action — the two facts needed to feed the reindexed orbit sum into the reducer.
-/

namespace GQ2

namespace VanishClose

open OrbitVanish (sumDatum)

variable {C C' V : Type*} [Group C] [Group C'] [AddCommGroup V]
  [DistribMulAction C V] [DistribMulAction C' V]

omit [Group C] [Group C'] [AddCommGroup V] [DistribMulAction C V] [DistribMulAction C' V] in
/-- **`reindexHom` distributes over `sumDatum`** (P-15f2d wiring): reindexing a datum sum's acting
group along `φ` is the sum of the reindexed per-orbit data.  Both sides have the same factor set
(`f` is untouched by `reindexHom`) and the same corrections (`m` pre-composes `φ` inside each
summand), so this is definitional. -/
theorem reindexHom_sumDatum {ι : Type*} (s : Finset ι) (datf : ι → FactorSet C V) (φ : C' → C) :
    (sumDatum s datf).reindexHom φ = sumDatum s (fun o => (datf o).reindexHom φ) := rfl

/-- **Equivariance is preserved under `reindexHom`** (P-15f2d wiring): if `dat` is an equivariant
factor set for `q` over `C`, `φ : C' →* C` is a group hom, and the `C'`-action on `V` is the
`φ`-pullback of the `C`-action (`hφ`), then `dat.reindexHom φ` is an equivariant factor set for `q`
over `C'`.  The factor-set clauses are inherited verbatim (`f` unchanged); the correction clauses
(59)/(60) transport by `φ`'s multiplicativity and the `hφ` action identity. -/
theorem isEquivariantFactorSet_reindexHom {q : V → ZMod 2} {dat : FactorSet C V}
    (h : IsEquivariantFactorSet q dat) (φ : C' →* C)
    (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v) :
    IsEquivariantFactorSet q (dat.reindexHom φ) where
  f_cocycle := h.f_cocycle
  f_diag := h.f_diag
  f_polar := h.f_polar
  f_zero_left := h.f_zero_left
  f_zero_right := h.f_zero_right
  m_quad c' v w := by
    rw [hφ c' v, hφ c' w]
    exact h.m_quad (φ c') v w
  m_mul c' d' v := by
    show dat.m (φ (c' * d')) v = dat.m (φ c') (d' • v) + dat.m (φ d') v
    rw [map_mul, hφ d' v]; exact h.m_mul (φ c') (φ d') v
  m_one v := by
    show dat.m (φ 1) v = 0
    rw [map_one]; exact h.m_one v

/-! ## The classifying equivalence `e : C ≃* AbsGalQ2 ⧸ ker ρ` -/

section ETower

variable {C : Type} [Group C] [TopologicalSpace C]

/-- **The classifying equivalence** `e : C ≃* AbsGalQ2 ⧸ ker ρ` (P-15f2d): for a surjective `ρ`,
the inverse of the first-isomorphism `AbsGalQ2 ⧸ ker ρ ≃* C`.  It is what f2b's
`regular_isometric_embedding_orbit` consumes to give the regular module `W = Fin K → RegRep (ker ρ)`
its `C`-view (the `e`-pullback of the canonical `G ⧸ N`-action). -/
noncomputable def eOfSurj (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ρ) :
    C ≃* AbsGalQ2 ⧸ (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm

/-- **`e ∘ ρ = mk'`** (P-15f2d): the classifying equivalence sends `ρ g` back to its coset, so
`e` composed with `ρ` is the quotient map.  This is the identity that turns the `C`-level reindexed
pullback into the `mk' N`-level orbit map (where `lemma_6_15_*` are stated) and supplies the
`Q0loc`/reducer compatibility `hρW : g • w = ρ g • w` on `W`. -/
theorem eOfSurj_rho (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρsurj : Function.Surjective ρ)
    (g : AbsGalQ2) :
    eOfSurj ρ hρsurj (ρ g) = QuotientGroup.mk g :=
  (QuotientGroup.quotientKerEquivOfSurjective ρ.toMonoidHom hρsurj).symm_apply_eq.mpr
    (QuotientGroup.kerLift_mk _ g).symm

end ETower

/-! ## The final assembly of `lemma_6_17_vanish`

Compose f2a (datum-independence) + Lemma 6.14 + f2b (regular embedding) + f2c1 (`hcoh_*`) +
the deep-class vanishing (`hvanish_cup` square/free, `InvolutionSplice.hvanish_involution_ker`
involution) through `OrbitVanish.Q0loc_vanish_of_datum_decomp`.  The `W = Fin K → RegRep (ker ρ)`
instances are `letI`-supplied on the **base** `RegRep (ker ρ)` (so f2c1's `RegRep`-instance
arguments resolve and the block module's action is the `Pi`-lift); `RegRep`'s opacity blocks the
global trivial `AbsGalQ2`-action, so this is clean. -/

section Assembly

open ContCoh QuadraticFp2 SectionSix DimAssembly ShapiroRead LocalKummer

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **Out-lift of an order-2 nontrivial coset is a non-`N` involution mod `N`** (P-15f2d wiring):
for `w : AbsGalQ2 ⧸ N` with `w * w = 1` and `w ≠ 1`, the section lift `Quotient.out w` lies outside
`N` yet squares into `N`.  The involution-position fact shared by the three `Sum.inr (Sum.inl _)`
orbit branches of the final assembly. -/
theorem out_notMem_and_out_sq_mem (N : Subgroup AbsGalQ2) [N.Normal] {w : AbsGalQ2 ⧸ N}
    (hw2 : w * w = 1) (hwne : w ≠ 1) :
    Quotient.out w ∉ N ∧ Quotient.out w * Quotient.out w ∈ N := by
  have hw : QuotientGroup.mk' N (Quotient.out w) = w := by
    rw [QuotientGroup.mk'_apply]; exact QuotientGroup.out_eq' w
  refine ⟨fun h => hwne ?_, ?_⟩
  · have h1 : QuotientGroup.mk' N (Quotient.out w) = 1 := by
      rw [QuotientGroup.mk'_apply]; exact (QuotientGroup.eq_one_iff _).mpr h
    rwa [hw] at h1
  · have h1 : QuotientGroup.mk' N (Quotient.out w * Quotient.out w) = 1 := by
      rw [map_mul, hw]; exact hw2
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1

/-- **The involution orbit's inner cochain is a 2-cocycle** (P-15f2d wiring): the `evensNormFun`
splice attached to an involution coset `g ∉ N`, `g² ∈ N` on the index-2 pair `N ≤ N ⊔ ⟨g⟩`, built
from a block cocycle `shapiroCoord N β`, is a `Z²`.  Discharges the `Sum.inr (Sum.inl _)` branch of
the `hZ2` obligation. -/
theorem evensNormFun_orbit_mem_Z2 (N : Subgroup AbsGalQ2) [N.Normal]
    (hNopen : IsOpen (N : Set AbsGalQ2)) (g : AbsGalQ2) (hgN : g ∉ N) (hg2 : g * g ∈ N)
    (β : AbsGalQ2 → RegRep N) (hZ1 : shapiroCoord N β ∈ Z1 ↥N (ZMod 2)) :
    evensNormFun (N.subgroupOf (N ⊔ Subgroup.zpowers g))
        ⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g)⟩
        (fun w => shapiroCoord N β ⟨w.1.1, w.2⟩)
      ∈ Z2 ↥(N ⊔ Subgroup.zpowers g) (ZMod 2) := by
  have hsU : (⟨g, Subgroup.mem_sup_right (Subgroup.mem_zpowers g)⟩ : ↥(N ⊔ Subgroup.zpowers g))
      ∉ N.subgroupOf (N ⊔ Subgroup.zpowers g) :=
    fun h => hgN (Subgroup.mem_subgroupOf.mp h)
  have hUi : (N.subgroupOf (N ⊔ Subgroup.zpowers g)).index = 2 :=
    InvolutionSplice.index_eq_two_of_decomp hsU (fun bb hbb => by
      rcases InvolutionSplice.mem_or_mul_mem_of_mem_sup hg2 bb.2 with hbN | hbg
      · exact absurd (Subgroup.mem_subgroupOf.mpr hbN) hbb
      · exact Subgroup.mem_subgroupOf.mpr hbg)
  have hUo : IsOpen (((N.subgroupOf (N ⊔ Subgroup.zpowers g))
      : Subgroup ↥(N ⊔ Subgroup.zpowers g)) : Set ↥(N ⊔ Subgroup.zpowers g)) :=
    hNopen.preimage continuous_subtype_val
  obtain ⟨hjc, hjhom⟩ := (mem_Z1_iff_of_trivial (fun _ _ => rfl)).mp hZ1
  have hα : ∀ w z : ↥(N.subgroupOf (N ⊔ Subgroup.zpowers g)),
      shapiroCoord N β ⟨(w * z).1.1, (w * z).2⟩
        = shapiroCoord N β ⟨w.1.1, w.2⟩ + shapiroCoord N β ⟨z.1.1, z.2⟩ := by
    intro w z
    have := hjhom ⟨w.1.1, w.2⟩ ⟨z.1.1, z.2⟩
    rwa [show (⟨(w * z).1.1, (w * z).2⟩ : ↥N) = ⟨w.1.1, w.2⟩ * ⟨z.1.1, z.2⟩ from Subtype.ext rfl]
  have hαc : Continuous fun w : ↥(N.subgroupOf (N ⊔ Subgroup.zpowers g)) =>
      shapiroCoord N β ⟨w.1.1, w.2⟩ :=
    hjc.comp (Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _)
  exact evensNormFun_mem_Z2 (fun _ _ => rfl) hUo hUi hsU _ hα hαc

omit [Finite C] in
/-- **The free orbit's inner cochain vanishes in `H²`** (P-15f2d wiring): the cup product of a deep
`ker ρ`-block cocycle with the `g`-conjugate of another deep block cocycle is an `H²`-coboundary.
Discharges the `Sum.inr (Sum.inr _)` branch of the `hvanish` obligation. -/
theorem hvanish_free_conj (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (β γ : AbsGalQ2 → RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) (g : AbsGalQ2)
    (hZβ : shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) β
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hZγ : shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2))
    (hDβ : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      (shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) β)
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
    (hDγ : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
      (shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ)
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) :
    H2ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
        (cup11Fun AddMonoidHom.mul (shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) β)
          (fun n => shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ (conjMap ρ g n))) = 0 := by
  have hZ1conj : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
      shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ (conjMap ρ g n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) :=
    comp_conjMap_mem_Z1 ρ hZγ g
  have hdeepconj : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (fun n =>
      shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ (conjMap ρ g n))
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
    have heq : H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (fun n =>
        shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ (conjMap ρ g n))
        = conjAct ρ g (H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ)) :=
      (conjAct_h1ofFun ρ g hZγ).symm
    rw [heq]
    exact conjAct_deepClasses (ρ := ρ) g hDγ
  exact InvolutionSplice.hvanish_cup_ker ρ (shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) β)
    (fun n => shapiroCoord (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) γ (conjMap ρ g n))
    hZβ hZ1conj hDβ hdeepconj

/-- **`lemma_6_17_vanish`, closed downstream** (P-15f2d): the base connecting map `Q⁰loc`
vanishes on the deep half, from `lemma_6_17_vanish`'s own hypotheses plus the reciprocity datum
`(R, horient)` threaded per the c2c4 consumer note (P-20 flag). -/
theorem lemma_6_17_vanish_final (D : TateDuality 2) (R : LocalReciprocity) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (horient : TameUnitOrientation R B.tameF)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (x : H1 AbsGalQ2 V) (hx : x ∈ deepPart (V := V) ρ) :
    Q0loc D dat ρ x = 0 := by
  classical
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := gen_of_surjective c hc
  set N : Subgroup AbsGalQ2 := ρ.toMonoidHom.ker with hN
  have hNopen : IsOpen (N : Set AbsGalQ2) := by
    have hset : (N : Set AbsGalQ2) = ρ ⁻¹' {1} := by
      ext g; simp only [hN, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
        Set.mem_singleton_iff]; rfl
    rw [hset]; exact (isOpen_discrete {1}).preimage ρ.continuous_toFun
  haveI hNn : N.Normal := inferInstance
  haveI : Finite (AbsGalQ2 ⧸ N) :=
    Finite.of_injective _ (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom).injective
  haveI : Fintype (AbsGalQ2 ⧸ N) := Fintype.ofFinite _
  set e : C ≃* AbsGalQ2 ⧸ N := eOfSurj ρ hρsurj with he_def
  obtain ⟨K, ι, r, hEqfs, hIso, hιe, hri⟩ :=
    regular_isometric_embedding_orbit (G := AbsGalQ2) N e c hgen q hq hinv hV2
      hfaith hsimple hram
  -- base `RegRep N` instances (the block module is the `Pi`-lift)
  haveI : Finite (RegRep N) := inferInstanceAs (Finite ((AbsGalQ2 ⧸ N) → ZMod 2))
  letI : TopologicalSpace (RegRep N) := ⊥
  haveI : DiscreteTopology (RegRep N) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (RegRep N) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  haveI hdq : DiscreteTopology (AbsGalQ2 ⧸ N) := QuotientGroup.discreteTopology hNopen
  letI actAbs : DistribMulAction AbsGalQ2 (RegRep N) :=
    DistribMulAction.compHom _ (QuotientGroup.mk' N)
  letI actC : DistribMulAction C (RegRep N) := DistribMulAction.compHom _ e.toMonoidHom
  haveI : ContinuousSMul AbsGalQ2 (RegRep N) := by
    refine ⟨?_⟩
    have h1 : Continuous fun p : AbsGalQ2 × RegRep N =>
        ((QuotientGroup.mk' N p.1, p.2) : (AbsGalQ2 ⧸ N) × RegRep N) :=
      (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd
    exact (continuous_of_discreteTopology
      (f := fun p : (AbsGalQ2 ⧸ N) × RegRep N => p.1 • p.2)).comp h1
  haveI : Finite (Fin K → RegRep N) := inferInstance
  haveI : DiscreteTopology (Fin K → RegRep N) := Pi.discreteTopology
  haveI : ContinuousSMul AbsGalQ2 (Fin K → RegRep N) := by
    refine ⟨?_⟩
    have h1 : Continuous fun p : AbsGalQ2 × (Fin K → RegRep N) =>
        ((QuotientGroup.mk' N p.1, p.2) : (AbsGalQ2 ⧸ N) × (Fin K → RegRep N)) :=
      (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd
    exact (continuous_of_discreteTopology
      (f := fun p : (AbsGalQ2 ⧸ N) × (Fin K → RegRep N) => p.1 • p.2)).comp h1
  -- the base compatibility identities (Pi-lifts inherit them)
  have hmk : ∀ (g : AbsGalQ2) (y : RegRep N), g • y = QuotientGroup.mk' N g • y :=
    fun _ _ => rfl
  have hρW : ∀ (g : AbsGalQ2) (w : Fin K → RegRep N), g • w = ρ g • w := by
    intro g w
    funext k
    show QuotientGroup.mk' N g • w k = e (ρ g) • w k
    rw [QuotientGroup.mk'_apply, ← eOfSurj_rho ρ hρsurj g, he_def]
  set qW : (Fin K → RegRep N) → ZMod 2 := fun F => q (r F) with hqW_def
  set datW : FactorSet (AbsGalQ2 ⧸ N) (Fin K → RegRep N) :=
    sumDatum (orbitIndexSet N qW) (orbitDatum N) with hdatW_def
  set datWC : FactorSet C (Fin K → RegRep N) := datW.reindexHom e.toMonoidHom with hdatWC_def
  have hEqfsC : IsEquivariantFactorSet qW datWC :=
    isEquivariantFactorSet_reindexHom hEqfs e.toMonoidHom (fun _ _ => rfl)
  have hqeq : (fun v => qW (ι v)) = q := funext hIso
  have hcomap : IsEquivariantFactorSet q (datWC.comap ι) := by
    have := datum_comap hEqfsC ι (fun cc v => hιe cc v)
    rwa [hqeq] at this
  have hodd : Odd (Nat.card (Subgroup.zpowers (c tameTau))) := by
    rw [Nat.card_zpowers]; exact odd_orderOf_tameInertia c
  have hVI : ∀ v : V, (∀ i ∈ Subgroup.zpowers (c tameTau), i • v = v) → v = 0 :=
    fixedByNormal_eq_bot (Subgroup.zpowers (c tameTau)) (tameInertia_normal c hgen) hsimple
      (by obtain ⟨v, hv⟩ := hram; exact ⟨c tameTau, Subgroup.mem_zpowers _, v, hv⟩)
  have hstep1 : Q0loc D dat ρ x = Q0loc D (datWC.comap ι) ρ x :=
    OrbitVanish.Q0loc_datum_indep D dat (datWC.comap ι) hdat hcomap ρ hρ hV2
      (Subgroup.zpowers (c tameTau)) (tameInertia_normal c hgen) hodd hVI x
  have hic : Continuous (ι : V → Fin K → RegRep N) := continuous_of_discreteTopology
  have heρ : ∀ g : AbsGalQ2, e (ρ g) = QuotientGroup.mk' N g := by
    intro g
    rw [he_def, eOfSurj_rho ρ hρsurj g, QuotientGroup.mk'_apply]
  have hicompat : ∀ (g : AbsGalQ2) (v : V), ι (g • v) = g • ι v := by
    intro g v
    rw [hρ g v, hιe (ρ g) v, heρ g]
    rfl
  have hstep2 : Q0loc D (datWC.comap ι) ρ x
      = Q0loc D datWC ρ (mapCoeff1 ι hic hicompat x) :=
    RepIndependence.lemma_6_14 D datWC ρ ι hic hicompat hEqfsC (fun cc v => hιe cc v) hρW x
  rw [hstep1, hstep2]
  set xW : H1 AbsGalQ2 (Fin K → RegRep N) := mapCoeff1 ι hic hicompat x with hxW_def
  have hxW : xW ∈ deepPart (V := Fin K → RegRep N) ρ :=
    ShapiroDeepness.deepPart_mapCoeff1 hρ hρW ι hic hicompat hx
  set b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N)) := Quotient.out xW with hb_def
  -- the per-orbit subgroup and inner cochain (matching `hcoh_*`)
  set Uf : OrbitIx K (AbsGalQ2 ⧸ N) → Subgroup AbsGalQ2 := fun o =>
    match o with
    | Sum.inl _ => N
    | Sum.inr (Sum.inl (_, u)) => N ⊔ Subgroup.zpowers (Quotient.out u)
    | Sum.inr (Sum.inr _) => N with hUf_def
  set innerf : (o : OrbitIx K (AbsGalQ2 ⧸ N)) → ↥(Uf o) × ↥(Uf o) → ZMod 2 := fun o =>
    match o with
    | Sum.inl j => fun p =>
        shapiroCoord N (fun g => b.1 g j) p.1 * shapiroCoord N (fun g => b.1 g j) p.2
    | Sum.inr (Sum.inl (j, u)) => fun p =>
        evensNormFun (N.subgroupOf (N ⊔ Subgroup.zpowers (Quotient.out u)))
          ⟨Quotient.out u, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩
          (fun w => shapiroCoord N (fun g => b.1 g j) ⟨w.1.1, w.2⟩) (p.1, p.2)
    | Sum.inr (Sum.inr (j, k, u)) => fun p =>
        shapiroCoord N (fun g => b.1 g j) p.1 *
          shapiroCoord N (fun g => b.1 g k) ⟨(Quotient.out u)⁻¹ * (p.2 : AbsGalQ2) * Quotient.out u,
            by simpa using Subgroup.Normal.conj_mem hNn _ p.2.2 (Quotient.out u)⁻¹⟩
      with hinnerf_def
  -- shared facts: `N ≤ Uf o`, openness, finiteness
  have hNleU : ∀ o : OrbitIx K (AbsGalQ2 ⧸ N), N ≤ Uf o := by
    intro o
    match o with
    | Sum.inl _ => exact le_refl N
    | Sum.inr (Sum.inl (_, u)) => exact le_sup_left
    | Sum.inr (Sum.inr _) => exact le_refl N
  have hUopen : ∀ o, IsOpen ((Uf o : Subgroup AbsGalQ2) : Set AbsGalQ2) := fun o =>
    Subgroup.isOpen_mono (hNleU o) hNopen
  have hUfin : ∀ o, Finite (AbsGalQ2 ⧸ Uf o) := by
    intro o
    haveI hfi : N.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
    have hdvd : (Uf o).index ∣ N.index := Subgroup.index_dvd_of_le (hNleU o)
    haveI : (Uf o).FiniteIndex :=
      ⟨fun h0 => hfi.index_ne_zero (Nat.eq_zero_of_zero_dvd (h0 ▸ hdvd))⟩
    exact Subgroup.finite_quotient_of_finiteIndex
  -- the block coordinates are deep `Z¹`-cocycles
  have hZ1blk : ∀ j : Fin K,
      shapiroCoord N (fun g => (Quotient.out xW).1 g j) ∈ Z1 ↥N (ZMod 2) :=
    fun j => shapiroCoord_mem_Z1 (ShapiroRead.block_cocycle N hmk (Quotient.out xW) j)
      (ShapiroRead.block_continuous N (Quotient.out xW) j) (fun _ _ => rfl)
  have hdeepblk : ∀ j : Fin K,
      H1ofFun ↥N (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) ∈ deepClasses N :=
    fun j => shapiroCoord_mem_deepClasses ρ j hxW
  -- involution-position facts, shared across the three `Sum.inr (Sum.inl _)` branches
  have hu_all : ∀ w : AbsGalQ2 ⧸ N, QuotientGroup.mk' N (Quotient.out w) = w := fun w => by
    rw [QuotientGroup.mk'_apply]; exact QuotientGroup.out_eq' w
  refine OrbitVanish.Q0loc_vanish_of_datum_decomp D datWC ρ hρW xW
    (orbitIndexSet N qW) (fun o => (orbitDatum N o).reindexHom e.toMonoidHom)
    (orbitSquareMap N) ?_ ?_ Uf ?_ ?_ innerf ?_ ?_ ?_
  · exact fun o ho =>
      isEquivariantFactorSet_reindexHom (isEqFS_orbitDatum N qW o ho) e.toMonoidHom
        (fun _ _ => rfl)
  · rw [hdatWC_def, hdatW_def]
    exact reindexHom_sumDatum (orbitIndexSet N qW) (orbitDatum N) (⇑e.toMonoidHom)
  · exact fun o _ => hUfin o
  · exact fun o _ => hUopen o
  · -- hZ2
    intro o ho
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · exact cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
        ⟨_, hZ1blk j⟩ ⟨_, hZ1blk j⟩
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_mem N hu2 hune
      exact evensNormFun_orbit_mem_Z2 N hNopen (Quotient.out u) hgN hg2
        (fun g => (Quotient.out xW).1 g j) (hZ1blk j)
    · exact cup11_mem_Z2 AddMonoidHom.mul (fun _ _ _ => rfl)
        ⟨_, hZ1blk j⟩ ⟨_, comp_conjMap_mem_Z1 ρ (hZ1blk k) (Quotient.out u)⟩
  · -- hcoh
    intro o ho
    have hcomp : (⇑e.toMonoidHom ∘ ⇑ρ : AbsGalQ2 → AbsGalQ2 ⧸ N) = ⇑(QuotientGroup.mk' N) :=
      funext heρ
    rw [ShapiroDeepness.graphPullback_reindexHom (orbitDatum N o) (⇑e.toMonoidHom)
      (fun _ _ => rfl) (⇑ρ) (Quotient.out xW).1, hcomp]
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · exact hcoh_square N hmk j hNopen (Quotient.out xW)
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      have hu : QuotientGroup.mk' N (Quotient.out u) = u := hu_all u
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_mem N hu2 hune
      have hs : (⟨Quotient.out u, Subgroup.mem_sup_right (Subgroup.mem_zpowers _)⟩ :
          ↥(N ⊔ Subgroup.zpowers (Quotient.out u)))
          ∉ N.subgroupOf (N ⊔ Subgroup.zpowers (Quotient.out u)) :=
        fun h => hgN (Subgroup.mem_subgroupOf.mp h)
      have hg := hcoh_involution N hmk j (Quotient.out u) hNopen hgN hg2
        (N ⊔ Subgroup.zpowers (Quotient.out u)) rfl hs (Quotient.out xW)
      rw [hu] at hg
      exact hg
    · have hu : QuotientGroup.mk' N (Quotient.out u) = u := hu_all u
      have hg := hcoh_free N hmk j k (Quotient.out u) hNopen (Quotient.out xW)
      rw [hu] at hg
      exact hg
  · -- hvanish
    intro o ho
    rcases o with j | ⟨j, u⟩ | ⟨j, k, u⟩
    · exact InvolutionSplice.hvanish_cup_ker ρ (shapiroCoord N (fun g => (Quotient.out xW).1 g j))
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) (hZ1blk j) (hZ1blk j)
        (hdeepblk j) (hdeepblk j)
    · simp only [mem_orbitIndexSet_inv, invIdx, Finset.mem_filter, Finset.mem_univ,
        true_and] at ho
      obtain ⟨hu2, hune, -⟩ := ho
      obtain ⟨hgN, hg2⟩ := out_notMem_and_out_sq_mem N hu2 hune
      exact InvolutionSplice.hvanish_involution_ker R B c hc ρ hfac horient
        (shapiroCoord N (fun g => (Quotient.out xW).1 g j)) (hZ1blk j) (hdeepblk j)
        (Quotient.out u) hgN hg2 (N ⊔ Subgroup.zpowers (Quotient.out u)) rfl
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    · exact hvanish_free_conj ρ (fun g => (Quotient.out xW).1 g j)
        (fun g => (Quotient.out xW).1 g k) (Quotient.out u) (hZ1blk j) (hZ1blk k)
        (hdeepblk j) (hdeepblk k)

end Assembly

end VanishClose

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.14 = ⟦lem-regularrealization⟧
-/
