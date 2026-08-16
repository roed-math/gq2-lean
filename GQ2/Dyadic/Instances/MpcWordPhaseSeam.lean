import GQ2.Dyadic.Instances.WordPhaseSeam
import GQ2.Dyadic.Instances.MpcPairings

namespace GQ2.Dyadic.Instances.MpcWordPhaseSeam

noncomputable section

open GQ2 GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Count GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MProcyclic
open GQ2.Dyadic.LSquare GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Instances.WordPhaseSeam

attribute [local instance] GQ2.Dyadic.Count.heisTopologicalSpace
  GQ2.Dyadic.Count.heisDiscreteTopology

/-! ## The scalar word trace -/

theorem wPmpc_heisD1_resolvedFamily_apply
    {alpha r pp h q : ℕ} {d : EtaDisplay}
    {C : Type*} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ alpha) (hq : Even q)
    (x : Generator (2 + 2 * h) → ZMod 2) :
    heisD1 (A := ZMod 2) ⇑t
        (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) x =
      ![x .tau, x .tau] := by
  obtain ⟨E, E₂, hfam, hlift, _, _⟩ :=
    exists_resolver_full (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q)
      (C := C) (A := ZMod 2) (B := ZMod 2) d (by decide) (by decide)
  rw [hfam]
  exact GQ2.Dyadic.MProcyclicUnram.heisD1_mpcFamOf_tauRow_of_split
    t E E₂ hlift (by decide) hα hq (fun g a ↦ ResidueLift.htriv_zmod2 (t g) a) x

def wPmpcWordH2TraceEquiv
    {alpha r pp h q : ℕ} {d : EtaDisplay}
    {C : Type*} [Group C] [Finite C] [DistribMulAction C (ZMod 2)]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift ⇑t
      (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C) k) = 1) :
    WordH2 ⇑t (resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)) (ZMod 2) ≃+
      ZMod 2 :=
  wPsWordH2TraceEquiv ⇑t _ hr
    (resolvedFamily_isStokesEndpoint (fourMulExponent_ne_zero_and_even C).1
      (fourMulExponent_ne_zero_and_even C).2 hα hq d)
    ⟨wPsCompactTauBasis h, by
      rw [wPmpc_heisD1_resolvedFamily_apply t hα hq]
      simp [wPsCompactTauBasis]⟩

/-! ## Flexible scalar orientation -/

section Orientation

variable {alpha r pp h q : ℕ} {d : EtaDisplay} {C : Type}
  [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)] [DiscreteTopology (ZMod 2)]
  [DistribMulAction ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2)]
  [ContinuousSMul ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2)]
  [DistribMulAction C (ZMod 2)]

local notation "Gamma" => ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type)
local notation "gen" => gammaGen (2 + 2 * h) q (mpcW alpha r pp d h)
local notation "W" => gammaFam (2 + 2 * h) q (mpcW alpha r pp d h)
local notation "w" => resolvedFamily alpha r pp h q d (4 * Monoid.exponent C)

def wPmpcScalarFlexibleResolverSystem
    (rho : ContinuousMonoidHom Gamma C) (hα : 1 ≤ alpha) (hq : Even q) :
    ∀ (V : OpenNormalSubgroup Gamma)
      (hV : V.toSubgroup ≤ rho.toMonoidHom.ker),
      letI : DistribMulAction (Gamma ⧸ V.toSubgroup) (ZMod 2) :=
        DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
      ModuleFlexibleResolverAt (A := ZMod 2) W
        (fun i ↦ rho (gen i)) w
        (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i)) := by
  intro V hV
  let Q := Gamma ⧸ V.toSubgroup
  letI : DistribMulAction Q (ZMod 2) :=
    DistribMulAction.compHom (ZMod 2) (quotientActionHom rho V hV)
  let wV := resolvedFamily alpha r pp h q d (4 * Monoid.exponent Q)
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := Q) (A := ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hq d
  have hres : ResolvesAt W wV (WordLift (ZMod 2) Q) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) Q) (HeisLift (ZMod 2) Q) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  refine { word := wV, resolves := hres, range_eq := ?_ }
  apply congrArg AddMonoidHom.range
  apply DFunLike.ext _ _
  intro x
  have hleft := wPmpc_heisD1_resolvedFamily_apply
    (alpha := alpha) (r := r) (pp := pp) (d := d)
    (t := Marking.mk (fun i ↦ QuotientGroup.mk' V.toSubgroup (gen i))) hα hq x
  have hright := wPmpc_heisD1_resolvedFamily_apply
    (alpha := alpha) (r := r) (pp := pp) (d := d)
    (t := Marking.mk (fun i ↦ rho (gen i))) hα hq x
  exact hleft.trans hright.symm

noncomputable def wPmpcScalarH2WordFlexible
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q) :
    H2 Gamma (ZMod 2) →+ WordH2 (fun i ↦ rho (gen i)) w (ZMod 2) :=
  globalModuleH2WordFlexible
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPmpcScalarFlexibleResolverSystem rho hα hq)

theorem wPmpcScalarH2WordFlexible_injective
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q) :
    Function.Injective (wPmpcScalarH2WordFlexible rho hcompat hα hq) :=
  globalModuleH2WordFlexible_injective
    (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
    rho hcompat (fun V ↦ hwildLevel_gammaR V) (by decide)
    (wPmpcScalarFlexibleResolverSystem rho hα hq)

def wPmpcScalarH2TraceEquiv_of_surjective
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hsurj : Function.Surjective (wPmpcScalarH2WordFlexible rho hcompat hα hq)) :
    H2 Gamma (ZMod 2) ≃+ ZMod 2 :=
  (AddEquiv.ofBijective (wPmpcScalarH2WordFlexible rho hcompat hα hq)
    ⟨wPmpcScalarH2WordFlexible_injective rho hcompat hα hq, hsurj⟩).trans
      (wPmpcWordH2TraceEquiv (Marking.mk (fun i ↦ rho (gen i))) hα hq hr)

@[simp] theorem wPmpcScalarH2TraceEquiv_of_surjective_mk
    (rho : ContinuousMonoidHom Gamma C)
    (hcompat : ∀ (g : Gamma) (s : ZMod 2), g • s = rho g • s)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1)
    (hsurj : Function.Surjective (wPmpcScalarH2WordFlexible rho hcompat hα hq))
    (f : Z2 Gamma (ZMod 2)) :
    wPmpcScalarH2TraceEquiv_of_surjective rho hcompat hα hq hr hsurj
        (H2mk Gamma (ZMod 2) f) =
      ∑ k, moduleObsFun W gen rho hcompat f k := rfl

omit [TopologicalSpace (ZMod 2)] [IsTopologicalAddGroup (ZMod 2)]
  [DiscreteTopology (ZMod 2)] [DistribMulAction Gamma (ZMod 2)]
  [ContinuousSMul Gamma (ZMod 2)] [DistribMulAction C (ZMod 2)] in
theorem wPmpcScalarH2WordFlexible_surjective
    (rho : ContinuousMonoidHom Gamma C)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
      Nat.card (H2 Gamma (ZMod 2)) = 2)
    (hr : ∀ k, FreeGroup.lift (fun i ↦ rho (gen i)) (w k) = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
    letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
    letI : ContinuousSMul Gamma (ZMod 2) := scalarActionZmodTwo_continuousSMul Gamma
    Function.Surjective (wPmpcScalarH2WordFlexible rho (fun _ _ ↦ rfl) hα hq) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction C (ZMod 2) := scalarActionZmodTwo C
  letI : DistribMulAction Gamma (ZMod 2) := scalarActionZmodTwo Gamma
  letI : ContinuousSMul Gamma (ZMod 2) := scalarActionZmodTwo_continuousSMul Gamma
  let f := wPmpcScalarH2WordFlexible rho (fun _ _ ↦ rfl) hα hq
  have hinj : Function.Injective f :=
    wPmpcScalarH2WordFlexible_injective rho (fun _ _ ↦ rfl) hα hq
  letI : Finite (H2 Gamma (ZMod 2)) := Finite.of_injective f hinj
  letI : Fintype (H2 Gamma (ZMod 2)) := Fintype.ofFinite _
  letI : Fintype (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) := Fintype.ofFinite _
  have hcard : Nat.card (H2 Gamma (ZMod 2)) =
      Nat.card (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) := by
    calc
      Nat.card (H2 Gamma (ZMod 2)) = 2 := hcardH2
      _ = Nat.card (ZMod 2) := (Nat.card_zmod 2).symm
      _ = Nat.card (WordH2 (fun i ↦ rho (gen i)) w (ZMod 2)) :=
        (Nat.card_congr
          (wPmpcWordH2TraceEquiv (Marking.mk (fun i ↦ rho (gen i))) hα hq hr).toEquiv).symm
  exact ((Fintype.bijective_iff_injective_and_card f).mpr
    ⟨hinj, by simpa only [Nat.card_eq_fintype_card] using hcard⟩).2

end Orientation

/-! ## The graph-Hessian trace seam -/

/-- The display-dependent uniform resolver resolves the two Mpc relators in the
`κ₀` graph extension.  In the genuine `.hat` case this uses both values of
`npcResolver`; it is not a constant-resolver surrogate. -/
theorem wPmpc_exists_graphResolver
    {alpha r pp h q : ℕ} (d : EtaDisplay)
    {C V : Type} [Group C] [Finite C] [AddCommGroup V] [Finite V]
    [DistribMulAction C V] {q0 : V → ZMod 2}
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q0 dat)
    (hV2 : ∀ v : V, v + v = 0)
    (m : Generator (2 + 2 * h) → SectionSix.SemiProd C V) :
    letI : Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))
    letI : Finite (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := inferInstance
    letI : TopologicalSpace
        (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := ⊥
    letI : DiscreteTopology
        (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := ⟨rfl⟩
    ∃ (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ),
      ResolverLifts E (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) ∧
      ∀ k, PWord.ResolvedAt
        (WordCoh.lift m (GQ2.Dyadic.kappa0Cocycle dat hdat)) E E₂
        (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h) k) := by
  letI : Finite (SectionSix.SemiProd C V) := inferInstanceAs (Finite (V × C))
  letI : Finite (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := inferInstance
  letI : TopologicalSpace
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := ⊥
  letI : DiscreteTopology
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)) := ⟨rfl⟩
  let L := SectionSix.SemiProd C V
  let N := 4 * Monoid.exponent L
  let K := WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle dat hdat)
  have hN : N ≠ 0 := (fourMulExponent_ne_zero_and_even L).1
  have hord : ∀ y : K, orderOf y ∣ N := by
    intro y
    rw [orderOf_dvd_iff_pow_eq_one]
    apply kappa0_pow_eq_one_of_snd_pow dat hdat hV2
    have hb : y.base ^ Monoid.exponent L = 1 := Monoid.pow_exponent_eq_one y.base
    calc
      y.base.2 ^ Monoid.exponent L = sdSnd (y.base ^ Monoid.exponent L) :=
        (map_pow (sdSnd : L →* C) y.base _).symm
      _ = 1 := by rw [hb]; exact map_one _
  let mu := WordCoh.lift m (GQ2.Dyadic.kappa0Cocycle dat hdat)
  cases d with
  | one =>
      let E : Zhat → ℤ := fun _ ↦ (omega2Exp N : ℤ)
      let E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp N : ℤ)
      have hE : ∀ y : K, y ^ᶻ omega2 = y ^ E omega2 := by
        intro y
        exact PWord.zpowHat_omega2_zpow hN (hord y)
      refine ⟨E, E₂, ?_, ?_⟩
      · intro y
        change y ^ (omega2Exp N : ℤ) = powOmega2 y
        rw [zpow_natCast]
        exact powOmega2_pow_eq y (hord y) hN
      · intro k
        fin_cases k
        · exact PWord.resolvedAt_of_isOmega2Only mu E E₂ hE _
            (isOmega2Only_tameRelW (2 + 2 * h) q)
        · exact PWord.resolvedAt_of_isOmega2Only mu E E₂ hE _
            (isOmega2Only_mpcW alpha r pp (show EtaDisplay.IsOmega2Only .one from trivial) h)
  | lit z =>
      let E : Zhat → ℤ := fun _ ↦ (omega2Exp N : ℤ)
      let E₂ : ℤ_[2] → ℤ := fun _ ↦ (omega2Exp N : ℤ)
      have hE : ∀ y : K, y ^ᶻ omega2 = y ^ E omega2 := by
        intro y
        exact PWord.zpowHat_omega2_zpow hN (hord y)
      refine ⟨E, E₂, ?_, ?_⟩
      · intro y
        change y ^ (omega2Exp N : ℤ) = powOmega2 y
        rw [zpow_natCast]
        exact powOmega2_pow_eq y (hord y) hN
      · intro k
        fin_cases k
        · exact PWord.resolvedAt_of_isOmega2Only mu E E₂ hE _
            (isOmega2Only_tameRelW (2 + 2 * h) q)
        · exact PWord.resolvedAt_of_isOmega2Only mu E E₂ hE _
            (isOmega2Only_mpcW alpha r pp
              (show EtaDisplay.IsOmega2Only (.lit z) from trivial) h)
  | hat num den =>
      have hω : ∀ y : K, y ^ᶻ omega2 =
          y ^ npcResolver N (⟨num, den⟩ : EtaData) omega2 := by
        intro y
        rw [npcResolver_omega2, PWord.zpowHat_omega2_zpow hN (hord y), zpow_natCast]
      have hη : ∀ y : K, y ^ᶻ (EtaDisplay.hat num den).zhat =
          y ^ npcResolver N (⟨num, den⟩ : EtaData) ((EtaDisplay.hat num den).zhat) := by
        intro y
        rw [show (EtaDisplay.hat num den).zhat = EtaData.toZhat ⟨num, den⟩ from rfl,
          npcResolver_toZhat, EtaData.toZhat, zpowHat_etaHatZ_zpow hN (hord y), zpow_natCast]
      refine ⟨npcResolver N ⟨num, den⟩, (fun _ ↦ 0), ?_, ?_⟩
      · intro y
        rw [npcResolver_omega2, zpow_natCast]
        exact powOmega2_pow_eq y (hord y) hN
      · intro k
        fin_cases k
        · exact PWord.resolvedAt_of_isOmega2Only mu _ _ hω _
            (isOmega2Only_tameRelW (2 + 2 * h) q)
        · exact GQ2.Dyadic.Count.resolvedAt_mpcW mu hω hη alpha r pp

theorem wPmpc_QZero_eq_graphHessianTrace
    {alpha r pp h q : ℕ} {d : EtaDisplay}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    {q0 : DD.Vmod → ZMod 2} (hdat : IsEquivariantFactorSet q0 DD.dat)
    (hα : 1 ≤ alpha) (hq : Even q)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hresolved :
      letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
        inferInstanceAs (Finite (DD.Vmod × DD.C0))
      letI : Finite
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) :=
        inferInstance
      letI : TopologicalSpace
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⊥
      letI : DiscreteTopology
          (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⟨rfl⟩
      ∀ k, PWord.ResolvedAt
        (WordCoh.lift
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) E E₂
        (gammaFam (2 + 2 * h) q (mpcW alpha r pp d h) k)) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c =
      hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂
          (tameRelW (2 + 2 * h) q) +
        hessRelZ
          (fun i ↦ graphSemiProdHom c
            (gammaGen (2 + 2 * h) q (mpcW alpha r pp d h) i))
          (GQ2.Dyadic.kappa0Cocycle DD.dat hdat) E E₂
          (mpcW alpha r pp d h) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
    inferInstanceAs (Finite (DD.Vmod × DD.C0))
  letI : Finite
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) :=
    inferInstance
  letI : TopologicalSpace
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⊥
  letI : DiscreteTopology
      (WordCoh.CentExt (GQ2.Dyadic.kappa0Cocycle DD.dat hdat)) := ⟨rfl⟩
  let L := SectionSix.SemiProd DD.C0 DD.Vmod
  letI : Finite L := inferInstanceAs (Finite (DD.Vmod × DD.C0))
  let W : Fin 2 → PWord (Generator (2 + 2 * h)) :=
    gammaFam (2 + 2 * h) q (mpcW alpha r pp d h)
  let w : Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
    resolvedFamily alpha r pp h q d (4 * Monoid.exponent L)
  let gen : Generator (2 + 2 * h) →
      ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) :=
    gammaGen (2 + 2 * h) q (mpcW alpha r pp d h)
  let graph : ContinuousMonoidHom
      ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) L :=
    ⟨graphSemiProdHom c, continuous_graphSemiProdHom c⟩
  let kappa := GQ2.Dyadic.kappa0Cocycle DD.dat hdat
  let f : Z2 ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type) (ZMod 2) :=
    ⟨graphPullback DD.dat (fun g ↦ rho0 DD rho g) c.c,
      graphPullback_mem_Z2_of_cocycle (fun _ _ ↦ rfl) c⟩
  have hb := resolvesAt_and_endpoint_uniformHeis
    (C := L) (A := ZMod 2) (by decide : ∀ a : ZMod 2, a + a = 0)
    (alpha := alpha) (r := r) (pp := pp) (h := h) (q := q) hα hq d
  have hresolve : ResolvesAt W w (WordLift (ZMod 2) L) := by
    let incl : ContinuousMonoidHom (WordLift (ZMod 2) L) (HeisLift (ZMod 2) L) :=
      ⟨heisPrim, continuous_of_discreteTopology⟩
    exact hb.1.pullback incl heisPrim_injective
  have hr : ∀ k, FreeGroup.lift (fun i ↦ graph (gen i)) (w k) = 1 :=
    lower_rel (A := ZMod 2) graph (fun _ ↦ rfl)
      (isAdmissibleMarkedPresentation_gammaR (2 + 2 * h) q (mpcW alpha r pp d h))
      hresolve
  have hsurj : Function.Surjective
      (wPmpcScalarH2WordFlexible graph (fun _ _ ↦ rfl) hα hq) :=
    wPmpcScalarH2WordFlexible_surjective graph hα hq hcardH2 hr
  let orient := wPmpcScalarH2TraceEquiv_of_surjective graph (fun _ _ ↦ rfl) hα hq hr hsurj
  have htrace : QZero DD rho c = ∑ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k := by
    rw [QZero]
    change iotaB f.1 = _
    rw [iotaB_eq_h2Equiv orient f]
    exact wPmpcScalarH2TraceEquiv_of_surjective_mk
      graph (fun _ _ ↦ rfl) hα hq hr hsurj f
  have hnorm : ∀ x y : ((displayedGamma alpha r pp h q d : ProfiniteGrp) : Type),
      moduleNormalize f.1 (x, y) = kappa.κ (graph x) (graph y) := by
    intro x y
    have h11 : f.1 (1, 1) = 0 := by
      change DD.dat.f (c.c 1) (rho0 DD rho 1 • c.c 1) +
        DD.dat.m (rho0 DD rho 1) (c.c 1) = 0
      rw [c.c_one, smul_zero, hdat.f_zero_left, map_one, hdat.m_one, add_zero]
    rw [moduleNormalize, h11, smul_zero, sub_zero]
    exact graphPullback_eq_dyadicKappa0_graph hdat c x y
  have hcoord : ∀ k, moduleObsFun W gen graph (fun _ _ ↦ rfl) f k =
      hessRelZ (fun i ↦ graph (gen i)) kappa E E₂ (W k) := by
    intro k
    exact moduleObsFun_eq_hessRelZ_of_normalized_pullback
      (fun _ _ ↦ rfl) (fun _ _ ↦ rfl) W gen graph f kappa hnorm E E₂ k (hresolved k)
  rw [htrace, Fin.sum_univ_two, hcoord, hcoord]
  rfl

#print axioms wPmpc_heisD1_resolvedFamily_apply
#print axioms wPmpcWordH2TraceEquiv
#print axioms wPmpcScalarFlexibleResolverSystem
#print axioms wPmpcScalarH2WordFlexible
#print axioms wPmpcScalarH2WordFlexible_injective
#print axioms wPmpcScalarH2TraceEquiv_of_surjective
#print axioms wPmpcScalarH2TraceEquiv_of_surjective_mk
#print axioms wPmpcScalarH2WordFlexible_surjective
#print axioms wPmpc_exists_graphResolver
#print axioms wPmpc_QZero_eq_graphHessianTrace

end
end GQ2.Dyadic.Instances.MpcWordPhaseSeam
