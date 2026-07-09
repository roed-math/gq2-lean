import GQ2.Demushkin
import GQ2.DyadicPresentation
import GQ2.MaxProP
import GQ2.Reciprocity
import GQ2.HilbertSymbol
import GQ2.GammaA
import GQ2.TameQuotient
import GQ2.AdmissibleLimit
import GQ2.Foundations.Axioms
import GQ2.ZtwoPowering
import GQ2.FinitelyGenerated
import GQ2.PropOneOne
import GQ2.FrattiniCriterion

/-!
# §3 statements: the tame and maximal pro-2 quotients  (ticket P-06)

Sorried, faithful Lean statements of the paper's §3 interior nodes — **Prop. 3.2**,
**Lemmas 3.5, 3.7, Prop. 3.8**, and **Prop. 1.1** — phrased against the step-1 def-layers.
Proof tickets: P-07 (3.5 ledger), P-08 (3.7/3.8), P-09 (3.2), P-10 (1.1).  The companion
design note `docs/section3-extraction.md` maps every statement to its paper display and
records the absorption/deviation/escalation decisions summarized here:

* **Lemma 3.4 is absorbed** by the axiom layer: its abstract-isomorphism clause *was* axiom B4
  (`absGalQ2_maxProTwo_presentation`, deleted 2026-07-10 as unused — B3c subsumes a marked
  B4), its orientation-value clause *is* the B3c interface
  (`DyadicOrientation`, route (ii)), and its classification-membership clause ("`D₀` is the
  standard rank-3, `q = 2` Demushkin group") is deliberately-unformalized Labute content per
  the standing B3b decision (T-10/T-11).  No sorried statement is introduced for it.
* **Lemma 3.6 is absorbed**: it is axiom B8 (`peripheralCyclotomicAction`) verbatim — the
  T-12 bundle was designed as exactly Lemma 3.6's group-theoretic conclusion.
* **Lemma 3.5's `(ν_ur, χ_D)` rows of eq. (13) and the abelianized relation `ā²s̄⁴ = 1` are
  already proved** (bundle-parametrized) in `GQ2/Reciprocity.lean`: `nu_ur_recip_neg4` /
  `nu_ur_recip_uniformizer` / `nu_ur_recip_neg3`, `chiCyc_recip_neg4` / `chiCyc_recip_neg3`,
  `abelianized_relator`.  What remains here: the marked pro-2-abelianization identification,
  the Hilbert-symbol square-class ledger, and the injectivity of the pair `(ν_ur, χ_D)`.
* **Prop. 3.2's local side rests on axiom B10** (`GQ2.tameQuotient`, added by explicit
  census decision after this ticket's escalation): the classical tame-quotient description
  of `G_{ℚ₂}` (NSW (7.5.3), Iwasawa) is not derivable from the 2-centric step-1 census.
  The bundle and citation discussion live in `GQ2/TameQuotient.lean`; what remains a
  *theorem* here is Lemma 3.3's maximality (the `maximal` field `prop_3_2_local` adds on
  top of the axiom's `TameQuotientData`).

Conventions: `x ^ g = g⁻¹xg` (`conjP`), `[x,y] = x⁻¹y⁻¹xy` (`commP`), reciprocity/`ν_ur`
normalizations as in the `LocalReciprocity` convention table (`GQ2/Reciprocity.lean`).
-/

open scoped Pointwise
open CategoryTheory Multiplicative

namespace GQ2

namespace SectionThree

/-! ## Topology on the topological abelianization

`GQ2.topAbelianization` (T-10) registered only the `Group` instance; the statements below
compare topological abelianizations, so we register its canonical quotient topology.  These
are the (unique) canonical instances, named explicitly to avoid auto-name collisions across
parallel tickets. -/

section TopAb

variable (G : Type*) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The quotient topology on `G^{ab} = G ⧸ closure ⁅G,G⁆`. -/
noncomputable instance instTopologicalSpaceTopAbelianization :
    TopologicalSpace (topAbelianization G) :=
  inferInstanceAs (TopologicalSpace (G ⧸ (commutator G).topologicalClosure))

/-- `G^{ab}` is a topological group. -/
instance instIsTopologicalGroupTopAbelianization :
    IsTopologicalGroup (topAbelianization G) :=
  inferInstanceAs (IsTopologicalGroup (G ⧸ (commutator G).topologicalClosure))

variable {G} in
/-- The abelianization projection `G →* G^{ab}` (cf. `GQ2.toAb` for `G = G_{ℚ₂}`). -/
def abMk : G →* topAbelianization G where
  toFun := QuotientGroup.mk
  map_one' := rfl
  map_mul' _ _ := rfl

variable {G} in
lemma continuous_abMk : Continuous (abMk (G := G)) := continuous_quot_mk

variable {G} in
lemma abMk_surjective : Function.Surjective (abMk (G := G)) := Quotient.mk_surjective

end TopAb

/-! ## Pro-2 abelianization infrastructure for `D₀`  (ticket P-07)

The instances and coordinate machinery that Lemmas 3.5/3.7/3.8 and Prop. 1.1 consume: the
profinite-group instances on `G^{ab}` (so `ZtwoPowering`'s `zpowZtwo` applies), the pro-2-ness of
`D₀^{ab}`, and the **coordinate surjection** `D0ab_coord`: every element of `D₀^{ab}` is
`Ā^a S̄^s Ȳ^y` (topological generation of `{Ā, S̄, Ȳ}` pushed through
`F₃ ↠ D0Full ↠ D₀ ↠ D₀^{ab}`, with the range a closed subgroup). -/

-- The `topAbelianization` profinite-group instances below are registered **`local`** (direct
-- `local instance`, so the `CommGroup` is the genuine construction — wrapping it in a `def` +
-- `attribute [local instance]` breaks the group structure downstream) and **file-scoped**: a global
-- generic `CommGroup`/`CompactSpace`/… on `topAbelianization G` perturbs instance resolution for
-- unrelated profinite quotients `K ⧸ M` in files that import this one (`AnabelianBridge`), whereas a
-- file-local instance stays confined to the P-07 proofs (`Phi`/`D0ab_coord`/`lemma_3_5_injective`).

/-- `G^{ab}` is commutative. -/
noncomputable local instance instCommGroupTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] : CommGroup (topAbelianization G) where
  __ := (inferInstance : Group (topAbelianization G))
  mul_comm := by
    intro x y
    obtain ⟨a, rfl⟩ := abMk_surjective (G := G) x
    obtain ⟨b, rfl⟩ := abMk_surjective (G := G) y
    rw [← map_mul, ← map_mul]
    show QuotientGroup.mk (a * b) = QuotientGroup.mk (b * a)
    refine (QuotientGroup.eq).mpr ?_
    have hcomm : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b * a := by group
    rw [hcomm]
    apply Subgroup.le_topologicalClosure
    have hmem := Subgroup.commutator_mem_commutator (G := G)
      (Subgroup.mem_top b⁻¹) (Subgroup.mem_top a⁻¹)
    rw [commutator_def]
    simpa [commutatorElement_def] using hmem

local instance instCompactSpaceTopAb {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : CompactSpace (topAbelianization G) :=
  inferInstanceAs (CompactSpace (G ⧸ (commutator G).topologicalClosure))

local instance instT2SpaceTopAb {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] : T2Space (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (T2Space (G ⧸ (commutator G).topologicalClosure))

local instance instTotallyDisconnectedSpaceTopAb {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    TotallyDisconnectedSpace (topAbelianization G) :=
  haveI : IsClosed ((commutator G).topologicalClosure : Set G) :=
    (commutator G).isClosed_topologicalClosure
  inferInstanceAs (TotallyDisconnectedSpace (G ⧸ (commutator G).topologicalClosure))

/-- `IsProP p` passes along a continuous surjection. -/
theorem isProP_of_surjective {p : ℕ} {G H : Type*}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (f : G →* H) (hf : Continuous f) (hfs : Function.Surjective f)
    (hG : IsProP p G) : IsProP p H := by
  intro V
  set φ : G →* (H ⧸ V.toSubgroup) := (QuotientGroup.mk' V.toSubgroup).comp f with hφ
  have hφs : Function.Surjective φ := (QuotientGroup.mk'_surjective _).comp hfs
  have hset : ((φ.ker : Subgroup G) : Set G) = f ⁻¹' (V.toSubgroup : Set H) := by
    ext x
    simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, hφ, MonoidHom.comp_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hopen : IsOpen ((φ.ker : Subgroup G) : Set G) := by
    rw [hset]; exact V.toOpenSubgroup.isOpen.preimage hf
  let U : OpenNormalSubgroup G := { toSubgroup := φ.ker, isOpen' := hopen }
  have hpg : IsPGroup p (G ⧸ U.toSubgroup) := hG U
  exact hpg.of_equiv (QuotientGroup.quotientKerEquivOfSurjective φ hφs)

/-- `topAbelianization D0` is pro-2 (image of the pro-2 group `D0` under `abMk`). -/
theorem isProP_two_topAb_D0 : IsProP 2 (topAbelianization D0) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective isProP_maxProPQuotient

/-! ### `zpowZtwo` helper lemmas -/

/-- Powering a square-trivial element: `g ^ a = g ^ (a mod 2)`. -/
lemma zpowZtwo_of_sq_eq_one {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (g : P) (hg : g ^ 2 = 1) (a : ℤ_[2]) :
    zpowZtwo hP g a = g ^ (PadicInt.toZModPow 1 a).val := by
  have hg' : g ^ 2 ^ 1 = 1 := by rwa [pow_one]
  have h := zpowZtwoHom_unique hP (φ := powZModTwoHom g 1 hg')
    (continuous_powZModTwoHom g 1 hg') a
  have hone : powZModTwoHom g 1 hg' (ofAdd (1 : ℤ_[2])) = g := by
    show g ^ (PadicInt.toZModPow 1 (ofAdd (1 : ℤ_[2])).toAdd).val = g
    rw [show (ofAdd (1 : ℤ_[2])).toAdd = (1 : ℤ_[2]) from rfl, map_one,
      show ZMod.val (1 : ZMod (2 ^ 1)) = 1 from by decide, pow_one]
  rw [hone] at h
  rw [← h]
  rfl

/-- In a commutative pro-2 group, `ℤ₂`-powering distributes over the base. -/
lemma zpowZtwo_mul_base {P : Type} [CommGroup P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x y : P) (u : ℤ_[2]) :
    zpowZtwo hP (x * y) u = zpowZtwo hP x u * zpowZtwo hP y u := by
  set φ : Multiplicative ℤ_[2] →* P :=
    (zpowZtwoHom hP x).toMonoidHom * (zpowZtwoHom hP y).toMonoidHom with hφdef
  have hφcont : Continuous φ :=
    (zpowZtwoHom hP x).continuous_toFun.mul (zpowZtwoHom hP y).continuous_toFun
  have h := zpowZtwoHom_unique hP (φ := φ) hφcont u
  have h1 : φ (ofAdd (1 : ℤ_[2])) = x * y := by
    show zpowZtwoHom hP x (ofAdd (1 : ℤ_[2])) * zpowZtwoHom hP y (ofAdd (1 : ℤ_[2])) = x * y
    rw [zpowZtwoHom_ofAdd_one, zpowZtwoHom_ofAdd_one]
  rw [h1] at h
  rw [← h]
  rfl

/-- `ℤ₂`-powering in `Multiplicative ℤ₂` is multiplication of exponents. -/
lemma zpowZtwo_ofAdd (c u : ℤ_[2]) :
    zpowZtwo PropOneOne.isProP_two_multPadicInt (ofAdd c) u = ofAdd (c * u) := by
  set φ : Multiplicative ℤ_[2] →* Multiplicative ℤ_[2] :=
    AddMonoidHom.toMultiplicative (AddMonoidHom.mulLeft c) with hφdef
  have hφcont : Continuous φ :=
    continuous_ofAdd.comp ((continuous_const_mul c).comp continuous_toAdd)
  have h := zpowZtwoHom_unique PropOneOne.isProP_two_multPadicInt (φ := φ) hφcont u
  have h1 : φ (ofAdd (1 : ℤ_[2])) = ofAdd c := by
    show ofAdd (c * (ofAdd (1 : ℤ_[2])).toAdd) = ofAdd c
    rw [show (ofAdd (1 : ℤ_[2])).toAdd = (1 : ℤ_[2]) from rfl, mul_one]
  rw [h1] at h
  rw [← h]
  rfl

/-- `x ^ (0 : ℤ₂) = 1`. -/
lemma zpowZtwo_zero {P : Type} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [T2Space P] [TotallyDisconnectedSpace P]
    (hP : IsProP 2 P) (x : P) : zpowZtwo hP x 0 = 1 := by
  have : zpowZtwo hP x ((0 : ℤ) : ℤ_[2]) = x ^ (0 : ℤ) := zpowZtwo_intCast hP x 0
  simpa using this

/-! ### `Φ : ℤ₂³ → D0^ab` and its surjectivity -/

/-- The coordinate hom `Φ(a,s,y) = Ā^a · S̄^s · Ȳ^y` on `D0^{ab}`. -/
noncomputable def Phi : Multiplicative (ℤ_[2] × ℤ_[2] × ℤ_[2]) →* topAbelianization D0 where
  toFun p := zpowZtwo isProP_two_topAb_D0 (abMk d0A) p.toAdd.1
    * zpowZtwo isProP_two_topAb_D0 (abMk d0S) p.toAdd.2.1
    * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) p.toAdd.2.2
  map_one' := by
    show zpowZtwo _ (abMk d0A) 0 * zpowZtwo _ (abMk d0S) 0 * zpowZtwo _ (abMk d0Y) 0 = 1
    rw [zpowZtwo_zero, zpowZtwo_zero, zpowZtwo_zero, mul_one, mul_one]
  map_mul' p q := by
    show zpowZtwo _ (abMk d0A) (p.toAdd.1 + q.toAdd.1)
        * zpowZtwo _ (abMk d0S) (p.toAdd.2.1 + q.toAdd.2.1)
        * zpowZtwo _ (abMk d0Y) (p.toAdd.2.2 + q.toAdd.2.2)
      = (zpowZtwo _ (abMk d0A) p.toAdd.1 * zpowZtwo _ (abMk d0S) p.toAdd.2.1
          * zpowZtwo _ (abMk d0Y) p.toAdd.2.2)
        * (zpowZtwo _ (abMk d0A) q.toAdd.1 * zpowZtwo _ (abMk d0S) q.toAdd.2.1
          * zpowZtwo _ (abMk d0Y) q.toAdd.2.2)
    rw [zpowZtwo_add, zpowZtwo_add, zpowZtwo_add]
    ac_rfl

lemma continuous_Phi : Continuous Phi := by
  show Continuous fun p : Multiplicative (ℤ_[2] × ℤ_[2] × ℤ_[2]) =>
    zpowZtwo isProP_two_topAb_D0 (abMk d0A) p.toAdd.1
      * zpowZtwo isProP_two_topAb_D0 (abMk d0S) p.toAdd.2.1
      * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) p.toAdd.2.2
  refine ((?_ : Continuous _).mul (?_ : Continuous _)).mul (?_ : Continuous _)
  · exact (continuous_zpowZtwo _ _).comp (continuous_fst.comp continuous_toAdd)
  · exact (continuous_zpowZtwo _ _).comp ((continuous_fst.comp continuous_snd).comp continuous_toAdd)
  · exact (continuous_zpowZtwo _ _).comp ((continuous_snd.comp continuous_snd).comp continuous_toAdd)

/-- **Coordinate surjectivity of `D0^{ab}`**: every element is `Ā^a S̄^s Ȳ^y`. -/
lemma D0ab_coord (z : topAbelianization D0) :
    ∃ a s y : ℤ_[2], z = zpowZtwo isProP_two_topAb_D0 (abMk d0A) a
      * zpowZtwo isProP_two_topAb_D0 (abMk d0S) s
      * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) y := by
  -- The composite surjection `q : F₃ ↠ D0^ab`.
  set q : FreeProfiniteGroup (Fin 3) →* topAbelianization D0 :=
    abMk.comp ((maxProPMk 2 D0Full).toMonoidHom.comp
      (quotientMk (relatorSubgroup {d0Relator})).toMonoidHom) with hqdef
  have hqcont : Continuous q :=
    continuous_abMk.comp ((maxProPMk 2 D0Full).continuous_toFun.comp
      (quotientMk (relatorSubgroup {d0Relator})).continuous_toFun)
  have hqsurj : Function.Surjective q :=
    abMk_surjective.comp ((quotientMk_surjective (proPKernel 2 D0Full)).comp
      (quotientMk_surjective (relatorSubgroup {d0Relator})))
  -- Free generators topologically generate `F₃`.
  have hfree : (Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin 3)))).topologicalClosure
      = ⊤ := by
    set g : FreeGroup (Fin 3) →* FreeProfiniteGroup (Fin 3) :=
      (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (FreeGroup (Fin 3)))).hom with hg
    have hrange : Subgroup.closure (Set.range (FreeProfiniteGroup.of (X := Fin 3))) = g.range := by
      have h1 : Set.range (FreeProfiniteGroup.of (X := Fin 3))
          = ⇑g '' Set.range (FreeGroup.of : Fin 3 → FreeGroup (Fin 3)) := by
        rw [← Set.range_comp]; rfl
      rw [h1, ← MonoidHom.map_closure, FreeGroup.closure_range_of, ← MonoidHom.range_eq_map]
    rw [hrange]
    have hdense : DenseRange g := ProfiniteGrp.ProfiniteCompletion.denseRange _
    rw [SetLike.ext'_iff]
    simpa only [Subgroup.topologicalClosure_coe, Subgroup.coe_top, MonoidHom.coe_range]
      using hdense.closure_range
  -- Push through `q`.
  have hgen : (Subgroup.closure (q '' Set.range (FreeProfiniteGroup.of (X := Fin 3)))).topologicalClosure
      = ⊤ := by
    have := hqsurj.denseRange.topologicalClosure_map_subgroup hqcont hfree
    rwa [MonoidHom.map_closure] at this
  -- `Φ.range` is a closed subgroup containing the generators.
  have hΦclosed : IsClosed (Phi.range : Set (topAbelianization D0)) := by
    rw [MonoidHom.coe_range]
    exact (isCompact_range continuous_Phi).isClosed
  have hsub : Subgroup.closure (q '' Set.range (FreeProfiniteGroup.of (X := Fin 3))) ≤ Phi.range := by
    rw [Subgroup.closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_range]
    fin_cases i
    · exact ⟨ofAdd (1, 0, 0), by
        show zpowZtwo _ (abMk d0A) 1 * zpowZtwo _ (abMk d0S) 0 * zpowZtwo _ (abMk d0Y) 0 = q _
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, mul_one, mul_one]; rfl⟩
    · exact ⟨ofAdd (0, 1, 0), by
        show zpowZtwo _ (abMk d0A) 0 * zpowZtwo _ (abMk d0S) 1 * zpowZtwo _ (abMk d0Y) 0 = q _
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, one_mul, mul_one]; rfl⟩
    · exact ⟨ofAdd (0, 0, 1), by
        show zpowZtwo _ (abMk d0A) 0 * zpowZtwo _ (abMk d0S) 0 * zpowZtwo _ (abMk d0Y) 1 = q _
        rw [zpowZtwo_one_exp, zpowZtwo_zero, zpowZtwo_zero, one_mul, one_mul]; rfl⟩
  have hΦtop : Phi.range = ⊤ := by
    rw [eq_top_iff, ← hgen]
    exact Subgroup.topologicalClosure_minimal _ hsub hΦclosed
  -- Extract coordinates.
  have hz : z ∈ Phi.range := by rw [hΦtop]; exact Subgroup.mem_top z
  rw [MonoidHom.mem_range] at hz
  obtain ⟨p, hp⟩ := hz
  exact ⟨p.toAdd.1, p.toAdd.2.1, p.toAdd.2.2, hp.symm⟩

/-! ## The finite-quotient tame group `T_tame`  (paper §3, first display)

`T_tame = ⟨σ, τ | τ^σ = τ²⟩_prof` is `GQ2.Ttame` with marked generators
`tameSigma`/`tameTau` (the P-11 layer, `GQ2/BoundaryFrame.lean`; the tame relation
`τ^σ = τ²` is proved as `GQ2.tame_relation` in `GQ2/TameQuotient.lean`).
`GQ2/Tame.lean` (Lemma 3.1, fully proved) describes its finite quotients. -/

/-! ## The marked generators of `Γ_A` and its wild subgroup `W_A`  (paper §2.1/§3)

`W_A` is the closed normal subgroup of `Γ_A` generated by the images of `x₀, x₁` (paper
§2.1, after eq. (7)).  **Deduplicated with P-04** (`GQ2/AdmissibleLimit.lean`): `wildPart`
is definitionally `GQ2.wildCore` (the generator spellings agree up to `rfl`), so P-04's
limit theorems transfer verbatim — in particular `isProP_wildPart` below *is*
`isProP_wildCore`, the pro-2 clause of eq. (7) in the limit. -/

/-- The image of `σ` in `Γ_A`. -/
noncomputable def gammaSigma : GammaA :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  quotientMk NA univMarking.σ

/-- The image of `τ` in `Γ_A`. -/
noncomputable def gammaTau : GammaA :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  quotientMk NA univMarking.τ

/-- The image of `x₀` in `Γ_A`. -/
noncomputable def gammaX0 : GammaA :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  quotientMk NA univMarking.x₀

/-- The image of `x₁` in `Γ_A`. -/
noncomputable def gammaX1 : GammaA :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  quotientMk NA univMarking.x₁

/-- **`W_A`** (paper §2.1): the closed normal subgroup of `Γ_A` generated by `x₀, x₁` —
definitionally `GQ2.wildCore` (P-04), under the `Subgroup GammaA` spelling of this layer.
(`normalClosure {gammaX0, gammaX1}`-based unfoldings still hold by `rfl`;
see `wildPart_eq_closure`.) -/
noncomputable def wildPart : Subgroup GammaA := wildCore

/-- The original normal-closure shape of `wildPart` (definitional). -/
theorem wildPart_eq_closure :
    wildPart = (Subgroup.normalClosure {gammaX0, gammaX1}).topologicalClosure := rfl

instance wildPart_normal : wildPart.Normal := wildCore_normal

theorem wildPart_isClosed : IsClosed (wildPart : Set GammaA) := wildCore_isClosed

/-- **`W_A` is pro-2** — the pro-2 clause of eq. (7) holds in the limit.  This is P-04's
`isProP_wildCore` (`GQ2/AdmissibleLimit.lean`), re-exported under the §3 name; it is the
input Prop. 3.2's `Γ_A` side needs for "`W_A` is the wild part". -/
theorem isProP_wildPart : IsProP 2 wildPart := isProP_wildCore


/-! ## Proposition 3.2 — the common tame quotient

Paper: *"There are canonical isomorphisms `Γ_A/W_A ≅ T_tame ≅ G_{ℚ₂}/W_F`, where `W_F` is
wild inertia."*  Split into the two sides; "canonical" is realized as (i) generator-pinning
on the `Γ_A` side and (ii) uniqueness-by-maximality of the wild subgroup on the local side
(the residual choice of local isomorphism is count-invisible downstream — design note §3.2). -/

/- **Prop. 3.2, `Γ_A` side** is stated and **proved** in `GQ2/Prop32.lean`
(`GQ2.SectionThree.prop_3_2_gammaA`, ticket P-09) — declared there because its proof needs
this file's def-layer. -/

/-- **Prop. 3.2, local side + Lemma 3.3's characterization, bundled.**  Extends the B10
bundle `TameQuotientData` (`GQ2/TameQuotient.lean`: `W` closed normal pro-2 with
`G_{ℚ₂}/W ≅ T_tame` — the paper's wild inertia, encoded intrinsically since Mathlib has no
ramification theory; **deviation, flagged there**) by Lemma 3.3's **maximality**, which pins
`W` uniquely (the "canonical" of Prop. 3.2 on the local side).  Maximality is deliberately
*not* part of axiom B10 — it is the paper's own proved content. -/
structure LocalTameQuotient extends TameQuotientData where
  /-- `W_F` is the **maximal** closed normal pro-2 subgroup — Lemma 3.3's `O₂(G_{ℚ₂}) = W_F`. -/
  maximal : ∀ N : Subgroup AbsGalQ2, N.Normal → IsClosed (N : Set AbsGalQ2) →
    IsProP 2 N → N ≤ W

/- **Prop. 3.2, local side** (`GQ2.SectionThree.prop_3_2_local : Nonempty
LocalTameQuotient`) is stated and **proved** in `GQ2/Prop32.lean` (ticket P-09, `Ax = B10`):
the axiom supplies the `TameQuotientData`, and Lemma 3.3's maximality is proved there via
Lemma 3.1's finite analysis and the order-`2^{2^m}−1` inertia levels of the paper's proof. -/

/-! ## Equation (11) — the marked decomposition of `B = D₀^{ab}`

Paper (9)–(11): `B = D₀^{ab} = ⟨Ā, S̄, Ȳ | 2Ā + 4S̄ = 0⟩_{ℤ₂} = C₂·t ⊕ ℤ₂·S̄ ⊕ ℤ₂·Ȳ` with
`t = Ā + 2S̄`.  Bundled so that Lemmas 3.7/3.8 can be phrased against a fixed coordinate
system (house bundle style, cf. `LocalReciprocity`).  In coordinates `(t, S̄, Ȳ)`, note
`Ā ↦ (1, −2, 0)` (forced: `Ā = t − 2S̄`). -/

/-- **Equation (11), bundled**: a continuous isomorphism `B = D₀^{ab} ≅ ℤ/2 × ℤ₂ × ℤ₂`
sending `t̄ = A·S²`, `S̄`, `Ȳ` to the standard basis. -/
structure BDecomposition where
  /-- The coordinate isomorphism `B ≅ C₂ ⊕ ℤ₂ ⊕ ℤ₂` of (11). -/
  e : ContinuousMulEquiv (topAbelianization D0) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]))
  /-- The torsion coordinate: `t = Ā + 2S̄ ↦ (1,0,0)`. -/
  map_t : e (abMk (d0A * d0S ^ 2)) = Multiplicative.ofAdd (1, 0, 0)
  /-- `S̄ ↦ (0,1,0)`. -/
  map_S : e (abMk d0S) = Multiplicative.ofAdd (0, 1, 0)
  /-- `Ȳ ↦ (0,0,1)`. -/
  map_Y : e (abMk d0Y) = Multiplicative.ofAdd (0, 0, 1)

/-! ### Universal property of `D₀` (local replica of `AnabelianBridge.d0Lift`)

`AnabelianBridge.d0Lift` is exactly this, but that file imports `SectionThree`, so we replicate
it here to build the coordinate homs `τ, σ, γ` out of `D₀^ab`. -/

section Lifts

variable {H : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H] [CompactSpace H]
  [T2Space H] [TotallyDisconnectedSpace H]

/-- **Universal property of `D₀`**: a triple in a pro-2 group satisfying the Demushkin relation
classifies a continuous hom `D₀ → H`. -/
noncomputable def d0LiftHom (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    ContinuousMonoidHom D0 H :=
  (maxProPHomEquiv hH).symm
    (quotientLift (relatorSubgroup {d0Relator})
      ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
      (by
        set f := ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of H)).symm m).hom
        have hone : f.toMonoidHom d0Relator = 1 := by
          have h0 : f.toMonoidHom (FreeProfiniteGroup.of 0) = m 0 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h1 : f.toMonoidHom (FreeProfiniteGroup.of 1) = m 1 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          have h2 : f.toMonoidHom (FreeProfiniteGroup.of 2) = m 2 :=
            FreeProfiniteGroup.homEquiv_symm_of _ _ _
          simp only [d0Relator, map_mul, map_pow, Marking.map_commP, h0, h1, h2]
          exact hrel
        refine Subgroup.topologicalClosure_minimal _
          (Subgroup.normalClosure_le_normal ?_) ?_
        · intro r hr
          rw [Set.mem_singleton_iff.mp hr, SetLike.mem_coe, MonoidHom.mem_ker]
          exact hone
        · have hker : (f.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3)))
              = ⇑f ⁻¹' {1} := by
            ext x
            simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
              Set.mem_singleton_iff]
            rfl
          rw [hker]
          exact isClosed_singleton.preimage f.continuous_toFun))

@[simp] lemma d0LiftHom_A (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0A = m 0 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 0))) = m 0
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma d0LiftHom_S (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0S = m 1 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 1))) = m 1
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

@[simp] lemma d0LiftHom_Y (hH : IsProP 2 H) (m : Fin 3 → H)
    (hrel : m 0 ^ 2 * m 1 ^ 4 * commP (m 1) (m 2) = 1) :
    d0LiftHom hH m hrel d0Y = m 2 := by
  show ((maxProPHomEquiv hH).symm _) (maxProPMk 2 D0Full
    (quotientMk (relatorSubgroup {d0Relator}) (FreeProfiniteGroup.of 2))) = m 2
  rw [maxProPHomEquiv_symm_apply_maxProPMk]
  exact (quotientLift_quotientMk _ _ _ _).trans (FreeProfiniteGroup.homEquiv_symm_of _ _ _)

end Lifts

/-- `Multiplicative (ZMod 2)` is pro-2 (a finite 2-group). -/
theorem isProP_two_multZMod2 : IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup (IsPGroup.of_card (p := 2) (n := 1)
    (by rw [Nat.card_eq_fintype_card]; decide))

/-! ### Descending a hom `D₀ → H` (H abelian) through `abMk` -/

/-- A continuous hom from `D₀` to an abelian group factors through `D₀^{ab}`. -/
noncomputable def abLift {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (g : ContinuousMonoidHom D0 H) : ContinuousMonoidHom (topAbelianization D0) H :=
  quotientLift (commutator D0).topologicalClosure g (by
    refine Subgroup.topologicalClosure_minimal _ (Abelianization.commutator_subset_ker g.toMonoidHom) ?_
    have hset : (g.toMonoidHom.ker : Set D0) = g ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    rw [hset]
    exact isClosed_singleton.preimage g.continuous_toFun)

@[simp] lemma abLift_abMk {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H]
    [T2Space H] (g : ContinuousMonoidHom D0 H) (d : D0) : abLift g (abMk d) = g d := rfl

/-- Source-generic `abLift`: descend a continuous hom `G → H` (H abelian, T2) through `abMk`. -/
noncomputable def abLiftG {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (g : ContinuousMonoidHom G H) : ContinuousMonoidHom (topAbelianization G) H :=
  quotientLift (commutator G).topologicalClosure g (by
    refine Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker g.toMonoidHom) ?_
    have hset : (g.toMonoidHom.ker : Set G) = g ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff]
      rfl
    rw [hset]
    exact isClosed_singleton.preimage g.continuous_toFun)

@[simp] lemma abLiftG_abMk {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {H : Type} [CommGroup H] [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]
    (g : ContinuousMonoidHom G H) (d : G) : abLiftG g (abMk d) = g d := rfl

/-! ### The three coordinate homs `σ` (S-coord), `γ` (Y-coord), `τ` (t-coord) -/

/-- The `S̄`-coordinate hom `σ : D₀^ab → ℤ₂`, with `Ā ↦ −2`, `S̄ ↦ 1`, `Ȳ ↦ 0`. -/
noncomputable def sHom : ContinuousMonoidHom (topAbelianization D0) (Multiplicative ℤ_[2]) :=
  abLift (d0LiftHom PropOneOne.isProP_two_multPadicInt
    ![ofAdd (-2 : ℤ_[2]), ofAdd (1 : ℤ_[2]), ofAdd (0 : ℤ_[2])] (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring))

/-- The `Ȳ`-coordinate hom `γ : D₀^ab → ℤ₂`, with `Ā ↦ 0`, `S̄ ↦ 0`, `Ȳ ↦ 1`. -/
noncomputable def yHom : ContinuousMonoidHom (topAbelianization D0) (Multiplicative ℤ_[2]) :=
  abLift (d0LiftHom PropOneOne.isProP_two_multPadicInt
    ![ofAdd (0 : ℤ_[2]), ofAdd (0 : ℤ_[2]), ofAdd (1 : ℤ_[2])] (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      rw [← ofAdd_zero]; congr 1; simp only [nsmul_eq_mul]; push_cast; ring))

/-- The `t̄`-coordinate hom `τ : D₀^ab → ZMod 2`, with `Ā ↦ 1`, `S̄ ↦ 0`, `Ȳ ↦ 0`. -/
noncomputable def tHom : ContinuousMonoidHom (topAbelianization D0) (Multiplicative (ZMod 2)) :=
  abLift (d0LiftHom isProP_two_multZMod2
    ![ofAdd (1 : ZMod 2), ofAdd (0 : ZMod 2), ofAdd (0 : ZMod 2)] (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons, commP, ← ofAdd_nsmul, ← ofAdd_neg, ← ofAdd_add]
      rw [← ofAdd_zero]; congr 1))

@[simp] lemma sHom_A : sHom (abMk d0A) = ofAdd (-2 : ℤ_[2]) := by simp [sHom]
@[simp] lemma sHom_S : sHom (abMk d0S) = ofAdd (1 : ℤ_[2]) := by simp [sHom]
@[simp] lemma sHom_Y : sHom (abMk d0Y) = ofAdd (0 : ℤ_[2]) := by simp [sHom]
@[simp] lemma yHom_A : yHom (abMk d0A) = ofAdd (0 : ℤ_[2]) := by simp [yHom]
@[simp] lemma yHom_S : yHom (abMk d0S) = ofAdd (0 : ℤ_[2]) := by simp [yHom]
@[simp] lemma yHom_Y : yHom (abMk d0Y) = ofAdd (1 : ℤ_[2]) := by simp [yHom]
@[simp] lemma tHom_A : tHom (abMk d0A) = ofAdd (1 : ZMod 2) := by simp [tHom]
@[simp] lemma tHom_S : tHom (abMk d0S) = ofAdd (0 : ZMod 2) := by simp [tHom]
@[simp] lemma tHom_Y : tHom (abMk d0Y) = ofAdd (0 : ZMod 2) := by simp [tHom]

/-! ### The combined coordinate hom `φ = (τ, σ, γ)` -/

/-- The combined coordinate map `φ : D₀^ab → ZMod 2 × ℤ₂ × ℤ₂`. -/
noncomputable def phiHom :
    topAbelianization D0 →* Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2]) where
  toFun z := ofAdd ((tHom z).toAdd, (sHom z).toAdd, (yHom z).toAdd)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, toAdd_mul]
    rw [← ofAdd_add]
    rfl

lemma continuous_phiHom : Continuous phiHom := by
  show Continuous fun z => ofAdd ((tHom z).toAdd, (sHom z).toAdd, (yHom z).toAdd)
  exact continuous_ofAdd.comp
    ((continuous_toAdd.comp tHom.continuous_toFun).prodMk
      ((continuous_toAdd.comp sHom.continuous_toFun).prodMk
        (continuous_toAdd.comp yHom.continuous_toFun)))

@[simp] lemma phiHom_A : phiHom (abMk d0A) = ofAdd ((1 : ZMod 2), (-2 : ℤ_[2]), (0 : ℤ_[2])) := by
  simp only [phiHom, MonoidHom.coe_mk, OneHom.coe_mk, sHom_A, tHom_A, yHom_A, toAdd_ofAdd]

@[simp] lemma phiHom_S : phiHom (abMk d0S) = ofAdd ((0 : ZMod 2), (1 : ℤ_[2]), (0 : ℤ_[2])) := by
  simp only [phiHom, MonoidHom.coe_mk, OneHom.coe_mk, sHom_S, tHom_S, yHom_S, toAdd_ofAdd]

@[simp] lemma phiHom_Y : phiHom (abMk d0Y) = ofAdd ((0 : ZMod 2), (0 : ℤ_[2]), (1 : ℤ_[2])) := by
  simp only [phiHom, MonoidHom.coe_mk, OneHom.coe_mk, sHom_Y, tHom_Y, yHom_Y, toAdd_ofAdd]

/-! ### Coordinate computations on `Ā^a S̄^s Ȳ^y` -/

/-- Abbreviation for the coordinate word. -/
private noncomputable def word (a s y : ℤ_[2]) : topAbelianization D0 :=
  zpowZtwo isProP_two_topAb_D0 (abMk d0A) a * zpowZtwo isProP_two_topAb_D0 (abMk d0S) s
    * zpowZtwo isProP_two_topAb_D0 (abMk d0Y) y

lemma sHom_word (a s y : ℤ_[2]) : sHom (word a s y) = ofAdd ((-2) * a + s) := by
  rw [word, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt sHom,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt sHom,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt sHom,
    sHom_A, sHom_S, sHom_Y, zpowZtwo_ofAdd, zpowZtwo_ofAdd, zpowZtwo_ofAdd,
    ← ofAdd_add, ← ofAdd_add]
  congr 1; ring

lemma yHom_word (a s y : ℤ_[2]) : yHom (word a s y) = ofAdd y := by
  rw [word, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt yHom,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt yHom,
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt yHom,
    yHom_A, yHom_S, yHom_Y, zpowZtwo_ofAdd, zpowZtwo_ofAdd, zpowZtwo_ofAdd,
    ← ofAdd_add, ← ofAdd_add]
  congr 1; ring

lemma tHom_word (a s y : ℤ_[2]) :
    tHom (word a s y) = zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) a := by
  rw [word, map_mul, map_mul,
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_multZMod2 tHom,
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_multZMod2 tHom,
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_multZMod2 tHom,
    tHom_A, tHom_S, tHom_Y]
  rw [show ofAdd (0 : ZMod 2) = 1 from ofAdd_zero, zpowZtwo_one_base, zpowZtwo_one_base,
    mul_one, mul_one]

/-! ### `φ` is injective -/

/-- `Ā² S̄⁴ = 1` in `D₀^ab`. -/
lemma abMk_rel : (abMk d0A) ^ 2 * (abMk d0S) ^ 4 = 1 := by
  have hcommP : abMk (commP d0S d0Y) = 1 := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (abMk d0S)⁻¹ (abMk d0Y)⁻¹]
    group
  have h2 : abMk (d0A ^ 2 * d0S ^ 4 * commP d0S d0Y) = 1 := by rw [d0_relation]; exact map_one abMk
  rw [map_mul, map_mul, map_pow, map_pow, hcommP, mul_one] at h2
  exact h2

/-- `t̄ = Ā · S̄²` is 2-torsion. -/
lemma tbar_sq : (abMk d0A * zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2) ^ 2 = 1 := by
  rw [mul_pow, pow_two (zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2), ← zpowZtwo_add,
    show (2 : ℤ_[2]) + 2 = ((4 : ℕ) : ℤ_[2]) by push_cast; ring, zpowZtwo_natCast]
  exact abMk_rel

lemma phiHom_injective : Function.Injective phiHom := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨a, s, y, rfl⟩ := D0ab_coord z
  change phiHom (word a s y) = 1 at hz
  -- extract the three coordinate equations
  have hv : ((tHom (word a s y)).toAdd, (sHom (word a s y)).toAdd, (yHom (word a s y)).toAdd)
      = (0, 0, 0) := by
    have h1 : (ofAdd ((tHom (word a s y)).toAdd, (sHom (word a s y)).toAdd,
        (yHom (word a s y)).toAdd) : Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) = ofAdd 0 := by
      rw [ofAdd_zero]; exact hz
    exact Multiplicative.ofAdd.injective h1
  rw [Prod.mk.injEq, Prod.mk.injEq] at hv
  obtain ⟨hvt, hvs, hvy⟩ := hv
  -- `sHom`: `s = 2a`
  have hsval : sHom (word a s y) = 1 := by rw [← ofAdd_toAdd (sHom (word a s y)), hvs, ofAdd_zero]
  rw [sHom_word] at hsval
  have hs : s = 2 * a := by
    have := Multiplicative.ofAdd.injective (hsval.trans ofAdd_zero.symm)
    push_cast at this; linear_combination this
  -- `yHom`: `y = 0`
  have hyval : yHom (word a s y) = 1 := by rw [← ofAdd_toAdd (yHom (word a s y)), hvy, ofAdd_zero]
  rw [yHom_word] at hyval
  have hy0 : y = 0 := Multiplicative.ofAdd.injective (hyval.trans ofAdd_zero.symm)
  -- `tHom`: `a` even
  have htval : tHom (word a s y) = 1 := by rw [← ofAdd_toAdd (tHom (word a s y)), hvt, ofAdd_zero]
  rw [tHom_word, zpowZtwo_of_sq_eq_one isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) (by decide) a]
    at htval
  have hval0 : (PadicInt.toZModPow 1 a).val = 0 := by
    have hlt : (PadicInt.toZModPow (p := 2) 1 a).val < 2 := by
      have := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 a); simpa using this
    rcases (by omega : (PadicInt.toZModPow 1 a).val = 0 ∨ (PadicInt.toZModPow 1 a).val = 1)
      with h0 | h1
    · exact h0
    · rw [h1, pow_one] at htval
      exact absurd (Multiplicative.ofAdd.injective htval) (by decide)
  -- conclude `word a s y = 1`
  show word a s y = 1
  rw [word, hs, hy0, zpowZtwo_zero, mul_one,
    ← zpowZtwo_zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2 a, ← zpowZtwo_mul_base,
    zpowZtwo_of_sq_eq_one isProP_two_topAb_D0 _ tbar_sq a, hval0, pow_zero]

/-! ### `φ` is surjective -/

/-- The `ZMod 2` powering hits every class: `(ofAdd 1)^(c.val) = ofAdd c`. -/
lemma zpowZtwo_ofAdd_one_zmod2 (c : ZMod 2) :
    zpowZtwo isProP_two_multZMod2 (ofAdd (1 : ZMod 2)) ((c.val : ℤ_[2])) = ofAdd c := by
  rw [zpowZtwo_natCast, ← ofAdd_nsmul]
  congr 1
  rw [nsmul_eq_mul, mul_one]
  exact ZMod.natCast_rightInverse c

lemma phiHom_surjective : Function.Surjective phiHom := by
  intro w
  rw [← ofAdd_toAdd w]
  obtain ⟨c, s, y⟩ := w.toAdd
  refine ⟨word ((c.val : ℤ_[2])) (s + 2 * (c.val : ℤ_[2])) y, ?_⟩
  show ofAdd ((tHom (word _ _ _)).toAdd, (sHom (word _ _ _)).toAdd, (yHom (word _ _ _)).toAdd)
    = ofAdd (c, s, y)
  rw [tHom_word, sHom_word, yHom_word, zpowZtwo_ofAdd_one_zmod2]
  congr 1
  refine Prod.ext (by simp) (Prod.ext ?_ (by simp))
  simp only [toAdd_ofAdd]
  ring

/-! ### Assembly -/

/-- The coordinate isomorphism `φ : D₀^ab ≃ₜ* ZMod 2 × ℤ₂ × ℤ₂`. -/
noncomputable def phiEquiv :
    ContinuousMulEquiv (topAbelianization D0) (Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2])) :=
  continuousMulEquivOfBijective ⟨phiHom, continuous_phiHom⟩
    ⟨phiHom_injective, phiHom_surjective⟩

@[simp] lemma phiEquiv_apply (z : topAbelianization D0) : phiEquiv z = phiHom z := rfl

/-- **Equation (11)** (paper §3.1 preamble): the marked decomposition of `B` exists.
(Proof ticket P-07, std-3: the marked pro-2 abelianization `D₀^ab ≅ ℤ/2 × ℤ₂ × ℤ₂` via the
coordinate homs `τ, σ, γ` built from `d0LiftHom` + `abLift`, shown bijective.) -/
theorem b_decomposition : Nonempty BDecomposition :=
  ⟨{ e := phiEquiv
     map_t := by
       rw [phiEquiv_apply]
       simp only [map_mul, map_pow, phiHom_A, phiHom_S]
       rw [pow_two, ← ofAdd_add, ← ofAdd_add]
       congr 1
       simp only [Prod.mk_add_mk]
       refine Prod.ext ?_ (Prod.ext ?_ ?_)
       · decide
       · push_cast; ring
       · simp
     map_S := by rw [phiEquiv_apply, phiHom_S]
     map_Y := by rw [phiEquiv_apply, phiHom_Y] }⟩

/-! ## Lemma 3.5 — marked abelianization, orientation, and initial form

The `(ν_ur, χ_D)`-rows of eq. (13) and `ā²s̄⁴ = 1` are proved in `GQ2/Reciprocity.lean`
(see the module docstring above).  The three remaining clauses: -/

/-- `−4 ∈ ℚ₂ˣ` — the class `ā = rec(−4)` of Lemma 3.5.  (Public counterpart of the private
`uNeg4` in `GQ2/Reciprocity.lean`.) -/
noncomputable def unitNeg4 : ℚ_[2]ˣ := Units.mk0 (-4 : ℚ_[2]) (by norm_num)

/-- `−3 ∈ ℚ₂ˣ` — the class `ȳ = rec(−3)` of Lemma 3.5. -/
noncomputable def unitNeg3 : ℚ_[2]ˣ := Units.mk0 (-3 : ℚ_[2]) (by norm_num)

/-! ### Marked-abelianization clause

**Reduced to the single reciprocity-iso lemma `markedHom_bijective`** (the one census-gated gap,
Escalation 5 in `docs/section3-extraction.md`): the descent `markedPi`, the marked hom
`markedHom` (`Ā,S̄,Ȳ ↦ rec(−4), rec(1/2), rec(−3)`, relation verified), and the generator matching
are all **std-3**; only `markedHom` being *bijective* — i.e. the three reciprocity classes
coordinatize `(G_ℚ₂(2))^ab`, the pro-2 local-reciprocity iso, which B5 does not pin — remains open. -/

/-! ### Arithmetic input for `markedHom_bijective`'s surjectivity

Finite-2-group Frattini (`sq_generate`), Hensel square roots (`hensel_sq`), and the square-class
generation of `ℚ₂ˣ` by `{−4, 2, −3}` (`units_gen`).  None of these use the Galois-theoretic
section variables. -/

/-- If every element of a finite 2-group `Q` is `s·t²` with `s ∈ S`, then `S = ⊤`.  (Squares lie in
every index-2 subgroup, so a coatom `M ≥ S` would swallow all of `Q`.) -/
theorem sq_generate {Q : Type*} [Group Q] [Finite Q] (hQ : IsPGroup 2 Q) {S : Subgroup Q}
    (hgen : ∀ q : Q, ∃ s ∈ S, ∃ t : Q, q = s * t ^ 2) : S = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (Subgroup Q) := Finite.of_injective _ SetLike.coe_injective
  by_contra hne
  obtain ⟨M, hM, hSM⟩ := (eq_top_or_exists_le_coatom S).resolve_left hne
  haveI : M.Normal := coatom_normal_of_pGroup hQ hM
  have hidx : M.index = 2 := coatom_index_of_pGroup hQ hM
  haveI : Fintype (Q ⧸ M) := Fintype.ofFinite _
  have hc2 : Fintype.card (Q ⧸ M) = 2 := by rw [← Nat.card_eq_fintype_card]; exact hidx
  have hsq : ∀ t : Q, t ^ 2 ∈ M := by
    intro t
    have h1 : (QuotientGroup.mk' M t) ^ 2 = 1 := by rw [← hc2]; exact pow_card_eq_one
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact h1
  refine hM.1 ?_
  rw [eq_top_iff]
  intro q _
  obtain ⟨s, hs, t, rfl⟩ := hgen q
  exact M.mul_mem (hSM hs) (hsq t)

/-- **Hensel square roots**: a 2-adic unit `≡ 1 (mod 8)` is a square. -/
lemma hensel_sq (u : ℤ_[2]ˣ) (h8 : (8 : ℤ_[2]) ∣ ((u : ℤ_[2]) - 1)) :
    ∃ w : ℤ_[2]ˣ, u = w ^ 2 := by
  set F : Polynomial ℤ_[2] := Polynomial.X ^ 2 - Polynomial.C (u : ℤ_[2]) with hF
  have hevAll : ∀ a : ℤ_[2], Polynomial.aeval a F = a ^ 2 - (u : ℤ_[2]) := by
    intro a; simp [hF, map_sub, map_pow]
  have hdev : Polynomial.aeval (1 : ℤ_[2]) F.derivative = 2 := by
    rw [hF, Polynomial.derivative_sub, Polynomial.derivative_C, sub_zero,
      Polynomial.derivative_X_pow]
    simp
  have h2pos : (0 : ℝ) < ‖(2 : ℤ_[2])‖ := by rw [norm_pos_iff]; norm_num
  have h2lt1 : ‖(2 : ℤ_[2])‖ < 1 :=
    lt_of_le_of_ne (PadicInt.norm_le_one 2)
      (fun h => not_isUnit_two (PadicInt.isUnit_iff.mpr h))
  have hnorm : ‖Polynomial.aeval (1 : ℤ_[2]) F‖ <
      ‖Polynomial.aeval (1 : ℤ_[2]) F.derivative‖ ^ 2 := by
    rw [hevAll, hdev, one_pow]
    have hle : ‖(1 : ℤ_[2]) - (u : ℤ_[2])‖ ≤ ‖(8 : ℤ_[2])‖ := by
      obtain ⟨c, hc⟩ := h8
      rw [norm_sub_rev, hc, norm_mul]
      calc ‖(8 : ℤ_[2])‖ * ‖c‖ ≤ ‖(8 : ℤ_[2])‖ * 1 :=
            mul_le_mul_of_nonneg_left (PadicInt.norm_le_one c) (norm_nonneg _)
        _ = ‖(8 : ℤ_[2])‖ := mul_one _
    have h82 : ‖(8 : ℤ_[2])‖ < ‖(2 : ℤ_[2])‖ ^ 2 := by
      have h8eq : (8 : ℤ_[2]) = (2 : ℤ_[2]) ^ 3 := by norm_num
      rw [h8eq, norm_pow]
      calc ‖(2 : ℤ_[2])‖ ^ 3 = ‖(2 : ℤ_[2])‖ ^ 2 * ‖(2 : ℤ_[2])‖ := by ring
        _ < ‖(2 : ℤ_[2])‖ ^ 2 * 1 := mul_lt_mul_of_pos_left h2lt1 (pow_pos h2pos 2)
        _ = ‖(2 : ℤ_[2])‖ ^ 2 := mul_one _
    exact lt_of_le_of_lt hle h82
  obtain ⟨z, hz, _⟩ := hensels_lemma hnorm
  rw [hevAll] at hz
  have hz2 : z ^ 2 = (u : ℤ_[2]) := by linear_combination hz
  have hzu : IsUnit z := by
    have hu2 : IsUnit (z ^ 2) := by rw [hz2]; exact u.isUnit
    rw [pow_two] at hu2
    exact isUnit_of_mul_isUnit_left hu2
  refine ⟨hzu.unit, ?_⟩
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, IsUnit.unit_spec, hz2]

/-- `toZModPow 3` detects divisibility by `8` in `ℤ₂`. -/
lemma toZModPow3_eq_zero_iff (y : ℤ_[2]) :
    PadicInt.toZModPow 3 y = 0 ↔ (8 : ℤ_[2]) ∣ y := by
  rw [← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton,
    show ((2 : ℕ) : ℤ_[2]) ^ 3 = 8 by norm_num]

/-- `-3` as a 2-adic unit. -/
noncomputable def neg3Int : ℤ_[2]ˣ :=
  (show IsUnit (-3 : ℤ_[2]) by
    rw [PadicInt.isUnit_iff]
    refine le_antisymm (PadicInt.norm_le_one _) (not_lt.mp ?_)
    rw [show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring,
      PadicInt.norm_int_lt_one_iff_dvd]
    norm_num).unit

@[simp] lemma neg3Int_val : (neg3Int : ℤ_[2]) = -3 := IsUnit.unit_spec _

/-- A norm-`1` element of `ℚ₂ˣ` comes from a `ℤ₂`-unit. -/
lemma norm_one_unit (u : ℚ_[2]ˣ) (h : ‖(u : ℚ_[2])‖ = 1) :
    ∃ u₂ : ℤ_[2]ˣ, unitEmbed u₂ = u := by
  have hmem : ‖(u : ℚ_[2])‖ ≤ 1 := le_of_eq h
  let y : ℤ_[2] := ⟨(u : ℚ_[2]), hmem⟩
  have hyu : IsUnit y := PadicInt.isUnit_iff.mpr h
  refine ⟨hyu.unit, ?_⟩
  apply Units.ext
  rw [unitEmbed_val, IsUnit.unit_spec]
  rfl

/-- **Mod-8 square decomposition of `ℤ₂ˣ`**: every 2-adic unit is `s·w²` with `s ∈ {1,−1,−3,3}`. -/
lemma mod8_sq (u₂ : ℤ_[2]ˣ) :
    ∃ s₂ : ℤ_[2]ˣ, (s₂ = 1 ∨ s₂ = -1 ∨ s₂ = neg3Int ∨ s₂ = -neg3Int) ∧
      ∃ w : ℤ_[2]ˣ, u₂ = s₂ * w ^ 2 := by
  have main : ∀ s₂ : ℤ_[2]ˣ,
      PadicInt.toZModPow 3 (↑u₂ : ℤ_[2]) = PadicInt.toZModPow 3 (↑s₂ : ℤ_[2]) →
      ∃ w : ℤ_[2]ˣ, u₂ = s₂ * w ^ 2 := by
    intro s₂ hres
    have hdvd : (8 : ℤ_[2]) ∣ ((↑u₂ : ℤ_[2]) - ↑s₂) := by
      rw [← toZModPow3_eq_zero_iff, map_sub, hres, sub_self]
    have hs1 : (↑s₂ : ℤ_[2]) * ↑s₂⁻¹ = 1 := by
      rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have heq : (↑(u₂ * s₂⁻¹) : ℤ_[2]) - 1 = ((↑u₂ : ℤ_[2]) - ↑s₂) * ↑s₂⁻¹ := by
      rw [Units.val_mul, sub_mul, hs1]
    have hdvd1 : (8 : ℤ_[2]) ∣ ((↑(u₂ * s₂⁻¹) : ℤ_[2]) - 1) := by
      rw [heq]; exact hdvd.mul_right _
    obtain ⟨w, hw⟩ := hensel_sq (u₂ * s₂⁻¹) hdvd1
    exact ⟨w, by rw [← hw, mul_comm s₂ (u₂ * s₂⁻¹), mul_assoc, inv_mul_cancel, mul_one]⟩
  have hunit : IsUnit (PadicInt.toZModPow 3 (↑u₂ : ℤ_[2])) := u₂.isUnit.map _
  have hcls : ∀ r : ZMod 8, IsUnit r → r = 1 ∨ r = 3 ∨ r = 5 ∨ r = 7 := by decide
  rcases hcls _ hunit with hr | hr | hr | hr
  · exact ⟨1, Or.inl rfl, main 1 (by rw [hr]; simp)⟩
  · refine ⟨-neg3Int, Or.inr (Or.inr (Or.inr rfl)), main (-neg3Int) ?_⟩
    rw [hr, show (↑(-neg3Int) : ℤ_[2]) = ((3 : ℤ) : ℤ_[2]) by
      rw [Units.val_neg, neg3Int_val]; push_cast; ring, map_intCast]
    decide
  · refine ⟨neg3Int, Or.inr (Or.inr (Or.inl rfl)), main neg3Int ?_⟩
    rw [hr, show (↑neg3Int : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by
      rw [neg3Int_val]; push_cast; ring, map_intCast]
    decide
  · refine ⟨-1, Or.inr (Or.inl rfl), main (-1) ?_⟩
    rw [hr, show (↑(-1 : ℤ_[2]ˣ) : ℤ_[2]) = ((-1 : ℤ) : ℤ_[2]) by
      rw [Units.val_neg, Units.val_one]; push_cast; ring, map_intCast]
    decide

/-- **`ℚ₂ˣ = ⟨−4, 2, −3⟩ · (ℚ₂ˣ)²`**: every unit of `ℚ₂` is `s·t²` with `s` in the subgroup
generated by `{−4, 2, −3}`.  (Valuation split `x = 2ⁿ·u` + mod-8 square classes of `ℤ₂ˣ`.) -/
theorem units_gen (x : ℚ_[2]ˣ) :
    ∃ s ∈ Subgroup.closure {unitNeg4, uniformizer, unitNeg3}, ∃ t : ℚ_[2]ˣ, x = s * t ^ 2 := by
  set C := Subgroup.closure {unitNeg4, uniformizer, unitNeg3} with hCdef
  have hmem_unif : uniformizer ∈ C := Subgroup.subset_closure (by simp)
  have hmem_n4 : unitNeg4 ∈ C := Subgroup.subset_closure (by simp)
  have hmem_n3 : unitNeg3 ∈ C := Subgroup.subset_closure (by simp)
  have hmem_neg1 : (-1 : ℚ_[2]ˣ) ∈ C := by
    have hval : (-1 : ℚ_[2]ˣ) = unitNeg4 * uniformizer⁻¹ ^ 2 := by
      apply Units.ext
      simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val,
        uniformizer_val, unitNeg4, Units.val_mk0, Units.val_neg, Units.val_one]
      norm_num
    rw [hval]
    exact C.mul_mem hmem_n4 (Subgroup.pow_mem _ (Subgroup.inv_mem _ hmem_unif) 2)
  have hemb_neg1 : unitEmbed (-1 : ℤ_[2]ˣ) = (-1 : ℚ_[2]ˣ) := by
    apply Units.ext
    simp only [unitEmbed_val, Units.val_neg, Units.val_one, map_neg, map_one]
  have hemb_n3 : unitEmbed neg3Int = unitNeg3 := by
    apply Units.ext
    rw [unitEmbed_val, neg3Int_val,
      show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]
    simp only [unitNeg3, Units.val_mk0]; push_cast; ring
  -- valuation split: x = uniformizer^n * u, u a norm-1 unit
  set n := v2 x with hndef
  set u : ℚ_[2]ˣ := uniformizer ^ (-n) * x with hudef
  have hxu : x = uniformizer ^ n * u := by
    rw [hudef, ← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  have hu_norm : ‖(u : ℚ_[2])‖ = 1 := by
    have huval : (u : ℚ_[2]) = (2 : ℚ_[2]) ^ (-n) * (x : ℚ_[2]) := by
      rw [hudef, Units.val_mul, Units.val_zpow_eq_zpow_val, uniformizer_val]
    rw [huval, norm_mul, norm_zpow, Padic.norm_eq_zpow_neg_valuation x.ne_zero,
      show ‖(2 : ℚ_[2])‖ = (2 : ℝ)⁻¹ by
        rw [show (2 : ℚ_[2]) = ((2 : ℕ) : ℚ_[2]) by norm_num, Padic.norm_p]; norm_num,
      show (x : ℚ_[2]).valuation = n from rfl]
    push_cast
    rw [inv_zpow]
    exact inv_mul_cancel₀ (zpow_ne_zero _ (by norm_num : (2 : ℝ) ≠ 0))
  obtain ⟨u₂, hu₂⟩ := norm_one_unit u hu_norm
  obtain ⟨s₂, hs₂cases, w, hw⟩ := mod8_sq u₂
  have hs_mem : unitEmbed s₂ ∈ C := by
    rcases hs₂cases with rfl | rfl | rfl | rfl
    · rw [map_one]; exact one_mem C
    · rw [hemb_neg1]; exact hmem_neg1
    · rw [hemb_n3]; exact hmem_n3
    · rw [show (-neg3Int : ℤ_[2]ˣ) = (-1) * neg3Int from (neg_one_mul neg3Int).symm,
        map_mul, hemb_neg1, hemb_n3]
      exact C.mul_mem hmem_neg1 hmem_n3
  refine ⟨uniformizer ^ n * unitEmbed s₂,
    C.mul_mem (Subgroup.zpow_mem _ hmem_unif n) hs_mem, unitEmbed w, ?_⟩
  rw [hxu, ← hu₂, hw, map_mul, map_pow, mul_assoc]

/-- **Lemma 3.5, injectivity clause**: the pair `(ν_ur, χ_D) : B → ℤ₂ × ℤ₂ˣ` is injective.
Stated intrinsically on `B = D₀^{ab}`: any continuous pair with the eq. (13) rows on the
marked generator classes separates points.  (The rows pin `ν, χ` on a dense subgroup, hence
everywhere, so this *is* the paper's clause.)  Proof ticket P-07 — from `b_decomposition`
plus `v₂(η − 1) = 2` (`η = (−3)⁻¹` topologically generates `1 + 4ℤ₂`). -/
theorem lemma_3_5_injective
    (ν : topAbelianization D0 →* Multiplicative ℤ_[2]) (hν : Continuous ν)
    (χ : topAbelianization D0 →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (hνA : ν (abMk d0A) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2]))
    (hνS : ν (abMk d0S) = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]))
    (hνY : ν (abMk d0Y) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2]))
    (hχA : χ (abMk d0A) = -1)
    (hχS : χ (abMk d0S) = 1)
    (hχY : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → χ (abMk d0Y) = y⁻¹) :
    ∀ x y : topAbelianization D0, ν x = ν y → χ x = χ y → x = y := by
  -- naturality of ν, χ w.r.t. `zpowZtwo`
  have hνnat : ∀ (x : topAbelianization D0) (u : ℤ_[2]),
      ν (zpowZtwo isProP_two_topAb_D0 x u)
        = zpowZtwo PropOneOne.isProP_two_multPadicInt (ν x) u := fun x u =>
    map_zpowZtwo isProP_two_topAb_D0 PropOneOne.isProP_two_multPadicInt
      (⟨ν, hν⟩ : ContinuousMonoidHom (topAbelianization D0) (Multiplicative ℤ_[2])) x u
  have hχnat : ∀ (x : topAbelianization D0) (u : ℤ_[2]),
      χ (zpowZtwo isProP_two_topAb_D0 x u)
        = zpowZtwo isProP_two_unitsPadicInt (χ x) u := fun x u =>
    map_zpowZtwo isProP_two_topAb_D0 isProP_two_unitsPadicInt
      (⟨χ, hχ⟩ : ContinuousMonoidHom (topAbelianization D0) ℤ_[2]ˣ) x u
  -- the class `y₀ = -3`
  obtain ⟨y₀, hy₀⟩ : ∃ y₀ : ℤ_[2]ˣ, (y₀ : ℤ_[2]) = -3 :=
    ⟨(isUnit_intCast_of_odd (show Odd (-3 : ℤ) by decide)).unit, by
      rw [IsUnit.unit_spec]; push_cast; ring⟩
  have hχY' : χ (abMk d0Y) = y₀⁻¹ := hχY y₀ hy₀
  have hsq : (-1 : ℤ_[2]ˣ) ^ 2 = 1 := by rw [pow_two, ← Units.val_eq_one]; push_cast; ring
  -- mod-4 fact: `η ^ w ≡ 1 (mod 4)` for all `w`
  letI : TopologicalSpace (ZMod 4) := ⊥
  letI : DiscreteTopology (ZMod 4) := ⟨rfl⟩
  have hcont_toZMod : Continuous (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] → ZMod 4) := by
    rw [continuous_def]; intro T _; exact isOpen_preimage_toZModPow 2 T
  have hy0mod : (PadicInt.toZModPow (p := 2) 2 ((y₀ : ℤ_[2])) : ZMod 4) = 1 := by
    rw [hy₀, show (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) by push_cast; ring, map_intCast]; decide
  have hinv_mod : (PadicInt.toZModPow (p := 2) 2 ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) : ZMod 4) = 1 := by
    have hmul : ((y₀⁻¹ : ℤ_[2]ˣ) : ℤ_[2]) * ((y₀ : ℤ_[2]ˣ) : ℤ_[2]) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have h := congrArg (PadicInt.toZModPow (p := 2) 2) hmul
    rw [map_mul, map_one, hy0mod, mul_one] at h
    exact h
  have hmod4 : ∀ w : ℤ_[2],
      (PadicInt.toZModPow (p := 2) 2
        ((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ w : ℤ_[2]ˣ) : ℤ_[2])) = 1 := by
    set f : Multiplicative ℤ_[2] →* ZMod 4 :=
      (PadicInt.toZModPow (p := 2) 2 : ℤ_[2] →+* ZMod 4).toMonoidHom.comp
        ((Units.coeHom ℤ_[2]).comp
          (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).toMonoidHom) with hfdef
    have hfcont : Continuous f :=
      hcont_toZMod.comp (Units.continuous_val.comp
        (zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹).continuous_toFun)
    have hf1 : f = (1 : Multiplicative ℤ_[2] →* ZMod 4) := by
      refine multPadicIntHom_ext hfcont continuous_const ?_
      show PadicInt.toZModPow (p := 2) 2
        ((zpowZtwoHom isProP_two_unitsPadicInt y₀⁻¹ (ofAdd (1 : ℤ_[2])) : ℤ_[2]ˣ) : ℤ_[2]) = 1
      rw [zpowZtwoHom_ofAdd_one]; exact hinv_mod
    intro w
    have hw := DFunLike.congr_fun hf1 (ofAdd w)
    rw [MonoidHom.one_apply] at hw
    exact hw
  -- main reduction
  suffices hkey : ∀ z : topAbelianization D0, ν z = 1 → χ z = 1 → z = 1 by
    intro x y hxy hxy'
    have hz : x * y⁻¹ = 1 :=
      hkey _ (by rw [map_mul, map_inv, hxy, mul_inv_cancel])
        (by rw [map_mul, map_inv, hxy', mul_inv_cancel])
    exact mul_inv_eq_one.mp hz
  intro z hνz hχz
  obtain ⟨a, s, y, rfl⟩ := D0ab_coord z
  -- ν gives `s = 2a`
  rw [map_mul, map_mul, hνnat, hνnat, hνnat, hνA, hνS, hνY] at hνz
  have harith : ((-2 : ℤ) : ℤ_[2]) * a + ((1 : ℤ) : ℤ_[2]) * s + ((0 : ℤ) : ℤ_[2]) * y = 0 := by
    rw [zpowZtwo_ofAdd, zpowZtwo_ofAdd, zpowZtwo_ofAdd, ← ofAdd_add, ← ofAdd_add,
      show (1 : Multiplicative ℤ_[2]) = ofAdd (0 : ℤ_[2]) from (ofAdd_zero).symm] at hνz
    exact Multiplicative.ofAdd.injective hνz
  have hs : s = 2 * a := by push_cast at harith; linear_combination harith
  -- χ gives `(-1)^r * η^y = 1`
  rw [map_mul, map_mul, hχnat, hχnat, hχnat, hχA, hχS, hχY', zpowZtwo_one_base, mul_one,
    zpowZtwo_of_sq_eq_one isProP_two_unitsPadicInt (-1) hsq a] at hχz
  -- `r ∈ {0,1}`
  have hrlt : (PadicInt.toZModPow (p := 2) 1 a).val < 2 := by
    have h := ZMod.val_lt (PadicInt.toZModPow (p := 2) 1 a)
    simpa using h
  -- `t = Ā · S̄²` is 2-torsion; rewrite `z`
  have hcommP : abMk (commP d0S d0Y) = 1 := by
    rw [commP, map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (abMk d0S)⁻¹ (abMk d0Y)⁻¹]
    group
  have hrel : (abMk d0A) ^ 2 * (abMk d0S) ^ 4 = 1 := by
    have h2 : abMk (d0A ^ 2 * d0S ^ 4 * commP d0S d0Y) = 1 := by rw [d0_relation]; exact map_one abMk
    rw [map_mul, map_mul, map_pow, map_pow, hcommP, mul_one] at h2
    exact h2
  set t : topAbelianization D0 := abMk d0A * zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2 with htdef
  have ht2 : t ^ 2 = 1 := by
    rw [htdef, mul_pow, pow_two (zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2), ← zpowZtwo_add,
      show (2 : ℤ_[2]) + 2 = ((4 : ℕ) : ℤ_[2]) by push_cast; ring, zpowZtwo_natCast]
    exact hrel
  have hz_eq : zpowZtwo isProP_two_topAb_D0 (abMk d0A) a
      * zpowZtwo isProP_two_topAb_D0 (abMk d0S) (2 * a)
      = zpowZtwo isProP_two_topAb_D0 t a := by
    rw [← zpowZtwo_zpowZtwo isProP_two_topAb_D0 (abMk d0S) 2 a, ← zpowZtwo_mul_base]
  -- case split on `r`
  rcases (by omega : (PadicInt.toZModPow (p := 2) 1 a).val = 0
      ∨ (PadicInt.toZModPow (p := 2) 1 a).val = 1) with hr0 | hr1
  · -- `r = 0`: `η^y = 1 ⟹ y = 0`, and `t^a = t^0 = 1`
    rw [hr0, pow_zero, one_mul] at hχz
    have hy0 : y = 0 :=
      (zpowZtwo_injective_neg_three_inv y₀ hy₀) (by rw [hχz, zpowZtwo_zero])
    rw [hs, hz_eq, zpowZtwo_of_sq_eq_one isProP_two_topAb_D0 t ht2 a, hy0, zpowZtwo_zero,
      mul_one, hr0, pow_zero]
  · -- `r = 1`: contradiction, `η^y = -1 ∉ 1 + 4ℤ₂`
    exfalso
    rw [hr1, pow_one] at hχz
    have hXval : ((zpowZtwo isProP_two_unitsPadicInt y₀⁻¹ y : ℤ_[2]ˣ) : ℤ_[2]) = -1 := by
      have h := congrArg Units.val hχz
      rw [Units.val_mul, Units.val_neg, Units.val_one, neg_one_mul] at h
      linear_combination -h
    have hbad := hmod4 y
    rw [hXval, map_neg, map_one] at hbad
    exact absurd hbad (by decide)


section MarkedAb

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- `(G_ℚ₂(2))^ab` is pro-2 (image of the pro-2 `G_ℚ₂(2)` under `abMk`). -/
theorem isProP_two_topAb_maxProP2 :
    IsProP 2 (topAbelianization (maxProPQuotient 2 AbsGalQ2)) :=
  isProP_of_surjective abMk continuous_abMk abMk_surjective isProP_maxProPQuotient

/-- The descent `π : G_ℚ₂^ab → (G_ℚ₂(2))^ab` of `abMk ∘ maxProPMk` through `toAb`.  Abelian
target ⇒ all lifts of a class agree (`markedPi_toAb`). -/
noncomputable def markedPi :
    AbsGalQ2ab →* topAbelianization (maxProPQuotient 2 AbsGalQ2) :=
  QuotientGroup.lift commClosure (abMk.comp (maxProPMk 2 AbsGalQ2).toMonoidHom) (by
    refine Subgroup.topologicalClosure_minimal _
      (Abelianization.commutator_subset_ker _) ?_
    have hset : ((abMk.comp (maxProPMk 2 AbsGalQ2).toMonoidHom).ker : Set AbsGalQ2)
        = (fun g => abMk (maxProPMk 2 AbsGalQ2 g)) ⁻¹' {1} := by
      ext x
      simp only [SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage, Set.mem_singleton_iff,
        MonoidHom.comp_apply]
      rfl
    rw [hset]
    exact isClosed_singleton.preimage
      (continuous_abMk.comp (maxProPMk 2 AbsGalQ2).continuous_toFun))

@[simp] lemma markedPi_toAb (g : AbsGalQ2) :
    markedPi (toAb g) = abMk (maxProPMk 2 AbsGalQ2 g) := rfl

/-- The marked hom `D₀^ab → (G_ℚ₂(2))^ab`, `Ā,S̄,Ȳ ↦ rec(−4), rec(1/2), rec(−3)`.  Well-defined:
`rec(−4)²·rec(1/2)⁴ = rec((−4)²·2⁻⁴) = rec(1) = 1`. -/
noncomputable def markedHom (R : LocalReciprocity) :
    ContinuousMonoidHom (topAbelianization D0) (topAbelianization (maxProPQuotient 2 AbsGalQ2)) :=
  abLift (d0LiftHom isProP_two_topAb_maxProP2
    ![markedPi (R.recip unitNeg4), (markedPi (R.recip uniformizer))⁻¹, markedPi (R.recip unitNeg3)]
    (by
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons]
      set f : ℚ_[2]ˣ →* topAbelianization (maxProPQuotient 2 AbsGalQ2) :=
        markedPi.comp R.recip with hf
      show f unitNeg4 ^ 2 * ((f uniformizer)⁻¹) ^ 4 * commP ((f uniformizer)⁻¹) (f unitNeg3) = 1
      have hc : commP ((f uniformizer)⁻¹) (f unitNeg3) = 1 := by
        rw [commP, mul_comm ((f uniformizer)⁻¹)⁻¹ (f unitNeg3)⁻¹]; group
      have hu : unitNeg4 ^ 2 * (uniformizer ^ 4)⁻¹ = 1 := by
        apply Units.ext
        push_cast [unitNeg4, uniformizer]
        norm_num
      rw [hc, mul_one, inv_pow, ← map_pow, ← map_pow, ← map_inv, ← map_mul, hu, map_one]))

@[simp] lemma markedHom_A (R : LocalReciprocity) :
    markedHom R (abMk d0A) = markedPi (R.recip unitNeg4) := by
  rw [markedHom, abLift_abMk, d0LiftHom_A]; rfl

@[simp] lemma markedHom_S (R : LocalReciprocity) :
    markedHom R (abMk d0S) = (markedPi (R.recip uniformizer))⁻¹ := by
  rw [markedHom, abLift_abMk, d0LiftHom_S]; rfl

@[simp] lemma markedHom_Y (R : LocalReciprocity) :
    markedHom R (abMk d0Y) = markedPi (R.recip unitNeg3) := by
  rw [markedHom, abLift_abMk, d0LiftHom_Y]; rfl

/-! #### `markedHom` is bijective (the two coordinate descents + density) -/

/-- `ν̃ : (G_ℚ₂(2))^ab → ℤ₂`, the descent of the unramified coordinate `ν_ur`. -/
noncomputable def nuT (R : LocalReciprocity) :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient 2 AbsGalQ2)) (Multiplicative ℤ_[2]) :=
  abLiftG (PropOneOne.nuUrBar R)

/-- `χ̃ : (G_ℚ₂(2))^ab → ℤ₂ˣ`, the descent of the cyclotomic character (via the max-pro-2 UP). -/
noncomputable def chiT (R : LocalReciprocity) :
    ContinuousMonoidHom (topAbelianization (maxProPQuotient 2 AbsGalQ2)) ℤ_[2]ˣ :=
  abLiftG ((maxProPHomEquiv isProP_two_unitsPadicInt).symm ⟨chiCyc, continuous_chiCyc⟩)

lemma nuT_markedPi (R : LocalReciprocity) (x : AbsGalQ2ab) :
    nuT R (markedPi x) = R.nu_ur x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show nuT R (markedPi (toAb g)) = R.nu_ur (toAb g)
  rw [markedPi_toAb, nuT, abLiftG_abMk, PropOneOne.nuUrBar_maxProPMk]

lemma chiT_markedPi (R : LocalReciprocity) (x : AbsGalQ2ab) :
    chiT R (markedPi x) = chiCycAb x := by
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  show chiT R (markedPi (toAb g)) = chiCycAb (toAb g)
  rw [markedPi_toAb, chiT, abLiftG_abMk, maxProPHomEquiv_symm_apply_maxProPMk, chiCycAb_toAb]
  rfl

/-- **`markedHom` is injective** — the two coordinate descents `(ν̃, χ̃)` compose with `markedHom`
to the six generator values of the already-proved `lemma_3_5_injective`. -/
theorem markedHom_injective (R : LocalReciprocity) : Function.Injective (markedHom R) := by
  set ν : topAbelianization D0 →* Multiplicative ℤ_[2] :=
    (nuT R).toMonoidHom.comp (markedHom R).toMonoidHom with hνdef
  set χ : topAbelianization D0 →* ℤ_[2]ˣ :=
    (chiT R).toMonoidHom.comp (markedHom R).toMonoidHom with hχdef
  have hνcont : Continuous ν := (nuT R).continuous_toFun.comp (markedHom R).continuous_toFun
  have hχcont : Continuous χ := (chiT R).continuous_toFun.comp (markedHom R).continuous_toFun
  have hνA : ν (abMk d0A) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2]) := by
    show nuT R (markedHom R (abMk d0A)) = _
    rw [markedHom_A, nuT_markedPi]; exact nu_ur_recip_neg4 R
  have hνS : ν (abMk d0S) = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2]) := by
    show nuT R (markedHom R (abMk d0S)) = _
    rw [markedHom_S, map_inv, nuT_markedPi, nu_ur_recip_uniformizer, ← ofAdd_neg,
      show -((-1 : ℤ) : ℤ_[2]) = ((1 : ℤ) : ℤ_[2]) from by push_cast; ring]
  have hνY : ν (abMk d0Y) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2]) := by
    show nuT R (markedHom R (abMk d0Y)) = _
    rw [markedHom_Y, nuT_markedPi]; exact nu_ur_recip_neg3 R
  have hχA : χ (abMk d0A) = -1 := by
    show chiT R (markedHom R (abMk d0A)) = _
    rw [markedHom_A, chiT_markedPi]; exact chiCyc_recip_neg4 R
  have hχS : χ (abMk d0S) = 1 := by
    show chiT R (markedHom R (abMk d0S)) = _
    rw [markedHom_S, map_inv, chiT_markedPi, R.chiCyc_recip_uniformizer, inv_one]
  have hχY : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → χ (abMk d0Y) = y⁻¹ := by
    intro y hy
    show chiT R (markedHom R (abMk d0Y)) = _
    rw [markedHom_Y, chiT_markedPi]; exact chiCyc_recip_neg3 R y hy
  intro x z hxz
  refine lemma_3_5_injective ν hνcont χ hχcont hνA hνS hνY hχA hχS hχY x z ?_ ?_
  · show nuT R (markedHom R x) = nuT R (markedHom R z); rw [hxz]
  · show chiT R (markedHom R x) = chiT R (markedHom R z); rw [hxz]

lemma continuous_markedPi : Continuous (markedPi : AbsGalQ2ab → _) := by
  refine (QuotientGroup.isQuotientMap_mk commClosure).continuous_iff.mpr ?_
  have hfun : (markedPi ∘ (QuotientGroup.mk : AbsGalQ2 → AbsGalQ2ab))
      = fun g => abMk (maxProPMk 2 AbsGalQ2 g) := by
    funext g; exact markedPi_toAb g
  rw [hfun]
  exact continuous_abMk.comp (maxProPMk 2 AbsGalQ2).continuous_toFun

lemma markedPi_surjective : Function.Surjective (markedPi : AbsGalQ2ab → _) := by
  intro y
  obtain ⟨t, rfl⟩ := abMk_surjective y
  obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) t
  exact ⟨toAb g, markedPi_toAb g⟩

/-- **`markedHom` is surjective** — `markedPi ∘ rec` is dense, `ℚ₂ˣ = ⟨−4,2,−3⟩·(ℚ₂ˣ)²`
(`units_gen`), and a finite-2-group Frattini argument (`sq_generate`) makes the three `rec`-classes
generate every finite quotient of `(G_ℚ₂(2))^ab`; so their closed span is everything. -/
theorem markedHom_surjective (R : LocalReciprocity) : Function.Surjective (markedHom R) := by
  have hdense : DenseRange (markedPi ∘ R.recip) :=
    markedPi_surjective.denseRange.comp R.denseRange_recip continuous_markedPi
  set S : Subgroup (topAbelianization (maxProPQuotient 2 AbsGalQ2)) :=
    Subgroup.closure {markedPi (R.recip unitNeg4), markedPi (R.recip uniformizer),
      markedPi (R.recip unitNeg3)} with hSdef
  have hSrange : S ≤ (markedHom R).toMonoidHom.range := by
    rw [hSdef, Subgroup.closure_le]
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact ⟨abMk d0A, markedHom_A R⟩
    · exact ⟨(abMk d0S)⁻¹, by
        show markedHom R ((abMk d0S)⁻¹) = markedPi (R.recip uniformizer)
        rw [map_inv, markedHom_S, inv_inv]⟩
    · exact ⟨abMk d0Y, markedHom_Y R⟩
  have hUgen : ∀ U : OpenNormalSubgroup (topAbelianization (maxProPQuotient 2 AbsGalQ2)),
      S.map (QuotientGroup.mk' U.toSubgroup) = ⊤ := by
    intro U
    haveI hfin : Finite (topAbelianization (maxProPQuotient 2 AbsGalQ2) ⧸ U.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen _ U.isOpen'
    haveI hdisc : DiscreteTopology
        (topAbelianization (maxProPQuotient 2 AbsGalQ2) ⧸ U.toSubgroup) := by
      refine discreteTopology_of_isOpen_singleton_one ?_
      have hpre : (QuotientGroup.mk :
          topAbelianization (maxProPQuotient 2 AbsGalQ2) → _ ⧸ U.toSubgroup) ⁻¹' {1}
          = (U.toSubgroup : Set _) := by
        ext δ
        simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
          QuotientGroup.eq_one_iff]
      rw [← (QuotientGroup.isQuotientMap_mk U.toSubgroup).isOpen_preimage, hpre]
      exact U.isOpen'
    set q : ℚ_[2]ˣ →* _ :=
      (QuotientGroup.mk' U.toSubgroup).comp (markedPi.comp R.recip) with hqdef
    have hq_surj : Function.Surjective q := by
      have hcd : DenseRange ⇑q :=
        (QuotientGroup.mk'_surjective U.toSubgroup).denseRange.comp hdense continuous_coinduced_rng
      rw [← Set.range_eq_univ, ← hcd.closure_range, (isClosed_discrete _).closure_eq]
    rw [hSdef, MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
      Set.image_singleton]
    apply sq_generate (isProP_two_topAb_maxProP2 U)
    intro y
    obtain ⟨x, rfl⟩ := hq_surj y
    obtain ⟨s, hs, t, hst⟩ := units_gen x
    refine ⟨q s, ?_, q t, ?_⟩
    · have hmem : q s ∈ Subgroup.map q (Subgroup.closure {unitNeg4, uniformizer, unitNeg3}) :=
        Subgroup.mem_map_of_mem q hs
      rwa [MonoidHom.map_closure, Set.image_insert_eq, Set.image_insert_eq,
        Set.image_singleton] at hmem
    · rw [hst, map_mul, map_pow]
  have htop : S.topologicalClosure = ⊤ :=
    eq_top_of_forall_map_eq_top (Subgroup.isClosed_topologicalClosure S)
      (fun U => top_le_iff.mp
        ((hUgen U).ge.trans (Subgroup.map_mono (Subgroup.le_topologicalClosure S))))
  refine MonoidHom.range_eq_top.mp (top_le_iff.mp ?_)
  rw [← htop]
  exact Subgroup.topologicalClosure_minimal _ hSrange
    (by rw [MonoidHom.coe_range]; exact (isCompact_range (markedHom R).continuous_toFun).isClosed)

/-- **The marked abelianization is bijective** (Lemma 3.5's last clause).  Injective via the two
coordinate descents + `lemma_3_5_injective`; surjective via density of `markedPi ∘ rec` and the
square-class generation `units_gen`.  Std-3 + B5 — *no census cost* (B5 as bundled suffices). -/
theorem markedHom_bijective (R : LocalReciprocity) : Function.Bijective (markedHom R) :=
  ⟨markedHom_injective R, markedHom_surjective R⟩

/-- **Lemma 3.5, marked-abelianization clause**: the pro-2 abelianization of `D = G_{ℚ₂}(2)`
is identified with `B = D₀^{ab}` by `Ā ↦ ā = rec(−4)`, `S̄ ↦ s̄ = rec(2)⁻¹ = rec(1/2)`,
`Ȳ ↦ ȳ = rec(−3)`.  The `rec`-classes live in `G^{ab}` (`R.recip`); the matching is quantified
over lifts `g ∈ G_{ℚ₂}` (all lifts agree via `markedPi`, an abelian descent).  **Proved modulo
`markedHom_bijective`** (the sole census-gated gap; ticket P-07, `Ax = B5`). -/
theorem lemma_3_5_marked_abelianization (R : LocalReciprocity) :
    ∃ e : ContinuousMulEquiv (topAbelianization D0)
      (topAbelianization (maxProPQuotient 2 AbsGalQ2)),
      (∀ g : AbsGalQ2, toAb g = R.recip unitNeg4 →
        e (abMk d0A) = abMk (maxProPMk 2 AbsGalQ2 g)) ∧
      (∀ g : AbsGalQ2, toAb g = (R.recip uniformizer)⁻¹ →
        e (abMk d0S) = abMk (maxProPMk 2 AbsGalQ2 g)) ∧
      (∀ g : AbsGalQ2, toAb g = R.recip unitNeg3 →
        e (abMk d0Y) = abMk (maxProPMk 2 AbsGalQ2 g)) := by
  refine ⟨continuousMulEquivOfBijective (markedHom R) (markedHom_bijective R), ?_, ?_, ?_⟩
  · intro g hg
    show markedHom R (abMk d0A) = _
    rw [markedHom_A, ← markedPi_toAb, hg]
  · intro g hg
    show markedHom R (abMk d0S) = _
    rw [markedHom_S, ← markedPi_toAb, hg, map_inv]
  · intro g hg
    show markedHom R (abMk d0Y) = _
    rw [markedHom_Y, ← markedPi_toAb, hg]

end MarkedAb

open HilbertSymbol in
/-- **Lemma 3.5, Hilbert-symbol ledger** (the "initial form" clause in symbol vocabulary):
on the square-class basis `(−1, 2, −3)` of Lemma 3.5, the dyadic Hilbert symbol takes the
values `(−1,−1)₂ = −1`, `(2,−3)₂ = −1`, and `+1` on every other (unordered) pair.  In the
dual basis `(α, β, γ)` of `H¹(D, 𝔽₂)` this is exactly the quadratic initial form
`α² + βγ + γβ` — the degree-two initial form of `r₀ = A²S⁴[S,Y]` (design note §3.5 for the
dictionary; the Kummer-cocycle cup reading enters at §6, tickets P-14/P-15).
(Proof ticket P-07, `Ax = B7′`: six evaluations of `hilbertSymbol_dyadic`.) -/
theorem lemma_3_5_hilbert_ledger :
    hilbertSymbol (unitCoe (-1)) (unitCoe (-1)) = -1 ∧
    (∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → hilbertSymbol unit2 (unitCoe y) = -1) ∧
    hilbertSymbol (unitCoe (-1)) unit2 = 1 ∧
    (∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → hilbertSymbol (unitCoe (-1)) (unitCoe y) = 1) ∧
    hilbertSymbol unit2 unit2 = 1 ∧
    (∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → hilbertSymbol (unitCoe y) (unitCoe y) = 1) := by
  have eps_neg3 : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → ε y = 0 := by
    intro y hy
    rw [ε, hy]
    have : (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) := by push_cast; ring
    rw [this, map_intCast]; decide
  have omega_neg3 : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → ω y = 1 := by
    intro y hy
    rw [ω, hy]
    have : (-3 : ℤ_[2]) = ((-3 : ℤ) : ℤ_[2]) := by push_cast; ring
    rw [this, map_intCast]; decide
  have eps_one : ε (1 : ℤ_[2]ˣ) = 0 := by rw [ε, Units.val_one, map_one]; decide
  have omega_one : ω (1 : ℤ_[2]ˣ) = 0 := by rw [ω, Units.val_one, map_one]; decide
  have unitCoe_one : unitCoe 1 = 1 := by rw [unitCoe, map_one]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `(−1, −1)₂ = −1`
    have h := hilbertSymbol_dyadic 0 0 (-1) (-1)
    rw [zpow_zero, one_mul] at h
    rw [h, ε_neg_one, ω_neg_one]; decide
  · -- `(2, −3)₂ = −1`
    intro y hy
    have h := hilbertSymbol_dyadic 1 0 1 y
    rw [zpow_one, unitCoe_one, mul_one, zpow_zero, one_mul] at h
    rw [h, eps_one, omega_neg3 y hy]
    simp only [Int.cast_one, Int.cast_zero, zero_mul, one_mul, add_zero, zero_add]
    decide
  · -- `(−1, 2)₂ = 1`
    have h := hilbertSymbol_dyadic 0 1 (-1) 1
    rw [zpow_zero, one_mul, zpow_one, unitCoe_one, mul_one] at h
    rw [h, eps_one, ω_neg_one, omega_one]
    simp only [Int.cast_one, Int.cast_zero, mul_zero, add_zero]
    decide
  · -- `(−1, −3)₂ = 1`
    intro y hy
    have h := hilbertSymbol_dyadic 0 0 (-1) y
    simp only [zpow_zero, one_mul] at h
    rw [h, ε_neg_one, eps_neg3 y hy]
    simp only [Int.cast_zero, zero_mul, mul_zero, add_zero]
    decide
  · -- `(2, 2)₂ = 1`
    have h := hilbertSymbol_dyadic 1 1 1 1
    rw [zpow_one, unitCoe_one, mul_one] at h
    rw [h, eps_one, omega_one]
    simp only [Int.cast_one, mul_zero, add_zero]
    decide
  · -- `(−3, −3)₂ = 1`
    intro y hy
    have h := hilbertSymbol_dyadic 0 0 y y
    rw [zpow_zero, one_mul] at h
    rw [h, eps_neg3 y hy]
    simp only [Int.cast_zero, zero_mul, mul_zero, add_zero]
    decide

/-! ## Lemma 3.7 and Proposition 3.8 — lifting automorphisms of `(B, χ₀)`

Phrased against a `BDecomposition` coordinate system.  A continuous group isomorphism of
pro-2 abelian groups is automatically `ℤ₂`-linear, so the coordinate transcriptions below
are exactly the paper's `ℤ₂`-module statements (design note §3.7–3.8). -/

/- **Lemma 3.7 (square-root and HNN lifting)** is stated and **proved** in
`GQ2/AnabelianBridge.lean` (`GQ2.SectionThree.lemma_3_7`, ticket P-08, `Ax = B8`) — declared
there because its proof needs the anabelian bridge (B8's peripheral identity pushed along
`Δ → D₀`), which imports this file; same namespace, per the P-09 precedent (`GQ2/Prop32.lean`). -/

/- **Proposition 3.8, lifting half** is stated and **proved** in `GQ2/AnabelianBridge.lean`
(`GQ2.SectionThree.prop_3_8_lift`, ticket P-08, `Ax = B8`): `Ψ_u` composed with the shear
`Θ_{b'}` of paper (19). -/

/- **Proposition 3.8, classification half** is stated and **proved** in
`GQ2/AnabelianBridge.lean` (`GQ2.SectionThree.prop_3_8_classification`, ticket P-08,
axiom-free): `ker χ₀ = ℤ₂S̄`, the torsion subgroup is `⟨t⟩`, and `η`-injectivity
(P-21 (iii)) — pure (11) module algebra over this file's `D0ab_coord` toolkit. -/

/-! ## Proposition 1.1 — the marked dyadic Demushkin normalization

Paper: *"There exist topological generators `a, s, y` of `D = G_{ℚ₂}(2)` with
`D ≅ ⟨a,s,y | a²s⁴[s,y] = 1⟩_{pro-2}` and `ν_ur(a,s,y) = (−2,1,0)`."*  The generators-plus-
presentation clause is packaged as a continuous isomorphism `e : G_{ℚ₂}(2) ≅ D₀` (then
`a = e⁻¹(A)`, `s = e⁻¹(S)`, `y = e⁻¹(Y)` topologically generate and satisfy the relation, by
transport of `d0_relation`); the `ν_ur`-row is read through arbitrary lifts to `G_{ℚ₂}`, as
in the T-11 full-group readings (`chiCyc_eq_neg_one_of_lift_A`). -/

/- **Proposition 1.1** (proof ticket P-10) is stated and **proved** in
`GQ2/PropOneOneAssembly.lean` (`GQ2.SectionThree.prop_1_1`): a marked isomorphism
`G_{ℚ₂}(2) ≅ D₀` with unramified coordinates `ν_ur(a, s, y) = (−2, 1, 0)`.  It composes B3c
(`orientBundle.equiv`) with Lemma 3.5 (`lemma_3_5_marked_abelianization`) and Prop. 3.8
(`prop_3_8_classification`/`prop_3_8_lift`), and so inherits Lemma 3.5's sole census-gated gap
`markedHom_bijective`.  Declared in that downstream file (P-09 precedent: it imports the P-08
`AnabelianBridge` layer, which imports this file). -/

end SectionThree

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (13) = ⟦eq-localmarkingorientation⟧
  * eq. (7) = ⟦eq-candidateinverse⟧
  * Lemma 3.1 = ⟦lem-tamefinite⟧
  * Lemma 3.3 = ⟦lem-o2tame⟧
  * Lemma 3.4 = ⟦lem-standardorientation⟧
  * Lemma 3.5 = ⟦lem-markedinitialform⟧
  * Lemma 3.6 = ⟦lem-peripheralpower⟧ (= lemma 3.7 in current tex)
  * Lemma 3.7 = ⟦lem-squarerootHNN⟧ (= lemma 3.8 in current tex)
  * Proposition 1.1 = ⟦prop-markedDem⟧
  * Prop 3.2 = ⟦prop-tamequotient⟧
  * Prop 3.8 = ⟦prop-orientationlift⟧ (= proposition 3.9 in current tex)
-/
