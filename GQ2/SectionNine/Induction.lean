/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.SectionNine.Terminal

/-!
# The terminal and recursive regimes of the Section 9 induction

The terminal count, κ⁰ base class, recursion frame, and recursion solver.

See `GQ2.SectionNine` for the paper-facing overview, source citations, and deviations.
-/

namespace GQ2

open SectionEight QuadraticFp2

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

namespace SectionNine

/-! ## The terminal regime -/

/-- **The terminal case** (§9.1): if every chief factor of `L_Y` is scalar (a trivial
`H`-module — `IsScalarStack`), the two exact-image problems are *identical*: Lemma 9.2
splits `Y ≅ H ×_{H₂} Q` off the odd part of `H` (Schur–Zassenhaus,
`GQ2.FiniteGroup.oddOrder_twoQuotient_split`), the boundary data descend to the finite
2-group `Q` (`θ` kills the odd complement since `E` has exponent 2), and the (144)
correspondence + `coprime_fiber_product` identify boundary-framed maps from either source
with marked maps `Π → Q` — the same set for both sources by the marked pro-2 isomorphisms. -/
theorem terminal_count_eq (B : BoundaryMaps) (F : BoundaryFrame H E)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1)
    (hstack : SectionSeven.IsScalarStack T.LY) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  obtain ⟨M, hMn, hModd, hMtwo⟩ := head_two_nilpotent F
  obtain ⟨Ntil, hNn, hNodd, hNQ2, hNL, _hNcomm, hmapM, hNLsup⟩ :=
    lemma_9_2_core T.piY T.piY_surjective T.LY T.ker_piY T.isPGroup_two hstack M hModd hMtwo
  set D : L92 H Y := ⟨T.piY, T.piY_surjective, T.LY, T.ker_piY, M, hMn, hModd, Ntil, hNn,
    hNodd, hNL, hmapM, hNLsup, hNQ2⟩ with hD
  have hDpi : D.piY = T.piY := by rw [hD]
  have hbA : Function.Surjective B.bA := fun x => by
    obtain ⟨g, hg⟩ := B.surjA x
    exact ⟨g, Subtype.ext (by rw [B.bA_apply_coe]; exact congrArg Subtype.val hg)⟩
  have hbF : Function.Surjective B.bF := fun x => by
    obtain ⟨g, hg⟩ := B.surjF x
    exact ⟨g, Subtype.ext (by rw [B.bF_apply_coe]; exact congrArg Subtype.val hg)⟩
  have hbpro2A : ∀ g, (B.bA g).val.2 = B.pro2A g := fun g => by rw [B.bA_apply_coe]
  have hbpro2F : ∀ g, (B.bF g).val.2 = B.pro2F g := fun g => by rw [B.bF_apply_coe]
  have hpro2A_surj : Function.Surjective B.pro2A := fun p => by
    obtain ⟨t, ht⟩ := SectionThree.nuT_surjective (nuTwo p)
    obtain ⟨g, hg⟩ := B.surjA ⟨(t, p), ht⟩
    exact ⟨g, congrArg (fun x : ↥boundarySubgroup => x.val.2) hg⟩
  show Nat.card (BoundaryLifts B.bA F T) = Nat.card (BoundaryLifts B.bF F T)
  calc Nat.card (BoundaryLifts B.bA F T)
      = Nat.card (QLifts F T hE2 D B.bA) := boundaryLifts_equiv_qlifts F T hE2 D hDpi B.bA hbA
    _ = Nat.card (CommonLifts F T hE2 D) :=
        qlifts_equiv_commonLifts F T hE2 D B.bA hbA B.pro2A hpro2A_surj hbpro2A (ker_pro2A B)
    _ = Nat.card (QLifts F T hE2 D B.bF) :=
        (qlifts_equiv_commonLifts F T hE2 D B.bF hbF B.pro2F B.pro2F_surjective hbpro2F
          B.ker_pro2F).symm
    _ = Nat.card (BoundaryLifts B.bF F T) :=
        (boundaryLifts_equiv_qlifts F T hE2 D hDpi B.bF hbF).symm

/-! ## The κ⁰ base class

### Reusable structural core (the Lemma 6.3 skeleton)

The paper's *existence* proof for the base class `κ⁰_q` is **Lemma 6.3**, not Lemma 6.1
(Lemma 6.1 only records the equivalence "(59)+(60) ⟺ `E_f` carries a lifted `C`-action" and
*assumes* a lift is chosen).  Lemma 6.3 builds the datum for a **simple self-dual tame** module
`V` by three structural moves, each of which is a self-contained, source-generic fact proved
here; see `docs/orchestration/p17e-kappa0-scoping.md` for why the *general* `kappa0_exists` below is **not**
a paper theorem (the lift obstruction in `H²(C, V^∨)` need not vanish for an arbitrary module)
and for the honest restatement these lemmas assemble into.

* `isEquivariantFactorSet_of_invariant` — an **invariant** normalized factor set needs no
  corrections (`m = 0`): the paper's orbit factor sets (75)/(76).
* `IsEquivariantFactorSet.add` — the datum of a **sum** `q + q'` is the sum of the data: the
  "sum of the cocycles corresponding to the orbit polynomials occurring in `q_W`" step.
* `IsEquivariantFactorSet.comap` — **pullback** along an equivariant additive map (eq. (77)),
  packaged as `kappa0_exists_of_split` (the Lemma 6.3 reduction to a split embedding). -/


/-- **Pullback** of an equivariant factor-set datum along an equivariant additive map
`i : V →+ W` (eq. (77), datum level): if `i` is `C`-equivariant, then `dat.comap i` is an
equivariant factor-set datum for the pulled-back form `q ∘ i`. -/
theorem IsEquivariantFactorSet.comap {C V W : Type*} [Group C] [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction C V] [DistribMulAction C W] {q : W → ZMod 2} {dat : FactorSet C W}
    (hdat : IsEquivariantFactorSet q dat) (i : V →+ W)
    (hi : ∀ (c : C) (v : V), i (c • v) = c • i v) :
    IsEquivariantFactorSet (fun v => q (i v)) (dat.comap i) where
  f_cocycle v w x := by
    show dat.f (i (v + w)) (i x) + dat.f (i v) (i w) = dat.f (i v) (i (w + x)) + dat.f (i w) (i x)
    rw [map_add, map_add]; exact hdat.f_cocycle (i v) (i w) (i x)
  f_diag v := hdat.f_diag (i v)
  f_polar v w := by
    show dat.f (i v) (i w) + dat.f (i w) (i v) = polar (fun v => q (i v)) v w
    rw [hdat.f_polar (i v) (i w)]; simp only [polar, map_add]
  f_zero_left v := by
    show dat.f (i 0) (i v) = 0
    rw [map_zero]; exact hdat.f_zero_left (i v)
  f_zero_right v := by
    show dat.f (i v) (i 0) = 0
    rw [map_zero]; exact hdat.f_zero_right (i v)
  m_quad c v w := by
    show dat.m c (i (v + w)) + dat.m c (i v) + dat.m c (i w)
       = dat.f (i (c • v)) (i (c • w)) + dat.f (i v) (i w)
    rw [map_add, hi c v, hi c w]; exact hdat.m_quad c (i v) (i w)
  m_mul c d v := by
    show dat.m (c * d) (i v) = dat.m c (i (d • v)) + dat.m d (i v)
    rw [hi d v]; exact hdat.m_mul c d (i v)
  m_one v := hdat.m_one (i v)

/-- **Pullback of an equivariant factor-set datum along a group homomorphism** `π : C →* D`
compatible with the actions (`c • v = π c • v`): `f` is unchanged, `m_c := m_{π c}`.  This is
the reduction of the κ⁰ existence problem to any group the action factors through — e.g. the
faithful tame image of `ActsThroughTame` below (existence over the image gives existence over
`C`), which is how Lemma 6.3's "let `H = H_V` be the faithful tame image" step enters. -/
theorem IsEquivariantFactorSet.comapHom {C D V : Type*} [Group C] [Group D] [AddCommGroup V]
    [DistribMulAction C V] [DistribMulAction D V] {q : V → ZMod 2} {dat : FactorSet D V}
    (hdat : IsEquivariantFactorSet q dat) (π : C →* D)
    (hπ : ∀ (c : C) (v : V), c • v = π c • v) :
    IsEquivariantFactorSet q (⟨dat.f, fun c v => dat.m (π c) v⟩ : FactorSet C V) where
  f_cocycle := hdat.f_cocycle
  f_diag := hdat.f_diag
  f_polar := hdat.f_polar
  f_zero_left := hdat.f_zero_left
  f_zero_right := hdat.f_zero_right
  m_quad c v w := by
    show dat.m (π c) (v + w) + dat.m (π c) v + dat.m (π c) w
       = dat.f (c • v) (c • w) + dat.f v w
    rw [hπ c v, hπ c w]; exact hdat.m_quad (π c) v w
  m_mul c d v := by
    show dat.m (π (c * d)) v = dat.m (π c) (d • v) + dat.m (π d) v
    rw [map_mul, hπ d v]; exact hdat.m_mul (π c) (π d) v
  m_one v := by
    show dat.m (π 1) v = 0
    rw [map_one]; exact hdat.m_one v


/-- The `C`-action on `V` **factors through a finite tame group**: a finite `H` acting on `V`,
generated by a pair `s, t` with the tame relation `s⁻¹ t s = t²` (the finite avatar of a
`Ttame`-quotient, the same interface as `tame_two_nilpotent`), and a *surjective* `π : C →* H`
with `c • v = π c • v`.  Surjectivity makes `H`-data (invariance of `q`, submodule lattice)
agree with `C`-data, so an equivariant factor-set datum over `H` pulls back along
`IsEquivariantFactorSet.comapHom`.  At the §9 induction call site this is discharged with `H :=` the
frame head: `K` acts trivially on `V = P/S` by `[K,P] ≤ [P,P] ≤ S`, and the rest of `L_Y`
acts trivially by `FoxH.lemma_5_12` (normal 2-subgroup on a chief factor), so the `C = Y/K`
action descends to `Y/L_Y ≅ H`, whose marked generators satisfy the tame relation. -/
def ActsThroughTame (C : Type*) [Group C] (V : Type*) [AddCommGroup V]
    [DistribMulAction C V] : Prop :=
  ∃ (H : Type) (_ : Group H) (_ : Finite H) (_ : DistribMulAction H V)
    (π : C →* H) (s t : H),
    Function.Surjective π ∧ (∀ (c : C) (v : V), c • v = π c • v) ∧
    Subgroup.closure {s, t} = ⊤ ∧ s⁻¹ * t * s = t ^ 2

/-- Every element of `𝔽₂` is `0` or `1` (kernel-`decide`d at top level, where the context is
free of the `V`/`q` variables that would otherwise trip `decide`'s free-variable guard). -/
private theorem zmod_two_cases : ∀ b : ZMod 2, b = 0 ∨ b = 1 := by decide


/-! ### The orbit factor sets are equivariant (Lemma 6.3's (75)/(76))

The concrete `m = 0` orbit data from `GQ2/OrbitData.lean` are `IsEquivariantFactorSet` for their
square maps: biadditive in the coordinates, and `G/N`-invariant because the left-regular action
merely permutes coordinates (`finsum_comp_equiv` along `Equiv.mulLeft`).  Entry point:
`isEquivariantFactorSet_of_biadditive_invariant` (now polar-free). -/


/-- **Existence of the equivariant factor-set datum** (the base determinant class `κ⁰_q`) —
**the paper's Lemma 6.3**, p. 26: a `C`-invariant nonsingular quadratic form on a **simple tame**
`𝔽₂[C]`-module admits a normalized equivariant factor-set datum.  (Self-duality is implied:
`hns` + `hinv` make `v ↦ polar q v ·` a `C`-isomorphism `V ≅ V^∨`.)

**Encoding correction** (documented deviation: `docs/orchestration/p17e-kappa0-scoping.md`).  The earlier form
omitted `hsimple`/`htame`, making the statement
*stronger than the paper's* and in fact **false** — Lemma 6.1 only proves the equivalence
"(59)+(60) ⟺ `E_f` carries a lifted `C`-action" and *assumes* the lift exists; a datum is
exactly a splitting of `1 → V^∨ → Aut_Z(E_f) → O(q) → 1` pulled back along `ρ : C → O(q)`, and
for `C = O(q)` itself that extension is **non-split** for large extraspecial `E_f` (Griess,
Pacific J. Math. 48 (1973)).  The added hypotheses are Lemma 6.3's own, are dischargeable at the
sole call site (the §9 induction, see `ActsThroughTame`'s docstring), and restore truth via the paper's
construction: reduce to the faithful tame image (`comapHom`), split-embed `V` into a permutation
module (Lemma 6.11 / Maschke — projectivity is where simplicity+tameness are consumed), decompose
the extended form into orbit polynomials, and sum their explicit data ((75)/(76)/Lemma 6.2) —
the proved lemmas above are exactly these assembly steps.  The proof unpacks `htame`, transports
invariance and simplicity along the surjection, applies `GQ2.kappa0_exists_tame`
(`GQ2/KappaNormalForm.lean` — faithful-image reduction, the odd/unramified averaging branch,
and the ramified branch through `lemma_6_11_of_tame_pair` + the permutation-module normal
form), and pulls back with `comapHom`. -/
theorem kappa0_exists {C : Type} [Group C] [Finite C]
    {V : Type} [AddCommGroup V] [Finite V] [DistribMulAction C V]
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : IsInvariant C q) (hsimple : FoxH.IsSimpleModTwo C V)
    (htame : ActsThroughTame C V) :
    ∃ dat : FactorSet C V, IsEquivariantFactorSet q dat := by
  obtain ⟨H, hG, hF, hA, π, s, t, hπsurj, hπcompat, hgen, hrel⟩ := htame
  letI := hG
  letI := hF
  letI := hA
  -- transport invariance and simplicity along the surjection `π`
  have hinvH : IsInvariant H q := by
    intro h v
    obtain ⟨c, rfl⟩ := hπsurj h
    rw [← hπcompat, hinv]
  have hsimpleH : ∀ W : AddSubgroup V,
      (∀ (g : H) (w : V), w ∈ W → g • w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    refine hsimple.2 W fun g w hw => ?_
    rw [hπcompat]
    exact hW (π g) w hw
  obtain ⟨dat, hdat⟩ :=
    kappa0_exists_tame hgen hrel q hq hns hinvH hsimple.1 hsimpleH
  exact ⟨_, IsEquivariantFactorSet.comapHom hdat π hπcompat⟩

/-! ## The concrete block frame and enrichment

The §7 block `Blk` on a target `T` determines the recursion frame of §8 concretely:
`B = Y/R`, `C = Y/K` with the boundary data descended through `lemma_7_3` (this is where
`hE2` enters), `D_R` = the kernel-encoded scalar characters (`card_DR`'s subtype itself),
and the scalar covers `p_λ = Y/R' ↠ Y/R`.  The enrichment fields are the §7.4 outputs:
`q_λ` via `prop_7_4` + `mForm_of_qbar` (the Prop. 8.9 assembly), quadraticity/nonsingularity of `q̄_λ`
derived from the block (design routes in `docs/section9-extraction.md`), the descended
module from `GQ2/BlockModule.lean`'s `blockAction`, and the κ⁰ datum from `kappa0_exists`.
Spec and size lemmas about these constructions (the (145)/(148)/(153) bounds, Lemma 9.4)
are the §9 induction, stated per the design note. -/

/-- **The concrete recursion frame of the block** (the §9 induction).  `R = ⊥` is allowed (the frame
is then degenerate; the induction's `R = ⊥` lane uses `mStage_partition` instead of
`prop_8_9`). -/
noncomputable def blockFrame {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] (T : MarkedTarget H E Y) (Blk : SectionSeven.MinimalBlock T.LY)
    (hE2 : ∀ e : E, e ^ 2 = 1) : RecursionFrame T Blk :=
  blockFrameImpl T Blk hE2

/- **The concrete enrichment of the block frame** (the §9 induction): the per-`λ` §7.4 square-form data
and the descended κ⁰ datum, discharging `prop_8_9`'s `En` hypothesis.  **Defined in
`GQ2/BlockEnrichment.lean`** (`SectionNine.blockEnrichment`, the §9 induction) — it must sit downstream of
this file because it consumes `kappa0_exists`/`ActsThroughTame`; its signature gains
`F : BoundaryFrame H E` (supplying `cH := F.alpha` for `prop_7_4` and the tame generators for
`htame`).  Axiom-clean modulo `kappa0_exists` (the §9 induction). -/

/-! ## The elementary `M`-stage partition -/

/-- Stages (A)+(B) of `mStage_partition`: the boundary-lift set `Mset` (unrestricted `B`-lifts
whose `C`-projection is a boundary-framed surjection) fibres over its `C`-image, and the
`LiftsOver`-fibration collapses through the uniform multiplicity `hmult` to `mult · e_Γ(C)`. -/
private theorem mStage_Mset_card_eq_mult {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E) (mult : ℕ)
    (hmult : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (RF.LiftsOver b F ρ) = mult) :
    Nat.card {m : ContinuousMonoidHom Γ RF.YB //
        IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)}
      = mult * exactImageCount b F RF.TC := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (BoundaryLifts b F RF.TC) := finite_boundaryLifts b F RF.TC hfg
  haveI : Fintype (BoundaryLifts b F RF.TC) := Fintype.ofFinite _
  have hheadBC : RF.TC.piY.comp RF.piBC = RF.TB.piY := RF.headBC
  have hthetaBC : RF.TC.thetaY.comp RF.piBC = RF.TB.thetaY := RF.thetaBC
  set Mset := {m : ContinuousMonoidHom Γ RF.YB //
    IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)} with hMsetdef
  haveI : Finite Mset := Subtype.finite
  -- (A) the `LiftsOver`-fibration collapses by `hmult` (the `half139_of` pattern)
  have hmultsum : ∑ ρ : BoundaryLifts b F RF.TC, Nat.card (RF.LiftsOver b F ρ)
      = mult * exactImageCount b F RF.TC := by
    rw [Finset.sum_congr rfl (fun ρ _ => hmult ρ), Finset.sum_const, Finset.card_univ,
      smul_eq_mul, exactImageCount, Nat.card_eq_fintype_card]
    exact mul_comm _ _
  -- (B) `Mset` fibres over the `C`-image `ρ`, the fibre being `LiftsOver ρ`
  have eUnion : Nat.card Mset = ∑ ρ : BoundaryLifts b F RF.TC, Nat.card (RF.LiftsOver b F ρ) := by
    set Φ : Mset → BoundaryLifts b F RF.TC := fun m =>
      ⟨⟨⟨RF.piBC.comp m.1.toMonoidHom,
          (continuous_of_discreteTopology (f := ⇑RF.piBC)).comp m.1.continuous_toFun⟩, m.2.2⟩,
        fun γ => by
          show (RF.TC.piY (RF.piBC (m.1 γ)), RF.TC.thetaY (RF.piBC (m.1 γ))) = F.frameMap (b γ)
          have h1 : RF.TC.piY (RF.piBC (m.1 γ)) = RF.TB.piY (m.1 γ) := by
            rw [show RF.TC.piY (RF.piBC (m.1 γ)) = (RF.TC.piY.comp RF.piBC) (m.1 γ) from rfl,
              hheadBC]
          have h2 : RF.TC.thetaY (RF.piBC (m.1 γ)) = RF.TB.thetaY (m.1 γ) := by
            rw [show RF.TC.thetaY (RF.piBC (m.1 γ)) = (RF.TC.thetaY.comp RF.piBC) (m.1 γ) from rfl,
              hthetaBC]
          rw [h1, h2]
          exact m.2.1 γ⟩ with hΦdef
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv Φ).symm, Nat.card_sigma]
    refine Finset.sum_congr rfl (fun ρ _ => Nat.card_congr ?_)
    exact
      { toFun := fun mm =>
          ⟨mm.1.1, fun γ => congrArg (fun x : BoundaryLifts b F RF.TC => x.1.1 γ) mm.2⟩
        invFun := fun n =>
          ⟨⟨n.1, RF.isBoundaryLift_of_over b F n.1 ρ n.2,
              by rw [show (⇑RF.piBC ∘ ⇑n.1) = ⇑ρ.1.1 from funext n.2]; exact ρ.1.2⟩,
            Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ => n.2 γ))⟩
        left_inv := fun mm => Subtype.ext (Subtype.ext rfl)
        right_inv := fun n => Subtype.ext rfl }
  rw [eUnion]; exact hmultsum

/-- Stage (C), `C`-onto head-surjective stratum: the exact-image fibre of `Mset` over a subgroup
`J ↠ C` that is head-surjective counts the boundary-framed exact-image lifts of the stratum
`T_B|_J` (the `partition137_of`/`lemma_8_3` image-stratification). -/
private theorem mStage_stratum_fiber_card {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E) (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC = ⊤) (hJh : Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J}
      = exactImageCount b F (RF.TB.stratum J hJh) := by
  classical
  rw [exactImageCount]
  have hmem : ∀ (m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)}),
      m.1.toMonoidHom.range = J → ∀ γ, m.1 γ ∈ J := by
    intro m hm γ
    have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
    rwa [hm] at this
  refine Nat.card_congr ⟨fun m =>
    ⟨⟨cmhCodRestrict m.1.1 J (hmem m.1 m.2), fun j => ?_⟩, fun γ => ?_⟩,
    fun f => ⟨⟨cmhInclude J f.1.1, fun γ => f.2 γ, ?_⟩, ?_⟩,
    fun m => Subtype.ext (Subtype.ext rfl),
    fun f => Subtype.ext (Subtype.ext (ContinuousMonoidHom.ext fun γ => Subtype.ext rfl))⟩
  · -- corestriction surjective onto `↥J`
    have hj : (j : RF.YB) ∈ m.1.1.toMonoidHom.range := by rw [m.2]; exact j.2
    obtain ⟨γ, hγ⟩ := hj
    exact ⟨γ, Subtype.ext hγ⟩
  · -- stratum boundary equation (definitional transport)
    exact m.1.2.1 γ
  · -- `C`-surjectivity of the included map, from `J ↠ C`
    intro c
    have hc : c ∈ J.map RF.piBC := by rw [hJc]; trivial
    obtain ⟨y, hyJ, hyc⟩ := Subgroup.mem_map.mp hc
    obtain ⟨γ, hγ⟩ := f.1.2 ⟨y, hyJ⟩
    exact ⟨γ, by show RF.piBC ((f.1.1 γ : RF.YB)) = c; rw [hγ, hyc]⟩
  · -- the included map has range exactly `J`
    have h1 : (cmhInclude J f.1.1).toMonoidHom.range
        = f.1.1.toMonoidHom.range.map J.subtype := MonoidHom.range_comp _ _
    rw [h1, MonoidHom.range_eq_top.mpr f.1.2, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]

/-- Stage (C), `C`-missing stratum: a subgroup `J` that does not surject onto `C` has empty
exact-image fibre in `Mset` (each `Mset`-member is `C`-onto, so its range is too). -/
private theorem mStage_fiber_empty_of_not_onto {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E) (J : Subgroup RF.YB)
    (hJc : J.map RF.piBC ≠ ⊤) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J} = 0 := by
  classical
  have hE : IsEmpty {m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
      m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJc
    rw [← hm, ← MonoidHom.range_comp, MonoidHom.range_eq_top]
    intro c
    obtain ⟨γ, hγ⟩ := m.2.2 c
    exact ⟨γ, hγ⟩
  exact Nat.card_of_isEmpty

/-- Stage (C), head-missing stratum: under the head-surjectivity hypothesis `hhead`, a subgroup
`J` whose head projection misses `C` has empty exact-image fibre in `Mset`. -/
private theorem mStage_fiber_empty_of_not_head {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) (J : Subgroup RF.YB)
    (hJh : ¬ Function.Surjective (RF.TB.piY.comp J.subtype)) :
    Nat.card {m : {n : ContinuousMonoidHom Γ RF.YB //
          IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
        m.1.toMonoidHom.range = J} = 0 := by
  classical
  have hE : IsEmpty {m : {n : ContinuousMonoidHom Γ RF.YB //
      IsBoundaryLift b F RF.TB n ∧ Function.Surjective (⇑RF.piBC ∘ ⇑n)} //
      m.1.toMonoidHom.range = J} := by
    constructor
    rintro ⟨m, hm⟩
    apply hJh
    intro hh
    obtain ⟨γ, hγ⟩ := hhead hh
    have hmemJ : m.1 γ ∈ J := by
      have : m.1 γ ∈ m.1.toMonoidHom.range := ⟨γ, rfl⟩
      rwa [hm] at this
    refine ⟨⟨m.1 γ, hmemJ⟩, ?_⟩
    show RF.TB.piY (m.1 γ) = hh
    have hbd := m.2.1 γ
    have := congrArg Prod.fst hbd
    simpa [hγ] using this
  exact Nat.card_of_isEmpty

/-- Stage (C) of `mStage_partition`: `Mset` stratifies by exact image into the `C`-onto strata
of `T_B`, assembling the three fibre classifications (`mStage_stratum_fiber_card`,
`mStage_fiber_empty_of_not_onto`, `mStage_fiber_empty_of_not_head`). -/
private theorem mStage_Mset_card_eq_finsum {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ]
    [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1)) :
    Nat.card {m : ContinuousMonoidHom Γ RF.YB //
        IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)}
      = ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤}, exactImageCountOn b F RF.TB J := by
  classical
  haveI : Finite (ContinuousMonoidHom Γ RF.YB) := finite_continuousMonoidHom hfg RF.YB
  haveI : Finite (Subgroup RF.YB) :=
    Finite.of_injective (fun J : Subgroup RF.YB => (J : Set RF.YB)) SetLike.coe_injective
  haveI : Fintype (Subgroup RF.YB) := Fintype.ofFinite _
  set Mset := {m : ContinuousMonoidHom Γ RF.YB //
    IsBoundaryLift b F RF.TB m ∧ Function.Surjective (⇑RF.piBC ∘ ⇑m)} with hMsetdef
  -- stratify `Mset` by the exact image `range m`
  have e2 : Nat.card Mset
      = ∑ J : Subgroup RF.YB, Nat.card {m : Mset // m.1.toMonoidHom.range = J} := by
    rw [Nat.card_congr (Equiv.sigmaFiberEquiv
      (fun m : Mset => m.1.toMonoidHom.range)).symm, Nat.card_sigma]
  set fib : Subgroup RF.YB → ℕ :=
    fun J => Nat.card {m : Mset // m.1.toMonoidHom.range = J} with hfibdef
  set S : Finset (Subgroup RF.YB) :=
    Finset.univ.filter (fun J => J.map RF.piBC = ⊤) with hSdef
  -- assemble: restrict to `S`, match `fib` to `exactImageCountOn`, convert to `finsum`
  have hStep : (∑ J : Subgroup RF.YB, fib J) = ∑ J ∈ S, fib J := by
    rw [hSdef, ← Finset.sum_filter_add_sum_filter_not Finset.univ
      (fun J => J.map RF.piBC = ⊤) fib]
    have hz : ∑ J ∈ Finset.univ.filter (fun J => ¬ J.map RF.piBC = ⊤), fib J = 0 :=
      Finset.sum_eq_zero (fun J hJ =>
        mStage_fiber_empty_of_not_onto RF b F J (Finset.mem_filter.mp hJ).2)
    rw [hz, add_zero]
  have hmatch : ∀ J ∈ S, fib J = exactImageCountOn b F RF.TB J := by
    intro J hJ
    rw [hSdef, Finset.mem_filter] at hJ
    obtain ⟨_, hJc⟩ := hJ
    by_cases hJh : Function.Surjective (RF.TB.piY.comp J.subtype)
    · simp only [exactImageCountOn, dif_pos hJh]
      exact mStage_stratum_fiber_card RF b F J hJc hJh
    · simp only [exactImageCountOn, dif_neg hJh]
      exact mStage_fiber_empty_of_not_head RF b F hhead J hJh
  have hsetconv : {J : Subgroup RF.YB | J.map RF.piBC = ⊤} = ↑S := by
    rw [hSdef]; ext J; simp
  have hfinsum : ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤},
        exactImageCountOn b F RF.TB J
      = ∑ J ∈ S, exactImageCountOn b F RF.TB J := by
    rw [hsetconv, finsum_mem_coe_finset]
  rw [e2, hStep, Finset.sum_congr rfl hmatch]
  exact hfinsum.symm

/-- **The `M`-stage partition** (§9.2): the unrestricted `B`-lifts of the lower exact-image
maps, all with the same multiplicity `mult` over each lower map (`hmult` — the
`|Z¹_{Γ,ρ}(M)| = 2^{2·dim M}` numerics of props 5.15/5.16, source-discharged at the §9 induction),
partition by exact image into the `C`-onto strata of `T_B`:
`mult · e_Γ(C) = Σ_{J ↠ C} e_Γ(stratum J)`.  Machinery: the `LiftsOver`-fibration of
the Prop. 8.9 assembly + the image-stratification of `partition137_of`/`lemma_8_3`.
[the §9 induction statement; proof the §9 induction.] -/
theorem mStage_partition {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y]
    [Finite Y] {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY}
    (RF : RecursionFrame T Blk) {Γ : Type} [Group Γ] [TopologicalSpace Γ]
    [IsTopologicalGroup Γ] [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤)
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (hhead : Function.Surjective (fun γ : Γ => (F.frameMap (b γ)).1))
    (mult : ℕ)
    (hmult : ∀ ρ : BoundaryLifts b F RF.TC, Nat.card (RF.LiftsOver b F ρ) = mult) :
    mult * exactImageCount b F RF.TC
      = ∑ᶠ J ∈ {J : Subgroup RF.YB | J.map RF.piBC = ⊤},
          exactImageCountOn b F RF.TB J := by
  classical
  rw [← mStage_Mset_card_eq_mult RF hfg b F mult hmult]
  exact mStage_Mset_card_eq_finsum RF hfg b F hhead

/-! ## The recursion solver -/

/-- **Solving the closed recursion** (the §9.3 bookkeeping): two sources satisfying the
boxed system (136)–(140) for the *same* frame and the *same* shared data `(μ, G⁰, D_T,
phase)` have equal exact-image counts at the top, provided the strictly-smaller ingredient
counts agree — the atoms the induction hypothesis supplies:

* `hTB`/`hTC` — the quotient-stage counts (`|L_B|, |L_C| < |L_Y|`);
* `hpull` — the (138) pullback-stratum counts at every scalar cover, restricted to the
  strata over **proper `C`-onto** images (the only ones (137) consumes; exactly the (148)
  regime, kernels `≤ 2|J ∩ L_B| ≤ |L_B| < |L_Y|` — for an improper image the pulled kernel
  can equal `|L_Y|` at `|R| = 2`, so an unrestricted atom would be un-suppliable by the
  induction) [restriction added the §9 induction, documented];
* `hphase` — the phase-cover liftable counts (derived at the §9 induction from `lemma_8_3` at the
  phase covers + the (153) bound `2|L_C| < |L_Y|`; here taken as an atom).

Derivation: (138) + `hpull` give the `m_J` agreement (cancel 8); (139)/(140) + `hTC` +
`hphase` give the `Z_{B/C}` agreement (cancel `2`, resp. `2·#D_T ≠ 0`); (137) then gives
the `m_B` agreement; (136) + `#D_R ≠ 0` gives the top count.  Pure `ℤ`-arithmetic.
[the §9 induction statement; proof the §9 induction.] -/
theorem count_eq_of_closedRecursion {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] {T : MarkedTarget H E Y}
    {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)
    {Γ₁ : Type} [Group Γ₁] [TopologicalSpace Γ₁]
    {Γ₂ : Type} [Group Γ₂] [TopologicalSpace Γ₂]
    (b₁ : ContinuousMonoidHom Γ₁ ↥boundarySubgroup)
    (b₂ : ContinuousMonoidHom Γ₂ ↥boundarySubgroup)
    (F : BoundaryFrame H E) (μ : ℕ) (G0 : ℤ) (DT : Type) [Fintype DT]
    (phase : (l : RF.DR) → l ≠ RF.zeroDR → DT → CentralCover RF.YC)
    (h₁ : ClosedRecursion RF b₁ F μ G0 DT phase)
    (h₂ : ClosedRecursion RF b₂ F μ G0 DT phase)
    (hDT : Nat.card DT ≠ 0)
    (hTB : exactImageCount b₁ F RF.TB = exactImageCount b₂ F RF.TB)
    (hTC : exactImageCount b₁ F RF.TC = exactImageCount b₂ F RF.TC)
    (hpull : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (J' : Subgroup (RF.scalarCover l h).cover),
      J'.map (RF.scalarCover l h).p ≠ ⊤ → (J'.map (RF.scalarCover l h).p).map RF.piBC = ⊤ →
      exactImageCountOn b₁ F ((RF.scalarCover l h).pullTarget RF.TB) J'
        = exactImageCountOn b₂ F ((RF.scalarCover l h).pullTarget RF.TB) J')
    (hphase : ∀ (l : RF.DR) (h : l ≠ RF.zeroDR) (ζ : DT),
      RF.nPhase b₁ F (phase l h ζ) = RF.nPhase b₂ F (phase l h ζ)) :
    exactImageCount b₁ F T = exactImageCount b₂ F T := by
  classical
  -- (138) + `hpull`: the proper `C`-onto stratum counts `m_J` agree (cancel the `8`), hence
  -- so do `mJOn` (only these instances are consumed by (137) below)
  have hmJOn : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR) (J : Subgroup RF.YB),
      J ≠ ⊤ → J.map RF.piBC = ⊤ →
      RF.mJOn b₁ F l hl J = RF.mJOn b₂ F l hl J := by
    intro l hl J hJne hJC
    simp only [RecursionFrame.mJOn]
    by_cases hJ : Function.Surjective (RF.TB.piY.comp J.subtype)
    · rw [dif_pos hJ, dif_pos hJ]
      have h8 : 8 * RF.mJ b₁ F l hl J hJ = 8 * RF.mJ b₂ F l hl J hJ := by
        rw [h₁.eq138 l hl J hJ, h₂.eq138 l hl J hJ]
        refine finsum_mem_congr rfl (fun J' hJ' => ?_)
        have hJ'' : J'.map (RF.scalarCover l hl).p = J := hJ'
        exact hpull l hl J' (by rw [hJ'']; exact hJne) (by rw [hJ'']; exact hJC)
      omega
    · rw [dif_neg hJ, dif_neg hJ]
  -- (139)/(140): the compatible-lift counts `zBC` agree (case split on the descent-∃)
  have hzBC : ∀ (l : RF.DR) (hl : l ≠ RF.zeroDR),
      RF.zBC b₁ F l hl = RF.zBC b₂ F l hl := by
    intro l hl
    by_cases hdesc : ∃ N : Subgroup (RF.scalarCover l hl).cover, N.Normal ∧
        N.map (RF.scalarCover l hl).p = RF.TBsub ∧ (RF.scalarCover l hl).z ∉ N
    · -- descent: (140), cancel `2·#DT ≠ 0`
      have hns : (∑ᶠ ζ : DT,
            (2 * (RF.nPhase b₁ F (phase l hl ζ) : ℤ) - (exactImageCount b₁ F RF.TC : ℤ)))
          = ∑ᶠ ζ : DT,
            (2 * (RF.nPhase b₂ F (phase l hl ζ) : ℤ) - (exactImageCount b₂ F RF.TC : ℤ)) :=
        finsum_congr (fun ζ => by rw [hphase l hl ζ, hTC])
      have hcancel : 2 * (Nat.card DT : ℤ) * (RF.zBC b₁ F l hl : ℤ)
          = 2 * (Nat.card DT : ℤ) * (RF.zBC b₂ F l hl : ℤ) := by
        rw [h₁.eq140 l hl hdesc, h₂.eq140 l hl hdesc, hns, hTC]
      have hne : (2 : ℤ) * (Nat.card DT : ℤ) ≠ 0 :=
        mul_ne_zero two_ne_zero (Nat.cast_ne_zero.mpr hDT)
      exact_mod_cast mul_left_cancel₀ hne hcancel
    · -- no descent: (139), cancel `2`
      have hcancel : 2 * RF.zBC b₁ F l hl = 2 * RF.zBC b₂ F l hl := by
        rw [h₁.eq139 l hl hdesc, h₂.eq139 l hl hdesc, hTC]
      omega
  -- (137) + `mB(0) = e(T_B)`: the top-stratum counts `m_B` agree
  have hmB : ∀ l : RF.DR, RF.mB b₁ F l = RF.mB b₂ F l := by
    intro l
    by_cases hl : l = RF.zeroDR
    · subst hl
      simp only [RecursionFrame.mB]
      exact hTB
    · have hsum : (∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (RF.mJOn b₁ F l hl J : ℤ))
          = ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
            (RF.mJOn b₂ F l hl J : ℤ) :=
        finsum_mem_congr rfl (fun J hJmem => by
          obtain ⟨hJne, hJC⟩ := hJmem
          rw [hmJOn l hl J hJne hJC])
      have hz : (RF.zBC b₁ F l hl : ℤ) = (RF.zBC b₂ F l hl : ℤ) := by rw [hzBC l hl]
      have hcast : (RF.mB b₁ F l : ℤ) = (RF.mB b₂ F l : ℤ) := by
        have h137 : (RF.mB b₁ F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (RF.mJOn b₁ F l hl J : ℤ)
            = (RF.mB b₂ F l : ℤ)
            + ∑ᶠ J ∈ {J : Subgroup RF.YB | J ≠ ⊤ ∧ J.map RF.piBC = ⊤},
                (RF.mJOn b₂ F l hl J : ℤ) := by
          rw [← h₁.eq137 l hl, ← h₂.eq137 l hl, hz]
        rw [hsum] at h137
        exact add_right_cancel h137
      exact_mod_cast hcast
  -- (136): the top counts `e(T)` agree (cancel `#D_R ≠ 0`)
  have hDRne : (Nat.card RF.DR : ℤ) ≠ 0 := by
    have h : Nat.card RF.DR ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨RF.zeroDR⟩, inferInstance⟩
    exact_mod_cast h
  have hrhs : (RF.zR : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b₁ F l : ℤ) - exactImageCount b₁ F RF.TB)
      = (RF.zR : ℤ) * ∑ᶠ l : RF.DR,
        (2 * (RF.mB b₂ F l : ℤ) - exactImageCount b₂ F RF.TB) := by
    congr 1
    exact finsum_congr (fun l => by rw [hmB l, hTB])
  have hcast : (exactImageCount b₁ F T : ℤ) = (exactImageCount b₂ F T : ℤ) := by
    refine mul_left_cancel₀ hDRne ?_
    rw [h₁.eq136, h₂.eq136, hrhs]
  exact_mod_cast hcast

end SectionNine

end GQ2
