import GQ2.SectionNine
import GQ2.Prop23
import GQ2.MaxProP

/-!
# §10 — Passage to all finite quotients  (P-18; statements: P-18a)

Paper §10 (pp. 47–48): **Lemma 10.1** (exhaustion by tame boundary frames) and the assembly of
**eq. (154)** `|Sur(Γ_A, G)| = |Sur(G_ℚ₂, G)|`, which combined with Prop 2.3 gives
`main_surjection_count` (`GQ2/Statement.lean`) and hence Theorem 1.2.

Design (`docs/p18-plan.md`, extraction ledger `docs/section10-extraction.md`):

* **The 2-core.**  Lemma 10.1 fixes `L = O₂(G)` — ONE marked target `tameTarget G` for all
  epimorphisms; only the tame frame `α : Ttame ↠ G/O₂(G)` varies.  The image of the source's
  pro-2 wild kernel under any epimorphism is a normal 2-subgroup, hence lands in `O₂(G)`
  automatically — so the `E = 0` boundary-framing condition *is* the fixed-frame condition, the
  fixed-frame sets are literally `BoundaryLifts`, and no Möbius/poset induction is needed.
  Mathlib has no `pCore`; `twoCore` is defined here, its three properties proved by **P-18b**.

* **Γ-generic form.**  The paper's "for either source" is encoded hypothesis-side: `lemma_10_1`
  and `card_contSurj_eq` are stated over any `(Γ, b)` with `htame` (the tame coordinate of `b`
  is onto) and `hwild` (its kernel is pro-2); **P-18d** discharges both per source — the
  `G_ℚ₂` side from the `BoundaryMaps` clauses (`tameF_surjective`, `wild_isProP`), the `Γ_A`
  side from the generator clauses + `isProP_wildCore` (P-04).

* **Trivial decoration.**  `E = 0` is `E₀ := PUnit` (`hE2` and the `ψ̄`-condition are trivial).

* **Splice geometry** (P-18e): `Statement.lean` is imported by `GammaA`/`FoxHeisenberg`, i.e. it
  sits UPSTREAM of the whole tower, so `main_surjection_count` cannot be proven in place.  The
  proof lives here as `main_surjection_count'`; at P-18e the `Statement.lean` sorry is resolved
  by the statement-move pattern (comment-pointer upstream; `main_presentation` goes
  hypothesis-form) and gains the two `AbsGalQ2` instance binders (they are file-level
  `variable`s throughout the tower, not global instances).

Sorried here (proof tickets in parentheses): `twoCore_normal`/`twoCore_isPGroup` (P-18b),
`isPGroup_map_of_isProP` (P-18b), `lemma_10_1`/`card_contSurj_eq` (P-18c), `eq_154` (P-18e,
consuming `thm_4_2` per frame).  `SORRY_ALLOWLIST` carries this file until P-18b–e land.
-/

namespace GQ2

namespace SectionTen

/-! ## The 2-core `O₂(G)`  (P-18b proves the three properties)

The family of normal 2-subgroups is directed (the join of two normal 2-subgroups is again a
normal 2-subgroup, by the second isomorphism theorem and closure of `p`-groups under
extensions), so its `sSup` is itself a normal 2-subgroup — the largest one. -/

section TwoCore

variable (G : Type*) [Group G]

/-- **The 2-core `O₂(G)`**: the join of all normal 2-subgroups of `G`. -/
def twoCore : Subgroup G :=
  sSup {N : Subgroup G | N.Normal ∧ IsPGroup 2 N}

/-- `O₂(G) ◁ G`  (an sSup of normal subgroups is normal). -/
instance twoCore_normal : (twoCore G).Normal :=
  Subgroup.sSup_normal _ fun _ hH => hH.1

/-- `O₂(G)` is a 2-group  (`Sylow.sSup_of_normal`: the sSup of a family of normal 2-subgroups is
a 2-group — the extension/Sylow content lives in mathlib; `[Finite G]`, which §10 always has). -/
theorem twoCore_isPGroup [Finite G] : IsPGroup 2 (twoCore G) :=
  Sylow.sSup_of_normal _ (fun _ hH => hH.2) fun _ hH => hH.1

/-- Every normal 2-subgroup lies in the 2-core. -/
theorem le_twoCore {G : Type*} [Group G] {N : Subgroup G} (hN : N.Normal)
    (h2 : IsPGroup 2 N) : N ≤ twoCore G :=
  le_sSup ⟨hN, h2⟩

end TwoCore

/-- **The pro-2 image bridge** (P-18b): the image of a pro-2 subgroup under a continuous
homomorphism into a finite discrete group is a 2-group.  (`f(K) ≅ K ⧸ ker(f|_K)`, and the
kernel is open since the codomain is discrete, so this is an `IsProP` quotient.) -/
theorem isPGroup_map_of_isProP {Γ G' : Type*} [Group Γ] [TopologicalSpace Γ] [Group G']
    [TopologicalSpace G'] [DiscreteTopology G'] [Finite G'] (K : Subgroup Γ)
    (hK : IsProP 2 K) (f : ContinuousMonoidHom Γ G') :
    IsPGroup 2 (K.map f.toMonoidHom) := by
  -- `g : ↥K →* G'`, the restriction of `f` to `K`
  set g : K →* G' := f.toMonoidHom.comp K.subtype with hg
  -- `g` is continuous, so (codomain discrete) its kernel is open in `K`
  have hgcont : Continuous g := f.continuous_toFun.comp continuous_subtype_val
  have hopen : IsOpen (g.ker : Set K) := by
    have hpre : (g.ker : Set K) = g ⁻¹' {1} := by
      ext x; simp [MonoidHom.mem_ker]
    rw [hpre]; exact (isOpen_discrete {(1 : G')}).preimage hgcont
  -- package `ker g` as an open normal subgroup of `K` and apply `IsProP`
  let U : OpenNormalSubgroup K := ⟨⟨g.ker, hopen⟩, MonoidHom.normal_ker g⟩
  have hquot : IsPGroup 2 (K ⧸ U.toSubgroup) := hK U
  -- transfer along `K ⧸ ker g ≃ range g = K.map f`
  have hrange : (g.range : Subgroup G') = K.map f.toMonoidHom := by
    rw [hg, MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hrange]
  exact hquot.of_equiv (QuotientGroup.quotientKerEquivRange g)

/-! ## The §10 target and frames  (`E = 0`) -/

section Builders

/-- The trivial decoration group (`E = 0` of Theorem 4.2's §10 consumption). -/
abbrev E₀ : Type := PUnit

variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

/-- The quotient head `G/O₂(G)` of a finite discrete group is discrete (the quotient topology
is coinduced, so every set is open). -/
instance : DiscreteTopology (G ⧸ twoCore G) :=
  discreteTopology_iff_forall_isOpen.mpr fun _ => isOpen_coinduced.mpr (isOpen_discrete _)

/-- **The §10 marked target** `𝒴_G = (G, O₂(G), π, θ = 0)`: the single boundary-framed marked
target through which ALL epimorphisms onto `G` are counted (Lemma 10.1). -/
noncomputable def tameTarget : MarkedTarget (G ⧸ twoCore G) E₀ G where
  LY := twoCore G
  normal := twoCore_normal G
  isPGroup_two := twoCore_isPGroup G
  piY := QuotientGroup.mk' (twoCore G)
  piY_surjective := QuotientGroup.mk'_surjective (twoCore G)
  ker_piY := QuotientGroup.ker_mk' (twoCore G)
  thetaY := 1

/-- **The §10 boundary frame** of a tame frame `α : Ttame ↠ H` (decoration `E₀` trivial,
`ψ̄ = 1`). -/
noncomputable def tameFrame {H : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] (α : ContinuousMonoidHom Ttame H) (hα : Function.Surjective α) :
    BoundaryFrame H E₀ where
  alpha := α
  alpha_surjective := hα
  exponent_two := fun _ => rfl
  psiBar := 1

/-- **The tame-frame index** of Lemma 10.1: continuous surjections `Ttame ↠ G/O₂(G)`.
Finite because `Ttame` is topologically 2-generated (`gen_ttame_quotient`); the finiteness
instance is P-18c's. -/
def TameFrames : Type :=
  {α : ContinuousMonoidHom Ttame (G ⧸ twoCore G) // Function.Surjective α}

/-- `Ttame` is topologically finitely generated (by `σ, τ`): `topGen_ttame` in the `Finset`
form consumed by the t.f.g.-hom-finiteness machinery.  [P-18c] -/
theorem ttame_tfg :
    ∃ s : Finset Ttame, (Subgroup.closure (s : Set Ttame)).topologicalClosure = ⊤ := by
  classical
  refine ⟨{tameSigma, tameTau}, ?_⟩
  have hcoe : (({tameSigma, tameTau} : Finset Ttame) : Set Ttame) = {tameSigma, tameTau} := by
    simp
  rw [hcoe]
  exact SectionThree.topGen_ttame

/-- **The tame-frame index is finite** (so Lemma 10.1's sum is a finite sum): continuous
homomorphisms from the topologically `2`-generated `Ttame` into the finite discrete `G/O₂(G)`
form a finite type.  [P-18c] -/
instance : Finite (TameFrames G) := by
  haveI : Finite (ContinuousMonoidHom Ttame (G ⧸ twoCore G)) :=
    finite_continuousMonoidHom ttame_tfg _
  exact Subtype.finite

end Builders

/-! ## The tame coordinate of a boundary map -/

section TameCoord

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- The tame coordinate `pr₁ ∘ b : Γ → Ttame` of a boundary map `b : Γ → ∂bd`.  For the two
sources this is `B.tameA` resp. `B.tameF` on the nose (`bA_apply_coe`/`bF_apply_coe`). -/
noncomputable def tameCoord (b : ContinuousMonoidHom Γ ↥boundarySubgroup) :
    ContinuousMonoidHom Γ Ttame where
  toFun γ := (b γ : Ttame × PiBd).1
  map_one' := by rw [map_one]; rfl
  map_mul' x y := by rw [map_mul]; rfl
  continuous_toFun := (continuous_fst.comp continuous_subtype_val).comp b.continuous_toFun

@[simp] theorem tameCoord_apply (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (γ : Γ) :
    tameCoord b γ = (b γ : Ttame × PiBd).1 := rfl

end TameCoord

/-! ## Lemma 10.1 — exhaustion by tame boundary frames  (P-18c proves) -/

section Exhaustion

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (b : ContinuousMonoidHom Γ ↥boundarySubgroup)
variable (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G]

omit [IsTopologicalGroup Γ] in
/-- The image of the wild kernel under a continuous epimorphism `f : Γ ↠ G` lands in the
2-core: it is normal (image of a kernel under a surjection) and a 2-group (the pro-2 image
bridge `isPGroup_map_of_isProP`).  [P-18c] -/
theorem map_wildKer_le_twoCore (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker)
    (f : ContSurj Γ G) :
    ((tameCoord b).toMonoidHom.ker.map f.1.toMonoidHom) ≤ twoCore G :=
  le_twoCore ((MonoidHom.normal_ker _).map f.1.toMonoidHom f.2)
    (isPGroup_map_of_isProP _ hwild f.1)

/-- **The descended homomorphism** of Lemma 10.1's forward map: `π ∘ f` kills the wild kernel
(`map_wildKer_le_twoCore`), so it factors through the surjective tame coordinate as
`α_f : Ttame →* G/O₂(G)`.  [P-18c] -/
noncomputable def inducedHom (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker) (f : ContSurj Γ G) :
    Ttame →* G ⧸ twoCore G :=
  (tameCoord b).toMonoidHom.liftOfSurjective htame
    ⟨(QuotientGroup.mk' (twoCore G)).comp f.1.toMonoidHom, fun x hx => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, QuotientGroup.ker_mk']
      exact map_wildKer_le_twoCore b G hwild f (Subgroup.mem_map_of_mem _ hx)⟩

omit [IsTopologicalGroup Γ] in
/-- The defining property of the descent: `α_f ∘ (pr₁ ∘ b) = π ∘ f` pointwise.  [P-18c] -/
theorem inducedHom_tameCoord (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker) (f : ContSurj Γ G) (γ : Γ) :
    inducedHom b G htame hwild f (tameCoord b γ) = QuotientGroup.mk' (twoCore G) (f.1 γ) :=
  MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ γ

/-- **The induced tame frame** of a continuous epimorphism `f : Γ ↠ G` (Lemma 10.1, forward
map): the descent `α_f`, continuous because the tame coordinate of a *compact* source is a
topological quotient map (a continuous surjection onto the Hausdorff `Ttame` is closed, hence
quotient), and surjective because `π ∘ f` is.  [P-18c; the `[CompactSpace Γ]` binder is a
statement amendment over the P-18a skeleton — see `docs/section10-extraction.md`] -/
noncomputable def inducedFrame [CompactSpace Γ] (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker) (f : ContSurj Γ G) : TameFrames G :=
  have hquot : Topology.IsQuotientMap (tameCoord b) :=
    (tameCoord b).continuous_toFun.isClosedMap.isQuotientMap (tameCoord b).continuous_toFun
      htame
  ⟨{ toMonoidHom := inducedHom b G htame hwild f
     continuous_toFun := hquot.continuous_iff.mpr <|
       (QuotientGroup.continuous_mk.comp f.1.continuous_toFun).congr fun γ =>
         (inducedHom_tameCoord b G htame hwild f γ).symm },
   fun y => by
     obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective (twoCore G) y
     obtain ⟨γ, rfl⟩ := f.2 g
     exact ⟨tameCoord b γ, inducedHom_tameCoord b G htame hwild f γ⟩⟩

omit [IsTopologicalGroup Γ] in
/-- **Lemma 10.1 (Exhaustion by tame boundary frames)**, partition form: for a source `(Γ, b)`
whose tame coordinate is onto with pro-2 kernel, the ordinary continuous epimorphisms `Γ ↠ G`
are exactly the boundary-framed epimorphisms onto the single target `tameTarget G`, fibered
over the (finitely many) tame frames — `f` lands in the fiber of its induced frame `α_f`
(well-defined because `f(ker (pr₁ ∘ b))` is a normal 2-subgroup of `G`, hence `≤ O₂(G)`);
distinct frames give disjoint fibers (`α` is determined by `α ∘ (pr₁ ∘ b)`).  [P-18c;
`[CompactSpace Γ]` added over the P-18a skeleton — the descent's continuity needs the tame
coordinate to be a quotient map.  Both sources are profinite, so this is free at P-18e.] -/
theorem lemma_10_1 [CompactSpace Γ]
    (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker) :
    Nonempty (ContSurj Γ G ≃
      (α : TameFrames G) × BoundaryLifts b (tameFrame α.1 α.2) (tameTarget G)) := by
  refine ⟨(Equiv.sigmaFiberEquiv (inducedFrame b G htame hwild)).symm.trans
    (Equiv.sigmaCongrRight fun α => Equiv.subtypeEquivRight fun f => ?_)⟩
  constructor
  · -- membership in the fiber of `α_f` IS the boundary-framing condition for `α_f`
    rintro rfl γ
    refine Prod.ext ?_ (Subsingleton.elim _ _)
    exact (inducedHom_tameCoord b G htame hwild f γ).symm
  · -- disjointness: the framing condition for `α` forces `α_f = α`, since both agree with
    -- `π ∘ f` after composition with the surjective tame coordinate
    intro hf
    refine Subtype.ext (ContinuousMonoidHom.ext fun t => ?_)
    obtain ⟨γ, rfl⟩ := htame t
    exact (inducedHom_tameCoord b G htame hwild f γ).trans (congrArg Prod.fst (hf γ))

/-- **Lemma 10.1, counting form** (the (154)-assembly workhorse): the ordinary surjection count
is the sum of the fixed-frame exact-image counts over all tame frames.  [P-18c; finiteness of
the fibers from `hfg` via `finite_boundaryLifts` (whence the `[TotallyDisconnectedSpace Γ]`
binder, an amendment over the P-18a skeleton like `lemma_10_1`'s `[CompactSpace Γ]`), of the
index from `Ttame` t.f.g.] -/
theorem card_contSurj_eq [CompactSpace Γ] [TotallyDisconnectedSpace Γ]
    (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card (ContSurj Γ G)
      = ∑ᶠ α : TameFrames G, exactImageCount b (tameFrame α.1 α.2) (tameTarget G) := by
  classical
  obtain ⟨e⟩ := lemma_10_1 b G htame hwild
  haveI : ∀ α : TameFrames G, Finite (BoundaryLifts b (tameFrame α.1 α.2) (tameTarget G)) :=
    fun α => finite_boundaryLifts b (tameFrame α.1 α.2) (tameTarget G) hfg
  haveI : Fintype (TameFrames G) := Fintype.ofFinite _
  rw [Nat.card_congr e, Nat.card_sigma, finsum_eq_sum_of_fintype]
  rfl

end Exhaustion

/-! ## Eq. (154) and the surjection-count theorem  (P-18d/P-18e prove) -/

section EQ154

variable [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]

/-- **Eq. (154)**: the two sources have identical continuous-surjection counts onto every
finite group.  [P-18e: `card_contSurj_eq` for `B₀.bA` and `B₀.bF` (`B₀ := boundaryMapsWitness`;
per-source hypotheses P-18d) + `thm_4_2 B₀ (tameFrame α) (tameTarget G)` per frame, `hE2`
trivial.  Carries `sorryAx` through the allowlisted `thm_4_2` sorry until P-17i closes.] -/
theorem eq_154 (G : Type) [Group G] [TopologicalSpace G] [DiscreteTopology G] [Finite G] :
    Nat.card (ContSurj GammaA G) = Nat.card (ContSurj AbsGalQ2 G) := by
  sorry

/-- **Theorem 1.2, surjection-count form** — the statement of
`GQ2.main_surjection_count` (`GQ2/Statement.lean:46`), proved from eq. (154) + Prop 2.3.
At P-18e this replaces the `Statement.lean` sorry by the statement-move pattern (that file is
upstream of the tower and cannot import this one); the move also adds the two `AbsGalQ2`
instance binders (file-level `variable`s tower-wide, not global instances) — documented
amendment, invisible to `main_presentation`, which binds them itself. -/
theorem main_surjection_count'
    (G : Type) [Group G] [Finite G] [TopologicalSpace G] [DiscreteTopology G] :
    contSurjCount G = admissibleCount G :=
  (eq_154 G).symm.trans (prop_2_3 (G := G))

end EQ154

end SectionTen

end GQ2
