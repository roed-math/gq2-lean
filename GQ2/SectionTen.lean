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

/-- **Lemma 10.1 (Exhaustion by tame boundary frames)**, partition form: for a source `(Γ, b)`
whose tame coordinate is onto with pro-2 kernel, the ordinary continuous epimorphisms `Γ ↠ G`
are exactly the boundary-framed epimorphisms onto the single target `tameTarget G`, fibered
over the (finitely many) tame frames — `f` lands in the fiber of its induced frame `α_f`
(well-defined because `f(ker (pr₁ ∘ b))` is a normal 2-subgroup of `G`, hence `≤ O₂(G)`);
distinct frames give disjoint fibers (`α` is determined by `α ∘ (pr₁ ∘ b)`).  [P-18c] -/
theorem lemma_10_1
    (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker) :
    Nonempty (ContSurj Γ G ≃
      (α : TameFrames G) × BoundaryLifts b (tameFrame α.1 α.2) (tameTarget G)) := by
  sorry

/-- **Lemma 10.1, counting form** (the (154)-assembly workhorse): the ordinary surjection count
is the sum of the fixed-frame exact-image counts over all tame frames.  [P-18c; finiteness of
the fibers from `hfg` via `finite_boundaryLifts`, of the index from `Ttame` t.f.g.] -/
theorem card_contSurj_eq
    (htame : Function.Surjective (tameCoord b))
    (hwild : IsProP 2 (tameCoord b).toMonoidHom.ker)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Nat.card (ContSurj Γ G)
      = ∑ᶠ α : TameFrames G, exactImageCount b (tameFrame α.1 α.2) (tameTarget G) := by
  sorry

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
