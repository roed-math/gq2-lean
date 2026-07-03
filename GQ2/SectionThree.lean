import GQ2.Demushkin
import GQ2.DyadicPresentation
import GQ2.MaxProP
import GQ2.Reciprocity
import GQ2.HilbertSymbol
import GQ2.GammaA

/-!
# §3 statements: the tame and maximal pro-2 quotients  (ticket P-06)

Sorried, faithful Lean statements of the paper's §3 interior nodes — **Prop. 3.2**,
**Lemmas 3.5, 3.7, Prop. 3.8**, and **Prop. 1.1** — phrased against the step-1 def-layers.
Proof tickets: P-07 (3.5 ledger), P-08 (3.7/3.8), P-09 (3.2), P-10 (1.1).  The companion
design note `docs/section3-extraction.md` maps every statement to its paper display and
records the absorption/deviation/escalation decisions summarized here:

* **Lemma 3.4 is absorbed** by the axiom layer: its abstract-isomorphism clause *is* axiom B4
  (`absGalQ2_maxProTwo_presentation`), its orientation-value clause *is* the B3c interface
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
* **Prop. 3.2's local side carries a flagged design escalation** (see `prop_3_2_local`):
  the classical description of `G_{ℚ₂}/W_F` is not derivable from the frozen ten-axiom
  census.  Recorded per step-2 rule 1; see the design note §"escalations".

Conventions: `x ^ g = g⁻¹xg` (`conjP`), `[x,y] = x⁻¹y⁻¹xy` (`commP`), reciprocity/`ν_ur`
normalizations as in the `LocalReciprocity` convention table (`GQ2/Reciprocity.lean`).
-/

open scoped Pointwise

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

/-! ## The finite-quotient tame group `T_tame`  (paper §3, first display)

`T_tame = ⟨σ, τ | τ^σ = τ²⟩_prof`, as a profinite presentation on two generators.
`GQ2/Tame.lean` (Lemma 3.1, fully proved) describes its finite quotients. -/

/-- The tame relator `τ^σ · (τ²)⁻¹` in the free profinite group on `σ = of 0`, `τ = of 1`
(relation (5) restricted to the tame letters). -/
noncomputable def tameRelator2 : FreeProfiniteGroup (Fin 2) :=
  conjP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 0) * (FreeProfiniteGroup.of 1 ^ 2)⁻¹

/-- **`T_tame`** (paper §3): the profinite group `⟨σ, τ | τ^σ = τ²⟩_prof`. -/
noncomputable def Ttame : ProfiniteGrp := profinitePresentation {tameRelator2}

/-- The marked generator `σ ∈ T_tame`. -/
noncomputable def tameSigma : Ttame := quotientMk (relatorSubgroup {tameRelator2})
  (FreeProfiniteGroup.of 0)

/-- The marked generator `τ ∈ T_tame`. -/
noncomputable def tameTau : Ttame := quotientMk (relatorSubgroup {tameRelator2})
  (FreeProfiniteGroup.of 1)

/-- The tame relation holds in `T_tame`: `τ^σ = τ²`. -/
theorem tame_relation : conjP tameTau tameSigma = tameTau ^ 2 := by
  have h := relator_quotientMk_eq_one {tameRelator2} rfl
  rw [tameRelator2] at h
  simp only [conjP] at h ⊢
  exact mul_inv_eq_one.mp h

/-! ## The marked generators of `Γ_A` and its wild subgroup `W_A`  (paper §2.1/§3)

`W_A` is the closed normal subgroup of `Γ_A` generated by the images of `x₀, x₁` (paper
§2.1, after eq. (7)).  P-04 (Track A) works with the same subgroup on its own board row;
if its file lands an equivalent definition, P-09 deduplicates at proof time (recorded in
the design note). -/

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

/-- **`W_A`** (paper §2.1): the closed normal subgroup of `Γ_A` generated by `x₀, x₁`. -/
noncomputable def wildPart : Subgroup GammaA :=
  (Subgroup.normalClosure {gammaX0, gammaX1}).topologicalClosure

instance wildPart_normal : wildPart.Normal :=
  Subgroup.is_normal_topologicalClosure _

/-! ## Proposition 3.2 — the common tame quotient

Paper: *"There are canonical isomorphisms `Γ_A/W_A ≅ T_tame ≅ G_{ℚ₂}/W_F`, where `W_F` is
wild inertia."*  Split into the two sides; "canonical" is realized as (i) generator-pinning
on the `Γ_A` side and (ii) uniqueness-by-maximality of the wild subgroup on the local side
(the residual choice of local isomorphism is count-invisible downstream — design note §3.2). -/

/-- **Prop. 3.2, `Γ_A` side**: the quotient of `Γ_A` by `W_A` is `T_tame`, canonically —
the isomorphism matches the marked generators `σ ↦ σ`, `τ ↦ τ`.  (Proof ticket P-09; the
`Γ_A` side consumes Lemma 3.1 = `GQ2/Tame.lean` and the relator bridges of `GQ2/GammaA.lean`.) -/
theorem prop_3_2_gammaA :
    ∃ e : ContinuousMulEquiv (GammaA ⧸ wildPart) Ttame,
      e (QuotientGroup.mk gammaSigma) = tameSigma ∧
      e (QuotientGroup.mk gammaTau) = tameTau := by
  sorry

/-- **Prop. 3.2, local side + Lemma 3.3's characterization, bundled.**  The paper's wild
inertia `W_F` is encoded *intrinsically* as the maximal closed normal pro-2 subgroup (the
2-core `O₂(G_{ℚ₂})`) — by paper Lemma 3.3 these agree, and Mathlib has no ramification
theory to say "wild inertia" directly (**deviation, flagged**).  The instance-binder field
`normal` makes the quotient's group structure available to the `equiv` field. -/
structure LocalTameQuotient [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] where
  /-- The local wild subgroup `W_F ≤ G_{ℚ₂}`. -/
  W : Subgroup AbsGalQ2
  /-- `W_F` is normal. -/
  [normal : W.Normal]
  /-- `W_F` is closed. -/
  isClosed : IsClosed (W : Set AbsGalQ2)
  /-- `W_F` is pro-2. -/
  isProP : IsProP 2 W
  /-- `W_F` is the **maximal** closed normal pro-2 subgroup — Lemma 3.3's `O₂(G_{ℚ₂}) = W_F`,
  which pins `W` uniquely (the "canonical" of Prop. 3.2 on the local side). -/
  maximal : ∀ N : Subgroup AbsGalQ2, N.Normal → IsClosed (N : Set AbsGalQ2) →
    IsProP 2 N → N ≤ W
  /-- **Prop. 3.2, local side**: `G_{ℚ₂}/W_F ≅ T_tame`. -/
  equiv : ContinuousMulEquiv (AbsGalQ2 ⧸ W) Ttame

/-- **Prop. 3.2, local side** (paper §3): the tame quotient of `G_{ℚ₂}` is `T_tame`.

**Design escalation (step-2 rule 1, recorded here and in the design note):** the paper's
proof cites *"the standard description of the tame quotient in the geometric normalization"*
— a classical literature input (NSW (7.5.2)-family: `G_{ℚ₂}/W_F ≅ Ẑ^{(2')} ⋊ Ẑ`, Frobenius
acting by squaring) that is **not derivable from the frozen ten-axiom census** (the census is
2-centric; B5 sees only the abelianization).  P-09 cannot close this sorry from the declared
`Ax = B5` alone; resolving it needs a census discussion (option A: extend by the tame
description as a B-axiom; option B: re-scope what Lemma 10.1 consumes).  Until then this is
an honest, faithfully-stated gap. -/
theorem prop_3_2_local [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nonempty LocalTameQuotient := by
  sorry

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

/-- **Equation (11)** (paper §3.1 preamble): the marked decomposition of `B` exists.
(Proof ticket P-07: pure presented-group computation from (8)/(9), no arithmetic axioms.) -/
theorem b_decomposition : Nonempty BDecomposition := by
  sorry

/-! ## Lemma 3.5 — marked abelianization, orientation, and initial form

The `(ν_ur, χ_D)`-rows of eq. (13) and `ā²s̄⁴ = 1` are proved in `GQ2/Reciprocity.lean`
(see the module docstring above).  The three remaining clauses: -/

/-- `−4 ∈ ℚ₂ˣ` — the class `ā = rec(−4)` of Lemma 3.5.  (Public counterpart of the private
`uNeg4` in `GQ2/Reciprocity.lean`.) -/
noncomputable def unitNeg4 : ℚ_[2]ˣ := Units.mk0 (-4 : ℚ_[2]) (by norm_num)

/-- `−3 ∈ ℚ₂ˣ` — the class `ȳ = rec(−3)` of Lemma 3.5. -/
noncomputable def unitNeg3 : ℚ_[2]ˣ := Units.mk0 (-3 : ℚ_[2]) (by norm_num)

/-- **Lemma 3.5, marked-abelianization clause**: the pro-2 abelianization of `D = G_{ℚ₂}(2)`
is identified with `B = D₀^{ab}` by `Ā ↦ ā = rec(−4)`, `S̄ ↦ s̄ = rec(2)⁻¹ = rec(1/2)`,
`Ȳ ↦ ȳ = rec(−3)`.  The `rec`-classes live in `G^{ab}` (`R.recip`), so the matching is
quantified over lifts `g ∈ G_{ℚ₂}` of each class (all lifts agree in `D^{ab}`; the statement
form makes this an obligation of the proof, ticket P-07, `Ax = B5`). -/
theorem lemma_3_5_marked_abelianization
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] (R : LocalReciprocity) :
    ∃ e : ContinuousMulEquiv (topAbelianization D0)
      (topAbelianization (maxProPQuotient 2 AbsGalQ2)),
      (∀ g : AbsGalQ2, toAb g = R.recip unitNeg4 →
        e (abMk d0A) = abMk (maxProPMk 2 AbsGalQ2 g)) ∧
      (∀ g : AbsGalQ2, toAb g = (R.recip uniformizer)⁻¹ →
        e (abMk d0S) = abMk (maxProPMk 2 AbsGalQ2 g)) ∧
      (∀ g : AbsGalQ2, toAb g = R.recip unitNeg3 →
        e (abMk d0Y) = abMk (maxProPMk 2 AbsGalQ2 g)) := by
  sorry

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
  sorry

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
  sorry

/-! ## Lemma 3.7 and Proposition 3.8 — lifting automorphisms of `(B, χ₀)`

Phrased against a `BDecomposition` coordinate system.  A continuous group isomorphism of
pro-2 abelian groups is automatically `ℤ₂`-linear, so the coordinate transcriptions below
are exactly the paper's `ℤ₂`-module statements (design note §3.7–3.8). -/

/-- **Lemma 3.7 (square-root and HNN lifting)**: for every `u ∈ ℤ₂ˣ` there is a continuous
automorphism `Ψ_u` of `D₀` acting on `B` by `Ā ↦ uĀ`, `S̄ ↦ uS̄` (paper (15); `Ȳ` is not
constrained).  In `(t, S̄, Ȳ)`-coordinates: `Ā = (1,−2,0) ↦ (1,−2u,0)`, `S̄ ↦ (0,u,0)`.
(Proof ticket P-08, `Ax = B2, B8`: the paper's proof runs through Lemma 3.6 = B8, the
`E□ ≅ ⟨P,A⟩` HNN presentation (16), and the pro-2 Burnside basis theorem.) -/
theorem lemma_3_7 (B : BDecomposition) (u : ℤ_[2]ˣ) :
    ∃ Ψ : ContinuousMulEquiv D0 D0,
      B.e (abMk (Ψ d0A)) = Multiplicative.ofAdd (1, -2 * (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0S)) = Multiplicative.ofAdd (0, (u : ℤ_[2]), 0) := by
  sorry

/-- **Proposition 3.8, lifting half**: every `α_{u,b} ∈ Aut(B, χ₀)` — `t ↦ t`, `S̄ ↦ uS̄`,
`Ȳ ↦ Ȳ + bS̄` (paper (18)) — lifts to a continuous automorphism of `D₀` (surjectivity of
(17), in the explicit form Prop. 1.1's proof consumes).  Coordinates: `Ā ↦ (1,−2u,0)`,
`S̄ ↦ (0,u,0)`, `Ȳ ↦ (0,b,1)`.  (Proof ticket P-08: Lemma 3.7 composed with the shear
`Θ_b` of paper (19).) -/
theorem prop_3_8_lift (B : BDecomposition) (u : ℤ_[2]ˣ) (b : ℤ_[2]) :
    ∃ Ψ : ContinuousMulEquiv D0 D0,
      B.e (abMk (Ψ d0A)) = Multiplicative.ofAdd (1, -2 * (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0S)) = Multiplicative.ofAdd (0, (u : ℤ_[2]), 0) ∧
      B.e (abMk (Ψ d0Y)) = Multiplicative.ofAdd (0, b, 1) := by
  sorry

/-- **Proposition 3.8, classification half**: every continuous automorphism of `B`
preserving the orientation character `χ₀` (specified by its eq. (12)/(13) rows) has the form
`α_{u,b}` for a **unique** pair `(u, b) ∈ ℤ₂ˣ × ℤ₂` (paper (18)).  (Proof ticket P-08:
`ker χ₀ = ℤ₂S̄`, the torsion subgroup is `⟨t⟩`, and `η` generates `1 + 4ℤ₂` — pure (11)
module algebra.) -/
theorem prop_3_8_classification (B : BDecomposition)
    (ξ : ContinuousMulEquiv (topAbelianization D0) (topAbelianization D0))
    (χ : topAbelianization D0 →* ℤ_[2]ˣ) (hχ : Continuous χ)
    (hχA : χ (abMk d0A) = -1)
    (hχS : χ (abMk d0S) = 1)
    (hχY : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → χ (abMk d0Y) = y⁻¹)
    (hpres : ∀ x, χ (ξ x) = χ x) :
    ∃! p : ℤ_[2]ˣ × ℤ_[2],
      B.e (ξ (abMk d0A)) = Multiplicative.ofAdd (1, -2 * (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0S)) = Multiplicative.ofAdd (0, (p.1 : ℤ_[2]), 0) ∧
      B.e (ξ (abMk d0Y)) = Multiplicative.ofAdd (0, p.2, 1) := by
  sorry

/-! ## Proposition 1.1 — the marked dyadic Demushkin normalization

Paper: *"There exist topological generators `a, s, y` of `D = G_{ℚ₂}(2)` with
`D ≅ ⟨a,s,y | a²s⁴[s,y] = 1⟩_{pro-2}` and `ν_ur(a,s,y) = (−2,1,0)`."*  The generators-plus-
presentation clause is packaged as a continuous isomorphism `e : G_{ℚ₂}(2) ≅ D₀` (then
`a = e⁻¹(A)`, `s = e⁻¹(S)`, `y = e⁻¹(Y)` topologically generate and satisfy the relation, by
transport of `d0_relation`); the `ν_ur`-row is read through arbitrary lifts to `G_{ℚ₂}`, as
in the T-11 full-group readings (`chiCyc_eq_neg_one_of_lift_A`). -/

/-- **Proposition 1.1** (proof ticket P-10, `Ax = B3c, B4, B5, B7′`): a marked isomorphism
`G_{ℚ₂}(2) ≅ D₀` whose generators have unramified coordinates `ν_ur(a, s, y) = (−2, 1, 0)`.
The paper's proof composes B3c/B4 with Lemma 3.5 and Prop. 3.8; P-10 additionally needs the
descent lemma "`ν_ur ∘ toAb` is constant on `maxProPMk`-fibres" (i.e. `IsProP 2` of the
target, via `proPKernel_le_ker` — design note §1.1). -/
theorem prop_1_1 [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]
    (R : LocalReciprocity) :
    ∃ e : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0,
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0A →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((-2 : ℤ) : ℤ_[2])) ∧
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0S →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((1 : ℤ) : ℤ_[2])) ∧
      (∀ g : AbsGalQ2, maxProPMk 2 AbsGalQ2 g = e.symm d0Y →
        R.nu_ur (toAb g) = Multiplicative.ofAdd ((0 : ℤ) : ℤ_[2])) := by
  sorry

end SectionThree

end GQ2
