import GQ2.GammaA
import GQ2.MaxProP
import GQ2.ProfinitePresentation

/-!
# §4: the common boundary and Theorem 4.2  (ticket P-11)

The paper's §4 fixes, **once and for all**, a common finite-headed boundary shared by the two
source groups `Γ_A` and `G_ℚ₂`, and states the *boundary-framed exact-image theorem* (Thm 4.2) —
the technical heart of the proof of eq. (154), proved in §9 by strong induction on `|L_Y|`.
This file provides the §4 objects and the **statement** of Theorem 4.2 (`thm_4_2`, sorried:
the proof is tickets P-12–P-17).

## The paper's objects and their encodings

* **`Ttame`** (§3 opening display): the "finite-quotient tame group" `⟨σ, τ ∣ τ^σ = τ²⟩_prof` —
  `profinitePresentation {tameWord}` with `tameWord = conjP τ σ * (τ²)⁻¹` on `σ, τ = of 0, of 1`
  (paper conventions `x^g = g⁻¹xg`, `GQ2/Words.lean`).
* **`PiBd`** (paper `Π`, Prop 3.10 eq. (20)): the pro-2 group
  `⟨σ, x₀, x₁ ∣ x₀^{σ²} x₀ [x₁,σ] = 1⟩_pro-2`, encoded as
  `maxProPQuotient 2 (profinitePresentation {piRelator})` — a pro-`2` presentation is the maximal
  pro-2 quotient of the profinite presentation (same universal property on pro-2 targets; this is
  the repo's standing encoding, cf. `Δ` in `GQ2/PeripheralAction.lean`).  Generator order
  `σ, x₀, x₁ = of 0, of 1, of 2`; the relator's conjugation is by `σ²` (eq. (24) — note the
  superscript, easily lost: `x₀^{σ²}`, not `x₀^σ`).
* **`Ztwo`** (paper `Z₂`): the additive 2-adics as a profinite group, encoded
  `maxProPQuotient 2 Zhat` (the pro-2 completion of `ℤ`; `GQ2/Zhat.lean`).  `ztwoOne` is the
  image of `1 ∈ ℤ`.
* **`nuT`, `nuTwo`** (Prop 3.14's `ν_t` and eq. (21)'s `ν₂`): the unramified markings, pinned by
  `ν_t(σ) = 1, ν_t(τ) = 0` and `ν₂(σ) = 1, ν₂(x₀) = ν₂(x₁) = 0`, built by `presentationLift`
  (kill the relator, descend) and — for `nuTwo` — the T-05 universal property of `maxProP`
  (`proPKernel_le_ker`; the target `Ztwo` is pro-2 by `isProP_maxProPQuotient`).  The generator
  values are **proved** below (`nuT_tameSigma`, …) — they are this file's stress tests.
* **`boundarySubgroup` / `Boundary`** (eq. (26)): `∂bd = Ttame ×_{Z₂} Π`, encoded as the
  equalizer subgroup `{x : Ttame × Π ∣ ν_t x.1 = ν₂ x.2}` — closed (T2 target), hence profinite.
* **`BoundaryFrame`** (eq. (28)): the fixed frame data — a finite tame quotient
  `α : Ttame ↠ H`, an elementary abelian 2-group `E` (`[CommGroup E]` + `exponent_two`), and
  `ψ̄ : Π → E`; `frameMap` is `β(t, p) = (α t, ψ̄ p)`.
* **`MarkedTarget`** (Definition 4.1): `𝒴 = (Y, L_Y, π_Y, θ_Y)` with `L_Y ◁ Y` a finite
  2-group, `π_Y : Y ↠ H` with kernel `L_Y`, `θ_Y : Y → E`.  `[Finite Y]` is carried as a
  parameter (the paper implies it: `L_Y` finite + `H` finite); `IsPGroup 2 L_Y` then says
  exactly "finite 2-group".  `stratum` is the sub-target `𝒥 = (J, J ∩ L_Y, π_Y|_J, θ_Y|_J)`
  for `J ≤ Y` projecting onto `H`.
* **`IsBoundaryLift` / `BoundaryLifts` / `exactImageCount`** (eq. (29)): the *boundary
  equation* `q_Y ∘ f = β ∘ b_Γ` (pointwise, as one `H × E`-valued equation), the set of
  continuous epimorphisms satisfying it, and `e^β_Γ(𝒴) = Nat.card` of it.  `Nat.card` is `0`
  on infinite sets — same convention as `contSurjCount`/`admissibleCount`; under topological
  finite generation the set is genuinely finite (`finite_boundaryLifts`).  §5's "`ρ : Γ ↠ C`
  satisfies the boundary equation" and §8's `X_Γ(C)` (Def 8.1) are `BoundaryLifts` verbatim.

## The design decision: `BoundaryMaps` (the (27) epimorphisms as a hypothesis bundle)

Theorem 4.2 is stated relative to the maps `b_Γ : Γ ↠ ∂bd` of eq. (27), whose *existence* is
Proposition 3.14 — a §3 result (tickets P-06/P-09/P-10), **not constructible today** (the
`G_ℚ₂`-side needs wild inertia / B5-derived structure; the `Γ_A`-side needs Prop 3.2's
wild-relator computation).  Following the repo's bundle pattern (B5/B6/B8), the structure
`BoundaryMaps` carries the tame and pro-2 components of both maps together with the properties
Prop 3.14 asserts of them:

* `Γ_A`-side: pinned **rigidly** by generator values — `tameA : σ ↦ σ, τ ↦ τ, x₀, x₁ ↦ 1` and
  `pro2A : σ ↦ σ, τ ↦ 1, xᵢ ↦ xᵢ` (Prop 3.10 and Prop 3.14's proof).  A continuous hom out of
  `Γ_A` is determined by its values on the four topological generators, so these eight equations
  determine `tameA`/`pro2A` uniquely.
* `G_ℚ₂`-side: pinned **intrinsically** — `tameF` is surjective with kernel *the* characteristic
  2-core (Lemma 3.3's characterization of wild inertia `W_F = O₂(G_ℚ₂)`: the kernel is pro-2
  normal and contains every closed normal pro-2 subgroup), and `pro2F` is surjective with kernel
  exactly `proPKernel 2 AbsGalQ2` (i.e. *the* maximal pro-2 quotient map, T-05).
* both sides: the ν-compatibility (`compatA`/`compatF` — Prop 3.14's conclusion; this is what
  makes the pairs land in `∂bd`) and joint surjectivity onto `∂bd` (eq. (27); the paper derives
  it by profinite Goursat, so instantiators may prove rather than assume it).

`thm_4_2` quantifies over **all** `BoundaryMaps` witnesses.  This is the faithful reading:
Prop 3.14 says the quotient maps "**may be chosen** so that" the compatibility holds, and §4
fixes such a choice "**once and for all**" — nothing after §4 uses more about the choice than
the properties above.  **Flagged residual risk** (for P-17/P-20 review): if the §9 induction
turns out to use a property of the Prop 3.14 choice not listed here (cf. Remark 3.15 on the full
marking being load-bearing — the ν-compatibility field is exactly that marking), `BoundaryMaps`
must be extended, which is a reviewed statement change.  Instantiation: P-06 states Prop 3.10 /
3.14 against these definitions; P-09/P-10 prove them.

Axioms: **none** — the statement layer is axiom-free (matching App. D, where Thm 4.2's inputs
B6/B7/B7′/B8/B9 enter only through the §§5–9 *proof*, ticket P-17).  `thm_4_2` is the P-11
sorry (allowlisted, removed by P-17); `thm_4_2_stratum` — the theorem's second clause — is
*derived* from it, demonstrating that strata need no separate statement.
-/

open scoped Pointwise

namespace GQ2

/-! ## Descending homs from a profinite presentation

A continuous hom out of the free profinite group killing every relator kills their closed normal
closure (the kernel is closed and normal), hence descends to the presented group.  Stated here
for P-11's `ν`-maps; P-12 may promote it to `GQ2/ProfinitePresentation.lean`. -/

/-- Descend a relator-killing continuous hom to the profinite presentation. -/
noncomputable def presentationLift {X : Type} (rels : Set (FreeProfiniteGroup X)) {P : Type}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (f : ContinuousMonoidHom (FreeProfiniteGroup X) P) (hf : ∀ r ∈ rels, f r = 1) :
    ContinuousMonoidHom (FreeProfiniteGroup X ⧸ relatorSubgroup rels) P :=
  quotientLift (relatorSubgroup rels) f <| by
    have hker : IsClosed (f.toMonoidHom.ker : Set (FreeProfiniteGroup X)) := by
      have hset : (f.toMonoidHom.ker : Set (FreeProfiniteGroup X)) = f ⁻¹' {1} := by
        ext g; simp [MonoidHom.mem_ker]
      rw [hset]
      exact IsClosed.preimage f.continuous_toFun isClosed_singleton
    exact Subgroup.topologicalClosure_minimal _
      (Subgroup.normalClosure_le_normal fun r hr => MonoidHom.mem_ker.mpr (hf r hr)) hker

@[simp] theorem presentationLift_mk {X : Type} (rels : Set (FreeProfiniteGroup X)) {P : Type}
    [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [T2Space P]
    (f : ContinuousMonoidHom (FreeProfiniteGroup X) P) (hf : ∀ r ∈ rels, f r = 1)
    (w : FreeProfiniteGroup X) :
    presentationLift rels f hf (quotientMk (relatorSubgroup rels) w) = f w :=
  rfl

/-! ## The three boundary constituents: `Ttame`, `Π`, `Z₂` -/

/-- The tame relator `τ^σ · (τ²)⁻¹` in the free profinite group on `σ, τ = of 0, of 1`. -/
noncomputable def tameWord : FreeProfiniteGroup (Fin 2) :=
  conjP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 0) * (FreeProfiniteGroup.of 1 ^ 2)⁻¹

/-- **`T_tame`** (§3 opening): the finite-quotient tame group `⟨σ, τ ∣ τ^σ = τ²⟩_prof`. -/
noncomputable def Ttame : ProfiniteGrp := profinitePresentation {tameWord}

/-- The image of `σ` in `Ttame`. -/
noncomputable def tameSigma : Ttame :=
  quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 0)

/-- The image of `τ` in `Ttame`. -/
noncomputable def tameTau : Ttame :=
  quotientMk (relatorSubgroup {tameWord}) (FreeProfiniteGroup.of 1)

/-- The relator of eq. (24)/(20): `x₀^{σ²} · x₀ · [x₁, σ]` in the free profinite group on
`σ, x₀, x₁ = of 0, of 1, of 2`.  (Conjugation by `σ` **squared**.) -/
noncomputable def piRelator : FreeProfiniteGroup (Fin 3) :=
  conjP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 0 ^ 2) * FreeProfiniteGroup.of 1 *
    commP (FreeProfiniteGroup.of 2) (FreeProfiniteGroup.of 0)

/-- **`Π`** (Prop 3.10, eq. (20)): the pro-2 group `⟨σ, x₀, x₁ ∣ x₀^{σ²} x₀ [x₁,σ] = 1⟩_pro-2`,
encoded as the maximal pro-2 quotient of the profinite presentation. -/
noncomputable def PiBd : ProfiniteGrp :=
  maxProPQuotient 2 (profinitePresentation {piRelator})

/-- The image of `σ` in `Π`. -/
noncomputable def piSigma : PiBd :=
  maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 0))

/-- The image of `x₀` in `Π`. -/
noncomputable def piX0 : PiBd :=
  maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 1))

/-- The image of `x₁` in `Π`. -/
noncomputable def piX1 : PiBd :=
  maxProPMk 2 (profinitePresentation {piRelator})
    (quotientMk (relatorSubgroup {piRelator}) (FreeProfiniteGroup.of 2))

/-- **`Z₂`**: the additive 2-adic integers as a profinite group, encoded as the pro-2
completion of `ℤ` (the maximal pro-2 quotient of `ℤ̂`, `GQ2/Zhat.lean`). -/
noncomputable def Ztwo : ProfiniteGrp := maxProPQuotient 2 Zhat

/-- The image of `1 ∈ ℤ` in `Z₂` — the common value `ν_t(σ) = ν₂(σ) = 1`. -/
noncomputable def ztwoOne : Ztwo := maxProPMk 2 Zhat (Zhat.ofInt 1)

/-! ## The unramified markings `ν_t` and `ν₂`  (Prop 3.14, eq. (21)) -/

/-- The classifying map `σ ↦ 1, τ ↦ 0` into `ℤ̂` (multiplicative: `ofInt 1`, `1`). -/
noncomputable def tameToZhat : ContinuousMonoidHom (FreeProfiniteGroup (Fin 2)) Zhat :=
  ((FreeProfiniteGroup.homEquiv (Fin 2) Zhat).symm ![Zhat.ofInt 1, 1]).hom

@[simp] theorem tameToZhat_of_zero : tameToZhat (FreeProfiniteGroup.of 0) = Zhat.ofInt 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem tameToZhat_of_one : tameToZhat (FreeProfiniteGroup.of 1) = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem tameToZhat_tameWord : tameToZhat tameWord = 1 := by
  simp only [tameWord, conjP, map_mul, map_inv, map_pow, tameToZhat_of_zero, tameToZhat_of_one]
  group

/-- **`ν_t : Ttame ↠ Z₂`** (Prop 3.14): `ν_t(σ) = 1`, `ν_t(τ) = 0`.  (Surjectivity is a
§3 fact, P-06/P-09 scope; only the map is needed to *state* §4.) -/
noncomputable def nuT : ContinuousMonoidHom Ttame Ztwo :=
  presentationLift {tameWord} ((maxProPMk 2 Zhat).comp tameToZhat) <| by
    intro r hr
    rcases hr with rfl
    show maxProPMk 2 Zhat (tameToZhat tameWord) = 1
    rw [tameToZhat_tameWord, map_one]

@[simp] theorem nuT_tameSigma : nuT tameSigma = ztwoOne := by
  show maxProPMk 2 Zhat (tameToZhat (FreeProfiniteGroup.of 0)) = ztwoOne
  rw [tameToZhat_of_zero]
  rfl

@[simp] theorem nuT_tameTau : nuT tameTau = 1 := by
  show maxProPMk 2 Zhat (tameToZhat (FreeProfiniteGroup.of 1)) = 1
  rw [tameToZhat_of_one, map_one]

/-- The classifying map `σ ↦ 1, x₀ ↦ 0, x₁ ↦ 0` into `ℤ̂`. -/
noncomputable def wildToZhat : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) Zhat :=
  ((FreeProfiniteGroup.homEquiv (Fin 3) Zhat).symm ![Zhat.ofInt 1, 1, 1]).hom

@[simp] theorem wildToZhat_of_zero : wildToZhat (FreeProfiniteGroup.of 0) = Zhat.ofInt 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem wildToZhat_of_one : wildToZhat (FreeProfiniteGroup.of 1) = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

@[simp] theorem wildToZhat_of_two : wildToZhat (FreeProfiniteGroup.of 2) = 1 :=
  FreeProfiniteGroup.homEquiv_symm_of _ _ _

theorem wildToZhat_piRelator : wildToZhat piRelator = 1 := by
  simp only [piRelator, conjP, commP, map_mul, map_inv, map_pow, wildToZhat_of_zero,
    wildToZhat_of_one, wildToZhat_of_two]
  group

/-- The descent of `wildToZhat` to the presented (not yet pro-2) group. -/
noncomputable def prePiToZtwo :
    ContinuousMonoidHom (profinitePresentation {piRelator}) Ztwo :=
  presentationLift {piRelator} ((maxProPMk 2 Zhat).comp wildToZhat) <| by
    intro r hr
    rcases hr with rfl
    show maxProPMk 2 Zhat (wildToZhat piRelator) = 1
    rw [wildToZhat_piRelator, map_one]

/-- **`ν₂ : Π ↠ Z₂`** (eq. (21)): `ν₂(σ) = 1`, `ν₂(x₀) = ν₂(x₁) = 0`.  Descends through the
maximal pro-2 quotient by the T-05 universal property (`Z₂` is pro-2). -/
noncomputable def nuTwo : ContinuousMonoidHom PiBd Ztwo :=
  quotientLift (proPKernel 2 (profinitePresentation {piRelator})) prePiToZtwo
    (proPKernel_le_ker isProP_maxProPQuotient prePiToZtwo)

@[simp] theorem nuTwo_piSigma : nuTwo piSigma = ztwoOne := by
  show maxProPMk 2 Zhat (wildToZhat (FreeProfiniteGroup.of 0)) = ztwoOne
  rw [wildToZhat_of_zero]
  rfl

@[simp] theorem nuTwo_piX0 : nuTwo piX0 = 1 := by
  show maxProPMk 2 Zhat (wildToZhat (FreeProfiniteGroup.of 1)) = 1
  rw [wildToZhat_of_one, map_one]

@[simp] theorem nuTwo_piX1 : nuTwo piX1 = 1 := by
  show maxProPMk 2 Zhat (wildToZhat (FreeProfiniteGroup.of 2)) = 1
  rw [wildToZhat_of_two, map_one]

/-! ## The common boundary `∂bd = Ttame ×_{Z₂} Π`  (eq. (26)) -/

/-- The fiber product (26) as the equalizer subgroup of `Ttame × Π`. -/
noncomputable def boundarySubgroup : Subgroup (Ttame × PiBd) where
  carrier := {x | nuT x.1 = nuTwo x.2}
  one_mem' := by simp only [Set.mem_setOf_eq, Prod.fst_one, Prod.snd_one, map_one]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq, Prod.fst_mul, Prod.snd_mul, map_mul] at *
    rw [ha, hb]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq, Prod.fst_inv, Prod.snd_inv, map_inv] at *
    rw [ha]

theorem isClosed_boundarySubgroup :
    IsClosed (boundarySubgroup : Set (Ttame × PiBd)) :=
  isClosed_eq (nuT.continuous_toFun.comp continuous_fst)
    (nuTwo.continuous_toFun.comp continuous_snd)

instance instCompactSpaceBoundarySubgroup : CompactSpace ↥boundarySubgroup :=
  isCompact_iff_compactSpace.mp isClosed_boundarySubgroup.isCompact

/-- **`∂bd`** (eq. (26)), packaged as a profinite group.  The working definitions below use the
underlying type `↥boundarySubgroup` directly. -/
noncomputable def Boundary : ProfiniteGrp := ProfiniteGrp.of ↥boundarySubgroup

/-! ## The frame  (eq. (28)) -/

/-- **The boundary frame** (§4, eq. (28)): a finite tame quotient `α : Ttame ↠ H`, an
elementary abelian 2-group `E`, and a homomorphism `ψ̄ : Π → E`.  (`[Finite E]` is carried:
frames with infinite `E` factor through the finite image of `ψ̄`/`θ_Y`, and Lemma 10.1 sums
over finitely many frames.) -/
structure BoundaryFrame (H E : Type) [Group H] [TopologicalSpace H] [DiscreteTopology H]
    [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E] where
  /-- The finite tame quotient map `α : Ttame ↠ H`. -/
  alpha : ContinuousMonoidHom Ttame H
  alpha_surjective : Function.Surjective alpha
  /-- `E` has exponent 2 ("elementary abelian"). -/
  exponent_two : ∀ e : E, e ^ 2 = 1
  /-- The scalar datum `ψ̄ : Π → E`. -/
  psiBar : ContinuousMonoidHom PiBd E

/-- The comparison map `β : ∂bd → H × E`, `β(t, p) = (α t, ψ̄ p)`  (eq. (28)). -/
noncomputable def BoundaryFrame.frameMap {H E : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    [Finite E] (F : BoundaryFrame H E) (x : ↥boundarySubgroup) : H × E :=
  (F.alpha x.val.1, F.psiBar x.val.2)

/-! ## Boundary-framed marked targets  (Definition 4.1) -/

/-- **Boundary-framed marked target** (Definition 4.1): `𝒴 = (Y, L_Y, π_Y, θ_Y)` with
`L_Y ◁ Y` a finite 2-group, `π_Y : Y ↠ H` with kernel `L_Y`, and `θ_Y : Y → E` a homomorphism.
`Y` finite is implied by the paper (`L_Y` and `H` finite) and carried as `[Finite Y]`. -/
structure MarkedTarget (H E Y : Type) [Group H] [Group E] [Group Y] [Finite Y] where
  /-- The marked normal 2-subgroup `L_Y`. -/
  LY : Subgroup Y
  normal : LY.Normal
  /-- `L_Y` is a 2-group (finite, since `Y` is). -/
  isPGroup_two : IsPGroup 2 LY
  /-- The head map `π_Y : Y ↠ H`. -/
  piY : Y →* H
  piY_surjective : Function.Surjective piY
  /-- `ker π_Y = L_Y`. -/
  ker_piY : piY.ker = LY
  /-- The scalar decoration `θ_Y : Y → E`. -/
  thetaY : Y →* E

variable {H E Y : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]

/-- **Exact-image stratum** (§4, after Def 4.1): for `J ≤ Y` projecting onto `H`, the
sub-target `𝒥 = (J, J ∩ L_Y, π_Y|_J, θ_Y|_J)` — "an ordinary object of the same category". -/
def MarkedTarget.stratum [Group Y] [Finite Y] (T : MarkedTarget H E Y) (J : Subgroup Y)
    (hJ : Function.Surjective (T.piY.comp J.subtype)) : MarkedTarget H E ↥J where
  LY := T.LY.subgroupOf J
  normal := T.normal.subgroupOf J
  isPGroup_two := by
    intro x
    obtain ⟨k, hk⟩ := T.isPGroup_two ⟨(x : ↥J), Subgroup.mem_subgroupOf.mp x.2⟩
    exact ⟨k, by ext : 2; simpa using congrArg Subtype.val hk⟩
  piY := T.piY.comp J.subtype
  piY_surjective := hJ
  ker_piY := by
    ext x
    simp [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, ← T.ker_piY]
  thetaY := T.thetaY.comp J.subtype

/-! ## The exact-image counts  (eq. (29)) -/

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]

/-- The **boundary equation** of eq. (29) (also §5's "`ρ` satisfies the boundary equation"):
`q_Y ∘ f = β ∘ b_Γ`, pointwise on `Γ`, where `q_Y = (π_Y, θ_Y)`. -/
def IsBoundaryLift [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) (f : ContinuousMonoidHom Γ Y) : Prop :=
  ∀ γ : Γ, (T.piY (f γ), T.thetaY (f γ)) = F.frameMap (b γ)

/-- The set counted by eq. (29): continuous epimorphisms `f : Γ ↠ Y` satisfying the boundary
equation.  §8's `X_Γ(C)` (Def 8.1) is this set for the lower target `C`. -/
def BoundaryLifts [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) : Type :=
  {f : ContSurj Γ Y // IsBoundaryLift b F T f.1}

/-- **`e^β_Γ(𝒴)`** (eq. (29)): the number of boundary-compatible continuous epimorphisms
`Γ ↠ Y`.  `Nat.card` (`0` on infinite sets, as for `contSurjCount`); finiteness under
topological finite generation is `finite_boundaryLifts`. -/
noncomputable def exactImageCount [Group Y] [TopologicalSpace Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y) : ℕ :=
  Nat.card (BoundaryLifts b F T)

/-- The count (29) is genuinely finite when `Γ` is a topologically finitely generated
profinite group (`Γ_A` after P-03; `G_ℚ₂` by axiom B1). -/
theorem finite_boundaryLifts [IsTopologicalGroup Γ] [CompactSpace Γ]
    [TotallyDisconnectedSpace Γ] [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (b : ContinuousMonoidHom Γ ↥boundarySubgroup) (F : BoundaryFrame H E)
    (T : MarkedTarget H E Y)
    (hfg : ∃ s : Finset Γ, (Subgroup.closure (s : Set Γ)).topologicalClosure = ⊤) :
    Finite (BoundaryLifts b F T) := by
  haveI : Finite (ContinuousMonoidHom Γ Y) := finite_continuousMonoidHom hfg Y
  haveI : Finite (ContSurj Γ Y) := Subtype.finite
  exact Subtype.finite

/-! ## The Prop 3.14 interface: the epimorphisms `b_Γ`  (eq. (27)) -/

/-- **The boundary maps of eq. (27)**, as the tame/pro-2 component pairs Prop 3.14 provides —
carried as a hypothesis bundle (its existence is §3 content: P-06 states it, P-09/P-10 prove
it).  See the module docstring for the pinning rationale: the `Γ_A`-components are determined
by their generator values; the `G_ℚ₂`-components by Lemma 3.3's 2-core characterization of wild
inertia and by `proPKernel` (T-05); `compat…` is Prop 3.14's ν-compatibility (the "full
marking", Remark 3.15); `surj…` is eq. (27)'s joint surjectivity. -/
structure BoundaryMaps where
  /-- The tame quotient map of `Γ_A`. -/
  tameA : ContinuousMonoidHom GammaA Ttame
  /-- The maximal pro-2 quotient map of `Γ_A` (Prop 3.10). -/
  pro2A : ContinuousMonoidHom GammaA PiBd
  /-- Prop 3.14 for `Γ_A`: `ν_t ∘ tame = ν₂ ∘ pro2`. -/
  compatA : ∀ g : GammaA, nuT (tameA g) = nuTwo (pro2A g)
  tameA_sigma : tameA (quotientMk NA univMarking.σ) = tameSigma
  tameA_tau : tameA (quotientMk NA univMarking.τ) = tameTau
  tameA_x0 : tameA (quotientMk NA univMarking.x₀) = 1
  tameA_x1 : tameA (quotientMk NA univMarking.x₁) = 1
  pro2A_sigma : pro2A (quotientMk NA univMarking.σ) = piSigma
  pro2A_tau : pro2A (quotientMk NA univMarking.τ) = 1
  pro2A_x0 : pro2A (quotientMk NA univMarking.x₀) = piX0
  pro2A_x1 : pro2A (quotientMk NA univMarking.x₁) = piX1
  /-- Eq. (27) for `Γ_A`: `b_{Γ_A} : Γ_A ↠ ∂bd`. -/
  surjA : Function.Surjective
    (fun g : GammaA => (⟨(tameA g, pro2A g), compatA g⟩ : ↥boundarySubgroup))
  /-- The tame quotient map of `G_ℚ₂`. -/
  tameF : ContinuousMonoidHom AbsGalQ2 Ttame
  /-- The maximal pro-2 quotient map of `G_ℚ₂`. -/
  pro2F : ContinuousMonoidHom AbsGalQ2 PiBd
  /-- Prop 3.14 for `G_ℚ₂` (Cor 3.12: the full marked identification). -/
  compatF : ∀ g : AbsGalQ2, nuT (tameF g) = nuTwo (pro2F g)
  tameF_surjective : Function.Surjective tameF
  /-- The kernel of the tame quotient is pro-2 (wild inertia is a pro-2 group). -/
  wild_isProP : IsProP 2 tameF.toMonoidHom.ker
  /-- …and it is the **largest** closed normal pro-2 subgroup — Lemma 3.3's characterization
  `W_F = O₂(G_ℚ₂)`, which pins the tame quotient intrinsically. -/
  wild_isMax : ∀ N : Subgroup AbsGalQ2, N.Normal → IsClosed (N : Set AbsGalQ2) →
    IsProP 2 N → N ≤ tameF.toMonoidHom.ker
  pro2F_surjective : Function.Surjective pro2F
  /-- `pro2F` is *the* maximal pro-2 quotient map: its kernel is the pro-2 kernel of T-05. -/
  ker_pro2F : pro2F.toMonoidHom.ker = proPKernel 2 AbsGalQ2
  /-- Eq. (27) for `G_ℚ₂`: `b_{G_ℚ₂} : G_ℚ₂ ↠ ∂bd`. -/
  surjF : Function.Surjective
    (fun g : AbsGalQ2 => (⟨(tameF g, pro2F g), compatF g⟩ : ↥boundarySubgroup))

namespace BoundaryMaps

variable (B : BoundaryMaps)

/-- `b_{Γ_A} : Γ_A → ∂bd`  (eq. (27)). -/
noncomputable def bA : ContinuousMonoidHom GammaA ↥boundarySubgroup :=
  ⟨(B.tameA.toMonoidHom.prod B.pro2A.toMonoidHom).codRestrict boundarySubgroup
      fun g => B.compatA g,
    (B.tameA.continuous_toFun.prodMk B.pro2A.continuous_toFun).subtype_mk _⟩

/-- `b_{G_ℚ₂} : G_ℚ₂ → ∂bd`  (eq. (27)). -/
noncomputable def bF : ContinuousMonoidHom AbsGalQ2 ↥boundarySubgroup :=
  ⟨(B.tameF.toMonoidHom.prod B.pro2F.toMonoidHom).codRestrict boundarySubgroup
      fun g => B.compatF g,
    (B.tameF.continuous_toFun.prodMk B.pro2F.continuous_toFun).subtype_mk _⟩

@[simp] theorem bA_apply_coe (g : GammaA) : (B.bA g : Ttame × PiBd) = (B.tameA g, B.pro2A g) :=
  rfl

@[simp] theorem bF_apply_coe (g : AbsGalQ2) :
    (B.bF g : Ttame × PiBd) = (B.tameF g, B.pro2F g) := rfl

theorem bA_surjective : Function.Surjective B.bA := B.surjA

theorem bF_surjective : Function.Surjective B.bF := B.surjF

end BoundaryMaps

/-! ## Theorem 4.2 -/

/-- **Theorem 4.2 (boundary-framed exact-image theorem).**  For every boundary frame and every
boundary-framed marked target `𝒴`, the exact-image lift counts from the two sources agree:
`e^β_{Γ_A}(𝒴) = e^β_{G_ℚ₂}(𝒴)`.

Stated for any `BoundaryMaps` witness of the Prop 3.14 data (see the module docstring; the
choice is fixed "once and for all" in §4 and only its bundled properties are used).

*Status*: sorried — this is the technical heart (P-11 statement; proof = §§5–9, tickets
P-12–P-17, by strong induction on `|L_Y|` with Lemma 9.4's strict decrease; axioms
B6/B7/B7′/B8/B9 enter there, per App. D). -/
theorem thm_4_2 (B : BoundaryMaps) {H E : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    [Finite E] (F : BoundaryFrame H E) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y) :
    exactImageCount B.bA F T = exactImageCount B.bF F T := by
  sorry

/-- Theorem 4.2's second clause: "the same equality holds for every exact-image target `𝒥`" —
an *instance* of the first (strata are ordinary objects of the same category), recorded to fix
the consumption shape for §8. -/
theorem thm_4_2_stratum (B : BoundaryMaps) {H E : Type} [Group H] [TopologicalSpace H]
    [DiscreteTopology H] [Finite H] [CommGroup E] [TopologicalSpace E] [DiscreteTopology E]
    [Finite E] (F : BoundaryFrame H E) {Y : Type} [Group Y] [TopologicalSpace Y]
    [DiscreteTopology Y] [Finite Y] (T : MarkedTarget H E Y) (J : Subgroup Y)
    (hJ : Function.Surjective (T.piY.comp J.subtype)) :
    exactImageCount B.bA F (T.stratum J hJ) = exactImageCount B.bF F (T.stratum J hJ) :=
  thm_4_2 B F (T.stratum J hJ)

end GQ2
