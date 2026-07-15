/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.LocalKummer
import GQ2.OrbitVanish
import GQ2.Shapiro.Extend

/-!
# Shapiro coordinates + scalar deepness (the `hvanish` producers)

The two per-orbit hypotheses of `OrbitVanish.Q0loc_vanish_of_datum_decomp` for the deep half
`x ∈ deepPart ρ`:

* **`hcoh`** — each per-orbit graph pullback is cohomologous to its `cor2Fun` corestriction.
  This is a direct application of the banked `SectionSix.lemma_6_15_{square,free,involution}`;
  the Lemma 6.17 vanishing proof (`OrbitDecomp.lean`) structures each `datf o` as a definitional `comap` of the
  literal orbit datum so the pullbacks are *syntactically* the Lemma-6.15 inputs — the
  instantiation is done at f2d.

* **`hvanish`** — each corestriction's **inner** cocycle vanishes in its subgroup's `H²`.
  For square/free orbits the inner cocycle is a cup `α ⌣ α'` of scalar Shapiro coordinates,
  which vanish because those coordinates are **deep** (`x ∈ deepPart` ⟹ every scalar
  restriction is a deep Kummer class, `LocalKummer.mem_deepPart_iff`), via the eq.-(94)
  orthogonality `LocalKummer.cup_deepClasses`.  This file proves that reduction —
  **`hvanish_cup`** — the self-contained core of the square and free cases.  (The involution
  case, `hvanish` via `lemma_6_16`'s Evens-norm vanishing, is the remaining piece;
  design record `docs/orchestration/p15f2c-design.md`.)

Axioms: B9, B11a (through `cup_deepClasses`/(94)).
-/

namespace GQ2

namespace ShapiroDeepness

open ContCoh SectionSix LocalKummer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]

/-- **The `H²mk → H²ofFun` vanishing bridge**: a 2-cocycle whose `H²mk` class is `0` has trivial
`H²ofFun`.  The shared tail of both `hvanish` cases. -/
theorem H2ofFun_eq_zero_of_H2mk {φ : G × G → ZMod 2} (hZ2 : φ ∈ Z2 G (ZMod 2))
    (h0 : H2mk G (ZMod 2) ⟨φ, hZ2⟩ = 0) : H2ofFun G φ = 0 := by
  rwa [H2ofFun_of_mem hZ2]

/-- **The deep-class cup vanishing** (the Lemma 6.17 vanishing proof, the square/free `hvanish` core): if two scalar
cocycles `a, b` over `k.fixingSubgroup` have **deep** classes, their cup 2-cochain
`α ⌣ β` has trivial `H²ofFun` class.  Composes the eq.-(94) orthogonality
`LocalKummer.cup_deepClasses` (`trivialCupPairing = 0`) with the `cup11`/`H2mk` identification
and `B²`-extraction.  This is `H2ofFun ↥(U o) (inner o) = 0` for the square orbit
(`inner o = α ⌣ α`, `U o = k.fixingSubgroup = ker ρ`) and, at `a ≠ b`, the free orbit. -/
theorem hvanish_cup (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (a b : Z1 k.fixingSubgroup (ZMod 2))
    (ha : H1mk k.fixingSubgroup (ZMod 2) a ∈ deepClasses k.fixingSubgroup)
    (hb : H1mk k.fixingSubgroup (ZMod 2) b ∈ deepClasses k.fixingSubgroup) :
    H2ofFun k.fixingSubgroup (cup11Fun AddMonoidHom.mul a.1 b.1) = 0 := by
  have hZ2 : cup11Fun AddMonoidHom.mul a.1 b.1 ∈ Z2 k.fixingSubgroup (ZMod 2) :=
    cup11_mem_Z2 AddMonoidHom.mul (fun g m n => by rw [htriv, htriv, htriv]) a b
  -- eq.-(94): the deep classes cup to zero; `trivialCupPairing = cup11 = H2mk ⟨cup11Fun⟩`
  exact H2ofFun_eq_zero_of_H2mk hZ2 (cup_deepClasses k htriv ha hb)

/-- **The involution `hvanish` cochain bridge** (the Lemma 6.17 vanishing proof): the Evens-norm class `evensNormH2`
being zero (its content is `lemma_6_16`, for a **deep** scalar coordinate) gives the required
`H2ofFun (evensNormFun …) = 0` — the involution-orbit `inner o = evensNormFun`, `U o = U₀`.
f2d composes `lemma_6_16` (with the block's concrete Kummer field data) with this bridge. -/
theorem hvanish_evensNorm {U : Subgroup G} {s : G}
    (htriv : ∀ (g : G) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (U : Set G)) (hUi : U.index = 2) (hs : s ∉ U)
    (α : ↥U → ZMod 2) (hα : ∀ u v : ↥U, α (u * v) = α u + α v) (hαc : Continuous α)
    (h0 : evensNormH2 htriv hUo hUi hs α hα hαc = 0) :
    H2ofFun G (evensNormFun U s α) = 0 :=
  H2ofFun_eq_zero_of_H2mk (evensNormFun_mem_Z2 htriv hUo hUi hs α hα hαc) h0

/-! ## Deepness transport across the equivariant coefficient embedding (f2d) -/

section DeepTransport

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {W₁ W₂ : Type}
  [AddCommGroup W₁] [TopologicalSpace W₁] [DiscreteTopology W₁] [Finite W₁]
  [DistribMulAction AbsGalQ2 W₁] [ContinuousSMul AbsGalQ2 W₁] [DistribMulAction C W₁]
  [AddCommGroup W₂] [TopologicalSpace W₂] [DiscreteTopology W₂] [Finite W₂]
  [DistribMulAction AbsGalQ2 W₂] [ContinuousSMul AbsGalQ2 W₂] [DistribMulAction C W₂]
  [IsTopologicalAddGroup W₁] [IsTopologicalAddGroup W₂]
variable {ρ : ContinuousMonoidHom AbsGalQ2 C}

omit [DiscreteTopology C] [Finite C] [Finite W₁] [Finite W₂] in
/-- **Deepness transports along an equivariant coefficient map** (the Lemma 6.17 vanishing proof): if `x ∈ deepPart ρ`
over `W₁` and `f : W₁ →+ W₂` is a continuous `AbsGalQ2`-equivariant map, then the pushed-forward
class `mapCoeff1 f x` is in `deepPart ρ` over `W₂`.  Every scalar restriction of `mapCoeff1 f x`
is a scalar restriction of `x` at the pre-composed functional (`ShapiroExtend.phiRes_mapCoeff1`),
which is deep because `x` is.  This carries the deep half `X₊` across the Lemma-6.14 regular
embedding `ι : V →+ W` (the deepness half of the transport, the companion of the isometry). -/
theorem deepPart_mapCoeff1
    (hρ₁ : ∀ (g : AbsGalQ2) (w : W₁), g • w = ρ g • w)
    (hρ₂ : ∀ (g : AbsGalQ2) (w : W₂), g • w = ρ g • w)
    (f : W₁ →+ W₂) (hf : Continuous f)
    (hcompat : ∀ (g : AbsGalQ2) (w : W₁), f (g • w) = g • f w)
    {x : H1 AbsGalQ2 W₁} (hx : x ∈ deepPart ρ) :
    mapCoeff1 f hf hcompat x ∈ deepPart ρ := by
  rw [mem_deepPart_iff] at hx ⊢
  intro φ
  rw [ShapiroExtend.phiRes_mapCoeff1 hρ₁ hρ₂ f hf hcompat x φ]
  exact hx (φ.comp f)

end DeepTransport

/-! ## Reindexing the acting group of a factor-set datum (the C ↔ `AbsGalQ2 ⧸ ker ρ` bridge) -/

section Reindex

variable {C C' V Γ : Type*} [Group C] [Group C'] [AddCommGroup V]
  [DistribMulAction C V] [DistribMulAction C' V]

/-- Reindex a factor-set datum's acting group along `φ : C' → C` — only the correction `m` sees
the group, so `f` is unchanged and `m` pre-composes with `φ`. -/
def _root_.GQ2.FactorSet.reindexHom (dat : FactorSet C V) (φ : C' → C) : FactorSet C' V where
  f := dat.f
  m c' v := dat.m (φ c') v

/-- **`graphPullback` reindexing** (the Lemma 6.17 vanishing proof, the linchpin of the C ↔ `AbsGalQ2 ⧸ ker ρ` bridge):
pulling back the `φ`-reindexed datum along `ρ' : Γ → C'` equals pulling back the original datum
along `φ ∘ ρ'`, provided the `C'`-action on `V` is the `φ`-pullback of the `C`-action (`hφ`).
f2b's orbit datum lives over `G ⧸ N` while the ambient `Q0loc`/Lemma-6.14 transport is over `C`;
with `φ = e : C → AbsGalQ2 ⧸ ker ρ` and `e ∘ ρ = mk' (ker ρ)` this identifies the two graph
pullbacks so the banked `lemma_6_15_*` (stated at `mk' N`) apply. -/
theorem graphPullback_reindexHom (dat : FactorSet C V) (φ : C' → C)
    (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v) (ρ' : Γ → C') (b : Γ → V) :
    graphPullback (dat.reindexHom φ) ρ' b = graphPullback dat (φ ∘ ρ') b := by
  funext p
  show dat.f (b p.1) (ρ' p.1 • b p.2) + dat.m (φ (ρ' p.1)) (b p.2)
      = dat.f (b p.1) (φ (ρ' p.1) • b p.2) + dat.m (φ (ρ' p.1)) (b p.2)
  rw [hφ]

end Reindex

section ReindexQ0loc

variable {C C' : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
  [Group C'] [TopologicalSpace C'] [DiscreteTopology C'] [Finite C']
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V]
  [DistribMulAction C V] [DistribMulAction C' V]

omit [DiscreteTopology C] [Finite C] [DiscreteTopology C'] [Finite C'] [Finite V]
  [ContinuousSMul AbsGalQ2 V] in
/-- **`Q0loc` reindexing** (the Lemma 6.17 vanishing proof): lifts `graphPullback_reindexHom` from the raw cochain to the
base connecting map — `Q⁰_loc` of the `φ`-reindexed datum along `ρ'` equals `Q⁰_loc` of the datum
along `φ ∘ ρ'`.  In the assembly, with `φ = e : C → AbsGalQ2 ⧸ ker ρ` (`e ∘ ρ = mk' (ker ρ)`), this
rewrites the C-level Lemma-6.14 output as the `mk'`-level orbit map so the orbit reducer fires. -/
theorem Q0loc_reindexHom (D : TateDuality 2) (dat : FactorSet C V)
    (φ : ContinuousMonoidHom C' C) (hφ : ∀ (c' : C') (v : V), c' • v = φ c' • v)
    (ρ' : ContinuousMonoidHom AbsGalQ2 C') (x : H1 AbsGalQ2 V) :
    Q0loc D (dat.reindexHom φ) ρ' x = Q0loc D dat (φ.comp ρ') x := by
  show iotaF D (H2ofFun AbsGalQ2 (graphPullback (dat.reindexHom ⇑φ) ⇑ρ' (Quotient.out x).1))
      = iotaF D (H2ofFun AbsGalQ2 (graphPullback dat (⇑(φ.comp ρ')) (Quotient.out x).1))
  rw [graphPullback_reindexHom dat (⇑φ) hφ ⇑ρ' (Quotient.out x).1]
  rfl

end ReindexQ0loc

/-! ## The involution-orbit `hvanish`, assembled -/

section InvolutionAssembly

/-- **The involution-orbit `hvanish`, assembled from `lemma_6_16`** (the Lemma 6.17 vanishing proof, the spine's
assembly core): given the concrete Kummer field data of the deep unit `A` at an involution block
coordinate — the tower `k ≤ L` (index 2, unramified `hunram`), the √-generator `(d, δ, hδ, hδL,
hLδ)`, the coordinates `A = u + vδ`, and the deep-unit/side-condition witnesses — the involution
inner cochain `evensNormFun (…)` has trivial `H²ofFun` over `↥(k.fixingSubgroup)`.  This is the
reducer's involution `hvanish`, stated in `k.fixingSubgroup` vocabulary (f2d bridges
`k.fixingSubgroup = U₀` — the InfiniteGalois transport `fixingSubgroup (fixedField U₀) = U₀` — to
the reducer's `↥U₀` form).

Proof: `SectionSix.lemma_6_16` gives `evensNormH2 … = 0`; the banked `hvanish_evensNorm` descends
it to `H²ofFun`.

The field data is threaded as hypotheses — the c2a "abstract Kummer presentation package"
∃-interface `(d, δ, hδ, hδL, hLδ, u, v, hAuv)` plus the deep witness `(A, β, hdeep, …)` from
`mem_deepPart_iff`/`deepClass_eq_kummerClassK` (the f2d/plumbing step).  **`hunram` HOLDS for every
involution orbit** (Step-0 decision, `docs/orchestration/p15f2c-design.md`): `ρ(ĝ)` is order 2 in `C`, but `C`'s
tame inertia `⟨c tameTau⟩` has odd order (`Tame.tame_odd_order`), so `ρ(ĝ) ∉ inertia` ⟹ `L/k`
unramified; c2c discharges `hunram` in spectral-norm vocabulary.
**Ax: B9, B11a (via `lemma_6_16`).** -/
theorem hvanish_involution (k L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] k] (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)).index = 2)
    (hunram : ∀ x : AlgebraicClosure ℚ_[2], x ≠ 0 → x ∈ L →
      ∃ y : AlgebraicClosure ℚ_[2], y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖)
    (d : (↥k)ˣ) (δ : AlgebraicClosure ℚ_[2]) (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
    (hδL : δ ∈ L)
    (hLδ : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
      = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup))
    (A β : AlgebraicClosure ℚ_[2]) (hdeep : IsDeepUnit L.fixingSubgroup A) (hβ : β ^ 2 = A)
    (hβ0 : β ≠ 0) (u : (↥k)ˣ) (v : ↥k)
    (hAuv : A = ((u : ↥k) : AlgebraicClosure ℚ_[2]) + (v : AlgebraicClosure ℚ_[2]) * δ)
    (s : k.fixingSubgroup) (hs : s ∉ (L.fixingSubgroup).subgroupOf (k.fixingSubgroup))
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((L.fixingSubgroup).subgroupOf (k.fixingSubgroup) :
        Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (hα : ∀ w z : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup),
      Kummer.kummerCocycleFun β ((w * z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
        = Kummer.kummerCocycleFun β ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
          + Kummer.kummerCocycleFun β ((z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
    (hαc : Continuous fun w : (L.fixingSubgroup).subgroupOf (k.fixingSubgroup) ↦
      Kummer.kummerCocycleFun β ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])) :
    H2ofFun k.fixingSubgroup
      (evensNormFun ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)) s
        (fun w ↦ Kummer.kummerCocycleFun β
          ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))) = 0 :=
  hvanish_evensNorm htriv hUo hindex hs _ hα hαc
    (lemma_6_16 k L hkL hindex hunram d δ hδ hδL hLδ A β hdeep hβ hβ0 u v hAuv s hs htriv hUo
      hα hαc)

/-- **Deep class → involution `hvanish`** (the Lemma 6.17 vanishing proof, the witness-plumbing step): given a deep
Kummer class `ξ ∈ deepClasses (L.fixingSubgroup)` at the involution block coordinate and the c2a
"abstract Kummer presentation package" `hc2a` (`IsDeepUnit L.fixingSubgroup A ⟹ ∃ d δ u v, …`),
the involution inner cochain vanishes for the class's own square root `β`.

Extracts the deep unit `(A, β)` from `ξ` (unpacking the `deepClasses` definition), derives the
mechanical side-conditions `hα` (additivity via `kummerCocycleFun_hom_on` on `L.fixingSubgroup`,
which fixes `A`) and `hαc` (continuity via `kummerCocycleFun_continuous`), and applies `hc2a` +
`hvanish_involution`.  This is steps (2)–(5) of the Lemma 6.17 vanishing proof in `L`-vocabulary; the remaining
`ker ρ = L.fixingSubgroup` transport (to feed `mem_deepPart_iff`) and the c2a-package proof
(the Lemma 6.17 vanishing proof) are the last pieces.  **Ax: B9, B11a, B11b (via `hvanish_involution`/`lemma_6_16`).** -/
theorem hvanish_involution_of_deepClass
    (k L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (hkL : k ≤ L)
    (hindex : ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)).index = 2)
    (hunram : ∀ x : AlgebraicClosure ℚ_[2], x ≠ 0 → x ∈ L →
      ∃ y : AlgebraicClosure ℚ_[2], y ≠ 0 ∧ y ∈ k ∧ ‖x‖ = ‖y‖)
    (hc2a : ∀ A : AlgebraicClosure ℚ_[2], IsDeepUnit L.fixingSubgroup A →
      ∃ (d : (↥k)ˣ) (δ : AlgebraicClosure ℚ_[2]) (u : (↥k)ˣ) (v : ↥k),
        δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]) ∧ δ ∈ L ∧
        (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
          = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup) ∧
        A = ((u : ↥k) : AlgebraicClosure ℚ_[2]) + (v : AlgebraicClosure ℚ_[2]) * δ)
    (s : k.fixingSubgroup) (hs : s ∉ (L.fixingSubgroup).subgroupOf (k.fixingSubgroup))
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
    (hUo : IsOpen (((L.fixingSubgroup).subgroupOf (k.fixingSubgroup) :
        Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
    (ξ : H1 L.fixingSubgroup (ZMod 2)) (hξ : ξ ∈ deepClasses L.fixingSubgroup) :
    ∃ β : AlgebraicClosure ℚ_[2],
      H2ofFun k.fixingSubgroup
        (evensNormFun ((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)) s
          (fun w ↦ Kummer.kummerCocycleFun β
            ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))) = 0 := by
  obtain ⟨A, β, hdeep, hβ, hβ0, hclass⟩ := hξ
  obtain ⟨d, δ, u, v, hδ, hδL, hLδ, hAuv⟩ := hc2a A hdeep
  have hAfix : ∀ g ∈ L.fixingSubgroup, g • A = A := hdeep.2.1
  have hα : ∀ w z : ↥((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)),
      Kummer.kummerCocycleFun β ((w * z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
        = Kummer.kummerCocycleFun β ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
          + Kummer.kummerCocycleFun β ((z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) := by
    intro w z
    have hwL : ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) ∈ L.fixingSubgroup :=
      Subgroup.mem_subgroupOf.mp w.2
    have hzL : ((z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) ∈ L.fixingSubgroup :=
      Subgroup.mem_subgroupOf.mp z.2
    have hmul : ((w * z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
        = ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2])
          * ((z : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) := by
      push_cast; rfl
    rw [hmul]
    exact kummerCocycleFun_hom_on hβ hβ0 hAfix ⟨_, hwL⟩ ⟨_, hzL⟩
  have hαc : Continuous fun w : ↥((L.fixingSubgroup).subgroupOf (k.fixingSubgroup)) ↦
      Kummer.kummerCocycleFun β ((w : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]) :=
    (Kummer.kummerCocycleFun_continuous β).comp (continuous_subtype_val.comp continuous_subtype_val)
  exact ⟨β, hvanish_involution k L hkL hindex hunram d δ hδ hδL hLδ A β hdeep hβ hβ0 u v hAuv
    s hs htriv hUo hα hαc⟩

end InvolutionAssembly

end ShapiroDeepness

end GQ2
