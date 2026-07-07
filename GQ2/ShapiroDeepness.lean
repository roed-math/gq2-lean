import GQ2.LocalKummer
import GQ2.OrbitVanish
import GQ2.ShapiroExtend

/-!
# P-15f2c: Shapiro coordinates + scalar deepness (the `hvanish` producers)

The two per-orbit hypotheses of `OrbitVanish.Q0loc_vanish_of_datum_decomp` for the deep half
`x ∈ deepPart ρ`:

* **`hcoh`** — each per-orbit graph pullback is cohomologous to its `cor2Fun` corestriction.
  This is a direct application of the banked `SectionSix.lemma_6_15_{square,free,involution}`;
  P-15f2b (`OrbitDecomp.lean`) structures each `datf o` as a definitional `comap` of the
  literal orbit datum so the pullbacks are *syntactically* the Lemma-6.15 inputs — the
  instantiation is done at f2d.

* **`hvanish`** — each corestriction's **inner** cocycle vanishes in its subgroup's `H²`.
  For square/free orbits the inner cocycle is a cup `α ⌣ α'` of scalar Shapiro coordinates,
  which vanish because those coordinates are **deep** (`x ∈ deepPart` ⟹ every scalar
  restriction is a deep Kummer class, `LocalKummer.mem_deepPart_iff`), via the eq.-(94)
  orthogonality `LocalKummer.cup_deepClasses`.  This file proves that reduction —
  **`hvanish_cup`** — the self-contained core of the square and free cases.  (The involution
  case, `hvanish` via `lemma_6_16`'s Evens-norm vanishing, is the remaining piece;
  design record `docs/p15f2c-design.md`.)

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
  rw [H2ofFun_of_mem hZ2]; exact h0

/-- **The deep-class cup vanishing** (P-15f2c, the square/free `hvanish` core): if two scalar
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
  refine H2ofFun_eq_zero_of_H2mk hZ2 ?_
  exact cup_deepClasses k htriv ha hb

/-- **The involution `hvanish` cochain bridge** (P-15f2c): the Evens-norm class `evensNormH2`
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

/-- **Deepness transports along an equivariant coefficient map** (P-15f2d): if `x ∈ deepPart ρ`
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

/-- **`graphPullback` reindexing** (P-15f2d, the linchpin of the C ↔ `AbsGalQ2 ⧸ ker ρ` bridge):
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
/-- **`Q0loc` reindexing** (P-15f2d): lifts `graphPullback_reindexHom` from the raw cochain to the
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

end ShapiroDeepness

end GQ2
