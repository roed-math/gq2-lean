import GQ2.OrbitDecomp
import GQ2.RepIndependence
import GQ2.LocalKummer

/-!
# P-15f2c1: the Shapiro H¹ coordinate read  (`hcoh`, the f2c keystone)

The remaining cohomological input of the `lemma_6_17_vanish` orbit route (P-15f2, handoff
`docs/p15f2-handoff.md` §5): each block coordinate of a `Z¹(G_ℚ₂, 𝔽₂[G/N]^K)`-representative is
**cohomologous to the Shapiro cochain of its scalar coordinate**, so the banked
`SectionSix.lemma_6_15_{square,free,involution}` (stated at `shapiroFun`, acting map `mk' N`)
fire on the per-orbit graph pullbacks of `OrbitDecomp`'s block datums.

**The read** (Shapiro's lemma for `H¹(G, 𝔽₂[G/N])`, explicit-witness form).  For a 1-cocycle
`β : G → 𝔽₂[G/N]` w.r.t. the `mk'`-pulled-back left-regular action:

* the **scalar coordinate** `α := shapiroCoord β : n ↦ β(n)(1̄)` is a 1-cocycle on `N`
  (trivial coefficients) — evaluation at the base coset;
* the **primitive** `w := shapiroPrim β : u ↦ β(ũ)(u)` (`~` = `Quotient.out`, the same canonical
  transversal as `GQ2/Corestriction.lean`) satisfies the pointwise identity
  `Sh(α)(g) = β(g) + (mk'(g)•w − w)`  (`shapiroFun_shapiroCoord_eq`).

Proof: evaluate the cocycle rule on both factorizations of `g·(g⁻¹•u)~ = ũ·ℓ_u(g)` at the coset
`u`; the `ℓ`-term is the Shapiro cochain, the two transversal terms are the primitive.  No
choices beyond the canonical transversal, no sign bookkeeping (`𝔽₂`).

**Per-orbit `hcoh`** (§PerOrbit, at `G := G_ℚ₂`): the coboundary shift is transported through the
graph pullback by the banked `RepIndependence.graphPullback_sub_mem_B2`, the block datum is
converted to the literal orbit datum by `graphPullback_comap` (both are definitional
`FactorSet.comap`s along `blockProj`/`blockProj₂`), and Lemma 6.15 closes:

* `hcoh_square`     — eq. (103) at the block-`j` coordinate;
* `hcoh_free`       — eq. (104) at the block pair `(j, k)` with shift `mk' ĝ`;
* `hcoh_involution` — eq. (105) at block `j` with involution lift `ĝ`.

**The deep coordinate** (§DeepCoordinate): the scalar coordinate at block `j` **is** the scalar
restriction `phiRes ρ x (evalW j)` on the nose (`phiRes_evalW`, a `rfl`), so `x ∈ deepPart ρ`
hands each block coordinate a deep Kummer class (`shapiroCoord_mem_deepClasses`) — the f2d feed
for `hvanish` (`ShapiroDeepness.hvanish_cup` / `lemma_6_16`).

Paper: §6.2–§6.3, proof of Lemma 6.15 / eq. (102)–(105).  Axioms: **∅** (std-3).
-/

namespace GQ2

open ContCoh Corestriction

namespace ShapiroRead

/-! ## Preliminaries -/

section Prelim

/-- Quotients by open normal subgroups are discrete (the `AnabelianBridge` argument, made
available at this layer for `G_ℚ₂ ⧸ N`). -/
theorem discreteTopology_quotient_of_isOpen {G : Type*} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] (hNo : IsOpen (N : Set G)) :
    DiscreteTopology (G ⧸ N) := by
  refine discreteTopology_of_isOpen_singleton_one ?_
  have hpre : (QuotientGroup.mk : G → G ⧸ N) ⁻¹' {1} = (N : Set G) := by
    ext δ
    simp only [Set.mem_preimage, Set.mem_singleton_iff, SetLike.mem_coe,
      QuotientGroup.eq_one_iff]
  rw [← (QuotientGroup.isQuotientMap_mk N).isOpen_preimage, hpre]
  exact hNo

/-- `graphPullback` functoriality along an equivariant `comap`: pulling the comapped datum back
along `(ρ', b)` is pulling the datum back along `(ρ', i ∘ b)`.  Turns the block datums of
`OrbitDecomp` (definitional `comap`s) into the literal orbit datums of Lemma 6.15. -/
theorem graphPullback_comap {C V W : Type*} [Group C] [AddCommGroup V] [AddCommGroup W]
    [DistribMulAction C V] [DistribMulAction C W] {Γ : Type*}
    (dat : FactorSet C W) (i : V →+ W) (hi : ∀ (c : C) (v : V), i (c • v) = c • i v)
    (ρ' : Γ → C) (b : Γ → V) :
    graphPullback (dat.comap i) ρ' b = graphPullback dat ρ' (fun γ => i (b γ)) := by
  funext p
  show dat.f (i (b p.1)) (i (ρ' p.1 • b p.2)) + dat.m (ρ' p.1) (i (b p.2))
      = dat.f (i (b p.1)) (ρ' p.1 • i (b p.2)) + dat.m (ρ' p.1) (i (b p.2))
  rw [hi]

end Prelim

/-! ## The scalar read and its primitive -/

section Read

variable {G : Type*} [Group G] {N : Subgroup G} [N.Normal]

/-- The coset action bridge: the group-multiplication translate in `G ⧸ N` is the `G`-action
translate (the `hact` of `lemma_6_15_square`, extracted). -/
theorem mk'_inv_mul (g : G) (u : G ⧸ N) : (QuotientGroup.mk' N g)⁻¹ * u = g⁻¹ • u := by
  refine QuotientGroup.induction_on u fun u₀ => ?_
  rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  rfl

variable (N) in
/-- The **scalar Shapiro coordinate** of a `𝔽₂[G/N]`-valued 1-cochain: evaluate at the base
coset and restrict to `N` (the forward half of Shapiro's `H¹(G, 𝔽₂[G/N]) ≅ H¹(N, 𝔽₂)`). -/
def shapiroCoord (β : G → RegRep N) : ↥N → ZMod 2 := fun n => β (n : G) (1 : G ⧸ N)

variable (N) in
/-- The **Shapiro primitive**: the explicit 0-cochain trivializing `β − Sh(shapiroCoord β)`:
`w(u) = β(ũ)(u)` with `~` the canonical transversal (`Quotient.out`). -/
noncomputable def shapiroPrim (β : G → RegRep N) : RegRep N := fun u => β u.out u

variable {β : G → RegRep N}
  (hβ : ∀ g h : G, β (g * h) = β g + QuotientGroup.mk' N g • β h)

include hβ

/-- The scalar coordinate is multiplicative on `N` (the base coset is `N`-fixed). -/
theorem shapiroCoord_mul (n m : ↥N) :
    shapiroCoord N β (n * m) = shapiroCoord N β n + shapiroCoord N β m := by
  have h1 : QuotientGroup.mk' N (n : G) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff (n : G)).mpr n.2
  show β ((n : G) * (m : G)) 1 = β (n : G) 1 + β (m : G) 1
  rw [hβ (n : G) (m : G), h1, one_smul]
  rfl

/-- **The Shapiro read** (pointwise): the Shapiro cochain of the scalar coordinate differs from
the cocycle by the explicit `shapiroPrim` coboundary.  Evaluate the cocycle rule on the two
factorizations of `g · (g⁻¹•u)~ = ũ · ℓ_u(g)` at the coset `u`. -/
theorem shapiroFun_shapiroCoord_apply (g : G) (u : G ⧸ N) :
    shapiroFun N (shapiroCoord N β) g u
      = β g u + (shapiroPrim N β (g⁻¹ • u) + shapiroPrim N β u) := by
  -- the transversal-word factorization
  have hkey : g * (g⁻¹ • u : G ⧸ N).out = u.out * lWord N u g := by
    unfold lWord
    group
  -- the cocycle rule on both sides
  have hcross : β g + QuotientGroup.mk' N g • β (g⁻¹ • u : G ⧸ N).out
      = β u.out + QuotientGroup.mk' N u.out • β (lWord N u g) := by
    rw [← hβ g (g⁻¹ • u : G ⧸ N).out, hkey, hβ u.out (lWord N u g)]
  have h := congrFun hcross u
  -- evaluate the two smul terms
  have hout : QuotientGroup.mk' N u.out = u := by
    rw [QuotientGroup.mk'_apply, QuotientGroup.out_eq']
  have e1 : (β g + QuotientGroup.mk' N g • β (g⁻¹ • u : G ⧸ N).out) u
      = β g u + β (g⁻¹ • u : G ⧸ N).out (g⁻¹ • u) := by
    show β g u + β (g⁻¹ • u : G ⧸ N).out ((QuotientGroup.mk' N g)⁻¹ * u) = _
    rw [mk'_inv_mul]
  have e2 : (β u.out + QuotientGroup.mk' N u.out • β (lWord N u g)) u
      = β u.out u + β (lWord N u g) 1 := by
    show β u.out u + β (lWord N u g) ((QuotientGroup.mk' N u.out)⁻¹ * u) = _
    rw [hout, inv_mul_cancel]
  rw [e1, e2] at h
  -- h : β g u + β (g⁻¹•u)~ (g⁻¹•u) = β ũ u + β (ℓ_u g) 1̄;  identify and shuffle (char 2)
  show β (lWord N u g) 1 = β g u + (β (g⁻¹ • u : G ⧸ N).out (g⁻¹ • u) + β u.out u)
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h

/-- The Shapiro read, **coboundary form**: `Sh(shapiroCoord β)(g) = β(g) + (mk'(g)•w − w)` with
`w = shapiroPrim β` — the exact shift shape of `RepIndependence.graphPullback_sub_mem_B2`. -/
theorem shapiroFun_shapiroCoord_eq (g : G) :
    shapiroFun N (shapiroCoord N β) g
      = β g + (QuotientGroup.mk' N g • shapiroPrim N β - shapiroPrim N β) := by
  funext u
  show shapiroFun N (shapiroCoord N β) g u
      = β g u + (shapiroPrim N β ((QuotientGroup.mk' N g)⁻¹ * u) - shapiroPrim N β u)
  rw [mk'_inv_mul, CharTwo.sub_eq_add]
  exact shapiroFun_shapiroCoord_apply hβ g u

end Read

/-! ## The `Z¹`-package of the scalar coordinate -/

section Z1Layer

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable {N : Subgroup G} [N.Normal]

omit [IsTopologicalGroup G] [ContinuousSMul G (ZMod 2)] in
/-- The scalar coordinate of a continuous `mk'`-cocycle is a continuous 1-cocycle on `N`
(trivial coefficients). -/
theorem shapiroCoord_mem_Z1 {β : G → RegRep N}
    (hβ : ∀ g h : G, β (g * h) = β g + QuotientGroup.mk' N g • β h)
    (hβc : Continuous fun g => β g (1 : G ⧸ N))
    (htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m) :
    shapiroCoord N β ∈ Z1 ↥N (ZMod 2) := by
  rw [mem_Z1_iff_of_trivial htriv]
  exact ⟨hβc.comp continuous_subtype_val, fun n m => shapiroCoord_mul hβ n m⟩

end Z1Layer

/-! ## Per-orbit `hcoh` at `G_ℚ₂`

The block-level shift: `b` is replaced by `b + δ⁰W₀` for the block-supported primitive `W₀`
(a `B²`-move on the graph pullback, `graphPullback_sub_mem_B2`), whose block coordinate is the
Shapiro cochain (`shapiroFun_shapiroCoord_eq`); then `graphPullback_comap` exposes the literal
orbit datum and Lemma 6.15 evaluates it as a corestriction.

Instance context: `RegRep N` is a type synonym with no registered topology, so the topological
instances (and the `G_ℚ₂`-action, the `mk'`-pullback of the left-regular action) enter as
instance arguments with the compatibility hypothesis `hmk` — the f2d assembly supplies them as
`letI`s (`DistribMulAction.compHom` along `mk' N`), for which `hmk` is `rfl`. -/

section PerOrbit

open SectionSix

variable (N : Subgroup AbsGalQ2) [N.Normal] [Finite (AbsGalQ2 ⧸ N)]
variable [TopologicalSpace (RegRep N)] [DiscreteTopology (RegRep N)] [Finite (RegRep N)]
  [DistribMulAction AbsGalQ2 (RegRep N)] [ContinuousSMul AbsGalQ2 (RegRep N)]
variable (hmk : ∀ (g : AbsGalQ2) (y : RegRep N), g • y = QuotientGroup.mk' N g • y)

/-- `mk' N` as a continuous monoid hom (quotient topology). -/
private noncomputable def mkQ : ContinuousMonoidHom AbsGalQ2 (AbsGalQ2 ⧸ N) :=
  ⟨QuotientGroup.mk' N, continuous_quotient_mk'⟩

omit [Finite (AbsGalQ2 ⧸ N)] [Finite (RegRep N)] [ContinuousSMul AbsGalQ2 (RegRep N)] in
include hmk in
/-- The block coordinate of a `Z¹`-representative is an `mk'`-cocycle (raw form). -/
theorem block_cocycle {K : ℕ} (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) (j : Fin K) :
    ∀ g h : AbsGalQ2, b.1 (g * h) j = b.1 g j + QuotientGroup.mk' N g • b.1 h j := by
  intro g h
  rw [(mem_Z1_iff.mp b.2).2 g h]
  show b.1 g j + (g • b.1 h) j = b.1 g j + QuotientGroup.mk' N g • b.1 h j
  rw [Pi.smul_apply, hmk]

omit [Finite (AbsGalQ2 ⧸ N)] [Finite (RegRep N)] [ContinuousSMul AbsGalQ2 (RegRep N)] in
/-- The base-coset evaluation of a block coordinate is continuous (`W` is discrete). -/
theorem block_continuous {K : ℕ} (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) (j : Fin K) :
    Continuous fun g => b.1 g j (1 : AbsGalQ2 ⧸ N) :=
  (continuous_of_discreteTopology
    (f := fun F : Fin K → RegRep N => F j (1 : AbsGalQ2 ⧸ N))).comp (mem_Z1_iff.mp b.2).1

include hmk in
/-- The shared `B²`-shift engine: replacing the `Z¹`-representative by its `δ⁰W₀`-shift does not
change the `H²ofFun` class of any equivariant graph pullback (banked
`graphPullback_sub_mem_B2`). -/
private theorem H2ofFun_graphPullback_shift {K : ℕ} {qW : (Fin K → RegRep N) → ZMod 2}
    (dat : FactorSet (AbsGalQ2 ⧸ N) (Fin K → RegRep N))
    (hdat : IsEquivariantFactorSet qW dat) (hNo : IsOpen (N : Set AbsGalQ2))
    (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) (W₀ : Fin K → RegRep N) :
    H2ofFun AbsGalQ2 (graphPullback dat (⇑(QuotientGroup.mk' N))
        (fun g => b.1 g + (g • W₀ - W₀)))
      = H2ofFun AbsGalQ2 (graphPullback dat (⇑(QuotientGroup.mk' N)) b.1) := by
  haveI : DiscreteTopology (AbsGalQ2 ⧸ N) := discreteTopology_quotient_of_isOpen N hNo
  have hρW : ∀ (g : AbsGalQ2) (F : Fin K → RegRep N), g • F = (mkQ N) g • F := by
    intro g F
    funext k
    exact hmk g (F k)
  have hB2 := RepIndependence.graphPullback_sub_mem_B2 dat hdat (mkQ N) hρW b W₀
  exact ShapiroLedger.H2ofFun_eq_of_sub_mem_B2 hB2

include hmk in
/-- **P-15f2c1, square-orbit `hcoh`** (Lemma 6.15 eq. (103) at a block coordinate): the graph
pullback of the square block datum at any `Z¹`-representative is, in `H²`, the corestriction of
the cup square of the block's scalar Shapiro coordinate. -/
theorem hcoh_square {K : ℕ} (j : Fin K) (hNo : IsOpen (N : Set AbsGalQ2))
    (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) :
    H2ofFun AbsGalQ2 (graphPullback (squareBlockDatum N j) (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 * shapiroCoord N (fun g => b.1 g j) p.2)) := by
  classical
  have hβ := block_cocycle N hmk b j
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun _ _ => rfl
  set W₀ : Fin K → RegRep N :=
    Pi.single j (shapiroPrim N (fun g => b.1 g j)) with hW₀def
  have hblock : (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))
      = shapiroFun N (shapiroCoord N (fun g => b.1 g j)) := by
    funext g
    show b.1 g j + ((g • W₀) j - W₀ j) = _
    rw [hW₀def, Pi.smul_apply, Pi.single_eq_same, hmk,
      shapiroFun_shapiroCoord_eq hβ g]
  calc H2ofFun AbsGalQ2 (graphPullback (squareBlockDatum N j) (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (graphPullback (squareBlockDatum N j) (⇑(QuotientGroup.mk' N))
          (fun g => b.1 g + (g • W₀ - W₀))) :=
        (H2ofFun_graphPullback_shift N hmk (squareBlockDatum N j)
          (isEquivariantFactorSet_squareBlockDatum N j) hNo b W₀).symm
    _ = H2ofFun AbsGalQ2 (graphPullback (squareOrbitDatum N) (⇑(QuotientGroup.mk' N))
          (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))) :=
        congrArg (H2ofFun AbsGalQ2)
          (graphPullback_comap (squareOrbitDatum N) (blockProj N j)
            (fun c v => blockProj_smul N j c v) (⇑(QuotientGroup.mk' N))
            (fun g => b.1 g + (g • W₀ - W₀)))
    _ = H2ofFun AbsGalQ2 (graphPullback (squareOrbitDatum N) (⇑(QuotientGroup.mk' N))
          (shapiroFun N (shapiroCoord N (fun g => b.1 g j)))) := by rw [hblock]
    _ = H2ofFun AbsGalQ2 (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 * shapiroCoord N (fun g => b.1 g j) p.2)) :=
        lemma_6_15_square N hNo
          ⟨shapiroCoord N (fun g => b.1 g j),
            shapiroCoord_mem_Z1 hβ (block_continuous N b j) htriv⟩

include hmk in
/-- **P-15f2c1, free-orbit `hcoh`** (Lemma 6.15 eq. (104) at a block pair): the graph pullback
of the free block datum with shift `mk' ĝ` at any `Z¹`-representative is, in `H²`, the
corestriction of `α_j ⌣ ĝα_k` (conjugated second coordinate). -/
theorem hcoh_free {K : ℕ} (j k : Fin K) (ghat : AbsGalQ2) (hNo : IsOpen (N : Set AbsGalQ2))
    (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) :
    H2ofFun AbsGalQ2 (graphPullback (freeBlockDatum N j k (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 *
            shapiroCoord N (fun g => b.1 g k) ⟨ghat⁻¹ * (p.2 : AbsGalQ2) * ghat, by
              simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ p.2.2 ghat⁻¹⟩)) := by
  classical
  have hβj := block_cocycle N hmk b j
  have hβk := block_cocycle N hmk b k
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun _ _ => rfl
  set W₀ : Fin K → RegRep N :=
    Function.update (Pi.single j (shapiroPrim N (fun g => b.1 g j))) k
      (shapiroPrim N (fun g => b.1 g k)) with hW₀def
  have hW₀k : W₀ k = shapiroPrim N (fun g => b.1 g k) := by
    rw [hW₀def, Function.update_self]
  have hW₀j : W₀ j = shapiroPrim N (fun g => b.1 g j) := by
    by_cases hjk : j = k
    · subst hjk
      rw [hW₀def, Function.update_self]
    · rw [hW₀def, Function.update_of_ne hjk, Pi.single_eq_same]
  have hblock : (fun g => blockProj₂ N j k (b.1 g + (g • W₀ - W₀)))
      = fun g => (shapiroFun N (shapiroCoord N (fun g' => b.1 g' j)) g,
          shapiroFun N (shapiroCoord N (fun g' => b.1 g' k)) g) := by
    funext g
    refine Prod.ext ?_ ?_
    · show b.1 g j + ((g • W₀) j - W₀ j)
          = shapiroFun N (shapiroCoord N (fun g' => b.1 g' j)) g
      rw [Pi.smul_apply, hW₀j, hmk]
      exact (shapiroFun_shapiroCoord_eq (β := fun g' => b.1 g' j) hβj g).symm
    · show b.1 g k + ((g • W₀) k - W₀ k)
          = shapiroFun N (shapiroCoord N (fun g' => b.1 g' k)) g
      rw [Pi.smul_apply, hW₀k, hmk]
      exact (shapiroFun_shapiroCoord_eq (β := fun g' => b.1 g' k) hβk g).symm
  calc H2ofFun AbsGalQ2 (graphPullback (freeBlockDatum N j k (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (graphPullback (freeBlockDatum N j k (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N)) (fun g => b.1 g + (g • W₀ - W₀))) :=
        (H2ofFun_graphPullback_shift N hmk (freeBlockDatum N j k (QuotientGroup.mk' N ghat))
          (isEquivariantFactorSet_freeBlockDatum N j k (QuotientGroup.mk' N ghat)) hNo b
          W₀).symm
    _ = H2ofFun AbsGalQ2 (graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N))
          (fun g => blockProj₂ N j k (b.1 g + (g • W₀ - W₀)))) :=
        congrArg (H2ofFun AbsGalQ2)
          (graphPullback_comap (freeOrbitDatum N (QuotientGroup.mk' N ghat))
            (blockProj₂ N j k) (fun c v => blockProj₂_smul N j k c v)
            (⇑(QuotientGroup.mk' N)) (fun g => b.1 g + (g • W₀ - W₀)))
    _ = H2ofFun AbsGalQ2 (graphPullback (freeOrbitDatum N (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N))
          (fun g => (shapiroFun N (shapiroCoord N (fun g' => b.1 g' j)) g,
            shapiroFun N (shapiroCoord N (fun g' => b.1 g' k)) g))) :=
        congrArg (fun c => H2ofFun AbsGalQ2 (graphPullback
          (freeOrbitDatum N (QuotientGroup.mk' N ghat)) (⇑(QuotientGroup.mk' N)) c)) hblock
    _ = H2ofFun AbsGalQ2 (cor2Fun N (fun p =>
          shapiroCoord N (fun g => b.1 g j) p.1 *
            shapiroCoord N (fun g => b.1 g k) ⟨ghat⁻¹ * (p.2 : AbsGalQ2) * ghat, by
              simpa using Subgroup.Normal.conj_mem ‹N.Normal› _ p.2.2 ghat⁻¹⟩)) :=
        lemma_6_15_free N hNo
          ⟨shapiroCoord N (fun g => b.1 g j),
            shapiroCoord_mem_Z1 hβj (block_continuous N b j) htriv⟩
          ⟨shapiroCoord N (fun g => b.1 g k),
            shapiroCoord_mem_Z1 hβk (block_continuous N b k) htriv⟩ ghat

include hmk in
/-- **P-15f2c1, involution-orbit `hcoh`** (Lemma 6.15 eq. (105) at a block coordinate): the
graph pullback of the involution block datum at any `Z¹`-representative is, in `H²`, the
`U₀`-corestriction of the Evens norm of the block's scalar Shapiro coordinate. -/
theorem hcoh_involution {K : ℕ} (j : Fin K) (ghat : AbsGalQ2) (hNo : IsOpen (N : Set AbsGalQ2))
    (hg : ghat ∉ N) (hg2 : ghat * ghat ∈ N)
    (U₀ : Subgroup AbsGalQ2) (hU₀ : U₀ = N ⊔ Subgroup.zpowers ghat)
    (hs : (⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩ : U₀)
        ∉ N.subgroupOf U₀)
    (b : ↥(Z1 AbsGalQ2 (Fin K → RegRep N))) :
    H2ofFun AbsGalQ2 (graphPullback (invBlockDatum N j (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (cor2Fun U₀ (fun p =>
          evensNormFun (N.subgroupOf U₀)
            ⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩
            (fun u => shapiroCoord N (fun g => b.1 g j) ⟨u.1.1, u.2⟩) (p.1, p.2))) := by
  classical
  have hβ := block_cocycle N hmk b j
  have htriv : ∀ (n : ↥N) (m : ZMod 2), n • m = m := fun _ _ => rfl
  have hu2 : QuotientGroup.mk' N ghat * QuotientGroup.mk' N ghat = 1 := by
    rw [← map_mul]
    exact (QuotientGroup.eq_one_iff _).mpr hg2
  set W₀ : Fin K → RegRep N :=
    Pi.single j (shapiroPrim N (fun g => b.1 g j)) with hW₀def
  have hblock : (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))
      = shapiroFun N (shapiroCoord N (fun g => b.1 g j)) := by
    funext g
    show b.1 g j + ((g • W₀) j - W₀ j) = _
    rw [hW₀def, Pi.smul_apply, Pi.single_eq_same, hmk,
      shapiroFun_shapiroCoord_eq hβ g]
  calc H2ofFun AbsGalQ2 (graphPullback (invBlockDatum N j (QuotientGroup.mk' N ghat))
        (⇑(QuotientGroup.mk' N)) b.1)
      = H2ofFun AbsGalQ2 (graphPullback (invBlockDatum N j (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N)) (fun g => b.1 g + (g • W₀ - W₀))) :=
        (H2ofFun_graphPullback_shift N hmk (invBlockDatum N j (QuotientGroup.mk' N ghat))
          (isEquivariantFactorSet_invBlockDatum N j hu2) hNo b W₀).symm
    _ = H2ofFun AbsGalQ2 (graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N))
          (fun g => blockProj N j (b.1 g + (g • W₀ - W₀)))) :=
        congrArg (H2ofFun AbsGalQ2)
          (graphPullback_comap (invOrbitDatum N (QuotientGroup.mk' N ghat)) (blockProj N j)
            (fun c v => blockProj_smul N j c v) (⇑(QuotientGroup.mk' N))
            (fun g => b.1 g + (g • W₀ - W₀)))
    _ = H2ofFun AbsGalQ2 (graphPullback (invOrbitDatum N (QuotientGroup.mk' N ghat))
          (⇑(QuotientGroup.mk' N))
          (shapiroFun N (shapiroCoord N (fun g => b.1 g j)))) := by rw [hblock]
    _ = H2ofFun AbsGalQ2 (cor2Fun U₀ (fun p =>
          evensNormFun (N.subgroupOf U₀)
            ⟨ghat, by rw [hU₀]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ghat)⟩
            (fun u => shapiroCoord N (fun g => b.1 g j) ⟨u.1.1, u.2⟩) (p.1, p.2))) :=
        lemma_6_15_involution N hNo
          ⟨shapiroCoord N (fun g => b.1 g j),
            shapiroCoord_mem_Z1 hβ (block_continuous N b j) htriv⟩ ghat hg hg2 U₀ hU₀ hs

end PerOrbit

/-! ## The deep coordinate: `shapiroCoord = phiRes` at the block functional -/

section DeepCoordinate

open SectionSix LocalKummer

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]

/-- The block-coordinate evaluation functional `F ↦ F j (1̄)`. -/
noncomputable def evalW (N : Subgroup AbsGalQ2) [N.Normal] {K : ℕ} (j : Fin K) :
    (Fin K → RegRep N) →+ ZMod 2 where
  toFun F := F j (1 : AbsGalQ2 ⧸ N)
  map_zero' := rfl
  map_add' _ _ := rfl

variable (ρ : ContinuousMonoidHom AbsGalQ2 C)

section

variable {K : ℕ}
  [TopologicalSpace (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [DiscreteTopology (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [DistribMulAction AbsGalQ2 (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [ContinuousSMul AbsGalQ2 (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]

omit [DiscreteTopology C] [Finite C]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [ContinuousSMul AbsGalQ2 (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))] in
/-- **The deep-coordinate identification**: the scalar restriction of a class at the block
functional `evalW j` **is** the `H1ofFun` of the Shapiro coordinate of its canonical
representative's block — on the nose. -/
theorem phiRes_evalW (j : Fin K)
    (x : H1 AbsGalQ2 (Fin K → RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))) :
    phiRes ρ x (evalW _ j)
      = H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
          (shapiroCoord _ (fun g => (Quotient.out x).1 g j)) := rfl

omit [DiscreteTopology C] [Finite C]
  [Finite (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [ContinuousSMul AbsGalQ2 (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))]
  [DistribMulAction C (RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))] in
/-- **The block coordinates of a deep class are deep** (the f2d `hvanish` feed): for
`x ∈ deepPart ρ` on the block module, every block's scalar Shapiro coordinate has a deep
Kummer class. -/
theorem shapiroCoord_mem_deepClasses (j : Fin K)
    {x : H1 AbsGalQ2 (Fin K → RegRep (ρ.toMonoidHom.ker : Subgroup AbsGalQ2))}
    (hx : x ∈ deepPart ρ) :
    H1ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
        (shapiroCoord _ (fun g => (Quotient.out x).1 g j))
      ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) := by
  have h := (mem_deepPart_iff ρ x).mp hx (evalW _ j)
  rwa [phiRes_evalW] at h

end

end DeepCoordinate

end ShapiroRead

end GQ2
