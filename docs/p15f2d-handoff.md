# P-15f2d handoff — final assembly of `lemma_6_17_vanish` (`Q⁰loc|X₊ = 0`)

*Self-contained continuation guide (Opus, 2026-07-07). The front-half is VERIFIED (compiles);
this doc carries it verbatim so the next session drops it in and only builds the reducer.*

## 0. State

- **f2a** (`OrbitVanish.Q0loc_datum_indep`), **f2b** (`regular_isometric_embedding_orbit`),
  **f2c1** (`ShapiroRead.hcoh_{square,free,involution}` + `shapiroCoord_mem_deepClasses`),
  **f2c2/c2c** (`ShapiroDeepness.hvanish_involution_of_deepClass`, `hunram` discharged) — ALL LANDED.
- **f2d wiring bricks** (`GQ2/VanishClose.lean`, sorry-free): `reindexHom_sumDatum`,
  `isEquivariantFactorSet_reindexHom`, `eOfSurj`, `eOfSurj_rho`.
- **f2d front-half — VERIFIED THIS SESSION** (compiles with one trailing `sorry` at the reducer):
  the whole `lemma_6_17_vanish` → `Q0loc D datWC ρ (ι∗x) = 0` reduction, code in §2 below.
- **Remaining**: the reducer application (per-orbit `hcoh` + `hvanish`) — §3 — and the SectionSix
  statement-move — §4.

## 1. ⚡ Key finding: `RegRep N` opacity — NO synonym needed for `W`

The P-15f handoff §2 warned the global trivial `AbsGalQ2`-action on `ZMod 2` lifts pointwise over
`RegMod C Nr` and beats `letI`.  **This does NOT apply to `W = Fin K → RegRep (ker ρ)`**: `RegRep`
is an opaque `def` (`OrbitData.lean:97`), so `DistribMulAction AbsGalQ2 (RegRep N)` and
`… (Fin K → RegRep N)` **fail to synthesize by default** (verified: `#synth` errors).  Hence the
intended `mk'`-pullback action `letI`s cleanly — **no `RegMod`-style wrapper is needed**.  The
`W`-instance block in §2 is the reference pattern.

## 2. The verified front-half (drop-in; compiles)

`GQ2/VanishClose.lean`, `open ContCoh QuadraticFp2 SectionSix DimAssembly ShapiroRead LocalKummer`,
`variable {C} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]`,
`variable {V} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]`
`  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]`.

```lean
theorem lemma_6_17_vanish_of_deepData (D : TateDuality 2) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (hcup : ∀ a b : Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2),
      H1ofFun _ a.1 ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) →
      H1ofFun _ b.1 ∈ deepClasses (ρ.toMonoidHom.ker : Subgroup AbsGalQ2) →
      H2ofFun ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)
        (cup11Fun AddMonoidHom.mul a.1 b.1) = 0)
    (x : H1 AbsGalQ2 V) (hx : x ∈ deepPart (V := V) ρ) :
    Q0loc D dat ρ x = 0 := by
  classical
  have hρsurj : Function.Surjective ⇑ρ := rho_surjective B c hc ρ hfac
  have hgen : Subgroup.closure {c tameSigma, c tameTau} = ⊤ := gen_of_surjective c hc
  set N : Subgroup AbsGalQ2 := ρ.toMonoidHom.ker with hN
  have hNopen : IsOpen (N : Set AbsGalQ2) := by
    have hset : (N : Set AbsGalQ2) = ρ ⁻¹' {1} := by
      ext g; simp only [hN, SetLike.mem_coe, MonoidHom.mem_ker, Set.mem_preimage,
        Set.mem_singleton_iff]; rfl
    rw [hset]; exact (isOpen_discrete {1}).preimage ρ.continuous_toFun
  haveI : Finite (AbsGalQ2 ⧸ N) :=
    Finite.of_injective _ (QuotientGroup.quotientKerEquivRange ρ.toMonoidHom).injective
  haveI : Fintype (AbsGalQ2 ⧸ N) := Fintype.ofFinite _
  set e : C ≃* AbsGalQ2 ⧸ N := eOfSurj ρ hρsurj with he_def
  obtain ⟨K, ι, r, hEqfs, hIso, hιe, hri⟩ :=
    regular_isometric_embedding_orbit (G := AbsGalQ2) N e c hgen q hq hinv hV2
      hfaith hsimple hram
  -- W-instances: RegRep's opacity blocks the global trivial action (see §1), so these are clean
  haveI : Finite (RegRep N) := inferInstanceAs (Finite ((AbsGalQ2 ⧸ N) → ZMod 2))
  haveI : Finite (Fin K → RegRep N) := inferInstance
  letI : TopologicalSpace (Fin K → RegRep N) := ⊥
  haveI : DiscreteTopology (Fin K → RegRep N) := ⟨rfl⟩
  haveI : IsTopologicalAddGroup (Fin K → RegRep N) :=
    { continuous_add := continuous_of_discreteTopology
      continuous_neg := continuous_of_discreteTopology }
  haveI hdq : DiscreteTopology (AbsGalQ2 ⧸ N) := discreteTopology_quotient_of_isOpen N hNopen
  letI actAbs : DistribMulAction AbsGalQ2 (Fin K → RegRep N) :=
    DistribMulAction.compHom _ (QuotientGroup.mk' N)
  letI actC : DistribMulAction C (Fin K → RegRep N) :=
    DistribMulAction.compHom _ e.toMonoidHom
  haveI : ContinuousSMul AbsGalQ2 (Fin K → RegRep N) := by
    refine ⟨?_⟩
    have h1 : Continuous fun p : AbsGalQ2 × (Fin K → RegRep N) =>
        ((QuotientGroup.mk' N p.1, p.2) : (AbsGalQ2 ⧸ N) × (Fin K → RegRep N)) :=
      (continuous_quotient_mk'.comp continuous_fst).prodMk continuous_snd
    exact (continuous_of_discreteTopology
      (f := fun p : (AbsGalQ2 ⧸ N) × (Fin K → RegRep N) => p.1 • p.2)).comp h1
  have hmk : ∀ (g : AbsGalQ2) (y : Fin K → RegRep N), g • y = QuotientGroup.mk' N g • y :=
    fun _ _ => rfl
  have hρW : ∀ (g : AbsGalQ2) (w : Fin K → RegRep N), g • w = ρ g • w := by
    intro g w
    show QuotientGroup.mk' N g • w = e (ρ g) • w
    rw [QuotientGroup.mk'_apply, ← eOfSurj_rho ρ hρsurj g, he_def]
  set qW : (Fin K → RegRep N) → ZMod 2 := fun F => q (r F) with hqW_def
  set datW : FactorSet (AbsGalQ2 ⧸ N) (Fin K → RegRep N) :=
    sumDatum (orbitIndexSet N qW) (orbitDatum N) with hdatW_def
  set datWC : FactorSet C (Fin K → RegRep N) := datW.reindexHom e.toMonoidHom with hdatWC_def
  have hEqfsC : IsEquivariantFactorSet qW datWC :=
    isEquivariantFactorSet_reindexHom hEqfs e.toMonoidHom (fun _ _ => rfl)
  have hqeq : (fun v => qW (ι v)) = q := funext hIso
  have hcomap : IsEquivariantFactorSet q (datWC.comap ι) := by
    have := datum_comap hEqfsC ι (fun cc v => hιe cc v)
    rwa [hqeq] at this
  have hodd : Odd (Nat.card (Subgroup.zpowers (c tameTau))) := by
    rw [Nat.card_zpowers]; exact odd_orderOf_tameInertia c
  have hVI : ∀ v : V, (∀ i ∈ Subgroup.zpowers (c tameTau), i • v = v) → v = 0 :=
    fixedByNormal_eq_bot (Subgroup.zpowers (c tameTau)) (tameInertia_normal c hgen) hsimple
      (by obtain ⟨v, hv⟩ := hram; exact ⟨c tameTau, Subgroup.mem_zpowers _, v, hv⟩)
  have hstep1 : Q0loc D dat ρ x = Q0loc D (datWC.comap ι) ρ x :=
    OrbitVanish.Q0loc_datum_indep D dat (datWC.comap ι) hdat hcomap ρ hρ hV2
      (Subgroup.zpowers (c tameTau)) (tameInertia_normal c hgen) hodd hVI x
  have hic : Continuous (ι : V → Fin K → RegRep N) := continuous_of_discreteTopology
  have hicompat : ∀ (g : AbsGalQ2) (v : V), ι (g • v) = g • ι v := by
    intro g v
    rw [hρ g v, hιe (ρ g) v, hmk g (ι v), QuotientGroup.mk'_apply,
      ← eOfSurj_rho ρ hρsurj g, he_def]
  have hstep2 : Q0loc D (datWC.comap ι) ρ x
      = Q0loc D datWC ρ (mapCoeff1 ι hic hicompat x) :=
    RepIndependence.lemma_6_14 D datWC ρ ι hic hicompat hEqfsC (fun cc v => hιe cc v) hρW x
  rw [hstep1, hstep2]
  have hxW : mapCoeff1 ι hic hicompat x ∈ deepPart (V := Fin K → RegRep N) ρ :=
    ShapiroDeepness.deepPart_mapCoeff1 hρ hρW ι hic hicompat hx
  -- GOAL HERE: `Q0loc D datWC ρ (mapCoeff1 ι hic hicompat x) = 0`   ← the reducer, §3
  sorry
```

Needs `import GQ2.DimAssembly` and `import GQ2.ShapiroRead` (added).

## 3. The remaining reducer application (the last build)

Apply `OrbitVanish.Q0loc_vanish_of_datum_decomp D datWC ρ hρW xW` (`xW := mapCoeff1 ι … x`) with:

- `s := orbitIndexSet N qW`, `datf := fun o => (orbitDatum N o).reindexHom e.toMonoidHom`,
  `qf := orbitSquareMap N`.
- **`hdat_eq`** : `datWC = sumDatum s datf` — `rw [hdatWC_def, hdatW_def]; exact reindexHom_sumDatum …`.
- **`hdatf o ho`** : `isEquivariantFactorSet_reindexHom (isEqFS_orbitDatum N qW o ho) e.toMonoidHom (fun _ _ => rfl)`.
- **`U`/`inner`** by cases on `o : OrbitIx K (AbsGalQ2 ⧸ N)` (`Fin K ⊕ (Fin K × ·) ⊕ (Fin K × Fin K × ·)`),
  matching f2c1's `hcoh_*` RHS **verbatim**.  `b := (Quotient.out xW).1`:
  - `Sum.inl j` (square): `U = N`, `inner = fun p => shapiroCoord N (fun g => b g j) p.1 * … p.2`.
  - `Sum.inr (Sum.inr (j,k,u))` (free): `U = N`, `inner = fun p => shapiroCoord N (b·j) p.1 * shapiroCoord N (b·k) ⟨ĝ⁻¹ p.2 ĝ, …⟩` with `ĝ` a lift of `u`.
  - `Sum.inr (Sum.inl (j,u))` (involution): `ĝ := Quotient.out u` (`mk' ĝ = u` by `QuotientGroup.out_eq'`;
    `ĝ ∉ N` since `u ≠ 1`; `ĝ² ∈ N` since `u² = 1`), `U₀ = N ⊔ zpowers ĝ`,
    `inner = evensNormFun (N.subgroupOf U₀) ⟨ĝ,_⟩ (fun u => shapiroCoord N (b·j) ⟨u.1.1,u.2⟩)`.
- **`hcoh o ho`** (mechanical): `graphPullback (datf o) ρ b`
  `=[graphPullback_reindexHom (orbitDatum N o) e (fun _ _ => rfl) ρ b]` `graphPullback (orbitDatum N o) (⇑e ∘ ⇑ρ) b`.
  Then `⇑e ∘ ⇑ρ = ⇑(QuotientGroup.mk' N)` (`funext g; simp [eOfSurj_rho, QuotientGroup.mk'_apply]`),
  so it is `graphPullback (orbitDatum N o) (mk' N) b`, and `orbitDatum N (inl j) = squareBlockDatum N j`
  (etc., definitional) feeds `hcoh_square N hmk j hNopen (Quotient.out xW)` (resp. free/involution).
- **`hvanish o ho`**:
  - square: `hcup ⟨α_j,_⟩ ⟨α_j,_⟩ hdeep hdeep` where `α_j := shapiroCoord N (b·j)`, `hdeep :=
    shapiroCoord_mem_deepClasses ρ j hxW` (f2c1) — the `Z1`-membership `_` is `shapiroCoord_mem_Z1`.
  - free: `hcup ⟨α_j,_⟩ ⟨conj α_k,_⟩ hdeep_j hdeep_k'` — `conj α_k`'s class is deep via
    `AdmissibleCount.conjAct_deepClasses` (banked); check its cocycle shape matches f2c1's free RHS.
  - **involution**: THE OPEN PIECE — see §3a.

### 3a. The involution `hvanish` — the one genuine gap (Evens-norm cohomology-invariance)

f2c1's `hcoh_involution` gives `inner = evensNormFun … (shapiroCoord N (b·j))`.
c2's `hvanish_involution_of_deepClass` (`ShapiroDeepness.lean:224`) gives, for the deep class
`ξ = [shapiroCoord N (b·j)]`, `∃ β, H2ofFun U₀ (evensNormFun … (kummerCocycleFun β)) = 0`.
`[shapiroCoord N (b·j)] = [kummerCocycleFun β] = ξ` (cohomologous, both deep) but the two cochains
are NOT equal, and `evensNormFun` is degree-2 (a norm), so its output is not obviously invariant.

**The missing bridge**: `evensNormFun U s α - evensNormFun U s α' ∈ B²(U₀)` whenever `α - α' ∈ B¹(N)`
(cohomologous scalar inputs) — i.e. the Evens/transfer norm descends to `H¹(N) → H²(U₀)`.  With it,
`H2ofFun U₀ (evensNormFun (shapiroCoord)) = H2ofFun U₀ (evensNormFun (kummerCocycleFun β)) = 0`.
This is the last piece of §6.3 mathematics; ~50–100 lines of explicit degree-2 coboundary analysis
(`EvensKahn.lean`).  RECOMMENDED to prove it as a standalone lemma
`evensNormFun_sub_mem_B2_of_cohomologous`, then the involution `hvanish` is one line.

**Isolation option**: state the involution `hvanish` as an extra theorem hypothesis over a RAW
cochain `b : AbsGalQ2 → Fin K → RegRep (ker ρ)` (NOT `Z1 AbsGalQ2 W`, whose action instance is
proof-internal):
`∀ {K} (b) (j) (ĝ) (hĝ : ĝ ∉ ker ρ) (hĝ2 : ĝ*ĝ ∈ ker ρ) (U₀) (hU₀) (hmem),
  H1ofFun (ker ρ) (shapiroCoord (ker ρ) (b·j)) ∈ deepClasses (ker ρ) →
  H2ofFun ↥U₀ (evensNormFun ((ker ρ).subgroupOf U₀) ⟨ĝ,hmem⟩ (fun u => shapiroCoord (ker ρ) (b·j) ⟨u.1.1,u.2⟩)) = 0`.
Then `lemma_6_17_vanish_of_deepData` is sorry-free with `hcup`+`hinv_van` isolated (the f2a/b/c/f8
pattern), and the bridge above discharges `hinv_van` later.

## 4. The SectionSix statement-move (shared with P-15f8 — coordinate)

The sole consumer `DeepPart.prop_6_18_ramified` (`DeepPart.lean:1428`) calls BOTH sorries
`SectionSix.lemma_6_17_dim` (873) and `lemma_6_17_vanish` (894) and sits UPSTREAM of both downstream
proofs.  **The dim proof `ResidueLift.lemma_6_17_dim_final` is LANDED (P-15f8, std-3 + §6.3 budget).**
Once the vanish proof lands downstream, do the JOINT move: relocate `prop_6_18_ramified` to a new leaf
importing `ResidueLift` (dim) + this file (vanish), cite both `_final` proofs, delete the two
SectionSix sorried statements (comment-pointers à la lemma_6_14/P-15d), drop `SectionSix.lean` from the
dim/vanish `SORRY_ALLOWLIST` entries.  `prop_6_18_ramified` has no code consumers → low blast radius.

## 5. Discharging `hcup` (square/free, the other clean hypothesis)

`hvanish_cup` (`ShapiroDeepness.lean:50`) is over `k.fixingSubgroup`.  For `hcup` over `ker ρ`, set
`k := ResidueLift.splitField ρ` (P-15f8), `hker := ResidueLift.hker_splitField ρ`
(`ker ρ = k.fixingSubgroup` pointwise), `htriv := ResidueLift.htriv_zmod2`.  Transport the two deep
`Z1`s and the `deepClasses` membership along `DeepCount.h1KerFixEquiv` / the pointwise `hker`
(the `DeepCount §KerTransport` pattern) — same infra the f7 lane already built.
