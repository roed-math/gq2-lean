# Axiom statement closures

*Generated 2026-07-27 by `scripts/axiom_closure.sh`; regenerate after
any change to `GQ2/Foundations/Axioms.lean` or to a definition listed below.*

For each of the nine literature axioms this lists every **project** constant a reader
must understand to know *what the axiom asserts*: the transitive closure of the axiom's
statement through definition bodies and structure fields.  Mathlib constants are not
listed (they are the shared trusted vocabulary), and **proofs are pruned**: a theorem
reached by a definition contributes only its statement, since its proof is
machine-checked — the Lean-Compass review model (`docs/atlas.md`).  Definitions and
structures are what a human auditor reads; the referenced theorems are listed
separately since only their (checked) statements participate in meaning.

## Summary

| axiom | leaf | defs/structures to read | proved theorems referenced |
|---|---|---:|---:|
| **B1** | `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` | 1 | 0 |
| **B7** | `GQ2.Foundations.absGalQ2_localEulerCharacteristic` | 13 | 0 |
| **B3c** | `GQ2.dyadicOrientation` | 22 | 4 |
| **B5** | `GQ2.localReciprocity` | 12 | 0 |
| **B6** | `GQ2.tateDualityAt` | 36 | 5 |
| **B8** | `GQ2.peripheralCyclotomicAction` | 19 | 3 |
| **B9** | `GQ2.relativeStiefelWhitney_dyadic` | 37 | 4 |
| **B10** | `GQ2.tameQuotient` | 39 | 4 |
| **B11a** | `GQ2.hilbertSymbol_normCriterion_finiteDyadic` | 24 | 2 |
| **union** | all nine | 115 | 12 |

The union spans 24 modules: `GQ2.BoundaryFrame`, `GQ2.Cohomology`, `GQ2.CupProduct`, `GQ2.Demushkin`, `GQ2.DyadicPresentation`, `GQ2.EvensKahn`, `GQ2.Foundations.Axioms`, `GQ2.FreeProfinite`, `GQ2.Kummer`, `GQ2.MaxProP`, `GQ2.MuN`, `GQ2.Orientation`, `GQ2.PeripheralAction`, `GQ2.ProfinitePresentation`, `GQ2.ProfiniteQuotient`, `GQ2.Reciprocity`, `GQ2.Statement`, `GQ2.StiefelWhitney`, `GQ2.TameQuotient`, `GQ2.TateDuality`, `GQ2.TraceForm`, `GQ2.Words`, `GQ2.Zhat`, `GQ2.ZtwoPowering`.

## Vocabulary (union across the nine axioms)

Grouped by module; *(kind, source)* — *used by* — first docstring line.
### `GQ2/BoundaryFrame.lean`

- `GQ2.presentationLift` (def, [GQ2/BoundaryFrame.lean:101](../GQ2/BoundaryFrame.lean#L101)) — *B10* — Descend a relator-killing continuous hom to the profinite presentation. 
- `GQ2.tameWord` (def, [GQ2/BoundaryFrame.lean:120](../GQ2/BoundaryFrame.lean#L120)) — *B10* — The tame relator `τ^σ · (τ²)⁻¹` in the free profinite group on `σ, τ = of 0, of 1`. 
- `GQ2.Ttame` (def, [GQ2/BoundaryFrame.lean:124](../GQ2/BoundaryFrame.lean#L124)) — *B10* — **`T_tame`** (§3 opening): the finite-quotient tame group `⟨σ, τ ∣ τ^σ = τ²⟩_prof`. 
- `GQ2.Ztwo` (def, [GQ2/BoundaryFrame.lean:162](../GQ2/BoundaryFrame.lean#L162)) — *B10* — **`Z₂`**: the additive 2-adic integers as a profinite group, encoded as the pro-2
- `GQ2.ztwoOne` (def, [GQ2/BoundaryFrame.lean:165](../GQ2/BoundaryFrame.lean#L165)) — *B10* — The image of `1 ∈ ℤ` in `Z₂` — the common value `ν_t(σ) = ν₂(σ) = 1`. 
- `GQ2.tameToZhat` (def, [GQ2/BoundaryFrame.lean:170](../GQ2/BoundaryFrame.lean#L170)) — *B10* — The classifying map `σ ↦ 1, τ ↦ 0` into `ℤ̂` (multiplicative: `ofInt 1`, `1`). 
- `GQ2.nuT` (def, [GQ2/BoundaryFrame.lean:185](../GQ2/BoundaryFrame.lean#L185)) — *B10* — **`ν_t : Ttame ↠ Z₂`** (Prop 3.14): `ν_t(σ) = 1`, `ν_t(τ) = 0`.  (Surjectivity is a

### `GQ2/Cohomology.lean`

- `GQ2.ContCoh.H0` (def, [GQ2/Cohomology.lean:75](../GQ2/Cohomology.lean#L75)) — *B6, B7* — `H⁰(G, M)`: the invariants `M^G`, as an additive subgroup of `M`. 
- `GQ2.ContCoh.C1` (def, [GQ2/Cohomology.lean:84](../GQ2/Cohomology.lean#L84)) — *B6, B7, B9, B11a* — Continuous 1-cochains `C¹(G, M)`. 
- `GQ2.ContCoh.C2` (def, [GQ2/Cohomology.lean:91](../GQ2/Cohomology.lean#L91)) — *B6, B7, B9, B11a* — Continuous 2-cochains `C²(G, M)`. 
- `GQ2.ContCoh.dZero` (def, [GQ2/Cohomology.lean:98](../GQ2/Cohomology.lean#L98)) — *B6, B7, B9, B11a* — The differential `δ⁰ : M → C¹`, `(δ⁰m)(g) = g•m − m`. 
- `GQ2.ContCoh.dOne` (def, [GQ2/Cohomology.lean:104](../GQ2/Cohomology.lean#L104)) — *B6, B7, B9, B11a* — The differential `δ¹ : C¹ → C²`, `(δ¹ψ)(g,h) = g•ψ(h) − ψ(gh) + ψ(g)`. 
- `GQ2.ContCoh.dTwo` (def, [GQ2/Cohomology.lean:111](../GQ2/Cohomology.lean#L111)) — *B6, B7, B9, B11a* — The differential `δ² : C² → C³`,
- `GQ2.ContCoh.Z1` (def, [GQ2/Cohomology.lean:120](../GQ2/Cohomology.lean#L120)) — *B6, B7, B9, B11a* — Continuous 1-cocycles: continuous cochains killed by `δ¹`. 
- `GQ2.ContCoh.Z2` (def, [GQ2/Cohomology.lean:123](../GQ2/Cohomology.lean#L123)) — *B6, B7, B9, B11a* — Continuous 2-cocycles: continuous cochains killed by `δ²`. 
- `GQ2.ContCoh.B1` (def, [GQ2/Cohomology.lean:126](../GQ2/Cohomology.lean#L126)) — *B6, B7, B9, B11a* — 1-coboundaries `δ⁰(M)` (automatically continuous). 
- `GQ2.ContCoh.B2` (def, [GQ2/Cohomology.lean:129](../GQ2/Cohomology.lean#L129)) — *B6, B7, B9, B11a* — 2-coboundaries `δ¹(C¹)` — the image of the **continuous** 1-cochains. 
- `GQ2.ContCoh.H1` (def, [GQ2/Cohomology.lean:132](../GQ2/Cohomology.lean#L132)) — *B6, B7, B9, B11a* — `H¹(G, M)`: continuous 1-cocycles modulo 1-coboundaries. 
- `GQ2.ContCoh.H1mk` (def, [GQ2/Cohomology.lean:138](../GQ2/Cohomology.lean#L138)) — *B9, B11a* — The class map `Z¹ → H¹`. 
- `GQ2.ContCoh.H2` (def, [GQ2/Cohomology.lean:141](../GQ2/Cohomology.lean#L141)) — *B6, B7, B9, B11a* — `H²(G, M)`: continuous 2-cocycles modulo coboundaries of continuous 1-cochains. 
- `GQ2.ContCoh.H2mk` (def, [GQ2/Cohomology.lean:147](../GQ2/Cohomology.lean#L147)) — *B6, B9, B11a* — The class map `Z² → H²`. 
- `GQ2.ContCoh.instAddCommGroupH1` (def, [GQ2/Cohomology.lean](../GQ2/Cohomology.lean)) — *B6, B9, B11a*
- `GQ2.ContCoh.instAddCommGroupH2` (def, [GQ2/Cohomology.lean](../GQ2/Cohomology.lean)) — *B6, B9, B11a*

### `GQ2/CupProduct.lean`

- `GQ2.ContCoh.cup11Fun` (def, [GQ2/CupProduct.lean:49](../GQ2/CupProduct.lean#L49)) — *B6, B9, B11a* — The `(1,1)`-cup cochain `(a ∪ b)(g,h) = μ (a g) (g • b h)`. 
- `GQ2.ContCoh.cup11_mem_Z2` (theorem, [GQ2/CupProduct.lean:85](../GQ2/CupProduct.lean#L85)) — *B6, B9, B11a* — **Cup of cocycles is a cocycle**: the key 2-cocycle identity for `(1,1)`. 
- `GQ2.ContCoh.cup11ZH` (def, [GQ2/CupProduct.lean:100](../GQ2/CupProduct.lean#L100)) — *B6, B9, B11a* — The `(1,1)` cup, bundled biadditively at the cocycle level and post-composed with the class
- `GQ2.ContCoh.cup11` (def, [GQ2/CupProduct.lean:153](../GQ2/CupProduct.lean#L153)) — *B6, B9, B11a* — **The `(1,1)` cup product** `H¹(G,M) →+ H¹(G,N) →+ H²(G,P)`, bilinear by construction. 
- `GQ2.ContCoh.cup02Fun` (def, [GQ2/CupProduct.lean:196](../GQ2/CupProduct.lean#L196)) — *B6* — The `(0,2)`-cup cochain `(a ∪ b)(g,h) = μ a (b (g,h))`. 
- `GQ2.ContCoh.cup02_mem_Z2` (theorem, [GQ2/CupProduct.lean:220](../GQ2/CupProduct.lean#L220)) — *B6* — Cup of an invariant with a 2-cocycle is a 2-cocycle. 
- `GQ2.ContCoh.cup02FlipZH` (def, [GQ2/CupProduct.lean:245](../GQ2/CupProduct.lean#L245)) — *B6* — The `(0,2)` cup, bundled biadditively at the cocycle level (`Z²`-slot first, so that it can be
- `GQ2.ContCoh.cup02` (def, [GQ2/CupProduct.lean:260](../GQ2/CupProduct.lean#L260)) — *B6* — **The `(0,2)` cup product** `H⁰(G,M) →+ H²(G,N) →+ H²(G,P)`. 
- `GQ2.ContCoh.cup20Fun` (def, [GQ2/CupProduct.lean:272](../GQ2/CupProduct.lean#L272)) — *B6* — The `(2,0)`-cup cochain `(a ∪ b)(g,h) = μ (a (g,h)) ((g·h) • b)`. 
- `GQ2.ContCoh.cup20_mem_Z2` (theorem, [GQ2/CupProduct.lean:301](../GQ2/CupProduct.lean#L301)) — *B6* — Cup of a 2-cocycle with an invariant is a 2-cocycle. 
- `GQ2.ContCoh.cup20ZH` (def, [GQ2/CupProduct.lean:330](../GQ2/CupProduct.lean#L330)) — *B6* — The `(2,0)` cup, bundled biadditively at the cocycle level. 
- `GQ2.ContCoh.cup20` (def, [GQ2/CupProduct.lean:345](../GQ2/CupProduct.lean#L345)) — *B6* — **The `(2,0)` cup product** `H²(G,M) →+ H⁰(G,N) →+ H²(G,P)`. 

### `GQ2/Demushkin.lean`

- `GQ2.trivialCupPairing` (def, [GQ2/Demushkin.lean:95](../GQ2/Demushkin.lean#L95)) — *B9, B11a* — The cup-product form `H¹(G,𝔽_p) × H¹(G,𝔽_p) → H²(G,𝔽_p)` relative to the multiplication

### `GQ2/DyadicPresentation.lean`

- `GQ2.d0Relator` (def, [GQ2/DyadicPresentation.lean:45](../GQ2/DyadicPresentation.lean#L45)) — *B3c* — The **dyadic Demushkin relator** `r₀ = A²S⁴[S,Y]` (Labute [2], Thm 8 at `d = 1`; the paper's
- `GQ2.D0Full` (def, [GQ2/DyadicPresentation.lean:56](../GQ2/DyadicPresentation.lean#L56)) — *B3c* — The full profinite presentation `⟨A, S, Y | A²S⁴[S,Y]⟩` (before taking the pro-2 quotient).
- `GQ2.D0` (def, [GQ2/DyadicPresentation.lean:62](../GQ2/DyadicPresentation.lean#L62)) — *B3c* — **`D₀`** (paper Prop. 1.1): the **pro-2** group presented by `⟨A, S, Y | A²S⁴[S,Y] = 1⟩`, i.e.
- `GQ2.d0FullA` (def, [GQ2/DyadicPresentation.lean:72](../GQ2/DyadicPresentation.lean#L72)) — *B3c* — The generator `A` in the full presentation `D0Full` (image of `of 0`). 
- `GQ2.d0FullS` (def, [GQ2/DyadicPresentation.lean:75](../GQ2/DyadicPresentation.lean#L75)) — *B3c* — The generator `S` in the full presentation `D0Full` (image of `of 1`). 
- `GQ2.d0FullY` (def, [GQ2/DyadicPresentation.lean:78](../GQ2/DyadicPresentation.lean#L78)) — *B3c* — The generator `Y` in the full presentation `D0Full` (image of `of 2`). 
- `GQ2.d0A` (def, [GQ2/DyadicPresentation.lean:89](../GQ2/DyadicPresentation.lean#L89)) — *B3c* — The generator `A ∈ D₀` (image of `A` under the pro-2 quotient map). 
- `GQ2.d0S` (def, [GQ2/DyadicPresentation.lean:91](../GQ2/DyadicPresentation.lean#L91)) — *B3c* — The generator `S ∈ D₀`. 
- `GQ2.d0Y` (def, [GQ2/DyadicPresentation.lean:93](../GQ2/DyadicPresentation.lean#L93)) — *B3c* — The generator `Y ∈ D₀`. 

### `GQ2/EvensKahn.lean`

- `GQ2.evensAux` (def, [GQ2/EvensKahn.lean:123](../GQ2/EvensKahn.lean#L123)) — *B9* — The first Shapiro component (paper eq. (97), `u = 1`):
- `GQ2.bS` (def, [GQ2/EvensKahn.lean:127](../GQ2/EvensKahn.lean#L127)) — *B9* — The second Shapiro component `b(γ)_s`, via the identity `b(γ)_s = b(s⁻¹γ)₁`. 
- `GQ2.corFun` (def, [GQ2/EvensKahn.lean:231](../GQ2/EvensKahn.lean#L231)) — *B9* — The **degree-1 corestriction cocycle**: `cor(α) = b₁ + b_s` (sum over the transversal
- `GQ2.corFun_mem_Z1` (theorem, [GQ2/EvensKahn.lean:253](../GQ2/EvensKahn.lean#L253)) — *B9* — `cor(α)` as a continuous 1-cocycle (trivial action): membership in `Z¹(G, 𝔽₂)`. 
- `GQ2.corH1` (def, [GQ2/EvensKahn.lean:261](../GQ2/EvensKahn.lean#L261)) — *B9* — The **degree-1 corestriction class** `cor([α]) ∈ H¹(G, 𝔽₂)`. 
- `GQ2.evensNormFun` (def, [GQ2/EvensKahn.lean:277](../GQ2/EvensKahn.lean#L277)) — *B9* — The paper's eq. (98): `ν_α(γ,η) = b(γ)₁·b(η)_{γ̄⁻¹s} + ε(γ̄)·b(η)₁·b(η)_s`.  Its class is
- `GQ2.evensNormFun_mem_Z2` (theorem, [GQ2/EvensKahn.lean:303](../GQ2/EvensKahn.lean#L303)) — *B9* — **`ν_α` is a 2-cocycle** — the pairwise-cancellation calculation of the module docstring
- `GQ2.evensNormH2` (def, [GQ2/EvensKahn.lean:332](../GQ2/EvensKahn.lean#L332)) — *B9* — The **index-two Evens norm** `N^{Ev}([α]) ∈ H²(G, 𝔽₂)`, defined as the class of the
- `GQ2.sqrtCl` (def, [GQ2/EvensKahn.lean:414](../GQ2/EvensKahn.lean#L414)) — *B9, B11a* — A canonical square root in the algebraically closed `ℚ̄₂`. 
- `GQ2.kummerClassK` (def, [GQ2/EvensKahn.lean:437](../GQ2/EvensKahn.lean#L437)) — *B9, B11a* — **The base-general Kummer class** `[a] ∈ H¹(G_k, 𝔽₂)` of a unit `a ∈ kˣ`, over the subtype

### `GQ2/Foundations/Axioms.lean`

- `GQ2.localReciprocity` (axiom, [GQ2/Foundations/Axioms.lean:171](../GQ2/Foundations/Axioms.lean#L171)) — *B10* — **The B5 axiom.** Local class field theory for `ℚ₂` provides the reciprocity bundle.

### `GQ2/FreeProfinite.lean`

- `GQ2.FreeProfiniteGroup` (def, [GQ2/FreeProfinite.lean:38](../GQ2/FreeProfinite.lean#L38)) — *B3c, B8, B10* — The **free profinite group** on a type `X`: the profinite completion of the discrete free
- `GQ2.FreeProfiniteGroup.of` (def, [GQ2/FreeProfinite.lean:42](../GQ2/FreeProfinite.lean#L42)) — *B3c, B8, B10* — The canonical inclusion of the generators `X → FreeProfiniteGroup X`. 
- `GQ2.grpCatHomEquiv` (def, [GQ2/FreeProfinite.lean:46](../GQ2/FreeProfinite.lean#L46)) — *B10* — `GrpCat` morphisms between `of`-objects are exactly monoid homs. 
- `GQ2.FreeProfiniteGroup.homEquiv` (def, [GQ2/FreeProfinite.lean:56](../GQ2/FreeProfinite.lean#L56)) — *B10* — **Universal property of the free profinite group.**  Morphisms of profinite groups

### `GQ2/Kummer.lean`

- `GQ2.Kummer.GaloisGroup` (def, [GQ2/Kummer.lean:68](../GQ2/Kummer.lean#L68)) — *B9, B11a* — The absolute Galois group `Gal(k̄/k)` as `k̄ ≃ₐ[k] k̄`.  A reducible abbreviation (so instance
- `GQ2.Kummer.kummerCocycleFun` (def, [GQ2/Kummer.lean:93](../GQ2/Kummer.lean#L93)) — *B9, B11a* — The Kummer cocycle function `κ : G_k → 𝔽₂` attached to a square root `α = √a ∈ k̄`:
- `GQ2.Kummer.instContinuousSMulGaloisGroupZModOfNatNat` (theorem, [GQ2/Kummer.lean](../GQ2/Kummer.lean)) — *B9, B11a*
- `GQ2.Kummer.instDistribMulActionGaloisGroupZModOfNatNat` (def, [GQ2/Kummer.lean](../GQ2/Kummer.lean)) — *B9, B11a* — The **trivial** action of `Gal(k̄/k)` on `𝔽₂ = ZMod 2` (`±1 ∈ k` is fixed).  This is the

### `GQ2/MaxProP.lean`

- `GQ2.IsProP` (def, [GQ2/MaxProP.lean:61](../GQ2/MaxProP.lean#L61)) — *B10* — A topological group `P` is **pro-`p`** if every finite continuous quotient `P ⧸ U`
- `GQ2.proPKernel` (def, [GQ2/MaxProP.lean:131](../GQ2/MaxProP.lean#L131)) — *B3c, B8, B10* — The **pro-`p` kernel** of `G`: the intersection of all open normal subgroups `U ≤ G` with
- `GQ2.proPKernel_normal` (theorem, [GQ2/MaxProP.lean:134](../GQ2/MaxProP.lean#L134)) — *B3c, B8, B10*
- `GQ2.proPKernel_isClosed` (theorem, [GQ2/MaxProP.lean:138](../GQ2/MaxProP.lean#L138)) — *B3c, B8, B10*
- `GQ2.maxProPQuotient` (def, [GQ2/MaxProP.lean:152](../GQ2/MaxProP.lean#L152)) — *B3c, B8, B10* — The **maximal pro-`p` quotient** `G(p)` of a profinite group `G`, as an object of
- `GQ2.maxProPMk` (def, [GQ2/MaxProP.lean:158](../GQ2/MaxProP.lean#L158)) — *B3c, B8, B10* — The canonical projection `G → G(p)`, a continuous homomorphism. 

### `GQ2/MuN.lean`

- `GQ2.galRootsOfUnity` (def, [GQ2/MuN.lean:78](../GQ2/MuN.lean#L78)) — *B6* — **The Galois action on `μₙ(L) = rootsOfUnity n L`.**  `Gal(L/K)` acts by restricting its
- `GQ2.MuN` (def, [GQ2/MuN.lean:151](../GQ2/MuN.lean#L151)) — *B6* — **`μₙ` over `ℚ₂`**, the group of `n`-th roots of unity in a fixed algebraic closure of `ℚ₂`,
- `GQ2.instDistribMulActionAbsGalQ2MuN` (def, [GQ2/MuN.lean](../GQ2/MuN.lean)) — *B6* — The additive Galois action of `G_ℚ₂` on `μₙ`. 

### `GQ2/Orientation.lean`

- `GQ2.DyadicOrientation` (structure, [GQ2/Orientation.lean:73](../GQ2/Orientation.lean#L73)) — *B3c* — **B3c (dyadic orientation, cyclotomic interface — route (ii)).**  A B4 isomorphism

### `GQ2/PeripheralAction.lean`

- `GQ2.Delta` (def, [GQ2/PeripheralAction.lean:72](../GQ2/PeripheralAction.lean#L72)) — *B8* — **`Δ`** (paper §3): the maximal pro-2 quotient of the free profinite group on two generators —
- `GQ2.deltaP` (def, [GQ2/PeripheralAction.lean:75](../GQ2/PeripheralAction.lean#L75)) — *B8* — The peripheral generator `P` (image of the first free generator in `Δ`). 
- `GQ2.deltaT` (def, [GQ2/PeripheralAction.lean:79](../GQ2/PeripheralAction.lean#L79)) — *B8* — The peripheral generator `T` (image of the second free generator in `Δ`). 
- `GQ2.deltaC` (def, [GQ2/PeripheralAction.lean:83](../GQ2/PeripheralAction.lean#L83)) — *B8* — The third peripheral generator `C := (P·T)⁻¹` (so `P·T·C = 1`). 
- `GQ2.PeripheralCyclotomicAction` (structure, [GQ2/PeripheralAction.lean:92](../GQ2/PeripheralAction.lean#L92)) — *B8* — **Lemma 3.6 (B8), bundled.**  The cyclotomic action on the peripheral generators of

### `GQ2/ProfinitePresentation.lean`

- `GQ2.relatorSubgroup` (def, [GQ2/ProfinitePresentation.lean:34](../GQ2/ProfinitePresentation.lean#L34)) — *B3c, B10* — The **closed normal closure** of a set `rels` in the free profinite group on `X`: the smallest
- `GQ2.profinitePresentation` (def, [GQ2/ProfinitePresentation.lean:43](../GQ2/ProfinitePresentation.lean#L43)) — *B3c, B10* — The profinite group **presented** by generators `X` and relators `rels`: the free profinite
- `GQ2.instNormalCarrierToTopTotallyDisconnectedSpaceToProfiniteFreeProfiniteGroupRelatorSubgroup` (theorem, [GQ2/ProfinitePresentation.lean](../GQ2/ProfinitePresentation.lean)) — *B3c, B10*

### `GQ2/ProfiniteQuotient.lean`

- `GQ2.instTotallyDisconnectedSpace_quotient` (theorem, [GQ2/ProfiniteQuotient.lean:74](../GQ2/ProfiniteQuotient.lean#L74)) — *B3c, B8, B10* — **Total disconnectedness of `G ⧸ N`** for `G` profinite and `N` closed normal.  Together with
- `GQ2.profiniteQuotient` (def, [GQ2/ProfiniteQuotient.lean:83](../GQ2/ProfiniteQuotient.lean#L83)) — *B3c, B8, B10* — The quotient of a profinite group `G` by a closed normal subgroup `N`, packaged as an object of
- `GQ2.quotientMk` (def, [GQ2/ProfiniteQuotient.lean:88](../GQ2/ProfiniteQuotient.lean#L88)) — *B3c, B8, B10* — The quotient projection `G → G ⧸ N` as a continuous homomorphism. 
- `GQ2.quotientLift` (def, [GQ2/ProfiniteQuotient.lean:108](../GQ2/ProfiniteQuotient.lean#L108)) — *B10* — **Universal property of the profinite quotient.**  A continuous homomorphism `f : G →ₜ* P`

### `GQ2/Reciprocity.lean`

- `GQ2.AbsGalQ2ab` (def, [GQ2/Reciprocity.lean:110](../GQ2/Reciprocity.lean#L110)) — *B5, B10* — `G_{ℚ₂}^{ab}`, the **topological abelianization** of `G_{ℚ₂}`.  This *is* Mathlib's
- `GQ2.commClosure` (def, [GQ2/Reciprocity.lean:117](../GQ2/Reciprocity.lean#L117)) — *B5, B10* — The closed commutator subgroup `closure⁅G_{ℚ₂}, G_{ℚ₂}⁆` — precisely the subgroup Mathlib's
- `GQ2.toAb` (def, [GQ2/Reciprocity.lean:121](../GQ2/Reciprocity.lean#L121)) — *B10* — The abelianization projection `G_{ℚ₂} ↠ G_{ℚ₂}^{ab}` (the missing
- `GQ2.chiCyc` (def, [GQ2/Reciprocity.lean:128](../GQ2/Reciprocity.lean#L128)) — *B3c, B5, B10* — The 2-adic cyclotomic character `χ_cyc : G_{ℚ₂} →* ℤ₂ˣ`, `g ↦ (ζ ↦ ζ^{χ(g)})` on
- `GQ2.chiCycAb` (def, [GQ2/Reciprocity.lean:144](../GQ2/Reciprocity.lean#L144)) — *B5, B10* — The cyclotomic character as a map out of the abelianization, `χ_cyc : G_{ℚ₂}^{ab} →* ℤ₂ˣ`. 
- `GQ2.v2` (def, [GQ2/Reciprocity.lean:155](../GQ2/Reciprocity.lean#L155)) — *B5, B10* — The 2-adic valuation `v₂ : ℚ₂ˣ → ℤ` of a unit of `ℚ₂` (`Padic.valuation`).  `v₂(2) = 1`,
- `GQ2.normSubgroup` (def, [GQ2/Reciprocity.lean:161](../GQ2/Reciprocity.lean#L161)) — *B5, B10* — The **norm subgroup** `N_{L/ℚ₂}(Lˣ) ≤ ℚ₂ˣ` of a finite layer `L/ℚ₂`: the image of the field norm
- `GQ2.restrictHom` (def, [GQ2/Reciprocity.lean:171](../GQ2/Reciprocity.lean#L171)) — *B5, B10* — Mathlib's `AlgEquiv.restrictNormalHom` for the layer `L/ℚ₂`, but with its domain presented as
- `GQ2.restrictAb` (def, [GQ2/Reciprocity.lean:192](../GQ2/Reciprocity.lean#L192)) — *B5, B10* — The **abelianized restriction** `G_{ℚ₂}^{ab} → Gal(L/ℚ₂)` for a finite abelian Galois layer
- `GQ2.unitEmbed` (def, [GQ2/Reciprocity.lean:209](../GQ2/Reciprocity.lean#L209)) — *B5, B10* — A `ℤ₂`-unit as a `ℚ₂`-unit, `ℤ₂ˣ ↪ ℚ₂ˣ`. 
- `GQ2.uniformizer` (def, [GQ2/Reciprocity.lean:216](../GQ2/Reciprocity.lean#L216)) — *B5, B10* — The uniformizer `2 ∈ ℚ₂ˣ`. 
- `GQ2.LocalReciprocity` (structure, [GQ2/Reciprocity.lean:225](../GQ2/Reciprocity.lean#L225)) — *B5, B10* — **B5 (local reciprocity for `ℚ₂`), the bundle.**  The arithmetic reciprocity map `rec` and the

### `GQ2/Statement.lean`

- `GQ2.AbsGalQ2` (def, [GQ2/Statement.lean:40](../GQ2/Statement.lean#L40)) — *B1, B3c, B5, B6, B7, B10* — `G_{ℚ₂}`, the absolute Galois group of the 2-adic numbers, as a topological group. 

### `GQ2/StiefelWhitney.lean`

- `GQ2.diagForm` (def, [GQ2/StiefelWhitney.lean:82](../GQ2/StiefelWhitney.lean#L82)) — *B9* — The **diagonal binary quadratic form** `⟨x, y⟩` over `↥k` with unit weights, on the model
- `GQ2.IsDiagonalization` (def, [GQ2/StiefelWhitney.lean:92](../GQ2/StiefelWhitney.lean#L92)) — *B9* — `Q` **is diagonalized by the unit pair** `(x, y)`: an isometry `Q ≃ ⟨x, y⟩` onto the
- `GQ2.swOne` (def, [GQ2/StiefelWhitney.lean:413](../GQ2/StiefelWhitney.lean#L413)) — *B9* — The **degree-1 Stiefel–Whitney class** `w₁ Q ∈ H¹(G_k, 𝔽₂)` of a quadratic form over `↥k`:
- `GQ2.swTwo` (def, [GQ2/StiefelWhitney.lean:423](../GQ2/StiefelWhitney.lean#L423)) — *B9* — The **degree-2 Stiefel–Whitney class** `w₂ Q ∈ H²(G_k, 𝔽₂)`: the cup product

### `GQ2/TameQuotient.lean`

- `GQ2.TameQuotientData` (structure, [GQ2/TameQuotient.lean:70](../GQ2/TameQuotient.lean#L70)) — *B10* — **B10 (tame quotient of `G_ℚ₂`), the bundle.**  A closed normal pro-2 subgroup
- `GQ2.OrientedTameQuotient` (structure, [GQ2/TameQuotient.lean:99](../GQ2/TameQuotient.lean#L99)) — *B10* — **B10′ (oriented tame quotient), the bundle.**  A B10 tame-quotient datum whose unramified

### `GQ2/TateDuality.lean`

- `GQ2.MuDual` (def, [GQ2/TateDuality.lean:80](../GQ2/TateDuality.lean#L80)) — *B6* — **The `μₙ`-dual module** `M′ = Hom(M, μₙ)` of a discrete `G`-module `M`, with the conjugation
- `GQ2.muDualPairing` (def, [GQ2/TateDuality.lean:169](../GQ2/TateDuality.lean#L169)) — *B6* — **The evaluation pairing** `Hom(M, μₙ) →+ M →+ μₙ` — under the type synonym, literally the
- `GQ2.muDualPairing_equivariant` (theorem, [GQ2/TateDuality.lean:179](../GQ2/TateDuality.lean#L179)) — *B6* — Equivariance of the evaluation pairing — the `hμ` hypothesis of the cup products. 
- `GQ2.TateDualityG` (structure, [GQ2/TateDuality.lean:208](../GQ2/TateDuality.lean#L208)) — *B6* — **B6 (local Tate duality), the bundle at a local Galois group `G`** — per-`n` form (see the
- `GQ2.IsLocalDualizingGroup` (def, [GQ2/TateDuality.lean:244](../GQ2/TateDuality.lean#L244)) — *B6* — **`G` is a local dualizing group over `ℚ₂`** — the truth-side hypothesis gating the
- `GQ2.instAddCommGroupMuDual` (def, [GQ2/TateDuality.lean](../GQ2/TateDuality.lean)) — *B6*
- `GQ2.instDiscreteTopologyMuDual` (theorem, [GQ2/TateDuality.lean](../GQ2/TateDuality.lean)) — *B6*
- `GQ2.instDistribMulActionMuDual` (def, [GQ2/TateDuality.lean](../GQ2/TateDuality.lean)) — *B6* — The conjugation action of `G` on `Hom(M, μₙ)`. 
- `GQ2.instFunLikeMuDualMuN` (def, [GQ2/TateDuality.lean](../GQ2/TateDuality.lean)) — *B6*
- `GQ2.instTopologicalSpaceMuDual` (def, [GQ2/TateDuality.lean](../GQ2/TateDuality.lean)) — *B6*

### `GQ2/TraceForm.lean`

- `GQ2.quadExt` (def, [GQ2/TraceForm.lean:68](../GQ2/TraceForm.lean#L68)) — *B9* — The extension `k(δ)` of the finite dyadic base `k`, as an intermediate field of `ℚ̄₂/↥k`.
- `GQ2.traceFormOne` (def, [GQ2/TraceForm.lean:142](../GQ2/TraceForm.lean#L142)) — *B9* — The **untwisted trace form** `Tr⟨1⟩` of `k(δ)/k`: the quadratic form
- `GQ2.traceFormTwisted` (def, [GQ2/TraceForm.lean:153](../GQ2/TraceForm.lean#L153)) — *B9* — The **`a`-twisted trace form** `Tr⟨a⟩` of `k(δ)/k`: the quadratic form

### `GQ2/Words.lean`

- `GQ2.omega2Exp` (def, [GQ2/Words.lean:42](../GQ2/Words.lean#L42)) — *B8* — A concrete nonnegative-integer representative of the profinite idempotent `ω₂` modulo `n`:
- `GQ2.conjP` (def, [GQ2/Words.lean:56](../GQ2/Words.lean#L56)) — *B8, B10* — Right conjugation `x ^ g = g⁻¹ x g` (paper's convention). 
- `GQ2.commP` (def, [GQ2/Words.lean:59](../GQ2/Words.lean#L59)) — *B3c* — Commutator `[x, y] = x⁻¹ y⁻¹ x y` (paper's convention). 

### `GQ2/Zhat.lean`

- `GQ2.Zhat` (def, [GQ2/Zhat.lean:119](../GQ2/Zhat.lean#L119)) — *B8, B10* — **`ℤ̂`** — the profinite completion of the integers, i.e. `lim_N ℤ/N` over all finite-index
- `GQ2.Zhat.ofInt` (def, [GQ2/Zhat.lean:126](../GQ2/Zhat.lean#L126)) — *B10* — The canonical dense embedding `ℤ → ℤ̂` (written multiplicatively:
- `GQ2.omega2` (def, [GQ2/Zhat.lean:155](../GQ2/Zhat.lean#L155)) — *B8* — **The profinite idempotent `ω₂ ∈ ℤ̂`** (paper §1 and App. A/B): the unique element of
- `GQ2.zpowHatHom` (def, [GQ2/Zhat.lean:175](../GQ2/Zhat.lean#L175)) — *B8* — The `ẑ`-power morphism: for `x` in a profinite group `G`, the unique continuous extension of
- `GQ2.zpowHat` (def, [GQ2/Zhat.lean:181](../GQ2/Zhat.lean#L181)) — *B8* — `x ^ᶻ γ`: the `γ`-th power of `x : G` for a profinite exponent `γ : ℤ̂` (`G` profinite).

### `GQ2/ZtwoPowering.lean`

- `GQ2.zhatProjTwo` (def, [GQ2/ZtwoPowering.lean:204](../GQ2/ZtwoPowering.lean#L204)) — *B8* — **The canonical projection `ℤ̂ → ℤ₂`** (multiplicatively: onto `Multiplicative ℤ₂`), as the

## Per-axiom closures

### B1 — `GQ2.Foundations.absGalQ2_isTopologicallyFinitelyGenerated` ([GQ2/Foundations/Axioms.lean:97](../GQ2/Foundations/Axioms.lean#L97))

*Read (1):* `GQ2.AbsGalQ2`

### B7 — `GQ2.Foundations.absGalQ2_localEulerCharacteristic` ([GQ2/Foundations/Axioms.lean:117](../GQ2/Foundations/Axioms.lean#L117))

*Read (13):* `GQ2.AbsGalQ2`, `GQ2.ContCoh.B1`, `GQ2.ContCoh.B2`, `GQ2.ContCoh.C1`, `GQ2.ContCoh.C2`, `GQ2.ContCoh.H0`, `GQ2.ContCoh.H1`, `GQ2.ContCoh.H2`, `GQ2.ContCoh.Z1`, `GQ2.ContCoh.Z2`, `GQ2.ContCoh.dOne`, `GQ2.ContCoh.dTwo`, `GQ2.ContCoh.dZero`

### B3c — `GQ2.dyadicOrientation` ([GQ2/Foundations/Axioms.lean:158](../GQ2/Foundations/Axioms.lean#L158))

*Read (22):* `GQ2.AbsGalQ2`, `GQ2.D0`, `GQ2.D0Full`, `GQ2.DyadicOrientation`, `GQ2.FreeProfiniteGroup`, `GQ2.FreeProfiniteGroup.of`, `GQ2.chiCyc`, `GQ2.commP`, `GQ2.d0A`, `GQ2.d0FullA`, `GQ2.d0FullS`, `GQ2.d0FullY`, `GQ2.d0Relator`, `GQ2.d0S`, `GQ2.d0Y`, `GQ2.maxProPMk`, `GQ2.maxProPQuotient`, `GQ2.proPKernel`, `GQ2.profinitePresentation`, `GQ2.profiniteQuotient`, `GQ2.quotientMk`, `GQ2.relatorSubgroup`

*Checked statements referenced (4):* `GQ2.instNormalCarrierToTopTotallyDisconnectedSpaceToProfiniteFreeProfiniteGroupRelatorSubgroup`, `GQ2.instTotallyDisconnectedSpace_quotient`, `GQ2.proPKernel_isClosed`, `GQ2.proPKernel_normal`

### B5 — `GQ2.localReciprocity` ([GQ2/Foundations/Axioms.lean:171](../GQ2/Foundations/Axioms.lean#L171))

*Read (12):* `GQ2.AbsGalQ2`, `GQ2.AbsGalQ2ab`, `GQ2.LocalReciprocity`, `GQ2.chiCyc`, `GQ2.chiCycAb`, `GQ2.commClosure`, `GQ2.normSubgroup`, `GQ2.restrictAb`, `GQ2.restrictHom`, `GQ2.uniformizer`, `GQ2.unitEmbed`, `GQ2.v2`

### B6 — `GQ2.tateDualityAt` ([GQ2/Foundations/Axioms.lean:197](../GQ2/Foundations/Axioms.lean#L197))

*Read (36):* `GQ2.AbsGalQ2`, `GQ2.ContCoh.B1`, `GQ2.ContCoh.B2`, `GQ2.ContCoh.C1`, `GQ2.ContCoh.C2`, `GQ2.ContCoh.H0`, `GQ2.ContCoh.H1`, `GQ2.ContCoh.H2`, `GQ2.ContCoh.H2mk`, `GQ2.ContCoh.Z1`, `GQ2.ContCoh.Z2`, `GQ2.ContCoh.cup02`, `GQ2.ContCoh.cup02FlipZH`, `GQ2.ContCoh.cup02Fun`, `GQ2.ContCoh.cup11`, `GQ2.ContCoh.cup11Fun`, `GQ2.ContCoh.cup11ZH`, `GQ2.ContCoh.cup20`, `GQ2.ContCoh.cup20Fun`, `GQ2.ContCoh.cup20ZH`, `GQ2.ContCoh.dOne`, `GQ2.ContCoh.dTwo`, `GQ2.ContCoh.dZero`, `GQ2.ContCoh.instAddCommGroupH1`, `GQ2.ContCoh.instAddCommGroupH2`, `GQ2.IsLocalDualizingGroup`, `GQ2.MuDual`, `GQ2.MuN`, `GQ2.TateDualityG`, `GQ2.galRootsOfUnity`, `GQ2.instAddCommGroupMuDual`, `GQ2.instDistribMulActionAbsGalQ2MuN`, `GQ2.instDistribMulActionMuDual`, `GQ2.instFunLikeMuDualMuN`, `GQ2.instTopologicalSpaceMuDual`, `GQ2.muDualPairing`

*Checked statements referenced (5):* `GQ2.ContCoh.cup02_mem_Z2`, `GQ2.ContCoh.cup11_mem_Z2`, `GQ2.ContCoh.cup20_mem_Z2`, `GQ2.instDiscreteTopologyMuDual`, `GQ2.muDualPairing_equivariant`

### B8 — `GQ2.peripheralCyclotomicAction` ([GQ2/Foundations/Axioms.lean:225](../GQ2/Foundations/Axioms.lean#L225))

*Read (19):* `GQ2.Delta`, `GQ2.FreeProfiniteGroup`, `GQ2.FreeProfiniteGroup.of`, `GQ2.PeripheralCyclotomicAction`, `GQ2.Zhat`, `GQ2.conjP`, `GQ2.deltaC`, `GQ2.deltaP`, `GQ2.deltaT`, `GQ2.maxProPMk`, `GQ2.maxProPQuotient`, `GQ2.omega2`, `GQ2.omega2Exp`, `GQ2.proPKernel`, `GQ2.profiniteQuotient`, `GQ2.quotientMk`, `GQ2.zhatProjTwo`, `GQ2.zpowHat`, `GQ2.zpowHatHom`

*Checked statements referenced (3):* `GQ2.instTotallyDisconnectedSpace_quotient`, `GQ2.proPKernel_isClosed`, `GQ2.proPKernel_normal`

### B9 — `GQ2.relativeStiefelWhitney_dyadic` ([GQ2/Foundations/Axioms.lean:266](../GQ2/Foundations/Axioms.lean#L266))

*Read (37):* `GQ2.ContCoh.B1`, `GQ2.ContCoh.B2`, `GQ2.ContCoh.C1`, `GQ2.ContCoh.C2`, `GQ2.ContCoh.H1`, `GQ2.ContCoh.H1mk`, `GQ2.ContCoh.H2`, `GQ2.ContCoh.H2mk`, `GQ2.ContCoh.Z1`, `GQ2.ContCoh.Z2`, `GQ2.ContCoh.cup11`, `GQ2.ContCoh.cup11Fun`, `GQ2.ContCoh.cup11ZH`, `GQ2.ContCoh.dOne`, `GQ2.ContCoh.dTwo`, `GQ2.ContCoh.dZero`, `GQ2.ContCoh.instAddCommGroupH1`, `GQ2.ContCoh.instAddCommGroupH2`, `GQ2.IsDiagonalization`, `GQ2.Kummer.GaloisGroup`, `GQ2.Kummer.instDistribMulActionGaloisGroupZModOfNatNat`, `GQ2.Kummer.kummerCocycleFun`, `GQ2.bS`, `GQ2.corFun`, `GQ2.corH1`, `GQ2.diagForm`, `GQ2.evensAux`, `GQ2.evensNormFun`, `GQ2.evensNormH2`, `GQ2.kummerClassK`, `GQ2.quadExt`, `GQ2.sqrtCl`, `GQ2.swOne`, `GQ2.swTwo`, `GQ2.traceFormOne`, `GQ2.traceFormTwisted`, `GQ2.trivialCupPairing`

*Checked statements referenced (4):* `GQ2.ContCoh.cup11_mem_Z2`, `GQ2.Kummer.instContinuousSMulGaloisGroupZModOfNatNat`, `GQ2.corFun_mem_Z1`, `GQ2.evensNormFun_mem_Z2`

### B10 — `GQ2.tameQuotient` ([GQ2/Foundations/Axioms.lean:325](../GQ2/Foundations/Axioms.lean#L325))

*Read (39):* `GQ2.AbsGalQ2`, `GQ2.AbsGalQ2ab`, `GQ2.FreeProfiniteGroup`, `GQ2.FreeProfiniteGroup.homEquiv`, `GQ2.FreeProfiniteGroup.of`, `GQ2.IsProP`, `GQ2.LocalReciprocity`, `GQ2.OrientedTameQuotient`, `GQ2.TameQuotientData`, `GQ2.Ttame`, `GQ2.Zhat`, `GQ2.Zhat.ofInt`, `GQ2.Ztwo`, `GQ2.chiCyc`, `GQ2.chiCycAb`, `GQ2.commClosure`, `GQ2.conjP`, `GQ2.grpCatHomEquiv`, `GQ2.localReciprocity`, `GQ2.maxProPMk`, `GQ2.maxProPQuotient`, `GQ2.normSubgroup`, `GQ2.nuT`, `GQ2.presentationLift`, `GQ2.proPKernel`, `GQ2.profinitePresentation`, `GQ2.profiniteQuotient`, `GQ2.quotientLift`, `GQ2.quotientMk`, `GQ2.relatorSubgroup`, `GQ2.restrictAb`, `GQ2.restrictHom`, `GQ2.tameToZhat`, `GQ2.tameWord`, `GQ2.toAb`, `GQ2.uniformizer`, `GQ2.unitEmbed`, `GQ2.v2`, `GQ2.ztwoOne`

*Checked statements referenced (4):* `GQ2.instNormalCarrierToTopTotallyDisconnectedSpaceToProfiniteFreeProfiniteGroupRelatorSubgroup`, `GQ2.instTotallyDisconnectedSpace_quotient`, `GQ2.proPKernel_isClosed`, `GQ2.proPKernel_normal`

### B11a — `GQ2.hilbertSymbol_normCriterion_finiteDyadic` ([GQ2/Foundations/Axioms.lean:368](../GQ2/Foundations/Axioms.lean#L368))

*Read (24):* `GQ2.ContCoh.B1`, `GQ2.ContCoh.B2`, `GQ2.ContCoh.C1`, `GQ2.ContCoh.C2`, `GQ2.ContCoh.H1`, `GQ2.ContCoh.H1mk`, `GQ2.ContCoh.H2`, `GQ2.ContCoh.H2mk`, `GQ2.ContCoh.Z1`, `GQ2.ContCoh.Z2`, `GQ2.ContCoh.cup11`, `GQ2.ContCoh.cup11Fun`, `GQ2.ContCoh.cup11ZH`, `GQ2.ContCoh.dOne`, `GQ2.ContCoh.dTwo`, `GQ2.ContCoh.dZero`, `GQ2.ContCoh.instAddCommGroupH1`, `GQ2.ContCoh.instAddCommGroupH2`, `GQ2.Kummer.GaloisGroup`, `GQ2.Kummer.instDistribMulActionGaloisGroupZModOfNatNat`, `GQ2.Kummer.kummerCocycleFun`, `GQ2.kummerClassK`, `GQ2.sqrtCl`, `GQ2.trivialCupPairing`

*Checked statements referenced (2):* `GQ2.ContCoh.cup11_mem_Z2`, `GQ2.Kummer.instContinuousSMulGaloisGroupZModOfNatNat`

