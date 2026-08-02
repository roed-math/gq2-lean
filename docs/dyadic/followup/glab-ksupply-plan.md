# From a ramified-`i` field to `KSupply`: G-Lab follow-up plan

Date: 2026-08-02
Scope: theorem-level route for an arbitrary finite `K/ℚ₂` with `K(i)/K` ramified.
Trust rule: no new axioms and no `sorry`. Literature may enter only through the existing
eleven-axiom boundary, or through explicitly named hypothesis `def`s while a proof is under
construction.

## 1. Executive result

The end of the route already exists.  The theorem

```lean
theorem candidate_equiv_galK_of_supply {R : PWord (Generator n)}
    (W : WordCertificate n (qOf K FF) R P hP nuP SN)
    (KS : KSupply T n P hP nuP SN)
    (params : FieldParameters) (params_n : params.n = n)
    (params_qK : params.qK = qOf K FF)
    (ramified : ∀ δi : ℚ̄₂, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi)
    (ramifiedData : …)
    (hnuP : Function.Surjective nuP) :
    Nonempty (ContinuousMulEquiv
      ((candidateGroup n (qOf K FF) R : Type)) (GalK K))
```

is already proved in `GQ2/Dyadic/Instances/KSupply.lean`. It is uniform in `K`, the
degree `n`, the word `R`, and the standard pro-2 core `P`. Therefore the shortest
conditional all-`K` theorem reachable before G-Lab is discharged is **this theorem itself**.
A branch-explicit theorem before G-Lab would merely bundle its `WordCertificate` and
`KSupply` arguments.

The missing work divides cleanly into three independent producers:

1. **G-Lab / marked core:** construct the four pro-2 fields of `KSupply` from an
   identification of `G_K(2)` with `D_M`, `D_N`, or `D_sq`.
2. **Arithmetic semantics:** construct `exactLifting`, `stokes`, and `determinant`.
3. **Candidate semantics:** construct the corresponding analytic fields of the branch's
   `WordCertificate`.

This document plans the first producer and records its dependencies on the other two. G-Lab is
not the only remaining obstacle to an unconditional presentation theorem.

## 2. A correction to the present G-Lab interface

The quadratic pilot uses an abelianization slot

```lean
piAb  : ((maxProPQuotient 2 (GalK K)) : Type) →* GalKab K
hpiAb : Continuous piAb
hpiNu : ∀ g, B.nu_ur (piAb (maxProPMk 2 (GalK K) g))
  = B.nu_ur (toAbK K g)
```

in `sqrtNegTwoKSupply`. This is stronger than necessary and is not canonical: the full
abelianization need not itself be pro-2, so `toAbK` does not factor through `G_K(2)`.
What does factor canonically is each character whose target is pro-2.

The common replacement is:

```lean
noncomputable def chiCycKTwo (K) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K)) ℤ_[2]ˣ :=
  (maxProPHomEquiv isProP_two_unitsPadicInt).symm
    ⟨chiCycK K, continuous_chiCycK K⟩

@[simp] theorem chiCycKTwo_maxProPMk (g : GalK K) :
    chiCycKTwo K (maxProPMk 2 (GalK K) g) = chiCycK K g

noncomputable def nuUrKTwo (B : MarkedRecip R K) :
    ContinuousMonoidHom (maxProPQuotient 2 (GalK K))
      (Multiplicative ℤ_[2]) :=
  (maxProPHomEquiv PropOneOne.isProP_two_multPadicInt).symm
    ⟨fun g ↦ B.nu_ur (toAbK K g), …⟩

@[simp] theorem nuUrKTwo_maxProPMk (g : GalK K) :
    nuUrKTwo B (maxProPMk 2 (GalK K) g) = B.nu_ur (toAbK K g)
```

This seam is shared by all five branches. It removes `piAb`, `hpiAb`, and `hpiNu`
from the eventual theorem surfaces and lets every marked-core certificate be stated directly on
`G_K(2)`.

The corresponding proposed K-facing abbreviations are:

```lean
abbrev MarkedCoreCertificateKTwoM (B : MarkedRecip R K) (α h : ℕ) (hα : 1 ≤ α) :=
  MarkedCoreCertificateM α h hα (chiCycKTwo K).toMonoidHom
    (nuUrKTwo B).toMonoidHom

abbrev MarkedCoreCertificateKTwoN (B : MarkedRecip R K) (α h : ℕ) :=
  MarkedCoreCertificateN α h (chiCycKTwo K).toMonoidHom
    (nuUrKTwo B).toMonoidHom

abbrev MarkedCoreCertificateKTwoSq (B : MarkedRecip R K) (h : ℕ) :=
  MarkedCoreCertificateSq h (chiCycKTwo K).toMonoidHom
    (nuUrKTwo B).toMonoidHom
```

## 3. What the repository already proves

### 3.1 Generic assembly

- `KSupply.toSourceN` turns a `KSupply` into the arithmetic `SourceDataN`.
- `candidate_equiv_galK_of_supply` is the final arbitrary-degree comparison theorem.
- `qOf_hyps` discharges `2 ≤ q_K` and `Even q_K`.
- `boundary_jointly_surjective_of_maxProP` supplies joint boundary surjectivity once
  `pro2` is known to be the maximal pro-2 map.

### 3.2 Field-side cohomology, but on `G_K`

`GQ2/Dyadic/FieldData.lean` proves:

```lean
FieldData.card_H1_zmodTwo K :
  Nat.card (H1 (GalK K) (ZMod 2)) = 2 ^ ([K : ℚ₂] + 2)

FieldData.demushkinRank_galK K :
  demushkinRank 2 (GalK K) = [K : ℚ₂] + 2

FieldData.nondegFp2_cupFormK K :
  NondegFp2 (FieldData.cupFormK K)
```

It also has the one-dimensional `H²` consequence of local Tate duality. These are the
right arithmetic facts, but they are stated on `G_K`, not on its maximal pro-2 quotient.

### 3.3 Standard cores and marked matching

- `DM α h` and `DN α h` are presented pro-2 groups with rank `4 + 2h`,
  `q = 2`, canonical characters `chiM`/`chiN`, and standard markings
  `nuM`/`nuN`.
- `DSq h` is the square-commutator core of rank `3 + 2h`, with `chiSq` and
  `nuSq`. At `h = 0` it is `DR`.
- `MarkedCoreCertificateM`, `MarkedCoreCertificateN`, and
  `MarkedCoreCertificateSq` store exactly the abstract isomorphism, orientation equality,
  and marking-correcting automorphism needed downstream.
- `marked_matching_certificate_M` and `marked_matching_certificate_N` construct the
  first two certificates from an abstract isomorphism and branch-specific marked data.
- `marked_matching_certificate_sq` and its strengthened one-binder variant do the same for
  `DSq`.
- `MLabHypothesis` and `NLabHypothesis` are explicit `def`-valued classification
  hypotheses, never axioms.

### 3.4 The rank-three Labute precedent

`GQ2/Roe/Labute/` proves `bLab : BLabHypothesis` without axioms or sorries. Its route is:

1. construct compatible maps at every finite two-central level;
2. assemble continuous epimorphisms in both directions;
3. use profinite Hopficity to obtain an isomorphism.

This is an excellent implementation precedent, but not a drop-in proof for arbitrary `K`.
The `bLab` levelwise sets compare two explicitly presented groups, `DR` and `D0`.
For `G_K(2)` there is not yet a generator/relator presentation from which analogous finite
level sets can be defined. The efficient route is therefore to formalize the general Labute
classification theorem and prove that `G_K(2)` has its antecedents, rather than clone the
rank-three relation-specific tower separately for every field.

## 4. The first genuine G-Lab blocker: move duality to `G_K(2)`

There is currently no theorem relating continuous `H¹` or `H²` of `G_K` with
trivial 2-primary coefficients to that of `G_K(2)`. Consequently the repository has no
theorem of any of the following forms:

```lean
H1 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H1 (GalK K) (ZMod 2)

H2 (maxProPQuotient 2 (GalK K)) (ZMod 2) ≃+ H2 (GalK K) (ZMod 2)

IsDemushkin 2 (maxProPQuotient 2 (GalK K))
```

The first two equivalences must respect cup products. This is not optional plumbing:
`MLabHypothesis` and `NLabHypothesis` require `IsDemushkin`, rank, and `q`
on the actual group supplied to them, namely `G_K(2)`.

Proposed API:

```lean
noncomputable def H1MaxProTwoEquiv
    (G : Type*) […] :
    H1 (maxProPQuotient 2 G) (ZMod 2) ≃+ H1 G (ZMod 2)

noncomputable def H2MaxProTwoEquiv
    (G : Type*) […] :
    H2 (maxProPQuotient 2 G) (ZMod 2) ≃+ H2 G (ZMod 2)

theorem H2MaxProTwoEquiv_cup11 (x y : H1 (maxProPQuotient 2 G) (ZMod 2)) :
    H2MaxProTwoEquiv G (x ⌣ y)
      = H1MaxProTwoEquiv G x ⌣ H1MaxProTwoEquiv G y

theorem isDemushkin_maxProTwo_galK :
    IsDemushkin 2 (maxProPQuotient 2 (GalK K))

theorem demushkinRank_maxProTwo_galK :
    demushkinRank 2 (maxProPQuotient 2 (GalK K))
      = Module.finrank ℚ_[2] K + 2
```

Implementation should first search for a general inflation theorem for maximal pro-`p`
quotients in Mathlib. If absent, prove the degree-1 statement from the universal property of
`maxProPQuotient` and prove degree 2/cup compatibility through extensions or cocycle
inflation. The degree-2 surjectivity is the hard part and deserves its own design review.

The `q = 2` fact is separate. It should be obtained from the 2-primary torsion in local
reciprocity/abelianization, not inferred merely from `H¹` and `H²`:

```lean
theorem demushkinQ_maxProTwo_galK
    (hram : ∀ δi, δi ^ 2 = -1 → ¬ HasEqualNormValueGroups K δi) :
    demushkinQ (maxProPQuotient 2 (GalK K)) = 2
```

The precise hypothesis may be weaker or different; it must be established from local
reciprocity before freezing this signature.

## 5. Abstract classification and branch selection

### 5.1 The even families

Once the preceding invariants exist, the current hypothesis interfaces yield the following
small theorems.

```lean
theorem abstractEquiv_KM (α h : ℕ) (hα : 2 ≤ α)
    (mIsCanonical : …)
    (hLab : MLabHypothesis α h mIsCanonical)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hcanonical : mIsCanonical _ (chiCycKTwo K).toMonoidHom)
    (hrange : MonoidHom.range (chiCycKTwo K).toMonoidHom = imChiM α) :
    Nonempty (ContinuousMulEquiv
      ((DM α h) : Type) ((maxProPQuotient 2 (GalK K)) : Type))

theorem abstractEquiv_KN (α h : ℕ) (hα : 2 ≤ α)
    (hLab : NLabHypothesis α h)
    (hD : IsDemushkin 2 (maxProPQuotient 2 (GalK K)))
    (hrank : demushkinRank 2 (maxProPQuotient 2 (GalK K)) = coreRank h)
    (hq : demushkinQ (maxProPQuotient 2 (GalK K)) = 2)
    (hrange : MonoidHom.range (chiCycKTwo K).toMonoidHom = imChiN α) :
    Nonempty (ContinuousMulEquiv
      ((DN α h) : Type) ((maxProPQuotient 2 (GalK K)) : Type))
```

The real G-Lab deliverable is to replace the `hLab` binders by proved general
classification theorems. A direct formalization of Labute's even-rank `q = 2` theorem is
preferable to one relation-specific levelwise campaign per value of `α` and `h`. If the
general classification proof stalls, the fallback is a family-parametric version of the
`GQ2/Roe/Labute/` two-epi architecture, not a list of field-specific proofs.

### 5.2 The `L` family

There is no general `SqLabHypothesis` analogous to `MLabHypothesis` and
`NLabHypothesis`. `BLabHypothesis` is specialized to the rank-three Roe core and does
not classify `G_K(2)` for odd degree `> 1`. Introduce a temporary `def`, never an
axiom, with the same abstract-group posture:

```lean
def SqLabHypothesis (h : ℕ)
    (sqIsCanonical : ∀ (G : Type) […], (G →* ℤ_[2]ˣ) → Prop) : Prop :=
  ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)],
    IsDemushkin 2 G →
    demushkinRank 2 G = 3 + 2 * h →
    demushkinQ G = 2 →
    (∃ χ : G →* ℤ_[2]ˣ, Continuous χ ∧ sqIsCanonical G χ ∧
      MonoidHom.range χ = MonoidHom.range (chiSq h).toMonoidHom) →
    Nonempty (ContinuousMulEquiv G (DSq h : Type))
```

This signature is provisional because the correct image invariant for the odd family should be
checked against Labute's theorem before it is merged. At `h = 0` the theorem must reduce to
the existing `bLab`/`DSq 0 = DR` seam.

### 5.3 Selecting `L`, `Mα`, or `Nα`

`MarkedRecip` derives the level `r`, the quotient `λ`, and the parameters
`ε` and `η` **after** a type-`M` or type-`N` splitting and its parameter
`α` have been supplied. It does not currently prove that the cyclotomic image is
`imChiM α` or `imChiN α` for some `α`, nor that odd degree selects type
`L`.

The needed theorem is a classification of closed subgroups of `ℤ₂ˣ` in the image of a
dyadic cyclotomic character, paired with degree parity:

```lean
inductive LabuteBranchWitness (K) (B : MarkedRecip R K) : Type
  | L (hn : Odd (Module.finrank ℚ_[2] K))
      (hrange : MonoidHom.range (chiCycKTwo K).toMonoidHom
        = MonoidHom.range (chiSq (([K : ℚ₂] - 1) / 2)).toMonoidHom)
  | M (α : ℕ) (hα : 2 ≤ α) (hn : Even ([K : ℚ₂]))
      (hrange : MonoidHom.range (chiCycKTwo K).toMonoidHom = imChiM α)
  | N (α : ℕ) (hα : 2 ≤ α) (hn : Even ([K : ℚ₂]))
      (hrange : MonoidHom.range (chiCycKTwo K).toMonoidHom = imChiN α)

theorem labuteBranchWitness (K) (B : MarkedRecip R K) :
    Nonempty (LabuteBranchWitness K B)
```

The final signature should avoid the displayed arithmetic expressions by using
`FieldParameters` and `Compatible.handleCount`. The point of the sketch is the missing
mathematics: this is not presently a consequence of `Branches.lean`.

Once the Labute family and `α` are known, the existing marked splitting machinery plus
the ramified-`i` hypothesis excludes the even-`η` row and selects one of
`L/N0/Npc/M0/Mpc`.

## 6. Marking correction, branch by branch

All branches use the same abstract sequence:

```text
standard core --fLab--> G_K(2)
      | correction u
      v
standard core --E = u.trans fLab--> G_K(2)
      | E⁻¹ ∘ maxProPMk
      v
     G_K ---------------------------> standard core.
```

For a certificate `C`, define `E := C.correction.trans C.abstractEquiv` and

```lean
pro2K := E.symm.toContinuousMonoidHom.comp (maxProPMk 2 (GalK K))
```

Then:

- surjectivity follows from surjectivity of `maxProPMk` and bijectivity of `E`;
- the kernel is `proPKernel 2 (GalK K)` by injectivity of `E.symm`;
- `nu_compat` follows from `C.correction_nu` and
  `nuUrKTwo_maxProPMk`.

This proof is currently duplicated in `sqrtNegTwoKSupply`. After the direct-character seam
lands, factor it into a core-agnostic helper whose only input is an equivalence `E` and a
pointwise marking equality.

### `N0`, compact `N`

- Core: `DN α h`.
- Abstract classification: `NLabHypothesis`/general Labute theorem.
- Current correction residue: `NScalingHypothesis α h`.
- Marked datum: the `(σ̄,x̄₂)` pair is unimodular.
- Word/core dictionary and certificates exist generically for compact `N`.
- This is the best first end-to-end G-Lab test because the quadratic pilot already contains the
  complete `KSupply` pro-2 construction.

### `Npc`, procyclic `N`

- Same abstract core and Labute theorem as `N0`; only the marking/word dictionary changes.
- The branch carries `r ≥ 1` and a lift `η` of `λ(v)`.
- The marked-core correction should still be expressed through `nuUrKTwo B` and the
  `N` certificate, but the repository lacks the `CoreReindex` dictionary and the final
  `WordCertificate` constructor for `Npc`.
- Its module-specific Stokes endpoint cannot be replaced by the compact diagonal criterion.
  This is outside G-Lab but blocks the unconditional branch theorem.

### `M0`, compact `M`

- Core: `DM α h`.
- Abstract classification: `MLabHypothesis`/general Labute theorem with the canonical
  orientation predicate and image `imChiM α`.
- Current correction residue: `MMixHypothesis α h hα`.
- Marked datum: compact-row χ-kernel unimodularity. At rank four the
  `CompactCoV.marked_matching_certificate_M_of_chiKer` interface converts this to the
  pivot-unit fact; a general-h version is still needed.
- The compact `M` word/core dictionary is already general in `h`.

### `Mpc`, procyclic `M`

- Same abstract core and Labute theorem as `M0`.
- Marked data include `r ≥ 1`, `ε`, and `η`.
- The present dictionary is only implemented at `h = 0` and `η = 1`. General
  `h` and the exponent `η̂` must be added before an arbitrary-`K` theorem.
- The generic `HessRelZTarget`/`hlinrow` argument is also still branch-specific work.

### `L`

- Core: `DSq h` with `[K:ℚ₂] = 2h+1`.
- General abstract classification is missing; only the `h = 0` Roe/`bLab` seam is
  complete.
- Marked correction currently uses `SqHandleMixHypothesis` plus
  `SqCoreShearHypothesis`. The preferred target is the stronger
  `SqHandleMixFixesCore`, after which `marked_matching_certificate_sq_of_fixesCore`
  needs only the standard `σ` and `x₀` marked values.
- The canonical pivot exponent is already proved in `SqCore/PivotLemma.lean`.
- The word/certificate stack is general in `h`, but the final general odd-degree assembly
  and the `qDouble` determinant endpoint remain outside G-Lab.

## 7. Proposed generic `KSupply` constructor

After the direct descents and core certificates exist, the common pro-2 construction should be
factored before writing four more branch copies. One possible interface is:

```lean
structure MarkedCoreRealization
    (P : ProfiniteGrp) (nuP : ContinuousMonoidHom P Ztwo) where
  equiv : ContinuousMulEquiv (P : Type)
    ((maxProPQuotient 2 (GalK K)) : Type)
  nu_equiv : ∀ x, ztwoIota (nuP x) = nuUrKTwo B (equiv x)

noncomputable def KSupply.ofMarkedCoreRealization
    (hdeg : Module.finrank ℚ_[2] K = n)
    (hhom : SN.homScalar = 2 ^ (n + 2))
    (MC : MarkedCoreRealization (K := K) (B := B) P nuP)
    (exactLifting : ExactLiftingSemantics …)
    (stokes : StokesDualityCertificate …)
    (determinant : AffineDeterminantCertificate …) :
    KSupply T n P hP nuP SN
```

The constructor proves `pro2`, `hpro2`, `ker_pro2`, and `nu_compat`
once. Each branch only has to turn its `MarkedCoreCertificate*` into a
`MarkedCoreRealization`.

## 8. Dependency DAG

```text
existing B5-K MarkedRecip                 existing B6/B7 FieldData on G_K
           |                                           |
           v                                           v
 direct character descents to G_K(2)       H¹/H² inflation to G_K(2)
           |                                           |
           |                                 IsDemushkin/rank/q on G_K(2)
           |                                           |
           +----------------------+--------------------+
                                  |
                    cyclotomic image / Labute-type selector
                                  |
              +-------------------+------------------+
              |                   |                  |
          L/DSq class.         M/DM class.       N/DN class.
              |                   |                  |
          Sq correction       M correction       N correction
              +-------------------+------------------+
                                  |
                       MarkedCoreRealization
                                  |
                KSupply.ofMarkedCoreRealization
                                  |
               +------------------+------------------+
               |                                     |
      arithmetic analytic clauses             branch WordCertificate
               |                                     |
               +------------------+------------------+
                                  |
                  candidate_equiv_galK_of_supply
```

The branch selector also depends on the ramified-`i` exclusion in
`MarkedRecipBundle/Branches`. `Npc` and general `Mpc` have independent
word-certificate tails after G-Lab closes.

## 9. Where the existing literature axioms enter

- **B1:** topological finite generation of `G_K`, used by the arithmetic source and some
  cohomological counting arguments.
- **B5-K / `markedRecipAt`:** supplies `MarkedRecip`, hence `ν_ur`, the marked level,
  `λ`, and the ramified-`i` bridge. It does **not** supply the Labute family or a
  presentation of `G_K(2)`.
- **B6 / `tateDualityAt`:** supplies local duality on `G_K`. It does not directly state
  duality or the Demushkin property on `G_K(2)`.
- **B7:** via Shapiro/Euler, supplies `#H¹(G_K,𝔽₂)` and the degree formula.
- **B8:** is the advertised route for the `NScalingHypothesis` conjugator/scaling step;
  that wiring still has to be implemented.
- **B10-K / `orientedTameQuotientAt`:** supplies the tame boundary used by `KSupply`,
  but not the G-Lab isomorphism.
- **B11a/B13 and related existing inputs:** support ramified arithmetic, residue degree, and the
  determinant/counting lanes; they do not classify `G_K(2)`.

Labute 1967 is cited by the comments on `MLabHypothesis` and `NLabHypothesis`, but no
general Labute classification theorem is currently an axiom or a theorem. Under this plan it
must be formalized. Turning the final classification statement into a new literature axiom is
explicitly outside scope.

## 10. Reviewable PR decomposition

Each PR must be sorry-free, introduce no axiom, and pass the targeted build plus
`scripts/check_dyadic.sh`.

1. **GL0 — direct marked-character descents.** Add `chiCycKTwo`,
   `nuUrKTwo`, and their `maxProPMk` lemmas. No consumer changes.
2. **GL1 — refactor marked-core K interfaces.** Add direct-`G_K(2)` variants of
   `marked_matching_certificate_KM/KN/KSq`. Keep the old `piAb` wrappers for
   compatibility until consumers migrate.
3. **GL2 — generic pro-2 composite.** Add `MarkedCoreRealization` and prove once the
   surjectivity, kernel, and marking compatibility of `E⁻¹ ∘ maxProPMk`. Refactor
   `sqrtNegTwoKSupply` as a regression.
4. **GL3 — `H¹` inflation.** Prove the degree-1 equivalence for trivial 2-primary
   coefficients and its naturality.
5. **GL4 — `H²` inflation and cup compatibility.** Design-review the cochain/extension
   proof before implementation. This is the first high-risk mathematical PR.
6. **GL5 — Demushkin package on `G_K(2)`.** Combine GL3/GL4 with `FieldData` to prove
   `IsDemushkin` and rank. Prove `q = 2` as a separate local-reciprocity theorem.
7. **GL6 — cyclotomic image classification.** Classify the image as odd `L` or even
   `Mα/Nα`, with `α ≥ 2` and exact image equalities. Produce `BranchData`
   using the existing `λ/ε/η` API and ramified-`i` exclusion.
8. **GL7M / GL7N — general Labute classification.** Formalize the even-rank classification
   theorem, first in the exact `MLabHypothesis`/`NLabHypothesis` interfaces, then
   eliminate the binders. Split M and N only after the common theorem is in place.
9. **GL7L — odd-rank classification.** Introduce, review, and discharge the `Sq`
   classification interface; verify `h=0` agrees with `bLab`.
10. **GL8N / GL8M / GL8L — marking corrections.** Discharge `NScalingHypothesis`,
    `MMixHypothesis`, and the preferred `SqHandleMixFixesCore` interface. These PRs
    can proceed in parallel after GL1.
11. **GL9 — branch-to-`KSupply` constructors.** Produce `KSupply` for each family from
    the generic realization constructor. Keep analytic clauses as explicit arguments.
12. **GL10 — conditional branch assembly.** State the arbitrary-`K` theorem selecting
    `BranchData` and applying `candidate_equiv_galK_of_supply`. At this point any
    remaining arguments should be exactly candidate/arithmetic analytic certificates, not
    G-Lab data.

The existing Roe/Labute campaign's repository estimates describe a relation-specific rank-four
clone as a several-thousand-line tail per core. GL7 should not begin as two blind clones: freeze
the abstract classification signature and shared finite-level machinery first.

## 11. Acceptance tests

### GL0

- The two descended maps compile for arbitrary finite `K` and arbitrary supplied
  `MarkedRecip R K`.
- Their evaluation on `maxProPMk` is a simp theorem.
- `#print axioms` reports only the standard three logical axioms for the bundle-parametric
  declarations.

### GL1–GL2

- New direct-character K-certificate constructors have no `piAb` argument.
- The old `sqrtNegTwoKSupply` theorem remains source-compatible or has a documented wrapper.
- The generic composite proves `hpro2` and `ker_pro2`, rather than accepting them.
- A stress theorem instantiates it once at `DN 2 0`, once at `DM 2 0`, and once at
  `DSq 0`.

### GL3–GL5

- Both cohomology equivalences round-trip and commute with inflation on cocycle
  representatives.
- Cup compatibility is stated and tested before `IsDemushkin` is assembled.
- The rank theorem reduces definitionally or by a short rewrite to
  `FieldData.card_H1_zmodTwo`.
- `IsDemushkin.isProP` is supplied by `isProP_maxProPQuotient`, not assumed.
- The `q = 2` theorem has a separate proof and an explicit literature audit.

### GL6–GL7

- Image equalities are equalities of closed subgroup ranges, not only abstract group
  isomorphisms or mod-2 shadows.
- Both `M` and `N` occur in non-vacuity tests; `α=1` is rejected.
- Odd degree produces the `L` family and even degree produces only `M/N`.
- The ramified-`i` theorem removes exactly the even-`η` row.
- The resulting theorems inhabit the existing `MLabHypothesis` and
  `NLabHypothesis` types verbatim; the `Sq` theorem reduces to `bLab` at `h=0`.

### GL8–GL10

- The final G-Lab output contains full `ℤ₂` marking, not only mod-2 values.
- Compact and procyclic rows use the same abstract core isomorphism but distinct marking data.
- No final theorem carries `fLab`, `piAb`, `horient`,
  `NScalingHypothesis`, `MMixHypothesis`, or an `Sq*` hypothesis.
- Before analytic lanes close, the only remaining arguments are named
  `ExactLiftingSemantics`, `StokesDualityCertificate`,
  `AffineDeterminantCertificate`, and the branch `WordCertificate` residues.
- After those lanes close, the headline is an existentially selected corrected word
  `R_K` together with `Nonempty (ContinuousMulEquiv (candidateGroup … R_K) (GalK K))`.

Mechanical checks for every PR:

```sh
lake env lean GQ2/Dyadic/<edited-file>.lean
bash scripts/check_dyadic.sh
rg -n '\b(sorry|axiom)\b' GQ2/Dyadic/<edited-files>
```

## 12. First milestone worth shipping

The first mathematically meaningful milestone is not a new presentation theorem. It is:

> For every finite `K/ℚ₂`, the marked cyclotomic and unramified characters descend
> canonically to `G_K(2)`; for every supplied marked-core certificate, those descents produce
> the pro-2 block of `KSupply` without an abelianization-section hypothesis.

This removes three artificial binders from the pilot, fixes the right common interface for all
five branches, and exposes the true remaining G-Lab mathematics: cohomological invariance under
the maximal pro-2 quotient, Labute classification, and the marked automorphism corrections.
