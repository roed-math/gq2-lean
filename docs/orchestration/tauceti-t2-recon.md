# Tau Ceti discharge campaign: T2 recon memo

Ticket T2 of [`tauceti-tickets.md`](tauceti-tickets.md), against plan
[`tauceti-proof-plan.md`](tauceti-proof-plan.md) §3. Written 2026-10-16 at Tau Ceti `706344c35`,
Mathlib `cfc55fc58`, Lean `v4.35.0`, on branch `tauceti` after T1.

**Smoke file.** [`GQ2/TauCeti/Smoke.lean`](../../GQ2/TauCeti/Smoke.lean) imports 112 modules (99 Tau
Ceti, 13 gq2, none reaching `GQ2.Foundations.Axioms`/`AxiomInstance`) and `#check`s 567
declarations by full name, one `section` per lane below, plus the `example`s that pin every
definitional-equality answer recorded here. It is not imported by the library. Build it with the
Tau Ceti cache variables set, so Lake unpacks Tau Ceti instead of compiling it:

```bash
export LAKE_CONFIG=$PWD/.lake/tauceti-lake-cache.toml LAKE_CACHE_DIR=$PWD/.lake/cache
lake build GQ2.TauCeti.Smoke
```

(`.lake/tauceti-lake-cache.toml` is the `tauceti-public` service declaration of plan §2; `lake cache
get` against it needs `--repo=TauCetiProject/TauCeti`.)

**Scratch evidence.** The recon ran one agent per lane group; each probed in scratch `module` files.
The files cited below as `artifacts/<lane>/…` are kept outside the repository, on mimir at
`/scratch/claudeM/tauceti-t2-artifacts/<lane>/`. Every one of them elaborates with `lake env lean`,
contains no `sorry`, and every `#print axioms` in them is within `propext, Classical.choice,
Quot.sound` (re-checked when this memo was assembled). They are prototypes, not tickets: the
adapter tickets still own their files and must re-do the work under the board protocol.

| lane | scratch status | prototype |
|---|---|---|
| A1 | `↥k.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥k` and its composites built | `galois/a1_b11a_prototype.lean` |
| A2 | H¹/H² dictionary (propositional route), restriction naturality, `cup11` and the `trivialF2` cup proved; Kummer identification **not** attempted | `cohom/evidence/` |
| P1 | kernel, `maxProPQuotient`, `Delta`, `zpowZtwo = padicPow`, pro-p presentation equivalence, `D0`, `Zhat ≃ₜ* zHat` built | `prop/proto_p1.lean`, `prop/proto_zhat.lean` |
| B1 | one line, in `Smoke.lean` | — |
| B3c | **complete term** | `orient/adapter_sketch.lean` |
| B5 | **complete term** (all ten fields) | `recip/draft_b5_b10.lean` |
| B6 | group reconstruction (Q4) and the bijectivity packaging (Q3) built; `μₙ` seam and cup naturality open | `tate/b6check.lean` |
| B7 | **complete** modulo A2's H¹/H² equivalences | `cohom/evidence/b7_proof.lean` |
| B8 | **complete term** | `prop/proto_b8.lean` |
| B9 | both Tau Ceti identities instantiated at `K = ↥k`, `L = ↥(quadExt k δ)`; field shapes, trace forms and cochains matched; needs A1's ring iso and A2 | `sw/test*.lean`, `Smoke.lean` |
| B10 | **complete term** | `recip/draft_b5_b10.lean` |
| B11a | Tau Ceti half proved over `↥k.fixingSubgroup`; needs A2's H¹/H²/cup | `galois/a1_b11a_prototype.lean` |

## Answers to the six T2 questions

1. **Is `GQ2.FreeProfiniteGroup X` definitionally `TauCeti.freeProfiniteGroup X`?** Yes, as
   `ProfiniteGrp.{u}` objects and as carriers, in a `module` file (`rfl`, pinned in `Smoke.lean`); no
   universe or `ULift` gap. Not reducibly (gq2's is a plain `def`, Tau Ceti's an `abbrev`), and the
   generators are **not** `rfl`-equal from a `module` file because `TauCeti.freeProfiniteGroup.of`
   is not exposed; `rw [← fromFreeGroup_of, coe_fromFreeGroup]; rfl` proves it. Details under P1.
2. **Do the two `proPKernel` definitions agree?** The bodies are textually identical, so they are
   definitionally equal, but `rfl` fails from a `module` file (`TauCeti.proPKernel` is not exposed).
   The adapter proof is three lines through `TauCeti.mem_proPKernel_iff` and `Subgroup.mem_iInf`.
   `IsProP` likewise: `TauCeti.isProP_iff.symm`, not `Iff.rfl`.
3. **Does `Perfect.lean` state bijectivity?** In substance yes: `tateDualityPairing_perfect_mixed`
   gives zero left kernel **and** "every `φ : Hʲ(A) →+ ZMod n` is `⟨x, ·⟩`", i.e. injectivity and
   surjectivity of `Hⁱ(A') → Hom(Hʲ(A), ℤ/n)`, gq2's direction. Packaging as `Function.Bijective`
   is three lines (`tate/b6check.lean`, `bijective_of_perfect`); no counting argument is needed.
4. **Open finite-index subgroup of `Field.absoluteGaloisGroup K` → `K'.fixingSubgroup`?** Mathlib's
   Krull correspondence: `InfiniteGalois.fixingSubgroup_fixedField` (with `Subgroup.isClosed_of_isOpen`)
   and `InfiniteGalois.isOpen_iff_finite` (finiteness of `K'`); `IntermediateField.finrank_eq_fixingSubgroup_index`
   gives the degree. Tau Ceti's analogues are stated on the separable-closure model
   `TauCeti.AbsoluteGaloisGroup K` and do not apply to `AbsGalQ2`. The full reconstruction from
   `IsLocalDualizingGroup` to `G ≃ₜ* Field.absoluteGaloisGroup K'` is built (`tate/b6check.lean`).
5. **Which theorems give `standardD0Orientation` on `d0A/d0S/d0Y`?** `TauCeti.standardD0Orientation_d0A`
   (`= -1`), `_d0S` (`= 1`), `_d0Y` (`= TauCeti.negThreeUnit⁻¹`, with `negThreeUnit_coe : ↑negThreeUnit = -3`),
   in `Demushkin/Orientation.lean:96/101/106`, **not** `D0/Invariants.lean`. They match gq2's
   `(-1, 1, (-3)⁻¹)`. The two `d0Relator`s are the same word (`x⁻¹y⁻¹xy` commutator, generators
   `of 0/1/2`, `Fin 3`, universe 0, no `ULift`); no inverse needs inserting.
6. **Which `ZHat` declaration is the ℤ₂-component, and its section?** `TauCeti.zHat.component 2 :
   Additive zHat →+* ℤ_[2]`, in `ZHat/Component.lean:70` (not `Decomposition.lean`, which bundles all
   components as `zHat.ringEquivPiPadicInt`). There is no named section: use
   `ringEquivPiPadicInt.symm (Pi.single ⟨2, _⟩ v)`, whose value at `v = 1` is `zHat.idem 2`.
   `component 2 (ofMul (zHat.ofInt z)) = z` by `zHat.ofMul_ofInt` and `map_intCast`.

## Cross-cutting findings (read before any adapter ticket)

1. **Tau Ceti definitions are not exposed.** Tau Ceti files are `public section` without
   `@[expose]`, so from a `module` adapter `rfl`/`Iff.rfl`/`unfold`/`simp [def]` cannot see through
   them ("definition is not exposed"). This defeats every "by unfolding"/"word for word" bridge in
   plan §3 except `H0` and the `abbrev`s (`freeProfiniteGroup`, `freeProP`, `presentedProfiniteGroup`,
   `presentedProP`, `maximalProPQuotient`, `absoluteGaloisGroupProP`, `tameQuotient`, `GalRep`).
   Go through Tau Ceti's stated `_iff`/`_apply`/`mem_`/`_mk`/`_def` lemmas. The same `rfl`s do hold
   in a non-`module` file and after `import all TauCeti.…` (Lake v4.35.0 does not check cross-package
   `import all`), but that couples gq2 to Tau Ceti internals and every downstream file needs it too;
   the recon recommends against it.
2. **Instance-search timeouts under heavy Tau Ceti imports.**
   - With `TauCeti.NumberTheory.LocalField.ClassModule` in the import closure (the B1, B5, B6, B7
     source modules all have it), `Module.IsTorsionFree ℚ_[2] (AlgebraicClosure ℚ_[2])` never finishes,
     hence `IsAlgClosure`, `Normal`, `IsGalois`, `Algebra.IsSeparable` for `ℚ̄₂/ℚ₂` and compactness of
     its Galois group time out (the search wanders through `TauCeti.FinitePadicExtension.toModuleFinite`).
     Fix (tested in the B6 lane): file-level `local instance : Module.IsTorsionFree ℚ_[2] ℚ̄₂ :=
     DivisionSemiring.to_moduleIsTorsionFree`, `local instance : IsAlgClosure ℚ_[2] ℚ̄₂ :=
     AlgebraicClosure.instIsAlgClosure ℚ_[2]`, `local instance : IsGalois ℚ_[2] ℚ̄₂ :=
     IsAlgClosure.isGalois _ _` (raising the priority of the existing instance does **not** help).
     Recommended structure: `GaloisDict.lean` stays on light imports and exports these facts as named
     theorems; heavy adapters `haveI` them.
   - Under the Euler-characteristic imports, `Nontrivial ℚ_[2]` and `StrongRankCondition ℚ_[2]` loop
     through `TauCeti.IsAdicComplete.henselianLocalRing`; use
     `attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in` (B7).
   - `Algebra.IsSeparable ℚ_[2] ↥L` for a finite layer times out: supply `IsGalois.to_isSeparable` (B5).
   - Not found at all (supply them): `CompactSpace`/`LocallyCompactSpace ↥k.fixingSubgroup` (from
     `IntermediateField.fixingSubgroup_isClosed`), `Invertible (2 : ↥k)` unless
     `Mathlib.Algebra.CharP.Invertible` is imported (its `invertibleTwo`; otherwise
     `invertibleOfNonzero two_ne_zero`),
     `CharP 𝓀[ℚ_[2]] 2` (`TauCeti.charP_residueField ℚ_[2] 2`), and `ContinuousSMul G (trivialF2 G).V`
     (local instance after `attribute [local instance] TopRep.distribMulAction`).
     `LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)` needs `synthInstance.maxHeartbeats` raised.
3. **Two topologies on a finite `↥k`.** gq2's imports give `ℚ̄₂` Mathlib's `PadicAlgCl` topology, so
   `↥k` has a global subspace topology; Tau Ceti's `finiteIntermediateFieldTopology` is equal but not
   definitionally. Install Tau Ceti's local-field package on `↥k` with `let`/`have` inside proofs, never
   as global instances; apply Tau Ceti theorems at `↥k` with explicit `@` arguments where needed.
   No gq2 field mentions a topology on `↥k`.
4. **Separable closure vs algebraic closure.** Tau Ceti's cohomology is stated on
   `TauCeti.AbsoluteGaloisGroup K = Gal(SeparableClosure K/K)`; gq2's finite-level statements use
   `↥k.fixingSubgroup ≤ Gal(ℚ̄₂/ℚ₂)` acting on `ℚ̄₂`. A1 must therefore export not just
   `Φ : ↥k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup ↥k` but a ring iso/embedding `e` between
   `SeparableClosure ↥k` and `ℚ̄₂` with `Φ g = e⁻¹ ∘ g ∘ e` (e.g. via
   `absoluteGaloisGroupEquivFixingSubgroup` and `separableClosureRingEquiv`). The A2 Kummer
   identification, the B9 `σ`/root, and the B6 `μₙ(ℚ̄₂) ↔ μₙ(Kˢᵉᵖ)` transport all rest on it; this is
   the main open seam of the campaign.
5. **Import hygiene for adapters.**
   - `module` adapters cannot import non-`module` gq2 files: `GQ2/DyadicNielsen.lean`
     (`SectionThree.topGen_d0`) and `GQ2/AnabelianBridge/Construction.lean` (`zpowHat_omega2_eq_self`)
     are needed by B3c and B8; the prototypes re-prove the lemmas locally (15 and 25 lines).
   - Adapters must **not** import `GQ2.Prop32` (or anything reaching `GQ2.Foundations.Interfaces`):
     C2 makes `Interfaces` import the adapters, which would close an import cycle. The B3c sketch
     currently imports `GQ2.Prop32` for `topGen_map`/`monoidHom_eq_of_topGen`; the B3c ticket must
     replace that import (copy the lemmas or move them to a lighter module).
   - B5's `recip` must stay definitionally visible to B10 (keep gq2's `@[expose] public section` in
     `B5.lean`, or export `localReciprocity_tauceti_recip : … = artinMap ℚ_[2] := rfl`).
6. **`AbsGalQ2` vs `Kummer.GaloisGroup ℚ_[2]`** are definitionally equal with equal instances, but not
   reducibly; elements of `↥k.fixingSubgroup` must be cast through `(g : Kummer.GaloisGroup ℚ_[2])`,
   and `rw` with Tau Ceti lemmas stated on `Field.absoluteGaloisGroup` can miss on `AbsGalQ2`-typed
   terms (apply as terms with `.trans`, as in the T1 transparency fixes).
7. **Spelling mismatches between definitionally equal types** (`GQ2.FreeProfiniteGroup` vs
   `TauCeti.freeProfiniteGroup`, gq2 `ProfiniteGrp` objects vs Tau Ceti `Type`s with instances): state
   each dictionary on Tau Ceti spellings and transport each gq2 element once through an `abbrev`.

## Corrections to the plan and board

- **Dependencies.** B5 needs none of A1, A2, P1. B10 needs only B5 (not P1). B3c is self-contained
  (it builds its own `D0` and Galois-group equivalences; P1 is optional). B9 does not need B11a
  (use the diagonal-presentation theorems). B1 needs no dictionary. B8 needs P1's `maxProPEquiv`,
  `Zhat ≃ₜ* zHat` and `zpowZtwo = padicPow`. B6, B7, B9, B11a need A2; B6, B9, B11a need A1.
- **B5.** Use `localCyclotomicCharacter_artinMap_padic` (not `_unit`); `ν_ur = (zHat.lift (ofAdd 1) ∘
  unramifiedCoordinate)⁻¹` needs no P1; `norm_reciprocity` goes through `artinMap_restrict`,
  `surjective_localArtinMap`, `localArtinMap_eq_zero_iff` (not `localArtinEquiv`/`ClassFormation.ker_artinMap`).
- **B10.** `nuT ∘ equiv = zHat.lift ztwoOne⁻¹ ∘ iwasawaCoordinateGeometric` (the geometric generator
  has coordinate `gen⁻¹`); both orientation clauses follow from one lemma for an arbitrary lift, and
  `tameQuotientGeometricEquiv_toTameQuotient_frobenius` is the wrong tool (it covers only the chosen σ).
- **B3c.** The orientation values are in `Demushkin/Orientation.lean`; the relators agree.
- **B7.** The call is `eulerCharacteristic_mixed 2 ℚ_[2] (Nat.card M) hn A hA` (`F` explicit, `Finite A.V`
  explicit); `IsSmoothDiscrete` comes from `ofDiscreteModule_isSmoothDiscrete`. Only `M : Type` is
  reachable, so C2's `M : Type*` restatement needs an extra transport.
- **B8.** Build `ι u := e.symm (ofMul (e ω₂) · sec u)` rather than "trivial odd part" (the latter needs
  the odd components of gq2's `omega2` to vanish, which gq2 does not prove). The theorem is
  `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two` (namespace `Peripheral`).
- **B9.** Use `sw1_eq_add_galoisCor_of_equivalent_traceTransfer` / `sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer`;
  the degree-2 summands differ only by `add_right_comm`; `galoisF2Iso_inv_kummerClass` is the key bridge.
- **P1.** Tau Ceti has no `maximalProPQuotient p (presentedProfiniteGroup X R) ≃ₜ* presentedProP p X R'`
  (only the surjection `toPresentedProP`); P1 must prove it (~60 lines, prototyped). `GQ2.Zhat` is not
  `zHat.{0}` (Tau Ceti completes a `ULift`).
- **A1.** Tau Ceti's `localCyclotomicCharacter` is over `AlgebraicClosure K`, not the separable closure:
  `chiCyc = localCyclotomicCharacter 2 ℚ_[2]` by `MonoidHom.ext` + `localCyclotomicCharacter_apply`.
  `absoluteGaloisGroupExtend` is at `FiniteExtension.lean:247`. The A1 and B6 lanes built the same
  `range_absoluteGaloisGroupExtend` lemma for a finite intermediate field independently (the Shapiro
  proof, generalized); it belongs in A1.
- **A2.** "AddEquiv by unfolding" fails in a `module` file except for `H0`; use the propositional route
  (`mem_*_iff` + `QuotientAddGroup.congr`). B6 needs cup compatibility for an arbitrary pairing `μ`,
  not only `trivialF2`. State the maps in Tau Ceti's `(eqToHom _).hom` form (wrapping as
  `eqToIso … .toAddEquiv` makes `rfl`/`erw` time out).
- **Paths.** Tau Ceti's local class field theory is under `NumberTheory/ClassFieldTheory/`, not
  `ClassFieldTheory/`; several line numbers in plan §3 are off by a few lines (corrected in the
  sections below).

## A1: Galois-group dictionary

Scratch evidence (lane `galois`, all elaborate with `lake env lean`, no `sorry`): `GQ2/TauCeti/Smoke.lean`
(64 `#check`s, 11 pinned examples; output in the `#check` output of `Smoke.lean`), `artifacts/galois/a1_b11a_prototype.lean` (the A1
equivalences and the Tau Ceti half of B11a; `#print axioms` = standard three).
Tau Ceti paths below are relative to `.lake/packages/TauCeti/TauCeti/`.

### gq2 side
- `GQ2.AbsGalQ2 : Type := Field.absoluteGaloisGroup ℚ_[2]` (`noncomputable abbrev`, `GQ2/Statement.lean:40`).
- `GQ2.Kummer.GaloisGroup K := AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K` (`abbrev`, `GQ2/Kummer.lean:68`);
  trivial action on `ZMod 2` as a global instance (`GQ2/Kummer.lean:75`, `smul _ m := m`).
- For `k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])`, gq2's `G_k` is
  `↥k.fixingSubgroup : Subgroup (Kummer.GaloisGroup ℚ_[2])` with the subspace Krull topology
  (used by the B9/B11a fields, `GQ2/Foundations/LiteratureInputs.lean:70-105`).
- `GQ2.chiCyc : AbsGalQ2 →* ℤ_[2]ˣ := (cyclotomicCharacter (AlgebraicClosure ℚ_[2]) 2).comp
  (MulSemiringAction.toRingAut (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]) (AlgebraicClosure ℚ_[2]))`
  (`GQ2/Reciprocity.lean:128`); `GQ2.chiCycAb` (`:144`) its `QuotientGroup.lift` to `AbsGalQ2ab`
  (`= Field.absoluteGaloisGroupAbelianization ℚ_[2]`, `:110`).

### Tau Ceti sources
- `TauCeti.absoluteGaloisGroupRestrictEquiv` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Basic` (`FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:325`)
  ```lean
  TauCeti.absoluteGaloisGroupRestrictEquiv : (K : Type u_1) →
    [inst : Field K] → Field.absoluteGaloisGroup K ≃ₜ* TauCeti.AbsoluteGaloisGroup K
  ```
  (`AbsoluteGaloisGroup K := Gal(SeparableClosure K/K)`, `:312`.) Value lemma
  `coe_absoluteGaloisGroupRestrictEquiv_apply` (`:339`): `↑((… K) σ x) = σ ↑x`. Tested at `ℚ_[2]`, `↥k`.
- `TauCeti.galoisSubgroup` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.FiniteExtension` (`…/FiniteExtension.lean:138`)
  ```lean
  TauCeti.galoisSubgroup : (K : Type u_1) → [inst : Field K] → (L : Type u_2) → [inst_1 : Field L] →
    [inst_2 : Algebra K L] → (L →ₐ[K] SeparableClosure K) → [FiniteDimensional K L] → OpenSubgroup (TauCeti.AbsoluteGaloisGroup K)
  ```
  Body not exposed: use `galoisSubgroup_toSubgroup` (`:146`, `= σ.fieldRange.fixingSubgroup`) and
  `mem_galoisSubgroup_iff` (`:153`). `galoisSubgroupEquiv` (`:212`): `AbsoluteGaloisGroup L ≃ₜ* ↥↑(galoisSubgroup K L σ)`.
- `TauCeti.absoluteGaloisGroupExtend` — same module (`…/FiniteExtension.lean:247`; plan said `:201`)
  ```lean
  TauCeti.absoluteGaloisGroupExtend : (K : Type u_1) → [inst : Field K] → (L : Type u_2) → [inst_1 : Field L] →
    [inst_2 : Algebra K L] → (L →ₐ[K] SeparableClosure K) → [FiniteDimensional K L] → Field.absoluteGaloisGroup L →* Field.absoluteGaloisGroup K
  ```
  with `mem_range_absoluteGaloisGroupExtend_iff` (`:290`), `absoluteGaloisGroupExtendEquiv` (`:325`):
  `{U : Subgroup (Field.absoluteGaloisGroup K)} → (absoluteGaloisGroupExtend K L σ).range = U → Field.absoluteGaloisGroup L ≃ₜ* ↥U`,
  `coe_absoluteGaloisGroupExtendEquiv_apply` (`:337`), `absoluteGaloisGroupRestrictSubgroupEquiv` (`:363`):
  `… → (absoluteGaloisGroupExtend K L σ).range = U → ↥U ≃ₜ* ↥σ.fieldRange.fixingSubgroup`. Tested at `K = ℚ_[2]`, `L = ↥k`.
- Pattern to copy: `TauCeti.ClassFieldTheory.shapiroFieldEmbedding` (`NumberTheory/ClassFieldTheory/Local/EulerCharacteristic/Shapiro.lean:144`,
  `IntermediateField.inclusion` into `separableClosure`) and `range_absoluteGaloisGroupExtend_shapiroFieldEmbedding` (`:160`).
- `TauCeti.finiteIntermediateFieldValuativeRel` / `finiteIntermediateFieldTopology` — `TauCeti.NumberTheory.LocalField.FiniteExtension.IntermediateField` (`NumberTheory/LocalField/FiniteExtension/IntermediateField.lean:69, :75`)
  ```lean
  TauCeti.finiteIntermediateFieldValuativeRel : (K : Type u_1) → [inst : Field K] → [inst_1 : ValuativeRel K] →
    [inst_2 : TopologicalSpace K] → [IsNonarchimedeanLocalField K] → (Ω : Type u_2) → [inst_4 : Field Ω] →
    [inst_5 : Algebra K Ω] → (M : IntermediateField K Ω) → [Module.Finite K ↥M] → ValuativeRel ↥M
  ```
  (`…Topology` identical with `TopologicalSpace ↥M`); `finiteIntermediateField_isNonarchimedeanLocalField` (`:97`),
  `finiteIntermediateField_valuativeExtension` (`:81`) give `IsNonarchimedeanLocalField ↥M`, `ValuativeExtension K ↥M`
  (both stated with `@`/`letI` on the two named structures).
- `TauCeti.FinitePadicExtension` (class, `NumberTheory/LocalField/AbsoluteRamificationIndex.lean:64`; bundles its own
  `algebra` field) and `FinitePadicExtension.ofInstances` (`:83`, an instance from `[Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K]`).
- `TauCeti.localCyclotomicCharacter` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Character` (`…/Cyclotomic/Character.lean:33`)
  ```lean
  TauCeti.localCyclotomicCharacter : (p : ℕ) →
    [inst : Fact (Nat.Prime p)] → (K : Type u_1) → [inst_1 : Field K] → Field.absoluteGaloisGroup K →* ℤ_[p]ˣ
  ```
  `localCyclotomicCharacter_apply` (`:41`): `= (cyclotomicCharacter (AlgebraicClosure K) p) σ.toRingEquiv`;
  `continuousLocalCyclotomicCharacter` (`:54`), `abelianizedLocalCyclotomicCharacter` (`:66`, on
  `Field.absoluteGaloisGroupAbelianization K`) with `_mk` (`:73`). `Fact (Nat.Prime 2)` = `Nat.fact_prime_two` (synthesized).

Instances at `K = ℚ_[2]` (tested, `#synth`): `ValuativeRel ℚ_[2]` = `Padic.instValuativeRel` (Mathlib
`NumberTheory/Padics/ValuativeRel.lean:34`), `IsNonarchimedeanLocalField ℚ_[2]` = `instIsNonarchimedeanLocalFieldPadic`
(Mathlib `NumberTheory/Padics/LocalField.lean:25`), `Module.Finite ℚ_[2] ℚ_[2]` = `FiniteDimensional.finiteDimensional_self`,
`ValuativeExtension ℚ_[2] ℚ_[2]` = `TauCeti.valuativeExtension_self` (`RingTheory/Valuation/ValuativeRel/Basic.lean:69`),
`FinitePadicExtension ℚ_[2] 2` = `ofInstances`, and `FinitePadicExtension.toAlgebra ℚ_[2] 2 = Algebra.id ℚ_[2]` by `rfl`.

Instances at finite `↥k` (tested): none of `ValuativeRel ↥k`, `IsNonarchimedeanLocalField ↥k` exists globally. But
`↥k` already has a global `TopologicalSpace` (`instTopologicalSpaceSubtype`, from `(PadicAlgCl.valued 2).toTopologicalSpace`
on `AlgebraicClosure ℚ_[2]`: Mathlib's `PadicAlgCl p` is an `abbrev`, imported via `Mathlib.NumberTheory.Padics.Complex`
by `GQ2.Reciprocity`) and a global `NormedField ↥k` (`SubfieldClass.toNormedField k`). With
`let _ := finiteIntermediateFieldValuativeRel ℚ_[2] (AlgebraicClosure ℚ_[2]) k`, `let _ := finiteIntermediateFieldTopology …`,
`have := finiteIntermediateField_isNonarchimedeanLocalField …`, `have := finiteIntermediateField_valuativeExtension …`
(gq2's `[FiniteDimensional ℚ_[2] k]` serves as `Module.Finite`), instance search then finds
`FinitePadicExtension k 2` (`ofInstances`), its `toAlgebra` is the intermediate-field algebra by `rfl`, the local
topology beats the global subtype topology (`(inferInstance : TopologicalSpace k) = finiteIntermediateFieldTopology … := rfl`
succeeds), and `isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 k` applies.

### Translation
- Base: no transport. `example : GQ2.Kummer.GaloisGroup ℚ_[2] = GQ2.AbsGalQ2 := rfl` and the `Group`/`TopologicalSpace`
  instances agree by `rfl` (smoke). But `Field.absoluteGaloisGroup` is a plain `def … deriving Group, TopologicalSpace,
  IsTopologicalGroup`, so it is not reducible: `g : ↥k.fixingSubgroup` is not coerced to `Field.absoluteGaloisGroup ℚ_[2]`
  automatically (error observed); write `(g : GQ2.Kummer.GaloisGroup ℚ_[2])` and pass that. A subgroup of
  `Kummer.GaloisGroup ℚ_[2]` is accepted where `Subgroup (Field.absoluteGaloisGroup ℚ_[2])` is expected (tested).
- `G_k`: proved in `artifacts/galois/a1_b11a_prototype.lean`, all sorry-free:
  `kEmb k : ↥k →ₐ[ℚ_[2]] SeparableClosure ℚ_[2] := IntermediateField.inclusion (… Algebra.IsSeparable.isSeparable …)`;
  `range_extend_kEmb : (absoluteGaloisGroupExtend ℚ_[2] k (kEmb k)).range = k.fixingSubgroup` (the Shapiro proof verbatim);
  `galEquivFixing k : Field.absoluteGaloisGroup k ≃ₜ* ↥(k.fixingSubgroup : Subgroup (GQ2.Kummer.GaloisGroup ℚ_[2]))`
  (`absoluteGaloisGroupExtendEquiv`); `fixingEquivTC k : k.fixingSubgroup ≃ₜ* TauCeti.AbsoluteGaloisGroup k`
  (composite with `absoluteGaloisGroupRestrictEquiv k`); and, the one B11a actually needs,
  `rho k : k.fixingSubgroup ≃ₜ* ↥(galoisSubgroup ℚ_[2] k (kEmb k)).toSubgroup`, `g ↦ restrictEquiv ℚ_[2] g`,
  built by hand (the library's `absoluteGaloisGroupRestrictSubgroupEquiv` lands in `↥σ.fieldRange.fixingSubgroup`,
  which is not definitionally `↥(galoisSubgroup …).toSubgroup` from a `module` file).
- Instance package: provide it as `let`/`letI` (or `attribute [local instance]`) per proof, as Tau Ceti does
  (`EulerCharacteristic/Theorem.lean:59-64`). Do not make `finiteIntermediateFieldTopology` a global instance on `↥k`:
  it would sit beside the global subtype topology (propositionally equal, not defeq). No gq2 field mentions a topology
  on `↥k`, so this diamond never reaches a statement.
- `chiCyc`: same formula, but `rfl` fails from a `module` file (`localCyclotomicCharacter` not exposed). Use
  `MonoidHom.ext fun σ => (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] σ).symm` (smoke), and for `chiCycAb`,
  `QuotientGroup.induction_on` + `abelianizedLocalCyclotomicCharacter_mk` (smoke). `rfl` does succeed from a plain-import
  (non-`module`) file. Correction to the board: Tau Ceti's character is on `Field.absoluteGaloisGroup K` over
  `AlgebraicClosure K`, not "through the separable closure".
- Compactness: `CompactSpace ↥k.fixingSubgroup` is not found by instance search; prove it from
  `IntermediateField.fixingSubgroup_isClosed k` (prototype). It supplies the `[LocallyCompactSpace G]` that
  `explicitH2AddEquivContinuousCohomology` needs. `LocallyCompactSpace (TauCeti.AbsoluteGaloisGroup ↥k)` times out at
  the default `synthInstance.maxHeartbeats` (at `R1Space`); 200000 suffices (smoke).
- **Hardest seam: instance-search blow-up from heavy imports.** In any file whose imports contain
  `TauCeti.NumberTheory.LocalField.ClassModule`, including the B1 (`Generation.AbsoluteGaloisGroup`), B5
  (`Local.ArtinMap`), B6 (`Local.Duality.Perfect`) and B7 (`Local.EulerCharacteristic.Theorem`) modules, synthesizing
  `Module.IsTorsionFree ℚ_[2] (AlgebraicClosure ℚ_[2])` never finishes (still running after 10 min at 2M heartbeats).
  The search goes through `Module.Flat`/`FaithfullyFlat` → `HenselianLocalRing`/`IsAdicComplete` →
  `TauCeti.FinitePadicExtension.toModuleFinite`/`toValuativeExtension`. That class is an instance argument of
  `IsAlgClosure`, so `IsAlgClosure`/`Normal`/`IsGalois ℚ_[2] ℚ̄₂` and `CompactSpace Gal(ℚ̄₂/ℚ₂)` all time out there,
  and even *stating* `IsAlgClosure ℚ_[2] (AlgebraicClosure ℚ_[2])` fails. Raising the local priority of
  `DivisionSemiring.to_moduleIsTorsionFree` did not help. Not affected (tested): `Tame.Geometric`, `ProP.RatPadic`,
  `StiefelWhitney.QuadraticExtension`, `Tame.Layer`, `Generation.Quotient`, `MuTwo.CupNorm`/`KummerCharacter`,
  `GaloisCohomology.Restriction`, `AbsoluteGaloisGroup.{Basic,FiniteExtension}`, `FiniteExtension.IntermediateField`,
  `EulerCharacteristic.Shapiro`, `GQ2.Foundations.LiteratureInputs`. The B11a and B1 field types do still elaborate in
  a heavy file (tested). Recommendation: `GaloisDict.lean` imports only the light modules above, and exports as named
  theorems everything that needs Galois instances at `ℚ̄₂` (`isGalois` of `ℚ̄₂/ℚ₂`, `CompactSpace ↥k.fixingSubgroup`,
  `k.fixingSubgroup = U` for open `U`, `galEquivFixing`, `rho`). Heavy adapters (B5/B6/B7) then `haveI` them and
  do not search.

### Answers
- *Can the local-field instances on `↥k` be obtained?* Yes, as `let`/`have` (tested; see above). As global
  instances: not advisable (topology diamond with the `PadicAlgCl` subspace topology). `IsNonarchimedeanLocalField ↥k`,
  `ValuativeExtension ℚ_[2] ↥k`, `FinitePadicExtension ↥k 2` and `Module.Finite ℚ_[2] ↥k` all follow (the last from
  `FiniteDimensional`), and a Tau Ceti local theorem (`isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 k`)
  applies with no further arguments.
- *`k.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥k`?* Yes: `(galEquivFixing k).symm`; no new library lemma
  needed beyond the 8-line `range_extend_kEmb`.
- *`Kummer.GaloisGroup ℚ_[2]` vs `AbsGalQ2`?* Definitionally equal (`rfl`, with equal instances), not reducibly.

## A2: cohomology, cup and Kummer dictionary

### gq2 side
Objects (all in `@[expose] public section`, so they unfold in any importing file):
- `GQ2.ContCoh.H0 G M : AddSubgroup M`, carrier `{m | ∀ g : G, g • m = m}` (`GQ2/Cohomology.lean:75`).
- `C1 = {φ : G → M | Continuous φ}` (`:84`), `C2` on `G × G` (`:91`); `dZero m = fun g => g • m - m` (`:98`),
  `dOne ψ = fun p => p.1 • ψ p.2 - ψ (p.1 * p.2) + ψ p.1` (`:104`), `dTwo` (`:111`).
- `Z1 = C1 ⊓ (dOne G M).ker` (`:120`), `Z2 = C2 ⊓ (dTwo G M).ker` (`:123`), `B1 = (dZero G M).range` (`:126`),
  `B2 = (C1 G M).map (dOne G M)` (`:129`); `H1 = Z1 ⧸ (B1).addSubgroupOf Z1` (a `def`, instance by
  `inferInstanceAs`, `:132`), `H1mk` (`:138`), `H2` (`:141`), `H2mk` (`:147`). Readable forms `mem_Z1_iff`
  (`:189`, `φ (g*h) = φ g + g • φ h`), `mem_Z2_iff` (`:199`).
- `res1 G M U := H1comap (subgroupIncl G U) (AddMonoidHom.id M) …` (`:332`), `res2` (`:336`);
  `H1comap (π : G →ₜ* Q) (f : N →+ M) (hcompat : f (π g • n) = g • f n) : H1 Q N →+ H1 G M` (`:289`).
- `cup11 μ hμ` (`GQ2/CupProduct.lean:153`, cochain `μ (a g) (g • b h)`, `:49`), `cup02` (`:259`),
  `cup20` (`:344`, cochain `μ (a p) ((p.1 * p.2) • n)`, `:271`). `trivialCupPairing p G htriv :=
  cup11 AddMonoidHom.mul _` on `H1 G (ZMod p)` for an arbitrary action assumed trivial by `htriv`
  (`GQ2/Demushkin.lean:95`), notation `a ⌣[htriv] b` (`:104`).
- `kummerClassK k a : H1 (↥k.fixingSubgroup) (ZMod 2)` = class of
  `g ↦ Kummer.kummerCocycleFun (sqrtCl ↑↑a) ↑g` (`GQ2/EvensKahn.lean:437`), where
  `kummerCocycleFun α g = if g • α = α then 0 else 1` on `Kummer.GaloisGroup K = AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K`
  (`GQ2/Kummer.lean:68, :93`) and the action on `ZMod 2` is the global trivial instance (`GQ2/Kummer.lean:75`).

### Tau Ceti sources
Low-degree complex, module `TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree`
(`…/ContCohomology/LowDegree.lean`): `C1 := continuousAddSubgroup G M` (`:137`), `C2 := C1 (G × G) M` (`:140`),
`d0` (`:177`), `B1 := (d0 G M).range` (`:184`), `d1` (`:236`), `d2` (`:243`), `abbrev H0 := FixedPoints.addSubgroup G M`
(`:344`), `Z1 := C1 G M ⊓ (d1 G M).ker` (`:507`), `Z2` (`:510`), `B2 := AddSubgroup.map (d1 G M) (C1 G M)` (`:516`),
`abbrev H1 := let _h := B1_le_Z1 G M; Z1 G M ⧸ (B1 G M).addSubgroupOf (Z1 G M)` (`:830`), `H1pi` (`:835`), `H2` (`:897`).
Same formulas as gq2 (`d*` over `DistribSMul`); the file is `public section` **without** `@[expose]`, so
`C1, C2, d0, d1, d2, Z1, Z2, B1, B2` have hidden bodies; `H0, H1, H2, H1pi, H2pi` are `abbrev`s.
  ```lean
  TauCeti.ContCohomology.H1 : (G : Type u_1) → [inst : Monoid G] → [inst_1 : TopologicalSpace G] → (M : Type u_2) → [inst_2 : AddCommGroup M] → [inst_3 : TopologicalSpace M] → [IsTopologicalAddGroup M] → [inst_5 : DistribMulAction G M] → [hcont : ContinuousSMul G M] → Type (max u_1 u_2)
  ```
  ```lean
  TauCeti.ContCohomology.H2 : (G : Type u_1) → [inst : Monoid G] → [inst_1 : TopologicalSpace G] → [hcontMul : ContinuousMul G] → (M : Type u_2) → [inst_2 : AddCommGroup M] → [inst_3 : TopologicalSpace M] → [IsTopologicalAddGroup M] → [inst_5 : DistribMulAction G M] → [hcontSmul : ContinuousSMul G M] → Type (max u_1 u_2)
  ```
Comparisons (`…/ContCohomology/CohomologyComparison.lean`, `ContinuousCohomologyIso.lean`, `RestrictScalars.lean`):
- `TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology` (`CohomologyComparison.lean:134`)
  ```lean
  TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology : (G M : Type u_1) → [inst : Group G] → [inst_1 : TopologicalSpace G] → [inst_2 : IsTopologicalGroup G] → [inst_3 : AddCommGroup M] → [inst_4 : TopologicalSpace M] → [inst_5 : DiscreteTopology M] → [inst_6 : DistribMulAction G M] → [inst_7 : ContinuousSMul G M] → TauCeti.ContCohomology.H1 G M ≃+ ↑(continuousCohomology 1 (TauCeti.ofDiscreteModule ℤ G M)).toModuleCat
  ```
- `TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology` (`:232`)
  ```lean
  TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology : (G M : Type u_1) → [inst : Group G] → [inst_1 : TopologicalSpace G] → [inst_2 : IsTopologicalGroup G] → [inst_3 : AddCommGroup M] → [inst_4 : TopologicalSpace M] → [inst_5 : DiscreteTopology M] → [inst_6 : DistribMulAction G M] → [inst_7 : ContinuousSMul G M] → [LocallyCompactSpace G] → TauCeti.ContCohomology.H2 G M ≃+ ↑(continuousCohomology 2 (TauCeti.ofDiscreteModule ℤ G M)).toModuleCat
  ```
- `TauCeti.ContCohomology.explicitH0IsoContinuousCohomology` (`ContinuousCohomologyIso.lean:165`)
  ```lean
  TauCeti.ContCohomology.explicitH0IsoContinuousCohomology : (G : Type u_1) → [inst : Group G] → [inst_1 : TopologicalSpace G] → [inst_2 : IsTopologicalGroup G] → (M : Type u_1) → [inst_3 : AddCommGroup M] → [inst_4 : TopologicalSpace M] → [inst_5 : IsTopologicalAddGroup M] → [inst_6 : DiscreteTopology M] → [inst_7 : DistribMulAction G M] → ↧↥(TauCeti.ContCohomology.H0 G M) ≅ continuousCohomology 0 (TauCeti.ofDiscreteModule ℤ G M)
  ```
- `TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete` (`CohomologyComparison.lean:475`), `…H2…OfDiscrete` (`:531`)
  ```lean
  @TopRep.explicitH1AddEquivContinuousCohomologyOfDiscrete : {G : Type u_1} → [inst : Group G] → [inst_1 : TopologicalSpace G] → [inst_2 : IsTopologicalGroup G] → {k : Type u_2} → [inst_3 : Ring k] → [inst_4 : TopologicalSpace k] → (X : TopRep k G) → [DiscreteTopology ↑X] → [inst_6 : ContinuousSMul G ↑X] → TauCeti.ContCohomology.H1 G ↑X ≃+ ↑(continuousCohomology 1 X).toModuleCat
  ```
- `TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv` (`RestrictScalars.lean:656`)
  ```lean
  @TauCeti.ContCohomology.ofDiscreteModuleRestrictScalarsIntEquiv : {k : Type u_1} → [inst : Ring k] → [inst_1 : TopologicalSpace k] → {G : Type u_2} → [inst_2 : Group G] → [inst_3 : TopologicalSpace G] → [inst_4 : IsTopologicalGroup G] → (X : TopRep k G) → [inst_5 : DiscreteTopology ↑X] → (n : ℕ) → ↑(continuousCohomology n (TauCeti.ofDiscreteModule ℤ G ↑X)).toModuleCat ≃+ ↑(continuousCohomology n X).toModuleCat
  ```
- `TauCeti.ofDiscreteModule` (`SmoothDiscrete/Basic.lean:223`, `@[expose]`); `TopRep.distribMulAction` (`:135`, not a global instance)
  ```lean
  TauCeti.ofDiscreteModule : (R : Type u_1) → [inst : Ring R] → [inst_1 : TopologicalSpace R] → (G : Type u_2) → [inst_2 : Monoid G] → (M : Type u_3) → [inst_3 : AddCommGroup M] → [inst_4 : Module R M] → [inst_5 : TopologicalSpace M] → [DiscreteTopology M] → [inst_7 : DistribMulAction G M] → [SMulCommClass G R M] → [ContinuousSMul R M] → TopRep R G
  ```
Functoriality (`…/ExplicitFunctoriality.lean`): `explicitMap1` (`:354`), `explicitMap1Equiv` (`:439`), `explicitMap2` (`:488`),
`explicitMap2Equiv` (`:546`), `explicitRes1` (`:604`), `explicitRes1_mk` (`:610`), `explicitRes2` (`:663`), `cocyclesMap1_apply` (`:252`).
  ```lean
  TauCeti.ContCohomology.explicitRes1 : (G : Type u_1) → [inst : Group G] → [inst_1 : TopologicalSpace G] → (M : Type u_2) → [inst_2 : AddCommGroup M] → [inst_3 : TopologicalSpace M] → [inst_4 : IsTopologicalAddGroup M] → [inst_5 : DistribMulAction G M] → [inst_6 : ContinuousSMul G M] → (S : Subgroup G) → TauCeti.ContCohomology.H1 G M →+ TauCeti.ContCohomology.H1 (↥S) M
  ```
  ```lean
  TauCeti.ContCohomology.explicitRes2 : (G : Type u_1) → [inst : Group G] → [inst_1 : TopologicalSpace G] → (M : Type u_2) → [inst_2 : AddCommGroup M] → [inst_3 : TopologicalSpace M] → [inst_4 : IsTopologicalAddGroup M] → [inst_5 : DistribMulAction G M] → [inst_6 : ContinuousSMul G M] → (S : Subgroup G) → [inst_7 : ContinuousMul G] → [inst_8 : ContinuousMul ↥S] → TauCeti.ContCohomology.H2 G M →+ TauCeti.ContCohomology.H2 (↥S) M
  ```
  ```lean
  TauCeti.ContCohomology.explicitMap1Equiv : (G : Type u_1) → [inst : Monoid G] → [inst_1 : TopologicalSpace G] → (M : Type u_3) → [inst_2 : AddCommGroup M] → [inst_3 : TopologicalSpace M] → [inst_4 : IsTopologicalAddGroup M] → [inst_5 : DistribMulAction G M] → [inst_6 : ContinuousSMul G M] → (H : Type u_2) → [inst_7 : Monoid H] → [inst_8 : TopologicalSpace H] → (N : Type u_4) → [inst_9 : AddCommGroup N] → [inst_10 : TopologicalSpace N] → [inst_11 : IsTopologicalAddGroup N] → [inst_12 : DistribMulAction H N] → [inst_13 : ContinuousSMul H N] → (φ : H ≃ₜ* G) → (e : M ≃+ N) → Continuous ⇑e → Continuous ⇑e.symm → (∀ (h : H) (m : M), e (φ h • m) = h • e m) → TauCeti.ContCohomology.H1 G M ≃+ TauCeti.ContCohomology.H1 H N
  ```
Cups (`Cup/Product.lean`, `Cup/Comparison.lean`, `Cup/Naturality.lean`, `Cup/Cohomology.lean`, `Cup/TrivialF2/Basic.lean`,
`TrivialF2.lean`): `explicitCup11` (`Product.lean:567`), `explicitCup02` (`:365`), `explicitCup20` (`:422`, a coefficient map;
`explicitCup20_mk` `:441` gives the `(g*h) • n` form), `explicitAddEquiv_cup11/02/20` (`Comparison.lean:319/303/337`),
`explicitMap2_explicitCup11` (`Naturality.lean:300`), `TopPairing.cup` (`Cup/Cohomology.lean:169`), `trivialF2` (`TrivialF2.lean:92`,
carrier `ULift.{u} (ZMod 2)`, body hidden), `trivialF2Equiv` (`:99`), `ofDiscreteModule_trivialF2` (`:146`),
`trivialF2TopPairing` (`Cup/TrivialF2/Basic.lean:66`), `trivialF2TopPairing_cup_one_one_explicitH1` (`:256`).
  ```lean
  @TauCeti.TopPairing.cup : {R : Type u_1} → [inst : CommRing R] → [inst_1 : TopologicalSpace R] → {G : Type u_2} → [inst_2 : Group G] → [inst_3 : TopologicalSpace G] → [inst_4 : IsTopologicalGroup G] → {X Y Z : TopRep R G} → TauCeti.TopPairing X Y Z → (m n : ℕ) → ↑(continuousCohomology m X).toModuleCat →ₗ[R] ↑(continuousCohomology n Y).toModuleCat →ₗ[R] ↑(continuousCohomology (m + n) Z).toModuleCat
  ```
  ```lean
  TauCeti.trivialF2TopPairing : (G : Type u_1) → [inst : Monoid G] → TauCeti.TopPairing (TauCeti.trivialF2 G) (TauCeti.trivialF2 G) (TauCeti.trivialF2 G)
  ```
  ```lean
  TauCeti.trivialF2TopPairing_cup_one_one_explicitH1 : ∀ (G : Type u_1) [inst : Group G] [inst_1 : TopologicalSpace G] [inst_2 : IsTopologicalGroup G] [inst_3 : LocallyCompactSpace G] (x y : TauCeti.ContCohomology.H1 G ↑(TauCeti.trivialF2 G)), (((TauCeti.trivialF2TopPairing G).cup 1 1) ((TopModuleCat.Hom.hom (CategoryTheory.eqToHom ⋯)) ((TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G ↑(TauCeti.trivialF2 G)) x))) ((TopModuleCat.Hom.hom (CategoryTheory.eqToHom ⋯)) ((TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology G ↑(TauCeti.trivialF2 G)) y)) = (TopModuleCat.Hom.hom (CategoryTheory.eqToHom ⋯)) ((TauCeti.ContCohomology.explicitH2AddEquivContinuousCohomology G ↑(TauCeti.trivialF2 G)) (((TauCeti.ContCohomology.explicitCup11 G (↑(TauCeti.trivialF2 G)) (↑(TauCeti.trivialF2 G)) (↑(TauCeti.trivialF2 G)) (TauCeti.trivialF2Pairing G) ⋯ ⋯) x) y))
  ```
Kummer (`TauCeti.FieldTheory.GaloisCohomology.MuTwo.Basic`, `…/MuTwo/Basic.lean`): `kummerClass` (`:355`),
`kummerCocycleModTwo` (`:399`), `kummerCocycleModTwo_apply` (`:434`), `kummerCocycleModTwoClass` (`:450`),
`kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq` (`:585`); `AbsoluteGaloisGroup K := Gal(SeparableClosure K/K)`
(`FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:312`).
  ```lean
  @TauCeti.kummerClass : {K : Type u_1} → [inst : Field K] → [Invertible 2] → Kˣ → ↑(continuousCohomology 1 (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K))).toModuleCat
  ```
  ```lean
  TauCeti.kummerCocycleModTwo_apply : ∀ (K : Type u_1) [inst : Field K] [inst_1 : Invertible 2] {a : Kˣ} {α : (SeparableClosure K)ˣ} (hα : α ^ 2 = (Units.map ↑(algebraMap K (SeparableClosure K))) a) (g : TauCeti.AbsoluteGaloisGroup K), (TauCeti.trivialF2Equiv (TauCeti.AbsoluteGaloisGroup K)) (↑(TauCeti.kummerCocycleModTwo K hα) g) = if g • α = α then 0 else 1
  ```
  ```lean
  TauCeti.kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq : ∀ (K : Type u_1) [inst : Field K] [inst_1 : Invertible 2] (a : Kˣ) (α : (SeparableClosure K)ˣ) (hα : α ^ 2 = (Units.map ↑(algebraMap K (SeparableClosure K))) a), TauCeti.kummerClass a = (TopModuleCat.Hom.hom (CategoryTheory.eqToHom ⋯)) ((TauCeti.ContCohomology.explicitH1AddEquivContinuousCohomology (TauCeti.AbsoluteGaloisGroup K) ↑(TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K))) (TauCeti.kummerCocycleModTwoClass K hα))
  ```
All 87 `#check`s (verbatim, unwrapped) are in `artifacts/cohom/sigs.txt`; wrapped output in the `#check` output of `Smoke.lean`.

Instances (tested): `CompactSpace (Field.absoluteGaloisGroup ℚ_[2])` = `TauCeti.instCompactSpaceAbsoluteGaloisGroup_tauCeti`,
also found for `GQ2.AbsGalQ2` and `GQ2.Kummer.GaloisGroup ℚ_[2]` (`instCompactSpaceAlgEquiv_tauCeti`); `LocallyCompactSpace`
from it; `TotallyDisconnectedSpace` found. `[Invertible (2 : ↥k)]` and `[Invertible (2 : ℚ_[2])]` synthesize.
**Not** found: `LocallyCompactSpace ↥k.fixingSubgroup`, `CompactSpace ↥k.fixingSubgroup` (adapter supplies them from
`IntermediateField.fixingSubgroup_isClosed`; needed for every degree-2 comparison over `k.fixingSubgroup`).
`ContinuousSMul G (trivialF2 G).V` is not global: `(TauCeti.isSmoothDiscrete_trivialF2 G).continuousSMul` after
`attribute [local instance] TopRep.distribMulAction` (order matters).

### Translation
- **Plan correction: "AddEquiv by unfolding" fails in a `module` adapter.** `rfl` succeeds for `H0` only; for
  `C1/C2/d0/d1/d2/Z1/Z2/B1/B2/H1/H2` Lean reports "definition is not exposed" (tested). Three working routes, all tested:
  (a) **propositional** (recommended, protocol-compliant, ~60 lines): `Z1_eq`, `B1_eq`, `Z2_eq`, `B2_eq` as `AddSubgroup`
  equalities via the two `mem_*_iff`s, then `QuotientAddGroup.congr _ _ (AddEquiv.addSubgroupCongr hZ) _`; the
  class-map rule `h1Equiv (H1mk z) = H1pi ⟨z.1, Z1_eq ▸ z.2⟩` is `rfl` (`artifacts/cohom/evidence/a2_dict_propositional.lean`);
  (b) `import all TauCeti.RepresentationTheory.Homological.ContCohomology.LowDegree` (+ `ExplicitFunctoriality`,
  `Cup.Product`) in a `module` file: Lake v4.35.0 has the cross-package `import all` check commented out
  (`~/.elan/toolchains/leanprover--lean4---v4.35.0/src/lean/lake/Lake/Build/Module.lean:431`; TauCeti sets no `allowImportAll`), and then `H1`, `H2`, `AddEquiv.refl`, `res1 = explicitRes1`,
  `res2 = explicitRes2`, `cup11 = explicitCup11` are `rfl` (`artifacts/cohom/evidence/a2_importall.lean`) — fragile, depends on Tau Ceti internals;
  (c) a non-`module` file: everything incl. instances is `rfl` (`artifacts/cohom/evidence/a2_nonmodule.lean`), but violates the board's module rule.
- `explicitH{1,2}AddEquivContinuousCohomology` land in `continuousCohomology i (ofDiscreteModule ℤ G M)` (ℤ scalars), not in
  `continuousCohomology i A` for a `GalRep`; for `A : TopRep k G` use `TopRep.explicitH{1,2}AddEquivContinuousCohomologyOfDiscrete A`
  and in degree 0 `explicitH0IsoContinuousCohomology … ≪≫ ofDiscreteModuleRestrictScalarsIntEquiv A 0`. `G` and `M` must share a
  universe; degree 2 needs `[LocallyCompactSpace G]`.
- gq2 module bundle → Tau Ceti object: `TauCeti.ofDiscreteModule ℤ G M` (what the ℤ-comparisons use; its `Module ℤ`,
  `SMulCommClass`, `ContinuousSMul ℤ` arguments synthesize) or `ofDiscreteModule (ZMod n) G M` with a chosen
  `Module (ZMod n) M` for a `GalRep` (B7). `(ofDiscreteModule R G M).V = M` and `TopRep.distribMulAction (ofDiscreteModule R G M)`
  `= ‹DistribMulAction G M›` are `rfl` (pinned in `GQ2/TauCeti/Smoke.lean`); the action on `X.V` is only visible after
  `attribute [local instance] TopRep.distribMulAction`.
- Restriction: same variance as gq2 (`explicitMap1 G M H N (φ : H →ₜ* G) (f : M →+ N)` ↔ `H1comap (π : G →ₜ* Q) (f : N →+ M)`,
  names swapped); `subgroupIncl` ↔ `ContinuousMonoidHom.subgroupSubtype`. `h1Equiv U M (res1 G M U x) = explicitRes1 G M U (h1Equiv G M x)`
  and the degree-2 analogue proved by induction + `explicitRes{1,2}_mk` + `cocyclesMap{1,2}_apply` (route (a)). `explicitRes2` needs
  `[ContinuousMul G] [ContinuousMul ↥S]`.
- Cups: the `(1,1)` cochain formulas agree verbatim (no order/sign issue): `h2Equiv (cup11 μ hμ x y) = explicitCup11 … (h1Equiv x) (h1Equiv y)`
  proved (route (a)); `cup02` agrees by `rfl` per element (route b); `cup20` needs `explicitCup20_mk` (Tau Ceti's is the coefficient
  map `μ (a q) n`). **Proved in scratch** (`artifacts/cohom/evidence/a2_cup.lean`, std-3 axioms): for `[LocallyCompactSpace G]` and trivial `htriv`,
  `cont2 (trivialCupPairing 2 G htriv x y) = (trivialF2TopPairing G).cup 1 1 (cont1 x) (cont1 y)` with
  `cont1 x := (eqToHom (congrArg (continuousCohomology 1) (ofDiscreteModule_trivialF2 G))).hom (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V (toF2 (h1Equiv G _ x)))`,
  `toF2 := explicitMap1Equiv G (ZMod 2) G (trivialF2 G).V (ContinuousMulEquiv.refl G) (trivialF2Equiv G).symm …`; proof = 
  `trivialF2TopPairing_cup_one_one_explicitH1` + `explicitMap2_explicitCup11` with `hpair` by `simp`. Seam: packaging the
  `eqToHom` step as `(eqToIso _).toContinuousLinearEquiv.toAddEquiv` makes `rfl`/`erw` against Tau Ceti's lemmas time out at 200k
  heartbeats (tested); state the dictionary maps in the `(eqToHom _).hom` form Tau Ceti uses (an `AddEquiv` wrapper with those
  `toFun`/`invFun` is fine).
- Kummer: confirmed the cocycles match pointwise (`kummerCocycleModTwo_apply`: `trivialF2Equiv (c g) = if g • α = α then 0 else 1`
  vs gq2 `kummerCocycleFun`), but on different groups/closures: gq2 over `↥k.fixingSubgroup ≤ Gal(ℚ̄₂/ℚ₂)` with `sqrtCl a ∈ ℚ̄₂`;
  Tau Ceti over `AbsoluteGaloisGroup ↥k = Gal(SeparableClosure ↥k/↥k)` with `α : (SeparableClosure ↥k)ˣ`. The A2 statement must be
  `trivialF2Map ψ 1 (kummerClass a) = cont1 (kummerClassK k a)` (or `trivialF2Iso`) for A1's `ψ`; its proof needs A1 to export a
  `↥k`-embedding `ι : SeparableClosure ↥k →ₐ[↥k] ℚ̄₂` with `ι (ψ g • x) = g • ι x` (choose `α` with `ι α = sqrtCl a`, then
  `kummerClass_eq_kummerCocycleModTwoClass_of_sq_eq` and `explicitH1AddEquivContinuousCohomology_map`/`eqToHom_comp_trivialF2Map`).
  **Hardest seam of A2**; not attempted.

### Answers
(none assigned to this lane)

## P1: pro-p, free, presentation and ℤ̂ dictionary

Scratch evidence (all in `artifacts/prop/`, each
elaborates with `lake env lean`, `#print axioms` = `propext, Classical.choice, Quot.sound`):
`GQ2/TauCeti/Smoke.lean` (117 `#check`s, output in the `#check` output of `Smoke.lean`), `artifacts/prop/proto_p1.lean` (kernel, `maxProPQuotient`, `Delta`,
`zpowZtwo = padicPow`, generic pro-p presentation equivalence, `GQ2.D0 ≃ₜ* demushkinD0`),
`artifacts/prop/proto_zhat.lean` (`Zhat ≃ₜ* zHat.{0}`, `zhatProjTwo = component 2`), `artifacts/prop/proto_absgal.lean`,
`artifacts/prop/defeq_nonmodule.lean`, `artifacts/prop/defeq_importall.lean`, `artifacts/prop/defeq_module_FAILS.lean` (the failing `rfl`s, kept on purpose).

### gq2 side
No `LiteratureInputs` field; the dictionary objects (all `@[expose]`, all `module` files):
- `GQ2.IsProP` (`GQ2/MaxProP.lean:61`): `def IsProP (p : ℕ) (P : Type*) [Group P] [TopologicalSpace P] : Prop := ∀ U : OpenNormalSubgroup P, IsPGroup p (P ⧸ U.toSubgroup)`
- `GQ2.proPKernel` (`MaxProP.lean:132`): `⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup`
- `GQ2.maxProPQuotient p G : ProfiniteGrp` (`MaxProP.lean:153`) `:= profiniteQuotient (proPKernel p G)` (`= ProfiniteGrp.of (G ⧸ N)`, `GQ2/ProfiniteQuotient.lean:83`); `GQ2.maxProPMk` (`:159`) `= quotientMk` (`ProfiniteQuotient.lean:88`); `GQ2.isProP_maxProPQuotient` (`:273`, needs `[T2Space G]`).
- `GQ2.FreeProfiniteGroup (X : Type u) : ProfiniteGrp.{u}` (`GQ2/FreeProfinite.lean:38`) `:= ProfiniteGrp.profiniteCompletion.obj (GrpCat.of (FreeGroup X))`; `.of` (`:42`) `:= etaFn _ (FreeGroup.of x)`.
- `GQ2.relatorSubgroup rels := (Subgroup.normalClosure rels).topologicalClosure` (`GQ2/ProfinitePresentation.lean:34`); `GQ2.profinitePresentation rels : ProfiniteGrp.{u}` (`:43`).
- `GQ2.Zhat : ProfiniteGrp := ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))` (`GQ2/Zhat.lean:119`); `Zhat.ofInt` (`:126`); `Zhat.funext_ofInt` (`:139`); `GQ2.omega2` (`:156`); `zpowHatHom`/`zpowHat` (`:176/:182`, `G : Type` only).
- `GQ2.zhatProjTwo : ContinuousMonoidHom Zhat (Multiplicative ℤ_[2]) := (zpowHatHom (ofAdd 1)).hom` (`GQ2/ZtwoPowering.lean:205`; its `zhatProjTwo_ofInt` is `private`); `ztwoEquivPadic` (`:303`); `zpowZtwo (hP : IsProP 2 P) (x : P) (u : ℤ_[2]) : P` (`:352`, `P : Type`, needs `[T2Space P]`); `continuous_zpowZtwo` (`:355`), `zpowZtwo_natCast` (`:378`), `zpowHat_eq_zpowZtwo` (`:459`).
- `GQ2.D0Full := profinitePresentation {d0Relator}`, `GQ2.D0 := maxProPQuotient 2 D0Full` (`GQ2/DyadicPresentation.lean:56,62`); `GQ2.d0Relator = of 0 ^ 2 * of 1 ^ 4 * commP (of 1) (of 2)` (`:46`), `commP x y = x⁻¹ * y⁻¹ * x * y` (`GQ2/Words.lean:59`).

### Tau Ceti sources
All under `TauCeti/Topology/Algebra/Group/` unless noted; full verbatim `#check` output for every name is in the `#check` output of `Smoke.lean`.
- `TauCeti.IsProP` — `TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic` (`Profinite/ProP/Basic.lean:68`), body word-for-word gq2's, **not exposed**
  ```lean
  TauCeti.IsProP : ℕ → (G : Type u_1) → [Group G] → [TopologicalSpace G] → Prop
  @TauCeti.isProP_iff : ∀ {p : ℕ} {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G],
    TauCeti.IsProP p G ↔ ∀ (U : OpenNormalSubgroup G), IsPGroup p (G ⧸ ↑U.toOpenSubgroup)
  ```
- `TauCeti.proPKernel` — `…Profinite.MaximalProP` (`Profinite/MaximalProP.lean:97`), body identical to gq2's, **not exposed**; `TauCeti.mem_proPKernel_iff` (`:132`)
  ```lean
  @TauCeti.mem_proPKernel_iff : ∀ {p : ℕ} {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G] {x : G},
    x ∈ TauCeti.proPKernel p G ↔ ∀ (U : OpenNormalSubgroup G), IsPGroup p (G ⧸ ↑U.toOpenSubgroup) → x ∈ ↑U.toOpenSubgroup
  ```
- `TauCeti.maximalProPQuotient` (`MaximalProP.lean:105`, `abbrev … : Type u := G ⧸ proPKernel p G`, a **Type**, not a `ProfiniteGrp`); `.mk` (`:108`, `abbrev := QuotientGroup.mk'`), `.mk_surjective` (`:118`), `.lift` (`:353`), `.lift_mk` (`:359`), `.continuous_lift` (`:371`), `isProP_maximalProPQuotient` (`:318`, `[SeparatelyContinuousMul G] [CompactSpace G]`)
  ```lean
  TauCeti.maximalProPQuotient : ℕ → (G : Type u_1) → [Group G] → [TopologicalSpace G] → Type u_1
  ```
- `ContinuousMulEquiv.quotientCongr` — `TauCeti.Topology.Algebra.Group.ClosedSubgroup` (`ClosedSubgroup.lean:153`, not exposed; `_mk` at `:166`). MaximalProP imports this module privately: the adapter must `public import` it.
  ```lean
  … (e : G ≃ₜ* H) → (N : Subgroup G) → (M : Subgroup H) → [inst_4 : N.Normal] → [inst_5 : M.Normal] →
    Subgroup.map e.toMonoidHom N = M → G ⧸ N ≃ₜ* H ⧸ M
  ```
- `TauCeti.freeProfiniteGroup` — `…Profinite.Free.Basic` (`Profinite/Free/Basic.lean:60`, exposed `abbrev := ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (FreeGroup X))`); `.of` (`:74`, not exposed), `.fromFreeGroup_of` (`:79`), `.coe_fromFreeGroup` (`:83`), `.hom_ext` (`:108`), `.lift` (`:124`)
  ```lean
  TauCeti.freeProfiniteGroup : Type u_1 → ProfiniteGrp.{u_1}
  TauCeti.freeProfiniteGroup.coe_fromFreeGroup : ∀ (X : Type u_1),
    ⇑(TauCeti.freeProfiniteGroup.fromFreeGroup X) = ProfiniteGrp.ProfiniteCompletion.etaFn ↧(FreeGroup X)
  ```
- `TauCeti.freeProP` — `…Profinite.Free.ProP` (`Profinite/Free/ProP.lean:72`, exposed `abbrev := maximalProPQuotient p (freeProfiniteGroup X)`); `.fromFreeProfiniteGroup` (`:85`), `_apply` (`:92`), `.of` (`:98`), `fromFreeProfiniteGroup_of` (`:104`), `_surjective` (`:109`), `isProP_freeProP` (`:76`)
  ```lean
  TauCeti.freeProP : ℕ → Type u_1 → Type u_1
  ```
- `TauCeti.presentedProfiniteGroup` / `TauCeti.presentedProP` — `…Profinite.Presentation.Basic` (`Presentation/Basic.lean:99`, `:490`; both exposed `abbrev`s, quotient by `(Subgroup.normalClosure rels).topologicalClosure`); `.mk` (`:106/:496`), `.mk_apply`, `.mk_surjective`, `.mk_relator` (`:139`), `.lift`/`.lift_mk`, `presentedProP.isProP` (`:526`), `.congrOfClosureEq` (`:798`), `presentedProfiniteGroup.toPresentedProP` (`:914`, only a surjection)
  ```lean
  TauCeti.presentedProfiniteGroup : (X : Type u_1) → Set ↑(TauCeti.freeProfiniteGroup X).toProfinite.toTop → Type u_1
  TauCeti.presentedProP : (p : ℕ) → (X : Type u_1) → Set (TauCeti.freeProP p X) → Type u_1
  ```
- `TauCeti.absoluteGaloisGroupProP` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP` (`:28`, `abbrev := maximalProPQuotient p (Field.absoluteGaloisGroup K)`).
- `TauCeti.zHat` — `…Profinite.ZHat.Basic` (`Profinite/ZHat/Basic.lean:66`, `abbrev := completion (GrpCat.of (ULift.{u} (Multiplicative ℤ)))`); `zHat.ofInt` (`:75`, a `Multiplicative ℤ →*`), `gen` (`:89`), `ofInt_ofAdd` (`:94`), `hom_ext` (`:125`), `lift` (`:140`, target any universe), `lift_gen` (`:154`)
  ```lean
  TauCeti.zHat : ProfiniteGrp.{u_1}
  TauCeti.zHat.ofInt : Multiplicative ℤ →* ↑TauCeti.zHat.toProfinite.toTop
  TauCeti.zHat.ofInt_ofAdd : ∀ (n : ℤ), TauCeti.zHat.ofInt (Multiplicative.ofAdd n) = TauCeti.zHat.gen ^ n
  ```
- `TauCeti.zHat.component` — `…ZHat.Component` (`Profinite/ZHat/Component.lean:70`); `component_apply` (`:99`), `continuous_component` (`:121`); ring structure `zHat.instCommRing` and `zHat.ofMul_ofInt` in `…ZHat.Ring` (`Ring.lean:69,131`)
  ```lean
  TauCeti.zHat.component : (ℓ : ℕ) → [inst : Fact (Nat.Prime ℓ)] → Additive ↑TauCeti.zHat.toProfinite.toTop →+* ℤ_[ℓ]
  TauCeti.zHat.component_apply : ∀ (ℓ : ℕ) [inst : Fact (Nat.Prime ℓ)] (a : Additive ↑TauCeti.zHat.toProfinite.toTop),
    (TauCeti.zHat.component ℓ) a = Multiplicative.toAdd ((TauCeti.zHat.lift (Multiplicative.ofAdd 1)) (Additive.toMul a))
  TauCeti.zHat.ofMul_ofInt : ∀ (z : Multiplicative ℤ), Additive.ofMul (TauCeti.zHat.ofInt z) = ↑(Multiplicative.toAdd z)
  ```
- `TauCeti.zHat.ringEquivPiPadicInt` — `…ZHat.Decomposition` (`Decomposition.lean:164`); `component_ringEquivPiPadicInt_symm` (`:179`), `continuous_ringEquivPiPadicInt_symm` (`:189`), `ext_of_component` (`:90`), `idem` (`:201`), `component_idem` (`:223`)
  ```lean
  TauCeti.zHat.ringEquivPiPadicInt : Additive ↑TauCeti.zHat.toProfinite.toTop ≃+* ((ℓ : Nat.Primes) → ℤ_[↑ℓ])
  TauCeti.zHat.component_ringEquivPiPadicInt_symm : ∀ (u : (ℓ : Nat.Primes) → ℤ_[↑ℓ]) (ℓ : Nat.Primes),
    (TauCeti.zHat.component ↑ℓ) (TauCeti.zHat.ringEquivPiPadicInt.symm u) = u ℓ
  ```
- `TauCeti.IsProP.padicPow` — `…Profinite.ProP.PadicPow` (`ProP/PadicPow.lean:135`); `eq_padicPow_of_continuous` (`:252`), `padicPow_natCast` (`:158`), `map_padicPow` (`:296`)
  ```lean
  @TauCeti.IsProP.padicPow : {p : ℕ} → [hp : Fact (Nat.Prime p)] → {A : Type u_1} → [inst : Group A] →
    [inst_1 : TopologicalSpace A] → [IsTopologicalGroup A] → [CompactSpace A] → [TotallyDisconnectedSpace A] →
    TauCeti.IsProP p A → A → ℤ_[p] → A
  @TauCeti.IsProP.eq_padicPow_of_continuous : ∀ … (hA : TauCeti.IsProP p A) {a : A} {f : ℤ_[p] → A},
    Continuous f → (∀ (k : ℕ), f ↑k = a ^ k) → ∀ (l : ℤ_[p]), f l = hA.padicPow a l
  ```
- Also useful: `TauCeti.zpowHat_eq_padicPow_component` (`ZHat/Pow.lean:261`): `TauCeti.zpowHat x a = hG.padicPow x (component ℓ a)`.

Instances (tested, `#synth`): `Fact (Nat.Prime 2)` = `Nat.fact_prime_two`. On `GQ2.Delta`: `GQ2.Delta.isTopologicalGroup`,
`GQ2.Delta.toProfinite.is_compact`, `Profinite.instTotallyDisconnectedSpaceCarrierToTop`, `GQ2.Delta.toProfinite.is_hausdorff`.
On `GQ2.AbsGalQ2`: `Field.instIsTopologicalGroupAbsoluteGaloisGroup ℚ_[2]`, `TauCeti.instCompactSpaceAbsoluteGaloisGroup_tauCeti ℚ_[2]`,
`TotallySeparatedSpace.totallyDisconnectedSpace`. On `maximalProPQuotient 2 (presentedProfiniteGroup X rels)`: compact,
topological group and totally disconnected all synthesize (the last via `GQ2.instTotallyDisconnectedSpace_quotient`). Nothing needs supplying by hand.

### Translation
Confirmed (all tested in a `module` file, no `import all`):
- `GQ2.IsProP p G ↔ TauCeti.IsProP p G := TauCeti.isProP_iff.symm`.
- `GQ2.proPKernel p G = TauCeti.proPKernel p G`: `ext x; rw [TauCeti.mem_proPKernel_iff, GQ2.proPKernel, Subgroup.mem_iInf]; exact ⟨fun h U hU => h ⟨U, hU⟩, fun h U => h U.1 U.2⟩`.
- `maxProPEquiv p G : GQ2.maxProPQuotient p G ≃ₜ* TauCeti.maximalProPQuotient p G := (ContinuousMulEquiv.refl G).quotientCongr _ _ (by rw [proPKernel_eq]; exact Subgroup.map_id _)`, with `maxProPMk ↦ maximalProPQuotient.mk` by `quotientCongr_mk` (not `rfl`). At `G = AbsGalQ2` this is the plan's `maxProPQuotient 2 AbsGalQ2 ≃ₜ* absoluteGaloisGroupProP 2 ℚ_[2]` verbatim.
- `deltaEquiv : GQ2.Delta ≃ₜ* TauCeti.freeProP 2 (Fin 2) := maxProPEquiv 2 (GQ2.FreeProfiniteGroup (Fin 2))`, with `deltaEquiv deltaP = freeProP.of 0`, `deltaEquiv deltaT = freeProP.of 1`.
- `zpowZtwo hP x u = ((isProP_iff 2 P).1 hP).padicPow x u := TauCeti.IsProP.eq_padicPow_of_continuous _ (GQ2.continuous_zpowZtwo hP x) (GQ2.zpowZtwo_natCast hP x) u` (one line, as the plan says).
- `Zhat ≃ₜ* TauCeti.zHat.{0}`: forward `(GQ2.zpowHatHom (G := zHat.{0}) zHat.gen).hom`, backward `zHat.lift (Zhat.ofInt 1)`, inverses by `Zhat.funext_ofInt` and `zHat.hom_ext`; `e (Zhat.ofInt n) = zHat.ofInt (ofAdd n)`; then `zhatProjTwo γ = ofAdd (zHat.component 2 (ofMul (e γ)))` (by `funext_ofInt`, `ofMul_ofInt`, `map_intCast`). About 45 lines, `artifacts/prop/proto_zhat.lean`.

Corrections to the plan:
- "same predicate word for word" is true of the source text, but `TauCeti.IsProP`, `proPKernel`, `freeProfiniteGroup.of`, `presentedProfiniteGroup.mk`, `quotientCongr`, `Peripheral.periphP` etc. are **not exposed** (Tau Ceti uses `public section` without `@[expose]`). So `Iff.rfl`/`rfl` fail from a `module` adapter ("definition is not exposed"). They succeed in a non-`module` file, and in a `module` file after `import all TauCeti.Topology.Algebra.Group.Profinite.MaximalProP` (+ `…ProP.Basic`). `import all` across packages is accepted, but every downstream file that unfolds the result needs it too. Use the propositional bridges above.
- `TauCeti.maximalProPQuotient`, `freeProP`, `presentedProP`, `absoluteGaloisGroupProP` are `Type`s with instances, not `ProfiniteGrp` objects. gq2's are `ProfiniteGrp` objects, so the equivalences are between `↥(gq2 obj)` and a Tau Ceti type.
- `GQ2.Zhat` is not `zHat.{0}`: Tau Ceti completes `ULift.{u} (Multiplicative ℤ)`, and `ULift.{0}` is still a structure (`rfl` fails). Build the equivalence from the universal properties (done).
- The ℤ₂-component is in `ZHat/Component.lean`, not `Decomposition.lean` (see answer 6).
- Tau Ceti has **no** `maximalProPQuotient p (presentedProfiniteGroup X rels) ≃ₜ* presentedProP p X (fromFreeProfiniteGroup p X '' rels)`. It only has `toPresentedProP` (a surjection). gq2's pro-2 presentations are `maxProPQuotient 2 (profinitePresentation rels)`, so P1 must prove this. Done in `artifacts/prop/proto_p1.lean` (about 60 lines: `lift` both ways, inverses by `mk_surjective`). With it, `GQ2.D0 ≃ₜ* TauCeti.demushkinD0` elaborates as `(maxProPEquiv 2 D0Full).trans (maxProPPresentedEquiv 2 {d0RelatorT}) |>.trans (presentedProP.congrOfClosureEq …)`. The relator image is computed by `fromFree_d0Relator`. The commutator conventions agree: gq2 `commP x y = x⁻¹y⁻¹xy`, Tau Ceti `(S,Y) = S⁻¹Y⁻¹SY` (`Demushkin/D0/Basic.lean:77`).
- Universes: free/presentation objects are `Type u → … Type u` on both sides, with no ULift. `GQ2.zpowZtwo`/`zpowHatHom` are `Type`-only, while Tau Ceti's `padicPow`/`zHat.lift` are polymorphic. That is harmless at `Delta`, `AbsGalQ2` and `ℤ_[2]`.

**Hardest seam: spelling, not mathematics.** `GQ2.FreeProfiniteGroup X` (a plain `def`) and
`TauCeti.freeProfiniteGroup X` (an `abbrev`) are defeq, but instances, `simp` and `rw` keyed on one
spelling miss the other. Observed cases:
- `{GQ2.d0Relator}` builds `Set.instSingletonSet` at the gq2 carrier, so `Set.image_singleton` fails.
- With `rels : Set (TauCeti.freeProfiniteGroup X)`, `(GQ2.relatorSubgroup rels).Normal` is not found.
- With `rels : Set (GQ2.FreeProfiniteGroup X)`, `Mul (TauCeti.presentedProfiniteGroup X rels)` is not found.
- `simp [map_mul]` does not fire on a gq2-typed word pushed through `fromFreeProfiniteGroup`.

The fix: state the P1 API on Tau Ceti spellings, and transport each gq2 element once through an
`abbrev` (`d0RelatorT : TauCeti.freeProfiniteGroup (Fin 3) := GQ2.d0Relator`). Then rewrite the
word with a `simp only [GQ2.d0Relator, GQ2.commP, of_eq]; rfl` lemma before applying hom lemmas.

### Answers
**(1) Is `GQ2.FreeProfiniteGroup X` definitionally `TauCeti.freeProfiniteGroup X`?** Yes, as `ProfiniteGrp.{u}`
objects and as carriers (universe `u` on both sides, no `ULift`): `example (X : Type u) : GQ2.FreeProfiniteGroup X = TauCeti.freeProfiniteGroup X := rfl`
succeeds in a `module` file (in `GQ2/TauCeti/Smoke.lean`), because Tau Ceti's is an exposed `abbrev` of
`ProfiniteCompletion.completion (GrpCat.of (FreeGroup X))` and `profiniteCompletion.obj` unfolds to it.
`by with_reducible rfl` fails, because gq2's is a semireducible `def`. Consequences:
- `TauCeti.maximalProPQuotient 2 (GQ2.FreeProfiniteGroup (Fin 2)) = TauCeti.freeProP 2 (Fin 2) := rfl` succeeds.
- `(GQ2.profinitePresentation rels : Type u) = TauCeti.presentedProfiniteGroup X rels := rfl` succeeds.
- `GQ2.profinitePresentation rels ≃ₜ* TauCeti.presentedProfiniteGroup X rels := ContinuousMulEquiv.refl _` succeeds, with `rels` typed against `TauCeti.freeProfiniteGroup X`.

The generators are **not** `rfl` from a `module` file:
- `GQ2.FreeProfiniteGroup.of x = TauCeti.freeProfiniteGroup.of x := rfl` fails with "not unfolded … `TauCeti.freeProfiniteGroup.of` not exposed".
- The propositional proof `rw [← TauCeti.freeProfiniteGroup.fromFreeGroup_of, TauCeti.freeProfiniteGroup.coe_fromFreeGroup]; rfl` succeeds.
- In a non-`module` file (`artifacts/prop/defeq_nonmodule.lean`) the `of` equation is `rfl`. So are `(GQ2.Delta : Type) = TauCeti.freeProP 2 (Fin 2)` and `GQ2.deltaP = TauCeti.freeProP.of 0`.

**(2) Do the two `proPKernel`s agree?** The definitions are textually identical (`⨅ U : {U : OpenNormalSubgroup G // IsPGroup p (G ⧸ U.toSubgroup)}, U.1.toSubgroup`,
`GQ2/MaxProP.lean:132` vs `Profinite/MaximalProP.lean:97`), so they are definitionally equal. But
`rfl` fails from a `module` file ("`TauCeti.proPKernel` not exposed"). `rfl` succeeds in a non-module
file and with `import all TauCeti.Topology.Algebra.Group.Profinite.MaximalProP` (`artifacts/prop/defeq_importall.lean`).
Propositionally: `TauCeti.mem_proPKernel_iff` + `Subgroup.mem_iInf`, a 3-line proof (in `GQ2/TauCeti/Smoke.lean`).
`IsProP` behaves the same way: `TauCeti.isProP_iff.symm` works, `Iff.rfl` does not.

**(6) Which `ZHat/Decomposition.lean` declaration is the ℤ₂-component, and which is its section?**
- **Component.** `TauCeti.zHat.component 2 : Additive zHat →+* ℤ_[2]`, which lives in `ZHat/Component.lean:70`, not in
  Decomposition. `Decomposition.lean` bundles all components as `zHat.ringEquivPiPadicInt` (`:164`), and
  `ringEquivPiPadicInt_apply : ringEquivPiPadicInt a ℓ = component ℓ a` (`:172`).
- **No named section.** Tau Ceti has no named section `ℤ₂ → ℤ̂`. Use `fun v ↦ ringEquivPiPadicInt.symm (Pi.single (M := fun ℓ : Nat.Primes ↦ ℤ_[ℓ]) ⟨2, Nat.prime_two⟩ v)`.
  - Component: `component_ringEquivPiPadicInt_symm` + `Pi.single_eq_same`.
  - Continuity: `continuous_ringEquivPiPadicInt_symm` + `continuous_single`.
  - At `v = 1` it is `zHat.idem 2` (`:201`).
  - Pass the `M :=` explicitly; without it, `Nat.Primes`/`{p // p.Prime}` unification breaks `Pi.single_zero`.
  - Prove continuity by `unfold` + `continuous_single (A := …) ⟨2, _⟩`; the direct term `continuous_single _` hit a `whnf` timeout.
- **Composition with `zHat.ofInt`.** `component 2 (ofMul (zHat.ofInt z)) = (z.toAdd : ℤ_[2])`, by `zHat.ofMul_ofInt` (`Ring.lean:131`) then `map_intCast`.
- **Group-theoretic form.** `component_apply : component ℓ a = toAdd (lift (ofAdd 1) a.toMul)` (`Component.lean:99`) is literally gq2's `zhatProjTwo = (zpowHatHom (ofAdd 1)).hom`. Hence `zhatProjTwo γ = ofAdd (component 2 (ofMul (e γ)))` (tested).
- **Matching gq2's `ztwoEquivPadic`.** It corresponds to `zHat.maximalProPQuotientEquivPadicInt 2` (`ZHat/PadicInt.lean:67`; `_mk_eq_component`, `Component.lean:128`).

## B1: topological finite generation

### gq2 side
`absGalQ2_isTopologicallyFinitelyGenerated : ∃ s : Finset AbsGalQ2, (Subgroup.closure (s : Set AbsGalQ2)).topologicalClosure = ⊤`
(`GQ2/Foundations/LiteratureInputs.lean:48-49`; `AbsGalQ2` at `GQ2/Statement.lean:40`).

### Tau Ceti sources
- `TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup` — `TauCeti.NumberTheory.LocalField.Generation.AbsoluteGaloisGroup` (`NumberTheory/LocalField/Generation/AbsoluteGaloisGroup.lean:67`)
  ```lean
  TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (K : Type)
    [inst_1 : Field K] [inst_2 : ValuativeRel K] [inst_3 : TopologicalSpace K] [IsNonarchimedeanLocalField K]
    [inst_5 : Algebra ℚ_[p] K] [Module.Finite ℚ_[p] K] [ValuativeExtension ℚ_[p] K],
    TauCeti.IsTopologicallyFinitelyGenerated (Field.absoluteGaloisGroup K)
  ```
  At `K = ℚ_[2]` every instance argument synthesizes (names under A1). Tested.
- `TauCeti.IsTopologicallyFinitelyGenerated` — `TauCeti.Topology.Algebra.Group.Generation` (`Topology/Algebra/Group/Generation.lean:73`)
  ```lean
  TauCeti.IsTopologicallyFinitelyGenerated : (G : Type u_1) →
    [inst : Group G] → [inst_1 : TopologicalSpace G] → [IsTopologicalGroup G] → Prop
  ```
- `TauCeti.isTopologicallyFinitelyGenerated_iff` — same module (`:83`)
  ```lean
  @TauCeti.isTopologicallyFinitelyGenerated_iff : ∀ {G : Type u_1} [inst : Group G] [inst_1 : TopologicalSpace G]
    [inst_2 : IsTopologicalGroup G],
    TauCeti.IsTopologicallyFinitelyGenerated G ↔ ∃ s, (Subgroup.closure ↑s).topologicalClosure = ⊤
  ```

### Translation
The whole adapter, tested in `GQ2/TauCeti/Smoke.lean` and also in a file that also imports the B6/B7 modules:
```lean
TauCeti.isTopologicallyFinitelyGenerated_iff.mp
  (TauCeti.isTopologicallyFinitelyGenerated_absoluteGaloisGroup 2 ℚ_[2])
```
Corrections: the instances come from Mathlib (`Padics/ValuativeRel.lean`, `Padics/LocalField.lean`) and
`TauCeti.valuativeExtension_self`, not `NumberTheory/LocalField/Padic.lean`. The definition cannot be unfolded from a
`module` file (not exposed): direct elaboration fails with "definitions were not unfolded … not exposed:
`TauCeti.IsTopologicallyFinitelyGenerated`", so go through the `_iff` lemma. Universe: `K : Type`, fine. Keep `B1.lean`
minimal: its import makes Galois-instance search at `ℚ̄₂` time out (A1, hardest seam).

## B7: local Euler characteristic

### gq2 side
`GQ2.LiteratureInputs.absGalQ2_localEulerCharacteristic` (`GQ2/Foundations/LiteratureInputs.lean:51`), verbatim:
```lean
  absGalQ2_localEulerCharacteristic (M : Type) [AddCommGroup M] [TopologicalSpace M]
      [DiscreteTopology M] [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M]
      [Finite M] :
      Finite (H0 AbsGalQ2 M) ∧ Finite (H1 AbsGalQ2 M) ∧ Finite (H2 AbsGalQ2 M) ∧
        Nat.card (H1 AbsGalQ2 M) =
          Nat.card (H0 AbsGalQ2 M) * Nat.card (H2 AbsGalQ2 M) *
            2 ^ padicValNat 2 (Nat.card M)
```
`H0/H1/H2` are `GQ2.ContCoh.*` (A2); `GQ2.AbsGalQ2 := Field.absoluteGaloisGroup ℚ_[2]` (`noncomputable abbrev`,
`GQ2/Statement.lean:40`). Legacy axiom (`GQ2/Foundations/Axioms.lean:117`) has `M : Type*`.

### Tau Ceti sources
- `TauCeti.ClassFieldTheory.eulerCharacteristic_mixed` — `TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem` (`…/Local/EulerCharacteristic/Theorem.lean:98`)
  ```lean
  TauCeti.ClassFieldTheory.eulerCharacteristic_mixed : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (F : Type) [inst_1 : Field F] [inst_2 : ValuativeRel F] [inst_3 : TopologicalSpace F] [inst_4 : IsNonarchimedeanLocalField F] [inst_5 : TauCeti.FinitePadicExtension F p] (n : ℕ), n ≠ 0 → ∀ (A : TauCeti.ClassFieldTheory.GalRep n F), Finite ↑A → ∀ [Fact (TauCeti.IsSmoothDiscrete (ZMod n) A)], Nat.card ↑(continuousCohomology 1 A).toModuleCat = Nat.card ↑(continuousCohomology 0 A).toModuleCat * Nat.card ↑(continuousCohomology 2 A).toModuleCat * p ^ (Module.finrank ℚ_[p] F * padicValNat p (Nat.card ↑A))
  ```
- `TauCeti.ClassFieldTheory.finite_H` — `TauCeti.NumberTheory.ClassFieldTheory.FiniteCohomology.DegreeTwo` (`…/FiniteCohomology/DegreeTwo.lean:97`)
  ```lean
  @TauCeti.ClassFieldTheory.finite_H : ∀ {F : Type} [inst : Field F] [inst_1 : ValuativeRel F] [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] {n : ℕ}, ↑n ≠ 0 → ∀ (A : TauCeti.ClassFieldTheory.GalRep n F), TauCeti.IsSmoothDiscrete (ZMod n) A → ∀ [Finite ↑A] {i : ℕ}, i ≤ 2 → Finite ↑(continuousCohomology i A).toModuleCat
  ```
- `TauCeti.ClassFieldTheory.GalRep` — `TauCeti.NumberTheory.ClassFieldTheory.MuNRep` (`…/MuNRep.lean:130`, `abbrev … := TopRep.{u} (ZMod n) (Field.absoluteGaloisGroup F)`)
  ```lean
  TauCeti.ClassFieldTheory.GalRep : ℕ → (F : Type u_1) → [Field F] → Type (u_1 + 1)
  ```
- `TauCeti.IsSmoothDiscrete` — `TauCeti.RepresentationTheory.Homological.ContCohomology.SmoothDiscrete.Basic` (`…/SmoothDiscrete/Basic.lean:259`)
  ```lean
  TauCeti.IsSmoothDiscrete : (R : Type u_1) → [inst : Ring R] → [inst_1 : TopologicalSpace R] → {G : Type u_2} → [inst_2 : Monoid G] → [TopologicalSpace G] → TopRep R G → Prop
  ```
- `TauCeti.ofDiscreteModule_isSmoothDiscrete` (`:345`), `TauCeti.isSmoothDiscrete_iff_continuousSMul` (`:368`), `IsSmoothDiscrete.continuousSMul` (`:376`)
  ```lean
  TauCeti.ofDiscreteModule_isSmoothDiscrete : ∀ (R : Type u_1) [inst : Ring R] [inst_1 : TopologicalSpace R] (G : Type u_2) [inst_2 : Monoid G] [inst_3 : TopologicalSpace G] (M : Type u_3) [inst_4 : AddCommGroup M] [inst_5 : Module R M] [inst_6 : TopologicalSpace M] [inst_7 : DiscreteTopology M] [inst_8 : DistribMulAction G M] [inst_9 : SMulCommClass G R M] [inst_10 : ContinuousSMul R M] [ContinuousSMul G M], TauCeti.IsSmoothDiscrete R (TauCeti.ofDiscreteModule R G M)
  ```
- Packaging helpers: `AddCommGroup.zmodModule` (Mathlib), `TauCeti.ZMod.smulCommClass'` (`Algebra/Module/ZMod/SMulCommClass.lean:38`),
  `TauCeti.ZMod.continuousSMul_of_discreteTopology` (`Topology/Instances/ZMod.lean:29`), `TauCeti.FinitePadicExtension.ofInstances`
  (`NumberTheory/LocalField/AbsoluteRamificationIndex.lean:83`); comparisons as in A2.

Instances at `F = ℚ_[2]` (all tested by `#synth`): `Fact (Nat.Prime 2)` = `Nat.fact_prime_two`; `ValuativeRel ℚ_[2]` =
`Padic.instValuativeRel`; `IsNonarchimedeanLocalField ℚ_[2]` = `instIsNonarchimedeanLocalFieldPadic`;
`TauCeti.FinitePadicExtension ℚ_[2] 2` = `FinitePadicExtension.ofInstances ℚ_[2] 2` (its algebra is `Algebra.id`, `rfl`);
`CompactSpace`/`LocallyCompactSpace`/`IsTopologicalGroup (Field.absoluteGaloisGroup ℚ_[2])` found. Adapter supplies:
`Module (ZMod (Nat.card M)) M` (`AddCommGroup.zmodModule fun _ => card_nsmul_eq_zero'`, with `NeZero` from `Nat.card_pos`),
`Fact (IsSmoothDiscrete (ZMod (Nat.card M)) A)`, `Finite A.V`, `DiscreteTopology A.V` and `ContinuousSMul AbsGalQ2 A.V`
(the last three by `inferInstanceAs` — not found through the `def`). `SMulCommClass AbsGalQ2 (ZMod n) M` and
`ContinuousSMul (ZMod n) M` synthesize (`smulCommClass'`, `continuousSMul_of_discreteTopology`).

### Translation
- **B7 closes in scratch** (`artifacts/cohom/evidence/b7_proof.lean`, ~45 lines on top of A2's propositional `h1Equiv`/`h2Equiv`; the field's
  exact statement; `#print axioms` = `propext, Classical.choice, Quot.sound`): `A := TauCeti.ofDiscreteModule (ZMod (Nat.card M))
  (Field.absoluteGaloisGroup ℚ_[2]) M`; `A.V = M` and `TopRep.distribMulAction A = ‹DistribMulAction AbsGalQ2 M›` are `rfl`, so
  `H1 AbsGalQ2 A.V` is `H1 AbsGalQ2 M`; `e1 := h1Equiv.trans A.explicitH1AddEquivContinuousCohomologyOfDiscrete`, `e2` likewise,
  `e0 := (explicitH0IsoContinuousCohomology AbsGalQ2 A.V).toContinuousLinearEquiv.toAddEquiv.trans (ofDiscreteModuleRestrictScalarsIntEquiv A 0)`
  (`GQ2.ContCoh.H0 = TauCeti…H0` is `rfl`); finiteness from `finite_H hn A hA (i := 0/1/2)`; the count from
  `eulerCharacteristic_mixed 2 ℚ_[2] (Nat.card M) _ A inferInstance`, `Module.finrank_self`, `one_mul`, `Nat.card_congr`.
- Plan/ticket corrections: `Finite A.V` is the explicit argument `hA` of `eulerCharacteristic_mixed` (instance in `finite_H`); `F` is
  an explicit argument after `p` — the ticket's `eulerCharacteristic_mixed 2 (Nat.card M) _ A _` must read
  `eulerCharacteristic_mixed 2 ℚ_[2] (Nat.card M) hn A hA`. `finite_H` takes `hn : (n : F) ≠ 0` and `IsSmoothDiscrete` explicitly;
  `eulerCharacteristic_mixed` takes `n ≠ 0` and `[Fact (IsSmoothDiscrete …)]`. `IsSmoothDiscrete` comes from
  `ofDiscreteModule_isSmoothDiscrete` directly (no stabilizer argument needed).
- **Instance pathology (tested):** under the `EulerCharacteristic.Theorem` import closure, `Nontrivial ℚ_[2]` and
  `StrongRankCondition ℚ_[2]` time out (also at 100k heartbeats, 100 s) through the loop
  `IsLocalRing → HenselianLocalRing → TauCeti.IsAdicComplete.henselianLocalRing → IsLocalRing …` (`RingTheory/Henselian/Basic.lean:88`),
  so `Module.finrank_self ℚ_[2]` fails. Fix: `attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing in` or
  `@Module.finrank_self ℚ_[2] _ (@commRing_strongRankCondition ℚ_[2] _ DivisionRing.toNontrivial)` (`artifacts/cohom/evidence/b7_finrank_workaround.lean`).
- Universes: `eulerCharacteristic_mixed` fixes `F : Type`, `GalRep n F = TopRep.{0}`, and the explicit comparisons need `G M` in one
  universe, so the adapter covers `M : Type` only (matches `LiteratureInputs`). C2's restatement with `M : Type*` would need an
  extra transport of `M` to a `Type`-sized copy (e.g. along `Finite.equivFin`), which Tau Ceti does not provide.
- Hardest seam: none left beyond A2's `H1`/`H2` dictionary; B7 can land right after A2's first half.

### Answers
(none assigned to this lane)

## B6: local Tate duality at every finite `k/ℚ₂`

Scratch evidence: `GQ2/TauCeti/Smoke.lean` (77 `#check`s + 6 `rfl`/`Iff.rfl` pins, elaborates clean; output in
the `#check` output of `Smoke.lean`) and `artifacts/tate/b6check.lean` (the Q4 reconstruction and the instance-package test, elaborates
clean, `#print axioms` = `propext, Classical.choice, Quot.sound`), both in `artifacts/tate/`.

### gq2 side

`LiteratureInputs` field (`GQ2/Foundations/LiteratureInputs.lean:64`), verbatim:
```lean
  tateDualityAt (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      (n : ℕ) [NeZero n] [DistribMulAction G (MuN n)] [ContinuousSMul G (MuN n)]
      (hloc : IsLocalDualizingGroup G n) : TateDualityG G n
```
- `GQ2.TateDualityG` (`GQ2/TateDuality.lean:208`): fields `inv : H2 G (MuN n) ≃+ ZMod n` and
  `perfect02/11/20 : ∀ (M : Type) [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction G M] [ContinuousSMul G M] [Finite M], (∀ x : M, n • x = 0) →
  Function.Bijective fun c : Hⁱ G (MuDual n M) => inv.toAddMonoidHom.comp (cupi(2-i) (muDualPairing n M) (muDualPairing_equivariant n M) c)`
  (`H0` is an `AddSubgroup`, coerced; `H1/H2` are quotients, `GQ2/Cohomology.lean:75,132,141`).
- `GQ2.IsLocalDualizingGroup` (`GQ2/TateDuality.lean:244`), pinned by `Iff.rfl` in `GQ2/TauCeti/Smoke.lean`:
  `∃ ι : G →* AbsGalQ2, Topology.IsOpenEmbedding ι ∧ (ι.range).FiniteIndex ∧ ∀ (g : G) (x : MuN n), g • x = ι g • x`.
- `GQ2.MuN n := Additive (rootsOfUnity n (AlgebraicClosure ℚ_[2]))` (`GQ2/MuN.lean:151`, `rfl`);
  `GQ2.MuDual n M := M →+ MuN n` (`TateDuality.lean:80`, a `def`, `rfl`), action
  `(g • φ) m = g • φ (g⁻¹ • m)` (`:115`, `muDual_smul_apply`); `muDualPairing` = identity (`:169`).
- Cups `GQ2.cup11/cup02/cup20` (`GQ2/CupProduct.lean:153,259,344`): `(a∪b)(g,h) = μ (a g) (g • b h)`,
  `μ m (b(g,h))`, `μ (a(g,h)) ((g*h) • n)` — the same cochain formulas as Tau Ceti's
  `explicitCup11/02/20` (`ContCohomology/Cup/Product.lean:24-29`).
- Live consumers instantiate `G = AbsGalQ2` (`Foundations/Interfaces.lean:89`) and
  `G = ↥(ρ.toMonoidHom.ker)` (`GQ2/DeepDualityK.lean:86`), so the adapter must work for subgroup types.

### Tau Ceti sources

All under `.lake/packages/TauCeti/TauCeti/`; `CFT/` = `NumberTheory/ClassFieldTheory/`.
- `TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed` — module `…Local.Duality.Perfect` (`CFT/Local/Duality/Perfect.lean:280`)
  ```lean
  TauCeti.ClassFieldTheory.tateDualityPairing_perfect_mixed : ∀ (F : Type) [inst : Field F] [CharZero F]
    [inst_2 : ValuativeRel F] [inst_3 : TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ),
    n ≠ 0 →
      ∀ (A : TauCeti.ClassFieldTheory.GalRep n F)
        (tr : ↑(continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n F)).toModuleCat ≃+ ZMod n),
        Finite ↑A →
          ∀ [inst_5 : DiscreteTopology ↑A] [Fact (TauCeti.IsSmoothDiscrete (ZMod n) A)] (i j : ℕ) (hij : i + j = 2),
            (∀ (x : ↑(continuousCohomology i (TauCeti.ClassFieldTheory.tateDual A)).toModuleCat),
                (∀ (y : ↑(continuousCohomology j A).toModuleCat),
                    TauCeti.ClassFieldTheory.tateDualityPairing A tr i j hij x y = 0) →
                  x = 0) ∧
              ∀ (φ : ↑(continuousCohomology j A).toModuleCat →+ ZMod n),
                ∃ x,
                  ∀ (y : ↑(continuousCohomology j A).toModuleCat),
                    TauCeti.ClassFieldTheory.tateDualityPairing A tr i j hij x y = φ y
  ```
  Same conclusion for `tateDualityPairing_perfect` (`:242`, hypothesis `IsUnit (n : F)` instead of
  `CharZero`/`n ≠ 0`); the converse adjoint is `tateDualityPairing_flip_perfect` (`:220`).
  At `F = ↥K`, `K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])` finite: `CharZero ↥K` synthesizes;
  `ValuativeRel`, `TopologicalSpace`, `IsNonarchimedeanLocalField` must be installed by the adapter from
  `TauCeti.finiteIntermediateFieldValuativeRel/Topology ℚ_[2] (AlgebraicClosure ℚ_[2]) K` and
  `finiteIntermediateField_isNonarchimedeanLocalField` (`NumberTheory/LocalField/FiniteExtension/IntermediateField.lean:69,75,97`);
  `Finite`, `DiscreteTopology`, `Fact IsSmoothDiscrete` come from building `A` (below). **Tested**
  (`artifacts/tate/b6check.lean`, all three `(i,j)`).
- `TauCeti.ClassFieldTheory.tateDualityPairing` — `…Local.Duality.Basic` (`CFT/Local/Duality/Basic.lean:385`), `= tr (hij ▸ (tateEvaluationPairing A).cup i j x y)` (`tateDualityPairing_def`)
  ```lean
  @TauCeti.ClassFieldTheory.tateDualityPairing : {n : ℕ} →
    {F : Type u_1} →
      [inst : Field F] →
        (A : TauCeti.ClassFieldTheory.GalRep n F) →
          [DiscreteTopology ↑A] →
            ↑(continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n F)).toModuleCat ≃+ ZMod n →
              (i j : ℕ) →
                i + j = 2 →
                  ↑(continuousCohomology i (TauCeti.ClassFieldTheory.tateDual A)).toModuleCat →
                    ↑(continuousCohomology j A).toModuleCat → ZMod n
  ```
- `TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed` — `…Brauer.RootsOfUnity` (`CFT/Brauer/RootsOfUnity.lean:145`; the data is `h2MuEquivZMod F hn`, `:89`)
  ```lean
  TauCeti.ClassFieldTheory.h2MuEquivZMod_mixed : ∀ (F : Type) [inst : Field F] [inst_1 : ValuativeRel F]
    [inst_2 : TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] (n : ℕ),
    n ≠ 0 → Nonempty (↑(continuousCohomology 2 (TauCeti.ClassFieldTheory.muNRep n F)).toModuleCat ≃+ ZMod n)
  ```
- `TauCeti.ClassFieldTheory.tateDual` (`Duality/Basic.lean:97`), `tateDualEquiv` (`:107`), `tateDualEquiv_ρ_apply` (`:144`)
  ```lean
  @TauCeti.ClassFieldTheory.tateDual : {n : ℕ} →
    {F : Type u_1} → [inst : Field F] → TauCeti.ClassFieldTheory.GalRep n F → TauCeti.ClassFieldTheory.GalRep n F
  @TauCeti.ClassFieldTheory.tateDualEquiv : … (A : TauCeti.ClassFieldTheory.GalRep n F) →
          ↑(TauCeti.ClassFieldTheory.tateDual A) ≃+ (↑A →+ ↑(TauCeti.ClassFieldTheory.muNRep n F))
  -- tateDualEquiv_ρ_apply:  tateDualEquiv A ((tateDual A).ρ g φ) a = (muNRep n F).ρ g (tateDualEquiv A φ (A.ρ g⁻¹ a))
  ```
- `TauCeti.ClassFieldTheory.GalRep` (`CFT/MuNRep.lean:130`, `abbrev` for `TopRep (ZMod n) (Field.absoluteGaloisGroup F)`), `muNRep` (`:137`), `kummerCoeffEquivMuNRep(_smul)` (`:150,:165`)
  ```lean
  TauCeti.ClassFieldTheory.GalRep : ℕ → (F : Type u_1) → [Field F] → Type (u_1 + 1)
  TauCeti.ClassFieldTheory.muNRep : (n : ℕ) → (F : Type u_1) → [inst : Field F] → TauCeti.ClassFieldTheory.GalRep n F
  TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep_smul : ∀ (n : ℕ) (F : Type u_1) [inst : Field F]
    (g : Field.absoluteGaloisGroup F) (x : TauCeti.KummerCoeff F n),
    (TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep n F) ((TauCeti.absoluteGaloisGroupRestrictEquiv F) g • x) =
      ((TauCeti.ClassFieldTheory.muNRep n F).ρ g) ((TauCeti.ClassFieldTheory.kummerCoeffEquivMuNRep n F) x)
  ```
  `TauCeti.KummerCoeff F n = Additive (rootsOfUnity n (SeparableClosure F))` (`rfl`, pinned).
- `TauCeti.ClassFieldTheory.muNRepToTateDual` (`CFT/Local/Duality/RootsOfUnity.lean:61`): needs a primitive
  `ζ : F` with `IsPrimitiveRoot ζ n`; **not needed for B6** (it is the `μₙ ≅ μₙ'` self-duality when `μₙ ⊆ F`).
- `TauCeti.ClassFieldTheory.range_absoluteGaloisGroupExtend_shapiroFieldEmbedding` (`CFT/Local/EulerCharacteristic/Shapiro.lean:160`)
  ```lean
  … (V : OpenNormalSubgroup (Field.absoluteGaloisGroup F)) (C : Subgroup (Field.absoluteGaloisGroup F ⧸ ↑V.toOpenSubgroup))
    [inst_1 : IsGalois F (AlgebraicClosure F)],
    (TauCeti.absoluteGaloisGroupExtend F (↥(TauCeti.ClassFieldTheory.shapiroField F V C))
          (TauCeti.ClassFieldTheory.shapiroFieldEmbedding F V C)).range =
      Subgroup.comap (QuotientGroup.mk' ↑V.toOpenSubgroup) C
  ```
  The only `range_absoluteGaloisGroupExtend_*` lemma in Shapiro.lean (plus
  `index_eq_finrank_of_range_absoluteGaloisGroupExtend_eq_comap`, `:114`). Its 12-line proof works
  verbatim for any finite `E : IntermediateField ℚ_[2] ℚ̄₂` (`T2Tate.range_absoluteGaloisGroupExtend_sepEmb` in `artifacts/tate/b6check.lean`).
- `TauCeti.absoluteGaloisGroupExtend` / `absoluteGaloisGroupExtendEquiv` / `coe_absoluteGaloisGroupExtendEquiv_apply`
  (`FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:247,325,337`)
  ```lean
  TauCeti.absoluteGaloisGroupExtendEquiv : (K : Type u_1) → [inst : Field K] → (L : Type u_2) → [inst_1 : Field L] →
    [inst_2 : Algebra K L] → (σ : L →ₐ[K] SeparableClosure K) → [inst_3 : FiniteDimensional K L] →
    {U : Subgroup (Field.absoluteGaloisGroup K)} →
    (TauCeti.absoluteGaloisGroupExtend K L σ).range = U → Field.absoluteGaloisGroup L ≃ₜ* ↥U
  ```
- Coefficient transport: `TauCeti.kummerCoeffMap K n L σ : KummerCoeff K n →+ KummerCoeff L n` and
  `kummerCoeffMap_smul` (`FieldTheory/GaloisCohomology/Kummer.lean:576,592`; inverse `kummerCoeffMapSymm`, `:765`),
  `absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend` (`FiniteExtension.lean:256`),
  `coe_absoluteGaloisGroupRestrictEquiv_apply` (`AbsoluteGaloisGroup/Basic.lean:339`: `↑(restrictEquiv K σ x) = σ ↑x`).
- Building `A`: `TauCeti.ofDiscreteModule (ZMod n) (Field.absoluteGaloisGroup K) M` (`ContCohomology/SmoothDiscrete/Basic.lean:223`),
  `.V = M` by `rfl` (pinned); `Fact IsSmoothDiscrete` from `ofDiscreteModule_isSmoothDiscrete` (`:345`);
  `Module (ZMod n) M := AddCommGroup.zmodModule htor`; `SMulCommClass`/`ContinuousSMul (ZMod n)` synthesize
  from `TauCeti.ZMod.smulCommClass'` and `TauCeti.ZMod.continuousSMul_of_discreteTopology`. **Tested.**
- Cup bridges (general `μ`): `tateDualityPairing_eq_explicitDualityPairing02/11/20` (`CFT/Local/Duality/Explicit.lean:137,182,225`),
  `TauCeti.TopPairing.cup_one_one_explicitH1AddEquivContinuousCohomologyOfDiscrete`,
  `cup_zero_two/two_zero_ofDiscreteModuleRestrictScalarsInt` (`ContCohomology/Cup/RestrictScalars.lean:330,298,311`),
  `TauCeti.ContCohomology.explicitAddEquiv_cup02/20` (`Cup/Comparison.lean:303,337`),
  change of group + coefficients `explicitMap1Equiv/explicitMap2Equiv` (`ExplicitFunctoriality.lean:439,546`),
  `explicitMap0_bijective` (`LowDegree.lean:387`), naturality `explicitMap2_explicitCup02/20/11` (`Cup/Naturality.lean:201,248,300`).

### Translation

1. **Group** (Q4, done in `artifacts/tate/b6check.lean`): `K := fixedField ι.range`, `K.fixingSubgroup = ι.range`,
   `FiniteDimensional ℚ_[2] K`, `e : G ≃ₜ* Field.absoluteGaloisGroup K` with
   `absoluteGaloisGroupExtend ℚ_[2] K (sepEmb K) (e g) = ι g`. Offer `range_absoluteGaloisGroupExtend_sepEmb` to A1:
   with `absoluteGaloisGroupExtendEquiv` it *is* A1's `k.fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥k`.
2. **Modules**: put the `G_K`-action on `M` along `e.symm` (`DistribMulAction.compHom`), `A := ofDiscreteModule …`.
   `MuDual n M ≅ (tateDual A).V` via `tateDualEquiv A` plus a coefficient iso `MuN n ≃+ (muNRep n K).V`;
   gq2's conjugation formula is exactly `tateDualEquiv_ρ_apply` (confirmed).
3. **`μₙ` seam** (plan claim (ii) confirmed but understated): `MuN n` is `μₙ(ℚ̄₂)`, `muNRep n K` is
   `μₙ(Kˢᵉᵖ)` reached only through `kummerCoeffEquivMuNRep` (`muNRep`, `tateDual`, `galoisSubgroupEquiv`,
   `absoluteGaloisGroupEquivFixingSubgroup` are **not exposed**: `rfl` fails, tested). Chain:
   `(muNRep n K).V ≃ KummerCoeff K n --kummerCoeffMapSymm ℚ_[2] n K σ--> KummerCoeff ℚ_[2] n ≃ μₙ(ℚ̄₂)`;
   the last step is `restrictRootsOfUnity` of `SeparableClosure ℚ_[2] = separableClosure ℚ_[2] ℚ̄₂ ↪ ℚ̄₂`,
   bijective in char 0 (not in Tau Ceti; ~30 lines). Equivariance: `kummerCoeffEquivMuNRep_smul`,
   `kummerCoeffMapSymm_smul`, `absoluteGaloisGroupRestrictEquiv_absoluteGaloisGroupExtend` (bridge
   `galoisSubgroupEquiv` ↔ `absoluteGaloisGroupEquivFixingSubgroup` by their `_apply` lemmas + ext),
   `coe_absoluteGaloisGroupRestrictEquiv_apply`, and gq2's `hloc` compatibility `g • x = ι g • x`.
4. **Cohomology/cup**: A2's `GQ2.ContCoh.Hi G M ≃+ TauCeti.ContCohomology.Hi G M` (for arbitrary `G`), then
   `explicitMap{1,2}Equiv`/`explicitMap0_bijective` along `e.symm` and the coefficient isos, then
   `explicitH{1,2}AddEquivContinuousCohomologyOfDiscrete`. **A2 must also give cup compatibility for an
   arbitrary pairing `μ`** (gq2 `cupXY μ hμ` vs `explicitCupXY G M N P μ _ hμ`), not only `trivialF2`;
   the formulas agree, so it should be by unfolding on `H?mk`.
5. **`inv`**: define `inv := (H² dictionary for MuN n) ≪≫ h2MuEquivZMod ↥K _`; the Tau Ceti theorem holds for
   every `tr`, so normalization is irrelevant. Bijectivity transfers through any commuting square of
   `AddEquiv`s, so a sign or coefficient automorphism in the cup comparison would be harmless.
6. Conventions: universes fine (`F : Type`, `A.V : Type`, gq2 `M : Type`); additive `μₙ` on both sides;
   no Frobenius/commutator issue; `(ι.range).FiniteIndex` in `hloc` is not needed (openness suffices).
7. **Instance hazard (tested, affects every adapter over `ℚ̄₂` that imports Tau Ceti's CFT)**: with
   `…Brauer.RootsOfUnity` or `…Local.Duality.Perfect` imported, `Module.IsTorsionFree ℚ_[2] ℚ̄₂`,
   `IsAlgClosure ℚ_[2] ℚ̄₂`, `IsGalois ℚ_[2] ℚ̄₂`, `Algebra.IsSeparable ℚ_[2] ℚ̄₂` all **time out**
   (20000 heartbeats; the search wanders into `Module.Finite ℚ_[2] ℚ̄₂` via
   `TauCeti.FinitePadicExtension.toModuleFinite`; with `synthInstance.maxHeartbeats 400000` it runs into the global 200000). Fix (tested): file-level
   `local instance : Module.IsTorsionFree ℚ_[2] ℚ̄₂ := DivisionSemiring.to_moduleIsTorsionFree`,
   `local instance : IsAlgClosure ℚ_[2] ℚ̄₂ := AlgebraicClosure.instIsAlgClosure ℚ_[2]`,
   `local instance : IsGalois ℚ_[2] ℚ̄₂ := IsAlgClosure.isGalois _ _`. Put these in a shared dictionary file.
8. Topology diamond on `↥K`: gq2's imports give `ℚ̄₂` a topology (`PadicAlgCl.valued 2`), so `↥K` has a
   subspace topology as well as Tau Ceti's `finiteIntermediateFieldTopology`. Harmless here (the conclusion
   only uses the Krull topology of `G_K`), but apply the theorem with `@…perfect_mixed (↥K) _ _ _ _ hLF …`;
   with `A` a `let`, `[DiscreteTopology ↑A]` is "stuck" unless passed explicitly (tested).
Hardest seam: item 3 + item 4 together (coefficient transport `μₙ(ℚ̄₂) ↔ μₙ(Kˢᵉᵖ)` through opaque defs,
then cup naturality across `e` and the two coefficient isos in three bidegrees).

### Answers

**(3) Does `Perfect.lean` state bijectivity?** Yes, in substance. `tateDualityPairing_perfect(_mixed)`
(`Perfect.lean:242,280`, verbatim above) gives, for `Φ x y := tateDualityPairing A tr i j hij x y`,
(a) `∀ x, (∀ y, Φ x y = 0) → x = 0` and (b) `∀ φ : Hʲ(A) →+ ZMod n, ∃ x, ∀ y, Φ x y = φ y`: injectivity and
surjectivity of `x ↦ Φ x · : Hⁱ(A') → Hom(Hʲ(A), ZMod n)`, which is exactly gq2's direction (dual in the left
slot). `tateDualityPairing_flip_perfect` (`:220`) gives the same for `y ↦ Φ · y`. So this is not just
two-sided nondegeneracy: (b) is the surjectivity half. It is not packaged as `Function.Bijective` of a
bundled hom; the packaging is 3 lines, checked: `T2Tate.bijective_of_perfect` in `artifacts/tate/b6check.lean`
(`(Φ : X →+ Y →+ ZMod n) → (h.1 ∧ h.2) → Function.Bijective Φ`, via `injective_iff_map_eq_zero` +
`AddMonoidHom.ext`). No counting is needed in the adapter (Tau Ceti did it internally with
`TauCeti.forall_eq_zero_and_exists_eq_of_bijective_flip`, `Algebra/Module/ZMod/Dual.lean:99`). If only two-sided
nondegeneracy were available, a counting argument would need: finiteness of both groups
(`TauCeti.ClassFieldTheory.finite_H : ↑n ≠ 0 → ∀ A, IsSmoothDiscrete (ZMod n) A → ∀ [Finite ↑A] {i}, i ≤ 2 → Finite …`,
`CFT/FiniteCohomology/DegreeTwo.lean:97`, applied to `A` and `tateDual A`), `n`-torsion of both,
`TauCeti.natCard_addMonoidHom_zmod : Nat.card (M →+ ZMod n) = Nat.card M` (`Dual.lean:57`) to get
`#Hⁱ(A') ≤ #Hom(Hʲ(A),ℤ/n) = #Hʲ(A) ≤ #Hom(Hⁱ(A'),ℤ/n) = #Hⁱ(A')` from the two injections, then
`Function.Injective.bijective_of_nat_card_le`.

**(4) Open finite-index subgroup ⇒ `K'.fixingSubgroup` for a finite `K'`.** Mathlib (Krull correspondence,
`Mathlib/FieldTheory/Galois/Infinite.lean`), checked:
```lean
@InfiniteGalois.fixingSubgroup_fixedField : ∀ {k : Type u_1} {K : Type u_2} [inst : Field k] [inst_1 : Field K]
  [inst_2 : Algebra k K] (H : ClosedSubgroup Gal(K/k)) [IsGalois k K],
  (IntermediateField.fixedField ↑H).fixingSubgroup = ↑H
@InfiniteGalois.isOpen_iff_finite : ∀ {k : Type u_1} {K : Type u_2} [inst : Field k] [inst_1 : Field K]
  [inst_2 : Algebra k K] (L : IntermediateField k K) [IsGalois k K],
  IsOpen L.fixingSubgroup.carrier ↔ FiniteDimensional k ↥L
@IntermediateField.finrank_eq_fixingSubgroup_index : ∀ {F : Type u_1} (E' : Type u_2) [inst : Field F]
  [inst_1 : Field E'] [inst_2 : Algebra F E'] (L : IntermediateField F E') [IsGalois F E'],
  Module.finrank F ↥L = L.fixingSubgroup.index
```
plus `Subgroup.isClosed_of_isOpen` (open ⇒ closed). Tau Ceti's analogues
`TauCeti.toSubgroup_eq_fixingSubgroup_of_fixedField_eq` / `finiteDimensional_fixedField_toSubgroup`
(`FiniteExtension.lean:514,523`) are stated on `TauCeti.AbsoluteGaloisGroup K` (separable closure), **not** on
`Field.absoluteGaloisGroup`/`AbsGalQ2`, so use the Mathlib ones directly (`AbsGalQ2` is
`AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] …` up to the `def` `Field.absoluteGaloisGroup`; `ι.range` coerces to
`Subgroup (ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂)` without friction). `IsGalois ℚ_[2] ℚ̄₂` is required (see item 7).
What `IsLocalDualizingGroup G n` provides: `ι : G →* AbsGalQ2`, `hι : IsOpenEmbedding ι`, `ι.range.FiniteIndex`
(redundant), and `∀ g x, g • x = ι g • x` on `MuN n`. Reconstruction, **checked**
(`T2Tate.exists_absoluteGaloisGroup_equiv`, `artifacts/tate/b6check.lean`, standard three axioms):
`U := ι.range` open by `hι.isOpen_range`; `K := fixedField U`; `K.fixingSubgroup = U` by
`fixingSubgroup_fixedField ⟨U, Subgroup.isClosed_of_isOpen _ hUopen⟩`; `FiniteDimensional ℚ_[2] K` by
`(InfiniteGalois.isOpen_iff_finite K).mp` (or degree `= U.index` by `finrank_eq_fixingSubgroup_index`);
`σ := IntermediateField.inclusion (…mem_separableClosure_iff… Algebra.IsSeparable.isSeparable …) : K →ₐ[ℚ_[2]] SeparableClosure ℚ_[2]`;
`(absoluteGaloisGroupExtend ℚ_[2] K σ).range = K.fixingSubgroup` (Shapiro proof generalized); then
`e := (⟨ι, hι.continuous⟩ : G →ₜ* AbsGalQ2).equivRangeOfIsEmbedding hι.isEmbedding ≪≫ (absoluteGaloisGroupExtendEquiv ℚ_[2] K σ hU).symm : G ≃ₜ* Field.absoluteGaloisGroup ↥K`
(`ContinuousMonoidHom.equivRangeOfIsEmbedding`, `TauCeti/Topology/Algebra/ContinuousMonoidHom/Basic.lean:190`),
with `absoluteGaloisGroupExtend ℚ_[2] K σ (e g) = ι g` (by `coe_absoluteGaloisGroupExtendEquiv_apply` and
`ContinuousMonoidHom.equivRangeOfIsEmbedding_apply`). The `MuN` compatibility then reads
`g • x = absoluteGaloisGroupExtend … (e g) • x`, the input to item 3.

## B11a: Hilbert-symbol norm criterion

### gq2 side
```lean
hilbertSymbol_normCriterion_finiteDyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m) :
    ∀ a b : (↥k)ˣ,
      kummerClassK k a ⌣[htriv] kummerClassK k b = 0 ↔
        ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2
```
(`GQ2/Foundations/LiteratureInputs.lean:100-105`). Uses `GQ2.kummerClassK` (`GQ2/EvensKahn.lean:437`:
`H1mk _ _ ⟨fun g ↦ Kummer.kummerCocycleFun (sqrtCl ↑↑a) ↑g, _⟩ : H1 k.fixingSubgroup (ZMod 2)`), `sqrtCl` (`:414`),
`Kummer.kummerCocycleFun α g := if g • α = α then 0 else 1` (`GQ2/Kummer.lean:93`), `⌣[htriv]` =
`GQ2.trivialCupPairing _ _ htriv` = `cup11 AddMonoidHom.mul _` (`GQ2/Demushkin.lean:95, :104`; `GQ2/CupProduct.lean:153`),
`GQ2.ContCoh.H1/H2/H1mk` (`GQ2/Cohomology.lean:132, :141, :138`).

### Tau Ceti sources
- `TauCeti.cup_kummerClass_eq_zero_iff` — `TauCeti.FieldTheory.GaloisCohomology.MuTwo.CupNorm` (`FieldTheory/GaloisCohomology/MuTwo/CupNorm.lean:100`)
  ```lean
  @TauCeti.cup_kummerClass_eq_zero_iff : ∀ {K : Type} [inst : Field K] [inst_1 : Invertible 2] (a b : Kˣ),
    (((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup K)).cup 1 1) (TauCeti.kummerClass a))
          (TauCeti.kummerClass b) =
        0 ↔
      ∃ x y, ↑b = x ^ 2 - ↑a * y ^ 2
  ```
  At `K = ↥k`: `Invertible (2 : ↥k)` is **not** synthesized; supply `invertibleOfNonzero two_ne_zero` (`CharZero ↥k` =
  `IntermediateField.charZero k`). The RHS is then syntactically gq2's RHS (smoke `example`, tested).
- `TauCeti.galoisF2Iso_inv_kummerClass` — `TauCeti.FieldTheory.GaloisCohomology.MuTwo.KummerCharacter` (`…/MuTwo/KummerCharacter.lean:269`)
  ```lean
  @TauCeti.galoisF2Iso_inv_kummerClass : ∀ {K : Type u_1} [inst : Field K] {L : Type u_1} [inst_1 : Field L]
    [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L] [inst_4 : Invertible 2] (σ : L →ₐ[K] SeparableClosure K)
    (a : Lˣ) (r : SeparableClosure K) (hr : r ^ 2 = σ ↑a),
    (CategoryTheory.ConcreteCategory.hom (TauCeti.galoisF2Iso K L σ 1).inv) (TauCeti.kummerClass a) =
      TauCeti.ContCohomology.homClass (↥↑(TauCeti.galoisSubgroup K L σ)) (TauCeti.galoisKummerCharacter σ a r hr) ⋯
  ```
  Tested at `K = ℚ_[2]`, `L = ↥k`, `σ = kEmb k`, `r = ⟨sqrtCl ↑↑a, _⟩`.
- `TauCeti.galoisF2Iso` (`FieldTheory/GaloisCohomology/Restriction.lean:62`, `K L : Type u` same universe), `galoisF2Iso_inv`
  (`:78`), `galoisF2Iso_inv_cup` (`:95`); `TauCeti.trivialF2Iso` (`RepresentationTheory/Homological/ContCohomology/TrivialF2.lean:395`)
  with `trivialF2Iso_hom` (`:413`, `= trivialF2Map ↑e.symm n`), `trivialF2Map` (`:300`), `trivialF2Map_cup`
  (`…/Cup/TrivialF2/Basic.lean:116`); `TauCeti.ContCohomology.homClass` (`…/TrivialF2/Character.lean:103`, class of a continuous
  `H →* Multiplicative (ZMod 2)`), `homClass_def` (`:109`, `= eqToHom ∘ explicitH1AddEquivContinuousCohomology (evensHomCocycle α hα)`),
  `homClass_inj` (`:178`, `H` explicit), `trivialF2Map_homClass` (`:208`); `rootSign_of_apply_eq/_ne`
  (`…/MuTwo/KummerCharacter.lean:78, :84`; `rootSign` itself is not exposed). Verbatim in the `#check` output of `Smoke.lean`.
- For A2: `TauCeti.trivialF2TopPairing_cup_one_one_explicitH1` (`…/Cup/TrivialF2/Basic.lean:256`, needs
  `[LocallyCompactSpace G]`): on explicit classes, cup = `explicitCup11 G _ _ _ (trivialF2Pairing G)`;
  `explicitH1AddEquivContinuousCohomology` / `explicitH2AddEquivContinuousCohomology`
  (`…/ContCohomology/CohomologyComparison.lean:134, :232`, namespace `TauCeti.ContCohomology`; H2 needs
  `[LocallyCompactSpace G]`); `trivialF2 G` has carrier `ULift.{u} (ZMod 2)` (`TrivialF2.lean:92-96`).

### Translation
- Tau Ceti half done (`artifacts/galois/a1_b11a_prototype.lean`, sorry-free, standard axioms). With `G := ↥k.fixingSubgroup` and
  `gq2KummerChar k a : G →* Multiplicative (ZMod 2)`, `g ↦ ofAdd (kummerCocycleFun (sqrtCl ↑↑a) ↑g)`:
  ```lean
  theorem cup_gq2KummerChar_eq_zero_iff (a b : (↥k)ˣ) :
      letI : Invertible (2 : k) := invertibleOfNonzero two_ne_zero
      (TauCeti.trivialF2TopPairing k.fixingSubgroup).cup 1 1
          (TauCeti.ContCohomology.homClass _ (gq2KummerChar k a) (continuous_gq2KummerChar k a))
          (TauCeti.ContCohomology.homClass _ (gq2KummerChar k b) (continuous_gq2KummerChar k b)) = 0 ↔
        ∃ x y : ↥k, (b : ↥k) = x ^ 2 - (a : ↥k) * y ^ 2
  ```
  Proof: `Φ n := (galoisF2Iso ℚ_[2] k (kEmb k) n).symm ≪≫ trivialF2Iso (rho k).symm n`. Then
  `Φ 1 (kummerClass c) = homClass G (gq2KummerChar k c)` by `galoisF2Iso_inv_kummerClass`, `trivialF2Map_homClass`,
  `homClass_inj`, and the pointwise identity `rootSign r (rho g) = kummerCocycleFun (sqrtCl ↑↑c) ↑g`
  (`coe_absoluteGaloisGroupRestrictEquiv_apply`). `Φ` commutes with cup (`galoisF2Iso_inv_cup`, `trivialF2Map_cup`), and
  `Φ 2` is injective. No `Field.absoluteGaloisGroup ↥k` and no local-field instance is needed. The plan's route through
  `fixingSubgroup ≃ₜ* Field.absoluteGaloisGroup ↥k` would also work, but it needs one more transport.
- **What A2 must supply** (at `G = ↥k.fixingSubgroup`, `M = ZMod 2`, trivial action, `htriv` given):
  (i) `ψ1 : GQ2.ContCoh.H1 G (ZMod 2) ≃+ continuousCohomology 1 (TauCeti.trivialF2 G)` with
  `ψ1 (H1mk G (ZMod 2) z) = TauCeti.ContCohomology.homClass G α hα` whenever `∀ g, z.1 g = Multiplicative.toAdd (α g)`
  (then `ψ1 (kummerClassK k a) = homClass G (gq2KummerChar k a) _` holds by unfolding, since `kummerClassK` is exposed);
  (ii) `ψ2 : GQ2.ContCoh.H2 G (ZMod 2) ≃+ continuousCohomology 2 (TauCeti.trivialF2 G)` (needs
  `[LocallyCompactSpace G]`: `compactSpace_fixingSubgroup` in the prototype);
  (iii) `ψ2 (x ⌣[htriv] y) = (TauCeti.trivialF2TopPairing G).cup 1 1 (ψ1 x) (ψ1 y)`. The cup lands in degree `1 + 1`.
  Tau Ceti itself needed `convert … using 2` for `1 + 1` vs `2` (`Cup/TrivialF2/Basic.lean:275-277`), so state (iii)
  with ψ2 at `1 + 1` or with `degreeCast`. Coefficients: gq2 `ZMod 2` vs Tau Ceti `ULift.{0} (ZMod 2)` (`trivialF2Equiv`).
  The cochain formulas agree under trivial action (gq2 `cup11Fun a b (g,h) = a g * (g • b h)`, Tau Ceti `a g * b h`).
  Then B11a = `(map_eq_zero_iff ψ2 …).symm.trans` (rewrite by (iii), (i)) `cup_gq2KummerChar_eq_zero_iff k a b`.
- `B11a.lean` should import only the light modules the prototype uses (`AbsoluteGaloisGroup.{Basic,FiniteExtension}`,
  `MuTwo.{CupNorm,KummerCharacter}`, `GaloisCohomology.Restriction`, plus A1/A2). Plan claims confirmed: no local
  hypothesis, any field with `Invertible 2`, `K : Type`.

## B9: the relative Stiefel-Whitney identity

### gq2 side

`LiteratureInputs.relativeStiefelWhitney_dyadic` (`GQ2/Foundations/LiteratureInputs.lean:69-96`), verbatim:

```lean
  relativeStiefelWhitney_dyadic
      (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
      (d : (↥k)ˣ) (δ β : AlgebraicClosure ℚ_[2])
      (hδ : δ ^ 2 = ((d : ↥k) : AlgebraicClosure ℚ_[2]))
      (hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2)
      (a : (↥(quadExt k δ))ˣ)
      (hβ : β ^ 2 = ((a : ↥(quadExt k δ)) : AlgebraicClosure ℚ_[2]))
      (hβ0 : β ≠ 0)
      (hidx : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
          k.fixingSubgroup).index = 2)
      (s : k.fixingSubgroup)
      (hs : s ∉ (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf k.fixingSubgroup)
      (htriv : ∀ (g : k.fixingSubgroup) (m : ZMod 2), g • m = m)
      (hUo : IsOpen (((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
          k.fixingSubgroup : Subgroup k.fixingSubgroup) : Set k.fixingSubgroup))
      (α : ((MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf
          k.fixingSubgroup) → ZMod 2)
      (hαdef : ∀ g, α g = Kummer.kummerCocycleFun β
          ((g : k.fixingSubgroup) : Kummer.GaloisGroup ℚ_[2]))
      (hα : ∀ g h, α (g * h) = α g + α h)
      (hαc : Continuous α) :
      (swOne k (traceFormTwisted k δ ↑a) =
          swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc) ∧
        (swTwo k htriv (traceFormTwisted k δ ↑a) =
          swTwo k htriv (traceFormOne k δ) +
            swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc +
              evensNormH2 htriv hUo hidx hs α hα hαc)
```

Shape: base `↥k` (a finite `IntermediateField ℚ_[2] ℚ̄₂`); group `G := ↥k.fixingSubgroup ≤ Kummer.GaloisGroup ℚ_[2] = ℚ̄₂ ≃ₐ[ℚ_[2]] ℚ̄₂` (`GQ2/Kummer.lean:68`), acting on `ℚ̄₂`; `U := (stabilizer δ).subgroupOf G` (implicit in `corH1`/`evensNormH2`, fixed by `hUo`/`hidx`/`hs`); no embedding `σ`. Degree-2 summand order: `w₂(1) + w₁(1) ⌣ cor + N^Ev`.

- `GQ2.swOne k Q : H1 ↥k.fixingSubgroup (ZMod 2)` (`GQ2/StiefelWhitney.lean:413`): `if h : ∃ x y, IsDiagonalization k Q x y then kummerClassK k h.choose + kummerClassK k h.choose_spec.choose else 0`. `GQ2.swTwo k htriv Q` (`:423`): the same with `⌣[htriv]`. They are binary-only, with value `0` otherwise. `diagForm k x y = weightedSumSquares ↥k ![x, y]` (`:82`), `IsDiagonalization k Q x y := Q.Equivalent (diagForm k x y)` (`:92`), `exists_isDiagonalization` (`:247`, needs `finrank = 2` and `(associated Q).SeparatingLeft`). `swTwo_diag` (`:443`) needs `hnorm` (= B11a), but `dif_pos` does not (see Translation).
- `GQ2.quadExt k δ := IntermediateField.adjoin ↥k {δ} : IntermediateField ↥k ℚ̄₂` (`GQ2/TraceForm.lean:68`); `finiteDimensional_quadExt k d hδ` (`:79`) is a theorem, not an instance. `traceFormOne k δ := toQuadraticMap (Algebra.traceForm ↥k ↥(quadExt k δ))` (`:142`). `traceFormTwisted k δ a := toQuadraticMap ((traceForm).compl₁₂ (mulLeft ↥k a) id)` (`:153`), with value `Tr(a * z * z)` (`:158`). `traceFormOne_isDiagonalization k d hδ hdeg` gives `⟨2, 2d⟩` (`:164`).
- `GQ2.evensAux U s α x = if x ∈ U then α x else if x*s ∈ U then α (x*s) else 0` (`GQ2/EvensKahn.lean:123`); `bS U s α x = evensAux U s α (s⁻¹*x)` (`:127`); `corFun = evensAux + bS` (`:231`); `corH1 … := H1mk ⟨corFun U s α, _⟩` (`:261`). `evensNormFun` (`:277`) is eq. (98): `if γ ∈ U then b₁γ·b_sη else b₁γ·b₁η + b₁η·b_sη`; `evensNormH2 … := H2mk ⟨evensNormFun U s α, _⟩` (`:332`).
- `kummerClassK k a` (`:437`) is the class of `g ↦ kummerCocycleFun (sqrtCl a) g`, where `kummerCocycleFun β g = if g • β = β then 0 else 1` (`GQ2/Kummer.lean:93`). The cup is `x ⌣[htriv] y = trivialCupPairing htriv x y = cup11 AddMonoidHom.mul`, with cochain `(g,h) ↦ x g * (g • y h)` (`GQ2/Demushkin.lean:95,104`, `GQ2/CupProduct.lean:49`).

### Tau Ceti sources

All are tested by `#check` in `GQ2/TauCeti/Smoke.lean`: 80 Tau Ceti and 17 gq2 declarations. The full signatures are in the `#check` output of `Smoke.lean`. Here are the main ones, verbatim.

- `TauCeti.sw1Class_formClass_traceTransfer_smul_sq`, module `…StiefelWhitney.Transfer` (`TauCeti/FieldTheory/QuadraticForm/StiefelWhitney/Transfer.lean:91`)
  ```lean
  ∀ {K L : Type u_1} [inst : Field K] [inst_1 : Field L] [inst_2 : Algebra K L] [inst_3 : FiniteDimensional K L]
    [inst_4 : Invertible 2] [inst_5 : Invertible 2] (σ : L →ₐ[K] SeparableClosure K) (a : Lˣ)
    (ha : QuadraticMap.Nondegenerate) (h1 : QuadraticMap.Nondegenerate),
    TauCeti.sw1Class (TauCeti.formClass (QuadraticMap.traceTransfer K (↑a • QuadraticMap.sq)) ha) =
      TauCeti.sw1Class (TauCeti.formClass (QuadraticMap.traceTransfer K QuadraticMap.sq) h1) +
        (ConcreteCategory.hom (TauCeti.galoisCor K L σ 1)) (TauCeti.kummerClass a)
  ```
- `TauCeti.sw2Class_formClass_traceTransfer_smul_sq`, module `…StiefelWhitney.QuadraticExtension` (`…/StiefelWhitney/QuadraticExtension.lean:209`)
  ```lean
  ∀ {K L : Type} [inst : Field K] [inst_1 : Invertible 2] [inst_2 : Field L] [inst_3 : Algebra K L]
    [inst_4 : FiniteDimensional K L] [inst_5 : Invertible 2] (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) (a : Lˣ) (ha : QuadraticMap.Nondegenerate) (h1 : QuadraticMap.Nondegenerate),
    TauCeti.sw2Class (TauCeti.formClass (QuadraticMap.traceTransfer K (↑a • QuadraticMap.sq)) ha) =
      TauCeti.sw2Class (TauCeti.formClass (QuadraticMap.traceTransfer K QuadraticMap.sq) h1) +
          TauCeti.galoisEvens K L σ hfin (TauCeti.kummerClass a) +
        (((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup K)).cup 1 1)
            (TauCeti.sw1Class (TauCeti.formClass (QuadraticMap.traceTransfer K QuadraticMap.sq) h1)))
          ((ConcreteCategory.hom (TauCeti.galoisCor K L σ 1)) (TauCeti.kummerClass a))
  ```
- **Better (use these):** `TauCeti.sw1_eq_add_galoisCor_of_equivalent_traceTransfer` (`Transfer.lean:122`) and `TauCeti.sw2_eq_add_galoisEvens_add_cup_of_equivalent_traceTransfer` (`QuadraticExtension.lean:251`). These are the same identities on diagonal presentations. They need no `Nondegenerate` and no `formClass`.
  ```lean
  ∀ {K L : Type} [inst : Field K] [inst_1 : Invertible 2] [inst_2 : Field L] [inst_3 : Algebra K L]
    [inst_4 : FiniteDimensional K L] [inst_5 : Invertible 2] (σ : L →ₐ[K] SeparableClosure K)
    (hfin : Module.finrank K L = 2) (a : Lˣ) {m n : ℕ} {t : Fin m → Kˣ} {b : Fin n → Kˣ},
    QuadraticMap.Equivalent (QuadraticMap.traceTransfer K QuadraticMap.sq)
        (QuadraticMap.weightedSumSquares K fun i => ↑(t i)) →
      QuadraticMap.Equivalent (QuadraticMap.traceTransfer K (↑a • QuadraticMap.sq))
          (QuadraticMap.weightedSumSquares K fun i => ↑(b i)) →
        TauCeti.sw2 b =
          TauCeti.sw2 t + TauCeti.galoisEvens K L σ hfin (TauCeti.kummerClass a) +
            (((TauCeti.trivialF2TopPairing (TauCeti.AbsoluteGaloisGroup K)).cup 1 1) (TauCeti.sw1 t))
              ((ConcreteCategory.hom (TauCeti.galoisCor K L σ 1)) (TauCeti.kummerClass a))
  ```
  The sw1 version has `{K L : Type u_1}`, no `hfin`, and the conclusion `TauCeti.sw1 b = TauCeti.sw1 t + (galoisCor K L σ 1) (kummerClass a)`. For two coefficients, `sw1_fin_two : sw1 w = kummerClass (w 0) + kummerClass (w 1)` and `sw2_fin_two : sw2 w = (cup 1 1) (kummerClass (w 0)) (kummerClass (w 1))` (`StiefelWhitney/Basic.lean:183,189`). `sw1`/`sw2` themselves are at `:78,:84`.
- `TauCeti.sw1Class : {K : Type u_1} → [Field K] → [Invertible 2] → TauCeti.RegularFormClass K → ↑(continuousCohomology 1 (TauCeti.trivialF2 (TauCeti.AbsoluteGaloisGroup K))).toModuleCat` (`StiefelWhitney/Class.lean:99`). `TauCeti.sw2Class` is the same with `{K : Type}` and degree 2 (`:190`). Both are `RegularFormClass.liftDiagonal (fun p => swᵢ p.2) …`. `sw{1,2}Class_formClass Q hQ w (h : Q.Equivalent (weightedSumSquares K fun i => ↑(w i))) : sw{1,2}Class (formClass Q hQ) = sw{1,2} w` (`:111,:208`).
- `TauCeti.RegularFormClass : (K : Type u_1) → [Field K] → Type u_1` is `Quotient (regularFormSetoid K)` (`LinearAlgebra/QuadraticForm/RegularFormClass/Basic.lean:209`). `TauCeti.formClass : … [Invertible 2] {V} [AddCommGroup V] [Module K V] [FiniteDimensional K V] (Q : QuadraticForm K V) → QuadraticMap.Nondegenerate → RegularFormClass K` (`:653`). `TauCeti.RegularFormClass.liftDiagonal {α} (f : RegularFormPresentation K → α) (hperm) (hbin) (hone) : RegularFormClass K → α` (`…/RegularFormClass/Descent.lean:116`).
- `QuadraticMap.traceTransfer : (K : Type u_1) → {L V} → [CommRing K] → [CommRing L] → [Algebra K L] → [AddCommMonoid V] → [Module L V] → [Module K V] → [IsScalarTower K L V] → QuadraticForm L V → QuadraticForm K V`. It is in the root `QuadraticMap` namespace, defined by Tau Ceti (`LinearAlgebra/QuadraticForm/Transfer/Basic.lean:139`), and **not exposed**. Related lemmas: `traceTransfer_apply : (traceTransfer K Q) x = (Algebra.trace K L) (Q x)`; `traceTransfer_sq : traceTransfer K QuadraticMap.sq = LinearMap.BilinMap.toQuadraticMap (Algebra.traceForm K L)` (`:151`); `nondegenerate_traceTransfer_iff` (`:270`, needs `Algebra.IsSeparable`); `QuadraticMap.nondegenerate_smul_sq : a ≠ 0 → (a • sq).Nondegenerate` (`…/QuadraticForm/Radical.lean:658`).
- `TauCeti.galoisSubgroup : (K) → [Field K] → (L) → [Field L] → [Algebra K L] → (L →ₐ[K] SeparableClosure K) → [FiniteDimensional K L] → OpenSubgroup (TauCeti.AbsoluteGaloisGroup K)` (`FieldTheory/Galois/AbsoluteGaloisGroup/FiniteExtension.lean:138`). It is `σ.fieldRange.fixingSubgroup`. Related: `galoisSubgroup_index : (↑(galoisSubgroup K L σ)).index = Module.finrank K L` (`:179`); `mem_galoisSubgroup_iff_apply_eq_of_finrank_eq_two : finrank K L = 2 → x ∉ Set.range (algebraMap K L) → (g ∈ galoisSubgroup K L σ ↔ g (σ x) = σ x)` (`:171`).
- `TauCeti.galoisCor : (K) → [Field K] → (L : Type u_1) → [Field L] → [Algebra K L] → (L →ₐ[K] SeparableClosure K) → [FiniteDimensional K L] → (n : ℕ) → continuousCohomology n (trivialF2 (AbsoluteGaloisGroup L)) ⟶ continuousCohomology n (trivialF2 (AbsoluteGaloisGroup K))` (`FieldTheory/GaloisCohomology/Corestriction/Basic.lean:75`). It is `(galoisF2Iso K L σ n).inv ≫ trivialF2CorMap (AbsoluteGaloisGroup K) ↑(galoisSubgroup K L σ) _ n` (`galoisCor_def`).
- `TauCeti.galoisEvens : (K) → … → (L →ₐ[K] SeparableClosure K) → [FiniteDimensional K L] → Module.finrank K L = 2 → ↑(continuousCohomology 1 (trivialF2 (AbsoluteGaloisGroup L))).toModuleCat → ↑(continuousCohomology 2 (trivialF2 (AbsoluteGaloisGroup K))).toModuleCat` (`FieldTheory/GaloisCohomology/EvensNorm.lean:84`). `galoisEvens_def` (`:92`) gives `= evensNormIndexTwo (galoisSubgroup K L σ) _ ((galoisF2Iso K L σ 1).inv x)`. Both maps are σ-independent: `galoisCor_embedding_independent` (`Corestriction/Basic.lean:176`) and `galoisEvens_embedding_independent` (`EvensNorm.lean:157`).
- `TauCeti.ContCohomology.evensNormIndexTwo_homClass : ∀ {G} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] (U : OpenSubgroup G) (hU : (↑U).index = 2) (α : ↥↑U →* Multiplicative (ZMod 2)) (hα : Continuous ⇑α), evensNormIndexTwo U hU (homClass (↥↑U) α hα) = graphClass U hU α hα` (`RepresentationTheory/Homological/ContCohomology/Evens/IndexTwoNorm.lean:89`)
- `TauCeti.ContCohomology.graphClass : {G} → … → [LocallyCompactSpace G] → (U : OpenSubgroup G) → (↑U).index = 2 → (α : ↥↑U →* Multiplicative (ZMod 2)) → Continuous ⇑α → ↑(continuousCohomology 2 (trivialF2 G)).toModuleCat` (`…/Evens/Class.lean:258`). Related: `graphClass_eq_evensGraphCochainClass U hU s hs α hα : graphClass U hU α hα = evensGraphCochainClass U s α hU hs hα` (`:265`), which holds for every `s ∉ U`; `evensGraphCochainClass_def`, which gives `= eqToHom.hom (explicitH2AddEquivContinuousCohomology G (trivialF2 G).V (evensGraphCocycle U s α hU hs hα))`.
- Bridges not named in the plan, which carry the field identities to cochains:
  - `TauCeti.galoisF2Iso_inv_kummerClass (σ) (a : Lˣ) (r) (hr : r ^ 2 = σ ↑a) : (galoisF2Iso K L σ 1).inv (kummerClass a) = homClass ↥↑(galoisSubgroup K L σ) (galoisKummerCharacter σ a r hr) _` (`…/MuTwo/KummerCharacter.lean:269`). Here `galoisKummerCharacter` is `γ ↦ ofAdd (rootSign r γ)` (`:243`) and `rootSign r g = if g r = r then 0 else 1` (`:73`).
  - `homClass_eq_evensHomCocycleAmbient` (`Evens/Identities.lean:87`), `trivialF2CorMap_explicitH1AddEquivContinuousCohomology` (`Corestriction/TrivialF2.lean:208`) and `explicitCor1_evensHomCocycleAmbient U hU s hs α hα : explicitCor1 … (evensHomCocycleAmbient U α hα) = evensCorCocycle U s α hU hs hα` (`Evens/Corestriction.lean:135`).
  - Cochain API: `evensB1_of_mem`, `evensB1_of_notMem`, `evensBs_apply`, `evensExtend_of_mem`, `evensExtend_of_notMem`, `evensCorCochain_apply`, `evensGraphCochain_of_mem`, `evensGraphCochain_of_notMem` (`Evens/Cochain.lean:245-416`); the defs `evensGraphCochain` (`:399`) and `evensCorCochain` (`:238`) are not exposed.
  - Naturality: `evensGraphCochain_comap`, `evensB1_comap`, `evensBs_comap` (`Cochain.lean:679-693`); `trivialF2Map_graphClass (φ : H →ₜ* G) U hU hφU α hα` (`Evens/Naturality.lean:72`, needs `G H` in one universe with `LocallyCompactSpace`); `trivialF2Map_evensNormIndexTwo` (`:141`).
  - Separable closures: `separableClosureRingEquiv K L σ : SeparableClosure L ≃+* SeparableClosure K` (`AbsoluteGaloisGroup/Extension.lean:70`); `absoluteGaloisGroupEquivFixingSubgroup K L σ : AbsoluteGaloisGroup L ≃ₜ* ↥σ.fieldRange.fixingSubgroup` (`:181`, for any `L`, not only finite ones) with `_apply : ↑(e g) y = sCRE (g (sCRE.symm y))`.
- `TauCeti.trivialF2TopPairing_cup_comm : ∀ (G) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (m n : ℕ) (x : cohomF2 G m) (y : cohomF2 G n), ((trivialF2TopPairing G).cup m n x) y = (ConcreteCategory.hom (ContinuousCohomology.degreeCast (trivialF2 G) ⋯).hom) (((trivialF2TopPairing G).cup n m y) x)` (`…/Cup/TrivialF2/Basic.lean:137`). It exists but B9 does not need it.

**Instances at `K = ↥k`, `L = ↥(quadExt k δ)`** (all tested with `#synth`):
- `Invertible (2 : ↥k)` and `Invertible (2 : L)` synthesize as `invertibleTwo`.
- `Field L` is `(quadExt k δ).toField`, `Algebra ↥k L` is `IntermediateField.instAlgebraSubtypeMem_1`, and `IsScalarTower ↥k L L` is `IsScalarTower.right`.
- `Algebra.IsSeparable ↥k L` comes from `infer_instance` once `FiniteDimensional` is present.
- `CompactSpace (AbsoluteGaloisGroup ↥k)` is `instCompactSpaceAlgEquiv_tauCeti`, `TotallyDisconnectedSpace` is `TotallySeparatedSpace.totallyDisconnectedSpace`, and `IsTopologicalGroup` is `instIsTopologicalGroupAlgEquiv`.
- `LocallyCompactSpace (AbsoluteGaloisGroup ↥k)` (`WeaklyLocallyCompactSpace.locallyCompactSpace`) **times out at the default `synthInstance.maxHeartbeats` 20000** and succeeds at 400000.

The adapter must supply:
- `FiniteDimensional ↥k L`, by `haveI := finiteDimensional_quadExt k d hδ`.
- `σ`.
- For the explicit-model statements, `attribute [local instance] TopRep.distribMulAction` and `local instance : ContinuousSMul G (trivialF2 G).V := (isSmoothDiscrete_trivialF2 G).continuousSMul`. Every Tau Ceti `Evens` file declares the latter locally; tested.
- `LocallyCompactSpace ↥k.fixingSubgroup` does **not** synthesize, so any route through `trivialF2Map_graphClass` must supply it. It follows from `CompactSpace` via `isCompact_iff_compactSpace.mp (IntermediateField.fixingSubgroup_isClosed k).isCompact` (tested).

### Translation

1. **Use the diagonal-presentation theorems, not `formClass`.** gq2's `swOne`/`swTwo` are `dite` on a chosen diagonalization, so `dif_pos h` gives `[x₀]+[y₀]` and `[x₀]⌣[y₀]` at the chosen pair, with `h.choose_spec.choose_spec : IsDiagonalization k Q x₀ y₀` (tested). Existence for `Tr⟨1⟩` comes from `traceFormOne_isDiagonalization k d hδ hdeg`. Existence for `Tr⟨a⟩` comes from `exists_isDiagonalization k _ hdeg`, using `(associated (traceFormTwisted k δ ↑a)).SeparatingLeft` from `(nondegenerate_associated_iff.mpr ((nondegenerate_traceTransfer_iff _).2 (nondegenerate_smul_sq a.ne_zero))).1` (tested). Then `IsDiagonalization k Q x y ↔ Q.Equivalent (weightedSumSquares ↥k fun i => ↑(![x, y] i))`, since `diagForm k x y = weightedSumSquares ↥k (fun i => ↑(![x,y] i))` by `ext; simp [diagForm, weightedSumSquares_apply, Units.smul_def]` (tested). Feed the result to the two `…_of_equivalent_traceTransfer` theorems and finish with `sw1_fin_two`/`sw2_fin_two` (a full instantiation at `K = ↥k`, `L = ↥(quadExt k δ)` elaborates in `GQ2/TauCeti/Smoke.lean`). **This makes the B9 adapter independent of B11a (`hnorm`)**, which `swTwo_diag` would need. The plan's mapping "`swOne k Q = sw1Class (formClass Q _)`" is correct but unnecessary.
2. **Trace forms** (plan claim confirmed, though neither identity is `rfl`, because `traceTransfer` is not exposed).
   - `traceFormOne k δ = QuadraticMap.traceTransfer ↥k (QuadraticMap.sq (R := L) (A := L))` is `QuadraticMap.traceTransfer_sq.symm`.
   - `traceFormTwisted k δ a = traceTransfer ↥k (a • sq)` is `ext z; rw [traceFormTwisted_apply, traceTransfer_apply, smul_apply, sq_apply, smul_eq_mul, mul_assoc]`; the point is `Tr(a*z*z)` against `Tr(a*(z*z))`. Both are tested.
3. **`↥(quadExt k δ)` needs no identification**: Tau Ceti's `L` is any `Type` field, so `L := ↥(quadExt k δ)` directly. Tau Ceti's `hfin` is gq2's `hdeg` verbatim (the same type; tested). Universes are fine: `QuadraticExtension.lean` wants `K L : Type`, and `↥k : Type`.
4. **`σ` and `r` (the hardest seam; A1).** gq2 has no `σ`, and its `G_k` acts on `ℚ̄₂`, while Tau Ceti's `AbsoluteGaloisGroup ↥k` acts on `SeparableClosure ↥k`. A1's `Φ : ↥k.fixingSubgroup ≃ₜ* AbsoluteGaloisGroup ↥k` must be conjugation by a ring iso `e` (`Φ g y = e⁻¹ (g (e y))`). The natural choice is `absoluteGaloisGroupEquivFixingSubgroup ℚ_[2] ↥k σₖ` with `σₖ : ↥k ↪ SeparableClosure ℚ_[2]` (which is `⊤` in char 0), conjugating by `separableClosureRingEquiv ℚ_[2] ↥k σₖ`, followed by `absoluteGaloisGroupRestrictEquiv ℚ_[2]`. Then:
   - `σ y := e⁻¹ y` is `↥k`-linear (`separableClosureRingEquiv_symm_apply_eq_algebraMap`).
   - `Φ g ∈ galoisSubgroup ↥k L σ ↔ Φ g (σ δ') = σ δ' ↔ g δ = δ`, using `mem_galoisSubgroup_iff_apply_eq_of_finrank_eq_two` with `δ' = AdjoinSimple.gen ↥k δ ∉ range (algebraMap)` from `hdeg` (tested). So `Φ(U) = galoisSubgroup ↥k L σ`, and `Φ s ∉ galoisSubgroup` by `hs`.
   - `r := e⁻¹ β`, `hr` comes from `hβ`, and `rootSign r (Φ g) = kummerCocycleFun β g = α g` (`hαdef`). `hβ0`, `hidx` and `hUo` are not needed on the Tau Ceti side, because the index comes from `galoisSubgroup_index` and `hdeg`.
5. **`corH1` against `galoisCor`** (plan claim confirmed).
   - Tau Ceti side, tested in `GQ2/TauCeti/Smoke.lean`: `galoisCor ↥k L σ 1 (kummerClass a) = eqToHom.hom (explicitH1AddEquivContinuousCohomology G (trivialF2 G).V (evensCorCocycle (galoisSubgroup ↥k L σ) s' α' _ hs' _))` for every `s' ∉ G_L`, with `α' = galoisKummerCharacter σ a r hr`. The proof is `rw [galoisCor_def, comp_apply, galoisF2Iso_inv_kummerClass, homClass_eq_evensHomCocycleAmbient, trivialF2CorMap_explicitH1AddEquivContinuousCohomology, explicitCor1_evensHomCocycleAmbient]`.
   - gq2 side, tested on any group: `corFun U s α = evensCorCochain U s α'` pointwise, given `toAdd (α' u) = α u`.
   - What remains is A2: its explicit-H1 iso must be natural along `Φ`, sending gq2's `H1mk ⟨f, _⟩` to the class of `trivialF2Equiv.symm ∘ f`. Pull back pointwise with `evensB1_comap`/`evensBs_comap`, or by direct case split.
   - The shortcut `galoisCor_kummerClass` (cor `(a)` = `(N a)`) does not help: gq2 has no `corH1 = kummerClassK (N a)`.
6. **`evensNormH2` against `galoisEvens`** (plan claim confirmed).
   - gq2's eq. (98) cocycle is Tau Ceti's `evensGraphCochain` verbatim: `evensNormFun U s α = evensGraphCochain U s α'` and `evensAux = evensB1`, `bS = evensBs` (tested).
   - Tau Ceti side (tested): `galoisEvens ↥k L σ hdeg (kummerClass a) = evensGraphCochainClass (galoisSubgroup ↥k L σ) s' α' _ hs' _`, by `galoisEvens_def`, `galoisF2Iso_inv_kummerClass`, `evensNormIndexTwo_homClass` and `graphClass_eq_evensGraphCochainClass`. Then `evensGraphCochainClass_def` reaches the explicit H2. Transport along `Φ` with `trivialF2Map_graphClass`, or pointwise with `evensGraphCochain_comap`.
   - Expect a dependent-type cast: `U'.comap Φ = U` holds as a propositional equality of subgroups, and `α'.comp (Φ.subgroupComap U')` must match `α` over it. The direct pointwise route (membership iff plus values) avoids the cast.
7. **Summand order and cup convention.**
   - Degree 1: both sides read `w₁(1) + cor (a)`.
   - Degree 2: gq2 is `w₂(1) + w₁(1) ⌣ cor + N`, Tau Ceti is `w₂(1) + N + w₁(1) ∪ cor`. Only the additive order differs, so `add_right_comm` fixes it.
   - The cup factors are in the same order (`w₁(Tr⟨1⟩)` left, `cor (a)` right), and both cochains are `(g,h) ↦ x g · y h` under trivial action (gq2 `cup11Fun`; Tau Ceti `cup11_homClass`, `…/Cup/TrivialF2/Inhomogeneous.lean:85`). So `trivialF2TopPairing_cup_comm` is not needed. If A2 is ever stated with swapped factors, that lemma applies, together with its `degreeCast (Nat.add_comm 1 1)`.
8. **Pitfalls met.**
   - `rfl`, `unfold` and `simp [def]` fail on the unexposed Tau Ceti defs (`traceTransfer`, `evensB1`, `evensBs`, `evensCorCochain`, `evensGraphCochain`); use their `_apply`/`_of_mem` lemmas.
   - `rw [hs2] at e2` (rewriting `sw2 ![u,v]` in the degree-2 identity) **times out** (whnf, 200000 heartbeats), while `simp only [hs2, hs1] at e2` works. Prefer `simp only` on these cohomology equations.
   - `LocallyCompactSpace` needs `synthInstance.maxHeartbeats 400000`; gq2's `StiefelWhitney`/`TraceForm` files already set this.

### Answers

- **Shapes.** gq2 works over `↥k` with group `↥k.fixingSubgroup` acting on `ℚ̄₂`, `U = (stab δ).subgroupOf`, no `σ`, `hdeg` and `hidx`. Tau Ceti works over any `K L : Type` with `G = AbsoluteGaloisGroup K` (on `SeparableClosure K`), an explicit `σ : L →ₐ[K] SeparableClosure K`, `G_L = galoisSubgroup K L σ`, and `hfin : finrank K L = 2` (= `hdeg`). `↥(quadExt k δ)` is used as `L` itself; only `ℚ̄₂ ≃ SeparableClosure ↥k` (A1) has to be identified. Evidence: `GQ2/TauCeti/Smoke.lean` instantiates both identities at `K = ↥k`, `L = ↥(quadExt k δ)`.
- **Summand order and cup.** They differ only additively (`add_right_comm`); the cup factor order and cochain convention agree.
- **`trivialF2TopPairing_cup_comm`.** It exists (`Cup/TrivialF2/Basic.lean:137`, with a `degreeCast`) and is not needed.

## B5: local reciprocity

Result: **closed in scratch.** A complete `localReciprocity_tauceti : GQ2.LocalReciprocity`, with
all ten fields including `norm_reciprocity`, elaborates with `#print axioms` = `[propext,
Classical.choice, Quot.sound]` (`artifacts/recip/draft_b5_b10.lean`, lines 26-139, about 115
lines). It imports only Tau Ceti modules and `GQ2.Reciprocity`, and uses none of A1, A2 or P1.

### gq2 side
- Field: `localReciprocity : LocalReciprocity` (`GQ2/Foundations/LiteratureInputs.lean:62`).
- `GQ2.LocalReciprocity` (`GQ2/Reciprocity.lean:225`), with these fields, verbatim:
  ```lean
  recip : ℚ_[2]ˣ →* AbsGalQ2ab
  continuous_recip : Continuous recip
  denseRange_recip : DenseRange recip
  nu_ur : AbsGalQ2ab →* Multiplicative ℤ_[2]
  continuous_nu_ur : Continuous nu_ur
  surjective_nu_ur : Function.Surjective nu_ur
  norm_reciprocity : ∀ (L : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
      [FiniteDimensional ℚ_[2] L] [IsGalois ℚ_[2] L]
      (hab : ∀ σ τ : (L ≃ₐ[ℚ_[2]] L), σ * τ = τ * σ),
      Function.Surjective ((restrictAb L hab).comp recip) ∧
        ((restrictAb L hab).comp recip).ker = normSubgroup L
  nu_ur_recip : ∀ x : ℚ_[2]ˣ,
      nu_ur (recip x) = Multiplicative.ofAdd ((-(v2 x) : ℤ) : ℤ_[2])
  chiCyc_recip_unit : ∀ u : ℤ_[2]ˣ, chiCycAb (recip (unitEmbed u)) = u⁻¹
  chiCyc_recip_uniformizer : chiCycAb (recip uniformizer) = 1
  ```
- Definitions used, all in `GQ2/Reciprocity.lean` unless noted:
  - `AbsGalQ2` (`GQ2/Statement.lean:40`) and `AbsGalQ2ab` `:110`, an `abbrev` for
    `Field.absoluteGaloisGroupAbelianization ℚ_[2]`.
  - `commClosure` `:117`, `toAb` `:121` (`QuotientGroup.mk' commClosure`).
  - `chiCyc` `:128`, `chiCycAb` `:144` (a `QuotientGroup.lift`), `chiCycAb_toAb` `:149`.
  - `v2` `:155` (`Padic.valuation`), `normSubgroup` `:161` (`(Units.map (Algebra.norm ℚ_[2])).range`).
  - `restrictHom` `:171`, `restrictAb` `:192`, `restrictAb_toAb` `:201` (proved by `rfl`).
  - `unitEmbed` `:209`, `uniformizer` `:216` (`Units.mk0 (2 : ℚ_[2]) _`).

### Tau Ceti sources
All paths are relative to `.lake/packages/TauCeti/TauCeti/`. The `#check` output is verbatim from
the `#check` output of `Smoke.lean`.
- `TauCeti.ClassFieldTheory.artinMap`, in `NumberTheory/ClassFieldTheory/Local/ArtinMap.lean:114`
  ```lean
  TauCeti.ClassFieldTheory.artinMap : (K : Type) → [inst : Field K] → [inst_1 : ValuativeRel K] →
      [inst_2 : TopologicalSpace K] → [IsNonarchimedeanLocalField K] → Kˣ →* Field.absoluteGaloisGroupAbelianization K
  ```
- `continuous_artinMap` (`:248`) and `denseRange_artinMap` (`:188`). Both are
  `∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
  with conclusions `Continuous ⇑(TauCeti.ClassFieldTheory.artinMap K)` and
  `DenseRange ⇑(TauCeti.ClassFieldTheory.artinMap K)`.
- `injective_artinMap` (`LocalExistence/ArtinMap.lean:113`) has the same binders plus
  `[CharZero K]`, and concludes `Function.Injective ⇑(TauCeti.ClassFieldTheory.artinMap K)`.
  gq2 does not need it.
- `TauCeti.unramifiedCoordinate` (`NumberTheory/LocalField/Unramified/Coordinate.lean:77`); its
  type ends in `Field.absoluteGaloisGroupAbelianization K →ₜ* ↑TauCeti.zHat.toProfinite.toTop`.
  The namespace is `TauCeti`, not `TauCeti.ClassFieldTheory`. `unramifiedCoordinate_surjective` is
  at `:170` and `unramifiedCoordinate_mk` at `:88`.
- `TauCeti.ClassFieldTheory.unramifiedCoordinate_artinMap`, in `Local/Unramified.lean:407`
  ```lean
  ∀ (K : Type) [inst : Field K] [inst_1 : ValuativeRel K] [inst_2 : TopologicalSpace K] [inst_3 : IsNonarchimedeanLocalField K] (x : Kˣ),
    (TauCeti.unramifiedCoordinate K) ((TauCeti.ClassFieldTheory.artinMap K) x) = TauCeti.zHat.ofInt ((TauCeti.normalizedValuation K) x)
  ```
- `TauCeti.normalizedValuation` (`NumberTheory/LocalField/NormalizedValuation.lean:114`) has type
  `Kˣ →* Multiplicative ℤ`. Its bridge to gq2 is `Padic.toAdd_normalizedValuation_eq_valuation`
  (`LocalField/Padic.lean:86`; root namespace `Padic`):
  `∀ (p : ℕ) [Fact (Nat.Prime p)] (x : ℚ_[p]ˣ), Multiplicative.toAdd ((TauCeti.normalizedValuation ℚ_[p]) x) = (↑x).valuation`.
- The ℤ₂-reduction is `TauCeti.zHat.lift (Multiplicative.ofAdd (1 : ℤ_[2]))`
  (`Topology/Algebra/Group/Profinite/ZHat/Basic.lean:140`), with these lemmas:
  - `zHat.lift_ofInt` `:146`: `(TauCeti.zHat.lift a) (TauCeti.zHat.ofInt z) = a ^ Multiplicative.toAdd z`.
  - `zHat.lift_gen` `:154`.
  - `zHat.lift_ofAdd_one_padicInt_apply` (`ZHat/Component.lean:116`).
  - `zHat.component_surjective` `:136`, which gives surjectivity.
- Finite-layer reciprocity, all in `Local/Reciprocity.lean`:
  - `localArtinEquiv` `:83` has type
    `… (L : Type u_1) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] → (L →ₐ[K] SeparableClosure K) → Additive (Kˣ ⧸ TauCeti.normGroup K L) ≃+ Additive (Abelianization Gal(L/K))`.
  - `localArtinMap` `:118` has the same binders and ends in
    `→ Additive Kˣ →+ Additive (Abelianization Gal(L/K))`.
  - `localArtinMap_eq_zero_iff` `:137`:
    `(TauCeti.ClassFieldTheory.localArtinMap K L ι) (Additive.ofMul a) = 0 ↔ a ∈ TauCeti.normGroup K L`.
  - `ker_localArtinMap` `:142`: `(localArtinMap K L ι).ker = Subgroup.toAddSubgroup (TauCeti.normGroup K L)`.
  - `surjective_localArtinMap` `:149`: `Function.Surjective ⇑(TauCeti.ClassFieldTheory.localArtinMap K L ι)`.
- The bridge between the absolute and finite maps is
  `TauCeti.ClassFieldTheory.artinMap_restrict` (`Local/ArtinMap.lean:132`):
  ```lean
  ∀ … (L : Type u_1) [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (ι : L →ₐ[K] SeparableClosure K)
    (x : Kˣ) (σ : Field.absoluteGaloisGroup K), ↑σ = (TauCeti.ClassFieldTheory.artinMap K) x →
      (TauCeti.ClassFieldTheory.localArtinMap K L ι) (Additive.ofMul x) =
        Additive.ofMul (Abelianization.of (ι.restrictNormalHom ((TauCeti.absoluteGaloisGroupRestrictEquiv K) σ)))
  ```
  Supporting lemmas:
  - `mem_normGroup_of_mk_eq_artinMap_of_fixes` (`:165`). Its proof builds the `ι` for an
    `IntermediateField K (AlgebraicClosure K)`, and I copied that construction.
  - `TauCeti.coe_absoluteGaloisGroupRestrictEquiv_apply` (`FieldTheory/Galois/AbsoluteGaloisGroup/Basic.lean:339`).
  - `TauCeti.normGroup` (`RingTheory/Norm/Units.lean:87`) and `TauCeti.mem_normGroup_iff` `:93`:
    `x ∈ TauCeti.normGroup K L ↔ ∃ y, (Algebra.norm K) ↑y = ↑x`.
- The kernel description cited by the plan is
  `TauCeti.ClassFieldTheory.ClassFormation.ker_artinMap` (`Formation/ArtinMap.lean:210`, not
  `:159`): `(cf.artinMap L).ker = (L.normSubgroup F).toAddSubgroup`. It is abstract, sits at
  formation level, and is not needed; use `localArtinMap_eq_zero_iff`.
- The better source for the unit clause is
  `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic`
  (`Local/ExplicitCyclotomicSymbol/ArtinMap.lean:294`):
  ```lean
  ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (u : ℤ_[p]ˣ) (σ : Field.absoluteGaloisGroup ℚ_[p]),
    ↑σ = (TauCeti.ClassFieldTheory.artinMap ℚ_[p]) ((Units.map ↑(algebraMap ℤ_[p] ℚ_[p])) u) →
      (TauCeti.localCyclotomicCharacter p ℚ_[p]) σ = u⁻¹
  ```
  The plan's `localCyclotomicCharacter_artinMap_unit` (`:311`) concludes
  `Units.map … (localCyclotomicCharacter p F σ) = ((Units.map (Algebra.norm ℚ_[p])) u)⁻¹`. It
  needs `[Algebra ℚ_[p] F] [FiniteDimensional ℚ_[p] F] [ValuativeExtension ℚ_[p] F]` at
  `F = ℚ_[2]` and the hypothesis `valuation u = 1`. Avoid it.
- `TauCeti.ClassFieldTheory.localCyclotomicCharacter_artinMap_padic_uniformizer` (`Local/Cyclotomic.lean:364`):
  `∀ (p : ℕ) [Fact (Nat.Prime p)] (σ : Field.absoluteGaloisGroup ℚ_[p]), ↑σ = (TauCeti.ClassFieldTheory.artinMap ℚ_[p]) (Units.mk0 ↑p ⋯) → (TauCeti.localCyclotomicCharacter p ℚ_[p]) σ = 1`.
- `TauCeti.localCyclotomicCharacter_apply` (`FieldTheory/Galois/AbsoluteGaloisGroup/Cyclotomic/Character.lean:41`):
  `(TauCeti.localCyclotomicCharacter p K) σ = (cyclotomicCharacter (AlgebraicClosure K) p) σ.toRingEquiv`.
  This is the only bridge from gq2's `chiCyc`; `rfl` fails (see Answers).
- Instances at `K = ℚ_[2]`, all synthesized automatically (tested with `#synth`):
  - `ValuativeRel` from `Padic.instValuativeRel`.
  - `IsNonarchimedeanLocalField` from `instIsNonarchimedeanLocalFieldPadic`.
  - `CharZero` from `Padic.instCharZero 2`, and `Fact (Nat.Prime 2)`.
  - `TopologicalSpace ℚ_[2]` is gq2's metric topology: `continuous_artinMap ℚ_[2]` is accepted
    for the field `Continuous recip` (tested).
- Instances at a finite layer `↥L`. `localArtinMap` needs only the gq2 binders
  `[FiniteDimensional] [IsGalois]`, and no local-field instance on `L`. **But** instance search
  for `Algebra.IsSeparable ℚ_[2] ↥L` hits a deterministic timeout at 20000 heartbeats, so supply
  `haveI := IsGalois.to_isSeparable` (tested).

### Translation (all tested in `artifacts/recip/draft_b5_b10.lean`)
- **`recip := TauCeti.ClassFieldTheory.artinMap ℚ_[2]`**, with no cast. Continuity and density
  are the two Tau Ceti theorems verbatim. Both sides are arithmetic: `localArtinMap_uniformizer`
  sends a uniformizer to arithmetic Frobenius, and gq2's docstring fixes `rec(2)` as arithmetic.
  Plan confirmed.
- **`nu_ur := invMonoidHom.comp ((zHat.lift (ofAdd (1 : ℤ_[2]))).toMonoidHom.comp (unramifiedCoordinate ℚ_[2]).toMonoidHom)`.**
  Tau Ceti's coordinate is arithmetic (`unramifiedCoordinate_mk_eq_gen_iff`: coordinate `gen` ⇔
  arithmetic Frobenius lift), while gq2's `ν_ur` is geometric. The inversion supplies the sign.
  - `continuous_nu_ur`: `continuous_inv.comp (… .continuous.comp …)`.
  - `surjective_nu_ur`: `component_surjective` + `unramifiedCoordinate_surjective`.
  - `nu_ur_recip`: `simp only [nuUr, …, unramifiedCoordinate_artinMap, zHat.lift_ofInt, invMonoidHom_apply, v2, ← Padic.toAdd_normalizedValuation_eq_valuation]; rw [← ofAdd_zsmul, ← ofAdd_neg]; simp`.
  - Plan confirmed. It needs **no P1**: the plan's "use P1's `zHat` component" is unnecessary,
    because `zHat.lift` goes straight into `Multiplicative ℤ_[2]`.
- **`chiCyc_recip_unit`.** Take a lift `g` with `QuotientGroup.mk' commClosure g = artinMap (unitEmbed u)`,
  then `change chiCycAb (toAb g) = u⁻¹; rw [chiCycAb_toAb]` and
  `rwa [localCyclotomicCharacter_apply] at (localCyclotomicCharacter_artinMap_padic 2 u g hg)`.
  `hg` is accepted as is, because `unitEmbed u` is `rfl` to Tau Ceti's embedding. Correction to the
  plan: use `_padic`, not `_unit`, and A1's character identification is not needed.
- **`chiCyc_recip_uniformizer`.** The same proof with
  `localCyclotomicCharacter_artinMap_padic_uniformizer 2 g hg`. gq2's `uniformizer` is `rfl` to
  `Units.mk0 ((2:ℕ):ℚ_[2]) _`.
- **`norm_reciprocity`** (about 50 lines, `draft_b5_b10.lean:26-92`) does not need
  `localArtinEquiv` directly:
  1. Build `ι := L.val.codRestrict (separableClosure ℚ_[2] (AlgebraicClosure ℚ_[2])).toSubalgebra …`.
  2. Prove `ι.restrictNormalHom (absoluteGaloisGroupRestrictEquiv ℚ_[2] σ) = restrictHom L σ`
     with `AlgEquiv.ext`, `restrictNormalHom_commutes`, `coe_absoluteGaloisGroupRestrictEquiv_apply`,
     `AlgHom.coe_codRestrict` and `AlgEquiv.restrictNormal_commutes`.
  3. From `artinMap_restrict`, conclude
     `localArtinMap ℚ_[2] L ι (ofMul x) = ofMul (Abelianization.of (restrictAb L hab (artinMap x)))`.
  4. Use `hab` to define a local `CommGroup` structure on `L ≃ₐ[ℚ_[2]] L`, so that
     `Abelianization.equivOfComm` makes `Abelianization.of` injective.
  5. Surjectivity follows from `surjective_localArtinMap`.
  6. The kernel follows from `localArtinMap_eq_zero_iff`, together with
     `normSubgroup L = TauCeti.normGroup ℚ_[2] L` by `ext; rw [mem_normGroup_iff]; simp [normSubgroup, Units.ext_iff]`.

  The shape differs from Tau Ceti's: Tau Ceti's map is additive into `Additive (Abelianization Gal(L/K))`
  and takes `L : Type*` with an embedding `ι`, while gq2's is multiplicative into `Gal(L/K)` and
  takes `L` as an intermediate field with `hab`.
- **Pitfalls met:**
  - Tau Ceti definitions are not `@[expose]`d, so `rfl` cannot see through them.
  - The `Algebra.IsSeparable` instance search times out (fixed above).
  - `rw [coe_absoluteGaloisGroupRestrictEquiv_apply]` fails ("did not find pattern") when
    `σ : AbsGalQ2`, because of the `AbsGalQ2` vs `Gal(K̄/K)` instance path. Use
    `refine (coe_absoluteGaloisGroupRestrictEquiv_apply (K := ℚ_[2]) σ _).trans ?_` and write
    `DFunLike.coe (F := Gal(AlgebraicClosure ℚ_[2]/ℚ_[2])) σ`.
- **Ticket dependency:** B5 needs neither A1 nor A2 nor P1, so it can start right after T2.
- **Hardest seam:** `norm_reciprocity`, now closed.

### Answers
1. *Is `artinMap ℚ_[2]`'s target literally `AbsGalQ2ab`?* **Yes.**
   - `example : GQ2.AbsGalQ2ab = Field.absoluteGaloisGroupAbelianization ℚ_[2] := rfl` succeeds.
   - `recip := artinMap ℚ_[2]` typechecks with no cast.
   - `example (g : GQ2.AbsGalQ2) : GQ2.toAb g = (g : Field.absoluteGaloisGroupAbelianization ℚ_[2]) := rfl`
     succeeds, so Tau Ceti's `hσ : ↑σ = artinMap K x` hypotheses are exactly gq2 lifts.
   - All three are in `GQ2/TauCeti/Smoke.lean`.
2. *Conventions in `nu_ur_recip`.* Both `recip` and Tau Ceti's coordinate are arithmetic
   (`unramifiedCoordinate (artinMap x) = gen ^ v(x)`). gq2's `ν_ur` is geometric, so
   `nu_ur = (red ∘ unramifiedCoordinate)⁻¹`, giving `nu_ur (recip 2) = ofAdd (-1)`. Tested
   (`nu_ur_recip` closes).
3. *Finite-layer shape vs `norm_reciprocity`.* Explained above. The adapter needs about 50 lines
   and is tested. `localArtinEquiv` and `ClassFormation.ker_artinMap` are not needed.
4. *Failed definitional checks* (the first and third errors say the definition is not exposed;
   the second gives no note):
   - `GQ2.chiCyc = TauCeti.localCyclotomicCharacter 2 ℚ_[2] := rfl` fails on
     `TauCeti.localCyclotomicCharacter ↦ 7`. `MonoidHom.ext fun σ => (localCyclotomicCharacter_apply 2 ℚ_[2] σ).symm`
     works instead.
   - `chiCycAb = ↑(abelianizedLocalCyclotomicCharacter 2 ℚ_[2]) := rfl` fails. The pointwise
     equality on `toAb g` holds through `abelianizedLocalCyclotomicCharacter_mk` and `_apply`.
   - `normSubgroup L = TauCeti.normGroup ℚ_[2] L := rfl` fails on `TauCeti.normGroup ↦ 34`.
     `mem_normGroup_iff` works instead.

## B10: oriented tame quotient

Result: **closed in scratch.** A complete `tameQuotient_tauceti : OrientedTameQuotient localReciprocity_tauceti`
elaborates at the standard three axioms (`artifacts/recip/draft_b5_b10.lean`, lines 142-330, about 190 lines,
including the `Ttame` equivalence). It does **not** need P1.

### gq2 side
- Field: `tameQuotient : OrientedTameQuotient localReciprocity` (`GQ2/Foundations/LiteratureInputs.lean:98`).
- `TameQuotientData` (`GQ2/TameQuotient.lean:70`):
  ```lean
  W : Subgroup AbsGalQ2
  [normal : W.Normal]
  isClosed : IsClosed (W : Set AbsGalQ2)
  isProP : IsProP 2 W
  equiv : ContinuousMulEquiv (AbsGalQ2 ⧸ W) Ttame
  ```
- `OrientedTameQuotient (R : LocalReciprocity) extends TameQuotientData` (`:99`) adds:
  ```lean
  nuT_recip_unit : ∀ (u : ℤ_[2]ˣ) (g : AbsGalQ2),
      toAb g = R.recip (unitEmbed u) →
      nuT (equiv (QuotientGroup.mk g)) = 1
  nuT_recip_uniformizer : ∀ g : AbsGalQ2,
      toAb g = R.recip uniformizer →
      nuT (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹
  ```
- Definitions used:
  - `GQ2.IsProP` (`GQ2/MaxProP.lean:61`).
  - `tame_relation` (`GQ2/TameQuotient.lean:57`): `conjP tameTau tameSigma = tameTau ^ 2`.
  - In `GQ2/BoundaryFrame.lean`:
    - `tameWord` `:120` is `conjP (of 1) (of 0) * (of 1 ^ 2)⁻¹`, that is `σ⁻¹τσ(τ²)⁻¹`,
      with `conjP x g = g⁻¹ * x * g` (`GQ2/Words.lean:56`).
    - `Ttame` `:124`, `tameSigma` `:127`, `tameTau` `:131`.
    - `Ztwo` `:162`, `ztwoOne` `:165`.
    - `nuT` `:185`, with `nuT_tameSigma = ztwoOne` `:191` and `nuT_tameTau = 1` `:196`.
    - `presentationLift` `:101` and `presentationLift_mk` `:110`.
  - `FreeProfiniteGroup.homEquiv` and its `_apply`/`_symm_of` lemmas (`GQ2/FreeProfinite.lean:56-78`).
  - `quotientMk_surjective` (`GQ2/ProfiniteQuotient.lean:92`).

### Tau Ceti sources
Paths are relative to `.lake/packages/TauCeti/TauCeti/NumberTheory/LocalField/` unless they start
with `Topology/`.
- `TauCeti.wildInertiaSubgroup` (`WildInertia.lean:245`) has type
  `Subgroup (Field.absoluteGaloisGroup K)` under `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`.
  - `isClosed_wildInertiaSubgroup` `:279`: `IsClosed ↑(TauCeti.wildInertiaSubgroup K)`.
  - `wildInertiaSubgroup_normal` `:284` is an instance and synthesizes at `ℚ_[2]` (tested).
- `TauCeti.isProP_wildInertiaSubgroup` `:473`:
  ```lean
  ∀ (K : Type u_1) … (p : ℕ) [CharP (IsLocalRing.ResidueField ↥(ValuativeRel.valuation K).integer) p],
    TauCeti.IsProP p ↥(TauCeti.wildInertiaSubgroup K)
  ```
  `CharP 𝓀[ℚ_[2]] 2` does **not** synthesize (tested `#synth`). Supply
  `TauCeti.charP_residueField ℚ_[2] 2` (`AbsoluteRamificationIndex.lean:173`); its
  `[TauCeti.FinitePadicExtension ℚ_[2] 2]` synthesizes as
  `TauCeti.FinitePadicExtension.ofInstances ℚ_[2] 2` (tested).
- `TauCeti.isProP_iff` (`Topology/Algebra/Group/Profinite/ProP/Basic.lean:75`):
  `TauCeti.IsProP p G ↔ ∀ (U : OpenNormalSubgroup G), IsPGroup p (G ⧸ ↑U.toOpenSubgroup)`.
  `TauCeti.isProP_iff.mp` lands directly in `GQ2.IsProP` (tested). `Iff.rfl` fails (see Answers).
- `TauCeti.tameQuotient` (`Tame/Quotient.lean:144`) is an `abbrev` for
  `Field.absoluteGaloisGroup K ⧸ wildInertiaSubgroup K`. Related lemmas:
  - `toTameQuotient` `:159` and `toTameQuotient_apply` `:164`: `(TauCeti.toTameQuotient K) σ = ↑σ`.
  - `tameQuotientToZHat_toTameQuotient` `:404`, whose right-hand side is identical to that of
    `unramifiedCoordinate_mk` (`Unramified/Coordinate.lean:88`).
- `@TauCeti.tameQuotientGeometricEquiv` (`Tame/Geometric.lean:194`):
  ```lean
  {K : Type u_1} → … → {σ : Field.absoluteGaloisGroup K} → TauCeti.IsArithFrobeniusLift K σ →
    (τ : ↥(TauCeti.inertiaSubgroup K)) → (Subgroup.zpowers ((TauCeti.inertiaTameCharacter K) τ)).topologicalClosure = ⊤ →
      TauCeti.tameQuotient K ≃ₜ* TauCeti.IwasawaGroupGeometric K
  ```
- `TauCeti.IwasawaGroupGeometric` (`:61`) is `presentedProfiniteGroup (ULift.{u} (Fin 2)) {iwasawaRelatorGeometric K}`.
  - `iwasawaRelatorGeometric_def` (`:53`):
    `(of {down := 0})⁻¹ * of {down := 1} * of {down := 0} * (of {down := 1} ^ Nat.card 𝓀[K])⁻¹`.
  - `inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` (`:160`):
    `(iwasawaSigmaGeometric K)⁻¹ * iwasawaTauGeometric K * iwasawaSigmaGeometric K = iwasawaTauGeometric K ^ Nat.card 𝓀[K]`.
- `TauCeti.iwasawaCoordinateGeometric` (`:167`) has type
  `IwasawaGroupGeometric K →ₜ* ↑TauCeti.zHat.toProfinite.toTop`. Its values:
  - `_iwasawaSigmaGeometric` `:178`: `= TauCeti.zHat.gen⁻¹`.
  - `_iwasawaTauGeometric` `:184`: `= 1`.
  - `_tameQuotientGeometricEquiv` `:231`:
    `(iwasawaCoordinateGeometric K) ((tameQuotientGeometricEquiv hσ τ hτ) x) = (tameQuotientToZHat K) x`.
- `tameQuotientGeometricEquiv_toTameQuotient_frobenius` (`:199`):
  `(tameQuotientGeometricEquiv hσ τ hτ) ((toTameQuotient K) σ) = (iwasawaSigmaGeometric K)⁻¹`.
  It applies only to the *chosen* `σ`, so the adapter does not use it.
- Frobenius lift and tame generator:
  - `TauCeti.IsArithFrobeniusLift` (`Unramified/Inertia/Basic.lean:331`).
  - `TauCeti.exists_isArithFrobeniusLift` (`:384`): `∃ σ, TauCeti.IsArithFrobeniusLift K σ`.
  - `exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top` (`Tame/Quotient.lean:186`,
    not `:160`): `∃ τ, (Subgroup.zpowers ((TauCeti.inertiaTameCharacter K) τ)).topologicalClosure = ⊤`.
  - Both elaborate at `K = ℚ_[2]` with every instance found automatically (tested).
- `Padic.natCard_residueField` (`Padic.lean:155`; namespace `Padic`, not `TauCeti`):
  `Nat.card (IsLocalRing.ResidueField ↥(ValuativeRel.valuation ℚ_[p]).integer) = p`.
- Universal properties (`Topology/Algebra/Group/Profinite/`):
  - `presentedProfiniteGroup.lift` (`Presentation/Basic.lean:166`), into a `T1Space` monoid.
  - `presentedProfiniteGroup.lift_of` `:195`.
  - `presentedProfiniteGroup.hom_ext_of` `:214`, into a `T2Space` group.
  - `freeProfiniteGroup.lift` (`Free/Basic.lean:124`), into a compact totally disconnected group
    in the same universe as `X`.
  - `freeProfiniteGroup.lift_of` `:129`.
- Alternatives, not needed: `isArithFrobeniusLift_of_mk_eq_artinMap_uniformizer` and
  `mem_inertiaSubgroup_of_mk_eq_artinMap` (`ClassFieldTheory/Local/Unramified.lean:464, :456`).

### Translation (all tested in `artifacts/recip/draft_b5_b10.lean`)
- **Fields other than `equiv`:**
  - `W := TauCeti.wildInertiaSubgroup ℚ_[2]`.
  - `normal := TauCeti.wildInertiaSubgroup_normal ℚ_[2]`.
  - `isClosed := isClosed_wildInertiaSubgroup ℚ_[2]`.
  - `isProP := haveI := charP_residueField ℚ_[2] 2; isProP_iff.mp (isProP_wildInertiaSubgroup ℚ_[2] 2)`.
  - `AbsGalQ2 ⧸ W` is `rfl` to `TauCeti.tameQuotient ℚ_[2]`, and
    `QuotientGroup.mk g = toTameQuotient ℚ_[2] g` holds by `toTameQuotient_apply`.
- **`equiv := (tameQuotientGeometricEquiv hσ0 τ0 hτ0).trans iwEquiv`**, where `σ0` and `τ0` are
  chosen by `Classical.choose` from the two existence theorems.
- **`iwEquiv : IwasawaGroupGeometric ℚ_[2] ≃ₜ* Ttame`** is built directly in about 90 lines,
  without P1:
  - Forward map: `presentedProfiniteGroup.lift (freeProfiniteGroup.lift fun i => ![tameSigma, tameTau] i.down)`.
    The relator is killed by `rw [iwasawaRelatorGeometric_def, Padic.natCard_residueField]`
    followed by `tame_relation`.
  - Backward map: `presentationLift {tameWord} ((FreeProfiniteGroup.homEquiv (Fin 2) (ProfiniteGrp.of (IwasawaGroupGeometric ℚ_[2]))).symm ![γ, τ]).hom`.
    The relator is killed by `inv_iwasawaSigmaGeometric_mul_iwasawaTauGeometric_mul` with `q = 2`.
  - Inverse laws: `presentedProfiniteGroup.hom_ext_of` with `rintro ⟨i⟩; fin_cases i`, which
    handles the `ULift`, together with `FreeProfiniteGroup.homEquiv` injectivity applied to
    `ConcreteCategory.ofHom` after `quotientMk_surjective`.
  - **The relator matches:** both words are `γ⁻¹τγ(τ^q)⁻¹` with generators in the same order.
    gq2's `σ` is geometric Frobenius, as is Tau Ceti's `γ`; gq2's `of 0`/`of 1` correspond to
    Tau Ceti's `of (up 0)`/`of (up 1)`. Plan confirmed.
  - **Do not** import `GQ2.Prop32` for its `topGen_ttame`/`monoidHom_eq_of_topGen`. It imports
    `GQ2.Foundations.Interfaces`, so it would create an import cycle once C2 makes `Interfaces`
    import the adapters.
- **The sign of `nuT` (correction to the plan).** The plan says "`nuT` against the ℤ₂-reduction
  of `iwasawaCoordinateGeometric`" and "`ztwoOne` against the reduction of `zHat.gen`". The
  correct statement is `nuT ∘ iwEquiv = zHat.lift ztwoOne⁻¹ ∘ iwasawaCoordinateGeometric`.
  - Reason: `nuT tameSigma = ztwoOne`, while the geometric generator has coordinate `zHat.gen⁻¹`.
  - So `ν_t` is the *inverse* of the reduction along `gen ↦ ztwoOne`.
  - Proved for any generator-preserving `e` by `presentedProfiniteGroup.hom_ext_of`, using
    `nuT_tameSigma`, `iwasawaCoordinateGeometric_iwasawaSigmaGeometric`, `zHat.lift_gen` and `map_inv`.
- **Both orientation clauses come from one lemma, for any lift `g` of `artinMap x`:**
  `nuT (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹ ^ v2 x`. Its proof is the chain
  `iwasawaCoordinateGeometric_tameQuotientGeometricEquiv` → `tameQuotientToZHat_toTameQuotient` =
  `unramifiedCoordinate_mk` → `unramifiedCoordinate_artinMap` → `zHat.lift_ofInt` →
  `Padic.toAdd_normalizedValuation_eq_valuation`. Then:
  - At `uniformizer`, `v2 = 1` gives `ztwoOne⁻¹`.
  - At `unitEmbed u`, `v2 = 0` gives `1`.

  Correction to the plan: `tameQuotientGeometricEquiv_toTameQuotient_frobenius` is the wrong tool,
  because `g` is an arbitrary lift and not the chosen `σ0`.
- **Ticket dependency:** B10 depends on B5 only. It uses one gq2-side fact from B5, namely that
  `localReciprocity_tauceti.recip` reduces to `artinMap ℚ_[2]`. Drop the P1 dependency.
- **Hardest seam:** the cross-module definitional unfolding of `R.recip` (see Answers 3).

### Answers
1. *Can `σ` and `τ` be obtained at `ℚ_[2]` with automatic instances?* **Yes.**
   `TauCeti.exists_isArithFrobeniusLift ℚ_[2]` and
   `TauCeti.exists_topologicalClosure_zpowers_inertiaTameCharacter_eq_top ℚ_[2]` elaborate as is
   (examples in `GQ2/TauCeti/Smoke.lean`). The only missing instance in B10 is `CharP 𝓀[ℚ_[2]] 2`, for
   `isProP_wildInertiaSubgroup`; it comes from `TauCeti.charP_residueField ℚ_[2] 2`.
2. *Conventions in `nuT_recip_uniformizer`:*
   - `rec 2` is arithmetic Frobenius: its unramified coordinate is `gen`.
   - Tau Ceti's geometric generator `γ` has coordinate `gen⁻¹`.
   - gq2's `tameSigma` corresponds to `γ` and has `nuT = ztwoOne`.
   - Hence `nuT(rec 2) = ztwoOne⁻¹`. Tested.
3. *Cross-module unfolding of `R.recip`.* The clauses have type
   `toAb g = localReciprocity_tauceti.recip …`, and the proof unifies `.recip` with `artinMap ℚ_[2]`
   definitionally. B5.lean must therefore keep gq2's `@[expose] public section`, or export
   `@[simp] theorem localReciprocity_tauceti_recip : localReciprocity_tauceti.recip = artinMap ℚ_[2] := rfl`.
   Not tested across two modules: the draft holds both terms in one file, and the risk is inferred
   from how Tau Ceti's unexposed definitions behave. Tau Ceti's own definitions are not exposed. As tested, `GQ2.IsProP p G ↔ TauCeti.IsProP p G := Iff.rfl`
   fails with "not exposed: `TauCeti.IsProP ↦ 5`", and `TauCeti.isProP_iff.symm` works instead.

## B3c: the dyadic orientation

### gq2 side
`GQ2/Foundations/LiteratureInputs.lean:58-60`:
```lean
  dyadicOrientation [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    DyadicOrientation
```
- `GQ2.DyadicOrientation` (`GQ2/Orientation.lean:73-91`): fields `equiv : ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0`,
  `chiTwo : maxProPQuotient 2 AbsGalQ2 →* ℤ_[2]ˣ` (plain `MonoidHom`), `continuous_chiTwo`,
  `chiTwo_factors : ∀ g : AbsGalQ2, chiTwo (maxProPMk 2 AbsGalQ2 g) = chiCyc g`, `surjective_chiTwo`,
  `chi_A : chiTwo (equiv.symm d0A) = -1`, `chi_S : chiTwo (equiv.symm d0S) = 1`,
  `chi_Y : ∀ y : ℤ_[2]ˣ, (y : ℤ_[2]) = -3 → chiTwo (equiv.symm d0Y) = y⁻¹`.
- `GQ2.d0Relator` (`GQ2/DyadicPresentation.lean:45`), with `GQ2.commP x y = x⁻¹ * y⁻¹ * x * y` (`GQ2/Words.lean:59`):
  ```lean
  noncomputable def d0Relator : FreeProfiniteGroup (Fin 3) :=
    FreeProfiniteGroup.of 0 ^ 2 * FreeProfiniteGroup.of 1 ^ 4 *
      commP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 2)
  ```
  `D0Full := profinitePresentation {d0Relator}` (:56), `D0 := maxProPQuotient 2 D0Full` (:62),
  `d0A/d0S/d0Y := maxProPMk 2 D0Full (quotientMk _ (of 0/1/2))` (:89-93), `d0_relation` (:98).
- `GQ2.chiCyc` (`GQ2/Reciprocity.lean:128`): `(cyclotomicCharacter (AlgebraicClosure ℚ_[2]) 2).comp (MulSemiringAction.toRingAut (AlgebraicClosure ℚ_[2] ≃ₐ[ℚ_[2]] AlgebraicClosure ℚ_[2]) _)`.
- `GQ2.AbsGalQ2 := Field.absoluteGaloisGroup ℚ_[2]` (abbrev, `GQ2/Statement.lean:40`); `GQ2.proPKernel` (`GQ2/MaxProP.lean:132`),
  `maxProPQuotient` (:153, a `ProfiniteGrp` = `profiniteQuotient (proPKernel p G)`), `maxProPMk` (:159),
  `maxProPHomEquiv` (:195), `isProP_maxProPQuotient` (:273); `presentationLift` (`GQ2/BoundaryFrame.lean:101`);
  `SectionThree.topGen_map`/`topGen_freeProfiniteGroup`/`monoidHom_eq_of_topGen` (`GQ2/Prop32.lean:84/68/105`).

### Tau Ceti sources
All `#check` output below is verbatim from `GQ2/TauCeti/Smoke.lean` (57 declarations, elaborates clean).
- `TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked` — `TauCeti.NumberTheory.LocalField.ProP.RatPadic` (`:91`); also `absoluteGaloisGroupProP_two_ratPadic` (:125), `ratPadicTwo_hasPrimitiveRoot` (:48)
  ```lean
  TauCeti.absoluteGaloisGroupProP_two_ratPadic_marked : ∃ (e :
    TauCeti.absoluteGaloisGroupProP 2 ℚ_[2] ≃ₜ* TauCeti.demushkinD0),
    TauCeti.standardD0Orientation.comp ↑e = TauCeti.cyclotomicOrientation 2 ℚ_[2] TauCeti.ratPadicTwo_hasPrimitiveRoot ∧
      Function.Surjective ⇑(TauCeti.cyclotomicOrientation 2 ℚ_[2] TauCeti.ratPadicTwo_hasPrimitiveRoot)
  TauCeti.ratPadicTwo_hasPrimitiveRoot : ∃ ζ, IsPrimitiveRoot ζ 2
  ```
  No instance arguments. `#print axioms` of the assembled adapter (below) is the standard three, so this Tau Ceti chain is sorry-free.
- `TauCeti.absoluteGaloisGroupProP` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.ProP` (`:28`, `abbrev` = `maximalProPQuotient p (Field.absoluteGaloisGroup K)`)
  ```lean
  TauCeti.absoluteGaloisGroupProP : ℕ → (K : Type u_1) → [Field K] → Type u_1
  ```
- `TauCeti.cyclotomicOrientation` — `TauCeti.FieldTheory.Galois.AbsoluteGaloisGroup.Cyclotomic.Orientation` (`:82`, `ContinuousMonoidHom.quotientLift (continuousLocalCyclotomicCharacter p K) _ _`); `cyclotomicOrientation_mk` (:90), `_comp_absoluteGaloisGroupProPQuotientMap` (:98), `_range` (:108)
  ```lean
  TauCeti.cyclotomicOrientation : (p : ℕ) →
    [inst : Fact (Nat.Prime p)] →
      (K : Type u_1) → [inst_1 : Field K] → (∃ ζ, IsPrimitiveRoot ζ p) → TauCeti.absoluteGaloisGroupProP p K →ₜ* ℤ_[p]ˣ
  @TauCeti.cyclotomicOrientation_mk : ∀ {p : ℕ} [inst : Fact (Nat.Prime p)] {K : Type u_1} [inst_1 : Field K]
    (hmu : ∃ ζ, IsPrimitiveRoot ζ p) (g : Field.absoluteGaloisGroup K),
    (TauCeti.cyclotomicOrientation p K hmu) ↑g = (TauCeti.localCyclotomicCharacter p K) g
  ```
- `TauCeti.continuousLocalCyclotomicCharacter` / `localCyclotomicCharacter` — `…Cyclotomic.Character` (`:54` / `:33`); `localCyclotomicCharacter_apply` (:41, `(rfl)`)
  ```lean
  TauCeti.continuousLocalCyclotomicCharacter : (p : ℕ) →
    [inst : Fact (Nat.Prime p)] → (K : Type u_1) → [inst_1 : Field K] → Field.absoluteGaloisGroup K →ₜ* ℤ_[p]ˣ
  TauCeti.localCyclotomicCharacter_apply : ∀ (p : ℕ) [inst : Fact (Nat.Prime p)] (K : Type u_1) [inst_1 : Field K]
    (σ : Field.absoluteGaloisGroup K),
    (TauCeti.localCyclotomicCharacter p K) σ = (cyclotomicCharacter (AlgebraicClosure K) p) σ.toRingEquiv
  ```
- `TauCeti.d0Relator`, `demushkinD0`, `d0A/d0S/d0Y`, `d0_relation`, `d0Lift`, `d0_hom_ext` — `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.D0.Basic` (`:77`, `:95` abbrev `presentedProP 2 (Fin 3) {d0Relator}`, `:104/107/110`, `:139`, `:155`, `:180`)
  ```lean
  TauCeti.d0Relator_def : TauCeti.d0Relator =
    TauCeti.freeProP.of 0 ^ 2 * TauCeti.freeProP.of 1 ^ 4 *
      ((TauCeti.freeProP.of 1)⁻¹ * (TauCeti.freeProP.of 2)⁻¹ * TauCeti.freeProP.of 1 * TauCeti.freeProP.of 2)
  TauCeti.demushkinD0 : Type
  @TauCeti.d0Lift : {P : Type} →
    [inst : Group P] →
      [inst_1 : TopologicalSpace P] →
        [IsTopologicalGroup P] →
          [CompactSpace P] →
            [TotallyDisconnectedSpace P] →
              TauCeti.IsProP 2 P → (a s y : P) → a ^ 2 * s ^ 4 * (s⁻¹ * y⁻¹ * s * y) = 1 → TauCeti.demushkinD0 →ₜ* P
  @TauCeti.d0_hom_ext : ∀ {Q : Type u_1} [inst : Group Q] [inst_1 : TopologicalSpace Q] [T2Space Q]
    {φ ψ : TauCeti.demushkinD0 →ₜ* Q},
    φ TauCeti.d0A = ψ TauCeti.d0A → φ TauCeti.d0S = ψ TauCeti.d0S → φ TauCeti.d0Y = ψ TauCeti.d0Y → φ = ψ
  ```
  plus `d0Lift_d0A/_d0S/_d0Y : (TauCeti.d0Lift hP a s y h) TauCeti.d0A = a` etc. (:162-172), `isProP_demushkinD0` (:264).
- `TauCeti.standardD0Orientation` and its values — `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation` (`:91`, `:96/101/106`; `negThreeUnit` :62, `negThreeUnit_coe` :66, `standardD0Orientation_surjective` :112, `_unique` :134)
  ```lean
  TauCeti.standardD0Orientation : TauCeti.demushkinD0 →ₜ* ℤ_[2]ˣ
  TauCeti.standardD0Orientation_d0A : TauCeti.standardD0Orientation TauCeti.d0A = -1
  TauCeti.standardD0Orientation_d0S : TauCeti.standardD0Orientation TauCeti.d0S = 1
  TauCeti.standardD0Orientation_d0Y : TauCeti.standardD0Orientation TauCeti.d0Y = TauCeti.negThreeUnit⁻¹
  TauCeti.negThreeUnit_coe : ↑TauCeti.negThreeUnit = -3
  ```
- `D0/Invariants.lean`: `isDemushkin_demushkinD0` (:64), `hasPrescriptionProperty_standardD0Orientation` (:91), `demushkinCharacter_demushkinD0 : ∀ hG, demushkinCharacter hG = standardD0Orientation` (:113). Not needed by the adapter.
- Support: `TauCeti.isProP_iff` (`ProP/Basic.lean:75`), `TauCeti.mem_proPKernel_iff` (`MaximalProP.lean:132`), `TauCeti.isProP_maximalProPQuotient` (:318), `TauCeti.isProP_units_padicInt_two` (`ProP/PadicUnits.lean:107`).

Instances at `ℚ_[2]` (tested by `#synth`): `Fact (Nat.Prime 2)` is `Nat.fact_prime_two`; `CompactSpace (Field.absoluteGaloisGroup ℚ_[2])` is
`TauCeti.instCompactSpaceAbsoluteGaloisGroup_tauCeti ℚ_[2]` (`AbsoluteGaloisGroup/Basic.lean:359`); `TotallyDisconnectedSpace` comes from Tau Ceti's
`TotallySeparatedSpace` instance (:365). So once Tau Ceti is imported, gq2's `[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` binders are
dischargeable. On `absoluteGaloisGroupProP 2 ℚ_[2]` and `demushkinD0`: `QuotientGroup.instCompactSpaceQuotientSubgroup`,
`QuotientGroup.instIsTopologicalGroup`, `GQ2.instTotallyDisconnectedSpace_quotient`; `T2Space ℤ_[2]ˣ` is `Units.instT2Space`. The adapter supplies
nothing by hand except the `IsProP` proofs passed explicitly to `d0Lift`/`proPKernel_le_ker`.

### Translation
**Tested end to end**: `artifacts/orient/adapter_sketch.lean` (186 lines, `module` with `public import` of 4 Tau Ceti modules + `GQ2.Orientation` + `GQ2.Prop32`)
builds `dyadicOrientation_tauceti [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] : GQ2.DyadicOrientation`; `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`; the field shape matches. What it does:
1. **Tau Ceti bodies are not exposed** (none of the B3c files has `@[expose]`). Every `rfl` bridge fails with "definitions were not unfolded because their
   definition is not exposed" — tested: `GQ2.chiCyc = TauCeti.localCyclotomicCharacter 2 ℚ_[2] := rfl`, `GQ2.proPKernel 2 G = TauCeti.proPKernel 2 G := rfl`,
   `(GQ2.maxProPQuotient 2 AbsGalQ2 : Type) = TauCeti.absoluteGaloisGroupProP 2 ℚ_[2] := rfl`, `ContinuousMulEquiv.refl _` between them,
   `GQ2.IsProP 2 P ↔ TauCeti.IsProP 2 P := Iff.rfl` all fail; `TauCeti.isProP_maximalProPQuotient : TauCeti.IsProP 2 GQ2.D0` times out (whnf). Go through the stated lemmas instead:
   `IsProP` via `by rw [TauCeti.isProP_iff]; rfl`; `proPKernel` equality via `ext` + `TauCeti.mem_proPKernel_iff`; `chiCyc g` via `(localCyclotomicCharacter_apply 2 ℚ_[2] g).symm`.
2. `galEquiv : GQ2.maxProPQuotient 2 AbsGalQ2 ≃ₜ* TauCeti.absoluteGaloisGroupProP 2 ℚ_[2]` is `QuotientGroup.quotientMulEquivOfEq (proPKernel_eq …)`, with continuity
   from `QuotientGroup.isQuotientMap_mk … |>.continuous_iff`; `galEquiv (maxProPMk 2 AbsGalQ2 g) = (QuotientGroup.mk g)` is `rfl`.
3. `d0Equiv : TauCeti.demushkinD0 ≃ₜ* GQ2.D0` (generators to generators, ~70 lines). This does **not** need P1's generic presentation dictionary:
   forward is `TauCeti.d0Lift isProP_D0 GQ2.d0A GQ2.d0S GQ2.d0Y GQ2.d0_relation` (gq2's `d0_relation` is accepted as is, since `commP` unfolds to the same word);
   backward is `GQ2.quotientLift (proPKernel 2 D0Full) (presentationLift {d0Relator} ((FreeProfiniteGroup.homEquiv (Fin 3) (ProfiniteGrp.of demushkinD0)).symm ![d0A,d0S,d0Y]).hom _) (proPKernel_le_ker _ _)`;
   the round trips come from `TauCeti.d0_hom_ext` and `GQ2.SectionThree.monoidHom_eq_of_topGen` + topological generation of `GQ2.D0`.
   The structural difference: gq2's `D0` is (F̂₃/⟨⟨r⟩⟩)(2), presentation first and then max pro-2; Tau Ceti's is F̂₃(2)/⟨⟨r⟩⟩, pro-2 first, with
   `d0Relator : freeProP 2 (Fin 3)`. Tau Ceti has no `maximalProPQuotient (presentedProfiniteGroup X R) ≃ₜ* presentedProP p X _` (only the surjection
   `presentedProfiniteGroup.toPresentedProP`, `Presentation/Basic.lean:914`).
4. `equiv := (galEquiv.trans e).trans d0Equiv` with `e := Classical.choose absoluteGaloisGroupProP_two_ratPadic_marked`;
   `chiTwo := ((cyclotomicOrientation 2 ℚ_[2] ratPadicTwo_hasPrimitiveRoot).comp galEquiv).toMonoidHom`; `chiTwo_factors` by `rw [galEquiv_mk, cyclotomicOrientation_mk]`
   then `localCyclotomicCharacter_apply`; `surjective_chiTwo := he.2.comp galEquiv.surjective`; for `chi_A/S/Y`, `cyc x = standardD0Orientation (e x)` comes from
   `← he.1; rfl`, then `simp` cancels `galEquiv (galEquiv.symm (e.symm (d0Equiv.symm (d0Equiv a))))`, then the `standardD0Orientation_d0X` value lemmas apply;
   for `chi_Y`, `congr 1` plus `Units.ext (by rw [hy, negThreeUnit_coe])`.
5. Pitfall: `GQ2.SectionThree.topGen_d0` lives in the **non-module** `GQ2/DyadicNielsen.lean`, so `module` files cannot import it ("cannot import
   non-`module` GQ2.DyadicNielsen"). The sketch re-proves it in 15 lines from `GQ2.SectionThree.topGen_map`/`topGen_freeProfiniteGroup` (`GQ2/Prop32.lean`, a module).

Plan/ticket claims checked:
- Plan §3: "values … (`Demushkin/D0/Invariants.lean`)". **Wrong file.** The values are in `Demushkin/Orientation.lean:96/101/106`. Invariants.lean only identifies the
  standard orientation with the canonical character.
- Plan: "check `d0Relator` on both sides is `A²S⁴[S,Y]` in the same commutator convention". **Confirmed** (see the Answers below). No inverse needs inserting.
- Plan: "`cyclotomicOrientation` is the `quotientLift` of `continuousLocalCyclotomicCharacter` … which is the descent clause". **Confirmed** (`cyclotomicOrientation_mk`).
- Ticket A1: "Tau Ceti's goes through the separable closure". **Not at this revision for this character.** `localCyclotomicCharacter p K` is
  `(cyclotomicCharacter (AlgebraicClosure K) p).comp (MulSemiringAction.toRingAut Gal(AlgebraicClosure K/K) (AlgebraicClosure K))` (`Character.lean:33-36`), the
  same expression as `GQ2.chiCyc`, so the identification is the one-line pointwise `_apply` above.
- Ticket B3c "insert the inverse if they differ": they do not differ.
- Hardest seam: none is left open for B3c. The real cost is (1): every cross-library identification has to be a stated lemma or an explicit construction, never `rfl`.

### Answers
**(5) Which theorems give `standardD0Orientation` on `d0A/d0S/d0Y`?** `TauCeti.standardD0Orientation_d0A : standardD0Orientation d0A = -1`,
`TauCeti.standardD0Orientation_d0S : … d0S = 1`, `TauCeti.standardD0Orientation_d0Y : … d0Y = TauCeti.negThreeUnit⁻¹`. All are `@[simp]`, all are in
`TauCeti/Topology/Algebra/Group/Profinite/Demushkin/Orientation.lean:96/101/106` (module `TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Orientation`), **not** in
`D0/Invariants.lean`. They match gq2's `(-1, 1, (-3)⁻¹)`. For `-3`, gq2 quantifies `∀ y, (y : ℤ_[2]) = -3 → … = y⁻¹`; Tau Ceti uses
`negThreeUnit := isUnit_neg_three.unit` with `negThreeUnit_coe : ↑negThreeUnit = -3` (:66). The bridge `y = negThreeUnit := Units.ext (by rw [hy, negThreeUnit_coe])`
is pinned in `GQ2/TauCeti/Smoke.lean`. They reach gq2's `equiv.symm` form through the first conjunct of the marked theorem (step 4, tested).
`D0/Invariants.lean` contributes only `hasPrescriptionProperty_standardD0Orientation` (:91) and `demushkinCharacter_demushkinD0` (:113).

**`d0Relator`: the same word?** Yes. The commutator is `x⁻¹y⁻¹xy` on both sides: gq2's `commP` (`GQ2/Words.lean:59`, `example : GQ2.commP x y = x⁻¹ * y⁻¹ * x * y := rfl`
succeeds), and Tau Ceti writes it inline. The generator order is the same (`A, S, Y = of 0, of 1, of 2`), the index type is `Fin 3` on both sides, both live in universe 0
(`demushkinD0 : Type`, `GQ2.D0 : ProfiniteGrp.{0}`, `d0Lift` wants `P : Type`), and there is no `ULift`. Definitions:
```lean
-- gq2, GQ2/DyadicPresentation.lean:45
noncomputable def d0Relator : FreeProfiniteGroup (Fin 3) :=
  FreeProfiniteGroup.of 0 ^ 2 * FreeProfiniteGroup.of 1 ^ 4 *
    commP (FreeProfiniteGroup.of 1) (FreeProfiniteGroup.of 2)
-- Tau Ceti, TauCeti/Topology/Algebra/Group/Profinite/Demushkin/D0/Basic.lean:77
noncomputable def d0Relator : freeProP 2 (Fin 3) :=
  freeProP.of 0 ^ 2 * freeProP.of 1 ^ 4 *
    ((freeProP.of 1)⁻¹ * (freeProP.of 2)⁻¹ * freeProP.of 1 * freeProP.of 2)
```
The only difference is the ambient group: profinite F̂₃ in gq2, pro-2 F̂₃(2) in Tau Ceti. Pinned: gq2's `d0Relator` unfolds by `rfl` to the inline word, and
`GQ2.d0_relation` typechecks against `d0Lift`'s hypothesis `a ^ 2 * s ^ 4 * (s⁻¹ * y⁻¹ * s * y) = 1`.

**`cyclotomicOrientation` codomain and normalization vs `chiTwo`.** Both are multiplicative and land in `ℤ_[2]ˣ`, with Mathlib's topology on units. Tau Ceti's is
a `ContinuousMonoidHom` (`→ₜ* ℤ_[p]ˣ` at `p = 2`); gq2's `chiTwo` is a bare `→*` with continuity as a separate field. Neither is inverted: both are Mathlib's
`cyclotomicCharacter (AlgebraicClosure ·) p` on `σ.toRingEquiv`. The tested pointwise identity is
`example (g : GQ2.AbsGalQ2) : GQ2.chiCyc g = TauCeti.localCyclotomicCharacter 2 ℚ_[2] g := (TauCeti.localCyclotomicCharacter_apply 2 ℚ_[2] g).symm`; the bare
`MonoidHom` `rfl` fails because the definition is not exposed. `cyclotomicOrientation` takes the witness `hmu`; use `TauCeti.ratPadicTwo_hasPrimitiveRoot`, the witness the
marked theorem is stated with.

## B8: peripheral cyclotomic action

### gq2 side
`LiteratureInputs.peripheralCyclotomicAction : PeripheralCyclotomicAction` (`GQ2/Foundations/LiteratureInputs.lean:68`).
`structure GQ2.PeripheralCyclotomicAction` (`GQ2/PeripheralAction.lean:92`), verbatim fields:
```lean
  ι : ℤ_[2]ˣ → Zhat
  hι_cont : Continuous ι
  hι_one : ι 1 = omega2
  hι_proj : ∀ u : ℤ_[2]ˣ, zhatProjTwo (ι u) = Multiplicative.ofAdd ((u : ℤ_[2]))
  aut : ℤ_[2]ˣ → ContinuousMulEquiv Delta Delta
  cP : ℤ_[2]ˣ → Delta
  cT : ℤ_[2]ˣ → Delta
  cC : ℤ_[2]ˣ → Delta
  hP : ∀ u : ℤ_[2]ˣ, aut u deltaP = conjP (deltaP ^ᶻ ι u) (cP u)
  hT : ∀ u : ℤ_[2]ˣ, aut u deltaT = conjP (deltaT ^ᶻ ι u) (cT u)
  hC : ∀ u : ℤ_[2]ˣ, aut u deltaC = conjP (deltaC ^ᶻ ι u) (cC u)
```
`Delta := maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))` (`:72`, `abbrev`), `deltaP/deltaT` (`:75,:79`, `maxProPMk … (of 0/1)`),
`deltaC := (deltaP * deltaT)⁻¹` (`:83`), `conjP x g = g⁻¹ * x * g` (`GQ2/Words.lean:56`), `omega2` (`GQ2/Zhat.lean:156`).

### Tau Ceti sources
- `TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two` — `TauCeti.Topology.Algebra.Group.Profinite.Free.Peripheral.Dyadic` (`Profinite/Free/Peripheral/Dyadic.lean:124`). The plan omits the `Peripheral.` namespace.
  ```lean
  @TauCeti.Peripheral.exists_peripheralPowerAutomorphism_two : ∀ {F : Type u_1} [inst : Group F]
    [inst_1 : TopologicalSpace F] [inst_2 : IsTopologicalGroup F] [inst_3 : CompactSpace F]
    [inst_4 : TotallyDisconnectedSpace F] (hF : TauCeti.IsProP 2 F) (e : F ≃ₜ* TauCeti.freeProP 2 (Fin 2)) (u : ℤ_[2]ˣ),
    ∃ φ cP cT cC,
      cP = 1 ∧
        φ (TauCeti.Peripheral.periphP e) = cP⁻¹ * hF.padicPow (TauCeti.Peripheral.periphP e) ↑u * cP ∧
          φ (TauCeti.Peripheral.periphT e) = cT⁻¹ * hF.padicPow (TauCeti.Peripheral.periphT e) ↑u * cT ∧
            φ (TauCeti.Peripheral.periphC e) = cC⁻¹ * hF.padicPow (TauCeti.Peripheral.periphC e) ↑u * cC
  ```
  `φ : TauCeti.ContinuousAut F`, where `abbrev ContinuousAut G := G ≃ₜ* G` (`ContinuousAut/Basic.lean:83`), i.e. gq2's `ContinuousMulEquiv Delta Delta`.
  Instances at `F = ↥GQ2.Delta`: all four synthesize (`GQ2.Delta.isTopologicalGroup`, `…is_compact`, `Profinite.instTotallyDisconnectedSpaceCarrierToTop`). `hF` is supplied as `(isProP_iff 2 _).1 GQ2.isProP_maxProPQuotient` (tested).
- `TauCeti.Peripheral.periphP/periphT/periphC` (`Dyadic.lean:70,74,78`, not exposed), `periphP_eq_basis` (`:84`), `periphT_eq_basis` (`:90`), `periphC_def` (`:95`); `TauCeti.Peripheral.basis_apply` (`Peripheral/Basic.lean:85`)
  ```lean
  @TauCeti.Peripheral.periphC_def : ∀ {F : Type u_1} [inst : Group F] [inst_1 : TopologicalSpace F]
    (e : F ≃ₜ* TauCeti.freeProP 2 (Fin 2)),
    TauCeti.Peripheral.periphC e = (TauCeti.Peripheral.periphP e * TauCeti.Peripheral.periphT e)⁻¹
  @TauCeti.Peripheral.basis_apply : ∀ {p r : ℕ} {F : Type u_1} [inst : Group F] [inst_1 : TopologicalSpace F]
    (e : F ≃ₜ* TauCeti.freeProP p (Fin r)) (i : Fin r), TauCeti.Peripheral.basis e i = e.symm (TauCeti.freeProP.of i)
  ```

### Translation
Plan claims confirmed:
- `C = (PT)⁻¹` on both sides.
- Conjugation convention: Tau Ceti `cP⁻¹ * x * cP` is `GQ2.conjP x cP`, closed by `rfl`.
- `e = deltaEquiv` from P1; `periphP deltaEquiv = deltaP` by `periphP_eq_basis, basis_apply, ContinuousMulEquiv.symm_apply_eq, deltaEquiv_deltaP`, and likewise T, C.
- `deltaP ^ᶻ ι u = padicPow deltaP u`, by `zpowHat_eq_zpowZtwo`, `hι_proj` and P1's `zpowZtwo_eq_padicPow`.
- `cP = 1` is available but not needed.

**The whole bundle elaborates in scratch** (`artifacts/prop/proto_b8.lean`, `Scratch.b8 : GQ2.PeripheralCyclotomicAction`,
`#print axioms` = standard three, about 230 lines including the P1 pieces it needs). The pattern:
1. Prove an `autSpec u : ∃ φ cP cT cC, φ deltaP = conjP (deltaP ^ᶻ iota u) cP ∧ …` by `obtain` from the Tau Ceti theorem, rewriting `periph* deltaEquiv` before choosing.
2. Take `aut u := (autSpec u).choose`, etc.

Rewriting inside `.choose` after choosing fails with "motive is not type correct".

Correction: build `ι` without the plan's "trivial odd part". Proving `ι 1 = omega2` for
`ι u := e.symm (idem 2 · …)` would need `e omega2 = toMul (zHat.idem 2)`, i.e. the odd components of
gq2's `omega2` vanish, and gq2 does not prove that. Instead, with `e = zhatEquiv`:
- `ι u := e.symm (toMul (ofMul (e omega2) * sec u))`, where `sec u := ringEquivPiPadicInt.symm (single2 (u - 1)) + 1`.
- `hι_one`: `sec 1 = 1`.
- `hι_proj`: `component 2 (ofMul (e ω₂)) = 1`, which is `zhatProjTwo ω₂ = ofAdd 1`, i.e. `x ^ᶻ ω₂ = x` on the pro-2 group `Multiplicative ℤ_[2]`.
- `hι_cont`: by composition.

Hardest seam: `GQ2.zpowHat_omega2_eq_self` (`GQ2/AnabelianBridge/Construction.lean:74`) lives in a
**non-`module`** file. A `module` adapter cannot import it ("cannot import non-`module` … from `module`").
The prototype copies its 25-line proof, which uses `GQ2.map_zpowHat_omega2` and
`GQ2.powOmega2_eq_self_of_orderOf_two_pow` (`GQ2/AppendixB.lean:44`, a module). The docstrings'
`GQ2.zhatProjTwo_omega2` does not exist as a declaration. The B8 ticket should either keep the
local copy or move the lemma into a `module` file (that move is outside B8's owned files).
