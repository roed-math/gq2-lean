# B9-A / T0 — mathlib QuadraticForm & trace API recon

Read-only inventory for nodes **N1** (Stiefel–Whitney of binary forms) and **N3** (twisted
trace forms) of the B9-A plan.  Pinned mathlib is at
`.lake/packages/mathlib`, commit **`ec410d23dfa4e7540d4663405b5e0dc71f3c3363`**, toolchain
`leanprover/lean4:v4.31.0-rc2`.  Every path below is relative to
`/Users/roed/claude/gq2-lean/.lake/packages/mathlib/` (mathlib) or the repo root (GQ2).
Every declaration name was confirmed by `grep`/`rg` and, where a signature is quoted, read from
source.  Where I did **not** find something, it is stated explicitly.

Target setting: `F := ↥k`, `k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])`,
`[FiniteDimensional ℚ_[2] k]`.  `F` is a field of **characteristic 0** (subfield of `ℚ̄₂`), so
`(2 : F) ≠ 0` and `Invertible (2 : F)` is available via
`invertibleOfNonzero` (`Mathlib/Algebra/GroupWithZero/Invertible.lean:53`,
`def invertibleOfNonzero {a : α} (h : a ≠ 0) : Invertible a`) applied to `two_ne_zero`.  This
unlocks essentially all char-≠-2 quadratic-form API below.

---

## 1. Quadratic forms, equivalence, diagonalization, nondegeneracy

### 1.1 Core definitions
`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`:

* `QuadraticMap` (structure, line 149):
  ```
  structure QuadraticMap (R : Type u) (M : Type v) (N : Type w) [CommSemiring R] [AddCommMonoid M]
      [Module R M] [AddCommMonoid N] [Module R N] where
    toFun : M → N
    toFun_smul : ∀ (a : R) (x : M), toFun (a • x) = (a * a) • toFun x
    exists_companion' : ∃ B : BilinMap R M N, ∀ x y, toFun (x + y) = toFun x + toFun y + B x y
  ```
* `QuadraticForm` (abbrev, line 163): `abbrev QuadraticForm : Type _ := QuadraticMap R M R`.
  So a form over `F` on a module `V` is `QuadraticForm F V = QuadraticMap F V F`.
* `QuadraticMap.polar` (line 99): `polar f x y = f (x + y) - f x - f y` (2× the associated
  bilinear map).

### 1.2 Equivalence (`Isometry` / `IsometryEquiv` / `Equivalent`)
`Mathlib/LinearAlgebra/QuadraticForm/Isometry.lean`:
* `QuadraticMap.Isometry` (structure, line 36) `extends M₁ →ₗ[R] M₂`, notation `Q₁ →qᵢ Q₂`
  (line 43): a linear **map** commuting with the forms (`map_app' : ∀ m, Q₂ (f m) = Q₁ m`).

`Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean`:
* `QuadraticMap.IsometryEquiv` (structure, line 40) `extends M₁ ≃ₗ[R] M₂`: a linear **equivalence**
  with `map_app' : ∀ m, Q₂ (toFun m) = Q₁ m`.
* `QuadraticMap.Equivalent` (def, line 47):
  `def Equivalent (Q₁ : QuadraticMap R M₁ N) (Q₂ : QuadraticMap R M₂ N) : Prop := Nonempty (Q₁.IsometryEquiv Q₂)`.
* `Equivalent.refl / .symm / .trans` (lines 115/119/123) — it is an equivalence relation.
* `IsometryEquiv.map_app` (line 73): `Q₂ (f m) = Q₁ m` (simp).

**This is the isometry-class equivalence the axiom must quotient by** (N1/N2). `swOne`/`swTwo`
will be `Equivalent`-invariant by design (N2).

### 1.3 `weightedSumSquares` (the diagonal model)
`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`:
* `weightedSumSquares` (def, line 1458):
  ```
  def weightedSumSquares [Monoid S] [DistribMulAction S R] [SMulCommClass S R R] (w : ι → S) :
      QuadraticMap R (ι → R) R := ∑ i : ι, w i • (proj (R := R) (n := ι) i i)
  ```
  It is a `QuadraticForm R (ι → R)` on the **function model** `ι → R`.
* `weightedSumSquares_apply` (line 1465): `weightedSumSquares R w v = ∑ i, w i • (v i * v i)`.
* `basisRepr` (def, line 1438): `Q.basisRepr v = Q.comp v.equivFun.symm : QuadraticMap R (ι → R) N`
  — transports a form on `V` to the model `ι → R` via a basis. For `⟨x,y⟩` diagonal forms use
  `ι = Fin 2`, `w = ![x, y]`, giving a `QuadraticForm F (Fin 2 → F)`.

### 1.4 Diagonalization theorems (with the exact char-≠-2 hypotheses)
`Mathlib/LinearAlgebra/QuadraticForm/IsometryEquiv.lean`, section
`namespace QuadraticForm` opened by `variable [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V]`
(line 147) then `variable [FiniteDimensional K V]` (line 160):

* **Plain diagonalization** (line 164):
  ```
  theorem equivalent_weightedSumSquares (Q : QuadraticForm K V) :
      ∃ w : Fin (Module.finrank K V) → K, Equivalent Q (weightedSumSquares K w)
  ```
  Needs `Field K`, `Invertible (2:K)`, `FiniteDimensional K V`. No nondegeneracy — weights may be 0.
* **Diagonalization into UNITS** (line 169) — the one T2 wants, so diagonal entries are `Kˣ`:
  ```
  theorem equivalent_weightedSumSquares_units_of_nondegenerate' (Q : QuadraticForm K V)
      (hQ : (associated (R := K) Q).SeparatingLeft) :
      ∃ w : Fin (Module.finrank K V) → Kˣ, Equivalent Q (weightedSumSquares K w)
  ```
  **Extra hypothesis: `(associated Q).SeparatingLeft`** (nondegeneracy of the associated bilinear
  form). This is exactly "nondegenerate ⇒ diagonal entries are units."
* Supporting: `isometryEquivWeightedSumSquares` (line 151, needs an orthogonal basis via
  `associated`), `isometryEquivBasisRepr` (line 140), `exists_orthogonal_basis`
  (in `QuadraticForm/Basic.lean`, needs `Invertible (2:K)`).
* Rescaling isometries (same file):
  `weightedSumSquaresCongr (h : w = w')` (line 183) and
  `isometryEquivWeightedSumSquaresWeightedSumSquares (u : ι → Sˣ) (h : ∀ i, w' i * u i ^ 2 = w i)`
  (line 190) — give `⟨x,y⟩ ≃ ⟨x u², y v²⟩`, useful for "complete the square" chain steps in N2.

### 1.5 Nondegeneracy notions
* `QuadraticMap.Anisotropic` (`Basic.lean:1104`): `∀ x, Q x = 0 → x = 0`.
* `LinearMap.SeparatingLeft` (`Mathlib/LinearAlgebra/SesquilinearForm/Basic.lean:672`):
  `def SeparatingLeft (B) : Prop := ∀ x, (∀ y, B x y = 0) → x = 0`; `SeparatingRight` (line 690);
  `LinearMap.Nondegenerate` (line 694) `:= SeparatingLeft B ∧ SeparatingRight B`.
* `LinearMap.BilinForm.Nondegenerate` (`Mathlib/LinearAlgebra/BilinearForm/Properties.lean:291`):
  `abbrev Nondegenerate (B : BilinForm R M) : Prop := LinearMap.Nondegenerate B`.
* Bridge anisotropic→separating (`Basic.lean:1122`):
  ```
  theorem separatingLeft_of_anisotropic [Invertible (2 : R)] (Q : QuadraticMap R M R)
      (hB : Q.Anisotropic) : (QuadraticMap.associated' (N := R) Q).SeparatingLeft
  ```
* **Extracting "diagonal entries are units":** the cleanest route is
  `equivalent_weightedSumSquares_units_of_nondegenerate'` directly — it hands back `w : Fin n → Kˣ`.
  Its proof (lines 169–175) uses `IsOrtho.not_isOrtho_basis_self_of_separatingLeft` +
  `Units.mk0`, i.e. nondegeneracy ⇒ each diagonal `Q (v i) ≠ 0`.

### 1.6 A 2-dim form vs `Fin 2 → F`
A binary form is `QuadraticForm F V` with `Module.finrank F V = 2`; the diagonal representatives
live on the concrete model `Fin 2 → F` as `weightedSumSquares F ![x, y]` (units `x, y : Fˣ`).
`Equivalent` connects them; `basisRepr`/`isometryEquivBasisRepr` moves between an abstract `V`
and `Fin 2 → F`. There is **no** special "binary" (`finrank = 2`) API — dimension 2 is just
`Fin 2`.

---

## 2. Bilinear ↔ quadratic passage (and the ½ factors)

`Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`:

* `BilinMap.toQuadraticMap` (def, line 711): `toFun x := B x x`; `toQuadraticMap_apply` (717):
  `B.toQuadraticMap x = B x x`. **No `Invertible 2` needed** for this direction.
* `associatedHom` (def, line 897) — needs `[Invertible (2 : Module.End R N)]` (declared at line 888):
  `associatedHom S Q := ⅟(2 : Module.End R N) • polarBilin Q`; `associated_apply` (905):
  `associatedHom S Q x y = ⅟(2 : Module.End R N) • (Q (x + y) - Q x - Q y)`.
  For `N = R = F` a field, `Invertible (2:F)` gives `Invertible (2 : Module.End F F)` via the
  instance at `Basic.lean:860` (`instance [Invertible (2 : R)] : Invertible (2 : Module.End R M)`).
* `associated` (abbrev, line 1008): `abbrev associated : QuadraticMap R M N →ₗ[R] BilinMap R M N := associatedHom R`.
* **Round trips (both directions, needing `Invertible 2`):**
  * `associated_toQuadraticMap` (938):
    `associatedHom S B.toQuadraticMap x y = ⅟(2:Module.End R N) • (B x y + B y x)`.
  * `toQuadraticMap_associated` (960): `(associatedHom S Q).toQuadraticMap = Q`.
  * For **symmetric** `B`: `associatedHom S B.toQuadraticMap = B` (lines 945/951; the `IsSymm`
    variants — proved with `associated_toQuadraticMap` + `B x y = B y x`). This is what recovers
    `traceForm` from `q₁ = traceForm.toQuadraticMap` (traceForm is symmetric, see §3).
* `polarBilin` (def, line 319), `two_nsmul_associated` (911): `2 • associatedHom S Q = Q.polarBilin`.

Net: over `F` (char 0) the correspondence `QuadraticForm F V ↔ symmetric BilinForm F V` is a
clean bijection; the only `Invertible 2` friction is on the `associated` side, and it discharges
automatically for `F`.

---

## 3. Trace machinery (`Algebra.trace`, `Algebra.traceForm`) and `↥L`/`↥k` friction

`Mathlib/RingTheory/Trace/Defs.lean`:
* `Algebra.trace R S : S →ₗ[R] R` (def, line 71) `:= (LinearMap.trace R S).comp (lmul R S).toLinearMap`;
  `trace_apply` (78). `trace_algebraMap` (110, needs `[StrongRankCondition R] [Module.Free R S]`):
  `trace R S (algebraMap R S x) = finrank R S • x`.
* `Algebra.traceForm R S : BilinForm R S` (def, line 171)
  `:= LinearMap.compr₂ (lmul R S).toLinearMap (trace R S)`; `traceForm_apply` (178):
  `traceForm R S x y = trace R S (x * y)`; `traceForm_isSymm` (181); `traceForm_toMatrix` (184).
* Tower laws: `trace_trace` (138), `trace_comp_trace` (146) (need `Module.Free`+`Module.Finite`
  on both steps).

`Mathlib/RingTheory/Trace/Basic.lean`:
* **`traceForm_nondegenerate`** (line 504):
  ```
  theorem traceForm_nondegenerate [FiniteDimensional K L] [Algebra.IsSeparable K L] :
      (traceForm K L).Nondegenerate
  ```
  and `det_traceForm_ne_zero` (477). This is how a **twisted** trace form gets nondegeneracy for
  free (see below).
* Separability is automatic in char 0: `Algebra.IsSeparable.of_integral`
  (`Mathlib/FieldTheory/Separable.lean:670`, `priority 100` instance,
  "An integral field extension in characteristic 0 is separable"). So for finite `↥L/↥k`
  (both char 0) the `[Algebra.IsSeparable ↥k ↥L]` instance fires.

### The twisted trace form `q_a(z) = Tr_{L/k}(a z²)`
**There is NO packaged "twisted trace form" or `Tr⟨a⟩` in mathlib** (searched
`RingTheory/Trace/*`). Build it by hand from `traceForm` + composition:

* Untwisted: `Tr_{L/k}⟨1⟩ := (Algebra.traceForm ↥k ↥L).toQuadraticMap`, value `z ↦ Tr(z·z)`.
* Twisted: bilinear `B_a := (Algebra.traceForm ↥k ↥L).compl₁₂ (LinearMap.mulLeft ↥k a) LinearMap.id`
  gives `B_a z w = Tr((a·z)·w) = Tr(a z w)` (symmetric since `a z w = a w z`), then
  `Tr_{L/k}⟨a⟩ := B_a.toQuadraticMap`, value `z ↦ Tr(a z²)`.  Pieces exist:
  * `LinearMap.mulLeft R a : A →ₗ[R] A` — `Mathlib/Algebra/Algebra/Bilinear.lean` (confirmed
    present: `mulLeft_mul` line ~84, `commute_mulLeft_right` line 91).
  * `LinearMap.compl₁₂` — `Mathlib/LinearAlgebra/BilinearMap.lean:331`.
  * Nondegeneracy of `B_a`: `a ∈ Lˣ`, so `mulLeft a` is a linear equiv and `B_a` is nondegenerate
    iff `traceForm` is — provable from `traceForm_nondegenerate`, but **the "`a` a unit ⇒ twist stays
    nondegenerate" step is not a single lemma** (small hand proof; a gap).

### Instantiating `↥L / ↥k` — the three candidate constructions of "`L = k(δ)` over `↥k`"
`k, L : IntermediateField ℚ_[2] ℚ̄₂` with `k ≤ L`. Options:

1. **`IntermediateField.extendScalars hkL : IntermediateField ↥k ℚ̄₂`**
   (`Mathlib/FieldTheory/IntermediateField/Basic.lean:832`; carrier defeq to `↥L`). **Recommended.**
   The repo already commits to this: `Algebra ↥k ↥(extendScalars hkL)`, `Module.finrank ↥k ↥(extendScalars hkL)`,
   and `FiniteDimensional ℚ_[2] ↥(extendScalars hkL)` all appear in `GQ2/KummerKrullBridge.lean`.
   Full trace/finrank API applies (`Algebra.trace ↥k ↥(extendScalars hkL)`,
   `Algebra.traceForm ↥k ↥(extendScalars hkL)`).
2. **`IntermediateField.adjoin ↥k {δ} : IntermediateField ↥k ℚ̄₂`** (= `↥k⟮δ⟯`). Also a `↥k`-algebra
   with trace/finrank; `IntermediateField.adjoin.powerBasis` (below) gives the `{1, δ}` basis
   directly. `GQ2/KummerSurjectivity.lean`'s `exists_sqrt_generator` proves
   `adjoin ↥k {δ} = extendScalars hkL`, so (1) and (2) coincide.
3. `restrictScalars` route — not needed; more friction.

**Recommendation: option (1)** for the field object (matches the repo bridge output) with option
(2)'s `adjoin.powerBasis` used to name the `{1, δ}` basis for the Gram-matrix computation.

### finrank-2 and the `{1, δ}` basis
* `IntermediateField.adjoin.finrank` (`Mathlib/FieldTheory/IntermediateField/Adjoin/Basic.lean:468`):
  `Module.finrank K K⟮x⟯ = (minpoly K x).natDegree` (needs `IsIntegral K x`).
* `IntermediateField.adjoin.powerBasis` (`Adjoin/Basic.lean:450`):
  `PowerBasis K K⟮x⟯` with `gen := AdjoinSimple.gen K x`, `dim := (minpoly K x).natDegree`,
  `basis_eq_pow i` (`= gen^i`). For degree 2 this **is** the `{1, δ}` basis.
* **Getting `natDegree (minpoly) = 2` / finrank = 2:**
  * From the subgroup index (the axiom's `hidx`) — via the repo bridge (§5). This is the route
    the plan's N3 prescribes and is fully proved in-repo.
  * From `¬IsSquare d` directly — **GAP** (see §6): mathlib's
    `X_pow_sub_C_irreducible_of_prime_pow` (`Mathlib/FieldTheory/KummerExtension.lean:153`)
    **explicitly requires `p ≠ 2`** ("`-- TODO: generalize to p = 2`", line ~150), so there is
    **no** mathlib lemma "`X² − C d` irreducible ⇔ `d` not a square." Do not rely on it.

---

## 4. Units / discriminant / Gram-matrix det utilities

* `IsSquare` (`Mathlib/Algebra/Group/Even.lean:57`): `def IsSquare (a) : Prop := ∃ r, a = r * r`;
  `isSquare_iff_exists_sq` (130): `IsSquare a ↔ ∃ r, a = r ^ 2`. Field/unit `IsSquare` API is all
  here + `Mathlib/Algebra/GroupWithZero/*`.
* `QuadraticForm.toMatrix` (`QuadraticForm/Basic.lean:1258`) — the Gram matrix `Matrix n n R`
  of a form w.r.t. a basis; `toMatrix'` (1218) on `Fin n → R`.
* **Discriminant** (`Basic.lean`):
  * `QuadraticForm.discr b Q := (Q.toMatrix b).det` (def, line 1320).
  * `discr_smul` (1324): `(a • Q).discr b = a ^ Fintype.card n * Q.discr b`.
  * **`discr_comp`** (1327) — the "change-of-basis determinant squares" fact for N2 degree-1:
    ```
    theorem discr_comp (b' : Basis n R P) (Q : QuadraticForm R P) (f : N →ₗ[R] P) :
        QuadraticForm.discr b (Q.comp f)
          = (f.toMatrix b b').det * (f.toMatrix b b').det * (Q.discr b')
    ```
* `LinearMap.BilinForm.toMatrix` and congruence/det:
  `Mathlib/LinearAlgebra/Matrix/BilinearForm.lean` — `toMatrix_comp` (280), `toMatrix_compLeft`
  (288), `toMatrix_compRight` (295); `Nondegenerate.toMatrix` (499); and
  **`nondegenerate_iff_det_ne_zero`** (550):
  `B.Nondegenerate ↔ (BilinForm.toMatrix b B).det ≠ 0`, plus `nondegenerate_of_det_ne_zero` (554).
* `Matrix.nondegenerate_iff_det_ne_zero` (`Mathlib/LinearAlgebra/Matrix/Nondegenerate.lean`).

These cover **degree-1 (discriminant) invariance** of N2 completely. They do **not** provide the
degree-2 (Hasse/`w₂`) well-definedness — see gaps.

---

## 5. The repo bridge: index-2 subgroup ↔ quadratic subextension

### `GQ2/KummerKrullBridge.lean` (namespace `GQ2.KummerSurjectivity`, `local notation ℚ̄₂`)
* **`exists_quadratic_of_open_index_two`** (line 132) — the central bridge:
  ```
  theorem exists_quadratic_of_open_index_two
      (k : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] k]
      (H : Subgroup ↥(k.fixingSubgroup)) (hHopen : IsOpen (↑H : Set ↥(k.fixingSubgroup)))
      (hHindex : H.index = 2) :
      ∃ (L : IntermediateField ℚ_[2] ℚ̄₂) (hkL : k ≤ L), FiniteDimensional ℚ_[2] L ∧
        (L.fixingSubgroup).subgroupOf k.fixingSubgroup = H ∧
        Module.finrank ↥k ↥(extendScalars hkL) = 2
  ```
* Private degree lemmas (verbatim-modulo-namespace copies of `GQ2.ShapiroDeepness.*`):
  `finiteDimensional_extendScalars` (63), `index_extendScalars_fixingSubgroup` (80),
  **`finrank_extendScalars_eq_two`** (95): index-2 `subgroupOf` ⇒ `finrank ↥k ↥(extendScalars hkL) = 2`.
  Uses `InfiniteGalois.{fixingSubgroup_fixedField, fixedField_fixingSubgroup, normalAutEquivQuotient,
  isOpen_iff_finite, normal_iff_isGalois}`, `IntermediateField.fixingSubgroupEquiv`,
  `Subgroup.normal_of_index_eq_two`.

### `GQ2/KummerSurjectivity.lean` (namespace `GQ2.KummerSurjectivity`)
Cocycle→subgroup machinery and the **field-side extraction** T2/T3 will reuse:
* `zHom` (51), `zHom_ker_isOpen` (70), `zHom_index_ker` (87), `zHom_surjective` (76),
  `mem_zHom_ker` (65) — turn a 1-cocycle `z ≠ 0` into an open index-2 kernel.
* **`exists_sqrt_generator`** (private, 160) — **key for T2/T3** (extracts `δ, d` from finrank 2):
  ```
  private theorem exists_sqrt_generator {k L : IntermediateField ℚ_[2] ℚ̄₂} (hkL : k ≤ L)
      (hdeg : Module.finrank ↥k ↥(extendScalars hkL) = 2) :
      ∃ (d : (↥k)ˣ) (δ : ℚ̄₂), δ ^ 2 = ((d : ↥k) : ℚ̄₂) ∧ δ ∈ L ∧ δ ∉ k ∧
        IntermediateField.adjoin ↥k {δ} = extendScalars hkL
  ```
  (completes the square on the degree-2 minpoly; `d := a²−4b` as a unit).
* **`fixingSubgroup_subgroupOf_eq_stabilizer`** (private, 245) — connects the axiom's `hidx/hs`
  (stabilizer of `δ`) to the field `L`:
  ```
  private theorem fixingSubgroup_subgroupOf_eq_stabilizer {k L : …} (hkL : k ≤ L) {δ : ℚ̄₂}
      (hadj : IntermediateField.adjoin ↥k {δ} = extendScalars hkL) :
      (L.fixingSubgroup).subgroupOf (k.fixingSubgroup)
        = (MulAction.stabilizer (Kummer.GaloisGroup ℚ_[2]) δ).subgroupOf (k.fixingSubgroup)
  ```
* `fixingSubgroup_adjoin_simple` (private, 131), `mem_bot_iff_mem` (152), `kcf_root_indep'` (262),
  `kcf_eq_zero_iff` (269), `kummerClassK_one` (103).
* Capstone `kummerClassK_surjective'` (280).

> **GOTCHA (flag for T1/T2):** `exists_sqrt_generator` and
> `fixingSubgroup_subgroupOf_eq_stabilizer` are **`private`** to `KummerSurjectivity.lean` (as are
> the bridge's degree lemmas). T2 cannot import them by name. Either (a) re-derive the needed
> facts, (b) ask the owner to de-`private` / re-home them, or (c) route through the public
> `exists_quadratic_of_open_index_two`. The plan's R2 mitigation ("T2 starts by inventorying its
> lemmas") is exactly this.

### `GQ2/EvensKahn.lean`, section `BaseGeneral` (what T1 reuses for the class values)
* `sqrtCl (x : ℚ̄₂) : ℚ̄₂` (414), `sqrtCl_sq` (417): `sqrtCl x ^ 2 = x`, `sqrtCl_ne_zero` (420).
* `fixingSubgroup_smul` (424), `unitCoe_ne_zero` (430).
* **`kummerClassK (k) (a : (↥k)ˣ) : H1 k.fixingSubgroup (ZMod 2)`** (def, 437) — the base-general
  Kummer class `[a] ∈ H¹(G_k, 𝔽₂)`. `swOne ⟨x,y⟩ = kummerClassK k x + kummerClassK k y`.
* **`twoUnit (k) : (↥k)ˣ`** (def, 448) — the unit `2`; the diagonalizations are
  `Tr⟨1⟩ ≃ ⟨2, 2d⟩ = ⟨twoUnit, twoUnit*d⟩`, `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`.
* Cup/cor/norm plumbing consumed by the current B9 and reused verbatim: `corH1` (261),
  `evensNormH2` (332), `kummerZ1On` (390), `⌣[htriv]` = `trivialCupPairing`.
* `swTwo ⟨x,y⟩ = kummerClassK k x ⌣[htriv] kummerClassK k y` — the cup of two Kummer classes.

---

## 6. Surprises for T1 (coercions, `IsSquare` ↔ index-2, char-2)

* **`↥(extendScalars hkL)` vs `↥L`.** Carriers are defeq (both `{x // x ∈ L}`) but **not
  syntactically equal**. All trace/finrank API must be stated on `↥(extendScalars hkL)` (the repo
  convention), or Lean will fail to unify `Algebra ↥k ↥L` (which does not exist — `L` is over
  `ℚ_[2]`, not `↥k`). The `Algebra ↥k _` structure lives only on `extendScalars`/`adjoin`.
* **`IsSquare` ↔ index-2 (base-general).** In-repo facts (not one packaged iff):
  * `Kummer.kummerClass_eq_zero_iff (a : Kˣ) : kummerClass a = 0 ↔ IsSquare a`
    (`GQ2/Kummer.lean:220`) — **base-field** `K`, via mathlib infinite Galois.
  * `GQ2.kummerClassK_eq_zero_of_sq (a : (↥k)ˣ) (w : ↥k) (hw : w ^ 2 = a) : kummerClassK k a = 0`
    (`GQ2/KummerFiltration.lean:73`) — one direction, base-general.
  * The converse "class-zero ⇒ square" is advertised as `exists_sq_of_kummerClassK_eq_zero` in
    `GQ2/DeepCount.lean:24`'s module docstring, **but I did not find a `theorem` of that exact
    name** by `grep` — likely renamed or private; T1/T2 should locate the actual declaration
    before depending on it.
  * `¬IsSquare d ⇔ stabilizer index = 2` is therefore assembled from `kummerClassK d ≠ 0`
    (⇔ not a square) + `zHom_index_ker`, i.e. the surjectivity machinery — **there is no single
    mathlib or repo lemma** stating it. The axiom sidesteps this by carrying `hidx` as a hypothesis
    (as today's B9 does).
* **No `X² − C d` for `p = 2`** (repeated for emphasis): finrank-2 must come from `hidx` via the
  bridge, never from a mathlib nonsquare-⇒-irreducible lemma.
* **char-2 cup algebra** for N4 lives in the repo, not mathlib: `GQ2/CupSymmetry.lean`,
  `HilbertLedger.trivialCupPairing_comm`, `CharTwo.add_self_eq_zero` (mathlib). Cup bilinearity
  is the `trivialCupPairing` API already used throughout `EvensKahn.lean`.
* **`SeparatingLeft` vs `Nondegenerate`.** `equivalent_weightedSumSquares_units_of_nondegenerate'`
  wants `(associated Q).SeparatingLeft`; `traceForm_nondegenerate` yields `.Nondegenerate`
  (`= SeparatingLeft ∧ SeparatingRight`). Take `.1`. For the associated form of `q_a` you also
  need `associated (B_a.toQuadraticMap) = B_a` (symmetric-round-trip, §2), then transport
  nondegeneracy of `B_a` from `traceForm`.
* No universe issues beyond the above (`H1 k.fixingSubgroup (ZMod 2)` is the established cohomology
  target; all forms live in `Type`).

---

## Recommended design

**Use mathlib `QuadraticForm F V` (`= QuadraticMap F V F`) with `QuadraticMap.Equivalent`, on a
2-dimensional `V` (concretely `Fin 2 → F` via `weightedSumSquares F ![x, y]`), rather than a
bespoke light structure of diagonal representatives.** Rationale grounded in what is pinned:
(1) the diagonalization-into-units theorem `equivalent_weightedSumSquares_units_of_nondegenerate'`
is exactly `swOne`/`swTwo`'s input and needs only `Invertible (2:F)` (free, char 0) plus
`(associated Q).SeparatingLeft`; (2) the trace forms `Tr⟨1⟩ = traceForm.toQuadraticMap` and
`Tr⟨a⟩ = B_a.toQuadraticMap` are genuine `QuadraticForm ↥k ↥(extendScalars hkL)` objects whose
nondegeneracy is `traceForm_nondegenerate` (char-0 separable, automatic); (3) `discr`/`discr_comp`
already prove the degree-1 (discriminant) half of N2 with determinant-squaring, and
`nondegenerate_iff_det_ne_zero` links it to Gram matrices; (4) `Equivalent` is a ready equivalence
relation with rescaling isometries for the complete-the-square chain. Define `swOne q`/`swTwo q`
by `Classical.choice` of a `equivalent_weightedSumSquares_units_of_nondegenerate'` witness, with
values `kummerClassK k x (+ / ⌣) kummerClassK k y` from `EvensKahn.BaseGeneral`; N2 discharges
well-definedness. Instantiate the field as `IntermediateField.extendScalars hkL` (matches the repo
bridge) and name the `{1, δ}` basis via `IntermediateField.adjoin.powerBasis`. **Fallback** (plan
R1): if N2's degree-2 well-definedness balloons, state `swOne/swTwo` on diagonalizations with a
well-definedness clause inside the axiom — the `QuadraticForm` scaffolding above is still what
computes the diagonal reps.

## Top gaps (things NOT in pinned mathlib — T1 must build by hand)

1. **Stiefel–Whitney / Hasse–Witt invariants of forms as Galois-cohomology classes.** Mathlib has
   **no** `w₁`/`w₂`/Hasse-invariant API (nothing under `QuadraticForm/` maps forms to `Hⁱ(G,𝔽₂)`).
   `swOne`/`swTwo` and their **degree-2 Delzant well-definedness** (representation lemma
   `⟨x,y⟩≃⟨x',y'⟩ ⇒ x' = xa²+yb²`, chain equivalence, cup identities) are entirely bespoke — only
   the degree-1 discriminant half (`discr_comp`) is provided by mathlib. This is node N2, the hard one.
2. **The twisted trace form and "unit twist preserves nondegeneracy."** No `Tr_{L/k}⟨a⟩` exists;
   build via `traceForm.compl₁₂ (mulLeft a) id |>.toQuadraticMap` and hand-prove that `a ∈ Lˣ`
   keeps it nondegenerate (transport from `traceForm_nondegenerate`). The two explicit
   diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩` (Lemma 6.16, basis `{1,δ}`,
   complete-the-square with `u ∈ kˣ`) are pure hand-work (node N3).
3. **finrank-2 from a nonsquare, and the private repo bridge.** No mathlib "`X²−C d` irreducible
   ⇔ `d` not a square" (`X_pow_sub_C_irreducible_of_prime_pow` excludes `p = 2`). finrank 2 must
   flow from the axiom's `hidx` through `KummerKrullBridge.exists_quadratic_of_open_index_two` +
   `exists_sqrt_generator` + `fixingSubgroup_subgroupOf_eq_stabilizer` — **the last two are
   `private`** in `KummerSurjectivity.lean`, so T2 must re-derive or get them exposed.
