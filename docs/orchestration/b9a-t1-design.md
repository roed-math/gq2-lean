# B9-A / T1 — statement design memo

Deliverables: `GQ2/StiefelWhitney.lean` (N1) and `GQ2/TraceForm.lean` (N3 skeleton + draft
axiom), both passing `lake env lean` with only `sorry` warnings; this memo.  Recon basis:
`docs/orchestration/b9a-t0-recon.md` (all mathlib names below re-verified by grep against the
pinned `ec410d2` mathlib during T1).

## N1 decision: mathlib `QuadraticForm` (T0's recommendation adopted)

Model: `QuadraticForm ↥k V` with `QuadraticMap.Equivalent`; diagonal representatives
`diagForm k x y := QuadraticMap.weightedSumSquares ↥k ![x, y]` with **unit** weights
`x y : (↥k)ˣ` on `Fin 2 → ↥k`.  `IsDiagonalization k Q x y := Q.Equivalent (diagForm k x y)`.
`swOne k Q` / `swTwo k htriv Q` choose a diagonalization by `Classical.choice` (`dite` +
`Exists.choose`), values `kummerClassK k x + kummerClassK k y` in `H1 k.fixingSubgroup (ZMod 2)`
and `kummerClassK k x ⌣[htriv] kummerClassK k y` in `H2 …`; junk value `0` when no unit
diagonalization exists (repo junk-value convention, cf. `IsDemushkin`).

The mathlib route did **not** fight the `IntermediateField` types; no fallback structure needed.
Two facts discovered during verification:

* `Invertible (2 : ↥k)` is **global**: `invertibleTwo` (`Mathlib/Algebra/CharP/Invertible.lean:125`,
  `[DivisionSemiring K] [CharZero K]`) + `Subsemiring.instCharZero`.  No local instance needed.
* The instance chains (`SMulCommClass (↥k)ˣ ↥k ↥k`, `DistribMulAction`, `Invertible`) exceed the
  default 20000 typeclass heartbeats over the `IntermediateField` instance space; both files set
  `set_option synthInstance.maxHeartbeats 400000` file-level (elaboration stays ≈ 2–5 s/file).

Mathlib declarations relied on (names verified in the pinned tree):
`QuadraticMap.weightedSumSquares` (+ `weightedSumSquares_apply`, simp), `QuadraticMap.Equivalent`
(`.refl/.symm/.trans`), `QuadraticForm.equivalent_weightedSumSquares_units_of_nondegenerate'`
(hypothesis `(associated (R := K) Q).SeparatingLeft`; gives `w : Fin (finrank K V) → Kˣ`),
`QuadraticMap.associated`, `LinearMap.SeparatingLeft`, `LinearMap.BilinMap.toQuadraticMap`
(+ `_apply`, simp; note the namespace — **not** dot-accessible on `BilinForm` terms),
`LinearMap.compl₁₂` (+ `_apply`, simp), `LinearMap.mulLeft` (`Mathlib/Algebra/Module/LinearMap/
Defs.lean:1023`, + `mulLeft_apply`, simp), `Algebra.traceForm` (+ `_apply`),
`Algebra.traceForm_nondegenerate` (T2/T3 input), `IntermediateField.adjoin.finiteDimensional`,
`IntermediateField.adjoin.finrank`, `IntermediateField.adjoin.powerBasis` (T2 input),
`Polynomial.monic_X_pow_sub_C`, `QuadraticForm.discr`/`discr_comp` (T3 degree-1 input).

## L-encoding decision (draft axiom): adjoin-only field side + verbatim B9 subgroup side

The RHS operators `corH1`/`evensNormH2` force the subgroup encoding to stay: the axiom carries
`hidx/s/hs/htriv/hUo/α/hαdef/hα/hαc` **byte-identical** to B9 (diffed against
`Foundations/Axioms.lean:316–328`).  For the field side the axiom does **not** carry an ambient
`L : IntermediateField ℚ_[2] ℚ̄₂`: it uses `quadExt k δ := IntermediateField.adjoin ↥k {δ}`,
built from the *same* `δ` as the stabilizer subgroup, so subgroup↔field compatibility is
provable, never hypothesized.  One field-side hypothesis is added:
`hdeg : Module.finrank ↥k ↥(quadExt k δ) = 2`.  `hdeg` is mathematically redundant given
`hidx`+`hUo` (bridge: `KummerKrullBridge.exists_quadratic_of_open_index_two`; stated as
`finrank_quadExt_eq_two`, T2), but carrying it (a) weakens the axiom, (b) makes the statement
locally readable as Kahn's Théorème 2 setting "`L/k` quadratic" without chasing the Galois
correspondence, and (c) guarantees the `swOne/swTwo` dites fire (trace forms of a genuine
quadratic extension are nondegenerate in char 0), so the identity is about real invariants, not
junk values.  Rejected alternative: carrying `L` + `k ≤ L` + `δ ∈ L` + a fixing-subgroup
compatibility hypothesis — more plumbing, further from Kahn, nothing gained for the derivation.

New generality vs B9: `a : (↥(quadExt k δ))ˣ` is **arbitrary** (B9's `u n v hn` disappear from
the axiom; they return only in T2's Lemma 6.16 diagonalization lemmas used at the flip).

## Draft axiom (exact Lean source, elaborates in `GQ2/TraceForm.lean`)

```lean
theorem relativeStiefelWhitney_dyadic
    (k : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] k]
    (d : (↥k)ˣ)
    (δ β : AlgebraicClosure ℚ_[2])
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
    (swOne k (traceFormTwisted k δ ↑a)
      = swOne k (traceFormOne k δ) + corH1 htriv hUo hidx hs α hα hαc)
    ∧ (swTwo k htriv (traceFormTwisted k δ ↑a)
      = swTwo k htriv (traceFormOne k δ)
        + swOne k (traceFormOne k δ) ⌣[htriv] corH1 htriv hUo hidx hs α hα hαc
        + evensNormH2 htriv hUo hidx hs α hα hαc) :=
  sorry -- T5: becomes the B9-A axiom in Foundations/Axioms.lean after owner sign-off
```

## Upstream constraint and the B11a firewall (T2/T3 must read this)

`StiefelWhitney`/`TraceForm` must stay **strictly upstream of `Foundations/Axioms.lean`**
(at T5 the axiom file imports them; any import of it from here is a cycle).  Consequences:

* The Delzant lemmas' Steinberg-type cup inputs are B11a consequences, and every proved cup
  helper (`cup_of_normForm`, `cup_steinberg`, `cup_self_eq_neg_one`, …) lives in
  `GQ2/HilbertLedger.lean`, which imports the axiom file.  So `swTwo_well_defined`/`swTwo_diag`/
  `swTwo_congr` take the B11a clause as an explicit hypothesis `hnorm` (statement-identical to
  `hilbertSymbol_normCriterion_finiteDyadic k htriv`'s conclusion); the flip instantiates it.
  This realizes plan node N2's "relation inputs come from B11a" without an import cycle, and
  `#print axioms` of the flipped `evensKahn_dyadic` will show {new axiom, B11a} as predicted.
* Axiom-free helpers T3 will still need (`h1_add_self`, `h2_add_self`, `kummerClassK_mul`,
  `kummerClassK_inv`, `kummerClassK_mul_self`, `kcf_root_indep'`, `kcf_mul_of_fixed`,
  `kummerClassK_eq_of_sq_ratio`) also live in `HilbertLedger.lean` (downstream).  Options:
  re-prove privately (KummerKrullBridge precedent) or ask the owner to re-home HilbertLedger's
  Tiers 0–1 upstream (they import nothing from the axiom).  **Owner question Q3.**
* `trivialCupPairing` symmetry IS available upstream: `GQ2/CupSymmetry.lean` (`cup11_comm`).
* T2's bridge helpers `exists_sqrt_generator` / `fixingSubgroup_subgroupOf_eq_stabilizer` are
  `private` in `GQ2/KummerSurjectivity.lean` (T0 gotcha): re-derive or route through the public
  `exists_quadratic_of_open_index_two`.

## Sorry inventory

| file:decl | ticket | content |
|---|---|---|
| `StiefelWhitney.lean` `exists_isDiagonalization` | T3 | nondegenerate binary ⇒ unit diagonalization |
| `StiefelWhitney.lean` `swOne_well_defined` | T3 | N2 degree 1 (discriminant) |
| `StiefelWhitney.lean` `swTwo_well_defined` | T3 | N2 degree 2 (Delzant, `hnorm`-parametrized) |
| `TraceForm.lean` `finrank_quadExt_eq_two` | T2 | hidx/hUo ⇒ `[k(δ):k] = 2` (bridge) |
| `TraceForm.lean` `traceFormOne_isDiagonalization` | T2 | `Tr⟨1⟩ ≃ ⟨2, 2d⟩` |
| `TraceForm.lean` `traceFormTwisted_isDiagonalization` | T2 | `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩` |
| `TraceForm.lean` `relativeStiefelWhitney_dyadic` | T5 | the draft axiom (never proved) |

Proved now (no sorry): `diagForm(_apply)`, `IsDiagonalization`, `isDiagonalization_of_equivalent`,
`swOne`/`swTwo` + `swOne_diag`/`swTwo_diag`/`swOne_congr`/`swTwo_congr` (from the two
well-definedness sorries), `quadExt`, `isIntegral_of_sq_eq`, `finiteDimensional_quadExt`,
`traceFormOne(_apply)`, `traceFormTwisted(_apply)`.

## Open questions for the owner

1. **`hdeg` redundancy**: keep the redundant-but-readable `hdeg` (current draft), or drop it for
   a minimal hypothesis list?  (Keeping is safer; dropping is closer to "no derived facts".)
2. **`hnorm` firewall**: confirm that N2's B11a dependence via the `hnorm` hypothesis (instead of
   axiom hypotheses inside `relativeStiefelWhitney_dyadic`, plan R4) matches your intent.  The
   draft axiom itself carries **no** cup-relation hypotheses.
3. **Re-home HilbertLedger Tiers 0–1?**  T3 needs its axiom-free Kummer/two-torsion helpers
   upstream; private re-proofs work but re-homing is cleaner.  Your call before T3 starts.
4. `quadExt` naming (vs. spelling `IntermediateField.adjoin ↥k {δ}` inline in the axiom) and the
   file-level `synthInstance.maxHeartbeats 400000` are T1 conveniences — flag if either should
   change before T5 freezes the statement.
