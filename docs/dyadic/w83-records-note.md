# W83-RECORDS lane note

Lane targets: (A) strengthen the branch-producer existentials so they carry the marking, and
(B) instantiate `GenAsmRowResidual.cand` at the tied quadratic rows.
Base `23041e0f`; new module `GQ2/Dyadic/Instances/CanonicalRecords.lean`, prefix `canRec`,
24 declarations, all pinned in the file with the measured split. No sorry, no new axiom, no
`native_decide`, no heartbeat or recursion option. Every edited file and every direct importer
of one regenerates green against the mirror.

## §0 The site census, verified against the Lean

The defect (W82-CAND caution 2): the branch producers return `∃ G : GenAsmBranch K B,
G.pres = S`, which forgets `G.nuP`, while `GenAsmRowResidual.cand` and the three ASK fields are
all stated at `G.nuP` and every committed certificate producer lives at the row's canonical
marking.

`grep` for `∃ G : GenAsmBranch` returns 36 hits; all but a handful are re-exports that apply an
earlier producer. **The sites that construct the datum are eight, not four**, and the brief's
guess at their location was off in one place: there is no branch producer in
`GeneralCertificates.lean`, and the "canonical M/N producers" are in
`Instances/FieldUnimodularity.lean`.

| # | declaration | file:line | row | marking chosen | taken? |
| --- | --- | --- | --- | --- | --- |
| 1 | `genAsm_branch_of_oddSq` | `GeneralAssembly.lean:761` | `.L h` | the argument `nuP` | **yes** |
| 2 | `genAsm_branch_of_oddSq_canonical` | `GeneralAssembly.lean:797` | `.L h` | `lNu h` | **yes** |
| 3 | `fieldUni_genAsmBranch_of_orientedM_level_zero` | `FieldUnimodularity.lean:263` | `.M0 α 0` | `fieldId_mNuZtwo α 0` | **yes** |
| 4 | `fieldUni_genAsmBranch_of_orientedN_level_zero` | `FieldUnimodularity.lean:282` | `.N0 α 0` | `nNuZtwo α 0` | **yes** |
| 5 | `mpcCert_genAsmBranch_of_orientedMpc` | `MpcCertificate.lean:415` | `.Mpc α r ε η 0` | `mpcNu α r pp` | **yes** |
| 6 | `genAsm_branch_of_evenN` | `GeneralAssembly.lean:709` | `.N0 α h` | the argument `nuP` | no |
| 7 | `genAsm_branch_of_evenM` | `GeneralAssembly.lean:724` | `.M0 α h` | the argument `nuP` | no |
| 8 | `mpcPiv_genAsmBranch_sqrtNegTen` | `MpcPivot.lean:498` | `.Mpc 2 1 true 1 0` | `mpcPiv_nuZtwo` (transported) | **cannot be** |

The five taken are the ones the four tied quadratic rows and the odd row actually route
through, which is the criterion the brief set ("determine which are the five load-bearing
ones"). Two findings on the three not taken:

* **Sites 6 and 7 are a genuine sixth and seventh instance of the same defect**, reported and
  not taken per the brief. They are the free-`h` even producers; the frozen quadratic rows do
  not use them (they go through the level-zero producers, sites 3 and 4), so nothing in ticket
  B is blocked, but a general even-`h` row still cannot reach `cand`. This is the remaining
  owner item, and it is now marked in `GeneralAssembly.lean`'s own record.
* **Site 8 cannot be strengthened at all.** It builds its datum at the *transported* marking
  `mpcPiv_nuZtwo (fieldUni_nuPullbackM B e)`, and its own docstring already says in terms that
  what it does not carry is that the marking is `mpcNu 2 1 1`. No comparison of the two markings
  exists at this tree. The tied statement at `ℚ₂(√−10)` is the sibling
  `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`, which routes through site 5 and therefore does
  carry `mpcNu`, but it is conditional on `MpcPivShift 2`. That is why `ℚ₂(√−10)` is not one of
  the four rows of ticket B.

## §1 Ticket A: the strengthening

At each of the five sites the conclusion gained one conjunct,

```
∃ G : GenAsmBranch K B, G.pres = S ∧ HEq G.nuP <the marking the proof chose>
```

and the proof gained `HEq.rfl`. Nothing else changed in any of the five proofs: the marking was
already being read off the construction, exactly as the brief predicted.

**Why `HEq` and not `Eq`.** `GenAsmBranch.nuP` has type
`ContinuousMonoidHom ((genAsmCore pres : ProfiniteGrp) : Type) Ztwo`, which depends on the
record's own `pres` field, so `G.nuP = nu0` is ill-typed under the existential. The obvious
repair `∃ hp : G.pres = S, hp ▸ G.nuP = nu0` **does not elaborate**: `▸` cannot find a motive,
because the equation's type `G.pres = S` does not occur in the cast's result type
`ContinuousMonoidHom (DN α h) Ztwo` on either side. That was checked against the mirror before
committing to `HEq`. A consumer recovers the honest equation in three lines: destructure `G`,
`subst` the row equation (`pres` is then a local variable, so `subst` applies), and
`eq_of_heq`. `canRec_rowResidual_of_tied` is that consumer, written once.

**Downstream.** Every re-export of a strengthened producer keeps its old statement; the conjunct
is dropped at the call site with `Exists.imp (fun _ hG => hG.1)`, which is a proof-only edit.
Touched: `fieldUni_genAsmBranch_sqrt{NegTwo,Two}`, `fieldUni_genAsmBranch_sqrtFive_of_unramified`
(`FieldUnimodularity.lean`), `mpcCert_genAsmBranch_sqrt{Ten,NegTen}` (`MpcCertificate.lean`),
`mpcPiv_genAsmBranch_sqrtNegTen_of_shift` (`MpcPivot.lean`),
`oddId_genAsmBranch_L_of_supply` (`OddIdentification.lean`). So the only statement changes in
the tree are the five, as the grant requires.

**Pins.** No declaration was added or removed anywhere, so no pins block changed count.
`genAsm_branch_of_oddSq` and `genAsm_branch_of_oddSq_canonical` still print std-3; the three
even producers still print their inherited sets. `GeneralAssembly.lean` stays at 42 pins.

## §2 Ticket B: `Instances/CanonicalRecords.lean`

### The obstruction the brief did not know about, and its removal

Ticket A alone is **not** enough at the two `M0` rows. The branch datum there is built at
`FieldBranchId.fieldId_mNuZtwo α h hα` (which is `ν_M` read backwards through `ztwoIota`), while
the row's committed certificate producer `Instances.MCompactCore.mWordCertificate` takes its
marking together with the two normalization clauses `hnuSigma`/`hnuWild`, and **the tree proves
those only at a different marking**, `Instances.MCompactCore.mNu α h hα` (the `dmNu` witness for
the exponent vector `mNuExp`). An exhaustive grep found no lemma relating the two, in either
direction, and no sigma/wild lemma at `fieldId_mNuZtwo` at all.

`canRec_mNu_eq_mNuZtwo` proves `mNu α h hα = fieldId_mNuZtwo α h hα` at free `(α, h)`, by
`dm_hom_ext` and a four-way generator check: both send `μ₀ ↦ −m`, `μ₂ ↦ 1` and every other
marked generator to `0`, once `mOf α = 2 ^ (α − 1)` is pushed through the `ℕ → ℤ → ℤ_[2]` cast.
`canRec_mNuZtwo_sigma` and `canRec_mNuZtwo_wild` follow, and are what make
`mWordCertificate` typecheck at the branch datum's own marking. All three are **std-3**.

A second, free identification fell out on the `N` side: `SqrtNeg2.pilotNuP` and
`SelectedCoreLeavesRN.nNuZtwo 2 0` are the same term, so `canRec_pilotNuP_eq` is `rfl`. It was
never stated (`CertificateSupplyRN.lean:222` only says in prose that one is the handle-generic
form of the other). With it the `√−2` row is served at **both** committed spellings, which is
what the brief asked for where cheap.

### What landed

* **§1** `canRec_mNu_eq_mNuZtwo`, `canRec_mNuZtwo_sigma`, `canRec_mNuZtwo_wild`.
* **§2** the four tied branch data `canRec_branch_sqrt{NegTwo,Two,Five,Ten}`, each
  **unconditional** over the field's own bundle and the standing instance binders.
* **§3** one `CAND` producer per branch shape, `canRec_cand{M,N,Mpc}`, each concluding at
  *literally* the type of `GenAsmRowResidual.cand` over a datum on that row (the degree, word,
  core and `IsProP` witness are written as `SelectedPresentation` projections and `genAsmCore` /
  `genAsmCoreIsProP`, so the elaborator checks the certificate layer's spellings agree with the
  table's); plus `canRec_pilotNuP_eq` and `canRec_candPilot`.
* **§4** `canRec_rowResidual_of_tied`, the transport, and the three shape-level residuals
  `canRec_rowResidual_{M0,N0,Mpc}_of_analytic` at free row parameters.
* **§5** the four rows, twice each: `canRec_rowResidual_<field>` with `cand` as one binder, and
  `canRec_analytic_<field>`, §4's shape lemma instantiated at the row (the instantiation is the
  acceptance check that §2's branch datum and §3's producer agree on the marking).
* **§6** 24 pins.

### The per-row table, from the Lean

Writing `q = q_K` and `Γ = Γ_R (deg) q (word)`:

| row | `K` | canonical marking | `CAND` producer | branch datum | what remains |
| --- | --- | --- | --- | --- | --- |
| `N0 2 0` | `ℚ₂(√−2)` | `nNuZtwo 2 0` | `genCertNWordCertificateCanonical`, or `sqrtNegTwoWordCertificate` | free | 4 analytic clauses at `Γ`; ASK `exactLifting`; ASK `stokes` |
| `M0 3 0` | `ℚ₂(√2)` | `fieldId_mNuZtwo 3 0` | `mWordCertificate`, via §1 | free | the same |
| `M0 2 0` | `ℚ₂(√5)` | `fieldId_mNuZtwo 2 0` | `mWordCertificate`, via §1 | free | the same |
| `Mpc 2 1 false 1 0` | `ℚ₂(√10)` | `mpcNu 2 1 (p false 1)` | `mpcWordCertificate` | free | the same |

Three readings, each checkable in the file.

1. **ASK `determinant` is not a binder of any statement in §4 or §5.** The residual is assembled
   through `Instances.MpcRow.mpcRow_genAsmRowResidual_of_counting`, which derives it from
   `affineDeterminant_galK` and the field inputs' `ramifiedData`, the two Gauss pins being `rfl`
   at `standardNumerics`. So the record costs **two** ASK blocks, not three. Wave 79's and wave
   82's house notes both said the determinant rung was "a wiring job"; this is the wiring, at
   the general record rather than at the two procyclic rows only.
2. **The residue is uniform across the four rows**: the same four analytic clauses at the row's
   own candidate carrier, and no per-row analytic obligation. That extends W82-CAND's "uniform
   residue" observation from the `CorePresentation`-backed rows to the whole tied set.
3. **The branch datum and its marking are free at all four rows.** The four `canRec_branch_*`
   are unconditional; wave 78 through wave 81 removed the last clause at each of them, and
   ticket A is what makes that freedom usable rather than decorative.

### Axioms: 24 pins, and the split

* **std-3 on all of §1 and all of §3** (8 declarations). Placing the committed word certificate
  on the row's canonical marking introduces **no campaign axiom** at any of the three branch
  shapes, and neither does the `M0` marking bridge that makes the `M0` case possible.
* **The `GaussZ` set** (`hilbertSymbol_normCriterion_finiteDyadic`,
  `relativeStiefelWhitney_dyadic`, `tateDualityAt`, `absGalQ2_localEulerCharacteristic`) on §4's
  four declarations, inherited from `affineDeterminant_galK` through the determinant wiring.
  `absGalQ2_isTopologicallyFinitelyGenerated` is not in it.
* **The even route's endpoint set** on `canRec_branch_sqrtNegTwo`, and that set plus
  `peripheralCyclotomicAction` on the other three, inherited verbatim from
  `fieldUni_genAsmBranch_*` / `mpcCert_genAsmBranch_*`: **tying the marking into the conclusion
  costs nothing**.
* **The union of the two** on §5's eight declarations, and nothing beyond it.

## §3 Housekeeping owed

1. `GQ2/Dyadic/Instances/CanonicalRecords.lean` is **not registered** in `GQ2.lean` (the lane may
   not edit it). It imports `GQ2.Dyadic.GeneralCertificates`,
   `GQ2.Dyadic.Instances.FieldSqrtFiveUnramified` and `GQ2.Dyadic.Instances.MpcNormValues`, and
   should be registered after those three.
2. `GeneralAssembly.lean`'s W82-HOUSE caution has been corrected in place (the census was four
   sites, it is eight; five now carry the marking). The `GeneralAssembly` constructor table's
   `L h` row and `oddId_candidate_equiv_galK_of_supply`'s docstring are still stale from W82-CAND
   and were not touched here.
3. `Instances.LRowCand.lCandBranch` exists only because the odd producer forgot its marking.
   With site 2 strengthened the definition is no longer forced, though it is still convenient
   (it gives the datum definitionally rather than through `Classical.choice`). Not removed.
