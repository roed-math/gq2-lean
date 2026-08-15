# W75-STATE: the general-degree final theorem, stated

Lane W75-STATE, statement wave.  Produced against tree `f0a71688`, shared cache at the
4342-job green umbrella.  Verification of record: `scripts/mirror.sh` (sweep, gen, check).
**No `lake` command was run.**

One new module, `GQ2/Dyadic/GeneralAssembly.lean`, prefix `genAsm`.  No `sorry`, no new axiom,
no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.  `GQ2.lean` was not edited, so the
module is outside the umbrella; it elaborates against the mirror and every declaration was
`#print axioms`-measured (§5 below).

## 0.  What this lane did and did not do

It **stated** the `n`-free analogue of `ramifiedI_candidate_equiv_galK` and separated its
hypotheses into selectors and obligations.  It did **not** prove the general theorem, and the
module says so in its own docstring.  The one thing proved outright is the assembly step: that
the obligations, once supplied, compose to the conclusion.  That step was already `n`-free in
the tree (`candidate_equiv_galK_of_supply`, `KSupply.lean:451`); what was missing was a general
branch datum to instantiate it at, and a place to name what is owed.
**[W76-HOUSE, watch round 13: written here as `KSupply.candidate_equiv_galK_of_supply`, which
is not a name in the tree.  That theorem sits *after* `end KSupply` (`:380`), in
`namespace GQ2.Dyadic`, and all eight of its call sites write it bare.  The qualifier reads as
a namespace because this note uses real ones elsewhere (`KSupply.scalarHilbert_galK`,
`KSupply.ofMarkedCoreRealization`).  The file reference is what was meant and is now given as
one.]**

## 1.  What landed

### 1.1  §1, the third column of the constructor table

`SelectedPresentation` (`GQ2/Dyadic/SelectedWords.lean`) was already the R5 table at free
`(α, r, ε, η, h)` with `degree` and `word`.  It had no core column.

* `genAsmCore : SelectedPresentation → ProfiniteGrp`: `D_sq h` on `L`, `D_N α h` on both `N`
  rows, `D_M α h` on both `M` rows.
* `genAsmCoreIsProP`, `genAsmHandles`, `genAsmIsEven`.
* `genAsm_degree_odd` (`1 + 2h` on `L`), `genAsm_degree_even` (`2 + 2h` elsewhere),
  `genAsm_degree_parity`.  These are the degree-parity coherence: the same `h` indexes the
  degree and the core.

### 1.2  §2, the selector / obligation split

Three records over `K`, `B`, `FF`:

* `GenAsmFieldInputs K B FF n`: `Main.lean`'s `FieldInputs` with `params_n : params.n = 2`
  freed to `params.n = n`.  Six fields, every other one verbatim.
* `GenAsmBranch K B`: the **selector**.  Five fields: `pres`, `hdeg`, `nuP`, `hnuP`,
  `realization`.  `realization : MarkedCoreRealization (genAsmCore pres) nuP` is the direct
  `G_K(2)` spelling (`LabuteInterface.lean:313`; cited as `:308`, which is a `variable` line
  five above, W76-HOUSE round 13), i.e. the `KTwoN`/`KTwoM`/`KTwoSq` clause the
  critical-path memo §1.5 says the classification workstream actually produces.
* `GenAsmRowResidual G T`: the **obligations**.  Four fields: `exactLifting`, `stokes`,
  `determinant` at `galKProfinite K` (ASK, names taken from `KSupply`), and `cand`, the
  `WordCertificate` over the row's own slot (CAND).

Derived, not assumed, on `GenAsmBranch`: `degree`, `word`, `core`, `coreIsProP`, and `pro2`
(the composite `G_K ↠ G_K(2) ≃ core`, from `MarkedCoreRealization.pro2`).

### 1.3  §3, the statement

* `genAsm_candidate_equiv_galK_of_supply (S : SelectedPresentation) nuP hnuP W KS F`: the
  supply-facing form.  This is `Main.lean` §6's `candidate_equiv_galK_of_frozenRow_certificates`
  with the frozen five-row table replaced by the whole R5 table and `n = 2` replaced by
  `S.degree`.
* `genAsm_candidate_equiv_galK (G : GenAsmBranch K B) (F : GenAsmFieldInputs K B FF G.degree)
  (S : GenAsmRowResidual G F.T)`: the general-degree final theorem.  Conclusion
  `Nonempty (ContinuousMulEquiv (candidateGroup G.degree (qOf K FF) G.word) (GalK K))`.
  Proof: `KSupply.ofMarkedCoreRealization` on the selector, then the supply-facing form.

### 1.4  §4, the reconciliation

* **4.1** ten `rfl`s: each frozen row's word and core are definitionally the general table's at
  that row's pin (`genAsm_word_*`, `genAsm_core_*`), plus `genAsm_degree_frozen`,
  `genAsm_core_L`, and `genAsm_nonempty_equiv_L_core_piBd` (finding, §3.1 below).
* **4.2** five theorems stating the general-shaped conclusion at each frozen pin and proving it
  with the committed `rowEquiv_*` term (`genAsm_rowEquiv_*`).  That the committed proof terms
  typecheck against the general-shaped statements is the anti-drift check.
* **4.3** the classification join: `genAsm_evenRoute_output`, `genAsm_branch_of_evenN`,
  `genAsm_branch_of_evenM`, `genAsm_oddResidual_gives_mix`, `genAsm_branch_of_oddSq`,
  `genAsm_lNu_surjective`, `genAsm_branch_of_oddSq_canonical`.

## 2.  The reconciliation table

Every field of `Main.lean`'s six records, mapped or retired.

| `Main.lean` field | general counterpart |
| --- | --- |
| `FieldInputs.T` | `GenAsmFieldInputs.T`, verbatim |
| `FieldInputs.params` | `GenAsmFieldInputs.params`, verbatim |
| `FieldInputs.params_n : params.n = 2` | `GenAsmFieldInputs.params_n : params.n = n` |
| `FieldInputs.params_qK` | verbatim |
| `FieldInputs.ramified` | verbatim (the standing hypothesis; never to be discharged) |
| `FieldInputs.ramifiedData` | verbatim |
| pilot `hdeg`, `KSupply.hdeg` | `GenAsmBranch.hdeg`, at the row's own degree |
| pilot `fLab` | `GenAsmBranch.realization.equiv` |
| pilot `horient` | inside `GenAsmBranch.realization` (the `KTwo*` producer's clause) |
| pilot `hpair` | input to `marked_matching_certificate_KTwoN`, i.e. to `genAsm_branch_of_evenN` |
| pilot `piAb`, `hpiAb`, `hpiNu` | **RETIRED**: the abelianization slot exists only in the older `marked_matching_certificate_KN` spelling |
| `KSupply.pro2`, `hpro2`, `ker_pro2`, `nu_compat` | **DERIVED** from `GenAsmBranch.realization` (`MarkedCoreRealization.pro2`, `pro2_surjective`, `ker_pro2`, `nu_compat`) |
| `KSupply.hhom` | **RETIRED**: `rfl` at `standardNumerics n` in every degree |
| `KSupply.exactLifting` | `GenAsmRowResidual.exactLifting` |
| `KSupply.stokes` | `GenAsmRowResidual.stokes` |
| `KSupply.determinant` | `GenAsmRowResidual.determinant` |
| pilot `hexact`, `hstokes` | the same two ASK fields |
| pilot `hsimp`, `hsplit`, `hZcount`, `hdet` | inside `GenAsmRowResidual.cand` (through `sqrtNegTwoWordCertificate`) |
| `M`-row `exactLifting`, `stokes`, `scalar`, `determinant` | inside `GenAsmRowResidual.cand` (through `mWordCertificate` / `mpcWordCertificate`) |
| `M`-row `nuP`, `hnuP` | `GenAsmBranch.nuP`, `GenAsmBranch.hnuP` |
| `M`-row `hnuSigma`, `hnuWild` | inputs to the per-branch `WordCertificate` producer, not to the assembly |
| `ScalarHilbertCertificate` at `G_K` | absent from both records: `KSupply.scalarHilbert_galK` proves it, and its proof is `n`-free |

Net: the pilot's 13 fields become 2 selector fields plus 4 obligation fields plus whatever the
CAND producer still takes; the `M` rows' 9 (expanding to 17) become the same 6 plus the CAND
producer's four clauses.  Three pilot fields are retired outright.

## 3.  The memo's eight items, located

Items are `docs/dyadic/w74-critical-path.md` §3.

| # | item | where it now lives |
| --- | --- | --- |
| 1 | branch identification per field (`range chiCycKTwo = imChiN α`) | still open; it is the `α` pin the even route does not supply, flagged in `genAsm_evenRoute_output`'s docstring |
| 2 | the `KTwoN`/`KTwoM` adapter | **DONE this lane**: `GenAsmBranch` is spelled in `KTwo*` from the start, and `genAsm_branch_of_evenN`/`_evenM`/`_oddSq` are the adapters, all elaborating |
| 3 | `ExactLiftingSemantics` at `G_K` | `GenAsmRowResidual.exactLifting` |
| 4 | `StokesDualityCertificate` at `G_K` | `GenAsmRowResidual.stokes` |
| 5 | `AffineDeterminantCertificate` at `G_K` (LG5 ⇒ `GaussZResidueK`) ⚠⚠ | `GenAsmRowResidual.determinant` |
| 6 | the four analytic clauses at `GammaR n q word` | inside `GenAsmRowResidual.cand`, through the per-branch producers |
| 7 | the pilot's four candidate residuals | inside `GenAsmRowResidual.cand` on the `N0` row, at `(α, h) = (2, 0)` only |
| 8 | the `nuP` construction | `GenAsmBranch.nuP`/`hnuP`; producers `lNu h`, `mNu α h`, `mpcNu α r p` |

## 3.1  Findings

**F1.  The `n = 1` row does not come out unconditional, and the reason is a core mismatch.**
The brief expected the `L`/`n = 1` case to fall out unconditionally.  It does not.
`Main.lean` §6's `wordCertificate_nonempty_lSq` is unconditional but is a
`WordCertificate 1 2 (lSqW 0) PiBd _ nuTwo _`: its core is `Π` (`GQ2/BoundaryFrame.lean:142`,
relator `x₀^{σ²} x₀ [x₁,σ]`).  The constructor table's `L` row, `lCorePresentation`,
`marked_matching_certificate_KTwoSq` and the odd route's residual `SqLamMarkTransitivity h` all
live over `D_sq h` instead.  `PiBd = D_sq 0` is not `rfl`.

The equivalence does exist, and this lane builds it from committed pieces
(`genAsm_nonempty_equiv_L_core_piBd`): `D_sq 0 ≃ D_R` (`SqCore.sqEquivDRMarked`), `D_R ≃ D₀`
(`SqCore.nonempty_equiv_DR_D0`, the rank-three Labute equivalence with `bLab`'s four
antecedents discharged), `D₀ ≃ Π` (`SectionThree.d0PiEquiv`, paper Cor. 3.12).  What does not
exist is a **`WordCertificate` core transport** along such an equivalence: the tree has none
(`CertificateMain.lean` has `toSource` and nothing else), and the record's core-dependent fields
(`coreRel`, `proTwoWord`, `pro2`, `ker_pro2`, `hpro2`, `compat`) do not move on their own.  That
single restatement is the whole distance between the committed `n = 1` endpoint and the general
statement's `L` row at `h = 0`.

**F2.  The CAND layer has a free-parameter producer on one row out of five.**  Recounted at this
tree: `GQ2/` contains exactly four `def`s whose value is a branch row's `WordCertificate`
(`wordCertificateLSq`, `sqrtNegTwoWordCertificate`, `mWordCertificate`, `mpcWordCertificate`),
plus one format converter at `n = 1` (`WordCertificateRN.toWordCertificateStandardOne`) and the
consumer `WordCertificate.toSource`.  Their coverage over the general table:

| row | producer | coverage |
| --- | --- | --- |
| `M0 α h` | `Instances.MCompactCore.mWordCertificate α h q` | free `(α, h)`, four clauses carried |
| `Mpc α r ε η h` | `Instances.MProcyclicCore.mpcWordCertificate α r p q` | `h = 0` only (the `h` slot is literally `0` in the signature) |
| `N0 α h` | `SqrtNeg2.sqrtNegTwoWordCertificate` | `(α, h) = (2, 0)` only, at the single frozen word |
| `Npc α r η h` | none | none |
| `L h` | none over `D_sq h` | see F1 |

The memo's item 6 says the four analytic clauses are "one statement per clause, uniform in the
row", which is true of the *clauses*; it is not true of the *producers* that turn them into a
`WordCertificate`.  Generalising the compact-`N` producer off `(2, 0)` is the largest single
piece of CAND work the memo does not name, and the `Npc` row has no producer at all, which is
the certificate-side echo of `Main.lean`'s `no_frozen_Npc`.

**F3.  The `M`-row records are not derivable from the general one in the selector direction, and
this is structural, not a defect.**  A `ResidualSqrtTwo` carries a `KSupply`, whose four pro-`2`
data fields are a *surjection with the right kernel*; the general branch datum carries an
*equivalence* `core ≃ G_K(2)`.  The tree has `KSupply.ofMarkedCoreRealization` (equivalence ⇒
supply) and no converse.  So the general theorem's **supply-facing** form
(`genAsm_candidate_equiv_galK_of_supply`) is the one the committed quadratic rows feed, and the
**classification-facing** form is the one the even/odd routes feed.  Both are stated; they meet
at `ofMarkedCoreRealization`.  The anti-drift check in §4.2 is therefore done at the level of
the conclusion, which is where drift would actually show: the five committed `rowEquiv_*` terms
typecheck against the general-shaped statements at their pins, unchanged.

**F4.  `KSupply.hhom` is definitional in every degree, not just at `n = 2`.**  The memo marks it
"`rfl` at the slot".  It is `rfl` at `standardNumerics n` for free `n` (`homScalar := 2 ^ (n + 2)`,
`Recursion/Numerics.lean:79`), so the general record retires it rather than carrying it.  The
assembly passes `rfl` at the general degree and elaborates.

## 4.  The classification join, stated

**Even route.**  `EvenParity.parityFinal_evenClassification` (`Instances/EvenParityModel.lean:156`)
gives, at a ramified-`i` `K` with `[K : ℚ₂] = 2 + 2h`:

> `∃ α, 2 ≤ α ∧ (Nonempty (OrientedContinuousMulEquiv (chiM α h) chiCycKTwo) ∨
>  Nonempty (OrientedContinuousMulEquiv (chiN α h) chiCycKTwo))`

`genAsm_evenRoute_output` re-exports this with the degree hypothesis written as
`Module.finrank ℚ_[2] K = (SelectedPresentation.N0 2 h).degree`, which is the same statement by
`rfl`.  So the route's hypothesis **is** the general branch datum's `hdeg` on any even row, and
its conclusion **is** the `(f, horient)` pair the `KTwo*` producers consume.
`genAsm_branch_of_evenN` and `genAsm_branch_of_evenM` complete the join: they take that pair
plus the producer's own remaining binders (`hpair` on `N`; `MMixHypothesis` and `hpivot` on `M`)
plus a `Ztwo` marking agreeing with `nuN`/`nuM`, and return a `GenAsmBranch` pinned to the row.

What the even route does **not** supply is the `α` pin: it produces an existential and the
branch datum asks for a row.  That is memo item 1 and it stays open.

**Odd route.**  `SqCore.SqLamMarkTransitivity h` (`SqCore/DsqDemushkin.lean:424`, the target of
waves 68-73) gives `SqCore.SqHandleMixFixesCore h c` at every `h ≥ 1` and every unit `c`
(`sqHandleMixFixesCore_of_lamMarkTransitivity`).  `genAsm_oddResidual_gives_mix` restates that,
and `genAsm_branch_of_oddSq` shows it is exactly the `hMix` binder of
`marked_matching_certificate_KTwoSq_of_fixesCore`, hence of the `L`-row branch datum.
`genAsm_branch_of_oddSq_canonical` then fixes the marking to the canonical `lNu h`, discharging
both marking binders (`genAsm_lNu_surjective`, and `LSquare.ztwoIota_lNu`, which already existed
in `Instances/GammaLSylowPreimageRealizationBypass.lean:82`).  So on the odd side the general
selector reduces to exactly four things: the degree pin, an oriented equivalence
`D_sq h ≃ G_K(2)`, `SqLamMarkTransitivity h`, and the two `ν` normalizations at `σ` and `x₀`.

This is worth stating plainly because the critical-path memo lists the whole `Sq` graded
programme as *not* on the path.  That is correct **for the frozen quadratic table**, which is
even-degree at `h = 0`.  It is not correct for the general statement: `SqLamMarkTransitivity h`
is a named input to the general `L` row's selector at every `h ≥ 1`.

## 5.  Axiom posture

Every declaration measured with `#print axioms` against the mirror.  No new axiom, nothing
outside what the cited inputs already carry.

* std-3 `[propext, Classical.choice, Quot.sound]`: `genAsmCore`, `genAsmCoreIsProP`,
  `genAsmIsEven`, `genAsm_degree_odd`, `genAsm_degree_even`, `genAsm_degree_parity`,
  `GenAsmFieldInputs`, `GenAsmBranch` and its five projections, `GenAsmRowResidual`, all ten
  `genAsm_word_*`/`genAsm_core_*`, `genAsm_core_L`, `genAsm_nonempty_equiv_L_core_piBd`,
  `genAsm_branch_of_evenN`, `genAsm_branch_of_evenM`, `genAsm_oddResidual_gives_mix`,
  `genAsm_branch_of_oddSq`, `genAsm_lNu_surjective`, `genAsm_branch_of_oddSq_canonical`.
* no axioms at all: `genAsmHandles`, `genAsm_degree_frozen`.
* std-3 ∪ {B6 `tateDualityAt`, B1 `absGalQ2_isTopologicallyFinitelyGenerated`,
  B7 `absGalQ2_localEulerCharacteristic`}: `genAsm_candidate_equiv_galK_of_supply`,
  `genAsm_candidate_equiv_galK`, and the four `M`-row `genAsm_rowEquiv_*`.
* the same plus {B9 `hilbertSymbol_normCriterion_finiteDyadic`,
  B11a `relativeStiefelWhitney_dyadic`}: `genAsm_rowEquiv_sqrtNegTwo`.
* the same plus {B9}: `genAsm_evenRoute_output`.

These are exactly the sets `Main.lean` §5 already prints, so the general statement costs no
census movement.

## 6.  What the statement wave's finish needs

1. **A `WordCertificate` core transport** along a marked core equivalence (F1).  One
   restatement; it closes the gap between the committed `n = 1` endpoint and the general `L`
   row at `h = 0`, and it is reusable wherever a classification output lands on a different
   presentation of the same core.
2. **The compact-`N` word certificate at free `(α, h)`** (F2), i.e. the `nWordCertificate`
   sibling of `mWordCertificate`.  Until it exists the general statement's `N0` row has a CAND
   producer only at the pilot's pin.  The `Npc` row needs one built from scratch, and the
   procyclic-`M` one needs lifting off `h = 0`.
3. **The `α` pin** (memo item 1, unchanged): `range chiCycKTwo = imChiN α` per field, which
   turns the even route's existential into the row.  Nothing in this lane moves it.
4. ~~**Registration.**  `GQ2/Dyadic/GeneralAssembly.lean` is not in `GQ2.lean` (lane protocol
   forbade editing it).  A later wave should add it so the umbrella carries the statement.~~
   **[W76-HOUSE, watch round 13: DONE, in this wave, `1 min 28 s` after this note.**  The
   orchestrator registered the module at `a19fac5a` (04:18:12), against the lane's last commit
   `88a29ef7` (04:16:44).  The item was stale as written, which is the fourth wave running for
   this exact finding; the convention adopted in W76 is that a lane note's claim about
   `GQ2.lean` is written **as of** the lane's last commit, and §0's "`GQ2.lean` was not edited"
   should be read that way.]**
5. Nothing on the `L`-row marking: the bridge `ztwoIota (lNu h x) = nuSq h x` already existed
   (`LSquare.ztwoIota_lNu`) and this lane wires it in, so `genAsm_branch_of_oddSq_canonical`
   carries no marking binder at all.
