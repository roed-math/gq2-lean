# W76-CERT: the certificate plumbing for the general-degree statement

Lane W76-CERT.  Produced against tree `97d51e93` (branch `claude/w76-cert`), shared cache at the
4344-job green umbrella.  Verification of record: `scripts/mirror.sh` (sweep, gen, check).
**No `lake` command was run.**

One new module, `GQ2/Dyadic/GeneralCertificates.lean`, prefix `genCert`, 778 lines, 48
declarations.  No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no
`maxRecDepth`.  `GQ2.lean` was not edited and no existing module was touched, so the module is
outside the umbrella; it elaborates against the mirror and every declaration was
`#print axioms`-measured (§6 below).

## 0.  What this lane did

Four tickets, all four landed.  The lane's job was to make the general-degree theorem
(`GQ2/Dyadic/GeneralAssembly.lean`, lane W75-STATE) able to consume the tree's committed
certificate producers.  The `CAND` field of `GenAsmRowResidual` is a `WordCertificate` over the
row's own core; W75 found that on four of the five rows nothing could reach it.  This lane fixes
three of the four, opens the fourth, and diagnoses the one obstruction that is genuinely a
residual rather than a missing construction.

| ticket | status |
| --- | --- |
| T1 `WordCertificate` core transport | **landed**, with the `L`-row corollary unconditional |
| T2 compact-`N` producer at free `(α, h)` | **landed**, at free `(α, h, q)` and with no `α` bound |
| T3 procyclic-`M` off `h = 0` | **landed** at every `.hat` display; residual named, and diagnosed |
| T4 (stretch) `Npc` producer | **landed** at free `(α, r, h, q)` at the `⟨1, 1⟩` display |

## 1.  T1, the core transport

`WordCertificate.genCertTransport (W) (hP₂) (e : P₁ ≃ P₂) (hnu : ∀ x, ν₂ (e x) = ν₁ x)`.

### 1.1  Why it works, in one sentence

The core enters the record only through the boundary `boundarySubgroupQ q νP` and the boundary
frame `BoundaryFrameK q P H E` (whose only `P`-dependent field is `psiBar : P → E`), and every
downstream recursion object factors through the *composite* `F.frameMap ∘ b : Γ → H × E` rather
than through `P`.

The module makes that factorisation explicit in three layers.

* **§1** `genCertBdHom`/`genCertBdPull` move the boundary map backwards along a hom of cores;
  `genCertFramePull` moves the frame backwards; `genCertFrameMap_pull` says the two moves cancel
  on `frameMap`.  The frame pullback keeps `alpha`, `alpha_surjective` and `exponent_two` as the
  original frame's own fields, which is what leaves the entire block layer (`blockEnrichmentDK`
  and everything it calls, all of which read `F` only through `F.alpha` and
  `F.alpha_surjective`) **definitionally** unchanged.
* **§2** is stated at a bare hypothesis `hfm : ∀ γ, F₁.frameMap (b₁ γ) = F₂.frameMap (b₂ γ)`,
  not at the pullback.  That is deliberate and load-bearing: the determinant clause's boundary
  map is not the pulled-back one (it is rebuilt from the certificate's own `pro2`), and there
  `hfm` holds by `rfl` with no `apply_symm_apply` at all.  The key object is
  `genCertBdLiftEquiv`, the bijection of `BoundaryLiftsK`: it is the **identity on the underlying
  `ContSurj`**, so `LiftsOverK`, `rhoPrimeK` and the `mBK` fibre condition, all of which read a
  lift only through `ρ.1.1`, are literally the same objects on both cores.  Only
  `exactImageCountK` and `mBK` need a `Nat.card_congr`.
* **§3** transports the three core-dependent analytic clauses.

### 1.2  Finding: the state note's field split is wrong by two

`docs/dyadic/w75-state-note.md` §3.1 (F1) names six core-dependent fields, `coreRel`,
`proTwoWord`, `pro2`, `ker_pro2`, `hpro2`, `compat`.  Checked against the Lean, **`coreRel` and
`proTwoWord` are not core-dependent**: both quantify over *every* pro-`2` group
(`coreRel : ∀ (G : Type) [Group G] … , Marking n G → G`) and mention no core.  They move
verbatim.  The true split of the seventeen fields is

* **ten mention no core**: `tameSpecialization`, `coreRel`, `proTwoWord`, `tfg`, `smulZmod2`,
  `contSMulZmod2`, `htriv`, `scalar`, `htame`, `hwild`;
* **four move by naturality**: `pro2` (post-compose), `ker_pro2` (`e` injective adds no kernel),
  `hpro2` (`e` onto), `compat` (the *only* place the marking compatibility `hnu` is used);
* **three are the analytic clauses**, and they are the whole of the work.

`ScalarHilbertCertificate` needed no transport lemma at all: it is the same `Prop` on both sides.

### 1.3  The acceptance test

`genCert_wordCertificate_nonempty_L_zero`: the general constructor table's `L` row at `h = 0`
carries an **unconditional** `WordCertificate` over its own core `D_sq 0`, at the marking
`genCertLNu`.  This is `Main.lean` §6's `wordCertificate_nonempty_lSq` (which lives over `Π`)
moved along `genAsm_nonempty_equiv_L_core_piBd`, and it closes item 1 of the W75 note's §6 at
`h = 0`.

`genCert_candidate_equiv_galK_L_zero` consumes it: at a `K` with `q_K = 2`, the `n = 1` case of
`genAsm_candidate_equiv_galK_of_supply` on the `L 0` row asks for the arithmetic supply `KS` and
the field inputs `F` and nothing else, i.e. `GenAsmRowResidual`'s three `ASK` fields rather than
its four.

⚠ Two honest limits, both stated in the module.  (a) The transported marking `genCertLNu` is
`ν₂ ∘ genCertLEquiv`; it is **not** claimed to be the canonical `lNu 0`, and no such comparison
exists at this tree (`LSquare.ztwoIota_lNu` compares `lNu` with `nuSq`, not with `nuTwo` across
the equivalence).  (b) The residue pin `q_K = 2` is carried as a hypothesis; a degree-`1` `K` is
`ℚ₂` so it is a coherence condition rather than a new obligation, but the lane did not prove the
implication.

## 2.  T2, the compact-`N` producer

`genCertNWordCertificate (α h q) (hq0) (hqe) (nuP) (hnuSigma) (hnuWild) (four clauses)` at
`WordCertificate (2 + 2h) q (nCompactW α h) (DN α h) (isProP_DN α h) nuP SN`.

Same posture as `mWordCertificate`: thirteen fields proved, the four analytic clauses as
explicit arguments (the certificate-to-count bridge does not exist at the candidate carrier).

Two findings against the M template.

* **No `1 ≤ α`.**  The `M` row carries `hα` because WM0-a's Gate-C headline needs `2m = 2^α`.
  Nothing on the `N` side does: `nCorePresentation`, `eval_pro2_nCompact` and
  `tameSpecializes_nCompact` are all free in `α`.  The producer therefore has **no `α` bound at
  all**.
* **The missing piece was `coreRel`/`proTwoWord`.**  The tree's only `N`-row statement of that
  shape is `Count.PilotN.eval_pro2_nCompact_reindex`, which carries `[T2Space G]` because it is
  written through `CoreReindex.toCore`, whose binder list has one; `WordCertificate.coreRel` has
  none.  §6 re-derives the pair from `Words.eval_pro2_nCompact` directly, exactly as the `M` row
  does through `mCoreMark`.  `SqrtNeg2`'s pilot writes the same trick inline at `(2, 0)`.

Two further items land with it: `genCertNNuZtwo_surjective` (the missing twin of
`SqrtNeg2.pilotNuP_surjective` at free `(α, h)`, a one-liner nobody had stated), and
`genCertNWordCertificateCanonical`, the producer at the canonical marking with all three marking
binders discharged.

## 3.  T3, the procyclic-`M` lift, and its diagnosis

**The diagnosis** (the W75 note flagged the hole without one).  The `h = 0` pin on
`Instances.MProcyclicCore.mpcWordCertificate` is **not** in the word layer, not in Gate B, not in
the core `D_M`, and not in the Fox or Stokes layers.  Every one of those is already free in `h`:
`Words.Mpc.eval_pro2_mpcW`, `Count.tameSpecializes_mpcW`, `Count.hwild_mpcW`, `isProP_DM`,
`presentedBy_DM`, `dm_relation`, `Certificates.MProcyclic.mpc_stokesDuality`.  The pin is the
`CoreReindex` dictionary `Instances.MProcyclicCore.mpcReindex` (`Instances/Cores.lean:882`),
stated at `Fin (coreRank 0)` and proved by `fin_cases`; at symbolic `h` its four obligations are
blocked on `(k : Fin (2 + 2h + 1)).val = k % (2h + 3)`.  The compact-`M` row escapes only because
`mReindex` factors through `nReindex`.

**And the block is already bypassed in the tree.**  `mpcCorePresentationUnit`
(`Instances/MpcCoreUnit.lean:381`) is a `CorePresentation` at *every* `h` and every `2`-adic
unit, built from the arbitrary-unit dictionary rather than from a `CoreReindex`.  What it is
stated over is `mpcWUnit`, not the constructor table's `mpcW`.  So the lift is a **word-syntax**
question, not a structural one, and the lane names it:

`GenCertMpcDisplayWordEq α r p h η dsp : Prop := mpcWUnit α r p η h = mpcW α r p dsp h`

* discharged at every `.hat` display, at every handle count
  (`genCertMpcDisplayWordEq_hat`, from `Words.Mpc.mpcWUnit_eq_hatDisplay`);
* open at `.one` and `.lit`, where only the evaluated form `eval_mpcWUnit_eq_display` is
  available.

Given it, `genCertMpcWordCertificate` is the producer at the table's word, at free `(α, r, p, q,
h)`, with the same thirteen-of-seventeen posture.  `1 ≤ α` is genuine here (it is
`eval_pro2_mpcWUnit`'s and `tameSpecializes_mpcW`'s own hypothesis).

`WordCertificate.genCertWordTransport` (a `WordCertificate` moves along an equality of `PWord`s)
is landed alongside; it is trivial, and named because the `Mpc` lift is what consumes it.

## 4.  T4, the procyclic-`N` producer

`genCertNpcWordCertificate (α r h q) (hq0) (hqe) (nuP) (hnuSigma) (hnuWild) (four clauses)` at
`WordCertificate (2 + 2h) q (npcW α r h ⟨1, 1⟩) (DN α h) (isProP_DN α h) nuP SN`.

The W75 note records `Npc` as the one row with no `CAND` producer at all.  It was not missing its
inputs: `Instances.NProcyclicCore` already carries the `η = 1` dictionary at every handle count
(`npcReindexOne`, `npcCoreRelOne`, `npcProTwoWordOne`, `npcCorePresentationOne`,
`Instances/NpcCore.lean:542-593`), and Gate B and the wild discharge are free in every parameter.
So the row's first producer is assembly, and it has no `α` bound either.

⚠ Not covered: an arbitrary `EtaData`.  `npcCorePresentationUnit` is the arbitrary-unit
presentation at every `h` but is stated over `npcWUnit`, so the row's residual is the exact
analogue of `GenCertMpcDisplayWordEq`.  Naming it and building the arbitrary-display producer is
W77 work.

## 5.  The coverage table, before and after

W75's table (`GeneralAssembly.lean:266-273`, `w75-state-note.md` F2) against this tree:

| row | before | after |
| --- | --- | --- |
| `M0 α h` | free `(α, h)`, `1 ≤ α` | unchanged |
| `Mpc α r ε η h` | `h = 0` only | free `h`, at every `.hat` display (`GenCertMpcDisplayWordEq` otherwise) |
| `N0 α h` | `(α, h) = (2, 0)` only | free `(α, h)`, **no `α` bound** |
| `Npc α r η h` | none | free `(α, r, h)` at the `⟨1, 1⟩` display |
| `L h` | none over `D_sq h` | unconditional at `h = 0`; `h ≥ 1` needs the `D_sq h ≃ Π_h` analogue |

The four producers all take the same four analytic clauses as arguments, so what the `CAND`
layer now owes is uniform across the four even rows: `ExactLiftingSemantics`,
`StokesDualityCertificate`, `ScalarHilbertCertificate` and `AffineDeterminantCertificate` at the
candidate carrier.  That is the shape the W75 note's item 6 predicted for the *clauses*; it is
now also true of the *producers*, which is what F2 said it was not.

## 6.  Axiom posture

Every declaration measured with `#print axioms` against the mirror.  No new axiom.

* **no axioms at all**: `genCert_L_zero_degree`.
* **`[propext, Quot.sound]`**: `genCertNCoreMark`.
* **std-3 `[propext, Classical.choice, Quot.sound]`**: the other 44 declarations, including every
  transport lemma, all four row producers, and `WordCertificate.genCertTransport` itself.
* **std-3 plus `{dyadicOrientation, localReciprocity, peripheralCyclotomicAction}`**:
  `genCert_wordCertificate_nonempty_L_zero`.  This is **exactly** the print of its input
  `wordCertificate_nonempty_lSq`, so the core transport costs zero axiom movement.
* **the same plus `{tateDualityAt, absGalQ2_isTopologicallyFinitelyGenerated,
  absGalQ2_localEulerCharacteristic}`**: `genCert_candidate_equiv_galK_L_zero`.  This is exactly
  the union of the previous set with `genAsm_candidate_equiv_galK_of_supply`'s own print.

So the whole lane costs no census movement: the two arithmetic-facing declarations print the
union of their inputs' sets, and everything else is std-3.

## 7.  What is left, for W77

1. **`L h` at `h ≥ 1`.**  The transport is general; what is missing is the equivalence.
   `genAsm_nonempty_equiv_L_core_piBd` builds `D_sq 0 ≃ Π` from `sqEquivDRMarked`,
   `nonempty_equiv_DR_D0` and `d0PiEquiv`, all of which are `h = 0` objects.  There is no
   `Π_h` and no committed unconditional `n = 2h+1` certificate to transport, so this is not
   plumbing but new mathematics.
2. **The `Mpc`/`Npc` word-syntax residual.**  `GenCertMpcDisplayWordEq` at `.one` and `.lit`,
   and its unnamed `Npc` analogue.  `SemanticSelected.lean:179`'s
   `Words.Mpc.GammaR_mpcWUnit_eq_display` shows the *presented groups* already agree at any
   compatible display; what a `WordCertificate` needs is the equality one level down, at the
   `PWord` index.  A refinement of `genCertWordTransport` that asks only for the evaluated
   agreement (`freeMarking`-level, which `SelectedEta.lean` already has) would close it.
3. **The four analytic clauses at the candidate carrier**, now the uniform residual on all four
   even rows.  `Instances/N0Exact.lean` has `exactLifting` at free `(α, h)` but at the degree
   spelling `2*h+2` rather than the record's `2+2*h`; that mismatch is a cast, not a gap, and is
   worth closing so the `N0` row's `exactLifting` argument can be discharged rather than passed.
4. **Registration.**  Neither `GeneralAssembly.lean` nor `GeneralCertificates.lean` is in
   `GQ2.lean` (lane protocol forbade editing it).  A later wave should add both.
   **[W77-HOUSE, ticket 3, STALENESS: DONE, and half of it was already done when this item was
   written.**  At `1d3d5a84` both are registered: `GQ2.lean:857` `import GQ2.Dyadic.GeneralAssembly`
   and `GQ2.lean:858` `import GQ2.Dyadic.GeneralCertificates`.  `GeneralAssembly` was registered by
   `a19fac5a` at 04:18, and this lane's base is `97d51e93` (04:59), so **the registration was
   already in the lane's own base** and the word "Neither" was wrong when written, not merely
   overtaken.  `GeneralCertificates` was registered by `b1bc9d48` at 05:35, one minute after this
   note was committed (`edd7dd7a`, 05:34) and immediately after the lane merged.  The sibling
   module `SqCore/GradedJoinBase.lean` was likewise registered at 05:37 (`681ce981`,
   `GQ2.lean:777`).  **Nothing is left of this item.**  For the wave-78 checklist: "is my module
   registered" is a one-line grep of `GQ2.lean` and belongs in the staleness pass, since the
   owner registers modules within the hour and lane notes are written against a frozen base.]**
5. **The canonical `L` marking.**  Comparing `genCertLNu` with `Instances.LSquareCore.lNu 0`
   would let `genAsm_branch_of_oddSq_canonical` and the `L`-row certificate meet at one marking.
