# L1 — Labute-campaign statement freeze: design memo

**Date**: 2026-07-25 · **Worker**: Fable (L1) · **Ticket**: L1 of `labute-plan.md` §4.
**Upstream**: `labute-spike.md` (GREEN, commit db7003a) — its §4 freeze list is binding here.
**Deliverables**: this memo + four compiling sorry-skeletons, **statements final**:

| file | lines | sorries | proven (non-sorry) decls | fill ticket(s) |
|---|---:|---:|---|---|
| `GQ2/Roe/Labute/TwoCentralTower.lean` | 353 | 15 | 12 (defs + 8 smoke) | L2 |
| `GQ2/Roe/Labute/Levelwise.lean` | 343 | 20 | 15 (defs + 5 smoke) | L3 + L4a (split below) |
| `GQ2/Roe/Labute/StageLemma.lean` | 353 | 16 | 10 (defs + 6 smoke + **2 stage steps**) | L4a + L4b |
| `GQ2/Roe/Labute/Assembly.lean` | 194 | 5 | 7 (incl. **`bLab` itself**) | L5 |

Commits: `66fd908`, `40b1332` (tower + convention note), `1160e59` (levelwise),
`0de9635` (stage), `d725f7a` (assembly).  Each `GQ2.lean` import landed with its file.
Namespace (uniform): **`GQ2.Roe.Labute`**.

**Statement-freeze contract.**  L2–L5 fill `sorry`s only.  A fill that *needs* a statement
change is a process failure: stop, report loudly to the orchestrator, do not patch
silently.  The two `stageStep*` theorems and `bLab` are already **proven against the
frozen statements** — they are the composability certificate: any statement drift breaks
them first.

---

## 1. What is frozen, and where it comes from

### 1.1 TwoCentralTower — the λ-tower (plan §2.4 Tier F; spike §1, §2.1, §4.1)

* `twoCentralSucc H = cl(⟨squares of H⟩ ⊔ ⁅H, ⊤⁆)`; `twoCentralSeries G k` **1-based**
  (`λ₁ = ⊤`, junk `λ₀ = ⊤`) so every k in the file = every k in the memos (`k₀ = 3`,
  `m(k) = k`, threshold `k ≥ 3`, `2^{k-1}`-tails).  The `k = 0` junk value is harmless:
  no statement below `k = 1` carries content.
* `levelQuot G k = G ⧸ λₖ` (abbrev), `levelMk`, `levelProj` (+ proven `rfl`-naturality and
  surjectivity), `canonLift` = `Function.surjInv` section (+ proven section identity).
* `lambdaImage G j k = λⱼλₖ/λₖ ≤ Qₖ` two-index images; `zLayer G k := lambdaImage k (k+1)`
  (the memo's `Zₖ`, realized inside `Q_{k+1}` — the encoding all defect/span/SL statements
  use; `zLayer_eq_ker_levelProj` pins it as the projection kernel).
* Structure (L2 sorries): normality (+ *instance* riding on it — quotient groups exist
  from day one), antitonicity, closedness (proven), centrality + exponent-2 of `zLayer`,
  openness/finiteness/2-group-ness of the levels under `(hfg, hpro)`, **cofinality**
  `exists_twoCentralSeries_le` (the assembly's bridge), `⨅ λₖ = ⊥`, functoriality
  (`map_le` any continuous hom; `map_eq` for compact-to-T2 epis — the descent mechanism).
* χ-shadow layer: `twoCentralSeries_units_le` (`λₖ(ℤ₂ˣ) ⊆ ker(mod 2^{k+1})`, `k ≥ 2` —
  the spike's modulus lemma, ⊆ only), `chiShadow_eq_one_of_mem`, and
  `chiLevel χ k : Qₖ →* (ZMod 2^k)ˣ` (total in `k`; proven `rfl`-evaluation on residues)
  with naturality `chiLevel_levelProj` along the tower.

**Hypothesis spellings frozen**: t.f.g. is
`∃ s : Finset G, (Subgroup.closure (s : Set G)).topologicalClosure = ⊤` (the
`profinite_hopfian` shape — discharged at the instances by `drFinsetTopGen` /
`d0FinsetTopGen`); pro-2 is `IsProP 2 G` (discharged by `isProP_DR` / `d0_isProP`).

### 1.2 Levelwise — sets, defect, base cases (spike §2.4 FINAL FORM, §3.1, §3.4, §4)

* `d0Word a s y = a²s⁴[s,y]` (repo `commP`), the `r₀`-mirror of the in-tree `drWord`;
  definitionally the relator expression of `d0LiftHom`, so triples-⟺-homs needs no
  rewriting.  Proven: naturality, abelian collapse, `d0Word_eq_one` on `(A,S,Y)`.
* χ-data: `negThreeUnit` (+ proven value pin `= -3`), `etaUnit = negThreeUnit⁻¹`
  (η = (1−4)⁻¹), **`chiD0pres`** — the direction-2 character `(A,S,Y) ↦ (−1,1,η)` built
  from `d0LiftHom` **at the presentation** (see §4.1: the in-tree `chiD0G` is
  B3c-assembled and census-forbidden here), with three sorried generator-value pins.
* Targets: `chiTargetUnitsR0 = ![-1, 1, etaUnit]`, `chiTargetUnitsR2 =
  ![SvalUnit, rootXUnit, YvalUnit]` (R10/R11's Hensel-root data — the only place `f = 2`
  enters, per the spike); `chiTargetR0/R2 k` their mod-`2^k` reductions; numeric pins
  frozen as statements: mod-8 `(7,1,5)` / `(5,5,7)` (level-3 load-bearing) and mod-`2^9`
  `(511,1,341)` / `(253,437,7)` (stress).  **The mod-`2^9` values were independently
  re-verified by hand during L1** (root check `437³+2·437²+1 ≡ 0 (512)`, `S ≡ −13·431⁻¹ ≡
  253`, `Y ≡ −505 ≡ 7`, `η ≡ −171 ≡ 341`) — they will not move.
* Sets (three clauses, spike §2.4 verbatim): `sZeroR0/sZeroR2` (relator kill + plain
  `Subgroup.closure (Set.range T) = ⊤` — the quotients are finite, so plain closure is
  the honest clause) and `sPR0/sPR2` adding the χ-clause
  `∀ i, chiLevel χ k (T i) = chiTarget k i` at modulus `2^k = 2^{m(k)}`.
* Defect via `canonLift` (`defectR0/R2`), lift-independence (`*_eq_of_lift` — stated
  hypothesis-free: no relator-kill, no threshold; the central-kernel computation needs
  neither), membership in `zLayer` under the relator clause only, restrictions
  `sPR0_levelProj`/`sPR2_levelProj` (all three clauses weaken).
* Base `k₀ = 3`: `witnessR0 = (y, s·x, x)` in the `(A,S,Y)`-slots, `witnessR2 = (S·Y, Y, A)`
  in the `(s,x,y)`-slots (spike §3.1/§3.4; slot-consistency against the mod-8 pins was
  re-derived during L1 — χ-values match targets exactly), sorried memberships +
  **proven** `Nonempty`-packagings.  Level-4 stress words recorded in a comment for L3
  (deliberately *not* frozen as statements — see §3.6).
* Tower-size regression pins (spike §1 table): `|Q₂| = 8`, `|Q₃| = 256`, `|Z₁| = 8`.
* Smoke: `sPR0_one_nonempty` **proven** — the trivial triple inhabits the level-1 set
  (all three clauses degenerate), an end-to-end elaboration test of the set definition.

### 1.3 StageLemma — calculus, span, SL1/SL2 (spike §2.1–2.5, §4.3–4.5, §4.8)

* Shift words `dbarWordR0 (a,s,y) w = w₁²[w₁,a][w₂,y][w₃,s]` and
  `dbarWordR2 (s,x,y) (u,v,w) = w²[w,y][u,x][v,s]` — the spike §2.2 formulas with one
  multiplicative order fixed (immaterial after centrality, which is a theorem, not part
  of the def).  Proven smoke: naturality, abelian collapse (`= w₁²`), value 1 at trivial
  modification.
* Congruence calculus, generic over profinite `G`, `k ≥ 3` (4 sorries, L4a):
  `*_congr_slots` (Frattini-only dependence on the triple — spike §4.3's "worth its own
  lemma") and `*_congr_mod` (`Z_{k-1}`-class dependence on the modification).
* Shift formulas `defectR0_mul`/`defectR2_mul` (L4a): modification by `levelProj ∘ w`
  multiplies the defect by `dbarWord` at the canonical lift — stated **relator-free**
  (the identity is pure `k ≥ 3` λ-calculus).
* Modification stability `sPR0_mul_mem`/`sPR2_mul_mem` (L4a): `λ_{k-1}`-moves preserve
  all three clauses (the χ-clause survives because `χ(λ_{k-1}) ⊆ 1 + 2^kℤ₂` — the design
  reason P works).
* **Span theorem** (L4b): `freeProTwo` (= pro-2 completion of `F₃`) + `freeGen`;
  `span_free_r0/r2`: `Zₖ(F₃) ≤ closure(d̄-image over λ_{k-1}-modifications ∪ two tails)`,
  `k ≥ 3`, with the **relator-adapted tail pairs** (r₀: slots 1,2 = `(S,Y)`;
  r₂: slots 0,1 = `(s,x)`) and the **`2^{k-1}` exponent** (Serre §7 erratum, spike §2.3)
  baked into the statements; `span_descent_r0/r2` at *any generating triple* of the
  towers.  Only `≤` is frozen (no consumer needs `=`).
* **SL1** (L4b): `∃ w ∈ (λ_{k-1}-image)³, d̄_T(w) = (δ(T))⁻¹` — existential form, inverse
  right-hand side (see §3.4).  **SL2** (L4a): given `δ(T) = 1`, a `ker d̄`-modification of
  the canonical lift lands in `S^P_{k+1}` — the memo's `(ℤ/2)²`-ontoness in consumed form
  (see §3.5).
* **`stageStepR0/R2` proven in L1** from SL1 → shift → stability → SL2 — the
  composability certificate, and the only stage-lemma statement Assembly consumes.

### 1.4 Assembly — epis, Hopfian, `bLab` (plan §2.1 items 2–3; spike §4.7)

* `drFinsetTopGen`/`d0FinsetTopGen` proven (Finset-packagings of `dr_topGen`,
  `SectionThree.topGen_d0`).
* **`exists_contSurj_of_levelwise_nonempty`** (L5): the generic statement whose proof is
  lines 224–309 of `exists_contSurj_of_card_le` verbatim — the two `haveI`s promoted to
  hypotheses `(hne, hfin)` over `U : OpenNormalSubgroup (ProfiniteGrp.of R)`.
  **L5 relocation protocol** (byte-identical-consumers gate): prove it *inside*
  `GQ2/Reconstruction.lean` (module file; the statement is mathlib-only), re-derive
  `exists_contSurj_of_card_le` from it via `contSurj_quotient_nonempty_finite`, keep
  `reconstruction`/`reconstruction_of_equinum` and all consumers byte-identical, then
  discharge the Assembly sorry by a one-line application.  The Labute-namespaced
  statement here stays the consumer-facing frozen form regardless.
* `finite_contSurj_quotient` **proven** (t.f.g. source ⇒ finite level sets — the
  `reconstruction_of_equinum` pattern).
* `sPR0_nonempty`/`sPR2_nonempty` `∀ k` (L5: base + `stageStep` upward, restrictions
  downward — all inputs frozen; the `∀ k` form is true and consumer-friendliest).
* Cofinality bridges `nonempty_contSurj_levelQuot_r0/r2` (L5): tower cofinality +
  triples-⟺-homs (`d0LiftHom`/`drLiftHom` at the finite 2-group `Qₖ`) + quotient
  composition.
* Two epis **assembled** (proven modulo the sorried suppliers), and **`bLab :
  BLabHypothesis` proven**: antecedents discarded (plan §1 — the pinned χ-data enters via
  the levelwise sets), Hopfian endgame byte-for-byte `reconstruction_of_equinum:350–354`.
  `bLab` elaborates against the *actual* `BLabHypothesis` of `GQ2/Roe/MarkedPro2.lean`
  `section Draft` — verified by the build and by `lean_verify` (§5).

---

## 2. Fill-ticket dispatch specs (exact sorry inventories)

Every sorry below cites its spike/plan anchor; fills must not touch statements (§0).

### L2 — `TwoCentralTower.lean` (15 sorries; opus-able)

| # | sorry | anchor / proof sketch |
|---|---|---|
| 1 | `twoCentralSeries_normal` | verbal series: conjugation-stable generating family; closure/topClosure preserve normality |
| 2 | `twoCentralSeries_antitone` | `succ ≤ id` via closure-minimality into the closed `λₖ` (needs 1: `⁅H,⊤⁆ ≤ H` for `H` normal); junk `λ₀` step is `≤ ⊤` |
| 3 | `zLayer_eq_ker_levelProj` | `mem_map` + `QuotientGroup.ker_mk'`-style unfolding |
| 4 | `zLayer_le_center` | spike §2.1: `[λₖ, G] ⊆ λ_{k+1}`; `k = 0` vacuous (`Q₁` trivial) |
| 5 | `zLayer_sq` | `λₖ² ⊆ λ_{k+1}` (`sq_mem_twoCentralSucc` + `twoCentralSeries_succ`); `k = 0` via `Subsingleton Q₁` |
| 6 | `isOpen_twoCentralSeries` | plan §2.4: induction; f.g. ⇒ finitely many square/commutator classes generate `Zₖ`, elementary-abelian finite ⇒ finite index; open-of-finite-index-closed in profinite |
| 7 | `finite_levelQuot` | from 6 (open ⇒ finite index in compact) |
| 8 | `isPGroup_levelQuot` | `hpro` + quotient of 2-group tower; or directly: `Qₖ` is a quotient of a finite 2-group by construction |
| 9 | `exists_twoCentralSeries_le` | plan §2.4: `G/core(U)` finite 2-group is nilpotent, its 2-central series reaches 1; pull back |
| 10 | `iInf_twoCentralSeries` | from 9 + T2 separation of `1` |
| 11 | `map_twoCentralSeries_le` | verbal: image of generators lands in generators; continuity for the closure step |
| 12 | `map_twoCentralSeries_eq` | 11 + compact-to-T2 maps are closed ⇒ image of closure = closure of image; `Subgroup.map_commutator`, image of squares |
| 13 | `twoCentralSeries_units_le` | spike §2.4 "exact, elementary": induction; squares of `1+2^kℤ₂` land in `1+2^{k+1}ℤ₂`, commutators trivial (abelian); base `k = 2`: units square into `1+8ℤ₂` |
| 14 | `chiShadow_eq_one_of_mem` | `k ≤ 1`: target subsingleton (`⟨by decide⟩` as in `sPR0_one_nonempty`); `k ≥ 2`: 11 + 13 one precision step down (`2^k ∣ 2^{k+1}`) |
| 15 | `chiLevel_levelProj` | both sides on `levelMk`-residues are `Units.map`-composites of `PadicInt.zmod_cast_comp_toZModPow`; finish by `levelMk_surjective` |

Note: `chiLevel` and `levelProj` *definitions* embed sorries 14 and 2 respectively —
until L2 lands, every downstream decl whose statement mentions them (all `sPR*`-statements
included) prints `sorryAx`.  This is expected and tracked (§5).

### L3 — `Levelwise.lean`, base-case/numeric family (12 sorries; opus-able)

| # | sorry | anchor / route |
|---|---|---|
| 1–3 | `chiD0pres_d0A/_d0S/_d0Y` | replicate `SectionThree.d0LiftHom_A/S/Y`'s (private when this table was written; public since the L6 cleanup) `show`/`maxProPHomEquiv_symm_apply_maxProPMk`/`quotientLift_quotientMk`/`homEquiv_symm_of` pattern |
| 4 | `chiTargetR0_three` | `(−1,1,η) ≡ (7,1,5) (mod 8)`: `toZModPow`-numerics; η via `negThreeUnit_val` (`5·5 ≡ 1 (8)`) |
| 5 | `chiTargetR2_three` | `(S,X,Y) ≡ (5,5,7) (mod 8)`: from R10's mod-16 congruences (`X ≡ 5, S ≡ 13 (16)`) + `Yval_eq` (`Y = −X²`) |
| 6–7 | `chiTargetR0_nine`, `chiTargetR2_nine` | stress; mod-`2^9` Newton refinement of the root (values re-verified by hand, §1.2); if the Hensel-digging is disproportionate, L3 may propose *deleting* the two `_nine` stress pins via the orchestrator (they are marked stress; deletion ≠ statement change of the load-bearing freeze) — do not weaken them silently |
| 8–9 | `chiTargetR0_castHom`, `chiTargetR2_castHom` | `ZMod.castHom_comp_toZModPow`-compatibility (`PadicInt.zmod_cast_comp_toZModPow`), `Units.map`-functoriality |
| 10 | `witnessR0_mem` | plan §2.3: transport to a concrete 256-element model of `Q₃(D_R)` (pc-presentation `F₃/(r₂, λ₃-words)`), `decide` relator+generation, χ mod 8 against pin 4; spike per-seed table §3.1 is the regression target |
| 11 | `witnessR2_mem` | same in `Q₃(D₀)` against pin 5 |
| 12* | `card_levelQuot_two/three`, `card_zLayer_one` (3 statements) | same model transport; spike §1 table row k=1,2 |

(*rows 12 count as three sorries; L3 total = 14.*)

### L4a — calculus + SL2 (`StageLemma.lean` 10 + `Levelwise.lean` 6; opus-able with fable review)

`Levelwise.lean` part: `defectR0_eq_of_lift`, `defectR0_mem_zLayer`, `defectR2_eq_of_lift`,
`defectR2_mem_zLayer` (central-kernel computation, spike §2.1/plan §2.2 — uses
`zLayer_le_center`, `zLayer_sq`, `zLayer_eq_ker_levelProj`), `sPR0_levelProj`,
`sPR2_levelProj` (three-clause weakening; χ-clause via `chiLevel_levelProj` +
`chiTarget*_castHom`).

`StageLemma.lean` part: `dbarWordR0/R2_congr_slots`, `dbarWordR0/R2_congr_mod` (spike
§2.1's group-identity list: `[λ_{k-1},λ_{k-1}] ⊆ λ_{2k-2} ⊆ λ_{k+1}`, `[λ_{k-1},λ₂] ⊆
λ_{k+1}`, 𝔽₂-linearity of squaring, `k ≥ 3` everywhere), `defectR0/R2_mul` (the §2.2
derivation: `S⁴`-inertness, π-diagonal, cross terms; machine-verified 24/24),
`sPR0/sPR2_mul_mem` (Frattini generation + shift-in-`λₖ` + `χ(λ_{k-1}) ⊆ 1+2^kℤ₂`),
`stageSL2R0/R2` (digit adjustment: the `(ℤ/2)²`-onto mechanism *or* the dimension-count
fallback of spike §2.5(c), plus the automatic π'd-slot digit — all internal, unfrozen).

File-ownership note: L4a edits **both** `Levelwise.lean` and `StageLemma.lean`; L3 edits
`Levelwise.lean` too.  **Orchestrator must serialize L3 and L4a on `Levelwise.lean`** (or
split the defect/restriction block into a new file at dispatch time — allowed, it is not
a statement change if the statements move verbatim).

### L4b — span + SL1 (`StageLemma.lean`, 6 sorries; fable — carries the campaign's residual risk)

`span_free_r0`, `span_free_r2` (THE load-bearing wall: spike §2.5(a)'s no-basis-theorem
structural induction — atoms `πv`, `[v,g]` reduced by the diagonal trick + char-2 Jacobi +
`ad(πu) = (ad u)²` + degree bookkeeping; measure (degree, π-height, left-depth); on a
snag: O1 = axiomatize exactly the free span statement, O2 = axiomatize levelwise
nonemptiness — both owner-gated, plan §7), `span_descent_r0/r2` (`map_twoCentralSeries_eq`
along `F₃ ↠ D` + `congr_slots` to move between generating triples), `stageSL1R0/R2`
(span + the two separating functionals of spike §2.5(b): χ̂-depth of the η-slot tail via
`v₂(η^{2^{k-1}} − 1) = k+1`, and the abelianized shadow for the S-slot tail; the
P-congruence pins the defect's functional values).

### L5 — assembly (`Assembly.lean`, 5 sorries + the serialized `Reconstruction.lean` refactor; opus-able)

`exists_contSurj_of_levelwise_nonempty` (relocation protocol §1.4 — regression gate:
`reconstruction`/`reconstruction_of_equinum` and all their consumers byte-identical),
`sPR0_nonempty`/`sPR2_nonempty` (induction from `sPR0_three_nonempty` + `stageStepR0/R2`
upward; `sPR0_levelProj` downward for `k ≤ 2`; note `sPR0_one_nonempty` is already
proven), `nonempty_contSurj_levelQuot_r0/r2` (cofinality `exists_twoCentralSeries_le`
with (`drFinsetTopGen`/`d0FinsetTopGen`, `isProP_DR`/`d0_isProP`); triple-to-hom via
`d0LiftHom`/`drLiftHom` at `H = Qₖ` — the finite quotient's profinite instance pack comes
from openness (L2 #6) + discreteness; surjectivity from the generation clause via
`MonoidHom.range_eq_top`-style closure argument; then compose with
`Qₖ ↠ R/U` (`projMap`-style)).

L6 (unchanged from the plan): docs/ledger/`lean_verify bLab` = std-3 exactly, board notes.

---

## 3. Design decisions and deviations (all deliberate; none change the mathematics)

1. **Module system**: all four files are **plain** (non-module) files.  Forced:
   `BLabHypothesis` lives in `MarkedPro2.lean`, a plain file (R15's conversion note), and
   module files cannot import plain files; plain files can import both.  (For the record:
   `Reconstruction`, `DRPresentation`, `ChiR`, `DyadicPresentation`, `MaxProP` are module
   files; `MarkedPro2`, `DyadicNielsen`, `SectionThree` are plain.)
2. **1-based λ with junk `λ₀ = ⊤`** (three-case recursion; `twoCentralSeries_succ` needs
   `1 ≤ k`).  Chosen so every index in every statement equals the memos' — the numerology
   (`k₀ = 3`, `m(k) = k`, `2^{k-1}`) is too load-bearing to survive an off-by-one
   convention.
3. **χ̂-precision notation deviation** (vs spike §2.4's `χ̂ₖ : Qₖ → (ℤ/2^{k+1})ˣ`): the
   frozen `chiLevel χ k` has target `(ZMod 2^k)ˣ` — exactly the P-clause's modulus, total
   in `k` with no side condition.  The spike's extra digit of precision is available to
   fills through `twoCentralSeries_units_le` (kept at the sharp `2^{k+1}` modulus); L4a
   builds finer shadows locally where the pinned-slot argument needs them.  Notational
   only.
4. **SL1 in inverse form** (`d̄(w) = δ(T)⁻¹`): composes with the shift formula without
   invoking elementary-abelian-ness (`δ⁻¹ = δ` in `Zₖ` anyway).  The memo's
   `δ ∈ Im d̄` form is recovered verbatim once d̄'s image is known to be a subgroup.
5. **SL2 mechanism-free**: frozen as "some `ker d̄`-modification of the canonical lift
   lies in `S^P_{k+1}`", not as the `(ℤ/2)²`-onto digit map.  The spike itself hedges the
   mechanism (§2.5(c): explicit kernel elements *or* dimension count), so freezing the
   role, not the mechanism, is the correct contract.  The `(ℤ/2)²`-ontoness and the
   ~~automatic π'd-slot digit (re-derived during L1: the relator's χ-shadow forces
   `d₁² ≡ 1 (mod 2^{k+2})`, hence digit 0 — r₀: A-slot; r₂: y-slot)~~ are L4a-internal.

   **⚠ FLAGGED 2026-07-26 by L4c — the "automatic π'd-slot digit" claim does not
   re-derive.** Applying `χ_{k+1}` to `δ(T) = 1` yields `χ(A)²χ(S)⁴ = 1` in
   `(ZMod 2^{k+1})ˣ`, which is **vacuous**: `χ(A) ≡ −1 (mod 2^k)` already forces
   `χ(A)² ≡ 1 (mod 2^{k+1})`, and `χ(S)⁴ ≡ 1 (mod 2^{k+2})` regardless.  The parenthetical
   above runs at `2^{k+2}`, i.e. it needs a relator identity one level higher (in
   `Q_{k+2}`), which does **not** follow from `δ(T) = 1` in `Q_{k+1}`.  Either the step
   needs restating or SL2 needs an extra hypothesis.  Statements are unaffected (this was
   L4a-internal, never frozen), but SL2 has no known proof route until it is resolved.
6. **Not frozen, deliberately**: the categorical `G ≅ lim G/λₖ` (plan §2.4 lists it; no
   L-consumer needs it — cofinality + `⨅ = ⊥` carry the content; flagged as the one
   omission from the plan's Tier-F list), the reverse span inclusion, the π'd-generator
   tail-absorption bonus (`g₁^{2^{k-1}} ∈ Im d̄` — proof ingredient, not interface), the
   defect homomorphism *as a bundled hom* (the ∃-forms never need it), sZero-restrictions
   (unconsumed), the χ-intertwining of the limit epi (spike §2.4 bonus for R15 — needs the
   α-architecture: König over the `S^P`-towers directly instead of the `ContSurj`-system;
   sketch: apply `nonempty_sections_of_finite_cofiltered_system` to `k ↦ S^P_k` with the
   restriction maps, then assemble the compatible triple family into an epi via
   `d0LiftHom` at each level and the Cantor argument, χ-compatibility for free from the
   clause; record only), level-4 stress witnesses (comment for L3, not statements — a
   frozen-then-deleted stress lemma would look like a statement change).
7. **Generic calculus over-hypothesization**: the congruence lemmas carry the full
   profinite pack (`[Group][TopologicalSpace][IsTopologicalGroup][CompactSpace][T2Space]
   [TotallyDisconnectedSpace]`) though some may be provable with less — all three
   instantiations (`D_R`, `D₀`, `freeProTwo`) satisfy it, and extra generality has no
   consumer.  Weakening later is a conservative statement change (allowed only via the
   orchestrator, though nothing should ever need it).
8. **Commutator conventions**: repo `commP` everywhere a formula lives; mathlib `⁅H,⊤⁆`
   only inside `twoCentralSucc` (for `Subgroup.map_commutator` etc.); proven bridge
   `commP_mem_twoCentralSucc` (`commP v g = ⁅v⁻¹,g⁻¹⁆`).  Full paragraph in
   `TwoCentralTower.lean`'s docstring (orchestrator directive, board §10).
9. **`d0Word` naming**: the plan's §2.1 pseudocode name, defined here (no in-tree
   `d0Word` existed); definitionally aligned with `d0LiftHom`'s relator expression.
10. **Direction naming**: `*R0*` = `r₀`-relator triples in the `D_R`-tower (direction 1);
    `*R2*` = `r₂`-relator triples in the `D₀`-tower (direction 2).  Slot order is always
    the relator's own: r₀ = `(A,S,Y)`, r₂ = `(s,x,y)`.

---

## 4. Census / axiom-hygiene audit (plan §8)

### 4.1 The `chiD0G` trap (found and avoided)

The in-tree `D₀`-orientation `chiD0G` (`GQ2/Roe/MarkedMatching.lean:318`) is
`chiD0.comp abMk` with `chiD0` **from the B3c Galois bundle** — consuming it would wire
`dyadicOrientation` into the lane.  L1 instead defines `chiD0pres` from `d0LiftHom` at
`(−1, 1, η)` (presentation-side; relator dies by commutativity), and replicates the
`−3`-unit locally (`negThreeUnit`; same `isUnit_intCast_of_odd` recipe as
`GQ2.unitNegThree`, which lives in the Galois-side `PropOneOneAssembly.lean` and is not
imported).

### 4.2 Import-closure audit (measured, BFS over `import GQ2.*`)

| file | transitive GQ2 imports | reaches axiom files? |
|---|---:|---|
| TwoCentralTower | 3 (`MaxProP`, `Words`, +1) | **no** |
| Levelwise | 57 | `Foundations.Axioms`, `EvensKahnDerived` — **via `SectionThree` (direct import there) and via `ChiR → SectionThree`** |
| StageLemma | 58 | same (inherited) |
| Assembly | 77 | same + `PropOneOneAssembly`, `MarkedMatching` — via `MarkedPro2` (the `BLabHypothesis` home) |

**Finding**: import-closure freedom from `Foundations/Axioms` is impossible for this
campaign *as the plan itself designed it* — the plan mandates `chiR` (R11) and
`d0LiftHom`, and `ChiR → SectionThree → Foundations.Axioms` is a direct-import chain in
the landed tree.  Plan §8's sentence "no Foundations/Axioms transitive dependencies"
cannot be import-literal; its own operative clause is the second one:
**`lean_verify bLab` must report std-3 exactly** — proof-term closure, which axiom
*declarations* in the environment do not taint.

### 4.3 Print-closure evidence (the operative gate), measured at L1

* `lean_verify GQ2.Roe.Labute.bLab` → `[propext, sorryAx, Classical.choice, Quot.sound]`
  — **std-3 + the interim `sorryAx`, zero census axioms.**  When L2–L5 discharge the
  sorries, `sorryAx` drops out and the L6 gate (`std-3 exactly`) is satisfiable as
  specified.
* `lean_verify GQ2.Roe.Labute.d0Word_eq_one` → std-3 exactly (proven, axiom-free — the
  D₀-relator fact comes from the presentation, as required).
* ~~`sPR0_one_nonempty` (proven) prints `sorryAx` **through the definitions**: `chiLevel`
  embeds `chiShadow_eq_one_of_mem` (L2 #14) in its lift-condition and `levelProj` embeds
  `twoCentralSeries_antitone` (L2 #2).  Every `sorryAx` in the lane's proven decls traces
  to L2's two definitional sorries — none to axioms.~~
  **RETIRED 2026-07-26 (orchestrator): L2 landed 15/15 (`5442ef6`), so the two definitional
  sorries are gone. `sPR0_one_nonempty` now prints std-3 exactly, as do all of L3's and
  L4a-Levelwise's fills. Do not expect interim `sorryAx` from `chiLevel`/`levelProj`; if a
  fill shows `sorryAx`, trace it — it is real, not definitional.**
* Discipline for fills: never cite `chiD0G`, `unitNegThree`, `dyadicOrientation`, or
  anything from `Foundations/Axioms`/`SourceData`/`EvensKahnDerived`/`AxiomLedger`;
  D₀-side facts only from `DyadicPresentation`/`DyadicNielsen`/`SectionThree`'s proven
  layer.  L6 re-runs the print audit as the final gate.

No new `axiom`, no `native_decide` anywhere in the four files (source-scanned by
`lean_verify`, warnings empty).

---

## 5. Risks (delta to the spike's §4 assessment)

1. **L4b span** — unchanged, the named residual risk (spike §2.5(a) reduction; O1/O2
   priced, owner-gated).  The L1 statements are shaped so O1 would axiomatize *exactly*
   `span_free_r0/r2` (a ∀k sentence about `freeProTwo` only).
2. **L3 `decide` budget** — `|Q₃| = 256`; the model-transport route is standard but the
   `Q₃`-model construction (pc-presentation + iso to the abstract quotient) is the real
   work; the frozen `card_levelQuot_three = 256` pin is the sanity rail.  `native_decide`
   stays owner-gated (house rule) — not needed at 256 by the spike's budget note.
3. **L2 openness** (#6) is the only tower sorry with real content; the rest are
   mechanical.  If `IsProP`-based finiteness fights, the `hpro`-hypothesis spelling
   already matches the in-tree `maxProPQuotient` API.
4. **File-contention**: L3 ∥ L4a both own `Levelwise.lean` sorries — serialize or split
   (see §2/L4a note).  The `Reconstruction.lean` edit stays serialized in L5 (R30
   pattern).
5. ~~**Definitional sorries** (L2 #2/#14 inside `levelProj`/`chiLevel`): benign but they
   make *every* downstream `lean_verify` show `sorryAx` until L2 lands — reviewers should
   not mistake that for a stalled fill.  Dispatch L2 first (it is also the dependency of
   L4a's χ-clause work).~~ **RESOLVED 2026-07-26: L2 landed 15/15; this risk is closed and
   the `sorryAx` expectation above is retired (see §4).**

---

## 6. Verification protocol run at L1 (all green)

* `lake build GQ2.Roe.Labute.{TwoCentralTower,Levelwise,StageLemma,Assembly}` — clean;
  the **only** diagnostics are the 56 `declaration uses 'sorry'` warnings (15+20+16+5).
* Composability certificates compiled: `stageStepR0/R2` (SL1+shift+stability+SL2 compose),
  `sPR0_three_nonempty`/`sPR2_three_nonempty` (witnesses typecheck against the sets),
  `sPR0_one_nonempty` (set definition inhabitable end-to-end), the two epi assemblies
  (generic König statement applicable), and `bLab` against the real `BLabHypothesis`.
* Numeric anchors hand-re-verified (mod-512 root/S/Y/η — §1.2).
* Axiom audit: §4.2–4.3.
