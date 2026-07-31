# SD1 — the two-sided degree-n source record (design memo)

**Ticket SD1** (board: `docs/dyadic/tickets.md`, SD lane; dispatched 2026-07-31 at G-1).
Worker: fable, worktree `gq2-dyadic-sd`, branch `dyadic-sd1`. Read-only vs Lean source;
all file:line anchors verified in-session at `dyadic` = 9efff9f (Lean-identical to the G-1
board commit 9cf27f6, which is docs-only). Scratch probes were typechecked with
`lake env lean` against the built `gq2-dyadic-pj` audit worktree (same Lean tree); probe
results are quoted inline as **P1/P2/P3** and the probe file was never committed.

Feeder notes honored (all board-ratified, cited where used): LG1's drop-`eulerChar`
(board log 2026-07-29, LG1 outcomes), F3 outcome (viii) `Tq (qOf K FF)` + refl-bridge,
AX1/FG1 Route D (tfg as record field), MC1 §(ix) (rank enters only as
`demushkinRank = n+2`, `card_H1 = 2^{n+2}`), plan §3 A2 (two-sided restatement = packet
Thm 11.1 `thm:source-abstract`), the LG5 board row (`local_gauss_K` +
`ramifiedCertificateOfSubtype`), AX3/AX4 census axioms B5-K `markedRecipAt` / B10-K
`orientedTameQuotientAt` (consumable directly), and the G-1 release entry (WW4 queued
behind this memo's §6; `selection-freeze.md` row 5 warning).

---

## 0. Executive summary and the one structural discovery

The packet (§11, Thm `thm:source-abstract`) and the ticket both frame SD-n as "replace the
hard-coded `8`, `|V|²`, and base Gauss exponent by parameter fields; the induction is
unchanged". The numeric claim is **verified below and is even cheaper than advertised**
(§4: every literal-shape carrier consumes its constant opaquely, so the parameterized
proofs are byte-identical). But the survey's §3 finding understated one cost, and this memo's
main structural discovery is its resolution:

> **The entire §4–§9 generic machinery is typed at the concrete ℚ₂ boundary.** Every
> generic count is stated at `b : ContinuousMonoidHom Γ ↥boundarySubgroup`
> (`GQ2/BoundaryFrame.lean:248`), frames are `alpha : ContinuousMonoidHom Ttame H` /
> `psiBar : ContinuousMonoidHom PiBd E` (`BoundaryFrame.lean:267-275`), and the head
> dichotomy names the element `tameTau` (e.g. `GQ2/SourceData.lean:241,265`,
> `GQ2/SectionNine/Terminal.lean:346-350`). A degree-n *two-sided* theorem cannot be
> stated against this boundary at all — `T_{q_K}` has a different tame relation and the
> pro-2 slot a different rank.

Consequently SD-n is **not** two new files atop the frozen stack; it is a
**boundary-abstracted clone of the b-typed recursion spine** (≈9.1k lines over ~20 files,
sized in §4.3 — the same order and the same mechanical character as the LG lane's 9.2k-line
retype, which is the campaign's precedent for exactly this decision: LG1 ruled "in-place is
A6-incompatible; clone"). The payoff of the clone architecture is decisive for plan A6:

* **the frozen-ℚ₂-file edit list is EMPTY** (§4.2) — zero behavioral or textual edits, no
  wrapper gymnastics, capstone axiom prints untouched by construction;
* the deep layer **below** the boundary — the master count `two_mul_card_centralImage`
  (`GQ2/VLiftCount.lean:764`), the whole descent/keystone/Fourier/torsor machinery, §5–§7,
  `Reconstruction.lean` (checked: zero boundary mentions) — is **reused as-is**, and it is
  where the hard mathematics lives;
* the numeric parameterization rides along inside the clones for free (§4.1).

The n = 1 compatibility story survives in a *stronger* form than wrappers: the K-boundary
already generalizes the ℚ₂ one **definitionally** — probe **P1** verified
`boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl` (F3's refl-bridge
`Tq 2 ≡ Ttame`, `nuTq 2 ≡ nuT`, `GQ2/Dyadic/TameQuotientK.lean:436-444`, extends to the
subgroup level with no transport), so the n = 1 instances of the cloned stack are stated at
*literally* the old boundary, and the regression theorem (§8, SD3) re-derives `thm_4_2`'s
statement from the clone.

Everything else in the ticket's items (i)–(v) is confirmed with details below; §6 is the
WW4 coordination section; §7 has the owner questions; §8 re-plans SD2/SD3 (one new
mechanical wave SD-R is required — the budget change).

---

## 1. (i) `SourceNumerics n` — the exact field list

### 1.1 Design shape: opaque shared constants, formulas confined to one instance

The recursion never needs to *unfold* a formula: the solver
`count_eq_of_closedRecursion` (`GQ2/SectionNine/Induction.lean:503`) consumes the boxed
system only by rewriting both sources' equations to syntactically equal right-hand sides
and cancelling the **shared** coefficient (verified at `Induction.lean:534-539` for the 8,
`:553-558` for `2·#D_T`, `:560-562` for the 2 — see §4.1). The existing seam already
passes `μ`, `G0`, `DT`, `phase` as opaque shared data. `SourceNumerics` therefore stores
**values, not proofs**, and the packet formulas live in exactly one place
(`standardNumerics`):

```lean
/-- Degree-n numeric leaf values consumed by the two-sided recursion.  Opaque to the
induction; both sources of a comparison share one `SN`.  Plain-import file (§5). -/
structure SourceNumerics (n : ℕ) where
  /-- `#Hom_cont(Γ, 𝔽₂)`; replaces the literal `8` (`GQ2/SourceData.lean:131`,
  `SectionEight/Partition.lean:214-216`, `SectionEight/Recursion.lean:407,744`). -/
  homScalar : ℕ
  homScalar_pos : 0 < homScalar          -- the solver's cancellation needs ≠ 0 (§4.1)
  /-- `#LiftsOver ρ` as a function of `|M_B|`; replaces `(Nat.card ↥RF.MB) ^ 2`
  (`SourceData.lean:143`, `RadicalEdge/Bridge.lean:116-117`, `Recursion.lean:417,721`). -/
  mMult : ℕ → ℕ
  /-- `#Z¹(T)` as a function of `|T|` (the `fixedPts` factor stays a separate literal
  factor in the field shape — see 1.2); replaces the `^ 2` at `SourceData.lean:174-175`
  and inside `muZero` (`Prop89Close.lean:130-133`). -/
  tMult : ℕ → ℕ
  /-- `#Z¹(V) / |V|` = `#H¹(V)`, as a function of `|V|`; replaces the *inner* `|V|`
  factor — `hZcard`'s second `|V|` (`SourceData.lean:218`), `two_mul_card_centralImage`'s
  inner factor (`VLiftCount.lean:780,784`), and eq. (140)'s
  `Nat.card ↥RF.MB / Nat.card ↥RF.TBsub` display (`Recursion.lean:429`, `Phase140/
  Obstruction.lean:408`).  The *outer* `|V|` is `#B¹` and is degree-independent (1.3). -/
  h1Mult : ℕ → ℕ
  /-- Gauss residue, unramified head, as a function of the half-dimension `m`
  (`#V = 2^{2m}`); replaces `-(2 ^ m : ℤ)` (`SourceData.lean:244`). -/
  gaussUnram : ℕ → ℤ
  /-- Gauss residue, ramified head; replaces `(2 ^ m : ℤ)` (`SourceData.lean:268`). -/
  gaussRam : ℕ → ℤ

/-- The packet §11 values (`thm:source-abstract`; magnitudes from `thm:local-gauss`). -/
def standardNumerics (n : ℕ) : SourceNumerics n where
  homScalar   := 2 ^ (n + 2)          -- = 8 at n = 1 (P3: defeq by rfl)
  homScalar_pos := by positivity
  mMult       := fun M => M ^ (n + 1) -- = M² at n = 1 (P3: defeq by rfl)
  tMult       := fun T => T ^ (n + 1)
  h1Mult      := fun V => V ^ n       -- = V¹ at n = 1 (NOT defeq to V — see 1.4)
  gaussUnram  := fun m => (-1) ^ n * 2 ^ (n * m)   -- = −2^m at n = 1 (one `ring_nf`)
  gaussRam    := fun m => 2 ^ (n * m)              -- = +2^m at n = 1 (one rewrite)
```

Notes.
* `n` is a phantom index on the structure (the values determine everything); keeping it
  makes instantiation sites self-documenting and lets `standardNumerics` state the
  formulas. Alternative — drop the index — is fine; recorded as a taste call, not an
  owner question.
* `cardH2 = 2` **stays a literal** in the record (`SourceData.lean:134`): `dim H² = 1`
  for every local field (survey §2; packet §11 lists it among the unchanged scalars).
* `lem86`'s half-torsor `2` and `stageR136`'s `2` and `zR` stay literal: the `2`s are the
  ±-scalar-class / half-torsor indices, sourced from `cardH2 = 2`, not from `n`
  (survey §2 flags "re-derive, not assume" — that burden falls on the K-side *proofs* of
  the fields, not on the field shapes).
* eq. (136)'s and (140)'s standalone `2`s and `2 * (Nat.card DT)` are likewise
  degree-independent shapes (they cancel; §4.1).

### 1.2 The parameterized record: field-by-field delta vs `GQ2.SourceData`

`SourceDataN` is parameterized by `(n q : ℕ) (P : ProfiniteGrp) (hP : IsProP 2 ↥P)
(nuP : ContinuousMonoidHom P Ztwo) (SN : SourceNumerics n)` — §2 justifies the type
parameters. Fields, relative to `GQ2/SourceData.lean:75-268`:

| field (n = 1 line) | degree-n shape | change |
|---|---|---|
| `Γ` (:78) | unchanged (`ProfiniteGrp`) | — |
| `sigma/tau/x0/x1` (:80-86) + 8 pinnings (:94-108) | **dropped** | owner Q2; consumed nowhere (`Roe/Main.lean:68-81`), unsatisfiable-at-honest-generators precedent for Γ_R, and MC1 §(ix): rank enters only numerically |
| `tame` (:88) | `ContinuousMonoidHom Γ (Tq q)` | type: F3's `Tq` (§2.1) |
| `pro2` (:90) | `ContinuousMonoidHom Γ P` | type: abstract slot (§2.2) |
| `compat` (:92) | `∀ g, nuTq q (tame g) = nuP (pro2 g)` | retarget |
| `surj` (:110) | onto `↥(boundarySubgroupQ q nuP)` | retarget (`Dyadic/TameBoundary.lean:159`) |
| `ker_pro2` (:115) | unchanged shape (`= proPKernel 2 Γ`) | — |
| `smulZmod2/contSMulZmod2/htriv` (:119-123) | unchanged | — |
| `tfg` (:127) | unchanged shape | — (Route D: a record field is the permanent shape; G-side discharge = FG1's theorem, `GQ2/Dyadic/FinitelyGeneratedK.lean`) |
| `hom8` (:131) | `homCard : Nat.card (ContinuousMonoidHom Γ (Multiplicative (ZMod 2))) = SN.homScalar` | value |
| `cardH2` (:134) | unchanged (`= 2`) | — |
| `liftsOver_card` (:137-143) | `… = SN.mMult (Nat.card ↥RF.MB)` | value |
| `lem86` (:147-150) | unchanged shape (`2 * #central = #MLifts`) | — |
| `stageR136` (:154-165) | unchanged shape | — |
| `tcocycle_card` (:168-177) | `… = SN.tMult (Nat.card (Additive ↥T)) * Nat.card (fixedPts …)` | value |
| `hsep` (:180-190) | unchanged shape | — |
| `hpartial` (:193-204) | unchanged shape | — |
| `hZcard` (:207-218) | `… = Nat.card En.Vmod * SN.h1Mult (Nat.card En.Vmod)` | value (outer `|V|` = `#B¹`, kept literal; 1.3) |
| `gaussZ_unramified` (:223-244) | conclusion `GaussZResidue … (SN.gaussUnram m)` | value |
| `gaussZ_ramified` (:247-268) | conclusion `GaussZResidue … (SN.gaussRam m)` | value |

(The `∀`-shapes of the obligation families re-target the cloned frame/enrichment types of
§4.3, but are otherwise verbatim; the interface docs `b`/`b_apply_coe`/`b_surjective`/
`pro2_surjective` (:276-289) carry over unchanged.)

### 1.3 The formulas, verified against the packet

All five moving values are instances of the local Euler characteristic
`#H¹ = #H⁰·#H²·|V|^n` (packet `thm:local-gauss` clause 1: `dim H¹ = n·dim V` for
nontrivial simple `V`) plus `#Z¹ = #B¹·#H¹`, `#B¹ = |V|/#H⁰`:

* `homScalar`: trivial module `𝔽₂` — `#H⁰ = #H² = 2` ⇒ `#Hom = #H¹ = 2^{n+2}`
  (MC1 §(ix)'s `card_H1 = 2^{n+2}`, and `lemma_8_2_gammaA`'s "free `𝔽₂³` of σ,x₀,x₁
  values" becomes the free `𝔽₂^{n+2}` of σ,x₀,…,x_n values).
* `hZcard`: nontrivial simple `V` — `#H⁰ = 1 = #H²` (dual also nontrivial simple) ⇒
  `#Z¹ = |V|·|V|^n`. The **outer** factor is `#B¹ = |V|`, degree-independent — this is
  why `GaussZResidue`'s normalization `(Nat.card En.Vmod : ℤ) * G0`
  (`Phase140/Assembly.lean:145-149`) needs **no change** at degree n (its docstring's
  layer-(I) reduction divides by `#B¹`), and why the **inner** factor is the one that
  moves (`h1Mult`).
* `tcocycle_card`: `T` elementary abelian, possibly non-simple action —
  `#Z¹ = |T|^{n+1}·#H⁰(T^∨)`; the `fixedPts` factor *is* the `#H²`-by-duality term and
  stays a separate literal factor of the field shape, exactly as at n = 1.
* `mMult`: props 5.15/5.16's `#LiftsOver = #Z¹(M_B)`-torsor count; packet §11's
  `#Z¹(S,V) = |V|^{n+1}`. Hedge: if the eventual K-side proof produces an extra
  `#H²(M)`-style factor for the non-simple `M_B`, only `standardNumerics` changes — the
  record shape and the recursion are insulated (the point of the opaque design).
* `gaussUnram/gaussRam`: packet `thm:local-gauss` — `Gsum(Q⁰_{K,V}) = (−1)^n 2^{n·dim V/2}`
  unramified, `+2^{n·dim V/2}` ramified; with `#V = 2^{2m}` (the source-independent `m`
  obtained at `SourceData.lean:416-420`), `G0 = (−1)^n·2^{nm}` resp. `+2^{nm}`. Matches
  LG5's endpoint: `local_gauss_K` (`GQ2/Dyadic/LocalGauss/Main.lean:348-367`) gives
  `#H¹(G_K,V) = 2^{2mn}` and `arf = if ramified then 0 else n mod 2`, i.e. sign
  `(−1)^n` unramified / `+` ramified, magnitude `2^{mn}`.

### 1.4 n = 1 definitional status (probe P3)

Verified by scratch probe against the built tree:
`(2:ℕ)^(1+2) = 8 := rfl` and `x^(1+1) = x^2 := rfl` — so `standardNumerics 1`'s
`homScalar`, `mMult`, `tMult` are **definitionally** the n = 1 literals. But
`x^(0+1) = x` is **not** `rfl` (`pow_one` is a theorem): `h1Mult V = V^1` is not defeq to
the current inner `|V|`, and `gaussUnram m = (-1)^1 * 2^(1*m)` is not defeq to `-(2^m)`.
**This is the argument for the opaque-constant design** at the recursion interface: the
n = 1 *instances* pass the exact old expressions as values (no `pow`), and only the
`SourceData → SourceDataN 1 …` adapter fields for `hZcard`/`gaussZ_*` need a one-line
`rw [pow_one]` / `ring_nf`-style bridge (SD2 acceptance, §8).

---

## 2. (ii) The two degree-one type fields

### 2.1 `tame`: `Ttame` → `Tq q`, with `q = qOf K FF` at instantiation

Adopting F3 outcome (viii) verbatim. The general tame group is F3's
`Tq q = ⟨σ,τ | τ^σ = τ^q⟩_prof` (`GQ2/Dyadic/TameQuotientK.lean:257`); at a field it is
instantiated at `q := qOf K FF = 2^FF.f` (`GQ2/Dyadic/OrientedTameBundle.lean:178` —
deliberately not unfolded, per its docstring, because it occurs as a type index). The
record and the whole cloned spine are parameterized by a bare `q : ℕ` (with `2 ≤ q`,
`Even q` hypotheses exactly where F3's lemmas need them — `o2_Tq_eq_bot` takes exactly
these, board F3 outcome (iii)); no `IntermediateField` enters the recursion layer.

**Refl-bridge (probe P1, the load-bearing fact):** `Tq 2 ≡ Ttame`, `nuTq 2 ≡ nuT`
definitionally (`tq_two_equiv = ContinuousMulEquiv.refl`, `TameQuotientK.lean:436-444`),
and this extends to the boundary:

```lean
example : boundarySubgroupQ 2 nuTwo = boundarySubgroup := rfl                  -- P1 ✓
example (b : ContinuousMonoidHom Γ ↥(boundarySubgroupQ 2 nuTwo)) :
    ContinuousMonoidHom Γ ↥boundarySubgroup := b                               -- P1b ✓
```

So the ℚ₂ record instantiations of `SourceDataN 1 2 PiBd _ nuTwo _` need **no transport
anywhere in the tame/boundary types** — `sourceA`'s and `sourceR`'s existing field
witnesses are accepted as-is (up to the two value bridges of §1.4).

The head-dichotomy element: every `tameTau` occurrence in the cloned spine becomes
`tqTau q` (`TameQuotientK.lean:268`); at q = 2 this **is** `tameTau` by the same
refl-bridge. The tame relation and generation facts the terminal lane consumes at
`Terminal.lean:346-350` (`α(σ)⁻¹α(τ)α(σ) = α(τ)²`, closure of `{α σ, α τ}`) are exactly
F3's exports `tame_relation_q` + `gen_tq_quotient` (the board's F3-acceptance-grew items)
— no new tame mathematics is needed by the clone.

### 2.2 `pro2`: `PiBd` → an abstract marked pro-2 slot `(P, nuP)` — NOT MC2's cores

**Recommendation (the choice the recon flags; owner Q4): the abstract slot.** The record
and spine take

```lean
(P : ProfiniteGrp) (hP : IsProP 2 ↥P) (nuP : ContinuousMonoidHom P Ztwo)
```

and the common boundary is `boundarySubgroupQ q nuP : Subgroup (Tq q × P)`
(`Dyadic/TameBoundary.lean:159-174` — F3 already built the general boundary for exactly
this use, together with the relative-Goursat kit `hkerQ_uniform` at :186).

Why abstract, not MC2's presented cores:

1. **SD must not wait on MC5** (dispatch constraint; MC5 is queued behind MC-OB and now
   fable-tier). The recursion uses the pro-2 slot only through `nuP`, `ker_pro2`, `surj`,
   and `IsProP 2` — verified: the terminal lane's `pro2Iso`/`compPro2Equiv` layer
   (`Terminal.lean:729-786`) needs precisely "a pro-2 `P` with `pro2 : Γ ↠ P` whose
   kernel is `proPKernel 2 Γ`", nothing about a presentation.
2. **Both sources must share one `P`.** At AS1-time the slot is instantiated at the
   branch core `D_P` (MC2's `Cores.lean`), the candidate side maps onto it by its
   presentation, and the `G_K` side composes its maximal pro-2 quotient with the
   marked-core certificate's `D_P ≅ D_K` (packet `def:core-certificate` item 1 — the
   `MLabHypothesis`/`NLabHypothesis` binders). That composition is **exactly the
   `sourceR` recipe** (`GQ2/Roe/Main.lean:61-67`: transport `pro2` through
   `e : G(2) ≅ D_R`, ν-compatibility by density at the topological generator) — the
   pattern is proven at n = 1 and both degree-n instantiations follow it.
3. Rank never enters structurally (MC1 §(ix)): no `Fin (n+2)`-indexed generator family is
   needed in the record once the pinning fields are dropped (Q2). MC2's `coreRank h = 4 + 2h`
   handle-count convention therefore never touches SD — the slot is rank-blind.

`nuP`-surjectivity: not a record field — where the spine needs it (e.g. the analogue of
`SectionThree.nuT_surjective` used by `pro2_surjective`, `SourceData.lean:286-289`), it is
derivable from `surj` + the tame side, or taken as one hypothesis of the relevant cloned
lemma; SD2 decides locally. (At the AS1 instantiation both `nuTq q` and the core's `nuP`
are surjective for free.)

---

## 3. (iii) The two-sided restatement (packet Thm 11.1)

### 3.1 What the current one-sided theorem pins (the removal list)

`thm_4_2_of_sources` (`GQ2/ThmFourTwo.lean:386-414`) fixes the second source to `G_ℚ₂`
through: `B : BoundaryMaps` + `R : LocalReciprocity` + `horient : TameUnitOrientation R
B.tameF` binders; `[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` instance
binders; `Foundations.absGalQ2_isTopologicallyFinitelyGenerated` (:122, :310);
`liftsOver_card_local` (:128-131); `lemma_8_2_local B` (:275); the terminal lane's
`B.pro2F/B.pro2F_surjective/B.ker_pro2F` (`SourceData.lean:363-377`); the Gauss obtain's
`gaussZResidueD_local_{un}ramified` + `tateDuality 2` + `(R, horient)`
(`SourceData.lean:426-432`); and `prop_8_9_of_source`'s `_local` discharge block
(`Prop89Close.lean:349-360`: `lemma_8_2_local`, `RStageLocal.stageR136_local`,
`half139_local`, `phase140_local`, `tcocycle_card_local`). **All of these disappear from
the two-sided statement** — they become the `S₂`-instantiation's proof obligations.

### 3.2 The parameterized theorem (SD3's target signature)

```lean
theorem thm_source_generic {n q : ℕ} {P : ProfiniteGrp} {hP : IsProP 2 ↥P}
    {nuP : ContinuousMonoidHom P Ztwo} {SN : SourceNumerics n}
    (S₁ S₂ : SourceDataN n q P hP nuP SN)
    {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
    [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
    (F : BoundaryFrameK q P H E)          -- alpha : Tq q ↠ H, psiBar : P → E (clone of
                                          -- BoundaryFrame.lean:267-275 at the K-boundary)
    {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
    (T : MarkedTarget H E Y) (hE2 : ∀ e : E, e ^ 2 = 1) :
    exactImageCountK S₁.b F T = exactImageCountK S₂.b F T
```

Notes on the shape:
* `MarkedTarget` is reused verbatim (target-side, boundary-free —
  `BoundaryFrame.lean:288`); `BoundaryFrameK`/`exactImageCountK`/`BoundaryLiftsK` are the
  §4.3 clones. No `AbsGalQ2`, no `BoundaryMaps`, no reciprocity binders.
* The Gauss dichotomy (`gaussZ_obtain_blockD_of_sources`-clone): the source-independent
  `m`-obtain and `F.alpha (tqTau q)`-dichotomy are unchanged
  (`SourceData.lean:408-434` replayed); each side contributes its record leaf at the
  shared `G0 := SN.gaussUnram m` resp. `SN.gaussRam m`. Both sides read the **same** `SN`,
  so the shared-constant discipline is definitional — no equality side conditions between
  the two sources' numerics ever arise (the ledger §8's "recursion consumes only equality
  of the two sources' leaves" is realized as sharing one `SN`).
* Downstream corollaries (SD3): the K-clone of §10's frame summation
  (`SectionTen.lean`, 278 ln + `SectionTenSources.lean`, 139 ln — `eq_154`'s shape) gives
  `#Sur(S₁.Γ, G) = #Sur(S₂.Γ, G)` for every finite `G`; then the **unchanged, boundary-free**
  `GQ2/Reconstruction.lean` API (454 ln; zero boundary mentions, checked) upgrades count
  equality + the two `tfg` fields to `Nonempty (ContinuousMulEquiv S₁.Γ S₂.Γ)` — packet
  Thm 11.1's final clause. This is what AS1 calls.

### 3.3 The `S₂ = G_K` record instantiation (supply map)

Not SD work (it is the LG-K/AS seam), but the memo fixes the interface so AS1/LG can build
against it. `Γ := ↥U` for the open `U ≤ AbsGalQ2` of index n (LG5's realization;
compact/t.d. instances flow from openness — the `RamifiedCertificate` pattern,
`LocalGauss/Main.lean:255-283`). Field-by-field:

| `SourceDataN` field | `G_K` supplier |
|---|---|
| `tame`, `compat`-tame side | **B10-K** `orientedTameQuotientAt K FF` (`Foundations/Axioms.lean:388`): `W_K`, `equiv : G_K/W_K ≅ Tq (qOf K FF)`, derived `tameF_K`, orientation clauses (`Dyadic/OrientedTameBundle.lean:275-297`) — the AX4 flip already executed, so the memo consumes the axiom directly |
| `pro2`, `ker_pro2`, `surj`, `compat` | max-pro-2 quotient of `G_K` composed with the MC marked-core certificate `D_P ≅ D_K` (`def:core-certificate` item 1, the `A3` binders); joint surjectivity via F3's `hkerQ_uniform` (`Dyadic/TameBoundary.lean:186` — its docstring names the ℚ₂ precedent `hker_uniform`); ν-compatibility by the `sourceR` density argument (`Roe/Main.lean:61-67`) with **B5-K** `markedRecipAt` (`Axioms.lean:204`) pinning the full ℤ₂-valued marking (merge gate 6) |
| `tfg` | FG1's theorem (`Dyadic/FinitelyGeneratedK.lean`, from B1 — Route D: field, not binder) |
| `homCard`, `cardH2` | LG2a's Euler-char route (`card_H1_eq_of_markingK` — the **drop-eulerChar** note: derived from B7 via Shapiro, never an input) + the K-duality `#H² = 2` |
| `liftsOver_card`, `tcocycle_card`, `hZcard` | K-clones of the `MStageCount`/`Phase140/Local` count lemmas (Euler-char based; the n = 1 sources are `liftsOver_card_local`, `tcocycle_card_local` `Prop89Close.lean:349-360`, `hZcard`-local `Phase140/Local.lean:332`) |
| `lem86`, `hsep`, `hpartial` | K-clones of `lemma_8_6_local` (`SectionEight/Partition.lean:304`), `hsep_local` (`Phase140/Local.lean:537`), `hpartial_local` (`Phase140/Local.lean:864`) — leaf-shaped locals exist at n = 1, so the record's leaf granularity is instantiable (checked; this was the one plausible gap) |
| `stageR136` | K-clone of `RStageLocal.stageR136_local` |
| `gaussZ_unramified/ramified` | **LG5's `local_gauss_K`** (`LocalGauss/Main.lean:348`) + the zero-count corollaries (:447,:487) through the (83)-evaluation bridge (the K-analogue of the n = 1 `gaussZResidueD_local_*` twins); the ramified case consumes `Nonempty (RamifiedCertificate …)` with `ramifiedCertificateOfSubtype` (:688) discharging 4/13 fields — **its binder list is AS1's arithmetic input** (LG5 board row), and `hpkg`/`hker₀` are the AX3 field-side entry points |

The candidate side `S₁ = Γ_{R_K}` is the branch lanes' obligation (word certificate ⇒
fields; §6 fixes the shapes they must hit).

### 3.4 n = 1 wrappers and the per-literal-site story (plan A6)

Under the clone architecture **no existing declaration moves**, so "wrappers keep names"
is satisfied vacuously; what remains is the *reproduction* obligation, per site:

* **`BoundaryMaps.sourceA` (`SourceData.lean:297`)**: SD2 defines
  `sourceA_N : SourceDataN 1 2 PiBd _ nuTwo (standardNumerics 1)` with every field the
  *same witness term* as `sourceA`'s (accepted without transport by P1/P3), except
  `hZcard`/`gaussZ_*` which compose the old witnesses with the §1.4 one-line value
  bridges. Acceptance: `sourceA_N.b = B.bA := rfl` must hold (the clone's `b` is the same
  `sourceBoundaryMap` construction at the defeq boundary — the analogue of the
  load-bearing `sourceA_b` simp lemma, `SourceData.lean:339`).
* **`Roe.sourceR` (`Roe/Main.lean:388`)**: same recipe under the `hBLab` binder;
  `sourceR_N.b = (sourceR hBLab).b := rfl` is the acceptance.
* **`G_ℚ₂` as a record** (new at n = 1): `sourceF_N B : SourceDataN 1 2 PiBd _ nuTwo _`
  assembled from the `*_local` pack (§3.1's removal list — every leaf exists, incl.
  leaf-shaped `hsep_local`/`hpartial_local`). This is the two-sided flip's genuinely new
  n = 1 object. One packaging note: the record's carrier is a bundled `ProfiniteGrp`
  (the R31a decision, kept), so `sourceF_N` is defined under the same
  `[CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2]` binders that `thm_4_2`
  carries today (`ThmFourTwo.lean:432-437` documents the discipline) and bundles
  `ProfiniteGrp.of AbsGalQ2` — i.e. the old theorem-level instance binders migrate into
  the `S₂`-instantiation, which is exactly where §3.1 said they go.
* **`thm_4_2` (`ThmFourTwo.lean:443`)**: untouched (still proved via the old
  `thm_4_2_of_sources` at `B.sourceA`). SD3 adds the **regression theorem**
  `thm_4_2_via_N : exactImageCount B.bA F T = exactImageCount B.bF F T := thm_source_generic
  (sourceA_N B) (sourceF_N B) …` — same statement, derived through the clone (P1b makes
  the statement typecheck at the old boundary). Gate: `scripts/check_axioms.sh` check 5
  stays green **and** `thm_4_2_via_N`'s print is contained in the frozen capstone set
  (expected: identical — the clone spine is axiom-free generic; the instances cite the
  same `_local`/`_gammaA` lemmas as today).
* **`prop_8_9`/`prop_8_9_of_sources`/`gaussZ_obtain_blockD_of_sources`/`terminal_count_eq_of_sources`**:
  untouched; their clones live under `GQ2/Dyadic/` with new names.

---

## 4. (iv) The literal shapes: carriers, parameters, and the frozen-file edit list

### 4.1 The complete carrier chain (verified line-by-line this session)

Degree enters the *generic* layer at exactly three shapes; every carrier below consumes
its constant opaquely (rewrite-in / cancel-out), so the parameterized clone proofs are
**byte-identical** except where noted:

**(a) `homScalar` (the literal 8).**
`lemma_8_3` (`SectionEight/Partition.lean:209-218`; hypothesis `hscalar … = 8` :214,
coefficient :216) — proof already value-generic: fibres counted as
`Nat.card (ContinuousMonoidHom Γ 𝔽₂)` then rewritten by `hscalar` (:236-243). →
`ClosedRecursion.eq138` (`SectionEight/Recursion.lean:407`) and `prop_8_9_aux`'s
`hscalar` (:744, applied :752). → `rStage_phase` (`ThmFourTwo.lean:271-285`) applies it
to both sides and cancels by `omega` (:285); the solver cancels its copy at
`Induction.lean:534-539` (`omega`). **The only non-verbatim proof steps in the whole
parameterization**: the two `omega`-cancels of a now-variable coefficient become
`Nat.eq_of_mul_eq_mul_left (SN.homScalar_pos)` — hence the `homScalar_pos` field.

**(b) `mMult` (the `^ 2` multiplicity).**
Chain: `half139_of` (`RadicalEdge/Bridge.lean:110-117`; proof rewrites `hMcount` in, then
`sum_const` + `ring` — value-opaque) → `half139_via_radData` (`RecursionSplice.lean:115-129`)
→ `half139_of_leaves` (`Prop89Close.lean:218-236`) → `ClosedRecursion.eq139`
(`Recursion.lean:417`) / `RecursionInputs.half139` (:721). Solver consumption
(`Induction.lean:560-562`): rewrites both eq139s and cancels the literal `2` — the
multiplicity term is *identical on both sides and never inspected*. The `M`-stage lane is
**already multiplicity-generic**: `mStage_partition` takes `(mult : ℕ)`
(`Induction.lean:467-478`) — zero changes there; the two-sided `mStage_lane`-clone just
instantiates `mult := SN.mMult (Nat.card ↥RF.MB)` from both records' fields.

**(c) `h1Mult` (the inner `|V|`).**
Bottom: `two_mul_card_centralImage` (`VLiftCount.lean:764-816`) — `hZcard` (:780) and
`hGaussZ` (:781) enter only in the terminal `rw [...]; ring` (:812-816); with
`hZcard : #Z¹ = |V| * vH` and conclusion `|V| * (vH + G0·Σ)` the same `ring` closes. →
`hMobst_of_residues` / `phase140_from_residues` (`Phase140/Assembly.lean:158-189,
243-282`; conclusions :187-188, :268-273). → `phase140_of_phaseObstruction`
(`Phase140/Obstruction.lean:386-410`) — **already carries the factor as an opaque
`(cardV : ℕ)`** with the pin `hWV : cardV = Nat.card ↥RF.MB / Nat.card ↥RF.TBsub` (:398)
used only to pretty-print the display (:454-458); the clone splits outer/inner roles
(`cardV` = `#B¹`, stays; `vH` = `SN.h1Mult #V`, new) and drops the pin — the display
becomes `vH * exactImageCount …`. → `ClosedRecursion.eq140` (`Recursion.lean:429`) /
`RecursionInputs.phase140` (:728). Solver consumption (`Induction.lean:553-558`): both
sides rewritten, `2·#DT` cancelled — the factor is never inspected. `muZero`
(`Prop89Close.lean:130-133`) and `μ := #V · muZero` (:331) are *values of the opaque
shared `μ`*: the clone's `muZeroN` uses `SN.tMult`; no shape change anywhere (`μ₀` is
already an opaque parameter of `phase140_from_residues`, :247-249).

**Non-movers (checked, with reasons):** `GaussZResidue`'s `|V|·G0` normalization
(`Assembly.lean:145-149` — outer `#B¹`, §1.3); eq. (136)'s `2` and `zR`
(`Recursion.lean:390-392` — ±-classes via `cardH2 = 2`, frame quantity); eq. (140)'s
`2·#DT` (definitionally `2^{r+1}`, `D_T` is shared data); `lem86`'s `2` (half-torsor);
`sum_phaseSign`'s `2·nPhase − e(C)` (`Phase140/Obstruction.lean:346-358` — sign
bookkeeping); `cardH2 = 2`.

### 4.2 The frozen-ℚ₂-file edit list: **EMPTY** (primary plan)

Under the clone architecture (§0, owner Q1) the three shapes are parameterized **inside
the clones**, the ℚ₂ files keep their literals, and plan A6 is satisfied with zero risk:
no wrapper story is needed because no frozen declaration changes. This answers the ticket's
item (iv) in the architecture actually recommended.

**Plan B (recorded because the ticket asks for it; NOT recommended).** If the owner
prefers in-place parameterization of the *numeric* shapes (it cannot help with the
*boundary* types, which force the clone anyway — so it buys nothing but merge risk), the
minimal-diff edit list with name-keeping wrappers is:

| file:line | edit | wrapper (old name, byte-identical statement) |
|---|---|---|
| `SectionEight/Partition.lean:209-218` | insert `lemma_8_3_count` (coefficient `Nat.card (ContinuousMonoidHom Γ 𝔽₂)`, no `hscalar`; proof = current minus the two `hscalar` rewrites) | `lemma_8_3 … hscalar … := by rw [← hscalar]; exact lemma_8_3_count …` |
| `SectionEight/Recursion.lean:383-431` | rename structure to `ClosedRecursionP`, add params `(cS mM vH : ℕ)`, fields use them | `abbrev ClosedRecursion RF b F μ G0 DT phase := ClosedRecursionP RF b F μ G0 DT phase 8 ((Nat.card ↥RF.MB)^2) (Nat.card ↥RF.MB / Nat.card ↥RF.TBsub)` — probe **P2** verified dot-access (`h.eq138`), anonymous constructors, and `where`-instances all resolve through such an abbrev |
| `SectionEight/Recursion.lean:706-754` | same for `RecursionInputs` + `prop_8_9_aux` (its `hscalar : … = 8` → `= cS`) | same abbrev pattern |
| `SectionNine/Induction.lean:503-` | `count_eq_of_closedRecursionP` with `(hcS : cS ≠ 0)`; `omega` at :539 → `Nat.eq_of_mul_eq_mul_left` | old name := instance at the abbrev values |
| `RadicalEdge/Bridge.lean:110-117` | `half139_of` gains `(mM : ℕ)`; `hMcount = mM`; conclusion `mM * …` | old name := `mM := (Nat.card ↥RF.MB)^2` |
| `RecursionSplice.lean:115-129`, `Prop89Close.lean:218-236` | thread `mM` | ditto |
| `VLiftCount.lean:764-816` | `(vH : ℕ)`; `hZcard = |V| * vH`; conclusion `|V| * (vH + …)` | old name := `vH := Nat.card DD.Vmod` |
| `Phase140/Assembly.lean:158-282` | thread `vH` | ditto |
| `Phase140/Obstruction.lean:386-459` | split `cardV`/`vH`; conclusion display at `vH`; drop `hWV` from the generic form | old name keeps `hWV` and rewrites |
| `Prop89Close.lean:245-367` | `prop_8_9_of_source` gains `(SN …)`-shaped constants | old name at the literal values |
| `ThmFourTwo.lean:271-285` | `omega` → positivity-cancel if `rStage_phase` generalized | n/a (private) |

Everything else (`mStage_partition`, `GaussZResidue`, `phaseSign`, `muZero`-consumers)
needs no edit in either plan.

### 4.3 The boundary-abstracted clone (the real SD-n surface), sized

Clone target `GQ2/Dyadic/Recursion/` (namespace `GQ2.Dyadic`), parameterized by
`(q : ℕ) (P : ProfiniteGrp) (hP) (nuP)` with boundary `boundarySubgroupQ q nuP`,
`tameTau → tqTau q`, `Ttame → Tq q`, `PiBd → P`; numeric parameterization per §4.1 riding
along. Measured surface (lines at 9efff9f):

| clone of | ln | notes |
|---|---|---|
| `BoundaryFrame.lean` (frame/lift/count layer only, :261-463) | ~200 | defs `BoundaryFrameK`, `IsBoundaryLiftK`, `BoundaryLiftsK`, `exactImageCountK`; the presentation layer (:1-260) is NOT cloned (F3 owns the K-tame side) |
| `Block/Enrichment.lean` + `Block/HeadDat.lean` + `Block/RStage.lean` | 340+370+449 | `F.alpha`-consumers; head action at `tqTau q` |
| `SectionEight/Covers,Fourier,Partition,Recursion` | 315+273+318+887 | incl. the (a)/(b)/(c) parameterizations |
| `SectionNine/Terminal.lean` | 879 | tame leaves from F3 (`gen_tq_quotient`, `tame_relation_q`); pro-2 layer at abstract `P` (`pro2Iso` :729-786 is slot-opaque, checked) |
| `SectionNine/Induction.lean` | 606 | solver + `mStage_partition` (multiplicity-generic already) |
| `Phase140/Obstruction,Assembly,LIndep` | 468+292+65 | |
| `MStageCount.lean` | 713 | |
| `RStage/Obstruction,ObstructionBuild` | 110+764 | |
| `RadicalEdge/Bridge.lean` | 198 | |
| `RecursionSplice.lean` (generic part) | ~150 | |
| `Prop89Close.lean` (generic part: `phaseFamily`/`muZero`/`half139_of_leaves`/`prop_8_9_of_source`-analogue) | ~300 | |
| `SourceData.lean`-analogue (= SD2's `SourceDataN.lean`) | ~500 | |
| `ThmFourTwo.lean`-analogue (= SD3's `ThmFourTwoN.lean`) | ~470 | |
| `SectionTen.lean` + `SectionTenSources.lean`-analogue | ~400 | frame summation, unframed counts (budgeted with SD3, which owns the corollary layer) |
| **total** | **≈9.1k** | vs LG-K's 9.2k retype — same class of mechanical work |

**Reused untouched (below the boundary; the hard mathematics):** `VLiftCount.lean` (with
its Plan-A vH-parameterization *inside the clone tree* as a thin generic wrapper — or, if
the owner accepts one frozen-file edit as the sole exception, the §4.2 row for
`VLiftCount` alone; either works, price one file), all of §§5–7, `SectionSeven/*`
(`MinimalBlock`), the descent/keystone/`CentralObstruction`/`ContCoh`/`FoxH` stacks,
`Reconstruction.lean`, `MarkedTarget`. The `*Local.lean` files (`Phase140/Local` 1359,
`Half139Local` 552, `RStage/Local` 659) are **not spine**: they are the `G_ℚ₂`
instantiation; their K-analogues are the §3.3 supply package (LG-K-lane-shaped, separate
budget line — owner Q6).

A finer split (reuse the target-side `RecursionFrame` fields, clone only the b-typed
count layer) could shrink this below 8k; SD-R workers may discover it file-by-file — the
table is an upper bound with the LG4a/b/c stop-and-report discipline.

---

## 5. (v) Plain-import placement

The module rule (plan A5 ⚠, recon §5) is one-directional: `module`-style files cannot
import plain-import files. The **entire clone tree imports the plain-import §5–§8 deep
layer** (`VLiftCount`, `Prop89Close`-adjacent stacks, `SectionSeven`, `SectionNine`), so:

* `GQ2/Dyadic/Recursion/*` (all §4.3 clones), `GQ2/Dyadic/SourceDataN.lean` (SD2),
  `GQ2/Dyadic/ThmFourTwoN.lean` (SD3), and later `CertificateMain.lean`/`Main.lean` (AS)
  are **plain-import**, sitting as new leaves in the position `GQ2/Roe/Main.lean`
  occupies (recon §5's "practical upshot", extended to the whole SD subtree).
* `SourceNumerics` has no §8 dependencies and *could* be `module`-style in
  `GQ2/Dyadic/Parameters.lean`-adjacent space — but every consumer is plain-import and
  plain→module imports are fine, so it lives in `SourceDataN.lean` (plain) unless F-lane
  wants it earlier; no constraint either way.
* Importing `module`-style suppliers (F1 `Parameters`, F3 `TameQuotientK`/`TameBoundary`
  — both module-style, checked; MC2 `Cores` at AS-time) **into** plain files is legal
  (the `Roe/Main.lean:82-90` precedent states exactly this pattern).
* `GQ2.lean` gains one import line per new file, committed path-limited with the file
  (worker protocol §5 of the plan).

---

## 6. (vi) Phase-interface fields — the WW4 coordination section

*Self-contained for the WW4 worker; written against the board's WW4 spec ("aligned with
the actual SourceData obligation families …, per the ledger's B4 warning; coordinate
field shapes with SD1's memo before freezing") and the G-1 release entry. Authorities:
packet §6 (`lem:gauss-translate`, `cor:gauss-count`, `def:affine-B4`, and the remark "the
current gq2-lean development does not make this erroneous inference … parameterize that
existing record"), ledger §3.4, refs/README override 3, `selection-freeze.md` (esp. row 5).*

### 6.1 What "affine phase interface" means here

The draft's B4 ("equal unshifted Gauss sums") is **insufficient** (packet §6's
insufficiency proposition): the induction consumes *shifted* sums
`Σ (−1)^{Q(x)+ℓ(x)} = (−1)^{Q(y)}·Σ (−1)^{Q(x)}` (`lem:gauss-translate`), and the sign
`(−1)^{Q(y)}` must be matched between the sources. In the Lean development this matching
is **not a new interface to build**: it is already factored into five obligation families
of the source record plus a *source-independent* phase-cover mechanism in the generic
layer (`DeltaChi`/`shChi`/`keystone`/`phaseChi`, consumed via
`two_mul_card_centralImage`'s `Δ`/`sh`/`hkey` slots, `VLiftCount.lean:775-778` — reused
untouched at degree n, §4.3). `def:affine-B4`'s three-item equivalent maps onto the
formalization as: (1) base dims/signs = the `gaussZ_*` leaves; (2) the common polar/edge
pairing = the `hsep`/`hpartial` pair; (3) the source-independent phase-cover theorem =
the generic `phaseChi` machinery (nothing for WW4 to prove — only to *feed*).

### 6.2 The five families, as the degree-n record-field shapes WW4 must target

WW4's certificates must let a branch lane discharge, for the candidate `Γ = Γ_{R_K}`
(fields of `SourceDataN`, §1.2; shapes quoted at the n = 1 anchors):

1. **Half-torsor** (`lem86`, `SourceData.lean:147-150`; shape unchanged at degree n):
   for every radical-cover datum `D` with `D.NoDescent` and every surjective
   `ρ : Γ → Bg⧸D.M`: `2 * #{f : MLifts D ρ // f.Central} = #(MLifts D ρ)`.
   *Word-side source*: the Fox certificate's lift-torsor structure (packet Prop 4.1) —
   the ℚ₂ template is `lemma_8_6_gammaA`.
2. **Separation** (`hsep`, :180-190): a `V`-cocycle whose `betaChi`-obstructions vanish
   for **all** `χ : (T^∨)^C` is `T`-liftable. *Word-side source*: the Stokes certificate's
   perfectness on the cross block (the `b_q(c₀,c₁)`-type terms of the frozen endpoints).
3. **Nondegeneracy** (`hpartial`, :193-204): `χ ≠ 0` admits a cocycle separating
   `betaChi χ · ` from `betaChi χ 0` (∂-surjectivity in the character).
4. **Cocycle cardinalities** (`hZcard`, :207-218 and `tcocycle_card`, :168-177), degree-n
   values `|V| * SN.h1Mult |V|` (= `|V|^{n+1}`) and `SN.tMult |T| * #fixedPts`
   (= `|T|^{n+1}·#fixedPts`). *Word-side source*: the Fox certificate's normal form (rank
   count of the evaluated Jacobian on the module — n+3 generators, 1 wild relation).
5. **Gauss residues** (`gaussZ_unramified/ramified`, :223-268): at the head-inflated
   enrichment, with externally given `m` (`#V = 2^{2m}`),
   `GaussZResidue … (SN.gaussUnram m)` resp. `(SN.gaussRam m)` — i.e. in expanded form
   (`Phase140/Assembly.lean:145-149`):
   `Σ_{c ∈ Z¹} (−1)^{Q⁰(c)} = |V| · (ε·2^{nm})` with `ε = (−1)^n` (unramified head:
   `F.alpha (tqTau q)` acts trivially on `P/S`) or `ε = +1` (ramified head).
   *Word-side source*: the **Hessian certificate** — change of variables to the frozen
   row's quadratic endpoint + `cor:gauss-count` — this is where WW4's `Phase.lean` does
   its real work.

### 6.3 What `Phase.lean` must therefore provide (proposed field shapes)

```lean
/-- Packet Lem 6.1 (`lem:gauss-translate`): unique polar representative + translation. -/
theorem affine_gauss_translate {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    (Q : W → ZMod 2) (hq : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (ℓ : W →ₗ[ZMod 2] ZMod 2) :
    ∃! y : W, (∀ x, ℓ x = polar Q x y) ∧
      gaussSum (fun x => Q x + ℓ x) = (-1 : ℤ) ^ (Q y).val * gaussSum Q

-- Packet Cor 6.2 (`cor:gauss-count`) in the shape the record leaves consume:
-- `(dim, ε)`-classification, `Gsum = ε·2^m`, zero counts `2^{2m−1} + ε·2^{m−1}`.
-- (ℚ₂ templates: `GQ2.QuadraticFp2.zeroCount_of_arf_zero/one`, reused by LG5 at
-- `LocalGauss/Main.lean:406-439`.)

/-- The per-branch certificate datum (Def 6.3's three items, targeted at §6.2). -/
structure PhaseCoverCertificate (…branch/module parameters…) where
  baseDim   : ℕ                 -- the half-dimension m; the module carries #V = 2^{2·baseDim}
  baseSign  : ℤ                 -- ε(Q) ∈ {±1} of the *normal form* (the frozen row's endpoint)
  gauss_eq  : gaussSum Qnf = baseSign * 2 ^ baseDim        -- via Cor 6.2
  polar_id  : …                 -- item (2): the endpoint's polar block IS the cup/edge
                                --   pairing (the b_q-block of the frozen row)
  kappa_id  : …                 -- item (3) is NOT a field: the phase-cover conversion is
                                --   the generic layer's (§6.1); the certificate only pins
                                --   the κ⁰-normalization (`CentExt κ⁰` route,
                                --   `GQ2/GaussZ/RelatorGammaA.lean:223` pattern) so the
                                --   evaluated Hessian IS `Q⁰` of the record's leaves
```

Binding constraints for WW4's freeze:

* **Target the §6.2 shapes verbatim** — do not introduce a parallel four-line B1–B4
  record (ledger §3.4: "Do not define the source interface only by equality of the
  zero-phase sums. Reuse the actual fields"; refs/README override 3).
* **The degree-n magnitudes are `SN`-valued** (§1): `Phase.lean` should state its Gauss
  outputs against an abstract `(ε, m, n)`-triple matching `SN.gaussUnram/gaussRam` — not
  against re-derived `2^{…}` literals — so branch lanes plug them into the record
  without arithmetic glue.
* **Satisfiability by WMP (the row-5 warning, binding).** `selection-freeze.md` row 5:
  *"The affine phase data required by packet row WC-Mpc has not been produced by any
  ticket"* — every procyclic certificate carries this in `known_proof_status`. So
  `HessianCertificate.affinePhase : PhaseCoverCertificate …` must be a **certificate
  input** (data the WMP-c worker will construct for the frozen `R(M,pc)` — shadow-split
  endpoint with all `T`-dependent central terms), NOT a derived/`decide`d field and NOT
  assumed present for any row until its lane produces it. Design test: the field shapes
  must be instantiable from (i) the frozen row's endpoint polynomial, (ii) a
  change-of-variables `LinearEquiv` with inverse witness, (iii) per-χ shift vectors
  `y_χ` with their `Q(y_χ)` values — nothing that presupposes the WC-Mpc analysis
  already done. The other four rows' endpoints (`q(c₀)+b_q(c₀,c₁)` twist-immune;
  `Q₀(c₀)+b_q(c₁,L_c c₀)` with the **corrected** `L_c = 1+(1+A⁻¹)(1+B)`, NC lane; the
  two compact-M projector forms; the L_sq n = 1 core) are certified in the freeze and
  bound WW4's worked examples.
* **Merge-gate echo**: gate 7 ("affine phase interface present, not just base Gauss
  signs") is checked against the §6.2 shapes; the `hE2`-exponent discipline and
  `cardH2 = 2` are not WW4's to restate.
* **Process**: per the G-1 entry, WW4 is queued behind WW3 **and this memo's review** —
  Phase.lean's field shapes freeze only after the orchestrator ratifies §6; if WW4 needs
  a deviation, it goes through the orchestrator as an SD1-memo amendment, not a silent
  divergence (two-lane file-ownership rule).

---

## 7. (vii) Owner questions

**Q1 — Architecture: clone-retype vs in-place (BINDING; blocks SD-R/SD2/SD3 dispatch).**
The b-typed spine cannot serve degree n without abstracting the boundary type (§0). Options:
(a) **clone-retype ≈9.1k lines into `GQ2/Dyadic/Recursion/`** (frozen-file edit list
EMPTY; LG1 precedent "in-place is A6-incompatible; clone"; mechanical, parallelizable
like LG4a/b/c); (b) in-place variable-ization of ~20 frozen files with abbrev-wrappers
(P2 shows the wrapper mechanics work; saves the clone lines but edits the frozen spine's
*definitions* — highest-risk merge surface of the campaign, and §4.2's numeric edits
still don't remove the boundary retype). **Recommendation: (a).** Sub-question: may
`VLiftCount.lean` alone take the one-file Plan-A edit (§4.3 note), or should its vH-form
also live clone-side? Recommendation: clone-side wrapper (keep the edit list at zero).

**Q2 — Drop the marked-generator + pinning fields from `SourceDataN`** (4 + 8 fields,
`SourceData.lean:80-108`). They are consumed nowhere (`Roe/Main.lean:68-81` documents
this and R32 could only satisfy them by *choice* elements), and MC1 §(ix) confirms rank
never enters structurally. Dropping removes the only `Fin (n+2)`-indexed family the
record would otherwise need. The marked-generator *documentation* moves to the
instantiations (which do have honest generators). **Recommendation: drop.** (Fallback: an
optional companion `structure SourceMarking (n : ℕ) (S : SourceDataN …)` for
instantiation-side convenience, never consumed by the recursion.)

**Q3 — Opaque shared constants vs n-exponent shapes in the cloned recursion interface.**
§1.1/§1.4: the solver only cancels shared constants; `pow_one` is not `rfl`, so opaque
values give strictly better definitional n = 1 adapters. **Recommendation: opaque
(`SourceNumerics` as specified), formulas confined to `standardNumerics`.**

**Q4 — Abstract marked pro-2 slot `(P, hP, nuP)` vs MC2 cores as the `PiBd` replacement**
(§2.2; the recon-flagged choice). **Recommendation: abstract slot** — SD stays
independent of MC5; AS1 instantiates at `D_P` through the marked-core certificate
(`sourceR` recipe).

**Q5 — Gauss-leaf encoding**: keep the external-`G0` seam and store the values as
`SN.gaussUnram/gaussRam : ℕ → ℤ` functions of the half-dimension `m` (recommended;
matches the source-independent `m`-obtain at `SourceData.lean:416-420`), vs inlining
`(−1)^n·2^{n·m}` in the field statements (couples every consumer to the formula).
**Recommendation: SN-valued.**

**Q6 — Budget: insert wave SD-R (the §4.3 clone) between SD1 and SD2** — the board's
current SD2/SD3 scoping (two files) cannot absorb the spine. Proposed split: SD-R1
frames+§8 (frame layer + Covers/Fourier/Partition/Recursion + Block trio, ≈3.2k), SD-R2
§9 (Terminal/Induction + MStageCount, ≈2.2k), SD-R3 Phase140+RStage+bridges+generic-Prop89
(≈2.3k), each opus-tier mechanical with stop-and-report; SD2 (fable, ≈0.5k) and SD3
(≈0.9k incl. the §10-clone corollary layer) then land on top. The K-side `*Local` supply
package (§3.3; the n = 1 scale of that pack is ≈2.6k) is a *further* line item, most
naturally an LG-lane or AS-lane ticket ("LG6"/"ASK") — owner assigns.
**Recommendation: adopt SD-R1–3 + one K-supply ticket.**

**Q7 — Ratify §6 as the WW4 coordination baseline** (field shapes + the four binding
constraints), unblocking WW4's queue position behind WW3.

---

## 8. (viii) SD2/SD3 skeletons and acceptance criteria

*(Assuming Q1(a), Q2–Q5 as recommended; SD-R1–3 land first per Q6.)*

**SD2 — `GQ2/Dyadic/SourceDataN.lean`** (fable): `SourceNumerics n` + `standardNumerics`
(§1.1); `SourceDataN n q P hP nuP SN` (§1.2, atop SD-R's cloned frame types);
`sourceBoundaryMapK`; derived API (`b`, `b_apply_coe`, `b_surjective`,
`pro2_surjective`); the three n = 1 instances `sourceA_N`, `sourceR_N` (under `hBLab`),
`sourceF_N` (§3.4).
*Acceptance*: (1) `sourceA_N.b = B.bA := rfl` and `(sourceR_N hBLab).b = (Roe.sourceR
hBLab).b := rfl`; (2) every `sourceA_N`/`sourceR_N` field witness is the n = 1 lemma
**unchanged** except the two §1.4 value bridges (`hZcard`, `gaussZ_*` — each ≤ 3 lines);
(3) `sourceF_N` assembled entirely from the existing `_local` pack (no new mathematics;
§3.1/§3.3 lists the exact lemmas incl. `hsep_local`/`hpartial_local`,
`Phase140/Local.lean:537+`); (4) plain-import; import line registered; full build green;
capstone prints byte-identical (they cannot move — no frozen file is touched).

**SD3 — `GQ2/Dyadic/ThmFourTwoN.lean`** (opus, per board): `thm_source_generic` (§3.2)
by the strong-induction skeleton of `ThmFourTwo.lean:386-414` replayed over the clones —
terminal lane via the cloned `terminal_count_eq_of_sources` (both sides through records —
the B-side special-casing at `SourceData.lean:363-377` disappears); `mStage_lane` at
`mult := SN.mMult …` (both sides record-supplied — `liftsOver_card_local` citation
disappears); `rStage_lane` via the cloned `gaussZ_obtain` (shared `G0 := SN.gauss… m`)
and `prop_8_9_of_sources`-clone (both sides through `prop_8_9_aux`-clone at
`cS := SN.homScalar` — the `_local` branch disappears); the two positivity-cancels (§4.1a).
Then: the §10-clone summation corollary `#Sur(S₁.Γ,G) = #Sur(S₂.Γ,G)` and the
`Reconstruction.lean` corollary `Nonempty (ContinuousMulEquiv S₁.Γ S₂.Γ)`.
*Acceptance*: (1) the regression theorem `thm_4_2_via_N` (§3.4) — the *statement* of
`thm_4_2` re-derived through the clone at n = 1, typechecking against the old boundary
by P1b with no cast; (2) `scripts/check_axioms.sh` check 5 green; `thm_4_2_via_N`
prints ⊆ the frozen capstone set; (3) `thm_4_2` (:443) itself untouched; (4) no sorries,
no new axioms, none of the nine obligations as axioms (`BLab`/`MLab`/`NLab` stay binders
— they don't enter SD3 at all under Q4's abstract slot); (5) plain-import.

**SD-R1–3** (opus, mechanical): per §4.3 table; acceptance = builds green, zero sorries,
zero axioms, no frozen-file edits, each clone's docstring cites its ℚ₂ source file:line
and the parameterization delta (the LG4a stop-and-report discipline on any resisting seam
— in particular any spot where a spine file turns out to use boundary structure
non-opaquely, which this survey found none of beyond the tabulated `Ttame`-relation and
`tameTau`-dichotomy sites).

---

## 9. Cross-lane notes

* **WW4**: §6 is the coordination deliverable; queue-release condition is Q7.
* **LG lane**: the `gaussZ_reduction` chain (`GQ2/GaussZ/Reduction.lean:287` — pins
  `#Z¹ = |V|²`) is n = 1-instantiation-side; its K-analogue should be stated at
  `|V|·SN.h1Mult |V|` from the start so the K Gauss bridge (§3.3 last row) lands in the
  record shape directly. Flag for the K-supply ticket, not for LG's frozen deliverables.
* **AS1**: consumes `thm_source_generic` + the §3.3 supply map; `DyadicLocalInput` has
  **no `eulerChar` field** (LG1 note — it is derived via `card_H1_eq_of_markingK`);
  `ramifiedCertificateOfSubtype`'s binder list is AS1's arithmetic input (LG5 row).
* **F5**: no impact — finite-target regressions don't touch the record.
* **MC5**: unaffected by Q4 (the certificate is consumed at AS1-time, not by SD); but if
  MC5's `MarkedCoreCertificate` shape changes the `D_P ≅ D_K` packaging, only §3.3's
  `pro2` row moves.
* **Packet citation hygiene**: this memo cites packet environments by **label**
  (`thm:source-abstract`, `def:affine-B4`, `thm:local-gauss`, `def:core-certificate`,
  `def:word-certificate`, `sec:local-inputs`). Note for the errata pass: the vendored
  TeX's *rendered* numbering places the marked-matching section 8th (its Def renders as
  8.1), while campaign documents cite "Def 7.1" (and similarly Thm 6.15 / Prop 8.1 /
  Def 9.1 shifted by one) — the §11/§12/§14 cites match. Off-by-one between the
  campaign's citation convention and the vendored compile for sections 7–10; labels are
  unambiguous, so nothing here depends on it. Worth one line in the errata bundle's
  clarification note.

---

## §6.3 amendment (orchestrator, 2026-07-31 — the AS-LANDED field shapes)

WW4 landed `PhaseCoverCertificate`/`HessianCertificate` in `GQ2/Dyadic/Word/{Phase,Hessian}.lean`
with five deviations from the proposed shapes above, all ADOPTED (this block is the record;
the landed Lean is authoritative):

1. `[Fintype W]` replaces `[Finite W]` in `affine_gauss_translate` (module-side
   `QuadraticFp2.gaussSum` target; the `[Finite]` Fourier lives in a non-module file).
2. `card_eq : Fintype.card W = 2 ^ (2 * baseDim)` is an explicit FIELD (the prose
   "#V = 2^{2m}" made binding; without it `baseDim` is unconstrained; consumed verbatim as
   the `gaussZ_*` leaves' `hcard`).
3. `polar_id` is stated through block inclusions `j₀ j₁ : V →+ W` against the
   f-antisymmetrization `dat.f v w + dat.f w v` — normalization-independent, twisted-row-safe.
4. `kappa_id` pins the diagonal to an ABSTRACT κ⁰-datum parameter `diag : V → ZMod 2`, not to
   `q` — NECESSARY: the corrected-Npc endpoint's diagonal is `npcQ0`(∘L_c⁻¹), which is not
   `q`; compact rows instantiate `diag := fun v ↦ dat.f v v`.
5. Certificate parameters are explicit `(dat, diag, Qnf, j₀, j₁)`; no `Group C` /
   `DistribMulAction` instances bound on the records.

Worked rows landed: compact-N, compact-M P=1, compact-M P=0, corrected-Npc SHAPE (the literal
`npc_cross_operators` identification is WNP-c's — module rule blocks the plain-import bridge
here). `L_sq` deliberately absent (its endpoint is the rank-3 core, not a plus form). The
six-item WMP-c `affinePhase` gap list is in WW4's report (board row pointer) — item 5 (the
`hessRelZ`-at-graph-marking word-side equation) plus the σ-column lemma are the WMP-c
dispatch's spine.
