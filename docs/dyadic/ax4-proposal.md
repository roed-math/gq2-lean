# AX4 proposal — the oriented tame quotient of `G_K` at `q_K = 2^f`

**Ticket AX4** (dyadic campaign, lane AX; board `docs/dyadic/tickets.md:393`, plan §4 row AX4).
Memo only — no Lean lands with this commit, census unchanged (9).  Protocol: this memo → owner
sign-off (**G-AX**) → census-flip commit per the b9a checklist (`docs/orchestration/b9a-tickets.md`).
Until the flip, every consumer binds the statement as an explicit hypothesis (§5).

Composes with **AX3** (`docs/dyadic/ax3-proposal.md`), whose §4.1 "B1 boundary lane" bullet
recommends exactly this shape: *"recommend AX4 adopt `structure OrientedTameQuotientK
(B : MarkedRecip R K)` whose `ν_t` clauses are pinned against `B.recip` on
units/uniformizers"*.  That recommendation is **adopted**, with one addition forced by the
analysis of §1.4: the bundle is *also* parametrized by a `DyadicUnitFiltration K` (B13's
structure), because the residue degree `f` is not visible in AX3's `ℤ₂`-marked data and an
unpinned `f` makes the axiom **inconsistent** (§7 R2 — the sharpest soundness finding of this
memo).

Sources: packet `refs/dyadic-presentations-formalization-proof.tex` §3 (`T_q` display :198–203,
Lem. 3.1 :205, Lem. 3.2 :219, Lem. 3.3 :230, Prop. 3.4 :258, Thm. 3.5 :288), §12 local-inputs
table :988–1021 (note: the tame quotient is **not** a row there — see §0.0), §13 module graph
:1033; draft `refs/dyadic-presentations.tex` §2; board `tickets.md:187–194` (F3 spec),
`:298–336` (LG lane), `:92–134` (2026-07-29 AX5/LG1/AX3 log entries); plan §4 (AX4 row :192),
§7.6 (full `ℤ₂`-valued marking).  Packet overrides drafts (`refs/README.md`); nothing here hits
a disagreement.

Repo state referenced at branch `dyadic-ax` (= `dyadic`; ℚ₂ files identical to `master`
`d0714a7`).

---

## 0. What the interface must deliver (consumer-derived spec)

### 0.0 Why there is no packet row for this input

The packet's §12 local-inputs table has rows for reciprocity, Tate duality, Euler
characteristic, square classes, projectivity, Shapiro–Evens, deep Evens norm, Demushkin
classification, and profinite reconstruction — but **no tame-quotient row**, because §3 treats
`T_q` purely as an abstract profinite group and the sentence that consumes the field side is a
half-line inside Thm. 3.5's proof (:305): *"The field case is identical, using the wild inertia
and maximal pro-2 quotient of `G_K`."*  That half-line is the whole of AX4.  The ℚ₂ development
made the same input explicit as axiom **B10** only when `BoundaryMaps.tameF` had to be
constructed (`GQ2/BoundaryMapsWitness.lean:235–248`); the K-side repeats that history.  So the
packet's silence is *not* evidence that the input is free — it is an omission, and this memo is
the audit trail for it.

### 0.1 Consumer inventory

`W_K` denotes the wild subgroup at `K`, `T_{q_K} = ⟨σ, τ ∣ τ^σ = τ^{q_K}⟩_prof`, `ν_t` its
`ℤ₂`-valued unramified coordinate, `tameF_K : G_K ↠ T_{q_K}` the tame quotient map.

| consumer | exact clause consumed | where |
|---|---|---|
| **F3, Thm. 3.5 field side** (`GQ2/Dyadic/TameBoundary.lean`) | (i) *existence of the quotient map*: a continuous surjection `tameF_K : G_K ↠ T_{q_K}` whose kernel is closed normal pro-2; (ii) *ν-compatibility*: `ν_t(tameF_K g) = ν₂(pro2F_K g)` — the equalizer condition that lands `g` in `∂_K = T_{q_K} ×_{ℤ₂} D_K`.  Everything else in Thm. 3.5 (relative Goursat, `ker ν₂` pro-odd, `ker ν_t ⊆ proPKernel`) is F3's own group theory | packet :288–307; ℚ₂ precedent `BoundaryMaps.surjF` (`GQ2/BoundaryFrame.lean:403`) built by `fiberProductExists` + `ker_nuT_le_proPKernel` (`GQ2/TameTwoQuotient.lean:74`) |
| **F3, Prop. 3.4(1) field side** | *generator structure is not consumed*; only "`W_K` is `O₂(G_K)`", which is **derived** from F3's Lem. 3.3 at `q` (§1.6), exactly as `tameData_maximal` (`GQ2/Prop32.lean:1236`) derives it at ℚ₂ | packet :258–286 |
| **LG3 `c_cyclic` re-proof** (`GQ2/Dyadic/LocalGauss/Unramified.lean`) | *nothing from AX4 in the statement*: `c_cyclic` (`GQ2/UnramifiedModel.lean:69`) consumes only `gen_tq_quotient` (topological generation of `T_q` by `σ, τ`, transported along a surjection) — F3's export, axiom-free.  AX4 enters one layer up, at `prop_6_18_unramified`'s `(ρ, hfac : ∀ g, ρ g = c (B.tameF g))` and `hρsurj` (`GQ2/UnramifiedModel.lean:586–612`): the *field-side factorization + surjectivity* clauses | board `tickets.md:113` ("LG3's `c_cyclic` re-proof consumes the T_q structure") |
| **LG4 `inflationVanishes_ramifiedTame` retype** (`GQ2/LocalKummer.lean:588`) | same split: the four bricks are finite-image facts at general `q` (PJ1's `tame_odd_order_pow` / `tame_zpowers_normal_pow`, replacing `odd_orderOf_tameInertia` `:383` and `tameInertia_normal` `:410`, which hard-code `q = 2` via `tame_relation`), plus `hgen`.  AX4 supplies only the field-side `ρ = c ∘ tameF_K` + surjectivity of `tameF_K` at instantiation | board `tickets.md:98–99` (AX5 outcome (iv)) |
| **DetRamified retype** (`prop_6_18_ramified`, `GQ2/DetRamified.lean:54`) | `(c : ContinuousMonoidHom T_{q_K} C)`, `hfac` against `tameF_K`, **and `horient : TameUnitOrientation R B.tameF`** — i.e. the *orientation clause itself*, in its `TameOrientationWitness` packaging (`GQ2/TameOrientationWitness.lean:43`, discharged verbatim by `tameQuotient.nuT_recip_unit` at ℚ₂).  This is the one LG-lane consumer that touches AX4's orientation, not just its existence | `GQ2/DetRamified.lean:54–60` |
| **B1 boundary interface / `BoundaryMapsK`** (future; AS1's `DyadicLocalInput K`) | the full package: `tameF_K` surjective, `wild_isProP`, `wild_isMax` (derived), `pro2F_K` + `ker_pro2F` (axiom-free, `GQ2/MaxProP.lean`), `compatF`, `surjF` — the 21-field `BoundaryMaps` (`GQ2/BoundaryFrame.lean:368–405`) at `K` | plan §7.6; packet Thm. 1.1 :136–143 |
| **SD-n** (`SourceNumerics n`, board `tickets.md:228–232`) | the degree-one **type** field `Ttame ⇝ T_{q_K}`; the `G_K`-side record instantiation consumes the boundary package above.  No AX4 clause beyond what (B1 boundary) already needs | `GQ2/SourceData.lean:88` (`tame` field) |
| **AS5 final theorem** | statement vocabulary only: "the isomorphism identifies the tame quotient" (packet Thm. 1.1 :136) is spelled against `tameF_K` | `tickets.md:525` |

**Reading of the inventory.**  Four distinct clauses are consumed, and no more: *existence of
the quotient map with pro-2 kernel*, *the target being `T_{q_K}` with the right `q_K`*, *the two
orientation values of `ν_t` against `rec_K`*, and (derived, not asserted) *`O₂`-maximality*.
Generator structure (`tameF_K σ = σ` etc.) is **not** consumed on the field side — unlike the
`Γ_A` side, where `tameA_sigma`/`tameA_tau` pin the map (`GQ2/BoundaryFrame.lean:375–376`);
the field side is pinned by ν-compatibility alone, which is why the ℚ₂ bundle B10′ carries no
generator clause either.

Design constraint from the trust boundary (plan §0.3, packet :1023): the axiom may assert only
independently published local facts about `G_K`; never anything word- or presentation-side.  In
particular the axiom must **not** mention `Γ_R`, `W_R`, or any candidate relator.

---

## 1. Decomposition: derivable vs axiom-worthy

The dispatch asks whether the K-tame quotient is constructible from ℚ₂'s B10 plus
ramification-theoretic facts already in the repo.  §1.1–§1.3 answer that question in full (the
answer is **no**, but the analysis is what shrinks the axiom); §1.4–§1.9 classify the individual
components.

### 1.1 The restriction route, stated precisely

Write `W ≤ G_{ℚ₂}` for B10's wild subgroup (`GQ2.tameQuotient.W`), `G_K = K.fixingSubgroup`,
and `W ∩ G_K := W.subgroupOf G_K`.  The mathematics is:

* **(a)** `K^{tr} = K · ℚ₂^{tr}` — tame extensions are stable under base change, and over the
  maximal unramified `K^{ur}` all tame extensions of a given odd degree coincide (any two
  uniformizers differ by a unit, and units of `O_{K^{ur}}` are `m`-th powers for `m` odd by
  Hensel).  Hence `W_K = W ∩ G_K` as subgroups of `G_K`.  [Serre LF Ch. IV; NSW Ch. VII §7.5 —
  **UNVERIFIED-pending-PDF**, see Q7.]
* **(b)** Consequently `G_K / (W ∩ G_K) ≅ H`, the image of `G_K` in `T_tame = G_{ℚ₂}/W`, an
  **open** subgroup of index dividing `n = [K:ℚ₂]` (`G_K` is open — Mathlib's
  `fixingSubgroup_isOpen`, used at `GQ2/KummerKrullBridge.lean:144`).
* **(c)** *Classification of the open subgroups of `T_2`.*  Using the structure
  `T_q ≅ A ⋊_{q} Ẑ` with `A = Ẑ^{(2′)} = ∏_{ℓ odd} ℤ_ℓ` (NSW (7.5.2)): let `H ≤ T_2` be open,
  `c ≥ 1` the index of its image in the unramified `Ẑ`.  Then `H ∩ A = mA` for an odd `m`
  (`mA ≅ A` as topological groups, `ℓ^{a}ℤ_ℓ ≅ ℤ_ℓ` factorwise), and `H` is generated by `mA`
  and any `h = τ^b σ^c`; the closure of `⟨h⟩` meets `A` trivially (continuity of
  `x ↦ 2^x` on `Ẑ`), so `H = mA ⋊_{2^c} \overline{⟨h⟩} ≅ Ẑ^{(2′)} ⋊_{2^c} Ẑ = T_{2^c}`.
* **(d)** For the field, `c = f` = residue degree of `K/ℚ₂`, so `H ≅ T_{q_K}`, `q_K = 2^f`.

So the K-statement is **true for structural reasons** and the derivation is short *on paper*.
It is nevertheless not available in the repository, for two independent reasons.

### 1.2 Blocker 1 — the repo has the presentation of `T_2`, not its structure

`Ttame` is `profinitePresentation {tameWord}` (`GQ2/BoundaryFrame.lean:120–124`); everything the
repo knows about it is derived from the presentation through *finite* quotients: `tame_relation`
(`GQ2/TameQuotient.lean:57`), topological generation (`GQ2/Prop32.lean:129,141`), the Fermat
levels `C_{2^{2^m}−1} ⋊ C_{2^m}` (`GQ2/Prop32.lean:694–1215`), `O₂(T_tame) = 1`
(`eq_bot_of_normal_two_images`, `:1215`), τ-death in 2-groups (`GQ2/TameTwoQuotient.lean:40`).
The isomorphism `T_2 ≅ Ẑ^{(2′)} ⋊ Ẑ` — NSW **(7.5.2)**, the semidirect-product structure — is
**not** formalized, and step (c) above cannot even be stated without it (there is no `A`, no
inertia-vs-Frobenius splitting; `inertiaPart` at `GQ2/Prop32.lean:556` is the topological closure
of `⟨τ⟩`, with no proof that it is `Ẑ^{(2′)}` or that it splits off).

Formalizing (7.5.2) is a literature input of **exactly the same weight as B10 itself** (it is the
companion theorem in the same NSW subsection).  So the "derivation" would replace one axiom with
another, of equal strength, plus a hard profinite-subgroup classification.  **Nothing is saved.**

### 1.3 Blocker 2 — the residue degree is invisible to the campaign's marked data

Even granting (c), the derivation delivers `H ≅ T_{2^c}` with `c` = *the index of the image of
`G_K` in the unramified `Ẑ`*.  Pinning `c = f` is arithmetic that the repo does not have:

* The campaign's unramified marking is **`ℤ₂`-valued by design** (plan §7.6 merge gate 6;
  AX3 §2.2's `nu_ur : … →* Multiplicative ℤ_[2]`, with AX3 R5 recording that a `Ẑ`-valued
  variant is the *wrong* choice).  AX3 §1.2's relation `ν_{ℚ₂}|_{G_K} = f · ν_K` therefore pins
  only `v₂(f)`: for `f = 3` and `f = 1` the `ℤ₂`-images coincide (`3ℤ₂ = ℤ₂`).  **The odd part
  of `f` is not a function of any datum in AX3's bundle.**
* The tame index `c` is a `Ẑ`-level invariant, living in the odd directions the marking
  deliberately discards.
* The only in-repo handle on the residue degree is **B13's `DyadicUnitFiltration K`**
  (`GQ2/UnitFiltration.lean:134–157`), where `f` is pinned by the graded counts
  `#(U⁰/U¹) = 2^f − 1`, `#(U^i/U^{i+1}) = 2^f` — a *unit-filtration* invariant with no Galois
  content in the repo.  Connecting it to a Galois index is textbook ramification theory
  (`G_K → Gal(K^{ur}/K) ≅ Ẑ`, residue field `𝔽_{2^f}`) and is precisely what Mathlib lacks —
  the same gap B10's own docstring flags (`GQ2/Foundations/Axioms.lean:320–322`: *"cannot
  currently be derived … without local ramification theory for `Field.absoluteGaloisGroup`"*).

**Verdict: AX4 is a genuine new axiom.**  Its irreducible content is (i) NSW (7.5.3) at base
`K` and (ii) the identification *tame index = residue degree of B13's filtration*.  Item (ii) is
new relative to B10 (at ℚ₂ it is the vacuous `f = 1`) and is the reason the bundle must be
parametrized by a `DyadicUnitFiltration K`.

The burden **cannot be moved to the word side**: the packet's Prop. 3.4(1) produces the
*presented* `T_{q_K}` from `Γ_R`'s tame specialization, and the reconstruction compares the two
sources over the *same* boundary object, so a "define the boundary as the image `H`" dodge
merely relocates the same isomorphism `T_{q_K} ≅ H`.  Nor can it be deferred to LG: the Gauss /
deep-unit side reads `2^f` off B13's filtration, so *some* statement equating the two `f`'s is
unavoidable; AX4 is the cheapest honest place for it (§7 R2).

### 1.4 `q_K` and its pinning.  **(c) part of the irreducible clause; the parametrization is a soundness matter.**

Three ways to name `q_K` in the statement were considered:

1. **`(FF : DyadicUnitFiltration K)`, target `T_{2^{FF.f}}` — RECOMMENDED.**  Import-safe:
   `GQ2/UnitFiltration.lean` is `module`-style and imports only Mathlib +
   `GQ2.EvensKahn`, which `GQ2/Foundations/Axioms.lean:12` already imports — so
   `public import GQ2.UnitFiltration` in `Axioms.lean` is **cycle-free** (contrast AX3's R7,
   where `HasEqualNormValueGroups` sits in `Interfaces.lean`, *above* `Axioms.lean`).
   Consumers instantiate `FF := dyadicUnitFiltration K` (the proved B13 interface,
   `GQ2/Foundations/Interfaces.lean:311`).  Bonus: `FF.π` supplies a **canonical uniformizer**,
   so the orientation clause needs no `∀`-with-spec form and cannot be vacuous (kills AX3's R8
   failure mode at the tame layer).  Derived-layer obligation: `f` is independent of the chosen
   filtration (`‖π‖ = ‖π′‖` from `hπ_max` both ways, then `card_gr` at `i = 1`) — a short
   uniqueness lemma, worth landing with the bundle.
2. `(P : FieldParameters)` from F1 (`GQ2/Dyadic/Parameters.lean:80–93`) — rejected as the
   *axiom's* parameter: `FieldParameters` is an abstract record with no tie to `K`, so the axiom
   would assert the tame quotient at a caller-chosen `f`.  Inconsistent (§7 R2).  `FieldParameters`
   remains the right vocabulary one layer up, fed by `FF.f` and `finrank`.
3. A bare `(f : ℕ)` plus in-line unit-count hypotheses — same content as (1), more bytes,
   duplicates B13.

### 1.5 `W_K` closed / normal / pro-2.  **(c) axiom clauses — but see the packaging note.**

Mirrors B10's `TameQuotientData` (`GQ2/TameQuotient.lean:70–80`) verbatim at `K`.

*Packaging alternative (analysed, not recommended).*  If the bundle instead **named** the
subgroup as `W.subgroupOf G_K` (B10's `W` intersected with `G_K`), these three clauses become
derivable: closedness and normality-in-`G_K` are formal, and pro-2-ness follows from
`IsProP 2 W` once the generic lemma *"a closed subgroup of a pro-`p` group is pro-`p`"* exists
(it does **not** exist in the repo — `IsProP` is a predicate on types,
`GQ2/MaxProP.lean:61`, and the API has `isProP_of_surjective` (`GQ2/SectionThree.lean:157`) but
no subgroup version; the proof is the standard cofinality argument
`H/(H ∩ U) ↪ W/U`).  Cost: one generic lemma; benefit: three fewer clauses.  It is rejected
because it (a) makes the axiom's statement depend on B10's opaque witness rather than reading
like NSW (7.5.3) at `K`, (b) silently imports the base-change fact §1.1(a) into the trust
boundary, and (c) breaks the B10 mirror that reviewers will diff against.  Recorded as **Q3**.

### 1.6 Maximality (`W_K = O₂(G_K)`).  **(b) derived — never a clause.**

Verbatim the ℚ₂ pattern: B10 deliberately omits maximality
(`GQ2/TameQuotient.lean:41–47`), and `tameData_maximal` (`GQ2/Prop32.lean:1236`) proves it from
`eq_bot_of_normal_two_images`, i.e. from `O₂(T_tame) = 1`.  At general `q` the same proof runs
on **F3's Lem. 3.3** (`O₂(T_q) = 1`, packet :230–253): for `N ◁ G_K` closed normal pro-2, its
image in `T_{q_K}` is normal (surjectivity) and pro-2 (`isProP_of_surjective`), hence trivial,
hence `N ≤ ker tameF_K = W_K`.  **So `LocalTameQuotientK` = the AX4 bundle + a derived
`maximal` field**, exactly as `LocalTameQuotient` (`GQ2/SectionThree.lean:403`) relates to
`TameQuotientData`.

### 1.7 Surjectivity, pro-odd inertia, `ker ν₂ ⊆ proPKernel`, joint boundary surjectivity.  **(a)/(b) derived.**

* `tameF_K := equiv ∘ QuotientGroup.mk` is surjective by construction (ℚ₂ precedent
  `tameFHom_surjective`, `GQ2/BoundaryMapsWitness.lean:261`).
* Tame inertia pro-odd (packet Lem. 3.1) and `ker ν₂` pro-odd (Lem. 3.2) are **F3**, axiom-free.
* `ker ν_t ⊆ proPKernel 2 T_{q_K}` — F3's generalization of `ker_nuT_le_proPKernel`
  (`GQ2/TameTwoQuotient.lean:74`); the proof is τ-death in finite 2-groups, which at general
  `q = 2^f` is PJ1's `tame_odd_order_pow` (odd order ∧ 2-power ⇒ 1).
* Thm. 3.5's joint surjectivity at `K` = `fiberProductExists` + the above (F3), given AX4's
  ν-compatibility.

### 1.8 The orientation clauses.  **(c) axiom, two clauses, pinned against AX3.**

The B10′ pattern (`GQ2/TameQuotient.lean:99–108`): units land in `ker ν_t`; the uniformizer lands
in the geometric-Frobenius coordinate `ztwoOne⁻¹` (`rec` arithmetic, `ν` geometric — the B5 house
pair, `GQ2/Reciprocity.lean:49–66`).  Two deliberate deviations from a verbatim B10′-at-K:

* the reciprocity map is **AX3's `B.recip`**, not a fresh one — this is AX3 §4.1's "pairs with
  AX3 normalization" seam, and it is what makes §1.9's compatibility a theorem;
* the uniformizer is **`FF.π`**, a canonical element, rather than a `∀`-quantified spectral spec
  (AX3 §2.2's `nu_ur_recip_uniformizer` shape).  The unit clause stays `∀`-quantified over
  `‖u‖ = 1` because *all* units are needed for the density argument of §1.9.

Citation for both: Serre, *Local Fields*, Ch. XIII §4, Prop. 13 and its corollary (reciprocity
maps units onto inertia; a prime element to a Frobenius lift) — the same pair B10 cites
(`GQ2/Foundations/Axioms.lean:311–313`).  **UNVERIFIED-pending-PDF at base `K`** (Q7).

### 1.9 ν-compatibility `ι ∘ ν_t ∘ tameF_K = ν_ur^K` and `compatF` at `K`.  **(b) derived.**

This is the clause the B1-boundary lane actually consumes, and it is a **theorem over the two
bundles**, not an axiom clause — the ℚ₂ template is `tame_reciprocity`
(`GQ2/BoundaryMapsWitness.lean:346`): both sides are continuous homs `G_K^{ab} → Multiplicative ℤ₂`;
they agree on the dense image of `rec_K` (AX3's `denseRange_recip`) because they agree on
`rec_K(π)` and on `rec_K(O_K^×)` — the two orientation clauses of §1.8 matched against AX3's
`nu_ur_recip_unit` / `nu_ur_recip_uniformizer`.

One ingredient replaces ℚ₂'s two-generator lemma `padic_hom_eq_of_gens` (`ℚ₂ˣ = ⟨2⟩ × ⟨−3⟩`):
at `K` one needs `Kˣ = π^ℤ · O_K^×`, which is **in-repo derivable** from the value-group lemma
`norm_eq_zpow` (`GQ2/UnramifiedNorm.lean:46`: every nonzero `x ∈ k` has `‖x‖ = ‖FF.π‖^m`) — set
`u := x/π^m`, then `‖u‖ = 1`.  Cost: a dozen lines; no new input.  `compatF` at `K`
(`ν_t(tameF_K g) = ν₂(pro2F_K g)`) then follows exactly as at ℚ₂, through AX3's descended
`nuTwoK` on `D_K`.

### 1.10 B10-compatibility `W_K = W ∩ G_K`.  **Half-derivable; no consumer; OMIT.**

* `⊇` is derivable: `W ∩ G_K` is closed, normal in `G_K`, pro-2 (modulo §1.5's missing generic
  lemma), hence `≤ W_K` by §1.6's maximality.
* `⊆` is **not** cheaply derivable.  The image `P` of `W_K` in `T_tame` is pro-2 and normalized
  by the open image `H` of `G_K`, so `P ≤ O₂(H)`; concluding `O₂(H) = 1` needs `H ≅ T_{2^c}`,
  i.e. §1.2's blocker again.  The naive "take the normal closure of `W_K` in `G_{ℚ₂}`" fails:
  `G_K` need not be normal, and a subgroup generated by a conjugation-stable family of *non-normal*
  pro-2 subgroups need not be pro-2 (two involutions generate a dihedral group).
* No consumer needs it (§0.1: every K-side statement is intrinsic to `K`).  **Do not assert it.**
  The audit value it would have carried is delivered instead by the `K = ⊥` regression (§3),
  where both maximality theorems apply and force `W_⊥ = W` as a *theorem*.

### 1.11 Summary table

| component | class | mechanism |
|---|---|---|
| `W_K` closed, normal, pro-2 | **(c) axiom** (3 clauses) | NSW (7.5.2) + Serre LF Ch. IV at base `K`; derivable only under the rejected `W ∩ G_K` packaging (§1.5, Q3) |
| `G_K / W_K ≅ T_{q_K}` | **(c) axiom — the irreducible core** | NSW (7.5.3) (Iwasawa) at base `K`, `q = q_K` |
| `q_K = 2^{FF.f}`, `FF.f` = B13 residue degree | **(c) inside the same clause** | tame index = residue degree; *not* derivable (§1.3) — and unpinned `f` is inconsistent (§7 R2) |
| orientation: `ν_t(rec_K u) = 1` for `‖u‖ = 1` | **(c) axiom** | Serre LF Ch. XIII §4 Prop. 13 |
| orientation: `ν_t(rec_K π) = ztwoOne⁻¹` | **(c) axiom** | ibid., corollary; B10′ geometric convention |
| `tameF_K` surjective | (b) derived | `equiv ∘ mk` |
| `W_K = O₂(G_K)` (maximality) | (b) derived | F3 Lem. 3.3 at `q` + `isProP_of_surjective`; ℚ₂ precedent `tameData_maximal` |
| tame inertia pro-odd; `ker ν₂` pro-odd; `ker ν_t ≤ proPKernel` | (a) derived | F3 Lem. 3.1/3.2 (+ PJ1's `tame_odd_order_pow`) |
| `ι ∘ ν_t ∘ tameF_K = ν_ur^K`; `compatF` at `K` | (b) derived | §1.9, `tame_reciprocity` template + `norm_eq_zpow` |
| Thm. 3.5 joint surjectivity at `K` | (b) derived | F3 + `fiberProductExists` |
| `W_K = W ∩ G_K` | (⊇) derived / (⊆) blocked | **omitted, no consumer** (§1.10, Q3) |
| `T_{q_⊥} ≅ Ttame`, `W_⊥ = W` | (b) derived | §3 regression |
| generator pinning `tameF_K σ = σ` | — | never consumed on the field side (§0.1) |

---

## 2. The proposed interface

### 2.1 What F3 must export (the interface contract — coordinate, do not implement)

AX4's *type* mentions F3's objects, so `GQ2/Foundations/Axioms.lean` must be able to import
them.  The ℚ₂ precedent splits exactly here: `Ttame`/`nuT` live in the statement-layer
`GQ2/BoundaryFrame.lean`, while Lem. 3.1/3.3 and Prop. 3.2 live in `GQ2/Prop32.lean`, *above*
`Axioms.lean`.  F3's board spec (`tickets.md:187–194`) puts all of it in one file
`GQ2/Dyadic/TameBoundary.lean`; if that file ends up importing `GQ2/Foundations/Interfaces.lean`
or the §8/§9 stack, **the axiom cannot be stated**.  Requested contract (⚠ **Q4** — orchestrator
must arbitrate the file split before F3 starts):

```lean
-- statement layer (importable from `GQ2/Foundations/Axioms.lean`; `module`-style;
-- imports at most `GQ2.BoundaryFrame` / `GQ2.MaxProP` / `GQ2.ProfinitePresentation`)
noncomputable def tameWordQ (q : ℕ) : FreeProfiniteGroup (Fin 2)     -- conjP τ σ * (τ^q)⁻¹
noncomputable def Tq (q : ℕ) : ProfiniteGrp := profinitePresentation {tameWordQ q}
noncomputable def tqSigma (q : ℕ) : Tq q
noncomputable def tqTau   (q : ℕ) : Tq q
theorem tame_relation_q (q) : conjP (tqTau q) (tqSigma q) = tqTau q ^ q
noncomputable def tqToZhat (q : ℕ) : ContinuousMonoidHom (Tq q) Zhat     -- Ẑ-valued
noncomputable def nuTq (q : ℕ) : ContinuousMonoidHom (Tq q) Ztwo         -- 2-primary
@[simp] theorem nuTq_tqSigma (q) : nuTq q (tqSigma q) = ztwoOne
@[simp] theorem nuTq_tqTau   (q) : nuTq q (tqTau q) = 1

-- proof layer (may live above; `gen_tq_quotient` is LG's acceptance item, board :113)
theorem gen_tq_quotient {H} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (c : (Tq q) →* H) (hc : Continuous c) (hs : Function.Surjective c) :
    Subgroup.closure {c (tqSigma q), c (tqTau q)} = ⊤
theorem o2_Tq_eq_bot (q) …                      -- packet Lem. 3.3, feeds §1.6
theorem tq_two_equiv : ContinuousMulEquiv (Tq 2) Ttame   -- ideally `rfl`-level; §3, §7 R7
```

`Ztwo`, `ztwoOne`, `Zhat`, `conjP`, `profinitePresentation` are unchanged
(`GQ2/BoundaryFrame.lean:165`, `GQ2/Zhat.lean`, `GQ2/ProfinitePresentation.lean`).

### 2.2 Definition layer (axiom-free leaf, working name `GQ2/Dyadic/TameQuotientK.lean`)

Reuses AX3 §2.1's vocabulary verbatim (`GalK K`, `GalKab K`, `toAbK`, `commClosureK`), so the two
memos compose with no adapter.  New definitions:

```lean
variable (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])) [FiniteDimensional ℚ_[2] K]

/-- B13's uniformizer as a unit of `K` (`FF.π ∈ K`, `≠ 0`). -/
noncomputable def uniformizerK (FF : DyadicUnitFiltration K) : (↥K)ˣ :=
  Units.mk0 ⟨FF.π, FF.hπ_mem⟩ (by simpa using FF.hπ_ne)

/-- `q_K = 2 ^ f`, the residue cardinality read off B13. -/
def qOf (FF : DyadicUnitFiltration K) : ℕ := 2 ^ FF.f
```

### 2.3 The bundle

```lean
/-- **The oriented tame quotient of `G_K` at `q_K = 2^f` (the general-`K` form of B10′).**
A closed normal pro-2 subgroup `W ≤ G_K` (wild inertia, encoded intrinsically — Mathlib has no
ramification theory, the B10 deviation) with a continuous isomorphism
`G_K / W ≅ T_{q_K}`, `q_K = 2^{FF.f}` the residue cardinality of B13's unit filtration, whose
unramified coordinate `ν_t` is *compatible with AX3's marked reciprocity at `K`*: units land in
`ker ν_t`, and the B13 uniformizer — `rec_K(π)` = *arithmetic* Frobenius — lands in the
geometric-Frobenius coordinate `ztwoOne⁻¹` (the presented `σ` is geometric: `tame_relation_q`
reads `σ⁻¹τσ = τ^q`, so `σ` is NSW (7.5.3)'s `σ⁻¹`).

Both orientation clauses read the value through an arbitrary lift `g` of the abelianized class
(well-posed: `ν_t ∘ equiv ∘ mk` kills `commClosureK` — continuous into an abelian T2 target),
exactly as B10′ (`GQ2/TameQuotient.lean:99–108`).

**Maximality is not a field**: `W = O₂(G_K)` is F3's Lem. 3.3 at `q` (see
`GQ2/Prop32.lean:1236` for the `q = 2` precedent), a theorem obligation, not an assertion. -/
structure OrientedTameQuotientK {R : LocalReciprocity}
    (B : MarkedRecip R K) (FF : DyadicUnitFiltration K) where
  /-- The wild subgroup `W_K ≤ G_K`. -/
  W : Subgroup (GalK K)
  /-- `W_K` is normal. -/
  [normal : W.Normal]
  /-- `W_K` is closed. -/
  isClosed : IsClosed (W : Set (GalK K))
  /-- `W_K` is pro-2. -/
  isProP : IsProP 2 W
  /-- The tame quotient: `G_K / W_K ≅ T_{q_K}`, `q_K = 2 ^ f` the residue cardinality. -/
  equiv : ContinuousMulEquiv (GalK K ⧸ W) (Tq (qOf K FF))
  /-- **Orientation, units.** `ν_t(tame(rec_K u)) = 1` for every unit (`‖u‖ = 1`, the B11b
  idiom).  [Serre LF Ch. XIII §4, Prop. 13.] -/
  nuT_recip_unit : ∀ (u : (↥K)ˣ) (g : GalK K),
      ‖((u : ↥K) : AlgebraicClosure ℚ_[2])‖ = 1 →
      toAbK K g = B.recip u →
      nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = 1
  /-- **Orientation, uniformizer.** `ν_t(tame(rec_K π)) = ztwoOne⁻¹` for B13's `π`
  (arithmetic Frobenius, geometric coordinate `−1`).  [ibid., corollary; B10′ pattern.] -/
  nuT_recip_uniformizer : ∀ g : GalK K,
      toAbK K g = B.recip (uniformizerK K FF) →
      nuTq (qOf K FF) (equiv (QuotientGroup.mk g)) = ztwoOne⁻¹
```

Notes on the encoding:

* Five clauses + one `Prop`-carrying instance binder — **strictly fewer than B10′'s six**, because
  the `∀`-spec uniformizer of AX3 §2.2 is replaced by `FF.π` and no generator clause is needed
  (§0.1).
* `normal` is an instance binder so the quotient `GalK K ⧸ W` elaborates (verbatim B10's device,
  `GQ2/TameQuotient.lean:74` and its module note :48–50).
* The structure is parametrized by `(B : MarkedRecip R K)` — AX3 §4.1's recommendation — and by
  `FF`; at the axiom use-site both are pinned (§2.4).  This mirrors
  `OrientedTameQuotient (R : LocalReciprocity)` (`GQ2/TameQuotient.lean:99`).
* No `maximal`, no `f`-relation, no `W = W ∩ G_K`, no `Ẑ`-valued clause, no `compatF`: all
  derived or omitted per §1.

### 2.4 The axiom (draft statement for `GQ2/Foundations/Axioms.lean`)

```lean
/-- **[Composite — AX4 (oriented tame quotient of `G_K` at `q_K = 2^f`).]**  For every finite
`K/ℚ₂` inside `ℚ̄₂` and every B13 unit filtration `FF` of `K`, the tame quotient of `G_K` in the
geometric normalization: a closed normal pro-2 subgroup `W ≤ G_K` (wild inertia) with
`G_K / W ≅ T_{q_K} = ⟨σ, τ ∣ τ^σ = τ^{q_K}⟩_prof` at the residue cardinality
`q_K = 2^{FF.f}`, whose unramified coordinate `ν_t` matches the AX3 marked-reciprocity
normalization at `K` — `ν_t(tame(rec_K u)) = 1` for units `u` and
`ν_t(tame(rec_K π)) = ztwoOne⁻¹` for the filtration's uniformizer `π`.

The derived layer (`GQ2/Dyadic/TameQuotientK.lean`) constructs from these fields the surjection
`tameF_K : G_K ↠ T_{q_K}`, its `O₂`-maximality (F3's `O₂(T_q) = 1`, the general-`q` form of
Lemma 3.3 — `GQ2/Prop32.lean:1236` is the `q = 2` precedent), the tame-reciprocity identity
`ι(ν_t(tameF_K g)) = ν_ur^K(g^{ab})` and hence the boundary compatibility
`ν_t ∘ tameF_K = ν₂ ∘ pro2F_K`; none of these is a clause.

**Composite classification** (the B3c/B8/B11a class): (i) existence of the tame quotient with
the displayed presentation is classical [NSW (7.5.3) (Iwasawa) at base `K`, with (7.5.2) and
`G(k̄|k_tr)` pro-`p` — Serre LF Ch. IV]; (ii) the orientation clauses are classical [Serre LF
Ch. XIII §4, Prop. 13 and its corollary]; (iii) the identification of the tame index with
**B13's residue degree** `FF.f` is the ramification-theoretic bridge that the repository cannot
supply (no residue field at the Galois level) — it is vacuous at `K = ℚ₂` (`f = 1`), which is why
B10 has no analogue of it.  The clause set deliberately omits maximality of `W` (proved),
generator pinning (never consumed), the compatibility `W = W_{ℚ₂} ∩ G_K` (no consumer), and any
`Ẑ`-valued marking (plan §7.6 fixes the marking as `ℤ₂`-valued).

Citation: **NSW [1], Ch. VII §7.5, Theorem (7.5.3) (Iwasawa)** with **(7.5.2)**; Serre, *Local
Fields* [7], Ch. IV (wild inertia is pro-`p`) and Ch. XIII §4, Prop. 13 with its corollary
(reciprocity maps units onto inertia, a prime element to a Frobenius lift).  Paper: packet §3
(`T_q` display, Prop. 3.4, Thm. 3.5 field side).  `docs/literature-axioms.md` AX4 (dyadic).
Verification of the general-`q`/general-`K` forms against the cited PDFs is **pending G-AX**
(this docstring must not claim it before the check — Q7). -/
axiom orientedTameQuotientAt (K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2]))
    [FiniteDimensional ℚ_[2] K] (FF : DyadicUnitFiltration K) :
    Dyadic.OrientedTameQuotientK (markedRecipAt K) FF
```

**Faithfulness class: composite project interface** (Axioms.lean header taxonomy :55–59), with
clauses (i) and (ii) individually at "classical theorem with encoding choices" strength (B10's
own class) and (iii) as the composite element.  Honest deviations for
`docs/literature-axioms.md`: wild inertia characterized, not constructed (inherited from B10);
`q_K` named through B13's unit-filtration `f` rather than a residue field; uniformizer spelled
as B13's `π`; unit clause spelled by the spectral-norm idiom `‖u‖ = 1`; the presented `σ` is
geometric (NSW's `σ⁻¹`).

### 2.5 Derived layer shipped with the bundle file (axiom-free, bundle-parametrized)

Following the B5/B10′ stress-test discipline (everything below takes
`(B : MarkedRecip R K) (FF) (T : OrientedTameQuotientK B FF)`, so `#print axioms` = std-3):

* `tameFK T : ContinuousMonoidHom (GalK K) (Tq (qOf K FF))` (`equiv ∘ mk`), `tameFK_surjective`,
  `ker_tameFK` — the `GQ2/BoundaryMapsWitness.lean:248–290` template;
* `tameDataK_maximal` (§1.6) and the packaged `LocalTameQuotientK` extending the bundle with
  `maximal` — the `GQ2/SectionThree.lean:403` template;
* `tame_reciprocity_K` (§1.9) and `compatF_K` — via `norm_eq_zpow`
  (`GQ2/UnramifiedNorm.lean:46`) and AX3's `nu_ur_recip_*`;
* `TameUnitOrientationK` in the `GQ2/TameOrientationWitness.lean:43` packaging, the shape
  `prop_6_18_ramified` consumes (`GQ2/DetRamified.lean:57`);
* `f`-uniqueness for `DyadicUnitFiltration K` (§1.4) and the `f`-consistency stress test against
  AX3 §2.4's `ν_{ℚ₂} ∘ incl = f · ν_K` — with the **caveat recorded in §1.3** that this test can
  only ever confirm `v₂(f)`, so it is a regression, never a pin;
* the `K = ⊥` regression of §3.

---

## 3. The `K = ⊥` regression (merge-gate-8-style)

Statement to prove in the derived layer, at the bottom intermediate field
(`⊥.fixingSubgroup = ⊤`, `f = 1`, `q_⊥ = 2`):

```lean
theorem tameQuotientK_bot_reduces
    (FF : DyadicUnitFiltration (⊥ : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])))
    (B : MarkedRecip localReciprocity ⊥) (T : OrientedTameQuotientK B FF) :
    FF.f = 1 ∧ FF.e = 1 ∧
    (T.W.map (botGalEquiv : GalK ⊥ ≃* AbsGalQ2) = GQ2.tameQuotient.W)
```

Proof route (all bundle-level, no new axiom):

1. **`e = 1`, `f = 1`.**  In `⊥ = ℚ₂` the maximal spectral norm `< 1` is `‖2‖`
   (`hπ_max` applied to `2`, and `‖π‖ ≤ ‖2‖` in the other direction), so `FF.he` forces
   `e = 1`; then `card_gr` at `i = 1` computes `#(U¹/U²) = #((1+2ℤ₂)/(1+4ℤ₂)) = 2 = 2^f`.
   This is the *only* place in the campaign where `f` is computed from B13's clauses rather than
   assumed — the R2 guard (§7).
2. **`W_⊥ = W`.**  Both are maximal closed normal pro-2: `tameData_maximal`
   (`GQ2/Prop32.lean:1236`) gives `W_⊥ ≤ W`; §1.6 at `K = ⊥` gives `W ≤ W_⊥`.  **This is the
   compatibility of §1.10, delivered as a theorem where it can be.**
3. **`T_{q_⊥} = Tq 2 ≅ Ttame`** — F3's `tq_two_equiv` (ideally `rfl`; §7 R7).
4. Optional (recommended if cheap): the orientation transport — `T`'s two clauses reduce to
   B10′'s `nuT_recip_unit`/`nuT_recip_uniformizer` through AX3 §3's `⊥`-transport of `rec`/`ν`.
   Step 4 carries the plumbing burden (⊥-transport of units, `⊤` fixing subgroup, instance-path
   pinning — AX3 R6); if it stalls, steps 1–3 are already the substantive regression and step 4
   becomes a follow-up ticket.

Step 1 alone justifies the `DyadicUnitFiltration` parametrization: it is the check that the
`f` in the axiom's target is the arithmetic residue degree and not a free parameter.

---

## 4. Worked instances: `q_K` for the five quadratic test vectors

The AX3 §5 table already carries `(C, I, λ, γ, r, ε, η)`; the AX4-relevant column is `q_K`:

| `K` | `n` | `e` | `f` | `q_K` | tame target | note |
|---|---|---|---|---|---|---|
| `ℚ₂(√−2)` | 2 | 2 | 1 | 2 | `T_2` | ramified; `T_{q_K} ≅ Ttame` |
| `ℚ₂(√2)` | 2 | 2 | 1 | 2 | `T_2` | ramified |
| **`ℚ₂(√5)`** | 2 | 1 | **2** | **4** | `T_4` | **the only unramified row — the sole `q ≠ 2` exercise in the whole quadratic table** |
| `ℚ₂(√10)` | 2 | 2 | 1 | 2 | `T_2` | ramified |
| `ℚ₂(√−10)` | 2 | 2 | 1 | 2 | `T_2` | ramified |

Consequences for the implementation, both of which belong in the acceptance criteria:

* **`ℚ₂(√5)` is the load-bearing instance for AX4.**  Every other quadratic instance
  specializes `T_{q_K}` back to `Ttame`, where a wrong `q` is invisible.  AS3's √5 row must
  therefore include an explicit `q_K = 4` pin (`FF.f = 2` from the unramified unit-count row,
  `unramifiedQuadratic_units_are_norms`'s setting, `GQ2/Foundations/Interfaces.lean:217`).
* **A `q`-distinguishing regression is mandatory** (§7 R2): `T_2^{ab} = Ẑ` while
  `T_4^{ab} = Ẑ × ℤ/3` (the relator gives `τ^{q−1} ∈ [T_q,T_q]`, and `q−1` is odd), so e.g.
  `#Hom(T_4, ℤ/3) = 3` versus `#Hom(T_2, ℤ/3) = 1`.  F3 should land this as a finite-target
  stress lemma; it is the cheapest kernel-`decide`-able witness that the `q` in the axiom's
  target is doing work, and it is simultaneously the proof that an unpinned `f` would be
  inconsistent.

---

## 5. Interim binder spellings (pre-flip)

The **structure** (not the axiom) is what consumers name; they all keep compiling unchanged after
the census flip, which merely supplies the canonical instance.  Composing with AX3 §4.1:

```lean
variable {K : IntermediateField ℚ_[2] (AlgebraicClosure ℚ_[2])} [FiniteDimensional ℚ_[2] K]
variable (B : MarkedRecip localReciprocity K)      -- AX3, interim binder
variable (FF : DyadicUnitFiltration K)             -- B13, already a theorem (no binder needed
                                                   -- post-flip: `dyadicUnitFiltration K`)
variable (T : OrientedTameQuotientK B FF)          -- AX4, interim binder
```

* **F3** (`GQ2/Dyadic/TameBoundary.lean`): the group-theoretic content (Lem. 3.1–3.3, Prop. 3.4,
  and Thm. 3.5's *abstract* half) takes **no** binder.  Only the field half does:

  ```lean
  theorem boundary_surjective_field (B) (FF) (T : OrientedTameQuotientK B FF)
      (P2 : … maximal pro-2 data at K …) :
      Function.Surjective (fun g : GalK K =>
        (⟨(tameFK T g, pro2FK P2 g), compatF_K B FF T P2 g⟩ : ↥(boundarySubgroupK K FF)))
  ```

  i.e. AX4 enters through `tameFK`/`compatF_K` only.
* **LG3** (`…/LocalGauss/Unramified.lean`): statements stay at
  `(c : ContinuousMonoidHom (Tq (qOf K FF)) C)` + `hunram`/`hfaith` — **no AX4 binder**.  The
  `prop_6_18_unramified`-shaped consumers add `(T) (ρ) (hfac : ∀ g, ρ g = c (tameFK T g))` and
  get `hρsurj` from `tameFK_surjective`.
* **LG4** (`…/LocalGauss/DeepPackage.lean`, `…/Ramified.lean`): same, plus PJ1's general-`q`
  finite-image leaves for the two `q = 2`-hardcoded lemmas (`GQ2/LocalKummer.lean:383,410`); the
  ramified determinant statement additionally binds
  `(horient : TameUnitOrientationK B FF T)` — the §2.5 packaging of AX4's unit clause, which is
  what `GQ2/DetRamified.lean:57` consumes at ℚ₂.
* **MC5 / B1 boundary lane**: bind `(B)` and `(T)` together and assemble `BoundaryMapsK` (the
  21-field `BoundaryMaps` analogue); this is the single place where all of AX3 + AX4 + F3 meet.
* **SD-n**: consumes `BoundaryMapsK` as the `G_K`-side record instantiation; no direct binder.
* **AS5**: post-flip, `orientedTameQuotientAt K (dyadicUnitFiltration K)`.

Rule of thumb for reviewers: **if a statement mentions `T_q` only, it is F3 (axiom-free); if it
mentions `G_K` and `T_q` together, it is AX4.**

---

## 6. Census plan

**Count: exactly one new axiom** (`orientedTameQuotientAt`), census **10 → 11** on branch
`dyadic` (with AX3's `markedRecipAt` at 10; `master` stays at 9).  Running total for the whole
campaign so far: AX1 +0 (Route D), AX2 +0 (derivable), AX5 +0 (provable), AX3 +1, **AX4 +1**.

**Replace-vs-extend for B10.**  *Extend; do not replace.*  A b9a-style subsumption (state only
the general-`K` axiom and re-derive B10 at `K = ⊥` under the old name `GQ2.tameQuotient`) is
blocked by a chain of three dependencies:

1. **B10 is `localReciprocity`-parametrized; AX4 is `markedRecipAt K`-parametrized.**  Recovering
   `OrientedTameQuotient localReciprocity` from `OrientedTameQuotientK (markedRecipAt ⊥) FF`
   requires first bridging `markedRecipAt ⊥` to `localReciprocity` — i.e. AX3's own ⊥-subsumption,
   which **AX3 §6 explicitly declined** (its Q6: "confirm extend-not-replace for B5").  AX4 cannot
   subsume B10 more aggressively than AX3 subsumes B5.
2. The ⊥-transport plumbing (unit group of `⊥`, `⊥.fixingSubgroup = ⊤`, abelianization
   transport, the `Kummer.GaloisGroup` vs `AbsGalQ2` instance-path hazard of AX3 R6) is a real
   project whose failure modes are the silent-normalization kind.
3. `Tq 2` and `Ttame` are two definitions of the same group; a subsumption would have to be
   `rfl`-tight or every ℚ₂ consumer of `Ttame` re-elaborates through a transported iso
   (§7 R7) — precisely the frozen-ℚ₂-path violation plan A6 forbids.

The §3 regression delivers the same audit value at a fraction of the risk.  **B10 stays; B3c,
B5, B6, B7, B9, B11a untouched.**

**Ordering constraint (new, worth flagging at G-AX).**  AX4's axiom *type* mentions
`markedRecipAt K`, so **AX3's flip must land before AX4's**, or AX4 must be stated against a
bound `(B : MarkedRecip localReciprocity K)` and instantiated later.  Recommend flipping the two
in one wave, AX3 first, with a single `EXPECTED_AXIOMS` bump per commit (two commits, 9 → 10 →
11) so each is independently revertible.

**Could the delta be 0?**  Only by folding AX4's five clauses into AX3's `MarkedRecip` bundle
(one axiom `markedRecipAt` carrying reciprocity + tame data; census stops at 10).  Analysis:
*for* — the tame clauses are meaningless without AX3's `ν`, and the bundle would be
parametrized by nothing else; *against* — (a) at ℚ₂ the house keeps B5 and B10′ as **separate
leaves with different citations and different faithfulness rows**, and `#print axioms` is what
tells a reviewer whether a theorem depends on tameness or only on reciprocity; (b) AX3's memo is
already at the G-AX gate with its own clause list, and re-opening it costs a review cycle;
(c) Iwasawa's tame structure theorem and Lubin–Tate/norm-residue reciprocity are different
literature. **Recommendation: keep them separate (+1 → 11).**  Recorded as **Q1**.

**Census-flip checklist**, instantiated from the b9a template
(`docs/orchestration/b9a-tickets.md:27–45`):

1. Land F3's statement-layer leaf (`Tq`, `nuTq`, `tame_relation_q`, `tq_two_equiv`) — §2.1's
   contract, import-clean for `Axioms.lean` (**Q4**).
2. Land `GQ2/Dyadic/TameQuotientK.lean` (structure §2.3 + derived layer §2.5 + §3 regression) —
   axiom-free, `module`-style, `lake env lean` green.  Ownership: a small ticket **AX4-b**,
   paired with AX3-b (**Q5**); `GQ2.lean` import line is orchestrator-owned (board 2026-07-29
   protocol (a)).
3. Owner **G-AX** sign-off on §2.4's statement, the Q1–Q8 answers, and PDF verification of NSW
   (7.5.2)/(7.5.3) at general `q` and Serre LF Ch. XIII §4 Prop. 13 at general `K` (**Q7**) —
   the house "verified against the cited PDFs" line must not be written before that check.
4. Single atomic census commit on `dyadic`: the axiom into `GQ2/Foundations/Axioms.lean`
   (+ `public import GQ2.UnitFiltration` and `public import GQ2.Dyadic.TameQuotientK`; header
   census list 10 → 11 with an AX4/B10-K row); `scripts/check_axioms.sh` `EXPECTED_AXIOMS` bump;
   `docs/literature-axioms.md` new row (label: propose **B10-K**, alias AX4, keeping the
   B-taxonomy and matching AX3's proposed **B5-K**); `formalization.yaml`; `GQ2/AxiomLedger.lean`
   row (`GQ2/AxiomLedger.lean:60` is B10's); check whether `Challenge.lean` /
   `comparator-config.json` pin the axiom-name list (they did at b9a T5).
5. Gates before merge to `dyadic`: full build green; `check_axioms.sh` count exact; audited ℚ₂
   capstones print **byte-identical** axiom sets (check 5 — neither AX3 nor AX4 may leak into any
   ℚ₂ capstone; the `Ttame`-vs-`Tq 2` bridge is the leak risk, §7 R7); zero sorries outside the
   allowlist; consumers that pre-bound the structure keep compiling unchanged.
6. Docs sweep (`literature-axioms` cross-refs; this memo gains a "landed as" postscript; the
   `docs/dyadic/literature-axioms-dyadic.md` skeleton AS5 owns gets its AX4 row).

---

## 7. Risk register

* **R1 (geometric vs arithmetic Frobenius — the double convention).**  `rec` arithmetic + `ν`
  geometric is the B5 house pair; `σ ∈ T_q` is **geometric**, NSW's is arithmetic, matched by
  `σ ↦ σ⁻¹` (`GQ2/TameQuotient.lean:32–40`).  A `+1` where `−1` belongs in
  `nuT_recip_uniformizer` flips the boundary orientation and every `γ`-dependent branch row.
  Guard: the §3 regression (agrees with B10′'s `ztwoOne⁻¹`), and the rule that AX4's clauses are
  pinned against **AX3's `B.recip`**, never against a freshly chosen reciprocity map.
* **R2 (unpinned `f` ⇒ INCONSISTENCY — the sharpest trap).**  If the axiom is stated with a free
  `f : ℕ` (or with F1's `FieldParameters`, which is not tied to `K`), it asserts
  `G_K/W ≅ T_{2^f}` for *every* `f`.  But `T_{2}^{ab} = Ẑ` and `T_{4}^{ab} = Ẑ × ℤ/3` are not
  isomorphic (the relator forces `τ^{q−1} ∈ [T_q,T_q]`, `q − 1` odd), so two instantiations give
  `T_2 ≅ T_4`, from which `False` is derivable by a finite-quotient count.  This is the exact
  analogue of B5's discrete-target trap (`GQ2/Reciprocity.lean:75–79`).  **Mandatory guards:**
  (i) the `DyadicUnitFiltration` parametrization of §1.4; (ii) the §4 `#Hom(T_q, ℤ/3)`
  regression, which must be in the bundle file's test section from day one; (iii) the §3 step-1
  computation `FF.f = 1` at `⊥`, which is the only place `f` is *computed*.
* **R3 (odd part of `f` is invisible to every ν-based test).**  §1.3.  No amount of
  ν-compatibility testing can detect a wrong odd part of `f`; do not let a reviewer (or a future
  refactor) treat AX3 §2.4's `f`-relation stress test as a pin.  The unit-filtration counts are
  the only witness.
* **R4 (vacuous orientation clause).**  Mitigated by construction: `FF.π` exists and is a unit
  of `K`, so `nuT_recip_uniformizer` has content (contrast AX3 R8, where the `∀`-spec form could
  be vacuous).  Residual risk: `nuT_recip_unit`'s `‖u‖ = 1` guard — check that `1 : (↥K)ˣ` and
  at least one non-trivial unit satisfy it in the test section.
* **R5 (import layering).**  The axiom's type mentions `Tq`, `nuTq`, `MarkedRecip`,
  `DyadicUnitFiltration`.  `Axioms.lean` is `module`-style, so **every one of those must live in
  a `module` file below it**: `UnitFiltration.lean` ✓ (verified: imports only Mathlib +
  `GQ2.EvensKahn`), AX3's `MarkedRecipBundle.lean` ✓ (by AX3 §2.1's design), F3's leaf
  **⚠ unverified — Q4**.  Anything reaching `Foundations/Interfaces.lean` or the §8/§9 stack
  breaks the flip.
* **R6 (instance-path trap).**  Inherited from AX3 R6: `K.fixingSubgroup` lives in
  `Kummer.GaloisGroup ℚ_[2]` while the ℚ₂ tame development lives in `AbsGalQ2` — definitionally
  equal, different registered `Group` instances.  `GalK`/`toAbK` must be reused verbatim from
  AX3's bundle file; never introduce a second K-side abelianization.
* **R7 (`Tq 2` vs `Ttame` fork).**  Two definitions of the same group in one library is a
  maintenance hazard and a check-5 risk: if any ℚ₂ capstone is re-routed through `Tq 2`, its
  axiom print changes.  Requirement: F3 defines `tameWordQ q` so that `tameWordQ 2` is
  **syntactically** `tameWord` (`GQ2/BoundaryFrame.lean:120`), making `tq_two_equiv` an identity;
  and no existing ℚ₂ file is edited (plan A6).
* **R8 (maximality mistaken for a clause).**  A reviewer diffing against `LocalTameQuotient`
  (`GQ2/SectionThree.lean:403`) may ask why `maximal` is missing.  It is §1.6's theorem; the
  docstring says so explicitly, mirroring B10's module note.  Do **not** add it as a field: that
  would put a *proved* paper statement into the trust boundary.
* **R9 (over-claiming the citation).**  NSW (7.5.3) is stated for a general local field with
  residue cardinality `q`, so the general-`K` form is a *direct* instantiation for clause (i) —
  but clause (iii) (tame index = B13's `f`) is **not** in any single cited theorem; it is the
  composite element.  The docstring must keep them separated (it does), and
  `docs/literature-axioms.md` must not label the whole axiom "direct classical theorem".

---

## 8. Open questions for the owner (G-AX gate)

* **Q1** One separate axiom (**recommended**, §6: census 10 → 11) or fold the five tame clauses
  into AX3's `markedRecipAt` bundle (census stops at 10)?  *Interacts with AX3 Q1* (which asked
  the mirror question inside AX3: one axiom vs splitting plain reciprocity from the marked pack).
  A consistent answer is: one bundle per literature theorem — B5-K and B10-K separate.
* **Q2** Confirm the `DyadicUnitFiltration K` parametrization of `q_K` (§1.4), i.e. that the
  axiom's *residue degree* is B13's.  This is the soundness-critical choice (R2); the
  alternatives are a free `f` (inconsistent) or an in-line restatement of B13's counts
  (duplication).
* **Q3** Packaging of the wild subgroup: self-contained `W` with three clauses (**recommended**,
  mirrors B10) versus naming it as `W_{ℚ₂} ∩ G_K` and deriving the three clauses (§1.5), which
  imports the base-change fact §1.1(a) into the trust boundary.  Related: confirm **omitting**
  the compatibility `W_K = W_{ℚ₂} ∩ G_K` entirely (§1.10 — no consumer).
* **Q4** **F3 file split** (orchestrator arbitration needed *before* F3 is dispatched): F3's
  board spec puts `T_q` and all of §3's proofs in one file, but the axiom's type needs `Tq`,
  `nuTq`, `tame_relation_q` in a leaf importable from `GQ2/Foundations/Axioms.lean` (the ℚ₂
  precedent splits `BoundaryFrame.lean` from `Prop32.lean`).  Also: F3 must export
  `gen_tq_quotient` (already on the board, `tickets.md:113`), `o2_Tq_eq_bot`, and a
  `rfl`-tight `tq_two_equiv` (R7).
* **Q5** Ownership of `GQ2/Dyadic/TameQuotientK.lean` (structure + derived layer + §3
  regression + §4's `q`-distinguishing test): a small ticket **AX4-b**, or fold into F3 / into
  AX3-b (AX3 Q5)?  It blocks the B1-boundary lane's and LG's binder spellings, so it should land
  early in wave 1, right after AX3's bundle file.
* **Q6** Does any lane need the **`Ẑ`-valued** tame character `tqToZhat` (as opposed to the
  2-primary `nuTq`)?  Plan §7.6 fixes the *marking* as `ℤ₂`-valued and AX3 R5 argues `Ẑ` would
  be the wrong choice for `ν_ur`; the `Ẑ`-level object exists inside `T_q` (F3's `tqToZhat`) and
  is where the odd part of `f` lives (§1.3).  If the answer is "no", say so now — it is a
  statement change later.
* **Q7** PDF verification at sign-off (this memo deliberately does **not** claim it): NSW
  Ch. VII §7.5 (7.5.2)/(7.5.3) at general residue cardinality `q`; Serre *Local Fields* Ch. IV
  (wild inertia pro-`p`) at general `K`; Serre LF Ch. XIII §4 Prop. 13 + corollary at general
  `K`; and — only if Q3 goes the `W ∩ G_K` way — a citable form of "tameness is stable under base
  change / `K^{tr} = K·ℚ₂^{tr}`" (§1.1(a)).
* **Q8** Fallback route, if the owner prefers no new axiom: keep `OrientedTameQuotientK` as a
  permanent **hypothesis binder** (the `BLabHypothesis` / G-Lab pattern), leaving AS5's final
  theorem conditional on it.  This is available at zero census cost and costs one binder in
  every K-side boundary statement; it is *not* recommended (the input is published and the
  campaign's headline theorem should be unconditional), but it is the same option the owner took
  for the rank-four Demushkin classification.
