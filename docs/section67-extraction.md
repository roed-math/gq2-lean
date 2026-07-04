# §§6–7 statement extraction (ticket P-14)

Design note for the P-14 statement layer: `GQ2/QuadraticFp2.lean`, `GQ2/Corestriction.lean`
(sorry-free def-layers), `GQ2/SectionSix.lean` (18 sorried statements), `GQ2/SectionSeven.lean`
(7 sorried statements).  Companion to `docs/section3-extraction.md` (P-06).  Proofs: **P-15**
(declared Ax: B5, B6, B7′, B9 — plus B7 inside 6.17/6.18 dimension counts, matching the App. D
row for Thm 4.2's §6 inputs; the statement layer itself consumes **no** axioms).

## Statement ↔ display map

| Lean name (`GQ2.SectionSix` / `GQ2.SectionSeven`) | Paper | Notes |
|---|---|---|
| `graphPullback_mem_Z2` | Lemma 6.1, (62) | well-formedness of the pulled-back base cocycle |
| `lemma_6_6` | Lemma 6.6, (86) | Wall doubling; rank as `#im(1+U) = 2^k` |
| `lemma_6_8` | Lemma 6.8, (87)/(88) | isotypic data as explicit `≃+`-decomposition hypotheses |
| `prop_6_9_unramified` / `_ramified` | Prop 6.9, (91) | via (83)'s two branches (see deviations) |
| `lemma_6_13_dihedral` | Lemma 6.13 | fibre extension of `κ_J` is `D₈` (`CentralExt`, `decide`-group) |
| `lemma_6_13_evens` | Lemma 6.13, (96) | `[κ_J] = N^{Ev}(e₁^∨)` on `E ⋊ J` (`SemiProd`) |
| `lemma_6_15_square` | Lemma 6.15, (103) | `S_r ↦ cor(α ⌣ α)` |
| `lemma_6_15_free` | Lemma 6.15, (104) | `C_{r,s,g} ↦ cor(α ⌣ ĝβĝ⁻¹)` |
| `lemma_6_15_involution` | Lemma 6.15, (105) | `E_{r,g} ↦ cor_{K₀/F} N^{Ev}_{K/K₀}(α)`; absorbs (100) |
| `lemma_6_16` | Lemma 6.16, (110) | deep-unit Evens norm vanishing (the Hilbert ledger (111)–(114) is its P-15 proof) |
| `lemma_6_17_dim` / `_vanish` | Lemma 6.17 | `X₊ = deepPart`; `#X₊² = #H¹`; `Q⁰_loc∣_{X₊} = 0` |
| `prop_6_18_ramified` / `_unramified` | Prop 6.18, (115) | the dyadic base determinant theorem (headline) |
| `lemma_6_14` | Lemma 6.14, (102) | **proved P-15d** (`GQ2.RepIndependence.lemma_6_14`, std-3, no B-axioms) — regular-module realization via `FactorSet.comap` + `mapCoeff1`; the Lemma-6.4 rep-independence is the inner-conjugation coboundary on `V⋊C` (`innerConj`/`repIndep`).  Statement moved out of `SectionSix.lean` (comment-pointer). |
| `lemma_6_21` | Lemma 6.21 | transgression, consequence form (see deviations) |
| `lemma_6_22` | Lemma 6.22, (121)–(123) | shear formula, cochain-exact mod an explicit coboundary |
| `exists_minimalBlock` | §7 opening | block choice under `¬ IsScalarStack` |
| `lemma_7_1_radical` / `_head` / `_dual` | Lemma 7.1 | see §7 encodings below |
| `lemma_7_2` | Lemma 7.2 | `R` central elementary; `K⁴ = 1` (tame head required) |
| `lemma_7_3` | Lemma 7.3 | decorations vanish on `K` |
| `prop_7_4` | Prop 7.4 | descended head form `q̄_λ`, `∃`-bundled with its spec |

Def-layer (sorry-free): `polar`/`IsQuadraticFp2`/`Nonsingular`/`arf`/`zeroCount`/`qDouble`
(`QuadraticFp2`); `lWord`/`lTrans`/`shapiroFun`/`cor1Fun`/`cor2Fun` (eq. (108)) and
`H1ofFun`/`H2ofFun` (`Corestriction`); `iotaF` (= `ι_F = inv_{ℚ₂}` through `𝔽₂ ≅ μ₂`),
`FactorSet`/`IsEquivariantFactorSet`/`kappa0` (61)/`graphPullback` (62)/`FactorSet.comap` (77),
`Q0loc` (92), `swapE`/`twoPointDatum` (95)/`twoPointExt` (D₈ carrier), `SemiProd`,
`RegRep`/orbit data (75)/(76)/(67)–(70), `IsDeepUnit` (93)/(94), `deepPart`,
`gammaEdge` (64)/`inflScalar`/`shear`/`thetaPhase` (122)/`gammaCupA` (123) (`SectionSix`);
`IsScalarStack`/`frattiniLike`/`MinimalBlock` (`SectionSeven`).

## Key encoding decisions

* **D1 — quadratic forms** are plain functions `q : V → ZMod 2` + the Prop `IsQuadraticFp2`
  (normalized, biadditive polar), matching the repo's plain-function cochain style.  `arf` is the
  **democratic (majority) invariant**: total, choice-free, agrees with classical Arf exactly in
  the nonsingular even-dimensional case — the only case the paper uses, and only through the
  **zero counts** (91)/(115).
* **D2 — transversal calculus**: Shapiro/corestriction use the **canonical transversal**
  `Quotient.out`.  The paper proves transversal-independence (Lemmas 6.13/6.15); fixing the
  canonical one removes a choice parameter from every statement.  P-15 may need the independence
  lemma internally; it is not part of the statement layer.
* **D3 — junk-total class formers**: `H1ofFun`/`H2ofFun` map a raw function to its class when it
  is a continuous cocycle, else to `0`.  Statements about classes of cocycles whose cocycle
  property is itself sorried (e.g. `graphPullback_mem_Z2`) stay `def`-clean this way.
* **D4 — `Q⁰_loc` on classes** uses the canonical representative (`Quotient.out`);
  representative-independence is Lemma 6.4's content — **proved P-15d** (`GQ2.RepIndependence.repIndep`
  / `graphPullback_sub_mem_B2`, std-3): `graphPullback(b) = φ_b^*κ⁰` on `V⋊C`, and a `Quotient.out`
  change conjugates `φ_b` by `(−w₀,1)`, so the classes agree since inner automorphisms act trivially
  on `H²` (`innerConj`).  `lemma_6_14` (the datum-independence half) rides on the same layer.
* **D5 — deep units via the spectral norm**: Mathlib's `NormedField (AlgebraicClosure ℚ_[p])`
  makes `U_{e+1}(K)` encodable as `A = 1 + 2b`, `‖b‖ < 1`, `A, b` fixed by `G_K` — no
  ramification-index bookkeeping (`v_K(A−1) ≥ e+1 ⟺ ‖A−1‖ < ‖2‖` since `e = v_K(2)`).
  "Unramified quadratic `L/k`" in 6.16 = index-2 fixing subgroups + **equal norm value groups**.
* **D6 — ramified/unramified dichotomy** (6.8/6.9/6.17/6.18): the lower map factors through
  `GQ2.Ttame` (`c : Ttame → C`, `ρ = c ∘ B.tameF` with `B : GQ2.BoundaryMaps`), and ramifiedness
  is "`c tameTau` acts nontrivially on `V`" — the faithful reading of "tame module with
  (non)trivial inertia".
* **D7 — §7 at `Y`-level**: all §7 statements are about subgroups of the finite target `Y`
  (normality in `Y` = module condition), avoiding quotient-module instances.  `(M^∨)^C = 0`
  becomes "no `Y`-normal index-2 subgroup of `K` above `R`"; `q̄_λ` in 7.4 is `∃`-bundled with
  its defining spec `λ(k²) = q̄(k mod S)` and its invariance/nonsingularity/nonvanishing.

> **P-15 split (2026-07-03)**: the remaining 15 proof obligations are parallelized as board
> sub-tickets **P-15a–P-15i** (`docs/tickets.md`) — quadratic engine (a) → Gauss signs (b);
> Shapiro ledger (c); Lemma-6.4 layer → 6.14 (d); Hilbert ledger 6.16 (e); deep part + 6.18
> headline (f, assembly); §7: 7.2 (g) → `lam_sq_vanish`/7.4 (h); transgression 6.21 (i).
> Each sub-ticket works in its own new file and one-line-splices the `sorry` in
> `SectionSix/Seven.lean`; the umbrella P-15 row keeps the proved-log + amendment history.

## P-15 amendments (first proof pass, 2026-07-03)

* **`IsEquivariantFactorSet` gained the field `f_cocycle`** (the additive 2-cocycle identity of
  the factor set itself).  Caught by proving `graphPullback_mem_Z2`: the paper's "normalized
  factor set" (Lemma 6.1) includes associativity of `E_f`, which the P-14 field list had dropped;
  without it the graph pullback need not be a cocycle.  All of the paper's concrete factor sets
  ((73)/(75)/(76)/(95)) are coordinate-bilinear, hence satisfy it.  Pre-P-20 amendment to the
  same ticket-line's own statement layer.
* **Proved so far (std-3, no B-axioms — pure algebra tier)**: `graphPullback_mem_Z2`,
  `lemma_6_13_dihedral` (kernel-`decide` exponent-table iso), `lemma_6_13_evens` — the two-point
  cocycle `κ_J` and the repo's Evens-norm cocycle (98) agree **on the nose** on `E ⋊ J`, so (96)
  is a function identity plus class transport.
* **`lemma_6_16` gained `[FiniteDimensional ℚ_[2] k]` and the Kummer presentation of `L/k`**
  (P-15e amendment, 2026-07-03): the generator data `(d : (↥k)ˣ, δ, hδ : δ² = d, hLδ : G_L =
  Stab(δ)` at `subgroupOf`-level`)` and the coordinates `(u, v, hAuv : A = u + vδ)` of the deep
  unit — the paper's "write `L = k(√d)` … `a = u + v√d`".  Char-≠2 Kummer theory guarantees
  the data abstractly, and the 6.17 consumer constructs it concretely; carrying it avoids the
  infinite-Galois-correspondence plumbing (`fixedField_fixingSubgroup`, `[L:k] = 2` from
  index) that deriving it in-proof would need.  The finite-dimensionality was in the informal
  statement ("finite dyadic local fields") and is required by B9/B11.  Proof layer:
  `GQ2/HilbertLedger.lean` (P-15e F-draft — ledger tiers, B11-consequence lemmas proved).
* **`prop_7_4` gained the framed-target head hypotheses** (soundness amendment #3, same shape
  as `lemma_7_2`'s: `π : Y →* H` surjective with kernel `L`, `cH : Ttame → H` continuous
  surjective).  The paper proves Prop 7.4 under §7's standing framed-target assumption, and its
  step 2 (`q_λ|_{T₀} = 0`) genuinely consumes it: the extension-splitting needs
  `H¹(H_V, V^∨) = 0`, true for tame heads (odd inertia via `s⁻¹ts = t²` ⇒ ramified case;
  odd-cyclic action image ⇒ unramified case) but false for general finite heads (sharp at
  `H¹`, e.g. `L₃(2)`-type action images).  The P-14 statement had dropped the hypothesis —
  caught in the P-15 proof pass.  Step 1 (`b_λ(T₀, M) = 0`, the socle argument) is proved
  **abstractly** at subgroup level (`lam_comm_vanish`: right-kernel `T` of the pairing +
  first-escaping layer of the scalar-stack chain + `lemma_7_1_dual`); `prop_7_4` itself (choice
  of `K`-representatives, well-definedness, nonzeroness via `λ`-kills-`Φ(K)` closure argument,
  `Y`-invariance) is **complete** modulo the single sorried private helper `lam_sq_vanish`
  (step 2), whose averaging route is mapped in its docstring — char-2 odd-averaging
  (`w := Σ c(a)`, no division), `tame_odd_order`/`zpowers_normal_of_tame` from `GQ2/Tame.lean`,
  generation of finite quotients via `FreeProfiniteGroup.homEquiv` injectivity.
* **Escalation (6.16) — RESOLVED (census decision, user-approved 2026-07-03)**: axiom B9
  (`evensKahn_dyadic`) was scoped to base `k = ℚ₂` (T-18's choice), while `lemma_6_16`
  faithfully quantifies over a general finite dyadic base `k` (the 6.17 application needs
  `k = K₀`, a general tame field).  A reduction to ℚ₂ was analyzed and is **not available**
  (restriction reaches only a 3-dimensional subspace of `k^×/(k^×)²`; the corestriction route
  is equivalent to cor-inv compatibility, itself a general-base CFT input).  Resolution:
  **B9 base-generalized in place** (finite dyadic `k`, `kummerClassK`-classes over
  `k.fixingSubgroup`, canonical roots) **+ new axiom B11 `dyadicNormCriterion`** (symbol–norm
  criterion via the norm form, and unramified unit-norm surjectivity — the two general-base
  classical inputs of 6.16's step-2 arithmetic; also covers 6.17's (94)-orthogonality needs).
  Census 11 → 12; `docs/review-packet.md` §2 amendment history.  6.16–6.18 unblocked.

## Flagged deviations (for P-20 review)

1. **Prop 6.5 and Cor 6.19 are not stated here.**  6.5 (complete base second-order word
   expansion) evaluates the relator through §5's ledger — it belongs to the P-12 seam; its
   *output* (83) is used as the definition shape of `Q⁰_A` in 6.9 (`q` when inertia acts
   trivially, `qDouble q U`, `U = powOmega2 S`, when ramified).  6.19 (complete source
   interface) is a conjunction of 5.15/5.16/5.17 + 6.9/6.18, assembled at P-16; it has no
   independent mathematical content to freeze now.
2. **Eq. (100) is folded into (105)** (`lemma_6_15_involution`): the paper derives (105) via the
   corestriction realization (100); the Lean statement asserts the consumed composite directly.
   P-15 may reintroduce (100) as an internal lemma.
3. **Lemma 6.21 in consequence form**: the obstruction identity (116) is the proof mechanism;
   what §§8–9 consume is the splitting criterion, which is what `lemma_6_21` states.  If P-16/P-17
   turn out to need the `d₂`-valued form, that is a reviewed statement addition.
4. **Democratic `arf`** (D1) and **canonical transversals** (D2), as above.
5. **Lemma 7.1's head clause** is recorded as `R ≤ K ⊓ S` — given the block's `gen : K ⊔ S = P`,
   the exact sequence and `M/T₀ ≅ V` follow by Mathlib's second isomorphism theorem, so the
   inclusion is the §7-specific content.
6. **6.8's isotypic hypotheses as data**: the Clifford-theory facts (V|_I ≅ W^{⊕s}, #W = 2^f,
   f = 2^a r) enter as explicit hypotheses of `lemma_6_8` rather than being derived from
   simplicity — deriving them is Lemma 6.11-adjacent representation theory that the statement
   layer does not need to freeze.  6.7/6.10/6.11 (Hermitian-line uniqueness, middle unit layer,
   projectivity) are proof-internal to P-15 and not separately stated.
7. **`lemma_6_22` is cochain-exact modulo an explicit coboundary term** (`∃ w, … + δw`-shape)
   rather than an `H²`-equation on `SemiProd` — equivalent content, no quotient plumbing.

## P-15/P-16 consumption map

* `prop_6_9_*` + `prop_6_18_*` ⟶ 6.19(iv)-equality of base Gauss sums ⟶ §8's Fourier step
  (P-16, Prop 8.8/8.9).
* `lemma_6_21` + `lemma_6_22` ⟶ §8 phase covers (Prop 8.8) and §9.3's central formula (151).
* §7 block (`MinimalBlock`, 7.1–7.4) ⟶ §8 fixes `T = T₀`, `M`, `V`, `q̄_λ` (Def 8.1 onward);
  `IsScalarStack` is the §9.1/9.2 scalar-regime hypothesis.
* `lemma_6_16`/`lemma_6_17_*` are internal to the `prop_6_18_ramified` proof.

## P-15i status — Lemma 6.21 transgression (`GQ2/Transgression.lean`, 2026-07-04)

The (116) **mechanism and all supporting infrastructure are proved `std-3`**; the splitting
`lemma_6_21` is reduced to **one** isolated `sorry`.  Proven, reusable:

* `bflat_bijective` — `B_q^♭ : V ≅ V^∨` for nonsingular `q` on the finite elementary-abelian `V`
  (`LinearMap.BilinForm.toDual` on the `ZMod 2`-module `V`; additivity ⟹ `𝔽₂`-linearity via
  `AddMonoidHom.toZModLinearMap`).
* `polar_fibre` — `polar q u w = ξ(iu,iw) + ξ(iw,iu)` (the fibre antisymmetrization is the polar).
* `xi_conj_cobound` — conjugation of a trivial-coefficient 2-cocycle `ξ` by `s` is the coboundary
  of `β_s(z) = ξ(s,z) + ξ(szs⁻¹,s)`.  General group-cohomology fact, worth lifting elsewhere.
* `polar_conj` — `polar` is `C`-invariant (`polar_fibre` + `xi_conj_cobound`).
* `factorSet_spec`/`factorSet_cocycle` — the `H²(C,V)` factor set of the normalized section.
* **`key_transgression`** — the (116) identity `polar q(f c d) v = A c v + A d(c⁻¹v) + A(c*d)v`
  with `A = mixedA`, i.e. `δ(mixedA) = B_q^♭ f` at cochain level.  One char-2 `linear_combination`
  of nine `hcocycle` instances after normalizing group arguments by three `hconj`-moves.
* `splitting_of_global_cocycle` — **descent** (`f = δg` from a `B_q^♭`-representable primitive `g`,
  via `bflat_bijective`-injectivity + `polar_conj`) and the **section** `s c = i(ofAdd(g c))⁻¹·σc`
  (`hconj` + `factorSet_spec` + fibre 2-torsion) are proved.

**The one remaining `sorry` (the transgression vanishing `d₂ q = 0`)**: existence of a
`B_q^♭`-representable — i.e. additive — primitive `g : C → V` with `δ(B♭ g) = B♭ f`.  Note the
design subtlety: `mixedA c` from `key_transgression` is **not additive** in `v` (its defect
`D_c(v,v') = ξ(i(c⁻¹v),i(c⁻¹v')) + ξ(iv,iv')` is a nonzero symmetric zero-diagonal fibre
2-cocycle), so `δ(mixedA) = B♭ f` does **not** give `[B♭ f] = 0` formally — the cochain identity
holds but the class need not vanish.  The vanishing is the genuine content, forced by `ξ` being a
cocycle on the whole of `B` (its base values `ξ(σ·,σ·)`), i.e. `q` being a permanent cycle in the
LHS spectral sequence.  Concretely: `D_c = δκ_c` for `κ_c = β_{(σc)⁻¹}∘i∘ofAdd`, but that `κ` is
not a `C`-1-cocycle (`δκ` measures the section's factor set), and choosing the primitives so that
`δκ = 0` is exactly `[B♭ f] = 0`.  This is beyond the "direct cochain / no spectral sequence"
route as designed; closing it likely needs the base cochain explicitly (or a `groupCohomology`
LHS-SS `d₂` argument).
