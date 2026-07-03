# Ticket board — step 1 (formalized statements of B1–B9)

Source of truth for the statement-formalization effort. See `docs/formalization-plan.md` for the
rationale and designs. Difficulty: ⭐ easy · ⭐⭐ medium · ⭐⭐⭐ hard/design-sensitive.
Model: **F** = Fable (design-heavy), **O** = Opus (well-specified). Status: ☐ open · ◐ in
progress · ☑ done.

Rule: every definition ships with its stress tests in the same commit; every axiom's docstring
states conventions + paper-equation cross-reference; all `axiom`s live in
`GQ2/Foundations/Axioms.lean` only.

| ID | Title | Diff | Model | Deps | Status |
|---|---|---|---|---|---|
| T-00 | Mathlib + CFT survey (what already exists vs the B-leaves/tickets) | ⭐⭐ | O | — | ☑ 2026-07-03 (`docs/mathlib-cft-survey.md`) |
| T-01 | I1: finite discrete `G`-modules via Mathlib classes | ⭐ | O | — | ☑ 2026-07-02 (`GQ2/DiscreteModule.lean`, folded into the T-02 session) |
| T-02 | U2: continuous `H⁰/H¹/H²` — API design + core defs | ⭐⭐⭐ | **F** | T-01 | ☑ 2026-07-02 (`GQ2/Cohomology.lean`) |
| T-03 | I2b: cohomology lemma layer (cocycle algebra, inflation, restriction, functoriality) | ⭐⭐ | O | T-02 | ☑ 2026-07-02 (`GQ2/Cohomology.lean`) |
| T-04 | I3: cup products (0,2),(1,1),(2,0) rel. a pairing + bilinearity | ⭐⭐ | O | T-02 | ☑ 2026-07-02 (`GQ2/CupProduct.lean`) |
| T-05 | I4: `maxProPQuotient` + pro-`p`-ness + universal property | ⭐⭐ | O | — | ☑ 2026-07-03 (`GQ2/MaxProP.lean`) |
| T-06 | U1: `Zhat` via `profiniteCompletion ℤ`; `x ^ᶻ γ`; `ω₂ : Zhat`; finite-quotient compat | ⭐⭐ | **F**→O | — | ☑ 2026-07-02 (`GQ2/Zhat.lean`) |
| T-07 | B7′: Hilbert symbol def + `ε`,`ω` + axiom (Serre CiA III§1.2 Thm 1) + stress tests | ⭐⭐ | O | — | ☑ 2026-07-03 (`GQ2/HilbertSymbol.lean`) |
| T-08 | B4: axiom `G_ℚ₂(2) ≅ profinitePresentation (Fin 3) {A²S⁴[S,Y]}` | ⭐⭐ | O | T-05 | ☑ 2026-07-03 (`GQ2/DyadicPresentation.lean`) |
| T-09 | B3a: `IsDemushkin` definition + invariants + stress tests | ⭐⭐⭐ | **F** | T-02, T-04 | ☑ 2026-07-03 (`GQ2/Demushkin.lean`) |
| T-10 | B3b: rank-3 `q=2` classification statement (optional if B3c ships) | ⭐⭐ | O | T-09 | ☑ 2026-07-04 (`demushkinQ` in `GQ2/Demushkin.lean`; no axiom — carried by B4, documented) |
| T-11 | B3c: canonical orientation — choose route (Labute Prop 6 vs cyclotomic interface) | ⭐⭐⭐ | **F** | T-08 (+T-09 for route i) | ☑ 2026-07-04 (`GQ2/Orientation.lean`, route (ii)) |
| T-12 | B8: Lemma 3.6 group-theoretic statement on `Δ = maxPro2(FreeProfinite (Fin 2))` | ⭐⭐ | O | T-05, T-06 | ☑ 2026-07-03 (`GQ2/PeripheralAction.lean`) |
| T-13 | I5: Kummer class cocycle `kˣ → H¹(k,𝔽₂)` | ⭐⭐ | O | T-02 | ☑ 2026-07-03 (`GQ2/Kummer.lean`) |
| T-14 | B6: local Tate duality axiom (μ-pairing, perfectness, per-`n` form) | ⭐⭐⭐ | **F** draft, O finish | T-02, T-04, T-15 | ☑ 2026-07-03 (`GQ2/TateDuality.lean`) |
| T-15 | I10: `μ_n` as finite discrete `G_ℚ₂`-module | ⭐⭐ | O | T-01 | ☑ 2026-07-03 (`GQ2/MuN.lean`) |
| T-16 | B7: Euler-characteristic axiom (`card H¹ = card H⁰ · card H² · 2^{v₂#M}` + finiteness) | ⭐ | O | T-02 | ☑ 2026-07-03 (`GQ2/EulerCharacteristic.lean`) |
| T-17 | B5: reciprocity bundle axiom (`rec`, `ν_ur`; norm-kernels, `ν_ur∘rec = −v₂`, `χ_cyc∘rec = (·)⁻¹`) | ⭐⭐⭐ | **F** | T-00 | ☑ 2026-07-03 (`GQ2/Reciprocity.lean`) |
| T-18 | B9: Kummer/cor/Evens-norm/transfer-form defs + eq. (111) axiom (deg ≤ 2) | ⭐⭐⭐ | **F** design, O finish | T-02, T-04, T-13 | ☑ 2026-07-03 (`GQ2/EvensKahn.lean`) |
| T-19 | Meta: `GQ2/Foundations/Axioms.lean` consolidation + `scripts/check_axioms.sh` guard | ⭐ | O | first axioms landed | ☑ 2026-07-03 |
| T-20 | Meta: human-review packet v2 (Lean names per B-leaf + deviations table) | ⭐ | O | statements frozen | ☑ 2026-07-04 (`docs/review-packet.md`) |
| T-21 | Γ_A literal (paper eq. (7) marked quotient; `ω₂`-relator words + bridges) + literal Thm 1.2 statement | ⭐⭐ | O | T-06 | ☑ 2026-07-02 (`GQ2/GammaA.lean`) |

## Per-ticket acceptance criteria

Common to all: `lake build GQ2` green; `#print axioms` of every *theorem* = standard three;
axioms only in `Axioms.lean`; docstrings carry citations + conventions.

- **T-00**: `docs/cft-survey.md` covering: finite-level reciprocity shape (blueprint §3, incl.
  `rec(F_k) = π_k N(lˣ)` normalization), status of Inf-Res PRs (#126, #68), what
  `IsNonarchimedeanLocalField.Unramified`/Frobenius API provides for T-17, anything reusable for
  cup products / H¹H² explicit cocycles.
- **T-01** ☑: no new structures; section conventions (documented in the module docstring:
  `[AddCommGroup M] [TopologicalSpace M] (+[DiscreteTopology M]) [DistribMulAction G M]
  [ContinuousSMul G M]`, `IsTopologicalAddGroup M` for general `M`); lemmas: stabilizers open
  (`isOpen_stabilizer`); action kernel open for finite `M` (`isOpen_iInf_stabilizer`); action
  factors through a finite quotient over profinite `G`
  (`exists_openNormalSubgroup_smul_eq_self`).  *Done (`GQ2/DiscreteModule.lean`).*
- **T-02** ☑: `Z¹ C¹ B¹ H¹ Z² C² B² H²` (`AddCommGroup` instances), `H⁰`;
  inflation/restriction; stress: trivial-action `H¹`-characterization; `B¹ ≤ Z¹` etc.;
  finite-`G` comparison deferred to T-03.
  *Done (`GQ2/Cohomology.lean`, namespace `GQ2.ContCoh`; all proofs at standard axioms).*
  Design decisions (differences from this sketch are deliberate):
  (i) flat file, not `GQ2/Foundations/` — the directory migration is T-19;
  (ii) cochains are plain functions, continuity lives in the subgroups; `Z¹ = C¹ ⊓ ker δ¹`,
  `Z² = C² ⊓ ker δ²` (closure properties free; mirrors Mathlib's `groupCohomology` shape for
  the T-03 comparison), `B² = δ¹(C¹)`; readable forms `mem_Z1_iff`/`mem_Z2_iff` (Serre I §2.2
  conventions); chain-complex sanity `δ¹∘δ⁰ = 0`, `δ²∘δ¹ = 0`;
  (iii) **one** functoriality workhorse: pullback along a compatible pair
  (`π : G →ₜ* Q`, `f : N →+ M` continuous, `f (π g • n) = g • f n`) giving
  `H0comap/H1comap/H2comap`; `res0/res1/res2` are the `(inclusion, id)` instance (Mathlib's
  `Subgroup.continuousSMul` makes `hcompat` `rfl`), inflation is the
  `DistribMulAction.compHom`-instance recipe (documented, no separate def — avoids two actions
  on one type);
  (iv) the trivial-action stress test is delivered wrapper-free as a trio
  (`mem_Z1_iff_of_trivial` + `B1_eq_bot_of_trivial` + `H1equivZ1OfTrivial : H¹ ≃+ Z¹`) rather
  than via `Multiplicative`-wrapped `ContinuousAddMonoidHom`;
  (v) defs are for arbitrary topological groups/modules — profiniteness and discreteness enter
  only in theorems (via `GQ2/DiscreteModule.lean`).
  Note for T-09: `IsDemushkin` can state its rank conditions via `Nat.card (H1 …) = 2 ^ n` and
  `Nat.card (H2 …) = 2`, avoiding `Module 𝔽₂` instances on the quotients entirely.
- **T-03** ☑: coefficient functoriality `mapCoeff0/1/2` (the `π = id` case of `Hicomap`),
  inflation `inf0/1/2` (the `f = id` case, actions agreeing through `π`), cocycle algebra
  (`Z1_apply_inv`).  Restriction (`res0/1/2`) already shipped with T-02.  *Done, extending
  `GQ2/Cohomology.lean`.*  **Deferred (documented in-file)**: the finite-`G` comparison to
  Mathlib's `groupCohomology.H1/H2` — Mathlib's is over `Rep k G` (`ModuleCat`, no topology), so
  a comparison needs a `Rep ℤ G` bridge; it is a **step-3 verification** concern, not needed to
  *state* any axiom, and the trivial-action characterization already validates `H¹`.
- **T-04** ☑: `cup11 : H¹ →+ H¹ →+ H²`, `cup02 : H⁰ →+ H² →+ H²`, `cup20 : H² →+ H⁰ →+ H²`
  relative to a `G`-equivariant pairing `μ : M →+ N →+ P` (coefficients `M, N` discrete → all
  cup cochains continuous, no continuity hypothesis on `μ`).  Bilinearity is by construction
  (`→+ →+`); `∪ 0 = 0` / `0 ∪ = 0` are `map_zero`; coefficient naturality
  `cup11_mapCoeff_target` (post-composing the pairing with a target `G`-map = `mapCoeff2` after
  cupping).  `cup11_mk_mk` computes the pairing on explicit cocycle classes (for B3).
  *Done (`GQ2/CupProduct.lean`); all at standard axioms.*
  Key proof facts: `(1,1)` is the hard one (full Leibniz descent in **both** variables, using the
  opposite factor's cocycle identity); `(0,2)`/`(2,0)` descend in one variable (the other is
  `H⁰`-invariant).  Assembly pattern that worked: bundle the bi-hom at the **cocycle** level
  (`AddMonoidHom.mk'` with function-level `..Fun_add_left/right` helpers), then descend the
  quotient slot with a single `QuotientAddGroup.lift` (+ `AddMonoidHom.flip` when the quotient is
  the second slot, as in `cup02`).  Lean gotchas: inline `simp` inside `Subtype.ext` is fragile —
  use a named `cupFun_add_*` helper; `n.2` for `n : ↥(H0 …)` is a *membership prop*, coerce it
  with `have hn : ∀ x, x • n.1 = n.1 := n.2` before `simp`; give each cup cochain a dedicated
  `continuous_*Fun` lemma so `mem_Z2` continuity unifies on the right head.
- **T-05** ☑: defs + `IsPGroup`-quotient lemma + universal property (`∀ pro-p P, Hom_cont(G,P) ≃
  Hom_cont(G(p),P)` or factorization form); stress: finite case; idempotence.
  *Done (`GQ2/MaxProP.lean`; every theorem `#print axioms` = standard three).*
  `IsProP p P := ∀ U : OpenNormalSubgroup P, IsPGroup p (P ⧸ U.toSubgroup)`;
  `proPKernel p G := ⨅ U : {U // IsPGroup p (G ⧸ U.toSubgroup)}, U.toSubgroup` (closed normal —
  `proPKernel_isClosed`/`proPKernel_normal`); `maxProPQuotient p G := profiniteQuotient (proPKernel
  p G) : ProfiniteGrp`; projection `maxProPMk`.
  * **`IsPGroup`-quotient / pro-`p`-ness**: `isProP_maxProPQuotient` (and `isProP_quotient_proPKernel`
    on the bare quotient type), via `isPGroup_quotient_of_proPKernel_le` — the compactness core:
    a directed family (`isPGroup_quotient_inf` closes `𝒰` under `⊓`) of clopen sets whose
    intersection lands in an open `Ŵ ≥ K` has a member `⊆ Ŵ`
    (`IsCompact.nonempty_iInter_of_directed_nonempty_isCompact_isClosed`), so `G ⧸ Ŵ` is a quotient
    of a `p`-group.
  * **Universal property**: `maxProPHomEquiv : Hom_cont(G(p), P) ≃ Hom_cont(G, P)` for pro-`p` `P`,
    resting on `proPKernel_le_ker` (each `f⁻¹ V` is an open normal subgroup with `G ⧸ f⁻¹V ↪ P ⧸ V`
    a `p`-group; open normals of the profinite `P` intersect in `1` via
    `eq_one_of_forall_mem_openNormalSubgroup`).
  * **Stress**: idempotence `proPKernel_eq_bot_of_isProP` / `maxProPMk_bijective_of_isProP` /
    `maxProPEquivSelf : ContinuousMulEquiv G (maxProPQuotient p G)` (pro-`p` ⇒ `G(p) ≅ G`, using
    compact→T2); `isProP_of_isPGroup`; finite example `proPKernel 2 (Multiplicative (ZMod 4)) = ⊥`.
  Consumers: **T-08** (`maxProPQuotient 2 AbsGalQ2`) and **T-12** (`maxProPQuotient 2
  (FreeProfiniteGroup (Fin 2))`) are unblocked.
- **T-06** ☑: `Zhat`, `zpowHat`, notation; naturality (`lift_unique`); `ω₂ : Zhat` with
  compatibility lemma `N ∣ M → omega2Exp M ≡ omega2Exp N [MOD N]`; headline:
  `f (x ^ᶻ ω₂) = powOmega2 (f x)` for `f` into finite groups. Ring structure explicitly out of
  scope.
  *Done (`GQ2/Zhat.lean`, all criteria met; `#print axioms` = standard three throughout).* Extras
  shipped: `completion_exists_level` (congruence-neighborhood basis for **any** profinite
  completion — reusable for T-12/T-21), `Zhat.ofInt`/`denseRange_ofInt`/`funext_ofInt` (density
  API), `Zhat.commute`, and `S₃` sanity evaluations tying `^ᶻ ω₂` to the App. A/B ledger.
  Design notes: `ω₂` built **componentwise** (Mathlib's `completion` is the literal subtype of
  compatible families, so `⟨fun H => mk (ofAdd (omega2Exp H.index)), …⟩` typechecks); classes in
  `ℤ/H` handled *without* classifying subgroups of `ℤ` (`orderOf_mk_ofAdd_one`: the generator's
  class has order = index); finite-quotient evaluation via `completion_exists_level` at level
  `H₀` + integer representative at level `lcm(index H₀, orderOf x)` — no unfolding of
  Mathlib's `lift`/`isLimitCone` internals needed. **T-21 and T-12's `P ^ᶻ ι(u)` are unblocked.**
- **T-07**: `hilbertSymbol`; `ε`, `ω`; axiom `B7'` with the exact CiA formula; theorems:
  symmetry, `(a,−a)=1`, square-class invariance in one slot.
  *Done (`GQ2/HilbertSymbol.lean`, namespace `GQ2.HilbertSymbol`; all proved parts `#print axioms` =
  standard three).* Design: `hilbertSymbol : ℚ₂ˣ → ℚ₂ˣ → ℤˣ` via solvability of `a X²+b Y²=Z²`, so
  symmetry, `(a,−a)=1` (witness `(1,1,0)`), and one-slot square-class invariance are **theorems from
  the def**, not the axiom. `ε, ω : ℤ₂ˣ → 𝔽₂` factor through `ℤ₂ → ℤ/8` (`PadicInt.toZModPow 3`) with
  the literal `(u−1)/2`, `(u²−1)/8` on `ZMod.val`; additivity on units (`ε_mul`/`ω_mul`) and the ε/ω
  residue tables are `decide`, and the values on `−1` exercise the real `ℤ₂ˣ` reduction (`map_neg`).
  Axiom `hilbertSymbol_dyadic` = Serre CiA III §1.2 Thm 1 (`p=2`), quantified over `a=2^α u`,
  `b=2^β v` (`unit2^α * unitCoe u`) — covers all of `ℚ₂ˣ` with no valuation-decomposition lemma; an
  `example` derives `(−1,−1)₂ = −1` from it as a sign-convention faithfulness check. *(Axiom since
  migrated to `Foundations/Axioms.lean` by T-19, together with the `example`.)*
- **T-08**: `r₀` via `FreeProfiniteGroup.of`; axiom; stress: image of the generators under a
  concrete finite marking (via `homEquiv` + `decide`-able finite group) behaves as expected.
  *Done (`GQ2/DyadicPresentation.lean` defs + stress tests, all `#print axioms` = standard three;
  axiom `Foundations.absGalQ2_maxProTwo_presentation` in `Foundations/Axioms.lean`).* Design:
  `d0Relator = A²S⁴[S,Y]` (`A,S,Y = of 0,1,2`, `[·,·] = commP` per `Words.lean`), `ω₂`-free so a
  bare word in `FreeProfiniteGroup (Fin 3)`; `D0 := profinitePresentation {d0Relator}`. Axiom (B4) =
  `Nonempty (ContinuousMulEquiv (maxProPQuotient 2 AbsGalQ2) D0)` — NSW (7.5.11)(ii) rank `N+2=3` +
  Labute Thm 8 at `d=1`; `[CompactSpace/TotallyDisconnectedSpace AbsGalQ2]` hyps mirror
  `main_presentation` (Mathlib gap). Stress test: the marking `A↦sr 0, S↦r 1, Y↦r 2` of
  `DihedralGroup 4` (order 8) classifies `homD4 : F₃ ⟶ D₄` with `homD4_toMonoidHom_of` (generator
  images) and `homD4_d0Relator` (relator dies, by `decide`); `d0Relator_quotientMk_eq_one` gives the
  relation in `D0`. Guard `EXPECTED_AXIOMS` bumped 7→8.
- **T-09** ☑: `IsDemushkin`; `demushkinRank`; stress tests per plan (incl. one *negative* example).
  *Done (`GQ2/Demushkin.lean`; every theorem `#print axioms` = standard three; no axioms — all
  constructions/proofs).*  Design decisions (deviations deliberate, documented in-module):
  (i) `IsDemushkin p G : Prop` structure = Serre GC I §4.5 / NSW Def. 3.9.9 clauses over
  `ContCoh` with literal `ZMod p` coefficients: `smul_trivial` (constrains the ambient action
  instance — T-02/T-13 pattern), `isProP` (T-05), `finiteH1`, `cardH2 : Nat.card H² = p`
  (dimension via `Nat.card`, per the T-02 note), and **two-sided** non-degeneracy of
  `trivialCupPairing` (= T-04 `cup11` w.r.t. `AddMonoidHom.mul`; two-sided because
  graded-commutativity of `cup11` is not formalized; `nondegen_left'/right'` consume the
  clauses with any triviality proof, by proof irrelevance);
  (ii) the "fin. gen." clause is omitted as redundant (⟺ `finiteH1` for pro-`p`, Burnside
  basis NSW 3.9.1 — not needed to *state* B-leaves);
  (iii) `demushkinRank p G := padicValNat p (Nat.card H¹)` with content lemmas
  `IsDemushkin.card_H1_eq_pow` (`#H¹ = p ^ rank`, via `H¹` `p`-torsion + `IsPGroup.iff_card`)
  and `demushkinRank_eq_of_card` (T-10's computation rule).
  Stress tests: **positive** `isDemushkin_cyclicTwo` + `demushkinRank_cyclicTwo` — `ℤ/2` (as
  `DihedralGroup 1`) is Demushkin of rank 1, with `H¹ ≃+ 𝔽₂` (`h1CyclicTwoEquiv`, the plan's
  "H¹ = homs" check in wrapper-free T-02 form), `H² ≃+ 𝔽₂` (`h2CyclicTwoEquiv`, via the
  evaluation functional `f ↦ f(1,1)+f(σ,σ)` that kills coboundaries), and the generator's cup
  square = the product cocycle `(g,h) ↦ c₀(g)c₀(h)` (extension class of `ℤ/4`), *definitionally*
  (`cup_generator := rfl`) and detected `≠ 0` by the functional; **negative**
  `not_isDemushkin_punit` — the trivial group (free pro-`p` of rank 0) has `H² = 0` (`#H² = 1 ≠ p`),
  the plan's "`H² = 0`, pick cheap ones".
  **Gotcha for downstream users**: do NOT act on `ZMod`-coefficients with a
  `Multiplicative`-wrapped group — Mathlib's `Multiplicative.smul` transfer instance makes
  `g • m` mean base-multiplication and clashes with any trivial-action instance (hence
  `DihedralGroup 1`, not `Multiplicative (ZMod 2)`, in the stress test).
- **T-10** ☑: *(Delivered as invariant + documentation, per the plan's explicit fallback — NO new
  axiom.)*  `topAbelianization G := G ⧸ closure ⁅G,G⁆` and **`demushkinQ G`** := number of torsion
  elements of `G^{ab}` (= Labute's `q` when `G^{ab} ≅ ℤ_p^{n−1} × ℤ/q`, `q ≠ 0`; junk otherwise —
  the `q = 0` reading is not encoded, documented).  Stress: `demushkinQ_cyclicTwo = 2` (matching
  `q(⟨x | x²⟩) = 2`; proved via `commutator = ⊥` by `decide` + discrete-closure + `quotientBot`,
  std-3).  **Why no classification axiom**: stating abstract rank-3 `q=2` classification honestly
  requires Labute's *canonical*-character characterization (Prop. 6 = route (i) of T-11, deferred);
  an axiom quantified over an arbitrary character with the right image would be a *different and
  possibly false* statement (risk rule #2).  At the field level the used instance **is** B4
  (`absGalQ2_maxProTwo_presentation`), normalized by B3c.  Documented in `GQ2/Demushkin.lean`
  §"The `q`-invariant" and in the `Foundations/Axioms.lean` header.
- **T-11** ☑: **route (ii) — cyclotomic interface** (per the plan's recommendation; route (i),
  Labute Prop. 6's abstract dualizing characterization, deliberately deferred — deviation flagged
  in-module and at the axiom).
  *Done (`GQ2/Orientation.lean` + named generators `d0A/d0S/d0Y` + `d0_relation` added to
  `GQ2/DyadicPresentation.lean`; axiom `GQ2.dyadicOrientation : DyadicOrientation` in
  `Foundations/Axioms.lean`, census 9→10; build + guard green).*
  `DyadicOrientation` bundles: a **B4 isomorphism** `equiv : G_{ℚ₂}(2) ≅ D₀`; the **descent**
  `chiTwo` of `chiCyc` through `maxProPMk` (continuous, `chiTwo_factors`; carried as data to avoid
  formalizing `IsProP 2 ℤ₂ˣ` — an O-finish refinement: with it, descent follows from T-05's
  `proPKernel_le_ker`); **surjectivity** (= the Thm 4(2) image invariant `{±1} × U₂⁽²⁾ = ℤ₂ˣ`,
  the local B2); and the **values** `χ(A) = −1`, `χ(S) = 1`, `χ(Y) = (−3)⁻¹` under `equiv.symm`
  (Labute Thm 4 case (2) at `f = 2` — the paper's `χ_D`-row of eq. (13); `−3` quantified via its
  defining property, B5-stress-test style).  Stress (bundle-parametrized, axiom-free):
  `orientation_values_consistent` (`(−1)²·1⁴·[χS,χY] = 1` — the values respect the Demushkin
  relation; cross-checked by `orientation_relator_maps_to_one` via `d0_relation`),
  `chiCyc_eq_neg_one_of_lift_A` / `chiCyc_eq_inv_neg_three_of_lift_Y` (full-group readings of
  (13)) with `exists_lift_A` non-vacuity; `map_commP_eq_one` (commutators die in abelian targets).
  Consistency web: the values match the B5 stress tests (`chiCyc_recip_neg4 = −1`,
  `chiCyc_recip_neg3 = (−3)⁻¹` — eq. (13)'s two independent derivations agree).
- **T-12**: statement with `c_P, c_T, c_C` conjugators and `P ^ᶻ ι(u)`; documented deviation note
  (axiom = Lemma 3.6's conclusion; literature proof = Stix §3.3+Def 37).
  *Done (`GQ2/PeripheralAction.lean` defs + bundle; axiom `peripheralCyclotomicAction` in
  `Foundations/Axioms.lean`).* Design: `Delta = maxProPQuotient 2 (FreeProfiniteGroup (Fin 2))`
  (abbrev, so `^ᶻ`/group instances resolve), `deltaP/T/C` (`C = (PT)⁻¹`) via `maxProPMk`. **Bundle**
  `PeripheralCyclotomicAction` (mirrors B5/B6): carries the exponent embedding `ι : ℤ₂ˣ → Zhat` as
  *data* — pinned `hι_cont` + `hι_one : ι 1 = omega2` (the `u=1` exponent is T-06's idempotent;
  `P ^ᶻ ω₂ = P` on pro-2) — plus `aut : ℤ₂ˣ → ContinuousMulEquiv Δ Δ`, `cP/cT/cC`, and
  `hP/hT/hC : aut u P = conjP (P ^ᶻ ι u) (cP u)` (paper `x^c = c⁻¹xc`). Faithfulness deviation
  (π₁ absent from Mathlib; ι's full pin = ring structure of Ẑ, out of scope) documented in-module for
  reviewers. Also renamed `DyadicPresentation`'s `DihedralGroup 4` local instances (explicit names)
  to avoid an auto-name clash with `Zhat`'s `DihedralGroup 3` instances now that both reach
  `Axioms.lean`. Guard `EXPECTED_AXIOMS` bumped 8→9.
- **T-13** ☑: `kummerClass : kˣ → H¹(G_k, 𝔽₂)` as the class of the explicit continuous 1-cocycle
  `κ_a(g) = [g·√a = −√a]` (`= 0/1 ∈ ZMod 2`), over Mathlib's `Field.absoluteGaloisGroup` (spelled
  `GaloisGroup k := k̄ ≃ₐ[k] k̄`, defeq `AbsGalQ2` for `k = ℚ₂`; `example`s certify).  Stress tests
  (all at standard axioms, no new `axiom`s): `kummerCocycle_isHom` (continuous homomorphism — the
  1-cocycle condition under the trivial `𝔽₂`-action, `ContCoh.mem_Z1_iff_of_trivial`),
  `kummerClass_mul` (`[ab]=[a]+[b]`), `kummerClass_one`, and `kummerClass_eq_zero_iff`
  (`[a]=0 ⟺ IsSquare a` — injectivity of `kˣ/(kˣ)² ↪ H¹`).
  *Done (`GQ2/Kummer.lean`, namespace `GQ2.Kummer`).* Design notes:
  (i) coefficients `𝔽₂ := ZMod 2` with the **trivial** action (`±1 ∈ k` fixed), supplied as a plain
  `DistribMulAction (GaloisGroup k) (ZMod 2)` instance (no conflict — no other action of an absolute
  Galois group on `ZMod 2` exists);
  (ii) generality: works for any `[CharZero K]` field (covers `ℚ₂` and all its finite extensions —
  B9's setting; char-0 gives both char `≠ 2` and `IsGalois k k̄` for free); most lemmas `omit
  [CharZero K]`;
  (iii) continuity is `IsLocallyConstant` from the stabilizer of `√a` being (cl)open in the Krull
  topology (`stabilizer_isOpen_of_isIntegral`); the `= 0 ⟺ square` direction is the fixed-field
  theorem `InfiniteGalois.mem_range_algebraMap_iff_fixed`;
  (iv) root-independence (`κ` for `√a` and `−√a` coincide) makes `kummerClass` well-defined and
  drives `kummerClass_mul` (root `√a·√b` for `ab`).  **Unblocks T-18 (B9 Kummer/SW leg).**
- **T-14** ☑: per-`n` duality; Pontryagin-dual encoding decided + documented; μ-coefficient `H²`
  target with bundled `inv`.
  *Done (`GQ2/TateDuality.lean` + axiom `GQ2.tateDuality (n) [NeZero n] : TateDuality n` in
  `Foundations/Axioms.lean`, census 5→6; full build + guard green; all theorems std-3, stress
  tests bundle-parametrized hence axiom-free).*  🔴 decisions resolved (documented in-module):
  **per-`n`** form (not the `μ = ⋃μₙ`/`ℚ⧸ℤ` colimit — suffices for the paper's `n = 2`; cross-`n`
  compat of `inv` NOT asserted, flagged); **Pontryagin dual = `⋯ →+ ZMod n`** (for `n`-torsion
  finite `A`, `Hom(A, ℚ/ℤ) ≅ Hom(A, ℤ/n)` — no `AddCircle`); dual module **`MuDual n M`** = `def`
  synonym of `M →+ MuN n` with the conjugation action `(g•φ)(m) = g•φ(g⁻¹•m)` (a `def`, NOT
  `abbrev`: Mathlib has a codomain-only `DistribMulAction M (A →+ B)` instance — diamond);
  continuity via `continuousSMul_iff_stabilizer_isOpen` + T-01's `isOpen_iInf_stabilizer` (joint
  action kernel on `M` and `μₙ` is open and fixes every `φ`); pairing = literal evaluation
  (`muDualPairing := AddMonoidHom.id` under the synonym), equivariance is `inv_smul_smul`.
  `TateDuality n` bundles `inv : H2(μₙ) ≃+ ZMod n` + perfectness in the three degree pairs —
  exactly T-04's `cup02/cup11/cup20` shapes with `M′` left — as bijectivity of
  `x ↦ inv ∘ (x ∪ ·)` onto `H^{2−i}(M) →+ ZMod n`; modules quantified over `Type` (Type 0,
  Reconstruction precedent).  **Deviations flagged**: single currying per degree pair (opposite
  follows by counting for finite modules); `inv` unnormalized (existence-form; the explicit
  `n = 2` cup values enter via B7′, not `inv`).  Stress tests: `nsmul_muN_eq_zero` (`μₙ` is
  `n`-torsion — feeds `μₙ` itself to the duality), `TateDuality.card_H2_muN` (`#H²(μₙ) = n`),
  `card_H0/H1/H2_dual` (cardinality forms), `exists_cup_ne_zero_of_ne_zero` (the dimension-count
  workhorse), self-instantiation at `M = μₙ`.  Lean gotchas recorded: the `ext` tactic recurses
  through `Additive`/`Subtype` on `μₙ`-valued homs (use targeted `DFunLike.ext`); the synonym's
  own `FunLike` head needs its own `zero_apply`/`add_apply` simp lemmas; section-variable
  bundles used only in proofs need `include D`.
- **T-15** ☑: `μ_n` as a legal `ContCoh` coefficient over `AbsGalQ2`.  *Done (`GQ2/MuN.lean`; every
  proof `#print axioms` = standard three).*  Deliverables: `galRootsOfUnity`
  (`MulDistribMulAction (L ≃ₐ[K] L) (rootsOfUnity n L)`, by restricting the units action — Mathlib
  has the `Lˣ` action but **not** its restriction to `μ_n`) and `galRootsOfUnityAdd` (the same action
  through `Additive`, the project's additive discrete-module convention); then over `ℚ₂`,
  `MuN n := Additive (rootsOfUnity n ℚ̄₂)` with `DistribMulAction`/`ContinuousSMul` over `AbsGalQ2`.
  **Design decisions** (for the T-14 consumer and review):
  (i) `AbsGalQ2 = Field.absoluteGaloisGroup ℚ_[2]` is an opaque `def` (semireducible), so the
  `AlgEquiv` action/topology instances are transported to it by `inferInstanceAs` across the
  definitional equality `AbsGalQ2 ≡ (ℚ̄₂ ≃ₐ[ℚ₂] ℚ̄₂)`;
  (ii) **topology is inherited, not imposed** — `ℚ̄₂` carries the valued topology from
  ClassFieldTheory's `PadicAlgCl`, so `μ_n` gets the subspace topology, which is *provably discrete*
  (`Finite.instDiscreteTopology`: finite subset of a `T₁` space) — imposing `⊥` would diamond;
  (iii) continuity via `continuousSMul_iff_stabilizer_isOpen` + `stabilizer_isOpen_of_isIntegral`
  (Krull-open stabilizers), bridged by `stabilizer_additive_eq_field` (stabilizer of `x : μ_n` =
  stabilizer of the underlying field element).  Stress tests: `H⁰/H¹/H²(G_ℚ₂, μ_n)` all form (the
  faithfulness check), `Finite`, `DiscreteTopology`, `Nat.card (MuN n) = n` (⇒ `μ_n ≅ ℤ/n`), and
  action–field coherence.  **T-14 is unblocked.**
- **T-17** ☑: the three-clause bundle (a)(b)(c) from the plan; every clause cross-referenced to
  paper eq. (13)/Lemma 3.5; convention table in docstring.
  *Done (`GQ2/Reciprocity.lean`; `#print axioms` of every stress test = standard three).* The
  bundle is a `structure LocalReciprocity` (fields `recip`/`nu_ur` + clauses `norm_reciprocity`
  (a), `nu_ur_recip` (b), `chiCyc_recip_unit`/`chiCyc_recip_uniformizer` (c)) with `axiom
  localReciprocity : LocalReciprocity`. `χ_cyc = chiCycAb` is **Mathlib's own** `cyclotomicCharacter
  (AlgClosure ℚ₂) 2` factored through the topological abelianization `AbsGalQ2ab =
  Field.absoluteGaloisGroupAbelianization ℚ₂`; `rec` lands there. **Stress tests recompute paper
  eq. (13) from the bundle**: `nu_ur_recip_{uniformizer,neg4,neg3}` = the `ν_ur(ā,s̄,ȳ)=(−2,1,0)`
  row (`s̄=rec(2)⁻¹`); `chiCyc_recip_neg4` (`χ_D(ā)=−1`, flagship orientation check via
  `−4=(−1)·2²`) and `chiCyc_recip_neg3` (`χ_D(ȳ)=(−3)⁻¹`) = the orientation row;
  `abelianized_relator` = the abelianized relation `ā²s̄⁴=rec(1)=1`.
  Key design points (for review): **(i) soundness trap** — `ν_ur` targets `Multiplicative ℤ₂`,
  **not** `ℤ`: a continuous hom from compact `G^{ab}` to discrete `ℤ` is forced trivial, so the
  `ℤ`-target axiom would be *inconsistent* (documented in-file, cf. the earlier `Nat.card` bug).
  **(ii) instance diamond** — `AbsGalQ2 = Field.absoluteGaloisGroup ℚ₂` (a `def`) and Mathlib's raw
  `Gal(K̄/ℚ₂) = K̄ ≃ₐ[ℚ₂] K̄` carry *different* `Group` instances; `chiCyc`/`restrictHom` are built
  on the raw type and ascribed to the `AbsGalQ2` domain (defeq) to keep `commutator`/abelianization
  on one instance path. **(iii) deviations flagged**: `rec` injectivity omitted (follows from (a) in
  the limit `⋂_L N_{L/ℚ₂}Lˣ = 1`); axiom since migrated to `Foundations/Axioms.lean` by T-19
  (stress tests stayed — they are bundle-parametrized and axiom-free).
  Clause (a) is stated faithfully over finite abelian layers `L/ℚ₂`
  (`normSubgroup L` = image of `Algebra.norm`; `restrictAb L` = restriction factored through
  `G^{ab}`), aligning with the ClassFieldTheory finite-level `Gal(L/ℚ₂) ≅ ℚ₂ˣ/N Lˣ` shape.
- **T-18** ☑: defs as in plan; axiom = eq. (111) scoped to the forms used in Lemma 6.16; deviation
  note (truncation to deg ≤ 2, concrete diagonal representatives).
  *Done (`GQ2/EvensKahn.lean` + axiom `GQ2.evensKahn_dyadic` in `Foundations/Axioms.lean`, census
  6→7; full build + guard green; every theorem std-3 — all constructions proved, nothing bundled
  into the axiom beyond (111) itself).*
  **Definitions (fully proved, general `G` ⊇ index-2 open `U`, `s ∉ U`)**: `evensAux` = the (97)
  Shapiro component `b(γ)₁` (with the simplification `b(γ)_s = b(s⁻¹γ)₁` = `bS`, recorded);
  uniform expansion rules `evensAux_mul`/`bS_mul` (`b₁(xy) = b₁x + D₀(x;y)`, four subtype-mul
  cases via `Subtype.ext + group`); `corFun = b₁ + b_s` (deg-1 corestriction; hom by the
  cross-term recombination, `corFun_mem_Z1`, class `corH1`/`corH1Z`); **`evensNormFun` = the
  paper's two-point graph cocycle (98)**, with `evensNormFun_mem_Z2` — the cocycle identity by
  pairwise char-2 cancellation (`D₀(h;k)·D₁(h;k) = b₁(k)b_s(k)`; the two `p=1` cases need
  `linear_combination CharTwo.add_self_eq_zero _`, plain `ring` can't kill `2x`), continuity via
  `IsLocallyConstant` on the clopen pieces (`Continuous.if` + `IsClopen.frontier_eq`); class
  `evensNormH2`/`evensNormH2Z` — the **index-two Evens norm as a definition** (Lemma 6.13/(99)),
  exactly per plan.  Convention anchor: hand-checked `C₄ ⊇ C₂` model in the docstring.
  `mul_mem_iff_of_index_two` (+`notMem_mul_mem` etc.) proved from `Subgroup.index_eq_two_iff'`.
  **Subgroup Kummer (T-13 relativized)**: `kummerZ1On` — `[a] ∈ Z¹(G_L, 𝔽₂)` for `a = β²` fixed
  by `N` (`two_values_of_fixed`, `ne_neg_of_ne_zero`, `kummerCocycleFun_hom_on`);
  `stabilizer_fixes_linear` feeds `a = u + vδ` with `N = stab(δ)`.
  **Axiom** `evensKahn_dyadic`: for `k = ℚ₂`, `L = k(δ)` (`δ² = d`, `stab(δ)` of index 2),
  `a = u + vδ`, `n = u² − dv²`: the degree-1 and degree-2 components of (111) at the paper's
  diagonalizations `Tr⟨a⟩ ≃ ⟨2u, 2dn/u⟩`, `Tr⟨1⟩ ≃ ⟨2, 2d⟩`, with `w₁⟨x,y⟩ = [x]+[y]`,
  `w₂⟨x,y⟩ = [x]∪[y]` (`trivialCupPairing`, T-09).  **Deviations flagged** (in-module + axiom
  docstring): deg-≤2 truncation; concrete diagonal representatives (no `QuadraticForm`
  machinery — plan's recommendation; Delzant well-definedness absorbed into scoping); deg-1
  component ⟺ the classical `cor[a] = [N_{L/k}a]`.  **O-finish follow-ups** (not blocking):
  finite-level stress test of the Evens cocycle (e.g. `C₄ ⊇ C₂` in Lean, needs an `H²(C₄)`
  computation like T-09's); Evens Thm 1 `N(1+x)` expansion shape; `cor∘res`/projection-formula
  sanities.
- **T-19** ☑: *(Done: `GQ2/Foundations/Axioms.lean` + `scripts/check_axioms.sh`; full build green;
  all five fully-qualified axiom names preserved.)*
  **Layout**: `Axioms.lean` is the single file allowed to declare `axiom`s — currently five
  (B1 `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`, B2
  `Foundations.cyclotomicCharacter_two_surjective`, B5 `GQ2.localReciprocity`, B7
  `Foundations.absGalQ2_localEulerCharacteristic`, B7′ `HilbertSymbol.hilbertSymbol_dyadic`) —
  with docstrings/citations moved verbatim and the original namespaces reproduced, so **no
  consumer changes name**.  Import layering: definition files (`HilbertSymbol`, `Reciprocity`,
  `Cohomology`, `Statement`) sit *below* `Axioms.lean`; consumers sit above it
  (`EulerCharacteristic.lean` keeps B7's conventions docstring + the derived `finite_H1`/`card_H1`
  suite and now imports `Foundations.Axioms`; `Reciprocity.lean`'s stress tests are
  bundle-parametrized, hence axiom-free and unmoved; B7′'s faithfulness `example` moved next to
  its axiom).  `GQ2/Foundations.lean` remains as a re-export shim, its stale
  "cannot be written today" prose replaced by the refreshed review guide in `Axioms.lean`
  (B5/B7/B7′ *are* now faithfully stated; remaining doc-only leaves: B3-classification/B4/B6/B8/B9
  with their tickets).  Axiom-profile spot checks: `Foundations.card_H1` = std-3 + exactly its own
  B7 axiom; `Foundations.finite_H0` and the Reciprocity stress tests = std-3 only.
  **Guard** (`scripts/check_axioms.sh`, comment-aware — a nesting-correct `/- … -/`/`--` stripper,
  so prose mentioning "axiom"/"sorry" doesn't trip it; negative-tested against a planted
  axiom/sorry/native_decide file): (1) `axiom` only in `Foundations/Axioms.lean`; (2) `sorry`
  allowlist = the three intentional leaves (`Reconstruction`/`Statement`/`GammaA`); (3) axiom
  census = `EXPECTED_AXIOMS` (bump in the same commit that lands a new B-leaf); (4) no
  `native_decide` anywhere.  Wave-4 axiom tickets (T-08, T-12, T-14, T-18) should declare their
  axioms **directly in `Foundations/Axioms.lean`** and bump the census.
- **T-20** ☑: *Done (`docs/review-packet.md`).*  Contents: mechanical-verification instructions
  (build + `check_axioms.sh` + `#print axioms`); the **Lean-name table** for all ten axioms
  (B1, B2, B3c, B4, B5, B6, B7, B7′, B8, B9) with one-line statements, key citations, and
  defs-file pointers; the supporting-definitions checklist (ContCoh/cups, maxProP, D₀, Kummer,
  μₙ/duals, cor/Evens norm, Ẑ/ω₂/Γ_A); the **consolidated deviations table** (B3b no-axiom
  decision, B3c route (ii) + descent-as-data, B5 minimality + ℤ₂-target soundness, B6 per-`n`
  encoding choices, B7 faithful redundancy, B8 no-π₁ + ι-as-data, B9 deg-≤2 + concrete
  diagonals, ContCoh-vs-Mathlib note); the three-`sorry` inventory with status; and the
  machine-verified consistency cross-checks (B3c↔B5 eq.-(13) agreement, relator checks, B7′
  anchor value).  Also this commit: **all personal reviewer-name references removed** from the
  repository prose (docs + Lean docstrings) — the packet is audience-neutral; git dependency
  URLs/slugs retained for reproducibility.  `literature-axioms.md` gains a pointer to the
  packet (its citations remain the authoritative literature reference).
- **T-21** ☑: the relator words (`τ^σ τ⁻²` and `h₀u₁⁻¹x₁^σc₀`, ledger (1)–(3)) with `^ᶻ ω₂`;
  `GammaA : ProfiniteGrp`; statement
  `theorem main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)` (sorried,
  tied into `Statement.lean`); stress: image of each word under a finite marking = the `Marking`
  word (connects to `Words.lean` via T-06 headline lemma — this is the key faithfulness check).
  *Done (`GQ2/GammaA.lean`; proved parts `#print axioms` = standard three).*
  **Faithfulness correction vs this ticket's sketch**: the paper's `Γ_A` (§2.1, eq. (7)) is the
  **marked quotient** `F₄ ⧸ N_A`, `N_A = ⋂ ker(admissible finite quotients)` — the pro-2
  condition on `⟨⟨x₀,x₁⟩⟩` is part of the presentation data, so `Γ_A` is *not* the bare
  two-relator `profinitePresentation`. We formalized eq. (7) verbatim (`IsAdmissibleU` over open
  normal subgroups + `NA` + `GammaA := profiniteQuotient NA`), with `NA_le_ker` certifying the
  encoding captures the paper's full class `Q_A` (arbitrary finite targets). The `^ᶻ ω₂`-relator
  words are provided on any profinite marking (`Marking.sigma2Hat … wildRelator`) with bridges
  `map_tameRelator_eq_one_iff` / `map_wildRelator_eq_one_iff`: killing the profinite words in a
  finite quotient ⟺ `Words.lean`'s `TameRel`/`WildRel` — so admissibility's two readings agree.
  Bonus: `univMarking_map_toHom` (universal property round-trip), `gammaA_surjective_s3`
  (`Γ_A ↠ S₃` via the App-B marking — nonvacuity), `FreeProfiniteGroup.homEquiv_symm_of`.
  Step-2 consumers: Prop. 2.3 should combine `NA_le_ker`, the bridges, and `Subdirect.lean`.
