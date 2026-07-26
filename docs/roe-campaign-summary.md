# The Γ_R campaign: what was proved, and on what

*Written 2026-07-25, at the close of the R-campaign's mathematics. Audience: a reader who
knows the June formalization of the paper's candidate Γ_A. Companion documents: the plan and
its status block at [`orchestration/roe-verification-plan.md`](orchestration/roe-verification-plan.md),
the live board at [`orchestration/roe-tickets.md`](orchestration/roe-tickets.md), the source
note at [`../paper/roe-presentation-verification.tex`](../paper/roe-presentation-verification.tex).
Tags in ⟦…⟧ are that note's labels; `file:line` references are to this repository.*

## 1. The question

The paper presents `G_{ℚ₂}` as Γ_A: generators `σ, τ, x₀, x₁`, the normal closure of `x₀, x₁`
required to be pro-2, and two relators `τ^σ = τ²` and `h₀u₁⁻¹x₁^σc₀ = 1`. Months earlier a
*different* 4-generator 2-relator candidate had been found by machine search and checked
against LMFDB finite-quotient counts. Call it Γ_R ⟦def:GammaR⟧: same generators, same pro-2
condition, same tame relator, but the wild relator

```
r_R = (x₀^σ)⁻¹ · a · x₁² · c,    a = (x₀⁻³τ)^ω₂,   c = [x₁, x₁^{σ₂}],   σ₂ = σ^{ω₂}
```

⟦eq:defwords⟧⟦eq:relators⟧, in Lean `GQ2.Marking.wildValueR` (`GQ2/Roe/Words.lean:94`),
`WildRelR` (`:98`), `GQ2.admissibleCountR` (`:118`), `GQ2.GammaR`
(`GQ2/Roe/GammaR.lean:196`). Is Γ_R also `G_{ℚ₂}`?

The note answers yes, and does so as a **replacement theorem** ⟦thm:main⟧: the paper's
finite-target induction is reused *unchanged*, because Cor. 6.19 of the paper isolates
exactly four candidate-specific inputs ⟦prop:interface⟧ — the tame quotient with its
unramified marking, the fully marked maximal pro-2 quotient, deformation duality for every
elementary characteristic-2 coefficient module, and the quadratic Gauss signs. A pre-campaign
survey confirmed the claim mechanically: the §§7–10 induction engine contains **zero**
references to the wild word.

Two facts frame everything below. First, Γ_R ≅ Γ_A only *a posteriori*: no Nielsen or Tietze
transformation between the two presentations is known, and the reuse happens at the
linearized/cochain level, where the new Fox row is the old matrix with its two wild columns
interchanged. Second, the Roe word is *strictly simpler* at every word-level seam — no
`h₀`/`d₀`/`z₀`/`g₀`, a bare `x₁²` — and this repeatedly bought weaker hypotheses than Γ_A
needed (the split Fox row needs no `hU`; the ramified κ⁰ evaluation lands the unconditional
Wall shape on the nose, with no analogue of Γ_A's `htauf`/`hqg0`/`htau`).

## 2. The one genuinely new mathematics: the marked pro-2 quotient

For Γ_A the maximal pro-2 quotient *is* the boundary group Π, generator for generator
(Prop. 3.10). For Γ_R it is a **differently presented** group `D_R` ⟦lem:pro2word⟧⟦eq:DR⟧,
and identifying it with `G_{ℚ₂}(2)` *as a marked group* is the note's §3 — the part the
original formalization had bought, for `G_{ℚ₂}(2)`, as axiom B3c.

**Route N was eliminated by a theorem, not by a failed search.** The R2 spike
([`orchestration/roe-r2-spike.md`](orchestration/roe-r2-spike.md)) looked for explicit words
realizing `D_R ⇄ D₀` and instead proved none can exist: any word-epimorphism is automatically
an isomorphism by the five-term exact sequence; isomorphisms intertwine the canonical
orientations; and the resulting norm condition in `ℚ(X)` (discriminant −59) is unsatisfiable,
since `η` has norm −1/27 while all word-values land in `±4^ℤ`. The same spike independently
re-derived the note's §3.2 numerics (`X ≡ 5`, `S ≡ 13 mod 16`), which later tickets used as
cross-checks. Gate G1 therefore selected **Route L**, the note's own route.

Route L has four pieces, all now Lean theorems:

| ⟦tag⟧ | content | Lean |
|---|---|---|
| ⟦lem:pro2word⟧ | `maxPro2(Γ_R) ≅ D_R`, unconditional | `GQ2.Roe.maxPro2Bridge`, `GQ2/Roe/MaxPro2Bridge.lean:426` |
| ⟦lem:initial⟧ | `D_R` is Demushkin: rank 3, `q = 2`, cup–Bockstein Gram `[[0,1,0],[1,0,0],[0,0,1]]` nonsingular | `isDemushkin_DR` `GQ2/Roe/DRDemushkin.lean:473`, `demushkinRank_DR` `:506`, `demushkinQ_DR` `:513` |
| ⟦prop:orientation⟧ | the canonical orientation `χ_R`, its uniqueness, and `im χ_R = {±1}×(1+4ℤ₂)` | `GQ2.Roe.chiR` `GQ2/Roe/ChiR.lean:120`, `isLabuteOrientation_chiR` `:134` |
| ⟦prop:markedpro2⟧ | the ν-marked identification `G_{ℚ₂}(2) ≅ D_R` | `markedPro2_R`, `GQ2/Roe/MarkedPro2.lean:159` |

Three implementation choices are worth a reviewer's attention.

*Demushkin-ness took the cochain/cup route, not the note's Zassenhaus phrasing.* The note
argues via `D₂/D₃` initial forms; no Zassenhaus filtration is formalized. Instead a Γ_R-side
word-cohomology bridge (`GQ2/Roe/DRWordCoh.lean`, 936 lines) was built, and a single bilinear
form `drCup_obs`, evaluated by a 64-case `decide`, subsumes all nine Gram entries, the `H²`
cardinality, and both nondegeneracy clauses. This is the abstract `IsDemushkin` predicate's
first load-bearing use in the repository.

*The orientation calculus was the one new coefficient system.* Crossed derivations valued in
`ℤ₂(χ) ⋊ ℤ₂ˣ` (`GQ2/Roe/CrossedDerivation.lean`) yield the note's four equations
⟦eq:charrelation⟧⟦eq:Cx⟧⟦eq:Cs⟧⟦eq:Cy⟧; the branch `Y = X²` is excluded; the cubic
`X³ + 2X² + 1` is solved by Hensel's lemma (`GQ2/Roe/OrientationRoot.lean`, `rootX`),
reproducing `X ≡ 5`, `S ≡ 13 mod 16` ⟦eq:orientationvalues⟧. Surjectivity of `χ_R` came out
more cheaply than planned — Burnside/Frattini plus a mod-8 square argument, no `zpowZtwo`
closure needed. The Gröbner-certificate technique (sympy cofactors fed to
`linear_combination` over the unit ideal) kept all of this on the standard three axioms.

*The classification step is a hypothesis, not an axiom.* ⟦cor:abstractD0⟧ — Labute's 1967
classification, at the single instance rank 3 / `q = 2` / prescribed orientation image — was
proposed as a tenth literature axiom and **declined by the owner on 2026-07-25**. It is
carried instead as an explicit binder `GQ2.Roe.BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:137`)
so that the conditionality is visible in the statement of every theorem that uses it. All
four of its antecedents are theorems; only the classification implication is open. R15's
marked-matching assembly then improved on the plan: `(u, b)` is solved by a coordinate system
plus a mod-2 generation engine and τ₂-parity mod 16, and orientation functoriality is proved
for *every* continuous isomorphism (`isLabuteOrientation_comp_iso`) via three master crossed
derivations `D₀ → ℤ₂(χ₀) ⋊ ℤ₂ˣ` and an invertible 3×3 evaluation matrix.

## 3. The word-level layer, and the interface refactor

The remaining three candidate-specific inputs were re-verified along the note's §§4–6, each
one a small new calculation feeding machinery that was already abstract in the word:
the evaluated Fox row `L_w = P·b + (P + S⁻¹)·c` ⟦prop:jacobian⟧ (`GQ2/Roe/WildRow.lean`),
simple normal forms ⟦lem:normalforms⟧, the trivial-coefficient collapse ⟦lem:trivial⟧, the
Stokes endpoint ⟦lem:stokes⟧, the mixed Hessian and the `1 + U + U⁻¹` pairing
⟦prop:hessian⟧⟦eq:pairingoperator⟧, candidate deformation duality ⟦prop:duality⟧
(`GQ2.FoxH.prop_5_15_R`, `GQ2/Roe/DualityAssembly.lean:485`), the base word expansion
⟦prop:quadratic⟧ (`GQ2.QZeroR`, `GQ2/Roe/Gauss.lean:71`) and the Gauss signs ⟦cor:gauss⟧.

The R20 recon found that the dévissage argument states over a *fixed* definitional spine
(`wildValue → d1Fun → Z1w → H*w → mixedB`), so there is no drop-in `mixedB_R`. Rather than
generalize frozen Γ_A code overnight, the campaign **cloned** that tree onto the r_R spine
(~2.3 k lines, proofs porting verbatim, new files only). That is the single largest source of
the campaign's line-count overshoot, and it leaves a standing maintenance note: future Γ_A
dévissage edits must be hand-mirrored into `GQ2/Roe/Devissage/` and its two umbrellas.

The one place the campaign deliberately did touch frozen code is the idea worth keeping.
`GQ2.SourceData` (`GQ2/SourceData.lean:75`) turns the note's ⟦prop:interface⟧ — the paper's
Cor. 6.19, "the induction depends on no further feature of the source word" — into a
first-class Lean structure: carrier, boundary map, tame and pro-2 coordinates with their
compatibility and kernel conditions, and the seven supply obligations. `thm_4_2` and
`prop_8_9` were then generalized to `thm_4_2_of_sources` (`GQ2/ThmFourTwo.lean:386`) and
`prop_8_9_of_sources`, so the finite-target machine is proved once over an abstract source and
instantiated twice. The refactor was regression-gated and passed all four gates: Γ_A capstone
statement diffs empty, axiom prints identical pre/post, full build green. It also *shrank* its
own blast radius relative to the design — `BoundaryFrame.lean` and `SectionNine/Induction.lean`
were left untouched, their generic lanes replayed inside `SourceData.lean`.

Instantiating that interface at Γ_R took a supply wave of ~5 k lines of ports (R31b–R31g:
`WordCohBridgeR`, `CorrectionR`, `WordCoh2R`, `MixedBObsR`, `IotaGammaR`, `LedgerGammaR`,
`HalfTorsorGammaR`, `MStageCountGammaR`, `RStage/GammaR`, `CoverLiftR`, `Phase140/GammaR/*`,
`GaussZ/{KappaR,RelatorGammaR,CoordGammaR,GammaRD}`), mapped in advance by four surveys. Two
results there beat their specifications: `card_H2_gammaR` landed **unconditional** rather than
hypothesis-gated, and the R-word's κ⁰ evaluation is genuinely cleaner than Γ_A's, with no
`d₀`/`h₀` telescope. Two honest debts were recorded rather than hidden: ~300 lines of
Γ-free helpers are `private` in `Phase140/GammaA` and had to be restated binder-for-binder,
and `SourceData`'s eight pro-2 generator-pinning fields are **unsatisfiable at Γ_R's honest
generators** — they are consumed by no theorem (grep-verified), so `sourceR` supplies
marked-pinned choice elements and the finding is documented in
`GQ2/Roe/Main.lean`'s module docstring as a post-campaign cleanup candidate.

## 4. What is proved, and on exactly what

```lean
GQ2.main_presentation_literal_roe (hBLab : BLabHypothesis) :
  Nonempty (ContinuousMulEquiv GammaR AbsGalQ2)          -- GQ2/Roe/Main.lean:534
```

⟦thm:main⟧, with `GQ2.eq_154_R` (`:469`), `GQ2.main_surjection_count_R` (`:493`), and the
bonus `GQ2.admissibleCountR_eq_admissibleCount` (`:501`), which turns the June numerical
agreement of the two admissible-marking counts into a theorem for every finite group.

- **No `sorry`.** The Γ_R capstones and their whole import closure are sorry-free.
- **No new axiom.** The census stays at nine literature axioms. The axiom print of
  `main_presentation_literal_roe` is *byte-identical* to that of `main_presentation_literal` —
  standard three plus nine — and this is checked mechanically by `scripts/check_axioms.sh`
  (check 5 pins four capstones at the exact 12-axiom set and asserts three Γ_A↔Γ_R twin pairs
  print-identical) and by `GQ2/AxiomLedger.lean`, not asserted in prose.
- **One hypothesis.** `BLabHypothesis` is a theorem binder. The Γ_R result is conditional; the
  Γ_A result is not. A passing Comparator run on the Γ_R pair checks the *conditional*
  statement and is silent on whether the hypothesis is true.
- **Numerically anchored.** R5 checked `admissibleCountR` against the June LMFDB-verified
  finite-quotient counts four independent ways before any deep proof consumed the definitions:
  `C₂ : 7`, `C₄ : 24`, `V₄ : 42`, `D₄ : 144`, `Q₈ : 144`.

## 5. The open end: the L-campaign

Discharging `BLabHypothesis` is a live campaign, not a plan. The L0 recon compared Labute's
original argument, NSW III §9, and an instance-specific route, and recommended **levelwise
two-sided lifting**: build continuous surjections in both directions level by level along the
λ-tower, take a König limit through the existing `Reconstruction.lean` machinery, and close
with `profinite_hopfian`. No `Aut(F₃)`, no graded Lie algebra. Serre's Bourbaki 252 was
page-verified as the primary source.

The LS spike then de-risked it computationally and returned **GREEN** — but only after
*falsifying* the naive stage lemma (the cokernel of `d̄` is 2 at every level, and greedy
lifting stalls at k = 4/5). The repair is sharper than a tail-augmentation: an invariant
`P(T)` = χ-congruence mod `2^k` with `m(k) = k`, `k₀ = 3`, exhaustively verified at k = 3, 4
(256/256 both directions) and sampled to k = 6, with an `f = 3` control failing by exhaustion
for the right reason. This reduces the uniform input to **one span theorem** about free
groups, which is the campaign's residual risk.

L1 froze the statements as a 1,243-line, four-file compiling skeleton at exactly 56 sorries
(`GQ2/Roe/Labute/{TwoCentralTower,Levelwise,StageLemma,Assembly}.lean`), with the Hopfian
endgame, both stage compositions, and both epi assemblies already proved *inside* the
skeleton; the target is `GQ2.Roe.Labute.bLab : BLabHypothesis`
(`GQ2/Roe/Labute/Assembly.lean:184`). As of this writing L2 (λ-tower), L3 (base cases), and
L4b (the span theorem) are in flight; L4a, L5 (assembly, including a serialized refactor of
`GQ2/Reconstruction.lean`), and L6 (gates and docs) are queued.

Those four files are the **only** `sorry`s in the repository. They are allowlisted by name in
`scripts/check_axioms.sh`, so a `sorry` anywhere else still fails the gate, and nothing
outside `GQ2/Roe/Labute/` depends on them — verified by `AxiomLedger`'s gap map, and by the
fact that neither Comparator statement's import closure reaches that directory.

## 6. What a reviewer should check

1. That `r_R` in `GQ2/Roe/Words.lean` transcribes ⟦eq:defwords⟧⟦eq:relators⟧ — including the
   factor order and the two distinct `ω₂` occurrences. The count cross-check (§4) is the
   independent guard here.
2. That `BLabHypothesis` (`GQ2/Roe/MarkedPro2.lean:137`) states the Labute instance the note's
   ⟦cor:abstractD0⟧ actually needs, and no more. It is the whole conditionality.
3. That `GQ2.SourceData`'s fields are the honest interface — in particular that the eight
   unsatisfiable pinning fields really are consumed nowhere.
4. That `check_axioms.sh` check 5 and `AxiomLedger` are doing what §4 claims, since every
   axiom claim in this document is delegated to them.
