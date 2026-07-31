# Draft errata/queries for the packet author (orchestrator, 2026-07-30 — owner reviews & sends)

Items found while formalizing / machine-checking the packet
(`dyadic-presentations-formalization-proof.tex`). None threatens the main results; they
are places where the written text understates an obligation the formal development had to
meet. Line numbers refer to the July 28 packet. (Cover note: our own section-number
citations for packet §§7–10 drifted off by one against the vendored compile at one point —
items below cite by label wherever one exists; when replying, labels are authoritative.)

1. **proof.tex:757 — "hyperbolic handles can then be added by standard Nielsen moves
   preserving their commutator product" is incomplete for the *marked* statement — and we can
   offer the constructive fix.** The word-certificate transfer is fine, but for the marked
   transfer the 2h new ν-values require a handle↔core *mixing* element that Nielsen moves and
   the peripheral action cannot supply (the naive candidate is obstructed by the triple
   commutator [[σ,v₁],u₁]). However, a corrected mixing element EXISTS: an exhaustive
   small-word search found the unique solution of `[A,σ][U,v] = [a,σ][u,v]` fixing x₀, σ, v
   literally with Φ(P) = P on the nose, verified uniformly for the L (collector/twisted), N
   and M families, with 2-adic exponents handled by integer powers × diag(w,w⁻¹) conjugation.
   Suggested amendment: "standard Nielsen moves **plus one twist-type move per handle**".
   (Details: `general_2adic/artifacts/reports/marked-stabilization-memo.md` Lemma 6.3 +
   `gq2-dyadic/docs/dyadic/handlemixlift-spike.md` §4–§5.) Note the construction does NOT
   directly cover the square-commutator word's handle block (its prefix shares both
   commutator letters) — that case needs a change of variables first.

2. **§14 (line ~1077) — the Smith–Witt completion criterion implicitly assumes the same
   mixing stratum at rank four.** A finite Nielsen-generator list exists, but the
   constructions realize only the elementary and unit-scaling strata; the mixing
   transvections are in the stabilizer, are needed for the ν-correction, and are not
   reachable by Nielsen moves or the peripheral action. (MC1 memo §7.3,
   `gq2-dyadic/docs/dyadic/mc-design.md`.) Same question as item 1, at rank four.

3. **The compact-M marked change of variables is not in the packet or drafts.** Prop. 8.1
   fixes the two surviving M rows as compact (r = 0) and procyclic (r ≥ 1), but only the
   procyclic substitution is displayed, and it degenerates at r = 0 (ε·2^{r−1} = ε/2). The
   formal branch lanes need the compact-M substitution explicitly. (MC1 memo §7.2.)

4. **Prop. 8.1 implicitly assumes r ≥ 1.** At r = 0 the target ℤ/2⁰ is trivial, so "η even"
   holds vacuously while the conclusion r = 1 fails; the formalization states the r = 0
   alternative as an explicit dichotomy. Worth a parenthetical in the packet. (F4,
   `GQ2/Dyadic/Branches.lean`, `level_zero_or_not_even_eta`.)

5. **Draft eq:Ncross — the displayed cross operators are incorrect (conclusion unaffected).**
   Machine-verified through the exact class-two engine (symbolically in r and η, validated
   end-to-end on both twisted ramified simples at six instances): the corrected noncompact-N
   word's second-order cross operators are `L_c = A⁻¹ + B + BA⁻¹ = 1 + (1+A⁻¹)(1+B)` and
   `M_c = adj(L_c)`, not the displayed `M_c = A, L_c = A⁻¹`; the discrepancy `B(1+A⁻¹)`
   vanishes iff `A = 1`. The conclusion (L_c invertible on every ramified simple, hence the
   restored `c₀–c₁` pairing) survives with the corrected operator. (S3.2,
   `general_2adic/dyadic_search/families/N.py` §16 records; exact replacement supplied.)

6. **Draft compact-M forward-order rejection — right conclusion, wrong reason and wrong
   witness.** The draft says the forward `E_m` order "has determinant `R⁻²(1+R+R²+R³+R⁴)` …
   singular on a primitive fifth-root orbit". Measured: the forward-order form is
   NONSINGULAR (radical 0, same Gauss as reversed); what refutes it is that it is the WRONG
   form — it differs from the required one by a linear form (failure class second-order, not
   a rank drop), with the proof-grade difference `Q(fwd)+Q(rev) = b_q(Wd₀,d₀)+b_q(Wd₁,d₁)
   +b_q((1+W²)d₁,d₀)`, `dᵢ = (1+P)cᵢ`, `W = σ₂^m`. Moreover the fifth-root orbit separates
   the orders only at (α, q_K) = (2, 2) — NEITHER displayed instance (√2 is (3,2), √5 is
   (2,4)); the seventeenth-root orbit covers both. General criterion (proved): a separating
   orbit needs `2^{α−1} < ord₂(q_K mod ord T)`, hence dimension ≥ 2^α. (S4.1,
   `general_2adic/artifacts/rejected/M-compact-forward-order/`.)

7. **The √−10 relative-norm word does not repair the order-nine obstruction (as measured).**
   The draft presents the field-specific relative-norm word as repairing exactly the
   order-nine obstruction at `V = 𝔽₆₄`, `|ζ| = 9`. Measured through the exact class-two
   engine on the twisted route: plus-only gives radical 2, the relative-norm route ALSO gives
   radical 2, and only the procyclic **shadow** route reaches the plus form `Q₊` (radical 0)
   — the general shadow construction supersedes the field-specific word entirely. This is a
   *diagnostic* discrepancy on the twisted path (labelled as such; never used to reject a
   word), reported because the draft's claim is what motivates keeping `rel_minus10`.
   (S4.3, `general_2adic/artifacts/rejected/M-procyclic-order-nine/`.)

8. **Draft §7.3's `R₁₀` omits `𝒩_{U,m}(δ₂²)^{U^m}`.** The omitted factor is nontrivial (an
   S₃ witness separates the two relators as words), though no oracle in the compact/procyclic
   lane distinguishes them by jets, D₈ counts, or epimorphism rows. Likely a transcription
   slip in the displayed √10 specialization rather than a mathematical claim. (S4.3.)

**Closing clarification (not an erratum — a task-list trap worth a sentence).** The
simplification-campaign §8.5 task list says "prove their zero first jets" for the two
procyclic-M correction blocks. Measured through the exact first-jet engine: **neither
`E₀₁^pc` nor `E₂^pc` has a zero first jet** — the statement that is true (and certified) is
that the *hat copy's whole row* vanishes (via the shadow transport theorem), while at first
order the shadow copy reproduces `E₀₁^pc`'s entire contribution operator-for-operator, so
`E₀₁^pc`'s justification is second-order only (exact fifth-root-module refutation). Anyone
following the task list as written would try to prove something false. (S4.3, S4.4;
`general_2adic/artifacts/reports/{report-phase4,m-alternative-search}.md`.)
