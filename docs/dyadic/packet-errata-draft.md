# Draft errata/queries for the packet author (orchestrator, 2026-07-30 — owner reviews & sends)

Four items found while formalizing / machine-checking the packet
(`dyadic-presentations-formalization-proof.tex`). None threatens the main results; all four
are places where the written text understates an obligation the formal development had to
meet. Line numbers refer to the July 28 packet.

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
