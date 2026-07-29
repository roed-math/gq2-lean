# Reference documents for the dyadic campaign

Vendored 2026-07-28 from `~/claude/general_2adic/` and the repo root.

| File | Role | Authority |
|---|---|---|
| `dyadic-presentations-formalization-proof.tex` | **The proof packet** (July 28, 2026; externally prepared review supplement). Complete proofs of the boundary, lifting, composition-series, Fourier–Gauss, and local determinant reductions; the marked-matching reduction; the arithmetic branch correction; the nine-obligation inventory (§14). | **Highest.** Overrides both drafts wherever they disagree. |
| `dyadic-presentations.tex` | The July 2026 revision of the paper draft (relator families, B1–B4 interfaces, §10 Lean plan). | Second. Already contains the corrected compact words (`x₂^{-σ}`, not `x₂^{-σ₂}`). |
| (not vendored) `older-dyadic-presentations.pdf` | Superseded earlier draft, kept only in `~/claude/general_2adic/`. | Lowest — historical. |
| `dyadic-presentations-formalization-ledger.md` | The Lean-facing implementation ledger accompanying the packet: reuse table, decomposition, merge gates, implementation order. | Companion to the packet (same authority for Lean-architecture guidance). |
| `check_dyadic_current.py` | Dependency-free finite-target regression for the corrected quadratic-field words (S₃/D₈/A₄ counts), incl. the procyclic-vs-relative-norm √-10 comparison. Regressions, **not** proofs. | Test artifact. |

## Known packet-over-draft overrides (binding for this campaign)

1. **Sign-Frobenius row removed** from the ramified-`i` assembly: `η` even forces `r=1`, `ε=1`, and `K(i)/K` *unramified* (packet Prop. 8.1). Under the standing ramified-`i` hypothesis, `η` is odd; the `M_α` families are exactly **compact** (`r=0`) and **procyclic** (`r≥1`, `η ∈ ℤ₂ˣ`). The draft's `R_{M,sgn}` (draft eq. 5.10) and its §7.4 use for `ℚ₂(√-10)` are superseded.
2. **`ℚ₂(√-10)` is procyclic `M₂`** with `(r, ε, η) = (1, 1, 1)` (packet Cor. 8.2): `K(√5) = K(√-2)` is the unramified quadratic extension, `u = (-3)^{-1} ≡ 5 (mod 8)`. The draft's field-specific relative-norm word may be kept as an *alternative* (regression target), never as a sign-row specialization.
3. **B4 is the affine determinant interface** (packet Def. 6.3): equality of unshifted Gauss sums is insufficient; supply base dims/signs + polar pairing + a source-independent phase-cover theorem — i.e., reuse the actual `SourceData` obligation families, do not replace them by the draft's four-line B1–B4 record.
4. **B3 needs the natural chain map + five lemma** (packet Lem. 5.1): dimension equalities on simples are not enough; the composition-series induction requires commuting exact diagrams.
5. **The draft's two-character Labute theorem (draft Thm 2.1) is replaced** by the marked-matching reduction (packet Def. 7.1 + Prop. 7.2): only the per-core automorphism-lifting certificates MC-M / MC-N are new theorems.
6. **"when the inertia order is even" is deleted**: finite tame inertia in residue characteristic 2 has odd order (packet Lem. 3.1); the ramified middle-layer argument runs through odd inertia characters vs. trivial-inertia exceptional pieces.
7. Compact words use `x₂^{-σ}(x₂τ)^{ω₂}` (already fixed in the vendored draft).
