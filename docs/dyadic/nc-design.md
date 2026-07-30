# NC1 — the corrected noncompact-N cross-operator theorem: design memo + spike

**Ticket NC1** (dyadic campaign, R3(a) commission; board [`tickets.md`](tickets.md)). Written on
branch `dyadic-nc1` (worktree `~/claude/gq2-dyadic-lg`, at the `dyadic` head `337647f`). Every
Lean anchor below was opened and read in this checkout; Python anchors are from
`~/claude/general_2adic` (the simplification campaign's repo, read-only).

**Commission.** The simplification campaign machine-refuted the draft's eq:Ncross (S3.2,
`general_2adic/BOARD.md:581`; errata item 5, [`packet-errata-draft.md`](packet-errata-draft.md)):
for the corrected noncompact-N word the universal second jet on ramified simples carries

```
Q(c₀, c₁) = Q₀(c₀) + b_q(c₁, L_c c₀),
L_c = A⁻¹ + B + B·A⁻¹ = 1 + (1 + A⁻¹)(1 + B),   M_c = adj(L_c),
A = S^{η̂},  B = S^{2^r}
```

— NOT the draft's `L_c = A⁻¹`. The owner chose R3 option (a): prove the corrected identity in
Lean (symbolic in `r ≥ 1`, `η ∈ ℤ₂ˣ`, on ramified simples), replacing the twisted-path
diagnostic status. This memo designs that theorem: statement, proof route, missing machinery,
ticket plan, feasibility spike, timing.

*(Sections are committed incrementally; this header commit fixes scope.)*

---

## 0. Headline verdicts

(to be filled)

## 1. The mathematics being formalized

(to be filled — word, engine computation, reduction rules)

## 2. The Lean statement

(to be filled)

## 3. Proof route

(to be filled)

## 4. File map and NC2+ tickets

(to be filled)

## 5. Feasibility spike

(to be filled)

## 6. Timing: now vs post-G-1 (WNP-b/c)

(to be filled)

## 7. Risks

(to be filled)

## 8. Owner questions

(to be filled)
