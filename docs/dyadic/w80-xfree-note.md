# W80-XFREE lane note

Branch `claude/w80-xfree`, based on `4f30776b`.  One new module,
`GQ2/Dyadic/SqCore/GradedXFree.lean` (prefix `gXf`).  No `sorry`, no new axiom, no
`native_decide`, no heartbeat or recursion-depth bump.  Every declaration carries a
`#print axioms` line in the file's own pin section.

Verification of record: `scripts/mirror.sh sweep` at lane start, then
`scripts/mirror.sh gen GQ2.Dyadic.SqCore.GradedXFree` after every edit.  Nothing in the tree
imports this module (registration in `GQ2.lean` is the orchestrator's).

## Ticket

Close the extraction, the odd route's other open input, by the scoped repair wave 79 verified
at the entry points (`docs/dyadic/w79-extract-note.md`, "What repairs it"):

* **T1** the `x₁`-freeness thread: state the invariant, prove preservation and base;
* **T2** the two Lean steps (homomorphy of `gExtMove` in the correction tuple, and
  `gTower_commHom_span` restricted to `gTowerFar`), then the weakened extraction;
* **T3** compose with the committed chain and discharge `SqClassClearingSupply h 5`.

## T1: the invariant

`gXfSpan h := gTowerFar h ⊔ γ₂`, and `GXfFree h a := ∀ i, a i ∈ gXfSpan h`.

Taking the clause as membership in a **subgroup** is what makes it an invariant for free:

* **preservation** (`gXf_free_mul`, `gXf_free_mul_gamma`): a depth-`k` correction with `k ≥ 2`
  lies in `γ₂ ≤ gXfSpan h`, so `a · d` is `x₁`-free whenever `a` is.  No bracket computation
  is involved, unlike the "corrections are invisible to the brackets" phrasing of the wave-79
  note: that fact is used later, at the point where the clause is *consumed*, not here.
* **base** (`gXf_bridgeTuple_free`, via `gXf_bridgeDress_far`): `bridgeDress` is
  `u_j^{ν'(v_j)}·v_j^{ν'(u_j)}·w^{-2ν'(u_j)ν'(v_j)}`, three `ℤ₂`-powers of far-span elements
  (`gBase_handleU_far`, `gBase_handleV_far`, `gAbs_pivot_far`), and the far span is closed
  (`gTower_zpow_mem`).  So the base dressing lies in `gTowerFar h` **outright**, with no `γ₂`
  slack; the `γ₂` summand of `gXfSpan` is there only for the corrections.
