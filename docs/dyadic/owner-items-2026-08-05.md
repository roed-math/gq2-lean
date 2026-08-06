# Owner decision items — wave 37 (2026-08-05)

Six items surfaced during the wave. Item 1 is a genuine mathematical constraint on the
general-`K` program and needs a decision; items 2–6 are statement or documentation defects
with recommended fixes. Nothing here blocks the odd-degree L row, which is now unconditional
on the forward side.

## 1. DECISION: the ramified Arf conclusion is false at even residue degree

**Finding.** The determinant analysis' ramified branch concludes `Arf(q̄_U) = 0`. That
conclusion holds at residue cardinality `q = 2^f` **only when `f` is odd**. At `q = 4` it is
false, with an explicit counterexample: `C = D₅` acting on `V = 𝔽₁₆` with `t = ·ζ₅` and
`s = Frob²`, `q̄(x) = Tr(c x⁵)` for `c ∉ 𝔽₄`. There `V^U = 𝔽₄` has four elements rather than
the predicted two, `rank(1+U) = 2 ≢ s_V`, and Wall's formula gives `Arf(q̄_U) = 1`. The
witness was verified twice by independent routes (the rank formula, and directly via
`q̄_U = q̄ + ℓ`). The general count is

    #V^U = 2^(gcd(deg P, F·ω) · s_V),

whose exponent is odd exactly when `F` is odd.

**Impact.** None on the L row: odd degree forces `f` odd, and
`wordCertificateRN_lSq_pow` is stated with `Odd f`, so the L certificate is unconditional
on its whole branch. The **even rows** are affected, since they admit even residue degree.

**Options.**

1. **Restrict the even-row program to `f` odd.** Cheapest; leaves the even rows' general
   statement incomplete at even residue degree.
2. **Carry the corrected Gauss sign** `(−1)^(gcd(deg P, F·ω) + 1)` through §6 and the
   determinant bridge. More work, and it changes displayed statements in the paper's §6.
3. Split: prove the even rows at `f` odd now, open a separate ticket for the sign-corrected
   general form.

**Recommendation:** option 3 — it unblocks the even rows immediately and isolates the sign
work, which is a self-contained §6 revision.

## 2. `LRamifiedSourceArfSupply` is missing a hypothesis

`GQ2/Dyadic/Instances/GammaLDeterminantResidue.lean:44` quantifies over every block, level
and lift with **no ramification hypothesis**, while its only consumer
(`wordPhaseResidueK_ramified_lSq`) supplies one. In an unramified block the descended source
form has `Arf = 1`, so the literal statement is unprovable. The `hram`-conditioned form is
what is actually built and consumed (`lRamifiedSourceArf_blockK`).

**Recommended fix:** add `hram` to the binder list; `lRamifiedSourceArf_blockK` then produces
the supply verbatim.

## 3. `NLabHypothesis` is false-shaped

`GQ2/Dyadic/MarkedCore/N.lean:1306` has no canonicity guard, unlike its `M` twin. `DM α h`
satisfies **every** clause of `NLabHypothesis α h` (Demushkin, rank `coreRank h`, `q = 2`, and
a continuous character whose range is exactly `imChiN α` — `chiNOnDM`), so the hypothesis
forces `DM α h ≅ DN α h`, which is false: `imChiM α ≠ imChiN α` is now an unconditional
theorem (`EvenNLabWitness.lean`, α ≥ 2). A literal `¬ NLabHypothesis` needs canonicity of the
orientation, precisely the clause the binder drops.

**Recommended fix:** add the canonicity guard the `M` binder carries, or retire the binder —
the even-row route decided this wave (clone the L forward-generator architecture) does not use
it at all.

## 4. Superseded records to deprecate

`LUnramifiedGraphData` / `LRamifiedGraphData` (`GammaLDeterminantUnramified.lean:34`,
`GammaLDeterminantRamified.lean:37`) and their two `_of_graphData` theorems are stated one
level too high: their lower-marking conditions are equations in `DD.C0`, which at
`blockEnrichmentDK` force the whole C-stage to be procyclic (`yc_procyclic_of_c0_graphData`).
The head-factored replacements supersede them.

## 5. Documentation drift

* `docs/dyadic/followup/labute-interface-status.md` — its central finding (the Labute
  hypotheses conclude *unoriented* equivalences and are therefore insufficient) is superseded
  by `OrientationCorrection.lean:456,468,563,584`, which supply the oriented forms; and its
  "remaining invariant" list is off the forward path entirely after this wave.
* Two docstrings miscite `Kummer.kummerCocycleFun_root_indep`; the real name is
  `GQ2.kcf_root_indep'`.
* `HilbertLedger.norm_two_lt_one'` is `private` and was re-proved downstream; de-privatizing
  removes the duplication.

## 6. Small tickets worth opening

* **`MFrame` at general `h`.** `demushkinQ (DM α h) = 2` exists only at `h = 0` and only from
  an `MDecomposition α`, with no producer. The `N`-side template (`N.lean:176–337`) transfers
  almost verbatim; only the torsion generator changes, to `t = Ā·C̄₀^(2^(α−1))`. This would
  make the item-3 counterexample unconditional at every handle count.
* **`α = 1` even cores.** Everything even in this wave assumes `α ≥ 2` (at `α = 1` both cores
  leave the shared Gram). Whether the `α = 1` cores are Demushkin is open and deliberately
  unasserted.
* **`mpcW` Hessian/jet layer** at general `h` (the `npcW` analogue landed this wave).
