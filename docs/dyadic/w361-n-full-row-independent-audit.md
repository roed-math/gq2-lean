# W361 independent audit — torsion-sensitive N core-row lifting

2026-09-17, 16:44 UTC; integration comparison added 16:46 UTC.
**Proof and production-source comparison verified.** Final-status addendum at
17:30 UTC: the complete 1,541-module fresh build, 573-pin artifact audit and
source-bound staged replay have now passed, followed by an independent complete
post-replay content check. See `w361-final-verification.md`. The original timed
audit and its then-pending build observations are retained below as history.
This addendum supersedes the torsion-row gap, for the precise parameter family
below, recorded in `w361-n-general-scaling-audit.md`. It is not a release,
owner-approval, or transitive fresh-build certificate.

## Exact conclusion

`GQ2.Dyadic.MarkedCore.nStabParam_fullFrame_lift_general` takes only
`2 ≤ alpha`, an arbitrary handle rank `h`, a parameter `P : NStabParam`,
and `P.Admissible`. It returns an actual continuous automorphism `Psi` of
`DN alpha h` satisfying simultaneously:

1. preservation of the canonical character `chiN` on every group element;
2. the prescribed `P.nuAction` for every continuous ordinary Z₂-valued
   character, with the same automorphism for all characters;
3. literal equality
   `nPhiHom ha h (abMk (Psi (dnGen alpha h i))) = fullFrameMark P h i`
   for every marked generator `i`.

There is **no remaining `htau` premise**, no scaling or finite-stage supply,
and no assumed cup-isometry or unspecified matrix identity. The target
coordinates in `NFrameModel h = Multiplicative (F₂ × Z₂³ × Z₂^(2h))` are:

| Marked generator | Full coordinate image |
|---|---|
| `x0` | `(1, 0, 0, 0, 0)` |
| `x1` | `(P.tau, 1, P.p, P.q, 0)` |
| `sigma` | `(P.tauSigma, 0, P.g 0 0, P.g 1 0, 0)` |
| `x2` | `(P.tauX2, 0, P.g 0 1, P.g 1 1, 0)` |
| handle letter with coordinate `k` | `(0, 0, 0, 0, e_k)` |

Thus the core columns are exactly `P.rows`, with the same column convention
as its definition, and the handles have identity columns and no torsion
components. This is genuinely the full topological abelianization, not an
ordinary-character quotient: the existing `nPhiHom_injective` and
`nFrameExists_phiEquiv` identify these coordinates faithfully.

The conclusion is deliberately **not** a classification or lifting theorem
for arbitrary handle-mixing stabilizers. The newly closed torsion-sensitive
statement is the prescribed distinguished rank-four `NStabParam` action,
extended by the identity on all handles. Claims covering every automorphism
of the entire rank-`4+2h` invariant triple still require an explicit reduction
to the available generator families. Nothing here alone asserts that wider
reduction or the original packet's complete MC-M/MC-N acceptance.

## Independent proof review

### Actual automorphisms preserve the cup form

`DNAutomorphismCup.evenCupForm_comp_dn_aut` is proved for every actual DN
continuous automorphism, without an orientation assumption. It transports
the actual N presentation along the automorphism and compares the two
injective additive obstruction maps `H² → F₂`. The existing uniqueness
lemma makes those maps equal; the checked N word-cup identity then gives
the full mod-two cup-form equality. This is not an assumed matrix constraint.

### Cup comparison recovers the missing torsion entries

`NStabilizerFullRows.torsionChar` is the actual torsion coordinate
`nTHom ∘ abMk`, with value one at `x0` and zero at every other canonical
generator. Every nonzero ordinary coordinate is realized by an actual
continuous Z₂-character, reduced continuously modulo two. Write `a_i`
for the torsion character evaluated on `Psi(dnGen i)`.

The cup equation against the fixed ordinary `x1` character gives `a_0=1`.
The equations against paired handle characters give all handle `a_i=0`.
The two remaining ordinary plane characters give

```text
red(P.p) = a_3 red(g_00) + a_2 red(g_01),
red(P.q) = a_3 red(g_10) + a_2 red(g_11).
```

The already checked `nStabParam_tauSolve_unique`, using the actual unit
determinant in `P.Admissible`, identifies `a_2=P.tauSigma` and
`a_3=P.tauX2`. No desired torsion value is supplied to this deduction.
The free value `a_1` is intentionally left explicit at this intermediate
stage. The remaining integral coordinates are read from actual coordinate
characters through `nPhiHom_aut_coordinates`; hence no handle coordinate
or torsion summand is silently omitted in the final product equality.

### The remaining free entry is adjusted exactly

`NTorsionAdjust` uses `Psi' = Psi ∘ dnTauBEquiv(delta.val)`, with
`delta = P.tau - a_1`. Its composition order matters: every marked image
other than that of `x1` is literally unchanged, while

```text
Psi'(x1) = Psi(x0)^delta.val * Psi(x1).
```

The derived `a_0=1` makes its new torsion coordinate exactly `P.tau`.
Every ordinary character kills `Psi(x0)` because its composition with
`Psi` is again an ordinary character. Thus all ordinary rows remain
unchanged. The known N1 automorphism preserves `chiN`, so the adjustment
also preserves orientation. `nStabParam_fullFrame_lift_general` starts
with the unconditional `nStabParam_lift_general`, performs this adjustment,
and applies the full-frame theorem with the now-proved `htau`.

No circularity was found: cup invariance uses only the actual presentation,
the torsion adjustment is an existing explicit automorphism, and the new
ordinary-row producer comes from the separately audited uniform filtered
construction. The full-row existence theorem is not used upstream.

## Compilation and byte record

The four sources below were read completely. Each was independently
elaborated with the pinned Lean runner at default limits, without warnings.
Their **40 public axiom prints** contain exactly `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, new axiom, unsafe hook,
native decision, or resource-option override is introduced. Existing
dependency artifacts were reused; this is not a fresh transitive rebuild.

| Scratch source | Public pins | SHA-256 |
|---|---:|---|
| `/private/tmp/DNAutomorphismCup.lean` | 8 | `3369825da3020948de69346a3e1c7e49c25913b049d54b091b3a8b63a74a4a8b` |
| `/private/tmp/NTorsionAdjust.lean` | 7 | `eb1ba598bdd2c4583c30cdf48436fdbd7c2b08d9609c4838302ff20a9cbadfd6` |
| `/private/tmp/NStabilizerFullRows.lean` | 24 | `5fbd9cd770ce01463da505f353daa372146640f7f0e76be3a87b124bedc45e13` |
| `/private/tmp/NStabilizerFullLift.lean` | 1 | `4bd361052a7c58f1ef7d7e6097b519a1d8413ec3f7a48a7e65085b7defc47263` |

The final composition imports the newly banked production
`NPlaneGeneralScaling`, whose source hash remains the previously audited
`ddd4e79e91876b35b7785b0d2d4e2d1a3e5e68439a35fd4da99428b8d4489a0a`.
At the initial 16:44 checkpoint the four sources above were still scratch
modules pending production-name integration. The historical
1,531-module/504-pin snapshot does not certify this increment.

## Production integration comparison, 16:46 UTC

All four files are now banked and the mathematical source was frozen by the
root agent at 16:45 UTC. Independent byte comparison confirms that
`DNAutomorphismCup` and `NTorsionAdjust` are identical to their checked
scratch sources. `NStabilizerFullRows` changes only its cup-module import
to the fully qualified production path. `NStabilizerFullLift` changes only
its two scratch imports to the corresponding fully qualified production
paths. All declarations, hypotheses, conclusions, proof bodies, and pins
are byte-identical otherwise.

| Production source | SHA-256 |
|---|---|
| `GQ2/Dyadic/Instances/DNAutomorphismCup.lean` | `3369825da3020948de69346a3e1c7e49c25913b049d54b091b3a8b63a74a4a8b` |
| `GQ2/Dyadic/MarkedCore/NTorsionAdjust.lean` | `eb1ba598bdd2c4583c30cdf48436fdbd7c2b08d9609c4838302ff20a9cbadfd6` |
| `GQ2/Dyadic/MarkedCore/NStabilizerFullRows.lean` | `1d856eeb1ec66977c131f4fac1c9ecf88a6a538d68a750e0c80c098542fe6894` |
| `GQ2/Dyadic/MarkedCore/NStabilizerFullLift.lean` | `8b175aea4cbc4793005c7f95034269ff8d471eceab942331df4516046c2264e3` |

The root reports successful default compilation of all ten integrated
increment modules, including their 69 new pins (573 total artifact pins).
Its final hardened, zero-local-output-reuse rebuild is running with an
expected closure of 1,541 modules; log
`/private/tmp/gq2-w361-fresh-unconditional-final.log`. This audit does **not**
assert that this build or its subsequent source-bound replay has finished.
Those results must be checked separately. Publication and owner decisions
remain separate in either case.
