# Procyclic-`N` follow-up plan

**Milestone status (2026-08-02):** the `eta = <1,1>` precursor described below is landed in
`GQ2/Dyadic/Instances/NpcCore.lean`, uniformly in `h`, through `npcCorePresentationOne`.  The
remaining structural blocker for a full `WordCertificate` is exactly the arbitrary-unit
inverse-power interface.

The exact-lifting lane no longer waits on that dictionary.  `GQ2/Dyadic/Instances/NpcExact.lean`
works directly from the corrected `GammaR` presentation and the two-valued `npcResolver`.  It
proves the following constructor table uniformly in `alpha`, `r`, `h`, even `q`, and every
displayed unit:

| `ExactLiftingSemantics` clause | construction | genuine residual |
|---|---|---|
| lift cardinality | `liftsOver_cardN` at `npcFamOf` | per-simple `Hsimp` |
| half-torsor identity | `lem86_of_variation` | the same `Hsimp` |
| scalar `#H^2 = 2` | `cardH2_of_variation` plus the uniform two-element quotient | none beyond `Hsimp` |
| equation (136) stage | `blockStageR136K` | `StageSep` and `StageZ` |

The semantic arbitrary-unit constructor uses `Words.Npc.npcWUnit`; the regression theorem
`NProcyclic.gamma_eq_display` rewrites it exactly once through
`Words.Npc.npcWUnit_eq_display` to the corrected frozen `npcW`.  The selector theorem
`NProcyclic.exactLifting_of_fieldSelection` applies this constructor to a selected `.Npc` row.
No exact-lifting theorem mentions the retired uncorrected word.  The inverse-power work below
remains relevant to the stronger structural `WordCertificate` assembly, not to these three
exact-lifting clauses.

## Scope and current boundary

The word, Fox, Stokes, scalar, and Hessian lanes for the corrected procyclic-`N` word are
already present.  The earliest missing assembly layer is the alphabet-to-core dictionary needed
by `Count.CorePresentation.ofPresentedBy`.  The landed forward relation is
`Words.Npc.eval_pro2_npcW`:

```text
R_Npc |pro-2 = nRelWord alpha
  (mu0, mu1, mu2, mu3, handles)

mu0 = x0
mu1 = sigma ^ etaHat
mu2 = x1 * sigma ^ (2^r)
mu3 = x2
mu(4+2j) = u_j
mu(5+2j) = v_j.
```

Thus `Npc` uses the same core `DN alpha h` as compact `N`, but its generator dictionary is not
the compact dictionary: the core `sigma` slot is supplied by `x1 * sigma^(2^r)`, while the
second core slot is the profinite power `sigma^etaHat`.

## Intended `CoreReindex`

Factor the construction through `Count.PilotN.nReindex h`.  If

```text
c = (nReindex h).toCore t
  = (x0, x1, sigma, x2, handles),
```

define the forward twist

```text
npcTwist r gamma c:
  0 |-> c0
  1 |-> c2 ^ gamma
  2 |-> c1 * c2 ^ (2^r)
  3 |-> c3
  handle slots |-> themselves,
```

where `gamma = d.toZhat`.  If `gammaInv` is an inverse profinite exponent, define

```text
npcUntwist r gammaInv m:
  0 |-> m0
  1 |-> m2 * (m1 ^ gammaInv) ^ (-(2^r) : Z)
  2 |-> m1 ^ gammaInv
  3 |-> m3
  handle slots |-> themselves.
```

Then the intended dictionary is

```lean
noncomputable def npcReindex (r h : Nat) (d : EtaData)
    (hinv : ProfinitePowerInverse d.toZhat) :
    CoreReindex (2 + 2 * h) (Fin (coreRank h))
```

with

```text
toCore t = npcTwist r d.toZhat ((nReindex h).toCore t)
ofCore m = (nReindex h).ofCore (npcUntwist r hinv.invExp m).
```

The minimal missing exponent interface can be packaged as follows (the exact universe and
topology binders should mirror `zpowHat`):

```lean
structure ProfinitePowerInverse (gamma : Zhat) where
  invExp : Zhat
  left_inv  : forall (G) [profinite hypotheses] (x : G),
    (x ^z invExp) ^z gamma = x
  right_inv : forall (G) [profinite hypotheses] (x : G),
    (x ^z gamma) ^z invExp = x
```

Naturality of both directions then follows from `map_zpowHat`.

At the arithmetic boundary, the producer theorem should say that an `EtaData` representing a
2-adic unit supplies this inverse:

```lean
noncomputable def etaDataPowerInverse (d : EtaData)
    (hnum : d.num % 2 != 0) (hden : d.den % 2 != 0) :
    ProfinitePowerInverse d.toZhat
```

Equivalently it may take `IsUnit d.toPadic`.  The odd numerator/denominator spelling is listed
because it matches `Words.Npc.wf_rawNpc` and the frozen certificate side conditions.

### Generator-slot map

| core slot | `toCore` value | recovered alphabet letter |
|---|---|---|
| `0` | `x0` | `x0 = mu0` |
| `1` | `sigma ^ d.toZhat` | used to recover `sigma` by `hinv.invExp` |
| `2` | `x1 * sigma ^ (2^r)` | `x1 = mu2 * sigma ^ (-(2^r))` |
| `3` | `x2` | `x2 = mu3` |
| `4+2j` | `handleU j` | unchanged |
| `5+2j` | `handleV j` | unchanged |

Consequently the dictionary marking itself has

```text
mark sigma = (dnGen alpha h 1) ^ hinv.invExp
mark x0    = dnGen alpha h 0
mark x1    = dnGen alpha h 2 * (mark sigma)^(-(2^r))
mark x2    = dnGen alpha h 3
mark handles = the corresponding dnGen.
```

These formulas are the normalization facts needed later by `nu_compat_coreHom`.

## Relation transport and presentation targets

Once the dictionary exists, the word equality should have these signatures:

```lean
def npcCoreRel (alpha r h : Nat) (d : EtaData)
    (hinv : ProfinitePowerInverse d.toZhat)
    (G : Type) [profinite hypotheses]
    (t : Marking (2 + 2*h) G) : G :=
  nRelWord alpha ((npcReindex r h d hinv).toCore t)

theorem npcProTwoWord (alpha r h : Nat) (d : EtaData)
    (hinv : ProfinitePowerInverse d.toZhat)
    (G : Type) [profinite hypotheses]
    (t : Marking (2 + 2*h) G) :
    t.eval (pro2 (npcW alpha r h d)) = npcCoreRel alpha r h d hinv G t

theorem eval_pro2_npcW_reindex ... :
    t.eval (pro2 (npcW alpha r h d)) =
      (nNatWord alpha h).ev ((npcReindex r h d hinv).toCore t)

noncomputable def npcCorePresentation ... :
    CorePresentation (2 + 2*h) (npcW alpha r h d) (DN alpha h)
```

No `alpha` or `r` lower bound is consumed by this structural layer.  `alpha >= 1` belongs to the
Fox/Stokes validity layer; branch validity later strengthens to `alpha >= 2` and `r >= 1`.

### Maximal precursor that does not need new exponent algebra

For `d = <1,1>`, `sigma^etaHat = sigma`.  The inverse dictionary is ordinary group algebra and
can be implemented uniformly in `h` now:

```lean
noncomputable def npcReindexOne (r h : Nat) :
    CoreReindex (2 + 2*h) (Fin (coreRank h))

theorem eval_pro2_npcW_one_reindex (alpha r h : Nat) ...

noncomputable def npcCorePresentationOne (alpha r h : Nat) :
    CorePresentation (2 + 2*h) (npcW alpha r h <1,1>) (DN alpha h)
```

This covers the `(alpha,r,eta)=(2,1,1)` harness and establishes every index/naturality lemma
independently of the future inverse-power proof.

## From `CorePresentation` to the structural `WordCertificate` fields

Given `q != 0` and `Even q`, `npcCorePresentation` supplies:

1. `pro2 := CorePresentation.coreHom ...`;
2. `ker_pro2 := CorePresentation.ker_coreHom ...`;
3. `hpro2 := CorePresentation.coreHom_surjective ...`.

The remaining already-generic structural fields are:

4. `tameSpecialization` from `Count.tameSpecializes_npcW`;
5. `compat` from `CorePresentation.nu_compat_coreHom`, after proving the dictionary's
   `nuP(mark sigma)=ztwoOne` and `nuP(mark wild)=1` formulas;
6. `tfg` from `Count.gammaR_topologicallyFinitelyGenerated`;
7. `smulZmod2`, `contSMulZmod2`, and `htriv` from the scalar-action constructors;
8. `htame` from `Count.htame_of_tameSpecializes`;
9. `hwild` from `Count.hwild_npcW`.

The `N`-core marking should reuse `nuN alpha h`, transported through `ztwoIota.symm` exactly as
`SqrtNeg2.pilotNuP`; the procyclic dictionary rather than the core changes which alphabet
letter maps to which `nu` value.

The four analytic `WordCertificate` inputs remain explicit dependencies:

```text
ExactLiftingSemantics
StokesDualityCertificate
ScalarHilbertCertificate
AffineDeterminantCertificate.
```

The branch files provide the lower certificates feeding these (`npcJacobianCertUnram`,
`npcJacobianCertRam`, `npc_stokesDuality`, scalar Gram pins, and `npcHessianCertificate`), but
the generic certificate-to-count bridges are still separate campaign work.

## Module-specific analytic issue: do not use the compact endpoint

The unramified Fox reduction deliberately stops at the two-entry block row

```text
(A^-1 + 1, 1 + S^(-2^r)).
```

Neither entry is uniformly invertible.  On an unramified simple module, the two exact criteria
are fixed-space conditions for `A` and `S^(2^r)`; both entries vanish simultaneously only on the
scalar module.  Therefore `Npc` does not admit the compact-`N` uniform diagonal endpoint.  The
future exact-lifting/Stokes assembly must split on these per-module criteria (or prove the
appropriate simple-module dichotomy) and consume the two-valued resolver in
`Count/Frozen.lean`.  It must not state a false compact diagonal normal form.

The ramified side is better behaved: `npcJacobianCertRam` performs its two valid operations and
splits the `x2` column without assuming the `x0` block is invertible.

## Tests and acceptance gates

1. Targeted build of the new dictionary file.
2. Kernel checks for both round trips at `h=0` and `h=1`.
3. Relation transports at `(alpha,r,h)=(2,1,0)` and `(2,1,1)`.
4. `CorePresentation` smoke tests showing its `mark sigma` and the first three wild-letter
   formulas.
5. `#print axioms` on `npcReindexOne`, the relation transport theorem, and
   `npcCorePresentationOne`; only standard logical axioms are allowed.
6. `rg` checks: no `sorry`, no new `axiom`, no `native_decide`.
7. `bash scripts/check_dyadic.sh` after the targeted build if the full repository build remains
   within the time budget.

## Dependency order

1. Land the `eta=1`, all-handle dictionary and relation transport.
2. Add the generic profinite exponent-composition/inverse-unit API near `GQ2/Zhat.lean` or
   `Dyadic/Word/Syntax.lean` (not inside the branch instance file).
3. Generalize the dictionary from `npcReindexOne` to arbitrary unit `EtaData`.
4. Add the `DN`/`Ztwo` marking normalization and the 13-of-17 structural
   `npcWordCertificate` constructor.
5. Stabilize the generic Fox/Stokes/scalar/Hessian-to-count interfaces.
6. Solve the unramified simple-module dichotomy and instantiate the four analytic clauses.
