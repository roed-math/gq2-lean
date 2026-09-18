# W361 independent exact-word template audit

Status: read-only proof/tooling audit; no template, exporter, fixture, frozen manifest, or
source-certificate definition was changed by this audit.

## Result

The staged templates faithfully denote the actual pair/mobile splice constructors. The
headline theorems prove **literal PWord equality**, not only group-evaluation equality.
The symbolic AST is genuinely shared by the denotation and JSON traversal. No loss of
two-adic precision, implicit rationalization, mistaken shear sign, missing parameter, or
confusion with the frozen `Shadow` node was found.

Independently compiled, at default settings:

- `Word/GeneralTemplate.lean`
- `Word/GeneralTemplateM.lean`
- `Word/GeneralTemplateSplice.lean`
- `Word/GeneralTemplateEval.lean`
- `Word/GeneralTemplateExport.lean`

All 47 printed pins are at most the standard three axioms. The expanded Python self-test
independently passed all 37 checks. Strong `check --lean-runner` independently passed all four staged
artifacts: pair (alpha,h,j)=(2,1,0),(3,2,1), and mobile (alpha,r,p,h)=(2,1,0,0),(3,2,2,1).
Artifact provenance checking is discussed below; these proof and serialization checks do
not authorize an S1.1 migration or replace the acceptance appendix.

## Semantic exactness

`PadicTerm.denote` has codomain `Z_2`; `ProfiniteTerm.denote` has codomain `Zhat`. In particular,
`padicOmega k` denotes `padicOmega2 k`, while `etaHat eta` denotes `etaHatZ eta`. Integer,
two-adic-power, and profinite-power AST nodes remain distinct. Arbitrary mathematical values
live in a noncomputable environment, not in finite JSON digits.

The raw factories preserve binary product association, trailing identity nodes, and the
special no-handle-tail convention at h=0. `denote_compactM`, `denote_rawPair`, and
`denote_rawMobile` quantify over all their discrete inputs. The pair applies the head-handle
permutation followed by the tail-handle permutation. The mobile factory retains alpha, r,
p, and h, including the actual p-dependent branches and orbit-product lengths.

The normalization environment binds, for every wild index i,

```
k[i] = toAdd (ztwoIota (nuP (C.mark (wild i)))).
```

Here C is exactly `headHandlePairCorePresentation` or `mpcCorePresentationUnit`. This is the
full normalized-core coefficient, not merely a displayed residue. The tree substitutes
`wild i ↦ wild i * sigma^(padicOmega2 k[i])`, the actual **backward** shear used in the word;
the forward marking shear has the inverse power, and is not mistakenly serialized instead.

For mobile, `eta[0]` is bound to the supplied arbitrary unit's exact value. At the selected
field endpoint this is the actual D-coordinate unit etaD, not necessarily the displayed
selected eta; `SelectedWordProfile` separately proves their congruence modulo 2^r. The
selected relation `p = p epsilon r` is supplied by that profile, not assumed by the general
mobile factory.

The correction parameter is exactly `tamePrimeToTwoCorrectionExponent` for the same
normalized word and tame-inertia proof. The AST appends the inverse tau power. The defining
correction API proves its tau-power is the full tame defect and its maximal pro-two image
is trivial. It is a classically chosen profinite value, not a canonical numeric display.

`denote_pairSplice` and `denote_mobileSplice` include every alpha/r/p/h/j parameter in the
corresponding actual constructor. Their hypotheses include alpha≥1 and nonzero even q;
pair also requires j:Fin h. No hU/hD assumption is needed for **syntax equality**. The
stronger hypotheses for a normalized core or a full certificate (such as alpha≥2 and the
actual unit-head/D equation) remain in their existing producers and are not discharged by
exporting a template. Mobile h=0 is supported; pair h=0 has no legal j.

The generic `sourceEnvironment` intentionally maps all non-eta padic names to the same
indexed coefficient array and all profinite names to the correction value. The actual
factories use only `k`, `eta[0]`, and `correction`, so this permissive default does not weaken
the proved bridges; it is not a general parameter-name validation theorem.

`GeneralTemplateEval` additionally defines integer evaluation by direct AST recursion.
`Tree.evalZ_eq_denote` equates it with the existing PWord evaluator after exact binding.
`Tree.eval_eq_pinned` proves finite-target agreement when the nonzero common level kills
every target element. It does not compute or approximate arbitrary continuous parameters;
the resolver is applied to their exact denotations.

## One-tree serialization and provenance

`Tree.toJson` recursively traverses the same `Tree` passed to `Tree.denote`. Splice, tame
shadow, and shear are expanded by AST substitution, not represented by an unproved printer
macro. `pairPayload` and `mobilePayload` call those exact factories. The Python renderer
reads the resulting AST; its shared TeX aliases name repeated literal subtrees and do not
rewrite the hashed tree.

The staged hash includes the schema, complete symbolic tree, alphabet degree, family,
structural parameters, and the binding/bridge declaration names, under a new domain. It
does not touch frozen S1.1 hashes. It is a **template hash**, not a content hash of a fully
instantiated mathematical PWord: q, nuP, exact eta values, and the chosen correction value
are not serialized. A declaration name is also not a hash of that declaration's definition.
The final tooling adds a separate provenance sidecar hashing the five direct Lean source
files and the renderer. The sidecar is checked against their current bytes. Its declared
scope is direct sources only, not the transitive Lean dependency graph, toolchain, or a
complete reproducible-build identity; it does not change the meaning of the template hash.

There are two distinct validation levels:

1. `check` without a runner verifies grammar, exact JSON field sets, types, alphabet bounds,
   canonical filenames, the recomputed hash, direct-source sidecar, and the TeX rendering.
   The output explicitly labels this `artifact-only`. An arbitrary valid tree
   can be rehashed under the expected bridge-name string; this does not establish provenance.
2. `check --lean-runner /private/tmp/gq2-w360-lean.sh` re-emits the actual Lean factory at the
   recorded structural inputs and compares the entire envelope. This is the appropriate
   stronger mode for checking artifacts against the proved AST; the output explicitly labels
   it `Lean-replayed`. All four fixtures passed again after the final sidecar addition.

The CLI accepts general natural structural inputs; it does not certify alpha≥1/2, positive
selected r, the selected epsilon relation, or any field binding. One artifact fixes discrete
inputs and leaves continuous parameters symbolic. No single finite JSON tree quantifies
over every rank, and large factories have no proved resource bound.

## Remaining acceptance boundary

The staged mechanism is exact under the specified Lean environment bindings. It is not an
approved migration, a proof that arbitrary JSON parameter assignments yield certified
sources, or a substitute for specializations, Fox rows, Stokes, Hessian, polar matrices,
quadratic coordinates, and affine phase-cover certificates. Those mathematical components
remain separately checked and require an explicit compositional acceptance map.
