# W78-UNIMOD: the last clause on the five quadratic branch data

Lane W78-UNIMOD, ticket `docs/dyadic/w77-field-note.md` §7 item 1.  Produced against tree
`e6bbd2b9` on branch `claude/w78-unimod`, shared cache at the wave-77 umbrella (4348 jobs).
Verification of record: `scripts/mirror.sh` (sweep, gen, check).  **No `lake` command was run.**

One new module: `GQ2/Dyadic/Instances/FieldUnimodularity.lean`, declaration prefix `fieldUni`.
Nothing else was touched.

---

## 1.  The headline

**The residual clause is not a separate hypothesis from the level: it IS the level.**  At
`alpha >= 2` and `h = 0`, on every oriented equivalence, at every `K`:

> `hpivot` (M row) `<-> B.r = 0` and `hpair` (N row) `<-> B.r = 0`
> (`fieldUni_pivotM_iff_level_zero`, `fieldUni_pairN_iff_level_zero`)

and the level is then discharged, or shown to be the wrong question, per field:

| row | field | level | landed |
| --- | --- | --- | --- |
| `sqrtNegTwo` | `Q2(sqrt -2)` | `r = 0` | **`fieldUni_genAsmBranch_sqrtNegTwo`, no clause** |
| `sqrtTwo` | `Q2(sqrt 2)` | `r = 0` | **`fieldUni_genAsmBranch_sqrtTwo`, no clause** |
| `sqrtFive` | `Q2(sqrt 5)` | `r = 0` | over `fieldUni_TwoIsUniformizer KSqrtFive`, one Prop |
| `sqrtTen` | `Q2(sqrt 10)` | `r = 1` | clause restated as the level; **the row is wrong** |
| `sqrtNegTen` | `Q2(sqrt -10)` | `r = 1` | same |

So T3 (acceptance) lands on **two** of the five rows outright, on a third over one named
unramifiedness Prop, and is **refuted** on the remaining two, where the correct conclusion is
that wave 77 put those fields on the wrong row.

## 2.  T1: what `B.r` is, and where it is zero

`B.r` is a **field of the bundle** (`MarkedRecipBundle.lean:598`), not a derived quantity, and
the campaign instantiates no bundle at any field: everything is parametrized by
`B : MarkedRecip R K`, with `GQ2.markedRecipAt` landing only at the census flip.  So "prove
`B.r = 0` at this field" cannot mean "exhibit an instance with `r = 0`"; it means **derive
`B.r = 0` from the bundle's own clauses at that `K`**.  That is possible because the two level
clauses pin `r` uniquely (`nu_ur(ker chi) = 2^r Z_2`, and `2^r Z_2 = 2^s Z_2` forces `r = s`).
The usable half is `nu_ker_chi_le`:

> one `g` with `chi(g) = 1` and `nu_ur(g)` a **unit** forces `r = 0`
> (`fieldUni_level_eq_zero_of_chiKer`, the `bot_level_eq_zero` argument with the witness
> abstracted out; and `fieldUni_level_eq_zero_of_chiKerTwo` on `G_K(2)`).

Through `rec_K` the two conditions read off `Kx` (`fieldUni_level_eq_zero_of_decomp`):

* `chi_K(rec_K x) = 1` exactly when `N_{K/Q2}(x)` is a power of `2` with unit part **`1` on the
  nose** (norm functoriality plus the base bundle's clauses (c) at units and at the uniformizer:
  `fieldUni_chi_recip_of_norm`).  Not "`1` mod `8`": the value is the unit part inverted, and it
  has to be the identity.
* `nu_ur(rec_K x) = ofAdd(-1)` when `x` is a spectral unit times a uniformizer
  (`nu_ur_recip_of_decomp`, already in the tree).

### 2.1  The two ramified rows: proved

| field | `x` | `N(x)` | decomposition |
| --- | --- | --- | --- |
| `Q2(sqrt -2)` | `sqrt -2` | `0 - (-2) = 2` | `x = 1 * sqrt -2` |
| `Q2(sqrt 2)` | `2 + sqrt 2` | `4 - 2 = 2` | `x = (1 + sqrt 2) * sqrt 2` |

The `Q2(sqrt 2)` row needs the factorization: `sqrt 2` alone has norm `-2`, unit part `-1`, so it
is not in `ker chi`; `2 + sqrt 2` is, and it is `(1 + sqrt 2) * sqrt 2` with `|1 + sqrt 2| = 1`.

The missing input both rows needed, and which this lane supplies, is that **`sqrt a` is a
uniformizer of `Q2(sqrt a)` when `v(a)` is odd and `|a| = |2|**` (`fieldUni_sqrtIn_max`): the
spectral maximality half of the B13 spec, without which `nu_ur_recip_uniformizer` is vacuous at
the field.  It comes straight out of `Fields.lean` §4's separation lemma
(`norm_ne_norm_mul_sqrtIn`, `norm_add_mul_sqrtIn`) plus one discreteness step (a scalar of norm
`> 1` has norm at least `2`).  `Fields.lean` §4 built that machinery for `qOf_quadField`; this is
its second consumer.

Results: `fieldUni_level_sqrtNegTwo`, `fieldUni_level_sqrtTwo`, both over the field's own bundle
and the standing instance binders, both at the standard three axioms.

### 2.2  `Q2(sqrt 5)`: reduced to unramifiedness, and that is sharp

At the unramified row **no** norm computation can meet the criterion: `f = 2` there, so
`v_2(N x) = 2 v_K(x)` is always even, and an element of odd valuation never has a norm that is a
power of `2`.  What replaces it is the scalar `2` itself: `N_{K/Q2}(2) = 2^[K:Q2]` has unit part
`1` at every `K`, so `rec_K(2)` is always in `ker chi`, and its `nu`-value is a unit exactly when
`2` is a uniformizer.  Hence the clean general theorem

> **`fieldUni_level_eq_zero_of_twoUniformizer`: `K/Q2` unramified implies `B.r = 0`.**

This is the even-degree companion of `MarkedRecip.level_eq_zero_of_odd_finrank` (which corrects
`rec(pi)` by a scalar solving `w^n = chi(rec(N pi))`, unsolvable at even `n`), and it is cheaper:
no scalar correction at all.

So `Q2(sqrt 5)` costs exactly one Prop, `fieldUni_TwoIsUniformizer KSqrtFive`, i.e.
`forall z in K, z /= 0, |z| < 1 -> |z| <= |2|`.  **The tree does not carry it.**  All of
`Fields.lean` §4 runs under `Odd a.valuation`, false at `a = 5`; `Fields.lean:243`'s `q_K = 4` is
a docstring remark with no theorem behind it (contrast `qOf_KSqrt{NegTwo,Two,Ten,NegTen}`, which
are theorems).  Closing it is a self-contained follow-up: for `a = 5` the norm form
`t^2 - 5 u^2` has even valuation always, because `t'^2 - 5 u'^2 = -4 mod 8` when both are units.

### 2.3  `Q2(sqrt 10)` and `Q2(sqrt -10)`: the level is **one**, and the row is wrong

Two independent arguments, both hand computations, neither formalized here:

**(a) Field theory.**  `sqrt 10 * sqrt 2 = 2 sqrt 5`, so `sqrt 5` lies in `K(mu_8)`; likewise
`sqrt -10 * sqrt 2 = 2 sqrt -5` and `i * sqrt 5 = sqrt -5`, so `sqrt 5` lies in `K(mu_8)` there
too.  `Q2(sqrt 5)/Q2` is the unramified quadratic extension and `sqrt 5` is not in either field,
so `K(sqrt 5)/K` is an unramified quadratic subextension of `K(mu_{2^infty})/K`, whence
`nu_ur(ker chi) = 2 Z_2` and `r = 1` exactly.

**(b) Norms.**  `2^k` is a norm from `Q2(sqrt 10)` only for even `k`: `(2, 10)_2 = -1`, checkable
by hand (`a^2 - 10 b^2 = 2` and `= 8` are both insoluble mod `8`).  Same at `-10`.  So no element
of odd valuation has a norm whose unit part is `1`, which by §2 is what `r = 0` would require;
and the density argument (`rec` has dense image, `chi` and `nu` are continuous, `G_K^ab` is
compact) closes the gap between elements and limits.

**The tree already agrees.**  `Main.lean:136` and `:137` put those two fields on
`.Mpc 2 1 false 1` and `.Mpc 2 1 true 1`, and `FieldBranchSelector`'s `Matches` for an `.Mpc beta
r eps eta` row demands `r = Q.r`, i.e. `B.r = 1`, while its `.M0 beta` clause demands `Q.r = 0`.
By §1 of this lane, wave 77's `fieldId_genAsmBranch_sqrt{Ten,NegTen}` hypothesis is exactly
`B.r = 0`.  Both cannot hold.  The frozen table is the older and better attested of the two, and
the field theory in (a) confirms it: **wave 77's two `M0 2 0` branch data for `Q2(sqrt 10)` and
`Q2(sqrt -10)` are on the wrong row and their remaining clause is unsatisfiable.**

Nothing here refutes wave 77's *range identity* at those fields (`fieldId_hrange_sqrtTen`,
`_sqrtNegTen`: `range chi = imChiM 2 = top`); that is unaffected and stays true.  What is wrong is
only the last step, the branch datum built at `pres = .M0 2 0`.  The right target there is
`pres = .Mpc 2 1 _ .one 0`, which needs a *procyclic* producer: neither
`genAsm_branch_of_evenM` nor the level-zero producer of §2 below builds one, and the tree has no
`marked_matching_certificate` for the `Mpc` shape at all.  That is a new, correctly-scoped ticket.

## 3.  T2: the level-zero producers

`fieldUni_genAsmBranch_of_orientedM_level_zero` and `..._orientedN_level_zero`: the analogues of
`GeneralAssembly.genAsm_branch_of_even{M,N}` routed through
`marked_matching_certificate_KTwo{M,N}_of_level_zero`.  Two differences from the committed pair:

* the `MDecomposition`/`NDecomposition` binder is discharged from the tree's own existence
  theorems (`mFrameExists_mDecomposition`, `nFrameExists_nDecomposition`), so it is not a new
  input; and
* `hMix` disappears on the `M` side, the level-zero certificate producer having no such binder
  (its B8 transport supplies the M3 unit scaling instead).

Inputs left: the degree pin, the oriented equivalence, and `B.r = 0`.  Both are `h = 0` only,
which is where all five frozen rows sit.

## 4.  T3: the five rows after this lane

* `fieldUni_genAsmBranch_sqrtNegTwo : exists G : GenAsmBranch KSqrtNegTwo B, G.pres = .N0 2 0`
  and `fieldUni_genAsmBranch_sqrtTwo : ... G.pres = .M0 3 0`.  **No clause.**  Over the field's
  own bundle `B` and the standing instance binders, nothing carried.
* `fieldUni_genAsmBranch_sqrtFive_of_unramified`, over `fieldUni_TwoIsUniformizer KSqrtFive`.
* `fieldUni_level_zero_of_hpivot_sqrt{Five,Ten,NegTen}`: wave 77's clause at wave 77's chosen
  equivalence, restated as the level equation it is.

### What the two clause-free records still need

On the selector side: **nothing**.  The branch datum is the whole selector half of the general
statement at those two rows, and it is now unconditional.  What remains for a complete
`GenAsmRowResidual` at `Q2(sqrt -2)` and `Q2(sqrt 2)` is the two blocks of
`GeneralAssembly.lean:277` and nothing else:

* **ASK**, the arithmetic counting pack at `galKProfinite K`: `exactLifting` (ledger field 3),
  `stokes` (field 4), `determinant` (field 6, the Gauss-`Z` residue, the memo's sharpest open
  item, with no `K` clone and no owner lane).  Ledger field 5 stays discharged by
  `KSupply.scalarHilbert_galK`.
* **CAND**, the candidate-side `WordCertificate` over the row's own slot.  At `Q2(sqrt 2)`
  (`M0 3 0`) the four-clause producer `Instances.MCompactCore.mWordCertificate` covers free
  `(alpha, h)`; at `Q2(sqrt -2)` (`N0 2 0`) `SqrtNeg2.sqrtNegTwoWordCertificate` covers exactly
  that pin.

So on the two rows this lane closed, both remaining blocks are the *general* residual blocks, not
anything field-specific or classification-specific.

## 5.  Axiom pins

Recorded in the module's §6, printed beside the committed statements they inherit from.

* Every level statement (§1's two equivalences, §3's criterion, the quadratic uniformizer, §4's
  unramified reduction, and both fields' level equations) is at `propext, Classical.choice,
  Quot.sound`.  The arithmetic discharged here costs **no** axiom.
* `fieldUni_genAsmBranch_sqrtNegTwo` is at the standard three plus the even route's endpoint set
  (`hilbertSymbol_normCriterion_finiteDyadic`, `tateDualityAt`,
  `Foundations.absGalQ2_isTopologicallyFinitelyGenerated`,
  `Foundations.absGalQ2_localEulerCharacteristic`), i.e. **exactly** the set of wave 77's
  `fieldId_genAsmBranch_sqrtNegTwo`.  Removing the clause added nothing.
* `fieldUni_genAsmBranch_sqrtTwo` and `_sqrtFive_of_unramified` carry `peripheralCyclotomicAction`
  in addition, from `marked_matching_certificate_KTwoM_of_level_zero`.  Wave 77's `M`-row data
  carry the same axiom (there through `mMixHypothesis`), so the split is unchanged.

No `sorry`, no new axiom, no `native_decide`, no `maxHeartbeats`, no `maxRecDepth`.

## 6.  What is next

1. **`fieldUni_TwoIsUniformizer KSqrtFive`** (small, self-contained): `v_2(t^2 - 5 u^2)` is always
   even, because `t'^2 - 5 u'^2 = -4 mod 8` at units.  Closes the third row.
2. **The two procyclic rows** (new ticket): the tree has no marked-core certificate producer for
   the `Mpc` shape, so `Q2(sqrt 10)` and `Q2(sqrt -10)` have no branch-datum route at all once
   the `M0` route is seen to be the wrong row.  This is a genuine gap that wave 77's framing
   hid, and it is the natural successor to this lane.
3. **Wave 77's §5/§7 should be superseded at the merge** on the two procyclic rows only:
   `fieldId_genAsmBranch_sqrtTen` and `fieldId_genAsmBranch_sqrtNegTen` are true theorems with
   unsatisfiable hypotheses, and the note's claim that all five rows reduce "to one unimodularity
   clause" holds only for the three rows treated in §2.1 and §2.2 above.
