# W69: the classification on the `K(i)/K` unramified stratum

Lane W69-UNRAM.  New module `GQ2/Dyadic/Instances/EvenUnramified.lean`; no edits to existing
files.  Prefix `evenUnram`.

## 0.  Headline

The ticket's third option is the true one.  **The presented even cores do not cover the third
stratum.**  Precisely:

> **`evenUnram_imChiN_eq_prin_iff`**: for `alpha >= 2`,
> `imChiN a = evenRangePrin alpha  <->  (a <= 1 and alpha = 2)`,
>
> and `imChiM a` is never `evenRangePrin alpha` for `alpha >= 2`, at any `a`.

So the entire family of committed core images meets the third stratum in **one point**, on the
`N` row, at the *shifted* parameter `a = alpha - 1 = 1`.  Consequently, on the stratum at depth
`alpha >= 3`:

> **`evenUnram_classification_conclusion_false`**: the conclusion of
> `parityFinal_evenClassification`, stated verbatim, is FALSE.

That is a boundary result, not a gap: **the `hram` binder of the even classification is
necessary, not convenient.**  The campaign's theorem targets the two `q = 2` Labute families,
and the third stratum is exactly where `q >= 4`.

The module has **32** declarations; **31** carry an axiom pin, and all 31 pin inside the standard
three (two of them, `evenUnram_nWord_one` and `evenUnram_mWord_head`, to `[propext]` alone).  The
unpinned one is the `abbrev evenUnramKNegOne`.  No `sorry`, no new axiom, no `native_decide`, no
`maxHeartbeats`.  (Corrected from "All 31 declarations" by W72-HOUSE, watch round 9; the count
had equated "declaration" with "declaration carrying a `#print axioms` line", which drops the
`abbrev`.  The file also carries five comparison pins on other modules' declarations, one of
which, `parityFinal_evenClassification`, legitimately carries five census axioms.)

## 1.  What the stratum actually is

Wave 67's `evenRangeF_range_trichotomy` splits on whether the range meets the class `3 mod 4`.
The third branch is therefore, by construction, the locus

    range chi_cyc  <=  1 + 4 Z_2 ,

and the honest field-side entry condition is `i in K`, not unramifiedness of `K(i)/K`.  I landed
that direction, which the tree did not carry:

* **`evenUnram_range_le_prin_two_of_sqrt_neg_one`** - if `w in K` with `w^2 = -1` then every
  cyclotomic value on `G_K(2)` is `= 1 mod 4`.  Proof is `cyclotomicCharacter.spec` at `i`
  rather than at `zeta_8`: `chi(g) = -1 mod 4` would send `i` to `i^3 = -i`, but `g` fixes `K`.
* **`evenUnram_exists_range_eq_prin`** - with a marked reciprocity bundle, such a `K` sits on
  the third stratum at a depth `alpha >= 2` determined by `K`.

Arithmetically the depth is the largest `alpha` with `mu_{2^alpha} contained in K`, so
`q = 2^alpha` is the Demushkin invariant, and the stratum is the classical `q >= 4` case.  `K =
Q_2(i)` sits at `alpha = 2`, `Q_2(zeta_8)` at `alpha = 3`.

## 2.  Why the cores miss it, twice over

**From the image side (section 2 of the module).**  `imChiM a` contains `-1` unconditionally
(`neg_one_mem_imChiM`) and `evenRangePrin alpha` omits `-1` for `alpha >= 2`, so the `M` row
never meets the stratum, at any parameter.  On the `N` row, `nUnit a (1 + 2^a) = -1` gives

    nUnit a - 1 = (2 + 2^a) * nUnit a ,

so the exact level of `nUnit a` is `v_2(2 + 2^a)`, which is `1` for `a >= 2` (whence
`nUnit a = -1 mod 4`, and no principal unit is) and `2` at `a = 1`.  Two small facts fall out:

* `evenUnram_nUnit_zero_eq_one : nUnit 0 = nUnit 1` is **`rfl`** - the `Nat` subtraction in
  `onePlusTwoPow` truncates, so parameter `0` and parameter `1` are the same unit.
* `evenUnram_imChiN_one_eq_prin_two : imChiN 1 = evenRangePrin 2`, by exact-level generation.

**From the relator side (section 3).**  The `N` relator head is `a ^ (2 + 2^alpha)` and the `M`
head is `a^2` at every `alpha`.  A core can carry `q = 2^b >= 4` only if its head exponent is
that power, and

    evenUnram_head_eq_two_pow_iff :  2 + 2^a = 2^b  <->  (a = 1 and b = 2) .

So `DN 1 h` has relator `x0^4 [x0,x1] [x2,x3]` times handles - the `q = 4` Demushkin shape -
and nothing else in either family does.  The two sides agree: one point of overlap, at `q = 4`.

## 3.  What survives at `alpha = 2`, and what it costs

At the one matching depth the classification *statement* transports, at the shifted parameter,
and only there:

* `evenUnram_le_one_of_orientedN` - an oriented equivalence with `chiN a h` forces `a <= 1`.
* `evenUnram_eq_two_of_orientedN` - and forces `alpha = 2`.

The *proof* does not transport.  The `N` endpoint chain consumes `2 <= alpha` at five
independent leaves, and they are not bookkeeping:

1. `evenKernel_nUnit_add_one_dvd_four` (`nUnit alpha = -1 mod 4`) - **false at `alpha = 1`**,
   where `nUnit 1 = 5 mod 8`, so the derivation-kernel criterion's diagonal row fails.
2. `evenBridgeN_nUnit_modFour` (`nUnit alpha = 3 mod 4`) - the parity table, `kappa != 0`, the
   cup-adapted Frattini frame.
3. `nUnit_sq_sub_one` (exact level `alpha+1` of `nUnit alpha ^2`) - `1 + 2^{alpha-1}` is odd
   only for `alpha >= 2`.  Powers `evenRange_prin_le_imChiN`, the deep row supply, the digit
   layer.
4. `evenRawStageShift_n` - **documented false at `alpha = 1`** in its own file header
   (`StageAbstractionEvenRawSpan.lean:65`; the theorem is at `:625`): the head half
   `(2 + 2^1)/2 = 2` is even, so the diagonal atom drops out.
5. `isDemushkin_DN` via `diagCoeff_two_pow` - the Gram threshold.

And independently, the frame layer has nothing there: `nFrameExists_nonempty_iff` reads
`Nonempty (NFrame alpha h) <-> 2 <= alpha`.  I stated that obstruction in the form it takes on
this stratum, uniform in the depth:

> **`evenUnram_isEmpty_nFrame_of_orientedN`**: any core admitting an oriented equivalence with a
> third-stratum `G_K(2)` has an **empty** `N` frame.

So no transport of the wave-58 endpoint can reach `alpha = 2`.  Closing that point is a
different construction, not a re-parametrisation of this one.

**Cost estimate to close the `alpha = 2` point** (for the queue, not attempted here): a fresh
`q = 4` frame (the abelianization torsion there should be `Z/4`, not the `Z/2` that `NFrame`
demands), a fresh
Gram at head exponent `4` (alternating, not diagonal), and a replacement for the relator-shift
factorization at an even half-exponent.  Roughly one lane per item, three lanes, and the first
two are shared with residuals R1/R2 below.  Note this only reaches `q = 4`; `q >= 8` needs a
new core family, since no `2 + 2^a` is `8` or higher power of two.

## 4.  The orientation extractor the tree never had

Section 1 of the module lands the general fact that every even-lane consumer needed and none
stated:

> **`evenUnram_range_eq_of_oriented`**: `OrientedContinuousMulEquiv chiC chiG` gives
> `range chiG = range chiC`.

`OrientedContinuousMulEquiv` is a `ContinuousMulEquiv` plus `forall x, chiG (e x) = chiC x`, so
this is two lines; the point is that nothing committed had it.  Every `hrange` in the tree is
carried as a *separate hypothesis*, so no committed statement reads the image OFF a
classification.  With the extractor, the range identity is not only an input to the
classification but a consequence of it, and that is what turns a mismatched range into a
refutation of the classification statement.  (The converse direction stays false, and the tree
already says so: `inverseChiM_not_orientationMatches`.)

This is reusable outside this lane: any future "is `K` on branch M or N" question can now be
answered from a classification statement rather than only fed into one.

## 5.  Model field

`quadField (-1)`, that is `Q_2(i)`, named `evenUnramKNegOne`.  `quadField` is finite-dimensional
at every argument and consumes a non-square proof only for the degree computation, which nothing
here uses, so the field is available with no new arithmetic; `evenParity_sqrtIn_neg_one_sq` is
the committed square root.  This is the tree's **first named field on the third stratum**: none
of the five committed quadratic rows (`+-2, 5, +-10`) contains `i`, so all five are on the `M`
or `N` branch.

Landed there, over the field's own reciprocity bundle and the standing profinite instance
binders and nothing else:

* `evenUnram_exists_range_eq_prin_KNegOne` - the field is on the stratum.
* `evenUnram_isEmpty_orientedM_KNegOne` - no `M` core, at any parameter or handle count.
* `evenUnram_le_one_of_orientedN_KNegOne` - any `N` core is at `a <= 1`.

The last two hold **without pinning the depth**, which is why the field is cheap: pinning
`alpha = 2` exactly would need a cyclotomic value of exact level `2` at that field (a norm
computation in wave 68's style), and nothing above needs it.

## 6.  Even-route status prose, as I would now write it

The even route is closed as mathematics **at even degree with `K(i)/K` ramified**, and the
ramification hypothesis is now known to be **necessary**, not an artefact of the route.  The
committed statement of the even route should read:

> At every finite `K/Q_2` of even degree with `i not in K`, `G_K(2)` is oriented-isomorphic to a
> presented even core on the `M` or `N` branch at a depth `alpha >= 2` (`q = 2`).  At fields with
> `i in K` (`q = 2^alpha >= 4`) no presented core is oriented-isomorphic to `G_K(2)` once
> `alpha >= 3`, and at `alpha = 2` the only candidate is `DN 1 h`, for which the frame layer is
> empty.

Note the hypothesis is better stated as `i not in K` than as `K(i)/K ramified`: the two are not
equivalent, and it is the former that the trichotomy actually splits on (see section 7).

## 7.  Stale prose found, for the orchestrator

Three items.  I edited nothing; all are in committed files.

**(a) `EvenRangeModelFields.lean:826` (section 10 docstring) overclaims an `iff`.**  It reads
that the third case holds

> "exactly when `K(i)/K` fails to be ramified".

The committed theorem below it, `evenRangeF_hasEqualNormValueGroups_of_range_eq_prin`, proves
only *stratum implies unramified*.  The converse is **false**: if `K(i)/K` is unramified
quadratic then `i not in K`, so `chi mod 4` is the nontrivial character of `Gal(K(i)/K)`, a
quotient of `G_K(2)`, and the range meets the class `3 mod 4` - putting `K` on the `M` or `N`
branch, not the third.  Such `K` exist; `K = Q_2(sqrt(-5))` is one (`-5 = 3 mod 8` so `K/Q_2` is
ramified, `-5` is a square in `K` so `-1 = 5` mod squares, and `K(i) = K(sqrt 5)` is the
unramified quadratic extension).  Suggested repair: "exactly when `i in K`", which is what the
case split is, and which is also the `q >= 4` Demushkin locus.  The theorem statements are all
correct; only the docstring's "exactly when" is wrong.

**(b) `EvenDemushkin.lean:247`, residual R1, is stated in what looks like the wrong
direction.**  `EvenDemResidualAlphaOneN : forall h, not IsDemushkin 2 (DN 1 h)`, with the
reasoning "the head exponent is `2 + 2^1 = 4 = 0 mod 4`, so its Gram diagonal entry dies and the
mod-2 quadratic initial form degenerates".  A dying *diagonal* entry does not degenerate the
form: it makes it alternating.  `DN 1 h` has relator `x0^4 [x0,x1] [x2,x3]` times handles, whose
mod-2 cup form is the hyperbolic form - **nondegenerate**.  On the arithmetic side `DN 1 0`
should be `G_{Q_2(i)}(2)`, which is Demushkin with `q = 4`.  So R1 is very likely refutable
rather than provable, and its corroboration `evenDem_nFrame_isEmpty_alphaOne` is evidence for
`q = 4` (the abelianization torsion is `Z/4`, not `Z/2`, which is exactly "the torsion generator
in the wrong place" that the frame demands) rather than evidence against Demushkin-ness.  This
is a claim about an unformalised residual `Prop`, so it is a queue item, not a correction I can
land; but the residual's *stated direction* should be flipped before a lane is spent on it.

**(c) `EvenParityModel.lean:85-91` (the section 1 docstring) is now understated, not wrong.**
It says `Hfam` holds "with no hypothesis beyond the degree parity and `alpha >= 1`".  True, and
this lane makes the `alpha >= 1` significant rather than incidental: `Hfam` and the parity supply
already reach the surviving point `alpha = 1`, so they are not what blocks the `alpha = 2`
stratum.  Worth a sentence pointing at the five leaves in section 3 above, so a future lane does
not re-derive that the supplies are fine.

## 8.  Declarations landed

Section 1 (extractor, 2): `evenUnram_range_eq_of_oriented`,
`evenUnram_isEmpty_oriented_of_range_ne`.

Section 2 (which core images are principal, 11): `evenUnram_nUnit_zero_eq_one`,
`evenUnram_imChiN_zero_eq_one`, `evenUnram_nUnit_one_sub_one`,
`evenUnram_imChiN_one_eq_prin_two`, `evenUnram_imChiN_zero_eq_prin_two`,
`evenUnram_imChiM_ne_prin`, `evenUnram_notMem_prin_of_add_one`, `evenUnram_imChiN_ne_prin`,
`evenUnram_prin_two_ne_prin`, `evenUnram_imChiN_ne_prin_of_three_le`,
`evenUnram_imChiN_eq_prin_iff`.

Section 3 (head exponent, 3): `evenUnram_head_eq_two_pow_iff`, `evenUnram_nWord_one`,
`evenUnram_mWord_head`.

Section 4 (the verdict, 6): `evenUnram_isEmpty_orientedM`, `evenUnram_isEmpty_orientedN`,
`evenUnram_no_presented_core`, `evenUnram_classification_conclusion_false`,
`evenUnram_le_one_of_orientedN`, `evenUnram_eq_two_of_orientedN`.

Section 5 (frame obstruction, 1): `evenUnram_isEmpty_nFrame_of_orientedN`.

Section 6 (field side, 5): `evenUnram_toZModPow_two_eq_one_of_sqrt`,
`evenUnram_range_le_prin_two_of_sqrt_neg_one`, `evenUnram_exists_range_eq_prin`,
`evenUnram_isEmpty_orientedM_of_sqrt`, `evenUnram_le_one_of_orientedN_of_sqrt`.

Section 7 (model field, 3 plus the abbreviation `evenUnramKNegOne`):
`evenUnram_exists_range_eq_prin_KNegOne`, `evenUnram_isEmpty_orientedM_KNegOne`,
`evenUnram_le_one_of_orientedN_KNegOne`.

Section 8: axiom pins, the 31 statements printed beside `parityFinal_evenClassification`,
`evenRangeF_range_trichotomy`, `evenRangeF_hasEqualNormValueGroups_of_range_eq_prin`,
`evenRange_range_eq` and `evenDem_nFrame_nonempty_iff`.  All 31 are
`[propext, Classical.choice, Quot.sound]`; two are `[propext]` alone.

## 9.  Queue items this lane produces

1. **Flip residual R1's direction** (`EvenDemushkin.lean:247`) and, if the flip is right, prove
   `IsDemushkin 2 (DN 1 h)` by the alternating Gram.  This is the first half of closing the
   `alpha = 2` point, and it is shared with R2.
2. **The `q = 4` frame.**  `NFrame` demands `Z/2 + Z_2^{3+2h}`; the `alpha = 1` abelianization is
   `Z/4 + Z_2^{3+2h}`.  A `q`-parametrised frame would serve both R1 and the stratum.
3. **Fix the section 10 docstring** to "exactly when `i in K`".
4. **Decide whether the campaign wants `q >= 8` at all.**  No `2 + 2^a` is a power of two above
   `4`, so `Q_2(zeta_8)` and beyond need a new core family; the boundary theorem here says the
   present families provably cannot be stretched to cover them.
