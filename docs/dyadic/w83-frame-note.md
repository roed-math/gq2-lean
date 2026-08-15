# W83-FRAME lane note

Lane target: the odd classification's last input, one cup-adapted Frattini frame per
odd-degree field, in the exact form wave 82 left it (`SqMarkedForwardSupply B h` equivalent to
one cup-adapted frame with the improved relator and the two nu-rows). Ticket source:
`docs/dyadic/w82-seam-note.md`. New module: `GQ2/Dyadic/Instances/OddFrame.lean`, prefix
`oddFrame`, based at `23041e0f`; gen'd green against the mirror. No new axiom, no sorry, no
native_decide; `B` is a binder in every pin (no B5, no B5-K).

## T1: the form at odd degree (DONE, all measured pins in the module's section 6)

`H^1(G_K(2), F_2)` has odd dimension `2h + 3` (`oddFrame_card_H1`, std-3 + {B6, B7}). The odd
normal form `<1> perp H perp H^h` (the improved relator's quadratic initial Gram, `<1>`-slot at
`x1`, first plane at `(sigma, x0)`) is REALIZED by actual frames at every odd-degree K
(`oddFrame_isCupAdapted_exists`, repackaging `oddDegreeSqCyclotomicFrattiniFrameSupply_holds`
at the field's own h): the committed normal-form machinery covers the odd-dimensional case and
no odd companion was needed. The radical is trivial and the form is non-alternating with
Labute diagonal `b(kappa, x) = b(x, x)`.

The shape of the unramified class nu-bar against EVERY cup-adapted frame, each std-3 + {B6,
B11a} only:

- `oddFrame_nuRow_x1_of_isCupAdapted`: the `x1`-row vanishes (kappa-side sharp identity plus
  the committed isotropy `nuUrKappaCupZero_of_odd`).
- `oddFrame_nuRowSum_of_isCupAdapted`: the `sigma`-row and `x0`-row SUM to 1 (omega-side sharp
  identity plus `nuUrOmegaCupOne_of_odd`, the Hilbert value `(2, u)_K = -1` at odd `e`).
- `oddFrame_nuRow_dichotomy_of_isCupAdapted`: so the two selected mod-2 rows are `(1, 0)` or
  `(0, 1)`, never `(0, 0)` or `(1, 1)`.
- `oddFrame_nu_notin_kappaTau_span`: nu-bar is independent of `span{kappa, tau}`; the
  ramified-i clause is automatic at odd degree.

## T2: the frame, and the discovery (the seam's cost moved to the model side)

- **Unconditional half** (`oddFrame_presenting_relator_rowSum`): the presenting frame of the
  unconditional oriented equivalence is cup-adapted, kills the improved relator GLOBALLY, and
  carries the two mod-2 rows correct up to ONE shared bit (row sum 1, x1-row 0). {B1, B6, B7,
  B11a}.
- **The discovery** (`oddFrame_isUnit_transported_sqPivot`, std-3 + {B1, B6, B11a}): the pivot
  exponent `sqPivotExp` is a unit, so the parity of the transported pivot row IS the nu-bar row
  sum, and T1 pins that sum to 1. Hence at EVERY oriented equivalence the transported marking's
  pivot row is a unit, unconditionally. This is exactly the input
  `SqCore.SqNuOrientedClearAtUnitPivot h` consumes and exactly the input
  `GammaLOddDegreeBridge` section 9 proved no choice of f and no model automorphism can
  manufacture; the cup form manufactures it. Until now the clearing was known to suffice only
  TOGETHER with the supply's own rows (BridgePivot consumed both); the supply half is now free.

## T3: acceptance (all {B1, B6, B7, B11a} unless noted)

- `oddFrame_supply : SqCore.SqNuOrientedClearAtUnitPivot h -> SqMarkedForwardSupply B h` at
  every `[K : Q2] = 2h + 1` over bundle + filtration alone. The named residual Prop is
  therefore the MODEL-side clearing: a statement about `D_sq(h)`, `chi_sq`, `nu_sq` and
  continuous automorphisms, with no field, no bundle, no frame and no cup form in it.
- `oddFrame_supply_iff_clearInstance` (std-3 EXACTLY): for any fixed oriented f the seam is
  equivalent to the clearing's single instance at the transported marking. So the clearing
  overshoots the seam by its marking quantifier exactly as `SqCupAdaptedFrameRelator K`
  overshoots it by its frame quantifier; the seam is the instance at the one marking the cup
  form has already vetted.
- `oddFrame_supply_of_families`: handle stratum (`SqHandleMixFixesCore h sqPivotExp`) plus the
  two one-parameter pivot families (`SqPivotTranslation`, `SqPivotScaling`) buy the whole seam:
  the graded lanes' open moves now have the odd row as their direct payoff.
- Consumers over the clearing alone: `oddFrame_fullMarking_of_clear`,
  `oddFrame_cupAdaptedFrame_of_clear` (the ticket's frame with EXACT rows),
  `oddFrame_genAsmBranch_L_of_clear`, `oddFrame_realization_of_clear`,
  `oddFrame_candidate_equiv_galK_of_clear` (the general theorem needing exactly
  `GenAsmFieldInputs` + `GenAsmRowResidual`).
- **n = 1 sanity**: `oddFrame_clearAtUnitPivot_zero` proves the clearing at `h = 0` (std-3 +
  {dyadicOrientation, peripheralCyclotomicAction}, riding the committed degree-one pivot
  seeds), so `oddFrame_supply_degreeOne` reproves the committed floor; the stress pins land
  both routes on the same statement and feed the supply back through
  `oddSeam_supply_iff_cupAdaptedFrame`.

## Where the seam now sits

One Prop, unchanged in name: `SqMarkedForwardSupply B h` at `h >= 1`. Its cheapest producer is
NO LONGER frame-shaped: it is the model-side `SqCore.SqNuOrientedClearAtUnitPivot h`
(PivotClimb section 8, the strongest unrefuted statement of its shape), which needs no
arithmetic input anymore. The K-side arithmetic is complete: rows-up-to-a-bit and the unit
pivot are theorems. The remaining distance is entirely inside `D_sq(h)`: produce the
chi-preserving automorphism correcting a jointly-surjective unit-pivot marking onto `nu_sq`,
or equivalently discharge the two pivot families plus the handle stratum
(`oddFrame_supply_of_families`), which are the graded lanes' open moves (the W73 x1-bracket
question).

## What W84 needs

1. **The model clearing at `h >= 1`**: `SqNuOrientedClearAtUnitPivot h`, or its family inputs
   `SqPivotTranslation h c` / `SqPivotScaling h a` / `SqHandleMixFixesCore h sqPivotExp`. This
   is now the ONLY producer gap on the odd row's structural side, and it is a pure `D_sq(h)`
   statement; the graded-move machinery (W70-W74) is the standing attack.
2. **The record blocks at the L row** (unchanged from W82): ASK exactLifting + stokes wiring,
   the determinant wiring flagged by W79-HOUSE, and the CAND `WordCertificate` over `D_sq h`.
3. **Housekeeping**: register `GQ2.Dyadic.Instances.OddFrame` in `GQ2.lean` (this lane does
   not edit it). The pessimistic remark in `GammaLOddDegreeBridge` section 9 ("the model-side
   supply list cannot produce the unit pivot, so the bridge genuinely needs P3's supply") is
   now stale in its second half: `oddFrame_isUnit_transported_sqPivot` produces the unit pivot
   from the cup form, so the supply is not needed as an input there. Similarly
   `GammaLOddDegreeBridgePivot`'s consumers that take `hclear` AND `hsupply` together can be
   re-cut over `hclear` alone through `oddFrame_supply`.
