# W362-HOUSE lane note

Lane: housekeeping and audit, first Claude wave after the Codex handoff.
Worktree: `/Users/roed/claude/cla/worktrees/w362-house`, branch `claude/w362-house`.
Base: `6770a87e` ("checkpoint the verified W361 state left uncommitted by the
Codex handoff").

## Runtime facts (verified at base 6770a87e)

- Toolchain pin: `leanprover/lean4:v4.31.0-rc2` (`lean-toolchain`).
- `.lake/build` is a symlink to `/Users/roed/claude/cla/work/main-build-cache`.
- `.lake/packages` is a symlink to
  `/Users/roed/claude/gq2-paper/formalizations/gq2-claude/.lake/packages`.
- Lean checks in this lane use `bash scripts/w361_lean_runner.sh <file>` only.
  No `lake` invocation of any form, and no `scripts/check_dyadic.sh`.

## Tickets

- T1 verify the handoff's headline claims against the tree.
- T2 index the 71 `docs/dyadic/w36*` documents.
- T3 hygiene: ignore `tmp/` and `output/`.
- T4 draft the restartable W362 handoff skeleton.

## Log

(Entries appended as the lane runs.)

- Lane opened. First commit banked before any investigation.

## T1 findings (as of base 6770a87e)

### Verified

1. **The eleven N modules exist and are all directly imported by `GQ2.lean`.**
   `FreeProTwoMatrixBasis`, `NBasisRowRefinement`, `NBasisRelativeRefinement`,
   `NBasisExactStages`, `NFullFrameCompactness`, `NFullFrameStageTransfer`,
   `NBasisFullFrameLift`, `NFrameMatrixLift`, `NInitialCupDepth`,
   `NFrameCupCoordinates`, `NFullStabilizerLift`, all under
   `GQ2/Dyadic/MarkedCore/`.

2. **118 pins, and the per-module table in handoff section 4 is exact.**
   `#print axioms` counts per module are 19/6/1/2/7/4/4/30/30/9/6, matching the
   handoff's column line for line; total 118. Independently, the eleven modules
   contain exactly 118 public declarations and 7 private ones, and the pin set
   is in one-to-one correspondence with the public set: no public declaration
   is unpinned and no pin names a non-declaration.

3. **The two durable verification reports hash exactly as claimed.**
   `docs/dyadic/w361-claude-code-verification-report.json` is
   `aad5d041ec098c6f1d5dc0b8e24953322afdff2073a20a133a79e67e9f1a3711` and
   `docs/dyadic/w361-final-verification-report.json` is
   `bb20e9914dd86be093521808b0267f8ac0f6cd857fe6e13b8285d8213784abcb`,
   both as stated in handoff section 5.

4. **The base commit records the verified source state byte for byte.**
   Recomputing the verifier's own `local_source_set_sha256` (the canonical
   JSON digest of the `{module: sha256}` map over the `GQ2` import closure,
   `scripts/w361_verify_fresh.py:67` and `scripts/w361_fresh_build.py:141`)
   from the tree at `6770a87e` gives
   `34477d1c4c082aadda64e4a855ba66679765d486db8084fe931ed3b86e36e6dc`,
   identical to the handoff's "current verified source-set SHA-256". The
   checkpoint therefore carries no drift from the state the Codex replay bound.

5. **Registration is complete (T1e).** Of the 1,558 `.lean` files (root
   `GQ2.lean` plus 1,557 under `GQ2/`), the import closure of `GQ2` contains
   1,552. The six outside it are exactly `GQ2/AxiomLedger.lean` and the five
   exporter drivers `GQ2/Dyadic/Word/General{Fox,PhaseCover,Phase,,LN}...Export.lean`.
   No other file is unregistered. The handoff's arithmetic
   (1,557 = 1,551 + 1 + 5; closure = 1,551 + root = 1,552) is exact.

   Method note for future lanes: this tree uses Lean 4.31 module-system
   imports. 427 import lines are spelled `public import`, and a scan that
   matches only `^import ` misses 18 modules and reports 24 unregistered files
   instead of 6.

6. **The statements have exactly the shape the handoff states (T1b).**
   `GQ2/Dyadic/MarkedCore/NFullStabilizerLift.lean:46`:

   ```lean
   theorem nFullStabilizer_lift {alpha h : ℕ} (ha : 2 ≤ alpha)
       (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h))
       (hchi : ∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z)
       (hcup : NFrameCupIsometry ha phi) :
       ∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
         (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
         (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))
   ```

   and `:81`, the same two hypotheses as an iff with that existential:

   ```lean
   theorem nFullStabilizer_lift_iff {alpha h : ℕ} (ha : 2 ≤ alpha)
       (phi : ContinuousMulEquiv (NFrameModel h) (NFrameModel h)) :
       (∃ Psi : ContinuousMulEquiv (DN alpha h : Type) (DN alpha h : Type),
         (∀ x, chiN alpha h (Psi x) = chiN alpha h x) ∧
         (∀ x, nPhiHom ha h (abMk (Psi x)) = phi (nPhiHom ha h (abMk x)))) ↔
       (∀ z, nFrameOrientation ha h (phi z) = nFrameOrientation ha h z) ∧
         NFrameCupIsometry ha phi
   ```

   Both quantify `{alpha h : ℕ}` with `ha : 2 ≤ alpha` and no constraint on
   `h`, so "every alpha >= 2 and every handle count h" is exact. The three
   supporting claims also hold:

   - `NFrameModel h` is `Multiplicative (ZMod 2 × ℤ_[2] × ℤ_[2] × ℤ_[2] ×
     (Fin (2 * h) → ℤ_[2]))` (`GQ2/Dyadic/MarkedCore/N.lean:177`), which is
     the claimed `Z/2 × Z₂³ × Z₂^(2h)`.
   - `NFrameCupIsometry` (`NFrameCupCoordinates.lean:31`) quantifies
     `∀ c d : ContinuousMonoidHom (NFrameModel h) (Multiplicative (ZMod 2))`,
     so it genuinely ranges over every continuous F₂ character including the
     torsion one. It carries no orientation and no identity-handle condition.
   - `nFrameOrientation_preserved_iff` exists (`NFrameMatrixLift.lean:106`)
     and is exactly the claimed equivalence with preservation of the integral
     b-coordinate.

7. **All 118 N pins are registered in the 691-pin artifact audit.**
   `scripts/w361_artifact_axiom_audit.lean` lists 691 names, all distinct, 388
   of them under `MarkedCore`. Resolving each of the eleven modules' 118 pins
   against that list under the module's own namespace leaves zero unmatched.

8. **Census eleven, at source level (T1d).** Exactly eleven `axiom`
   declarations exist in the tree, all in `GQ2/Foundations/Axioms.lean` (lines
   104, 124, 165, 178, 204, 231, 259, 300, 359, 388, 433). Their names are set
   equal to `GQ2.AxiomLedger.bAxioms`, and `scripts/check_axioms.sh:28` sets
   `EXPECTED_AXIOMS=11`. Two further `^axiom ` grep hits, in
   `GQ2/EvensKahnDerived.lean:32` and
   `GQ2/Dyadic/Instances/EvenRouteModel.lean:55`, are docstring prose that
   line-wrapped onto the word.

9. **The general endpoint is exported where the handoff says (T1c).**
   `GQ2/Dyadic/GeneralMain.lean:54` opens `namespace GQ2.Dyadic`, `:67`
   `export`s `Instances.FieldFamilySpliceOriginalMarked`, and `:79` pins
   `hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`. So the short name
   the handoff gives, `GQ2.Dyadic.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`,
   is real; the underlying declaration is
   `GQ2.Dyadic.Instances.FieldFamilySpliceOriginalMarked.hasSelectedOriginalMarkedWordPresentationRN_ramifiedI`,
   which is the spelling `scripts/w361_general_axiom_audit.lean` audits. The
   driver's expected footprints are literal: `standardAxioms` (3),
   `suppliedFieldAxioms` (3 + 6) and `canonicalFieldAxioms` (3 + 6 + 3 = the
   standard three plus nine), over 16 declarations, failing on an extra **or**
   a missing dependency. That matches the handoff's trust-boundary paragraph
   exactly. Elaborating it is queued behind the concurrent umbrella build.
