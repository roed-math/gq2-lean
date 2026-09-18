# W362-MCUP lane note

Lane: M full-stabilizer lifting, step 4 of 5 (initial depth-three and cup
comparison adapter at M). Branch `claude/w362-mcup`, base `6770a87e`.

Route item 4 of `docs/dyadic/w361-m-next-general-scaffold.md`.

Targets:

- T1 the semantic M full-frame cup isometry predicate and its exact reduced
  coordinate consequence (twin of `NFrameCupIsometry` / `NFrameCupCoordinates`);
- T2 the initial depth: full cup preservation plus a fixed `T = A*C^m` head
  forces the actual `mRelWord` error into lambda-three;
- T3 the converse ingredient through `dmObs`.

Status: in progress. Log below records what has actually been verified with
`scripts/w361_lean_runner.sh`, not intentions.

## Log

- Lane opened. Reading the N templates and the actual M word/frame interfaces.
- `GQ2/Dyadic/MarkedCore/MInitialCupDepth.lean` VERIFIED with
  `bash scripts/w361_lean_runner.sh`, nine declarations, every one std-3
  (`propext`, `Classical.choice`, `Quot.sound`). T2 is closed:

  - `mCupSq_eq_of_zLayer`, `mCupSq_levelMk_eq_of_mem_two` -- a square in the
    class-two quotient depends only on the class of its base modulo lambda-two;
  - `mCupPow_eq_one` -- for `alpha >= 2` every element of the class-two quotient
    is killed by `2 ^ alpha`, so the actual `C^(2^alpha)` block of the M word
    disappears there;
  - `mCupPowHalf_mem_two`, `mCupHead_mem_two_of_fixed_T` -- the MINIT interface,
    discharged rather than assumed: a lift fixing `T = A * C^(2^(alpha-1))`
    literally has its `A` image congruent to `A` modulo lambda-two, whatever it
    does to `C`;
  - `mCupRelWord_levelMk_eq_head_mul_tail` -- the exact class-two shape of the M
    relator: head square times the shared N commutator tail;
  - `mCupRelWord_level_three_eq`, `mCupRelWord_error_mem_three`,
    `mCupRelWord_error_mem_three_of_fixed_T` -- the initial depth itself, as an
    actual quotient equality and as actual error membership in lambda-three.

  The commutator tail is not reproved: `NInitialCupDepth.freeTail_eq_of_cup`
  and `NInitialCupDepth.freeTail_value` are used verbatim. The M-specific part
  is exactly the head square and the `C`-power block.
