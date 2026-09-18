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
