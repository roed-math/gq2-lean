# W146: authoritative corrected-RN scoreboard

The campaign scoreboard can no longer silently trust a stale umbrella artifact.

- Every direct source import in `GQ2.lean` is compared with the imported environment.
- A mismatch emits `STALE_UMBRELLA`, marks every row and registration result unverified, and gives
  the exact mirror regeneration command.
- The board now includes the corrected Mpc/Npc certificates and tied consumers, both sqrt(10)
  endpoints, the closed odd endpoint, and the exact M6 absorption blocker.
- Legacy ASK and candidate records are labeled compatibility-only rather than active blockers.

Fresh and deliberately stale isolated mirrors were both tested.  Raw stale mode exits with a
distinct status, while the regenerated authoritative board resolves every added row.
