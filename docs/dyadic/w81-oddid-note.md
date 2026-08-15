# W81-ODDID lane note

Lane target: the oriented identification at the odd slot. `genAsm_branch_of_oddSq_canonical`
(`GeneralAssembly.lean:653`) consumes `e : OrientedContinuousMulEquiv (chiSq h) chiCycKTwo` at
odd-degree ramified-i `K` with `[K : ℚ₂] = 1 + 2h`; producing that `e` is the odd-degree
classification. New module: `GQ2/Dyadic/Instances/OddIdentification.lean`, prefix `oddId`.

## Status

- Skeleton banked. Reading the even pattern and the odd-side pieces.

## Tickets

- T1: invariants at odd degree (full cyclotomic image, demushkinQ = 2, rank d = [K:Q2] + 2).
- T2: the identification G_K(2) oriented-equiv D_sq h (named-Prop seam where the tree lacks
  the classification input; n = 1 must come out a theorem via the committed L row).
- T3: the consumer corollary through `genAsm_branch_of_oddSq_canonical`.
