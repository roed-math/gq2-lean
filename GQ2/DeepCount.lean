/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
module

public import GQ2.DeepCount.Filtration
public import GQ2.DeepCount.Bounds
public import GQ2.DeepCount.Transport
public import GQ2.DeepCount.Finale

@[expose] public section

/-!
# The (H4) structural count

This file proves the structural inequality `#(M ⧸ Deep) ≤ #E` for `M = H¹(G_k, 𝔽₂)`,
`Deep = deepClassesSubgroup = kummerDepth (e+1)`, `E = midClassesSubgroup = kummerDepth e`.
from the B13 bundle `DyadicUnitFiltration`, without extending that interface.

The proof provides the following `k`-level ingredients:

* `exists_sq_of_kummerClassK_eq_zero` — **the Kummer kernel**: class-zero units are squares
  (`B¹(G_k, 𝔽₂) = 0` since the action is trivial, so class-zero forces the cocycle to
  vanish, i.e. `G_k` fixes `sqrtCl a`, i.e. `sqrtCl a ∈ k`);
* `kummerClassK_mem_midClasses` / `coe_kummerDepth_mid` — stage `e` of the Kummer depth
  filtration IS the mid classes (the `≤`-mirror of `coe_kummerDepth_deep`; no discreteness
  upgrade needed since mid = `‖a−1‖ ≤ ‖2‖ = ‖π‖^e` on the nose);
* `norm_step_down` — the discreteness step (`x ∈ k`, `‖x‖ < ‖π‖^i ⟹ ‖x‖ ≤ ‖π‖^{i+1}`),
  extracted from `coe_kummerDepth_deep`;
* `norm_sq_sub_one` / `norm_sq_sub_one_le_succ_of_odd` — **square depths are even below
  `2e`**: `‖w² − 1‖ = ‖w − 1‖²` or `‖w² − 1‖ ≤ ‖4‖`, hence a square lying in `U_j` for odd
  `j ≤ 2e − 1` lies in `U_{j+1}` (the odd-level-fullness workhorse).

The auxiliary layer is axiom-free; the final `hduality_of_data` theorem consumes its arithmetic
and module-theoretic hypotheses explicitly.

**File organisation.**  The proof is split into `Filtration`, `Bounds`, `Transport`, and `Finale`, following the dependency order of the Kummer filtration argument.  This umbrella preserves the original import path and public declaration names.

-/
