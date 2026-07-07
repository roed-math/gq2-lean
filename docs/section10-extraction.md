# §10 extraction — Lemma 10.1 and eq. (154)  (P-18a, 2026-07-07)

Statement-layer encoding of paper §10 (pp. 47–48) in `GQ2/SectionTen.lean`.  Companion to the
lane plan `docs/p18-plan.md` (routes, per-source obligations, sub-ticket split P-18a–e).
Skeleton builds green; the six sorries and their owners are listed at the end.

## Node map

| paper node | Lean | status |
|---|---|---|
| `O₂(G)` (2-core; paper uses it implicitly in "put `L = O₂(G)`") | `SectionTen.twoCore` (sSup of normal 2-subgroups) + `twoCore_normal`/`twoCore_isPGroup`/`le_twoCore` | def ✓; props sorried (P-18b; `le_twoCore` proved) |
| "characteristic marked wild subgroup maps into `O₂(G)`" | `isPGroup_map_of_isProP` (pro-2 image bridge) + `le_twoCore` | sorried (P-18b) |
| the single §10 target `(G, L, π, θ=0)` | `tameTarget G : MarkedTarget (G ⧸ twoCore G) E₀ G` | ✓ built |
| a tame boundary frame with `E = 0` | `tameFrame α hα : BoundaryFrame H E₀` | ✓ built |
| the (finite) set of tame frames `Ttame ↠ G/L` | `TameFrames G` (subtype) | ✓; finiteness P-18c |
| Lemma 10.1 (exhaustion/disjointness) | `lemma_10_1` (sigma-equivalence) | sorried (P-18c) |
| the summed count identity | `card_contSurj_eq` (`Nat.card (ContSurj Γ G) = ∑ᶠ α, e^β`) | sorried (P-18c) |
| eq. (154) | `eq_154` | sorried (P-18e; consumes `thm_4_2` per frame) |
| `main_surjection_count` (Theorem 1.2, count form) | `main_surjection_count'` | **PROVED modulo `eq_154`** (std-3 + sorryAx verified) — the end-to-end wiring type-checks |

## Encoding decisions and deviations (flagged for P-20)

1. **`O₂(G)` is built, not cited.**  Mathlib has no `pCore`; `twoCore := sSup {N | N.Normal ∧
   IsPGroup 2 N}`.  The three properties are P-18b's (directedness via the second isomorphism
   theorem + `p`-groups closed under extension; statements hold for arbitrary groups, no
   finiteness needed).
2. **"For either source" is hypothesis-form.**  `lemma_10_1`/`card_contSurj_eq` are stated over
   any `(Γ, b)` with `htame : Surjective (tameCoord b)` and `hwild : IsProP 2 (ker (tameCoord
   b))`; P-18d discharges per source.  `tameCoord (B.bA) = B.tameA` and `tameCoord (B.bF) =
   B.tameF` hold on the nose (`bA_apply_coe`/`bF_apply_coe` are `rfl`).  The `G_ℚ₂` side is
   already bundled in `BoundaryMaps` (`tameF_surjective`, `wild_isProP`); the `Γ_A` side is the
   one open obligation (plan §4, P-18d, with the `BoundaryMaps`-amendment fallback).
3. **"Determines a unique tame boundary frame … disjoint sets" is the sigma-equivalence.**
   `ContSurj Γ G ≃ (α : TameFrames G) × BoundaryLifts b (tameFrame α) (tameTarget G)` — the
   fibration IS the partition + uniqueness; no standalone uniqueness lemma is stated.
4. **`E = 0` is `E₀ := PUnit`.**  `exponent_two` is `rfl`; `ψ̄ := 1`; `thm_4_2`'s `hE2` will be
   discharged by `fun _ => rfl` at P-18e.  (Precedent for `PUnit` group instances:
   `GQ2/Demushkin.lean` §PUnitNot.)
5. **The counting form uses `∑ᶠ` over the `TameFrames` subtype.**  Finiteness of the index is
   Ttame-t.f.g. content (`SectionThree.gen_ttame_quotient`, `GQ2/Prop32.lean:134`) and of the
   fibers is `finite_boundaryLifts` + `hfg` — both inside P-18c's proof; the statement carries
   only `hfg` (the house `∃ Finset …topologicalClosure = ⊤` shape).
6. **Eq. (154) is split**: `eq_154` (the two-source `Nat.card (ContSurj …)` equality) then
   `main_surjection_count' := (eq_154 G).symm.trans prop_2_3` — the latter **already compiles**
   (shape-validates the whole design: `contSurjCount` unfolds definitionally, `prop_2_3`'s
   binders match).
7. **Import geometry (load-bearing).**  `Statement.lean` is imported by `GammaA.lean` and
   `FoxHeisenberg.lean` — it sits UPSTREAM of the entire §§4–9 tower, so `main_surjection_count`
   cannot be proven in place (a `Statement → SectionTen` import would cycle).  **P-18e uses the
   statement-move pattern** (P-08/P-15d precedent): the theorem moves here (comment-pointer in
   `Statement.lean`), and `main_presentation` (which consumes it) goes **hypothesis-form**
   (gains `hcount : ∀ G …, contSurjCount G = admissibleCount G`; P-19 supplies it).  The moved
   statement also gains the two instance binders `[CompactSpace AbsGalQ2]
   [TotallyDisconnectedSpace AbsGalQ2]` — these are file-level `variable`s throughout the tower
   (e.g. `SectionThree.lean:1075`, `BoundaryMapsWitness.lean:291`), NOT global instances, so
   every theorem mentioning `AbsGalQ2` carries them; `main_presentation` already binds them, so
   the amendment is invisible downstream.  **P-19 note**: `main_presentation_literal`
   (`GammaA.lean:283`) is also upstream and will need the same statement-move at P-19 (its proof
   needs `prop_2_3` + `main_surjection_count`, both downstream of `GammaA.lean`).
8. **`[IsTopologicalGroup Γ]`** is added to the generic-section variables (the
   `exactImageCount` context requires it); both sources satisfy it.
9. **Quotient-head discreteness** `DiscreteTopology (G ⧸ twoCore G)` is proved via
   `discreteTopology_iff_forall_isOpen` + `isOpen_coinduced` (the `⟨rfl⟩` trick of
   `BlockFrameImpl.lean:39` does not transfer to an abstract `[DiscreteTopology G]`).
10. **P-18c statement amendments (landed 2026-07-07).**  Over the P-18a skeleton:
    `lemma_10_1` gains `[CompactSpace Γ]` — the induced frame `α_f` is continuous only because
    the tame coordinate is a topological *quotient map* (a continuous surjection from a compact
    source onto the Hausdorff `Ttame` is closed, hence quotient); without compactness the
    descended hom need not be continuous (no strong-completeness machinery is formalized).
    `card_contSurj_eq` gains `[CompactSpace Γ] [TotallyDisconnectedSpace Γ]` (the latter for
    `finite_boundaryLifts`/`finite_continuousMonoidHom`).  Both are free at the P-18e call
    sites, but note the `GammaA` instances are bound per-theorem in the tower — `eq_154` will
    bind `[CompactSpace GammaA] [TotallyDisconnectedSpace GammaA]` alongside deviation 7's
    `AbsGalQ2` binders.  Conversely `[IsTopologicalGroup Γ]` is `omit`ted on `lemma_10_1` and
    the P-18c helpers (unused there; deviation 8's rationale is the `exactImageCount` side,
    i.e. `card_contSurj_eq` keeps it).

## Sorry ledger (all allowlisted via `GQ2/SectionTen.lean`)

| decl | owner |
|---|---|
| `twoCore_normal`, `twoCore_isPGroup` | P-18b — ✅ PROVED (2026-07-07, std-3) |
| `isPGroup_map_of_isProP` | P-18b — ✅ PROVED (2026-07-07, std-3) |
| `lemma_10_1`, `card_contSurj_eq` | P-18c — ✅ PROVED (2026-07-07, std-3; statement amendments in deviation 10) |
| `eq_154` | P-18e (consumes `thm_4_2` per frame — carries `sorryAx` through the allowlisted `SectionNine` sorry until P-17i).  **The file's last sorry.** |

`main_surjection_count'` is proved (std-3 + sorryAx via `eq_154`, verified); at P-18e it
replaces the `Statement.lean:49` sorry by the statement move of deviation 7, taking
`Statement.lean` off the `SORRY_ALLOWLIST`.
