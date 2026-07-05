# P-16c3 execution blueprint (reconnaissance, 2026-07-06, Opus)

**Ticket:** the Γ_A twist / duality half — `GQ2/RadicalEdgeGammaA.lean` (~300 ln).  Produces, from
`NoDescent`, a nonzero mixed-pairing partner `w` (`mixedB t_ρ x_w y_φ ≠ 0`) and the crossed
`TCocycle u_w`, the input to P-16c4's Θ–mixedB comparison.

## Confirmed findings

1. **`GQ2/CentralObstruction.lean` is fully source-generic over `Γ`** — `variable {Γ : Type}
   [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]` then `ρ : ContinuousMonoidHom Γ
   (Bg ⧸ D.M)` (line 612).  So `TCocycle D ρ`, `varCoc D ρ S u`, `MLifts D ρ`, `half_count`,
   `not_noDescent_of_edge_trivial`, `edge`/`edgeQ`/`edge_add`/`conj_mem_T` are all Γ-generic.
   **The `RadicalEdgeLocal.exists_good_twist` prefix ports to `Γ = GA` by verbatim
   `AbsGalQ2 → GA` substitution** — nothing in the prefix uses arithmetic of `AbsGalQ2`.

2. **Source group = raw `GA := F₄ ⧸ N_A`, NOT the `GammaA` wrapper.**  `WordCohBridge` (P-16c1)
   is built over `GA` (its `variable`s), because the `ProfiniteGrp.of` wrapper's fresh instances
   break `q.comp (quotientMk NA)` unification (c1's structural finding #1).  So c3's `ρ` must be
   `ContinuousMonoidHom GA (Bg ⧸ D.M)` to feed `h1Equiv`.  The GA→GammaA transport is deferred to
   **c5** (`half_torsor_gammaA`), matching c1's "transports to the GammaA statement at the end".

3. **The bridge chain** (replaces `exists_good_twist`'s B6 tail, RadicalEdgeLocal L340–420):
   * `φf ∈ Z1 GA (MuDual 2 (Additive ↥D.T))` with `[φf] ≠ 0` — the ported prefix output.
   * `MuDual 2 A ≃+ ElemDual A` is `LocalLiftingDuality.dualAddEquiv` (P-13g;
     `dualAddEquiv_apply : dualAddEquiv φ a = muNTwoEquiv (φ a)`).  Transport `[φf]` to a class
     `y_φ ∈ H1w (ElemDual (Additive ↥D.T)) (markC ρ)` via `h1Equiv ρ hcompat hρ hA₂` (A =
     `Additive ↥D.T` on the *dual* side after `dualAddEquiv`).  **`hcompat : ∀ γ a, γ•a = ρ γ•a`
     holds by construction** — the prefix's `act γ = conj by out(ρ γ)` factors through `ρ γ`.
     `hA₂ : ∀ a, a+a=0` = `D.helem`/`MuDual`-2-torsion.
   * `prop_5_15 (markC ρ) … : IsSelfDual (markC ρ) (Additive ↥D.T)` (`GQ2.FoxH.prop_5_15`,
     `GQ2/DualityAssembly.lean:596`; needs `TameRel`/`WildRel`/`Generates`/`hcore`, all from
     `markC_admissible` + `Marking.push` at the finite quotient `ρ`).  Unpack its third clause:
     `∃ P, (∀ x y, P (h1wMk x) (h1wMk y) = mixedB t x.val y.val) ∧ (left-nondeg) ∧ (right-nondeg)`.
   * `y_φ ≠ 0` (image of `[φf]≠0` under the additive equivs) + **right-nondegeneracy** ⟹
     `∃ x_w-class, P x_w y_φ ≠ 0`, i.e. `mixedB (markC ρ) x_w.val y_φ.val ≠ 0`.
   * Pull `x_w` back through `z1Equiv ρ hcompat hρ hA₂` (A = `Additive ↥D.T`) to a `Z1 GA
     (Additive ↥D.T)` crossed cocycle; package as the `TCocycle D ρ` `u_w` (the `.u`-slot is the
     multiplicative shadow — `Additive.toMul`).

4. **Structural subtlety for the port:** the `Γ`-module action on `Additive ↥D.T` (and its dual)
   is **proof-local** in `exists_good_twist` (built by `letI actT`/`ContinuousSMul` from
   `D`+`ρ`).  For c3 it must be *in scope for the statement* (so `Z1 GA (MuDual …)` / `h1Equiv`
   typecheck).  Two options: (a) hoist the action to reusable `def`s
   `actModule D ρ : DistribMulAction GA (Additive ↥D.T)` + `ContinuousSMul` before the theorem
   (cleaner, reused by the `mixedB` side which needs the *same* action `markC ρ` induces); (b)
   keep it `letI` inside and phrase the conclusion existentially over the action.  **Prefer (a)** —
   the `prop_5_15` pairing is stated for the `C`-action `markC ρ` induces, and `hcompat` is
   exactly "the GA-action = the `C = Bg⧸M`-action pulled back through `ρ`", so hoisting makes the
   `hcompat` discharge one `rfl`.

## Dependency blocker (2026-07-06)

**`GQ2/WordCohBridge.lean` (P-16c1) is NOT committed** — untracked in the shared worktree (that
agent built it locally; not in committed `GQ2.lean`).  c3's bridge imports its `h1Equiv`/
`z1Equiv`, so **c3 cannot land until c1 is committed**.  The Γ-generic *prefix* (the nonzero
`[φf]` class) depends only on committed files (`CentralObstruction`, `LocalLiftingDuality`,
`ContCoh`) and could be extracted/committed independently — but per the plan's "do NOT churn the
closed P-16b file", the natural home is a shared Γ-generic lemma
`exists_edge_class {Γ} … : ∃ φf hφZ1, H1mk Γ _ ⟨φf,hφZ1⟩ ≠ 0` that both `RadicalEdgeLocal` and
`RadicalEdgeGammaA` could call (optional refactor; not required).

## Order of operations once c1 lands
1. Hoist `actModule`/`edgeCocycle φf`/`hφZ1`/`hφne` for `Γ = GA` (port of the prefix). *(std-3)*
2. `dualAddEquiv` + `h1Equiv` transport `[φf] → y_φ`; `y_φ ≠ 0`.
3. `prop_5_15` unpack + right-nondegeneracy ⟹ `x_w`, `mixedB ≠ 0`.
4. `z1Equiv⁻¹` ⟹ `u_w : TCocycle D ρ`; assemble the c3 output theorem (interface consumed by c4).
Expected `#print axioms` = std-3 (B6/B7 do **not** appear on the Γ_A side — the plan's Ax = ∅
finding, since the pairing comes from `prop_5_15` not B6).
