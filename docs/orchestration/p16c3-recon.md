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


---

## Update 2026-07-06 (Opus) — MuDual→ElemDual pivot + foundation ported

**Progress this session:**
* Committed the abandoned-but-built `WordCohBridge.lean` (P-16c1) — unblocks the lane.
* Created `GQ2/RadicalEdgeGammaA.lean`; the **entire `ρ`-conjugation module foundation ports
  verbatim** `AbsGalQ2 → GA` (`act`/`hact_*`/`actT : DistribMulAction GA (Additive ↥D.T)`/
  `ContinuousSMul GA (Additive ↥D.T)`/`htorT`) and **builds** (8630 jobs).  `tCommGroup`/
  `conj_eq_of_mk_eq` reused via `open RadicalEdgeLocal`.

**Structural pivot (supersedes the recon's `dualAddEquiv` plan):** `MuDual n M`'s
`DistribMulAction` is **hardcoded to `AbsGalQ2`** (`GQ2/TateDuality.lean:60` variable block +
`:101` instance) — there is NO `DistribMulAction GA (MuDual n M)`, so the ported prefix's
`φf : GA → MuDual 2 (Additive ↥D.T)` does not typecheck.  **Fix:** build the shifted-edge cocycle
directly in **`ElemDual (Additive ↥D.T)`** — `ElemDual A = A →+ ZMod 2` has a *generic*
`DistribMulAction C (ElemDual A)` (`FoxHeisenberg.lean:568`, `(g•λ)a = λ(g⁻¹•a)`,
`ElemDual.smul_apply`).  This also **eliminates `dualAddEquiv`** (the word complex's dual side is
already `ElemDual`).  A trivial `letI : DistribMulAction GA (MuN 2)` is *not* needed on this route.

**ElemDual rewrite recipe (the sorried tail, ~100 ln):**
* `φf γ := AddMonoidHom.mk' (fun s => edgeQ D S (ρ γ) (act γ⁻¹ (Additive.toMul s))) (hφadd γ)
    : ElemDual (Additive ↥D.T)` (drop `muNTwoEquiv.symm`); `hφadd`/`hcrossZ` port unchanged
  (edgeQ-only, MuDual-free).
* `hφZ1`: continuity factors through `ρ` (unchanged); cocycle law = `hcrossZ` +
  `ElemDual.smul_apply` (replaces `smul_muN_two_trivial` + `muNTwoEquiv`).
* `hφne`: `not_noDescent_of_edge_trivial` with `ℓ t := (lam : ElemDual (Additive ↥D.T))
    (Additive.ofMul t)` (ZMod 2 directly; no `muNTwoEquiv`).
* **Bridge:** `[φf]` is already an `ElemDual`-class ⟹ `h1Equiv`/`z1Equiv` (with `A =
  Additive ↥D.T`, so the *dual*-side class `y_φ` lands in `H1w (ElemDual (Additive T)) (markC ρ)`
  after transporting `[φf]` — note `h1Equiv` is `H1(GA, ElemDual (Additive T)) ≃ H1w (ElemDual …)`
  directly) + `prop_5_15 (markC ρ) … (Additive ↥D.T)` right-nondegeneracy ⟹ `x_w` with
  `mixedB ≠ 0` ⟹ `z1Equiv⁻¹` the crossed cocycle `u` ⟹ (Θ–mixedB, P-16c4) `varCoc u` not a
  coboundary.  `hcompat` for `h1Equiv` = `rfl` (the `actT` GA-action IS `ρ γ • ·`).

---

## Update 2026-07-05 (Opus) — P-16c3 CLOSED (sorry-free, std-3)

`GQ2/RadicalEdgeGammaA.lean` is **sorry-free**; `lake build GQ2` green (8669 jobs);
`#print axioms exists_good_pairing_gammaA = {propext, Classical.choice, Quot.sound}` (**std-3
only** — no B6/B7/B10, matching the board's `Ax ∅`).  `check_axioms` green (census 15, unchanged
— c3 adds no axioms; the file is sorry-free so needs no allowlist entry).

**Deliverable (the c3↔c4 interface).**  The headline theorem is the *nonzero mixed pairing*, in
the `C`-module (`Z1w`/`mixedB`) form so the signature needs only the file-level `C`-action:
```
theorem exists_good_pairing_gammaA (S : TComplement D) (hedge : D.NoDescent)
    (ρ : ContinuousMonoidHom GA (Bg ⧸ D.M)) (hρ : Function.Surjective ρ) :
    ∃ (x : Z1w (A := Additive ↥D.T) (markC ρ))
      (y : Z1w (A := ElemDual (Additive ↥D.T)) (markC ρ)),
      mixedB (markC ρ) x.val y.val ≠ 0
```
**c4 note:** c4 needs `x = eval w` for the specific crossed `w`/`u_w` and `y = eval φf` for *the*
edge dual, to run the Θ–mixedB ledger.  Those live inside this proof as `have`s (`x_w`, `yφ`);
when c4 lands (unblocked once c2's `θ` is complete), the natural move is to **strengthen this
theorem's conclusion in-place** to also expose the `TCocycle u_w` and the primal/edge structure
(same file), rather than re-deriving the `[φf]≠0` prefix.  The prefix (`φf`/`hφZ1`/`hφne`) is the
reusable half already proven here.

**Route as built (three landable stages).**
1. **File-level instances** (de-risked the instance-in-signature question first): `cActT :
   DistribMulAction (Bg ⧸ D.M) (Additive ↥D.T)` (the `C`-conjugation action, `cactFun` +
   `cactFun_eq/_one/_mul/_mul'/_one_elt`; unification recovers `D`), `AddCommGroup (Additive
   ↥D.T)` (built on the existing `AddGroup`, `add_comm` from `D.hcomm` — no diamond), and the
   `ElemDual` `⊥`-topology/discrete instances.  The `GA`-action is `DistribMulAction.compHom
   (Additive ↥D.T) ρ.toMonoidHom` **inside** the proof, so `hcompat : γ • a = ρ γ • a` and
   `hactGA : toMul (γ • s) = cactFun D (ρ γ) (toMul s)` are both `rfl`.
2. **`φf` + `[φf]≠0`** (the MuDual→ElemDual port): `φf γ := AddMonoidHom.mk' (fun s => edgeQ D S
   (ρ γ) (toMul (γ⁻¹ • s))) _ : ElemDual (Additive ↥D.T)`.  The one genuinely-new lemma is
   `hsmulD : (γ • l) a = l (γ⁻¹ • a)` (the `compHom`-contragredient, `= hcompatD +
   ElemDual.smul_apply + hcompat + map_inv`), which stands in for the local proof's
   `smul_muN_two_trivial`.  `hcrossZ`/`hΦadd`/continuity-factoring/`hφne` port verbatim
   (edgeQ-only), `hφne` via `not_noDescent_of_edge_trivial` with `ℓ t := lam (Additive.ofMul t)`.
3. **The bridge**: `prop_5_15 (markC ρ) adm.2.1 adm.2.2.1 adm.1 hA₂ adm.2.2.2` (admissibility from
   `markC_admissible ρ hρ`), unpack clause-3's `⟨P, hP, _, hright⟩`; transport `[φf]` via
   `h1Equiv ρ hcompatD hρ hA₂D` to `yφ ≠ 0` (AddEquiv injective); `hright yφ` ⟹ `x_w` with
   `P x_w yφ ≠ 0`; `QuotientAddGroup.mk_surjective` gives `Z1w`-representatives; `hP` rewrites the
   pairing to `mixedB`.

**Lean lessons.** (a) `mixedB`/`Z1w`/`markC` are `C = Bg⧸D.M`-module notions, so ONLY the
`C`-action must be a file-level instance (in the signature); the `GA`-action stays a proof-local
`letI` — this is why the whole thing is action-clean.  (b) `Additive.toMul (Additive.ofMul t) = t`
is not closed by `rw`'s post-rfl; use `exact inv_smul_smul γ (Additive.ofMul t)` on the
`toMul _ = t` goal directly (defeq fires under `exact`, not under `congrArg`).  (c) the
`compHom` `GA`-contragredient does NOT match `ElemDual.smul_apply` directly — route through
`hcompatD` first.
