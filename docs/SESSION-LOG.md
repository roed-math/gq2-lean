# Autonomous session log — 2026-07-02 (session 2)

Continued the autonomous push. **The whole project now builds green with only 2 `sorry`s left**
(`GQ2.reconstruction`, the profinite case of Lemma 2.5; and `GQ2.main_surjection_count`, the deep
§§3–9 arithmetic). Everything else is proved with standard axioms only.

## Proved this session

| declaration | file | significance |
|---|---|---|
| `tame_zpowers_disjoint` | `Tame.lean` | `⟨t⟩ ∩ ⟨s⟩ = ⊥` via `sⁿ=1` — completes the `C_e⋊C_n` decomposition |
| `tame_normal_two_subgroup_central` | `Tame.lean` | normal 2-subgroups are central — **Lemma 3.1 now fully proved** |
| `powOmega2_pow_eq` / `powOmega2_map` / `powOmega2_prod` | `Omega2.lean` | ω₂ is well-defined via any exponent multiple; is natural (commutes with all group homs); is coordinatewise |
| `Marking.map_*`, `map_tameRel`, `map_wildRel`, `map_admissible` | `Subdirect.lean` | the word ledger commutes with quotient maps ⟹ **§2 Lemmas 2.1–2.2** (admissibility is cofinal) |
| `reconstruction_finite` | `Reconstruction.lean` | **finite core of Lemma 2.5** (equal surjection counts ⟹ iso, for finite groups) |

Also: **imported [`kbuzzard/ClassFieldTheory`](https://github.com/kbuzzard/ClassFieldTheory)** as a
dependency (local fields, Tate cohomology, Herbrand quotient, ramification/inertia) — the substrate
for §3 and §§5–8. See `docs/foundations-audit.md` §E.

## Roadmap for the 2 remaining `sorry`s

**1. `GQ2.reconstruction` (profinite Lemma 2.5).**  The finite core is done
(`reconstruction_finite`).  Remaining: lift it to the profinite setting.  Plan:
- Show `P` (topologically f.g. profinite) is the inverse limit of its finite quotients `P/N`
  (`N` open normal), a cofinal system.  Mathlib: `ProfiniteGrp` limits + `ProfiniteGrp.Completion`.
- `|ContSurj(P, F)|` is finite for finite `F` (continuous homs factor through open normal subgroups;
  f.g. ⟹ finitely many).  This is the missing finiteness input.
- From equal counts + compactness (inverse limit of nonempty finite sets is nonempty) get an
  epimorphism `Q ↠ P`, symmetrically `P ↠ Q`; then the **Hopfian property** of topologically f.g.
  profinite groups (surjective continuous endo is injective — *not in Mathlib*, must be built)
  finishes, exactly as `reconstruction_finite` does with cardinalities.
- Grade F′: reachable, but needs the profinite-Hopfian lemma packaged on `ProfiniteGrp`.

**2. `GQ2.main_surjection_count` (paper eq. 154).**  The deep tower.  Now that `ClassFieldTheory`
is imported, the substrate exists for parts of it:
- §3 (marked dyadic Demushkin normalisation): needs Demushkin groups + Labute's classification
  (absent) and local reciprocity (CFT's `LocalCFT/` is nascent — Artin map not yet complete).
- §§5–8 (Fox–Heisenberg cup calculus, quadratic determinant, Fourier–Gauss): CFT provides Tate
  cohomology / Herbrand / corestriction / `LocalInv` (the H² invariant) to build on; still needs
  cup products, Stiefel–Whitney/Evens, and the finite-word Stokes machinery.
- This is the genuine research-scale gap; no quick path.

---

# Autonomous session log — 2026-07-01 (session 1)

A single autonomous working session pushing toward the formalization, after installing
[cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills) (now at
`~/.claude/skills/lean4`, full clone at `~/claude/lean4-skills`).

## What got proved (all compile, `lake build` green, no new axioms)

Working in **scripts_only** mode (no Lean LSP MCP connected): edits validated with
`lake env lean <file>` and lemma discovery via `rg` + in-file `exact?`.

| # | declaration | file | significance |
|---|---|---|---|
| 1 | `omega2_appendixB` | `Omega2.lean` | **certifies the paper's Appendix B number** `ω₂ = 40491355905 (mod 85667662080)` (both defining congruences) |
| 2 | `oddPart_dvd_omega2Exp`, `omega2Exp_modEq_one` | `Omega2.lean` | the `ω₂` spec: `≡ 0` on the odd part, `≡ 1` on the 2-part (Euler) |
| 3 | `coprime_fiber_product` | `FiniteGroupLemmas.lean` | **Lemma 9.1** — full proof via Mathlib's Goursat lemma |
| 4 | `FreeProfiniteGroup` + `.of` + `.homEquiv` + `grpCatHomEquiv` | `FreeProfinite.lean` | **the #1 missing foundation** — free profinite group + universal property, built on Mathlib's new `ProfiniteGrp.profiniteCompletion` |
| 5 | `zpowers_sq_eq_of_odd` | `Tame.lean` | `⟨t²⟩ = ⟨t⟩` for odd order (reusable) |
| 6 | `zpowers_normal_of_tame` | `Tame.lean` | **Lemma 3.1 normality** — `⟨t⟩ ◁ G` |
| 7 | `tame_semidirect` | `Tame.lean` | **Lemma 3.1 structure** — the `C_e ⋊ C_n` shape (minus disjointness) |

(Pre-session, the repo already had `tame_odd_order`, `conj_pow_iterate`,
`oddOrder_twoQuotient_split` = Lemma 9.2 core, the `Words.lean` machinery, and the
`main_presentation` logical wiring.)

## Key discoveries

- **Mathlib now has `ProfiniteGrp.profiniteCompletion`** (A. Topaz, 2026) — a full
  profinite-completion adjunction. This is what made `FreeProfiniteGroup` feasible; it was *not*
  usable when the original audit was written. The audit (`foundations-audit.md`) is updated.
- The paper's Lemma 9.1 maps cleanly onto Mathlib's `Subgroup.goursat`; the coprimality is used
  exactly once, via `Nat.Coprime.dvd_of_dvd_mul_right`, to force `ker g ≤ J.goursatSnd`.
- Lemma 3.1 normality reduces to `Subgroup.mem_normalizer_iff_map_conj_eq` + the odd-order fact
  `⟨t²⟩ = ⟨t⟩`.

## Honest state of the whole proof

Unchanged in the big picture: a **complete** machine-checked proof remains out of reach because
the deep arithmetic (Demushkin/Labute, local class field theory, local Tate duality, continuous
Galois cohomology with cup products, Stiefel–Whitney/Evens, the tame π₁ of ℙ¹∖{0,1,∞}) is absent
from Mathlib. That tower sits behind the single `sorry` in `main_surjection_count` (paper eq. 154).
This session did **not** touch that tower; it hardened the reachable periphery and built one
genuinely missing foundation.

## Cleanest next steps (for whoever continues — likely with an LSP connected)

1. **`tame_zpowers_disjoint`** — finish Lemma 3.1's `⋊`. Proof plan in the docstring; the only
   friction is ℤ-power / `orderOf (QuotientGroup.mk s)` lemma names (fast with LSP `exact?`).
2. **`tame_normal_two_subgroup_central`** — `[N, ⟨t⟩] ≤ N ∩ ⟨t⟩ = 1` then Frobenius-kernel centrality.
3. **`reconstruction` (Lemma 2.5)** — the highest-value remaining named lemma. Build
   "topologically f.g. profinite ⇒ Hopfian" on top of `ProfiniteGrp.Completion` (`denseRange`,
   `lift`, `lift_unique`, `homEquiv` are all there). No Mathlib `Hopfian` yet.
4. **Finish the foundations**: `FreeProfiniteGroup.homEquiv`-naturality (`homEquiv f x = f (of x)`),
   then a profinite-presentation quotient to define `Γ_A`; and `ℤ̂` as a topological ring with the
   `ω₂`-power action, to state Theorem 1.2 literally rather than only in surjection-count form.
5. Consider upstreaming `FreeProfiniteGroup` to Mathlib.
