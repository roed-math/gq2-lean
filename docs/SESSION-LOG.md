# Autonomous session log — 2026-07-02 (session 3)

Focused on **Lemma 2.5 (reconstruction)** and the **profinite-presentation foundations**, per a
request to prioritize content that is *non-standard* in the literature (e.g. the Artin map is
standard, so deprioritized). The project still builds green; standard axioms only for everything
proved. Notably this session **found and fixed a soundness bug** in the previous session's
`reconstruction` statement.

## Proved this session

| declaration | file | significance |
|---|---|---|
| `finite_continuousMonoidHom` | `Reconstruction.lean` | `Hom_cont(P,H)` finite for top. f.g. profinite `P`, finite discrete `H` (a continuous hom is pinned by its values on a topological generating set) |
| `profinite_hopfian` | `Reconstruction.lean` | **the profinite Hopfian property** (absent from Mathlib): a continuous surjective endomorphism of a top. f.g. profinite group is injective. Elementary counting proof (precomposition by φ is an injective, hence surjective, self-map of the finite hom-set) |
| `continuousMulEquivOfBijective` | `Reconstruction.lean` | bijective continuous hom compact→T2 is a topological iso |
| `reconstruction_of_equinum` | `Reconstruction.lean` | **Lemma 2.5, faithful form** — proved in full modulo the one standard input `exists_contSurj_of_card_le` |
| `FreeProfiniteGroup.homEquiv_apply` | `FreeProfinite.lean` | naturality of the free-profinite universal property (`homEquiv f x = f (of x)`) |
| `instTotallyDisconnectedSpace_quotient`, `profiniteQuotient` | `ProfiniteQuotient.lean` | **`G ⧸ N` is profinite** for `N` closed normal (the `TotallyDisconnected` instance Mathlib lacked, via a clopen basis) — the profinite-presentation gap in the audit |
| `quotientMk`, `quotientLift` (+ API) | `ProfiniteQuotient.lean` | projection and **universal property** of the profinite quotient (maps out = maps killing `N`) |
| `relatorSubgroup`, `profinitePresentation`, `relator_quotientMk_eq_one` | `ProfinitePresentation.lean` | the profinite group **presented** by generators + relators; `Γ_A = profinitePresentation (Fin 4) rels`; relators die in the quotient |
| `omega2Exp_appendixB_value` | `Omega2.lean` | the *computable* `omega2Exp 85667662080 = 40491355905` **exactly** — the definition matches the paper's App. B serialization (standard axioms, no `native_decide`) |

## ⚠ Soundness bug found and fixed: `reconstruction` is FALSE as stated

The session-2 `GQ2.reconstruction` uses `Nat.card (ContSurj P H) = Nat.card (ContSurj Q H)`.
`Nat.card` sends *infinite* sets to `0`, so this equality fails to encode "equal *finite* counts".
**Counterexample**: `P = Unit` (top. f.g.), `Q = (ℤ/2)^ℕ`; for every finite `H` both cards are `1`
(trivial `H`) or `0` (else — the `Q`-side is `0` because there are infinitely many surjections
`(ℤ/2)^ℕ ↠ H`), so the hypotheses hold but `P ≇ Q`.

Fix: the statement of `reconstruction` was left untouched (header-fenced — **needs a user decision**
to amend `hcount`), its body reverted to `sorry` + a warning note. The faithful
`reconstruction_of_equinum` uses genuine equinumerosity `Nonempty (ContSurj P H ≃ ContSurj Q H)`,
which forces the counts finite (via `P` f.g.) and is proved in full modulo the standard compactness
lemma `exists_contSurj_of_card_le` (target has finite level-sets ⇒ finite König over
`OpenNormalSubgroup R`; recipe recorded in that lemma's docstring). Both are now over `Type` (Type 0)
so the finite quotients match the `H : Type` count quantifier.

## The one remaining reachable `sorry` here

`exists_contSurj_of_card_le` — the standard (Ribes–Zalesskiĭ) compactness assembly of a surjection
`S ↠ R` from the finite, nonempty level-sets `{S ↠ R/V}` over `OpenNormalSubgroup R` (a
`SemilatticeInf`, hence cofiltered): apply `nonempty_sections_of_finite_cofiltered_system`, turn the
section into a cone over `ProfiniteGrp.diagram R`, transport through `isoLimittoFiniteQuotientFunctor`,
and conclude surjectivity from the dense (compact ⇒ closed) image. Deferred as *standard*; it is the
biggest remaining categorical chunk for Lemma 2.5.

## Net effect on `Γ_A`

`Γ_A` is now expressible as `profinitePresentation (X := Fin 4) rels`. The sole remaining blocker to
writing it *literally* is a genuine profinite `ω₂`-exponent (`ℤ̂`, still absent — roadmap item 5).

## Reconstruction repaired + literature-axiom reduction (later, session 3)

- **`reconstruction` repaired.** Review pointed out the `Nat.card` counterexample used a non-f.g. `Q`.
  Added `hQfg` (both `P,Q` topologically f.g.); with both f.g. the counts are finite, so equal
  `Nat.card` is genuine equinumerosity and `reconstruction` reduces to `reconstruction_of_equinum`.
  `reconstruction` is now **proved** (modulo the standard `exists_contSurj_of_card_le`).
  `main_presentation` gained `hfgG` (`G_ℚ₂` is topologically f.g. — true, assumed). Whole project
  down to **2 `sorry`s**: `exists_contSurj_of_card_le` (Mathlib-provable) and `main_surjection_count`.
- **Literature-axiom reduction (for expert review — Hill/Buzzard).** Reduced `main_surjection_count`
  to a minimal list of **nine classical results** (B1–B9) in `docs/literature-axioms.md`: precise
  statements + citations (NSW/Labute/Serre/Milne/Stix/Evens/Kahn/Guillot) + the dependency structure
  from paper App. D. `GQ2/Foundations.lean` states the two that Mathlib can type faithfully (B1 `G_ℚ₂`
  top. f.g.; B2 2-adic cyclotomic surjective); B3–B9 (Demushkin, local reciprocity, local Tate
  duality, local Euler char, dyadic Hilbert symbol, Galois action on `π₁(ℙ¹∖{0,1,∞})`, Evens/SW) need
  absent infrastructure and are documented. Two would-be inputs are already discharged: RZ Hopfian
  (`profinite_hopfian`) and Schur–Zassenhaus (Mathlib). `exists_contSurj_of_card_le` is Mathlib-
  provable, not a literature gap.

---

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

---

# Session 2026-07-02 (Fable): T-06 — `ℤ̂`, `ω₂`, and `ẑ`-exponentiation

First execution ticket of the step-1 program (`docs/formalization-plan.md`). New file
`GQ2/Zhat.lean` (+ `omega2Exp_modEq` in `Omega2.lean`); build green; every declaration
`#print axioms`-checked to the standard three.

- **`omega2Exp_modEq`** (`Omega2.lean`): `N ∣ M → omega2Exp M ≡ omega2Exp N [MOD N]` — the
  CRT argument extracted from `powOmega2_pow_eq` (now a corollary). This is the coherence of the
  family `(omega2Exp N)_N`.
- **`Zhat`** := Mathlib's `ProfiniteCompletion.completion` of `Multiplicative ℤ` (`= lim ℤ/N`);
  `Zhat.ofInt` dense embedding, `funext_ofInt` (extensionality by density), `Zhat.commute`.
- **Integer levels without classification** (`orderOf_mk_ofAdd_one`, `ofAdd_mem_iff_index_dvd`,
  `mk_ofAdd_eq_mk_ofAdd_iff`): in `ℤ/H` the class of `1` has order `= H.index` (generator +
  `Nat.card_zpowers`), so membership/equality are congruences mod the index — no
  `Int.subgroup_cyclic`, no `AddSubgroup` transfer.
- **`omega2 : Zhat`** constructed componentwise — Mathlib's completion is definitionally the
  subtype of compatible families, so the anonymous constructor works; compatibility is
  `omega2Exp_modEq` + `index_dvd_of_le`.
- **`zpowHat` / `x ^ᶻ γ`**: `ProfiniteCompletion.lift` of `zpowersHom G x`, for `G` any
  typeclass-profinite group (`Type 0`, matching `Reconstruction.lean` conventions).
  `zpowHat_ofInt` (extends `ℤ`-powers; proof is literally `congr_hom lift_eta`),
  `zpowHat_mul`/`zpowHat_one`/`one_zpowHat`, **naturality `map_zpowHat`** via `lift_unique`.
- **`completion_exists_level`**: in any profinite completion, "agrees with `γ` at one
  finite-index level" refines any open neighborhood of `γ` (isOpen_pi_iff + finite `iInf`,
  same skeleton as Mathlib's `denseRange`). The workhorse for evaluation.
- **Evaluation theorems**: `zpowHat_omega2 : x ^ᶻ ω₂ = powOmega2 x` in finite discrete groups
  (level `H₀` from `completion_exists_level`, integer representative at level
  `lcm(index H₀, orderOf x)`, close with `powOmega2_pow_eq`); headline
  **`map_zpowHat_omega2 : f (x ^ᶻ ω₂) = powOmega2 (f x)`** for continuous `f` into finite
  groups. Sanity in `S₃`: `(r 1) ^ᶻ ω₂ = 1`, `(sr 0) ^ᶻ ω₂ = sr 0`.

Lean gotchas recorded: `Zhat`-vs-`completion` semireducibility breaks `rw`-motives inside
categorical goals (state key equations at the `lift` level, extract with defeq-tolerant
`exact`); `rw` won't see through `↥(GrpCat.of _)` in quotient types (use `exact ...mpr` instead);
`omega2` must be `noncomputable` (`Subgroup.index` is); the anchor equation
`x ^ᶻ ofInt n = x ^ n` is *definitionally* `congr_hom lift_eta (ofAdd n)`.

**Unblocked**: T-21 (literal `Γ_A` + literal Theorem 1.2) and T-12's `P ^ᶻ ι(u)` notation.
Next per plan: T-02 (continuous cohomology API design, Fable); T-01/T-05/T-07/T-00 ready for
Opus in parallel.

---

# Session 2026-07-02 (Fable, cont.): T-21 — the literal `Γ_A` and Theorem 1.2

New file `GQ2/GammaA.lean` (+ `homEquiv_symm_of` in `FreeProfinite.lean`); build green; all
proved declarations at the standard three axioms; `main_presentation_literal` is the third
(intentional) sorry.

**Faithfulness finding (important):** the paper's `Γ_A` (§2.1, eq. (7)) is the **marked
quotient** `F₄ ⧸ N_A` with `N_A = ⋂ ker φ` over *admissible* finite quotients φ — the pro-2
condition on `⟨⟨x₀,x₁⟩⟩` is part of the presentation data, so `Γ_A` is NOT the bare two-relator
`profinitePresentation` the ticket sketch assumed. We formalized eq. (7) verbatim:

- `Marking.sigma2Hat … h0Hat, tameRelator, wildRelator` — the eqs. (1)–(3) ledger and relations
  (5)/(6) as words with genuine `ω₂ ∈ ℤ̂` exponents, on any marking of any profinite group.
- **Bridges** `map_sigma2Hat … map_h0Hat`, `map_tameRelator_eq_one_iff`,
  `map_wildRelator_eq_one_iff`: through any continuous hom to a finite group the `^ᶻω₂`-ledger
  computes the `powOmega2`-ledger of `Words.lean` (T-06 headline pushed through all ten words) —
  killing the profinite relators ⟺ `TameRel`/`WildRel`. The two readings of the relations agree.
- `Marking.toHom` / `univMarking` / `univMarking_map_toHom`: markings of profinite `P` ↔
  continuous homs `F₄ ⟶ P` (universal property round-trip; `homEquiv_symm_of` added).
- `IsAdmissibleU` (admissibility of an open normal subgroup via its canonical finite quotient),
  `NA` (iInf over the admissible subtype; normal + closed), **`GammaA := profiniteQuotient NA`**.
- `NA_le_ker`: `N_A ≤ ker f` for every admissible continuous `f` into ANY finite group — via
  `surjective_of_map_generates`, kernel-as-OpenNormalSubgroup, and admissibility transfer along
  `F₄ ⧸ ker f ≃* P` (`quotientKerEquivOfSurjective`; its `mk`-evaluation is `rfl`). This
  certifies the open-normal encoding captures the paper's whole class `Q_A`.
- **`main_presentation_literal : Nonempty (ContinuousMulEquiv GammaA AbsGalQ2)`** — Theorem 1.2
  as printed, sorried; route documented (Prop. 2.3 + `main_presentation` + tower).
- Sanity: `isAdmissible_markS3_toHom` (the App-B `S₃` marking classifies an admissible
  quotient — pure plumbing round-trip) and `gammaA_surjective_s3` (`Γ_A ↠ S₃` via
  `quotientLift`): the construction is nonvacuous.

Lean gotchas: keep ONE coercion in bridge statements (`f.toMonoidHom` application, matching
`Subdirect.lean`'s `map_*`; the CMH coercion is defeq but simp-invisible); Lean's
surjectivity-transfer through `quotientLift` needs term-mode `trans` (rw motives fail across
the `GammaA`-vs-`F₄⧸NA` defeq); `NA` noncomputable (`FreeProfiniteGroup` is).

Step-2 entry point is now concrete: **Prop. 2.3** (`Nat.card (ContSurj GammaA G) =
admissibleCount G`) from `NA_le_ker` + bridges + `Subdirect.lean` + `quotientLift`.
