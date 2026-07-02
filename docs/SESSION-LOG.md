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

---

# Session 2026-07-02 (Fable, cont.): T-01 + T-02 — discrete modules and continuous H⁰/H¹/H²

Two new files, build green, every declaration at the standard axioms (several need only
`propext`/`Quot.sound`).

**`GQ2/DiscreteModule.lean` (T-01, folded in):** the module conventions — pure Mathlib
typeclasses, no new structures (`AddCommGroup` + topology + `DistribMulAction` +
`ContinuousSMul`, `DiscreteTopology`/`Finite` as needed) — validated by the smoothness facts:
`isOpen_stabilizer`, `isOpen_iInf_stabilizer` (open action kernel, finite `M`), and
`exists_openNormalSubgroup_smul_eq_self` (over profinite `G` the action factors through a
finite quotient — the future bridge to finite group cohomology, T-03).

**`GQ2/Cohomology.lean` (T-02, namespace `GQ2.ContCoh`):** continuous inhomogeneous cochain
cohomology in degrees ≤ 2 (Serre GC I §2.2), the coefficient system for B3/B6/B7/B9.
- Carriers: plain function spaces; continuity carried by subgroups (`C1`, `C2`);
  `Z1 = C1 ⊓ ker δ¹`, `Z2 = C2 ⊓ ker δ²` (closure free, mirrors Mathlib `groupCohomology`),
  `B1 = δ⁰(M)`, `B2 = δ¹(C1)`; `H1`/`H2` = quotients (`AddCommGroup` instances), `H0` =
  invariants subgroup. Readable membership: `mem_Z1_iff`, `mem_Z2_iff` (Serre's identity).
- Chain sanity: `dOne_comp_dZero = 0`, `dTwo_comp_dOne = 0`; `B1_le_Z1`, `B2_le_Z2`;
  `Z1_apply_one`.
- **Functoriality via one workhorse**: pullback along a compatible pair (`π : G →ₜ* Q`,
  `f : N →+ M` continuous, `f (π g • n) = g • f n`) in all three degrees
  (`H0comap/H1comap/H2comap`); restriction `res0/1/2` = `(subgroup inclusion, id)` — Mathlib's
  `Subgroup.continuousSMul` instance makes the compatibility `rfl`; inflation = instantiate the
  source action by `DistribMulAction.compHom` (recipe in docstring; the two-actions-on-one-type
  encoding is deliberately avoided).
- Trivial-action stress trio (wrapper-free form of the acceptance test): `mem_Z1_iff_of_trivial`
  (`Z¹` = continuous additive-style homs), `B1_eq_bot_of_trivial`, `H1equivZ1OfTrivial`
  (`H¹ ≃+ Z¹`), plus `H0_eq_top_of_trivial`.
- Generality: defs for arbitrary topological groups and topological modules; profiniteness and
  discreteness only enter theorems.

Lean gotchas recorded: theorems consumed via `.mp`-dot-notation must have their carriers
**implicit** (explicit section variables silently break generalized field notation — restructure
into a defs-section (explicit) + lemmas-section (implicit)); hypotheses used only in *proofs*
need `include htriv in` (section variables are auto-included from statements only); the
`QuotientAddGroup.map` monotonicity goal is `comap`-membership (rewrite `mem_comap` before
`mem_addSubgroupOf`); range/image membership equalities against subtype coercions are best
consumed via `congrFun … |>.symm` (defeq) rather than `rw`.

Next per plan (wave 2): T-03 (cohomology lemma layer + finite-`G` comparison), T-04 (cup
products relative to a pairing — the `Z`-level API is ready for it), T-13 (Kummer), T-15 (μ);
T-05/T-07/T-00 still open for Opus. Note for T-09: state Demushkin ranks via `Nat.card`
(`= 2^n`, `= 2`) to avoid `Module 𝔽₂` instances on quotient types.

---

# Session 2026-07-02 (Opus): T-03 + T-04 — cohomology lemma layer and cup products

Extended `GQ2/Cohomology.lean` (T-03) and added `GQ2/CupProduct.lean` (T-04); build green, all
declarations at the standard axioms.

**T-03 (lemma layer, in `Cohomology.lean`):**
- `mapCoeff0/1/2` — coefficient functoriality, the `π = id` specialization of the `Hicomap`
  workhorse (a G-equivariant continuous `f : N →+ M` induces `Hⁱ(G,N) →+ Hⁱ(G,M)`).
- `inf0/1/2` — inflation, the `f = id` specialization along `π : G →ₜ* Q` with the `Q`-action on
  `M` agreeing through `π` (`hπ : π g • m = g • m`).  So restriction/inflation/coefficient-maps
  are all one construction.
- `Z1_apply_inv` (`φ(g⁻¹) = −g⁻¹·φ(g)`).
- **Deferred, documented in-file**: finite-`G` comparison to Mathlib `groupCohomology.H1/H2`.
  Mathlib's is over `Rep k G` (ModuleCat, no topology); the comparison needs a `Rep ℤ G` bridge
  matching inhomogeneous-cochain conventions — a step-3 *verification* task, not needed to state
  any B-axiom.  The trivial-action characterization (T-02) already validates `H¹`.

**T-04 (cup products, `CupProduct.lean`):** relative to a `G`-equivariant pairing
`μ : M →+ N →+ P`, coefficients `M, N` **discrete** (finite-discrete axiom setting → every cup
cochain is continuous with no continuity hypothesis on `μ`).
- `cup11 : H¹ →+ H¹ →+ H²` — the B3-critical one.  Cochain `(a∪b)(g,h)=μ(a g)(g·b h)`; cocycle
  identity `cup11_mem_Z2`; **descent in both variables** (`cup11_{a,b}cobound`, each using the
  opposite factor's cocycle identity).
- `cup02 : H⁰ →+ H² →+ H²`, `cup20 : H² →+ H⁰ →+ H²` — the shapes B6 needs; single-variable
  descent (the other factor is `H⁰`-invariant, which trivializes the `(g₁…gₚ)·` action).
- Bilinearity by construction (`→+ →+`); `∪0=0`/`0∪=0` are `map_zero`; `cup11_mk_mk` computes on
  explicit cocycle classes; `cup11_mapCoeff_target` = coefficient naturality
  (`cup(fP∘μ)=mapCoeff2 fP∘cup(μ)`, `postPairing` = `(compHom fP)∘μ`).

Assembly pattern that worked (after a fight): build the bi-hom at the **cocycle** level via
`AddMonoidHom.mk'` with **named** function-level `..Fun_add_left/right` helpers (NOT inline
`simp` inside `Subtype.ext`), then descend the quotient slot with a single
`QuotientAddGroup.lift`, using `AddMonoidHom.flip` when the quotient is the second slot (`cup02`).
Lean gotchas recorded: (i) `include hμ in` before any lemma using `hμ` only in its proof — else
"unknown identifier `hμ`" and call-site arity mismatch; (ii) `n.2` for `n : ↥(H0 …)` is a
*membership prop* — `have hn : ∀ x, x • n.1 = n.1 := n.2` before using it in `simp`;
(iii) give each cup cochain its own `continuous_*Fun` lemma so `mem_Z2`'s continuity slot
head-unifies; (iv) function-additivity helpers need `Pi.add_apply` in the `simp` set;
(v) `cup11_mk_mk` is `rfl` because `QuotientAddGroup.lift` computes on `mk`.

Wave-2 cohomology infrastructure (T-01/02/03/04) is now complete.  Remaining Opus wave-2:
T-05 (max pro-p), T-07 (Hilbert symbol), T-00 (CFT survey), plus T-13 (Kummer)/T-15 (μ).
Then wave-3 axiom statements (mostly Fable): B3 uses `cup11` nondegeneracy; B6 uses all three
cups + `mapCoeff`; B7 uses `Nat.card Hⁱ`.

---

# Session 2026-07-02 (Opus): integrate with Hill's continuous cohomology (steps 1–2)

Per user: build cup products on Richard Hill's `rmhi/ctsToDiscrete` continuous cohomology.

**Dependency + bump** (commit e92738a): added ctsToDiscrete as editable path dep `../ctsToDiscrete`;
bumped mathlib 23b0068→ec410d2 (clean 80-commit fast-forward; forced by his transitive dep set).
GQ2 builds unchanged.

**KEY DISCOVERY**: continuous cohomology is now IN MATHLIB (`Mathlib.Algebra.Category.
ContinuousCohomology.Basic`, Hill's work upstreamed at ec410d2) — `continuousCohomology (n) :
Action (TopModuleCat R) G ⥤ TopModuleCat R`, over Mathlib's `TopRep`/`ContRepresentation`.
It is MORE complete than his standalone repo: Mathlib has `continuousCohomologyZeroIso :
continuousCohomology R G 0 ≅ invariants R G` PROVED, whereas his repo `#exit`s + sorries it.
His standalone repo *redefines* the now-upstreamed core, so importing it alongside Mathlib
collides (`ContinuousCohomology.MultiInd.d` double-declared) — it is NOT co-importable. So we
bridge to the canonical Mathlib object (= his upstreamed work), not his repo copy.

**New file `GQ2/CtsCohBridge.lean`** (all standard axioms, build green):
- Step 1 (coefficient bridge): `smulCLM g : M →L[ℤ] M` (= `m↦g•m`); `toContRep : ContRepresentation
  ℤ G M`; `toTopRep : TopRep ℤ G`; `toAction : Action (TopModuleCat ℤ) G` built DIRECTLY (not via
  the `TopRep≌Action` equivalence) so `.V=M`, `(.ρ g).hom = (m↦g•m)` are defeq — keeps invariants
  concrete. (`End` mul is `a*b = b≫a`, so `ρ(gh)=ρ(h)≫ρ(g)` matches `(gh)•x=g•(h•x)`; morphism
  equalities via `ConcreteCategory.ext`.)
- Step 2, i=0 (H⁰ bridge, DONE): `invariantsEquivH0 : (invariants ℤ G).obj (toAction M) ≃+ H0 G M`
  (identity on carriers — the two membership predicates `∀g,(ρ g).hom x=x` and `∀g,g•x=x` are
  DEFEQ, so `⟨x.1,x.2⟩` typechecks both ways, proof is `rfl`); `H0Equiv : (continuousCohomology
  ℤ G 0).obj (toAction M) ≃+ H0 G M` via `continuousCohomologyZeroIso` +
  `Iso.toContinuousLinearEquiv.toLinearEquiv.toAddEquiv`. **Our H⁰ = Mathlib's continuous H⁰.**

**REMAINING (i=1, i=2, cup transport)**: needs the homogeneous↔inhomogeneous n-ary cochain iso in
low degree — Mathlib's OWN open TODO for ContinuousCohomology. Degree 1: inhomog `c:G→M`
(`c(gh)=c(g)+g•c(h)`) ↔ homog `f(g₀,g₁)=g₀•c(g₀⁻¹g₁)`, a chain iso. Substantial (Mathlib's abstract
`Rep R G` analogue is multi-hundred lines). Natural coordination point with Hill/mathlib. Once
H1/H2 bridges exist, CupProduct.lean cups transport (step 3). Documented in CtsCohBridge.lean tail.

Note: ctsToDiscrete path dep is currently dormant (collides with mathlib → not imported). Keep as
contribution reference or remove — user's call.
