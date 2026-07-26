# Blueprint chunk for the Γ_R campaign — prepared, not deployed

**Status: HANDOFF ONLY.** Nothing in this file has been applied. The site repository
(`~/claude/gq2-paper`) was **not** touched, no build was run there, and nothing was deployed.
This document contains (a) the Verso markup, written to that repository's conventions, and
(b) the exact steps to integrate it, for whoever decides to publish.

Prepared 2026-07-25 by ticket R41, from a read-only survey of `~/claude/gq2-paper`.

> **Addendum, 2026-07-26 (ticket L6) — the L-campaign landed; §7 is now live.** Still HANDOFF
> ONLY: nothing here has been applied and the site repository remains untouched. But the markup
> below was written for a *conditional* Γ_R theorem, and the theorem is now unconditional
> (`GQ2.Roe.Labute.bLab : BLabHypothesis` is proved, at the standard three axioms, sorry-free).
> Whoever integrates this chunk should therefore:
>
> * apply **§7's edits at the same time** — they are no longer contingent: delete the two
>   "Assume {bpref …}" sentences and the "**conditional**" paragraph in `thm-mainR`, keep the
>   `{uses "prop-labuteclassification"}[]` edges;
> * consider pointing `thm-mainR`'s `(lean := …)` at
>   `GQ2.main_presentation_literal_roe_unconditional` (`GQ2/Roe/Main.lean`), the hypothesis-free
>   form added at L6; `GQ2.main_presentation_literal_roe` still exists and is still the same
>   theorem with the discharged binder, so either reference renders complete;
> * ignore **§1 precondition 2** (expect `sorry` warnings from `import GQ2`): the library is
>   sorry-free repo-wide, so a clean build is now the expected outcome and warnings would mean
>   something is wrong;
> * treat §5's "renders in progress until the L-campaign lands" note as satisfied —
>   `prop-labuteclassification` renders **complete** as of the pinned revision containing
>   `GQ2/Roe/Labute/Assembly.lean`.
>
> The pin precondition (§1 item 1) is unchanged and now needs a revision containing *both*
> `GQ2/Roe/Main.lean` and `GQ2/Roe/Labute/`.

---

## 1. Preconditions — check these before integrating

1. **The pinned Lean checkout must contain the Γ_R capstones.** The blueprint's
   `lakefile.lean` has `require GQ2 from ".." / "formalizations" / "gq2-claude"`. Verso computes
   each node's status (sorry-free / in progress / missing) from its `(lean := …)` reference
   against *that* checkout. Unless it is at a revision containing `GQ2/Roe/Main.lean`, every
   node below renders as missing. Update the pin first.
2. **Expect `sorry` warnings during the blueprint build.** `import GQ2` pulls in the whole
   library, including the in-flight `GQ2/Roe/Labute/` files. Warnings, not errors — the build
   still succeeds.
3. **Verify the four cross-chapter labels** used in the `{uses}` edges below —
   `lem-reconstruction`, `thm-fixedframe`, `prop-epi-semantics`, `thm-main` — still exist in
   the current blueprint. They were present at survey time; an unknown label yields a dangling
   edge rather than a useful one. All other edges are internal to the new chapter.
4. **Decide the provenance-line policy** (see §5). The house style opens every statement body
   with an italic link into the rendered paper, and the Γ_R note is *not* on the site.

---

## 2. The chunk

New file: `~/claude/gq2-paper/blueprint/GQ2Blueprint/Chapters/RoeCandidate.lean`.

Lines 1–9 and the `tex_prelude` line must be **copied verbatim** from an existing chapter
(e.g. `Chapters/Candidate.lean:1-10`) — the prelude is one long Lean string literal with
doubled backslashes, identical across all chapters, and is reproduced here only as a
placeholder to avoid transcription errors.

````lean
import GQ2
import Verso
import VersoManual
import VersoBlueprint

open Verso.Genre
open Verso.Genre.Manual
open Informal

tex_prelude "…COPY THE SINGLE tex_prelude LINE VERBATIM FROM Chapters/Candidate.lean:10…"

#doc (Manual) "A second candidate: the Roe presentation" =>

:::group "ch-RoeCandidate"
A second candidate: the Roe presentation
:::

:::definition "def-gammaR" (lean := "GQ2.Marking.wildValueR, GQ2.Marking.WildRelR, GQ2.GammaR, GQ2.admissibleCountR") (parent := "ch-RoeCandidate")
*Definition 1.1 of the Roe verification note (The candidate $`\Gamma_R`).*

Let $`F` be the free profinite group on $`\sigma,\tau,x_0,x_1`, and put


$$`\sigma_2=\sigma^{\omega_2},\qquad a=(x_0^{-3}\tau)^{\omega_2},\qquad y_1=x_1^{\sigma_2},\qquad c=[x_1,y_1],`


where $`\omega_2\in\Zhat` is the idempotent extracting the $`2`-primary component of a procyclic group. The two relators are


$$`r_\tau=(\tau^\sigma)^{-1}\tau^2,\qquad r_R=(x_0^\sigma)^{-1}a\,x_1^2c.`


A finite quotient of $`F` is *$`R`-admissible* if the distinguished tuple generates it, both relators vanish, and the normal closure of the images of $`x_0,x_1` is a $`2`-group. Let $`\Gamma_R` be the inverse limit of all $`R`-admissible finite quotients, and let $`\mathrm{ac}_R(G)` denote the number of $`R`-admissible markings of a finite group $`G`.

This is the same finite-quotient semantics used for $`\GA`, with the same tame relator and the same pro-$`2` condition; only the wild relator differs. Conventions: $`x^g=g^{-1}xg` and $`[x,y]=x^{-1}y^{-1}xy`.
:::

:::proposition "prop-labuteclassification" (lean := "GQ2.Roe.Labute.bLab") (parent := "ch-RoeCandidate")
*Corollary 3.4 of the Roe verification note (Abstract identification of $`D_R`), an instance of Labute's classification of Demushkin groups.*

Let $`D` be a Demushkin pro-$`2` group of rank $`3` with $`q(D)=2`, and suppose $`D` carries a continuous surjective character $`\chi:D\to\mathbb{Z}_2^\times` that is a Labute orientation. Then $`D` is isomorphic, as a topological group, to


$$`D_0=\angles{A,S,Y\mid A^2S^4[S,Y]}.`


In the formalization this statement is packaged as `GQ2.Roe.BLabHypothesis` and is carried as an **explicit hypothesis binder**, not as an axiom: the census of literature axioms is unchanged at nine. Every theorem below that depends on it says so in its own statement.
:::

:::proof "prop-labuteclassification"
Labute \[Labute 1967\], Théorème 8 together with Théorème 4, at the single instance $`n=3`, $`q=2`, $`f=2`; the argument is presented in Serre's Bourbaki exposé 252. The Lean proof under `GQ2/Roe/Labute/` follows a levelwise route rather than the graded-Lie-algebra one: continuous surjections are built in both directions stage by stage along the $`\lambda`-tower, subject to a congruence invariant on the orientation; a König limit assembles them, and `profinite_hopfian` upgrades the composite to an isomorphism. Ingredients: {uses "lem-reconstruction"}[].
:::

:::proposition "prop-eq154R" (lean := "GQ2.eq_154_R") (parent := "ch-RoeCandidate")
*The paper's equation (154), transported to the Roe source.*

Assume {bpref "prop-labuteclassification"}[]. Then for every finite group $`G`,


$$`\#\Sur(\Gamma_R,G)=\#\Sur(\GQ,G).`


Equivalently, in the counting form, $`\#\Sur(\GQ,G)=\mathrm{ac}_R(G)` for every finite $`G`.
:::

:::proof "prop-eq154R"
The paper's finite-target induction is reused unchanged. It consumes its source only through an interface — topological finite generation, a tame coordinate, a marked pro-$`2` coordinate, and seven counting obligations — which is formalized as the structure `GQ2.SourceData`; the induction is proved once over an abstract source (`GQ2.thm_4_2_of_sources`) and instantiated twice, at $`\GA` and at $`\Gamma_R`. Discharging the Γ_R instance's obligations is the content of the note's §§2–6: the common tame quotient and unramified marking, the marked maximal pro-$`2` quotient, candidate deformation duality for every elementary characteristic-$`2` coefficient module, and equality of the candidate and local quadratic Gauss signs. Ingredients: {uses "def-gammaR"}[] {uses "prop-labuteclassification"}[] {uses "thm-fixedframe"}[] {uses "prop-epi-semantics"}[].
:::

:::theorem "thm-mainR" (lean := "GQ2.main_presentation_literal_roe, GQ2.main_surjection_count_R, GQ2.admissibleCountR_eq_admissibleCount") (parent := "ch-RoeCandidate")
*Theorem 1.2 of the Roe verification note (Replacement theorem).*

Assume {bpref "prop-labuteclassification"}[]. Then


$$`\Gamma_R\cong\GQ.`


Consequently the two candidates present the same group, and their admissible-marking counts agree: $`\mathrm{ac}_R(G)=\mathrm{ac}(G)` for every finite group $`G`.

The isomorphism is *not* obtained by transforming one presentation into the other — no Nielsen or Tietze transformation between them is known, and in fact no explicit word identification of their maximal pro-$`2` quotients exists. The two presentations are reconciled only at the linearized level, where the Roe Fox row is the $`\GA` one with its two wild columns interchanged.

This result is **conditional** on {bpref "prop-labuteclassification"}[]; the corresponding theorem for $`\GA` is not. Granting that one hypothesis, it costs nothing further: its kernel-reported axiom set is identical to that of the $`\GA` theorem.
:::

:::proof "thm-mainR"
Apply the one-sided profinite reconstruction lemma to $`\Gamma_R` and $`\GQ`, using topological finite generation of both and the equality of surjection counts. Ingredients: {uses "prop-eq154R"}[] {uses "lem-reconstruction"}[] {uses "def-gammaR"}[] {uses "thm-main"}[].
:::
````

---

## 3. Registration

Two lines in `~/claude/gq2-paper/blueprint/GQ2Blueprint/Blueprint.lean`:

```lean
import GQ2Blueprint.Chapters.RoeCandidate          -- with the other chapter imports
```

```
{include 0 GQ2Blueprint.Chapters.RoeCandidate}     -- after the last existing {include},
                                                   -- before {blueprint_graph}
```

Place the include **after `Allquotients`**: the narrative runs main theorem → candidate →
proof → status, and a second, conditional theorem about a *different* candidate reads best
after the paper's argument is complete, so that the status section's claims still scope
cleanly to the paper's theorem.

> **Regeneration hazard.** `paperforge/ingest/blueprint_gen.py` leaves a differently-named
> chapter file alone, but it **rewrites `Blueprint.lean` from scratch**. Both registration
> lines above must be re-added after every blueprint regeneration. If the chunk is to survive
> regeneration unattended, take the canonical route instead (§6).

---

## 4. Build and preview

From `~/claude/gq2-paper/blueprint`:

```sh
lake build GQ2Blueprint
lake lean GQ2BlueprintMain.lean -- --run GQ2BlueprintMain.lean --output _out/site
```

Output lands in `blueprint/_out/site/html-multi/`. `blueprint/scripts/ci-pages.sh` runs exactly
these two commands. To see the chunk in the assembled site, run `scripts/build-site.sh` from
`~/claude/gq2-paper` and serve `output/site` locally (the repo's `.claude/launch.json` has a
`gq2-site` config on port 8774).

**Do not run `scripts/deploy.sh`.** That script rsyncs into `roed314/gq2` and pushes; running
it *is* the publish decision, and this chunk has not been reviewed for publication.

---

## 5. Conventions applied, and the two judgment calls

Applied from the survey of the existing chapters:

- Six directives exist and no others: `:::definition`, `:::proposition`, `:::lemma_` (note the
  trailing underscore), `:::theorem`, `:::corollary`, `:::proof`. There is no `:::remark`.
- Attribute order is always `(lean := …) (parent := …)`, with `(tags := "axiom")` appended for
  axiom entries. `(lean := …)` is a **single string** holding a comma-space-separated list of
  fully qualified names.
- Proofs are a **separate** `:::proof "<same-label>"` block immediately after the statement.
- `{uses "label"}[]` appears **only inside proof bodies**, space-separated on one line, with an
  empty bracket payload, terminated by a period. `{bpref "label"}[]` is a link that does *not*
  create a graph edge, and is what statement bodies use.
- Math is `` $`…` `` inline and `` $$`…` `` on its own line, surrounded by blank lines, content
  all on one line. Backslashes are single inside math; they are doubled only inside the
  `tex_prelude` string literal.
- In prose, literal square brackets must be escaped — hence `\[Labute 1967\]`. Backticks and
  asterisks are live markup and are used as such.
- Lean status is computed automatically from `(lean := …)`; there is no `\leanok` to maintain.

Two judgment calls a reviewer should confirm:

1. **Provenance lines are not links.** Every generated statement opens with
   `*[Theorem 1.2 of the paper](../../paper/paper.html#tag) (Title).*`. The Roe note is not
   rendered on the site, so the blocks above use the same italic line **without** a link. If the
   note is published alongside the paper, convert these to links against its rendered anchors
   (`def:GammaR`, `cor:abstractD0`, `thm:main`).
2. **No `\GR`, `\omegaTwo`, or `\Z` macro exists.** The prelude defines `\GA` for `\Gamma_A`,
   `\Zhat`, `\Qtwo`, `\GQ`, `\Sur`, and `\angles{}` — all used above — but has no Γ_R
   counterpart and no bare `\Z`. The blocks therefore write `\Gamma_R`, `\omega_2`, and
   `\mathbb{Z}_2^\times` out in full. Adding `\GR` to `source/main.ptx`'s `<macros>` would
   propagate to every chapter's prelude on the next regeneration; writing them out avoids
   touching shared state. Verso lints KaTeX at elaboration time, so a macro that does not exist
   surfaces during `lake build`, not silently in the rendered page.

A third point is deliberate rather than a judgment call: `prop-labuteclassification` references
the in-flight `GQ2.Roe.Labute.bLab`, so Verso will render it **in progress** for as long as that
proof carries `sorry`s, and flip it to complete on its own when the L-campaign lands. That is
the correct behaviour — do not hand-mark it, and do not point it at the hypothesis definition
instead.

---

## 6. The canonical alternative

If the Γ_R material is to become part of the *paper* rather than a hand-authored blueprint
chapter, the generated route is preferable and survives regeneration:

1. Add the section to the LaTeX draft of record, `inputs/draft/gq2-paper.tex` (never hand-edit
   `source/` — it is generated), or as an insertion under `content/insertions/`.
2. Register the resulting `source/sec-roe-candidate.ptx` in `source/main.ptx`, between the
   `sec-allquotients` and `sec-status` includes; `blueprint_gen.py` reads chapter order from
   those lines.
3. Add the tag → Lean-declaration entries to `crosswalk/lean-decl-map.json`. **Without an entry
   there, no blueprint node is created at all.**
4. Re-run `python3 ~/claude/paperforge/ingest/blueprint_gen.py`, which writes
   `Chapters/RoeCandidate.lean` and regenerates `Blueprint.lean` with the import and include
   already in place.

Under that route the file in §2 becomes the model for the PreTeXt source and the crosswalk
entries rather than something pasted in directly.

---

## 7. When the L-campaign lands — **it landed, 2026-07-26**

`GQ2.Roe.Labute.bLab` is sorry-free (standard three axioms) and every capstone's hypothesis
binder discharges. So the following are not future conditions but edits to apply on integration:

- `prop-labuteclassification` flips to complete automatically. No markup change.
- The two "Assume {bpref …}" sentences and the "**conditional**" paragraph in `thm-mainR` must
  be deleted — that is the only hand edit required.
- The `{uses "prop-labuteclassification"}[]` edges stay: it remains a genuine ingredient, now a
  proved one.
