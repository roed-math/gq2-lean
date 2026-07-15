# Paper-facing Lean API

The public mathematical API is approximated by the named results in the
[maintained web writeup](https://roed314.github.io/gq2/). The paper is being reorganized, so
displayed numbers such as “Lemma 8.3” are metadata rather than stable API identifiers. The original
source snapshot remains at
[`paper/A_Profinite_Presentation_for_G__Q_2.pdf`](../paper/A_Profinite_Presentation_for_G__Q_2.pdf).

Each theorem-like block in the rendered HTML has a semantic id such as `lem-covertransform` or
`thm-main`, and PaperForge records its Lean targets in `data-lean-ref` attributes.  These two pieces
of metadata form the crosswalk:

- the semantic HTML id identifies the mathematical result across renumberings;
- the Lean target identifies its current formal declaration;
- the displayed theorem number may change without forcing a Lean rename.

Regenerate the current inventory from a local paper build with

```bash
python3 scripts/paper_api_audit.py ~/claude/gq2-paper/output/web/paper.html
```

The audit was rerun after the 2026-07-14 module split: the rendered paper contains 81 named results
and 111 links into this Lean formalization. All linked declarations remain public and documented;
the split changed their source modules where appropriate but not their public names.

## Visibility policy

A declaration remains public when at least one of the following holds:

1. the paper links to it directly;
2. it occurs in the type of a public declaration;
3. another Lean source file refers to it;
4. it is documented as a reusable mathematical or architectural interface.

An undocumented declaration may be made private only when it is absent from the paper crosswalk,
has no use in another tracked Lean source, and does not occur in another declaration's type.  This
conservative rule keeps proof-local calculations out of the API without hiding reusable
mathematics.  Existing number-based Lean names are not compatibility promises; new API names should
describe their mathematical content, and future renumbering should update the paper crosswalk
rather than propagate numbers through implementation code.
