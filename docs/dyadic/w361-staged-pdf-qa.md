# W361 staged certificate PDF review

2026-09-17, 14:37 UTC. **Review artifact, not an accepted amendment or release.**

Output: `output/pdf/w361-staged-certificates.pdf` (29 pages).
Wrapper: `scripts/w361_staged_certificates.tex`.

PDF SHA-256:
`3cec56dc3adde9ad9982225cbc376904a9284224f23ba0c1a07c72f17a4b71bb`.
Wrapper SHA-256:
`702e75cbcb6d881ea53c62c0a29d448d04662ad938515fbc668487cadf8c48e5`.

The wrapper inputs the four checked staged packet appendices, not copied word
or matrix formulas. Their combined packet hashes are:

| Specimen | Packet SHA-256 |
|---|---|
| mobile-alpha2-r1-p0-h0 | `5b6aa7356d32646c9627889e046320b9f1861e936c9408cb6098982ced0adff7` |
| mobile-alpha3-r2-p2-h1 | `bb10ab41c5540861473f3cedf9788988e08bf1910a51c5b1608d4f092cec3f18` |
| pair-alpha2-h1-j0 | `f4effaa2198ddc90e6acda083a433794084ccf60c4986bebc3a371648ec46ef0` |
| pair-alpha3-h2-j1 | `c506c6a8352740155453a1090e176437c431e376018c224a194e0c8bbe8d393d` |

The PDF adds no mathematical assertion to those staged packets. Their existing
symbolic-parameter, direct-provenance, editorial-prose and cached-artifact caveats
are printed in each appendix and documented in the generated directory README.

## Layout work and verification

The initial compilation exposed four overflowing word lines. The revised word
renderer names both repeated and sufficiently large exact subtrees. Its backward
references expand to the unchanged hashed AST, with a checked bound of eleven
visible constructor/reference nodes per definition. All142 renderer tests pass,
and all four original template hashes remain unchanged after Lean replay.

The final compilation has **zero overfull and zero underfull boxes**. All29 pages
were rendered to PNGs. Root visually inspected pages1–14; an independent reviewer
inspected every page15–29, including a second144-dpi inspection. No clipped or
missing formulas, lost word definitions, broken matrices, footer collisions or
orphaned headings were found. Very long Lean declaration names can wrap inside
an identifier (occasionally leaving one letter on the next line); this is a
cosmetic consequence of preserving the literal reference, not missing content.

After moving the wrapper to its durable script location, the PDF was regenerated
and all29 final rendered PNG hashes matched the visually reviewed renders exactly.
The final PDF above is that regenerated copy. This visual check is separate from
the strong Lean/AST/type-transcript checks, all of which passed through
`scripts/w361_check_staged.sh` at the recorded shared-cache snapshot.

Recompile from the repository root:

```sh
mkdir -p tmp/pdfs
pdflatex -jobname=w361-staged-certificates -interaction=nonstopmode \
  -halt-on-error -output-directory=tmp/pdfs scripts/w361_staged_certificates.tex
```

PDF metadata can change its byte hash on recompilation even when the rendered
pages are identical. The hash above identifies this reviewed file, not a claim
of byte-for-byte reproducible PDF generation across toolchain environments.
