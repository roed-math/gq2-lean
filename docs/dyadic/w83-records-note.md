# W83-RECORDS lane note

Lane targets: (A) strengthen the branch-producer existentials so they carry the marking, and
(B) instantiate `GenAsmRowResidual.cand` at the tied quadratic rows.
Base `23041e0f`; new module `GQ2/Dyadic/Instances/CanonicalRecords.lean`, prefix `canRec`.

## §0 The site census, verified against the Lean

The defect (W82-CAND caution 2): the branch producers return `∃ G : GenAsmBranch K B,
G.pres = S`, which forgets `G.nuP`, while `GenAsmRowResidual.cand` and the three ASK fields are
all stated at `G.nuP` and every committed certificate producer lives at the row's canonical
marking.

`grep` for `∃ G : GenAsmBranch` returns 36 hits; all but a handful are re-exports that apply an
earlier producer. The sites that **construct** the datum (a structure instance followed by
`rfl`, so the marking is chosen right there) are, verified by reading each:

| # | declaration | file:line | row | marking chosen |
| --- | --- | --- | --- | --- |
| 1 | `genAsm_branch_of_evenN` | `GeneralAssembly.lean:691` | `.N0 α h` | the argument `nuP` |
| 2 | `genAsm_branch_of_evenM` | `GeneralAssembly.lean:706` | `.M0 α h` | the argument `nuP` |
| 3 | `genAsm_branch_of_oddSq` | `GeneralAssembly.lean:735` | `.L h` | the argument `nuP` |
| 4 | `genAsm_branch_of_oddSq_canonical` | `GeneralAssembly.lean:762` | `.L h` | `lNu h` |
| 5 | `mpcCert_genAsmBranch_of_orientedMpc` | `Instances/MpcCertificate.lean:407` | `.Mpc α r ε η 0` | `mpcNu α r pp hα1` |

That is the five, and the grant covers exactly these.

**A sixth construction site exists and is deliberately NOT one of the five.**
`mpcPiv_genAsmBranch_sqrtNegTen` (`Instances/MpcPivot.lean:496`) builds its own datum with
`nuP := mpcPiv_nuZtwo (fieldUni_nuPullbackM B e)`, the *transported* marking, and its own
docstring already says so in terms: "What this branch datum does **not** carry is that the
marking is the row's canonical `mpcNu 2 1 1`." It cannot be strengthened to the canonical
marking, because no comparison of the transported marking with `mpcNu` exists in this tree. The
tied statement at that row is the sibling `mpcPiv_genAsmBranch_sqrtNegTen_of_shift`
(`MpcPivot.lean:456`), which routes through site 5 and therefore does carry `mpcNu`; it is
conditional on `MpcPivShift 2`. Reported, not taken.
