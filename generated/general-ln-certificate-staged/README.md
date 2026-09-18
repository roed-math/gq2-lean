# STAGED ten-item L/N0/Npc certificate packets

**Staged proposals only.** Nothing here is owner adoption, acceptance, a census
amendment, an entry in `generated/hash-manifest.json`, a replacement for the five
`generated/appendix/*.tex` skeletons, or a merge gate. No frozen identifier or hash
is changed by these artifacts.

## What is in each packet, and what is actually synchronized

The ledger's ten items are not all in the same state, so the packet says so per item
instead of in general.

| Ledger item | State in these packets |
|---|---|
| 1 exact syntax tree | **generated** from the Lean canonical tree via `w361_general_ln_word_tex` |
| 2 two specializations | checked declarations and stored transcripts; **no generated display** |
| 3 evaluated Fox Jacobian | checked declarations and stored transcripts; **no generated display** |
| 4 invertible operations | **generated** from the actual `FoxCertificate` fields via `w362_ln_fox_tex` |
| 5 reduced normal matrix | **generated** from the actual `FoxCertificate` fields via `w362_ln_fox_tex` |
| 6 Stokes chain identity | checked declarations and stored transcripts; **no generated display** |
| 7 extraspecial Hessian | checked declarations and stored transcripts; **no generated display** |
| 8 quadratic normal form | checked declarations and stored transcripts; **no generated display** |
| 9 affine phase-cover | checked declarations and stored transcripts; **no generated display** |
| 10 same-tree hash | **generated**: word, Fox and combined packet hashes |

"Checked declarations" means: the probe proves the declaration exists, has at most
`[propext, Classical.choice, Quot.sound]`, and prints its elaborated statement, and
`check` compares that stored transcript against a fresh replay. Every section without
a generated display carries an explicit TODO naming the exporter declaration that
would supply one and that does not exist. No formula anywhere is retyped from prose.

One class of declarations is deliberately exempt from the standard-three gate: the
field-selection adapters `FieldFamilyCampaignBoundary.hasSelectedRowResidualRN_l`,
`_n0` and `_npc` inherit the documented standing arithmetic and reciprocity inputs.
The probe prints their full axiom list instead of gating them, and each packet says
so in item 2. Standard-three analytic word certificates do not make the field theorem
axiom-free.

## Artifacts

Fox artifacts, ledger items 4 and 5, uniform in the rank by the `rfl` signature
theorems in `scripts/w362_ln_fox_export.lean`:

| Artifact | Sectors |
|---|---|
| `L-fox-h0-q2`, `L-fox-h4-q2` | unramified, ramified, scalar |
| `N0-fox-h0-q2`, `N0-fox-h3-q2` | unramified, ramified |
| `Npc-fox-h0-q2-r1`, `Npc-fox-h3-q2-r2` | unramified, ramified |

Packets, one per word instance, each with `.packet.json`, `.appendix.tex`,
`.proofs.lean`, `.proofs.txt` and a `.files.json` hash manifest:

| Packet | Word |
|---|---|
| `packet-L-h0` | `lSqW 0`, the frozen L appendix rank |
| `packet-L-h4` | `lSqW 4`, beyond the frozen rank |
| `packet-N0-alpha2-h0` | `nCompactW 2 0`, the frozen N0 appendix parameters |
| `packet-N0-alpha5-h3` | `nCompactW 5 3`, beyond them |
| `packet-Npc-alpha2-r1-h0-num1-den1` | `npcW 2 1 0 (1/1)`, the frozen Npc appendix display |
| `packet-Npc-alpha3-r2-h3-num3-den9` | `npcW 3 2 3 (3/9)`, a nonreduced odd display |

The three packets at frozen appendix parameters carry exactly the frozen word hashes
`d129037c...`, `a940b6ad...` and `08b7742c...` from `generated/hash-manifest.json`. They are
staged proposals all the same: carrying a frozen hash is not entering the manifest.

The Fox export instantiates `q` (and `r`) because `tameRow _ q` really contains `q`
norm terms and `npcRamOps h r` really contains the exponents `2^r`. `q = 2` is used
throughout. Uniformity in `h`, `q` and `r` is carried by the quantified signature
theorems, not by this finite selection of instances.

## Scope the artifacts do NOT establish

* The three L sectors, two N0 sectors and two Npc sectors are Fox records under their
  own hypotheses. Syntax and Fox reduction are not certificate success: the complete L
  certificate needs `q = 2^f` with odd `f`; N0 and Npc need `alpha >= 2` and nonzero
  even `q`; Npc additionally needs an exact `NpcDisplayFor` for the semantic unit.
* The Npc unramified target intentionally stops at the two blocks `A^-1 + 1` and
  `1 + B^-1`, and certifies neither as a unit.
* The Npc completed quadratic proof is the full-offset route. The old two-coordinate
  Gate-E slice, with its invertible `Lc` premise, must not be displayed as the completed
  normal-coordinate proof; it stays valid only in its own scope.
* `RawWord.shadow` in the old exporter is not W361's semantic `tameShadow`, and a
  matching declaration name is not a word-identity proof.
* The direct-source provenance sidecars hash source bytes only. They are not a
  transitive build attestation, and they do not prove that those bytes produced the
  olean artifacts the probe imported.

## Checking

From the repository root, with a matching Lean package/artifact tree:

```sh
export GQ2_W361_PACKAGES=/path/to/matching/.lake/packages
export GQ2_W361_ARTIFACTS=/path/to/matching/lib/lean
bash scripts/w362_check_ln_staged.sh
```

That script runs the W361 staged check first and then the new self-tests, the Fox
replay and the packet replay. The individual steps are

```sh
python3 scripts/w362_ln_fox_tex.py self-test
python3 scripts/w362_ln_certificate_packet.py self-test
python3 scripts/w362_ln_fox_tex.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
python3 scripts/w362_ln_certificate_packet.py check generated/general-ln-certificate-staged \
  --lean-runner scripts/w361_lean_runner.sh
```

Without `--lean-runner` the checks are labelled `artifact-only; NOT Lean-synchronized`:
a rehashed, well-typed but altered artifact can pass structural checking and is not
thereby proved to be the Lean output. Only the replay binds it.
