# T2 recon evidence (Tau Ceti discharge campaign)

Scratch Lean files written by the T2 recon lanes, kept as starting points for the adapter tickets.
The recon memo [`../tauceti-t2-recon.md`](../tauceti-t2-recon.md) explains every file; its summary
table says which lane each one closes. These are **prototypes, not library code**: they live outside
every `lean_lib` (nothing builds them), they are exempt from the board's file-ownership rule only
because no ticket owns them, and each adapter ticket must re-do the work in its own
`GQ2/TauCeti/<id>.lean` under the board protocol (module style, no top-level `open TauCeti`,
no import of `GQ2.Prop32`/`GQ2.Foundations.Interfaces`; see memo, cross-cutting finding 5).

Status at Tau Ceti `706344c35` / Mathlib `cfc55fc58` (re-checked when committed): every file
elaborates with `lake env lean <file>` from the repository root, contains no `sorry`, and every
`#print axioms` in them is within `propext, Classical.choice, Quot.sound`, except
`prop/defeq_module_FAILS.lean`, which is kept **because** its `rfl`s fail (it documents that Tau
Ceti definitions are not exposed to `module` files).

To run one, the Tau Ceti modules it imports must be unpacked from the cache once:

```bash
export LAKE_CONFIG=$PWD/.lake/tauceti-lake-cache.toml LAKE_CACHE_DIR=$PWD/.lake/cache
lake build TauCeti            # unpacks all 15,395 modules from the cache, about 2 minutes
lake env lean docs/orchestration/tauceti-t2-evidence/recip/draft_b5_b10.lean
```

| file | contents |
|---|---|
| `galois/a1_b11a_prototype.lean` | A1: `kEmb`, `range_extend_kEmb`, `galEquivFixing`, `fixingEquivTC`, `rho`, compactness of `↥k.fixingSubgroup`; B11a: Tau Ceti half `cup_gq2KummerChar_eq_zero_iff` |
| `cohom/evidence/a2_dict_propositional.lean` | A2: H¹/H² dictionary by the propositional route, restriction naturality |
| `cohom/evidence/a2_cup.lean` | A2: `trivialCupPairing` ↔ `(trivialF2TopPairing G).cup 1 1`, `cup11` compatibility |
| `cohom/evidence/a2_importall.lean`, `a2_nonmodule.lean` | A2: the `rfl` routes (`import all`, non-module), not recommended |
| `cohom/evidence/b7_proof.lean`, `b7_finrank_workaround.lean` | B7: the field, modulo A2's H¹/H² equivalences; the `finrank_self` instance workaround |
| `cohom/sigs.txt` | verbatim signatures of the A2/B7 declarations |
| `prop/proto_p1.lean` | P1: `proPKernel`, `maxProPEquiv`, `Delta ≃ₜ* freeProP 2 (Fin 2)`, `zpowZtwo = padicPow`, pro-p presentation equivalence, `GQ2.D0 ≃ₜ* demushkinD0` |
| `prop/proto_zhat.lean` | P1: `Zhat ≃ₜ* zHat.{0}`, `zhatProjTwo = component 2` |
| `prop/proto_b8.lean` | B8: complete `GQ2.PeripheralCyclotomicAction` |
| `prop/proto_absgal.lean`, `defeq_*.lean` | probes for the definitional-equality answers (T2 questions 1, 2) |
| `tate/b6check.lean` | B6: `exists_absoluteGaloisGroup_equiv` (T2 question 4), `bijective_of_perfect` (question 3), the instance package at a finite `K` |
| `sw/test1.lean` … `test5.lean` | B9: probes for shapes, trace forms, cochain identities, instances |
| `recip/draft_b5_b10.lean` | B5: complete `localReciprocity_tauceti`; B10: complete `tameQuotient_tauceti` |
| `orient/adapter_sketch.lean` | B3c: complete `dyadicOrientation_tauceti` (imports `GQ2.Prop32`: replace that import before landing) |
