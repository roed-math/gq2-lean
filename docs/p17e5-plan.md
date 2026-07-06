# P-17e5 execution plan — κ⁰ normal form + final assembly (closes `kappa0_exists`)

> **✅ EXECUTED (same session): `kappa0_exists` is PROVED, std-3.**  The plan below was
> followed with two in-flight adjustments: the faithful image uses `MulAction.toPermHom` into
> `Equiv.Perm V` with a bespoke `letI` action (2026-mathlib's `toAddAut` lands in
> `Multiplicative (AddAut V)`), and 2-torsion is derived inside `kappa0_exists_tame` from
> nonsingularity + simplicity.  Full closure notes: board row P-17e5.

**Claimed:** Fable, 2026-07-06b (same session as the P-17e4 closure).  **Target:** discharge
the `sorry` of `GQ2.SectionNine.kappa0_exists` (paper Lemma 6.3) — std-3, no new axioms.

## Route (deviation-lite: direct invariant refinement instead of full orbit-polynomial sums)

The paper decomposes the extended form `q_W` on `𝔽₂[H]^K` into orbit polynomials
`S_j`/`C_{j,k,g}`/`E_{j,g}` and sums their data.  We shortcut the `S`/`C` layers: the whole
square+free part of `q_W` admits a **single invariant biadditive refinement** built from the
relative-position coordinates, so only the **involution corrections** `E_{n,u}` (Lemma 6.2 =
P-17e3's `invOrbitDatum`, the only genuinely non-`m=0` piece) are subtracted orbit-by-orbit.
Equivalent to the paper's normal form, with far less case machinery.

### The core (new file `GQ2/KappaNormalForm.lean`, own file, imports
`RegularSummand + InvolutionDatum` — NOT `SectionNine`, which will import US for the splice)

1. **Carrier** `PermW H K := Fin K → H → ZMod 2` (type synonym, own
   `DistribMulAction H` instance `(h•F) n x = F n (h⁻¹x)`, mirroring `RegRep`).  Basis =
   `regBasis` (RegularSummand, reused).  Every `q`-coordinate is orbit-constant:
   `d n := Q (bas n 1)`, `β n m u := polar Q (bas n 1) (bas m u)` — invariance in the
   relative-position coordinate `u = x⁻¹y` (the H-action on `I = Fin K × H` is free, so
   ordered-pair orbits ↔ `(n, m, u)`).
2. **Expansion lemma** (ordered-pair form, no `Sym2`): for `f₀ : I → I → 𝔽₂` with
   `f₀ i i = Q(e_i)` and `f₀ i j + f₀ j i = polar Q (e_i) (e_j)` (`i ≠ j`):
   `Q F = ∑_{i,j} F_i F_j f₀ i j`.  Induction on the support finset;
   coefficients are 0/1 so `F = ∑_{supp} e_i`.
3. **Bad locus** `Bad := {(n,u) | u² = 1, u ≠ 1, β n n u = 1}` — exactly where an invariant
   refinement is obstructed (the swap `(i,j) ↦ (j,i)` lies in the SAME free ordered-orbit
   iff `u` is an involution; invariance then forces `f₀ i j = f₀ j i`, impossible against
   `β = 1`).  This is the extraspecial obstruction of the scoping note, localized.
4. **Involution correction transport**: instantiate `invOrbitDatum` at `G := H, N := ⊥`,
   `gbar := mk u`; transport to `H` acting on the block `H → ZMod 2` via
   `comapHom (mk' ⊥)` (a `MulEquiv` by `⊥`-triviality) + `comap` along the reindexing
   `(H → ZMod 2) →+ RegRep ⊥`, then `comap` along the block projection `PermW →+ (H → 𝔽₂)`.
   Needed facts about the transported square map `E_{n,u}`:
   `E(bas m x) = 0`; `polar E (bas m x) (bas m' y) = [m = m' = n ∧ y = xu ∨ x = yu]`
   (finsum-single over the `⟨mk u⟩`-coset space); `IsQuadraticFp2 E` (from
   `invOrbitDatum_f_add_left/right` + `f_polar`); `IsInvariant` (from the datum:
   `m_quad` at `(v,v)` + 2-torsion).
5. **Normal form** `exists_datum_of_invariant_quadratic`: `Q' := Q + ∑_{Bad} E_{n,u}` has
   all involution-β's zero; define `φ n m u := if (n,u)=(m,1)-diag then d n else β' n m u * χ n m u`
   with the half-indicator `χ` (linear order on `Fin K` + a `Fintype.equivFin`-order on `H`;
   `χ n m u + χ m n u⁻¹ = 1` off involutions), set
   `f(F,G) := ∑_{(n,x),(m,y)} F n x · G m y · φ n m (x⁻¹y)` — biadditive, invariant
   (relative-position), diagonal `= Q'` by the expansion lemma ⟹
   `isEquivariantFactorSet_of_biadditive_invariant` (private copy) gives the `m = 0` datum;
   add back the `E`-data (`IsEquivariantFactorSet.add` copy, `Finset`-induction sum lemma);
   `Q' + ∑E = Q` in char 2.
6. **Private copies** of the small SectionNine assembly layer (they live in namespace
   `GQ2.SectionNine`, which we cannot import): `of_invariant`, `of_biadditive_invariant`,
   `.add`, `.comap`, `.comapHom`, `of_split`, `exists_biadditive_refinement`, `of_odd`.
   (The scoping note already anticipated promoting these to a shared low file; deferred —
   copies are private here.)

### The assembly (`kappa0_exists_tame`, in the new file)

Over abstract finite `H` acting on `V` with tame pair `(s,t)` (`hgen`, `hrel`), `q` invariant
quadratic nonsingular, `V` finite nontrivial simple (AddSubgroup form):
* Derive `hV2 : ∀ v, v+v = 0`: the 2-torsion subgroup is stable, and `⊥` would give `|V|` odd
  ⟹ every `polar q v ·` is the zero hom ⟹ `Nonsingular` + `Nontrivial` contradict.
* **Faithful-image reduction without quotient groups**: `α := DistribMulAction.toAddAut H V`,
  `Ĥ := α.range ≤ AddAut V` with the tautological (apply) action — faithful, finite;
  `π := α.rangeRestrict` surjective; tame pair = images; datum over `Ĥ` pulls back by
  `comapHom` (copy).
* Dichotomy on `t̂`-action:
  - trivial ⟹ `t̂ = 1` (faithful) ⟹ `|Ĥ|` odd (else Cauchy gives an involution commuting
    with `t̂ = 1`, killed by `two_torsion_of_centralizer_eq_one` — P-17e4's O₂-linchpin) ⟹
    `kappa0_exists_of_odd` (copy).
  - nontrivial ⟹ **`lemma_6_11_of_tame_pair`** (new abstract-pair generalization in
    `RegularSummand.lean`; the `Ttame`-hom versions become wrappers — this resolves the
    banked e5 design flag by statement alignment, no `Ttame` universal property needed)
    gives the split pair `(ι, ret)` into `PermW Ĥ K`; `qW := q ∘ ret` is invariant quadratic;
    normal form (5) gives `datW`; `of_split` (copy) pulls back along `ι`.

### The splice (`SectionNine.lean`, one block)

`import GQ2.KappaNormalForm`; replace `kappa0_exists`'s `sorry`: unpack `htame`/`hsimple`,
transport `hinv`/simplicity along the surjection (surjectivity dictionary), call
`kappa0_exists_tame`, pull back with SectionNine's own `comapHom`.  `hns` is consumed by the
`hV2`-derivation only.

### Gates

Per-file `lake build GQ2.KappaNormalForm GQ2.RegularSummand GQ2.SectionNine`; whole
`lake build`; `check_axioms` (census 15 unchanged; SectionNine stays allowlisted for its
OTHER P-17 sorries); `#print axioms GQ2.SectionNine.kappa0_exists` = std-3 expected
(no B-axioms anywhere in this chain).

### Risk register

* `invOrbitDatum` transport plumbing (`Quotient.out` through two quotient layers) — confined
  to step 4; the polar/diag facts are computed on the *transported* map directly.
* `finsum` ↔ `Finset.sum` interface at the `RegRep ⊥` boundary.
* Instance discipline: `PermW`/`RegRep ⊥` type synonyms must not leak the pointwise `Pi`
  action — all instances on synonyms only.
* The χ case-bash (n/m order × u vs u⁻¹) is elementary but fiddly; `ord`-injectivity via
  `Fintype.equivFin`.
