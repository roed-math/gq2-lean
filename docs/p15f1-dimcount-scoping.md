# P-15f1 — scoping the final dimension count (`#X₊ = 2^m`)

**Date**: 2026-07-06 (Opus).  **For**: the last open piece of `lemma_6_17_dim` after the
cohomological inputs (`hinf`, `hext`) are handled.

## 0. Where we are

Everything in `lemma_6_17_dim` reduces to one number: **`#X₊ = 2^m`** (with `#V = 2^{2m}`,
so `#X₊² = #V = #H¹` — the banked `card_H1_eq_card_of_simple` gives `#H¹ = #V`).  Two banked
reducers both bottom out here:

* **Route A** — `DeepPart.card_deepPart_sq_of_selfperp` needs `hself : X₊ = X₊⊥` under the
  polar of `Q⁰loc` (= the B6 Tate cup pairing, `polar_Q0loc`).
* **Route B** — `LocalKummer.dim_deepPart_of_data` needs a `DeepKummerData` instance (the
  filtration `Hom`-count `card_fam`/`card_deepFam` + `hpair`/`hmid`).

Both converge on the same content; the analysis below shows the split into a **cheap upper
bound** and an **expensive lower bound**, and that the expensive half is where Lemma 6.11
genuinely enters.

## 1. Upper bound `#X₊ ≤ 2^m` — isotropy (no 6.11)

`X₊` is totally isotropic under the Tate pairing `P = polar(Q⁰loc)`: for deep classes
`x, y ∈ X₊`, `P(x, y) = 0`.  Given that, **`LocalKummer.card_sq_le_of_isotropic` (landed,
std-3)** gives `#X₊² ≤ #H¹ = 2^{2m}`, i.e. `#X₊ ≤ 2^m`.

**Remaining for the upper bound = the isotropy itself**: `P(x,y) = 0` for `x, y ∈ X₊`.  By
`polar_Q0loc`, `P(x,y) = ι_F(cup₁₁(polarBihom) y x)` — the cup product of the two Kummer
classes.  For deep classes (all scalar coordinates in `U_{e+1}(K)`), this is the Hilbert symbol
`(β_x, β_y)`, which vanishes because `U_{e+1} ⊆ U_{e+1}^⊥ = U_{2e−(e+1)+1} = U_e` — the (94)
orthogonality relation.

> **✅ Ingredient 2 BANKED 2026-07-06 — as theorems, NO new axiom** (`HilbertLedger.lean`
> Tier 5): `cup_deep_deep` / `cup_deep_neg_one` / `cup_deep_self` (std-3 ∪ {B11a});
> `normForm_of_deep` etc. std-3 sorry-free (Brahmagupta descent + `sq_of_near_one`; FV VII §4
> Ex. 4c/5b are exercises ⟹ proved per user directive).  Bridge:
> `norm_sub_one_lt_of_isDeepUnit` (LocalKummer).  Ingredient 1 (the cup₁₁-on-`H¹(G,V)` →
> scalar-symbol-over-`K` reduction) = the monomial-expansion bridge, gated on `lemma_6_11`
> (P-15f4).

**Ingredients:**
1. **cup = Hilbert symbol** on Kummer classes — relate `cup₁₁(polarBihom)` on `H¹(N,𝔽₂)`-image
   classes to the local Hilbert symbol.  This is the P-15b/`GaussSigns` and `HilbertLedger`
   territory (the symbol is `B7′`/`B11`); the bridge to the *cup* form is the (93)-cochain
   layer (`graphPullback_add_sub_mem_B2`, `polar_Q0loc` — both banked).  Non-trivial but the
   pieces exist.
2. **(94) `U_{e+1} ⊥ U_{e+1}`** — `U_i^⊥ = U_{2e−i+1}` from L3/eq. (94).  **NOT** currently a
   leaf (deferred from B13); the minimal instance needed is `(U_{e+1}, U_{e+1}) = 0`, which a
   conductor/depth bound on the symbol may give directly from `B11a` without the sharp (94)
   (see `docs/p15f1-axiom-proposal.md` §4.3).  **This same isotropy is exactly P-15f2's
   free-orbit vanishing** — shared work; coordinate with f2.

> **⚠ ROUTE CORRECTION 2026-07-06 (from paper §6.3 p. 34).** The paper's *dimension* clause does
> **not** use isotropy at all — it is the **graded route**: `H¹ ≅ Hom_{H_V}(V^∨, M_K)`,
> `Hom(V^∨,−)` exact (6.11), Hilbert duality pairs depth `j`↔`2e−j`, self-duality `V≅V^∨` gives
> equal multiplicities, middle `j=e` empty (6.10) ⟹ `dim X₊ = ½`. So the closure target is the
> **`DeepKummerData` construction** (`dim_deepPart_of_data`), i.e. the graded-Hom-over-filtration
> count `card_fam`/`card_deepFam` + `hpair`/`hmid` — §§1–2 below (the isotropy upper bound +
> Hom-exactness lower bound) are an *alternative* cross-check, not the paper's route. The (94)
> orthogonality (now banked as `cup_deepClasses`) belongs to the **vanishing** clause (f2), not
> the dim clause.

## 2. Lower bound `#X₊ ≥ 2^m` — this is where 6.11 lives

Left-exactness of `Hom(V^∨, −)` gives only `#X₊ = #Hom(V^∨, U_{e+1}) ≤ #Hom(V^∨, M_K) = 2^{2m}`
— an upper bound, useless here.  A **lower** bound needs surjectivity onto the deep graded
pieces, i.e. `Ext¹_{𝔽₂[H_V]}(V^∨, U_{e+1}) = 0` — **projectivity of `V^∨` (Lemma 6.11)**.  The
coprime-averaging trick that discharged `hinf`/`hext` provably does **not** substitute:
`(V ⊗ U_{e+1})^I ≠ 0` at the deep contributing depths, so `H¹(H_V, V ⊗ U_{e+1})` need not
vanish.

Equivalently (Route B, cleaner to formalize): with the filtration `M_K ⊇ U_{e+1} ⊇ …`,
projectivity gives the **multiplicativity**
`#Hom(V^∨, M_K) = #Hom(V^∨, U_{e+1}) · #Hom(V^∨, M_K/U_{e+1})`, and the **graded self-duality**
`#Hom(V^∨, U_{e+1}) = #Hom(V^∨, M_K/U_{e+1})` (from `V ≅ V^∨` + the Hilbert pairing pairing
depth `j` with `2e−j`, Lemma 6.10 killing the middle) forces both factors `= 2^m`.

### Lemma 6.11 (the mountain)

`V, V^∨` are projective `𝔽₂[H_V]`-modules.  Proof = **Higman's criterion**
(`𝔽₂[H_V]`-projective ⟺ `𝔽₂[P]`-projective, `P` a Sylow-2) + a **Clifford** weight-orbit
argument (`V|_P` is free because `P` permutes the odd-order inertia weights freely).  Neither is
in Mathlib.  References (proof-side): Webb, *A Course in FGRT* (free PDF), Ch. 5 §5.3 (Clifford)
+ Ch. 11 (relative projectivity); originals Clifford (Ann. Math. 38, 1937), Higman (Duke 21,
1954).  Discharges `Ext¹(V^∨, −) = 0`, i.e. `Hom(V^∨, −)` exact on the filtration.

## 3. Recommended order of attack

1. **cup = Hilbert-symbol bridge + (94)-minimal isotropy** → discharges the *upper bound*
   `#X₊ ≤ 2^m` via `card_sq_le_of_isotropic` (landed).  Shared with **P-15f2**; do it there or
   jointly.  No new axiom if the `(U_{e+1}, U_{e+1})=0` instance comes from `B11a`+conductor;
   else a small L3 leaf.
2. **Lemma 6.11 in-repo** (Higman + Clifford) — the lower bound.  Large, self-contained modular
   representation theory; the one genuine mountain.  *Or* leaf its consequence
   `Ext¹(V^∨,−)=0` (census decision, `docs/p15f1-axiom-proposal.md` §4.2 recommended prove).
3. Assemble: build the `DeepKummerData` fields (`card_fam`/`card_deepFam` from 1+2 over B12/B13;
   `hpair`/`hmid` from the graded self-duality + Lemma 6.10), then `dim_deepPart_of_data`.

## 4. What is already banked toward this

* `card_sq_le_of_isotropic` (upper-bound engine, std-3) — **NEW this session**.
* `card_sq_of_selfperp`, `mem_of_pairing_eq_zero` (Route A pairing engines, DeepPart).
* `polar_Q0loc` (pairing = cup), `isQuadraticFp2_Q0loc`, `nonsingular_Q0loc` (DeepPart).
* `dim_deepPart_of_data` + the whole Layer-2a/2b identification (LocalKummer).
* `card_H1_eq_card_of_simple` (`#H¹ = #V`, B7).
* `deepPartSubgroup` (X₊ an AddSubgroup), `card_deepPart_sq_of_selfperp` (Route A reducer).
* B12 (Kummer `M_K ≅ H¹(N)`), B13 (unit filtration graded counts).

The gap is exactly §1-ingredient-1 (cup=Hilbert), §1-ingredient-2 ((94)-minimal), and §2
(Lemma 6.11).  The first two are shared with P-15f2; the third is the isolated mountain.
