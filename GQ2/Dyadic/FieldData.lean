/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-5
-/
import GQ2.Dyadic.Certificates.L
import GQ2.Dyadic.LocalGauss.EulerShapiro
import GQ2.Dyadic.LocalGauss.PairingK
import GQ2.HilbertLedger

/-!
# Dyadic campaign, ticket FD1: the field-side data of `H¹(G_K, 𝔽₂)`

The field-side residual of WL-c's `hHilb` result (`GQ2/Dyadic/Certificates/L.lean` §1).  WL-c
discharged the *form-theoretic* half of packet Def. 9.1 item (5) as an unconditional theorem —
`exists_cupForm_normalForm : b ≅ ⟨1⟩ ⊥ H^{⊥m}` — by observing that the cup–Bockstein datum is a
symmetric **bilinear** form, not a quadratic one, so that no `𝔽₂` Witt cancellation is on the
path.  What that theorem still needs is a `W` satisfying its three hypotheses; WL-c's report
reduced the identification of `(H¹(G_K,𝔽₂), ⌣)` with such a `W` to three named field facts.
Those three are this file, at an arbitrary finite `K/ℚ₂` — no word, no relator, no certificate.

## The three facts

1. **`dim_{𝔽₂} H¹(G_K,𝔽₂) = n + 2`**, `n = [K:ℚ₂]` (§1).  From B7 at `K`
   (`absGalK_localEulerCharacteristic`, itself a *theorem* via Shapiro — `EulerShapiro.lean`)
   with the two Euler factors supplied here: `#H⁰ = 2` (trivial action) and `#H² = 2` (B6's
   invariant map transported to `𝔽₂`-coefficients — `invGalK`).  Delivered in all three of the
   repo's vocabularies: `card_H1_zmodTwo` (`Nat.card = 2^(n+2)`, MC1 §(ix)'s convention),
   `finrank_H1_zmodTwo` (`Module.finrank`) and `demushkinRank_galK`.
2. **Perfectness of the cup pairing** (§2), in the `NondegFp2` shape the consumer takes.  The
   form is `cupFormK K x y = inv_K(x ⌣ y)`; `isCupFormFp2_cupFormK` gives symmetry (char-2
   graded commutativity, `trivialCupPairing_comm`) and biadditivity, `nondegFp2_cupFormK` is
   B6's `(1,1)`-perfectness clause at `G_K`.  The bridge to B6's `MuDual`-slot — LG2's
   `pairingK` shape — is `cup11_muDual_eq_cup_mul`, a naturality statement that is `rfl` on
   representatives.
3. **`(−1,−1)_K = −1`, i.e. the `e`-datum** (§§3–4).  `kappaK = [−1]`, and the Labute identity
   `z ⌣ z = z ⌣ κ` is `HilbertLedger.cup_self_eq_neg_one` (B11a at `−a = 0² − a·1²`) quantified
   over all of `H¹` by Kummer surjectivity.  The anisotropy `b κ κ = 1` is **not** a fourth
   arithmetic input: §3 shows `b e e = 1 ⟺ dim W odd` for *any* nondegenerate cup form, so with
   fact (i) it is exactly `n` odd — which the type-`L` row (`n = 2h + 1`) carries.

## Two findings

* **Fact (iii) is a corollary of facts (i) and (ii)**, by parity.  The mechanism (§3) is the
  *alternating correction* `b' = b + d ⊗ d`, `d w = b w w`: over `𝔽₂` it is alternating for
  free, and `b'`-degeneracy is the equation `d(v) = d(v)²·b(e,e)`.  Under `b e e = 0` that
  forces `v = 0`, so `b'` is symplectic and `dim W` is even; under `b e e = 1` the `⟨1⟩ ⊥ ker d`
  splitting already in `Certificates/L.lean` makes `dim W` odd.  No plane-by-plane argument and
  no new arithmetic is needed — only `exists_symplectic_equiv`, which WL-c already proved.
* ⚠ **`b e e = 1` is `n` odd, not `q_K = 2`.**  `Certificates/L.lean` §1 states "`q_K = 2` is
  exactly `b e e = 1`"; the reading that the type-`L` row uses is sound (`n` odd forces
  `i ∉ K`, hence `q_K = 2`), but the stated *equivalence* fails: `K = ℚ₂(√2)` has `i ∉ K` and
  so `q_K = 2`, while `n = 2` is even and `(−1,−1)_K = +1`.  `cupFormK_kappa_self_iff` records
  the correct characterization.  Errata item for the L docstring; no consumer is affected.

## Statement shapes for AS4 / AS1

The capstone `exists_cupFormK_normalForm K h (hn : Module.finrank ℚ_[2] K = 2*h+1)` gives the
isometry with the hyperbolic count **pinned**: `⟨1⟩ ⊥ H^{⊥(h+1)}` at rank `n + 2`, which is
S2.4 §5.5's statement and is the same normal form WL-c's relator side (`sqRelWord_centLift_fib`)
lands on.  Assemblers wanting the pieces separately take `cupFormK`, `isCupFormFp2_cupFormK`,
`nondegFp2_cupFormK`, `kappaK`, `cupFormK_kappa`, `cupFormK_kappa_self`.

## Implementation notes

Not `module`-style (it imports the plain-import `Certificates.L`); the `module`-style imports
`LocalGauss.{EulerShapiro, PairingK}` and `HilbertLedger` are fine in this direction.  One new
global instance, `instModuleH1 : Module (ZMod 2) (H1 Γ (ZMod 2))` — the `H¹` twin of the
existing `GQ2.RStage.instModuleH2`, needed because `exists_cupForm_normalForm` produces a
`≃ₗ[ZMod 2]`.  No `native_decide`; the only `decide`s are two three-element `𝔽₂` checks inside
proofs.

## Axiom state

Audited by `#print axioms` on all 29 named declarations, run in a scratch file, not committed.
**No new axioms**; every declaration prints a subset of std-3 ∪ {B6, B7, B11a}, and the census
stays at eleven.  Zero `sorryAx`, zero `native_decide`.  Per headline:

* exactly `[propext, Classical.choice, Quot.sound]` — `finiteIndex_fixingSubgroup`,
  `galK_isLocalDualizingGroup`, `smul_muN_two_galK`, `muNTwoEquiv_symm_equivariant`,
  `h0_zmodTwo_eq_top`, `card_H0_zmodTwo`, `instModuleH1`, `smul_zmodTwo_galK`,
  `cup11_muDual_eq_cup_mul`, `altCorrection`, `isSymplecticFp2_altCorrection`,
  `exists_card_eq_four_pow_of_diag_isotropic`,
  `exists_card_eq_two_mul_four_pow_of_diag_anisotropic`, `diag_eq_one_iff_odd`, `kappaK`;
* std-3 + **B6** `tateDualityAt` — `tateDualityGalK`, `invGalK`, `card_H2_zmodTwo`, `cupFormK`,
  `isCupFormFp2_cupFormK`, `nondegFp2_cupFormK`;
* std-3 + **B7** `absGalQ2_localEulerCharacteristic` — `finite_H1_zmodTwo`;
* std-3 + **B6** + **B7** — `card_H1_zmodTwo`, `finrank_H1_zmodTwo`, `demushkinRank_galK`;
* std-3 + **B6** + **B11a** `hilbertSymbol_normCriterion_finiteDyadic` — `cupFormK_kappa`;
* std-3 + **B6** + **B7** + **B11a** — `cupFormK_kappa_self_iff`, `cupFormK_kappa_self`,
  **`exists_cupFormK_normalForm`** (the capstone).

Note what does *not* appear: `kummerClassK_surjective` is a theorem (ex-B12) and contributes no
axiom, and no B3c/B5-K/B8/B9/B10-K enters through any import chain.
-/

namespace GQ2.Dyadic.FieldData

open ContCoh GQ2

local notation "ℚ̄₂" => AlgebraicClosure ℚ_[2]

variable (K : IntermediateField ℚ_[2] ℚ̄₂) [FiniteDimensional ℚ_[2] K]

section Probes

-- `ℚ̄₂/ℚ₂` is Galois (char 0), which is what makes `index = degree` available below
example : IsGalois ℚ_[2] ℚ̄₂ := inferInstance
example : Module.finrank ℚ_[2] K = K.fixingSubgroup.index :=
  IntermediateField.finrank_eq_fixingSubgroup_index K

end Probes

/-! ## §1 The dimension of `H¹(G_K, 𝔽₂)` -/

section Dimension

/-- `G_K` has finite index in `G_ℚ₂` (open subgroup of a profinite group). -/
theorem finiteIndex_fixingSubgroup :
    (K.fixingSubgroup : Subgroup AbsGalQ2).FiniteIndex :=
  @Subgroup.finiteIndex_of_finite_quotient _ _ _
    (finite_quotient_of_isOpen _ (isOpen_fixingSubgroup K))

/-- `G_K = Gal(ℚ̄₂/K)` is a local dualizing group: it is an open finite-index subgroup of
`G_ℚ₂`, which is exactly the gate on the base-generalized B6 axiom `GQ2.tateDualityAt`. -/
theorem galK_isLocalDualizingGroup (n : ℕ) [NeZero n] :
    IsLocalDualizingGroup ↥(K.fixingSubgroup) n :=
  @subgroup_isLocalDualizingGroup n _ _ (isOpen_fixingSubgroup K)
    (finiteIndex_fixingSubgroup K)

/-- **The B6 duality bundle at `G_K`**, for `K/ℚ₂` finite. -/
noncomputable def tateDualityGalK : TateDualityG ↥(K.fixingSubgroup) 2 :=
  tateDualityAt ↥(K.fixingSubgroup) 2 (galK_isLocalDualizingGroup K 2)

omit [FiniteDimensional ℚ_[2] K] in
/-- `G_K` acts trivially on `μ₂ ⊂ ℚ₂`. -/
theorem smul_muN_two_galK (g : ↥(K.fixingSubgroup)) (x : MuN 2) : g • x = x :=
  LocalLiftingDuality.smul_muN_two_trivial g.1 x

omit [FiniteDimensional ℚ_[2] K] in
/-- The coefficient transport `𝔽₂ ≃+ μ₂` is `G_K`-equivariant (both actions are trivial). -/
theorem muNTwoEquiv_symm_equivariant (g : ↥(K.fixingSubgroup)) (a : ZMod 2) :
    LocalLiftingDuality.muNTwoEquiv.symm (g • a)
      = g • LocalLiftingDuality.muNTwoEquiv.symm a := by
  rw [smul_muN_two_galK K, show g • a = a from rfl]

/-- **The invariant map at `G_K` in `𝔽₂`-coefficients**: `H²(G_K, 𝔽₂) ≃+ 𝔽₂`, obtained from
B6's `inv : H²(G_K, μ₂) ≃+ ℤ/2` by the (trivial-action) transport `𝔽₂ ≃+ μ₂`.  For `n = 2` the
"unnormalized" deviation flagged on B6 is vacuous: `ZMod 2` has a unique automorphism. -/
noncomputable def invGalK : H2 ↥(K.fixingSubgroup) (ZMod 2) ≃+ ZMod 2 :=
  (H2congr LocalLiftingDuality.muNTwoEquiv.symm (muNTwoEquiv_symm_equivariant K)).trans
    (tateDualityGalK K).inv

omit [FiniteDimensional ℚ_[2] K] in
/-- `H⁰(G_K, 𝔽₂) = 𝔽₂`: the coefficient action is trivial, so the invariants are everything. -/
theorem h0_zmodTwo_eq_top : H0 ↥(K.fixingSubgroup) (ZMod 2) = ⊤ :=
  eq_top_iff.mpr fun _ _ _ => rfl

omit [FiniteDimensional ℚ_[2] K] in
/-- `#H⁰(G_K, 𝔽₂) = 2`. -/
theorem card_H0_zmodTwo : Nat.card ↥(H0 ↥(K.fixingSubgroup) (ZMod 2)) = 2 := by
  rw [h0_zmodTwo_eq_top, Nat.card_congr (AddSubgroup.topEquiv (G := ZMod 2)).toEquiv]
  simp

/-- **`#H²(G_K, 𝔽₂) = 2`** — the `dim H² = 1` clause, from B6's invariant map. -/
theorem card_H2_zmodTwo : Nat.card (H2 ↥(K.fixingSubgroup) (ZMod 2)) = 2 := by
  rw [Nat.card_congr (invGalK K).toEquiv]
  simp

/-- `H¹(G_K, 𝔽₂)` is finite (B7 at `K`). -/
theorem finite_H1_zmodTwo : Finite (H1 ↥(K.fixingSubgroup) (ZMod 2)) :=
  (absGalK_localEulerCharacteristic K (ZMod 2)).2.1

/-- **Fact (i): `#H¹(G_K, 𝔽₂) = 2 ^ (n + 2)`**, `n = [K : ℚ₂]`.

The local Euler–Poincaré characteristic at `K` (B7 through `absGalK_localEulerCharacteristic`)
reads `#H¹ = #H⁰ · #H² · 2^(n · v₂(#V))`; at the trivial module `V = 𝔽₂` the two outer factors
are `2` (`card_H0_zmodTwo`, `card_H2_zmodTwo` — the latter is B6) and `v₂(2) = 1`.  This is
MC1 §(ix)'s `card_H1 = 2^{n+2}` convention, at the field. -/
theorem card_H1_zmodTwo :
    Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
  have h := (absGalK_localEulerCharacteristic K (ZMod 2)).2.2.2
  rw [card_H0_zmodTwo, card_H2_zmodTwo, Nat.card_zmod,
    show padicValNat 2 2 = 1 from padicValNat.self one_lt_two, mul_one,
    ← IntermediateField.finrank_eq_fixingSubgroup_index K] at h
  rw [h, pow_add]
  ring

end Dimension

/-! ## §1.1 The dimension, as a dimension

`H¹(G_K,𝔽₂)` is elementary abelian, so it is an `𝔽₂`-vector space; `card_H1_zmodTwo` then reads
as `dim_{𝔽₂} H¹(G_K,𝔽₂) = n + 2`, in both of the repo's dimension vocabularies
(`Module.finrank` and `demushkinRank`). -/

section Finrank

variable {Γ : Type*} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

/-- `H¹(Γ, 𝔽₂)` is a `ZMod 2`-module (exponent `2`, being a subquotient of `𝔽₂`-cochains).  The
`H²` twin is `GQ2.RStage.instModuleH2`; the `H¹` one did not exist. -/
instance instModuleH1 : Module (ZMod 2) (H1 Γ (ZMod 2)) :=
  AddCommGroup.zmodModule (fun x => nsmul_H1_eq_zero x)

end Finrank

section FinrankK

/-- **Fact (i), in `Module.finrank` form**: `dim_{𝔽₂} H¹(G_K, 𝔽₂) = n + 2`. -/
theorem finrank_H1_zmodTwo :
    Module.finrank (ZMod 2) (H1 ↥(K.fixingSubgroup) (ZMod 2)) = Module.finrank ℚ_[2] K + 2 := by
  haveI := finite_H1_zmodTwo K
  have h : (2 : ℕ) ^ Module.finrank (ZMod 2) (H1 ↥(K.fixingSubgroup) (ZMod 2))
      = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
    rw [FiniteField.pow_finrank_eq_natCard 2 (H1 ↥(K.fixingSubgroup) (ZMod 2)),
      card_H1_zmodTwo K]
  exact Nat.pow_right_injective le_rfl h

/-- **Fact (i), in `demushkinRank` form** — the vocabulary MC1 §(ix) and the `MarkedCore`
consumers use (`coreRank h = 4 + 2h` is `n + 2` at `n = 2 + 2h`). -/
theorem demushkinRank_galK :
    demushkinRank 2 ↥(K.fixingSubgroup) = Module.finrank ℚ_[2] K + 2 :=
  demushkinRank_eq_of_card (card_H1_zmodTwo K)

end FinrankK

/-! ## §2 The cup form on `H¹(G_K, 𝔽₂)` and its nondegeneracy -/

section CupForm

omit [FiniteDimensional ℚ_[2] K] in
/-- The `G_K`-action on `𝔽₂` is trivial (definitionally). -/
theorem smul_zmodTwo_galK : ∀ (g : ↥(K.fixingSubgroup)) (m : ZMod 2), g • m = m :=
  fun _ _ => rfl

/-- **The cup form** `b_K(x, y) = inv_K(x ⌣ y)` on `H¹(G_K, 𝔽₂)`: the mod-2 cup product read
through the invariant map `H²(G_K,𝔽₂) ≃+ 𝔽₂`.  Under Kummer theory this is the Hilbert symbol
(census axiom **B11a**, `hilbertSymbol_normCriterion_finiteDyadic`, is the identification). -/
noncomputable def cupFormK (x y : H1 ↥(K.fixingSubgroup) (ZMod 2)) : ZMod 2 :=
  invGalK K (x ⌣[smul_zmodTwo_galK K] y)

/-- **The cup form is a cup–Bockstein form** in `Certificates/L.lean`'s sense: symmetric
(graded-commutativity in characteristic two, `trivialCupPairing_comm`) and additive
in the first slot (the cup product is an `AddMonoidHom`). -/
theorem isCupFormFp2_cupFormK :
    Certificates.LSqStokes.IsCupFormFp2 (cupFormK K) where
  symm v w := congrArg (invGalK K) (trivialCupPairing_comm _ v w)
  add_left u v w := by
    show invGalK K (trivialCupPairing 2 _ _ (u + v) w) = _
    rw [map_add]
    exact map_add (invGalK K) _ _

omit [FiniteDimensional ℚ_[2] K] in
/-- **Naturality of the `(1,1)` cup in the coefficient pairing.**  Transporting the left slot
along the bridge `𝔽₂ ≃+ Hom(𝔽₂, μ₂)` and pairing by evaluation gives the same `H²`-class as
cupping by multiplication and transporting the *value* along `𝔽₂ ≃+ μ₂`.  Both sides are the
cochain `p ↦ μ₂-lift of a(p₁)·(p₁ · b(p₂))`, so the identity is definitional on representatives.

This is what connects the `⌣[·]`-valued cup form to B6's `perfect11` clause, whose left slot
lives in the `MuDual`-coefficients (`Dyadic.pairingK`'s shape). -/
theorem cup11_muDual_eq_cup_mul (x y : H1 ↥(K.fixingSubgroup) (ZMod 2)) :
    cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2))
        (H1congr GQ2.Dyadic.zmodMuDualEquiv GQ2.Dyadic.zmodMuDualEquiv_equivariant x) y
      = H2congr LocalLiftingDuality.muNTwoEquiv.symm (muNTwoEquiv_symm_equivariant K)
          (x ⌣[smul_zmodTwo_galK K] y) := by
  obtain ⟨a, rfl⟩ := H1mk_surjective (G := ↥(K.fixingSubgroup)) (M := ZMod 2) x
  obtain ⟨b, rfl⟩ := H1mk_surjective (G := ↥(K.fixingSubgroup)) (M := ZMod 2) y
  rfl

/-- **Fact (ii): the cup form on `H¹(G_K, 𝔽₂)` is nondegenerate** — the `(1,1)`-perfectness
clause of local Tate duality (census axiom **B6**, `tateDualityAt`, at `G_K`), in the
`NondegFp2` shape `Certificates/L.lean`'s normal-form theorem consumes.

The proof is `Dyadic.pairingK_nondeg`'s, re-run at `G_K` against the `⌣[·]`-valued form: the
naturality lemma above identifies `b_K(x, ·)` with the functional `inv ∘ (x′ ∪ ·)` that
`perfect11` declares injective in `x′`. -/
theorem nondegFp2_cupFormK :
    Certificates.LSqStokes.NondegFp2 (cupFormK K) := by
  intro x hx
  have hperf := (tateDualityGalK K).perfect11 (ZMod 2) (by decide)
  set e := H1congr (G := ↥(K.fixingSubgroup)) GQ2.Dyadic.zmodMuDualEquiv
    GQ2.Dyadic.zmodMuDualEquiv_equivariant with he
  have h0 : (tateDualityGalK K).inv.toAddMonoidHom.comp
      ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2))) (e x))
      = (tateDualityGalK K).inv.toAddMonoidHom.comp
        ((cup11 (muDualPairing 2 (ZMod 2)) (muDualPairing_equivariant 2 (ZMod 2)))
          (0 : H1 ↥(K.fixingSubgroup) (MuDual 2 (ZMod 2)))) := by
    ext y
    rw [map_zero, AddMonoidHom.comp_zero]
    show (tateDualityGalK K).inv _ = _
    rw [he, cup11_muDual_eq_cup_mul K x y]
    exact hx y
  rw [← AddEquiv.symm_apply_apply e x, hperf.1 h0, map_zero]

end CupForm

/-! ## §3 Anisotropy of the Labute vector, by parity

The one place where the `e`-datum's second clause `b e e = 1` could have been another arithmetic
input.  It is not: given facts (i) and (ii) it is **forced by the parity of `dim H¹`**, and the
mechanism is elementary linear algebra over `𝔽₂`.

Write `d w = b w w` for the (linear, `IsCupFormFp2.diag_add`) diagonal and `b' = b + d ⊗ d`.
Then `b'` is always alternating, and its radical is computed by nondegeneracy of `b`:
`b'(v, ·) = 0` forces `v = d(v)·e`, whence `d(v) = d(v)²·b(e,e)`.  So

* if `b e e = 0` then `d(v) = 0` and `v = 0`: `b'` is **symplectic**, and `dim W` is even;
* if `b e e = 1` then `ker d` is symplectic (`isSymplectic_cupKer`) and `W = ⟨e⟩ ⊥ ker d`, so
  `dim W` is odd.

Hence `b e e = 1 ⟺ dim W odd`, and for `W = H¹(G_K,𝔽₂)` of dimension `n + 2` this is exactly
`n` odd — the hypothesis the type-`L` row carries (`n = 2h + 1`). -/

section Parity

open Certificates.LSqStokes

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]

/-- **The alternating correction** `b' = b + d ⊗ d` of a cup–Bockstein form (`d w = b w w`).
Over `𝔽₂` it is alternating for free, since `c + c² = 0` for every `c : 𝔽₂`. -/
def altCorrection (b : W → W → ZMod 2) (x y : W) : ZMod 2 := b x y + b x x * b y y

/-- **The alternating correction is symplectic when the Labute vector is isotropic.**  This is
the whole content of the parity dichotomy: `b'`-degeneracy is the equation `d(v) = d(v)²·b(e,e)`,
which under `b e e = 0` has only `d(v) = 0`, hence only `v = 0`. -/
theorem isSymplecticFp2_altCorrection {b : W → W → ZMod 2} (hb : IsCupFormFp2 b)
    (hnd : NondegFp2 b) {e : W} (he : ∀ w, b e w = b w w) (he0 : b e e = 0) :
    IsSymplecticFp2 (altCorrection b) where
  add_left u v w := by
    show b (u + v) w + b (u + v) (u + v) * b w w
      = (b u w + b u u * b w w) + (b v w + b v v * b w w)
    rw [hb.add_left, hb.diag_add, add_mul]
    ring
  add_right u v w := by
    show b u (v + w) + b u u * b (v + w) (v + w)
      = (b u v + b u u * b v v) + (b u w + b u u * b w w)
    rw [hb.add_right, hb.diag_add, mul_add]
    ring
  alt v := by
    show b v v + b v v * b v v = 0
    revert v
    have h : ∀ c : ZMod 2, c + c * c = 0 := by decide
    exact fun v => h (b v v)
  nondeg := by
    intro v hv
    have h2 : ∀ x : W, x + x = 0 := Certificates.module_zmod2_two_torsion
    have hkey : ∀ w, b (v + (b v v) • e) w = 0 := by
      intro w
      have h : b v w + b v v * b w w = 0 := hv w
      rw [hb.add_left, hb.smul_left, he w]
      exact h
    have hv0 : v + (b v v) • e = 0 := hnd _ hkey
    have hveq : v = (b v v) • e := by
      calc v = v + ((b v v) • e + (b v v) • e) := by rw [h2, add_zero]
        _ = (v + (b v v) • e) + (b v v) • e := by abel
        _ = (b v v) • e := by rw [hv0, zero_add]
    have hc0 : b v v = 0 := by
      conv_lhs => rw [hveq]
      rw [hb.smul_left, hb.smul_right, he0, mul_zero, mul_zero]
    rw [hveq, hc0, zero_smul]

/-- **The isotropic branch: `b e e = 0` forces `#W` to be a square** (`dim W` even), because the
alternating correction is then a symplectic form and `exists_symplectic_equiv` applies to it. -/
theorem exists_card_eq_four_pow_of_diag_isotropic [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e : W} (he : ∀ w, b e w = b w w)
    (he0 : b e e = 0) : ∃ m : ℕ, Nat.card W = 4 ^ m := by
  obtain ⟨m, φ, -⟩ :=
    exists_symplectic_equiv (altCorrection b) (isSymplecticFp2_altCorrection hb hnd he he0)
  refine ⟨m, ?_⟩
  rw [Nat.card_congr φ.toEquiv]
  simp

/-- **The anisotropic branch: `b e e = 1` forces `#W = 2·4^m`** (`dim W` odd) — the mirror of the
previous lemma, read off `Certificates/L.lean`'s own `⟨1⟩ ⊥ (symplectic)` splitting. -/
theorem exists_card_eq_two_mul_four_pow_of_diag_anisotropic [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e : W} (he : ∀ w, b e w = b w w)
    (he1 : b e e = 1) : ∃ m : ℕ, Nat.card W = 2 * 4 ^ m := by
  obtain ⟨m, ψ, -⟩ :=
    exists_symplectic_equiv (fun x y : cupKer hb => b (x : W) (y : W))
      (isSymplectic_cupKer hb hnd he he1)
  refine ⟨m, ?_⟩
  rw [Nat.card_congr (cupSplitEquiv hb he he1).toEquiv, Nat.card_prod,
    Nat.card_congr ψ.toEquiv]
  simp

/-- **`b e e = 1` ⟺ `dim_{𝔽₂} W` is odd.**  The single `𝔽₂` equation that `hHilb`'s splitting
needs is therefore *not* an independent arithmetic input once the dimension is known. -/
theorem diag_eq_one_iff_odd [Finite W] {b : W → W → ZMod 2}
    (hb : IsCupFormFp2 b) (hnd : NondegFp2 b) {e : W} (he : ∀ w, b e w = b w w)
    {k : ℕ} (hcard : Nat.card W = 2 ^ k) : b e e = 1 ↔ Odd k := by
  constructor
  · intro h1
    obtain ⟨m, hm⟩ := exists_card_eq_two_mul_four_pow_of_diag_anisotropic hb hnd he h1
    rw [hcard, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_succ'] at hm
    have hkm : k = 2 * m + 1 := Nat.pow_right_injective le_rfl hm
    exact ⟨m, by omega⟩
  · intro hk
    rcases ZMod.eq_zero_or_eq_one (b e e) with h0 | h1
    · exfalso
      obtain ⟨m, hm⟩ := exists_card_eq_four_pow_of_diag_isotropic hb hnd he h0
      rw [hcard, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul] at hm
      have hkm : k = 2 * m := Nat.pow_right_injective le_rfl hm
      obtain ⟨j, hj⟩ := hk
      omega
    · exact h1

end Parity

/-! ## §4 The `e`-datum at `K`, and the normal form -/

section EDatum

open Certificates.LSqStokes

/-- **The Labute vector** `κ_K = [−1] ∈ H¹(G_K, 𝔽₂)` — the class of `−1` in `K^×/(K^×)²`. -/
noncomputable def kappaK : H1 ↥(K.fixingSubgroup) (ZMod 2) := kummerClassK K (-1)

/-- **The Labute identity `z ⌣ z = z ⌣ κ`** (draft `eq` at `draft.tex:372–375`), at the field:
`κ = [−1]` represents the Bockstein diagonal of the cup form.

Two inputs, neither new: `HilbertLedger.cup_self_eq_neg_one` — the Hilbert-symbol identity
`(a,a) = (a,−1)`, whose proof is census axiom **B11a** at the norm representation
`−a = 0² − a·1²` — and Kummer surjectivity `kummerClassK_surjective` (a theorem, ex-B12), which
is what lets the identity be quantified over *all* of `H¹` and not just Kummer classes. -/
theorem cupFormK_kappa (w : H1 ↥(K.fixingSubgroup) (ZMod 2)) :
    cupFormK K (kappaK K) w = cupFormK K w w := by
  obtain ⟨a, rfl⟩ := kummerClassK_surjective K w
  show invGalK K _ = invGalK K _
  refine congrArg _ ?_
  rw [trivialCupPairing_comm]
  exact (cup_self_eq_neg_one K (smul_zmodTwo_galK K) a).symm

/-- **Fact (iii): `(−1,−1)_K = −1`, i.e. the anisotropy `b_K(κ,κ) = 1`, exactly when
`n = [K:ℚ₂]` is odd.**

The `⟸` direction is what `hHilb`'s splitting consumes, and the type-`L` row supplies its
hypothesis on the nose (`n = 2h + 1`).  It is *not* a fourth arithmetic input: given facts (i)
and (ii) it is forced by the parity of `dim H¹ = n + 2` (§3).

⚠ Note the exact shape.  What is proved — and what is true — is `(−1,−1)_K = −1 ↔ n odd`, which
is **strictly stronger than, and not equivalent to, `q_K = 2`** in the sense of the order of
`μ_{2^∞}(K)`: for `K = ℚ₂(√2)` one has `i ∉ K`, so `q_K = 2`, while `n = 2` is even and the
symbol is `+1`.  `n` odd does imply `q_K = 2` (it forces `i ∉ K`, since `ℚ₂(i)/ℚ₂` is quadratic),
so the type-`L` reading in `Certificates/L.lean` §1 is sound; the *converse* half of the
identification stated there ("`q_K = 2` is exactly `b e e = 1`") does not hold in general. -/
theorem cupFormK_kappa_self_iff :
    cupFormK K (kappaK K) (kappaK K) = 1 ↔ Odd (Module.finrank ℚ_[2] K) := by
  haveI := finite_H1_zmodTwo K
  rw [diag_eq_one_iff_odd (isCupFormFp2_cupFormK K) (nondegFp2_cupFormK K)
    (cupFormK_kappa K) (card_H1_zmodTwo K)]
  constructor
  · rintro ⟨j, hj⟩; exact ⟨j - 1, by omega⟩
  · rintro ⟨j, hj⟩; exact ⟨j + 1, by omega⟩

/-- **Fact (iii)**, in the direction the consumer uses. -/
theorem cupFormK_kappa_self (hodd : Odd (Module.finrank ℚ_[2] K)) :
    cupFormK K (kappaK K) (kappaK K) = 1 :=
  (cupFormK_kappa_self_iff K).mpr hodd

end EDatum

/-! ## §5 The three facts, delivered: `hHilb` at the field

`Certificates/L.lean`'s `exists_cupForm_normalForm` is unconditional given `IsCupFormFp2`,
`NondegFp2` and the `e`-datum; §§1–4 supply all three at `(H¹(G_K,𝔽₂), ⌣)`.  The capstone below
is the composite, with the hyperbolic count `m` **pinned** by fact (i): at `n = 2h + 1` the form
is `⟨1⟩ ⊥ H^{⊥(h+1)}`, which is S2.4 §5.5's statement and is literally the normal form WL-c's
relator side (`sqRelWord_centLift_fib`) lands on. -/

section NormalForm

open Certificates.LSqStokes

/-- **`hHilb` at the field `K`.**  For `K/ℚ₂` of odd degree `n = 2h + 1`, the mod-2 cup form of
`H¹(G_K, 𝔽₂)` is isometric to `⟨1⟩ ⊥ H^{⊥(h+1)}`.

Axioms: the standard three, plus **B6** (`tateDualityAt`, through nondegeneracy and `#H² = 2`),
**B7** (`absGalQ2_localEulerCharacteristic`, through the dimension) and **B11a**
(`hilbertSymbol_normCriterion_finiteDyadic`, through the Labute identity).  No new axiom, and no
`𝔽₂` quadratic-form classification. -/
theorem exists_cupFormK_normalForm (h : ℕ) (hn : Module.finrank ℚ_[2] K = 2 * h + 1) :
    ∃ φ : H1 ↥(K.fixingSubgroup) (ZMod 2)
        ≃ₗ[ZMod 2] ZMod 2 × (Fin (h + 1) → ZMod 2 × ZMod 2),
      ∀ x y, cupFormK K x y = (φ x).1 * (φ y).1 + hypGram (φ x).2 (φ y).2 := by
  haveI := finite_H1_zmodTwo K
  obtain ⟨m, φ, hφ⟩ :=
    exists_cupForm_normalForm (isCupFormFp2_cupFormK K) (nondegFp2_cupFormK K)
      (cupFormK_kappa K) (cupFormK_kappa_self K ⟨h, hn⟩)
  -- pin `m = h + 1` by counting: `2·4^m = #H¹ = 2^(n+2) = 2^(2h+3)`
  have hm : m = h + 1 := by
    have h1 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 * 4 ^ m := by
      rw [Nat.card_congr φ.toEquiv, Nat.card_prod]
      simp
    have h2 : Nat.card (H1 ↥(K.fixingSubgroup) (ZMod 2)) = 2 ^ (2 * m + 1) := by
      rw [h1, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul, ← pow_succ']
    have h3 : (2 : ℕ) ^ (2 * m + 1) = 2 ^ (Module.finrank ℚ_[2] K + 2) := by
      rw [← h2, card_H1_zmodTwo K]
    have h4 := Nat.pow_right_injective (le_refl 2) h3
    omega
  subst hm
  exact ⟨φ, hφ⟩

end NormalForm

end GQ2.Dyadic.FieldData
