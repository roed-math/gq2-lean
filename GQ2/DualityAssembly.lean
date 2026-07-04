import GQ2.Devissage
import GQ2.TrivialSelfDual

/-!
# P-13f: assembling `prop_5_15` (deformation duality) from the simple-module case + dévissage

`prop_5_15 : IsSelfDual t A` for every finite elementary `𝔽₂[C]`-module.  Route: the simple modules
are self-dual (trivial module via `trivialSelfDual`; nontrivial simples via `lemma_5_13` + the
degree-one pairing), then `lemma_5_11` (dévissage, `GQ2/Devissage.lean`) two-out-of-three along a
composition series.

This file lives outside `FoxHeisenberg.lean` because it needs `lemma_5_11` (in `Devissage`, which
imports `FoxHeisenberg`) — the import runs the other way, the `TrivialSelfDual.lean` pattern.

## Card bookkeeping for the simple case

For a nontrivial simple module the invariants `H⁰w(A) = A^C` vanish, so the normal form
`H¹w ≅ A` (`lemma_5_13`) forces `#Z¹w = #A²` and `#H²w = 1` — clauses 1 and 2 of `IsSelfDual`.
-/

namespace GQ2.FoxH

open scoped Classical

variable {C : Type*} [Group C] [Finite C] {A : Type*} [AddCommGroup A] [Finite A]
  [DistribMulAction C A]

/-- **`H¹w ≅ A` from the normal form**: when every `x₀`-supported tuple is a cocycle and every
cocycle is uniquely `x₀`-supported modulo coboundaries (`lemma_5_13`), the class map `A → H¹w`,
`c ↦ [x₀Supported c]`, is a bijection, so `#H¹w = #A`. -/
theorem card_H1w_of_normalForm (t : Marking C)
    (hx0mem : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnf : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t) :
    Nat.card (H1w (A := A) t) = Nat.card A := by
  have key : ∀ (a b : Z1w (A := A) t),
      h1wMk t a = h1wMk t b ↔ b.val - a.val ∈ B1w (A := A) t := by
    intro a b
    show QuotientAddGroup.mk a = QuotientAddGroup.mk b ↔ _
    rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
    show -a.val + b.val ∈ B1w (A := A) t ↔ b.val - a.val ∈ B1w (A := A) t
    rw [show -a.val + b.val = b.val - a.val from by abel]
  refine (Nat.card_eq_of_bijective (fun c => h1wMk t ⟨x0Supported c, hx0mem c⟩) ⟨?_, ?_⟩).symm
  · -- injective
    intro c c' hcc
    rw [key] at hcc
    -- `hcc : x₀Supported c' − x₀Supported c ∈ B¹w`
    obtain ⟨cu, -, huniq⟩ := hnf (x0Supported c) (hx0mem c)
    have e1 : c = cu := huniq c (show x0Supported c - x0Supported c ∈ B1w (A := A) t by
      rw [sub_self]; exact (B1w (A := A) t).zero_mem)
    have e2 : c' = cu := huniq c' (show x0Supported c - x0Supported c' ∈ B1w (A := A) t by
      have h := (B1w (A := A) t).neg_mem hcc; rwa [neg_sub] at h)
    exact e1.trans e2.symm
  · -- surjective
    intro h
    induction h using QuotientAddGroup.induction_on with
    | H x =>
      obtain ⟨c, hc, -⟩ := hnf x.val x.2
      exact ⟨c, (key ⟨x0Supported c, hx0mem c⟩ x).mpr hc⟩

/-- **No invariants for a nontrivial simple module**: `H⁰w(A) = A^C = 0`.  `H⁰w` is the `C`-fixed
space (`H0w_eq_fixedPts`, using `hgen`), a `C`-submodule, so `⊥` or `⊤` by simplicity; `⊤` would make
the action trivial, contradicting `hnt`. -/
theorem card_H0w_eq_one_of_nontrivial (t : Marking C) (hgen : t.Generates)
    (hsimple : IsSimpleModTwo C A) (hnt : ∃ (c : C) (a : A), c • a ≠ a) :
    Nat.card (H0w (A := A) t) = 1 := by
  have hfix : (H0w (A := A) t : Set A) = fixedPts C A := H0w_eq_fixedPts t hgen
  have hmem : ∀ w : A, w ∈ H0w (A := A) t → ∀ g : C, g • w = w := by
    intro w hw g
    have : w ∈ fixedPts C A := by rw [← hfix]; exact hw
    exact this g
  have hstable : ∀ (g : C) (w : A), w ∈ H0w (A := A) t → g • w ∈ H0w (A := A) t := by
    intro g w hw; rw [hmem w hw g]; exact hw
  rcases hsimple.2 (H0w (A := A) t) hstable with h | h
  · rw [h]; exact AddSubgroup.card_bot
  · exfalso
    obtain ⟨c, a, hca⟩ := hnt
    exact hca (hmem a (h ▸ AddSubgroup.mem_top a) c)

/-- **Card clauses for a nontrivial simple module** (feeding `IsSelfDual`): `#H²w = 1` and
`#Z¹w = #A²`, from `#H¹w = #A` (`card_H1w_of_normalForm`), `#H⁰w = 1`, and the Euler characteristic
`card_H1w_eq` / `card_Z1w_eq_sq_mul_card_H2w`. -/
theorem card_H2w_and_Z1w_of_nontrivial_simple (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (hgen : t.Generates) (hsimple : IsSimpleModTwo C A) (hnt : ∃ (c : C) (a : A), c • a ≠ a)
    (hx0mem : ∀ c : A, x0Supported c ∈ Z1w (A := A) t)
    (hnf : ∀ x ∈ Z1w (A := A) t, ∃! c : A, x - x0Supported c ∈ B1w (A := A) t) :
    Nat.card (H2w (A := A) t) = 1 ∧ Nat.card (Z1w (A := A) t) = Nat.card A ^ 2 := by
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hH0 : Nat.card (H0w (A := A) t) = 1 := card_H0w_eq_one_of_nontrivial t hgen hsimple hnt
  have hH1 : Nat.card (H1w (A := A) t) = Nat.card A := card_H1w_of_normalForm t hx0mem hnf
  have heuler := card_H1w_eq (A := A) t ht hw
  rw [hH1, hH0, mul_one] at heuler
  -- heuler : #A = #A * #H²w
  have hH2 : Nat.card (H2w (A := A) t) = 1 := by
    have : Nat.card A * 1 = Nat.card A * Nat.card (H2w (A := A) t) := by rw [mul_one]; exact heuler
    exact (Nat.eq_of_mul_eq_mul_left hApos this).symm
  refine ⟨hH2, ?_⟩
  rw [card_Z1w_eq_sq_mul_card_H2w, hH2, mul_one]

/-- **No dual invariants for a nontrivial simple module**: `#(A^∨)^C = 1`.  A nonzero `C`-invariant
`λ` has `C`-stable kernel, which is `⊥` by simplicity, so `λ` is injective; but `λ(c·a) = λ(a)`
(invariance) then forces `c·a = a`, a trivial action — contradicting `hnt`. -/
theorem card_fixedPts_elemDual_eq_one_of_nontrivial (hsimple : IsSimpleModTwo C A)
    (hnt : ∃ (c : C) (a : A), c • a ≠ a) :
    Nat.card (fixedPts C (ElemDual A)) = 1 := by
  have hzero : ∀ lam : ElemDual A, (∀ g : C, g • lam = lam) → lam = 0 := by
    intro lam hlam
    have hinv : ∀ (c : C) (a : A), lam (c • a) = lam a := by
      intro c a
      have h2 : (c⁻¹ • lam) a = lam a := by rw [hlam c⁻¹]
      rwa [ElemDual.smul_apply, inv_inv] at h2
    have hkerstable : ∀ (c : C) (a : A), a ∈ (lam : A →+ ZMod 2).ker →
        c • a ∈ (lam : A →+ ZMod 2).ker := by
      intro c a ha
      rw [AddMonoidHom.mem_ker] at ha ⊢
      exact (hinv c a).trans ha
    rcases hsimple.2 (lam : A →+ ZMod 2).ker hkerstable with hbot | htop
    · exfalso
      obtain ⟨c, a, hca⟩ := hnt
      have hinj : Function.Injective (lam : A →+ ZMod 2) :=
        (injective_iff_map_eq_zero (lam : A →+ ZMod 2)).mpr (fun u hu => by
          have hz : u ∈ (lam : A →+ ZMod 2).ker := AddMonoidHom.mem_ker.mpr hu
          rw [hbot, AddSubgroup.mem_bot] at hz; exact hz)
      exact hca (hinj (hinv c a))
    · ext a
      have hmem : a ∈ (lam : A →+ ZMod 2).ker := htop ▸ AddSubgroup.mem_top a
      rw [AddMonoidHom.mem_ker] at hmem
      rw [ElemDual.zero_apply]; exact hmem
  rw [Nat.card_eq_one_iff_unique]
  exact ⟨⟨fun x y => Subtype.ext ((hzero x.val x.2).trans (hzero y.val y.2).symm)⟩,
    ⟨⟨0, fun c => smul_zero c⟩⟩⟩

end GQ2.FoxH
