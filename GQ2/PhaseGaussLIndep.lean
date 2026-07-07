import GQ2.PhaseLIndep
import GQ2.SectionSix

/-!
# P-16d6c (part c3): `l`-independence of the descended Gauss sum `G⁰`

Companion to `GQ2/PhaseLIndep.lean` (c3-μ).  The shared (140) witness of `prop_8_9` fixes the Gauss
constant `G⁰ := gaussSum (En.qbar l₀ h₀)` once, at a reference scalar `l₀`, but the
`phase140_of_nonsingular` engine (`GQ2/RecursionSplice.lean`) consumes
`hG0 : gaussSum (En.qbar l h) = G⁰` at the **current** scalar `l`.  So the descended Gauss sum must
be **independent of `l`**.

This is the paper's §6.2 Gauss-sign computation (Prop 6.9 / Lemma 6.8, eqs. (87)/(91)) applied at
the descended module `V = En.Vmod`: for a faithful simple tame `C`-module `V`, **every** nonsingular
`C`-invariant `𝔽₂`-quadratic form on `V` has its Arf invariant pinned to a structural value —
`1` in the unramified case (`arf_qbar_eq_one_of_unramified`), the isotypic multiplicity `s` in the
ramified case (`arf_qbar_eq_s_of_ramified`) — independent of the form.  Since `q̄_λ = En.qbar l h`
is such a form for every `l` (via `En.hquad`/`En.hns`/`En.hinv`), its Arf, hence its Gauss sum
(`gaussSum` is `±2^m` with the sign set by Arf, `gaussSum_eq_of_arf_eq`), does not depend on `l`.

The tame structure — `C = RF.YC` marked by a tame cover `c : Ttame ↠ RF.YC`, faithfulness,
simplicity, the ramification dichotomy `c tameTau = 1`, and (ramified only) the isotypic
decomposition data — is **λ-free**: it does not vary with `l`, so it threads **hypothesis-side** and
is discharged per source `Γ` at the P-16d6e assembly (the `c3-μ`/`d6b`/`d6a` idiom;
`docs/p16d6c-handoff.md` §c3).  No `Enrichment` amendment is needed.

Axioms: none new (std-3).  B6/B7 enter per-`Γ` only at the d6e assembly.
-/

open scoped Classical

namespace GQ2

namespace SectionEight

open QuadraticFp2 (arf zeroCount IsQuadraticFp2 Nonsingular gaussSum_eq
  zeroCount_of_arf_zero zeroCount_of_arf_one)
open SectionSix (prop_6_9_unramified lemma_6_8 onePlusU)

/-- The two `sign` encodings agree: `SectionEight.sign a = (-1)^a.val` vs
`QuadraticFp2.sign a = if a = 0 then 1 else -1`. -/
private theorem sectionEight_sign_eq :
    ∀ a : ZMod 2, sign a = QuadraticFp2.sign a := by decide

/-- Bridge between the two `gaussSum` encodings on a finite type: `SectionEight.gaussSum` (a
`finsum` of `(-1)^Q`) equals `QuadraticFp2.gaussSum` (a `Finset.sum` of the `if`-`sign`), letting
the §6/P-15a Arf/zero-count machinery apply to the (140) engine's Gauss sum. -/
theorem gaussSum_eq_quadraticFp2 {W : Type*} [Fintype W] (Q : W → ZMod 2) :
    gaussSum Q = QuadraticFp2.gaussSum Q := by
  rw [gaussSum, finsum_eq_sum_of_fintype, QuadraticFp2.gaussSum]
  exact Finset.sum_congr rfl fun x _ => sectionEight_sign_eq (Q x)

/-- **Arf determines the Gauss sum.**  For nonsingular `𝔽₂`-quadratic forms `Q₁, Q₂` on the same
finite space with `#W = 2^{2m}`, equal Arf invariants force equal Gauss sums — the sign of the
`±2^m` value is exactly the Arf invariant (via the zero-count `2^{2m-1} ± 2^{m-1}`). -/
theorem gaussSum_eq_of_arf_eq {W : Type*} [AddCommGroup W] [Fintype W] (Q1 Q2 : W → ZMod 2)
    (hq1 : IsQuadraticFp2 Q1) (hns1 : Nonsingular Q1)
    (hq2 : IsQuadraticFp2 Q2) (hns2 : Nonsingular Q2)
    {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card W = 2 ^ (2 * m)) (harf : arf Q1 = arf Q2) :
    QuadraticFp2.gaussSum Q1 = QuadraticFp2.gaussSum Q2 := by
  have hzc : zeroCount Q1 = zeroCount Q2 := by
    rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (arf Q1) with h0 | h1
    · rw [zeroCount_of_arf_zero Q1 hq1 hns1 hm hcard h0,
          zeroCount_of_arf_zero Q2 hq2 hns2 hm hcard (harf ▸ h0)]
    · rw [zeroCount_of_arf_one Q1 hq1 hns1 hm hcard h1,
          zeroCount_of_arf_one Q2 hq2 hns2 hm hcard (harf ▸ h1)]
  rw [gaussSum_eq Q1, gaussSum_eq Q2, hzc]

variable {H E : Type} [Group H] [TopologicalSpace H] [DiscreteTopology H] [Finite H]
  [CommGroup E] [TopologicalSpace E] [DiscreteTopology E] [Finite E]
variable {Y : Type} [Group Y] [TopologicalSpace Y] [DiscreteTopology Y] [Finite Y]
variable {T : MarkedTarget H E Y} {Blk : SectionSeven.MinimalBlock T.LY} (RF : RecursionFrame T Blk)

/-- **§6.2 unramified Arf pin (Prop 6.9, eq. (91))** at the descended module: if inertia acts
trivially (`c tameTau = 1`) on the faithful simple tame `RF.YC`-module `V = En.Vmod`, then the
descended square form `q̄_λ = En.qbar l h` has `Arf = 1` — pinned by the invariance alone, so the
value does not depend on `l`.  The tame cover `c`/faithfulness/simplicity and `#V = 2^{2m}` are the
λ-free structural inputs threaded to P-16d6e. -/
theorem arf_qbar_eq_one_of_unramified (En : RF.Enrichment)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective c)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod, (∀ (g : RF.YC), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : En.Vmod, v ≠ 0) (hunram : c tameTau = 1)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    arf (En.qbar l h) = 1 := by
  letI : Fintype En.Vmod := Fintype.ofFinite _
  have hcard' : Fintype.card En.Vmod = 2 ^ (2 * m) := by rw [← Nat.card_eq_fintype_card]; exact hcard
  have hz := prop_6_9_unramified c hc hfaith hsimple hV hunram
    (En.qbar l h) (En.hquad l h) (En.hns l h) (En.hinv l h) m hm hcard
  rcases (show ∀ x : ZMod 2, x = 0 ∨ x = 1 from by decide) (arf (En.qbar l h)) with h0 | h1
  · -- `arf = 0` would force the `2^{2m-1}+2^{m-1}` zero count, contradicting Prop 6.9's `−`.
    exfalso
    have hz0 := zeroCount_of_arf_zero (En.qbar l h) (En.hquad l h) (En.hns l h) hm hcard' h0
    rw [hz0] at hz
    have hb : 1 ≤ 2 ^ (m - 1) := Nat.one_le_two_pow
    have hab : 2 ^ (m - 1) ≤ 2 ^ (2 * m - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · exact h1

/-- **`G⁰` is `l`-independent, unramified case** (P-16d6c, c3): the descended Gauss sum
`gaussSum (En.qbar l h)` is the same at any two scalars `l, l'` — both Arf invariants are pinned to
`1` by `arf_qbar_eq_one_of_unramified`, and Arf determines the Gauss sum.  Feeds the (140) `hG0`
field: pin `G⁰` at a reference `l₀`, transport to the current `l` here. -/
theorem gaussSum_qbar_l_indep_unramified (En : RF.Enrichment)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective c)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod, (∀ (g : RF.YC), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : En.Vmod, v ≠ 0) (hunram : c tameTau = 1)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR) (l' : RF.DR) (h' : l' ≠ RF.zeroDR) :
    gaussSum (En.qbar l h) = gaussSum (En.qbar l' h') := by
  letI : Fintype En.Vmod := Fintype.ofFinite _
  have hcard' : Fintype.card En.Vmod = 2 ^ (2 * m) := by rw [← Nat.card_eq_fintype_card]; exact hcard
  rw [gaussSum_eq_quadraticFp2 (En.qbar l h), gaussSum_eq_quadraticFp2 (En.qbar l' h')]
  refine gaussSum_eq_of_arf_eq _ _ (En.hquad l h) (En.hns l h) (En.hquad l' h') (En.hns l' h')
    hm hcard' ?_
  rw [arf_qbar_eq_one_of_unramified RF En c hc hfaith hsimple hV hunram m hm hcard l h,
      arf_qbar_eq_one_of_unramified RF En c hc hfaith hsimple hV hunram m hm hcard l' h']

/-- **§6.2 ramified Arf pin (Lemma 6.8, eq. (87))** at the descended module: if inertia acts
nontrivially (`c tameTau ≠ 1`) with the isotypic decomposition `V ≅ Wt^{⊕s}`, then the descended
square form `q̄_λ = En.qbar l h` has `Arf = s (mod 2)` — the first conjunct of Lemma 6.8, pinned by
the invariance and decomposition data alone, independent of `l`.  All of the ramification data is
λ-free and threaded to P-16d6e. -/
theorem arf_qbar_eq_s_of_ramified (En : RF.Enrichment)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective c)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod, (∀ (g : RF.YC), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1) (hV2 : ∀ v : En.Vmod, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers (c tameTau)) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers (c tameTau)) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r)) (e : En.Vmod ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers (c tameTau)) (v : En.Vmod) (j : Fin s),
      e ((t : RF.YC) • v) j = t • e v j)
    (hVU : Nat.card {v : En.Vmod // powOmega2 (c tameSigma) • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv En.Vmod (powOmega2 (c tameSigma)))).range
          = 2 ^ k → (k : ZMod 2) = (s : ZMod 2))
    (l : RF.DR) (h : l ≠ RF.zeroDR) :
    arf (En.qbar l h) = (s : ZMod 2) :=
  (lemma_6_8 c hc hfaith hsimple hram (En.qbar l h) (En.hquad l h) (En.hns l h)
    (En.hinv l h) hV2 s r a hr ha hs1 Wt hWt2 hWtsimple hWcard e he hVU hrank).1

/-- **`G⁰` is `l`-independent, ramified case** (P-16d6c, c3): the descended Gauss sum
`gaussSum (En.qbar l h)` is the same at any two scalars `l, l'` — both Arf invariants are pinned to
`s (mod 2)` by `arf_qbar_eq_s_of_ramified`, and Arf determines the Gauss sum.  Feeds the (140)
`hG0` field, ramified source. -/
theorem gaussSum_qbar_l_indep_ramified (En : RF.Enrichment)
    (c : ContinuousMonoidHom Ttame RF.YC) (hc : Function.Surjective c)
    (hfaith : ∀ g : RF.YC, (∀ v : En.Vmod, g • v = v) → g = 1)
    (hsimple : ∀ W : AddSubgroup En.Vmod, (∀ (g : RF.YC), ∀ w ∈ W, g • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : c tameTau ≠ 1) (hV2 : ∀ v : En.Vmod, v + v = 0)
    (s r a : ℕ) (hr : Odd r) (ha : 1 ≤ a) (hs1 : 1 ≤ s)
    (Wt : Type) [AddCommGroup Wt] [DistribMulAction (Subgroup.zpowers (c tameTau)) Wt]
    (hWt2 : ∀ w : Wt, w + w = 0)
    (hWtsimple : GQ2.FoxH.IsSimpleModTwo (Subgroup.zpowers (c tameTau)) Wt)
    (hWcard : Nat.card Wt = 2 ^ (2 ^ a * r)) (e : En.Vmod ≃+ (Fin s → Wt))
    (he : ∀ (t : Subgroup.zpowers (c tameTau)) (v : En.Vmod) (j : Fin s),
      e ((t : RF.YC) • v) j = t • e v j)
    (hVU : Nat.card {v : En.Vmod // powOmega2 (c tameSigma) • v = v} = 2 ^ (r * s))
    (hrank : ∀ k : ℕ,
      Nat.card (onePlusU (DistribMulAction.toAddEquiv En.Vmod (powOmega2 (c tameSigma)))).range
          = 2 ^ k → (k : ZMod 2) = (s : ZMod 2))
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card En.Vmod = 2 ^ (2 * m))
    (l : RF.DR) (h : l ≠ RF.zeroDR) (l' : RF.DR) (h' : l' ≠ RF.zeroDR) :
    gaussSum (En.qbar l h) = gaussSum (En.qbar l' h') := by
  letI : Fintype En.Vmod := Fintype.ofFinite _
  have hcard' : Fintype.card En.Vmod = 2 ^ (2 * m) := by rw [← Nat.card_eq_fintype_card]; exact hcard
  rw [gaussSum_eq_quadraticFp2 (En.qbar l h), gaussSum_eq_quadraticFp2 (En.qbar l' h')]
  refine gaussSum_eq_of_arf_eq _ _ (En.hquad l h) (En.hns l h) (En.hquad l' h') (En.hns l' h')
    hm hcard' ?_
  rw [arf_qbar_eq_s_of_ramified RF En c hc hfaith hsimple hram hV2 s r a hr ha hs1 Wt hWt2 hWtsimple
        hWcard e he hVU hrank l h,
      arf_qbar_eq_s_of_ramified RF En c hc hfaith hsimple hram hV2 s r a hr ha hs1 Wt hWt2 hWtsimple
        hWcard e he hVU hrank l' h']

end SectionEight

end GQ2
