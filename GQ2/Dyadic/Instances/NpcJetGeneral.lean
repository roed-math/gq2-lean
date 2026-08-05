/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Word.NpcBridge
import GQ2.Dyadic.Certificates.N0

/-!
# The noncompact-`N` jet layer at every handle count

The `hessRelZ` layer of the noncompact-`N` row was `h = 0` only: `hessRelZ_npcWord` and the two
`HessRelZTarget` inhabitants of `GQ2/Dyadic/Word/NpcBridge.lean` are pinned at
`hessMark (h := 0) s u ![c₀, c₁, 0]` and at the handle-free core.  This file generalizes them to
the frozen genus-`h` word `Words.Npc.npcW α r h e`, following the compact-`N` template
(`hessRelZ_nCompact`, `GQ2/Dyadic/Certificates/N0.lean`) and NC6's handle-tail discipline: the
core is *cited*, never re-proved.

The route is the substitution one:

* `npcCoreLift h` embeds the five core letters into `Generator (2 + 2h)`, and every core factor
  of the frozen word is literally the `npcCoreLift`-substitution of its `h = 0` form, so
  `eval_npcW_eq_core_mul_handles` splits the genus-`h` value into (transported core) × (handle
  block) at **every** marking of every profinite group.
* At the graph-type κ⁰-marking `hessMark (h := h) s u v` with `v x₂ = 0`, the transported core
  restricts to the Gate-E marking `npcMarkingW` (`lift_hessMark_npcCoreLift`), so WNP-a's
  pre-agreement and the transported NC5 headline `npc_cross_operators_word` evaluate it; the
  handle block is central with fibre the hyperbolic sum (`eval_lift_hessMark_handlesW`,
  the profinite twin of `hess_handlesW_eval`).

The headline `hessRelZ_npcW_handles` is the `npc_cross_operators` analogue of
`hessRelZ_nCompact` at every `h`:

```
hessRelZ (hessMark s u v) κ⁰ E E₂ (npcW α r h e)
  = Q₀(v x₀) + b_q(v x₁, L_c (v x₀)) + Σ_j b_q(v x_{3+2j}, v x_{4+2j}),
L_c = A⁻¹ + B + B·A⁻¹
```

with NC5's hypothesis surface (`hV2`, `hu`, `hVu`, `α ≥ 2` — still no `1 ≤ r`, no `IsUnit η`)
plus the honest `ResolvedAt` resolver hypothesis (`npcW` carries a genuine `η̂`-exponent, so the
row is not `ω₂`-only) and the Gate-E normalization `v x₂ = 0`.  WW4 gap item 5 then holds at
every handle count: `npcW_hessRelZTarget_handles`.
-/

namespace GQ2.Dyadic.NpcBridge

open GQ2.SectionSix GQ2.QuadraticFp2

noncomputable section

/-! ## §1. The core-letter substitution -/

/-- **The core embedding** `Generator 2 → Generator (2 + 2h)`: `σ ↦ σ`, `τ ↦ τ`, and the three
core wild letters to `coreLetter h`.  The frozen genus-`h` word is built from exactly these
letters plus the handle block, which is what makes the split below syntactic. -/
def npcCoreLift (h : ℕ) : Generator 2 → PWord (Generator (2 + 2 * h))
  | .sigma => .gen .sigma
  | .tau => .gen .tau
  | .wild i => .gen (Words.coreLetter h i)

@[simp] theorem npcCoreLift_sigma (h : ℕ) : npcCoreLift h .sigma = .gen .sigma := rfl

@[simp] theorem npcCoreLift_tau (h : ℕ) : npcCoreLift h .tau = .gen .tau := rfl

@[simp] theorem npcCoreLift_coreLetter (h : ℕ) (i : Fin 3) :
    npcCoreLift h (Words.coreLetter 0 i) = .gen (Words.coreLetter h i) := rfl

section Split

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The genus-`h` split**: at every marking of every profinite group, the frozen genus-`h`
noncompact word is the `npcCoreLift`-transported `h = 0` core times the handle block.  The five
core factors match factor-for-factor under substitution; only the trailing `handlesW 0 = 1`
versus `handlesW h` differs, and it splits off multiplicatively. -/
theorem eval_npcW_eq_core_mul_handles (α r h : ℕ) (e : EtaData)
    (μ : Generator (2 + 2 * h) → G) :
    PWord.eval μ (Words.Npc.npcW α r h e)
      = PWord.eval μ (PWord.subst (npcCoreLift h) (Words.Npc.npcW α r 0 e))
        * PWord.eval μ (Words.handlesW h) := by
  simp only [Words.Npc.npcW, Words.Npc.eBlockW, Words.Npc.dBlockW, Words.Npc.deltaZeroW,
    Words.Npc.aW, Words.Npc.bW, Words.handlesW_zero, PWord.omega2Pow,
    PWord.prodList_cons, PWord.prodList_nil,
    PWord.subst_mul, PWord.subst_one, PWord.subst_inv, PWord.subst_conj, PWord.subst_comm,
    PWord.subst_zpow, PWord.subst_profPow, PWord.subst_gen,
    npcCoreLift_sigma, npcCoreLift_tau, npcCoreLift_coreLetter,
    PWord.eval_mul, PWord.eval_one, mul_one, mul_assoc]

end Split

/-! ## §2. The graph-type κ⁰-marking at genus `h` -/

section Module

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
  [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C]

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- The genus-`h` graph marking restricts along `npcCoreLift` to the `h = 0` Gate-E marking, at
the wild offsets `v x₀`, `v x₁`; the boundary normalization `v x₂ = 0` is consumed exactly at
the third letter. -/
theorem lift_hessMark_npcCoreLift {h : ℕ} (s u : C) (v : Fin (2 + 2 * h + 1) → V)
    (hv2 : v (Certificates.x2Idx h) = 0) :
    (fun g ↦ PWord.eval
        (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
        (npcCoreLift h g))
      = ⇑(npcMarkingW dat hdat s u (v (Certificates.x0Idx h)) (v (Certificates.x1Idx h))) := by
  funext g
  cases g with
  | sigma => rfl
  | tau => rfl
  | wild i =>
      fin_cases i
      · rfl
      · rfl
      · show hessSlice dat hdat (v (Certificates.x2Idx h)) 0 = hessSlice dat hdat 0 0
        rw [hv2]

omit [TopologicalSpace C] [DiscreteTopology C] in
/-- **The handle block is central with the hyperbolic fibre** — the profinite twin of
`hess_handlesW_eval` (`GQ2/Dyadic/Certificates/N0.lean`), available on this row because the
handle block carries no profinite exponent. -/
theorem eval_lift_hessMark_handlesW (hV2 : ∀ v : V, v + v = 0) {h : ℕ} (s u : C)
    (v : Fin (2 + 2 * h + 1) → V) :
    PWord.eval (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
        (Words.handlesW h)
      = WordCoh.CentExt.incl _
          (∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j))) := by
  simp only [Words.handlesW]
  rw [PWord.eval_prodList, List.map_map]
  have hcong : (List.finRange h).map
        (PWord.eval (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
          ∘ fun j ↦ PWord.comm (.gen (Words.handleU j)) (.gen (Words.handleV j)))
      = (List.finRange h).map fun j ↦
          WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
            (polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j))) := by
    refine List.map_congr_left fun j _ ↦ ?_
    show PWord.eval (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
        (.comm (.gen (Words.handleU j)) (.gen (Words.handleV j))) = _
    rw [PWord.eval_comm, PWord.eval_gen, PWord.eval_gen,
      show WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat)
          (Words.handleU j)
        = hessSlice dat hdat (v (Certificates.hIdxU j)) 0 from rfl,
      show WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat)
          (Words.handleV j)
        = hessSlice dat hdat (v (Certificates.hIdxV j)) 0 from rfl,
      hessSlice_commR dat hdat hV2]
  rw [hcong,
    show ((List.finRange h).map fun j ↦ WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j))))
      = ((List.finRange h).map fun j ↦
          polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j))).map
            (WordCoh.CentExt.incl (kappa0Cocycle dat hdat)) from List.map_map.symm,
    centExt_incl_list_prod, ← Fin.sum_univ_def]

omit [Finite C] [Finite V] [TopologicalSpace C] [DiscreteTopology C] in
/-- A central slice element adds its charge to the fibre — the `Word/`-carrier twin of NC6's
`fib_mul_central`. -/
theorem fib_mul_hessSlice_zero (x : WordCoh.CentExt (kappa0Cocycle dat hdat)) (T : ZMod 2) :
    (x * hessSlice dat hdat 0 T).fib = x.fib + T := by
  rw [WordCoh.CentExt.mul_fib, hessSlice_fib]
  have hκ : (kappa0Cocycle dat hdat).κ x.base ((0 : V), (1 : C)) = 0 := by
    simp [kappa0Cocycle_κ, hdat.f_zero_right, factorSet_m_zero dat hdat]
  rw [show ((hessSlice dat hdat 0 T).base) = ((0 : V), (1 : C)) from rfl, hκ, add_zero]

/-! ## §3. The headline at every handle count -/

section Headline

/-- **The corrected noncompact-`N` cross-operator identity at the frozen genus-`h` word, in
`Word/` vocabulary.**  The value of `npcW α r h e` at the graph-type κ⁰-marking with `v x₂ = 0`
is the corrected `h = 0` endpoint plus the hyperbolic handle sum.  NC5's core and NC6's
handle-tail discipline are both cited, never re-proved. -/
theorem npc_cross_operators_npcW_word_handles (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) {h : ℕ}
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (Certificates.x2Idx h) = 0) :
    WordCoh.CentExt.fib (c := kappa0Cocycle dat hdat)
        (PWord.eval (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
          (Words.Npc.npcW α r h e))
      = NpcJet.npcQ0 dat s e.toPadic (v (Certificates.x0Idx h))
        + polar q (v (Certificates.x1Idx h))
            (NpcJet.lcOp s e.toPadic r (v (Certificates.x0Idx h)))
        + ∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j)) := by
  rw [eval_npcW_eq_core_mul_handles α r h e, PWord.eval_subst,
    lift_hessMark_npcCoreLift dat hdat s u v hv2,
    eval_lift_hessMark_handlesW dat hdat hV2 s u v,
    show WordCoh.CentExt.incl (kappa0Cocycle dat hdat)
        (∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j)))
      = hessSlice dat hdat 0
          (∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j))) from rfl,
    fib_mul_hessSlice_zero dat hdat,
    show PWord.eval
        ⇑(npcMarkingW dat hdat s u (v (Certificates.x0Idx h)) (v (Certificates.x1Idx h)))
        (Words.Npc.npcW α r 0 e)
      = (npcMarkingW dat hdat s u (v (Certificates.x0Idx h))
          (v (Certificates.x1Idx h))).eval (Words.Npc.npcW α r 0 e) from rfl,
    Words.Npc.eval_npcW_eq_eval_npcWord,
    npc_cross_operators_word dat hdat hV2 s u hu hVu α hα r e.toPadic
      (v (Certificates.x0Idx h)) (v (Certificates.x1Idx h))]

/-- **The word-side Hessian equation at every handle count** — the `npc_cross_operators`
analogue of `hessRelZ_nCompact`, on the frozen word.  The resolver hypothesis is the honest
one: `npcW` carries a genuine `η̂`-exponent, so `E₂` must compute `η̂` at the elements actually
reached. -/
theorem hessRelZ_npcW_handles (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) {h : ℕ}
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (Certificates.x2Idx h) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (Words.Npc.npcW α r h e)) :
    hessRelZ (Certificates.hessMark s u v) (kappa0Cocycle dat hdat) E E₂
        (Words.Npc.npcW α r h e)
      = NpcJet.npcQ0 dat s e.toPadic (v (Certificates.x0Idx h))
        + polar q (v (Certificates.x1Idx h))
            (NpcJet.lcOp s e.toPadic r (v (Certificates.x0Idx h)))
        + ∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j)) := by
  rw [hessRelZ, hessEvalZ, ← PWord.eval_eq_evalZ _ E E₂ _ hres]
  exact npc_cross_operators_npcW_word_handles dat hdat hV2 s u hu hVu α hα r e v hv2

/-- **WW4 gap item 5 at every handle count**: `HessRelZTarget` holds on the frozen genus-`h`
noncompact-`N` word, with the endpoint polynomial the corrected `h = 0` endpoint shifted by the
(offset-constant) hyperbolic handle sum. -/
theorem npcW_hessRelZTarget_handles (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) {h : ℕ}
    (v : Fin (2 + 2 * h + 1) → V) (hv2 : v (Certificates.x2Idx h) = 0)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark s u v) (kappa0Cocycle dat hdat))
      E E₂ (Words.Npc.npcW α r h e)) :
    Certificates.MProcyclic.HessRelZTarget dat hdat
      (Certificates.hessMark s u v) E E₂ (Words.Npc.npcW α r h e)
      (fun p ↦ NpcJet.npcQ0 dat s e.toPadic p.1
        + polar q p.2 (NpcJet.lcOp s e.toPadic r p.1)
        + ∑ j, polar q (v (Certificates.hIdxU j)) (v (Certificates.hIdxV j)))
      (v (Certificates.x0Idx h)) (v (Certificates.x1Idx h)) :=
  hessRelZ_npcW_handles dat hdat hV2 s u hu hVu α hα r e v hv2 E E₂ hres

/-- **The `h = 0` regression**: at genus `0` and the Gate-E offsets `![c₀, c₁, 0]`, the general
statement is exactly `npcW_hessRelZTarget`'s equation — the handle sum is empty. -/
theorem hessRelZ_npcW_handles_zero (hV2 : ∀ v : V, v + v = 0)
    (s u : C) (hu : Odd (orderOf u)) (hVu : ∀ v : V, u • v = v → v = 0)
    (α : ℕ) (hα : 2 ≤ α) (r : ℕ) (e : EtaData) (c₀ c₁ : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hres : PWord.ResolvedAt
      (WordCoh.lift (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0])
        (kappa0Cocycle dat hdat))
      E E₂ (Words.Npc.npcW α r 0 e)) :
    hessRelZ (Certificates.hessMark (h := 0) s u ![c₀, c₁, 0]) (kappa0Cocycle dat hdat) E E₂
        (Words.Npc.npcW α r 0 e)
      = NpcJet.npcQ0 dat s e.toPadic c₀ + polar q c₁ (NpcJet.lcOp s e.toPadic r c₀) := by
  rw [hessRelZ_npcW_handles dat hdat hV2 s u hu hVu α hα r e (h := 0) ![c₀, c₁, 0] rfl E E₂
      hres,
    Fin.sum_univ_zero, add_zero]
  rfl

end Headline

end Module

end

end GQ2.Dyadic.NpcBridge
