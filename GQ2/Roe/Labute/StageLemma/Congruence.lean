/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.Levelwise
import GQ2.Roe.Labute.GradedLie.SpanAssembly
import GQ2.FrattiniNongen

/-!
# The congruence calculus and the shift-calculus toolkit

Piece 1/6 of `GQ2.Roe.Labute.StageLemma` (see that module for the mathematical overview
and the statement freeze).  Generic pro-2 `G` at the calculus threshold `k ≥ 3`: the
`λ`-congruence rules that make the shift words well defined on modification classes, and
the pure group-identity toolkit (`commP` move rules, central reorderings) that the level
shift computations run on.
-/

namespace GQ2.Roe.Labute

/-! ## The congruence calculus (spike §2.1; generic pro-2 `G`, `k ≥ 3`)

The full profinite instance pack is carried deliberately (the fills run through
closed-map/compactness arguments on λ-layers); the three instantiations `D_R`, `D₀`,
`freeProTwo` all satisfy it. -/

section Congruence

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λₘ` dies in `Qₘ` (the top layer image is trivial). -/
theorem lambdaImage_self (m : ℕ) : lambdaImage G m m = ⊥ := by
  rw [lambdaImage, Subgroup.map_eq_bot_iff, levelMk, QuotientGroup.ker_mk']

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λ₁ = ⊤` survives to every level quotient. -/
theorem lambdaImage_one_eq_top (m : ℕ) : lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
open scoped commutatorElement in
/-- The λ-grading lemma, transported to the level quotients and to the repo commutator
convention: `commP λₐ λᵦ ⊆ λ_{a+b}` in `Qₘ`. -/
theorem commP_mem_lambdaImage_add {a b m : ℕ} {v g : levelQuot G m}
    (hv : v ∈ lambdaImage G a m) (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G ((twoCentralSeries G a).inv_mem hx)
    ((twoCentralSeries G b).inv_mem hy)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A `Zₖ`-congruence is realized by a *left* central factor (centrality moves it across). -/
private theorem exists_zLayer_mul_left {k : ℕ} {v v' : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : ∃ z ∈ zLayer G k, v' = z * v := by
  refine ⟨v⁻¹ * v', h, ?_⟩
  rw [← Subgroup.mem_center_iff.mp (zLayer_le_center G k h) v]
  group

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The slot-congruence atom** (spike §2.1): for `v ∈ λ_{k-1}`, `commP v g` depends only on
`g` modulo `λ₂`.  Both error terms die: `commP v (g⁻¹g') ∈ λ_{k+1} = 1`, and the surviving
`commP v g ∈ λₖ = Zₖ` is central, so the conjugation by `g⁻¹g'` is trivial. -/
private theorem commP_congr_slot (k : ℕ) (hk : 3 ≤ k) {v g g' : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (hg : g⁻¹ * g' ∈ lambdaImage G 2 (k + 1)) :
    commP v g = commP v g' := by
  have hg' : g' = g * (g⁻¹ * g') := by group
  have h1 : commP v (g⁻¹ * g') = 1 := by
    have h := commP_mem_lambdaImage_add hv hg
    rw [show k - 1 + 2 = k + 1 by omega, lambdaImage_self] at h
    simpa using h
  have h2 : commP v g ∈ zLayer G k := by
    have hgt : g ∈ lambdaImage G 1 (k + 1) := by rw [lambdaImage_one_eq_top]; trivial
    have h := commP_mem_lambdaImage_add hv hgt
    rwa [show k - 1 + 1 = k by omega] at h
  have key : commP v (g * (g⁻¹ * g')) =
      commP v (g⁻¹ * g') * ((g⁻¹ * g')⁻¹ * commP v g * (g⁻¹ * g')) := by
    simp only [commP]; group
  have hcen := Subgroup.mem_center_iff.mp (zLayer_le_center G k h2) (g⁻¹ * g')
  rw [hg', key, h1, one_mul, mul_assoc, ← hcen, ← mul_assoc, inv_mul_cancel, one_mul]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- **The modification-congruence atoms** (spike §2.1): squaring is `𝔽₂`-linear on `Zₖ`-classes
and `commP · g` is insensitive to a central left factor. -/
private theorem sq_congr_mod {k : ℕ} {v v' : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : v ^ 2 = v' ^ 2 := by
  obtain ⟨z, hz, rfl⟩ := exists_zLayer_mul_left h
  rw [(zLayer_commute hz v).mul_pow, zLayer_sq G hz, one_mul]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
private theorem commP_congr_mod {k : ℕ} {v v' g : levelQuot G (k + 1)}
    (h : v⁻¹ * v' ∈ zLayer G k) : commP v g = commP v' g := by
  obtain ⟨z, hz, rfl⟩ := exists_zLayer_mul_left h
  rw [commP_central_left (zLayer_commute hz)]

/-- **Frattini-only dependence on the triple slots** (spike §2.1: `[v, g]` depends only on
`g mod λ₂` for `v ∈ λ_{k-1}`; §4.3: worth its own lemma — it makes the census-style
base-case checks small): the `r₀`-shift word is unchanged when the slots move by
`λ₂`-classes.  Fill: L4a. -/
theorem dbarWordR0_congr_slots (k : ℕ) (hk : 3 ≤ k)
    {a s y a' s' y' : levelQuot G (k + 1)}
    (ha : a⁻¹ * a' ∈ lambdaImage G 2 (k + 1)) (hs : s⁻¹ * s' ∈ lambdaImage G 2 (k + 1))
    (hy : y⁻¹ * y' ∈ lambdaImage G 2 (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR0 a s y w = dbarWordR0 a' s' y' w := by
  simp only [dbarWordR0, commP_congr_slot k hk (hw 0) ha, commP_congr_slot k hk (hw 1) hy,
    commP_congr_slot k hk (hw 2) hs]

/-- Frattini-only dependence, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_slots (k : ℕ) (hk : 3 ≤ k)
    {s x y s' x' y' : levelQuot G (k + 1)}
    (hs : s⁻¹ * s' ∈ lambdaImage G 2 (k + 1)) (hx : x⁻¹ * x' ∈ lambdaImage G 2 (k + 1))
    (hy : y⁻¹ * y' ∈ lambdaImage G 2 (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s' x' y' w := by
  simp only [dbarWordR2, commP_congr_slot k hk (hw 2) hy, commP_congr_slot k hk (hw 0) hx,
    commP_congr_slot k hk (hw 1) hs]

-- `hk` and `hw` are part of the frozen interface; the `Zₖ`-congruence argument below
-- happens to need neither (it is pure centrality + exponent 2).
set_option linter.unusedVariables false in
/-- **`Z_{k-1}`-class dependence on the modification** (spike §2.1: `v ↦ v²` is
`𝔽₂`-linear on classes and `[v, g]` depends only on `v mod λₖ`): the `r₀`-shift word is
unchanged when `w` moves by `λₖ`-classes.  Fill: L4a. -/
theorem dbarWordR0_congr_mod (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR0 a s y w = dbarWordR0 a s y w' := by
  simp only [dbarWordR0, sq_congr_mod (hww' 0), commP_congr_mod (hww' 0),
    commP_congr_mod (hww' 1), commP_congr_mod (hww' 2)]

-- `hk` and `hw` are part of the frozen interface; the `Zₖ`-congruence argument below
-- happens to need neither (it is pure centrality + exponent 2).
set_option linter.unusedVariables false in
/-- `Z_{k-1}`-class dependence on the modification, `r₂` side.  Fill: L4a. -/
theorem dbarWordR2_congr_mod (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w w' : Fin 3 → levelQuot G (k + 1)}
    (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1))
    (hww' : ∀ i, (w i)⁻¹ * w' i ∈ lambdaImage G k (k + 1)) :
    dbarWordR2 s x y w = dbarWordR2 s x y w' := by
  simp only [dbarWordR2, sq_congr_mod (hww' 2), commP_congr_mod (hww' 2),
    commP_congr_mod (hww' 0), commP_congr_mod (hww' 1)]

end Congruence

/-! ### Shift-calculus toolkit (L4a fill helpers; not part of the frozen interface)

The whole shift computation runs on three facts about a modification `v ∈ λ_{k-1}` of
`Q_{k+1}` with `k ≥ 3`: `v²` and every `commP v g` lie in the central involutive layer `Zₖ`,
and `v` commutes with `λ₂` outright (`[λ₂, λ_{k-1}] ⊆ λ_{k+1} = 1`).  Everything else is the
move rule `v * a = a * v * commP v a`, which is a pure group identity. -/

/-- The fundamental move rule (pure group identity, no hypotheses). -/
private theorem mul_swap_commP {H : Type*} [Group H] (v a : H) :
    v * a = a * v * commP v a := by simp only [commP]; group

/-- Left expansion of `commP` (pure group identity). -/
theorem commP_mul_left {H : Type*} [Group H] (x u g : H) :
    commP (x * u) g = u⁻¹ * commP x g * u * commP u g := by simp only [commP]; group

/-- Right expansion of `commP` (pure group identity). -/
theorem commP_mul_right {H : Type*} [Group H] (x g v : H) :
    commP x (g * v) = commP x v * (v⁻¹ * commP x g * v) := by simp only [commP]; group

/-- `commP` is antisymmetric (pure group identity). -/
private theorem commP_symm {H : Type*} [Group H] (x y : H) : commP x y = (commP y x)⁻¹ := by
  simp only [commP]; group

/-- A vanishing `commP` is exactly a trivial conjugation. -/
theorem conj_eq_self_of_commP_eq_one {H : Type*} [Group H] {x u : H}
    (h : commP x u = 1) : u⁻¹ * x * u = x := by
  simp only [commP] at h
  calc u⁻¹ * x * u = x * (x⁻¹ * u⁻¹ * x * u) := by group
    _ = x := by rw [h, mul_one]

/-- Commuting elements have trivial `commP` (pure group identity). -/
theorem commP_eq_one_of_mul_comm {H : Type*} [Group H] {x y : H} (h : x * y = y * x) :
    commP x y = 1 := by
  have hy : y⁻¹ * (x * y) = x := by rw [h]; group
  calc commP x y = x⁻¹ * (y⁻¹ * (x * y)) := by simp only [commP]; group
    _ = x⁻¹ * x := by rw [hy]
    _ = 1 := by group

/-- Conjugation expressed through `commP` (pure group identity). -/
private theorem conj_eq_mul_commP {H : Type*} [Group H] (v a : H) :
    v⁻¹ * a * v = a * (commP v a)⁻¹ := by simp only [commP]; group

/-- **The conjugation-shift core**: an abstract two-central-factor rearrangement, stated with
opaque atoms so that the group-normalizing steps are honest free-group identities. -/
private theorem conj_shift_core {H : Type*} [Group H] (a v₀ v₁ c₀ c₁ : H)
    (h₀ : ∀ t : H, c₀ * t = t * c₀) (h₁ : ∀ t : H, c₁ * t = t * c₁)
    (hvv : v₁ * v₀ = v₀ * v₁) (hconj : v₀⁻¹ * a * v₀ = a * c₀) :
    v₀⁻¹ * (a * v₁ * c₁) * v₀ = a * v₁ * (c₀ * c₁) := by
  calc v₀⁻¹ * (a * v₁ * c₁) * v₀ = v₀⁻¹ * (a * (v₁ * (c₁ * v₀))) := by group
    _ = v₀⁻¹ * (a * (v₁ * (v₀ * c₁))) := by rw [h₁ v₀]
    _ = v₀⁻¹ * (a * (v₁ * v₀ * c₁)) := by group
    _ = v₀⁻¹ * (a * (v₀ * v₁ * c₁)) := by rw [hvv]
    _ = v₀⁻¹ * a * v₀ * (v₁ * c₁) := by group
    _ = a * c₀ * (v₁ * c₁) := by rw [hconj]
    _ = a * (c₀ * v₁) * c₁ := by group
    _ = a * (v₁ * c₀) * c₁ := by rw [h₀ v₁]
    _ = a * v₁ * (c₀ * c₁) := by group

/-- **The `r₂` two-inverse core**: the `x`-slot modification appears once in the `x^s` block and
once in the `x³` block, and the two copies cancel against `zB² = 1`. -/
private theorem dr_inv_core {H : Type*} [Group H] (X A v zA zB c : H)
    (hA : ∀ t : H, zA * t = t * zA) (hB : ∀ t : H, zB * t = t * zB)
    (hc : ∀ t : H, c * t = t * c) (hvA : v * A = A * v * c) (hzB : zB = v * v * c)
    (hzB2 : zB * zB = 1) :
    X * v * zB * (A * v * zA) = X * A * zA := by
  calc X * v * zB * (A * v * zA) = X * v * (zB * (A * v * zA)) := by group
    _ = X * v * ((A * v * zA) * zB) := by rw [hB]
    _ = X * (v * A) * v * (zA * zB) := by group
    _ = X * (A * v * c) * v * (zA * zB) := by rw [hvA]
    _ = X * A * v * (c * v) * (zA * zB) := by group
    _ = X * A * v * (v * c) * (zA * zB) := by rw [hc]
    _ = X * A * (v * v * c) * (zA * zB) := by group
    _ = X * A * zB * (zA * zB) := by rw [← hzB]
    _ = X * A * (zB * (zA * zB)) := by group
    _ = X * A * ((zA * zB) * zB) := by rw [hB (zA * zB)]
    _ = X * A * (zA * (zB * zB)) := by group
    _ = X * A * zA := by rw [hzB2, mul_one]

/-- Three central factors collected on the right (the `r₂` assembly shape). -/
private theorem central_reorder₃ {H : Type*} [Group H] {zA zC : H}
    (hA : ∀ t : H, zA * t = t * zA) (hC : ∀ t : H, zC * t = t * zC) (p q d : H) :
    p * zA * (q * zC) * d = p * q * d * (zC * zA) := by
  calc p * zA * (q * zC) * d = p * (zA * (q * zC)) * d := by group
    _ = p * ((q * zC) * zA) * d := by rw [hA]
    _ = p * q * (zC * (zA * d)) := by group
    _ = p * q * ((zA * d) * zC) := by rw [hC]
    _ = p * q * ((d * zA) * zC) := by rw [hA]
    _ = p * q * d * (zA * zC) := by group
    _ = p * q * d * (zC * zA) := by rw [hA zC]

/-- Two central factors can be collected on the right. -/
private theorem central_reorder₂ {H : Type*} [Group H] {z₀ z₁ : H}
    (h₀ : ∀ t : H, z₀ * t = t * z₀) (h₁ : ∀ t : H, z₁ * t = t * z₁) (p q r : H) :
    p * z₀ * q * (r * z₁) = p * q * r * (z₀ * z₁) := by
  simp only [mul_assoc]
  rw [h₀ (q * (r * z₁))]
  simp only [mul_assoc]
  rw [h₁ z₀]

section ShiftCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- The layer images are antitone in the depth index. -/
theorem lambdaImage_le_of_le {j j' m : ℕ} (h : j ≤ j') :
    lambdaImage G j' m ≤ lambdaImage G j m :=
  Subgroup.map_mono (twoCentralSeries_antitone G h)

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- A `λ_{k-1}`-modification squares into the central layer. -/
theorem sq_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) : v ^ 2 ∈ zLayer G k := by
  obtain ⟨x, hx, rfl⟩ := hv
  refine ⟨x ^ 2, ?_, by rw [map_pow]⟩
  have h := sq_mem_twoCentralSeries_succ G hx
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Every `commP` of a `λ_{k-1}`-modification is central. -/
theorem commP_mem_zLayer (k : ℕ) (hk : 3 ≤ k) {v : levelQuot G (k + 1)}
    (hv : v ∈ lambdaImage G (k - 1) (k + 1)) (g : levelQuot G (k + 1)) :
    commP v g ∈ zLayer G k := by
  have hgt : g ∈ lambdaImage G 1 (k + 1) := by rw [lambdaImage_one_eq_top]; trivial
  have h := commP_mem_lambdaImage_add hv hgt
  rwa [show k - 1 + 1 = k by omega] at h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- `λ₂` and `λ_{k-1}` commute outright in `Q_{k+1}` (`[λ₂, λ_{k-1}] ⊆ λ_{k+1} = 1`). -/
private theorem commP_lambdaTwo_eq_one (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP c v = 1 := by
  have h := commP_mem_lambdaImage_add hc hv
  rw [show 2 + (k - 1) = k + 1 by omega, lambdaImage_self] at h
  simpa using h

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Any `commP` of two elements of `Q_{k+1}` lies in `λ₂` (`λ₁ = ⊤`). -/
private theorem commP_mem_lambdaTwo (m : ℕ) (x y : levelQuot G m) :
    commP x y ∈ lambdaImage G 2 m := by
  have hx : x ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  have hy : y ∈ lambdaImage G 1 m := by rw [lambdaImage_one_eq_top]; trivial
  exact commP_mem_lambdaImage_add hx hy

/-- Conjugation by a `λ_{k-1}`-modification is trivial on `λ₂`. -/
private theorem conj_lambdaTwo_eq_self (k : ℕ) (hk : 3 ≤ k) {c v : levelQuot G (k + 1)}
    (hc : c ∈ lambdaImage G 2 (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    v⁻¹ * c * v = c :=
  conj_eq_self_of_commP_eq_one (commP_lambdaTwo_eq_one k hk hc hv)

/-- **The square shift**: `(a·v)² = a² · (v² · commP v a)`, the π-diagonal of spike §2.2. -/
private theorem sq_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (a : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (a * v) ^ 2 = a ^ 2 * (v ^ 2 * commP v a) := by
  have hc : commP v a * v = v * commP v a :=
    ((zLayer_commute (commP_mem_zLayer k hk hv a) v)).eq
  calc (a * v) ^ 2 = a * (v * a) * v := by rw [pow_two (a * v)]; group
    _ = a * (a * v * commP v a) * v := by rw [mul_swap_commP v a]
    _ = a * a * v * (commP v a * v) := by group
    _ = a * a * v * (v * commP v a) := by rw [hc]
    _ = a ^ 2 * (v ^ 2 * commP v a) := by rw [pow_two a, pow_two v]; group

/-- **The fourth-power inertness**: `(s·v)⁴ = s⁴` — the `S⁴` factor of `r₀` is inert
because the first-order correction is a central involution. -/
private theorem pow_four_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (s * v) ^ 4 = s ^ 4 := by
  have hz : v ^ 2 * commP v s ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk hv) (commP_mem_zLayer k hk hv s)
  have hcen := (zLayer_commute hz (s ^ 2)).eq
  calc (s * v) ^ 4 = ((s * v) ^ 2) ^ 2 := by rw [← pow_mul]
    _ = (s ^ 2 * (v ^ 2 * commP v s)) ^ 2 := by rw [sq_mul_lambdaImage k hk s hv]
    _ = s ^ 2 * ((v ^ 2 * commP v s) * s ^ 2) * (v ^ 2 * commP v s) := by
        rw [pow_two (s ^ 2 * (v ^ 2 * commP v s))]; group
    _ = s ^ 2 * (s ^ 2 * (v ^ 2 * commP v s)) * (v ^ 2 * commP v s) := by rw [hcen]
    _ = s ^ 2 * s ^ 2 * ((v ^ 2 * commP v s) * (v ^ 2 * commP v s)) := by group
    _ = s ^ 2 * s ^ 2 := by rw [← pow_two (v ^ 2 * commP v s), zLayer_sq G hz, mul_one]
    _ = s ^ 4 := by group

/-- **The cross-term shift**: `commP (s·v₁) (y·v₂) = commP s y · (commP v₁ y · commP v₂ s)` —
each modification contributes exactly one central cross term, and the conjugations they
generate are trivial because the surviving factors already lie in `λ₂`. -/
private theorem commP_mul_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s y : levelQuot G (k + 1))
    {v₁ v₂ : levelQuot G (k + 1)} (hv₁ : v₁ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₂ : v₂ ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (s * v₁) (y * v₂) = commP s y * (commP v₁ y * commP v₂ s) := by
  have hz₁ : commP v₁ y ∈ zLayer G k := commP_mem_zLayer k hk hv₁ y
  have hz₂ : commP v₂ s ∈ zLayer G k := commP_mem_zLayer k hk hv₂ s
  have hsy : commP s y ∈ lambdaImage G 2 (k + 1) := commP_mem_lambdaTwo (k + 1) s y
  have hv₂' : v₂ ∈ lambdaImage G 2 (k + 1) := lambdaImage_le_of_le (by omega) hv₂
  have h2 : commP v₁ (y * v₂) = commP v₁ y :=
    commP_congr_slot k hk hv₁ (by
      have h : (y * v₂)⁻¹ * y = v₂⁻¹ := by group
      rw [h]; exact (lambdaImage G 2 (k + 1)).inv_mem hv₂')
  have h3 : commP s (y * v₂) = commP v₂ s * commP s y := by
    rw [commP_mul_right, commP_symm s v₂, zLayer_inv_self hz₂,
      conj_lambdaTwo_eq_self k hk hsy hv₂]
  have h7 : v₁⁻¹ * (commP v₂ s * commP s y) * v₁ = commP v₂ s * commP s y :=
    conj_lambdaTwo_eq_self k hk
      (Subgroup.mul_mem _ (lambdaImage_le_of_le (by omega) hz₂) hsy) hv₁
  rw [commP_mul_left, h3, h2, h7, (zLayer_commute hz₂ (commP s y)).eq, mul_assoc,
    ← (zLayer_commute hz₁ (commP v₂ s)).eq]

omit [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] in
/-- Two `λ_{k-1}`-modifications commute: `[λ_{k-1}, λ_{k-1}] ⊆ λ_{2k-2} ⊆ λ_{k+1} = 1`
(this is exactly where `k ≥ 3` enters). -/
private theorem commP_lambdaImage_eq_one (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    commP u v = 1 := by
  have h := lambdaImage_le_of_le (G := G) (m := k + 1)
    (show k + 1 ≤ k - 1 + (k - 1) by omega) (commP_mem_lambdaImage_add hu hv)
  rw [lambdaImage_self] at h
  simpa using h

theorem mul_comm_lambdaImage (k : ℕ) (hk : 3 ≤ k) {u v : levelQuot G (k + 1)}
    (hu : u ∈ lambdaImage G (k - 1) (k + 1)) (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    u * v = v * u := by
  rw [mul_swap_commP u v, commP_lambdaImage_eq_one k hk hu hv, mul_one]

/-- **The conjugation shift** (`r₂`'s `x^s` block): `(x·v₁)^{s·v₀} = x^s · v₁ · ([v₀,x]·[v₁,s])`.
Both cross terms are central; the `v₀`-conjugation only sees `x` modulo `λ₂`. -/
private theorem conjP_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s x : levelQuot G (k + 1))
    {v₀ v₁ : levelQuot G (k + 1)} (hv₀ : v₀ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₁ : v₁ ∈ lambdaImage G (k - 1) (k + 1)) :
    conjP (x * v₁) (s * v₀) = conjP x s * v₁ * (commP v₀ x * commP v₁ s) := by
  have hax : commP v₀ (conjP x s) = commP v₀ x :=
    commP_congr_slot k hk hv₀ (by
      have h : (conjP x s)⁻¹ * x = commP s x := by simp only [conjP, commP]; group
      rw [h]; exact commP_mem_lambdaTwo (k + 1) s x)
  have hc₀ : commP v₀ x ∈ zLayer G k := hax ▸ commP_mem_zLayer k hk hv₀ (conjP x s)
  have hc₁ : commP v₁ s ∈ zLayer G k := commP_mem_zLayer k hk hv₁ s
  have hconj : v₀⁻¹ * conjP x s * v₀ = conjP x s * commP v₀ x := by
    rw [conj_eq_mul_commP, hax, zLayer_inv_self hc₀]
  have hstart : conjP (x * v₁) (s * v₀) = v₀⁻¹ * (conjP x s * v₁ * commP v₁ s) * v₀ := by
    simp only [conjP, commP]; group
  rw [hstart]
  exact conj_shift_core _ _ _ _ _ (fun t => (zLayer_commute hc₀ t).eq)
    (fun t => (zLayer_commute hc₁ t).eq) (mul_comm_lambdaImage k hk hv₁ hv₀) hconj

/-- **The cube shift** (`r₂`'s `x³` block): `(x·v)³ = x³ · v · (v²·[v,x])`. -/
private theorem pow_three_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (x : levelQuot G (k + 1))
    {v : levelQuot G (k + 1)} (hv : v ∈ lambdaImage G (k - 1) (k + 1)) :
    (x * v) ^ 3 = x ^ 3 * v * (v ^ 2 * commP v x) := by
  have hz : v ^ 2 * commP v x ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk hv) (commP_mem_zLayer k hk hv x)
  calc (x * v) ^ 3 = (x * v) ^ 2 * (x * v) := by rw [← pow_succ]
    _ = x ^ 2 * (v ^ 2 * commP v x) * (x * v) := by rw [sq_mul_lambdaImage k hk x hv]
    _ = x ^ 2 * ((v ^ 2 * commP v x) * x) * v := by group
    _ = x ^ 2 * (x * (v ^ 2 * commP v x)) * v := by rw [(zLayer_commute hz x).eq]
    _ = x ^ 3 * ((v ^ 2 * commP v x) * v) := by group
    _ = x ^ 3 * (v * (v ^ 2 * commP v x)) := by rw [(zLayer_commute hz v).eq]
    _ = x ^ 3 * v * (v ^ 2 * commP v x) := by group

/-- **Full inertness of the `[y, y^s]` block** (spike §2.2): the `y`-slot modification enters
both arguments of the commutator and cancels, so this block sees no shift at all. -/
private theorem commP_conjP_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s y : levelQuot G (k + 1))
    {v₀ v₂ : levelQuot G (k + 1)} (hv₀ : v₀ ∈ lambdaImage G (k - 1) (k + 1))
    (hv₂ : v₂ ∈ lambdaImage G (k - 1) (k + 1)) :
    commP (y * v₂) (conjP (y * v₂) (s * v₀)) = commP y (conjP y s) := by
  rw [conjP_mul_lambdaImage k hk s y hv₀ hv₂]
  have hz : commP v₀ y * commP v₂ s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk hv₀ y) (commP_mem_zLayer k hk hv₂ s)
  have hzy : commP v₂ y ∈ zLayer G k := commP_mem_zLayer k hk hv₂ y
  have hyb : commP y (conjP y s) ∈ lambdaImage G 2 (k + 1) :=
    commP_mem_lambdaTwo (k + 1) y (conjP y s)
  have hby : (conjP y s)⁻¹ * y = commP s y := by simp only [conjP, commP]; group
  have hv₂z : v₂ * (commP v₀ y * commP v₂ s) ∈ lambdaImage G (k - 1) (k + 1) :=
    Subgroup.mul_mem _ hv₂ (lambdaImage_le_of_le (by omega) hz)
  -- the second slot is `y` modulo `λ₂`, so the `v₂`-bracket only sees `y`
  have h2 : commP v₂ (conjP y s * v₂ * (commP v₀ y * commP v₂ s)) = commP v₂ y :=
    commP_congr_slot k hk hv₂ (by
      have h : (conjP y s * v₂ * (commP v₀ y * commP v₂ s))⁻¹ * y =
          (commP v₀ y * commP v₂ s)⁻¹ * (v₂⁻¹ * ((conjP y s)⁻¹ * y)) := by group
      rw [h, hby]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (lambdaImage_le_of_le (by omega) hz))
        (Subgroup.mul_mem _ (Subgroup.inv_mem _ (lambdaImage_le_of_le (by omega) hv₂))
          (commP_mem_lambdaTwo (k + 1) s y)))
  -- the `y`-bracket picks up exactly one central cross term
  have h3 : commP y (conjP y s * v₂ * (commP v₀ y * commP v₂ s)) =
      commP v₂ y * commP y (conjP y s) := by
    have hsplit : conjP y s * v₂ * (commP v₀ y * commP v₂ s) =
        conjP y s * (v₂ * (commP v₀ y * commP v₂ s)) := by group
    have hleft : commP y (v₂ * (commP v₀ y * commP v₂ s)) = commP v₂ y := by
      rw [commP_symm, commP_mul_left,
        commP_eq_one_of_mul_comm (zLayer_commute hz y).eq, mul_one,
        conj_eq_self_of_commP_eq_one
          (commP_eq_one_of_mul_comm (zLayer_commute hz (commP v₂ y)).eq.symm),
        zLayer_inv_self hzy]
    rw [hsplit, commP_mul_right, hleft, conj_lambdaTwo_eq_self k hk hyb hv₂z]
  rw [commP_mul_left, h2, h3, conj_lambdaTwo_eq_self k hk
    (Subgroup.mul_mem _ (lambdaImage_le_of_le (by omega) hzy) hyb) hv₂,
    (zLayer_commute hzy (commP y (conjP y s))).eq, mul_assoc, ← pow_two, zLayer_sq G hzy,
    mul_one]

/-- **The `r₂` shift identity** (spike §2.2): the `x`-block is π-inert but contributes both
cross terms, the `[y, y^s]` block is fully inert, and the `y²` block gives the diagonal. -/
theorem drWord_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (s x y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    drWord (s * w 0) (x * w 1) (y * w 2) = drWord s x y * dbarWordR2 s x y w := by
  have hzA : commP (w 0) x * commP (w 1) s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk (hw 0) x) (commP_mem_zLayer k hk (hw 1) s)
  have hzB : w 1 ^ 2 * commP (w 1) x ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 1)) (commP_mem_zLayer k hk (hw 1) x)
  have hzC : w 2 ^ 2 * commP (w 2) y ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 2)) (commP_mem_zLayer k hk (hw 2) y)
  have hcx : commP (w 1) x ∈ zLayer G k := commP_mem_zLayer k hk (hw 1) x
  have hvx : commP (w 1) (conjP x s) = commP (w 1) x :=
    commP_congr_slot k hk (hw 1) (by
      have h : (conjP x s)⁻¹ * x = commP s x := by simp only [conjP, commP]; group
      rw [h]; exact commP_mem_lambdaTwo (k + 1) s x)
  have hAB : (conjP x s * w 1 * (commP (w 0) x * commP (w 1) s))⁻¹ *
      (x ^ 3 * w 1 * (w 1 ^ 2 * commP (w 1) x))⁻¹ =
      (conjP x s)⁻¹ * (x ^ 3)⁻¹ * (commP (w 0) x * commP (w 1) s) := by
    rw [← mul_inv_rev, dr_inv_core (x ^ 3) (conjP x s) (w 1) _ _ (commP (w 1) x)
      (fun t => (zLayer_commute hzA t).eq) (fun t => (zLayer_commute hzB t).eq)
      (fun t => (zLayer_commute hcx t).eq)
      (by rw [mul_swap_commP, hvx]) (by rw [pow_two])
      (by rw [← pow_two, zLayer_sq G hzB]),
      mul_inv_rev (x ^ 3 * conjP x s) (commP (w 0) x * commP (w 1) s),
      zLayer_inv_self hzA, mul_inv_rev (x ^ 3) (conjP x s),
      (zLayer_commute hzA ((conjP x s)⁻¹ * (x ^ 3)⁻¹)).eq]
  rw [drWord, drWord, dbarWordR2, conjP_mul_lambdaImage k hk s x (hw 0) (hw 1),
    pow_three_mul_lambdaImage k hk x (hw 1), sq_mul_lambdaImage k hk y (hw 2),
    commP_conjP_mul_lambdaImage k hk s y (hw 0) (hw 2), hAB,
    central_reorder₃ (fun t => (zLayer_commute hzA t).eq)
      (fun t => (zLayer_commute hzC t).eq)]
  group

/-- **The `r₀` shift identity** (spike §2.2): modifying the triple `(a, s, y)` by
`λ_{k-1}`-elements multiplies the relator value by `dbarWordR0` — the `S⁴` block is inert,
the `A²` block contributes the π-diagonal `w₀²·[w₀,a]`, and `[S,Y]` the two cross terms. -/
theorem d0Word_mul_lambdaImage (k : ℕ) (hk : 3 ≤ k) (a s y : levelQuot G (k + 1))
    {w : Fin 3 → levelQuot G (k + 1)} (hw : ∀ i, w i ∈ lambdaImage G (k - 1) (k + 1)) :
    d0Word (a * w 0) (s * w 1) (y * w 2) = d0Word a s y * dbarWordR0 a s y w := by
  have hz₀ : w 0 ^ 2 * commP (w 0) a ∈ zLayer G k :=
    Subgroup.mul_mem _ (sq_mem_zLayer k hk (hw 0)) (commP_mem_zLayer k hk (hw 0) a)
  have hz₁ : commP (w 1) y * commP (w 2) s ∈ zLayer G k :=
    Subgroup.mul_mem _ (commP_mem_zLayer k hk (hw 1) y) (commP_mem_zLayer k hk (hw 2) s)
  rw [d0Word, d0Word, dbarWordR0, sq_mul_lambdaImage k hk a (hw 0),
    pow_four_mul_lambdaImage k hk s (hw 1), commP_mul_mul_lambdaImage k hk s y (hw 1) (hw 2),
    central_reorder₂ (fun t => (zLayer_commute hz₀ t).eq) (fun t => (zLayer_commute hz₁ t).eq)]
  group

end ShiftCalculus

end GQ2.Roe.Labute
