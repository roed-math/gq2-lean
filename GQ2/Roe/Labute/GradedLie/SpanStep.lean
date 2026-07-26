/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Opus-4.8 and Fable-5
-/
import GQ2.Roe.Labute.GradedLie.SpanIdentities

/-!
# GL-B: the span induction step

Design record: `docs/orchestration/span-gradedlie-plan.md` §2.1.
**Statements frozen (GL0); fills ticket GL-B.**  May cite the (possibly still
sorried) GL-A statements — axiom prints self-heal when GL-A lands (house pattern).

Proof shape (successor form, `S(k) ⇒ S(k+1)` for `k ≥ 3`, so the transport
threshold `k+1 ≥ 4` is automatic):

1. Atomize `zLayer (k+1)` by `lambdaImage_induction` at `j = k` (in `Q_{k+2}`):
   sq-atoms `mk(v²)` and bracket-atoms `mk⁅v,g⁆`, `v ∈ λ_k`, `g` ambient.
2. Bracket atoms: reduce `g` to the marked generator classes
   (`commP_mul_right_of_mem`/`commP_inv_right_of_mem` + `closure_levelMk_freeGen`);
   then `commP v β` IS a single-slot d̄-atom (`dbarWord*_single₁/₂`), and
   `commP v τ = (v²)⁻¹ · d̄(twisted slot at v)` (`dbarWord*_single₀/₂`), with `v²`
   a sq-atom.
3. Sq-atoms: `levelProj` sends `v` into `zLayer k ⊆ Q_{k+1}`; apply `prev`, pull the
   factorization back up (`exists_levelProj_preimage_lambdaImage`), absorb the
   `zLayer (k+1)`-defect (`sq_mul_zLayer`), split the square over the factors
   (`sq_mul_of_mem_lambdaImage_pred`), and transport per factor:
   tail lifts square to the level-`(k+1)` tails; d̄-atom lifts square via
   `dbarWordR0_sq`/`dbarWordR2_sq` to level-`(k+1)` d̄-atoms at the squared
   modifications.

Step 3 is packaged as the subgroup `SpanStepAux.liftSq` — the classes of `Q_{k+1}`
that lift to `λ_k(Q_{k+2})` with a controlled square — so that `prev` can be fed to it
through `Subgroup.closure_le`; the one/mul/inv bookkeeping is then the subgroup
structure itself and is shared by the two shapes, as are the layer-image calculus, the
tail transport and the commutator-convention bridge.
-/

namespace GQ2.Roe.Labute

namespace SpanStepAux

/-! ### Restated layer-image calculus

Private helpers restated binder-for-binder from `StageLemma.lean` (house precedent: the
import direction — `StageLemma` imports this file — forbids importing it).  They live in
an auxiliary namespace so that nothing here can shadow a sibling file's interface. -/

section LayerCalculus

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- `λ₁ = ⊤` survives to every level quotient. -/
private theorem lambdaImage_one_eq_top (m : ℕ) : lambdaImage G 1 m = ⊤ := by
  rw [lambdaImage, twoCentralSeries_one]
  exact Subgroup.map_top_of_surjective _ (levelMk_surjective G m)

/-- Everything lies in the depth-`1` layer image. -/
private theorem mem_lambdaImage_one {m : ℕ} (q : levelQuot G m) : q ∈ lambdaImage G 1 m := by
  rw [lambdaImage_one_eq_top]
  trivial

open scoped commutatorElement in
/-- The λ-grading lemma, transported to the level quotients and to the repo commutator
convention: `commP λₐ λᵦ ⊆ λ_{a+b}` in `Qₘ`. -/
private theorem commP_mem_lambdaImage_add {a b m : ℕ} {v g : levelQuot G m}
    (hv : v ∈ lambdaImage G a m) (hg : g ∈ lambdaImage G b m) :
    commP v g ∈ lambdaImage G (a + b) m := by
  obtain ⟨x, hx, rfl⟩ := hv
  obtain ⟨y, hy, rfl⟩ := hg
  refine ⟨commP x y, ?_, by simp only [commP, map_mul, map_inv]⟩
  have h : commP x y = ⁅x⁻¹, y⁻¹⁆ := by simp only [commP, commutatorElement_def, inv_inv]
  rw [h]
  exact commutator_mem_twoCentralSeries_add G ((twoCentralSeries G a).inv_mem hx)
    ((twoCentralSeries G b).inv_mem hy)

/-- Squares deepen a layer image by one. -/
private theorem sq_mem_lambdaImage_succ {j m : ℕ} {q : levelQuot G m}
    (hq : q ∈ lambdaImage G j m) : q ^ 2 ∈ lambdaImage G (j + 1) m := by
  obtain ⟨x, hx, rfl⟩ := hq
  exact ⟨x ^ 2, sq_mem_twoCentralSeries_succ G hx, by rw [map_pow]⟩

/-- Brackets against an arbitrary slot deepen a layer image by one. -/
private theorem commP_mem_lambdaImage_succ {j m : ℕ} {v : levelQuot G m}
    (hv : v ∈ lambdaImage G j m) (g : levelQuot G m) :
    commP v g ∈ lambdaImage G (j + 1) m :=
  commP_mem_lambdaImage_add hv (mem_lambdaImage_one g)

/-- `2ⁿ`-th powers deepen a layer image by `n` (iterated `sq_mem_lambdaImage_succ`). -/
private theorem pow_two_pow_mem_lambdaImage {j m : ℕ} {q : levelQuot G m}
    (hq : q ∈ lambdaImage G j m) (n : ℕ) : q ^ 2 ^ n ∈ lambdaImage G (j + n) m := by
  induction n with
  | zero => simpa using hq
  | succ n ih =>
      have h : q ^ 2 ^ (n + 1) = (q ^ 2 ^ n) ^ 2 := by rw [pow_succ, pow_mul]
      rw [h]
      exact sq_mem_lambdaImage_succ ih

/-- A `r₀`-shift word at `λⱼ`-modifications lies one layer deeper (all four factors do). -/
private theorem dbarWordR0_mem_lambdaImage_succ {j m : ℕ} (a s y : levelQuot G m)
    {w : Fin 3 → levelQuot G m} (hw : ∀ i, w i ∈ lambdaImage G j m) :
    dbarWordR0 a s y w ∈ lambdaImage G (j + 1) m := by
  simp only [dbarWordR0]
  exact mul_mem (mul_mem (mul_mem (sq_mem_lambdaImage_succ (hw 0))
    (commP_mem_lambdaImage_succ (hw 0) a)) (commP_mem_lambdaImage_succ (hw 1) y))
    (commP_mem_lambdaImage_succ (hw 2) s)

/-- A `r₂`-shift word at `λⱼ`-modifications lies one layer deeper. -/
private theorem dbarWordR2_mem_lambdaImage_succ {j m : ℕ} (s x y : levelQuot G m)
    {w : Fin 3 → levelQuot G m} (hw : ∀ i, w i ∈ lambdaImage G j m) :
    dbarWordR2 s x y w ∈ lambdaImage G (j + 1) m := by
  simp only [dbarWordR2]
  exact mul_mem (mul_mem (mul_mem (sq_mem_lambdaImage_succ (hw 2))
    (commP_mem_lambdaImage_succ (hw 2) y)) (commP_mem_lambdaImage_succ (hw 0) x))
    (commP_mem_lambdaImage_succ (hw 1) s)

end LayerCalculus

/-! ### Slot bookkeeping and the commutator-convention bridge -/

section Slots

variable {H : Type*} [Group H] {K : Subgroup H} {q : H}

/-- A single-slot modification triple stays inside a subgroup containing the slot value. -/
private theorem cons_slot₀_mem (hq : q ∈ K) (i : Fin 3) :
    (![q, 1, 1] : Fin 3 → H) i ∈ K := by
  fin_cases i
  exacts [hq, one_mem _, one_mem _]

/-- `cons_slot₀_mem` at the middle slot. -/
private theorem cons_slot₁_mem (hq : q ∈ K) (i : Fin 3) :
    (![1, q, 1] : Fin 3 → H) i ∈ K := by
  fin_cases i
  exacts [one_mem _, hq, one_mem _]

/-- `cons_slot₀_mem` at the last slot. -/
private theorem cons_slot₂_mem (hq : q ∈ K) (i : Fin 3) :
    (![1, 1, q] : Fin 3 → H) i ∈ K := by
  fin_cases i
  exacts [one_mem _, one_mem _, hq]

open scoped commutatorElement in
/-- Convention bridge: mathlib's `⁅v, g⁆ = v g v⁻¹ g⁻¹` is the repo's `commP` at the
inverted slots (`commP x y = x⁻¹ y⁻¹ x y`). -/
private theorem commutatorElement_eq_commP (v g : H) : ⁅v, g⁆ = commP v⁻¹ g⁻¹ := by
  simp only [commutatorElement_def, commP]
  group

/-- The bracket of anything with `1` is trivial (repo convention). -/
private theorem commP_one_right (v : H) : commP v 1 = 1 := by
  simp [commP]

end Slots

/-! ### The free pro-2 group: marked classes and target membership -/

/-- `F₃` is pro-2 (the `hpro`-hypothesis shape of the descent API). -/
private theorem freeIsProP : IsProP 2 (freeProTwo : Type) := isProP_maxProPQuotient

/-- The marked residue classes `ā, s̄, ȳ ∈ Qₘ(F₃)` — an abbreviation for the terms
appearing verbatim in `SpanTargetR0`/`SpanTargetR2`. -/
private noncomputable def mgen (m : ℕ) (i : Fin 3) : levelQuot (freeProTwo : Type) m :=
  levelMk (freeProTwo : Type) m (freeGen i)

/-- The d̄-atoms of the `r₀` target. -/
private theorem dbar_mem_spanTargetR0 (K : ℕ)
    {w : Fin 3 → levelQuot (freeProTwo : Type) (K + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (K - 1) (K + 1)) :
    dbarWordR0 (mgen (K + 1) 0) (mgen (K + 1) 1) (mgen (K + 1) 2) w ∈ SpanTargetR0 K :=
  Subgroup.subset_closure (Or.inl ⟨w, hw, rfl⟩)

/-- The d̄-atoms of the `r₂` target. -/
private theorem dbar_mem_spanTargetR2 (K : ℕ)
    {w : Fin 3 → levelQuot (freeProTwo : Type) (K + 1)}
    (hw : ∀ i, w i ∈ lambdaImage (freeProTwo : Type) (K - 1) (K + 1)) :
    dbarWordR2 (mgen (K + 1) 0) (mgen (K + 1) 1) (mgen (K + 1) 2) w ∈ SpanTargetR2 K :=
  Subgroup.subset_closure (Or.inl ⟨w, hw, rfl⟩)

/-- The `S`-tail of the `r₀` target. -/
private theorem tail_mem_spanTargetR0₁ (K : ℕ) :
    mgen (K + 1) 1 ^ 2 ^ (K - 1) ∈ SpanTargetR0 K :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

/-- The `Y`-tail of the `r₀` target. -/
private theorem tail_mem_spanTargetR0₂ (K : ℕ) :
    mgen (K + 1) 2 ^ 2 ^ (K - 1) ∈ SpanTargetR0 K :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-- The `s`-tail of the `r₂` target. -/
private theorem tail_mem_spanTargetR2₀ (K : ℕ) :
    mgen (K + 1) 0 ^ 2 ^ (K - 1) ∈ SpanTargetR2 K :=
  Subgroup.subset_closure (Or.inr (Or.inl rfl))

/-- The `x`-tail of the `r₂` target. -/
private theorem tail_mem_spanTargetR2₁ (K : ℕ) :
    mgen (K + 1) 1 ^ 2 ^ (K - 1) ∈ SpanTargetR2 K :=
  Subgroup.subset_closure (Or.inr (Or.inr rfl))

/-! ### The lift-with-square subgroup (Phase 1 of the step, shape-independent) -/

/-- **The lift-with-square subgroup**: the classes of `Q_{k+1}` that lift to
`λ_k(Q_{k+2})` with square inside the level-`(k+1)` target `T`.  It *is* a subgroup —
one/mul/inv are `map_one`/`sq_mul_of_mem_lambdaImage_pred`/`inv_pow` — which is what
makes `prev` usable through `Subgroup.closure_le`. -/
private noncomputable def liftSq (k : ℕ) (hk : 3 ≤ k)
    (T : Subgroup (levelQuot (freeProTwo : Type) (k + 1 + 1))) :
    Subgroup (levelQuot (freeProTwo : Type) (k + 1)) where
  carrier := {q | ∃ q' ∈ lambdaImage (freeProTwo : Type) k (k + 1 + 1),
      levelProj (freeProTwo : Type) (k + 1) q' = q ∧ q' ^ 2 ∈ T}
  one_mem' := ⟨1, one_mem _, map_one _, by rw [one_pow]; exact one_mem T⟩
  mul_mem' := by
    rintro x y ⟨x', hx', hxp, hxs⟩ ⟨y', hy', hyp, hys⟩
    refine ⟨x' * y', mul_mem hx' hy', by rw [map_mul, hxp, hyp], ?_⟩
    rw [sq_mul_of_mem_lambdaImage_pred (k + 1) (by omega) hx' hy']
    exact mul_mem hxs hys
  inv_mem' := by
    rintro x ⟨x', hx', hxp, hxs⟩
    exact ⟨x'⁻¹, inv_mem hx', by rw [map_inv, hxp], by rw [inv_pow]; exact inv_mem hxs⟩

/-- **Tail transport**: a level-`k` tail lifts to the corresponding level-`(k+1)` tail
(`(g^{2^{k-1}})² = g^{2^k}`). -/
private theorem tail_mem_liftSq (k : ℕ) (hk : 3 ≤ k) (i : Fin 3)
    (T : Subgroup (levelQuot (freeProTwo : Type) (k + 1 + 1)))
    (hT : mgen (k + 1 + 1) i ^ 2 ^ k ∈ T) :
    mgen (k + 1) i ^ 2 ^ (k - 1) ∈ liftSq k hk T := by
  refine ⟨mgen (k + 1 + 1) i ^ 2 ^ (k - 1), ?_, ?_, ?_⟩
  · have h := pow_two_pow_mem_lambdaImage (mem_lambdaImage_one (mgen (k + 1 + 1) i)) (k - 1)
    rwa [show 1 + (k - 1) = k by omega] at h
  · simp only [map_pow, mgen, levelProj_levelMk]
  · rw [← pow_mul, show (2 : ℕ) ^ (k - 1) * 2 = 2 ^ k by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ k)]]
    exact hT

/-! ### Phase 1: the sq-atom engine -/

/-- **The sq-atoms of `Z_{k+1}` lie in the level-`(k+1)` `r₀` target.**  Every
generator of `SpanTargetR0 k` lifts to `λ_k(Q_{k+2})` with square in
`SpanTargetR0 (k+1)` (d̄-atoms by the transport identity `dbarWordR0_sq`, tails by
`tail_mem_liftSq`), so `prev` lands inside `liftSq`; the two lifts of `mk_{k+1}(v)`
differ by a central involution, which squaring kills (`sq_mul_zLayer`). -/
private theorem key_sq_r0 (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer (freeProTwo : Type) k ≤ SpanTargetR0 k) :
    ∀ v ∈ twoCentralSeries (freeProTwo : Type) k,
      levelMk (freeProTwo : Type) (k + 1 + 1) (v ^ 2) ∈ SpanTargetR0 (k + 1) := by
  have hgen : SpanTargetR0 k ≤ liftSq k hk (SpanTargetR0 (k + 1)) := by
    rw [SpanTargetR0, Subgroup.closure_le]
    rintro q (⟨w, hw, rfl⟩ | (rfl | rfl))
    · -- d̄-atom: lift the modification slot-wise, then transport the square.
      choose w' hw'mem hw'proj using fun i =>
        exists_levelProj_preimage_lambdaImage (k - 1) (k + 1) (hw i)
      have hw2 : ∀ i, w' i ^ 2 ∈ lambdaImage (freeProTwo : Type) k (k + 1 + 1) := by
        intro i
        have h := sq_mem_lambdaImage_succ (hw'mem i)
        rwa [show k - 1 + 1 = k by omega] at h
      refine ⟨dbarWordR0 (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2) w',
        ?_, ?_, ?_⟩
      · have h := dbarWordR0_mem_lambdaImage_succ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1)
          (mgen (k + 1 + 1) 2) hw'mem
        rwa [show k - 1 + 1 = k by omega] at h
      · simp only [map_dbarWordR0, mgen, levelProj_levelMk, hw'proj]
      · rw [dbarWordR0_sq (k + 1) (by omega) (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1)
          (mgen (k + 1 + 1) 2) hw'mem]
        exact dbar_mem_spanTargetR0 (k + 1) hw2
    · exact tail_mem_liftSq k hk 1 _ (tail_mem_spanTargetR0₁ (k + 1))
    · exact tail_mem_liftSq k hk 2 _ (tail_mem_spanTargetR0₂ (k + 1))
  intro v hv
  obtain ⟨q', -, hproj, hsq⟩ := hgen (prev ⟨v, hv, rfl⟩)
  have hpr : levelProj (freeProTwo : Type) (k + 1) (levelMk (freeProTwo : Type) (k + 1 + 1) v)
      = levelProj (freeProTwo : Type) (k + 1) q' := by
    rw [levelProj_levelMk, hproj]
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul hpr
  rw [map_pow, hzeq, (zLayer_commute hz q').eq, sq_mul_zLayer (k + 1) hz]
  exact hsq

/-- The sq-atom engine, `r₂` shape (verbatim mirror of `key_sq_r0`). -/
private theorem key_sq_r2 (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer (freeProTwo : Type) k ≤ SpanTargetR2 k) :
    ∀ v ∈ twoCentralSeries (freeProTwo : Type) k,
      levelMk (freeProTwo : Type) (k + 1 + 1) (v ^ 2) ∈ SpanTargetR2 (k + 1) := by
  have hgen : SpanTargetR2 k ≤ liftSq k hk (SpanTargetR2 (k + 1)) := by
    rw [SpanTargetR2, Subgroup.closure_le]
    rintro q (⟨w, hw, rfl⟩ | (rfl | rfl))
    · choose w' hw'mem hw'proj using fun i =>
        exists_levelProj_preimage_lambdaImage (k - 1) (k + 1) (hw i)
      have hw2 : ∀ i, w' i ^ 2 ∈ lambdaImage (freeProTwo : Type) k (k + 1 + 1) := by
        intro i
        have h := sq_mem_lambdaImage_succ (hw'mem i)
        rwa [show k - 1 + 1 = k by omega] at h
      refine ⟨dbarWordR2 (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2) w',
        ?_, ?_, ?_⟩
      · have h := dbarWordR2_mem_lambdaImage_succ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1)
          (mgen (k + 1 + 1) 2) hw'mem
        rwa [show k - 1 + 1 = k by omega] at h
      · simp only [map_dbarWordR2, mgen, levelProj_levelMk, hw'proj]
      · rw [dbarWordR2_sq (k + 1) (by omega) (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1)
          (mgen (k + 1 + 1) 2) hw'mem]
        exact dbar_mem_spanTargetR2 (k + 1) hw2
    · exact tail_mem_liftSq k hk 0 _ (tail_mem_spanTargetR2₀ (k + 1))
    · exact tail_mem_liftSq k hk 1 _ (tail_mem_spanTargetR2₁ (k + 1))
  intro v hv
  obtain ⟨q', -, hproj, hsq⟩ := hgen (prev ⟨v, hv, rfl⟩)
  have hpr : levelProj (freeProTwo : Type) (k + 1) (levelMk (freeProTwo : Type) (k + 1 + 1) v)
      = levelProj (freeProTwo : Type) (k + 1) q' := by
    rw [levelProj_levelMk, hproj]
  obtain ⟨z, hz, hzeq⟩ := exists_zLayer_mul hpr
  rw [map_pow, hzeq, (zLayer_commute hz q').eq, sq_mul_zLayer (k + 1) hz]
  exact hsq

end SpanStepAux

open SpanStepAux in
/-- **The span induction step, `r₀` shape** (memo §2.1).  Fill: GL-B. -/
theorem span_step_r0 (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer (freeProTwo : Type) k ≤ SpanTargetR0 k) :
    zLayer (freeProTwo : Type) (k + 1) ≤ SpanTargetR0 (k + 1) := by
  intro q hq
  refine lambdaImage_induction (freeProTwo : Type) freeTopGenFinset freeIsProP (j := k)
    (by omega) (p := fun x => x ∈ SpanTargetR0 (k + 1)) (key_sq_r0 k hk prev) ?_ (one_mem _)
    (fun _ _ hx hy => mul_mem hx hy) (fun _ hx => inv_mem hx) hq
  -- Bracket atoms.  `v̄ = mk(v)⁻¹` is a `λ_k`-modification and `commP v̄ ·` is a
  -- homomorphism in the ambient slot, so it suffices to evaluate at the marked classes.
  intro v hv g
  have hvb : (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹
      ∈ lambdaImage (freeProTwo : Type) k (k + 1 + 1) := by
    rw [← map_inv]
    exact ⟨v⁻¹, inv_mem hv, rfl⟩
  have hvsq : ((levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹) ^ 2 ∈ SpanTargetR0 (k + 1) := by
    have h := key_sq_r0 k hk prev v⁻¹ (inv_mem hv)
    rwa [map_pow, map_inv] at h
  -- The twisted slot (`a`) costs one sq-atom; the two bracket slots are d̄-atoms outright.
  have h0 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 0)
      ∈ SpanTargetR0 (k + 1) := by
    have hd := dbarWordR0_single₀ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹
    rw [show commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 0) =
      (((levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹) ^ 2)⁻¹ *
        dbarWordR0 (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
          ![(levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹, 1, 1] by rw [hd]; group]
    exact mul_mem (inv_mem hvsq) (dbar_mem_spanTargetR0 (k + 1) (cons_slot₀_mem hvb))
  have h1 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 1)
      ∈ SpanTargetR0 (k + 1) := by
    rw [← dbarWordR0_single₂ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹]
    exact dbar_mem_spanTargetR0 (k + 1) (cons_slot₂_mem hvb)
  have h2 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 2)
      ∈ SpanTargetR0 (k + 1) := by
    rw [← dbarWordR0_single₁ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹]
    exact dbar_mem_spanTargetR0 (k + 1) (cons_slot₁_mem hvb)
  have key : ∀ z : levelQuot (freeProTwo : Type) (k + 1 + 1),
      commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ z ∈ SpanTargetR0 (k + 1) := by
    intro z
    have hz : z ∈ Subgroup.closure
        (Set.range fun i => levelMk (freeProTwo : Type) (k + 1 + 1) (freeGen i)) := by
      rw [closure_levelMk_freeGen]
      trivial
    refine Subgroup.closure_induction
      (p := fun x _ => commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ x
        ∈ SpanTargetR0 (k + 1)) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [h0, h1, h2]
    · rw [commP_one_right]
      exact one_mem _
    · intro x y _ _ hx hy
      rw [commP_mul_right_of_mem (k + 1) (by omega) hvb x y]
      exact mul_mem hx hy
    · intro x _ hx
      rw [commP_inv_right_of_mem (k + 1) (by omega) hvb x]
      exact inv_mem hx
  rw [map_commutatorElement, commutatorElement_eq_commP]
  exact key _

open SpanStepAux in
/-- The span induction step, `r₂` shape.  Fill: GL-B. -/
theorem span_step_r2 (k : ℕ) (hk : 3 ≤ k)
    (prev : zLayer (freeProTwo : Type) k ≤ SpanTargetR2 k) :
    zLayer (freeProTwo : Type) (k + 1) ≤ SpanTargetR2 (k + 1) := by
  intro q hq
  refine lambdaImage_induction (freeProTwo : Type) freeTopGenFinset freeIsProP (j := k)
    (by omega) (p := fun x => x ∈ SpanTargetR2 (k + 1)) (key_sq_r2 k hk prev) ?_ (one_mem _)
    (fun _ _ hx hy => mul_mem hx hy) (fun _ hx => inv_mem hx) hq
  intro v hv g
  have hvb : (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹
      ∈ lambdaImage (freeProTwo : Type) k (k + 1 + 1) := by
    rw [← map_inv]
    exact ⟨v⁻¹, inv_mem hv, rfl⟩
  have hvsq : ((levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹) ^ 2 ∈ SpanTargetR2 (k + 1) := by
    have h := key_sq_r2 k hk prev v⁻¹ (inv_mem hv)
    rwa [map_pow, map_inv] at h
  -- `r₂`: the twisted slot is `y` (generator 2); the bracket slots are `s`, `x`.
  have h0 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 0)
      ∈ SpanTargetR2 (k + 1) := by
    rw [← dbarWordR2_single₁ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹]
    exact dbar_mem_spanTargetR2 (k + 1) (cons_slot₁_mem hvb)
  have h1 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 1)
      ∈ SpanTargetR2 (k + 1) := by
    rw [← dbarWordR2_single₀ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹]
    exact dbar_mem_spanTargetR2 (k + 1) (cons_slot₀_mem hvb)
  have h2 : commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 2)
      ∈ SpanTargetR2 (k + 1) := by
    have hd := dbarWordR2_single₂ (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
      (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹
    rw [show commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ (mgen (k + 1 + 1) 2) =
      (((levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹) ^ 2)⁻¹ *
        dbarWordR2 (mgen (k + 1 + 1) 0) (mgen (k + 1 + 1) 1) (mgen (k + 1 + 1) 2)
          ![1, 1, (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹] by rw [hd]; group]
    exact mul_mem (inv_mem hvsq) (dbar_mem_spanTargetR2 (k + 1) (cons_slot₂_mem hvb))
  have key : ∀ z : levelQuot (freeProTwo : Type) (k + 1 + 1),
      commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ z ∈ SpanTargetR2 (k + 1) := by
    intro z
    have hz : z ∈ Subgroup.closure
        (Set.range fun i => levelMk (freeProTwo : Type) (k + 1 + 1) (freeGen i)) := by
      rw [closure_levelMk_freeGen]
      trivial
    refine Subgroup.closure_induction
      (p := fun x _ => commP (levelMk (freeProTwo : Type) (k + 1 + 1) v)⁻¹ x
        ∈ SpanTargetR2 (k + 1)) ?_ ?_ ?_ ?_ hz
    · rintro _ ⟨i, rfl⟩
      fin_cases i
      exacts [h0, h1, h2]
    · rw [commP_one_right]
      exact one_mem _
    · intro x y _ _ hx hy
      rw [commP_mul_right_of_mem (k + 1) (by omega) hvb x y]
      exact mul_mem hx hy
    · intro x _ hx
      rw [commP_inv_right_of_mem (k + 1) (by omega) hvb x]
      exact inv_mem hx
  rw [map_commutatorElement, commutatorElement_eq_commP]
  exact key _

end GQ2.Roe.Labute
