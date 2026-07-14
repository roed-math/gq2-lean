import GQ2.SectionSeven.Decorations

/-!
# Proposition 7.4, step 1 and the averaging machinery

Split off from `GQ2.SectionSeven`, building on `GQ2.SectionSeven.Decorations`.  This file provides
the abstract-block tier of Proposition 7.4:

* **Prop 7.4, step 1** (`b_λ(T₀, M) = 0`) and its dual-invariants endgame;
* the **odd averaging** (`odd_average`) and the `σ₀`-extension of a hom `K ∩ S → 𝔽₂`;
* the **quotient averaging** (the `H_V`-analogue of `odd_average`).

See `GQ2.SectionSeven` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionSeven

open QuadraticFp2

open scoped Pointwise

variable {Y : Type} [Group Y] [Finite Y]

variable {L : Subgroup Y}

/-! ## Proposition 7.4 (simple-head determinant)

The proof layer splits the paper's argument into an abstract-block tier (everything except
step 2) and the genuinely tame step 2 (`q_λ|_{T₀} = 0`), which needs `H¹(H_V, V^∨) = 0` for
the head's action image and is therefore stated with the framed-target head data
(P-15 amendment: the P-14 statement had dropped §7's standing framed-target hypothesis,
under which the paper proves 7.4 — restored here; see `docs/section67-extraction.md`). -/
omit [Finite Y] in
/-- Squares of `K` generate into `R = Φ(K)`. -/
theorem sq_mem_R (B : MinimalBlock L) {k : Y} (hk : k ∈ B.K) : k * k ∈ B.frattiniK :=
  Subgroup.subset_closure (Or.inl ⟨k, hk, rfl⟩)

omit [Finite Y] in
/-- Commutators of `K` generate into `R = Φ(K)`. -/
theorem comm_mem_R (B : MinimalBlock L) {k l : Y} (hk : k ∈ B.K) (hl : l ∈ B.K) :
    k * l * k⁻¹ * l⁻¹ ∈ B.frattiniK :=
  Subgroup.subset_closure (Or.inr ⟨k, hk, l, hl, rfl⟩)

omit [Finite Y] in
/-- Core of the dual-invariants endgame: a `Y`-invariant group homomorphism `ψ : K → 𝔽₂` that is
nonzero somewhere on `K` is impossible.  Such a `ψ` automatically kills `R = Φ(K)` (squares and
commutators die in `𝔽₂`), so its kernel is a `Y`-normal index-2 subgroup of `K` above `R`,
contradicting `lemma_7_1_dual`.  Shared by `lam_comm_vanish` and `invariant_hom_absurd`. -/
private theorem invariant_hom_absurd_core (B : MinimalBlock L)
    (ψ : Y → ZMod 2)
    (hψhom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l)
    (hψinv : ∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k)
    (t₀ : Y) (ht₀K : t₀ ∈ B.K) (ht₀ : ψ t₀ ≠ 0) : False := by
  classical
  have := B.hK
  have hψ1 : ψ 1 = 0 := by simpa using hψhom 1 (one_mem _) 1 (one_mem _)
  have hz2 : ∀ x y : ZMod 2, x + y = 0 → y = x := by decide
  have hψinvK : ∀ k, k ∈ B.K → ψ k⁻¹ = ψ k := by
    intro k hk
    have h := hψhom k hk k⁻¹ (inv_mem hk)
    rw [mul_inv_cancel, hψ1] at h
    exact hz2 _ _ h.symm
  -- the candidate index-2 subgroup `X = {k ∈ K | ψ k = 0}`
  let X : Subgroup Y :=
    { carrier := {k | k ∈ B.K ∧ ψ k = 0}
      one_mem' := ⟨one_mem _, hψ1⟩
      mul_mem' := fun {a b} ⟨haK, ha⟩ ⟨hbK, hb⟩ =>
        ⟨mul_mem haK hbK, by rw [hψhom a haK b hbK, ha, hb, add_zero]⟩
      inv_mem' := fun {a} ⟨haK, ha⟩ => ⟨inv_mem haK, by rw [hψinvK a haK, ha]⟩ }
  have hXmem : ∀ k, k ∈ X ↔ k ∈ B.K ∧ ψ k = 0 := fun k => Iff.rfl
  have hXn : X.Normal := by
    refine ⟨fun k hk y => ?_⟩
    rw [hXmem] at hk ⊢
    exact ⟨B.hK.conj_mem k hk.1 y, by rw [hψinv y k hk.1, hk.2]⟩
  have hXK : X ≤ B.K := fun k hk => hk.1
  have hRX : B.frattiniK ≤ X := by
    intro r hr
    refine Subgroup.closure_induction (p := fun g _ => g ∈ X) ?_ ⟨one_mem _, hψ1⟩
      (fun a b _ _ ha hb => mul_mem ha hb) (fun a _ ha => inv_mem ha) hr
    have hz4 : ∀ a b : ZMod 2, a + b + a + b = 0 := by decide
    rintro g (⟨k, hk, rfl⟩ | ⟨k, hk, l, hl, rfl⟩)
    · exact ⟨mul_mem hk hk, by rw [hψhom k hk k hk]; exact CharTwo.add_self_eq_zero (ψ k)⟩
    · have hmem : k * l * k⁻¹ * l⁻¹ ∈ B.K :=
        mul_mem (mul_mem (mul_mem hk hl) (inv_mem hk)) (inv_mem hl)
      refine ⟨hmem, ?_⟩
      rw [hψhom _ (mul_mem (mul_mem hk hl) (inv_mem hk)) _ (inv_mem hl),
        hψhom _ (mul_mem hk hl) _ (inv_mem hk),
        hψhom _ hk _ hl, hψinvK k hk, hψinvK l hl]
      exact hz4 _ _
  -- `(X.subgroupOf K).index = 2`, via `χ : ↥K →* Multiplicative (ZMod 2)`
  let χ : ↥B.K →* Multiplicative (ZMod 2) :=
    { toFun := fun k => Multiplicative.ofAdd (ψ ↑k)
      map_one' := by simp [hψ1]
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (ψ (↑a * ↑b))
          = Multiplicative.ofAdd (ψ ↑a) * Multiplicative.ofAdd (ψ ↑b)
        rw [hψhom ↑a a.2 ↑b b.2]; rfl }
  have hkerχ : X.subgroupOf B.K = χ.ker := by
    ext ⟨y, hy⟩
    rw [Subgroup.mem_subgroupOf, MonoidHom.mem_ker]
    show (y ∈ B.K ∧ ψ y = 0) ↔ Multiplicative.ofAdd (ψ y) = 1
    constructor
    · rintro ⟨_, h0⟩; rw [h0]; exact ofAdd_zero
    · intro h; exact ⟨hy, by simpa using congrArg Multiplicative.toAdd h⟩
  have hidx : (X.subgroupOf B.K).index = 2 := by
    rw [hkerχ, Subgroup.index_ker]
    have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
    have hdvd : Nat.card χ.range ∣ 2 := by
      have h := Subgroup.card_subgroup_dvd_card χ.range
      rwa [h2] at h
    rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with h1 | h1
    · exfalso
      have hbot : χ.range = ⊥ := Subgroup.card_eq_one.mp h1
      have hmem : χ ⟨t₀, ht₀K⟩ ∈ χ.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1' : Multiplicative.ofAdd (ψ t₀) = 1 := hmem
      exact ht₀ (by simpa using congrArg Multiplicative.toAdd h1')
    · exact h1
  exact lemma_7_1_dual B ⟨X, hXn, hRX, hXK, hidx⟩

omit [Finite Y] in
/-- **Prop 7.4, step 1** (`b_λ(T₀, M) = 0`): a `Y`-invariant additive `λ : R → 𝔽₂` kills every
commutator `[k, t]`, `k ∈ K`, `t ∈ K ∩ S`.  Abstract-block proof (no tame input) — the paper's
socle argument run at subgroup level: the right kernel `T` of the pairing
`(k, t) ↦ λ([k, t])` is a `Y`-normal subgroup; were some `t₀ ∈ K ∩ S` outside it, the
scalar-stack chain of `S` intersected with `K ∩ S` would have a first layer `⊄ T`, and any
`t*` there has all its `Y`-commutators inside `T` — making `k ↦ λ([k, t*])` a nonzero
`Y`-invariant functional on `K` killing `R`, whose kernel is a `Y`-normal index-2 subgroup of
`K` above `R`, contradicting `lemma_7_1_dual`. -/
theorem lam_comm_vanish (B : MinimalBlock L) (hRN : B.frattiniK.Normal)
    (lam : ↥B.frattiniK → ZMod 2)
    (hlam_hom : ∀ r r' : ↥B.frattiniK, lam (r * r') = lam r + lam r')
    (hlam_conj : ∀ (y r : Y) (hr : r ∈ B.frattiniK),
      lam ⟨y * r * y⁻¹, hRN.conj_mem r hr y⟩ = lam ⟨r, hr⟩) :
    ∀ k, k ∈ B.K → ∀ t, t ∈ B.K ⊓ B.S → ∀ (h : k * t * k⁻¹ * t⁻¹ ∈ B.frattiniK),
      lam ⟨k * t * k⁻¹ * t⁻¹, h⟩ = 0 := by
  classical
  -- λ-kit: value at 1
  have lam_one : lam 1 = 0 := by simpa using hlam_hom 1 1
  -- β-additivity in the `K`-slot: `[kk', t] = (k[k', t]k⁻¹)·[k, t]`
  have beta_add_k : ∀ (k k' t : Y) (hk : k ∈ B.K) (hk' : k' ∈ B.K) (ht : t ∈ B.K),
      lam ⟨k * k' * t * (k * k')⁻¹ * t⁻¹, comm_mem_R B (B.K.mul_mem hk hk') ht⟩
        = lam ⟨k' * t * k'⁻¹ * t⁻¹, comm_mem_R B hk' ht⟩
          + lam ⟨k * t * k⁻¹ * t⁻¹, comm_mem_R B hk ht⟩ := by
    intro k k' t hk hk' ht
    have e : (⟨k * k' * t * (k * k')⁻¹ * t⁻¹, comm_mem_R B (B.K.mul_mem hk hk') ht⟩ : ↥B.frattiniK)
        = ⟨k * (k' * t * k'⁻¹ * t⁻¹) * k⁻¹, hRN.conj_mem _ (comm_mem_R B hk' ht) k⟩
          * ⟨k * t * k⁻¹ * t⁻¹, comm_mem_R B hk ht⟩ := Subtype.ext (by
      show k * k' * t * (k * k')⁻¹ * t⁻¹
        = k * (k' * t * k'⁻¹ * t⁻¹) * k⁻¹ * (k * t * k⁻¹ * t⁻¹)
      group)
    rw [e, hlam_hom]
    congr 1
    exact hlam_conj k _ (comm_mem_R B hk' ht)
  -- β-additivity in the `t`-slot: `[k, tt'] = [k, t]·(t[k, t']t⁻¹)`
  have beta_add_t : ∀ (k t t' : Y) (hk : k ∈ B.K) (ht : t ∈ B.K) (ht' : t' ∈ B.K),
      lam ⟨k * (t * t') * k⁻¹ * (t * t')⁻¹, comm_mem_R B hk (B.K.mul_mem ht ht')⟩
        = lam ⟨k * t * k⁻¹ * t⁻¹, comm_mem_R B hk ht⟩
          + lam ⟨k * t' * k⁻¹ * t'⁻¹, comm_mem_R B hk ht'⟩ := by
    intro k t t' hk ht ht'
    have e : (⟨k * (t * t') * k⁻¹ * (t * t')⁻¹,
          comm_mem_R B hk (B.K.mul_mem ht ht')⟩ : ↥B.frattiniK)
        = ⟨k * t * k⁻¹ * t⁻¹, comm_mem_R B hk ht⟩
          * ⟨t * (k * t' * k⁻¹ * t'⁻¹) * t⁻¹, hRN.conj_mem _ (comm_mem_R B hk ht') t⟩ :=
      Subtype.ext (by
        show k * (t * t') * k⁻¹ * (t * t')⁻¹
          = (k * t * k⁻¹ * t⁻¹) * (t * (k * t' * k⁻¹ * t'⁻¹) * t⁻¹)
        group)
    rw [e, hlam_hom]
    congr 1
    exact hlam_conj t _ (comm_mem_R B hk ht')
  -- the right kernel `T` of the pairing, a subgroup of `Y` inside `K ⊓ S`
  let T : Subgroup Y :=
    { carrier := {t | t ∈ B.K ⊓ B.S ∧ ∀ k, k ∈ B.K → ∀ h : k * t * k⁻¹ * t⁻¹ ∈ B.frattiniK,
        lam ⟨k * t * k⁻¹ * t⁻¹, h⟩ = 0}
      one_mem' := by
        refine ⟨one_mem _, fun k hk h => ?_⟩
        have e : (⟨k * 1 * k⁻¹ * 1⁻¹, h⟩ : ↥B.frattiniK) = 1 := Subtype.ext (by
          show k * 1 * k⁻¹ * 1⁻¹ = 1
          group)
        rw [e, lam_one]
      mul_mem' := by
        rintro t t' ⟨htKS, ht⟩ ⟨ht'KS, ht'⟩
        refine ⟨mul_mem htKS ht'KS, fun k hk h => ?_⟩
        have e : (⟨k * (t * t') * k⁻¹ * (t * t')⁻¹, h⟩ : ↥B.frattiniK)
            = ⟨k * (t * t') * k⁻¹ * (t * t')⁻¹,
                comm_mem_R B hk (B.K.mul_mem htKS.1 ht'KS.1)⟩ := rfl
        rw [e, beta_add_t k t t' hk htKS.1 ht'KS.1,
          ht k hk (comm_mem_R B hk htKS.1), ht' k hk (comm_mem_R B hk ht'KS.1), add_zero]
      inv_mem' := by
        rintro t ⟨htKS, ht⟩
        refine ⟨inv_mem htKS, fun k hk h => ?_⟩
        have h1 := beta_add_t k t t⁻¹ hk htKS.1 (B.K.inv_mem htKS.1)
        have e1 : (⟨k * (t * t⁻¹) * k⁻¹ * (t * t⁻¹)⁻¹,
            comm_mem_R B hk (B.K.mul_mem htKS.1 (B.K.inv_mem htKS.1))⟩ : ↥B.frattiniK) = 1 :=
          Subtype.ext (by
            show k * (t * t⁻¹) * k⁻¹ * (t * t⁻¹)⁻¹ = 1
            group)
        rw [e1, lam_one, ht k hk (comm_mem_R B hk htKS.1), zero_add] at h1
        have e2 : (⟨k * t⁻¹ * k⁻¹ * t⁻¹⁻¹, h⟩ : ↥B.frattiniK)
            = ⟨k * t⁻¹ * k⁻¹ * t⁻¹⁻¹, comm_mem_R B hk (B.K.inv_mem htKS.1)⟩ := rfl
        rw [e2, ← h1] }
  -- suppose some `[k₀, t₀]` survives
  intro k₀ hk₀ t₀ ht₀ h₀
  by_contra hne
  have ht₀T : t₀ ∉ T := fun hT => hne (hT.2 k₀ hk₀ h₀)
  -- the scalar-stack chain of `S`, intersected with `K ⊓ S`, first escapes `T` at level `j`
  obtain ⟨n, c, hc0, hcn, hmono, hnorm, hcomm⟩ := B.scalar_below
  have hex : ∃ i, ¬ (c i ⊓ (B.K ⊓ B.S) ≤ T) := by
    refine ⟨n, fun hle => ht₀T (hle (Subgroup.mem_inf.mpr ⟨?_, ht₀⟩))⟩
    rw [hcn]
    exact ht₀.2
  set j := Nat.find hex with hjdef
  have hjspec : ¬ (c j ⊓ (B.K ⊓ B.S) ≤ T) := Nat.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h0
    apply hjspec
    rw [h0, hc0, bot_inf_eq]
    exact bot_le
  have hprev : c (j - 1) ⊓ (B.K ⊓ B.S) ≤ T :=
    not_not.mp (Nat.find_min hex (Nat.sub_lt (Nat.pos_of_ne_zero hj0) one_pos))
  obtain ⟨ts, htsmem, htsT⟩ := SetLike.not_le_iff_exists.mp hjspec
  have htsmem' := Subgroup.mem_inf.mp htsmem
  have htsK : ts ∈ B.K := htsmem'.2.1
  -- all `Y`-commutators of `ts` land in `T`
  have hcommT : ∀ y : Y, y * ts * y⁻¹ * ts⁻¹ ∈ T := by
    intro y
    have h1 : ts ∈ c ((j - 1) + 1) := by
      have hj1 : (j - 1) + 1 = j := by omega
      rw [hj1]
      exact htsmem'.1
    have h2 : y * ts * y⁻¹ * ts⁻¹ ∈ c (j - 1) := hcomm (j - 1) y ts h1
    have h3 : y * ts * y⁻¹ * ts⁻¹ ∈ B.K ⊓ B.S := Subgroup.mem_inf.mpr
      ⟨B.K.mul_mem (B.hK.conj_mem ts htsmem'.2.1 y) (B.K.inv_mem htsmem'.2.1),
        B.S.mul_mem (B.hS.conj_mem ts htsmem'.2.2 y) (B.S.inv_mem htsmem'.2.2)⟩
    exact hprev (Subgroup.mem_inf.mpr ⟨h2, h3⟩)
  -- the functional `β := λ([·, ts])` is `Y`-invariant
  have hbeta_conj : ∀ (y k : Y), k ∈ B.K →
      ∀ (h1 : y * k * y⁻¹ * ts * (y * k * y⁻¹)⁻¹ * ts⁻¹ ∈ B.frattiniK)
        (h2 : k * ts * k⁻¹ * ts⁻¹ ∈ B.frattiniK),
      lam ⟨y * k * y⁻¹ * ts * (y * k * y⁻¹)⁻¹ * ts⁻¹, h1⟩
        = lam ⟨k * ts * k⁻¹ * ts⁻¹, h2⟩ := by
    intro y k hk h1 h2
    -- `[yky⁻¹, ts] = y·[k, y⁻¹ts y]·y⁻¹`
    have hin : y⁻¹ * ts * y ∈ B.K := by simpa using B.hK.conj_mem ts htsK y⁻¹
    have hmemc : k * (y⁻¹ * ts * y) * k⁻¹ * (y⁻¹ * ts * y)⁻¹ ∈ B.frattiniK := comm_mem_R B hk hin
    have e1 : (⟨y * k * y⁻¹ * ts * (y * k * y⁻¹)⁻¹ * ts⁻¹, h1⟩ : ↥B.frattiniK)
        = ⟨y * (k * (y⁻¹ * ts * y) * k⁻¹ * (y⁻¹ * ts * y)⁻¹) * y⁻¹,
            hRN.conj_mem _ hmemc y⟩ := Subtype.ext (by
      show y * k * y⁻¹ * ts * (y * k * y⁻¹)⁻¹ * ts⁻¹
        = y * (k * (y⁻¹ * ts * y) * k⁻¹ * (y⁻¹ * ts * y)⁻¹) * y⁻¹
      group)
    rw [e1, hlam_conj y _ hmemc]
    -- `y⁻¹ ts y = w·ts` with `w := [y⁻¹, ts] ∈ T`
    set w := y⁻¹ * ts * y * ts⁻¹ with hw
    have hwT : w ∈ T := by
      rw [hw]
      simpa using hcommT y⁻¹
    have hwK : w ∈ B.K := (Subgroup.mem_inf.mp hwT.1).1
    have e2 : (⟨k * (y⁻¹ * ts * y) * k⁻¹ * (y⁻¹ * ts * y)⁻¹, hmemc⟩ : ↥B.frattiniK)
        = ⟨k * (w * ts) * k⁻¹ * (w * ts)⁻¹, comm_mem_R B hk (B.K.mul_mem hwK htsK)⟩ := by
      refine Subtype.ext ?_
      show k * (y⁻¹ * ts * y) * k⁻¹ * (y⁻¹ * ts * y)⁻¹ = k * (w * ts) * k⁻¹ * (w * ts)⁻¹
      rw [hw]
      group
    rw [e2, beta_add_t k w ts hk hwK htsK, hwT.2 k hk (comm_mem_R B hk hwK), zero_add]
  -- `β(k) = λ([k, ts])` is a `Y`-invariant hom on `K`, nonzero somewhere, so
  -- `invariant_hom_absurd_core` (which supplies the index-2 kernel above `R`) closes the goal
  have hone : ∀ x : ZMod 2, x ≠ 0 → x = 1 := by decide
  have hsurj : ∃ k, ∃ hk : k ∈ B.K,
      lam ⟨k * ts * k⁻¹ * ts⁻¹, comm_mem_R B hk htsK⟩ = 1 := by
    by_contra hall
    push Not at hall
    refine htsT ⟨htsmem'.2, fun k hk h => ?_⟩
    have e : (⟨k * ts * k⁻¹ * ts⁻¹, h⟩ : ↥B.frattiniK)
        = ⟨k * ts * k⁻¹ * ts⁻¹, comm_mem_R B hk htsK⟩ := rfl
    rw [e]
    by_contra hne0
    exact (hall k hk) (hone _ hne0)
  set ψ : Y → ZMod 2 := fun k => if hk : k ∈ B.K then
    lam ⟨k * ts * k⁻¹ * ts⁻¹, comm_mem_R B hk htsK⟩ else 0 with hψdef
  have hψhom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l := by
    intro k hk l hl
    rw [hψdef]
    simp only [dif_pos (mul_mem hk hl), dif_pos hk, dif_pos hl]
    exact (beta_add_k k l ts hk hl htsK).trans (add_comm _ _)
  have hψinv : ∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k := by
    intro y k hk
    have hyk : y * k * y⁻¹ ∈ B.K := B.hK.conj_mem k hk y
    rw [hψdef]
    simp only [dif_pos hyk, dif_pos hk]
    exact hbeta_conj y k hk (comm_mem_R B hyk htsK) (comm_mem_R B hk htsK)
  obtain ⟨ks, hks, hks1⟩ := hsurj
  exact invariant_hom_absurd_core B ψ hψhom hψinv ks hks (by
    rw [hψdef]
    simp only [dif_pos hks]
    rw [hks1]
    exact one_ne_zero)

omit [Finite Y] in
/-- **Endgame for Prop 7.4 step 2** (the `(K/R)^{∨ Y} = 0` clause, `= lemma_7_1_dual`): a
`Y`-invariant group homomorphism `ψ : K → 𝔽₂` that is nonzero somewhere on `K` is impossible.
Such a `ψ` automatically kills `R = Φ(K)` (squares and commutators die in `𝔽₂`), so its kernel
is a `Y`-normal index-2 subgroup of `K` above `R`, contradicting `lemma_7_1_dual`.  This is the
abstract-block back half of step 2; the tame front half (`key_extension`) supplies the `ψ`. -/
theorem invariant_hom_absurd (B : MinimalBlock L)
    (ψ : Y → ZMod 2)
    (hψhom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l)
    (hψinv : ∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k)
    (t₀ : Y) (ht₀K : t₀ ∈ B.K) (ht₀ : ψ t₀ ≠ 0) : False :=
  invariant_hom_absurd_core B ψ hψhom hψinv t₀ ht₀K ht₀

/-- **Odd averaging** (general, verified std-3): given an odd-order normal `A ◁ Y` with the
vanishing `(V∨)^A = 0` (any `A`-invariant hom `K → 𝔽₂` vanishing on `K ∩ S` is zero) and a hom
`σ₀ : K → 𝔽₂` whose restriction to `K ∩ S` is already `Y`-invariant, the average
`ψ = Σ_{a ∈ A} a·σ₀` is a genuinely `Y`-invariant hom on `K` still extending `σ₀|_{K∩S}`
(`A`-invariant by reindexing; `Y`-invariant since the defect `ψ∘conj_y + ψ ∈ (V∨)^A = 0`).
**Caveat for `key_extension`**: this `A ◁ Y` form is not directly applicable — the odd tame
action lives in `H_V = Y/Y_V` and `Y` itself is 2-heavy, so an odd `A ◁ Y` acting nontrivially on
`V` need not exist; the tame averaging must run over `H_V` instead (these sum mechanics carry over
once `σ₀`'s automatic `Y_V`-invariance is set up).  Kept as verified reusable infrastructure. -/
private theorem odd_average (B : MinimalBlock L) (A : Subgroup Y)
    (hAodd : Odd (Nat.card A)) (hAn : A.Normal)
    (σ₀ : Y → ZMod 2)
    (hσ₀hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → σ₀ (k * l) = σ₀ k + σ₀ l)
    (hσ₀inv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k)
    (hVA : ∀ φ : Y → ZMod 2, (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → φ (k * l) = φ k + φ l) →
      (∀ k, k ∈ B.K ⊓ B.S → φ k = 0) →
      (∀ (c : Y), c ∈ A → ∀ k, k ∈ B.K → φ (c⁻¹ * k * c) = φ k) →
      ∀ k, k ∈ B.K → φ k = 0) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k) := by
  classical
  have := B.hK
  have := B.hS
  haveI : Fintype ↥A := Fintype.ofFinite _
  set ψ : Y → ZMod 2 := fun k => ∑ a : A, σ₀ ((a : Y)⁻¹ * k * (a : Y)) with hψdef
  have hreindex : ∀ (c : A) (f : A → ZMod 2), (∑ a : A, f (c * a)) = ∑ a : A, f a :=
    fun c f => Equiv.sum_comp (Equiv.mulLeft c) f
  have hψhom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l := by
    intro k hk l hl
    rw [hψdef]
    simp only
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have hka : (a : Y)⁻¹ * k * (a : Y) ∈ B.K := by simpa using B.hK.conj_mem k hk (a : Y)⁻¹
    have hla : (a : Y)⁻¹ * l * (a : Y) ∈ B.K := by simpa using B.hK.conj_mem l hl (a : Y)⁻¹
    have e : (a : Y)⁻¹ * (k * l) * (a : Y)
        = ((a : Y)⁻¹ * k * (a : Y)) * ((a : Y)⁻¹ * l * (a : Y)) := by group
    rw [e, hσ₀hom _ hka _ hla]
  have hψext : ∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k := by
    intro k hk
    rw [hψdef]
    simp only
    have hconst : ∀ a : A, σ₀ ((a : Y)⁻¹ * k * (a : Y)) = σ₀ k := fun a => by
      simpa using hσ₀inv k hk (a : Y)⁻¹
    rw [Finset.sum_congr rfl (fun a _ => hconst a), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    obtain ⟨m, hm⟩ := hAodd
    rw [hm]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
  have hψAinv : ∀ (c : Y), c ∈ A → ∀ k, ψ (c⁻¹ * k * c) = ψ k := by
    intro c hc k
    rw [hψdef]
    simp only
    have key : (∑ a : A, σ₀ ((a : Y)⁻¹ * (c⁻¹ * k * c) * (a : Y)))
        = ∑ a : A, σ₀ (((⟨c, hc⟩ * a : A) : Y)⁻¹ * k * ((⟨c, hc⟩ * a : A) : Y)) := by
      refine Finset.sum_congr rfl (fun a _ => ?_)
      congr 1
      push_cast
      group
    rw [key, hreindex ⟨c, hc⟩ (fun a => σ₀ ((a : Y)⁻¹ * k * (a : Y)))]
  have hψYinv : ∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k := by
    intro y k hk
    set φ : Y → ZMod 2 := fun z => ψ (y * z * y⁻¹) + ψ z with hφdef
    have hφhom : ∀ a, a ∈ B.K → ∀ b, b ∈ B.K → φ (a * b) = φ a + φ b := by
      intro a ha b hb
      rw [hφdef]
      simp only
      have e : y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) := by group
      rw [e, hψhom _ (B.hK.conj_mem a ha y) _ (B.hK.conj_mem b hb y), hψhom a ha b hb]
      ring
    have hφ0 : ∀ z, z ∈ B.K ⊓ B.S → φ z = 0 := by
      intro z hz
      rw [hφdef]
      simp only
      have hyz : y * z * y⁻¹ ∈ B.K ⊓ B.S :=
        Subgroup.mem_inf.mpr ⟨B.hK.conj_mem z (Subgroup.mem_inf.mp hz).1 y,
          B.hS.conj_mem z (Subgroup.mem_inf.mp hz).2 y⟩
      rw [hψext _ hyz, hψext _ hz, hσ₀inv z hz y]
      exact CharTwo.add_self_eq_zero (σ₀ z)
    have hφAinv : ∀ (c : Y), c ∈ A → ∀ z, z ∈ B.K → φ (c⁻¹ * z * c) = φ z := by
      intro c hc z _
      rw [hφdef]
      simp only
      have hcy : y * c * y⁻¹ ∈ A := hAn.conj_mem c hc y
      have e : y * (c⁻¹ * z * c) * y⁻¹
          = (y * c * y⁻¹)⁻¹ * (y * z * y⁻¹) * (y * c * y⁻¹) := by group
      rw [e, hψAinv _ hcy, hψAinv c hc]
    have := hVA φ hφhom hφ0 hφAinv k hk
    rw [hφdef] at this
    simp only at this
    linear_combination this - (CharTwo.add_self_eq_zero (ψ k))
  exact ⟨ψ, hψhom, hψYinv, hψext⟩

omit [Finite Y] in
/-- The `σ₀` extension: a hom `σ : K ∩ S → 𝔽₂` killing `R` extends to a hom `σ₀ : K → 𝔽₂`.
Via `K/R` as an `𝔽₂`-vector space and `LinearMap.exists_extend`. -/
theorem sigma0_extends (B : MinimalBlock L) (σ : Y → ZMod 2)
    (hσhom : ∀ k, k ∈ B.K ⊓ B.S → ∀ l, l ∈ B.K ⊓ B.S → σ (k * l) = σ k + σ l)
    (hσR : ∀ r, r ∈ B.frattiniK → σ r = 0) :
    ∃ σ₀ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → σ₀ (k * l) = σ₀ k + σ₀ l) ∧
      (∀ k, k ∈ B.K ⊓ B.S → σ₀ k = σ k) := by
  classical
  haveI := B.hK
  haveI := B.hS
  -- === W = K/R as an 𝔽₂-vector space ===
  set Rsub : Subgroup ↥B.K := (frattiniLike B.K).subgroupOf B.K with hRsub
  haveI hRsubN : Rsub.Normal := (frattiniLike_normal B.K B.hK).subgroupOf B.K
  letI : CommGroup (↥B.K ⧸ Rsub) :=
    { (inferInstance : Group (↥B.K ⧸ Rsub)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with | _ a =>
        induction y using QuotientGroup.induction_on with | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hRsub,
          Subgroup.mem_subgroupOf]
        have hc : (((a * b)⁻¹ * (b * a) : ↥B.K) : Y)
            = (b : Y)⁻¹ * (a : Y)⁻¹ * ((b : Y)⁻¹)⁻¹ * ((a : Y)⁻¹)⁻¹ := by push_cast; group
        rw [hc]
        exact Subgroup.subset_closure
          (Or.inr ⟨(b : Y)⁻¹, inv_mem b.2, (a : Y)⁻¹, inv_mem a.2, rfl⟩) }
  letI : Module (ZMod 2) (Additive (↥B.K ⧸ Rsub)) := AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← ha, ← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hRsub, Subgroup.mem_subgroupOf]
    have hsq : ((a ^ 2 : ↥B.K) : Y) = (a : Y) * (a : Y) := by push_cast; rw [pow_two]
    rw [hsq]
    exact Subgroup.subset_closure (Or.inl ⟨(a : Y), a.2, rfl⟩))
  set W := Additive (↥B.K ⧸ Rsub) with hW
  set qW : ↥B.K → W := fun k => Additive.ofMul (QuotientGroup.mk k) with hqW
  have hqWadd : ∀ (a b : ↥B.K), qW (a * b) = qW a + qW b := by
    intro a b
    rw [hqW]; show Additive.ofMul (QuotientGroup.mk (a * b)) = _
    rw [QuotientGroup.mk_mul, ofMul_mul]
  -- === U = (K∩S)/R as an 𝔽₂-vector space ===
  set KS : Subgroup Y := B.K ⊓ B.S with hKS
  set RsubU : Subgroup ↥KS := (frattiniLike B.K).subgroupOf KS with hRsubU
  haveI hRsubUN : RsubU.Normal := (frattiniLike_normal B.K B.hK).subgroupOf KS
  letI : CommGroup (↥KS ⧸ RsubU) :=
    { (inferInstance : Group (↥KS ⧸ RsubU)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with | _ a =>
        induction y using QuotientGroup.induction_on with | _ b =>
        rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, hRsubU,
          Subgroup.mem_subgroupOf]
        have haK : (a : Y) ∈ B.K := (Subgroup.mem_inf.mp a.2).1
        have hbK : (b : Y) ∈ B.K := (Subgroup.mem_inf.mp b.2).1
        have hc : (((a * b)⁻¹ * (b * a) : ↥KS) : Y)
            = (b : Y)⁻¹ * (a : Y)⁻¹ * ((b : Y)⁻¹)⁻¹ * ((a : Y)⁻¹)⁻¹ := by push_cast; group
        rw [hc]
        exact Subgroup.subset_closure
          (Or.inr ⟨(b : Y)⁻¹, inv_mem hbK, (a : Y)⁻¹, inv_mem haK, rfl⟩) }
  letI : Module (ZMod 2) (Additive (↥KS ⧸ RsubU)) := AddCommGroup.zmodModule (by
    intro x
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    rw [← ha, ← QuotientGroup.mk_pow]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hRsubU, Subgroup.mem_subgroupOf]
    have haK : (a : Y) ∈ B.K := (Subgroup.mem_inf.mp a.2).1
    have hsq : ((a ^ 2 : ↥KS) : Y) = (a : Y) * (a : Y) := by push_cast; rw [pow_two]
    rw [hsq]
    exact Subgroup.subset_closure (Or.inl ⟨(a : Y), haK, rfl⟩))
  set U := Additive (↥KS ⧸ RsubU) with hU
  -- === ν : U →ₗ 𝔽₂ (from σ) ===
  set σhom : ↥KS →* Multiplicative (ZMod 2) :=
    { toFun := fun x => Multiplicative.ofAdd (σ ↑x)
      map_one' := by
        show Multiplicative.ofAdd (σ (1 : ↥KS)) = 1
        have : σ ((1 : ↥KS) : Y) = 0 := by simpa using hσhom 1 (one_mem _) 1 (one_mem _)
        rw [this]; rfl
      map_mul' := fun a b => by
        show Multiplicative.ofAdd (σ ↑(a * b))
          = Multiplicative.ofAdd (σ ↑a) * Multiplicative.ofAdd (σ ↑b)
        rw [show ((a * b : ↥KS) : Y) = (↑a * ↑b : Y) from rfl,
          hσhom ↑a a.2 ↑b b.2]; rfl } with hσhomdef
  have hkill : RsubU ≤ σhom.ker := by
    intro x hx
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (σ ↑x) = 1
    rw [hRsubU, Subgroup.mem_subgroupOf] at hx
    rw [hσR ↑x hx]; rfl
  set νmon : (↥KS ⧸ RsubU) →* Multiplicative (ZMod 2) :=
    QuotientGroup.lift RsubU σhom hkill with hνmon
  set νadd : U →+ ZMod 2 :=
    { toFun := fun x => Multiplicative.toAdd (νmon (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun a b => by
        show Multiplicative.toAdd (νmon (Additive.toMul (a + b)))
          = Multiplicative.toAdd (νmon (Additive.toMul a))
            + Multiplicative.toAdd (νmon (Additive.toMul b))
        rw [toMul_add, map_mul, toAdd_mul] } with hνadd
  set ν : U →ₗ[ZMod 2] ZMod 2 := νadd.toZModLinearMap (n := 2) with hν
  -- === Λ : U →ₗ W (from inclusion K∩S ↪ K) ===
  have hmap : RsubU ≤ Rsub.comap (Subgroup.inclusion (inf_le_left : KS ≤ B.K)) := by
    intro x hx
    rw [Subgroup.mem_comap, hRsub, Subgroup.mem_subgroupOf]
    rw [hRsubU, Subgroup.mem_subgroupOf] at hx
    simpa using hx
  set Λmon : (↥KS ⧸ RsubU) →* (↥B.K ⧸ Rsub) :=
    QuotientGroup.map RsubU Rsub (Subgroup.inclusion (inf_le_left : KS ≤ B.K)) hmap with hΛmon
  set Λadd : U →+ W :=
    { toFun := fun x => Additive.ofMul (Λmon (Additive.toMul x))
      map_zero' := by simp
      map_add' := fun a b => by
        show Additive.ofMul (Λmon (Additive.toMul (a + b)))
          = Additive.ofMul (Λmon (Additive.toMul a)) + Additive.ofMul (Λmon (Additive.toMul b))
        rw [toMul_add, map_mul, ofMul_mul] } with hΛadd
  set Λ : U →ₗ[ZMod 2] W := Λadd.toZModLinearMap (n := 2) with hΛ
  have hΛinj : Function.Injective Λ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨a, ha⟩ := QuotientGroup.mk_surjective (Additive.toMul x)
    have hx0 : Λmon (Additive.toMul x) = 1 := by
      have : Additive.ofMul (Λmon (Additive.toMul x)) = (0 : W) := hx
      simpa using this
    rw [← ha] at hx0
    rw [hΛmon, QuotientGroup.map_mk] at hx0
    -- `mk (incl a) = 1` in `↥K/Rsub`, i.e. `incl a ∈ Rsub`, i.e. `↑a ∈ frattiniLike`
    rw [QuotientGroup.eq_one_iff, hRsub, Subgroup.mem_subgroupOf] at hx0
    apply Additive.toMul.injective
    rw [← ha, toMul_zero]
    refine (QuotientGroup.eq_one_iff _).mpr ?_
    rw [hRsubU, Subgroup.mem_subgroupOf]
    simpa using hx0
  -- === extend the functional ===
  set e : U ≃ₗ[ZMod 2] ↥(LinearMap.range Λ) := LinearEquiv.ofInjective Λ hΛinj with he
  obtain ⟨φ, hφ⟩ := LinearMap.exists_extend (ν.comp e.symm.toLinearMap)
  -- === σ₀ ===
  refine ⟨fun y => if h : y ∈ B.K then φ (qW ⟨y, h⟩) else 0, ?_, ?_⟩
  · -- hom on K
    intro k hk l hl
    simp only [dif_pos (mul_mem hk hl), dif_pos hk, dif_pos hl]
    rw [show (⟨k * l, mul_mem hk hl⟩ : ↥B.K) = ⟨k, hk⟩ * ⟨l, hl⟩ from rfl, hqWadd, map_add]
  · -- extends σ on K∩S
    intro k hk
    have hkK : k ∈ B.K := (Subgroup.mem_inf.mp hk).1
    simp only [dif_pos hkK]
    -- `u := ⟦⟨k,hk⟩⟧ ∈ U`; `Λ u = qW ⟨k, hkK⟩` and `ν u = σ k`
    set u : U := Additive.ofMul (QuotientGroup.mk (⟨k, hk⟩ : ↥KS)) with hu
    have hΛu : Λ u = qW ⟨k, hkK⟩ := by
      rw [hΛ, hqW]
      show Additive.ofMul (Λmon (Additive.toMul u)) = Additive.ofMul (QuotientGroup.mk ⟨k, hkK⟩)
      rw [hu, toMul_ofMul, hΛmon, QuotientGroup.map_mk]
      congr 1
    have hνu : ν u = σ k := by
      rw [hν]
      show Multiplicative.toAdd (νmon (Additive.toMul u)) = σ k
      rw [hu, toMul_ofMul, hνmon, QuotientGroup.lift_mk]
      show Multiplicative.toAdd (Multiplicative.ofAdd (σ ↑(⟨k, hk⟩ : ↥KS))) = σ k
      simp
    -- `φ (qW ⟨k, hkK⟩) = φ (Λ u) = (ν ∘ e.symm) ⟨Λ u, _⟩ = ν u = σ k`
    rw [← hΛu]
    have hmem : Λ u ∈ LinearMap.range Λ := ⟨u, rfl⟩
    have : φ (Λ u) = (ν.comp e.symm.toLinearMap) ⟨Λ u, hmem⟩ := by
      have := LinearMap.congr_fun hφ ⟨Λ u, hmem⟩
      simpa using this
    rw [this]
    show ν (e.symm ⟨Λ u, hmem⟩) = σ k
    have : e.symm ⟨Λ u, hmem⟩ = u := by
      rw [he]
      apply (LinearEquiv.ofInjective Λ hΛinj).injective
      rw [LinearEquiv.apply_symm_apply]
      exact Subtype.ext rfl
    rw [this, hνu]

/-- **Quotient averaging** (the `H_V`-analogue of `odd_average`): average a `Y_V`-invariant hom
`σ₀` over the odd quotient `C̃/Y_V`.  With `(V∨)^C = 0` (any `C̃`-conj-invariant hom `K→𝔽₂`
vanishing on `K∩S` is 0), the average is a `Y`-invariant hom extending `σ₀|_{K∩S}`. -/
theorem quotient_average (B : MinimalBlock L)
    (YV Ctil : Subgroup Y) (hYVn : YV.Normal) (hCtiln : Ctil.Normal)
    (hodd : Odd (Nat.card (↥Ctil ⧸ (YV.subgroupOf Ctil))))
    (σ₀ : Y → ZMod 2)
    (hσ₀hom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → σ₀ (k * l) = σ₀ k + σ₀ l)
    (hσ₀KSinv : ∀ k, k ∈ B.K ⊓ B.S → ∀ y : Y, σ₀ (y * k * y⁻¹) = σ₀ k)
    (hσ₀YV : ∀ k, k ∈ B.K → ∀ z, z ∈ YV → σ₀ (z * k * z⁻¹) = σ₀ k)
    (hVC : ∀ φ : Y → ZMod 2, (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → φ (k * l) = φ k + φ l) →
      (∀ k, k ∈ B.K ⊓ B.S → φ k = 0) →
      (∀ (c : Y), c ∈ Ctil → ∀ k, k ∈ B.K → φ (c⁻¹ * k * c) = φ k) →
      ∀ k, k ∈ B.K → φ k = 0) :
    ∃ ψ : Y → ZMod 2,
      (∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l) ∧
      (∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k) ∧
      (∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k) := by
  classical
  haveI := B.hK
  haveI := B.hS
  set N : Subgroup ↥Ctil := YV.subgroupOf Ctil with hN
  haveI hNnormal : N.Normal := hYVn.subgroupOf Ctil
  set Q := ↥Ctil ⧸ N with hQ
  haveI : Fintype Q := Fintype.ofFinite _
  -- well-definedness of the conjugation summand for `k ∈ K`
  have hwd : ∀ k, k ∈ B.K → ∀ (a b : ↥Ctil), (QuotientGroup.leftRel N).r a b →
      σ₀ ((a : Y)⁻¹ * k * (a : Y)) = σ₀ ((b : Y)⁻¹ * k * (b : Y)) := by
    intro k hk a b hab
    rw [QuotientGroup.leftRel_apply] at hab
    have hv : ((a⁻¹ * b : ↥Ctil) : Y) ∈ YV := by
      rw [hN, Subgroup.mem_subgroupOf] at hab; exact hab
    set v := ((a⁻¹ * b : ↥Ctil) : Y) with hvdef
    have hbav : (b : Y) = (a : Y) * v := by rw [hvdef]; push_cast; group
    rw [hbav]
    have e : ((a : Y) * v)⁻¹ * k * ((a : Y) * v) = v⁻¹ * ((a : Y)⁻¹ * k * (a : Y)) * v := by group
    rw [e]
    have hwK : (a : Y)⁻¹ * k * (a : Y) ∈ B.K := by
      have := B.hK.conj_mem k hk (a : Y)⁻¹; simpa using this
    have h3 := hσ₀YV _ hwK v⁻¹ (inv_mem hv)
    rw [inv_inv] at h3
    exact h3.symm
  -- the averaged functional
  set ψ : Y → ZMod 2 := fun k => if hk : k ∈ B.K then
    ∑ q : Q, Quotient.liftOn q (fun c : ↥Ctil => σ₀ ((c : Y)⁻¹ * k * (c : Y))) (hwd k hk) else 0
    with hψdef
  -- per-representative value
  have hval : ∀ k (hk : k ∈ B.K) (c : ↥Ctil),
      Quotient.liftOn (QuotientGroup.mk c : Q) (fun c : ↥Ctil => σ₀ ((c : Y)⁻¹ * k * (c : Y)))
        (hwd k hk) = σ₀ ((c : Y)⁻¹ * k * (c : Y)) := fun k hk c => rfl
  -- reindex helper
  have hreindex : ∀ (c₀ : Q) (f : Q → ZMod 2), (∑ q : Q, f (c₀ * q)) = ∑ q : Q, f q :=
    fun c₀ f => Equiv.sum_comp (Equiv.mulLeft c₀) f
  -- `ψ` is a hom on `K`
  have hψhom : ∀ k, k ∈ B.K → ∀ l, l ∈ B.K → ψ (k * l) = ψ k + ψ l := by
    intro k hk l hl
    rw [hψdef]
    simp only [dif_pos (mul_mem hk hl), dif_pos hk, dif_pos hl]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    induction q using QuotientGroup.induction_on with | _ c =>
    rw [hval _ (mul_mem hk hl) c, hval _ hk c, hval _ hl c]
    have hka : (c : Y)⁻¹ * k * (c : Y) ∈ B.K := by
      have := B.hK.conj_mem k hk (c : Y)⁻¹; simpa using this
    have hla : (c : Y)⁻¹ * l * (c : Y) ∈ B.K := by
      have := B.hK.conj_mem l hl (c : Y)⁻¹; simpa using this
    rw [show (c : Y)⁻¹ * (k * l) * (c : Y)
        = ((c : Y)⁻¹ * k * (c : Y)) * ((c : Y)⁻¹ * l * (c : Y)) by group,
      hσ₀hom _ hka _ hla]
  -- `ψ` extends `σ₀` on `K ∩ S`
  have hψext : ∀ k, k ∈ B.K ⊓ B.S → ψ k = σ₀ k := by
    intro k hk
    have hkK := (Subgroup.mem_inf.mp hk).1
    rw [hψdef]
    simp only [dif_pos hkK]
    have hconst : ∀ q : Q, Quotient.liftOn q
        (fun c : ↥Ctil => σ₀ ((c : Y)⁻¹ * k * (c : Y))) (hwd k hkK) = σ₀ k := by
      intro q
      induction q using QuotientGroup.induction_on with | _ c =>
      rw [hval _ hkK c]
      have := hσ₀KSinv k hk (c : Y)⁻¹
      simpa using this
    rw [Finset.sum_congr rfl (fun q _ => hconst q), Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card, nsmul_eq_mul]
    obtain ⟨m, hm⟩ := hodd
    rw [hm]; push_cast; rw [show (2 : ZMod 2) = 0 by decide]; ring
  -- `ψ` is `Ctil`-invariant
  have hψCinv : ∀ (c₀ : Y), c₀ ∈ Ctil → ∀ k, k ∈ B.K → ψ (c₀⁻¹ * k * c₀) = ψ k := by
    intro c₀ hc₀ k hk
    have hck : c₀⁻¹ * k * c₀ ∈ B.K := by
      have := B.hK.conj_mem k hk c₀⁻¹; simpa using this
    rw [hψdef]
    simp only [dif_pos hck, dif_pos hk]
    conv_rhs => rw [← hreindex (QuotientGroup.mk (⟨c₀, hc₀⟩ : ↥Ctil) : Q)]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    induction q using QuotientGroup.induction_on with | _ c =>
    have hmul : (QuotientGroup.mk (⟨c₀, hc₀⟩ : ↥Ctil) : Q) * QuotientGroup.mk c
        = QuotientGroup.mk (⟨c₀, hc₀⟩ * c) := by rw [← QuotientGroup.mk_mul]
    rw [hval _ hck c, hmul, hval _ hk (⟨c₀, hc₀⟩ * c)]
    congr 1
    push_cast
    group
  -- `ψ` is `Y`-invariant via `(V∨)^C = 0`
  have hψYinv : ∀ (y k : Y), k ∈ B.K → ψ (y * k * y⁻¹) = ψ k := by
    intro y k hk
    set φ : Y → ZMod 2 := fun z => ψ (y * z * y⁻¹) + ψ z with hφdef
    have hφhom : ∀ a, a ∈ B.K → ∀ b, b ∈ B.K → φ (a * b) = φ a + φ b := by
      intro a ha b hb
      rw [hφdef]
      simp only
      rw [show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group,
        hψhom _ (B.hK.conj_mem a ha y) _ (B.hK.conj_mem b hb y), hψhom a ha b hb]
      ring
    have hφ0 : ∀ z, z ∈ B.K ⊓ B.S → φ z = 0 := by
      intro z hz
      rw [hφdef]
      simp only
      have hyz : y * z * y⁻¹ ∈ B.K ⊓ B.S :=
        Subgroup.mem_inf.mpr ⟨B.hK.conj_mem z (Subgroup.mem_inf.mp hz).1 y,
          B.hS.conj_mem z (Subgroup.mem_inf.mp hz).2 y⟩
      rw [hψext _ hyz, hψext _ hz, hσ₀KSinv z hz y]
      exact CharTwo.add_self_eq_zero (σ₀ z)
    have hφCinv : ∀ (c : Y), c ∈ Ctil → ∀ z, z ∈ B.K → φ (c⁻¹ * z * c) = φ z := by
      intro c hc z hz
      rw [hφdef]
      simp only
      have hcy : y * c * y⁻¹ ∈ Ctil := hCtiln.conj_mem c hc y
      have hyz : y * z * y⁻¹ ∈ B.K := B.hK.conj_mem z hz y
      rw [show y * (c⁻¹ * z * c) * y⁻¹
          = (y * c * y⁻¹)⁻¹ * (y * z * y⁻¹) * (y * c * y⁻¹) by group,
        hψCinv _ hcy _ hyz, hψCinv c hc z hz]
    have := hVC φ hφhom hφ0 hφCinv k hk
    rw [hφdef] at this
    simp only at this
    linear_combination this - (CharTwo.add_self_eq_zero (ψ k))
  exact ⟨ψ, hψhom, hψYinv, hψext⟩


end SectionSeven

end GQ2
