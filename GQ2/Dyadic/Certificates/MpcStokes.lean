/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Claude Fable-5
-/
import GQ2.Dyadic.Certificates.Mpc

/-!
# Dyadic campaign, ticket WMP-d: the procyclic `M_α` closer's standard items

WMP-c (`GQ2/Dyadic/Certificates/Mpc.lean`) discharged WMP-b's five-item handoff; this leaf
carries the *standard* `-c` closer items every sibling lane already has — the Stokes family, the
endpoint condition, the duality instantiation and a scalar Gram — plus WMP-c's one named
computational residual, the linear copy's Fox row.

-/

namespace GQ2.Dyadic.Certificates.MProcyclic

open GQ2.FoxH GQ2.Dyadic.Words.Mpc

open GQ2.Dyadic.Words.MCompact renaming deltaC → deltaCert

/-! ## §1 The traced mod-2 exponent, constructor by constructor

`heisEps i ∘ heisToFree E E₂` is what the endpoint condition measures.  The siblings computed it
by unfolding each word by hand; the target `Multiplicative (ZMod 2)` is *commutative and of
exponent two*, so every constructor has a one-line rule and the whole computation becomes
arithmetic.  Lane-generic — nothing below mentions this word (hoist candidate). -/

section Eps

variable {X : Type*} [DecidableEq X] (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : X)

/-- **The traced mod-2 exponent of a reflected word** at a resolver pair: the `i`-slot of the
abelianized, mod-2 exponent vector of `heisToFree E E₂ w`. -/
noncomputable def epsZ (w : PWord X) : Multiplicative (ZMod 2) :=
  heisEps i (heisToFree E E₂ w)

@[simp] theorem epsZ_one : epsZ E E₂ i (.one : PWord X) = 1 := map_one _

@[simp] theorem epsZ_gen (j : X) :
    epsZ E E₂ i (.gen j) = Multiplicative.ofAdd (if j = i then (1 : ZMod 2) else 0) :=
  Certificates.heisEps_of i j

@[simp] theorem epsZ_mul (u v : PWord X) :
    epsZ E E₂ i (.mul u v) = epsZ E E₂ i u * epsZ E E₂ i v :=
  map_mul _ _ _

@[simp] theorem epsZ_inv (u : PWord X) : epsZ E E₂ i (.inv u) = (epsZ E E₂ i u)⁻¹ :=
  map_inv _ _

/-- Conjugation is invisible: the target is commutative. -/
@[simp] theorem epsZ_conj (u g : PWord X) : epsZ E E₂ i (.conj u g) = epsZ E E₂ i u := by
  show heisEps i (conjR (heisToFree E E₂ u) (heisToFree E E₂ g)) = _
  rw [map_conjR, conjR_eq_self_of_comm]
  rfl

/-- Commutators are invisible. -/
@[simp] theorem epsZ_comm (u v : PWord X) : epsZ E E₂ i (.comm u v) = 1 := by
  show heisEps i (commR (heisToFree E E₂ u) (heisToFree E E₂ v)) = _
  exact monoidHom_commR_eq_one _ _ _

@[simp] theorem epsZ_zpow (u : PWord X) (k : ℤ) :
    epsZ E E₂ i (.zpow u k) = (epsZ E E₂ i u) ^ k :=
  map_zpow _ _ _

@[simp] theorem epsZ_z2pow (u : PWord X) (z : ℤ_[2]) :
    epsZ E E₂ i (.z2pow u z) = (epsZ E E₂ i u) ^ E₂ z :=
  map_zpow _ _ _

@[simp] theorem epsZ_profPow (u : PWord X) (γ : Zhat) :
    epsZ E E₂ i (.profPow u γ) = (epsZ E E₂ i u) ^ E γ :=
  map_zpow _ _ _

@[simp] theorem epsZ_omega2Pow (u : PWord X) :
    epsZ E E₂ i (PWord.omega2Pow u) = (epsZ E E₂ i u) ^ E omega2 :=
  map_zpow _ _ _

theorem epsZ_prodList : ∀ ws : List (PWord X),
    epsZ E E₂ i (PWord.prodList ws) = (ws.map (epsZ E E₂ i ·)).prod
  | [] => map_one _
  | w :: ws => by
      rw [PWord.prodList_cons, epsZ_mul, epsZ_prodList ws, List.map_cons, List.prod_cons]

/-! ### The two arithmetic facts of an exponent-two target -/

/-- Every element of the traced target is an involution. -/
theorem mult_zmod2_sq (u : Multiplicative (ZMod 2)) : u * u = 1 := by revert u; decide

/-- Even integer powers are trivial. -/
theorem mult_zmod2_even_zpow (u : Multiplicative (ZMod 2)) {k : ℤ} (hk : Even k) : u ^ k = 1 := by
  obtain ⟨j, rfl⟩ := hk
  rw [show j + j = 2 * j by ring, zpow_mul, zpow_two, mult_zmod2_sq, one_zpow]

/-- A natural even power is trivial. -/
theorem epsZ_even_zpow (u : PWord X) {k : ℕ} (hk : Even k) :
    epsZ E E₂ i (.zpow u (k : ℤ)) = 1 := by
  rw [epsZ_zpow]
  exact mult_zmod2_even_zpow _ (by exact_mod_cast hk)

end Eps

/-! ## §2 The `E₂^pc` count, and the traced vector of the procyclic-`M` word

⚠ The finding WMP-c predicted **by inspection**, machine-checked here.  The orbit-norm block
`E₂^pc = δ₂^{σ₂^s} · 𝒩_{U,m}(z)^{U^m}` carries the letter `δ₂` exactly `1 + 2m` times — one from
the head conjugate, two per orbit-norm factor (`z = δ₂δ₂^{σ₂^p}` in both emitted spellings, the
`p = 0` display `δ₂²` included).  That count is **odd at every `p`**, so `E₂^pc` is *visible* in
the traced vector: `2m` of the occurrences cancel in pairs and the head survives.

Consequence: the procyclic-`M` row does **not** die syntactically the way the compact-`M` row
does (`MCompact.heisEps_eRevW`: there each `δ` occurs exactly twice).  The endpoint condition
needs the **tame row** to absorb the surviving `δ₂`, exactly as in the pilot — WN0-c's route,
not WM0-c's.  Everything else in the word — both squares, all four commutators, both `E₀₁^pc`
copies, the plus block's `D₀²`, `Ĉ₀^{2^α}`, `C₀^{2^α}` and the handles — is invisible, and the
last two need `α ≥ 1`.  -/

section TracedVector

variable {h : ℕ} (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h))

/-- `σ₂ = σ^{ω₂}` resolves to the `E ω₂`-th power of `σ`. -/
@[simp] theorem epsZ_sigma2W :
    epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))
      = (epsZ E E₂ i (PWord.gen (Generator.sigma : Generator (2 + 2 * h)))) ^ E omega2 :=
  map_zpow _ _ _

/-- Every `σ₂`-power display is a power of `σ₂`. -/
theorem epsZ_sig2PowW : ∀ k : ℕ,
    epsZ E E₂ i (sig2PowW h k) = (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (k : ℤ)
  | 0 => by rw [show sig2PowW h 0 = .zpow sigma2W ((0 : ℕ) : ℤ) from rfl, epsZ_zpow]
  | 1 => by rw [show sig2PowW h 1 = sigma2W from rfl]; simp
  | k + 2 => by rw [show sig2PowW h (k + 2) = .zpow sigma2W ((k + 2 : ℕ) : ℤ) from rfl, epsZ_zpow]

/-- **The `δ`-row**: `δ_i = (x_iτ)^{ω₂}x_i⁻¹` resolves to `(x_iτ)^{E ω₂}x_i⁻¹`.  This is the only
letter of the whole word that ever reaches the traced vector. -/
theorem epsZ_dW (j : Fin 3) :
    epsZ E E₂ i (dW h j)
      = (epsZ E E₂ i (PWord.gen (coreLetter h j)) * epsZ E E₂ i (PWord.gen Generator.tau))
            ^ E omega2
          * (epsZ E E₂ i (PWord.gen (coreLetter h j)))⁻¹ := by
  rw [dW, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, uW,
    epsZ_omega2Pow, epsZ_prodList, epsZ_inv]

/-- `C₀ = x₂σ₂^s`. -/
theorem epsZ_c0W (s' : ℕ) :
    epsZ E E₂ i (c0W h s')
      = epsZ E E₂ i (PWord.gen (coreLetter h 2))
          * (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (s' : ℤ) := by
  rw [c0W, epsZ_prodList]
  simp

/-- `Ĉ₀ = σ₂^s`. -/
theorem epsZ_c0HatW (s' : ℕ) :
    epsZ E E₂ i (c0HatW h s')
      = (epsZ E E₂ i (sigma2W : PWord (Generator (2 + 2 * h)))) ^ (s' : ℤ) :=
  epsZ_zpow _ _ _ _ _

/-- **`E₀₁^pc` is invisible**: each of `δ₀`, `δ₁` occurs exactly twice. -/
theorem epsZ_e01W (aa bb : ℕ) : epsZ E E₂ i (e01W h aa bb) = 1 := by
  rw [e01W, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj,
    epsZ_prodList]
  rw [show ∀ u v : Multiplicative (ZMod 2), u * (u * v) * v = (u * u) * (v * v) by
      intro u v; group,
    mult_zmod2_sq, mult_zmod2_sq, one_mul]

/-- **The orbit-norm base is invisible**: `z = δ₂δ₂^{σ₂^p}` carries `δ₂` twice, in both emitted
spellings — the `p = 0` display `δ₂²` included. -/
theorem epsZ_zW : ∀ pp : ℕ, epsZ E E₂ i (zW h pp) = 1
  | 0 => by
      rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl]
      exact epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩
  | q + 1 => by
      rw [show zW h (q + 1) = PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (q + 1))] from rfl,
        epsZ_prodList]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj]
      exact mult_zmod2_sq _

/-- **The `E₂^pc` count, machine-checked**: the orbit-norm block contributes exactly the head
`δ₂`, because the `2m` occurrences inside the norm cancel in pairs.  `1 + 2m` is odd, so the
block is *visible* — the finding this ticket was asked to verify. -/
theorem epsZ_e2W (s' mm pp : ℕ) : epsZ E E₂ i (e2W h s' mm pp) = epsZ E E₂ i (dW h 2) := by
  rw [e2W, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_conj,
    epsZ_prodList]
  rw [List.prod_eq_one, mul_one]
  intro u hu
  rw [Export.orbitNormFactors, List.map_map, List.mem_map] at hu
  obtain ⟨j, -, rfl⟩ := hu
  rw [Function.comp_apply, epsZ_conj, epsZ_zW]

/-- The handle block is invisible (commutators). -/
theorem epsZ_handlesW : epsZ E E₂ i (handlesW h) = 1 := by
  rw [handlesW, epsZ_prodList]
  refine List.prod_eq_one fun u hu => ?_
  rw [List.map_map, List.mem_map] at hu
  obtain ⟨j, -, rfl⟩ := hu
  rw [Function.comp_apply, epsZ_comm]

/-- The handle tail's product is the handle block's exponent. -/
theorem epsZ_prod_handleTailW :
    (((handleTailW h).map (epsZ E E₂ i ·)).prod) = 1 := by
  cases h with
  | zero => rfl
  | succ n =>
      rw [show handleTailW (n + 1) = [handlesW (n + 1)] from rfl]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      exact epsZ_handlesW _ _ _

/-- **The linear copy's traced vector is the `E₂^pc` head, and nothing else.** -/
theorem epsZ_mpcLinW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcLinW α r pp η h) = epsZ E E₂ i (dW h 2) := by
  rw [mpcLinW, linFactors, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm,
    epsZ_e01W, epsZ_e2W]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩,
    epsZ_even_zpow _ _ _ _ (Nat.even_pow.mpr ⟨even_two, by omega⟩)]
  group

/-- **The hat copy is invisible to the traced vector** — every factor is a square, a commutator,
an even power or the `E₀₁^pc` block. -/
theorem epsZ_mpcHatW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcHatW α r pp η h) = 1 := by
  rw [mpcHatW, hatFactors, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm,
    epsZ_e01W]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩,
    epsZ_even_zpow _ _ _ _ (Nat.even_pow.mpr ⟨even_two, by omega⟩)]
  group

/-- The plus block `D₀²[D₀,D₁]` is invisible. -/
theorem epsZ_plusW : epsZ E E₂ i (plusW h) = 1 := by
  rw [plusW, epsZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩]

/-- **The whole procyclic-`M` word's traced vector is one `δ₂`**, at every resolver pair, every
`(r, p, η, h)` and every `α ≥ 1`.  The head of `E₂^pc` survives and nothing else does. -/
theorem epsZ_mpcW {α : ℕ} (hα : 1 ≤ α) (r pp : ℕ) (η : EtaDisplay) :
    epsZ E E₂ i (mpcW α r pp η h) = epsZ E E₂ i (dW h 2) := by
  rw [mpcW, epsZ_prodList, List.map_append, List.map_append, List.map_append, List.prod_append,
    List.prod_append, List.prod_append,
    show ((linFactors α r pp η h).map (epsZ E E₂ i ·)).prod = epsZ E E₂ i (mpcLinW α r pp η h) from
      (epsZ_prodList E E₂ i _).symm,
    show ((hatFactors α r pp η h).map (epsZ E E₂ i ·)).prod = epsZ E E₂ i (mpcHatW α r pp η h) from
      (epsZ_prodList E E₂ i _).symm,
    epsZ_mpcLinW E E₂ i hα r pp η, epsZ_mpcHatW E E₂ i hα r pp η,
    epsZ_prod_handleTailW E E₂ i]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one, epsZ_comm]
  rw [epsZ_even_zpow _ _ _ _ ⟨1, rfl⟩]
  group

end TracedVector

/-! ## §3 The resolved relator family and the endpoint condition

The two-relator family of `⟨σ, τ, x₀, …, x_{2h+2} ∣ τ^σ(τ^q)⁻¹, R_{M,pc}⟩` resolved at the
constant integer representative `e` of every profinite exponent, in WMP-b's Jacobian row order
(tame first, wild second).

**The route is the pilot's, and §2 says why it has to be.**  On the compact-`M` row every branch
factor dies syntactically, so `WM0-c`'s endpoint proof carries no `α`-hypothesis; here the
surviving `δ₂` of `E₂^pc` reaches the traced vector and has to be absorbed by the *tame* row.
The per-letter coefficients are then the pilot's exactly — `1 − q + e` on `τ` and `e − 1` on
`x₂`, both even — so the condition holds for all `α ≥ 1`, all `r, p, h`, every `η̂` display,
every even `q` and every odd `e`. -/

section Family

variable {α r pp h q e : ℕ} {η : EtaDisplay}

/-- **The resolved procyclic-`M` relator family** — the `ρ = Fin 2` family the WW3 machinery
consumes, in WMP-b's `foxJacobian` row order. -/
noncomputable def mpcFam (α r pp h q e : ℕ) (η : EtaDisplay) :
    Fin 2 → FreeGroup (Generator (2 + 2 * h)) :=
  ![heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q),
    heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h)]

@[simp] theorem mpcFam_zero :
    mpcFam α r pp h q e η 0
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) := rfl

@[simp] theorem mpcFam_one :
    mpcFam α r pp h q e η 1
      = heisToFree (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h) := rfl

/-- The tame relator's traced exponent. -/
theorem epsZ_tameRelW (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (i : Generator (2 + 2 * h)) (q' : ℕ) :
    epsZ E E₂ i (tameRelW (2 + 2 * h) q')
      = epsZ E E₂ i (PWord.gen (Generator.tau : Generator (2 + 2 * h)))
          * (epsZ E E₂ i (PWord.gen (Generator.tau : Generator (2 + 2 * h))) ^ (q' : ℤ))⁻¹ := by
  rw [tameRelW, epsZ_mul, epsZ_conj, epsZ_inv, epsZ_zpow]

/-- **The endpoint condition holds at every procyclic-`M` instance** (`α ≥ 1`, any `r, p, h`,
every `η̂` display, `q` even, `e` odd).

The traced vector of the branch word is the single `δ₂` that survives `E₂^pc`'s odd occurrence
count (§2's `epsZ_mpcW`), i.e. `(e − 1)·x₂ + e·τ`; the tame row contributes `(1 − q)·τ`; both
coefficients are even.  So the procyclic row's endpoint data is the *pilot's*, not the compact
`M` row's — the `E₂^pc` block is exactly the difference. -/
theorem mpc_isStokesEndpoint (hα : 1 ≤ α) (hq : Even q) (he : Odd e) :
    IsStokesEndpoint (mpcFam α r pp h q e η) := by
  intro i
  rw [Fin.sum_univ_two, mpcFam_zero, mpcFam_one]
  show Multiplicative.toAdd (epsZ (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) i
      (tameRelW (2 + 2 * h) q))
    + Multiplicative.toAdd (epsZ (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) i (mpcW α r pp η h)) = 0
  rw [epsZ_tameRelW, epsZ_mpcW _ _ _ hα, epsZ_dW]
  simp only [epsZ_gen, toAdd_mul, toAdd_inv, toAdd_zpow, toAdd_ofAdd]
  rw [zsmul_natCast_zmod2_even hq, zsmul_natCast_zmod2_odd he, CharTwo.neg_eq, CharTwo.neg_eq]
  abel_nf
  simp [CharTwo.two_eq_zero]

/-- The `√−10` instance pin — merge gate 9's row at `(α, r, p, η, h) = (2, 1, 1, .one, 0)`, the
ramified quadratic `q_K = 2` and the odd representative `e = 3`. -/
theorem sqrtNeg10_isStokesEndpoint : IsStokesEndpoint (mpcFam 2 1 1 0 2 3 .one) :=
  mpc_isStokesEndpoint (by norm_num) (by decide) (by decide)

/-- The `√10` twin (`ε = 0`, so `p = 0`): the `zW 0` display `δ₂²` is the case where the
orbit-norm base is a *literal square*, and the count is still odd. -/
theorem sqrt10_isStokesEndpoint : IsStokesEndpoint (mpcFam 2 1 0 0 2 3 .one) :=
  mpc_isStokesEndpoint (by norm_num) (by decide) (by decide)

end Family

/-! ## §4 The Stokes duality payload

WW3's packet-Lem-5.1 engine at the procyclic-`M` family.  The relator hypotheses are gate-level
`evalZ = 1` facts converted through `lift_heisToFree_eq_one_iff`; the endpoint condition is §3's
theorem; per-simple-module duality stays the hypothesis slot it is in the frozen `ℚ₂` chain
(gate-F / AS-lane discharge) — **`hsimp` is AS1's, as in every sibling lane**. -/

section Duality

universe u

variable {C : Type*} [Group C]

/-- **Packet Lem 5.1 at the procyclic-`M` row**: `stokesDuality_of_simple` instantiated at
`mpcFam`.  Downstream, WW3b's `stokesChi1_bijective` turns the conclusion into the perfect
pairing on `H¹` with no further row-specific input. -/
theorem mpc_stokesDuality {α r pp h q e : ℕ} {η : EtaDisplay} [Finite C]
    (t : Marking (2 + 2 * h) C) (hα : 1 ≤ α) (hq : Even q) (he : Odd e)
    (hrt : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (tameRelW (2 + 2 * h) q) = 1)
    (hrw : PWord.evalZ ⇑t (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h) = 1)
    (hsimp : ∀ (V : Type u) [AddCommGroup V] [DistribMulAction C V] [Finite V],
      (∀ v : V, v + v = 0) → IsSimpleModTwo C V → StokesDuality ⇑t (mpcFam α r pp h q e η) V)
    (A : Type u) [AddCommGroup A] [DistribMulAction C A] [Finite A]
    (hA₂ : ∀ a : A, a + a = 0) : StokesDuality ⇑t (mpcFam α r pp h q e η) A := by
  refine stokesDuality_of_simple ⇑t (mpcFam α r pp h q e η) ?_
    (mpc_isStokesEndpoint hα hq he) hsimp A hA₂
  intro k
  fin_cases k
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrt
  · exact (lift_heisToFree_eq_one_iff ⇑t _ _ _).mpr hrw

/-- **The traced Stokes pairing of the family** is the sum of the two second-order values — the
bridge between `heisEta1`/`stokesGram` entries and the per-word `heisEvalZ` closed forms, and in
particular the point where WMP-c's `mpcCopiesCancel` enters the Gram. -/
theorem heisEta1_mpcFam_apply {α r pp h q e : ℕ} {η : EtaDisplay} {A : Type*} [AddCommGroup A]
    [DistribMulAction C A] (t : Marking (2 + 2 * h) C) (x : Generator (2 + 2 * h) → A)
    (y : Generator (2 + 2 * h) → ElemDual A) :
    heisEta1 ⇑t (mpcFam α r pp h q e η) x y
      = (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ))
          (tameRelW (2 + 2 * h) q)).z
        + (heisEvalZ ⇑t x y (fun _ => (e : ℤ)) (fun _ => (e : ℤ)) (mpcW α r pp η h)).z := by
  rw [heisEta1_apply, Fin.sum_univ_two, mpcFam_zero, mpcFam_one,
    ← heisEvalZ_eq_lift, ← heisEvalZ_eq_lift]

end Duality

end GQ2.Dyadic.Certificates.MProcyclic
