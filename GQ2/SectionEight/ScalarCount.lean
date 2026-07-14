import GQ2.SectionEight.Covers

/-!
# §8: Lemma 8.2 — the common scalar character group

The exponent-2 abelian ledger collapse and the two character counts it yields:
`|Hom_cont(Γ_A, 𝔽₂)| = 8` (`lemma_8_2_gammaA`) and `|Hom_cont(G_ℚ₂, 𝔽₂)| = 8`
(`lemma_8_2_local`), via the `Π`-side count `card_char_piBd`.  Split out of
`GQ2.SectionEight` (wave 38a).
-/

open scoped Pointwise

namespace GQ2

namespace SectionEight

open QuadraticFp2

/-! ## Lemma 8.2: the common scalar character group

The `Γ_A`-side proof runs entirely over the P-04/P-05 layer: continuous characters of
`Γ_A` are `F₄`-generator values killing `N_A`; killing `N_A` forces `c(τ) = 1`
(`tameRelator_mem_NA`), and conversely `c(τ) = 1` makes `ker c` admissible — because in an
**exponent-2 abelian** quotient the whole `ω₂`-word ledger collapses and the wild relation
(6) follows from `τ = 1` (`wildRel_of_comm2` below, the §8 counterpart of the
`AppendixB` ledger evaluations; with the paper's `h₀` — eq. (3), including the bare `d₀` —
the wild value at `τ ≠ 1` is `τ`, so the relation is *not* unconditional). -/

section ExpTwoLedger

variable {A : Type*} [Group A]

/-- `powOmega2` is the identity on involutions (`orderOf ∣ 2` means order `2^0` or `2^1`). -/
lemma powOmega2_eq_self_of_sq (h2 : ∀ a : A, a * a = 1) (a : A) : powOmega2 a = a := by
  have hdvd : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact h2 a)
  rcases (Nat.prime_two.eq_one_or_self_of_dvd _ hdvd) with h | h
  · exact powOmega2_eq_self_of_orderOf_two_pow (k := 0) (by simpa using h)
  · exact powOmega2_eq_self_of_orderOf_two_pow (k := 1) (by simpa using h)

/-- In an abelian group, the paper's conjugation is trivial. -/
lemma conjP_of_comm (hcomm : ∀ a b : A, a * b = b * a) (x g : A) : conjP x g = x := by
  rw [conjP, hcomm g⁻¹ x, mul_assoc, inv_mul_cancel, mul_one]

/-- In an abelian group, the paper's commutator is trivial. -/
lemma commP_of_comm (hcomm : ∀ a b : A, a * b = b * a) (x y : A) : commP x y = 1 := by
  rw [commP, mul_assoc x⁻¹ y⁻¹ x, hcomm y⁻¹ x, ← mul_assoc x⁻¹ x y⁻¹, inv_mul_cancel,
    one_mul, inv_mul_cancel]

/-- **The wild relation follows from `τ = 1` in an exponent-2 abelian group** (the `ω₂`-ledger
collapse at `τ = 1`: `uᵢ = xᵢ`, `d₀ = 1`, `c₀ = h_c = 1`, `h₀ = x₀² = 1`, and (6) telescopes to
`1`).  For scalar characters the hypothesis is free — the tame relation already forces `τ = 1`
(`tameRel_iff_of_comm2`), so they see no *additional* wild obstruction.  (Without `τ = 1` the
wild value is `τ`: the paper's `h₀` — eq. (3), with the bare `d₀` — evaluates to `1`, not `τ`.) -/
lemma Marking.wildRel_of_comm2 (hcomm : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a * a = 1) (t : Marking A) (hτ : t.τ = 1) : t.WildRel := by
  have hpow : ∀ a : A, powOmega2 a = a := powOmega2_eq_self_of_sq h2
  have hconj : ∀ x g : A, conjP x g = x := conjP_of_comm hcomm
  have hcommP : ∀ x y : A, commP x y = 1 := commP_of_comm hcomm
  have hu1 : t.u1 = t.x₁ := by rw [Marking.u1, Marking.u, hpow, hτ, mul_one]
  have hd0 : t.d0 = 1 := by
    rw [Marking.d0, Marking.u0, Marking.u, hpow, hτ, mul_one, mul_inv_cancel]
  have hc0 : t.c0 = 1 := by rw [Marking.c0, hcommP]
  have hdg : t.dg = 1 := by rw [Marking.dg, hconj, hd0]
  have hhc : t.hc = 1 := by rw [Marking.hc, hcommP]
  have hh0 : t.h0 = 1 := by
    rw [Marking.h0, hconj, hdg, hd0, hhc]
    simp only [one_pow, mul_one]
    exact h2 t.x₀
  show t.h0 * t.u1⁻¹ * conjP t.x₁ t.σ * t.c0 = 1
  rw [hh0, hu1, hconj, hc0, one_mul, mul_one, inv_mul_cancel]

/-- In an exponent-2 abelian group, the tame relation says exactly `τ = 1`. -/
lemma Marking.tameRel_iff_of_comm2 (hcomm : ∀ a b : A, a * b = b * a)
    (h2 : ∀ a : A, a * a = 1) (t : Marking A) : t.TameRel ↔ t.τ = 1 := by
  rw [Marking.TameRel, conjP_of_comm hcomm, pow_two, h2]

/-- Exponent 2 forces commutativity (`ab = (ab)⁻¹ = b⁻¹a⁻¹ = ba`). -/
lemma mul_comm_of_exp_two (h2 : ∀ a : A, a * a = 1) (a b : A) : a * b = b * a := by
  have hinv : ∀ x : A, x⁻¹ = x := fun x => inv_eq_of_mul_eq_one_right (h2 x)
  calc a * b = (a * b)⁻¹ := (hinv _).symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev _ _
    _ = b * a := by rw [hinv, hinv]

end ExpTwoLedger

/-! ### The `Γ_A`-side character count -/

section CharGammaA

private lemma comp_quotientMk_ker {G : Type} [Group G] [TopologicalSpace G]
    (N : Subgroup G) [N.Normal]
    (φ : ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))) :
    N ≤ ((φ.comp (quotientMk N)).toMonoidHom).ker := fun x hx => by
  rw [MonoidHom.mem_ker]
  show φ (quotientMk N x) = 1
  rw [(quotientMk_eq_one_iff N).mpr hx, map_one]

private lemma quotientLift_comp_eq {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (φ : ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))) :
    quotientLift N (φ.comp (quotientMk N)) (comp_quotientMk_ker N φ) = φ := by
  ext y
  obtain ⟨x, rfl⟩ := quotientMk_surjective N y
  rfl

private lemma comp_quotientLift_eq {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal]
    (c : {c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) //
      N ≤ c.toMonoidHom.ker}) :
    (quotientLift N c.1 c.2).comp (quotientMk N) = c.1 := by
  ext x
  rfl

/-- Characters of a topological quotient group `G ⧸ N` are characters of `G` killing `N`
(the P-05 `push`/`descend` mechanics, without surjectivity; instantiated at `N_A` for the
`Γ_A`-count and at the relator subgroup for the `Π`-count). -/
noncomputable def charEquiv {G : Type} [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] (N : Subgroup G) [N.Normal] :
    ContinuousMonoidHom (G ⧸ N) (Multiplicative (ZMod 2))
      ≃ {c : ContinuousMonoidHom G (Multiplicative (ZMod 2)) //
          N ≤ c.toMonoidHom.ker} where
  toFun φ := ⟨φ.comp (quotientMk N), comp_quotientMk_ker N φ⟩
  invFun c := quotientLift N c.1 c.2
  left_inv φ := quotientLift_comp_eq N φ
  right_inv c := Subtype.ext (comp_quotientLift_eq N c)

private lemma homEquiv_symm_hom_of_values {X : Type}
    (c : ContinuousMonoidHom (FreeProfiniteGroup X) (Multiplicative (ZMod 2))) :
    ((FreeProfiniteGroup.homEquiv X
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))).hom = c := by
  have h : (FreeProfiniteGroup.homEquiv X
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm
        (fun i => c (FreeProfiniteGroup.of i))
      = CategoryTheory.ConcreteCategory.ofHom (C := ProfiniteGrp) c := by
    rw [Equiv.symm_apply_eq]
    funext i
    rw [FreeProfiniteGroup.homEquiv_apply]
    rfl
  rw [h]
  rfl

/-- Characters of a free profinite group are their generator values (the universal
property, in `ContinuousMonoidHom` form via the P-05 uniqueness lemma). -/
noncomputable def cmhEquivFun {X : Type} :
    ContinuousMonoidHom (FreeProfiniteGroup X) (Multiplicative (ZMod 2))
      ≃ (X → Multiplicative (ZMod 2)) where
  toFun c i := c (FreeProfiniteGroup.of i)
  invFun v :=
    ((FreeProfiniteGroup.homEquiv X
      (ProfiniteGrp.of (Multiplicative (ZMod 2)))).symm v).hom
  left_inv c := homEquiv_symm_hom_of_values c
  right_inv v := funext fun i =>
    FreeProfiniteGroup.homEquiv_symm_of (ProfiniteGrp.of (Multiplicative (ZMod 2))) v i

private lemma card_M2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
  rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]

/-- **The kills-`N_A` criterion**: a character of `F₄` kills `N_A` iff it kills `τ`.
Forward: `N_A` contains the tame relator (P-04), whose `𝔽₂`-image is `c(τ)`.  Backward:
`ker c` is then an *admissible* open normal subgroup (generation is automatic, the tame
relation is the `τ`-kill, and the wild relation and 2-core are unconditional in an
exponent-2 abelian quotient), so `N_A ≤ ker c` by the P-04 characterization. -/
theorem ker_char_NA_le_iff
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) (Multiplicative (ZMod 2))) :
    NA ≤ c.toMonoidHom.ker ↔ c univMarking.τ = 1 := by
  constructor
  · intro hNA
    have htame : c univMarking.tameRelator = 1 := by
      have := hNA tameRelator_mem_NA
      rwa [MonoidHom.mem_ker] at this
    rw [Marking.tameRelator, map_mul, map_inv, map_pow,
      show c (conjP univMarking.τ univMarking.σ)
          = (c univMarking.σ)⁻¹ * c univMarking.τ * c univMarking.σ from by
        rw [conjP, map_mul, map_mul, map_inv]] at htame
    have hM2 : ∀ s t : Multiplicative (ZMod 2),
        s⁻¹ * t * s * (t ^ 2)⁻¹ = 1 → t = 1 := by
      decide
    exact hM2 _ _ htame
  · intro hτ
    -- the kernel, as an open normal subgroup
    have hker_open :
        IsOpen ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
      have hset : ((c.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
          = c ⁻¹' {1} := Set.ext fun g => by simp [MonoidHom.mem_ker]
      rw [hset]
      exact (isOpen_discrete ({1} : Set (Multiplicative (ZMod 2)))).preimage
        c.continuous_toFun
    set U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
      { toSubgroup := c.toMonoidHom.ker, isOpen' := hker_open } with hU
    -- the quotient has order dividing 2, hence is exponent-2 abelian
    haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) := by
      exact Finite.of_equiv _
        (QuotientGroup.quotientKerEquivRange c.toMonoidHom).symm.toEquiv
    have hcard : Nat.card (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup) ∣ 2 := by
      calc Nat.card (FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup)
          = Nat.card c.toMonoidHom.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange c.toMonoidHom).toEquiv
        _ ∣ Nat.card (Multiplicative (ZMod 2)) := Subgroup.card_subgroup_dvd_card _
        _ = 2 := card_M2
    have h2q : ∀ y : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup, y * y = 1 := by
      intro y
      have horder : orderOf y ∣ 2 := (orderOf_dvd_natCard y).trans hcard
      rw [← pow_two]
      exact orderOf_dvd_iff_pow_eq_one.mp horder
    have hcommq : ∀ y z : FreeProfiniteGroup (Fin 4) ⧸ U.toSubgroup, y * z = z * y :=
      mul_comm_of_exp_two h2q
    -- `ker c` is admissible
    have hτq : (univMarking.map (QuotientGroup.mk' U.toSubgroup)).τ = 1 := by
      show QuotientGroup.mk' U.toSubgroup univMarking.τ = 1
      exact (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_ker.mpr hτ)
    have hadm : IsAdmissibleU U := by
      refine ⟨generates_univMarking_map U, ?_,
        Marking.wildRel_of_comm2 hcommq h2q _ hτq, ?_⟩
      · exact (Marking.tameRel_iff_of_comm2 hcommq h2q _).mpr hτq
      · intro g
        refine ⟨1, ?_⟩
        ext
        rw [SubgroupClass.coe_pow, OneMemClass.coe_one,
          show (2 : ℕ) ^ 1 = 2 from rfl, pow_two]
        exact h2q _
    exact (isAdmissibleU_iff_NA_le U).mp hadm

/-- Splitting off the `τ`-coordinate. -/
def vecEquiv : {v : Fin 4 → Multiplicative (ZMod 2) // v 1 = 1}
    ≃ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) where
  toFun v := (v.1 0, v.1 2, v.1 3)
  invFun p := ⟨![p.1, 1, p.2.1, p.2.2], rfl⟩
  left_inv v := Subtype.ext (funext fun i => by fin_cases i <;> simp [v.2])
  right_inv p := rfl

end CharGammaA

/-- **Lemma 8.2, candidate source**: `|Hom_cont(Γ_A, 𝔽₂)| = 8`.  **Proved** over the
P-04/P-05 layer: characters of `Γ_A` are `F₄`-generator values killing `N_A`
(`charEquiv`/`cmhEquivFun`), and killing `N_A` is exactly killing `τ`
(`ker_char_NA_le_iff` — the tame relator forces it, and conversely `c(τ) = 1` gives both
relations in exponent-2 abelian quotients, `Marking.wildRel_of_comm2`).  That leaves the free
`𝔽₂³` of `σ, x₀, x₁`-values. -/
theorem lemma_8_2_gammaA :
    Nat.card (ContinuousMonoidHom GammaA (Multiplicative (ZMod 2))) = 8 := by
  have e := (charEquiv NA).trans
    ((Equiv.subtypeEquiv cmhEquivFun (fun c => ker_char_NA_le_iff c)).trans vecEquiv)
  exact (Nat.card_congr e).trans (by rw [Nat.card_prod, Nat.card_prod, card_M2])

/-! ### The `Π`-side count and the local source

`𝔽₂`-characters kill the pro-2 kernel (T-05), so they factor through the maximal pro-2
quotient; `BoundaryMaps.ker_pro2F` pins that quotient as `Π`, whose characters are the
free `𝔽₂³` of `σ, x₀, x₁`-values (the `piRelator`-condition is vacuous by the same
exponent-2 ledger collapse). -/

/-- `𝔽₂` is a 2-group. -/
private lemma isPGroup_M2 : IsPGroup 2 (Multiplicative (ZMod 2)) := fun g =>
  ⟨1, by revert g; decide⟩

private lemma comm_M2 : ∀ a b : Multiplicative (ZMod 2), a * b = b * a := by decide

private lemma sq_M2 : ∀ a : Multiplicative (ZMod 2), a * a = 1 := by decide

/-- `𝔽₂` is pro-2 (finite discrete 2-group). -/
private lemma isProP_M2 :
    IsProP 2 (Multiplicative (ZMod 2)) :=
  isProP_of_isPGroup isPGroup_M2

/-- Every `𝔽₂`-character of `F₃` kills `piRelator` (the exponent-2 ledger collapse:
`x₀^{σ²}·x₀·[x₁,σ] ↦ c(x₀)² = 1`). -/
private lemma char_kills_piRelator
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :
    c piRelator = 1 := by
  have hexp : c piRelator
      = conjP (c (FreeProfiniteGroup.of 1)) (c (FreeProfiniteGroup.of 0) ^ 2)
          * c (FreeProfiniteGroup.of 1)
          * commP (c (FreeProfiniteGroup.of 2)) (c (FreeProfiniteGroup.of 0)) := by
    rw [piRelator, conjP, commP]
    simp only [map_mul, map_inv, map_pow]
    rw [conjP, commP]
  rw [hexp, conjP_of_comm comm_M2, commP_of_comm comm_M2, mul_one, sq_M2]

/-- The relator generates its relator subgroup's kernel condition: a character killing the
relator kills the whole (closed normal) relator subgroup — the `presentationLift` argument. -/
private lemma relatorSubgroup_le_ker
    (c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :
    relatorSubgroup {piRelator} ≤ c.toMonoidHom.ker := by
  have hker : IsClosed (c.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3))) := by
    have hset : (c.toMonoidHom.ker : Set (FreeProfiniteGroup (Fin 3))) = c ⁻¹' {1} :=
      Set.ext fun g => by simp [MonoidHom.mem_ker]
    rw [hset]
    exact IsClosed.preimage c.continuous_toFun isClosed_singleton
  exact Subgroup.topologicalClosure_minimal _
    (Subgroup.normalClosure_le_normal fun r hr => by
      rw [Set.mem_singleton_iff] at hr
      subst hr
      exact MonoidHom.mem_ker.mpr (char_kills_piRelator c)) hker

/-- Splitting the three `Π`-generator values. -/
private def vecEquiv₃ : (Fin 3 → Multiplicative (ZMod 2))
    ≃ (Multiplicative (ZMod 2) × Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) where
  toFun v := (v 0, v 1, v 2)
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv v := by
    funext i
    fin_cases i <;> rfl
  right_inv p := rfl

/-- **The `Π`-character count**: `|Hom_cont(Π, 𝔽₂)| = 8` — the presentation has three
generators and its relator has no mod-2 linear part (paper, proof of Lemma 8.2). -/
theorem card_char_piBd :
    Nat.card (ContinuousMonoidHom PiBd (Multiplicative (ZMod 2))) = 8 := by
  -- peel the maximal-pro-2 layer (T-05 universal property; `𝔽₂` is pro-2)
  have e1 : ContinuousMonoidHom PiBd (Multiplicative (ZMod 2))
      ≃ ContinuousMonoidHom (profinitePresentation {piRelator}) (Multiplicative (ZMod 2)) :=
    maxProPHomEquiv isProP_M2
  -- peel the presentation layer (characters of the quotient = characters killing relators)
  have e2 := charEquiv (G := FreeProfiniteGroup (Fin 3)) (relatorSubgroup {piRelator})
  -- the kernel condition is vacuous
  have e3 : {c : ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2)) //
      relatorSubgroup {piRelator} ≤ c.toMonoidHom.ker}
      ≃ (ContinuousMonoidHom (FreeProfiniteGroup (Fin 3)) (Multiplicative (ZMod 2))) :=
    Equiv.subtypeUnivEquiv relatorSubgroup_le_ker
  exact (Nat.card_congr (((e1.trans e2).trans e3).trans (cmhEquivFun.trans vecEquiv₃))).trans
    (by rw [Nat.card_prod, Nat.card_prod, card_M2])

/-- **Lemma 8.2, local source**: `|Hom_cont(G_ℚ₂, 𝔽₂)| = 8` (`= |ℚ₂ˣ/(ℚ₂ˣ)²|`).  **Proved**
via the common marked maximal pro-2 quotient: a `BoundaryMaps` witness pins `pro2F` as *the*
maximal pro-2 quotient map (`ker_pro2F`), every `𝔽₂`-character kills the pro-2 kernel
(T-05 `proPKernel_le_ker`), so precomposition with `pro2F` bijects characters of `Π` with
characters of `G_ℚ₂`, and `card_char_piBd` finishes.  [Statement amendment (F-owner): the
`BoundaryMaps` hypothesis and the `CompactSpace`/`TotallyDisconnectedSpace` instance
hypotheses on `AbsGalQ2` (the `main_presentation` house pattern) — without the bundle the
count is B4/B5-content outside the P-16 axiom budget.] -/
theorem lemma_8_2_local (B : BoundaryMaps)
    [CompactSpace AbsGalQ2] [TotallyDisconnectedSpace AbsGalQ2] :
    Nat.card (ContinuousMonoidHom AbsGalQ2 (Multiplicative (ZMod 2))) = 8 := by
  -- precomposition with `pro2F` is bijective
  have hbij : Function.Bijective
      (fun φ : ContinuousMonoidHom PiBd (Multiplicative (ZMod 2)) => φ.comp B.pro2F) := by
    constructor
    · intro φ₁ φ₂ h
      ext y
      obtain ⟨x, rfl⟩ := B.pro2F_surjective y
      exact DFunLike.congr_fun h x
    · intro c
      -- `c` kills the pro-2 kernel, which is `ker pro2F`
      have hkerc : B.pro2F.toMonoidHom.ker ≤ c.toMonoidHom.ker := by
        rw [B.ker_pro2F]
        exact proPKernel_le_ker isProP_M2 c
      -- descend `pro2F` to a continuous bijection from the canonical pro-2 quotient …
      have hKle : proPKernel 2 AbsGalQ2 ≤ B.pro2F.toMonoidHom.ker := le_of_eq B.ker_pro2F.symm
      set ψ : ContinuousMonoidHom (AbsGalQ2 ⧸ proPKernel 2 AbsGalQ2) PiBd :=
        quotientLift (proPKernel 2 AbsGalQ2) B.pro2F hKle with hψ
      have hψbij : Function.Bijective ψ := by
        constructor
        · rw [injective_iff_map_eq_one]
          intro x hx
          obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 AbsGalQ2) x
          have hx' : B.pro2F g = 1 := hx
          have hg : g ∈ proPKernel 2 AbsGalQ2 := by
            rw [← B.ker_pro2F]
            exact MonoidHom.mem_ker.mpr hx'
          exact (quotientMk_eq_one_iff _).mpr hg
        · intro y
          obtain ⟨x, hx⟩ := B.pro2F_surjective y
          exact ⟨quotientMk _ x, hx⟩
      -- … hence a topological isomorphism (compact source, T2 target)
      set e := continuousMulEquivOfBijective ψ hψbij with he
      -- factor `c` through the canonical quotient (T-05) and transport along `e`
      set c' : ContinuousMonoidHom (maxProPQuotient 2 AbsGalQ2) (Multiplicative (ZMod 2)) :=
        (maxProPHomEquiv isProP_M2).symm c with hc'
      refine ⟨c'.comp ⟨e.symm.toMulEquiv.toMonoidHom, e.symm.continuous_toFun⟩, ?_⟩
      ext x
      show c' (e.symm (B.pro2F x)) = c x
      have h1 : B.pro2F x = e (quotientMk (proPKernel 2 AbsGalQ2) x) := rfl
      rw [h1, ContinuousMulEquiv.symm_apply_apply]
      have h2 : c'.comp (maxProPMk 2 AbsGalQ2) = c :=
        (maxProPHomEquiv isProP_M2).apply_symm_apply c
      exact DFunLike.congr_fun h2 x
  exact (Nat.card_congr (Equiv.ofBijective _ hbij).symm).trans card_char_piBd

end SectionEight

end GQ2
