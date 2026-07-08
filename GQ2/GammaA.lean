import GQ2.Zhat
import GQ2.FreeProfinite
import GQ2.ProfiniteQuotient
import GQ2.Subdirect
import GQ2.Statement

/-!
# `Γ_A` and the literal Theorem 1.2  (ticket T-21)

The paper's candidate group, **exactly as defined in §2.1, eq. (7)** (the *marked quotient
construction*): let `F₄` be the free profinite group on `σ, τ, x₀, x₁`; call a finite quotient
`φ : F₄ ⟶ G` **admissible** if the pushed marking generates `G`, satisfies the relations
(5) `τ^σ = τ²` and (6) `h₀u₁⁻¹x₁^σc₀ = 1`, and the normal closure of the images of `x₀, x₁` is a
2-group; then

  `N_A = ⋂ {ker φ | φ admissible}`,   `Γ_A = F₄ ⧸ N_A`.

Note the pro-2 condition on the wild part is **part of the presentation data** — `Γ_A` is *not*
the bare two-relator profinite presentation.  Since kernels of continuous homs to finite discrete
groups are exactly the open normal subgroups, `N_A` is faithfully encoded as the intersection of
all *admissible open normal subgroups* (`GQ2.NA`); `NA_le_ker` certifies that every admissible
quotient in the paper's sense (arbitrary finite target) contains `N_A` in its kernel.

This file also provides the relations (5)/(6) in their **profinite reading**: the auxiliary words
of eqs. (1)–(3) with genuine `ω₂ ∈ ℤ̂` exponents (`Marking.sigma2Hat`, …, `Marking.wildRelator`,
via `^ᶻ omega2` from `GQ2/Zhat.lean`).  The bridge lemmas
`map_tameRelator_eq_one_iff` / `map_wildRelator_eq_one_iff` prove that killing these profinite
words in a finite quotient is **the same** as the finite-level relations of `GQ2/Words.lean`
(via the T-06 headline `map_zpowHat_omega2`) — so the two readings of Theorem 1.2's relations
provably agree, and the admissibility used in `N_A` is exactly the paper's.

Finally, **Theorem 1.2 in its literal form** (`main_presentation_literal`,
`Γ_A ≅ G_{ℚ₂}` as topological groups) is stated against this honest `Γ_A` — `sorry`-backed,
awaiting Prop. 2.3 + step 2 of the program (see `docs/formalization-plan.md`).

Sanity: the machine-checked admissible `S₃`-marking of `GQ2/AppendixB.lean` classifies an
admissible quotient of `F₄` (`isAdmissible_markS3_toHom`), and `Γ_A` surjects onto `S₃`
(`gammaA_surjective_s3`) — the marked quotient construction is nonvacuous.
-/

open CategoryTheory ProfiniteGrp

namespace GQ2

/-! ## The auxiliary words with genuine profinite `ω₂`-exponents (eqs. (1)–(3), profinitely) -/

namespace Marking

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] (t : Marking G)

noncomputable section

/-- `σ₂ = σ^{ω₂}` (eq. (1)), with the genuine profinite exponent `ω₂ ∈ ℤ̂`. -/
def sigma2Hat : G := t.σ ^ᶻ omega2
/-- `u(ξ) = (ξτ)^{ω₂}` (eq. (1)). -/
def uHat (xi : G) : G := (xi * t.τ) ^ᶻ omega2
/-- `u₀ = (x₀τ)^{ω₂}`. -/
def u0Hat : G := t.uHat t.x₀
/-- `u₁ = (x₁τ)^{ω₂}`. -/
def u1Hat : G := t.uHat t.x₁
/-- `d₀ = u₀x₀⁻¹` (eq. (1)). -/
def d0Hat : G := t.u0Hat * t.x₀⁻¹
/-- `z₀ = x₀^{σ₂}` (eq. (2)). -/
def z0Hat : G := conjP t.x₀ t.sigma2Hat
/-- `c₀ = [d₀, z₀]` (eq. (2)). -/
def c0Hat : G := commP t.d0Hat t.z0Hat
/-- `g₀ = σ₂²` (eq. (2)). -/
def g0Hat : G := t.sigma2Hat ^ 2
/-- `d_g = d₀^{g₀}` (eq. (2)). -/
def dgHat : G := conjP t.d0Hat t.g0Hat
/-- `h_c = [d_g, d₀]` (eq. (3)). -/
def hcHat : G := commP t.dgHat t.d0Hat
/-- `h₀ = x₀^{g₀} · x₀ · d_g · d₀ · d₀² · h_c` (eq. (3); note the bare `d₀`, cf.
`docs/erratum-h0-transcription.md`). -/
def h0Hat : G := (conjP t.x₀ t.g0Hat) * t.x₀ * t.dgHat * t.d0Hat * t.d0Hat ^ 2 * t.hcHat

/-- The **tame relator** `τ^σ · (τ²)⁻¹` — relation (5) as a word. -/
def tameRelator : G := conjP t.τ t.σ * (t.τ ^ 2)⁻¹

/-- The **wild relator** `h₀ · u₁⁻¹ · x₁^σ · c₀` — relation (6) as a word (its letters use the
profinite `ω₂`-exponents above). -/
def wildRelator : G := t.h0Hat * t.u1Hat⁻¹ * conjP t.x₁ t.σ * t.c0Hat

end

/-! ### Faithfulness bridge: the profinite words evaluate to the finite words

Through any continuous homomorphism to a finite group, the `^ᶻ omega2`-ledger computes the
`powOmega2`-ledger of `GQ2/Words.lean` (the T-06 headline `map_zpowHat_omega2`, pushed through
the whole word ledger).  In particular relations (5)/(6) read profinitely (relator dies) and
finitely (`TameRel`/`WildRel` of the pushed marking) are the same condition. -/

section Bridge

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
  {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
  (f : ContinuousMonoidHom G P) (t : Marking G)

@[simp] lemma map_sigma2Hat : (t.map f.toMonoidHom).sigma2 = f.toMonoidHom t.sigma2Hat := by
  simp only [sigma2, map_σ, sigma2Hat]
  exact (map_zpowHat_omega2 f t.σ).symm

@[simp] lemma map_u0Hat : (t.map f.toMonoidHom).u0 = f.toMonoidHom t.u0Hat := by
  simp only [u0, u, map_x₀, map_τ, ← map_mul, u0Hat, uHat]
  exact (map_zpowHat_omega2 f _).symm

@[simp] lemma map_u1Hat : (t.map f.toMonoidHom).u1 = f.toMonoidHom t.u1Hat := by
  simp only [u1, u, map_x₁, map_τ, ← map_mul, u1Hat, uHat]
  exact (map_zpowHat_omega2 f _).symm

@[simp] lemma map_d0Hat : (t.map f.toMonoidHom).d0 = f.toMonoidHom t.d0Hat := by
  simp only [d0, map_u0Hat, map_x₀, d0Hat, map_mul, map_inv]

@[simp] lemma map_z0Hat : (t.map f.toMonoidHom).z0 = f.toMonoidHom t.z0Hat := by
  simp only [z0, map_x₀, map_sigma2Hat, z0Hat, map_conjP]

@[simp] lemma map_c0Hat : (t.map f.toMonoidHom).c0 = f.toMonoidHom t.c0Hat := by
  simp only [c0, map_d0Hat, map_z0Hat, c0Hat, map_commP]

@[simp] lemma map_g0Hat : (t.map f.toMonoidHom).g0 = f.toMonoidHom t.g0Hat := by
  simp only [g0, map_sigma2Hat, g0Hat, map_pow]

@[simp] lemma map_dgHat : (t.map f.toMonoidHom).dg = f.toMonoidHom t.dgHat := by
  simp only [dg, map_d0Hat, map_g0Hat, dgHat, map_conjP]

@[simp] lemma map_hcHat : (t.map f.toMonoidHom).hc = f.toMonoidHom t.hcHat := by
  simp only [hc, map_dgHat, map_d0Hat, hcHat, map_commP]

@[simp] lemma map_h0Hat : (t.map f.toMonoidHom).h0 = f.toMonoidHom t.h0Hat := by
  simp only [h0, map_x₀, map_g0Hat, map_dgHat, map_d0Hat, map_hcHat, h0Hat, map_conjP,
    map_mul, map_pow]

omit [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
  [DiscreteTopology P] [Finite P] in
/-- **Relation (5), profinite = finite**: the tame relator dies in a finite quotient iff the
pushed marking satisfies the tame relation of `GQ2/Words.lean`.  (No `ω₂` occurs in (5), so no
topology is needed.) -/
lemma map_tameRelator_eq_one_iff :
    f.toMonoidHom t.tameRelator = 1 ↔ (t.map f.toMonoidHom).TameRel := by
  rw [tameRelator, map_mul, map_inv, mul_inv_eq_one]
  simp only [TameRel, map_conjP, map_pow, map_τ, map_σ]

/-- **Relation (6), profinite = finite**: the wild relator dies in a finite quotient iff the
pushed marking satisfies the wild relation of `GQ2/Words.lean`. -/
lemma map_wildRelator_eq_one_iff :
    f.toMonoidHom t.wildRelator = 1 ↔ (t.map f.toMonoidHom).WildRel := by
  simp only [WildRel, wildRelator, map_mul, map_inv, map_conjP,
    map_h0Hat, map_u1Hat, map_c0Hat, map_x₁, map_σ]

end Bridge

/-! ## The universal marking and the homs it classifies -/

/-- The continuous homomorphism `F₄ ⟶ P` classified by a marking of a profinite group `P`
(the universal property of the free profinite group, inverted). -/
noncomputable def toHom {P : ProfiniteGrp.{0}} (t : Marking P) :
    FreeProfiniteGroup (Fin 4) ⟶ P :=
  (FreeProfiniteGroup.homEquiv (Fin 4) P).symm ![t.σ, t.τ, t.x₀, t.x₁]

end Marking

/-- The **universal marking**: the four generators of the free profinite group on four letters,
in the paper's order `σ, τ, x₀, x₁`. -/
noncomputable def univMarking : Marking (FreeProfiniteGroup (Fin 4)) :=
  ⟨FreeProfiniteGroup.of 0, FreeProfiniteGroup.of 1,
   FreeProfiniteGroup.of 2, FreeProfiniteGroup.of 3⟩

/-- Pushing the universal marking through the hom classified by `t` recovers `t` — the universal
property really is "evaluate at the generators". -/
@[simp] lemma univMarking_map_toHom {P : ProfiniteGrp.{0}} (t : Marking P) :
    univMarking.map t.toHom.hom.toMonoidHom = t := by
  obtain ⟨a, b, c, d⟩ := t
  simp only [Marking.map, univMarking]
  congr 1 <;> exact FreeProfiniteGroup.homEquiv_symm_of _ _ _

/-- A marking whose pushforward of the universal marking generates classifies a **surjective**
hom (the image contains a generating set). -/
lemma surjective_of_map_generates {P : Type*} [Group P]
    (f : FreeProfiniteGroup (Fin 4) →* P)
    (hgen : (univMarking.map f).Generates) : Function.Surjective f := by
  rw [Marking.Generates] at hgen
  have hle : Subgroup.closure ({(univMarking.map f).σ, (univMarking.map f).τ,
      (univMarking.map f).x₀, (univMarking.map f).x₁} : Set P) ≤ f.range := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro z (rfl | rfl | rfl | rfl)
    · exact ⟨univMarking.σ, rfl⟩
    · exact ⟨univMarking.τ, rfl⟩
    · exact ⟨univMarking.x₀, rfl⟩
    · exact ⟨univMarking.x₁, rfl⟩
  intro y
  exact hle (hgen ▸ Subgroup.mem_top y)

/-! ## `N_A` and `Γ_A` (paper §2.1, eq. (7)) -/

/-- An open normal subgroup `U ≤ F₄` is **admissible** (paper §2.1) if the canonical finite
quotient `F₄ ⧸ U` carries an admissible pushed marking: the images of `σ, τ, x₀, x₁` generate,
satisfy relations (5) and (6) — equivalently (by `map_tameRelator_eq_one_iff` /
`map_wildRelator_eq_one_iff`) the profinite relator words die — and the normal closure of the
images of `x₀, x₁` is a 2-group.  Open normal subgroups are exactly the kernels of continuous
homs to finite discrete groups, so this encodes the paper's class `Q_A` of admissible finite
quotients (see `NA_le_ker` for the certificate). -/
def IsAdmissibleU (U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4))) : Prop :=
  (univMarking.map (QuotientGroup.mk' U.toSubgroup)).Admissible

/-- **`N_A`** (paper eq. (7)): the intersection of the kernels of all admissible finite
quotients of `F₄`, encoded as the intersection of all admissible open normal subgroups. -/
noncomputable def NA : Subgroup (FreeProfiniteGroup (Fin 4)) :=
  ⨅ U : {U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) // IsAdmissibleU U}, U.1.toSubgroup

instance NA_normal : NA.Normal :=
  Subgroup.normal_iInf_normal fun U => U.1.isNormal'

lemma NA_isClosed : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := by
  unfold NA
  rw [Subgroup.coe_iInf]
  exact isClosed_iInter fun U => U.1.toOpenSubgroup.isClosed

/-- **`Γ_A`** (paper §2.1, eq. (7)): the marked quotient `F₄ ⧸ N_A` — the profinite group
"topologically generated by `σ, τ, x₀, x₁`, with the closed normal subgroup generated by
`x₀, x₁` pro-2, subject to relations (5) and (6)" of Theorem 1.2, constructed exactly as in the
paper as the largest quotient of `F₄` all of whose finite quotients are admissible. -/
noncomputable def GammaA : ProfiniteGrp :=
  haveI : IsClosed (NA : Set (FreeProfiniteGroup (Fin 4))) := NA_isClosed
  profiniteQuotient NA

/-- **`N_A` is the paper's intersection** (eq. (7)): the kernel of *every* admissible continuous
hom to a finite (discrete) group — not just the canonical quotients `F₄ ⧸ U` — contains `N_A`.
(The pushed marking being admissible forces `f` surjective, and admissibility transfers to the
canonical quotient by the induced isomorphism `F₄ ⧸ ker f ≃* P`.) -/
theorem NA_le_ker {P : Type} [Group P] [TopologicalSpace P] [DiscreteTopology P] [Finite P]
    (f : ContinuousMonoidHom (FreeProfiniteGroup (Fin 4)) P)
    (hf : (univMarking.map f.toMonoidHom).Admissible) :
    NA ≤ f.toMonoidHom.ker := by
  have hsurj : Function.Surjective f := surjective_of_map_generates f.toMonoidHom hf.1
  -- the kernel, as an open normal subgroup
  have hker_open : IsOpen ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4))) := by
    have hset : ((f.toMonoidHom.ker : Subgroup _) : Set (FreeProfiniteGroup (Fin 4)))
        = f ⁻¹' {1} := by
      ext g; simp [MonoidHom.mem_ker]
    rw [hset]
    exact (isOpen_discrete ({1} : Set P)).preimage f.continuous_toFun
  let U : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) :=
    { toSubgroup := f.toMonoidHom.ker, isOpen' := hker_open }
  -- the induced isomorphism with the canonical quotient
  let e : (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) ≃* P :=
    QuotientGroup.quotientKerEquivOfSurjective f.toMonoidHom hsurj
  have hcomp : ∀ x : FreeProfiniteGroup (Fin 4),
      e.symm (f x) = QuotientGroup.mk' U.toSubgroup x := by
    intro x
    apply e.injective
    rw [MulEquiv.apply_symm_apply]
    rfl
  have hadm : IsAdmissibleU U := by
    have h1 : univMarking.map (QuotientGroup.mk' U.toSubgroup)
        = (univMarking.map f.toMonoidHom).map e.symm.toMonoidHom := by
      simp only [Marking.map]
      congr 1 <;> exact (hcomp _).symm
    show (univMarking.map (QuotientGroup.mk' U.toSubgroup)).Admissible
    rw [h1]
    haveI : Finite (FreeProfiniteGroup (Fin 4) ⧸ f.toMonoidHom.ker) :=
      Finite.of_equiv P e.symm.toEquiv
    exact Marking.map_admissible e.symm.toMonoidHom e.symm.surjective _ hf
  exact iInf_le
    (fun V : {V : OpenNormalSubgroup (FreeProfiniteGroup (Fin 4)) // IsAdmissibleU V} =>
      V.1.toSubgroup) ⟨U, hadm⟩

/-! ## Theorem 1.2, literal form -/

/-! **Theorem 1.2 (literal presentation form)** — `Γ_A ≅ G_{ℚ₂}` as topological groups, with `Γ_A`
the honest marked-quotient profinite group of paper eq. (7) defined above — is
`GQ2.main_presentation_literal`, proved in **`GQ2/PresentationLiteral.lean`** (P-19), **not here**:
its proof instantiates `Statement.main_presentation` at `Γ_A` with `hΓA := prop_2_3` (Prop. 2.3, the
`Γ_A` admissible-marking count) and `hcount := SectionTen.main_surjection_count'` (Theorem 1.2 count
form for `G_{ℚ₂}`, eq. (154) + Prop 2.3) plus the two topological finite-generation witnesses — and
`prop_2_3`/`main_surjection_count'` are **downstream** of this upstream file, so an in-place proof
would cycle (the statement-move pattern P-08/P-15d/P-18e).  It carries `sorryAx` through the
allowlisted §9 `thm_4_2` until P-17i. -/

/-! ## Sanity: a concrete admissible quotient, and `Γ_A ↠ S₃` -/

section SanityS3


end SanityS3

end GQ2
