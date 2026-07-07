import GQ2.DeepCount
import Mathlib

/-!
# Shapiro finiteness: `H¹(U, 𝔽₂)` is finite for an open subgroup `U ≤ G_ℚ₂`  (P-15f8 support)

The `[Finite (H¹(G_K, 𝔽₂))]` instance threaded through the whole deep-part counting layer
(`DeepCount`, `DimClose`, `DimAssembly`, `ResidueLift`, `AdmissibleCount`) is discharged here
from the **existing** axiom budget — no new axiom.

For `U` an *open* (hence finite-index) subgroup of `G_ℚ₂`, Shapiro's lemma identifies
`H¹(U, 𝔽₂)` with `H¹(G_ℚ₂, 𝔽₂[G/U])` where `𝔽₂[G/U] = Map(G ⧸ U, 𝔽₂)` is the finite
**coinduced/permutation module** (coinduced action `(g • f) x = f (g⁻¹ • x)`, trivial coefficient
action).  We build the Shapiro comparison map

  `θ : H¹(G_ℚ₂, 𝔽₂[G/U]) → H¹(U, 𝔽₂)`,   `θ = mapCoeff₁(ev) ∘ res₁`

(restrict to `U`, then evaluate at the base coset `⟦1⟧`), and prove it **surjective** via the
explicit Shapiro section `σ(c)(g)(x) = c(w(g,x))` built from the transversal word
`w(g,x) = sect(g⁻¹•x)⁻¹ · g⁻¹ · sect x ∈ U` — whose cocycle identity
`w(g₁g₂,x) = w(g₂, g₁⁻¹•x)·w(g₁,x)` is a pure group computation, and which collapses to `u⁻¹`
at the base coset (so the round-trip is the identity, `𝔽₂`-inversion being trivial).

Since `𝔽₂[G/U]` is finite, `H¹(G_ℚ₂, 𝔽₂[G/U])` is finite by **B7** (`finite_H1`, the local
Euler characteristic — already in the census), and the surjection transports finiteness to
`H¹(U, 𝔽₂)`.

`#print axioms finite_H1_open` = std-3 + B7 (`absGalQ2_localEulerCharacteristic`).  No `sorryAx`,
no new axiom.
-/

open GQ2 GQ2.ContCoh

namespace GQ2

/-- The finite **coinduced / permutation module** `𝔽₂[G/U]` for Shapiro's lemma: functions
`G ⧸ U → 𝔽₂` with the coinduced `G`-action `(g • f) x = f (g⁻¹ • x)`.  An instance-opaque
synonym (plain `def`) so the coinduced action is not shadowed by the global pointwise (trivial)
`Pi`-action on raw function types. -/
def PermMod (U : Subgroup AbsGalQ2) : Type := (AbsGalQ2 ⧸ U) → ZMod 2

namespace PermMod

variable {U : Subgroup AbsGalQ2}

noncomputable instance : AddCommGroup (PermMod U) :=
  inferInstanceAs (AddCommGroup ((AbsGalQ2 ⧸ U) → ZMod 2))
instance : TopologicalSpace (PermMod U) := ⊥
instance : DiscreteTopology (PermMod U) := ⟨rfl⟩
instance [Finite (AbsGalQ2 ⧸ U)] : Finite (PermMod U) :=
  inferInstanceAs (Finite ((AbsGalQ2 ⧸ U) → ZMod 2))
instance : IsTopologicalAddGroup (PermMod U) := by infer_instance

noncomputable instance : SMul AbsGalQ2 (PermMod U) :=
  ⟨fun g f => (fun x => (f : (AbsGalQ2 ⧸ U) → ZMod 2) (g⁻¹ • x))⟩

theorem smul_apply (g : AbsGalQ2) (f : PermMod U) (x : AbsGalQ2 ⧸ U) :
    (g • f) x = (f : (AbsGalQ2 ⧸ U) → ZMod 2) (g⁻¹ • x) := rfl

theorem add_apply (f₁ f₂ : PermMod U) (x : AbsGalQ2 ⧸ U) :
    (f₁ + f₂) x = f₁ x + f₂ x := rfl

noncomputable instance : DistribMulAction AbsGalQ2 (PermMod U) where
  one_smul f := by funext x; rw [smul_apply]; simp
  mul_smul g h f := by funext x; simp only [smul_apply, mul_inv_rev, mul_smul]
  smul_zero g := by funext x; rw [smul_apply]; rfl
  smul_add g f₁ f₂ := by funext x; rw [smul_apply, add_apply, add_apply, smul_apply, smul_apply]

/-- The orbit map `g ↦ g • x` on the coset space is continuous. -/
theorem continuous_orbit (x : AbsGalQ2 ⧸ U) :
    Continuous (fun g : AbsGalQ2 => g • x) := by
  induction x using QuotientGroup.induction_on with
  | H a =>
    have h : (fun g : AbsGalQ2 => g • (QuotientGroup.mk a : AbsGalQ2 ⧸ U))
        = fun g => (QuotientGroup.mk (g * a) : AbsGalQ2 ⧸ U) := by
      funext g; rfl
    rw [h]
    exact continuous_quotient_mk'.comp (continuous_mul_const a)

/-- For fixed `f`, the map `g ↦ g • f` into the discrete module is continuous. -/
theorem continuous_smul_left (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)]
    (f : PermMod U) : Continuous (fun g : AbsGalQ2 => g • f) := by
  haveI := QuotientGroup.discreteTopology hU
  refine (IsLocallyConstant.iff_isOpen_fiber.mpr (fun f₀ => ?_)).continuous
  have hset : (fun g : AbsGalQ2 => g • f) ⁻¹' {f₀}
      = ⋂ x : AbsGalQ2 ⧸ U, {g : AbsGalQ2 | (f : (AbsGalQ2 ⧸ U) → ZMod 2) (g⁻¹ • x) = f₀ x} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg x
      have := congrFun hg x
      rwa [smul_apply] at this
    · intro hg; funext x; rw [smul_apply]; exact hg x
  rw [hset]
  refine isOpen_iInter_of_finite (fun x => ?_)
  have hc : Continuous (fun g : AbsGalQ2 => (f : (AbsGalQ2 ⧸ U) → ZMod 2) (g⁻¹ • x)) :=
    (continuous_of_discreteTopology).comp ((continuous_orbit x).comp continuous_inv)
  exact hc.isOpen_preimage {f₀ x} (isOpen_discrete _)

/-- The coinduced action is (jointly) continuous. -/
theorem continuousSMul (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] :
    ContinuousSMul AbsGalQ2 (PermMod U) :=
  ⟨continuous_prod_of_discrete_right.mpr (fun f => continuous_smul_left hU f)⟩

/-- The base coset `⟦1⟧ ∈ G ⧸ U`. -/
noncomputable def basePt (U : Subgroup AbsGalQ2) : AbsGalQ2 ⧸ U := QuotientGroup.mk 1

theorem smul_base_of_mem {v : AbsGalQ2} (hv : v ∈ U) : v • (basePt U) = basePt U := by
  show (QuotientGroup.mk (v * 1) : AbsGalQ2 ⧸ U) = QuotientGroup.mk 1
  rw [mul_one]
  exact QuotientGroup.eq.mpr (by simpa using U.inv_mem hv)

/-- **Evaluation at the base coset** `f ↦ f ⟦1⟧`, a `U`-equivariant additive map to `𝔽₂`. -/
noncomputable def ev (U : Subgroup AbsGalQ2) : PermMod U →+ ZMod 2 where
  toFun f := (f : (AbsGalQ2 ⧸ U) → ZMod 2) (basePt U)
  map_zero' := rfl
  map_add' f₁ f₂ := rfl

theorem ev_continuous : Continuous (ev U) := continuous_of_discreteTopology

/-- `ev` intertwines the `U`-actions (both trivial on the base value). -/
theorem ev_compat (u : U) (n : PermMod U) : ev U (u • n) = u • ev U n := by
  have htriv : u • ev U n = ev U n := rfl
  rw [htriv]
  have h1 : (u • n : PermMod U) = (↑u : AbsGalQ2) • n := rfl
  show (((u • n : PermMod U)) : (AbsGalQ2 ⧸ U) → ZMod 2) (basePt U) = ev U n
  rw [h1, smul_apply, smul_base_of_mem (U.inv_mem u.2)]
  rfl

/-- **The Shapiro map** `θ : H¹(G, 𝔽₂[G/U]) → H¹(U, 𝔽₂)`: restrict to `U`, then evaluate at
the base coset.  We prove it *surjective*; since the source is finite (B7, `𝔽₂[G/U]` finite),
so is `H¹(U, 𝔽₂)`. -/
noncomputable def theta (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] : H1 AbsGalQ2 (PermMod U) →+ H1 U (ZMod 2) :=
  haveI := PermMod.continuousSMul hU
  (mapCoeff1 (ev U) ev_continuous (fun u n => ev_compat u n)).comp
    (res1 AbsGalQ2 (PermMod U) U)

/-- The `Z¹`-level Shapiro map underlying `theta`. -/
noncomputable def thetaZ1 (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] : Z1 AbsGalQ2 (PermMod U) →+ Z1 U (ZMod 2) :=
  haveI := PermMod.continuousSMul hU
  (Z1comap (ContinuousMonoidHom.id (↥U)) (ev U) ev_continuous (fun u n => ev_compat u n)).comp
    (Z1comap (subgroupIncl AbsGalQ2 U) (AddMonoidHom.id (PermMod U)) continuous_id (fun _ _ => rfl))

theorem theta_H1mk (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] (C : Z1 AbsGalQ2 (PermMod U)) :
    theta U hU (H1mk AbsGalQ2 (PermMod U) C) = H1mk (↥U) (ZMod 2) (thetaZ1 U hU C) := by
  haveI := PermMod.continuousSMul hU
  rfl

/-! ### The Shapiro section (surjectivity) -/

open Classical in
/-- A set-theoretic section of `G → G ⧸ U` normalized so the base coset lifts to `1`. -/
noncomputable def sect (x : AbsGalQ2 ⧸ U) : AbsGalQ2 :=
  if x = basePt U then 1 else Quotient.out x

theorem sect_mk (x : AbsGalQ2 ⧸ U) : (QuotientGroup.mk (sect x) : AbsGalQ2 ⧸ U) = x := by
  unfold sect
  split
  · rename_i h; rw [h]; rfl
  · exact QuotientGroup.out_eq' x

theorem sect_base : sect (basePt U) = 1 := by unfold sect; rw [if_pos rfl]

/-- The **Shapiro word** `w(g,x) = sect(g⁻¹•x)⁻¹ · g⁻¹ · sect x` lies in `U`. -/
theorem wElt_mem (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    (sect (g⁻¹ • x))⁻¹ * g⁻¹ * sect x ∈ U := by
  rw [mul_assoc]
  refine QuotientGroup.eq.mp ?_
  rw [sect_mk]
  show g⁻¹ • x = (QuotientGroup.mk (g⁻¹ * sect x) : AbsGalQ2 ⧸ U)
  rw [show (QuotientGroup.mk (g⁻¹ * sect x) : AbsGalQ2 ⧸ U)
      = g⁻¹ • (QuotientGroup.mk (sect x) : AbsGalQ2 ⧸ U) from rfl, sect_mk]

/-- The Shapiro word as an element of `U`. -/
noncomputable def wElt (g : AbsGalQ2) (x : AbsGalQ2 ⧸ U) : U :=
  ⟨(sect (g⁻¹ • x))⁻¹ * g⁻¹ * sect x, wElt_mem g x⟩

/-- **The cocycle identity for the Shapiro word**: `w(g₁g₂, x) = w(g₂, g₁⁻¹•x) · w(g₁, x)`. -/
theorem wElt_mul (g₁ g₂ : AbsGalQ2) (x : AbsGalQ2 ⧸ U) :
    wElt (g₁ * g₂) x = wElt g₂ (g₁⁻¹ • x) * wElt g₁ x := by
  apply Subtype.ext
  have hx : (g₁ * g₂)⁻¹ • x = g₂⁻¹ • (g₁⁻¹ • x) := by rw [mul_inv_rev, mul_smul]
  show (sect ((g₁ * g₂)⁻¹ • x))⁻¹ * (g₁ * g₂)⁻¹ * sect x
      = ((sect (g₂⁻¹ • (g₁⁻¹ • x)))⁻¹ * g₂⁻¹ * sect (g₁⁻¹ • x))
        * ((sect (g₁⁻¹ • x))⁻¹ * g₁⁻¹ * sect x)
  rw [hx]
  group

/-- The section cochain `σ(c)(g) = (x ↦ c(w(g,x)))`. -/
noncomputable def sigmaFun (c : Z1 U (ZMod 2)) : AbsGalQ2 → PermMod U :=
  fun g => (fun x => c.1 (wElt g x) : PermMod U)

theorem sigmaFun_continuous (c : Z1 U (ZMod 2)) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] : Continuous (sigmaFun c) := by
  haveI := QuotientGroup.discreteTopology hU
  refine (IsLocallyConstant.iff_isOpen_fiber.mpr (fun φ₀ => ?_)).continuous
  have hset : (sigmaFun c) ⁻¹' {φ₀}
      = ⋂ x : AbsGalQ2 ⧸ U, {g : AbsGalQ2 | c.1 (wElt g x) = φ₀ x} := by
    ext g
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_iInter, Set.mem_setOf_eq]
    constructor
    · intro hg x; exact congrFun hg x
    · intro hg; funext x; exact hg x
  rw [hset]
  refine isOpen_iInter_of_finite (fun x => ?_)
  have hcU : Continuous (fun g : AbsGalQ2 => wElt g x) := by
    apply Continuous.subtype_mk
    exact (((continuous_of_discreteTopology (f := sect)).comp
      ((PermMod.continuous_orbit x).comp continuous_inv)).inv.mul continuous_inv).mul
      continuous_const
  have hc1 : Continuous c.1 := (mem_Z1_iff.mp c.2).1
  exact (hc1.comp hcU).isOpen_preimage {φ₀ x} (isOpen_discrete _)

theorem sigmaFun_mem (c : Z1 U (ZMod 2)) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] : sigmaFun c ∈ Z1 AbsGalQ2 (PermMod U) := by
  rw [mem_Z1_iff]
  refine ⟨sigmaFun_continuous c hU, fun g₁ g₂ => ?_⟩
  funext x
  have hcyc := (mem_Z1_iff.mp c.2).2
  show c.1 (wElt (g₁ * g₂) x) = (sigmaFun c g₁ + g₁ • sigmaFun c g₂) x
  rw [PermMod.add_apply, PermMod.smul_apply, wElt_mul, hcyc]
  show c.1 (wElt g₂ (g₁⁻¹ • x)) + _ • c.1 (wElt g₁ x)
      = c.1 (wElt g₁ x) + c.1 (wElt g₂ (g₁⁻¹ • x))
  rw [show (wElt g₂ (g₁⁻¹ • x) : U) • c.1 (wElt g₁ x) = c.1 (wElt g₁ x) from rfl, add_comm]

/-- **The Shapiro round-trip on the base coset**: `c(w(u, ⟦1⟧)) = c(u)`.  The word collapses
to `u⁻¹` (since `sect ⟦1⟧ = 1`), and `𝔽₂`-inversion is the identity. -/
theorem sigma_eval (c : Z1 U (ZMod 2)) (u : U) :
    c.1 (wElt (↑u) (basePt U)) = c.1 u := by
  have hw : wElt (↑u) (basePt U) = u⁻¹ := by
    apply Subtype.ext
    show (sect (((u : AbsGalQ2))⁻¹ • basePt U))⁻¹ * ((u : AbsGalQ2))⁻¹ * sect (basePt U)
        = ((u : AbsGalQ2))⁻¹
    rw [smul_base_of_mem (U.inv_mem u.2)]
    simp only [sect_base]
    group
  rw [hw, Z1_apply_inv c u]
  have htriv : (u⁻¹ : U) • c.1 u = c.1 u := rfl
  rw [htriv]
  have hneg : ∀ y : ZMod 2, -y = y := by decide
  exact hneg _

/-- **Shapiro surjectivity.** -/
theorem theta_surjective (hU : IsOpen (U : Set AbsGalQ2)) [Finite (AbsGalQ2 ⧸ U)] :
    Function.Surjective (theta U hU) := by
  haveI := PermMod.continuousSMul hU
  intro ξ
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ ξ
  refine ⟨H1mk AbsGalQ2 (PermMod U) ⟨sigmaFun c, sigmaFun_mem c hU⟩, ?_⟩
  rw [theta_H1mk]
  show H1mk (↥U) (ZMod 2) (thetaZ1 U hU ⟨sigmaFun c, sigmaFun_mem c hU⟩) = H1mk (↥U) (ZMod 2) c
  congr 1
  apply Subtype.ext
  funext u
  show c.1 (wElt (↑u) (basePt U)) = c.1 u
  exact sigma_eval c u

end PermMod

/-- **Finiteness of `H¹(U, 𝔽₂)` for an open subgroup `U ≤ G_ℚ₂`** — Shapiro's lemma reduces it
to `H¹(G_ℚ₂, 𝔽₂[G/U])`, finite by B7.  Discharges the `[Finite (H¹(G_K, 𝔽₂))]` instance threaded
through the deep-part counting layer.  No new axiom (std-3 + B7). -/
theorem finite_H1_open (U : Subgroup AbsGalQ2) (hU : IsOpen (U : Set AbsGalQ2))
    [Finite (AbsGalQ2 ⧸ U)] : Finite (H1 U (ZMod 2)) := by
  haveI := PermMod.continuousSMul hU
  haveI : Finite (H1 AbsGalQ2 (PermMod U)) := GQ2.Foundations.finite_H1 (PermMod U)
  exact Finite.of_surjective (PermMod.theta U hU) (PermMod.theta_surjective hU)

end GQ2
