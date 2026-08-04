/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/
import GQ2.Dyadic.Count.H2MaxProTwoRightExactTransport

/-!
# H² inflation injectivity for finite elementary quotient modules

The scalar proof in `MaxProPCohomology` uses the central extension classified by a normalized
`ZMod 2`-valued cocycle.  The same argument works for a nontrivial finite elementary module
after replacing the central extension by its twisted analogue

`(q,a) * (r,b) = (qr, a + q • b + κ(q,r))`.

The twisted extension is still pro-`2`: modulo an open normal subgroup, first raise an element
until its base component lies in the chosen subgroup, and then square once more to kill the
elementary fiber.  The maximal pro-`2` universal property therefore descends a splitting of an
inflated cocycle, proving injectivity for every finite elementary quotient module.
-/

namespace GQ2

open ContCoh

namespace MaxProPH2TwistedInflation

noncomputable section

variable {Q M : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction Q M] [ContinuousSMul Q M]

/-- A continuous normalized two-cocycle with values in a possibly nontrivial module. -/
structure NormCocycle where
  kappa : Q → Q → M
  continuous_kappa : Continuous (fun p : Q × Q ↦ kappa p.1 p.2)
  one_left : ∀ q, kappa 1 q = 0
  one_right : ∀ q, kappa q 1 = 0
  cocyc : ∀ q r s,
    q • kappa r s + kappa q (r * s) = kappa (q * r) s + kappa q r

/-- Subtracting the coboundary of the constant `z(1,1)` normalizes a two-cocycle. -/
def normalize (z : Z2 Q M) : NormCocycle (Q := Q) (M := M) where
  kappa q r := z.1 (q, r) - q • z.1 (1, 1)
  continuous_kappa :=
    (mem_Z2_iff.mp z.2).1.sub (continuous_fst.smul continuous_const)
  one_left := by
    intro q
    have h := (mem_Z2_iff.mp z.2).2 1 1 q
    have hz : z.1 (1, q) = z.1 (1, 1) := by
      simp only [one_smul, one_mul] at h
      exact add_left_cancel h
    simp [hz]
  one_right := by
    intro q
    have h := (mem_Z2_iff.mp z.2).2 q 1 1
    have hz : z.1 (q, 1) = q • z.1 (1, 1) := by
      simp only [mul_one] at h
      exact (add_right_cancel h).symm
    simp [hz]
  cocyc := by
    intro q r s
    have h := (mem_Z2_iff.mp z.2).2 q r s
    change
      q • (z.1 (r, s) - r • z.1 (1, 1)) +
          (z.1 (q, r * s) - q • z.1 (1, 1)) =
        (z.1 (q * r, s) - (q * r) • z.1 (1, 1)) +
          (z.1 (q, r) - q • z.1 (1, 1))
    rw [smul_sub, mul_smul]
    calc
      q • z.1 (r, s) - q • r • z.1 (1, 1) +
            (z.1 (q, r * s) - q • z.1 (1, 1)) =
          (q • z.1 (r, s) + z.1 (q, r * s)) -
            (q • r • z.1 (1, 1) + q • z.1 (1, 1)) := by abel
      _ = (z.1 (q * r, s) + z.1 (q, r)) -
            (q • r • z.1 (1, 1) + q • z.1 (1, 1)) :=
        congrArg (fun t ↦ t -
          (q • r • z.1 (1, 1) + q • z.1 (1, 1))) h
      _ = z.1 (q * r, s) - q • r • z.1 (1, 1) +
            (z.1 (q, r) - q • z.1 (1, 1)) := by abel

/-- The topological group extension classified by a normalized module-valued cocycle. -/
def TwistedExt (_c : NormCocycle (Q := Q) (M := M)) := Q × M

namespace TwistedExt

variable {c : NormCocycle (Q := Q) (M := M)}

def base (x : TwistedExt c) : Q := x.1
def fib (x : TwistedExt c) : M := x.2

@[ext] theorem ext {x y : TwistedExt c} (hbase : base x = base y)
    (hfib : fib x = fib y) : x = y :=
  Prod.ext hbase hfib

private theorem inverse_cocycle (q : Q) :
    c.kappa q⁻¹ q = q⁻¹ • c.kappa q q⁻¹ := by
  have h := c.cocyc q⁻¹ q q⁻¹
  simpa [c.one_left, c.one_right] using h.symm

instance : Group (TwistedExt c) where
  mul x y := (x.1 * y.1, x.2 + x.1 • y.2 + c.kappa x.1 y.1)
  one := (1, 0)
  inv x := (x.1⁻¹, -(x.1⁻¹ • (x.2 + c.kappa x.1 x.1⁻¹)))
  mul_assoc x y z := by
    apply Prod.ext
    · exact mul_assoc _ _ _
    · change
        (x.2 + x.1 • y.2 + c.kappa x.1 y.1) + (x.1 * y.1) • z.2 +
            c.kappa (x.1 * y.1) z.1 =
          x.2 + x.1 • (y.2 + y.1 • z.2 + c.kappa y.1 z.1) +
            c.kappa x.1 (y.1 * z.1)
      have hc := c.cocyc x.1 y.1 z.1
      rw [smul_add, smul_add, mul_smul]
      have hkc : c.kappa x.1 y.1 + c.kappa (x.1 * y.1) z.1 =
          x.1 • c.kappa y.1 z.1 + c.kappa x.1 (y.1 * z.1) := by
        rw [hc]
        abel
      calc
        x.2 + x.1 • y.2 + c.kappa x.1 y.1 + x.1 • y.1 • z.2 +
              c.kappa (x.1 * y.1) z.1 =
            x.2 + x.1 • y.2 + x.1 • y.1 • z.2 +
              (c.kappa x.1 y.1 + c.kappa (x.1 * y.1) z.1) := by abel
        _ = x.2 + x.1 • y.2 + x.1 • y.1 • z.2 +
              (x.1 • c.kappa y.1 z.1 + c.kappa x.1 (y.1 * z.1)) :=
          congrArg (fun t : M ↦ x.2 + x.1 • y.2 + x.1 • y.1 • z.2 + t) hkc
        _ = x.2 + (x.1 • y.2 + x.1 • y.1 • z.2 + x.1 • c.kappa y.1 z.1) +
              c.kappa x.1 (y.1 * z.1) := by abel
  one_mul x := by
    apply Prod.ext
    · exact one_mul _
    · change 0 + 1 • x.2 + c.kappa 1 x.1 = x.2
      simp [c.one_left]
  mul_one x := by
    apply Prod.ext
    · exact mul_one _
    · change x.2 + x.1 • 0 + c.kappa x.1 1 = x.2
      simp [c.one_right]
  inv_mul_cancel x := by
    apply Prod.ext
    · exact inv_mul_cancel _
    · change
        -(x.1⁻¹ • (x.2 + c.kappa x.1 x.1⁻¹)) + x.1⁻¹ • x.2 +
            c.kappa x.1⁻¹ x.1 = 0
      rw [inverse_cocycle, smul_add]
      abel

instance : TopologicalSpace (TwistedExt c) :=
  inferInstanceAs (TopologicalSpace (Q × M))
instance [CompactSpace Q] [Finite M] [DiscreteTopology M] : CompactSpace (TwistedExt c) :=
  inferInstanceAs (CompactSpace (Q × M))
instance [T2Space Q] [DiscreteTopology M] : T2Space (TwistedExt c) :=
  inferInstanceAs (T2Space (Q × M))
instance [TotallyDisconnectedSpace Q] [DiscreteTopology M] :
    TotallyDisconnectedSpace (TwistedExt c) :=
  inferInstanceAs (TotallyDisconnectedSpace (Q × M))

@[simp] theorem mul_base (x y : TwistedExt c) : base (x * y) = base x * base y := rfl
@[simp] theorem mul_fib (x y : TwistedExt c) :
    fib (x * y) = fib x + base x • fib y + c.kappa (base x) (base y) := rfl
@[simp] theorem one_base : base (1 : TwistedExt c) = 1 := rfl
@[simp] theorem one_fib : fib (1 : TwistedExt c) = 0 := rfl
@[simp] theorem inv_base (x : TwistedExt c) : base x⁻¹ = (base x)⁻¹ := rfl
@[simp] theorem inv_fib (x : TwistedExt c) :
    fib x⁻¹ = -((base x)⁻¹ • (fib x + c.kappa (base x) (base x)⁻¹)) := rfl

theorem continuous_base : Continuous (base : TwistedExt c → Q) := continuous_fst
theorem continuous_fib : Continuous (fib : TwistedExt c → M) := continuous_snd

instance : IsTopologicalGroup (TwistedExt c) where
  continuous_mul := by
    apply Continuous.prodMk
    · exact (continuous_base.comp continuous_fst).mul (continuous_base.comp continuous_snd)
    · exact ((continuous_fib.comp continuous_fst).add
        ((continuous_base.comp continuous_fst).smul
          (continuous_fib.comp continuous_snd))).add
        (c.continuous_kappa.comp
          ((continuous_base.comp continuous_fst).prodMk
            (continuous_base.comp continuous_snd)))
  continuous_inv := by
    apply Continuous.prodMk
    · exact continuous_base.inv
    · exact (continuous_base.inv.smul
        (continuous_fib.add
          (c.continuous_kappa.comp (continuous_base.prodMk continuous_base.inv)))).neg

def proj (c : NormCocycle (Q := Q) (M := M)) : ContinuousMonoidHom (TwistedExt c) Q where
  toFun := base
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_base

def incl (c : NormCocycle (Q := Q) (M := M)) (a : M) : TwistedExt c := (1, a)

@[simp] theorem incl_base (a : M) : base (incl c a) = 1 := rfl
@[simp] theorem incl_fib (a : M) : fib (incl c a) = a := rfl
@[simp] theorem incl_zero : incl c 0 = 1 := rfl

theorem incl_mul_self (hM : ∀ a : M, a + a = 0) (a : M) :
    incl c a * incl c a = 1 := by
  apply ext
  · simp
  · change a + 1 • a + c.kappa 1 1 = 0
    simpa [c.one_left] using hM a

theorem pow_base (x : TwistedExt c) (n : ℕ) : base (x ^ n) = base x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- An extension of a pro-`2` group by a finite elementary module is pro-`2`, even when the
action and cocycle are nontrivial. -/
theorem isProP (hQ : IsProP 2 Q) (hM : ∀ a : M, a + a = 0)
    [CompactSpace Q] [T2Space Q] [TotallyDisconnectedSpace Q]
    [Finite M] [DiscreteTopology M] : IsProP 2 (TwistedExt c) := by
  intro W
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  let s : Q → TwistedExt c := fun q ↦ (q, 0)
  have hs : Continuous s := continuous_id.prodMk continuous_const
  have hOopen : IsOpen (s ⁻¹' (W.toSubgroup : Set (TwistedExt c))) :=
    W.toOpenSubgroup.isOpen.preimage hs
  have h1O : (1 : Q) ∈ s ⁻¹' (W.toSubgroup : Set (TwistedExt c)) := by
    exact W.one_mem
  obtain ⟨V, hVO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  obtain ⟨n, hn⟩ := hQ V
    (QuotientGroup.mk' V.toSubgroup (base x))
  refine ⟨n + 1, ?_⟩
  have hbase_mem : base x ^ 2 ^ n ∈ V.toSubgroup :=
    (QuotientGroup.eq_one_iff _).mp hn
  have hsW : s (base x ^ 2 ^ n) ∈ W.toSubgroup := hVO hbase_mem
  let b : Q := base x ^ 2 ^ n
  let a : M := b⁻¹ • fib (x ^ 2 ^ n)
  have hdecomp : x ^ 2 ^ n = s b * incl c a := by
    apply Prod.ext
    · change (x ^ 2 ^ n).1 = b * 1
      rw [mul_one]
      exact pow_base x (2 ^ n)
    · change fib (x ^ 2 ^ n) = 0 + b • a + c.kappa b 1
      simp [a, c.one_right]
  let mkW : TwistedExt c →* (TwistedExt c ⧸ W.toSubgroup) :=
    QuotientGroup.mk' W.toSubgroup
  have hy : mkW (x ^ 2 ^ n) = mkW (incl c a) := by
    have hy' := congrArg mkW hdecomp
    rw [map_mul, show mkW (s b) = 1 from
      (QuotientGroup.eq_one_iff _).mpr hsW, one_mul] at hy'
    exact hy'
  have hi : (incl c a) ^ 2 = 1 := by
    rw [pow_two, incl_mul_self hM]
  calc
    mkW x ^ 2 ^ (n + 1) = (mkW x ^ 2 ^ n) ^ 2 := by rw [pow_succ, pow_mul]
    _ = (mkW (x ^ 2 ^ n)) ^ 2 := by rw [map_pow]
    _ = (mkW (incl c a)) ^ 2 := congrArg (fun y ↦ y ^ 2) hy
    _ = mkW ((incl c a) ^ 2) := (map_pow mkW _ 2).symm
    _ = 1 := by rw [hi, map_one]

end TwistedExt

end

end MaxProPH2TwistedInflation

namespace ContCoh

noncomputable section

/-! ## Uniform injectivity -/

section DegreeTwoInflation

variable {G M : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
  [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DiscreteTopology M] [Finite M]
  [DistribMulAction G M] [ContinuousSMul G M]
  [DistribMulAction (maxProPQuotient 2 G) M]
  [ContinuousSMul (maxProPQuotient 2 G) M]

/-- Degree-two inflation from the maximal pro-`2` quotient is injective for every finite
elementary quotient module, including nontrivial actions. -/
theorem injective_inf2_maxProPMk_finiteElementary
    (hM : ∀ a : M, a + a = 0)
    (hcompat : ∀ (g : G) (a : M), maxProPMk 2 G g • a = g • a) :
    Function.Injective (inf2 (maxProPMk 2 G) hcompat) := by
  let pi := maxProPMk 2 G
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := maxProPQuotient 2 G) (M := M) x
  have hx' : H2mk G M
      (Z2comap pi (AddMonoidHom.id M) continuous_id hcompat z) = 0 := by
    simpa [pi] using hx
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hx'
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨psi, hpsi_cont, hpsi⟩ := hmem
  have hcob (g h : G) :
      g • psi h - psi (g * h) + psi g = z.1 (pi g, pi h) := by
    simpa [dOne, Z2comap] using congrFun hpsi (g, h)
  let c : MaxProPH2TwistedInflation.NormCocycle :=
    MaxProPH2TwistedInflation.normalize z
  let psi0 : G → M := fun g ↦ psi g - z.1 (1, 1)
  have hpsi_one : psi 1 = z.1 (1, 1) := by
    simpa using hcob 1 1
  have hpsi0_one : psi0 1 = 0 := by
    simp [psi0, hpsi_one]
  have hcob0 (g h : G) :
      c.kappa (pi g) (pi h) = g • psi0 h - psi0 (g * h) + psi0 g := by
    have hraw := hcob g h
    dsimp [c, MaxProPH2TwistedInflation.normalize, psi0]
    rw [hcompat]
    rw [← hraw, smul_sub]
    abel
  let f : ContinuousMonoidHom G (MaxProPH2TwistedInflation.TwistedExt c) :=
    { toFun := fun g ↦ (pi g, -(psi0 g))
      map_one' := by
        apply Prod.ext
        · exact map_one pi
        · change -(psi0 1) = 0
          rw [hpsi0_one]
          simp
      map_mul' := fun g h ↦ by
        apply Prod.ext
        · exact map_mul pi g h
        · change -(psi0 (g * h)) =
            -(psi0 g) + pi g • (-(psi0 h)) + c.kappa (pi g) (pi h)
          rw [hcob0, smul_neg, hcompat]
          abel
      continuous_toFun := pi.continuous_toFun.prodMk
        ((hpsi_cont.sub continuous_const).neg) }
  have hExt : IsProP 2 (MaxProPH2TwistedInflation.TwistedExt c) :=
    MaxProPH2TwistedInflation.TwistedExt.isProP isProP_maxProPQuotient hM
  let fbar : ContinuousMonoidHom (maxProPQuotient 2 G)
      (MaxProPH2TwistedInflation.TwistedExt c) :=
    (maxProPHomEquiv hExt).symm f
  have hfactor (g : G) : fbar (pi g) = f g :=
    DFunLike.congr_fun ((maxProPHomEquiv hExt).apply_symm_apply f) g
  have hbase (q : maxProPQuotient 2 G) :
      MaxProPH2TwistedInflation.TwistedExt.base (fbar q) = q := by
    obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 G) q
    change MaxProPH2TwistedInflation.TwistedExt.base (fbar (pi g)) = pi g
    have h := congrArg MaxProPH2TwistedInflation.TwistedExt.base (hfactor g)
    change MaxProPH2TwistedInflation.TwistedExt.base (fbar (pi g)) = pi g at h
    exact h
  let lam : maxProPQuotient 2 G → M := fun q ↦
    -(MaxProPH2TwistedInflation.TwistedExt.fib (fbar q)) + z.1 (1, 1)
  have hlam_cont : Continuous lam :=
    (MaxProPH2TwistedInflation.TwistedExt.continuous_fib.comp
      fbar.continuous_toFun).neg.add continuous_const
  have hfib_mul (q r : maxProPQuotient 2 G) :
      MaxProPH2TwistedInflation.TwistedExt.fib (fbar (q * r)) =
        MaxProPH2TwistedInflation.TwistedExt.fib (fbar q) +
          q • MaxProPH2TwistedInflation.TwistedExt.fib (fbar r) + c.kappa q r := by
    have h := congrArg MaxProPH2TwistedInflation.TwistedExt.fib (map_mul fbar q r)
    simpa [hbase] using h
  have hlam : dOne (maxProPQuotient 2 G) M lam = z.1 := by
    funext p
    change p.1 • lam p.2 - lam (p.1 * p.2) + lam p.1 = z.1 p
    dsimp [lam]
    rw [smul_add, smul_neg, hfib_mul]
    dsimp [c, MaxProPH2TwistedInflation.normalize]
    abel
  apply (QuotientAddGroup.eq_zero_iff z).mpr
  apply AddSubgroup.mem_addSubgroupOf.mpr
  exact ⟨lam, hlam_cont, hlam⟩

end DegreeTwoInflation

/-- The maximal pro-`2` quotient has the full uniform finite-elementary H² inflation
injectivity supply. -/
theorem finiteElementaryH2InflationInjective_maxProPMk
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G] :
    FiniteElementaryH2InflationInjective (maxProPMk 2 G) := by
  intro M _ _ _ _ _ _ _ _ _ hM hcompat
  exact injective_inf2_maxProPMk_finiteElementary hM hcompat

/-- For maximal pro-`2` inflation, the existing finite-elementary surjectivity supply is already
the full bijectivity supply: injectivity is automatic by the twisted-extension argument. -/
theorem finiteElementaryH2InflationBijective_maxProPMk_of_surjective
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hsurj : FiniteElementaryH2InflationSurjective (maxProPMk 2 G)) :
    FiniteElementaryH2InflationBijective (maxProPMk 2 G) := by
  intro M _ _ _ _ _ _ _ _ _ hM hcompat
  exact ⟨finiteElementaryH2InflationInjective_maxProPMk M hM hcompat,
    hsurj M hM hcompat⟩

/-- Thus a right-exactness supply on `G` descends to `G(2)` from the finite-elementary
surjectivity comparison alone. -/
theorem finiteElementaryH2RightExactSupply_maxProPQuotient_of_inflation_surjective
    {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : FiniteElementaryH2RightExactSupply G)
    (hsurj : FiniteElementaryH2InflationSurjective (maxProPMk 2 G)) :
    FiniteElementaryH2RightExactSupply (maxProPQuotient 2 G) :=
  finiteElementaryH2RightExactSupply_maxProPQuotient_of_inflation_surjective_injective
    hG hsurj finiteElementaryH2InflationInjective_maxProPMk

#print axioms injective_inf2_maxProPMk_finiteElementary
#print axioms finiteElementaryH2InflationInjective_maxProPMk
#print axioms finiteElementaryH2RightExactSupply_maxProPQuotient_of_inflation_surjective

end

end ContCoh

end GQ2
