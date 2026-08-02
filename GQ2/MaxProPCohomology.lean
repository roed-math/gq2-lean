/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using Codex GPT-5
-/
module

public import GQ2.Cohomology
public import GQ2.MaxProP

@[expose] public section

/-!
# Degree-one cohomology of a maximal pro-`p` quotient

For a trivial coefficient module `M`, continuous `1`-cocycles are exactly continuous
homomorphisms to `Multiplicative M`.  If that target is pro-`p`, the universal property of
`maxProPQuotient p G` therefore says that pullback along `maxProPMk p G` is an equivalence on
`Z¹`, and hence on `H¹` because trivial action also makes `B¹ = 0`.

The final computation theorem records that the resulting `H¹` equivalence is not merely an
abstract cardinality comparison: its forward map is the existing inflation map `inf1`.

In degree two, the file proves the standard injectivity of inflation for trivial `ZMod 2`
coefficients.  Its proof represents a normalized cocycle by a continuous central extension,
proves that the extension of a pro-2 group by `ZMod 2` is again pro-2, and then uses the same
universal property to descend a splitting.
-/

namespace GQ2

open ContCoh

/-! ## A continuous central-extension model for degree-two inflation

The injectivity of degree-two inflation is proved below by the standard extension argument.  The
auxiliary normalized cocycle and its central extension live in a dedicated namespace; the main
public output is the cohomological theorem rather than a second competing central-extension API.
-/

namespace MaxProPH2Inflation

variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]

/-- A continuous normalized `ZMod 2`-valued two-cocycle. -/
structure NormZ2 where
  kappa : Q → Q → ZMod 2
  continuous_kappa : Continuous (fun p : Q × Q => kappa p.1 p.2)
  norm : kappa 1 1 = 0
  cocyc : ∀ a b c, kappa a b + kappa (a * b) c = kappa a (b * c) + kappa b c

namespace NormZ2

variable (c : NormZ2 (Q := Q))

theorem one_left (q : Q) : c.kappa 1 q = 0 := by
  simpa [c.norm] using c.cocyc 1 1 q

theorem one_right (q : Q) : c.kappa q 1 = 0 := by
  simpa [c.norm] using c.cocyc q 1 1

theorem inv_eq (q : Q) : c.kappa q q⁻¹ = c.kappa q⁻¹ q := by
  simpa [c.one_left, c.one_right] using c.cocyc q q⁻¹ q

end NormZ2

/-- The central extension `Q ×_κ ZMod 2` with its product topology. -/
def CentExt (_c : NormZ2 (Q := Q)) := Q × ZMod 2

namespace CentExt

variable {c : NormZ2 (Q := Q)}

def base (x : CentExt c) : Q := x.1
def fib (x : CentExt c) : ZMod 2 := x.2

@[ext] theorem ext {x y : CentExt c} (hbase : base x = base y)
    (hfib : fib x = fib y) : x = y :=
  Prod.ext hbase hfib

instance : Group (CentExt c) where
  mul x y := (x.1 * y.1, x.2 + y.2 + c.kappa x.1 y.1)
  one := (1, 0)
  inv x := (x.1⁻¹, x.2 + c.kappa x.1 x.1⁻¹)
  mul_assoc x y z := by
    apply Prod.ext
    · exact mul_assoc _ _ _
    · show x.2 + y.2 + c.kappa x.1 y.1 + z.2 + c.kappa (x.1 * y.1) z.1 =
        x.2 + (y.2 + z.2 + c.kappa y.1 z.1) + c.kappa x.1 (y.1 * z.1)
      calc
        _ = x.2 + y.2 + z.2 +
            (c.kappa x.1 y.1 + c.kappa (x.1 * y.1) z.1) := by abel
        _ = x.2 + y.2 + z.2 +
            (c.kappa x.1 (y.1 * z.1) + c.kappa y.1 z.1) := by
              rw [c.cocyc]
        _ = _ := by abel
  one_mul x := by
    apply Prod.ext
    · exact one_mul _
    · show (0 : ZMod 2) + x.2 + c.kappa 1 x.1 = x.2
      rw [c.one_left]
      abel
  mul_one x := by
    apply Prod.ext
    · exact mul_one _
    · show x.2 + 0 + c.kappa x.1 1 = x.2
      rw [c.one_right]
      abel
  inv_mul_cancel x := by
    apply Prod.ext
    · exact inv_mul_cancel _
    · show x.2 + c.kappa x.1 x.1⁻¹ + x.2 + c.kappa x.1⁻¹ x.1 = 0
      rw [c.inv_eq]
      exact (by decide : ∀ a b : ZMod 2, a + b + a + b = 0) _ _

instance : TopologicalSpace (CentExt c) :=
  inferInstanceAs (TopologicalSpace (Q × ZMod 2))
instance [CompactSpace Q] : CompactSpace (CentExt c) :=
  inferInstanceAs (CompactSpace (Q × ZMod 2))
instance [T2Space Q] : T2Space (CentExt c) :=
  inferInstanceAs (T2Space (Q × ZMod 2))
instance [TotallyDisconnectedSpace Q] : TotallyDisconnectedSpace (CentExt c) :=
  inferInstanceAs (TotallyDisconnectedSpace (Q × ZMod 2))

@[simp] theorem mul_base (x y : CentExt c) : base (x * y) = base x * base y := rfl
@[simp] theorem mul_fib (x y : CentExt c) :
    fib (x * y) = fib x + fib y + c.kappa (base x) (base y) := rfl
@[simp] theorem one_base : base (1 : CentExt c) = 1 := rfl
@[simp] theorem one_fib : fib (1 : CentExt c) = 0 := rfl
@[simp] theorem inv_base (x : CentExt c) : base x⁻¹ = (base x)⁻¹ := rfl
@[simp] theorem inv_fib (x : CentExt c) :
    fib x⁻¹ = fib x + c.kappa (base x) (base x)⁻¹ := rfl

theorem continuous_base : Continuous (base : CentExt c → Q) := continuous_fst
theorem continuous_fib : Continuous (fib : CentExt c → ZMod 2) := continuous_snd

instance : IsTopologicalGroup (CentExt c) where
  continuous_mul := by
    apply Continuous.prodMk
    · exact (continuous_base.comp continuous_fst).mul (continuous_base.comp continuous_snd)
    · exact ((continuous_fib.comp continuous_fst).add (continuous_fib.comp continuous_snd)).add
        (c.continuous_kappa.comp
          ((continuous_base.comp continuous_fst).prodMk (continuous_base.comp continuous_snd)))
  continuous_inv := by
    apply Continuous.prodMk
    · exact continuous_base.inv
    · exact continuous_fib.add
        (c.continuous_kappa.comp (continuous_base.prodMk continuous_base.inv))

def proj (c : NormZ2 (Q := Q)) : ContinuousMonoidHom (CentExt c) Q where
  toFun := base
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_base

def incl (c : NormZ2 (Q := Q)) (a : ZMod 2) : CentExt c := (1, a)

@[simp] theorem incl_base (a : ZMod 2) : base (incl c a) = 1 := rfl
@[simp] theorem incl_fib (a : ZMod 2) : fib (incl c a) = a := rfl
@[simp] theorem incl_zero : incl c 0 = 1 := rfl

theorem incl_mul_self (a : ZMod 2) : incl c a * incl c a = 1 := by
  apply ext
  · simp
  · simp [c.norm, CharTwo.add_self_eq_zero]

theorem pow_base (x : CentExt c) (n : ℕ) : base (x ^ n) = base x ^ n := by
  induction n with
  | zero => simp
  | succ n ih => simp [pow_succ, ih]

/-- A central extension of a pro-2 profinite group by `ZMod 2` is again pro-2. -/
theorem isProP (hQ : IsProP 2 Q) [CompactSpace Q] [T2Space Q]
    [TotallyDisconnectedSpace Q] : IsProP 2 (CentExt c) := by
  intro W
  intro x
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective x
  let s : Q → CentExt c := fun q => (q, 0)
  have hs : Continuous s := continuous_id.prodMk continuous_const
  have hOopen : IsOpen (s ⁻¹' (W.toSubgroup : Set (CentExt c))) :=
    W.toOpenSubgroup.isOpen.preimage hs
  have h1O : (1 : Q) ∈ s ⁻¹' (W.toSubgroup : Set (CentExt c)) := by
    exact W.one_mem
  obtain ⟨V, hVO⟩ :=
    ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hOopen h1O
  obtain ⟨n, hn⟩ := hQ V
    (QuotientGroup.mk' V.toSubgroup (base (c := c) x))
  refine ⟨n + 1, ?_⟩
  have hbase : base x ^ 2 ^ n ∈ V.toSubgroup :=
    (QuotientGroup.eq_one_iff _).mp hn
  have hsW : s (base x ^ 2 ^ n) ∈ W.toSubgroup := hVO hbase
  have hdecomp : x ^ 2 ^ n = s (base x ^ 2 ^ n) * incl c (fib (x ^ 2 ^ n)) := by
    apply Prod.ext
    · change (x ^ 2 ^ n).1 = (base x ^ 2 ^ n) * 1
      rw [mul_one]
      exact pow_base x (2 ^ n)
    · change (x ^ 2 ^ n).2 =
        0 + (x ^ 2 ^ n).2 + c.kappa (base x ^ 2 ^ n) 1
      rw [c.one_right]
      abel
  let mkW : CentExt c →* (CentExt c ⧸ W.toSubgroup) :=
    QuotientGroup.mk' W.toSubgroup
  have hy : mkW (x ^ 2 ^ n) = mkW (incl c (fib (x ^ 2 ^ n))) := by
    have hy' := congrArg mkW hdecomp
    rw [map_mul, show mkW (s (base x ^ 2 ^ n)) = 1 from
      (QuotientGroup.eq_one_iff _).mpr hsW, one_mul] at hy'
    exact hy'
  have hi : (incl c (fib (x ^ 2 ^ n))) ^ 2 = 1 := by
    rw [pow_two, incl_mul_self]
  calc
    mkW x ^ 2 ^ (n + 1) = (mkW x ^ 2 ^ n) ^ 2 := by rw [pow_succ, pow_mul]
    _ = (mkW (x ^ 2 ^ n)) ^ 2 := by rw [map_pow]
    _ = (mkW (incl c (fib (x ^ 2 ^ n)))) ^ 2 := congrArg (fun y => y ^ 2) hy
    _ = mkW ((incl c (fib (x ^ 2 ^ n))) ^ 2) := (map_pow mkW _ 2).symm
    _ = 1 := by rw [hi, map_one]

end CentExt

variable [DistribMulAction Q (ZMod 2)] [ContinuousSMul Q (ZMod 2)]

/-- Subtracting the constant value at `(1,1)` normalizes a continuous two-cocycle. -/
def normalize (htriv : ∀ (q : Q) (a : ZMod 2), q • a = a) (z : Z2 Q (ZMod 2)) :
    NormZ2 (Q := Q) where
  kappa q r := z.1 (q, r) - z.1 (1, 1)
  continuous_kappa :=
    (mem_Z2_iff.mp z.2).1.sub continuous_const
  norm := sub_self _
  cocyc a b d := by
    have h := (mem_Z2_iff.mp z.2).2 a b d
    rw [htriv] at h
    have hraw : z.1 (a, b) + z.1 (a * b, d) =
        z.1 (a, b * d) + z.1 (b, d) := by
      simpa only [add_comm] using h.symm
    calc
      (z.1 (a, b) - z.1 (1, 1)) + (z.1 (a * b, d) - z.1 (1, 1)) =
          (z.1 (a, b) + z.1 (a * b, d)) - z.1 (1, 1) - z.1 (1, 1) := by abel
      _ = (z.1 (a, b * d) + z.1 (b, d)) - z.1 (1, 1) - z.1 (1, 1) := by
        rw [hraw]
      _ = (z.1 (a, b * d) - z.1 (1, 1)) + (z.1 (b, d) - z.1 (1, 1)) := by abel

end MaxProPH2Inflation

namespace ContCoh

section InflationComputations

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {Q : Type*} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [DistribMulAction G M] [ContinuousSMul G M] [DistribMulAction Q M] [ContinuousSMul Q M]
variable (pi : ContinuousMonoidHom G Q) (hpi : ∀ (g : G) (m : M), pi g • m = g • m)

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] [ContinuousSMul G M] [ContinuousSMul Q M] in
/-- Inflation in degree one computes by cocycle pullback on a represented class. -/
@[simp] theorem inf1_H1mk (z : Z1 Q M) :
    inf1 pi hpi (H1mk Q M z) =
      H1mk G M (Z1comap pi (AddMonoidHom.id M) continuous_id hpi z) :=
  rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] [ContinuousSMul G M] [ContinuousSMul Q M] in
/-- Inflation in degree two computes by cocycle pullback on a represented class. -/
@[simp] theorem inf2_H2mk (z : Z2 Q M) :
    inf2 pi hpi (H2mk Q M z) =
      H2mk G M (Z2comap pi (AddMonoidHom.id M) continuous_id hpi z) :=
  rfl

end InflationComputations

end ContCoh

section TrivialCoefficients

variable {p : ℕ}
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G]
variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
  [CompactSpace M] [T2Space M] [TotallyDisconnectedSpace M]
variable [DistribMulAction G M] [ContinuousSMul G M]
variable [DistribMulAction (maxProPQuotient p G) M]
  [ContinuousSMul (maxProPQuotient p G) M]

/-- A continuous `1`-cocycle for a trivial action, regarded as a continuous character into the
multiplicative copy of its additive coefficient group. -/
private def z1ToContinuousCharOfTrivial (htriv : ∀ (g : G) (m : M), g • m = m)
    (z : Z1 G M) : ContinuousMonoidHom G (Multiplicative M) where
  toFun g := Multiplicative.ofAdd (z.1 g)
  map_one' := congrArg Multiplicative.ofAdd (Z1_apply_one z)
  map_mul' g h :=
    congrArg Multiplicative.ofAdd (((mem_Z1_iff_of_trivial htriv).mp z.2).2 g h)
  continuous_toFun := ((mem_Z1_iff_of_trivial htriv).mp z.2).1

/-- A continuous character into a multiplicative copy, regarded as a `1`-cocycle for a trivial
action. -/
private def continuousCharToZ1OfTrivial (htriv : ∀ (g : G) (m : M), g • m = m)
    (f : ContinuousMonoidHom G (Multiplicative M)) : Z1 G M :=
  ⟨fun g => Multiplicative.toAdd (f g), (mem_Z1_iff_of_trivial htriv).mpr
    ⟨f.continuous_toFun, fun g h => congrArg Multiplicative.toAdd (map_mul f g h)⟩⟩

omit [T2Space M] [ContinuousSMul G M]
  [ContinuousSMul (maxProPQuotient p G) M] in
/-- Pullback on `1`-cocycles along `G → G(p)` is bijective for a trivial pro-`p` coefficient
group. -/
theorem bijective_Z1comap_maxProPMk_of_trivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    Function.Bijective
      (Z1comap (maxProPMk p G) (AddMonoidHom.id M) continuous_id
        (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm)) := by
  constructor
  · intro a b hab
    apply Subtype.ext
    funext q
    obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel p G) q
    exact congrFun (congrArg Subtype.val hab) g
  · intro z
    let f : ContinuousMonoidHom G (Multiplicative M) :=
      z1ToContinuousCharOfTrivial htrivG z
    let fbar : ContinuousMonoidHom (maxProPQuotient p G) (Multiplicative M) :=
      (maxProPHomEquiv hM).symm f
    refine ⟨continuousCharToZ1OfTrivial htrivQ fbar, ?_⟩
    apply Subtype.ext
    funext g
    exact congrArg (fun u => Multiplicative.toAdd (u g))
      ((maxProPHomEquiv hM).apply_symm_apply f)

/-- Pullback along `G → G(p)` as an additive equivalence on continuous `1`-cocycles with
trivial pro-`p` coefficients. -/
noncomputable def maxProPZ1EquivOfTrivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    Z1 (maxProPQuotient p G) M ≃+ Z1 G M :=
  AddEquiv.ofBijective
    (Z1comap (maxProPMk p G) (AddMonoidHom.id M) continuous_id
      (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm))
    (bijective_Z1comap_maxProPMk_of_trivial hM htrivG htrivQ)

/-- Inflation along `G → G(p)` as an additive equivalence on `H¹` with trivial pro-`p`
coefficients. -/
noncomputable def maxProPH1EquivOfTrivial
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m) :
    H1 (maxProPQuotient p G) M ≃+ H1 G M :=
  (H1equivZ1OfTrivial htrivQ).trans
    ((maxProPZ1EquivOfTrivial hM htrivG htrivQ).trans
      (H1equivZ1OfTrivial htrivG).symm)

omit [T2Space M] [ContinuousSMul G M]
  [ContinuousSMul (maxProPQuotient p G) M] in
/-- The forward map of `maxProPH1EquivOfTrivial` is the existing degree-one inflation map. -/
theorem maxProPH1EquivOfTrivial_apply
    (hM : IsProP p (Multiplicative M))
    (htrivG : ∀ (g : G) (m : M), g • m = m)
    (htrivQ : ∀ (g : maxProPQuotient p G) (m : M), g • m = m)
    (x : H1 (maxProPQuotient p G) M) :
    maxProPH1EquivOfTrivial hM htrivG htrivQ x =
      inf1 (maxProPMk p G)
        (fun g m => (htrivQ (maxProPMk p G g) m).trans (htrivG g m).symm) x := by
  obtain ⟨z, rfl⟩ := H1mk_surjective (G := maxProPQuotient p G) (M := M) x
  rfl

end TrivialCoefficients

section DegreeTwoInflation

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
variable [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
variable [DistribMulAction (maxProPQuotient 2 G) (ZMod 2)]
  [ContinuousSMul (maxProPQuotient 2 G) (ZMod 2)]

/-- Degree-two inflation from the maximal pro-2 quotient is injective with trivial mod-2
coefficients.  The proof forms the continuous central extension classified by a normalized
representative, observes that this extension is pro-2, and applies the universal property of
`maxProPQuotient` to descend a splitting of the inflated extension. -/
theorem injective_inf2_maxProPMk_zmodTwo
    (htrivG : ∀ (g : G) (a : ZMod 2), g • a = a)
    (htrivQ : ∀ (q : maxProPQuotient 2 G) (a : ZMod 2), q • a = a) :
    Function.Injective
      (inf2 (maxProPMk 2 G)
        (fun g a => (htrivQ (maxProPMk 2 G g) a).trans (htrivG g a).symm)) := by
  let pi := maxProPMk 2 G
  let hcompat : ∀ (g : G) (a : ZMod 2), pi g • a = g • a :=
    fun g a => (htrivQ (pi g) a).trans (htrivG g a).symm
  apply (injective_iff_map_eq_zero _).mpr
  intro x hx
  obtain ⟨z, rfl⟩ := H2mk_surjective (G := maxProPQuotient 2 G) (M := ZMod 2) x
  have hx' : H2mk G (ZMod 2)
      (Z2comap pi (AddMonoidHom.id (ZMod 2)) continuous_id hcompat z) = 0 := by
    simpa [pi, hcompat] using hx
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hx'
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨psi, hpsi_cont, hpsi⟩ := hmem
  have hcob (g h : G) :
      g • psi h - psi (g * h) + psi g = z.1 (pi g, pi h) := by
    simpa [dOne, Z2comap] using congrFun hpsi (g, h)
  let c : MaxProPH2Inflation.NormZ2 := MaxProPH2Inflation.normalize htrivQ z
  let psi0 : G → ZMod 2 := fun g => psi g - z.1 (1, 1)
  have hpsi_one : psi 1 = z.1 (1, 1) := by
    simpa [htrivG] using hcob 1 1
  have hpsi0_one : psi0 1 = 0 := by
    simp [psi0, hpsi_one]
  have hcob0 (g h : G) :
      c.kappa (pi g) (pi h) = psi0 h - psi0 (g * h) + psi0 g := by
    have hraw : psi h - psi (g * h) + psi g = z.1 (pi g, pi h) := by
      simpa [htrivG] using hcob g h
    dsimp [c, MaxProPH2Inflation.normalize, psi0]
    rw [← hraw]
    abel
  let f : ContinuousMonoidHom G (MaxProPH2Inflation.CentExt c) :=
    { toFun := fun g => (pi g, -(psi0 g))
      map_one' := by
        apply Prod.ext
        · exact map_one pi
        · change -(psi0 1) = 0
          rw [hpsi0_one]
          simp
      map_mul' := fun g h => by
        apply Prod.ext
        · exact map_mul pi g h
        · change -(psi0 (g * h)) =
            -(psi0 g) + -(psi0 h) + c.kappa (pi g) (pi h)
          rw [hcob0]
          abel
      continuous_toFun := pi.continuous_toFun.prodMk
        ((hpsi_cont.sub continuous_const).neg) }
  have hExt : IsProP 2 (MaxProPH2Inflation.CentExt c) :=
    MaxProPH2Inflation.CentExt.isProP isProP_maxProPQuotient
  let fbar : ContinuousMonoidHom (maxProPQuotient 2 G)
      (MaxProPH2Inflation.CentExt c) :=
    (maxProPHomEquiv hExt).symm f
  have hfactor (g : G) : fbar (pi g) = f g :=
    DFunLike.congr_fun ((maxProPHomEquiv hExt).apply_symm_apply f) g
  have hbase (q : maxProPQuotient 2 G) : MaxProPH2Inflation.CentExt.base (fbar q) = q := by
    obtain ⟨g, rfl⟩ := quotientMk_surjective (proPKernel 2 G) q
    change MaxProPH2Inflation.CentExt.base (fbar (pi g)) = pi g
    have h := congrArg MaxProPH2Inflation.CentExt.base (hfactor g)
    change MaxProPH2Inflation.CentExt.base (fbar (pi g)) = pi g at h
    exact h
  let lam : maxProPQuotient 2 G → ZMod 2 := fun q =>
    -(MaxProPH2Inflation.CentExt.fib (fbar q)) + z.1 (1, 1)
  have hlam_cont : Continuous lam :=
    (MaxProPH2Inflation.CentExt.continuous_fib.comp fbar.continuous_toFun).neg.add
      continuous_const
  have hfib_mul (q r : maxProPQuotient 2 G) :
      MaxProPH2Inflation.CentExt.fib (fbar (q * r)) =
        MaxProPH2Inflation.CentExt.fib (fbar q) +
          MaxProPH2Inflation.CentExt.fib (fbar r) + c.kappa q r := by
    have h := congrArg MaxProPH2Inflation.CentExt.fib (map_mul fbar q r)
    simpa [hbase] using h
  have hlam : dOne (maxProPQuotient 2 G) (ZMod 2) lam = z.1 := by
    funext p
    have hm := hfib_mul p.1 p.2
    change p.1 • lam p.2 - lam (p.1 * p.2) + lam p.1 = z.1 p
    rw [htrivQ]
    dsimp [lam] at ⊢
    dsimp [c, MaxProPH2Inflation.normalize] at hm
    calc
      -(MaxProPH2Inflation.CentExt.fib (fbar p.2)) + z.1 (1, 1) -
            (-(MaxProPH2Inflation.CentExt.fib (fbar (p.1 * p.2))) + z.1 (1, 1)) +
            (-(MaxProPH2Inflation.CentExt.fib (fbar p.1)) + z.1 (1, 1)) =
          -(MaxProPH2Inflation.CentExt.fib (fbar p.2)) + z.1 (1, 1) +
            (MaxProPH2Inflation.CentExt.fib (fbar (p.1 * p.2)) - z.1 (1, 1)) +
            (-(MaxProPH2Inflation.CentExt.fib (fbar p.1)) + z.1 (1, 1)) := by abel
      _ = -(MaxProPH2Inflation.CentExt.fib (fbar p.2)) + z.1 (1, 1) +
            ((MaxProPH2Inflation.CentExt.fib (fbar p.1) +
              MaxProPH2Inflation.CentExt.fib (fbar p.2) +
              (z.1 (p.1, p.2) - z.1 (1, 1))) - z.1 (1, 1)) +
            (-(MaxProPH2Inflation.CentExt.fib (fbar p.1)) + z.1 (1, 1)) := by
          exact congrArg (fun t =>
            -(MaxProPH2Inflation.CentExt.fib (fbar p.2)) + z.1 (1, 1) +
              (t - z.1 (1, 1)) +
              (-(MaxProPH2Inflation.CentExt.fib (fbar p.1)) + z.1 (1, 1))) hm
      _ = z.1 p := by abel
  apply (QuotientAddGroup.eq_zero_iff z).mpr
  apply AddSubgroup.mem_addSubgroupOf.mpr
  exact ⟨lam, hlam_cont, hlam⟩

end DegreeTwoInflation

end GQ2
