import GQ2.Dyadic.Instances.MpcWordPhaseSeam
import GQ2.Dyadic.Certificates.M0Assembly
import GQ2.Dyadic.Certificates.MpcJet

namespace GQ2.Dyadic.Instances.MpcUnramifiedHessian

/-! Exact handle-free Hessian values for the unramified procyclic-M word. -/

noncomputable section

open GQ2 GQ2.QuadraticFp2 GQ2.SectionSix GQ2.FoxH
open GQ2.SectionEight SectionSeven AffineTLift CentralObstruction ContCoh
open GQ2.Dyadic GQ2.Dyadic.Words GQ2.Dyadic.Words.Mpc
open GQ2.Dyadic.Count
open GQ2.Dyadic.LSquare GQ2.Dyadic.MProcyclicExact
open GQ2.Dyadic.Certificates GQ2.Dyadic.Certificates.MCompact
open GQ2.Dyadic.Certificates.MProcyclic

variable {C V : Type} [Group C] [AddCommGroup V] [DistribMulAction C V]
  {q : V → ZMod 2} (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)

theorem line_mul_slice_of_trivial (g : C) (hg : ∀ w : V, g • w = w)
    (v : V) (z : ZMod 2) :
    hessLine dat hdat g * hessSlice dat hdat v z =
      hessSlice dat hdat v (z + dat.m g v) * hessLine dat hdat g := by
  refine WordCoh.CentExt.ext (Prod.ext ?_ ?_) ?_
  · show (0 : V) + g • v = v + (1 : C) • (0 : V)
    rw [hg, smul_zero, add_zero, zero_add]
  · show g * (1 : C) = (1 : C) * g
    rw [mul_one, one_mul]
  · show (0 : ZMod 2) + z + (dat.f 0 (g • v) + dat.m g v) =
      (z + dat.m g v) + 0 + (dat.f v ((1 : C) • (0 : V)) + dat.m 1 (0 : V))
    rw [hdat.f_zero_left, smul_zero, hdat.f_zero_right, hdat.m_one]
    abel

include hdat in
theorem factorSet_m_inv_of_trivial (g : C) (hg : ∀ w : V, g • w = w) (v : V) :
    dat.m g⁻¹ v = dat.m g v := by
  have hm := hdat.m_mul g⁻¹ g v
  simp only [inv_mul_cancel, hdat.m_one, hg] at hm
  have hz : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  exact hz _ _ hm.symm

theorem commR_slice_line_of_trivial
    (g : C) (hg : ∀ w : V, g • w = w) (v : V) (z : ZMod 2) :
    commR (hessSlice dat hdat v z) (hessLine dat hdat g) =
      WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (dat.m g v) := by
  have hgi : ∀ w : V, g⁻¹ • w = w := fun w ↦ by
    rw [inv_smul_eq_iff, hg]
  have hlinv : (hessLine dat hdat g)⁻¹ = hessLine dat hdat g⁻¹ := by
    change (hessLineHom dat hdat g)⁻¹ = hessLineHom dat hdat (g⁻¹)
    rw [map_inv]
  have hswap := line_mul_slice_of_trivial dat hdat g⁻¹ hgi v z
  rw [factorSet_m_inv_of_trivial dat hdat g hg v] at hswap
  calc
    commR (hessSlice dat hdat v z) (hessLine dat hdat g) =
        (hessSlice dat hdat v z)⁻¹ *
          ((hessLine dat hdat g⁻¹ * hessSlice dat hdat v z) *
            hessLine dat hdat g) := by rw [commR, hlinv]; group
    _ = (hessSlice dat hdat v z)⁻¹ *
          ((hessSlice dat hdat v (z + dat.m g v) * hessLine dat hdat g⁻¹) *
            hessLine dat hdat g) := by rw [hswap]
    _ = WordCoh.CentExt.incl (kappa0Cocycle dat hdat) (dat.m g v) := by
      rw [← hessSlice_mul_incl dat hdat]
      rw [← hlinv]
      group

theorem commR_mul_right (x y z : WordCoh.CentExt (kappa0Cocycle dat hdat)) :
    commR x (y * z) = commR x z * conjR (commR x y) z := by
  simp only [commR, conjR, mul_inv_rev]
  group

theorem slice_comm_slice_mul_line_of_trivial (hV2 : ∀ v : V, v + v = 0)
    (g : C) (hg : ∀ w : V, g • w = w)
    (a b : V) (za zb : ZMod 2) :
    commR (hessSlice dat hdat a za) (hessSlice dat hdat b zb * hessLine dat hdat g) =
      hessLineZ dat hdat 1 (polar q a b + dat.m g a) := by
  rw [commR_mul_right dat hdat,
    commR_slice_line_of_trivial dat hdat g hg a za,
    hessSlice_commR dat hdat hV2]
  rw [conjR_eq_self_of_commute
    (GQ2.Dyadic.Certificates.MpcJet.incl_commute _ _).symm]
  rw [centExt_incl_mul]
  rw [← hessLineZ_incl, add_comm]

section Word

variable {h : ℕ} (s : C) (vv : Fin (2 + 2 * h + 1) → V)
  (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)

private noncomputable abbrev mu :=
  WordCoh.lift (Certificates.hessMark s (1 : C) vv) (kappa0Cocycle dat hdat)

theorem evalZ_dW_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (i : Fin 3) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (dW h i) = 1 := by
  rw [dW_eq_deltaCert]
  exact hessDeltaCert_P1 dat hdat s 1 vv E E₂ i
    (hessDeltaBlock_P1 dat hdat hV2 s vv E E₂ hE he i)

theorem evalZ_sig2PowW_line (p : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (sig2PowW h p) =
      hessLine dat hdat ((s ^ E omega2) ^ p) := by
  rcases p with _ | _ | p
  · rw [show sig2PowW h 0 = .zpow sigma2W (0 : ℤ) from rfl,
      PWord.evalZ_zpow, hessM_sigma2W dat hdat s 1 vv E E₂]
    simp
    rfl
  · rw [show sig2PowW h 1 = sigma2W from rfl]
    simp only [Nat.zero_add, pow_one]
    dsimp only [mu]
    exact hessM_sigma2W dat hdat s 1 vv E E₂
  · rw [show sig2PowW h (p + 2) = .zpow sigma2W ((p + 2 : ℕ) : ℤ) from rfl,
      hessM_sigma2Pow dat hdat s 1 vv E E₂]
    norm_cast

theorem evalZ_c0W_line (hv2 : vv (Certificates.x2Idx h) = 0) (s' : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (c0W h s') =
      hessLine dat hdat ((s ^ E omega2) ^ s') := by
  rw [c0W, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    PWord.evalZ_gen]
  rw [show mu dat hdat s vv (coreLetter h 2) =
      hessSlice dat hdat (vv (Certificates.x2Idx h)) 0 from rfl, hv2]
  change 1 * PWord.evalZ (mu dat hdat s vv) E E₂
      (.zpow sigma2W ((s' : ℕ) : ℤ)) = _
  rw [one_mul, hessM_sigma2Pow dat hdat s 1 vv E E₂]
  norm_cast

theorem evalZ_e01W_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (a b : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (e01W h a b) = 1 := by
  rw [e01W, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_conj, PWord.evalZ_prodList, PWord.evalZ_zpow, mul_one]
  rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 0,
    evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 1]
  simp

theorem evalZ_zW_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (p : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (zW h p) = 1 := by
  rcases p with _ | p
  · rw [show zW h 0 = .zpow (dW h 2) ((2 : ℕ) : ℤ) from rfl,
      PWord.evalZ_zpow, evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 2, one_zpow]
  · rw [show zW h (p + 1) =
        PWord.prodList [dW h 2, .conj (dW h 2) (sig2PowW h (p + 1))] from rfl,
      PWord.evalZ_prodList]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
      PWord.evalZ_conj, mul_one]
    rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 2]
    simp

theorem evalZ_e2W_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (s' mm p : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (e2W h s' mm p) = 1 := by
  have hnorm :
      ((Export.orbitNormFactors (zW h p) (.zpow sigma2W (s' : ℤ)) mm).map
        (PWord.evalZ (mu dat hdat s vv) E E₂ ·)).prod = 1 := by
    refine List.prod_eq_one fun y hy ↦ ?_
    rw [List.mem_map] at hy
    obtain ⟨w, hw, rfl⟩ := hy
    rw [orbitNormFactors_map, List.mem_map] at hw
    obtain ⟨j, -, rfl⟩ := hw
    rw [PWord.evalZ_conj,
      evalZ_zW_one dat hdat s vv E E₂ hV2 hE he p, one_conjR]
  rw [e2W, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_conj, PWord.evalZ_prodList, mul_one]
  rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 2]
  rw [one_conjR, one_mul, hnorm, one_conjR]

theorem evalZ_plusW_one (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (plusW h) = 1 := by
  rw [plusW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil,
    PWord.evalZ_zpow, PWord.evalZ_comm, mul_one]
  rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 0,
    evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 1]
  simp

theorem evalZ_aW (hV2 : ∀ v : V, v + v = 0)
    (hv2 : vv (Certificates.x2Idx h) = 0) (s' mm : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (aW h s' mm) =
      hessSlice dat hdat (vv (Certificates.x0Idx h)) (q (vv (Certificates.x0Idx h))) *
        hessLine dat hdat (((s ^ E omega2) ^ s') ^ (-(mm : ℤ))) := by
  rw [aW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    PWord.evalZ_inv, PWord.evalZ_gen, PWord.evalZ_zpow]
  rw [show mu dat hdat s vv (coreLetter h 0) =
      hessSlice dat hdat (vv (Certificates.x0Idx h)) 0 from rfl,
    hessSlice_inv dat hdat hV2, zero_add,
    evalZ_c0W_line dat hdat s vv E E₂ hv2 s']
  congr 1
  change (hessLineHom dat hdat ((s ^ E omega2) ^ s')) ^ (-(mm : ℤ)) =
    hessLineHom dat hdat (((s ^ E omega2) ^ s') ^ (-(mm : ℤ)))
  exact (map_zpow (hessLineHom dat hdat) _ _).symm

theorem evalZ_bW (pp : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (bW h pp) =
      hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 *
        hessLine dat hdat ((s ^ E omega2) ^ pp) := by
  rcases pp with _ | pp
  · rw [show bW h 0 = .gen (coreLetter h 1) from rfl, PWord.evalZ_gen]
    dsimp only [mu]
    simp only [pow_zero]
    change hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 =
      hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 * hessLine dat hdat 1
    rw [show hessLine dat hdat (1 : C) = 1 from rfl, mul_one]
  · rw [show bW h (pp + 1) =
        PWord.prodList [.gen (coreLetter h 1), sig2PowW h (pp + 1)] from rfl,
      PWord.evalZ_prodList]
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
      PWord.evalZ_gen]
    rw [show mu dat hdat s vv (coreLetter h 1) =
        hessSlice dat hdat (vv (Certificates.x1Idx h)) 0 from rfl,
      evalZ_sig2PowW_line dat hdat s vv E E₂ (pp + 1)]

theorem evalZ_aSq (hV2 : ∀ v : V, v + v = 0)
    (hv2 : vv (Certificates.x2Idx h) = 0) (hS₂ : ∀ v : V, (s ^ E omega2) • v = v)
    {α : ℕ} (hα : 2 ≤ α) (r : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂
        (.zpow (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α))
          ((2 : ℕ) : ℤ)) =
      hessLineZ dat hdat
        ((((s ^ E omega2) ^ GQ2.Dyadic.s r) ^
          (-(GQ2.Dyadic.m α : ℤ))) ^ 2)
        (q (vv (Certificates.x0Idx h))) := by
  let g := ((s ^ E omega2) ^ GQ2.Dyadic.s r) ^
    (-(GQ2.Dyadic.m α : ℤ))
  have hg : ∀ v : V, g • v = v := fun v ↦
    mem_trivAct.mp (zpow_mem (pow_mem (mem_trivAct.mpr hS₂)
      (GQ2.Dyadic.s r)) (-(GQ2.Dyadic.m α : ℤ))) v
  have hmg : ∀ v : V, dat.m g v = 0 := fun v ↦
    factorSet_m_zpow_even dat hdat
      (fun w ↦ mem_trivAct.mp (pow_mem (mem_trivAct.mpr hS₂)
        (GQ2.Dyadic.s r)) w)
      (even_neg_mOf hα) v
  have hc : Commute (hessSlice dat hdat (vv (Certificates.x0Idx h))
      (q (vv (Certificates.x0Idx h)))) (hessLine dat hdat g) :=
    (hessLine_slice_comm dat hdat hg hmg _ _).symm
  rw [PWord.evalZ_zpow, evalZ_aW dat hdat s vv E E₂ hV2 hv2,
    zpow_natCast, hc.mul_pow, sq, sq,
    hessSlice_sq dat hdat hV2, hessLine_mul dat hdat, incl_mul_hessLine dat hdat]
  simp only [g, pow_two]

theorem evalZ_commAB (hV2 : ∀ v : V, v + v = 0)
    (hv2 : vv (Certificates.x2Idx h) = 0) (hS₂ : ∀ v : V, (s ^ E omega2) • v = v)
    {α : ℕ} (hα : 2 ≤ α) (r pp : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂
        (.comm (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α)) (bW h pp)) =
      hessLineZ dat hdat 1
        (polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
          dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h))) := by
  let ga := ((s ^ E omega2) ^ GQ2.Dyadic.s r) ^
    (-(GQ2.Dyadic.m α : ℤ))
  let gb := (s ^ E omega2) ^ pp
  let a := hessSlice dat hdat (vv (Certificates.x0Idx h))
    (q (vv (Certificates.x0Idx h)))
  let b := hessSlice dat hdat (vv (Certificates.x1Idx h)) 0
  let La := hessLine dat hdat ga
  let Lb := hessLine dat hdat gb
  have hga : ∀ v : V, ga • v = v := fun v ↦
    mem_trivAct.mp (zpow_mem (pow_mem (mem_trivAct.mpr hS₂)
      (GQ2.Dyadic.s r)) (-(GQ2.Dyadic.m α : ℤ))) v
  have hmga : ∀ v : V, dat.m ga v = 0 := fun v ↦
    factorSet_m_zpow_even dat hdat
      (fun w ↦ mem_trivAct.mp (pow_mem (mem_trivAct.mpr hS₂)
        (GQ2.Dyadic.s r)) w)
      (even_neg_mOf hα) v
  have hgb : ∀ v : V, gb • v = v := fun v ↦
    mem_trivAct.mp (pow_mem (mem_trivAct.mpr hS₂) pp) v
  have hLaa : Commute La a := hessLine_slice_comm dat hdat hga hmga _ _
  have hLab : Commute La b := hessLine_slice_comm dat hdat hga hmga _ _
  have hgagb : Commute ga gb := by
    dsimp only [ga, gb]
    have hbase : Commute
        ((s ^ E omega2) ^ (GQ2.Dyadic.s r : ℤ))
        ((s ^ E omega2) ^ (pp : ℤ)) :=
      (Commute.refl (s ^ E omega2)).zpow_zpow _ _
    simpa only [zpow_natCast] using
      hbase.zpow_left (-(GQ2.Dyadic.m α : ℤ))
  have hLaLb : Commute La Lb := by
    exact hgagb.map (hessLineHom dat hdat)
  rw [PWord.evalZ_comm, evalZ_aW dat hdat s vv E E₂ hV2 hv2,
    evalZ_bW dat hdat s vv E E₂ pp]
  change commR (a * La) (b * Lb) = _
  rw [commR_mul_right_of_commute hLaa (hLab.mul_right hLaLb),
    slice_comm_slice_mul_line_of_trivial dat hdat hV2 gb hgb]

def IsHessLine (x : WordCoh.CentExt (kappa0Cocycle dat hdat)) : Prop :=
  ∃ g : C, x = hessLine dat hdat g

theorem isHessLine_one : IsHessLine dat hdat 1 := ⟨1, rfl⟩

theorem IsHessLine.mul {x y : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) (hy : IsHessLine dat hdat y) :
    IsHessLine dat hdat (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  exact (map_mul (hessLineHom dat hdat) a b).symm

theorem IsHessLine.inv {x : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) : IsHessLine dat hdat x⁻¹ := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨a⁻¹, ?_⟩
  exact (map_inv (hessLineHom dat hdat) a).symm

theorem IsHessLine.zpow {x : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) (n : ℤ) : IsHessLine dat hdat (x ^ n) := by
  rcases hx with ⟨a, rfl⟩
  refine ⟨a ^ n, ?_⟩
  exact (map_zpow (hessLineHom dat hdat) a n).symm

theorem IsHessLine.comm {x y : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) (hy : IsHessLine dat hdat y) :
    IsHessLine dat hdat (commR x y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨commR a b, ?_⟩
  exact (map_commR (hessLineHom dat hdat) a b).symm

theorem IsHessLine.conj {x y : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) (hy : IsHessLine dat hdat y) :
    IsHessLine dat hdat (conjR x y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨conjR a b, ?_⟩
  exact (map_conjR (hessLineHom dat hdat) a b).symm

theorem evalZ_c0HatW_line (ss : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (c0HatW h ss) =
      hessLine dat hdat ((s ^ E omega2) ^ ss) := by
  rw [c0HatW, PWord.evalZ_zpow, hessM_sigma2W dat hdat s 1 vv E E₂,
    zpow_natCast]
  exact (map_pow (hessLineHom dat hdat) (s ^ E omega2) ss).symm

theorem evalZ_aHatW_isLine (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) (ss mm : ℕ) :
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (aHatW h ss mm)) := by
  rw [aHatW, PWord.evalZ_prodList]
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one,
    PWord.evalZ_inv, PWord.evalZ_zpow]
  have hd : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (dW h 0)) := by
    rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 0]
    exact isHessLine_one dat hdat
  have hc : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (c0HatW h ss)) := by
    rw [evalZ_c0HatW_line dat hdat s vv E E₂ ss]
    exact ⟨_, rfl⟩
  exact IsHessLine.mul dat hdat (IsHessLine.inv dat hdat hd)
    (IsHessLine.zpow dat hdat hc _)

theorem evalZ_bHatW_isLine (hV2 : ∀ v : V, v + v = 0) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) : ∀ pp : ℕ,
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (bHatW h pp))
  | 0 => by
      rw [show bHatW h 0 = dW h 1 from rfl,
        evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 1]
      exact isHessLine_one dat hdat
  | pp + 1 => by
      rw [show bHatW h (pp + 1) =
        PWord.prodList [dW h 1, sig2PowW h (pp + 1)] from rfl,
        PWord.evalZ_prodList]
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
      have hd : IsHessLine dat hdat
          (PWord.evalZ (mu dat hdat s vv) E E₂ (dW h 1)) := by
        rw [evalZ_dW_one dat hdat s vv E E₂ hV2 hE he 1]
        exact isHessLine_one dat hdat
      have hs : IsHessLine dat hdat
          (PWord.evalZ (mu dat hdat s vv) E E₂ (sig2PowW h (pp + 1))) := by
        rw [evalZ_sig2PowW_line dat hdat s vv E E₂ (pp + 1)]
        exact ⟨_, rfl⟩
      exact IsHessLine.mul dat hdat hd hs

theorem evalZ_etaOne_isLine :
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ EtaDisplay.one.toPWord) := by
  refine ⟨s, ?_⟩
  rfl

def HasHessCharge (z : ZMod 2)
    (x : WordCoh.CentExt (kappa0Cocycle dat hdat)) : Prop :=
  ∃ g : C, x = hessLineZ dat hdat g z

theorem IsHessLine.hasHessCharge_zero
    {x : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : IsHessLine dat hdat x) : HasHessCharge dat hdat 0 x := by
  rcases hx with ⟨g, rfl⟩
  exact ⟨g, rfl⟩

theorem HasHessCharge.mul {z w : ZMod 2}
    {x y : WordCoh.CentExt (kappa0Cocycle dat hdat)}
    (hx : HasHessCharge dat hdat z x) (hy : HasHessCharge dat hdat w y) :
    HasHessCharge dat hdat (z + w) (x * y) := by
  rcases hx with ⟨a, rfl⟩
  rcases hy with ⟨b, rfl⟩
  refine ⟨a * b, ?_⟩
  exact hessLineZ_mul dat hdat a b z w

theorem evalZ_linFactors_hasCharge (hV2 : ∀ v : V, v + v = 0)
    (hv2 : vv (Certificates.x2Idx h) = 0)
    (hS₂ : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    {α : ℕ} (hα : 2 ≤ α) (r pp : ℕ) :
    HasHessCharge dat hdat
      (q (vv (Certificates.x0Idx h)) +
        polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E₂
        (PWord.prodList (linFactors α r pp .one h))) := by
  let f1 : PWord (Generator (2 + 2 * h)) :=
    .zpow (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α)) ((2 : ℕ) : ℤ)
  let f2 : PWord (Generator (2 + 2 * h)) :=
    .comm (aW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α)) (bW h pp)
  let f3 : PWord (Generator (2 + 2 * h)) :=
    .zpow (c0W h (GQ2.Dyadic.s r)) ((2 ^ α : ℕ) : ℤ)
  let f4 : PWord (Generator (2 + 2 * h)) :=
    .comm (c0W h (GQ2.Dyadic.s r)) EtaDisplay.one.toPWord
  let f5 : PWord (Generator (2 + 2 * h)) :=
    e01W h (pp + GQ2.Dyadic.s r * GQ2.Dyadic.m α)
    (GQ2.Dyadic.s r * GQ2.Dyadic.m α)
  let f6 : PWord (Generator (2 + 2 * h)) :=
    e2W h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α) pp
  have h1 : HasHessCharge dat hdat (q (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E₂ f1) := by
    refine ⟨((((s ^ E omega2) ^ GQ2.Dyadic.s r) ^
      (-(GQ2.Dyadic.m α : ℤ))) ^ 2), ?_⟩
    exact evalZ_aSq dat hdat s vv E E₂ hV2 hv2 hS₂ hα r
  have h2 : HasHessCharge dat hdat
      (polar q (vv (Certificates.x0Idx h)) (vv (Certificates.x1Idx h)) +
        dat.m ((s ^ E omega2) ^ pp) (vv (Certificates.x0Idx h)))
      (PWord.evalZ (mu dat hdat s vv) E E₂ f2) := by
    refine ⟨1, ?_⟩
    exact evalZ_commAB dat hdat s vv E E₂ hV2 hv2 hS₂ hα r pp
  have hc0 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (c0W h (GQ2.Dyadic.s r))) := by
    rw [evalZ_c0W_line dat hdat s vv E E₂ hv2]
    exact ⟨_, rfl⟩
  have h3 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ f3) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat hc0 _
  have h4 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ f4) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat hc0
      (evalZ_etaOne_isLine dat hdat s vv E E₂)
  have h5 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ f5) := by
    rw [evalZ_e01W_one dat hdat s vv E E₂ hV2 hE he]
    exact isHessLine_one dat hdat
  have h6 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ f6) := by
    rw [evalZ_e2W_one dat hdat s vv E E₂ hV2 hE he]
    exact isHessLine_one dat hdat
  have htail : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ f3 *
        (PWord.evalZ (mu dat hdat s vv) E E₂ f4 *
          (PWord.evalZ (mu dat hdat s vv) E E₂ f5 *
            (PWord.evalZ (mu dat hdat s vv) E E₂ f6 * 1)))) :=
    IsHessLine.mul dat hdat h3 (IsHessLine.mul dat hdat h4
      (IsHessLine.mul dat hdat h5
        (IsHessLine.mul dat hdat h6 (isHessLine_one dat hdat))))
  have hall := HasHessCharge.mul dat hdat h1
    (HasHessCharge.mul dat hdat h2 htail.hasHessCharge_zero)
  simpa only [PWord.evalZ_prodList, linFactors, f1, f2, f3, f4, f5, f6,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, add_zero, add_assoc] using hall

theorem evalZ_hatFactors_isLine (hV2 : ∀ v : V, v + v = 0)
    {e : ℕ} (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1)
    (α r pp : ℕ) :
    IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂
        (PWord.prodList (hatFactors α r pp .one h))) := by
  let a := aHatW h (GQ2.Dyadic.s r) (GQ2.Dyadic.m α)
  let b := bHatW h pp
  let c := c0HatW h (GQ2.Dyadic.s r)
  let eta : PWord (Generator (2 + 2 * h)) := EtaDisplay.one.toPWord
  let ee := e01W h (pp + GQ2.Dyadic.s r * GQ2.Dyadic.m α)
    (GQ2.Dyadic.s r * GQ2.Dyadic.m α)
  have ha := evalZ_aHatW_isLine dat hdat s vv E E₂ hV2 hE he
    (GQ2.Dyadic.s r) (GQ2.Dyadic.m α)
  have hb := evalZ_bHatW_isLine dat hdat s vv E E₂ hV2 hE he pp
  have hc : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ c) := by
    rw [evalZ_c0HatW_line dat hdat s vv E E₂]
    exact ⟨_, rfl⟩
  have heta := evalZ_etaOne_isLine dat hdat s vv E E₂
  have hee : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ ee) := by
    rw [evalZ_e01W_one dat hdat s vv E E₂ hV2 hE he]
    exact isHessLine_one dat hdat
  have h1 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (.zpow a ((2 : ℕ) : ℤ))) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat ha _
  have h2 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (.comm a b)) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat ha hb
  have h3 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (.zpow c ((2 ^ α : ℕ) : ℤ))) := by
    rw [PWord.evalZ_zpow]
    exact IsHessLine.zpow dat hdat hc _
  have h4 : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (.comm c eta)) := by
    rw [PWord.evalZ_comm]
    exact IsHessLine.comm dat hdat hc heta
  have hall := IsHessLine.mul dat hdat h1 (IsHessLine.mul dat hdat h2
    (IsHessLine.mul dat hdat h3 (IsHessLine.mul dat hdat h4
      (IsHessLine.mul dat hdat hee (isHessLine_one dat hdat)))))
  simpa only [PWord.evalZ_prodList, hatFactors, a, b, c, eta, ee,
    List.map_cons, List.map_nil, List.prod_cons, List.prod_nil] using hall

theorem evalZ_mpcW_factored_zero (s : C) (vv : Fin 3 → V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ) (α r pp : ℕ) :
    PWord.evalZ (mu dat hdat s vv) E E₂ (mpcW α r pp .one 0) =
      PWord.evalZ (mu dat hdat s vv) E E₂
          (PWord.prodList (linFactors α r pp .one 0)) *
        PWord.evalZ (mu dat hdat s vv) E E₂
          (PWord.prodList (hatFactors α r pp .one 0)) *
        PWord.evalZ (mu dat hdat s vv) E E₂ (plusW 0) := by
  rw [mpcW, plusW, PWord.evalZ_prodList, PWord.evalZ_prodList,
    PWord.evalZ_prodList, PWord.evalZ_prodList]
  simp only [handleTailW, List.append_nil, List.map_append, List.prod_append]

theorem hessRelZ_mpcW_unramified_zero (hV2 : ∀ v : V, v + v = 0)
    {α : ℕ} (hα : 2 ≤ α) (r pp : ℕ) (s : C) (c0 c1 : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
        (kappa0Cocycle dat hdat) E E₂ (mpcW α r pp .one 0) =
      q c0 + polar q c0 c1 + dat.m ((s ^ E omega2) ^ pp) c0 := by
  let vv : Fin 3 → V := ![c0, c1, 0]
  have hv0 : vv (Certificates.x0Idx 0) = c0 := rfl
  have hv1 : vv (Certificates.x1Idx 0) = c1 := rfl
  have hv2 : vv (Certificates.x2Idx 0) = 0 := rfl
  have hlin := evalZ_linFactors_hasCharge (h := 0) dat hdat s vv E E₂ hV2 hv2 hS₂
    hE he hα r pp
  have hhat := evalZ_hatFactors_isLine (h := 0) dat hdat s vv E E₂ hV2 hE he α r pp
  have hplus : IsHessLine dat hdat
      (PWord.evalZ (mu dat hdat s vv) E E₂ (plusW 0)) := by
    rw [evalZ_plusW_one (h := 0) dat hdat s vv E E₂ hV2 hE he]
    exact isHessLine_one dat hdat
  have hall := HasHessCharge.mul dat hdat
    (HasHessCharge.mul dat hdat hlin hhat.hasHessCharge_zero)
    hplus.hasHessCharge_zero
  have heval : HasHessCharge dat hdat
      (q c0 + polar q c0 c1 + dat.m ((s ^ E omega2) ^ pp) c0)
      (PWord.evalZ (mu dat hdat s vv) E E₂ (mpcW α r pp .one 0)) := by
    rw [evalZ_mpcW_factored_zero dat hdat s vv E E₂ α r pp]
    simpa only [hv0, hv1, add_zero] using hall
  rw [hessRelZ, hessEvalZ]
  change (PWord.evalZ (mu dat hdat s vv) E E₂ (mpcW α r pp .one 0)).fib = _
  rcases heval with ⟨g, hg⟩
  rw [hg, hessLineZ_fib]

theorem hessRelZ_mpcW_unramified_zero_pp_zero (hV2 : ∀ v : V, v + v = 0)
    {α : ℕ} (hα : 2 ≤ α) (r : ℕ) (s : C) (c0 c1 : V)
    (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hS₂ : ∀ v : V, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    hessRelZ (Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
        (kappa0Cocycle dat hdat) E E₂ (mpcW α r 0 .one 0) =
      plusFormD q q (c0, c1) := by
  rw [hessRelZ_mpcW_unramified_zero dat hdat hV2 hα r 0 s c0 c1 E E₂ hS₂ hE he,
    pow_zero, hdat.m_one, add_zero, plusFormD_apply]

theorem wPmpc_QZero_eq_plusFormD_pp_zero_of_headMark
    {alpha r qrel : ℕ}
    {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
    {D : RadicalCoverData Bg} {DD : DescData D}
    (rho : ContinuousMonoidHom
      ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (Bg ⧸ D.M))
    [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
    [TopologicalSpace DD.C0] [DiscreteTopology DD.C0]
    [Finite DD.Vmod] [Finite DD.C0]
    (hdat : IsEquivariantFactorSet DD.qbar DD.dat)
    (halpha : 2 ≤ alpha) (hq : Even qrel)
    (hcardH2 :
      letI : TopologicalSpace (ZMod 2) := ⊥
      letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
      letI : DistribMulAction
          ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2) :=
        scalarActionZmodTwo _
      Nat.card
        (H2 ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2)) = 2)
    (c : VCocycle DD rho) (E : Zhat → ℤ) (E₂ : ℤ_[2] → ℤ)
    (hresolved :
      letI : Finite (SectionSix.SemiProd DD.C0 DD.Vmod) :=
        inferInstanceAs (Finite (DD.Vmod × DD.C0))
      letI : Finite
          (WordCoh.CentExt (kappa0Cocycle DD.dat hdat)) := inferInstance
      letI : TopologicalSpace
          (WordCoh.CentExt (kappa0Cocycle DD.dat hdat)) := ⊥
      letI : DiscreteTopology
          (WordCoh.CentExt (kappa0Cocycle DD.dat hdat)) := ⟨rfl⟩
      ∀ k, PWord.ResolvedAt
        (WordCoh.lift
          (fun i ↦ graphSemiProdHom c
            (gammaGen 2 qrel (mpcW alpha r 0 .one 0) i))
          (kappa0Cocycle DD.dat hdat)) E E₂
        (gammaFam 2 qrel (mpcW alpha r 0 .one 0) k))
    (s : DD.C0) (c0 c1 : DD.Vmod)
    (hmark :
      (fun i ↦ graphSemiProdHom c
        (gammaGen 2 qrel (mpcW alpha r 0 .one 0) i)) =
        Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
    (hS₂ : ∀ v : DD.Vmod, (s ^ E omega2) • v = v) {e : ℕ}
    (hE : E omega2 = (e : ℤ)) (he : e % 4 = 1) :
    letI : TopologicalSpace (ZMod 2) := ⊥
    letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
    letI : DistribMulAction
        ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo _
    letI : ContinuousSMul
        ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2) :=
      scalarActionZmodTwo_continuousSMul _
    QZero DD rho c = plusFormD DD.qbar DD.qbar (c0, c1) := by
  letI : TopologicalSpace (ZMod 2) := ⊥
  letI : DiscreteTopology (ZMod 2) := ⟨rfl⟩
  letI : DistribMulAction
      ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo _
  letI : ContinuousSMul
      ((displayedGamma alpha r 0 0 qrel .one : ProfiniteGrp) : Type) (ZMod 2) :=
    scalarActionZmodTwo_continuousSMul _
  rw [GQ2.Dyadic.Instances.MpcWordPhaseSeam.wPmpc_QZero_eq_graphHessianTrace
      rho hdat (by omega) hq hcardH2 c E E₂ hresolved, hmark]
  have htame :
      hessRelZ (Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
        (kappa0Cocycle DD.dat hdat) E E₂ (tameRelW 2 qrel) = 0 :=
    GQ2.Dyadic.Instances.WordPhaseSeam.wPs_hessRelZ_tameRelW_hessMark_eq_zero
      (h := 0) (q := qrel) DD.dat hdat s 1 ![c0, c1, 0] E E₂
  change hessRelZ (Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
      (kappa0Cocycle DD.dat hdat) E E₂ (tameRelW 2 qrel) +
    hessRelZ (Certificates.hessMark (h := 0) s 1 ![c0, c1, 0])
      (kappa0Cocycle DD.dat hdat) E E₂ (mpcW alpha r 0 .one 0) = _
  rw [htame, zero_add,
    hessRelZ_mpcW_unramified_zero_pp_zero DD.dat hdat (Vmod_exp2 DD)
      halpha r s c0 c1 E E₂ hS₂ hE he]

end Word

#print axioms hessRelZ_mpcW_unramified_zero
#print axioms hessRelZ_mpcW_unramified_zero_pp_zero
#print axioms wPmpc_QZero_eq_plusFormD_pp_zero_of_headMark

end

end GQ2.Dyadic.Instances.MpcUnramifiedHessian
