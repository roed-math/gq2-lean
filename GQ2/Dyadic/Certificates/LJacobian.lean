import GQ2.Dyadic.Certificates.LFox
import GQ2.Dyadic.Certificates.N0Fox

/-!
# The full L Jacobian, uniformly in the handle rank

The established L wild row and the word-independent tame row assemble directly into
the original two-row `FoxCertificate`. This additive module closes the old packaging
gap without moving declarations or changing the frozen word. The three sector records
retain both actual relators and the supplied resolvers literally in their types.

Unramified: one row addition gives `(S⁻¹ x_tau, (1-S⁻¹) x0)`.
Ramified: one invertible column scaling gives `(tame row, x0)`.
Scalar: one row subtraction gives `(x_tau, 0)`.
These are all-cochain identities; there is no wild-relation-death or matrix hypothesis.
The ramified record explicitly retains the actual tame relation.
-/

namespace GQ2.Dyadic.Certificates.LSq
noncomputable section
open GQ2.FoxH GQ2.Dyadic.Words.LSq

/-- A single formal coefficient at a specified generator. -/
def lSingleCoeffRow {X S : Type*} [DecidableEq X] (g : X) (c : FoxCoeff S) :
    FoxRowNormalForm X S := ⟨fun x => if x = g then c else .zero⟩

theorem lSingleCoeffRow_toHom_apply {X S V : Type*} [Fintype X] [DecidableEq X]
    [AddCommGroup V] (rho : S → AddMonoid.End V) (g : X) (c : FoxCoeff S) (a : X → V) :
    (lSingleCoeffRow g c).toHom rho a = c.eval rho (a g) := by
  classical
  rw [FoxRowNormalForm.toHom_apply, Finset.sum_eq_single g]
  · simp [lSingleCoeffRow]
  · intro b _ hbg
    simp [lSingleCoeffRow, hbg]
  · simp

/-- The unramified L pivot is at x0, not the even-family x2 slot. -/
def lSqUnramNormalForm (h : ℕ) :
    FoxNormalForm (Generator (2*h+1)) (TameSym (2*h+1)) :=
  ⟨tameUnramRow _, lSingleCoeffRow (coreLetter h 0) (oneSubSInv _)⟩

def lSqRamNormalForm (h q : ℕ) :
    FoxNormalForm (Generator (2*h+1)) (TameSym (2*h+1)) :=
  ⟨tameRow _ q, .single (coreLetter h 0)⟩

def lSqRamOps (h : ℕ) : List (FoxColOp (Generator (2*h+1)) (TameSym (2*h+1))) :=
  [.scale (coreLetter h 0) (.atom (.gen .sigma 1)) (.atom (.gen .sigma (-1)))]

variable {h q : ℕ} {C V : Type*} [Group C] [Finite C] [AddCommGroup V] [Finite V]
  [DistribMulAction C V] (t : Marking (2*h+1) C) (E : Zhat → ℤ) (E2 : ℤ_[2] → ℤ)

/-- The L two-relator certificate for every unramified coefficient module. -/
def lSqJacobianCertUnram (hV2 : ∀ v : V, v+v=0)
    (hwild : ∀ (i : Fin (2*h+1+1)) (v : V), t.x i • v=v)
    (htau : ∀ v : V, t.τ • v=v) (hqe : Even q) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E2 (tameRelW (2*h+1) q) (lSqW h)) where
  rowOps := nCompactUnramOps _
  colOps := []
  target := lSqUnramNormalForm h
  rowOps_invertible := by
    intro r hr
    rw [nCompactUnramOps, List.mem_singleton] at hr
    subst r
    trivial
  colOps_invertible := by simp
  verifies := by
    apply AddMonoidHom.ext
    intro a
    rw [foxApplyOps_apply, FoxColOp.listHom_nil, AddMonoidHom.id_apply, nCompactUnramOps,
      FoxRowOp.listHom_cons, FoxRowOp.listHom_nil, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, foxJacobian_apply, FoxRowOp.toHom_addSnd_apply,
      FoxNormalForm.toHom_apply]
    apply Prod.ext
    · change foxD ⇑t a E E2 (tameRelW (2*h+1) q) = _
      rw [foxD_tameRelW_unram t E E2 hV2 htau hqe, lSqUnramNormalForm,
        TameSym.splitEnd, tameUnramRow_toHom_apply]
    · change foxD ⇑t a E E2 (lSqW h) +
          (FoxCoeff.atom (TameSym.gen .sigma 1)).eval _
            (foxD ⇑t a E E2 (tameRelW (2*h+1) q)) = _
      rw [foxD_lSq_unram t E E2 hV2 hwild htau,
        foxD_tameRelW_unram t E E2 hV2 htau hqe, FoxCoeff.eval_atom_apply,
        TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_one, smul_inv_smul,
        lSqUnramNormalForm, lSingleCoeffRow_toHom_apply]
      simp only [oneSubSInv, FoxCoeff.eval_add_apply, FoxCoeff.eval_neg_apply,
        FoxCoeff.eval_one_apply, FoxCoeff.eval_atom_apply, TameSym.toEnd_gen_apply,
        Marking.apply_sigma, zpow_neg, zpow_one, neg_eq_self hV2]
      rw [show a .tau + a (coreLetter h 0) + t.σ⁻¹ • a (coreLetter h 0) + a .tau =
          (a .tau + a .tau) + (a (coreLetter h 0) + t.σ⁻¹ • a (coreLetter h 0)) by abel,
        hV2, zero_add]

omit [Finite C] [Finite V] in
private theorem lSigmaAtom_mul (pi : AddMonoid.End V) {k l : ℤ} (hkl : k+l=0) :
    (FoxCoeff.atom (TameSym.gen (Generator.sigma (n := 2*h+1)) k)).eval
        (TameSym.toEnd t pi) *
      (FoxCoeff.atom (TameSym.gen (Generator.sigma (n := 2*h+1)) l)).eval
        (TameSym.toEnd t pi) = 1 := by
  rw [← FoxCoeff.eval_comp]
  apply DFunLike.ext
  intro v
  rw [FoxCoeff.eval_comp_apply, FoxCoeff.eval_atom_apply, FoxCoeff.eval_atom_apply,
    TameSym.toEnd_gen_apply, TameSym.toEnd_gen_apply, ← mul_smul, ← zpow_add,
    hkl, zpow_zero, one_smul]
  rfl

/-- The L two-relator certificate with fixed-point-free odd tame inertia. -/
def lSqJacobianCertRam (hV2 : ∀ v : V, v+v=0)
    (hwild : ∀ (i : Fin (2*h+1+1)) (v : V), t.x i • v=v)
    (hfpf : ∀ v : V, t.τ • v=v → v=0)
    (hodd : ∀ v : V, powOmega2 t.τ • v=v)
    (hrel : conjR t.τ t.σ = t.τ^q) :
    FoxCertificate (TameSym.ramifiedEnd (A := V) t)
      (foxJacobian ⇑t E E2 (tameRelW (2*h+1) q) (lSqW h)) where
  rowOps := []
  colOps := lSqRamOps h
  target := lSqRamNormalForm h q
  rowOps_invertible := by simp
  colOps_invertible := by
    intro c hc
    rw [lSqRamOps, List.mem_singleton] at hc
    subst c
    exact ⟨lSigmaAtom_mul t 0 (by ring), lSigmaAtom_mul t 0 (by ring)⟩
  verifies := by
    apply AddMonoidHom.ext
    intro a
    rw [foxApplyOps_apply, FoxRowOp.listHom_nil, AddMonoidHom.id_apply, lSqRamOps,
      FoxColOp.listHom_cons, FoxColOp.listHom_nil, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, foxJacobian_apply, FoxNormalForm.toHom_apply]
    set b := FoxColOp.toHom (TameSym.ramifiedEnd (A := V) t)
      (.scale (coreLetter h 0) (.atom (.gen .sigma 1)) (.atom (.gen .sigma (-1)))) a with hb
    have hbt : b .tau = a .tau := by
      rw [hb, FoxColOp.toHom_scale_apply, if_neg (tau_ne_coreLetter_zero h)]
    have hbs : b .sigma = a .sigma := by
      rw [hb, FoxColOp.toHom_scale_apply, if_neg (sigma_ne_coreLetter_zero h)]
    have hbx : b (coreLetter h 0) = t.σ • a (coreLetter h 0) := by
      rw [hb, FoxColOp.toHom_scale_apply, if_pos rfl, FoxCoeff.eval_atom_apply,
        TameSym.toEnd_gen_apply, Marking.apply_sigma, zpow_one]
    apply Prod.ext
    · change foxD ⇑t b E E2 (tameRelW (2*h+1) q) = _
      rw [foxD_tameRelW_of_tameRel t E E2 hrel, hbt, hbs, lSqRamNormalForm,
        TameSym.ramifiedEnd, tameRow_toHom_apply]
      simp only [smul_add, smul_sub]
      abel
    · change foxD ⇑t b E E2 (lSqW h) =
          (FoxRowNormalForm.single (coreLetter h 0)).toHom (TameSym.ramifiedEnd t) a
      rw [foxD_lSq_ram t E E2 hV2 hwild hfpf hodd, hbx, inv_smul_smul,
        FoxRowNormalForm.single_toHom_apply]

/-- The degenerate scalar two-relator certificate, with its zero wild row explicit. -/
def lSqJacobianCertScalar (hV2 : ∀ v : V, v+v=0)
    (hwild : ∀ (i : Fin (2*h+1+1)) (v : V), t.x i • v=v)
    (htau : ∀ v : V, t.τ • v=v) (hsigma : ∀ v : V, t.σ • v=v) (hqe : Even q) :
    FoxCertificate (TameSym.splitEnd (A := V) t)
      (foxJacobian ⇑t E E2 (tameRelW (2*h+1) q) (lSqW h)) where
  rowOps := [.addSnd (.neg .one)]
  colOps := []
  target := ⟨.single .tau, ⟨fun _ => .zero⟩⟩
  rowOps_invertible := by intro r hr; simp only [List.mem_singleton] at hr; subst r; trivial
  colOps_invertible := by simp
  verifies := by
    have hsinv : ∀ v : V, t.σ⁻¹ • v=v := fun v => inv_smul_eq_iff.mpr (hsigma v).symm
    apply AddMonoidHom.ext
    intro a
    rw [foxApplyOps_apply, FoxColOp.listHom_nil, AddMonoidHom.id_apply,
      FoxRowOp.listHom_cons, FoxRowOp.listHom_nil, AddMonoidHom.comp_apply,
      AddMonoidHom.id_apply, foxJacobian_apply, FoxRowOp.toHom_addSnd_apply,
      FoxNormalForm.toHom_apply, foxD_tameRelW_unram t E E2 hV2 htau hqe,
      foxD_lSq_split t E E2 hV2 hwild htau hsigma, hsinv]
    simp only [FoxRowNormalForm.single_toHom_apply, FoxCoeff.eval_neg_apply,
      FoxCoeff.eval_one_apply]
    apply Prod.ext
    · rfl
    · change a .tau + -(a .tau) = ∑ _g : Generator (2*h+1), (0 : V)
      simp

end
end GQ2.Dyadic.Certificates.LSq
