import GQ2.GaussZReduction
import GQ2.IotaBridge
import GQ2.ShapiroLedger
import GQ2.UnramifiedModel

/-!
# P-16d6e4a: the local (83)-evaluation — the `VCocycle ↔ H¹` transport and the pinned Gauss value

Layer (II) of the source-Gauss residue (design `docs/p16d6e4a-evaluation-design.md` §1): the
descended base-determinant form `Q̄⁰` on `Z¹_{Γ,ρ}(V) ⧸ B¹` is, over `Γ = G_ℚ₂`, carried by an
explicit bijection onto `(H¹(G_ℚ₂, V), Q⁰_loc)` — whose Gauss sum §6.2/§6.3 already computed
(`prop_6_18_{unramified,ramified}`, both sorry-free).  Pieces:

* **(A) the `Z¹`-bridge** `toZ1`/`ofZ1` (the shared e3 bridge as reusable declarations): a
  `VCocycle` IS a continuous 1-cocycle once the `Γ`-action on `V` factors through `ρ'`
  (`hcomp`); continuity crosses the topology-free `V` through the `iV ∘ ofAdd` embedding.
* **(B) the quotient bijection** `h1OfVQuot : (Z¹ ⧸ B¹) → H¹(Γ, V)` — `vCob`-cosets map to
  `dZero`-cosets; bijective.
* **(C′) the form-compatibility** `QZeroBar_eq_Q0loc`: `Q̄⁰ = Q⁰_loc ∘ Φ`, by the landed
  `iotaB_eq_iotaF` bridge (`IotaBridge`) + the `B¹`-shift invariance of the graph pullback
  (`GaussZReduction.graphPullback_shift_mem_B2`) absorbing the `Quotient.out` representative.
* **(D)/(E) the pinned value** `sum_sign_Q0loc_{unramified,ramified}`:
  `∑ᶠ sign(Q⁰_loc) = ∓2^m` from `prop_6_18` + `gaussSum_eq` + `card_H1_eq_card_of_simple`.

The e7 assembly composes these with `GaussZReduction.gaussZ_reduction` to discharge the local
`GaussZResidue` (`hGaussZF`).  Axioms: (A)/(B)/(C′) are std-3; (D)/(E) carry `prop_6_18`'s
budget (B6 via the `D` parameter, B7).
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh SectionSix

section Transport

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

/-! ### (A) the `Z¹`-bridge, as reusable declarations (the shared e3 bridge) -/

section Bridge

variable {DD : DescData D}
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod]
variable [DistribMulAction Γ DD.Vmod]

/-- **The `VCocycle → Z¹` bridge** (P-16d6e4a (A), the e3 bridge as a declaration): under an
action identification `γ • v = ρ'(γ) • v`, a crossed `V`-cocycle is a continuous 1-cocycle.
Continuity crosses the topology-free `V` through the injective `iV ∘ ofAdd` into the discrete
`Bg ⧸ T` (`IsLocallyConstant.desc`). -/
noncomputable def toZ1 (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (c : VCocycle DD ρ) : ↥(Z1 Γ DD.Vmod) :=
  ⟨c.c, by
    refine mem_Z1_iff.mpr ⟨?_, ?_⟩
    · have hinj : Function.Injective
          (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
        fun a a' haa' => iV_ofAdd_inj DD haa'
      have hlc : IsLocallyConstant
          (fun γ => iV DD (Multiplicative.ofAdd (c.c γ))) :=
        (IsLocallyConstant.iff_continuous _).mpr c.cont
      exact (IsLocallyConstant.desc (α := DD.Vmod) c.c
        (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) hlc hinj).continuous
    · intro γ δ
      rw [c.crossed γ δ, ← hcomp γ (c.c δ)]⟩

@[simp] theorem toZ1_c (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (c : VCocycle DD ρ) : ((toZ1 hcomp c : ↥(Z1 Γ DD.Vmod)) : Γ → DD.Vmod) = c.c := rfl

/-- The inverse direction: a continuous 1-cocycle is a crossed `V`-cocycle. -/
noncomputable def ofZ1 (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (z : ↥(Z1 Γ DD.Vmod)) : VCocycle DD ρ where
  c := z.1
  cont := by
    have hc : Continuous (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      continuous_of_discreteTopology
    exact hc.comp (mem_Z1_iff.mp z.2).1
  crossed := fun γ δ => by
    have hz := (mem_Z1_iff.mp z.2).2 γ δ
    rw [hz, hcomp γ (z.1 δ)]

theorem toZ1_ofZ1 (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (z : ↥(Z1 Γ DD.Vmod)) : toZ1 hcomp (ofZ1 hcomp z) = z := Subtype.ext rfl

theorem toZ1_surjective (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v) :
    Function.Surjective (toZ1 hcomp) := fun z => ⟨ofZ1 hcomp z, toZ1_ofZ1 hcomp z⟩

/-! ### (B) the quotient bijection `(Z¹ ⧸ B¹) → H¹` -/

/-- The `H¹`-class equality criterion, in `H1mk` vocabulary (`H1` is a semireducible `def`, so
the quotient coercion does not elaborate against it; this is the `show`-unfolded form). -/
theorem H1mk_eq_iff {M : Type*} [AddCommGroup M] [TopologicalSpace M]
    [IsTopologicalAddGroup M] [DistribMulAction Γ M] (x y : ↥(Z1 Γ M)) :
    H1mk Γ M x = H1mk Γ M y ↔ x - y ∈ (B1 Γ M).addSubgroupOf (Z1 Γ M) := by
  show (↑x : Z1 Γ M ⧸ (B1 Γ M).addSubgroupOf (Z1 Γ M)) = ↑y ↔ _
  exact QuotientAddGroup.eq_iff_sub_mem

/-- The `vCob ↦ dZero` correspondence on carriers. -/
theorem toZ1_vCob_c (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (w : DD.Vmod) : (vCob DD ρ w).c = dZero Γ DD.Vmod w := by
  funext γ
  show rho0 DD ρ γ • w - w = γ • w - w
  rw [hcomp γ w]

/-- **The quotient map** `Φ : Z¹_{Γ,ρ}(V) ⧸ B¹ → H¹(Γ, V)` (P-16d6e4a (B)). -/
noncomputable def h1OfVQuot (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (x : VCocycle DD ρ ⧸ vCobRange DD ρ) : H1 Γ DD.Vmod :=
  Quotient.liftOn' x (fun c => H1mk Γ DD.Vmod (toZ1 hcomp c)) fun a b hab => by
    rw [QuotientAddGroup.leftRel_apply] at hab
    obtain ⟨w, hw⟩ := hab
    rw [vCobHom_apply] at hw
    have hb : b = a + vCob DD ρ w := by rw [hw]; abel
    have hbγ : ∀ γ : Γ, b.c γ = a.c γ + (rho0 DD ρ γ • w - w) := by
      intro γ; rw [hb]; rfl
    symm
    rw [H1mk_eq_iff, AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.mpr ⟨w, ?_⟩
    funext γ
    have h1 : ((toZ1 hcomp b - toZ1 hcomp a : ↥(Z1 Γ DD.Vmod)) : Γ → DD.Vmod) γ
        = b.c γ - a.c γ := rfl
    rw [h1, hbγ γ]
    show γ • w - w = a.c γ + (rho0 DD ρ γ • w - w) - a.c γ
    rw [hcomp γ w]
    abel

@[simp] theorem h1OfVQuot_mk (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v)
    (c : VCocycle DD ρ) :
    h1OfVQuot hcomp (QuotientAddGroup.mk c) = H1mk Γ DD.Vmod (toZ1 hcomp c) := rfl

theorem h1OfVQuot_surjective
    (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v) :
    Function.Surjective (h1OfVQuot hcomp) := by
  intro y
  induction y using QuotientAddGroup.induction_on with
  | H z =>
    exact ⟨QuotientAddGroup.mk (ofZ1 hcomp z), by
      rw [h1OfVQuot_mk, toZ1_ofZ1]; rfl⟩

theorem h1OfVQuot_injective
    (hcomp : ∀ (γ : Γ) (v : DD.Vmod), γ • v = rho0 DD ρ γ • v) :
    Function.Injective (h1OfVQuot hcomp) := by
  intro x x' h
  induction x using QuotientAddGroup.induction_on with
  | H a =>
    induction x' using QuotientAddGroup.induction_on with
    | H b =>
      rw [h1OfVQuot_mk, h1OfVQuot_mk, H1mk_eq_iff, AddSubgroup.mem_addSubgroupOf] at h
      obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp h
      -- `a = b + vCob w`
      have hab : a = b + vCob DD ρ w := by
        refine VCocycle.ext ?_
        funext γ
        have hγ : (dZero Γ DD.Vmod w) γ = a.c γ - b.c γ := by
          have h1 : ((toZ1 hcomp a - toZ1 hcomp b : ↥(Z1 Γ DD.Vmod)) : Γ → DD.Vmod) γ
              = a.c γ - b.c γ := rfl
          rw [← h1]
          exact congrFun hw γ
        have hγ' : γ • w - w = a.c γ - b.c γ := hγ
        show a.c γ = b.c γ + (rho0 DD ρ γ • w - w)
        rw [← hcomp γ w, hγ']
        abel
      rw [QuotientAddGroup.eq_iff_sub_mem]
      refine AddMonoidHom.mem_range.mpr ⟨w, ?_⟩
      rw [vCobHom_apply, hab]
      abel

end Bridge

/-! ### (C′) the form compatibility over `G_ℚ₂` -/

section FormCompat

variable {DD : DescData D} {ρM : ContinuousMonoidHom AbsGalQ2 (Bg ⧸ D.M)}
variable [TopologicalSpace DD.Vmod] [DiscreteTopology DD.Vmod] [Finite DD.Vmod]
variable [DistribMulAction AbsGalQ2 DD.Vmod] [ContinuousSMul AbsGalQ2 DD.Vmod]
variable [TopologicalSpace DD.C0] [DiscreteTopology DD.C0] [Finite DD.C0]

/-- **The form compatibility** (P-16d6e4a (C′)): under the transport `Φ = h1OfVQuot`, the
descended base determinant form `Q̄⁰` is `Q⁰_loc` — the abstract `iotaB`-obstruction and the
Tate-invariant obstruction agree (`iotaB_eq_iotaF`), and the `Quotient.out` representative on
the `H¹` side differs from the transported cocycle by a `B¹`-shift, which the graph pullback
absorbs mod `B²` (`graphPullback_shift_mem_B2`). -/
theorem QZeroBar_eq_Q0loc (D6 : TateDuality 2)
    (hcomp : ∀ (γ : AbsGalQ2) (v : DD.Vmod), γ • v = rho0 DD ρM γ • v)
    (ρc : ContinuousMonoidHom AbsGalQ2 DD.C0) (hρc : ∀ γ, ρc γ = rho0 DD ρM γ)
    (htriv : ∀ (γ : AbsGalQ2) (m : ZMod 2), γ • m = m)
    (x : VCocycle DD ρM ⧸ vCobRange DD ρM) :
    QZeroBar DD ρM htriv x = Q0loc D6 DD.dat ρc (h1OfVQuot hcomp x) := by
  induction x using QuotientAddGroup.induction_on with
  | H c =>
    rw [QZeroBar_mk, h1OfVQuot_mk]
    -- the `out` representative differs from `toZ1 c` by a `B¹`-element
    have hout : H1mk AbsGalQ2 DD.Vmod (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c)))
        = H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c) := by
      show Quotient.mk'' (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c)))
        = H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c)
      exact Quotient.out_eq' _
    rw [H1mk_eq_iff, AddSubgroup.mem_addSubgroupOf] at hout
    obtain ⟨w, hw⟩ := AddMonoidHom.mem_range.mp hout
    -- its carrier is `(c + vCob w).c`
    have hz₀c : ((Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
        : ↥(Z1 AbsGalQ2 DD.Vmod)) : AbsGalQ2 → DD.Vmod) = (c + vCob DD ρM w).c := by
      funext γ
      have hγ : (dZero AbsGalQ2 DD.Vmod w) γ
          = (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
              : ↥(Z1 AbsGalQ2 DD.Vmod)).1 γ - c.c γ := by
        have hcoe : ((Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
            - toZ1 hcomp c : ↥(Z1 AbsGalQ2 DD.Vmod)) : AbsGalQ2 → DD.Vmod) γ
            = (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
                : ↥(Z1 AbsGalQ2 DD.Vmod)).1 γ - c.c γ := rfl
        rw [← hcoe]
        exact congrFun hw γ
      have hγ' : γ • w - w = (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
          : ↥(Z1 AbsGalQ2 DD.Vmod)).1 γ - c.c γ := hγ
      show (Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c))
          : ↥(Z1 AbsGalQ2 DD.Vmod)).1 γ = c.c γ + (rho0 DD ρM γ • w - w)
      rw [← hcomp γ w, hγ']
      abel
    -- assemble through the landed bridges
    show QZero DD ρM c = iotaF D6 (H2ofFun AbsGalQ2 (graphPullback DD.dat (⇑ρc)
      ((Quotient.out (H1mk AbsGalQ2 DD.Vmod (toZ1 hcomp c)) : ↥(Z1 AbsGalQ2 DD.Vmod)) : _)))
    have hρfun : (⇑ρc : AbsGalQ2 → DD.C0) = fun γ => rho0 DD ρM γ := funext hρc
    rw [hρfun, hz₀c,
      ShapiroLedger.H2ofFun_eq_of_sub_mem_B2 (graphPullback_shift_mem_B2 htriv c w),
      ← iotaB_eq_iotaF D6 (graphPullback_mem_Z2_of_cocycle htriv c)]
    rfl

end FormCompat

end Transport

/-! ### (D)/(E) the pinned Gauss value on `(H¹(G_ℚ₂, V), Q⁰_loc)` -/

section Pinned

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- The `C`-action moves some vector (else `V ≅ 𝔽₂`, contradicting `#V = 2^{2m}`, `m ≥ 1`) —
the mover block of `prop_6_18_unramified`, extracted. -/
theorem exists_smul_ne_of_card (hsimple : ∀ W : AddSubgroup V,
      (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0) (hV2 : ∀ v : V, v + v = 0)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∃ (h₀ : C) (v : V), h₀ • v ≠ v := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨v, hv⟩ := hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hord : addOrderOf v = 2 := addOrderOf_eq_prime (by rw [two_nsmul]; exact hV2 v) hv
  have htop : AddSubgroup.zmultiples v = ⊤ := by
    refine (hsimple _ (fun h w hw => by rw [hcon]; exact hw)).resolve_left (fun h0 => hv ?_)
    have hmem : v ∈ AddSubgroup.zmultiples v := AddSubgroup.mem_zmultiples v
    rw [h0, AddSubgroup.mem_bot] at hmem; exact hmem
  have hcard2 : Nat.card V = 2 := by
    have h1 : Nat.card ↥(AddSubgroup.zmultiples v) = 2 := by rw [Nat.card_zmultiples, hord]
    rwa [htop, Nat.card_congr AddSubgroup.topEquiv.toEquiv] at h1
  rw [hcard] at hcard2
  have h4 : (4 : ℕ) ≤ 2 ^ (2 * m) :=
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- The signed-sum extraction shared by both cases: with `zeroCount(Q⁰_loc)` and
`#H¹ = 2^{2m}` known, `∑ᶠ sign(Q⁰_loc) = 2·zeroCount − 2^{2m}`. -/
theorem finsum_sign_eq (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (zc : ℕ) (hzc : zeroCount (Q0loc D dat ρ (V := V)) = zc)
    {m : ℕ} (hH1 : Nat.card (H1 AbsGalQ2 V) = 2 ^ (2 * m)) :
    ∑ᶠ y : H1 AbsGalQ2 V, sign (Q0loc D dat ρ y) = 2 * (zc : ℤ) - 2 ^ (2 * m) := by
  classical
  haveI : Finite (H1 AbsGalQ2 V) := Foundations.finite_H1 V
  haveI : Fintype (H1 AbsGalQ2 V) := Fintype.ofFinite _
  rw [finsum_eq_sum_of_fintype]
  -- bridge the two `sign`s (`SectionEight.sign` in the residue, `QuadraticFp2.sign` in
  -- `gaussSum`), then evaluate through `gaussSum_eq`
  have hsign : ∀ s : ZMod 2, sign s = QuadraticFp2.sign s := by decide
  calc (∑ y : H1 AbsGalQ2 V, sign (Q0loc D dat ρ y))
      = ∑ y : H1 AbsGalQ2 V, QuadraticFp2.sign (Q0loc D dat ρ y) :=
        Finset.sum_congr rfl fun y _ => hsign _
    _ = 2 * (zc : ℤ) - 2 ^ (2 * m) := by
        have hge := gaussSum_eq (V := H1 AbsGalQ2 V) (Q0loc D dat ρ)
        unfold QuadraticFp2.gaussSum at hge
        rw [hge, hzc, ← Nat.card_eq_fintype_card, hH1]
        push_cast
        ring

/-- **The pinned local Gauss value, unramified** (P-16d6e4a (D)/(E)):
`∑ᶠ sign(Q⁰_loc) = −2^m` — `prop_6_18_unramified`'s zero count through `gaussSum_eq`. -/
theorem sum_sign_Q0loc_unramified (D : TateDuality 2) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hV : ∃ v : V, v ≠ 0)
    (hunram : ∀ v : V, c tameTau • v = v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ y : H1 AbsGalQ2 V, sign (Q0loc D dat ρ y) = -(2 ^ m : ℤ) := by
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  have hρsurj : Function.Surjective ⇑ρ := fun y => by
    obtain ⟨t, ht⟩ := hc y
    obtain ⟨g, hg⟩ := B.tameF_surjective t
    exact ⟨g, by rw [hfac, hg, ht]⟩
  obtain ⟨h₀, hmoves⟩ := exists_smul_ne_of_card hsimple hV hV2 m hm hcard
  have hH1 : Nat.card (H1 AbsGalQ2 V) = 2 ^ (2 * m) := by
    rw [DeepPart.card_H1_eq_card_of_simple V D ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves
      q hq hns hinv hV2, hcard]
  have hzc : zeroCount (Q0loc D dat ρ (V := V)) = 2 ^ (2 * m - 1) - 2 ^ (m - 1) :=
    UnramifiedModel.prop_6_18_unramified D B c hc ρ hfac hρ hfaith hsimple hV hunram
      q hq hns hinv dat hdat m hm hcard
  rw [finsum_sign_eq D dat ρ _ hzc hH1]
  have hle : (2 : ℕ) ^ (m - 1) ≤ 2 ^ (2 * m - 1) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast [Nat.cast_sub hle]
  linarith [e1, e2]

/-- **The pinned local Gauss value, ramified** (P-16d6e4a (D)/(E)):
`∑ᶠ sign(Q⁰_loc) = +2^m` — `prop_6_18_ramified`'s zero count through `gaussSum_eq`. -/
theorem sum_sign_Q0loc_ramified (D : TateDuality 2) (B : BoundaryMaps)
    (c : ContinuousMonoidHom Ttame C) (hc : Function.Surjective ⇑c)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hfac : ∀ g, ρ g = c (B.tameF g))
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hfaith : ∀ h : C, (∀ v : V, h • v = v) → h = 1)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hram : ∃ v : V, c tameTau • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q) (hinv : IsInvariant C q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    ∑ᶠ y : H1 AbsGalQ2 V, sign (Q0loc D dat ρ y) = (2 ^ m : ℤ) := by
  have hρsurj : Function.Surjective ⇑ρ := fun y => by
    obtain ⟨t, ht⟩ := hc y
    obtain ⟨g, hg⟩ := B.tameF_surjective t
    exact ⟨g, by rw [hfac, hg, ht]⟩
  have hV2 : ∀ v : V, v + v = 0 := DeepPart.exp_two_of_simple_of_card hsimple m hm hcard
  obtain ⟨v₀, hv₀⟩ := hram
  have hH1 : Nat.card (H1 AbsGalQ2 V) = 2 ^ (2 * m) := by
    rw [DeepPart.card_H1_eq_card_of_simple V D ρ.toMonoidHom hρsurj hρ hsimple (c tameTau)
      ⟨v₀, hv₀⟩ q hq hns hinv hV2, hcard]
  have hzc : zeroCount (Q0loc D dat ρ (V := V)) = 2 ^ (2 * m - 1) + 2 ^ (m - 1) :=
    DeepPart.prop_6_18_ramified D B c hc ρ hfac hρ hfaith hsimple ⟨v₀, hv₀⟩
      q hq hns hinv dat hdat m hm hcard
  rw [finsum_sign_eq D dat ρ _ hzc hH1]
  have e1 : (2 : ℤ) ^ (2 * m) = 2 * 2 ^ (2 * m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have e2 : (2 : ℤ) ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  push_cast
  linarith [e1, e2]

end Pinned

end AffineTLift

end SectionEight

end GQ2
