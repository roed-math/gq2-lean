import GQ2.VLiftCount

/-!
# The semidirect atom calculus and the `ω_χ`-decomposition

Split off from `GQ2.KeystoneDelta` (design §§1–2).  This file provides:

* the **raw semidirect calculus** on `V × C₀` (`pmul`, `pone`, associativity) with the
  transported product maps `jmap`/`Jmap` and their multiplicativity;
* the three **`T`-valued defect atoms** `mDef`/`conjDef`/`uDef` and the product formula
  `JDefT = conjDef · uDef · mDef`, with the `mDef`/`conjDef` atom identities;
* the **`ω_χ`-decomposition** `χ ∘ JDef = kappa0 (datχ χ) + inflScalar (eχ χ)` via the
  equivariant zero-form factor-set datum `datChi`.

See `GQ2.KeystoneDelta` for the umbrella module docstring.
-/

namespace GQ2

namespace SectionEight

namespace AffineTLift

open CentralObstruction QuadraticFp2 ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] [TopologicalSpace Bg] [DiscreteTopology Bg]
  {D : RadicalCoverData Bg}

/-! ## The raw semidirect calculus on `V × C₀` -/

section Semidirect

variable {DD : DescData D}

/-- The semidirect product on raw pairs (`lemma_6_22`'s convention). -/
def pmul (p q : DD.Vmod × DD.C0) : DD.Vmod × DD.C0 :=
  (p.1 + p.2 • q.1, p.2 * q.2)

/-- The semidirect identity. -/
def pone : DD.Vmod × DD.C0 := (0, 1)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pmul_assoc (p q r : DD.Vmod × DD.C0) :
    pmul (pmul p q) r = pmul p (pmul q r) := by
  simp [pmul, smul_add, mul_smul, add_assoc, mul_assoc]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pone_pmul (p : DD.Vmod × DD.C0) : pmul pone p = p := by
  simp [pmul, pone]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pmul_pone (p : DD.Vmod × DD.C0) : pmul p pone = p := by
  simp [pmul, pone]

variable (DD) in
/-- The transported product map into `Q = Bg/T`: `jmap (v, cc) = iV(v)·σ(cc)`. -/
noncomputable def jmap (σ : DD.C0 →* Bg ⧸ D.T) (p : DD.Vmod × DD.C0) : Bg ⧸ D.T :=
  iV DD (Multiplicative.ofAdd p.1) * σ p.2

variable {σ : DD.C0 →* Bg ⧸ D.T} (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `jmap` is multiplicative for the semidirect product. -/
theorem jmap_mul (p q : DD.Vmod × DD.C0) :
    jmap DD σ p * jmap DD σ q = jmap DD σ (pmul p q) := by
  unfold jmap pmul
  calc iV DD (Multiplicative.ofAdd p.1) * σ p.2 * (iV DD (Multiplicative.ofAdd q.1) * σ q.2)
      = iV DD (Multiplicative.ofAdd p.1) * (σ p.2 * iV DD (Multiplicative.ofAdd q.1)) * σ q.2 := by
        group
    _ = iV DD (Multiplicative.ofAdd p.1)
          * (iV DD (Multiplicative.ofAdd (p.2 • q.1)) * σ p.2) * σ q.2 := by
        rw [sigma_iV_comm DD σ hσ p.2 q.1]
    _ = iV DD (Multiplicative.ofAdd (p.1 + p.2 • q.1)) * σ (p.2 * q.2) := by
        rw [iV_ofAdd_add, map_mul]
        group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem jmap_pone : jmap DD σ pone = 1 := by
  unfold jmap pone
  show iV DD (Multiplicative.ofAdd (0 : DD.Vmod)) * σ 1 = 1
  rw [ofAdd_zero, map_one, map_one, one_mul]

end Semidirect

/-! ## The pointwise product lift `J` and the defect atoms -/

section Atoms

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)

/-- The pointwise product lift into `Bg`: `J (v, cc) = mV(v)·uσ(cc)`. -/
noncomputable def Jmap (p : DD.Vmod × DD.C0) : Bg := (S.mV p.1 : Bg) * S.uσ p.2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem piT_Jmap (p : DD.Vmod × DD.C0) : piT (D := D) (Jmap S p) = jmap DD σ p := by
  unfold Jmap jmap
  rw [map_mul, piT_mV, S.piT_uσ]

variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- The `J`-defect lands in `T`. -/
theorem Jmap_defect_mem (p q : DD.Vmod × DD.C0) :
    Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹ ∈ D.T := by
  have h : piT (D := D) (Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, piT_Jmap, piT_Jmap, piT_Jmap, jmap_mul hσ, mul_inv_cancel]
  rwa [piT, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

/-- **The `J`-defect** as a `T`-element. -/
noncomputable def JDefT (p q : DD.Vmod × DD.C0) : ↥D.T :=
  ⟨Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹, Jmap_defect_mem S hσ p q⟩

/-! ### The three atoms -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `mV`-additivity defect `mDef v w = mV(v)·mV(w)·mV(v+w)⁻¹ ∈ T`. -/
theorem mDef_mem (v w : DD.Vmod) :
    (S.mV v : Bg) * S.mV w * ((S.mV (v + w) : Bg))⁻¹ ∈ D.T := by
  have h : DD.descend (S.mV v * S.mV w * (S.mV (v + w))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, S.descend_mV, S.descend_mV, S.descend_mV, ← ofAdd_add,
      mul_inv_cancel]
  exact (DD.hdesc_ker _).mp h

variable (DD) in
/-- `mDef v w := mV(v)·mV(w)·mV(v+w)⁻¹`, the `mV`-additivity defect. -/
noncomputable def mDef (S : CountSections DD σ) (v w : DD.Vmod) : ↥D.T :=
  ⟨(S.mV v : Bg) * S.mV w * ((S.mV (v + w) : Bg))⁻¹, mDef_mem S v w⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- The conjugation defect `conjDef cc w = uσ(cc)·mV(w)·uσ(cc)⁻¹·mV(cc•w)⁻¹ ∈ T`. -/
theorem conjDef_mem (cc : DD.C0) (w : DD.Vmod) :
    S.uσ cc * (S.mV w : Bg) * (S.uσ cc)⁻¹ * ((S.mV (cc • w) : Bg))⁻¹ ∈ D.T := by
  have h : piT (D := D) (S.uσ cc * (S.mV w : Bg) * (S.uσ cc)⁻¹ * ((S.mV (cc • w) : Bg))⁻¹)
      = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, piT_mV, piT_mV, S.piT_uσ,
      show σ cc * iV DD (Multiplicative.ofAdd w) * (σ cc)⁻¹
        = iV DD (Multiplicative.ofAdd (cc • w)) from sigma_conj_iV DD σ hσ cc w,
      mul_inv_cancel]
  rwa [piT, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

variable (DD) in
/-- `conjDef cc w`, the conjugation defect of the sections. -/
noncomputable def conjDef (S : CountSections DD σ)
    (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (cc : DD.C0) (w : DD.Vmod) : ↥D.T :=
  ⟨S.uσ cc * (S.mV w : Bg) * (S.uσ cc)⁻¹ * ((S.mV (cc • w) : Bg))⁻¹, conjDef_mem S hσ cc w⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `uσ`-multiplicativity defect `uDef cc dd = uσ(cc)·uσ(dd)·uσ(cc·dd)⁻¹ ∈ T` — the class
`e` of Lemma 8.7. -/
theorem uDef_mem (cc dd : DD.C0) : S.uσ cc * S.uσ dd * (S.uσ (cc * dd))⁻¹ ∈ D.T := by
  have h : piT (D := D) (S.uσ cc * S.uσ dd * (S.uσ (cc * dd))⁻¹) = 1 := by
    rw [map_mul, map_mul, map_inv, S.piT_uσ, S.piT_uσ, S.piT_uσ, ← map_mul σ, mul_inv_cancel]
  rwa [piT, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h

variable (DD) in
/-- `uDef cc dd`, the base extension class `e` at cochain level. -/
noncomputable def uDef (S : CountSections DD σ) (cc dd : DD.C0) : ↥D.T :=
  ⟨S.uσ cc * S.uσ dd * (S.uσ (cc * dd))⁻¹, uDef_mem S cc dd⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `M` commutes with `T` elementwise (commutation form of `M_cent_T`). -/
theorem M_comm_T {m t : Bg} (hm : m ∈ D.M) (ht : t ∈ D.T) : m * t = t * m := by
  have h := M_cent_T (D := D) hm ht
  calc m * t = m * t * m⁻¹ * m := by group
    _ = t * m := by rw [h]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The product formula**: the `J`-defect is the all-`T` product
`conjDef · uDef · mDef` (`M` abelian, `T` centralized by `M`). -/
theorem JDefT_eq (p q : DD.Vmod × DD.C0) :
    JDefT S hσ p q
      = conjDef DD S hσ p.2 q.1 * uDef DD S p.2 q.2 * mDef DD S p.1 (p.2 • q.1) := by
  apply Subtype.ext
  show Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹
    = (S.uσ p.2 * (S.mV q.1 : Bg) * (S.uσ p.2)⁻¹ * ((S.mV (p.2 • q.1) : Bg))⁻¹)
      * (S.uσ p.2 * S.uσ q.2 * (S.uσ (p.2 * q.2))⁻¹)
      * ((S.mV p.1 : Bg) * (S.mV (p.2 • q.1) : Bg) * ((S.mV (p.1 + p.2 • q.1) : Bg))⁻¹)
  -- names for the atoms
  set A := (S.mV p.1 : Bg) with hA
  set B := (S.mV q.1 : Bg) with hB
  set U := S.uσ p.2 with hU
  set W := S.uσ q.2 with hW
  set X := (S.mV (p.2 • q.1) : Bg) with hX
  set Y := (S.mV (p.1 + p.2 • q.1) : Bg) with hY
  set Z := S.uσ (p.2 * q.2) with hZ
  have hconjT : U * B * U⁻¹ * X⁻¹ ∈ D.T := conjDef_mem S hσ p.2 q.1
  have huT : U * W * Z⁻¹ ∈ D.T := uDef_mem S p.2 q.2
  have hAM : A ∈ D.M := (S.mV p.1).2
  have hXM : X ∈ D.M := (S.mV (p.2 • q.1)).2
  show A * U * (B * W) * (Y * Z)⁻¹
    = (U * B * U⁻¹ * X⁻¹) * (U * W * Z⁻¹) * (A * X * Y⁻¹)
  calc A * U * (B * W) * (Y * Z)⁻¹
      = A * ((U * B * U⁻¹) * (U * W * Z⁻¹)) * Y⁻¹ := by group
    _ = A * ((U * B * U⁻¹ * X⁻¹) * (X * (U * W * Z⁻¹))) * Y⁻¹ := by group
    _ = A * ((U * B * U⁻¹ * X⁻¹) * ((U * W * Z⁻¹) * X)) * Y⁻¹ := by
        rw [M_comm_T hXM huT]
    _ = (A * (U * B * U⁻¹ * X⁻¹)) * (U * W * Z⁻¹) * (X * Y⁻¹) := by group
    _ = ((U * B * U⁻¹ * X⁻¹) * A) * (U * W * Z⁻¹) * (X * Y⁻¹) := by
        rw [M_comm_T hAM hconjT]
    _ = (U * B * U⁻¹ * X⁻¹) * (A * (U * W * Z⁻¹)) * (X * Y⁻¹) := by group
    _ = (U * B * U⁻¹ * X⁻¹) * ((U * W * Z⁻¹) * A) * (X * Y⁻¹) := by
        rw [M_comm_T hAM huT]
    _ = (U * B * U⁻¹ * X⁻¹) * (U * W * Z⁻¹) * (A * X * Y⁻¹) := by group

/-! ### The `mDef`-atom identities (through the abelian `↥D.M`) -/

/-- `↥D.M` is commutative (file-local instance — the underlying `Mul` is definitionally the
subgroup one, so no diamond escapes this leaf). -/
local instance commGroupM : CommGroup ↥D.M :=
  { (inferInstance : Group ↥D.M) with
    mul_comm := fun a b => Subtype.ext (D.hcomm _ a.2 _ b.2) }

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem mDef_symm (v w : DD.Vmod) : mDef DD S v w = mDef DD S w v := by
  apply Subtype.ext
  show (S.mV v : Bg) * S.mV w * ((S.mV (v + w) : Bg))⁻¹
    = (S.mV w : Bg) * S.mV v * ((S.mV (w + v) : Bg))⁻¹
  rw [D.hcomm _ (S.mV v).2 _ (S.mV w).2, add_comm]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem mDef_self (v : DD.Vmod) : mDef DD S v v = 1 := by
  apply Subtype.ext
  show (S.mV v : Bg) * S.mV v * ((S.mV (v + v) : Bg))⁻¹ = 1
  rw [Vmod_exp2 DD v, S.mV_zero, D.helem _ (S.mV v).2, OneMemClass.coe_one, inv_one, mul_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem mDef_zero_left (w : DD.Vmod) : mDef DD S 0 w = 1 := by
  apply Subtype.ext
  show (S.mV 0 : Bg) * S.mV w * ((S.mV (0 + w) : Bg))⁻¹ = 1
  rw [zero_add, S.mV_zero, OneMemClass.coe_one, one_mul, mul_inv_cancel]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem mDef_zero_right (v : DD.Vmod) : mDef DD S v 0 = 1 := by
  rw [mDef_symm, mDef_zero_left]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `mDef`-cocycle identity (the `f_cocycle` field of the zero-form factor set). -/
theorem mDef_cocycle (v w x : DD.Vmod) :
    mDef DD S (v + w) x * mDef DD S v w = mDef DD S v (w + x) * mDef DD S w x := by
  -- prove it in the commutative `↥D.M`, then push the coercion
  have hM : (S.mV (v + w) * S.mV x * (S.mV (v + w + x))⁻¹)
        * (S.mV v * S.mV w * (S.mV (v + w))⁻¹)
      = (S.mV v * S.mV (w + x) * (S.mV (v + (w + x)))⁻¹)
        * (S.mV w * S.mV x * (S.mV (w + x))⁻¹) := by
    rw [show v + w + x = v + (w + x) from add_assoc v w x]
    simp [mul_comm, mul_left_comm, mul_assoc, mul_inv_cancel_left]
  apply Subtype.ext
  show ((S.mV (v + w) : Bg) * S.mV x * ((S.mV (v + w + x) : Bg))⁻¹)
      * ((S.mV v : Bg) * S.mV w * ((S.mV (v + w) : Bg))⁻¹)
    = ((S.mV v : Bg) * S.mV (w + x) * ((S.mV (v + (w + x)) : Bg))⁻¹)
      * ((S.mV w : Bg) * S.mV x * ((S.mV (w + x) : Bg))⁻¹)
  exact_mod_cast congrArg Subtype.val hM

/-! ### The `conjDef`-atom identities -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `mV(w+w')` split through the defect: `mV(w+w') = mDef(w,w')⁻¹ · mV w · mV w'`. -/
theorem mV_add_split (w w' : DD.Vmod) :
    (S.mV (w + w') : Bg) = ((mDef DD S w w' : Bg))⁻¹ * S.mV w * S.mV w' := by
  show (S.mV (w + w') : Bg)
    = ((S.mV w : Bg) * S.mV w' * ((S.mV (w + w') : Bg))⁻¹)⁻¹ * S.mV w * S.mV w'
  group

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `conjDef` additivity defect (`m_quad`-shape): conjugating the `mV`-split by `uσ cc`. -/
theorem conjDef_add (cc : DD.C0) (w w' : DD.Vmod) :
    conjDef DD S hσ cc (w + w')
      = (⟨S.uσ cc * ((mDef DD S w w' : Bg))⁻¹ * (S.uσ cc)⁻¹,
          D.hT.conj_mem _ (inv_mem (mDef DD S w w').2) _⟩ : ↥D.T)
        * conjDef DD S hσ cc w * conjDef DD S hσ cc w'
        * mDef DD S (cc • w) (cc • w') := by
  apply Subtype.ext
  set U := S.uσ cc with hU
  set A := (S.mV w : Bg) with hA
  set B := (S.mV w' : Bg) with hB
  set X := (S.mV (cc • w) : Bg) with hX
  set Y := (S.mV (cc • w') : Bg) with hY
  set mD := ((mDef DD S w w' : Bg)) with hmD
  show U * (S.mV (w + w') : Bg) * U⁻¹ * ((S.mV (cc • (w + w')) : Bg))⁻¹
    = (U * mD⁻¹ * U⁻¹) * (U * A * U⁻¹ * X⁻¹) * (U * B * U⁻¹ * Y⁻¹)
      * (X * Y * ((S.mV (cc • w + cc • w') : Bg))⁻¹)
  have harg : cc • (w + w') = cc • w + cc • w' := smul_add cc w w'
  rw [mV_add_split S w w', harg]
  -- sort: the `T`-atoms commute past the `M`-elements `X`, `Y`
  have hcdw : U * A * U⁻¹ * X⁻¹ ∈ D.T := conjDef_mem S hσ cc w
  have hcdw' : U * B * U⁻¹ * Y⁻¹ ∈ D.T := conjDef_mem S hσ cc w'
  have hXM : X ∈ D.M := (S.mV (cc • w)).2
  have hYM : Y ∈ D.M := (S.mV (cc • w')).2
  calc U * (mD⁻¹ * A * B) * U⁻¹ * ((S.mV (cc • w + cc • w') : Bg))⁻¹
      = (U * mD⁻¹ * U⁻¹) * (U * A * U⁻¹) * (U * B * U⁻¹)
          * ((S.mV (cc • w + cc • w') : Bg))⁻¹ := by group
    _ = (U * mD⁻¹ * U⁻¹) * (U * A * U⁻¹ * X⁻¹) * (X * (U * B * U⁻¹ * Y⁻¹)) * Y
          * ((S.mV (cc • w + cc • w') : Bg))⁻¹ := by group
    _ = (U * mD⁻¹ * U⁻¹) * (U * A * U⁻¹ * X⁻¹) * ((U * B * U⁻¹ * Y⁻¹) * X) * Y
          * ((S.mV (cc • w + cc • w') : Bg))⁻¹ := by rw [M_comm_T hXM hcdw']
    _ = (U * mD⁻¹ * U⁻¹) * (U * A * U⁻¹ * X⁻¹) * (U * B * U⁻¹ * Y⁻¹)
          * (X * Y * ((S.mV (cc • w + cc • w') : Bg))⁻¹) := by group

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `conjDef` composition law (`m_mul`-shape): splitting `uσ(cc·dd)` through `uDef`. -/
theorem conjDef_mul (cc dd : DD.C0) (v : DD.Vmod) :
    conjDef DD S hσ (cc * dd) v
      = (⟨S.uσ cc * (conjDef DD S hσ dd v : Bg) * (S.uσ cc)⁻¹,
          D.hT.conj_mem _ (conjDef DD S hσ dd v).2 _⟩ : ↥D.T)
        * conjDef DD S hσ cc (dd • v) := by
  apply Subtype.ext
  set U := S.uσ cc with hU
  set W := S.uσ dd with hW
  set Z := S.uσ (cc * dd) with hZ
  set uD := ((uDef DD S cc dd : Bg)) with huD
  have hZsplit : Z = uD⁻¹ * U * W := by
    show Z = (U * W * Z⁻¹)⁻¹ * U * W
    group
  show Z * (S.mV v : Bg) * Z⁻¹ * ((S.mV ((cc * dd) • v) : Bg))⁻¹
    = (U * (W * (S.mV v : Bg) * W⁻¹ * ((S.mV (dd • v) : Bg))⁻¹) * U⁻¹)
      * (U * (S.mV (dd • v) : Bg) * U⁻¹ * ((S.mV (cc • dd • v) : Bg))⁻¹)
  have harg : (cc * dd) • v = cc • dd • v := mul_smul cc dd v
  rw [hZsplit, harg]
  -- `uD ∈ T` commutes with everything relevant: `T` abelian and `M`-central
  have huDT : uD ∈ D.T := (uDef DD S cc dd).2
  have hMv : ∀ y : DD.Vmod, (S.mV y : Bg) ∈ D.M := fun y => (S.mV y).2
  -- the inner conjugate commutes with `uD` (it lies in `M`)
  have hsplit : U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹
      = (U * ((W * (S.mV v : Bg) * W⁻¹ * ((S.mV (dd • v) : Bg))⁻¹)) * U⁻¹)
        * (U * (S.mV (dd • v) : Bg) * U⁻¹) := by group
  have hmem : U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹ ∈ D.M := by
    rw [hsplit]
    refine mul_mem (D.hM.conj_mem _ ?_ U) (D.hM.conj_mem _ (hMv (dd • v)) U)
    exact D.hTM (conjDef_mem S hσ dd v)
  have hKcomm : (U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹) * uD
      = uD * (U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹) := M_comm_T hmem huDT
  calc uD⁻¹ * U * W * (S.mV v : Bg) * (uD⁻¹ * U * W)⁻¹ * ((S.mV (cc • dd • v) : Bg))⁻¹
      = uD⁻¹ * ((U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹) * uD)
          * ((S.mV (cc • dd • v) : Bg))⁻¹ := by group
    _ = uD⁻¹ * (uD * (U * W * (S.mV v : Bg) * W⁻¹ * U⁻¹))
          * ((S.mV (cc • dd • v) : Bg))⁻¹ := by rw [hKcomm]
    _ = (U * (W * (S.mV v : Bg) * W⁻¹ * ((S.mV (dd • v) : Bg))⁻¹) * U⁻¹)
          * (U * (S.mV (dd • v) : Bg) * U⁻¹ * ((S.mV (cc • dd • v) : Bg))⁻¹) := by group

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `conjDef` at the identity of `C₀` is trivial. -/
theorem conjDef_one_left (w : DD.Vmod) : conjDef DD S hσ 1 w = 1 := by
  apply Subtype.ext
  show S.uσ 1 * (S.mV w : Bg) * (S.uσ 1)⁻¹ * ((S.mV ((1 : DD.C0) • w) : Bg))⁻¹ = 1
  rw [S.uσ_one, one_smul, one_mul, inv_one, mul_one, mul_inv_cancel]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `conjDef` at the zero vector is trivial. -/
theorem conjDef_zero_right (cc : DD.C0) : conjDef DD S hσ cc 0 = 1 := by
  apply Subtype.ext
  show S.uσ cc * (S.mV 0 : Bg) * (S.uσ cc)⁻¹ * ((S.mV (cc • (0 : DD.Vmod)) : Bg))⁻¹ = 1
  rw [smul_zero, S.mV_zero, OneMemClass.coe_one, mul_one, mul_inv_cancel, one_mul, inv_one]

/-! ### The zero-form factor set of the `χ`-pushout (design §2) -/

variable (DD) in
/-- **The `χ`-pushout factor-set datum**: `f_χ := χ ∘ mDef`, `m_χ := χ ∘ conjDef`.  Together
with the scalar `e_χ := χ ∘ uDef` this is the explicit `(130)`-normal form of the `χ`-pushout
cover (`chiJDef_eq`). -/
noncomputable def datChi (S : CountSections DD σ)
    (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc) (χ : ↥(TCharC D)) :
    FactorSet DD.C0 DD.Vmod where
  f v w := χ.1 (mDef DD S v w)
  m cc w := χ.1 (conjDef DD S hσ cc w)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `datChi` is an equivariant factor-set datum **for the zero form**. -/
theorem isEquivariantFactorSet_datChi (χ : ↥(TCharC D)) :
    IsEquivariantFactorSet (fun _ : DD.Vmod => (0 : ZMod 2)) (datChi DD S hσ χ) where
  f_cocycle v w x := by
    simpa only [datChi, TCharC.map_mul] using
      congrArg (fun t : ↥D.T => χ.1 t) (mDef_cocycle S v w x)
  f_diag v := by
    show χ.1 (mDef DD S v v) = 0
    rw [mDef_self, TCharC.map_one]
  f_polar v w := by
    show χ.1 (mDef DD S v w) + χ.1 (mDef DD S w v) = polar (fun _ => (0 : ZMod 2)) v w
    rw [mDef_symm S v w]
    show χ.1 (mDef DD S w v) + χ.1 (mDef DD S w v) = (0 : ZMod 2) + 0 + 0
    have hchar : ∀ a : ZMod 2, a + a = 0 + 0 + 0 := by decide
    exact hchar _
  f_zero_left v := by
    show χ.1 (mDef DD S 0 v) = 0
    rw [mDef_zero_left, TCharC.map_one]
  f_zero_right v := by
    show χ.1 (mDef DD S v 0) = 0
    rw [mDef_zero_right, TCharC.map_one]
  m_quad cc w w' := by
    show χ.1 (conjDef DD S hσ cc (w + w')) + χ.1 (conjDef DD S hσ cc w)
        + χ.1 (conjDef DD S hσ cc w')
      = χ.1 (mDef DD S (cc • w) (cc • w')) + χ.1 (mDef DD S w w')
    have h := congrArg (fun t : ↥D.T => χ.1 t) (conjDef_add S hσ cc w w')
    simp only [TCharC.map_mul] at h
    have hconj : χ.1 (⟨S.uσ cc * ((mDef DD S w w' : Bg))⁻¹ * (S.uσ cc)⁻¹,
        D.hT.conj_mem _ (inv_mem (mDef DD S w w').2) _⟩ : ↥D.T)
        = χ.1 (mDef DD S w w') :=
      (TCharC.conj_invariant χ (S.uσ cc) (mDef DD S w w')⁻¹
        (D.hT.conj_mem _ (inv_mem (mDef DD S w w').2) _)).trans (TCharC.map_inv χ _)
    rw [hconj] at h
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h
  m_mul cc dd v := by
    show χ.1 (conjDef DD S hσ (cc * dd) v)
      = χ.1 (conjDef DD S hσ cc (dd • v)) + χ.1 (conjDef DD S hσ dd v)
    have h := congrArg (fun t : ↥D.T => χ.1 t) (conjDef_mul S hσ cc dd v)
    simp only [TCharC.map_mul] at h
    have hconj : χ.1 (⟨S.uσ cc * (conjDef DD S hσ dd v : Bg) * (S.uσ cc)⁻¹,
        D.hT.conj_mem _ (conjDef DD S hσ dd v).2 _⟩ : ↥D.T)
        = χ.1 (conjDef DD S hσ dd v) :=
      TCharC.conj_invariant χ (S.uσ cc) (conjDef DD S hσ dd v)
        (D.hT.conj_mem _ (conjDef DD S hσ dd v).2 _)
    rw [hconj] at h
    linear_combination h
  m_one v := by
    show χ.1 (conjDef DD S hσ 1 v) = 0
    rw [conjDef_one_left, TCharC.map_one]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The `ω_χ`-decomposition** (design §2): the `χ`-pushforward of the `J`-defect is the base
cocycle of `datChi` plus the inflated scalar `e_χ = χ ∘ uDef` — the explicit `(130)`-normal
form of the `χ`-pushout cover. -/
theorem chiJDef_eq (χ : ↥(TCharC D)) (p q : DD.Vmod × DD.C0) :
    χ.1 (JDefT S hσ p q)
      = kappa0 (datChi DD S hσ χ) p q + χ.1 (uDef DD S p.2 q.2) := by
  have h := congrArg (fun t : ↥D.T => χ.1 t) (JDefT_eq S hσ p q)
  simp only [TCharC.map_mul] at h
  show χ.1 (JDefT S hσ p q)
    = (χ.1 (mDef DD S p.1 (p.2 • q.1)) + χ.1 (conjDef DD S hσ p.2 q.1))
      + χ.1 (uDef DD S p.2 q.2)
  linear_combination h

end Atoms

end AffineTLift

end SectionEight

end GQ2
