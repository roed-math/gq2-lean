import GQ2.VLiftCount

/-!
# P-16d6c1c/c2 (stage A): the semidirect atom calculus and the `ω_χ`-decomposition

First stage of the (135)-keystone build (`docs/p16d6c-keystone-design.md` — the authoritative
design record; this file implements §§1–2).  Contents:

* the **raw semidirect calculus** on `V × C₀` (`pmul`, `pone`, associativity — no bundled
  `V ⋊ C` group), the transported product maps `jmap` (into `Q = Bg/T`) and `J` (into `Bg`)
  with their multiplicativity, and the graph relations tying them to c1a/c1b's
  `fLift`/`tDef`/`qOfCocycle`;
* the three **`T`-valued defect atoms** `mDef`/`conjDef`/`uDef` (the last is Lemma 8.7's class
  `e`), and the **product formula** `JDef = conjDef · uDef · mDef`;
* the **explicit `ω_χ`-decomposition**: `χ ∘ JDef = kappa0 (datχ χ) + inflScalar (eχ χ)` with
  `datχ χ` an equivariant factor-set datum **for the zero form** — the `(130)`-normal form of
  the `χ`-pushout cover with no abstract extraction.

All std-3, source-generic.
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

/-! ## Stage B: the `V`-splitting lemma (design §3)

A symmetric, zero-diagonal, normalized 2-cocycle on a finite elementary-abelian 2-group is a
coboundary: the twisted extension it classifies is an `𝔽₂`-vector space, so the projection has
a linear section, whose first coordinate is the splitting cochain. -/

section Splitting

/-- Carrier of the twisted extension `𝔽₂ ×_φ V` (`φ` a phantom parameter). -/
private structure TwExt {V : Type} (φ : V → V → ZMod 2) where
  /-- The central `𝔽₂`-coordinate. -/
  z : ZMod 2
  /-- The base `V`-coordinate. -/
  v : V

namespace TwExt

variable {V : Type} [AddCommGroup V] {φ : V → V → ZMod 2}

private instance : Zero (TwExt φ) := ⟨⟨0, 0⟩⟩
private instance : Add (TwExt φ) := ⟨fun p q => ⟨p.z + q.z + φ p.v q.v, p.v + q.v⟩⟩
private instance : Neg (TwExt φ) := ⟨fun p => p⟩

end TwExt

/-- **The splitting lemma** (design §3): a symmetric zero-diagonal normalized 2-cocycle on a
finite elementary-abelian 2-group is `∂g` for a normalized `g`. -/
theorem exists_splitting_of_symm_zero_diag {V : Type} [AddCommGroup V] [Finite V]
    (hV2 : ∀ v : V, v + v = 0) (φ : V → V → ZMod 2)
    (hcoc : ∀ v w x : V, φ (v + w) x + φ v w = φ v (w + x) + φ w x)
    (hsymm : ∀ v w : V, φ v w = φ w v) (hdiag : ∀ v : V, φ v v = 0)
    (hzl : ∀ v : V, φ 0 v = 0) :
    ∃ g : V → ZMod 2, g 0 = 0 ∧ ∀ v w : V, φ v w = g (v + w) + g v + g w := by
  classical
  have hzr : ∀ v : V, φ v 0 = 0 := fun v => (hsymm v 0).trans (hzl v)
  have hE2 : ∀ p : TwExt φ, p + p = (0 : TwExt φ) := by
    intro p
    show TwExt.mk (p.z + p.z + φ p.v p.v) (p.v + p.v) = TwExt.mk 0 0
    rw [hdiag, hV2, add_zero, CharTwo.add_self_eq_zero]
  letI : AddCommGroup (TwExt φ) :=
    { add_assoc := fun p q r => by
        show TwExt.mk (p.z + q.z + φ p.v q.v + r.z + φ (p.v + q.v) r.v) (p.v + q.v + r.v)
          = TwExt.mk (p.z + (q.z + r.z + φ q.v r.v) + φ p.v (q.v + r.v)) (p.v + (q.v + r.v))
        refine congrArg₂ TwExt.mk ?_ (add_assoc _ _ _)
        linear_combination hcoc p.v q.v r.v
      zero_add := fun p => by
        show TwExt.mk (0 + p.z + φ 0 p.v) (0 + p.v) = p
        rw [hzl, add_zero, zero_add, zero_add]
      add_zero := fun p => by
        show TwExt.mk (p.z + 0 + φ p.v 0) (p.v + 0) = p
        rw [hzr, add_zero, add_zero, add_zero]
      add_comm := fun p q => by
        show TwExt.mk (p.z + q.z + φ p.v q.v) (p.v + q.v)
          = TwExt.mk (q.z + p.z + φ q.v p.v) (q.v + p.v)
        rw [hsymm, add_comm p.z q.z, add_comm p.v q.v]
      neg_add_cancel := fun p => hE2 p
      nsmul := nsmulRec
      zsmul := zsmulRec }
  haveI : Module (ZMod 2) (TwExt φ) := AddCommGroup.zmodModule (fun p => by
    rw [two_nsmul]; exact hE2 p)
  haveI : Module (ZMod 2) V := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact hV2 v)
  -- the projection is linear and surjective, so it splits over the field `𝔽₂`
  let π : TwExt φ →ₗ[ZMod 2] V :=
    { toFun := fun p => p.v
      map_add' := fun p q => rfl
      map_smul' := fun c p => by
        show (c • p).v = (RingHom.id (ZMod 2)) c • p.v
        rw [RingHom.id_apply]
        rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
        · rw [zero_smul, zero_smul]
          rfl
        · rw [one_smul, one_smul] }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsurj : LinearMap.range π = ⊤ := by
    rw [LinearMap.range_eq_top]
    exact fun v => ⟨⟨0, v⟩, rfl⟩
  obtain ⟨sec, hsec⟩ := π.exists_rightInverse_of_surjective hsurj
  have hsecv : ∀ v : V, (sec v).v = v := fun v => LinearMap.congr_fun hsec v
  refine ⟨fun v => (sec v).z, ?_, ?_⟩
  · exact congrArg TwExt.z (map_zero sec)
  · intro v w
    show φ v w = (sec (v + w)).z + (sec v).z + (sec w).z
    have hz : (sec (v + w)).z = (sec v).z + (sec w).z + φ (sec v).v (sec w).v :=
      congrArg TwExt.z (map_add sec v w)
    rw [hsecv, hsecv] at hz
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hz

end Splitting

/-! ## Stage C, part 1: `ξ`-normalization and the cover-commutator = polar lemma (design §5) -/

section XiCalculus

variable {DD : DescData D} (Dsc : Descent D)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem xi_one_left (x : Bg ⧸ D.T) : xi Dsc (1, x) = 0 := by
  show ccZsign Dsc (s0 Dsc 1 * s0 Dsc x * (s0 Dsc (1 * x))⁻¹) = 0
  rw [s0_one, one_mul, one_mul, mul_inv_cancel, ccZsign_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem xi_one_right (x : Bg ⧸ D.T) : xi Dsc (x, 1) = 0 := by
  show ccZsign Dsc (s0 Dsc x * s0 Dsc 1 * (s0 Dsc (x * 1))⁻¹) = 0
  rw [s0_one, mul_one, mul_one, mul_inv_cancel, ccZsign_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Kernel elements of `descP` are involutions. -/
theorem ker_sq_one {x : covQ Dsc} (hx : x ∈ (descP Dsc).ker) : x * x = 1 := by
  rcases descKerCases Dsc hx with rfl | rfl
  · rw [one_mul]
  · exact zbar_sq Dsc

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The diagonal of `ξ` at an involution is the section-square sign. -/
theorem xi_diag_sq {x : Bg ⧸ D.T} (hx : x * x = 1) :
    xi Dsc (x, x) = ccZsign Dsc (s0 Dsc x * s0 Dsc x) := by
  show ccZsign Dsc (s0 Dsc x * s0 Dsc x * (s0 Dsc (x * x))⁻¹) = _
  rw [hx, s0_one, inv_one, mul_one]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The cover-commutator = polar lemma** (design §5): the symmetry defect of `ξ` on the
`V`-fibre is the polar form of the descended square map `q̄`. -/
theorem xi_polar (v w : DD.Vmod) :
    xi Dsc (iV DD (Multiplicative.ofAdd v), iV DD (Multiplicative.ofAdd w))
      + xi Dsc (iV DD (Multiplicative.ofAdd w), iV DD (Multiplicative.ofAdd v))
      = polar DD.qbar v w := by
  classical
  set a := iV DD (Multiplicative.ofAdd v) with ha_def
  set b := iV DD (Multiplicative.ofAdd w) with hb_def
  -- the `iV`-image is elementary abelian
  have hmul : ∀ x y : DD.Vmod, iV DD (Multiplicative.ofAdd x) * iV DD (Multiplicative.ofAdd y)
      = iV DD (Multiplicative.ofAdd (x + y)) := fun x y => (iV_ofAdd_add DD x y).symm
  have hcomm : a * b = b * a := by
    rw [ha_def, hb_def, hmul, hmul, add_comm]
  have hsq : ∀ x : DD.Vmod,
      iV DD (Multiplicative.ofAdd x) * iV DD (Multiplicative.ofAdd x) = 1 := by
    intro x
    rw [hmul, Vmod_exp2 DD x, ofAdd_zero, map_one]
  have hab : a * b = iV DD (Multiplicative.ofAdd (v + w)) := by rw [ha_def, hb_def, hmul]
  have hab2 : (a * b) * (a * b) = 1 := by rw [hab]; exact hsq (v + w)
  -- kernel elements
  have hX : s0 Dsc a * s0 Dsc b * (s0 Dsc (a * b))⁻¹ ∈ (descP Dsc).ker :=
    defect_mem_ker Dsc a b
  set X := s0 Dsc a * s0 Dsc b * (s0 Dsc (a * b))⁻¹ with hX_def
  have hcomm' : s0 Dsc b * s0 Dsc a * (s0 Dsc b)⁻¹ * (s0 Dsc a)⁻¹ ∈ (descP Dsc).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, s0_sect, s0_sect]
    rw [← hcomm]
    group
  set C' := s0 Dsc b * s0 Dsc a * (s0 Dsc b)⁻¹ * (s0 Dsc a)⁻¹ with hC'_def
  -- step 1: the symmetry defect is `ccZsign C'`
  have hstep1 : xi Dsc (a, b) + xi Dsc (b, a) = ccZsign Dsc C' := by
    have hY : s0 Dsc b * s0 Dsc a * (s0 Dsc (b * a))⁻¹ = C' * X := by
      rw [← hcomm, hC'_def, hX_def]
      group
    show ccZsign Dsc X + ccZsign Dsc (s0 Dsc b * s0 Dsc a * (s0 Dsc (b * a))⁻¹) = _
    rw [hY, ccZsign_mul Dsc hcomm' hX]
    have hchar : ∀ x y : ZMod 2, x + (y + x) = y := by decide
    exact hchar _ _
  -- step 2: the square relation `s0(ab)² = C' · s0a² · s0b²`
  have hsq_ker : ∀ (x : Bg ⧸ D.T), x * x = 1 → s0 Dsc x * s0 Dsc x ∈ (descP Dsc).ker := by
    intro x hx
    rw [MonoidHom.mem_ker, map_mul, s0_sect, hx]
  have hstep2 : s0 Dsc (a * b) * s0 Dsc (a * b)
      = C' * (s0 Dsc a * s0 Dsc a) * (s0 Dsc b * s0 Dsc b) := by
    have hs0ab : s0 Dsc (a * b) = X⁻¹ * (s0 Dsc a * s0 Dsc b) := by rw [hX_def]; group
    have hX2 : X * X = 1 := ker_sq_one Dsc hX
    have hC'c : ∀ y : covQ Dsc, C' * y = y * C' := fun y => ker_central Dsc hcomm' y
    calc s0 Dsc (a * b) * s0 Dsc (a * b)
        = X⁻¹ * (s0 Dsc a * s0 Dsc b) * (X⁻¹ * (s0 Dsc a * s0 Dsc b)) := by rw [hs0ab]
      _ = X⁻¹ * X⁻¹ * (s0 Dsc a * s0 Dsc b * (s0 Dsc a * s0 Dsc b)) := by
          rw [show X⁻¹ * (s0 Dsc a * s0 Dsc b) * (X⁻¹ * (s0 Dsc a * s0 Dsc b))
              = X⁻¹ * ((s0 Dsc a * s0 Dsc b) * X⁻¹) * (s0 Dsc a * s0 Dsc b) from by group,
            ← ker_central Dsc (inv_mem hX) (s0 Dsc a * s0 Dsc b)]
          group
      _ = s0 Dsc a * s0 Dsc b * (s0 Dsc a * s0 Dsc b) := by
          rw [show X⁻¹ * X⁻¹ = (X * X)⁻¹ from by group, hX2, inv_one, one_mul]
      _ = s0 Dsc a * (s0 Dsc b * s0 Dsc a) * s0 Dsc b := by group
      _ = s0 Dsc a * (C' * (s0 Dsc a * s0 Dsc b)) * s0 Dsc b := by
          rw [show s0 Dsc b * s0 Dsc a = C' * (s0 Dsc a * s0 Dsc b) from by
            rw [hC'_def]; group]
      _ = (s0 Dsc a * C') * (s0 Dsc a * s0 Dsc b) * s0 Dsc b := by group
      _ = (C' * s0 Dsc a) * (s0 Dsc a * s0 Dsc b) * s0 Dsc b := by rw [← hC'c (s0 Dsc a)]
      _ = C' * (s0 Dsc a * s0 Dsc a) * (s0 Dsc b * s0 Dsc b) := by group
  -- step 3: apply signs and `xi_diag`
  have hdva : xi Dsc (a, a) = ccZsign Dsc (s0 Dsc a * s0 Dsc a) := xi_diag_sq Dsc (hsq v)
  have hdvb : xi Dsc (b, b) = ccZsign Dsc (s0 Dsc b * s0 Dsc b) := xi_diag_sq Dsc (hsq w)
  have hdab : xi Dsc (a * b, a * b) = ccZsign Dsc (s0 Dsc (a * b) * s0 Dsc (a * b)) :=
    xi_diag_sq Dsc hab2
  have hsign2 : ccZsign Dsc (s0 Dsc (a * b) * s0 Dsc (a * b))
      = ccZsign Dsc C' + ccZsign Dsc (s0 Dsc a * s0 Dsc a)
        + ccZsign Dsc (s0 Dsc b * s0 Dsc b) := by
    rw [hstep2, ccZsign_mul Dsc (mul_mem hcomm' (hsq_ker a (by rw [ha_def]; exact hsq v)))
      (hsq_ker b (by rw [hb_def]; exact hsq w)),
      ccZsign_mul Dsc hcomm' (hsq_ker a (by rw [ha_def]; exact hsq v))]
  -- assemble: `q̄`-values via `xi_diag`
  have hqa : xi Dsc (a, a) = DD.qbar v := by rw [ha_def]; exact xi_diag DD Dsc v
  have hqb : xi Dsc (b, b) = DD.qbar w := by rw [hb_def]; exact xi_diag DD Dsc w
  have hqab : xi Dsc (a * b, a * b) = DD.qbar (v + w) := by
    rw [hab]; exact xi_diag DD Dsc (v + w)
  have hCval : ccZsign Dsc C' = DD.qbar (v + w) + DD.qbar v + DD.qbar w := by
    have h1 : DD.qbar (v + w) = ccZsign Dsc C' + DD.qbar v + DD.qbar w := by
      rw [← hqab, hdab, hsign2, ← hdva, ← hdvb, hqa, hqb]
    linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1
  rw [hstep1, hCval]
  rfl

end XiCalculus

/-! ## Stage C, part 2: the descended-cover cocycle and the `Θ`-extraction (design §4) -/

section Theta

variable {DD : DescData D} (σ : DD.C0 →* Bg ⧸ D.T) (Dsc : Descent D)

/-- The descended central class `κfull`, transported to the raw semidirect pairs. -/
noncomputable def kfull (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  xi Dsc (jmap DD σ p, jmap DD σ q)

variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
include hσ in
/-- `κfull` satisfies the raw Serre identity for `pmul`. -/
theorem kfull_serre (p q r : DD.Vmod × DD.C0) :
    kfull σ Dsc q r + kfull σ Dsc p (pmul q r)
      = kfull σ Dsc (pmul p q) r + kfull σ Dsc p q := by
  unfold kfull
  rw [← jmap_mul hσ q r, ← jmap_mul hσ p q]
  exact xi_cocycle Dsc (jmap DD σ p) (jmap DD σ q) (jmap DD σ r)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
omit hσ in
theorem kfull_pone_left (q : DD.Vmod × DD.C0) : kfull σ Dsc pone q = 0 := by
  unfold kfull
  rw [jmap_pone]
  exact xi_one_left Dsc _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
omit hσ in
theorem kfull_pone_right (p : DD.Vmod × DD.C0) : kfull σ Dsc p pone = 0 := by
  unfold kfull
  rw [jmap_pone]
  exact xi_one_right Dsc _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `m_c(0) = 0` for an equivariant factor-set datum. -/
theorem m_zero {q : DD.Vmod → ZMod 2} {dat : FactorSet DD.C0 DD.Vmod}
    (hdat : IsEquivariantFactorSet q dat) (cc : DD.C0) : dat.m cc 0 = 0 := by
  have h := hdat.m_quad cc 0 0
  rw [add_zero, smul_zero, hdat.f_zero_left] at h
  have hchar : ∀ a : ZMod 2, a + a + a = 0 + 0 → a = 0 := by decide
  exact hchar _ h

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The raw Serre identity for `kappa0` of any equivariant factor-set datum. -/
theorem kappa0_serre {q : DD.Vmod → ZMod 2} {dat : FactorSet DD.C0 DD.Vmod}
    (hdat : IsEquivariantFactorSet q dat) (p q' r : DD.Vmod × DD.C0) :
    kappa0 dat q' r + kappa0 dat p (pmul q' r)
      = kappa0 dat (pmul p q') r + kappa0 dat p q' := by
  show (dat.f q'.1 (q'.2 • r.1) + dat.m q'.2 r.1)
      + (dat.f p.1 (p.2 • (q'.1 + q'.2 • r.1)) + dat.m p.2 (q'.1 + q'.2 • r.1))
    = (dat.f (p.1 + p.2 • q'.1) ((p.2 * q'.2) • r.1) + dat.m (p.2 * q'.2) r.1)
      + (dat.f p.1 (p.2 • q'.1) + dat.m p.2 q'.1)
  rw [mul_smul, smul_add]
  have hf := hdat.f_cocycle p.1 (p.2 • q'.1) (p.2 • (q'.2 • r.1))
  have hmm := hdat.m_mul p.2 q'.2 r.1
  have hmq := hdat.m_quad p.2 q'.1 (q'.2 • r.1)
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hf + hmm + hmq

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The `pmul`-coboundary of a 1-cochain satisfies the raw Serre identity. -/
theorem pcob_serre (G : DD.Vmod × DD.C0 → ZMod 2) (p q r : DD.Vmod × DD.C0) :
    (G (pmul q r) + G q + G r) + (G (pmul p (pmul q r)) + G p + G (pmul q r))
      = (G (pmul (pmul p q) r) + G (pmul p q) + G r)
        + (G (pmul p q) + G p + G q) := by
  rw [pmul_assoc]
  have hchar : ∀ a b c d e f : ZMod 2,
      (a + b + c) + (d + e + a) = (d + f + c) + (f + e + b) := by decide
  exact hchar _ _ _ _ _ _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **`Θ := κfull + κ⁰`** has zero diagonal and symmetric `V×V`-part. -/
theorem theta_facts :
    (∀ v : DD.Vmod, kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (v, 1)
        + kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (v, 1) = 0) ∧
      (∀ v w : DD.Vmod,
        (kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
            + kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (w, 1))
          = (kfull σ Dsc ((w, 1) : DD.Vmod × DD.C0) (v, 1)
            + kappa0 DD.dat ((w, 1) : DD.Vmod × DD.C0) (v, 1))) := by
  have hjV : ∀ v : DD.Vmod, jmap DD σ ((v, 1) : DD.Vmod × DD.C0)
      = iV DD (Multiplicative.ofAdd v) := by
    intro v
    show iV DD (Multiplicative.ofAdd v) * σ 1 = iV DD (Multiplicative.ofAdd v)
    rw [map_one, mul_one]
  constructor
  · intro v
    have h1 : kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (v, 1) = DD.qbar v := by
      unfold kfull
      rw [hjV]
      exact xi_diag DD Dsc v
    have h2 : kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (v, 1) = DD.qbar v := by
      show DD.dat.f v ((1 : DD.C0) • v) + DD.dat.m 1 v = DD.qbar v
      rw [one_smul, DD.hdat.f_diag, DD.hdat.m_one, add_zero]
    rw [h1, h2]
    exact CharTwo.add_self_eq_zero _
  · intro v w
    have hk : kfull σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
        + kfull σ Dsc ((w, 1) : DD.Vmod × DD.C0) (v, 1) = polar DD.qbar v w := by
      unfold kfull
      rw [hjV, hjV]
      exact xi_polar Dsc v w
    have hp : kappa0 DD.dat ((v, 1) : DD.Vmod × DD.C0) (w, 1)
        + kappa0 DD.dat ((w, 1) : DD.Vmod × DD.C0) (v, 1) = polar DD.qbar v w := by
      show (DD.dat.f v ((1 : DD.C0) • w) + DD.dat.m 1 w)
          + (DD.dat.f w ((1 : DD.C0) • v) + DD.dat.m 1 v) = polar DD.qbar v w
      rw [one_smul, one_smul, DD.hdat.m_one, DD.hdat.m_one, add_zero, add_zero]
      exact DD.hdat.f_polar v w
    have hchar : ∀ a b c d P : ZMod 2, a + b = P → c + d = P → a + c = b + d := by decide
    exact hchar _ _ _ _ _ hk hp

end Theta

/-! ## Stage C, part 3: `Θ'` and the four-chase extraction (design §4) -/

section ThetaPrime

variable {DD : DescData D} (σ : DD.C0 →* Bg ⧸ D.T) (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

/-- `Θ := κfull + κ⁰`. -/
noncomputable def theta (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  kfull σ Dsc p q + kappa0 DD.dat p q

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta_serre (p q r : DD.Vmod × DD.C0) :
    theta σ Dsc q r + theta σ Dsc p (pmul q r)
      = theta σ Dsc (pmul p q) r + theta σ Dsc p q := by
  have h1 := kfull_serre σ Dsc hσ p q r
  have h2 := kappa0_serre (DD := DD) DD.hdat p q r
  unfold theta
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta_pone_left (q : DD.Vmod × DD.C0) : theta σ Dsc pone q = 0 := by
  unfold theta
  rw [kfull_pone_left]
  show 0 + (DD.dat.f 0 ((1 : DD.C0) • q.1) + DD.dat.m 1 q.1) = 0
  rw [DD.hdat.f_zero_left, DD.hdat.m_one, add_zero, add_zero]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta_pone_right (p : DD.Vmod × DD.C0) : theta σ Dsc p pone = 0 := by
  unfold theta
  rw [kfull_pone_right]
  show 0 + (DD.dat.f p.1 (p.2 • (0 : DD.Vmod)) + DD.dat.m p.2 0) = 0
  rw [smul_zero, DD.hdat.f_zero_right, m_zero (DD := DD) DD.hdat, add_zero, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The splitting data for `Θ|_{V×V}` exists. -/
theorem gkappa_exists : ∃ g : DD.Vmod → ZMod 2, g 0 = 0 ∧
    ∀ v w : DD.Vmod, theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
      = g (v + w) + g v + g w := by
  refine exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)) ?_ ?_ ?_ ?_
  · -- cocycle: the Serre identity at `V`-triples
    intro v w x
    have hs := theta_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (w, 1) (x, 1)
    have pm1 : pmul ((w, 1) : DD.Vmod × DD.C0) (x, 1) = (w + x, 1) := by
      unfold pmul
      rw [one_smul, one_mul]
    have pm2 : pmul ((v, 1) : DD.Vmod × DD.C0) (w, 1) = (v + w, 1) := by
      unfold pmul
      rw [one_smul, one_mul]
    rw [pm1, pm2] at hs
    linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs
  · -- symmetric
    exact (theta_facts σ Dsc).2
  · -- zero diagonal
    exact (theta_facts σ Dsc).1
  · -- left-normalized
    exact fun v => theta_pone_left σ Dsc ((v, 1) : DD.Vmod × DD.C0)

/-- The `V×V`-splitting cochain `gκ`. -/
noncomputable def gkappa : DD.Vmod → ZMod 2 :=
  Classical.choose (gkappa_exists σ Dsc hσ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gkappa_zero : gkappa σ Dsc hσ 0 = 0 :=
  (Classical.choose_spec (gkappa_exists σ Dsc hσ)).1

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gkappa_split (v w : DD.Vmod) :
    theta σ Dsc ((v, 1) : DD.Vmod × DD.C0) (w, 1)
      = gkappa σ Dsc hσ (v + w) + gkappa σ Dsc hσ v + gkappa σ Dsc hσ w :=
  (Classical.choose_spec (gkappa_exists σ Dsc hσ)).2 v w

/-- **`Θ'`** — `Θ` with the `V×V`-part killed by the `gκ`-coboundary. -/
noncomputable def theta' (p q : DD.Vmod × DD.C0) : ZMod 2 :=
  theta σ Dsc p q
    + (gkappa σ Dsc hσ (pmul p q).1 + gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ q.1)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta'_serre (p q r : DD.Vmod × DD.C0) :
    theta' σ Dsc hσ q r + theta' σ Dsc hσ p (pmul q r)
      = theta' σ Dsc hσ (pmul p q) r + theta' σ Dsc hσ p q := by
  have h1 := theta_serre σ Dsc hσ p q r
  have h2 := pcob_serre (DD := DD) (fun x => gkappa σ Dsc hσ x.1) p q r
  unfold theta'
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h2

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem theta'_VV (v w : DD.Vmod) :
    theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (w, 1) = 0 := by
  unfold theta'
  have pm : pmul ((v, 1) : DD.Vmod × DD.C0) (w, 1) = (v + w, 1) := by
    unfold pmul
    rw [one_smul, one_mul]
  rw [pm, gkappa_split σ Dsc hσ v w]
  exact CharTwo.add_self_eq_zero _

/-! ### The extraction data -/

/-- `uκ(v, cc) := Θ'((v,1),(0,cc))`. -/
noncomputable def ukap (v : DD.Vmod) (cc : DD.C0) : ZMod 2 :=
  theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (0, cc)

/-- `δκ(cc, dd) := Θ'((0,cc),(0,dd))` — the scalar part of the descended class. -/
noncomputable def dkap (cc dd : DD.C0) : ZMod 2 :=
  theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (0, dd)

/-- `γκ`-raw: `Θ'((0,cc),(w,1))`. -/
noncomputable def gkraw (cc : DD.C0) (w : DD.Vmod) : ZMod 2 :=
  theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, 1)

/-- **The edge `γκ`** of the descended class (`gammaEdge`-calibrated). -/
noncomputable def gammakap (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  gkraw σ Dsc hσ cc (cc⁻¹ • x) + ukap σ Dsc hσ (x) (cc)

/- `pmul`-evaluations used in the chases. -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pm_v1_0c (v : DD.Vmod) (cc : DD.C0) :
    pmul ((v, 1) : DD.Vmod × DD.C0) (0, cc) = (v, cc) := by
  unfold pmul
  rw [smul_zero, add_zero, one_mul]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pm_0c_wd (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    pmul ((0, cc) : DD.Vmod × DD.C0) (w, dd) = (cc • w, cc * dd) := by
  unfold pmul
  rw [zero_add]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem pm_v1_x1 (v x : DD.Vmod) (ee : DD.C0) :
    pmul ((v, 1) : DD.Vmod × DD.C0) (x, ee) = (v + x, ee) := by
  unfold pmul
  rw [one_smul, one_mul]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E2: `Θ'` on a `V`-row. -/
theorem chaseE2 (v x : DD.Vmod) (ee : DD.C0) :
    theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (x, ee)
      = ukap σ Dsc hσ (v + x) (ee) + ukap σ Dsc hσ (x) (ee) := by
  have hs := theta'_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (x, 1) (0, ee)
  rw [pm_v1_0c, pm_v1_x1] at hs
  have hVV := theta'_VV σ Dsc hσ v x
  unfold ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs + hVV

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E1: peel the `V`-coordinate off the first argument. -/
theorem chaseE1 (v : DD.Vmod) (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, dd)
        + theta' σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (cc • w, cc * dd)
        + ukap σ Dsc hσ (v) (cc) := by
  have hs := theta'_serre σ Dsc hσ ((v, 1) : DD.Vmod × DD.C0) (0, cc) (w, dd)
  rw [pm_v1_0c, pm_0c_wd] at hs
  unfold ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E3: peel the `V`-coordinate off the second argument. -/
theorem chaseE3 (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, dd)
      = ukap σ Dsc hσ (w) (dd)
        + theta' σ Dsc hσ ((cc • w, cc) : DD.Vmod × DD.C0) (0, dd)
        + gkraw σ Dsc hσ cc w := by
  have hs := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (w, 1) (0, dd)
  have pmA : pmul ((0, cc) : DD.Vmod × DD.C0) (w, 1) = (cc • w, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  have pmB : pmul ((w, 1) : DD.Vmod × DD.C0) (0, dd) = (w, dd) := pm_v1_0c w dd
  rw [pmA, pmB] at hs
  unfold ukap gkraw
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E4: reduce the mixed corner to `δκ` and `uκ`. -/
theorem chaseE4 (cc dd : DD.C0) (y : DD.Vmod) :
    theta' σ Dsc hσ ((y, cc) : DD.Vmod × DD.C0) (0, dd)
      = dkap σ Dsc hσ cc dd + ukap σ Dsc hσ (y) (cc * dd) + ukap σ Dsc hσ (y) (cc) := by
  have hs := theta'_serre σ Dsc hσ ((y, 1) : DD.Vmod × DD.C0) (0, cc) (0, dd)
  have pmA : pmul ((0, cc) : DD.Vmod × DD.C0) (0, dd) = (0, cc * dd) := by
    unfold pmul
    rw [smul_zero, add_zero]
  rw [pm_v1_0c, pmA] at hs
  unfold dkap ukap
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hs

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The extraction** (design §4): `Θ'` in `Γγκ + inf δκ + ∂uκ` normal form (raw values). -/
theorem theta'_decomp (v : DD.Vmod) (cc : DD.C0) (w : DD.Vmod) (dd : DD.C0) :
    theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = (gkraw σ Dsc hσ cc w + ukap σ Dsc hσ (cc • w) (cc))
        + dkap σ Dsc hσ cc dd
        + (ukap σ Dsc hσ (v + cc • w) (cc * dd) + ukap σ Dsc hσ (v) (cc)
            + ukap σ Dsc hσ (w) (dd)) := by
  have h1 := chaseE1 σ Dsc hσ v cc w dd
  have h3 := chaseE3 σ Dsc hσ cc w dd
  have h4 := chaseE4 σ Dsc hσ cc dd (cc • w)
  have h2 := chaseE2 σ Dsc hσ v (cc • w) (cc * dd)
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h1 + h3 + h4 + h2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E5: `gkraw` additivity up to `uκ`-corrections. -/
theorem chaseE5 (cc : DD.C0) (a b : DD.Vmod) :
    gkraw σ Dsc hσ cc (a + b)
      = gkraw σ Dsc hσ cc a + gkraw σ Dsc hσ cc b
        + ukap σ Dsc hσ (cc • (a + b)) (cc) + ukap σ Dsc hσ (cc • b) (cc)
        + ukap σ Dsc hσ (cc • a) (cc) := by
  -- E5a
  have hsA := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (a, 1) (b, 1)
  have pmA : pmul ((a, 1) : DD.Vmod × DD.C0) (b, 1) = (a + b, 1) := pm_v1_x1 a b 1
  have pmB : pmul ((0, cc) : DD.Vmod × DD.C0) (a, 1) = (cc • a, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  rw [pmA, pmB] at hsA
  have hVV := theta'_VV σ Dsc hσ a b
  -- E5b
  have hsB := theta'_serre σ Dsc hσ ((cc • a, 1) : DD.Vmod × DD.C0) (0, cc) (b, 1)
  have pmC : pmul ((0, cc) : DD.Vmod × DD.C0) (b, 1) = (cc • b, cc) := by
    unfold pmul
    rw [zero_add, mul_one]
  rw [pm_v1_0c, pmC] at hsB
  -- E5c
  have hsC := chaseE2 σ Dsc hσ (cc • a) (cc • b) cc
  unfold gkraw ukap at *
  rw [show cc • (a + b) = cc • a + cc • b from smul_add cc a b]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero]))
    hsA + hVV + hsB + hsC

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γκ` is additive. -/
theorem gammakap_add (cc : DD.C0) (x y : DD.Vmod) :
    gammakap σ Dsc hσ cc (x + y)
      = gammakap σ Dsc hσ cc x + gammakap σ Dsc hσ cc y := by
  unfold gammakap
  have h5 := chaseE5 σ Dsc hσ cc (cc⁻¹ • x) (cc⁻¹ • y)
  rw [show cc • (cc⁻¹ • x + cc⁻¹ • y) = x + y from by
      rw [smul_add, smul_inv_smul, smul_inv_smul],
    smul_inv_smul, smul_inv_smul] at h5
  rw [show cc⁻¹ • (x + y) = cc⁻¹ • x + cc⁻¹ • y from smul_add cc⁻¹ x y]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h5

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Chase E6: the `gkraw`-composition law. -/
theorem chaseE6 (cc dd : DD.C0) (w : DD.Vmod) :
    gkraw σ Dsc hσ (cc * dd) w
      = gkraw σ Dsc hσ dd w + gkraw σ Dsc hσ cc (dd • w)
        + ukap σ Dsc hσ (dd • w) (dd) + ukap σ Dsc hσ (cc • dd • w) (cc * dd)
        + ukap σ Dsc hσ (cc • dd • w) (cc) := by
  -- E6a
  have hsA := theta'_serre σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) (0, dd) (w, 1)
  have pmA : pmul ((0, dd) : DD.Vmod × DD.C0) (w, 1) = (dd • w, dd) := by
    unfold pmul
    rw [zero_add, mul_one]
  have pmB : pmul ((0, cc) : DD.Vmod × DD.C0) (0, dd) = (0, cc * dd) := by
    unfold pmul
    rw [smul_zero, add_zero]
  rw [pmA, pmB] at hsA
  -- E6b
  have hsB := chaseE3 σ Dsc hσ cc (dd • w) dd
  -- E6c
  have hsC := chaseE4 σ Dsc hσ cc dd (cc • dd • w)
  unfold gkraw dkap ukap at *
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hsA + hsB + hsC

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The dual-crossed law for `γκ`** (design §6): `γκ(cc·dd)(x) = γκ(cc)(x) + γκ(dd)(cc⁻¹•x)`. -/
theorem gammakap_dual_crossed (cc dd : DD.C0) (x : DD.Vmod) :
    gammakap σ Dsc hσ (cc * dd) x
      = gammakap σ Dsc hσ cc x + gammakap σ Dsc hσ dd (cc⁻¹ • x) := by
  unfold gammakap
  have h6 := chaseE6 σ Dsc hσ cc dd ((cc * dd)⁻¹ • x)
  have harg1 : dd • (cc * dd)⁻¹ • x = cc⁻¹ • x := by
    rw [mul_inv_rev, mul_smul, smul_inv_smul]
  rw [harg1, smul_inv_smul] at h6
  rw [show (cc * dd)⁻¹ • x = dd⁻¹ • cc⁻¹ • x from by rw [mul_inv_rev, mul_smul]] at h6 ⊢
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) h6

end ThetaPrime

/-! ## The graph tie-in and the affineness `haff` (the master count's threaded hypothesis) -/

section Affine

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

omit [DiscreteTopology Bg] in
/-- The graph of a crossed cocycle is `pmul`-multiplicative. -/
theorem graph_pmul (c : VCocycle DD ρ) (γ δ : Γ) :
    pmul (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)
      = (c.c (γ * δ), rho0 DD ρ (γ * δ)) := by
  unfold pmul
  exact Prod.ext (c.crossed γ δ).symm (map_mul (rho0 DD ρ) γ δ).symm

include hσ in
/-- The `T`-defect of `fLift` is the `J`-defect at the graph. -/
theorem tDef_eq_JDefT (c : VCocycle DD ρ) (p : Γ × Γ) :
    tDef S hσ c p
      = JDefT S hσ (c.c p.1, rho0 DD ρ p.1) (c.c p.2, rho0 DD ρ p.2) := by
  apply Subtype.ext
  show fLift S c p.1 * fLift S c p.2 * (fLift S c (p.1 * p.2))⁻¹
    = Jmap S (c.c p.1, rho0 DD ρ p.1) * Jmap S (c.c p.2, rho0 DD ρ p.2)
      * (Jmap S (pmul (c.c p.1, rho0 DD ρ p.1) (c.c p.2, rho0 DD ρ p.2)))⁻¹
  rw [graph_pmul]
  rfl

variable (DD ρ) in
/-- **The cup part** of the `χ`-obstruction cochain: the `c`-additive component of the
`ω_χ`-decomposition at the graph. -/
noncomputable def cupChi (gχ : DD.Vmod → ZMod 2) (χ : ↥(TCharC D)) (c : VCocycle DD ρ)
    (p : Γ × Γ) : ZMod 2 :=
  χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
    + gχ (rho0 DD ρ p.1 • c.c p.2) + gχ (c.c p.2)

include hσ in
/-- **The `chiDef`-decomposition at a splitting of `f_χ`**: cup part + `g`-coboundary part +
inflated scalar. -/
theorem chiDef_decomp (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2)
    (hg : ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = gχ (v + w) + gχ v + gχ w)
    (c : VCocycle DD ρ) (p : Γ × Γ) :
    chiDef S hσ χ c p
      = cupChi DD S ρ hσ gχ χ c p
        + (gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2))
        + χ.1 (uDef DD S (rho0 DD ρ p.1) (rho0 DD ρ p.2)) := by
  show χ.1 (tDef S hσ c p) = _
  rw [tDef_eq_JDefT S hσ c p, chiJDef_eq S hσ χ]
  show χ.1 (mDef DD S (c.c p.1) (rho0 DD ρ p.1 • c.c p.2))
      + χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
      + χ.1 (uDef DD S (rho0 DD ρ p.1) (rho0 DD ρ p.2)) = _
  rw [hg (c.c p.1) (rho0 DD ρ p.1 • c.c p.2)]
  unfold cupChi
  have hcr : c.c (p.1 * p.2) = c.c p.1 + rho0 DD ρ p.1 • c.c p.2 := c.crossed p.1 p.2
  rw [hcr]
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) (rfl : (0 : ZMod 2) = 0)

include hσ in
/-- The cup part is additive in the cocycle. -/
theorem cupChi_add (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2)
    (hg : ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = gχ (v + w) + gχ v + gχ w)
    (c c' : VCocycle DD ρ) (p : Γ × Γ) :
    cupChi DD S ρ hσ gχ χ (c + c') p
      = cupChi DD S ρ hσ gχ χ c p + cupChi DD S ρ hσ gχ χ c' p := by
  unfold cupChi
  have hcc : (c + c').c p.2 = c.c p.2 + c'.c p.2 := rfl
  rw [hcc]
  -- `m_quad` for the conjugation part, `hg` for the two `g`-parts
  have hq := (isEquivariantFactorSet_datChi S hσ χ).m_quad (rho0 DD ρ p.1) (c.c p.2) (c'.c p.2)
  have hg1 : gχ (rho0 DD ρ p.1 • (c.c p.2 + c'.c p.2))
      = gχ (rho0 DD ρ p.1 • c.c p.2) + gχ (rho0 DD ρ p.1 • c'.c p.2)
        + χ.1 (mDef DD S (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2)) := by
    rw [smul_add]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hg (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2)
  have hg2 : gχ (c.c p.2 + c'.c p.2)
      = gχ (c.c p.2) + gχ (c'.c p.2) + χ.1 (mDef DD S (c.c p.2) (c'.c p.2)) := by
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hg (c.c p.2) (c'.c p.2)
  -- `m_quad`'s statement in `datChi`-vocabulary
  have hq' : χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2 + c'.c p.2))
      = χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c.c p.2))
        + χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) (c'.c p.2))
        + χ.1 (mDef DD S (rho0 DD ρ p.1 • c.c p.2) (rho0 DD ρ p.1 • c'.c p.2))
        + χ.1 (mDef DD S (c.c p.2) (c'.c p.2)) := by
    have hchar : ∀ x a b f1 f2 : ZMod 2, x + a + b = f1 + f2 → x = a + b + f1 + f2 := by decide
    exact hchar _ _ _ _ _ hq
  rw [hq', hg1, hg2]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) (rfl : (0 : ZMod 2) = 0)

include hσ in
omit [DiscreteTopology Bg] in
/-- The cup part vanishes at the zero cocycle. -/
theorem cupChi_zero (χ : ↥(TCharC D)) (gχ : DD.Vmod → ZMod 2) (hg0 : gχ 0 = 0)
    (p : Γ × Γ) :
    cupChi DD S ρ hσ gχ χ (0 : VCocycle DD ρ) p = 0 := by
  unfold cupChi
  show χ.1 (conjDef DD S hσ (rho0 DD ρ p.1) 0) + gχ (rho0 DD ρ p.1 • (0 : DD.Vmod)) + gχ 0 = 0
  rw [conjDef_zero_right, TCharC.map_one, smul_zero, hg0, add_zero, add_zero]

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The `g`-coboundary part of the `chiDef`-decomposition is a continuous coboundary. -/
theorem gPart_mem_B2 (_hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (gχ : DD.Vmod → ZMod 2) (cx : VCocycle DD ρ) :
    (fun p : Γ × Γ => gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1) + gχ (cx.c p.2))
      ∈ B2 Γ (ZMod 2) := by
  classical
  refine ⟨fun γ => gχ (cx.c γ), ?_, ?_⟩
  · have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b h => iV_ofAdd_inj DD h
    have heq : (fun γ => gχ (cx.c γ))
        = (fun q : Bg ⧸ D.T => gχ (Function.invFun
            (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) q))
          ∘ (fun γ => iV DD (Multiplicative.ofAdd (cx.c γ))) := by
      funext γ
      show gχ (cx.c γ)
        = gχ (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
            (iV DD (Multiplicative.ofAdd (cx.c γ))))
      rw [Function.leftInverse_invFun hinj (cx.c γ)]
    rw [heq]
    exact continuous_of_discreteTopology.comp cx.cont
  · funext p
    show p.1 • gχ (cx.c p.2) - gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1)
      = gχ (cx.c (p.1 * p.2)) + gχ (cx.c p.1) + gχ (cx.c p.2)
    rw [htriv]
    have hchar : ∀ a b cc : ZMod 2, a - b + cc = b + cc + a := by decide
    exact hchar _ _ _

omit [ContinuousSMul Γ (ZMod 2)] in
include hσ in
/-- **The affineness `haff`** (the master count's threaded hypothesis, design §6): `β_χ` is
affine in the cocycle — the cup part is additive, the `g`-part is a coboundary killed by
`ι_Γ`, and the inflated scalar cancels four-fold. -/
theorem betaChi_affine (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (χ : ↥(TCharC D)) (c c' : VCocycle DD ρ) :
    betaChi S hσ χ (c + c')
      = betaChi S hσ χ c + betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ) := by
  classical
  -- split `f_χ` (symmetric, zero-diagonal, normalized cocycle on the exponent-2 `V`)
  obtain ⟨gχ, hg0, hg⟩ := exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => χ.1 (mDef DD S v w))
    (fun v w x => (isEquivariantFactorSet_datChi S hσ χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])
  -- the four-fold sum of the obstruction cochains is a coboundary
  have hsum_mem : (chiDef S hσ χ (c + c') + chiDef S hσ χ c)
      + (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ)) ∈ B2 Γ (ZMod 2) := by
    have hfun : (chiDef S hσ χ (c + c') + chiDef S hσ χ c)
        + (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ))
        = ((fun p : Γ × Γ => gχ ((c + c').c (p.1 * p.2)) + gχ ((c + c').c p.1)
              + gχ ((c + c').c p.2))
            + (fun p : Γ × Γ => gχ (c.c (p.1 * p.2)) + gχ (c.c p.1) + gχ (c.c p.2)))
          + ((fun p : Γ × Γ => gχ (c'.c (p.1 * p.2)) + gχ (c'.c p.1) + gχ (c'.c p.2))
            + (fun p : Γ × Γ => gχ ((0 : VCocycle DD ρ).c (p.1 * p.2))
                + gχ ((0 : VCocycle DD ρ).c p.1) + gχ ((0 : VCocycle DD ρ).c p.2))) := by
      funext p
      have h1 := chiDef_decomp S hσ χ gχ hg (c + c') p
      have h2 := chiDef_decomp S hσ χ gχ hg c p
      have h3 := chiDef_decomp S hσ χ gχ hg c' p
      have h4 := chiDef_decomp S hσ χ gχ hg (0 : VCocycle DD ρ) p
      have hcup := cupChi_add S hσ χ gχ hg c c' p
      have hcup0 := cupChi_zero (ρ := ρ) S hσ χ gχ hg0 p
      show chiDef S hσ χ (c + c') p + chiDef S hσ χ c p
          + (chiDef S hσ χ c' p + chiDef S hσ χ (0 : VCocycle DD ρ) p) = _
      linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
        show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
        h1 + h2 + h3 + h4 + hcup + hcup0
    rw [hfun]
    exact AddSubgroup.add_mem _
      (AddSubgroup.add_mem _ (gPart_mem_B2 hσ htriv gχ (c + c'))
        (gPart_mem_B2 hσ htriv gχ c))
      (AddSubgroup.add_mem _ (gPart_mem_B2 hσ htriv gχ c')
        (gPart_mem_B2 hσ htriv gχ (0 : VCocycle DD ρ)))
  -- assemble through `ι_Γ`-additivity
  have hZ : ∀ cx : VCocycle DD ρ, chiDef S hσ χ cx ∈ Z2 Γ (ZMod 2) :=
    fun cx => chiDef_mem_Z2 S hσ htriv χ cx
  have h12 : betaChi S hσ χ (c + c') + betaChi S hσ χ c
      = iotaB (chiDef S hσ χ (c + c') + chiDef S hσ χ c) :=
    (iotaB_add hH2 (hZ _) (hZ _)).symm
  have h34 : betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ)
      = iotaB (chiDef S hσ χ c' + chiDef S hσ χ (0 : VCocycle DD ρ)) :=
    (iotaB_add hH2 (hZ _) (hZ _)).symm
  have htot : betaChi S hσ χ (c + c') + betaChi S hσ χ c
      + (betaChi S hσ χ c' + betaChi S hσ χ (0 : VCocycle DD ρ)) = 0 := by
    rw [h12, h34, ← iotaB_add hH2 (AddSubgroup.add_mem _ (hZ _) (hZ _))
      (AddSubgroup.add_mem _ (hZ _) (hZ _))]
    exact iotaB_of_mem_B2 hsum_mem
  have hchar : ∀ a b cc d : ZMod 2, a + b + (cc + d) = 0 → a = b + cc + d := by decide
  exact hchar _ _ _ _ htot

end Affine

/-! ## Stage D: the keystone assembly (design §6) -/

section Assembly

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The splitting data for `f_χ = χ ∘ mDef` exists. -/
theorem gchi_exists (χ : ↥(TCharC D)) : ∃ g : DD.Vmod → ZMod 2, g 0 = 0 ∧
    ∀ v w : DD.Vmod, χ.1 (mDef DD S v w) = g (v + w) + g v + g w :=
  exists_splitting_of_symm_zero_diag (Vmod_exp2 DD)
    (fun v w => χ.1 (mDef DD S v w))
    (fun v w x => (isEquivariantFactorSet_datChi S hσ χ).f_cocycle v w x)
    (fun v w => by rw [mDef_symm])
    (fun v => by rw [mDef_self, TCharC.map_one])
    (fun v => by rw [mDef_zero_left, TCharC.map_one])

/-- A fixed splitting `g_χ` of `f_χ`. -/
noncomputable def gchi (χ : ↥(TCharC D)) : DD.Vmod → ZMod 2 :=
  Classical.choose (gchi_exists S hσ χ)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gchi_split (χ : ↥(TCharC D)) (v w : DD.Vmod) :
    χ.1 (mDef DD S v w) = gchi S hσ χ (v + w) + gchi S hσ χ v + gchi S hσ χ w :=
  (Classical.choose_spec (gchi_exists S hσ χ)).2 v w

/-- **The `χ`-edge `γ''_χ`** of the zero-form normal form. -/
noncomputable def gamma2 (χ : ↥(TCharC D)) (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  χ.1 (conjDef DD S hσ cc (cc⁻¹ • x)) + gchi S hσ χ x + gchi S hσ χ (cc⁻¹ • x)

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γ''_χ(cc)` is additive. -/
theorem gamma2_add (χ : ↥(TCharC D)) (cc : DD.C0) (x y : DD.Vmod) :
    gamma2 S hσ χ cc (x + y) = gamma2 S hσ χ cc x + gamma2 S hσ χ cc y := by
  unfold gamma2
  have hmq := (isEquivariantFactorSet_datChi S hσ χ).m_quad cc (cc⁻¹ • x) (cc⁻¹ • y)
  simp only [datChi] at hmq
  have hg1 := gchi_split S hσ χ x y
  have hg2 := gchi_split S hσ χ (cc⁻¹ • x) (cc⁻¹ • y)
  rw [show cc⁻¹ • (x + y) = cc⁻¹ • x + cc⁻¹ • y from smul_add cc⁻¹ x y]
  have hsm : cc • cc⁻¹ • x = x := smul_inv_smul cc x
  have hsm' : cc • cc⁻¹ • y = y := smul_inv_smul cc y
  rw [hsm, hsm'] at hmq
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hmq + hg1 + hg2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The dual-crossed law for `γ''_χ`. -/
theorem gamma2_dual_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) (x : DD.Vmod) :
    gamma2 S hσ χ (cc * dd) x = gamma2 S hσ χ cc x + gamma2 S hσ χ dd (cc⁻¹ • x) := by
  unfold gamma2
  have hmm := (isEquivariantFactorSet_datChi S hσ χ).m_mul cc dd ((cc * dd)⁻¹ • x)
  simp only [datChi] at hmm
  have harg : dd • (cc * dd)⁻¹ • x = cc⁻¹ • x := by
    rw [mul_inv_rev, mul_smul, smul_inv_smul]
  rw [harg] at hmm
  rw [show (cc * dd)⁻¹ • x = dd⁻¹ • cc⁻¹ • x from by rw [mul_inv_rev, mul_smul]] at hmm ⊢
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hmm

/-! ### The total edge and the polar-inverse shear -/

/-- **The total edge** `γtot_χ := γ''_χ + γκ`. -/
noncomputable def gammatot (χ : ↥(TCharC D)) (cc : DD.C0) (x : DD.Vmod) : ZMod 2 :=
  gamma2 S hσ χ cc x + gammakap σ Dsc hσ cc x

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gammatot_add (χ : ↥(TCharC D)) (cc : DD.C0) (x y : DD.Vmod) :
    gammatot S Dsc hσ χ cc (x + y)
      = gammatot S Dsc hσ χ cc x + gammatot S Dsc hσ χ cc y := by
  unfold gammatot
  rw [gamma2_add S hσ χ cc x y, gammakap_add σ Dsc hσ cc x y]
  ring

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem gammatot_dual_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) (x : DD.Vmod) :
    gammatot S Dsc hσ χ (cc * dd) x
      = gammatot S Dsc hσ χ cc x + gammatot S Dsc hσ χ dd (cc⁻¹ • x) := by
  unfold gammatot
  rw [gamma2_dual_crossed S hσ χ cc dd x, gammakap_dual_crossed σ Dsc hσ cc dd x]
  ring

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar-inverse for additive functionals (module-free wrapper). -/
theorem exists_polar_inverse' {q : DD.Vmod → ZMod 2} (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (φ : DD.Vmod → ZMod 2)
    (hφ : ∀ x y : DD.Vmod, φ (x + y) = φ x + φ y) :
    ∃ a : DD.Vmod, ∀ v : DD.Vmod, polar q a v = φ v := by
  letI : Module (ZMod 2) DD.Vmod := AddCommGroup.zmodModule (fun v => by
    rw [two_nsmul]; exact Vmod_exp2 DD v)
  let φL : Module.Dual (ZMod 2) DD.Vmod :=
    { toFun := φ
      map_add' := hφ
      map_smul' := fun c v => by
        rcases (show ∀ b : ZMod 2, b = 0 ∨ b = 1 from by decide) c with rfl | rfl
        · rw [zero_smul]
          show φ 0 = (RingHom.id (ZMod 2)) 0 • φ v
          have h0 : φ 0 = 0 := by
            have h := hφ 0 0
            rw [add_zero] at h
            exact left_eq_add.mp h
          rw [h0, RingHom.id_apply, zero_smul]
        · rw [one_smul]
          show φ v = (RingHom.id (ZMod 2)) 1 • φ v
          rw [RingHom.id_apply, one_smul] }
  obtain ⟨a, ha⟩ := exists_polar_inverse q hq hns φL
  exact ⟨a, ha⟩

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar injectivity: nonsingular forms separate points through the polar pairing. -/
theorem polar_inj {q : DD.Vmod → ZMod 2} (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    {a b : DD.Vmod} (h : ∀ v : DD.Vmod, polar q a v = polar q b v) : a = b := by
  by_contra hne
  have hab : a + b ≠ 0 := fun h0 =>
    hne ((add_eq_zero_iff_eq_neg.mp h0).trans (neg_eq_of_add_eq_zero_left (Vmod_exp2 DD b)))
  obtain ⟨w, hw⟩ := hns (a + b) hab
  apply hw
  rw [hq.polar_add_left a b w, h w]
  exact CharTwo.add_self_eq_zero _

/-! ### The shear family `a_χ` and the total scalar phase -/
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- Polar equivariance for an invariant form: `B(cc•u, v) = B(u, cc⁻¹•v)`. -/
theorem polar_smul_inv {q : DD.Vmod → ZMod 2} (hinvQ : IsInvariant DD.C0 q)
    (cc : DD.C0) (u v : DD.Vmod) :
    polar q (cc • u) v = polar q u (cc⁻¹ • v) := by
  show q (cc • u + v) + q (cc • u) + q v = q (u + cc⁻¹ • v) + q u + q (cc⁻¹ • v)
  have h1 : cc • u + v = cc • (u + cc⁻¹ • v) := by rw [smul_add, smul_inv_smul]
  rw [h1, hinvQ cc (u + cc⁻¹ • v), hinvQ cc u,
    show q v = q (cc⁻¹ • v) from by
      conv_lhs => rw [show v = cc • cc⁻¹ • v from (smul_inv_smul cc v).symm]
      exact hinvQ cc (cc⁻¹ • v)]

variable (hinvQ : IsInvariant DD.C0 DD.qbar)

/-- **The shear family** `a_χ(cc) := B♭⁻¹(γtot_χ(cc))`. -/
noncomputable def achi (χ : ↥(TCharC D)) (cc : DD.C0) : DD.Vmod :=
  Classical.choose (exists_polar_inverse' (DD := DD) DD.hquad DD.hns
    (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
theorem achi_spec (χ : ↥(TCharC D)) (cc : DD.C0) (v : DD.Vmod) :
    polar DD.qbar (achi S Dsc hσ χ cc) v = gammatot S Dsc hσ χ cc v :=
  Classical.choose_spec (exists_polar_inverse' (DD := DD) DD.hquad DD.hns
    (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc)) v

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `a_χ` is a crossed 1-cocycle (the `ha` of `prop_8_8_target`). -/
theorem achi_crossed (χ : ↥(TCharC D)) (cc dd : DD.C0) :
    achi S Dsc hσ χ (cc * dd) = achi S Dsc hσ χ cc + cc • achi S Dsc hσ χ dd := by
  apply polar_inj (DD := DD) DD.hquad DD.hns
  intro v
  rw [achi_spec, gammatot_dual_crossed S Dsc hσ χ cc dd v, DD.hquad.polar_add_left,
    achi_spec, polar_smul_inv hinvQ, achi_spec]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The kill condition (`hkill` of `prop_8_8_target`). -/
theorem achi_kill (χ : ↥(TCharC D)) (cc : DD.C0) (v : DD.Vmod) :
    polar DD.qbar (achi S Dsc hσ χ cc) v
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc)) v = 0 := by
  show polar DD.qbar (achi S Dsc hσ χ cc) v + gammatot S Dsc hσ χ cc v = 0
  rw [achi_spec]
  exact CharTwo.add_self_eq_zero _

/-! ### The `Ψ_χ`-normal form -/

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The zero-form `kappa0` in `γ'' + ∂g`-normal form (pair level). -/
theorem kappa0_datChi_decomp (χ : ↥(TCharC D)) (p q : DD.Vmod × DD.C0) :
    kappa0 (datChi DD S hσ χ) p q
      = gamma2 S hσ χ p.2 (p.2 • q.1)
        + (gchi S hσ χ (pmul p q).1 + gchi S hσ χ p.1 + gchi S hσ χ q.1) := by
  show χ.1 (mDef DD S p.1 (p.2 • q.1)) + χ.1 (conjDef DD S hσ p.2 q.1) = _
  unfold gamma2
  rw [inv_smul_smul]
  have hg := gchi_split S hσ χ p.1 (p.2 • q.1)
  have hpm : (pmul p q).1 = p.1 + p.2 • q.1 := rfl
  rw [hpm]
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf))) hg

/-- The total scalar phase input `δtot_χ := e_χ + δκ`. -/
noncomputable def deltatot (χ : ↥(TCharC D)) (cc dd : DD.C0) : ZMod 2 :=
  χ.1 (uDef DD S cc dd) + dkap σ Dsc hσ cc dd

/-- The combined coboundary potential `W_χ`. -/
noncomputable def wtot (χ : ↥(TCharC D)) (x : DD.Vmod × DD.C0) : ZMod 2 :=
  gchi S hσ χ x.1 + gkappa σ Dsc hσ x.1 + ukap σ Dsc hσ x.1 x.2

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The `Ψ_χ`-normal form** (design §6): the full obstruction cochain is
`κ⁰ + Γγtot + inf δtot + ∂W_χ`, pointwise. -/
theorem psi_decomp (χ : ↥(TCharC D)) (p q : DD.Vmod × DD.C0) :
    χ.1 (JDefT S hσ p q) + kfull σ Dsc p q
      = kappa0 DD.dat p q
        + gammatot S Dsc hσ χ p.2 (p.2 • q.1)
        + deltatot S Dsc hσ χ p.2 q.2
        + (wtot S Dsc hσ χ (pmul p q) + wtot S Dsc hσ χ p + wtot S Dsc hσ χ q) := by
  obtain ⟨v, cc⟩ := p
  obtain ⟨w, dd⟩ := q
  have h1 := chiJDef_eq S hσ χ (v, cc) (w, dd)
  have h2 := kappa0_datChi_decomp S hσ χ (v, cc) (w, dd)
  have h3 := theta'_decomp σ Dsc hσ v cc w dd
  -- `θ'` unfolded back to `kfull + κ⁰ + ∂gκ`
  have h4 : theta' σ Dsc hσ ((v, cc) : DD.Vmod × DD.C0) (w, dd)
      = kfull σ Dsc ((v, cc) : DD.Vmod × DD.C0) (w, dd)
        + kappa0 DD.dat ((v, cc) : DD.Vmod × DD.C0) (w, dd)
        + (gkappa σ Dsc hσ (pmul ((v, cc) : DD.Vmod × DD.C0) (w, dd)).1
            + gkappa σ Dsc hσ v + gkappa σ Dsc hσ w) := rfl
  -- `γκ`-value at the calibrated argument
  have h5 : gammakap σ Dsc hσ cc (cc • w)
      = gkraw σ Dsc hσ cc w + ukap σ Dsc hσ (cc • w) cc := by
    unfold gammakap
    rw [inv_smul_smul]
  have hpm : pmul ((v, cc) : DD.Vmod × DD.C0) (w, dd) = (v + cc • w, cc * dd) := rfl
  unfold gammatot deltatot wtot
  rw [hpm] at h2 h4 ⊢
  simp only at h1 h2 h3 h4 ⊢
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
    h1 + h2 + h3 + h4 + h5

end Assembly

/-! ## Stage E: the keystone (design §6 — the (135)-Γ completed square)

Pulling the `Ψ_χ`-normal form back along the graph of `c` and completing the square with
`prop_8_8_target` at the shear family `a_χ` yields the master count's `hkey`:

  `β_χ(c) + β_ξ(c) = Q⁰(c + sh_χ) + ι_Γ(ρ'^* Δ_χ)`

at `Δ_χ := DeltaScalar (γtot_χ, δtot_χ, a_χ)` and `sh_χ := a_χ ∘ ρ'`.  The only Γ-residues
are `htriv` and `hH2`; everything else is the C-level data landed above. -/

section Keystone

open SectionSix

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ]
variable {ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M)}
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
variable (hinvQ : IsInvariant DD.C0 DD.qbar)

/-- **The shear cocycle** `sh_χ := a_χ ∘ ρ'`: the (133) shift-vector family as a crossed
`V`-cocycle (continuity through the discrete `Bg ⧸ M`). -/
noncomputable def shChi (χ : ↥(TCharC D)) : VCocycle DD ρ where
  c := fun γ => achi S Dsc hσ χ (rho0 DD ρ γ)
  cont := by
    haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
    have h : (fun γ => iV DD (Multiplicative.ofAdd (achi S Dsc hσ χ (rho0 DD ρ γ))))
        = (fun x : Bg ⧸ D.M => iV DD (Multiplicative.ofAdd (achi S Dsc hσ χ (liftC0 DD x))))
          ∘ ρ := rfl
    rw [h]
    exact continuous_of_discreteTopology.comp ρ.continuous_toFun
  crossed := fun γ δ => by
    rw [map_mul]
    exact achi_crossed S Dsc hσ hinvQ χ (rho0 DD ρ γ) (rho0 DD ρ δ)

/-- **The total scalar phase family** `Δ_χ` (the (134) total phase `Δ_{χ,κ}`, C-level). -/
noncomputable def DeltaChi (χ : ↥(TCharC D)) : DD.C0 × DD.C0 → ZMod 2 :=
  DeltaScalar DD.dat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ)

variable [IsTopologicalGroup Γ] [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- **Generic-Γ well-formedness of the graph pullback** (Lemma 6.1/(62); the `G_ℚ₂`-bound
ancestor is `SectionSix.graphPullback_mem_Z2`): along a crossed cocycle, the pullback of the
equivariant base datum is a continuous 2-cocycle. -/
theorem graphPullback_mem_Z2_of_cocycle (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (c : VCocycle DD ρ) :
    graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c ∈ Z2 Γ (ZMod 2) := by
  classical
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  refine mem_Z2_iff.mpr ⟨?_, fun g h k => ?_⟩
  · -- continuity: factor through the discrete `(Q × B/M) × (Q × B/M)`
    have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b hab => iV_ofAdd_inj DD hab
    have heq : graphPullback DD.dat (fun γ => rho0 DD ρ γ) c.c
        = (fun t : ((Bg ⧸ D.T) × (Bg ⧸ D.M)) × ((Bg ⧸ D.T) × (Bg ⧸ D.M)) =>
            DD.dat.f
              (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.1.1)
              (liftC0 DD t.1.2
                • Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.2.1)
            + DD.dat.m (liftC0 DD t.1.2)
                (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.2.1))
          ∘ (fun p : Γ × Γ => ((iV DD (Multiplicative.ofAdd (c.c p.1)), ρ p.1),
              (iV DD (Multiplicative.ofAdd (c.c p.2)), ρ p.2))) := by
      funext p
      show DD.dat.f (c.c p.1) (rho0 DD ρ p.1 • c.c p.2) + DD.dat.m (rho0 DD ρ p.1) (c.c p.2)
        = DD.dat.f
            (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
              (iV DD (Multiplicative.ofAdd (c.c p.1))))
            (liftC0 DD (ρ p.1)
              • Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
                  (iV DD (Multiplicative.ofAdd (c.c p.2))))
          + DD.dat.m (liftC0 DD (ρ p.1))
              (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
                (iV DD (Multiplicative.ofAdd (c.c p.2))))
      rw [Function.leftInverse_invFun hinj (c.c p.1), Function.leftInverse_invFun hinj (c.c p.2)]
      rfl
    rw [heq]
    exact continuous_of_discreteTopology.comp
      (((c.cont.comp continuous_fst).prodMk (ρ.continuous_toFun.comp continuous_fst)).prodMk
        ((c.cont.comp continuous_snd).prodMk (ρ.continuous_toFun.comp continuous_snd)))
  · -- the cocycle identity: (59) + (60) + the factor-set identity, in char 2
    rw [htriv]
    show DD.dat.f (c.c h) (rho0 DD ρ h • c.c k) + DD.dat.m (rho0 DD ρ h) (c.c k)
        + (DD.dat.f (c.c g) (rho0 DD ρ g • c.c (h * k)) + DD.dat.m (rho0 DD ρ g) (c.c (h * k)))
      = DD.dat.f (c.c (g * h)) (rho0 DD ρ (g * h) • c.c k)
          + DD.dat.m (rho0 DD ρ (g * h)) (c.c k)
        + (DD.dat.f (c.c g) (rho0 DD ρ g • c.c h) + DD.dat.m (rho0 DD ρ g) (c.c h))
    have hbk : c.c (h * k) = c.c h + rho0 DD ρ h • c.c k := c.crossed h k
    have hbg : c.c (g * h) = c.c g + rho0 DD ρ g • c.c h := c.crossed g h
    have hρm : rho0 DD ρ (g * h) = rho0 DD ρ g * rho0 DD ρ h := map_mul _ g h
    rw [hbk, hbg, hρm, smul_add, ← mul_smul]
    have h59 := DD.hdat.m_quad (rho0 DD ρ g) (c.c h) (rho0 DD ρ h • c.c k)
    have h60 := DD.hdat.m_mul (rho0 DD ρ g) (rho0 DD ρ h) (c.c k)
    have hco := DD.hdat.f_cocycle (c.c g) (rho0 DD ρ g • c.c h)
      ((rho0 DD ρ g * rho0 DD ρ h) • c.c k)
    rw [← mul_smul] at h59
    linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
      h59 + h60 + hco

omit [IsTopologicalGroup Γ] [ContinuousSMul Γ (ZMod 2)] in
/-- The graph-coboundary of any pair potential along a crossed cocycle is a continuous
coboundary (the `∂`-terms of the `Ψ_χ`-pullback). -/
theorem graphCob_mem_B2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (u : DD.Vmod × DD.C0 → ZMod 2) (cx : VCocycle DD ρ) :
    (fun p : Γ × Γ => u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + u (cx.c p.1, rho0 DD ρ p.1) + u (cx.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) := by
  classical
  haveI : DiscreteTopology (Bg ⧸ D.M) := CentralObstruction.discreteTopology_quotient D
  refine ⟨fun γ => u (cx.c γ, rho0 DD ρ γ), ?_, ?_⟩
  · have hinj : Function.Injective (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) :=
      fun a b hab => iV_ofAdd_inj DD hab
    have heq : (fun γ => u (cx.c γ, rho0 DD ρ γ))
        = (fun t : (Bg ⧸ D.T) × (Bg ⧸ D.M) =>
            u (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v)) t.1,
              liftC0 DD t.2))
          ∘ (fun γ => (iV DD (Multiplicative.ofAdd (cx.c γ)), ρ γ)) := by
      funext γ
      show u (cx.c γ, rho0 DD ρ γ)
        = u (Function.invFun (fun v : DD.Vmod => iV DD (Multiplicative.ofAdd v))
            (iV DD (Multiplicative.ofAdd (cx.c γ))), liftC0 DD (ρ γ))
      rw [Function.leftInverse_invFun hinj (cx.c γ)]
      rfl
    rw [heq]
    exact continuous_of_discreteTopology.comp (cx.cont.prodMk ρ.continuous_toFun)
  · funext p
    show p.1 • u (cx.c p.2, rho0 DD ρ p.2) - u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + u (cx.c p.1, rho0 DD ρ p.1)
      = u (cx.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2)) + u (cx.c p.1, rho0 DD ρ p.1)
        + u (cx.c p.2, rho0 DD ρ p.2)
    rw [htriv]
    have hchar : ∀ a b cc : ZMod 2, a - b + cc = b + cc + a := by decide
    exact hchar _ _ _

include hinvQ in
/-- **The keystone** (Prop 8.8's completed square (135) at Γ-level, design §6): the master
count's `hkey` at `Δ := DeltaChi` and `sh := shChi`.  Only `htriv` and `hH2` are Γ-residues. -/
theorem keystone (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (hH2 : Nat.card (H2 Γ (ZMod 2)) = 2)
    (χ : ↥(TCharC D)) (c : VCocycle DD ρ) :
    betaChi S hσ χ c + betaXi hσ Dsc c
      = QZero DD ρ (c + shChi S Dsc hσ hinvQ χ)
        + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (DeltaChi S Dsc hσ χ)) := by
  classical
  set c₀ : VCocycle DD ρ := c + shChi S Dsc hσ hinvQ χ with hc₀
  -- the completed square at the keystone data
  obtain ⟨w, hw⟩ := prop_8_8_target DD.qbar DD.hquad DD.dat DD.hdat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ) (achi_crossed S Dsc hσ hinvQ χ) (achi_kill S Dsc hσ χ)
  -- the exponent-2 shear collapse: `s_a(graph c₀) = graph c`
  have hcol : ∀ γ' : Γ, shear (achi S Dsc hσ χ) (c₀.c γ', rho0 DD ρ γ')
      = (c.c γ', rho0 DD ρ γ') := by
    intro γ'
    have h1 : c₀.c γ' = c.c γ' + achi S Dsc hσ χ (rho0 DD ρ γ') := by rw [hc₀]; rfl
    show (c₀.c γ' + achi S Dsc hσ χ (rho0 DD ρ γ'), rho0 DD ρ γ') = (c.c γ', rho0 DD ρ γ')
    rw [h1, add_assoc, Vmod_exp2 DD, add_zero]
  -- pointwise: the `Ψ_χ`-pullback of the completed square
  have hpoint : ∀ γ δ : Γ,
      chiDef S hσ χ c (γ, δ) + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) (γ, δ)
        = graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c (γ, δ)
            + pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) (γ, δ)
          + ((w (c₀.c (γ * δ), rho0 DD ρ (γ * δ)) + w (c₀.c γ, rho0 DD ρ γ)
                + w (c₀.c δ, rho0 DD ρ δ))
              + (wtot S Dsc hσ χ (c.c (γ * δ), rho0 DD ρ (γ * δ))
                + wtot S Dsc hσ χ (c.c γ, rho0 DD ρ γ)
                + wtot S Dsc hσ χ (c.c δ, rho0 DD ρ δ))) := by
    intro γ δ
    have hχval : chiDef S hσ χ c (γ, δ)
        = χ.1 (JDefT S hσ (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)) := by
      have h := tDef_eq_JDefT S hσ c (γ, δ)
      simp only at h
      exact congrArg χ.1 h
    have hξval : pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) (γ, δ)
        = kfull σ Dsc (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ) := rfl
    have hpsi := psi_decomp S Dsc hσ χ (c.c γ, rho0 DD ρ γ) (c.c δ, rho0 DD ρ δ)
    rw [graph_pmul c γ δ] at hpsi
    simp only at hpsi
    have h88 := hw (c₀.c γ, rho0 DD ρ γ) (c₀.c δ, rho0 DD ρ δ)
    rw [hcol γ, hcol δ] at h88
    simp only [gammaEdge, inflScalar, AddMonoidHom.mk'_apply] at h88
    rw [show c₀.c γ + rho0 DD ρ γ • c₀.c δ = c₀.c (γ * δ) from (c₀.crossed γ δ).symm,
      show rho0 DD ρ γ * rho0 DD ρ δ = rho0 DD ρ (γ * δ) from (map_mul (rho0 DD ρ) γ δ).symm]
      at h88
    have hQval : graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c (γ, δ)
        = kappa0 DD.dat (c₀.c γ, rho0 DD ρ γ) (c₀.c δ, rho0 DD ρ δ) := rfl
    have hΔval : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) (γ, δ)
        = DeltaScalar DD.dat
            (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
            (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
            (achi S Dsc hσ χ) (rho0 DD ρ γ, rho0 DD ρ δ) := rfl
    linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero]); (try ring_nf)))
      hχval + hξval + hpsi + h88 + hQval + hΔval
  -- memberships
  have hZχ : chiDef S hσ χ c ∈ Z2 Γ (ZMod 2) := chiDef_mem_Z2 S hσ htriv χ c
  have hZξ : pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc) ∈ Z2 Γ (ZMod 2) :=
    pullCoc_mem_Z2 htriv (qOfCocycle DD ρ σ hσ c).1 (fun g h k => xi_cocycle Dsc g h k)
  have hZQ : graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c ∈ Z2 Γ (ZMod 2) :=
    graphPullback_mem_Z2_of_cocycle htriv c₀
  have hBw : (fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
      + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) :=
    graphCob_mem_B2 htriv w c₀
  have hBW : (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
      + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
      + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2)) ∈ B2 Γ (ZMod 2) :=
    graphCob_mem_B2 htriv (wtot S Dsc hσ χ) c
  have hBΨ : ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
      + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
        + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
        + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) ∈ B2 Γ (ZMod 2) :=
    AddSubgroup.add_mem _ hBw hBW
  -- the function-level identity
  have hfun : chiDef S hσ χ c + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc)
      = (graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c
          + pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ))
        + ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
            + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
          + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
            + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
            + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) := by
    funext p
    obtain ⟨γ, δ⟩ := p
    exact hpoint γ δ
  -- Z²-membership of the Δ-pullback, by subtraction
  have hZΔ : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ) ∈ Z2 Γ (ZMod 2) := by
    have hrew : pullCoc (fun γ' => rho0 DD ρ γ') (DeltaChi S Dsc hσ χ)
        = (chiDef S hσ χ c + pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc)
            - graphPullback DD.dat (fun γ' => rho0 DD ρ γ') c₀.c)
          - ((fun p : Γ × Γ => w (c₀.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
              + w (c₀.c p.1, rho0 DD ρ p.1) + w (c₀.c p.2, rho0 DD ρ p.2))
            + (fun p : Γ × Γ => wtot S Dsc hσ χ (c.c (p.1 * p.2), rho0 DD ρ (p.1 * p.2))
              + wtot S Dsc hσ χ (c.c p.1, rho0 DD ρ p.1)
              + wtot S Dsc hσ χ (c.c p.2, rho0 DD ρ p.2))) := by
      rw [hfun]
      abel
    rw [hrew]
    exact AddSubgroup.sub_mem _
      (AddSubgroup.sub_mem _ (AddSubgroup.add_mem _ hZχ hZξ) hZQ) (B2_le_Z2 hBΨ)
  -- `ι_Γ`-assembly
  show iotaB (chiDef S hσ χ c) + iotaB (pullCoc (⇑(qOfCocycle DD ρ σ hσ c).1) (xi Dsc))
    = iotaB (graphPullback DD.dat (fun γ => rho0 DD ρ γ) c₀.c)
      + iotaB (pullCoc (fun γ => rho0 DD ρ γ) (DeltaChi S Dsc hσ χ))
  rw [← iotaB_add hH2 hZχ hZξ, hfun,
    iotaB_add hH2 (AddSubgroup.add_mem _ hZQ hZΔ) (B2_le_Z2 hBΨ),
    iotaB_add hH2 hZQ hZΔ, iotaB_of_mem_B2 hBΨ, add_zero]

end Keystone

/-! ## Stage F: the phase-cover data (design §6, c2)

`centralCoverOfCocycle` consumes a **normalized raw 2-cocycle** on `C₀`.  Here we supply the
three inputs for `Δ_χ`: the Serre identity (`DeltaChi_cocycle` — the completed square on the
`(0,·)`-section minus the bundle/base/coboundary Serre identities) and the two normalizations
(`DeltaChi_one_left`/`right` — from the landed normalization atoms).  All C-level. -/

section PhaseData

open SectionSix

variable {DD : DescData D} {σ : DD.C0 →* Bg ⧸ D.T} (S : CountSections DD σ)
variable (Dsc : Descent D)
variable (hσ : ∀ cc : DD.C0, piQbar DD (σ cc) = cc)
variable (hinvQ : IsInvariant DD.C0 DD.qbar)

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `Θ'` vanishes on `pone`-rows. -/
theorem theta'_pone_left (q : DD.Vmod × DD.C0) : theta' σ Dsc hσ pone q = 0 := by
  unfold theta'
  rw [theta_pone_left, pone_pmul]
  show 0 + (gkappa σ Dsc hσ q.1 + gkappa σ Dsc hσ 0 + gkappa σ Dsc hσ q.1) = 0
  rw [gkappa_zero, zero_add, add_zero]
  exact CharTwo.add_self_eq_zero _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `Θ'` vanishes on `pone`-columns. -/
theorem theta'_pone_right (p : DD.Vmod × DD.C0) : theta' σ Dsc hσ p pone = 0 := by
  unfold theta'
  rw [theta_pone_right, pmul_pone]
  show 0 + (gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ p.1 + gkappa σ Dsc hσ 0) = 0
  rw [gkappa_zero, zero_add, add_zero]
  exact CharTwo.add_self_eq_zero _

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `uσ`-defect normalization, left. -/
theorem uDef_one_left (cc : DD.C0) : uDef DD S 1 cc = 1 := by
  apply Subtype.ext
  show S.uσ 1 * S.uσ cc * (S.uσ (1 * cc))⁻¹ = 1
  rw [S.uσ_one, one_mul, one_mul, mul_inv_cancel]

omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `uσ`-defect normalization, right. -/
theorem uDef_one_right (cc : DD.C0) : uDef DD S cc 1 = 1 := by
  apply Subtype.ext
  show S.uσ cc * S.uσ 1 * (S.uσ (cc * 1))⁻¹ = 1
  rw [S.uσ_one, mul_one, mul_one, mul_inv_cancel]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γtot_χ(cc)` kills `0`. -/
theorem gammatot_zero (χ : ↥(TCharC D)) (cc : DD.C0) : gammatot S Dsc hσ χ cc 0 = 0 := by
  have h := gammatot_add S Dsc hσ χ cc 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `γtot_χ(1) = 0` (the edge is normalized at the identity). -/
theorem gammatot_one (χ : ↥(TCharC D)) (x : DD.Vmod) : gammatot S Dsc hσ χ 1 x = 0 := by
  unfold gammatot
  have h2 : gamma2 S hσ χ 1 x = 0 := by
    unfold gamma2
    rw [inv_one, one_smul, conjDef_one_left, TCharC.map_one, zero_add]
    exact CharTwo.add_self_eq_zero _
  have hk : gammakap σ Dsc hσ 1 x = 0 := by
    unfold gammakap gkraw ukap
    rw [inv_one, one_smul, theta'_VV σ Dsc hσ 0 x, theta'_VV σ Dsc hσ x 0, add_zero]
  rw [h2, hk, add_zero]

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- The shear family is normalized: `a_χ(1) = 0`. -/
theorem achi_one (χ : ↥(TCharC D)) : achi S Dsc hσ χ 1 = 0 := by
  have h := achi_crossed S Dsc hσ hinvQ χ 1 1
  rw [mul_one, one_smul] at h
  exact left_eq_add.mp h

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `δtot_χ` is normalized on the left. -/
theorem deltatot_one_left (χ : ↥(TCharC D)) (cc : DD.C0) : deltatot S Dsc hσ χ 1 cc = 0 := by
  unfold deltatot
  rw [uDef_one_left S cc, TCharC.map_one]
  have hd : dkap σ Dsc hσ 1 cc = 0 := by
    show theta' σ Dsc hσ pone (0, cc) = 0
    exact theta'_pone_left Dsc hσ (0, cc)
  rw [hd, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- `δtot_χ` is normalized on the right. -/
theorem deltatot_one_right (χ : ↥(TCharC D)) (cc : DD.C0) : deltatot S Dsc hσ χ cc 1 = 0 := by
  unfold deltatot
  rw [uDef_one_right S cc, TCharC.map_one]
  have hd : dkap σ Dsc hσ cc 1 = 0 := by
    show theta' σ Dsc hσ ((0, cc) : DD.Vmod × DD.C0) pone = 0
    exact theta'_pone_right Dsc hσ ((0, cc) : DD.Vmod × DD.C0)
  rw [hd, add_zero]

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Serre identity for `χ ∘ JDefT`**: the associativity defect of the product lift `Jmap`
conjugates by `Jmap p`, and the `C`-invariance of `χ` kills the conjugation. -/
theorem chiJDefT_serre (χ : ↥(TCharC D)) (p q r : DD.Vmod × DD.C0) :
    χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r))
      = χ.1 (JDefT S hσ (pmul p q) r) + χ.1 (JDefT S hσ p q) := by
  -- the nonabelian defect identity, raw
  have hraw : (JDefT S hσ p q : Bg) * (JDefT S hσ (pmul p q) r : Bg)
      = Jmap S p * (JDefT S hσ q r : Bg) * (Jmap S p)⁻¹ * (JDefT S hσ p (pmul q r) : Bg) := by
    show Jmap S p * Jmap S q * (Jmap S (pmul p q))⁻¹
          * (Jmap S (pmul p q) * Jmap S r * (Jmap S (pmul (pmul p q) r))⁻¹)
        = Jmap S p * (Jmap S q * Jmap S r * (Jmap S (pmul q r))⁻¹) * (Jmap S p)⁻¹
          * (Jmap S p * Jmap S (pmul q r) * (Jmap S (pmul p (pmul q r)))⁻¹)
    rw [pmul_assoc]
    group
  -- lift to the subtype and push through `χ`
  have hsub : JDefT S hσ p q * JDefT S hσ (pmul p q) r
      = (⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
          D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T)
        * JDefT S hσ p (pmul q r) := by
    apply Subtype.ext
    show (JDefT S hσ p q : Bg) * (JDefT S hσ (pmul p q) r : Bg)
      = Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹ * ↑(JDefT S hσ p (pmul q r))
    exact hraw
  have hkey : χ.1 (JDefT S hσ p q) + χ.1 (JDefT S hσ (pmul p q) r)
      = χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r)) := by
    calc χ.1 (JDefT S hσ p q) + χ.1 (JDefT S hσ (pmul p q) r)
        = χ.1 (JDefT S hσ p q * JDefT S hσ (pmul p q) r) := (TCharC.map_mul χ _ _).symm
      _ = χ.1 ((⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
            D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T) * JDefT S hσ p (pmul q r)) := by
          rw [hsub]
      _ = χ.1 (⟨Jmap S p * ↑(JDefT S hσ q r) * (Jmap S p)⁻¹,
            D.hT.conj_mem _ (JDefT S hσ q r).2 _⟩ : ↥D.T)
          + χ.1 (JDefT S hσ p (pmul q r)) := TCharC.map_mul χ _ _
      _ = χ.1 (JDefT S hσ q r) + χ.1 (JDefT S hσ p (pmul q r)) := by
          rw [TCharC.conj_invariant χ (Jmap S p) (JDefT S hσ q r)]
  linear_combination (norm := (ring_nf; try simp [CharTwo.two_eq_zero])) hkey

include hσ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Serre identity for the `Ψ_χ`-bundle** `κ⁰ + Γγtot + inf δtot`, by the `psi_decomp`
normal form and the three component Serre identities. -/
theorem bundle_serre (χ : ↥(TCharC D)) (p q r : DD.Vmod × DD.C0) :
    (kappa0 DD.dat q r + gammatot S Dsc hσ χ q.2 (q.2 • r.1) + deltatot S Dsc hσ χ q.2 r.2)
      + (kappa0 DD.dat p (pmul q r)
        + gammatot S Dsc hσ χ p.2 (p.2 • (pmul q r).1) + deltatot S Dsc hσ χ p.2 (pmul q r).2)
    = (kappa0 DD.dat (pmul p q) r
        + gammatot S Dsc hσ χ (pmul p q).2 ((pmul p q).2 • r.1)
        + deltatot S Dsc hσ χ (pmul p q).2 r.2)
      + (kappa0 DD.dat p q + gammatot S Dsc hσ χ p.2 (p.2 • q.1)
        + deltatot S Dsc hσ χ p.2 q.2) := by
  have h1 := psi_decomp S Dsc hσ χ q r
  have h2 := psi_decomp S Dsc hσ χ p (pmul q r)
  have h3 := psi_decomp S Dsc hσ χ (pmul p q) r
  have h4 := psi_decomp S Dsc hσ χ p q
  have hj := chiJDefT_serre S hσ χ p q r
  have hk := kfull_serre σ Dsc hσ p q r
  have hpw := pcob_serre (DD := DD) (wtot S Dsc hσ χ) p q r
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
    show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
    h1 + h2 + h3 + h4 + hj + hk + hpw

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **The phase-cover cocycle law** (`hcoc` of `centralCoverOfCocycle`): `Δ_χ` satisfies the
raw Serre identity on `C₀` — the completed square on the `(0,·)`-section, minus the
bundle/base/coboundary Serre identities. -/
theorem DeltaChi_cocycle (χ : ↥(TCharC D)) (g h k : DD.C0) :
    DeltaChi S Dsc hσ χ (h, k) + DeltaChi S Dsc hσ χ (g, h * k)
      = DeltaChi S Dsc hσ χ (g * h, k) + DeltaChi S Dsc hσ χ (g, h) := by
  obtain ⟨w, hw⟩ := prop_8_8_target DD.qbar DD.hquad DD.dat DD.hdat
    (fun cc => AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
    (fun cd => deltatot S Dsc hσ χ cd.1 cd.2)
    (achi S Dsc hσ χ) (achi_crossed S Dsc hσ hinvQ χ) (achi_kill S Dsc hσ χ)
  -- the `(0,·)`-section, its shear, and their `pmul`-multiplicativity
  have hsh : ∀ x : DD.C0, shear (achi S Dsc hσ χ) ((0, x) : DD.Vmod × DD.C0)
      = (achi S Dsc hσ χ x, x) := by
    intro x
    show ((0 : DD.Vmod) + achi S Dsc hσ χ x, x) = (achi S Dsc hσ χ x, x)
    rw [zero_add]
  have hpm0 : ∀ x y : DD.C0, pmul ((0, x) : DD.Vmod × DD.C0) (0, y) = (0, x * y) := by
    intro x y
    show ((0 : DD.Vmod) + x • (0 : DD.Vmod), x * y) = (0, x * y)
    rw [smul_zero, add_zero]
  have hpma : ∀ x y : DD.C0,
      pmul ((achi S Dsc hσ χ x, x) : DD.Vmod × DD.C0) (achi S Dsc hσ χ y, y)
        = (achi S Dsc hσ χ (x * y), x * y) := by
    intro x y
    show (achi S Dsc hσ χ x + x • achi S Dsc hσ χ y, x * y)
      = (achi S Dsc hσ χ (x * y), x * y)
    rw [← achi_crossed S Dsc hσ hinvQ χ x y]
  -- four completed squares on the section
  have h1 := hw (0, h) (0, k)
  have h2 := hw (0, g) (0, h * k)
  have h3 := hw (0, g * h) (0, k)
  have h4 := hw (0, g) (0, h)
  simp only [hsh, gammaEdge, inflScalar, AddMonoidHom.mk'_apply, smul_zero, add_zero]
    at h1 h2 h3 h4
  -- the bundle Serre at the sheared section, the base and coboundary Serre on the section
  have hb := bundle_serre S Dsc hσ χ (achi S Dsc hσ χ g, g) (achi S Dsc hσ χ h, h)
    (achi S Dsc hσ χ k, k)
  simp only [hpma] at hb
  have hk0 := kappa0_serre (DD := DD) DD.hdat ((0, g) : DD.Vmod × DD.C0) (0, h) (0, k)
  have hpw := pcob_serre (DD := DD) w ((0, g) : DD.Vmod × DD.C0) (0, h) (0, k)
  simp only [hpm0] at hk0 hpw
  simp only [DeltaChi]
  linear_combination (norm := (ring_nf; (try simp [CharTwo.two_eq_zero,
    show (4 : ZMod 2) = 0 from by decide]); (try ring_nf)))
    h1 + h2 + h3 + h4 + hb + hk0 + hpw

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Left normalization** (`hl` of `centralCoverOfCocycle`): `Δ_χ(1, ·) = 0`. -/
theorem DeltaChi_one_left (χ : ↥(TCharC D)) (cc : DD.C0) :
    DeltaChi S Dsc hσ χ (1, cc) = 0 := by
  show deltatot S Dsc hσ χ 1 cc
      + (DD.dat.f (achi S Dsc hσ χ 1) ((1 : DD.C0) • achi S Dsc hσ χ cc)
        + DD.dat.m 1 (achi S Dsc hσ χ cc))
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ 1) (gammatot_add S Dsc hσ χ 1))
          ((1 : DD.C0) • achi S Dsc hσ χ cc)
    = 0
  rw [deltatot_one_left S Dsc hσ χ cc, achi_one S Dsc hσ hinvQ χ, one_smul,
    DD.hdat.f_zero_left, DD.hdat.m_one, AddMonoidHom.mk'_apply,
    gammatot_one S Dsc hσ χ (achi S Dsc hσ χ cc)]
  decide

include hinvQ in
omit [TopologicalSpace Bg] [DiscreteTopology Bg] in
/-- **Right normalization** (`hr` of `centralCoverOfCocycle`): `Δ_χ(·, 1) = 0`. -/
theorem DeltaChi_one_right (χ : ↥(TCharC D)) (cc : DD.C0) :
    DeltaChi S Dsc hσ χ (cc, 1) = 0 := by
  show deltatot S Dsc hσ χ cc 1
      + (DD.dat.f (achi S Dsc hσ χ cc) (cc • achi S Dsc hσ χ 1)
        + DD.dat.m cc (achi S Dsc hσ χ 1))
      + (AddMonoidHom.mk' (gammatot S Dsc hσ χ cc) (gammatot_add S Dsc hσ χ cc))
          (cc • achi S Dsc hσ χ 1)
    = 0
  rw [deltatot_one_right S Dsc hσ χ cc, achi_one S Dsc hσ hinvQ χ, smul_zero,
    DD.hdat.f_zero_right, m_zero (DD := DD) DD.hdat cc, AddMonoidHom.mk'_apply,
    gammatot_zero S Dsc hσ χ cc]
  decide

end PhaseData

end AffineTLift

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 6.1 = ⟦lem-extraspecialconnecting⟧
  * Lemma 8.7 = ⟦lem-affinelifting⟧
  * Prop 8.8 = ⟦prop-phaseidentity⟧
-/
