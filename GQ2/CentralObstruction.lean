import GQ2.RadicalEdge.Data
import GQ2.Cohomology

/-!
# The central-obstruction engine for Lemma 8.6  (ticket P-16a)

The Γ-generic machinery behind the §8 half-torsor count (`docs/p16-ticket-split.md`,
`docs/section8-extraction.md` §"O-half work order" item 3), faithful to the paper's proof of
Lemma 8.6:

* **kernel-sign calculus** `zsign` on the central double cover (`ker p = {1, z} ≅ 𝔽₂`);
* the **commutator/square ledger** of the cover over `M` (`x̃ỹ = ỹx̃·z^{B_q}`, from `hq`);
* the **linear complement** `s(T)` to `⟨z⟩` in `p⁻¹(T)` (`TComplement`, exists since `p⁻¹(T)`
  is elementary abelian — `q|_T = 0` and `T ⊆ rad B_q`);
* the **edge cocycle** `edge b t` of (128) — the conjugation defect of the complement — with
  its crossed-cocycle law, additivity, `M`-invariance, and the **descent construction**
  (`not_noDescent_of_edge_trivial`: a crossed trivialization of the edge produces the normal
  complement, refuting `NoDescent`);
* the **twist involution** on `MLifts` by continuous crossed `T`-cocycles (`TCocycle`,
  `twist`);
* the **scalar obstruction class** `ob f ∈ H²(Γ, 𝔽₂)` (`Central f ↔ ob f = 0`) and the exact
  **variation formula (129)**: `ob (twist u f) = ob f + [varCoc u]`, with the variation class
  independent of `f`;
* the assembled **abstract half-count** `half_count`: a twist with nonzero variation class
  swaps `Central` and its complement, so exactly half the `M`-lifts are central.

The per-source content — producing the nonzero-variation twist from `NoDescent` (B6 for the
local source, 5.15/5.16 for the candidate source) — is P-16b/P-16c, in downstream files.
No axioms enter here; everything is std-3.
-/

namespace GQ2

namespace SectionEight

namespace CentralObstruction

open ContCoh

variable {Bg : Type} [Group Bg] [Finite Bg] (D : RadicalCoverData Bg)

/-! ## The kernel-sign calculus: `ker p = {1, z} ≅ 𝔽₂` -/

/-- The `z`-logarithm on the cover: `0` at `1`, `1` elsewhere — meaningful on `ker p = {1,z}`. -/
noncomputable def zsign (x : D.C.cover) : ZMod 2 :=
  letI := Classical.dec (x = 1)
  if x = 1 then 0 else 1

@[simp] theorem zsign_one : zsign D 1 = 0 := by simp [zsign]

theorem zsign_z : zsign D D.C.z = 1 := by simp [zsign, D.C.z_ne]

/-- `z` is in the kernel. -/
theorem z_mem_ker : D.C.z ∈ D.C.p.ker := D.C.ker_eq ▸ Subgroup.mem_zpowers _

/-- `p z = 1`. -/
theorem p_z_eq_one : D.C.p D.C.z = 1 := MonoidHom.mem_ker.mp (z_mem_ker D)

/-- The kernel of the cover has exactly the two elements `1` and `z`. -/
theorem ker_cases {x : D.C.cover} (hx : x ∈ D.C.p.ker) : x = 1 ∨ x = D.C.z := by
  rw [D.C.ker_eq, Subgroup.mem_zpowers_iff] at hx
  obtain ⟨n, rfl⟩ := hx
  have hz2 : D.C.z ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = 1 + 1 from rfl, zpow_add, zpow_one, D.C.z_sq]
  rcases Int.even_or_odd n with ⟨k, hk⟩ | ⟨k, hk⟩
  · left
    rw [hk, ← two_mul, zpow_mul, hz2, one_zpow]
  · right
    rw [hk, zpow_add, zpow_mul, hz2, one_zpow, one_mul, zpow_one]

/-- Reconstruction: a kernel element is `z` to its sign. -/
theorem z_pow_zsign {x : D.C.cover} (hx : x ∈ D.C.p.ker) :
    D.C.z ^ (zsign D x).val = x := by
  rcases ker_cases D hx with rfl | rfl
  · simp
  · rw [zsign_z, show ((1 : ZMod 2)).val = 1 by decide, pow_one]

/-- `zsign` is additive on the kernel. -/
theorem zsign_mul {x y : D.C.cover} (hx : x ∈ D.C.p.ker) (hy : y ∈ D.C.p.ker) :
    zsign D (x * y) = zsign D x + zsign D y := by
  rcases ker_cases D hx with rfl | rfl <;> rcases ker_cases D hy with rfl | rfl <;>
    simp [D.C.z_sq, zsign_z, zsign_one, CharTwo.add_self_eq_zero]

/-- Kernel elements are their own inverses. -/
theorem ker_inv_eq {x : D.C.cover} (hx : x ∈ D.C.p.ker) : x⁻¹ = x := by
  rcases ker_cases D hx with rfl | rfl
  · simp
  · exact inv_eq_of_mul_eq_one_left D.C.z_sq

/-- Kernel elements are central. -/
theorem ker_comm {d : D.C.cover} (hd : d ∈ D.C.p.ker) (w : D.C.cover) : d * w = w * d := by
  rcases ker_cases D hd with rfl | rfl
  · rw [one_mul, mul_one]
  · exact D.C.central w

/-- `zsign` of a `z`-power: `zsign (z^(a.val)) = a`. -/
theorem zsign_z_pow (a : ZMod 2) : zsign D (D.C.z ^ a.val) = a := by
  rcases ZMod.eq_zero_or_eq_one a with rfl | rfl
  · simp
  · rw [show ((1 : ZMod 2)).val = 1 by decide, pow_one, zsign_z]


/-! ## The cover ledger over `M`: squares and commutators -/

/-- Commutator membership: the commutator of two lifts of `M`-elements is in the kernel. -/
theorem comm_mem_ker {x y : D.C.cover} (hx : D.C.p x ∈ D.M) (hy : D.C.p y ∈ D.M) :
    y⁻¹ * x⁻¹ * y * x ∈ D.C.p.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hc : D.C.p x * D.C.p y = D.C.p y * D.C.p x := D.hcomm _ hx _ hy
  calc (D.C.p y)⁻¹ * (D.C.p x)⁻¹ * D.C.p y * D.C.p x
      = (D.C.p y)⁻¹ * (D.C.p x)⁻¹ * (D.C.p y * D.C.p x) := by group
    _ = (D.C.p y)⁻¹ * (D.C.p x)⁻¹ * (D.C.p x * D.C.p y) := by rw [← hc]
    _ = 1 := by group

/-- **The commutator/polar ledger** (extraspecial-style): for lifts `x, y` of `M`-elements,
`y·x = x·y·z^{B_q(px, py)}`.  Derived from `hq` (the square form) alone. -/
theorem mul_comm_z {x y : D.C.cover} (hx : D.C.p x ∈ D.M) (hy : D.C.p y ∈ D.M) :
    y * x = x * y * D.C.z ^ (polarMul D.q
      (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩) ⟨D.C.p x, hx⟩ ⟨D.C.p y, hy⟩).val := by
  -- `k := y⁻¹x⁻¹yx` is central of sign `q(pxpy) + q(px) + q(py)`.
  set k := y⁻¹ * x⁻¹ * y * x with hk
  have hkker : k ∈ D.C.p.ker := comm_mem_ker D hx hy
  have hkc : ∀ w : D.C.cover, k * w = w * k := by
    intro w
    rcases ker_cases D hkker with h | h
    · rw [h, one_mul, mul_one]
    · rw [h, D.C.central]
  have hyx : y * x = x * y * k := by rw [hk]; group
  have hxy : D.C.p (x * y) ∈ D.M := by rw [map_mul]; exact mul_mem hx hy
  have hker : ∀ a : ZMod 2, D.C.z ^ a.val ∈ D.C.p.ker := fun a => pow_mem (z_mem_ker D) _
  have hsq : (x * y) * (x * y) = D.C.z ^ (D.q ⟨D.C.p (x * y), hxy⟩).val := D.hq _ hxy
  have hsx : x * x = D.C.z ^ (D.q ⟨D.C.p x, hx⟩).val := D.hq _ hx
  have hsy : y * y = D.C.z ^ (D.q ⟨D.C.p y, hy⟩).val := D.hq _ hy
  -- expand `(xy)² = x(yx)y = x(xyk)y = x²·y²·k` using centrality of `k`
  have hexp : (x * y) * (x * y) = x * x * (y * y) * k := by
    calc (x * y) * (x * y) = x * (y * x) * y := by group
      _ = x * (x * y * k) * y := by rw [hyx]
      _ = x * x * y * (k * y) := by group
      _ = x * x * y * (y * k) := by rw [hkc]
      _ = x * x * (y * y) * k := by group
  -- solve for `k` as a product of `z`-powers (pure group identity)
  have hkval : k = (D.C.z ^ (D.q ⟨D.C.p x, hx⟩).val * D.C.z ^ (D.q ⟨D.C.p y, hy⟩).val)⁻¹
      * D.C.z ^ (D.q ⟨D.C.p (x * y), hxy⟩).val := by
    have h1 : D.C.z ^ (D.q ⟨D.C.p (x * y), hxy⟩).val
        = D.C.z ^ (D.q ⟨D.C.p x, hx⟩).val * D.C.z ^ (D.q ⟨D.C.p y, hy⟩).val * k := by
      rw [← hsx, ← hsy, ← hexp, hsq]
    rw [h1]
    group
  -- convert to the polar sign
  have hkz : zsign D k = polarMul D.q
      (fun a b => ⟨a.1 * b.1, mul_mem a.2 b.2⟩) ⟨D.C.p x, hx⟩ ⟨D.C.p y, hy⟩ := by
    have hprod : D.C.z ^ (D.q ⟨D.C.p x, hx⟩).val * D.C.z ^ (D.q ⟨D.C.p y, hy⟩).val
        ∈ D.C.p.ker := mul_mem (hker _) (hker _)
    have hinv := ker_inv_eq D hprod
    rw [hkval, hinv, zsign_mul D hprod (hker _), zsign_mul D (hker _) (hker _),
      zsign_z_pow, zsign_z_pow, zsign_z_pow]
    have hcast : D.q ⟨D.C.p (x * y), hxy⟩
        = D.q ⟨D.C.p x * D.C.p y, mul_mem hx hy⟩ := by
      congr 1
      exact Subtype.ext (map_mul _ _ _)
    rw [hcast]
    show _ = D.q ⟨D.C.p x * D.C.p y, _⟩ + D.q ⟨D.C.p x, hx⟩ + D.q ⟨D.C.p y, hy⟩
    ring
  calc y * x = x * y * k := hyx
    _ = x * y * D.C.z ^ (zsign D k).val := by rw [z_pow_zsign D hkker]
    _ = _ := by rw [hkz]

/-! ## The preimage of `T` and the linear complement `s(T)` -/

/-- Lifts of `T`-elements square to `1` (`q|_T = 0`). -/
theorem sq_eq_one_of_p_mem_T {x : D.C.cover} (hx : D.C.p x ∈ D.T) : x * x = 1 := by
  have hxM : D.C.p x ∈ D.M := D.hTM hx
  rw [D.hq x hxM, show D.q ⟨D.C.p x, hxM⟩ = 0 from D.hTzero _ hx,
    show ((0 : ZMod 2)).val = 0 by decide, pow_zero]

/-- Lifts of `T`-elements commute with all lifts of `M`-elements (`T ⊆ rad B_q`). -/
theorem comm_of_p_mem_T {x y : D.C.cover} (hx : D.C.p x ∈ D.T) (hy : D.C.p y ∈ D.M) :
    y * x = x * y := by
  rw [mul_comm_z D (D.hTM hx) hy, D.hrad _ hx _ hy,
    show ((0 : ZMod 2)).val = 0 by decide, pow_zero, mul_one]

/-- **The linear complement datum**: a homomorphic section `s : T → B̃` of `p` over `T`.
(The paper's complement `s(T)` to `⟨z⟩` in the elementary abelian `p⁻¹(T)`; `z ∉ range s` is
automatic since `s 1 = 1 ≠ z` and `p (s t) = t ≠ 1 = p z` otherwise.) -/
structure TComplement where
  /-- The section homomorphism. -/
  s : ↥D.T →* D.C.cover
  /-- It sections `p` over `T`. -/
  sect : ∀ t : ↥D.T, D.C.p (s t) = t

/-- **A linear complement exists**: split off `z` by an `𝔽₂`-functional on the elementary
abelian `p⁻¹(T)`. -/
theorem tComplement_nonempty : Nonempty (TComplement D) := by
  classical
  -- the preimage subgroup, elementary abelian
  set P : Subgroup D.C.cover := D.T.comap D.C.p with hP
  have hPelem : ∀ x : ↥P, x * x = 1 := by
    rintro ⟨x, hx⟩
    apply Subtype.ext
    show x * x = 1
    exact sq_eq_one_of_p_mem_T D (Subgroup.mem_comap.mp hx)
  have hPcomm : ∀ x y : ↥P, x * y = y * x := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    apply Subtype.ext
    show x * y = y * x
    exact comm_of_p_mem_T D (Subgroup.mem_comap.mp hy)
      (D.hTM (Subgroup.mem_comap.mp hx))
  have hzP : D.C.z ∈ P := by
    rw [hP, Subgroup.mem_comap, p_z_eq_one D]; exact one_mem _
  -- additivize: `A := Additive ↥P` is a finite elementary-2 `𝔽₂`-vector space
  letI : CommGroup ↥P := { (inferInstance : Group ↥P) with mul_comm := hPcomm }
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) (Additive ↥P) := AddCommGroup.zmodModule (fun x => by
    rw [two_nsmul]
    exact hPelem x.toMul)
  haveI : Module.Finite (ZMod 2) (Additive ↥P) := Module.Finite.of_finite
  -- a coordinate functional not vanishing on `z`
  obtain ⟨χ, hχ⟩ : ∃ χ : Additive ↥P →ₗ[ZMod 2] ZMod 2,
      χ (Additive.ofMul (⟨D.C.z, hzP⟩ : ↥P)) ≠ 0 := by
    by_contra! h
    set zP : Additive ↥P := Additive.ofMul (⟨D.C.z, hzP⟩ : ↥P) with hzPdef
    have hzero : zP = 0 := by
      let b := Module.Free.chooseBasis (ZMod 2) (Additive ↥P)
      refine b.forall_coord_eq_zero_iff.mp fun i => ?_
      simpa using h (b.coord i)
    have hone : (⟨D.C.z, hzP⟩ : ↥P) = 1 := by
      have h1 := congrArg Additive.toMul hzero
      rwa [show Additive.toMul zP = (⟨D.C.z, hzP⟩ : ↥P) from rfl,
        show Additive.toMul (0 : Additive ↥P) = (1 : ↥P) from rfl] at h1
    exact D.C.z_ne (congrArg Subtype.val hone)
  -- the complement: for `t ∈ T`, the unique lift in `ker χ`
  have hlift : ∀ t : ↥D.T, ∃ x : ↥P, D.C.p x.1 = t.1 ∧
      χ (Additive.ofMul x) = 0 := by
    intro t
    obtain ⟨x0, hx0⟩ := D.C.surj t.1
    have hx0P : x0 ∈ P := by rw [hP, Subgroup.mem_comap, hx0]; exact t.2
    by_cases hc : χ (Additive.ofMul (⟨x0, hx0P⟩ : ↥P)) = 0
    · exact ⟨⟨x0, hx0P⟩, hx0, hc⟩
    · refine ⟨⟨D.C.z * x0, mul_mem hzP hx0P⟩, ?_, ?_⟩
      · rw [map_mul, p_z_eq_one D, one_mul, hx0]
      · have hsplit : (⟨D.C.z * x0, mul_mem hzP hx0P⟩ : ↥P)
            = (⟨D.C.z, hzP⟩ : ↥P) * ⟨x0, hx0P⟩ := rfl
        have : χ (Additive.ofMul ((⟨D.C.z, hzP⟩ : ↥P) * ⟨x0, hx0P⟩))
            = χ (Additive.ofMul (⟨D.C.z, hzP⟩ : ↥P))
              + χ (Additive.ofMul (⟨x0, hx0P⟩ : ↥P)) := by
          rw [show Additive.ofMul ((⟨D.C.z, hzP⟩ : ↥P) * ⟨x0, hx0P⟩)
              = Additive.ofMul (⟨D.C.z, hzP⟩ : ↥P) + Additive.ofMul (⟨x0, hx0P⟩ : ↥P) from rfl,
            map_add]
        rw [hsplit, this]
        have h1 : χ (Additive.ofMul (⟨D.C.z, hzP⟩ : ↥P)) = 1 :=
          (ZMod.eq_zero_or_eq_one _).resolve_left hχ
        have h2 : χ (Additive.ofMul (⟨x0, hx0P⟩ : ↥P)) = 1 :=
          (ZMod.eq_zero_or_eq_one _).resolve_left hc
        rw [h1, h2]
        exact CharTwo.add_self_eq_zero 1
  choose sfun hsp hsχ using hlift
  -- uniqueness of the `χ = 0` lift over each `t`
  have huniq : ∀ (t : ↥D.T) (x : ↥P), D.C.p x.1 = t.1 → χ (Additive.ofMul x) = 0 →
      x = sfun t := by
    intro t x hx hxχ
    have hker : (x * (sfun t)⁻¹ : ↥P).1 ∈ D.C.p.ker := by
      rw [MonoidHom.mem_ker]
      show D.C.p (x.1 * ((sfun t).1)⁻¹) = 1
      rw [map_mul, map_inv, hx, hsp t, mul_inv_cancel]
    rcases ker_cases D hker with h | h
    · exact mul_inv_eq_one.mp (Subtype.ext h)
    · exfalso
      have hchi : χ (Additive.ofMul (x * (sfun t)⁻¹)) = 0 := by
        have hofmul : Additive.ofMul (x * (sfun t)⁻¹)
            = Additive.ofMul x + Additive.ofMul (sfun t)⁻¹ := rfl
        have hinv : Additive.ofMul ((sfun t)⁻¹) = -(Additive.ofMul (sfun t)) := rfl
        rw [hofmul, map_add, hxχ, hinv, map_neg, hsχ t, neg_zero, add_zero]
      have hzz : (x * (sfun t)⁻¹ : ↥P) = ⟨D.C.z, hzP⟩ := Subtype.ext h
      rw [hzz] at hchi
      exact hχ hchi
  refine ⟨⟨MonoidHom.mk' (fun t => (sfun t).1) ?_, fun t => hsp t⟩⟩
  intro t t'
  have hmul : sfun (t * t') = sfun t * sfun t' := by
    refine (huniq (t * t') (sfun t * sfun t') ?_ ?_).symm
    · show D.C.p ((sfun t).1 * (sfun t').1) = (t.1 * t'.1)
      rw [map_mul, hsp t, hsp t']
    · have hofmul : Additive.ofMul (sfun t * sfun t')
          = Additive.ofMul (sfun t) + Additive.ofMul (sfun t') := rfl
      rw [hofmul, map_add, hsχ t, hsχ t', add_zero]
  rw [hmul]
  rfl

/-! ## The edge cocycle of (128) -/

section Edge

variable (S : TComplement D)

/-- Conjugates of `T`-elements stay in `T` (`T` normal). -/
theorem conj_mem_T (b : Bg) (t : ↥D.T) : b * t.1 * b⁻¹ ∈ D.T := D.hT.conj_mem _ t.2 _

/-- **The edge cocycle** `ε(b)(t)` of (128): the `z`-defect of conjugating the complement,
`x·s(t)·x⁻¹ = s(btb⁻¹)·z^{ε(b)(t)}` for any lift `x` of `b`.  (Defined with the pinned
`surjInv` lift; lift-independence is `edge_spec`.) -/
noncomputable def edge (b : Bg) (t : ↥D.T) : ZMod 2 :=
  zsign D (Function.surjInv D.C.surj b * S.s t * (Function.surjInv D.C.surj b)⁻¹
    * (S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩)⁻¹)

/-- The conjugation defect is a kernel element. -/
theorem edge_defect_mem_ker {x : D.C.cover} {b : Bg} (hx : D.C.p x = b) (t : ↥D.T) :
    x * S.s t * x⁻¹ * (S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩)⁻¹ ∈ D.C.p.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hx, S.sect, S.sect]
  group

/-- **The edge specification**: for ANY lift `x` of `b`,
`x·s(t)·x⁻¹ = s(btb⁻¹)·z^{ε(b)(t)}`.  (Two lifts differ by the central `z`, which cancels in
conjugation, so the defect is lift-independent.) -/
theorem edge_spec {x : D.C.cover} {b : Bg} (hx : D.C.p x = b) (t : ↥D.T) :
    x * S.s t * x⁻¹ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ (edge D S b t).val := by
  -- conjugation by `x` agrees with conjugation by the pinned lift
  set x0 := Function.surjInv D.C.surj b with hx0
  have hpx0 : D.C.p x0 = b := Function.surjInv_eq D.C.surj b
  have hw : x * x0⁻¹ ∈ D.C.p.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hx, hpx0, mul_inv_cancel]
  have hconj_eq : x * S.s t * x⁻¹ = x0 * S.s t * x0⁻¹ := by
    have hx_eq : x = (x * x0⁻¹) * x0 := by group
    rcases ker_cases D hw with h | h
    · rw [hx_eq, h, one_mul]
    · rw [hx_eq, h]
      calc D.C.z * x0 * S.s t * (D.C.z * x0)⁻¹
          = D.C.z * (x0 * S.s t * x0⁻¹) * D.C.z⁻¹ := by group
        _ = (x0 * S.s t * x0⁻¹) * D.C.z * D.C.z⁻¹ := by rw [D.C.central]
        _ = x0 * S.s t * x0⁻¹ := by group
  rw [hconj_eq]
  have hdef := edge_defect_mem_ker D S hpx0 t
  have hcd := ker_comm D hdef
  calc x0 * S.s t * x0⁻¹
      = (x0 * S.s t * x0⁻¹ * (S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩)⁻¹)
        * S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ := by group
    _ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩
        * (x0 * S.s t * x0⁻¹ * (S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩)⁻¹) := by
        rw [hcd]
    _ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ (edge D S b t).val := by
        rw [show edge D S b t = zsign D (x0 * S.s t * x0⁻¹
          * (S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩)⁻¹) from rfl, z_pow_zsign D hdef]

/-- Read the edge off from any lift-conjugation identity. -/
theorem edge_eq_of_spec {x : D.C.cover} {b : Bg} (hx : D.C.p x = b) (t : ↥D.T) (a : ZMod 2)
    (h : x * S.s t * x⁻¹ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ a.val) :
    edge D S b t = a := by
  have h2 := edge_spec D S hx t
  rw [h] at h2
  have h3 := congrArg (zsign D) (mul_left_cancel h2)
  rw [zsign_z_pow, zsign_z_pow] at h3
  exact h3.symm

/-- **Edge crossed-cocycle law**: `ε(b₁b₂)(t) = ε(b₁)(b₂tb₂⁻¹) + ε(b₂)(t)`. -/
theorem edge_mul (b₁ b₂ : Bg) (t : ↥D.T) :
    edge D S (b₁ * b₂) t
      = edge D S b₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩ + edge D S b₂ t := by
  set x₁ := Function.surjInv D.C.surj b₁ with hx₁
  set x₂ := Function.surjInv D.C.surj b₂ with hx₂
  have hp₁ : D.C.p x₁ = b₁ := Function.surjInv_eq D.C.surj b₁
  have hp₂ : D.C.p x₂ = b₂ := Function.surjInv_eq D.C.surj b₂
  have hp₁₂ : D.C.p (x₁ * x₂) = b₁ * b₂ := by rw [map_mul, hp₁, hp₂]
  refine edge_eq_of_spec D S hp₁₂ t _ ?_
  have e₂ := edge_spec D S hp₂ t
  have e₁ := edge_spec D S hp₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩
  have hzc : ∀ (n : ℕ) (w : D.C.cover), D.C.z ^ n * w = w * D.C.z ^ n :=
    fun n w => Commute.pow_left (D.C.central w) n
  have hsub : (⟨b₁ * (b₂ * t.1 * b₂⁻¹) * b₁⁻¹,
      conj_mem_T D b₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩⟩ : ↥D.T)
      = ⟨(b₁ * b₂) * t.1 * (b₁ * b₂)⁻¹, conj_mem_T D (b₁ * b₂) t⟩ := by
    apply Subtype.ext
    show b₁ * (b₂ * t.1 * b₂⁻¹) * b₁⁻¹ = (b₁ * b₂) * t.1 * (b₁ * b₂)⁻¹
    group
  calc x₁ * x₂ * S.s t * (x₁ * x₂)⁻¹
      = x₁ * (x₂ * S.s t * x₂⁻¹) * x₁⁻¹ := by group
    _ = x₁ * (S.s ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩ * D.C.z ^ (edge D S b₂ t).val)
        * x₁⁻¹ := by rw [e₂]
    _ = (x₁ * S.s ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩ * x₁⁻¹)
        * D.C.z ^ (edge D S b₂ t).val := by
        rw [show x₁ * (S.s ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩
            * D.C.z ^ (edge D S b₂ t).val) * x₁⁻¹
          = x₁ * S.s ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩
            * (D.C.z ^ (edge D S b₂ t).val * x₁⁻¹) from by group, hzc]
        group
    _ = S.s ⟨b₁ * (b₂ * t.1 * b₂⁻¹) * b₁⁻¹,
          conj_mem_T D b₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩⟩
        * D.C.z ^ (edge D S b₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩).val
        * D.C.z ^ (edge D S b₂ t).val := by rw [e₁]
    _ = S.s ⟨(b₁ * b₂) * t.1 * (b₁ * b₂)⁻¹, conj_mem_T D (b₁ * b₂) t⟩
        * D.C.z ^ ((edge D S b₁ ⟨b₂ * t.1 * b₂⁻¹, conj_mem_T D b₂ t⟩ + edge D S b₂ t)).val := by
        rw [hsub, mul_assoc, ← CentralCover.z_pow_val_add]

/-- **Edge additivity in `t`** (the complement is linear). -/
theorem edge_add (b : Bg) (t t' : ↥D.T) :
    edge D S b (t * t') = edge D S b t + edge D S b t' := by
  set x := Function.surjInv D.C.surj b with hxdef
  have hpx : D.C.p x = b := Function.surjInv_eq D.C.surj b
  refine edge_eq_of_spec D S hpx (t * t') _ ?_
  have e1 := edge_spec D S hpx t
  have e2 := edge_spec D S hpx t'
  have hzc : ∀ (n : ℕ) (w : D.C.cover), D.C.z ^ n * w = w * D.C.z ^ n :=
    fun n w => Commute.pow_left (D.C.central w) n
  have hsmul : S.s (t * t') = S.s t * S.s t' := map_mul S.s t t'
  have hsub : (⟨b * (t.1 * t'.1) * b⁻¹, conj_mem_T D b (t * t')⟩ : ↥D.T)
      = ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * ⟨b * t'.1 * b⁻¹, conj_mem_T D b t'⟩ := by
    apply Subtype.ext
    show b * (t.1 * t'.1) * b⁻¹ = (b * t.1 * b⁻¹) * (b * t'.1 * b⁻¹)
    group
  calc x * S.s (t * t') * x⁻¹
      = (x * S.s t * x⁻¹) * (x * S.s t' * x⁻¹) := by rw [hsmul]; group
    _ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ (edge D S b t).val
        * (S.s ⟨b * t'.1 * b⁻¹, conj_mem_T D b t'⟩ * D.C.z ^ (edge D S b t').val) := by
        rw [e1, e2]
    _ = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * S.s ⟨b * t'.1 * b⁻¹, conj_mem_T D b t'⟩
        * (D.C.z ^ (edge D S b t).val * D.C.z ^ (edge D S b t').val) := by
        rw [show S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ * D.C.z ^ (edge D S b t).val
            * (S.s ⟨b * t'.1 * b⁻¹, conj_mem_T D b t'⟩ * D.C.z ^ (edge D S b t').val)
          = S.s ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩
            * (D.C.z ^ (edge D S b t).val * S.s ⟨b * t'.1 * b⁻¹, conj_mem_T D b t'⟩)
            * D.C.z ^ (edge D S b t').val from by group, hzc]
        group
    _ = S.s ⟨b * (t.1 * t'.1) * b⁻¹, conj_mem_T D b (t * t')⟩
        * D.C.z ^ ((edge D S b t + edge D S b t')).val := by
        rw [hsub, map_mul, ← CentralCover.z_pow_val_add]

/-- The value of `s` on a conjugate-by-`M` argument is unchanged (`M` centralizes `T`). -/
theorem conj_M_fix (m : Bg) (hm : m ∈ D.M) (t : ↥D.T) :
    (⟨m * t.1 * m⁻¹, conj_mem_T D m t⟩ : ↥D.T) = t := by
  apply Subtype.ext
  show m * t.1 * m⁻¹ = t.1
  rw [D.hcomm _ hm _ (D.hTM t.2)]
  group

/-- **`M` has zero edge**: conjugation by (lifts of) `M`-elements fixes the complement
pointwise (`T ⊆ rad B_q`). -/
theorem edge_M_zero (m : Bg) (hm : m ∈ D.M) (t : ↥D.T) : edge D S m t = 0 := by
  set x := Function.surjInv D.C.surj m with hxdef
  have hpx : D.C.p x = m := Function.surjInv_eq D.C.surj m
  refine edge_eq_of_spec D S hpx t 0 ?_
  have hst : D.C.p (S.s t) ∈ D.T := by rw [S.sect]; exact t.2
  have hxM : D.C.p x ∈ D.M := by rw [hpx]; exact hm
  have hcomm := comm_of_p_mem_T D hst hxM
  rw [conj_M_fix D m hm t, show ((0 : ZMod 2)).val = 0 by decide, pow_zero, mul_one]
  rw [show x * S.s t * x⁻¹ = (x * S.s t) * x⁻¹ from rfl, hcomm]
  group

/-- **Edge `M`-coset invariance**: `ε(bm) = ε(b)` for `m ∈ M`. -/
theorem edge_coset (b m : Bg) (hm : m ∈ D.M) (t : ↥D.T) :
    edge D S (b * m) t = edge D S b t := by
  rw [edge_mul, edge_M_zero D S m hm t, add_zero, conj_M_fix D m hm t]

/-- **The descent construction**: a crossed trivialization `ε(b)(t) = ℓ(btb⁻¹) + ℓ(t)` of the
edge by an additive `ℓ` yields a normal complement to `p⁻¹(T)` missing `z` — refuting
`NoDescent`.  (Alter the complement by `z^ℓ`; the new complement is conjugation-stable.) -/
theorem not_noDescent_of_edge_trivial (ℓ : ↥D.T → ZMod 2)
    (hadd : ∀ t t', ℓ (t * t') = ℓ t + ℓ t')
    (h : ∀ (b : Bg) (t : ↥D.T), edge D S b t = ℓ ⟨b * t.1 * b⁻¹, conj_mem_T D b t⟩ + ℓ t) :
    ¬ D.NoDescent := by
  intro hnd
  apply hnd
  have hzc : ∀ (n : ℕ) (w : D.C.cover), D.C.z ^ n * w = w * D.C.z ^ n :=
    fun n w => Commute.pow_left (D.C.central w) n
  -- the altered complement `s'(t) = s(t)·z^{ℓ(t)}`, a homomorphism
  have hker : ∀ a : ZMod 2, D.C.z ^ a.val ∈ D.C.p.ker :=
    fun a => pow_mem (z_mem_ker D) _
  have hs'mul : ∀ t t' : ↥D.T,
      S.s (t * t') * D.C.z ^ (ℓ (t * t')).val
        = (S.s t * D.C.z ^ (ℓ t).val) * (S.s t' * D.C.z ^ (ℓ t').val) := by
    intro t t'
    rw [map_mul S.s, hadd, CentralCover.z_pow_val_add]
    calc S.s t * S.s t' * (D.C.z ^ (ℓ t).val * D.C.z ^ (ℓ t').val)
        = S.s t * (S.s t' * D.C.z ^ (ℓ t).val) * D.C.z ^ (ℓ t').val := by group
      _ = S.s t * (D.C.z ^ (ℓ t).val * S.s t') * D.C.z ^ (ℓ t').val := by
          rw [ker_comm D (hker (ℓ t)) (S.s t')]
      _ = (S.s t * D.C.z ^ (ℓ t).val) * (S.s t' * D.C.z ^ (ℓ t').val) := by group
  set s' : ↥D.T →* D.C.cover :=
    MonoidHom.mk' (fun t => S.s t * D.C.z ^ (ℓ t).val) hs'mul with hs'def
  have hps' : ∀ t : ↥D.T, D.C.p (s' t) = t.1 := by
    intro t
    show D.C.p (S.s t * D.C.z ^ (ℓ t).val) = t.1
    rw [map_mul, map_pow, p_z_eq_one D, one_pow, mul_one, S.sect]
  have hl1 : ℓ 1 = 0 := by
    have h11 := hadd 1 1
    rw [one_mul] at h11
    exact left_eq_add.mp h11
  refine ⟨s'.range, ?_, ?_, ?_⟩
  · -- normality: conjugation lands back in the range, by `edge_spec` + the trivialization
    constructor
    intro n hn g
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hn
    have hspec := edge_spec D S (rfl : D.C.p g = D.C.p g) t
    refine MonoidHom.mem_range.mpr ⟨⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D _ t⟩, ?_⟩
    show S.s ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, _⟩
        * D.C.z ^ (ℓ ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D _ t⟩).val
      = g * s' t * g⁻¹
    have hexp : g * s' t * g⁻¹
        = (g * S.s t * g⁻¹) * D.C.z ^ (ℓ t).val := by
      show g * (S.s t * D.C.z ^ (ℓ t).val) * g⁻¹ = _
      calc g * (S.s t * D.C.z ^ (ℓ t).val) * g⁻¹
          = g * S.s t * (D.C.z ^ (ℓ t).val * g⁻¹) := by group
        _ = g * S.s t * (g⁻¹ * D.C.z ^ (ℓ t).val) := by rw [hzc]
        _ = (g * S.s t * g⁻¹) * D.C.z ^ (ℓ t).val := by group
    have hexp2 : edge D S (D.C.p g) t + ℓ t
        = ℓ ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩ := by
      rw [h (D.C.p g) t, add_assoc, CharTwo.add_self_eq_zero, add_zero]
    calc S.s ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩
          * D.C.z ^ (ℓ ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩).val
        = S.s ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩
          * D.C.z ^ ((edge D S (D.C.p g) t + ℓ t)).val := by rw [hexp2]
      _ = S.s ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩
          * (D.C.z ^ (edge D S (D.C.p g) t).val * D.C.z ^ (ℓ t).val) := by
          rw [← CentralCover.z_pow_val_add]
      _ = S.s ⟨D.C.p g * t.1 * (D.C.p g)⁻¹, conj_mem_T D (D.C.p g) t⟩
          * D.C.z ^ (edge D S (D.C.p g) t).val * D.C.z ^ (ℓ t).val := by group
      _ = (g * S.s t * g⁻¹) * D.C.z ^ (ℓ t).val := by rw [← hspec]
      _ = g * s' t * g⁻¹ := hexp.symm
  · -- image: `p` maps the range onto `T`
    apply le_antisymm
    · rintro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
      obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
      rw [hps' t]
      exact t.2
    · intro y hy
      exact Subgroup.mem_map.mpr ⟨s' ⟨y, hy⟩, MonoidHom.mem_range.mpr ⟨⟨y, hy⟩, rfl⟩,
        hps' ⟨y, hy⟩⟩
  · -- `z` is not in the range
    intro hz
    obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp hz
    have ht1 : t.1 = 1 := by
      have := congrArg D.C.p ht
      rwa [hps' t, p_z_eq_one D] at this
    have hteq : t = 1 := Subtype.ext ht1
    rw [hteq] at ht
    have : s' 1 = 1 := map_one s'
    rw [this] at ht
    exact D.C.z_ne ht.symm

/-! ## The quotient edge (M-coset descent of the edge cocycle) -/

/-- The edge evaluated at the canonical representative of an `Bg⧸M`-class (well-defined by
`edge_coset`). -/
noncomputable def edgeQ (c : Bg ⧸ D.M) (t : ↥D.T) : ZMod 2 :=
  edge D S (Quotient.out c) t

/-- `edgeQ` computes at any representative. -/
theorem edgeQ_eq (c : Bg ⧸ D.M) {b : Bg} (hb : QuotientGroup.mk b = c) (t : ↥D.T) :
    edgeQ D S c t = edge D S b t := by
  have hout : (QuotientGroup.mk (Quotient.out c) : Bg ⧸ D.M) = c := QuotientGroup.out_eq' c
  have hmem : (Quotient.out c)⁻¹ * b ∈ D.M :=
    (QuotientGroup.eq (s := D.M)).mp (hout.trans hb.symm)
  have hb' : b = Quotient.out c * ((Quotient.out c)⁻¹ * b) := by group
  calc edgeQ D S c t = edge D S (Quotient.out c) t := rfl
    _ = edge D S (Quotient.out c * ((Quotient.out c)⁻¹ * b)) t :=
        (edge_coset D S _ _ hmem t).symm
    _ = edge D S b t := by rw [← hb']

end Edge

/-! ## The Γ-layer: twisting, obstruction, and the variation formula (129) -/

section GammaLayer

variable [TopologicalSpace Bg] [DiscreteTopology Bg]
variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
variable (ρ : ContinuousMonoidHom Γ (Bg ⧸ D.M))

/-- **A continuous crossed `T`-valued 1-cocycle over `ρ`** (the paper's
`u ∈ Z¹_{Γ,ρ}(T)`): `u(γδ) = u(γ)·(b·u(δ)·b⁻¹)` for any representative `b` of `ρ(γ)`
(well-defined since `M` — hence its subgroup image in the conjugation — acts trivially on
the abelian `T`). -/
structure TCocycle where
  /-- The underlying function, valued in `T`. -/
  u : Γ → Bg
  mem : ∀ γ, u γ ∈ D.T
  cont : Continuous u
  crossed : ∀ γ δ (b : Bg), QuotientGroup.mk b = ρ γ → u (γ * δ) = u γ * (b * u δ * b⁻¹)

theorem TCocycle.u_one (u : TCocycle D ρ) : u.u 1 = 1 := by
  have h := u.crossed 1 1 1 (by rw [QuotientGroup.mk_one, map_one])
  simp only [one_mul, mul_one, inv_one] at h
  exact left_eq_mul.mp h

/-- **The twist** of an `M`-lift by a crossed `T`-cocycle: `(u·f)(γ) = u(γ)·f(γ)`. -/
noncomputable def twist (u : TCocycle D ρ) (f : MLifts D ρ) : MLifts D ρ :=
  ⟨⟨MonoidHom.mk' (fun γ => u.u γ * f.1 γ) (fun γ δ => by
      have hcr := u.crossed γ δ (f.1 γ) (f.2 γ)
      rw [map_mul, hcr]
      group),
    (u.cont.mul f.1.continuous_toFun)⟩,
   fun γ => by
     show QuotientGroup.mk (u.u γ * f.1 γ) = ρ γ
     rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff (u.u γ)).mpr (D.hTM (u.mem γ)),
       one_mul, f.2 γ]⟩


/-- **Twisting is an involution** (`T` has exponent 2). -/
theorem twist_twist (u : TCocycle D ρ) (f : MLifts D ρ) :
    twist D ρ u (twist D ρ u f) = f := by
  apply Subtype.ext
  apply ContinuousMonoidHom.ext
  intro γ
  show u.u γ * (u.u γ * f.1 γ) = f.1 γ
  rw [← mul_assoc, D.helem _ (D.hTM (u.mem γ)), one_mul]

/-! ### The scalar obstruction class -/

/-- The obstruction 2-cochain of a lift family `F : Γ → B̃`. -/
noncomputable def obCocOf (F : Γ → D.C.cover) : Γ × Γ → ZMod 2 :=
  fun gd => zsign D (F gd.1 * F gd.2 * (F (gd.1 * gd.2))⁻¹)

/-- The canonical lift family of an `M`-lift (pinned via `surjInv`). -/
noncomputable def liftFam (f : MLifts D ρ) : Γ → D.C.cover :=
  fun γ => Function.surjInv D.C.surj (f.1 γ)

theorem liftFam_p (f : MLifts D ρ) (γ : Γ) : D.C.p (liftFam D ρ f γ) = f.1 γ :=
  Function.surjInv_eq D.C.surj _

theorem liftFam_cont (f : MLifts D ρ) : Continuous (liftFam D ρ f) :=
  continuous_of_discreteTopology.comp f.1.continuous_toFun

/-- Section defects of a lift family lie in the kernel. -/
theorem obDefect_mem_ker {F : Γ → D.C.cover} {f : MLifts D ρ}
    (hF : ∀ γ, D.C.p (F γ) = f.1 γ) (γ δ : Γ) :
    F γ * F δ * (F (γ * δ))⁻¹ ∈ D.C.p.ker := by
  rw [MonoidHom.mem_ker, map_mul, map_mul, map_inv, hF, hF, hF, map_mul]
  group

variable [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)]

open ContCoh in
/-- The obstruction cochain of a (continuous) lift family is a continuous 2-cocycle. -/
theorem obCocOf_mem_Z2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    {F : Γ → D.C.cover} (hFc : Continuous F) {f : MLifts D ρ}
    (hF : ∀ γ, D.C.p (F γ) = f.1 γ) :
    obCocOf D F ∈ Z2 Γ (ZMod 2) := by
  rw [mem_Z2_iff]
  refine ⟨?_, ?_⟩
  · have h3 : Continuous (fun gd : Γ × Γ => (F gd.1, F gd.2, F (gd.1 * gd.2))) :=
      (hFc.comp continuous_fst).prodMk
        ((hFc.comp continuous_snd).prodMk (hFc.comp continuous_mul))
    exact (continuous_of_discreteTopology
      (f := fun abc : D.C.cover × D.C.cover × D.C.cover =>
        zsign D (abc.1 * abc.2.1 * abc.2.2⁻¹))).comp h3
  · intro g h k
    rw [htriv]
    have hker' : ∀ a b : Γ, F a * F b * (F (a * b))⁻¹ ∈ D.C.p.ker :=
      fun a b => obDefect_mem_ker D ρ hF a b
    have hR : obCocOf D F (g * h, k) + obCocOf D F (g, h)
        = zsign D (F g * F h * F k * (F (g * h * k))⁻¹) := by
      rw [add_comm]
      rw [show obCocOf D F (g, h) + obCocOf D F (g * h, k)
          = zsign D ((F g * F h * (F (g * h))⁻¹) * (F (g * h) * F k * (F (g * h * k))⁻¹))
        from (zsign_mul D (hker' g h) (hker' (g * h) k)).symm]
      congr 1
      group
    have hL : obCocOf D F (h, k) + obCocOf D F (g, h * k)
        = zsign D (F g * F h * F k * (F (g * h * k))⁻¹) := by
      rw [show obCocOf D F (h, k) + obCocOf D F (g, h * k)
          = zsign D ((F h * F k * (F (h * k))⁻¹) * (F g * F (h * k) * (F (g * (h * k)))⁻¹))
        from (zsign_mul D (hker' h k) (hker' g (h * k))).symm]
      congr 1
      have hd := ker_comm D (hker' h k) (F g)
      calc (F h * F k * (F (h * k))⁻¹) * (F g * F (h * k) * (F (g * (h * k)))⁻¹)
          = ((F h * F k * (F (h * k))⁻¹) * F g) * (F (h * k) * (F (g * (h * k)))⁻¹) := by
            group
        _ = (F g * (F h * F k * (F (h * k))⁻¹)) * (F (h * k) * (F (g * (h * k)))⁻¹) := by
            rw [hd]
        _ = F g * F h * F k * (F (g * (h * k)))⁻¹ := by group
        _ = F g * F h * F k * (F (g * h * k))⁻¹ := by
            rw [show g * h * k = g * (h * k) from mul_assoc g h k]
    rw [hL, hR]

open ContCoh in
/-- **The obstruction class** `ob(f) ∈ H²(Γ, 𝔽₂)` of an `M`-lift: the class of the section
defect of (any) continuous lift family through the cover. -/
noncomputable def ob (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (f : MLifts D ρ) :
    H2 Γ (ZMod 2) :=
  H2mk Γ (ZMod 2) ⟨obCocOf D (liftFam D ρ f),
    obCocOf_mem_Z2 D ρ htriv (liftFam_cont D ρ f) (liftFam_p D ρ f)⟩

omit [DistribMulAction Γ (ZMod 2)] [ContinuousSMul Γ (ZMod 2)] in
/-- **Lift-family difference formula**: two lift families of the same `M`-lift have
obstruction cochains differing by the explicit coboundary data of `c(γ) = zsign(F γ·F'γ⁻¹)`. -/
theorem obCocOf_diff {f : MLifts D ρ} {F F' : Γ → D.C.cover}
    (hF : ∀ γ, D.C.p (F γ) = f.1 γ) (hF' : ∀ γ, D.C.p (F' γ) = f.1 γ) (γ δ : Γ) :
    obCocOf D F (γ, δ)
      = obCocOf D F' (γ, δ) + (zsign D (F γ * (F' γ)⁻¹) + zsign D (F δ * (F' δ)⁻¹)
          + zsign D (F (γ * δ) * (F' (γ * δ))⁻¹)) := by
  have hd : ∀ a : Γ, F a * (F' a)⁻¹ ∈ D.C.p.ker := by
    intro a
    rw [MonoidHom.mem_ker, map_mul, map_inv, hF, hF']
    group
  have hker' : ∀ a b : Γ, F' a * F' b * (F' (a * b))⁻¹ ∈ D.C.p.ker :=
    fun a b => obDefect_mem_ker D ρ hF' a b
  -- express the F-defect as a product of central factors
  have hsplit : F γ * F δ * (F (γ * δ))⁻¹
      = (F' γ * F' δ * (F' (γ * δ))⁻¹) * ((F γ * (F' γ)⁻¹) * (F δ * (F' δ)⁻¹)
          * (F (γ * δ) * (F' (γ * δ))⁻¹)) := by
    have h1 : F γ = (F γ * (F' γ)⁻¹) * F' γ := by group
    have h2 : F δ = (F δ * (F' δ)⁻¹) * F' δ := by group
    have h3 : (F (γ * δ))⁻¹ = (F' (γ * δ))⁻¹ * (F (γ * δ) * (F' (γ * δ))⁻¹)⁻¹ := by group
    rw [h1, h2, h3]
    -- shuffle the central kernel factors to the right
    have hc1 := ker_comm D (hd γ)
    have hc2 := ker_comm D (hd δ)
    have hc3 := ker_comm D (hd (γ * δ))
    have hcinv : (F (γ * δ) * (F' (γ * δ))⁻¹)⁻¹ = F (γ * δ) * (F' (γ * δ))⁻¹ :=
      ker_inv_eq D (hd (γ * δ))
    rw [hcinv]
    calc (F γ * (F' γ)⁻¹) * F' γ * ((F δ * (F' δ)⁻¹) * F' δ)
          * ((F' (γ * δ))⁻¹ * (F (γ * δ) * (F' (γ * δ))⁻¹))
        = (F γ * (F' γ)⁻¹) * (F' γ * (F δ * (F' δ)⁻¹)) * F' δ
          * (F' (γ * δ))⁻¹ * (F (γ * δ) * (F' (γ * δ))⁻¹) := by group
      _ = (F γ * (F' γ)⁻¹) * ((F δ * (F' δ)⁻¹) * F' γ) * F' δ
          * (F' (γ * δ))⁻¹ * (F (γ * δ) * (F' (γ * δ))⁻¹) := by rw [hc2]
      _ = ((F γ * (F' γ)⁻¹) * (F δ * (F' δ)⁻¹)) * (F' γ * F' δ * (F' (γ * δ))⁻¹)
          * (F (γ * δ) * (F' (γ * δ))⁻¹) := by group
      _ = (F' γ * F' δ * (F' (γ * δ))⁻¹) * ((F γ * (F' γ)⁻¹) * (F δ * (F' δ)⁻¹))
          * (F (γ * δ) * (F' (γ * δ))⁻¹) := by
          rw [ker_comm D (mul_mem (hd γ) (hd δ)) (F' γ * F' δ * (F' (γ * δ))⁻¹)]
      _ = _ := by group
  show zsign D (F γ * F δ * (F (γ * δ))⁻¹) = _
  rw [hsplit, zsign_mul D (hker' γ δ) (mul_mem (mul_mem (hd γ) (hd δ)) (hd (γ * δ))),
    zsign_mul D (mul_mem (hd γ) (hd δ)) (hd (γ * δ)), zsign_mul D (hd γ) (hd δ)]
  rfl

open ContCoh in
/-- The obstruction class is lift-family independent. -/
theorem ob_eq_of_liftFam (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (f : MLifts D ρ)
    {F : Γ → D.C.cover} (hFc : Continuous F) (hFp : ∀ γ, D.C.p (F γ) = f.1 γ) :
    ob D ρ htriv f
      = H2mk Γ (ZMod 2) ⟨obCocOf D F, obCocOf_mem_Z2 D ρ htriv hFc hFp⟩ := by
  -- the difference cochain is the coboundary of `c(γ) = zsign(F γ · liftFam γ⁻¹)`
  have hdmem : obCocOf D F - obCocOf D (liftFam D ρ f) ∈ B2 Γ (ZMod 2) := by
    set c : Γ → ZMod 2 := fun γ => zsign D (F γ * (liftFam D ρ f γ)⁻¹) with hc
    have hccont : Continuous c := by
      have h2 : Continuous (fun γ => (F γ, liftFam D ρ f γ)) :=
        hFc.prodMk (liftFam_cont D ρ f)
      exact (continuous_of_discreteTopology
        (f := fun xy : D.C.cover × D.C.cover => zsign D (xy.1 * xy.2⁻¹))).comp h2
    refine AddSubgroup.mem_map.mpr ⟨c, hccont, ?_⟩
    funext gd
    obtain ⟨γ, δ⟩ := gd
    show γ • c δ - c (γ * δ) + c γ
      = (obCocOf D F - obCocOf D (liftFam D ρ f)) (γ, δ)
    rw [htriv]
    have hdiff := obCocOf_diff D ρ hFp (liftFam_p D ρ f) γ δ
    have hsub : (obCocOf D F - obCocOf D (liftFam D ρ f)) (γ, δ)
        = obCocOf D F (γ, δ) - obCocOf D (liftFam D ρ f) (γ, δ) := rfl
    rw [hsub]
    simp only [hc]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hdiff
  have hs : H2mk Γ (ZMod 2) ⟨obCocOf D F, obCocOf_mem_Z2 D ρ htriv hFc hFp⟩
      - H2mk Γ (ZMod 2) ⟨obCocOf D (liftFam D ρ f),
          obCocOf_mem_Z2 D ρ htriv (liftFam_cont D ρ f) (liftFam_p D ρ f)⟩ = 0 := by
    rw [← map_sub]
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddSubgroup.mem_addSubgroupOf.mpr hdmem)
  exact (sub_eq_zero.mp hs).symm

/-- The quotient of a discrete group is discrete. -/
theorem discreteTopology_quotient : DiscreteTopology (Bg ⧸ D.M) := by
  refine discreteTopology_iff_isOpen_singleton.mpr fun c => ?_
  have h1 : IsOpen (QuotientGroup.mk ⁻¹' {c} : Set Bg) := isOpen_discrete _
  have h2 : QuotientGroup.mk '' (QuotientGroup.mk ⁻¹' {c} : Set Bg) = {c} :=
    Set.image_preimage_eq _ QuotientGroup.mk_surjective
  rw [← h2]
  exact QuotientGroup.isOpenMap_coe _ h1

open ContCoh in
/-- **The central relation is the vanishing of the obstruction class**:
`f` lifts through the cover iff `ob f = 0`. -/
theorem central_iff_ob_eq_zero (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m)
    (f : MLifts D ρ) : f.Central ↔ ob D ρ htriv f = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    rw [ob_eq_of_liftFam D ρ htriv f (F := fun γ => g γ) g.continuous_toFun (fun γ => hg γ)]
    have hz : (⟨obCocOf D (fun γ => g γ),
        obCocOf_mem_Z2 D ρ htriv g.continuous_toFun (fun γ => hg γ)⟩
        : Z2 Γ (ZMod 2)) = 0 := by
      apply Subtype.ext
      funext gd
      show zsign D (g gd.1 * g gd.2 * (g (gd.1 * gd.2))⁻¹) = 0
      rw [show g gd.1 * g gd.2 * (g (gd.1 * gd.2))⁻¹ = 1 from by rw [← map_mul]; group,
        zsign_one]
    rw [hz, map_zero]
  · intro h0
    -- extract the trivializing continuous 1-cochain
    have hmem : obCocOf D (liftFam D ρ f) ∈ B2 Γ (ZMod 2) := by
      have h1 := (QuotientAddGroup.eq_zero_iff _).mp h0
      rwa [AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨c, hcC1, hceq⟩ := AddSubgroup.mem_map.mp hmem
    have hccont : Continuous c := hcC1
    -- pointwise value of the coboundary
    have hpt : ∀ γ δ : Γ, obCocOf D (liftFam D ρ f) (γ, δ) = c δ - c (γ * δ) + c γ := by
      intro γ δ
      have h := congrFun hceq (γ, δ)
      rw [← h]
      show γ • c δ - c (γ * δ) + c γ = c δ - c (γ * δ) + c γ
      rw [htriv]
    -- the corrected lift family is a homomorphism
    have key : ∀ γ δ : Γ,
        (D.C.z ^ (c γ).val * liftFam D ρ f γ) * (D.C.z ^ (c δ).val * liftFam D ρ f δ)
          = D.C.z ^ (c (γ * δ)).val * liftFam D ρ f (γ * δ) := by
      intro γ δ
      have hd := obDefect_mem_ker D ρ (liftFam_p D ρ f) γ δ
      have hLL : liftFam D ρ f γ * liftFam D ρ f δ
          = D.C.z ^ (obCocOf D (liftFam D ρ f) (γ, δ)).val * liftFam D ρ f (γ * δ) := by
        rw [show obCocOf D (liftFam D ρ f) (γ, δ) = zsign D (liftFam D ρ f γ
            * liftFam D ρ f δ * (liftFam D ρ f (γ * δ))⁻¹) from rfl, z_pow_zsign D hd]
        group
      have hkerp : ∀ a : ZMod 2, D.C.z ^ a.val ∈ D.C.p.ker :=
        fun a => pow_mem (z_mem_ker D) _
      calc (D.C.z ^ (c γ).val * liftFam D ρ f γ) * (D.C.z ^ (c δ).val * liftFam D ρ f δ)
          = D.C.z ^ (c γ).val * (liftFam D ρ f γ * D.C.z ^ (c δ).val)
            * liftFam D ρ f δ := by group
        _ = D.C.z ^ (c γ).val * (D.C.z ^ (c δ).val * liftFam D ρ f γ)
            * liftFam D ρ f δ := by
            rw [← ker_comm D (hkerp (c δ)) (liftFam D ρ f γ)]
        _ = (D.C.z ^ (c γ).val * D.C.z ^ (c δ).val)
            * (liftFam D ρ f γ * liftFam D ρ f δ) := by group
        _ = (D.C.z ^ (c γ).val * D.C.z ^ (c δ).val)
            * (D.C.z ^ (obCocOf D (liftFam D ρ f) (γ, δ)).val
              * liftFam D ρ f (γ * δ)) := by rw [hLL]
        _ = (D.C.z ^ (c γ).val * D.C.z ^ (c δ).val
              * D.C.z ^ (obCocOf D (liftFam D ρ f) (γ, δ)).val)
            * liftFam D ρ f (γ * δ) := by group
        _ = D.C.z ^ ((c γ + c δ + obCocOf D (liftFam D ρ f) (γ, δ))).val
            * liftFam D ρ f (γ * δ) := by
              rw [← CentralCover.z_pow_val_add, ← CentralCover.z_pow_val_add]
        _ = D.C.z ^ (c (γ * δ)).val * liftFam D ρ f (γ * δ) := by
            have harith : ∀ a b e : ZMod 2, a + b + (b - e + a) = e := by decide
            rw [hpt γ δ, harith]
    refine ⟨⟨MonoidHom.mk' (fun γ => D.C.z ^ (c γ).val * liftFam D ρ f γ)
        (fun γ δ => (key γ δ).symm), ?_⟩, ?_⟩
    · have hz : Continuous (fun γ : Γ => D.C.z ^ (c γ).val) :=
        (continuous_of_discreteTopology
          (f := fun a : ZMod 2 => D.C.z ^ a.val)).comp hccont
      exact hz.mul (liftFam_cont D ρ f)
    · intro γ
      show D.C.p (D.C.z ^ (c γ).val * liftFam D ρ f γ) = f.1 γ
      rw [map_mul, map_pow, p_z_eq_one D, one_pow, one_mul, liftFam_p]

/-! ### The variation class of a twist (the (129) cup term) -/

section Variation

variable (S : TComplement D)

/-- **The variation 2-cochain** of a crossed `T`-cocycle: the (129) cup term
`(γ, δ) ↦ ε̄(ρ(γ))(u(δ))` — independent of any `M`-lift. -/
noncomputable def varCoc (u : TCocycle D ρ) : Γ × Γ → ZMod 2 :=
  fun gd => edgeQ D S (ρ gd.1) ⟨u.u gd.2, u.mem gd.2⟩

open ContCoh in
/-- The variation cochain is a continuous 2-cocycle. -/
theorem varCoc_mem_Z2 (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (u : TCocycle D ρ) :
    varCoc D ρ S u ∈ Z2 Γ (ZMod 2) := by
  haveI := discreteTopology_quotient D
  rw [mem_Z2_iff]
  refine ⟨?_, ?_⟩
  · have h2 : Continuous
        (fun gd : Γ × Γ => ((ρ gd.1 : Bg ⧸ D.M), (⟨u.u gd.2, u.mem gd.2⟩ : ↥D.T))) :=
      (ρ.continuous_toFun.comp continuous_fst).prodMk
        ((u.cont.comp continuous_snd).subtype_mk _)
    exact (continuous_of_discreteTopology
      (f := fun cb : (Bg ⧸ D.M) × ↥D.T => edgeQ D S cb.1 cb.2)).comp h2
  · intro g h k
    rw [htriv]
    -- representatives
    set bg := Quotient.out (ρ g) with hbg
    set bh := Quotient.out (ρ h) with hbh
    have hmkg : (QuotientGroup.mk bg : Bg ⧸ D.M) = ρ g := QuotientGroup.out_eq' _
    have hmkh : (QuotientGroup.mk bh : Bg ⧸ D.M) = ρ h := QuotientGroup.out_eq' _
    have hmkgh : (QuotientGroup.mk (bg * bh) : Bg ⧸ D.M) = ρ (g * h) := by
      rw [QuotientGroup.mk_mul, hmkg, hmkh, map_mul]
    -- the four values
    have e1 : varCoc D ρ S u (h, k) = edge D S bh ⟨u.u k, u.mem k⟩ :=
      edgeQ_eq D S _ hmkh _
    have e2 : varCoc D ρ S u (g, h * k)
        = edge D S bg ⟨u.u h, u.mem h⟩
          + edge D S bg ⟨bh * u.u k * bh⁻¹,
              conj_mem_T D bh ⟨u.u k, u.mem k⟩⟩ := by
      have hcross := u.crossed h k bh hmkh
      have hsplit : (⟨u.u (h * k), u.mem (h * k)⟩ : ↥D.T)
          = ⟨u.u h, u.mem h⟩ * ⟨bh * u.u k * bh⁻¹, conj_mem_T D bh ⟨u.u k, u.mem k⟩⟩ := by
        apply Subtype.ext
        show u.u (h * k) = u.u h * (bh * u.u k * bh⁻¹)
        exact hcross
      calc varCoc D ρ S u (g, h * k)
          = edge D S bg ⟨u.u (h * k), u.mem (h * k)⟩ := edgeQ_eq D S _ hmkg _
        _ = _ := by rw [hsplit, edge_add]
    have e3 : varCoc D ρ S u (g * h, k)
        = edge D S bg ⟨bh * u.u k * bh⁻¹, conj_mem_T D bh ⟨u.u k, u.mem k⟩⟩
          + edge D S bh ⟨u.u k, u.mem k⟩ := by
      calc varCoc D ρ S u (g * h, k)
          = edge D S (bg * bh) ⟨u.u k, u.mem k⟩ := edgeQ_eq D S _ hmkgh _
        _ = _ := edge_mul D S bg bh _
    have e4 : varCoc D ρ S u (g, h) = edge D S bg ⟨u.u h, u.mem h⟩ :=
      edgeQ_eq D S _ hmkg _
    rw [e1, e2, e3, e4]
    ring

open ContCoh in
/-- **The variation formula (129), class level**: twisting shifts the obstruction class by
the (`f`-independent) variation class of `u`. -/
theorem ob_twist (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (u : TCocycle D ρ)
    (f : MLifts D ρ) :
    ob D ρ htriv (twist D ρ u f)
      = ob D ρ htriv f
        + H2mk Γ (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ := by
  -- the adapted lift family for the twist
  set F : Γ → D.C.cover :=
    fun γ => S.s ⟨u.u γ, u.mem γ⟩ * liftFam D ρ f γ with hFdef
  have hFp : ∀ γ, D.C.p (F γ) = (twist D ρ u f).1 γ := by
    intro γ
    show D.C.p (S.s ⟨u.u γ, u.mem γ⟩ * liftFam D ρ f γ) = u.u γ * f.1 γ
    rw [map_mul, S.sect, liftFam_p]
  have hFc : Continuous F := by
    have hs : Continuous (fun γ => S.s ⟨u.u γ, u.mem γ⟩) := by
      have h2 : Continuous (fun γ => (⟨u.u γ, u.mem γ⟩ : ↥D.T)) :=
        u.cont.subtype_mk _
      exact (continuous_of_discreteTopology (f := fun t : ↥D.T => S.s t)).comp h2
    exact hs.mul (liftFam_cont D ρ f)
  -- pointwise (129)
  have hpoint : obCocOf D F
      = fun gd => obCocOf D (liftFam D ρ f) gd + varCoc D ρ S u gd := by
    funext gd
    obtain ⟨γ, δ⟩ := gd
    have hLp : D.C.p (liftFam D ρ f γ) = f.1 γ := liftFam_p D ρ f γ
    have hspec := edge_spec D S hLp ⟨u.u δ, u.mem δ⟩
    have hcross := u.crossed γ δ (f.1 γ) (f.2 γ)
    have hker := obDefect_mem_ker D ρ (liftFam_p D ρ f) γ δ
    have hedge_ker : D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val ∈ D.C.p.ker :=
      pow_mem (z_mem_ker D) _
    -- the s-value at `u(γδ)` splits along the crossed law
    have hsplit : S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩
        = S.s ⟨u.u γ, u.mem γ⟩
          * S.s ⟨f.1 γ * u.u δ * (f.1 γ)⁻¹,
              conj_mem_T D (f.1 γ) ⟨u.u δ, u.mem δ⟩⟩ := by
      rw [← map_mul]
      congr 1
      apply Subtype.ext
      show u.u (γ * δ) = u.u γ * (f.1 γ * u.u δ * (f.1 γ)⁻¹)
      exact hcross
    -- assemble
    show zsign D (F γ * F δ * (F (γ * δ))⁻¹) = _
    have hEeq : F γ * F δ * (F (γ * δ))⁻¹
        = D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val
          * (liftFam D ρ f γ * liftFam D ρ f δ * (liftFam D ρ f (γ * δ))⁻¹) := by
      have hLs : liftFam D ρ f γ * S.s ⟨u.u δ, u.mem δ⟩
          = S.s ⟨f.1 γ * u.u δ * (f.1 γ)⁻¹, conj_mem_T D (f.1 γ) ⟨u.u δ, u.mem δ⟩⟩
            * D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val * liftFam D ρ f γ := by
        have h5 : liftFam D ρ f γ * S.s ⟨u.u δ, u.mem δ⟩ * (liftFam D ρ f γ)⁻¹
            * liftFam D ρ f γ = liftFam D ρ f γ * S.s ⟨u.u δ, u.mem δ⟩ := by group
        rw [← h5, hspec]
      calc F γ * F δ * (F (γ * δ))⁻¹
          = S.s ⟨u.u γ, u.mem γ⟩ * (liftFam D ρ f γ * S.s ⟨u.u δ, u.mem δ⟩)
            * liftFam D ρ f δ
            * ((S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩ * liftFam D ρ f (γ * δ)))⁻¹ := by
            rw [hFdef]
            group
        _ = S.s ⟨u.u γ, u.mem γ⟩
            * (S.s ⟨f.1 γ * u.u δ * (f.1 γ)⁻¹, conj_mem_T D (f.1 γ) ⟨u.u δ, u.mem δ⟩⟩
              * D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val * liftFam D ρ f γ)
            * liftFam D ρ f δ
            * ((S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩ * liftFam D ρ f (γ * δ)))⁻¹ := by
            rw [hLs]
        _ = S.s ⟨u.u γ, u.mem γ⟩
            * S.s ⟨f.1 γ * u.u δ * (f.1 γ)⁻¹, conj_mem_T D (f.1 γ) ⟨u.u δ, u.mem δ⟩⟩
            * (D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val
              * (liftFam D ρ f γ * liftFam D ρ f δ * (liftFam D ρ f (γ * δ))⁻¹))
            * (S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩)⁻¹ := by
            group
        _ = S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩
            * (D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val
              * (liftFam D ρ f γ * liftFam D ρ f δ * (liftFam D ρ f (γ * δ))⁻¹))
            * (S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩)⁻¹ := by
            rw [hsplit]
        _ = D.C.z ^ (edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩).val
            * (liftFam D ρ f γ * liftFam D ρ f δ * (liftFam D ρ f (γ * δ))⁻¹) := by
            rw [← ker_comm D (mul_mem hedge_ker hker) (S.s ⟨u.u (γ * δ), u.mem (γ * δ)⟩)]
            group
    rw [hEeq, zsign_mul D hedge_ker hker, zsign_z_pow]
    rw [show edge D S (f.1 γ) ⟨u.u δ, u.mem δ⟩
        = varCoc D ρ S u (γ, δ) from (edgeQ_eq D S (ρ γ) (f.2 γ) _).symm]
    exact add_comm _ _
  -- pass to classes
  rw [ob_eq_of_liftFam D ρ htriv (twist D ρ u f) hFc hFp]
  show H2mk Γ (ZMod 2) ⟨obCocOf D F, obCocOf_mem_Z2 D ρ htriv hFc hFp⟩
    = H2mk Γ (ZMod 2) ⟨obCocOf D (liftFam D ρ f),
        obCocOf_mem_Z2 D ρ htriv (liftFam_cont D ρ f) (liftFam_p D ρ f)⟩
      + H2mk Γ (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩
  rw [← map_add]
  congr 1
  apply Subtype.ext
  exact hpoint

end Variation

/-! ### The abstract half-count -/

/-- **Flip counting**: an involution swapping a predicate with its complement forces the
predicate to hold on exactly half of a finite type. -/
theorem two_mul_card_of_swap {X : Type} [Finite X] (σ : X → X)
    (hσ : Function.Involutive σ) (P : X → Prop) (hswap : ∀ x, P (σ x) ↔ ¬ P x) :
    2 * Nat.card {x // P x} = Nat.card X := by
  classical
  have e : {x // P x} ≃ {x // ¬ P x} :=
    { toFun := fun a => ⟨σ a.1, fun hP => ((hswap a.1).mp hP) a.2⟩
      invFun := fun b => ⟨σ b.1, (hswap b.1).mpr b.2⟩
      left_inv := fun a => Subtype.ext (hσ a.1)
      right_inv := fun b => Subtype.ext (hσ b.1) }
  have hsum : Nat.card X = Nat.card {x // P x} + Nat.card {x // ¬ P x} := by
    rw [← Nat.card_sum]
    exact Nat.card_congr (Equiv.sumCompl P).symm
  rw [hsum, ← Nat.card_congr e, two_mul]

open ContCoh in
/-- **The engine's half-count** (Lemma 8.6, count clause, source-generic): given a crossed
`T`-cocycle whose variation class is nonzero, and `#H²(Γ,𝔽₂) = 2`, exactly half of the
`M`-lifts satisfy the central relation. -/
theorem half_count [Finite (MLifts D ρ)] (S : TComplement D)
    (htriv : ∀ (γ : Γ) (m : ZMod 2), γ • m = m) (u : TCocycle D ρ)
    (hvar : H2mk Γ (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ ≠ 0)
    (hcard : Nat.card (H2 Γ (ZMod 2)) = 2) :
    2 * Nat.card {f : MLifts D ρ // f.Central} = Nat.card (MLifts D ρ) := by
  classical
  set v := H2mk Γ (ZMod 2) ⟨varCoc D ρ S u, varCoc_mem_Z2 D ρ S htriv u⟩ with hv
  -- `H²` with `𝔽₂`-coefficients is 2-torsion
  have htor : ∀ x : H2 Γ (ZMod 2), x + x = 0 := by
    intro x
    obtain ⟨φ, rfl⟩ := H2mk_surjective (G := Γ) (M := ZMod 2) x
    rw [← map_add]
    have hφ : φ + φ = 0 := by
      apply Subtype.ext
      funext gd
      show φ.1 gd + φ.1 gd = 0
      exact CharTwo.add_self_eq_zero _
    rw [hφ, map_zero]
  -- with `#H² = 2` and `v ≠ 0`, every class is `0` or `v`
  have hclass : ∀ x : H2 Γ (ZMod 2), x = 0 ∨ x = v := by
    intro x
    by_contra! hcon
    obtain ⟨hx0, hxv⟩ := hcon
    haveI : Finite (H2 Γ (ZMod 2)) := Nat.finite_of_card_ne_zero (by rw [hcard]; omega)
    have hinj : Function.Injective
        (fun i : Fin 3 => if i = 0 then (0 : H2 Γ (ZMod 2)) else if i = 1 then v else x) := by
      intro a b hab
      fin_cases a <;> fin_cases b <;> simp_all
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_eq_fintype_card, Fintype.card_fin, hcard] at hle
    omega
  refine two_mul_card_of_swap (fun f => twist D ρ u f) (twist_twist D ρ u)
    (fun f => f.Central) ?_
  intro f
  rw [central_iff_ob_eq_zero D ρ htriv (twist D ρ u f), central_iff_ob_eq_zero D ρ htriv f,
    ob_twist D ρ S htriv u f, ← hv]
  constructor
  · intro h h0
    rw [h0, zero_add] at h
    exact hvar h
  · intro hne
    rcases hclass (ob D ρ htriv f) with h | h
    · exact absurd h hne
    · rw [h]
      exact htor v

end GammaLayer

end CentralObstruction

end SectionEight

end GQ2

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * Lemma 8.6 = ⟦lem-radicaledge⟧
-/
