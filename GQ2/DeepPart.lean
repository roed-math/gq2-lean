import GQ2.EulerCharacteristic
import GQ2.GaussCount
import GQ2.TateDuality
import GQ2.RepIndependence

/-!
# Deep part and the §6 headline (Prop 6.18) — ticket P-15f

Proof-side layer for Lemma 6.17 (`X₊ = deepPart` is totally singular, `#X₊² = #H¹`) and
Proposition 6.18 (the dyadic base determinant theorem, eq. (115)).  The `lemma_6_17_*` /
`prop_6_18_*` statements live in `GQ2/SectionSix.lean`; the heavy proofs are assembled here (this
file imports `SectionSix` once the deep-part/`Q0loc` symbols are needed) and one-line-spliced,
per the P-15d (`RepIndependence`) pattern.

**Structure of `lemma_6_17_dim` (`#X₊² = #H¹`, ramified, Ax B6+B7):**
1. **Euler-characteristic collapse** `#H¹ = #V` — `card_H1_eq_card_of_H0_H2_trivial` below (this
   file): B7's `#H¹ = #H⁰·#H²·2^{v₂(#V)}` with `#H⁰ = #H² = 1`.
2. `#H⁰ = 1` (`V^{G_ℚ₂} = 0`) and `#H² = 1` (`(V^∨)^{G_ℚ₂} = 0` via B6 `perfect20`) — for a
   nontrivial **simple** module on which inertia acts nontrivially.  ⚠ NOTE: the frozen
   `lemma_6_17_dim` lacks `hc : Surjective c`; `V^{im ρ}` is `C`-stable (so simplicity ⟹ `⊥`)
   only when `im ρ ◁ C` (e.g. `c` surjective).  Likely a statement amendment (cf. `lemma_6_8`),
   flag for P-20.
3. **`#X₊ = 2^m`** — the Lagrangian half-count: `X₊` is self-orthogonal under the B6 Tate pairing
   on `H¹(V) ≅ H¹(V^∨)` (deep units pair trivially by (94)), and maximal, so `X₊ = X₊^⊥` and
   `#X₊·#X₊^⊥ = #H¹` gives `#X₊² = #H¹`.  This is the hard cohomological core (deep-unit Kummer
   image + Tate self-duality).

No `sorry` in this file.
-/

open scoped Classical

/-! ## Gauss sum over a Lagrangian (the ramified Prop 6.18 combinatorial core)

The zero-count of a nonsingular `𝔽₂` quadratic form `q` on `#V = 2^{2m}` is `2^{2m−1} ± 2^{m−1}`
by its Arf invariant (`GQ2/GaussCount.lean`, `zeroCount_of_arf_{zero,one}`).  Lemma 6.17 supplies
`Q⁰_loc` with a **half-dimensional totally singular subspace** `X₊` (deep units, `#X₊² = #H¹`,
`Q⁰_loc|X₊ = 0`).  The keystone below turns that into `arf = 0` (positive Gauss sign): a totally
singular, self-perpendicular `X` forces `g(q) = #X > 0`.  This is pure `𝔽₂` combinatorics — no
cohomology — proved by the two-way evaluation of `∑_v ∑_{x∈X} (−1)^{q(v+x)}`. -/

namespace GQ2.QuadraticFp2

private theorem zmod2_ne_zero_one : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
private theorem zmod2_eq_add_add : ∀ a b : ZMod 2, a = b + (a + b) := by decide

variable {V : Type*} [AddCommGroup V]

/-- **Gauss sum over a Lagrangian**: if `X ≤ V` is totally singular (`q|X = 0`) and
self-perpendicular (every `v` pairing trivially with all of `X` already lies in `X`), then the
Gauss sum is `g(q) = #X`.  The combinatorial heart of the ramified Prop 6.18: a half-dimensional
totally singular subspace forces the positive Gauss sign. -/
theorem gaussSum_eq_card_of_lagrangian [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (X : AddSubgroup V) (hsing : ∀ x ∈ X, q x = 0)
    (hperp : ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X) :
    gaussSum q = Nat.card ↥X := by
  classical
  haveI : Fintype ↥X := Fintype.ofFinite _
  -- X ⊆ X⊥ : totally singular ⟹ polar vanishes on X × X
  have hXperp : ∀ v : V, v ∈ X → ∀ x : ↥X, polar q v ↑x = 0 := by
    intro v hv x
    have hmem : v + ↑x ∈ X := X.add_mem hv x.2
    unfold polar
    rw [hsing _ hmem, hsing v hv, hsing ↑x x.2]; ring
  set S : ℤ := ∑ v : V, ∑ x : ↥X, sign (q (v + ↑x)) with hSdef
  -- (A) translate v ↦ v + x for each fixed x  ⟹  S = #X · g
  have hA : S = (Fintype.card ↥X : ℤ) * gaussSum q := by
    rw [hSdef, Finset.sum_comm]
    have hgx : ∀ x : ↥X, (∑ v : V, sign (q (v + ↑x))) = gaussSum q :=
      fun x => Equiv.sum_comp (Equiv.addRight (↑x : V)) (fun v => sign (q v))
    rw [Finset.sum_congr rfl (fun x _ => hgx x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  -- inner character sum: ∑_{x∈X} (−1)^{B(v,x)} = #X or 0 by (non)degeneracy at v
  have hinner : ∀ v : V, (∑ x : ↥X, sign (polar q v ↑x))
      = if (∀ x : ↥X, polar q v ↑x = 0) then (Fintype.card ↥X : ℤ) else 0 := by
    intro v
    split_ifs with hv
    · rw [Finset.sum_congr rfl (fun x _ => by rw [hv x, sign_zero]), Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul, mul_one]
    · push_neg at hv
      obtain ⟨x₀, hx₀⟩ := hv
      exact charSum_eq_zero
        (AddMonoidHom.mk' (fun x : ↥X => polar q v ↑x)
          (fun x x' => by push_cast; exact hq.polar_add_right v ↑x ↑x'))
        ⟨x₀, zmod2_ne_zero_one _ hx₀⟩
  -- (B) expand q(v+x) = q v + B(v,x) (using q x = 0), sign multiplicative
  have hB : S = (Fintype.card ↥X : ℤ) * (Fintype.card ↥X : ℤ) := by
    have hexp : S = ∑ v : V, sign (q v) * (∑ x : ↥X, sign (polar q v ↑x)) := by
      rw [hSdef]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun x _ => ?_)
      have key : q (v + ↑x) = q v + polar q v ↑x := by
        have hpx : polar q v ↑x = q (v + ↑x) + q v := by
          unfold polar; rw [hsing ↑x x.2, add_zero]
        rw [hpx]; exact zmod2_eq_add_add _ _
      rw [key, sign_add, mul_comm]
    have hterm : ∀ v : V, sign (q v) * (if (∀ x : ↥X, polar q v ↑x = 0) then
        (Fintype.card ↥X : ℤ) else 0) = if v ∈ X then (Fintype.card ↥X : ℤ) else 0 := by
      intro v
      by_cases hvX : v ∈ X
      · rw [if_pos hvX, if_pos (hXperp v hvX), hsing v hvX, sign_zero, one_mul]
      · rw [if_neg hvX, if_neg (fun hP => hvX (hperp v hP)), mul_zero]
    have hsum : (∑ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0))
        = (Fintype.card ↥X : ℤ) * (Fintype.card ↥X : ℤ) := by
      have h1 : ∀ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0)
          = (Fintype.card ↥X : ℤ) * (if v ∈ X then (1 : ℤ) else 0) := by
        intro v; by_cases hv : v ∈ X <;> simp [hv]
      rw [Finset.sum_congr rfl (fun v _ => h1 v), ← Finset.mul_sum, Finset.sum_boole]
      congr 1
      exact_mod_cast (Fintype.card_subtype (fun v => v ∈ X)).symm
    rw [hexp]
    have hstep : (∑ v : V, sign (q v) * (∑ x : ↥X, sign (polar q v ↑x)))
        = ∑ v : V, (if v ∈ X then (Fintype.card ↥X : ℤ) else 0) :=
      Finset.sum_congr rfl (fun v _ => by rw [hinner v]; exact hterm v)
    rw [hstep]; exact hsum
  -- cancel #X > 0
  have hcpos : 0 < Fintype.card ↥X := Fintype.card_pos_iff.mpr ⟨⟨0, X.zero_mem⟩⟩
  have hcne : (Fintype.card ↥X : ℤ) ≠ 0 := by exact_mod_cast hcpos.ne'
  have hg : gaussSum q = (Fintype.card ↥X : ℤ) :=
    mul_left_cancel₀ hcne (hA.symm.trans hB)
  rw [Nat.card_eq_fintype_card]; exact hg

/-- **A Lagrangian forces Arf 0** (positive Gauss sign).  Given a totally singular,
self-perpendicular `X ≤ V` (a "Lagrangian" for the nonsingular `q`), `arf q = 0`.  This is the
combinatorial step behind the ramified case of Prop 6.18 (eq. (115)). -/
theorem arf_zero_of_lagrangian [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (X : AddSubgroup V) (hsing : ∀ x ∈ X, q x = 0)
    (hperp : ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X) :
    arf q = 0 := by
  rw [arf_eq_zero_iff_gaussSum_pos, gaussSum_eq_card_of_lagrangian q hq X hsing hperp]
  haveI : Nonempty ↥X := ⟨⟨0, X.zero_mem⟩⟩
  exact_mod_cast Nat.card_pos

/-- **Self-perpendicularity of a half-dimensional totally singular subspace** (`𝔽₂` duality).
For a nonsingular `q` on an exponent-2 group with `q|X = 0` and `#X² = #V`, the perp `X⊥` equals
`X`: anything pairing trivially with all of `X` already lies in `X`.  Proof: the descended polar
functional injects `X⊥ ↪ (V/X)^∨` (injective by nonsingularity), so `#X⊥ ≤ #(V/X) = #V/#X = #X`;
with `X ⊆ X⊥` (total singularity) this forces `X⊥ = X`.  (No character-extension needed.) -/
theorem selfperp_of_card_sq [Finite V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (X : AddSubgroup V)
    (hsing : ∀ x ∈ X, q x = 0) (hcard : Nat.card ↥X ^ 2 = Nat.card V) :
    ∀ v : V, (∀ x : ↥X, polar q v ↑x = 0) → v ∈ X := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype ↥X := Fintype.ofFinite _
  haveI : Fintype {v : V // ∀ x : ↥X, polar q v ↑x = 0} := Fintype.ofFinite _
  haveI : Finite (V ⧸ X →+ ZMod 2) := Finite.of_injective _ DFunLike.coe_injective
  -- exponent 2 passes to the quotient
  have h2q : ∀ y : V ⧸ X, y + y = 0 := by
    intro y
    obtain ⟨u, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add, h2]; rfl
  -- total singularity ⟹ X ⊆ X⊥
  have hXsub : ∀ x : ↥X, ∀ y : ↥X, polar q (↑x) ↑y = 0 := by
    intro x y
    unfold polar
    rw [hsing _ (X.add_mem x.2 y.2), hsing _ x.2, hsing _ y.2]; ring
  -- X⊥ injects into (V/X)^∨ via the descended polar functional
  have hle : Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} ≤ Nat.card (V ⧸ X →+ ZMod 2) := by
    refine Nat.card_le_card_of_injective (fun v : {v : V // ∀ x : ↥X, polar q v ↑x = 0} =>
      QuotientAddGroup.lift X (polarHom q hq v.1) (fun x hx => by
        rw [AddMonoidHom.mem_ker, polarHom_apply, polar_comm]; exact v.2 ⟨x, hx⟩)) ?_
    rintro ⟨v₁, hv₁⟩ ⟨v₂, hv₂⟩ heq
    have hpe : ∀ u : V, polar q u v₁ = polar q u v₂ := by
      intro u
      have h := DFunLike.congr_fun heq (QuotientAddGroup.mk u)
      simpa [QuotientAddGroup.lift_mk, polarHom_apply] using h
    have hrad : ∀ u : V, polar q (v₁ + v₂) u = 0 := by
      intro u
      rw [polar_comm, hq.polar_add_right, hpe u]
      exact CharTwo.add_self_eq_zero _
    have hsum0 : v₁ + v₂ = 0 := by
      by_contra hne
      obtain ⟨w, hw⟩ := hns _ hne
      exact hw (hrad w)
    have : v₁ = v₂ := by
      have h := congrArg (· + v₂) hsum0
      rwa [add_assoc, h2, add_zero, zero_add] at h
    exact Subtype.ext this
  -- #(V/X) = #X from Lagrange + #X² = #V
  have hlag : Nat.card V = Nat.card (V ⧸ X) * Nat.card ↥X :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X
  have hXpos : 0 < Nat.card ↥X := Nat.card_pos
  have hquotX : Nat.card (V ⧸ X) = Nat.card ↥X := by
    have heq : Nat.card (V ⧸ X) * Nat.card ↥X = Nat.card ↥X * Nat.card ↥X := by
      rw [← hlag, ← hcard, sq]
    exact Nat.eq_of_mul_eq_mul_right hXpos heq
  -- so #X⊥ ≤ #X
  have hle' : Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} ≤ Nat.card ↥X := by
    rw [card_addHom_zmod2 (V ⧸ X) h2q, hquotX] at hle; exact hle
  -- inclusion X ↪ X⊥ is injective, so #X ≤ #X⊥
  have hincl_inj : Function.Injective (fun x : ↥X =>
      (⟨↑x, hXsub x⟩ : {v : V // ∀ x : ↥X, polar q v ↑x = 0})) := by
    intro a b hab
    exact Subtype.ext (by simpa using hab)
  have hge : Nat.card ↥X ≤ Nat.card {v : V // ∀ x : ↥X, polar q v ↑x = 0} :=
    Nat.card_le_card_of_injective _ hincl_inj
  -- equal cards ⟹ the inclusion is surjective
  have hbij : Function.Bijective (fun x : ↥X => (⟨↑x, hXsub x⟩ :
      {v : V // ∀ x : ↥X, polar q v ↑x = 0})) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hincl_inj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact le_antisymm hge hle'
  intro v hv
  obtain ⟨x, hx⟩ := hbij.surjective ⟨v, hv⟩
  have hxv : (↑x : V) = v := congrArg Subtype.val hx
  rw [← hxv]; exact x.2

/-- **A half-dimensional totally singular subspace forces Arf 0** (the ramified Prop 6.18 input).
Combines `selfperp_of_card_sq` (self-⊥ from `#X² = #V`) with `arf_zero_of_lagrangian`. -/
theorem arf_zero_of_card_sq [Fintype V] (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (h2 : ∀ v : V, v + v = 0) (hns : Nonsingular q) (X : AddSubgroup V)
    (hsing : ∀ x ∈ X, q x = 0) (hcard : Nat.card ↥X ^ 2 = Nat.card V) :
    arf q = 0 :=
  arf_zero_of_lagrangian q hq X hsing (selfperp_of_card_sq q hq h2 hns X hsing hcard)


/-- The polar form, bundled biadditively (first slot outer). -/
def polarBihom (q : V → ZMod 2) (hq : IsQuadraticFp2 q) : V →+ V →+ ZMod 2 :=
  AddMonoidHom.mk'
    (fun v => AddMonoidHom.mk' (fun w => polar q v w) (fun w w' => hq.polar_add_right v w w'))
    (fun v v' => by
      ext w
      exact hq.polar_add_left v v' w)

@[simp] theorem polarBihom_apply (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (v w : V) :
    polarBihom q hq v w = polar q v w := rfl

/-- **Restriction of `𝔽₂`-functionals to a subgroup is surjective** (pure counting: the
kernel of restriction is `Hom(A/X, 𝔽₂)`, so the image has the size of `Hom(X, 𝔽₂)`). -/
theorem addHom_restrict_surjective {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) (X : AddSubgroup A) :
    Function.Surjective (fun f : A →+ ZMod 2 => f.comp X.subtype) := by
  classical
  haveI : Finite (A →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (↥X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : ↥X → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (A ⧸ X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A ⧸ X → ZMod 2)) DFunLike.coe_injective
  set res : (A →+ ZMod 2) →+ (↥X →+ ZMod 2) :=
    AddMonoidHom.mk' (fun f => f.comp X.subtype) (fun f g => rfl) with hres
  -- the kernel of restriction is `Hom(A/X, 𝔽₂)`
  have hkerEquiv : ↥res.ker ≃ (A ⧸ X →+ ZMod 2) := by
    refine ⟨fun f => QuotientAddGroup.lift X f.1 (fun x hx => ?_),
      fun g => ⟨g.comp (QuotientAddGroup.mk' X), ?_⟩, fun f => ?_, fun g => ?_⟩
    · rw [AddMonoidHom.mem_ker]
      have := DFunLike.congr_fun f.2 (⟨x, hx⟩ : ↥X)
      exact this
    · have hg : ∀ x ∈ X, g.comp (QuotientAddGroup.mk' X) x = 0 := by
        intro x hx
        show g (QuotientAddGroup.mk' X x) = 0
        rw [show QuotientAddGroup.mk' X x = 0 from (QuotientAddGroup.eq_zero_iff x).mpr hx,
          map_zero]
      rw [AddMonoidHom.mem_ker]
      ext y
      exact hg ↑y y.2
    · apply Subtype.ext
      ext a
      rfl
    · ext yq
      rfl
  -- exponent 2 passes to the quotient
  have h2Q : ∀ y : A ⧸ X, y + y = 0 := by
    intro y
    obtain ⟨a, rfl⟩ := QuotientAddGroup.mk_surjective y
    rw [← QuotientAddGroup.mk_add, h2]; rfl
  have h2X : ∀ x : ↥X, x + x = 0 := fun x => Subtype.ext (h2 _)
  -- counting: `#im res = #Hom(X)`
  have hlag : Nat.card (A ⧸ X) * Nat.card ↥X = Nat.card A :=
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup X).symm
  have hkercard : Nat.card ↥res.ker = Nat.card (A ⧸ X) := by
    rw [Nat.card_congr hkerEquiv, card_addHom_zmod2 (A ⧸ X) h2Q]
  have hrn : Nat.card ↥res.range * Nat.card ↥res.ker = Nat.card (A →+ ZMod 2) := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange res).toEquiv]
    exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup res.ker).symm
  have hrange : Nat.card ↥res.range = Nat.card (↥X →+ ZMod 2) := by
    have e1 : Nat.card ↥res.range * Nat.card (A ⧸ X) = Nat.card A := by
      rw [← hkercard, hrn]
      exact card_addHom_zmod2 A h2
    have e2 : Nat.card ↥X * Nat.card (A ⧸ X) = Nat.card A := by
      rw [mul_comm]
      exact hlag
    have hQpos : 0 < Nat.card (A ⧸ X) := Nat.card_pos
    rw [card_addHom_zmod2 ↥X h2X]
    exact Nat.eq_of_mul_eq_mul_right hQpos (e1.trans e2.symm)
  -- full range ⟹ surjective
  have htop : res.range = ⊤ := by
    apply AddSubgroup.eq_top_of_card_eq
    rw [hrange]
  intro g
  have : g ∈ res.range := htop ▸ AddSubgroup.mem_top g
  obtain ⟨f, hf⟩ := this
  exact ⟨f, hf⟩

/-- **Perp membership from a Lagrangian count**: for a biadditive nondegenerate `𝔽₂`-pairing
and a subgroup `X` with `#X² = #A` on which the pairing vanishes, anything pairing trivially
with all of `X` lies in `X` (the perp has the size of `X` by counting, and contains it). -/
theorem mem_of_pairing_eq_zero {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) (P : A →+ A →+ ZMod 2)
    (hnd : ∀ z : A, z ≠ 0 → ∃ w : A, P z w ≠ 0)
    (X : AddSubgroup A) (hX : ∀ x ∈ X, ∀ x' ∈ X, P x x' = 0)
    (hcard : Nat.card ↥X * Nat.card ↥X = Nat.card A)
    {c : A} (hall : ∀ y ∈ X, P c y = 0) : c ∈ X := by
  classical
  haveI : Finite (A →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : A → ZMod 2)) DFunLike.coe_injective
  haveI : Finite (↥X →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : ↥X → ZMod 2)) DFunLike.coe_injective
  -- the pairing map `A → Hom(A, 𝔽₂)` is bijective (nondegenerate + counting)
  have hPinj : Function.Injective (fun z : A => (P z : A →+ ZMod 2)) := by
    intro z₁ z₂ hz
    have hz' : P z₁ = P z₂ := hz
    by_contra hne
    obtain ⟨w, hw⟩ := hnd _ (sub_ne_zero.mpr hne)
    apply hw
    rw [map_sub, hz', sub_self]
    rfl
  haveI : Fintype A := Fintype.ofFinite A
  haveI : Fintype (A →+ ZMod 2) := Fintype.ofFinite _
  have hPbij : Function.Bijective (fun z : A => (P z : A →+ ZMod 2)) := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hPinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_addHom_zmod2 A h2]
  -- `Θ : A →+ Hom(X, 𝔽₂)`, surjective as a composition
  set Θ : A →+ (↥X →+ ZMod 2) :=
    AddMonoidHom.mk' (fun z => (P z).comp X.subtype) (fun a b => by rw [map_add]; rfl) with hΘ
  have hΘsurj : Function.Surjective Θ := by
    intro g
    obtain ⟨f, hf⟩ := addHom_restrict_surjective h2 X g
    obtain ⟨z, hz⟩ := hPbij.2 f
    have hz' : P z = f := hz
    exact ⟨z, by show (P z).comp X.subtype = g; rw [hz']; exact hf⟩
  -- `ker Θ = X` by counting
  have hXle : X ≤ Θ.ker := by
    intro x hx
    rw [AddMonoidHom.mem_ker]
    ext y
    exact hX x hx ↑y y.2
  have hkercard : Nat.card ↥Θ.ker = Nat.card ↥X := by
    have hrn : Nat.card ↥Θ.range * Nat.card ↥Θ.ker = Nat.card A := by
      rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange Θ).toEquiv]
      exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Θ.ker).symm
    have hrangetop : Θ.range = ⊤ := AddMonoidHom.range_eq_top.mpr hΘsurj
    have h2X : ∀ x : ↥X, x + x = 0 := fun x => Subtype.ext (h2 _)
    have hrangecard : Nat.card ↥Θ.range = Nat.card ↥X := by
      have htopc : Nat.card ↥(⊤ : AddSubgroup (↥X →+ ZMod 2)) = Nat.card (↥X →+ ZMod 2) :=
        Nat.card_congr AddSubgroup.topEquiv.toEquiv
      rw [hrangetop, htopc, card_addHom_zmod2 ↥X h2X]
    rw [hrangecard] at hrn
    have hXpos : 0 < Nat.card ↥X := Nat.card_pos
    refine Nat.eq_of_mul_eq_mul_left hXpos ?_
    rw [hrn, ← hcard]
  have hkereq : (Θ.ker : Set A) = (X : Set A) := by
    symm
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hXle hx) ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact le_of_eq hkercard
  have hcmem : c ∈ Θ.ker := by
    rw [AddMonoidHom.mem_ker]
    ext y
    exact hall ↑y y.2
  have : c ∈ (X : Set A) := hkereq ▸ hcmem
  exact this

/-- The equivariant-lift correction kills `0`: `m_c(0) = 0` (from (59) at `v = w = 0`). -/
theorem _root_.GQ2.IsEquivariantFactorSet.m_zero {C : Type*} [Group C] [DistribMulAction C V]
    {q : V → ZMod 2} {dat : GQ2.FactorSet C V} (hdat : GQ2.IsEquivariantFactorSet q dat)
    (c : C) : dat.m c 0 = 0 := by
  have h := hdat.m_quad c 0 0
  rw [add_zero, smul_zero, hdat.f_zero_left, add_zero] at h
  -- h : m c 0 + m c 0 + m c 0 = 0
  have h2 : dat.m c 0 + dat.m c 0 = 0 := CharTwo.add_self_eq_zero _
  calc dat.m c 0 = dat.m c 0 + (dat.m c 0 + dat.m c 0) := by rw [h2, add_zero]
    _ = dat.m c 0 + dat.m c 0 + dat.m c 0 := by ring
    _ = 0 := h

end GQ2.QuadraticFp2

namespace GQ2.DeepPart

open GQ2 GQ2.ContCoh GQ2.Foundations

variable {M : Type*} [AddCommGroup M] [TopologicalSpace M] [DiscreteTopology M]
  [DistribMulAction AbsGalQ2 M] [ContinuousSMul AbsGalQ2 M] [Finite M]

/-- **Euler-characteristic collapse**: for a finite `2`-power-order `G_ℚ₂`-module with trivial
`H⁰` and `H²`, the local Euler characteristic (B7) reads `#H¹ = #M`. -/
theorem card_H1_eq_card_of_H0_H2_trivial (hH0 : Nat.card (H0 AbsGalQ2 M) = 1)
    (hH2 : Nat.card (H2 AbsGalQ2 M) = 1) {k : ℕ} (hk : Nat.card M = 2 ^ k) :
    Nat.card (H1 AbsGalQ2 M) = Nat.card M := by
  rw [card_H1_of_card_eq_two_pow M hk, hH0, hH2, one_mul, one_mul]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] [Finite M] in
/-- `H⁰(G_ℚ₂, M) = 0` (as `Nat.card = 1`) iff `M` has no nonzero `G_ℚ₂`-fixed vector. -/
theorem card_H0_eq_one_iff :
    Nat.card (H0 AbsGalQ2 M) = 1 ↔ ∀ m : M, (∀ g : AbsGalQ2, g • m = m) → m = 0 := by
  rw [Nat.card_eq_one_iff_unique]
  constructor
  · rintro ⟨hsub, _⟩ m hm
    have : (⟨m, hm⟩ : H0 AbsGalQ2 M) = ⟨0, fun g => smul_zero g⟩ := Subsingleton.elim _ _
    exact Subtype.ext_iff.mp this
  · intro h
    refine ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨0, fun g => smul_zero g⟩⟩
    rw [h a.1 (fun g => a.2 g), h b.1 (fun g => b.2 g)]

omit [TopologicalSpace M] [DiscreteTopology M] [ContinuousSMul AbsGalQ2 M] [Finite M] in
/-- **`H⁰`-vanishing** (§6.3 step 2, `V^{G_ℚ₂} = 0`): if the `G_ℚ₂`-action on `M` factors
through a *surjective* `ρ : G_ℚ₂ →* C`, the `C`-module `M` is simple, and some element of `C`
moves some vector, then `#H⁰ = 1`.  (`V^{im ρ} = V^C` is `C`-stable — even pointwise fixed —
so simplicity forces it to `⊥` or `⊤`, and `⊤` contradicts the moving element.) -/
theorem card_H0_eq_one_of_surjective {C : Type*} [Group C] [DistribMulAction C M]
    (ρ : AbsGalQ2 →* C) (hρsurj : Function.Surjective ρ)
    (hρ : ∀ (g : AbsGalQ2) (m : M), g • m = ρ g • m)
    (hsimple : ∀ W : AddSubgroup M, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ m : M, h₀ • m ≠ m) :
    Nat.card (H0 AbsGalQ2 M) = 1 := by
  rw [card_H0_eq_one_iff]
  intro m hm
  set W : AddSubgroup M :=
    { carrier := {x : M | ∀ h : C, h • x = x}
      zero_mem' := fun h => smul_zero h
      add_mem' := fun ha hb h => by rw [smul_add, ha h, hb h]
      neg_mem' := fun ha h => by rw [smul_neg, ha h] } with hWdef
  have hWmem : ∀ x : M, x ∈ W ↔ ∀ h : C, h • x = x := fun x => Iff.rfl
  have hstable : ∀ (h : C), ∀ w ∈ W, h • w ∈ W := by
    intro h w hw
    have hw' := (hWmem w).mp hw
    rw [hw' h]
    exact hw
  rcases hsimple W hstable with hbot | htop
  · have hmW : m ∈ W := by
      rw [hWmem]
      intro h
      obtain ⟨g, rfl⟩ := hρsurj h
      rw [← hρ g m]
      exact hm g
    rw [hbot, AddSubgroup.mem_bot] at hmW
    exact hmW
  · exfalso
    obtain ⟨m₀, hm₀⟩ := hmoves
    have hin : m₀ ∈ W := htop ▸ AddSubgroup.mem_top m₀
    exact hm₀ ((hWmem m₀).mp hin h₀)

/-- **Fixed-point transport**: an equivariant additive iso induces a cardinality equality of
`H⁰`s (it restricts to a bijection of the fixed-point subgroups). -/
theorem card_H0_congr {A B : Type*} [AddCommGroup A] [AddCommGroup B]
    [DistribMulAction AbsGalQ2 A] [DistribMulAction AbsGalQ2 B]
    (e : A ≃+ B) (he : ∀ (g : AbsGalQ2) (a : A), e (g • a) = g • e a) :
    Nat.card (H0 AbsGalQ2 B) = Nat.card (H0 AbsGalQ2 A) := by
  have hesymm : ∀ (g : AbsGalQ2) (b : B), e.symm (g • b) = g • e.symm b := by
    intro g b
    apply e.injective
    rw [he, e.apply_symm_apply, e.apply_symm_apply]
  refine Nat.card_congr ⟨fun y => ⟨e.symm y.1, fun g => ?_⟩,
    fun x => ⟨e x.1, fun g => ?_⟩, fun y => ?_, fun x => ?_⟩
  · rw [← hesymm g y.1, y.2 g]
  · rw [← he g x.1, x.2 g]
  · exact Subtype.ext (e.apply_symm_apply y.1)
  · exact Subtype.ext (e.symm_apply_apply x.1)

/-! ## The `μ₂` bricks: `μ₂ ≅ ℤ/2` with trivial Galois action

`MuN 2 = Additive (rootsOfUnity 2 ℚ̄₂) = {1, −1}` additively: classified by the value of the
underlying root, Galois-fixed because an additive automorphism of a two-element group is the
identity. -/

section MuTwo

/-- `−1` as the nonzero element of the additive `μ₂`. -/
noncomputable def muTwoGen : MuN 2 :=
  Additive.ofMul ⟨(-1 : (AlgebraicClosure ℚ_[2])ˣ), (mem_rootsOfUnity 2 _).mpr neg_one_sq⟩

theorem muTwoGen_ne_zero : muTwoGen ≠ 0 := by
  intro h
  have h1 : ((((Additive.toMul muTwoGen : rootsOfUnity 2 (AlgebraicClosure ℚ_[2])) :
      (AlgebraicClosure ℚ_[2])ˣ)) : AlgebraicClosure ℚ_[2]) = 1 := by
    rw [h]
    rfl
  have hneg : (-1 : AlgebraicClosure ℚ_[2]) = 1 := h1
  have h2 : (2 : AlgebraicClosure ℚ_[2]) = 0 := by linear_combination - hneg
  exact two_ne_zero h2

/-- Classification: `μ₂` has exactly the elements `0` and `muTwoGen`. -/
theorem muTwo_eq_zero_or_gen (x : MuN 2) : x = 0 ∨ x = muTwoGen := by
  set u : rootsOfUnity 2 (AlgebraicClosure ℚ_[2]) := Additive.toMul x with hu
  have hval : ((u : (AlgebraicClosure ℚ_[2])ˣ) : AlgebraicClosure ℚ_[2])
      * ((u : (AlgebraicClosure ℚ_[2])ˣ) : AlgebraicClosure ℚ_[2]) = 1 := by
    have hpow := (mem_rootsOfUnity 2 (u : (AlgebraicClosure ℚ_[2])ˣ)).mp u.2
    have hval' := congrArg Units.val hpow
    rwa [Units.val_pow_eq_pow_val, Units.val_one, pow_two] at hval'
  rcases mul_self_eq_one_iff.mp hval with h1 | hneg
  · left
    have hu1 : u = 1 := by
      apply Subtype.ext
      apply Units.ext
      simp only [OneMemClass.coe_one, Units.val_one]
      exact h1
    calc x = Additive.ofMul (Additive.toMul x) := rfl
      _ = Additive.ofMul u := by rw [← hu]
      _ = Additive.ofMul 1 := by rw [hu1]
      _ = 0 := rfl
  · right
    have hu1 : u = ⟨(-1 : (AlgebraicClosure ℚ_[2])ˣ), (mem_rootsOfUnity 2 _).mpr neg_one_sq⟩ := by
      apply Subtype.ext
      apply Units.ext
      rw [Units.val_neg, Units.val_one]
      exact hneg
    calc x = Additive.ofMul (Additive.toMul x) := rfl
      _ = Additive.ofMul u := by rw [← hu]
      _ = muTwoGen := by rw [hu1]; rfl

/-- The hom `ℤ/2 →+ μ₂`, `1 ↦ −1`. -/
noncomputable def zmodTwoToMuTwo : ZMod 2 →+ MuN 2 :=
  ZMod.lift 2 ⟨zmultiplesHom (MuN 2) muTwoGen, by
    show ((2 : ℕ) : ℤ) • muTwoGen = 0
    rw [natCast_zsmul]
    exact nsmul_muN_eq_zero 2 muTwoGen⟩

theorem zmodTwoToMuTwo_one : zmodTwoToMuTwo 1 = muTwoGen := by
  have h : ((1 : ℤ) : ZMod 2) = 1 := by norm_num
  rw [← h]
  show ZMod.lift 2 _ ((1 : ℤ) : ZMod 2) = muTwoGen
  rw [ZMod.lift_coe]
  exact one_zsmul muTwoGen

/-- `ℤ/2 ≃+ μ₂` (additive), `1 ↦ −1`. -/
noncomputable def zmodTwoEquivMuTwo : ZMod 2 ≃+ MuN 2 := by
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  refine AddEquiv.ofBijective zmodTwoToMuTwo ⟨?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro a ha
    rcases hcases a with rfl | rfl
    · rfl
    · rw [zmodTwoToMuTwo_one] at ha
      exact absurd ha muTwoGen_ne_zero
  · intro y
    rcases muTwo_eq_zero_or_gen y with rfl | rfl
    · exact ⟨0, map_zero _⟩
    · exact ⟨1, zmodTwoToMuTwo_one⟩

/-- **The Galois action on `μ₂` is trivial** — an additive automorphism of the two-element
group is the identity. -/
theorem muTwo_smul_trivial (g : AbsGalQ2) (x : MuN 2) : g • x = x := by
  rcases muTwo_eq_zero_or_gen x with rfl | rfl
  · exact smul_zero g
  · rcases muTwo_eq_zero_or_gen (g • muTwoGen) with h | h
    · exfalso
      have h0 : g⁻¹ • (g • muTwoGen) = g⁻¹ • (0 : MuN 2) := by rw [h]
      rw [inv_smul_smul, smul_zero] at h0
      exact muTwoGen_ne_zero h0
    · exact h

end MuTwo

/-! ## The polar self-duality `V ≃+ Hom(V, μ₂)` and `#H² = 1`  (§6.3 step 2, Ax B6 via `D`)

A nonsingular Galois-invariant `𝔽₂` quadratic form identifies `V` with its `μ₂`-dual
equivariantly, so `#H⁰(M′) = #H⁰(V)`; Tate duality's `(0,2)` clause at `M := V` then reads
`#H²(V) = #Hom(H²(V), ℤ/2) = #H⁰(M′) = #H⁰(V)` — no dual-simplicity argument needed. -/

section PolarDual

open GQ2.QuadraticFp2

variable (V : Type) [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [Finite V]

omit [TopologicalSpace V] [DiscreteTopology V] [ContinuousSMul AbsGalQ2 V] [Finite V] in
/-- A Galois-invariant form has Galois-invariant polar form. -/
theorem polar_smul_smul (q : V → ZMod 2) (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (g : AbsGalQ2) (a b : V) : polar q (g • a) (g • b) = polar q a b := by
  unfold GQ2.QuadraticFp2.polar
  rw [← smul_add, hqG, hqG, hqG]

/-- **Polar self-duality**: a nonsingular Galois-invariant quadratic form on a finite exp-2
module induces an equivariant additive iso `V ≃+ Hom(V, μ₂)`. -/
theorem exists_polarSelfDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    ∃ e : V ≃+ MuDual 2 V, ∀ (g : AbsGalQ2) (v : V), e (g • v) = g • e v := by
  classical
  set ε := zmodTwoEquivMuTwo with hε
  -- the underlying hom `v ↦ ε ∘ B(·, v)`
  set Ψ : V →+ MuDual 2 V :=
    { toFun := fun v => (ε.toAddMonoidHom.comp (polarHom q hq v) : MuDual 2 V)
      map_zero' := by
        refine DFunLike.ext _ _ fun m => ?_
        show ε (polar q m 0) = (0 : MuDual 2 V) m
        rw [MuDual.zero_apply]
        have hpz : polar q m 0 = 0 := by
          unfold GQ2.QuadraticFp2.polar
          rw [add_zero, hq.map_zero, add_zero]
          exact CharTwo.add_self_eq_zero _
        rw [hpz, map_zero]
      map_add' := fun v w => by
        refine DFunLike.ext _ _ fun m => ?_
        show ε (polar q m (v + w)) = ε (polar q m v) + ε (polar q m w)
        rw [hq.polar_add_right, map_add] } with hΨ
  have hΨapply : ∀ (v m : V), Ψ v m = ε (polar q m v) := fun v m => rfl
  -- injectivity from nonsingularity
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨w, hw⟩ := hns v hne
    have h0 : ε (polar q w v) = 0 := by
      have := DFunLike.congr_fun hv w
      rwa [MuDual.zero_apply] at this
    have hp0 : polar q w v = 0 := by
      apply ε.injective
      rw [h0, map_zero]
    rw [polar_comm] at hp0
    exact hw hp0
  -- cardinality: `#Hom(V, μ₂) = #Hom(V, ℤ/2) = #V`
  have hcards : Nat.card (MuDual 2 V) = Nat.card V := by
    have h1 : Nat.card (MuDual 2 V) = Nat.card (V →+ ZMod 2) := by
      refine Nat.card_congr ⟨fun f => ε.symm.toAddMonoidHom.comp (f : V →+ MuN 2),
        fun f => (ε.toAddMonoidHom.comp f : MuDual 2 V), fun f => ?_, fun f => ?_⟩
      · refine DFunLike.ext _ _ fun m => ?_
        show ε (ε.symm ((f : V →+ MuN 2) m)) = f m
        rw [ε.apply_symm_apply]
      · ext m
        show ε.symm (ε (f m)) = f m
        rw [ε.symm_apply_apply]
    rw [h1, card_addHom_zmod2 V h2]
  -- bijectivity
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (MuDual 2 V) := Fintype.ofFinite _
  have hbij : Function.Bijective Ψ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcards]
  -- equivariance
  refine ⟨AddEquiv.ofBijective Ψ hbij, fun g v => ?_⟩
  show Ψ (g • v) = g • Ψ v
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, muTwo_smul_trivial, hΨapply, hΨapply]
  congr 1
  have hps := polar_smul_smul V q hqG g (g⁻¹ • m) v
  rw [smul_inv_smul] at hps
  exact hps

/-- `H²` of an exponent-2 module has exponent 2 (pointwise, by quotient induction). -/
theorem h2_add_self (h2 : ∀ v : V, v + v = 0) (x : H2 AbsGalQ2 V) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext p
      exact h2 _
    show H2mk AbsGalQ2 V z + H2mk AbsGalQ2 V z = 0
    rw [← map_add, hz, map_zero]

/-- **`#H² = 1` from `#H⁰ = 1`** (Tate duality B6 via the parameter `D`, `(0,2)` clause at
`M := V`, through the polar self-duality and exp-2 Pontryagin duality). -/
theorem card_H2_eq_one_of_card_H0_eq_one (D : TateDuality 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (h2 : ∀ v : V, v + v = 0) (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (hfin : Finite (H2 AbsGalQ2 V))
    (hH0 : Nat.card (H0 AbsGalQ2 V) = 1) :
    Nat.card (H2 AbsGalQ2 V) = 1 := by
  have htor : ∀ x : V, (2 : ℕ) • x = 0 := fun x => by rw [two_nsmul]; exact h2 x
  obtain ⟨e, he⟩ := exists_polarSelfDual V q hq hns h2 hqG
  have hd : Nat.card (H0 AbsGalQ2 (MuDual 2 V)) = Nat.card (H0 AbsGalQ2 V) :=
    card_H0_congr e he
  have hdual := D.card_H0_dual V htor
  haveI := hfin
  have hhom := card_addHom_zmod2 (H2 AbsGalQ2 V) (h2_add_self V h2)
  calc Nat.card (H2 AbsGalQ2 V)
      = Nat.card (H2 AbsGalQ2 V →+ ZMod 2) := hhom.symm
    _ = Nat.card (H0 AbsGalQ2 (MuDual 2 V)) := hdual.symm
    _ = Nat.card (H0 AbsGalQ2 V) := hd
    _ = 1 := hH0

/-- A finite exponent-2 group has 2-power order. -/
theorem card_eq_two_pow_of_exp_two {A : Type*} [AddCommGroup A] [Finite A]
    (h2 : ∀ a : A, a + a = 0) : ∃ k : ℕ, Nat.card A = 2 ^ k := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : Module (ZMod 2) A := AddCommGroup.zmodModule (n := 2)
    (by intro x; rw [two_nsmul, h2 x])
  letI : Fintype A := Fintype.ofFinite A
  refine ⟨Module.finrank (ZMod 2) A, ?_⟩
  rw [Nat.card_eq_fintype_card, Module.card_eq_pow_finrank (K := ZMod 2) (V := A), ZMod.card]

/-- **`#H¹ = #V` in the §6.3 setting** (steps 1–2 of `lemma_6_17_dim` / Prop 6.18 assembled):
simple `C`-module, surjective classifying map, an element moving a vector, a nonsingular
invariant form.  Ax: **B6** (via `D`), **B7** (`finite_H2` + the Euler collapse). -/
theorem card_H1_eq_card_of_simple (D : TateDuality 2) {C : Type*} [Group C]
    [DistribMulAction C V]
    (ρ : AbsGalQ2 →* C) (hρsurj : Function.Surjective ρ)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ v : V, h₀ • v ≠ v)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (h2 : ∀ v : V, v + v = 0) :
    Nat.card (H1 AbsGalQ2 V) = Nat.card V := by
  have hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v := fun g v => by
    rw [hρ]; exact hinv _ v
  have hH0 : Nat.card (H0 AbsGalQ2 V) = 1 :=
    card_H0_eq_one_of_surjective ρ hρsurj hρ hsimple h₀ hmoves
  have hH2 : Nat.card (H2 AbsGalQ2 V) = 1 :=
    card_H2_eq_one_of_card_H0_eq_one V D q hq hns h2 hqG (finite_H2 V) hH0
  obtain ⟨k, hk⟩ := card_eq_two_pow_of_exp_two h2
  exact card_H1_eq_card_of_H0_H2_trivial hH0 hH2 hk

end PolarDual

/-! ## The `Q⁰_loc` quadratic structure  (§6.3, eq. (93))

`Q⁰_loc` is a quadratic map on `H¹(G_ℚ₂, V)` whose polar form is the cup product of the polar
pairing (through `ι_F`): at the cochain level,
`gp(b₁+b₂) − gp(b₁) − gp(b₂) − (b₂ ∪_B b₁) = δ¹(g ↦ f(b₁ g, b₂ g))`,
by four instances of the factor-set cocycle identity and `f_polar` — no bilinearity of `f`
needed.  Class level via `RepIndependence.repIndep` (Lemma 6.4). -/

section Q0locLayer

open Corestriction SectionSix RepIndependence GQ2.QuadraticFp2

variable {C : Type} [Group C] [TopologicalSpace C] [DiscreteTopology C] [Finite C]
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [DiscreteTopology V] [Finite V]
  [DistribMulAction AbsGalQ2 V] [ContinuousSMul AbsGalQ2 V] [DistribMulAction C V]

/-- **The (93) cochain identity**: the graph pullback is quadratic in the cocycle, with the
cup cocycle of the polar pairing (swapped slots) as cross-term, up to the explicit coboundary
`δ¹(g ↦ f(b₁ g, b₂ g))`. -/
theorem graphPullback_add_sub_mem_B2 (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (b₁ b₂ : ↥(Z1 AbsGalQ2 V)) :
    graphPullback dat ρ ((b₁ + b₂ : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)
      - (graphPullback dat ρ b₁.1 + graphPullback dat ρ b₂.1
        + cup11Fun (polarBihom q hq) b₂.1 b₁.1) ∈ B2 AbsGalQ2 (ZMod 2) := by
  obtain ⟨hb₁c, hb₁⟩ := mem_Z1_iff.mp b₁.2
  obtain ⟨hb₂c, hb₂⟩ := mem_Z1_iff.mp b₂.2
  refine AddSubgroup.mem_map.mpr ⟨fun g => dat.f (b₁.1 g) (b₂.1 g), ?_, ?_⟩
  · -- continuity of the correcting 1-cochain
    refine mem_C1_iff.mpr ?_
    have hF : Continuous fun g : AbsGalQ2 => ((b₁.1 g, b₂.1 g) : V × V) := hb₁c.prodMk hb₂c
    exact (continuous_of_discreteTopology (f := fun t : V × V => dat.f t.1 t.2)).comp hF
  · funext p
    obtain ⟨g, h⟩ := p
    have hgh₁ : b₁.1 (g * h) = b₁.1 g + ρ g • b₁.1 h := by rw [hb₁ g h, hρ]
    have hgh₂ : b₂.1 (g * h) = b₂.1 g + ρ g • b₂.1 h := by rw [hb₂ g h, hρ]
    have hm := hdat.m_quad (ρ g) (b₁.1 h) (b₂.1 h)
    have R₁ := hdat.f_cocycle (b₁.1 g) (b₂.1 g) (ρ g • b₁.1 h + ρ g • b₂.1 h)
    have R₂ := hdat.f_cocycle (b₁.1 g) (ρ g • b₁.1 h) (b₂.1 g + ρ g • b₂.1 h)
    have R₃ := hdat.f_cocycle (b₂.1 g) (ρ g • b₁.1 h) (ρ g • b₂.1 h)
    have R₄ := hdat.f_cocycle (ρ g • b₁.1 h) (b₂.1 g) (ρ g • b₂.1 h)
    have P := hdat.f_polar (b₂.1 g) (ρ g • b₁.1 h)
    rw [show b₂.1 g + (ρ g • b₁.1 h + ρ g • b₂.1 h)
        = ρ g • b₁.1 h + (b₂.1 g + ρ g • b₂.1 h) from by abel] at R₁
    rw [show ρ g • b₁.1 h + b₂.1 g = b₂.1 g + ρ g • b₁.1 h from by abel] at R₄
    simp only [dOne, AddMonoidHom.coe_mk, ZeroHom.coe_mk, absGal_smul_zmodTwo,
      Pi.sub_apply, Pi.add_apply, AddSubgroup.coe_add, graphPullback, cup11Fun,
      polarBihom_apply, smul_add]
    rw [hgh₁, hgh₂]
    simp only [hρ]
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
      hm + R₁ + R₂ + R₃ + R₄ + P

/-- `Q⁰_loc` unfolded (definitional). -/
theorem Q0loc_apply (D : TateDuality 2) (dat : FactorSet C V)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (x : H1 AbsGalQ2 V) :
    Q0loc D dat ρ x
      = iotaF D (H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1)) := rfl

/-- The polar pairing is `G_ℚ₂`-equivariant for a Galois-invariant `q` (`𝔽₂` acts trivially). -/
theorem polarBihom_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) (g : AbsGalQ2) (v w : V) :
    polarBihom q hq (g • v) (g • w) = g • polarBihom q hq v w := by
  rw [absGal_smul_zmodTwo, polarBihom_apply, polarBihom_apply]
  exact polar_smul_smul V q hqG g v w

/-- **Eq. (93), class level**: `Q⁰_loc(x+y) = Q⁰_loc(x) + Q⁰_loc(y) + ι_F(y ∪_B x)`. -/
theorem Q0loc_add (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (x y : H1 AbsGalQ2 V) :
    Q0loc D dat ρ (x + y)
      = Q0loc D dat ρ x + Q0loc D dat ρ y
        + iotaF D (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x) := by
  classical
  have hmem₁ : graphPullback dat ρ (Quotient.out x).1 ∈ Z2 AbsGalQ2 (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₂ : graphPullback dat ρ (Quotient.out y).1 ∈ Z2 AbsGalQ2 (ZMod 2) :=
    graphPullback_mem_Z2 dat hdat ρ hρ _
  have hmem₃ : cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1
      ∈ Z2 AbsGalQ2 (ZMod 2) :=
    cup11_mem_Z2 _ (polarBihom_equivariant q hq hqG) _ _
  have hrep : H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out (x + y)).1)
      = H2ofFun AbsGalQ2 (graphPullback dat ρ
          ((Quotient.out x + Quotient.out y : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)) := by
    apply repIndep dat hdat ρ hρ
    rw [H1mk_out, map_add, H1mk_out, H1mk_out]
  have hsplit : H2ofFun AbsGalQ2 (graphPullback dat ρ
        ((Quotient.out x + Quotient.out y : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V))
      = H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out x).1
          + graphPullback dat ρ (Quotient.out y).1
          + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1) :=
    h2ofFun_eq_of_sub_mem_B2 (graphPullback_add_sub_mem_B2 q hq dat hdat ρ hρ _ _)
  rw [Q0loc_apply, Q0loc_apply, Q0loc_apply, hrep, hsplit,
    H2ofFun_of_mem (add_mem (add_mem hmem₁ hmem₂) hmem₃),
    H2ofFun_of_mem hmem₁, H2ofFun_of_mem hmem₂]
  have hmk : (⟨graphPullback dat ρ (Quotient.out x).1
        + graphPullback dat ρ (Quotient.out y).1
        + cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1,
      add_mem (add_mem hmem₁ hmem₂) hmem₃⟩ : ↥(Z2 AbsGalQ2 (ZMod 2)))
      = ⟨graphPullback dat ρ (Quotient.out x).1, hmem₁⟩
        + ⟨graphPullback dat ρ (Quotient.out y).1, hmem₂⟩
        + ⟨cup11Fun (polarBihom q hq) (Quotient.out y).1 (Quotient.out x).1, hmem₃⟩ :=
    Subtype.ext rfl
  rw [hmk, map_add, map_add, map_add, map_add]
  congr 1
  conv_rhs => rw [← H1mk_out y, ← H1mk_out x, cup11_mk_mk]

/-- **The polar form of `Q⁰_loc`** is the (swapped) polar-pairing cup through `ι_F` —
eq. (93) in polar form. -/
theorem polar_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (x y : H1 AbsGalQ2 V) :
    polar (Q0loc D dat ρ) x y
      = iotaF D (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x) := by
  unfold GQ2.QuadraticFp2.polar
  rw [Q0loc_add D q hq dat hdat ρ hρ hqG x y]
  linear_combination CharTwo.add_self_eq_zero (Q0loc D dat ρ x)
    + CharTwo.add_self_eq_zero (Q0loc D dat ρ y)

/-- **`Q⁰_loc` is a quadratic map** on `H¹(G_ℚ₂, V)` (eq. (93)): normalized with biadditive
polar form. -/
theorem isQuadraticFp2_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    IsQuadraticFp2 (Q0loc D dat ρ (V := V)) := by
  constructor
  · -- normalization `Q⁰_loc(0) = 0`
    have hzero : graphPullback dat ρ ((0 : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V) = 0 := by
      funext p
      show dat.f ((0 : AbsGalQ2 → V) p.1) (ρ p.1 • (0 : AbsGalQ2 → V) p.2)
          + dat.m (ρ p.1) ((0 : AbsGalQ2 → V) p.2) = 0
      simp only [Pi.zero_apply]
      rw [hdat.f_zero_left, hdat.m_zero, add_zero]
    have hrep0 : H2ofFun AbsGalQ2 (graphPullback dat ρ (Quotient.out (0 : H1 AbsGalQ2 V)).1)
        = H2ofFun AbsGalQ2 (graphPullback dat ρ ((0 : ↥(Z1 AbsGalQ2 V)) : AbsGalQ2 → V)) := by
      apply repIndep dat hdat ρ hρ
      rw [H1mk_out, map_zero]
    rw [Q0loc_apply, hrep0, hzero, H2ofFun_of_mem (zero_mem _),
      show (⟨(0 : AbsGalQ2 × AbsGalQ2 → ZMod 2), zero_mem _⟩
        : ↥(Z2 AbsGalQ2 (ZMod 2))) = 0 from rfl,
      map_zero, map_zero]
  · -- polar additive, left
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, map_add]
  · -- polar additive, right
    intro u v w
    rw [polar_Q0loc D q hq dat hdat ρ hρ hqG, polar_Q0loc D q hq dat hdat ρ hρ hqG,
      polar_Q0loc D q hq dat hdat ρ hρ hqG, map_add, AddMonoidHom.add_apply, map_add]

/-! ### Nonsingularity of `Q⁰_loc`  (B6 `perfect11` via the polar `μ₂`-dual) -/

/-- SectionSix's `𝔽₂ → μ₂` bridge is (definitionally) the `DeepPart` one. -/
theorem muTwoOfF2_eq : SectionSix.muTwoOfF2 = zmodTwoToMuTwo := rfl

theorem zmodTwoToMuTwo_injective : Function.Injective zmodTwoToMuTwo := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  have hcases : ∀ z : ZMod 2, z = 0 ∨ z = 1 := by decide
  rcases hcases a with rfl | rfl
  · rfl
  · rw [zmodTwoToMuTwo_one] at ha
    exact absurd ha muTwoGen_ne_zero

theorem muTwoOfF2_injective : Function.Injective SectionSix.muTwoOfF2 := by
  rw [muTwoOfF2_eq]
  exact zmodTwoToMuTwo_injective

/-- The `μ₂`-valued polar self-duality `v ↦ (w ↦ bridge(B(v,w)))` — definitionally
`postPairing` of the polar pairing with the bridge, viewed into the `μ₂`-dual. -/
noncomputable def polarMuDual (q : V → ZMod 2) (hq : IsQuadraticFp2 q) : V →+ MuDual 2 V :=
  postPairing (polarBihom q hq) SectionSix.muTwoOfF2


/-- Equivariance of the polar `μ₂`-dual map. -/
theorem polarMuDual_equivariant (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) (g : AbsGalQ2) (v : V) :
    polarMuDual q hq (g • v) = g • polarMuDual q hq v := by
  refine DFunLike.ext _ _ fun m => ?_
  rw [muDual_smul_apply, muTwo_smul_trivial]
  show SectionSix.muTwoOfF2 (polar q (g • v) m) = SectionSix.muTwoOfF2 (polar q v (g⁻¹ • m))
  congr 1
  have hps := polar_smul_smul V q hqG g v (g⁻¹ • m)
  rwa [smul_inv_smul] at hps

/-- `#Hom(V, μ₂) = #V` for exp-2 `V`. -/
theorem card_muDual (h2 : ∀ v : V, v + v = 0) : Nat.card (MuDual 2 V) = Nat.card V := by
  have h1 : Nat.card (MuDual 2 V) = Nat.card (V →+ ZMod 2) := by
    refine Nat.card_congr ⟨fun f => zmodTwoEquivMuTwo.symm.toAddMonoidHom.comp (f : V →+ MuN 2),
      fun f => (zmodTwoEquivMuTwo.toAddMonoidHom.comp f : MuDual 2 V), fun f => ?_, fun f => ?_⟩
    · refine DFunLike.ext _ _ fun m => ?_
      show zmodTwoEquivMuTwo (zmodTwoEquivMuTwo.symm ((f : V →+ MuN 2) m)) = f m
      rw [AddEquiv.apply_symm_apply]
    · ext m
      show zmodTwoEquivMuTwo.symm (zmodTwoEquivMuTwo (f m)) = f m
      rw [AddEquiv.symm_apply_apply]
  rw [h1, card_addHom_zmod2 V h2]

/-- The polar `μ₂`-dual map is bijective (nonsingularity + counting). -/
theorem polarMuDual_bijective (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0) :
    Function.Bijective (polarMuDual q hq (V := V)) := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  haveI : Fintype (MuDual 2 V) := Fintype.ofFinite _
  have hinj : Function.Injective (polarMuDual q hq (V := V)) := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    by_contra hne
    obtain ⟨w, hw⟩ := hns v hne
    apply hw
    have h0 : SectionSix.muTwoOfF2 (polar q v w) = 0 := by
      have := DFunLike.congr_fun hv w
      rwa [MuDual.zero_apply] at this
    exact muTwoOfF2_injective (by rw [h0, map_zero])
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨hinj, ?_⟩
  rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_muDual h2]

/-- **`mapCoeff1` of an equivariant additive bijection is injective** (coboundaries pull back
along the inverse). -/
theorem mapCoeff1_injective {A B : Type} [AddCommGroup A] [AddCommGroup B]
    [TopologicalSpace A] [TopologicalSpace B] [DiscreteTopology A] [DiscreteTopology B]
    [DistribMulAction AbsGalQ2 A] [ContinuousSMul AbsGalQ2 A]
    [DistribMulAction AbsGalQ2 B] [ContinuousSMul AbsGalQ2 B]
    (f : A →+ B) (hf : Continuous f)
    (hcompat : ∀ (g : AbsGalQ2) (a : A), f (g • a) = g • f a)
    (hinj : Function.Injective f) (hsurj : Function.Surjective f) :
    Function.Injective (mapCoeff1 f hf hcompat) := by
  rw [injective_iff_map_eq_zero]
  intro xq
  induction xq using QuotientAddGroup.induction_on with
  | H b =>
    intro hxq
    have hxq' : H1mk AbsGalQ2 B
        (Z1comap (ContinuousMonoidHom.id AbsGalQ2) f hf (fun g n => hcompat g n) b) = 0 := hxq
    have hmem := (QuotientAddGroup.eq_zero_iff _).mp hxq'
    rw [AddSubgroup.mem_addSubgroupOf] at hmem
    obtain ⟨n, hn⟩ := hmem
    obtain ⟨m, rfl⟩ := hsurj n
    show H1mk AbsGalQ2 A b = 0
    refine (QuotientAddGroup.eq_zero_iff b).mpr ?_
    rw [AddSubgroup.mem_addSubgroupOf]
    refine ⟨m, ?_⟩
    funext g
    apply hinj
    have hg := congrFun hn g
    show f (g • m - m) = f (b.1 g)
    rw [map_sub, hcompat]
    exact hg

/-- **Cup coefficient naturality at the polar pairing**: pushing the `𝔽₂`-valued polar cup along
the `μ₂`-bridge is the `μ₂`-evaluation cup against the polar `μ₂`-dual class (definitional at
representatives). -/
theorem mapCoeff2_muTwo_cup (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v)
    (y x : H1 AbsGalQ2 V) :
    mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
        SectionSix.muTwoOfF2_equivariant
        (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) y x)
      = cup11 (muDualPairing 2 V) (muDualPairing_equivariant 2 V)
          (mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
            (polarMuDual_equivariant q hq hqG) y) x := by
  induction y using QuotientAddGroup.induction_on with
  | H b =>
    induction x using QuotientAddGroup.induction_on with
    | H a => rfl

/-- **`Q⁰_loc` is nonsingular** (§6.3): its polar form is a perfect pairing on `H¹(G_ℚ₂, V)`,
via B6's `perfect11` clause through the polar `μ₂`-self-duality. -/
theorem nonsingular_Q0loc (D : TateDuality 2) (q : V → ZMod 2) (hq : IsQuadraticFp2 q)
    (hns : Nonsingular q) (h2 : ∀ v : V, v + v = 0)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v) :
    Nonsingular (Q0loc D dat ρ (V := V)) := by
  intro x hx
  have htor : ∀ v : V, (2 : ℕ) • v = 0 := fun v => by rw [two_nsmul]; exact h2 v
  have hbij := polarMuDual_bijective q hq hns h2
  have hxne : mapCoeff1 (polarMuDual q hq) continuous_of_discreteTopology
      (polarMuDual_equivariant q hq hqG) x ≠ 0 := by
    intro h0
    exact hx (mapCoeff1_injective _ _ _ hbij.1 hbij.2 (by rw [h0, map_zero]))
  obtain ⟨d, hd⟩ := D.exists_cup_ne_zero_of_ne_zero V htor hxne
  refine ⟨d, ?_⟩
  rw [polar_comm, polar_Q0loc D q hq dat hdat ρ hρ hqG d x]
  have hnat := mapCoeff2_muTwo_cup q hq hqG x d
  intro h0
  apply hd
  have hz : mapCoeff2 SectionSix.muTwoOfF2 continuous_of_discreteTopology
      SectionSix.muTwoOfF2_equivariant
      (cup11 (polarBihom q hq) (polarBihom_equivariant q hq hqG) x d) = 0 := by
    apply D.inv.injective
    rw [map_zero]
    exact h0
  rw [hnat] at hz
  exact hz

/-! ### The deep half `X₊` is a subgroup

`0 ∈ X₊` (witness `A = β = 1`; the zero class restricts to `0` on `ker ρ` since coboundaries die
there) and `X₊ + X₊ ⊆ X₊` (witness products: deep units are closed under multiplication, Kummer
cocycles are multiplicative on `ker ρ`-fixed squares, and `out(x+y) = out x + out y` up to a
coboundary that dies on `ker ρ`). -/

/-- `H¹` of an exponent-2 module has exponent 2. -/
theorem h1_add_self (hV2 : ∀ v : V, v + v = 0) (x : H1 AbsGalQ2 V) : x + x = 0 := by
  induction x using QuotientAddGroup.induction_on with
  | H z =>
    have hz : z + z = 0 := by
      apply Subtype.ext
      funext g
      exact hV2 _
    show H1mk AbsGalQ2 V z + H1mk AbsGalQ2 V z = 0
    rw [← map_add, hz, map_zero]

/-- A `Z¹`-cocycle whose class vanishes dies pointwise on `ker ρ` (the coboundary
`g ↦ g•w₀ − w₀` is trivial there since the action factors through `ρ`). -/
theorem vanish_on_ker_of_H1mk_eq_zero (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    {d : ↥(Z1 AbsGalQ2 V)} (hd : H1mk AbsGalQ2 V d = 0)
    (n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2)) : d.1 ↑n = 0 := by
  have hmem := (QuotientAddGroup.eq_zero_iff _).mp hd
  rw [AddSubgroup.mem_addSubgroupOf] at hmem
  obtain ⟨w₀, hw₀⟩ := hmem
  have hn := congrFun hw₀ (↑n : AbsGalQ2)
  rw [← hn]
  show (↑n : AbsGalQ2) • w₀ - w₀ = 0
  rw [hρ, show ρ ↑n = 1 from n.2, one_smul, sub_self]

/-- The restricted Kummer cocycle of an `N`-fixed square is a hom on `N` (sign bookkeeping via
`two_values_of_fixed`). -/
theorem kummerRestrict_hom {N : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A β : AlgebraicClosure ℚ_[2]}
    (hsq : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ N, g • A = A) (n m : ↥N) :
    Kummer.kummerCocycleFun β ((↑n : Kummer.GaloisGroup ℚ_[2]) * ↑m)
      = Kummer.kummerCocycleFun β ↑n + Kummer.kummerCocycleFun β ↑m := by
  have h2v : ∀ (g : ↥N), (↑g : Kummer.GaloisGroup ℚ_[2]) • β = β
      ∨ (↑g : Kummer.GaloisGroup ℚ_[2]) • β = -β := fun g =>
    two_values_of_fixed hsq (hAfix ↑g g.2)
  have heq1 : ∀ {g : Kummer.GaloisGroup ℚ_[2]}, g • β = -β →
      Kummer.kummerCocycleFun β g = 1 := fun {g} h =>
    if_neg (fun e => ne_neg_of_ne_zero hβ0 (e.symm.trans h))
  rcases h2v n with hg | hg <;> rcases h2v m with hh | hh
  · rw [Kummer.kummerCocycleFun_eq0 hg, Kummer.kummerCocycleFun_eq0 hh,
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh, hg])]
    decide
  · rw [Kummer.kummerCocycleFun_eq0 hg, heq1 hh, heq1 (by rw [mul_smul, hh, smul_neg, hg])]
    decide
  · rw [heq1 hg, Kummer.kummerCocycleFun_eq0 hh, heq1 (by rw [mul_smul, hh, hg])]
    decide
  · rw [heq1 hg, heq1 hh,
      Kummer.kummerCocycleFun_eq0 (by rw [mul_smul, hh, smul_neg, hg, neg_neg])]
    decide

/-- The restricted Kummer cocycle of an `N`-fixed square lies in `Z¹(N, 𝔽₂)`. -/
theorem kummerRestrict_mem_Z1 {N : Subgroup (Kummer.GaloisGroup ℚ_[2])}
    {A β : AlgebraicClosure ℚ_[2]}
    (hsq : β ^ 2 = A) (hβ0 : β ≠ 0) (hAfix : ∀ g ∈ N, g • A = A) :
    (fun n : ↥N => Kummer.kummerCocycleFun β ↑n) ∈ Z1 ↥N (ZMod 2) := by
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (Kummer.kummerCocycleFun_continuous β).comp continuous_subtype_val
  · show Kummer.kummerCocycleFun β ↑(n * m)
      = Kummer.kummerCocycleFun β ↑n + n • Kummer.kummerCocycleFun β ↑m
    have htriv : n • Kummer.kummerCocycleFun β ↑m = Kummer.kummerCocycleFun β ↑m := rfl
    rw [htriv, show (↑(n * m) : Kummer.GaloisGroup ℚ_[2]) = ↑n * ↑m from rfl,
      kummerRestrict_hom hsq hβ0 hAfix n m]

/-- The `φ`-coordinate of a cocycle restricted to `ker ρ` lies in `Z¹(ker ρ, 𝔽₂)` (the action
is trivial there). -/
theorem phiRestrict_mem_Z1 (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (b : ↥(Z1 AbsGalQ2 V)) (φ : V →+ ZMod 2) :
    (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) => φ (b.1 ↑n))
      ∈ Z1 ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) (ZMod 2) := by
  obtain ⟨hbc, hb⟩ := mem_Z1_iff.mp b.2
  refine mem_Z1_iff.mpr ⟨?_, fun n m => ?_⟩
  · exact (continuous_of_discreteTopology (f := fun v : V => φ v)).comp
      (hbc.comp continuous_subtype_val)
  · show φ (b.1 ↑(n * m)) = φ (b.1 ↑n) + n • φ (b.1 ↑m)
    have htriv : n • φ (b.1 ↑m) = φ (b.1 ↑m) := rfl
    rw [htriv, show (↑(n * m) : AbsGalQ2) = ↑n * ↑m from rfl, hb ↑n ↑m, hρ,
      show ρ ↑n = 1 from n.2, one_smul, map_add]

/-- `H1ofFun` is additive on actual cocycles. -/
theorem H1ofFun_add {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [DistribMulAction G (ZMod 2)] [ContinuousSMul G (ZMod 2)]
    {f g : G → ZMod 2} (hf : f ∈ Z1 G (ZMod 2)) (hg : g ∈ Z1 G (ZMod 2)) :
    H1ofFun G (f + g) = H1ofFun G f + H1ofFun G g := by
  rw [H1ofFun_of_mem (add_mem hf hg), H1ofFun_of_mem hf, H1ofFun_of_mem hg, ← map_add]
  rfl

/-- **The deep half `X₊` is an additive subgroup** of `H¹(G_ℚ₂, V)`. -/
noncomputable def deepPartSubgroup (ρ : ContinuousMonoidHom AbsGalQ2 C)
    (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hV2 : ∀ v : V, v + v = 0) : AddSubgroup (H1 AbsGalQ2 V) where
  carrier := deepPart (V := V) ρ
  zero_mem' := by
    intro φ
    refine ⟨1, 1, ?_, one_pow 2, one_ne_zero, ?_⟩
    · exact ⟨one_ne_zero, fun g _ => by rw [AlgEquiv.smul_def, map_one],
        0, fun g _ => smul_zero g, by ring, by rw [norm_zero]; exact zero_lt_one⟩
    · congr 1
      funext n
      rw [Kummer.kummerCocycleFun_eq0 (by rw [AlgEquiv.smul_def, map_one])]
      have hv := vanish_on_ker_of_H1mk_eq_zero ρ hρ (H1mk_out (0 : H1 AbsGalQ2 V)) n
      rw [hv, map_zero]
  add_mem' := by
    intro x y hx hy φ
    obtain ⟨A₁, β₁, hd₁, hsq₁, hne₁, heq₁⟩ := hx φ
    obtain ⟨A₂, β₂, hd₂, hsq₂, hne₂, heq₂⟩ := hy φ
    obtain ⟨hA₁0, hA₁fix, b₁, hb₁fix, hA₁eq, hb₁⟩ := hd₁
    obtain ⟨hA₂0, hA₂fix, b₂, hb₂fix, hA₂eq, hb₂⟩ := hd₂
    have h2le : ‖(2 : AlgebraicClosure ℚ_[2])‖ ≤ 1 := by
      rw [show (2 : AlgebraicClosure ℚ_[2]) = 1 + 1 by norm_num]
      refine (IsUltrametricDist.norm_add_le_max 1 1).trans ?_
      rw [norm_one, max_self]
    refine ⟨A₁ * A₂, β₁ * β₂, ?_, by rw [mul_pow, hsq₁, hsq₂],
      mul_ne_zero hne₁ hne₂, ?_⟩
    · -- deep units are closed under products
      refine ⟨mul_ne_zero hA₁0 hA₂0, fun g hg => ?_, b₁ + b₂ + 2 * b₁ * b₂,
        fun g hg => ?_, by rw [hA₁eq, hA₂eq]; ring, ?_⟩
      · rw [AlgEquiv.smul_def, map_mul, ← AlgEquiv.smul_def, ← AlgEquiv.smul_def,
          hA₁fix g hg, hA₂fix g hg]
      · rw [AlgEquiv.smul_def, map_add, map_add, map_mul, map_mul, map_ofNat,
          ← AlgEquiv.smul_def, ← AlgEquiv.smul_def, hb₁fix g hg, hb₂fix g hg]
      · -- ‖b₁ + b₂ + 2b₁b₂‖ < 1 (ultrametric)
        have hprod : ‖(2 : AlgebraicClosure ℚ_[2]) * b₁ * b₂‖ < 1 := by
          rw [norm_mul, norm_mul]
          calc ‖(2 : AlgebraicClosure ℚ_[2])‖ * ‖b₁‖ * ‖b₂‖
              ≤ 1 * ‖b₁‖ * ‖b₂‖ := by
                have := mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_right h2le (norm_nonneg b₁)) (norm_nonneg b₂)
                simpa using this
            _ = ‖b₁‖ * ‖b₂‖ := by ring
            _ ≤ ‖b₁‖ * 1 := mul_le_mul_of_nonneg_left hb₂.le (norm_nonneg b₁)
            _ = ‖b₁‖ := mul_one _
            _ < 1 := hb₁
        refine lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_
        rw [max_lt_iff]
        refine ⟨lt_of_le_of_lt (IsUltrametricDist.norm_add_le_max _ _) ?_, hprod⟩
        rw [max_lt_iff]
        exact ⟨hb₁, hb₂⟩
    · -- the Kummer coordinate of the sum
      -- LHS: κ_{β₁β₂}|N = κ_{β₁}|N + κ_{β₂}|N
      have hLHS : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          Kummer.kummerCocycleFun (β₁ * β₂) (n : AbsGalQ2))
          = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₂ (n : AbsGalQ2) := by
        funext n
        exact kcf_mul_of_fixed (by rw [mul_pow, hsq₁, hsq₂]) hsq₁ hsq₂ hne₁ hne₂
          (hA₁fix (n : AbsGalQ2) n.2) (hA₂fix (n : AbsGalQ2) n.2)
      -- RHS: φ∘out(x+y)|N = φ∘out x|N + φ∘out y|N
      have hRHS : (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
          φ ((Quotient.out (x + y)).1 (n : AbsGalQ2)))
          = (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              φ ((Quotient.out x).1 (n : AbsGalQ2)))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              φ ((Quotient.out y).1 (n : AbsGalQ2)) := by
        funext n
        have hd0 : H1mk AbsGalQ2 V
            (Quotient.out (x + y) - (Quotient.out x + Quotient.out y)) = 0 := by
          rw [map_sub, map_add, H1mk_out, H1mk_out, H1mk_out, sub_self]
        have hv := vanish_on_ker_of_H1mk_eq_zero ρ hρ hd0 n
        have hpt : (Quotient.out (x + y)).1 (n : AbsGalQ2)
            = (Quotient.out x).1 (n : AbsGalQ2) + (Quotient.out y).1 (n : AbsGalQ2) := by
          have hexp : (Quotient.out (x + y) - (Quotient.out x + Quotient.out y) :
              ↥(Z1 AbsGalQ2 V)).1 (n : AbsGalQ2)
              = (Quotient.out (x + y)).1 (n : AbsGalQ2)
                - ((Quotient.out x).1 (n : AbsGalQ2)
                    + (Quotient.out y).1 (n : AbsGalQ2)) := by
            show (Quotient.out (x + y)).1 (n : AbsGalQ2)
                - ((Quotient.out x).1 + (Quotient.out y).1) (n : AbsGalQ2) = _
            rw [Pi.add_apply]
          rw [hexp] at hv
          exact sub_eq_zero.mp hv
        show φ ((Quotient.out (x + y)).1 (n : AbsGalQ2)) = _
        rw [hpt, map_add]
        rfl
      have hadd₁ : H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
          ((fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
              Kummer.kummerCocycleFun β₂ (n : AbsGalQ2))
          = H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
              (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                Kummer.kummerCocycleFun β₁ (n : AbsGalQ2))
            + H1ofFun (↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2))
              (fun n : ↥(ρ.toMonoidHom.ker : Subgroup AbsGalQ2) =>
                Kummer.kummerCocycleFun β₂ (n : AbsGalQ2)) :=
        H1ofFun_add (kummerRestrict_mem_Z1 hsq₁ hne₁ hA₁fix)
          (kummerRestrict_mem_Z1 hsq₂ hne₂ hA₂fix)
      rw [hLHS, hRHS, hadd₁,
        H1ofFun_add (phiRestrict_mem_Z1 ρ hρ _ φ) (phiRestrict_mem_Z1 ρ hρ _ φ),
        heq₁, heq₂]
  neg_mem' := by
    intro x hx
    have hneg : -x = x := neg_eq_of_add_eq_zero_left (h1_add_self hV2 x)
    rw [hneg]
    exact hx


/-! ### The dim clause and Prop 6.18 (ramified), reduced to the two Kummer cores -/


/-- **Prop 6.18 (eq. (115), ramified) from Lemma 6.17**: given the dim clause (`hdim`,
`#X₊² = #H¹`) and the vanishing clause (`hvanish`, `Q⁰_loc|X₊ = 0`), the zero-count of
`Q⁰_loc` is `2^{2m−1} + 2^{m−1}` — the positive Gauss sign, via the Lagrangian Arf package
(`arf_zero_of_card_sq`) and the Euler-characteristic count.  Ax: **B6** (via `D`), **B7**. -/
theorem card_Q0loc_zero_eq_of_dim_of_vanish (D : TateDuality 2)
    (q : V → ZMod 2) (hq : IsQuadraticFp2 q) (hns : Nonsingular q)
    (dat : FactorSet C V) (hdat : IsEquivariantFactorSet q dat)
    (ρ : ContinuousMonoidHom AbsGalQ2 C) (hρ : ∀ (g : AbsGalQ2) (v : V), g • v = ρ g • v)
    (hρsurj : Function.Surjective ρ)
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (h₀ : C) (hmoves : ∃ v : V, h₀ • v ≠ v)
    (hinv : ∀ (c : C) (v : V), q (c • v) = q v)
    (hV2 : ∀ v : V, v + v = 0)
    (hdim : Nat.card (deepPart (V := V) ρ) ^ 2 = Nat.card (H1 AbsGalQ2 V))
    (hvanish : ∀ x ∈ deepPart (V := V) ρ, Q0loc D dat ρ x = 0)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) :
    Nat.card {x : H1 AbsGalQ2 V // Q0loc D dat ρ x = 0}
      = 2 ^ (2 * m - 1) + 2 ^ (m - 1) := by
  haveI : Finite (H1 AbsGalQ2 V) := finite_H1 V
  haveI : Fintype (H1 AbsGalQ2 V) := Fintype.ofFinite _
  have hqG : ∀ (g : AbsGalQ2) (v : V), q (g • v) = q v := fun g v => by
    rw [hρ]; exact hinv _ v
  have hq' := isQuadraticFp2_Q0loc D q hq dat hdat ρ hρ hqG
  have hns' := nonsingular_Q0loc D q hq hns hV2 dat hdat ρ hρ hqG
  have h2H1 := h1_add_self (V := V) hV2
  have hH1card : Nat.card (H1 AbsGalQ2 V) = 2 ^ (2 * m) := by
    rw [card_H1_eq_card_of_simple V D ρ.toMonoidHom hρsurj hρ hsimple h₀ hmoves
      q hq hns hinv hV2, hcard]
  have harf : arf (Q0loc D dat ρ (V := V)) = 0 :=
    arf_zero_of_card_sq _ hq' h2H1 hns' (deepPartSubgroup ρ hρ hV2)
      (fun x hx => hvanish x hx) hdim
  have hzc := zeroCount_of_arf_zero (Q0loc D dat ρ) hq' hns' hm
    (by rw [← Nat.card_eq_fintype_card]; exact hH1card) harf
  exact hzc

/-- The two-torsion subgroup of a `2^{2m}`-order simple module is everything: `V` has
exponent 2 (additive Cauchy + simplicity). -/
theorem exp_two_of_simple_of_card {C : Type*} [Group C] [DistribMulAction C V]
    (hsimple : ∀ W : AddSubgroup V, (∀ (h : C), ∀ w ∈ W, h • w ∈ W) → W = ⊥ ∨ W = ⊤)
    (m : ℕ) (hm : 1 ≤ m) (hcard : Nat.card V = 2 ^ (2 * m)) : ∀ v : V, v + v = 0 := by
  classical
  haveI : Fintype V := Fintype.ofFinite V
  set T : AddSubgroup V :=
    { carrier := {v : V | v + v = 0}
      zero_mem' := by simp
      add_mem' := fun {a b} ha hb => by
        show a + b + (a + b) = 0
        have h : a + b + (a + b) = (a + a) + (b + b) := by abel
        rw [h, ha, hb, add_zero]
      neg_mem' := fun {a} ha => by
        show -a + -a = 0
        have h : -a + -a = -(a + a) := by abel
        rw [h, ha, neg_zero] } with hT
  have hstable : ∀ (h : C), ∀ w ∈ T, h • w ∈ T := by
    intro h w hw
    show h • w + h • w = 0
    rw [← smul_add, hw, smul_zero]
  have hTne : T ≠ ⊥ := by
    have h2 : (2 : ℕ) ∣ Nat.card V := by
      rw [hcard]
      exact dvd_pow_self 2 (by omega)
    rw [Nat.card_eq_fintype_card] at h2
    obtain ⟨v, hv⟩ := exists_prime_addOrderOf_dvd_card 2 h2
    intro hbot
    have hvT : v ∈ T := by
      show v + v = 0
      have := addOrderOf_nsmul_eq_zero v
      rwa [hv, two_nsmul] at this
    rw [hbot, AddSubgroup.mem_bot] at hvT
    rw [hvT] at hv
    simp at hv
  rcases hsimple T hstable with hbot | htop
  · exact absurd hbot hTne
  · intro v
    have : v ∈ T := htop ▸ AddSubgroup.mem_top v
    exact this

/- **Proposition 6.18 (dyadic base determinant theorem), ramified case** — re-homed to
`GQ2.DetRamified.prop_6_18_ramified` (P-15f8/f2d statement-move, 2026-07-08): now that both
Lemma-6.17 clauses are proved DOWNSTREAM (`ResidueLift.lemma_6_17_dim_final`,
`VanishClose.lemma_6_17_vanish_final`), `prop_6_18_ramified` — their sole consumer — moves below
them so it cites the real proofs (`card_Q0loc_zero_eq_of_dim_of_vanish` above is the banked
reduction it feeds).  This file (`DeepPart`) is upstream of the two proofs, hence the move; the
`(R, horient)` amendment travels with it. -/

end Q0locLayer

/-! ## The Hermitian-line count  (paper Prop 6.18, unramified computation)

The final computation of the paper's Prop 6.18 (unramified case): on `D = 𝔽_{2^{2m}}` the
Hermitian trace form `x ↦ Tr(c·x^{2^m+1})` (`c` outside the fixed field `D₀ = 𝔽_{2^m}`,
so the `D₀`-level form `Tr_{D₀/𝔽₂}(a·N(x))` in absolute-trace clothing) has exactly
`1 + (2^m+1)(2^{m−1}−1) = 2^{2m−1} − 2^{m−1}` zeros — the minus-type count.  Everything is
finite-field counting: norm fibres are `ker`-cosets of size `2^m+1` (cyclic `gcd` count), and
the nonzero trace-kernel of the fixed field contributes `2^{m−1}−1`. -/

section HermitianCount

open GQ2.QuadraticFp2

variable {D : Type*} [Field D] [Fintype D]

/-- A field of order `2^{2m}` (`m ≥ 1`) has characteristic 2. -/
theorem ringChar_eq_two_of_card {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) : ringChar D = 2 := by
  obtain ⟨n, hp, hn⟩ := FiniteField.card D (ringChar D)
  have h1 : ringChar D ∣ Fintype.card D := by
    rw [hn]
    exact dvd_pow_self _ n.2.ne'
  rw [hcard] at h1
  exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)

/-- The absolute trace of `D = 𝔽_{2^{2m}}`, written as the Frobenius-power sum. -/
theorem algebraMap_trace_eq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    algebraMap (ZMod (ringChar D)) D (Algebra.trace (ZMod (ringChar D)) D z)
      = ∑ i ∈ Finset.range (2 * m), z ^ 2 ^ i := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  have hcK : Nat.card (ZMod (ringChar D)) = 2 := by
    rw [Nat.card_eq_fintype_card, ZMod.card, hchar]
  have hrank : Module.finrank (ZMod (ringChar D)) D = 2 * m := by
    have hc2 : Fintype.card (ZMod (ringChar D)) = 2 := by rw [ZMod.card, hchar]
    have hpow := Module.card_eq_pow_finrank (K := ZMod (ringChar D)) (V := D)
    rw [hc2, hcard] at hpow
    exact (Nat.pow_right_injective le_rfl hpow.symm)
  have hsum := FiniteField.algebraMap_trace_eq_sum_pow (ZMod (ringChar D)) D z
  rw [hrank, hcK] at hsum
  exact hsum

/-- Detecting trace-vanishing through the Frobenius-power sum. -/
theorem trace_eq_zero_iff {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    Algebra.trace (ZMod (ringChar D)) D z = 0
      ↔ ∑ i ∈ Finset.range (2 * m), z ^ 2 ^ i = 0 := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  have hinj := (algebraMap (ZMod (ringChar D)) D).injective
  constructor
  · intro h
    have := algebraMap_trace_eq hm hcard z
    rw [h, map_zero] at this
    exact this.symm
  · intro h
    apply hinj
    rw [algebraMap_trace_eq hm hcard z, h, map_zero]

/-- **Frobenius-invariance of the trace**: `Tr(z²) = Tr(z)` (shift the Frobenius sum). -/
theorem trace_pow_two {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (z : D) :
    Algebra.trace (ZMod (ringChar D)) D (z ^ 2) = Algebra.trace (ZMod (ringChar D)) D z := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : Fact (Nat.Prime (ringChar D)) := ⟨by rw [hchar]; exact Nat.prime_two⟩
  apply (algebraMap (ZMod (ringChar D)) D).injective
  rw [algebraMap_trace_eq hm hcard, algebraMap_trace_eq hm hcard]
  have hpt : ∀ i, (z ^ 2) ^ 2 ^ i = z ^ 2 ^ (i + 1) := by
    intro i
    rw [← pow_mul, ← pow_succ']
  rw [Finset.sum_congr rfl (fun i _ => hpt i)]
  have h1 := Finset.sum_range_succ' (fun i => z ^ 2 ^ i) (2 * m)
  have h2 := Finset.sum_range_succ (fun i => z ^ 2 ^ i) (2 * m)
  have hf0 : z ^ 2 ^ 0 = z := by rw [pow_zero, pow_one]
  have hfn : z ^ 2 ^ (2 * m) = z := by
    rw [← hcard]
    exact FiniteField.pow_card z
  have hkey := h1.symm.trans h2
  rw [hf0, hfn] at hkey
  exact add_right_cancel hkey

/-- Iterated Frobenius-invariance: `Tr(z^{2^k}) = Tr(z)`. -/
theorem trace_pow_pow {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (k : ℕ) (z : D) :
    Algebra.trace (ZMod (ringChar D)) D (z ^ 2 ^ k) = Algebra.trace (ZMod (ringChar D)) D z := by
  induction k with
  | zero => rw [pow_zero, pow_one]
  | succ n ih =>
    have hz : z ^ 2 ^ (n + 1) = (z ^ 2 ^ n) ^ 2 := by
      rw [← pow_mul, pow_succ]
    rw [hz, trace_pow_two hm hcard, ih]

/-- **The trace vanishes on the fixed field**: `Tr(y) = 0` whenever `y^{2^m} = y` (the
Frobenius-sum doubles up in characteristic 2). -/
theorem trace_eq_zero_of_frobenius_fixed {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) [Algebra (ZMod (ringChar D)) D]
    {y : D} (hy : y ^ 2 ^ m = y) :
    Algebra.trace (ZMod (ringChar D)) D y = 0 := by
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  rw [trace_eq_zero_iff hm hcard]
  have hsplit : ∑ i ∈ Finset.range (2 * m), y ^ 2 ^ i
      = (∑ i ∈ Finset.range m, y ^ 2 ^ i) + ∑ i ∈ Finset.range m, y ^ 2 ^ (m + i) := by
    rw [two_mul]
    exact Finset.sum_range_add (fun i => y ^ 2 ^ i) m m
  have hshift : ∀ i, y ^ 2 ^ (m + i) = y ^ 2 ^ i := by
    intro i
    rw [pow_add, pow_mul, hy]
  rw [hsplit, Finset.sum_congr rfl (fun i _ => hshift i)]
  exact CharTwo.add_self_eq_zero _

/-- **Solution count of `y^n = y`** via the unit split: `1 + #{u : Dˣ | u^{n−1} = 1}`. -/
theorem card_pow_fixed (n : ℕ) (hn : 2 ≤ n) :
    Nat.card {y : D // y ^ n = y} = 1 + Nat.card {u : Dˣ // u ^ (n - 1) = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype,
    Fintype.card_subtype]
  have hzero : (0 : D) ∈ Finset.univ.filter (fun y : D => y ^ n = y) := by
    simp [zero_pow (by omega : n ≠ 0)]
  have hsplit : Finset.univ.filter (fun y : D => y ^ n = y)
      = insert (0 : D) ((Finset.univ.filter (fun y : D => y ^ n = y)).erase 0) := by
    rw [Finset.insert_erase hzero]
  rw [hsplit, Finset.card_insert_of_notMem (Finset.notMem_erase 0 _), add_comm]
  congr 1
  symm
  refine Finset.card_bij (fun u _ => (↑u : D)) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu
    rw [Finset.mem_erase, Finset.mem_filter]
    refine ⟨u.ne_zero, Finset.mem_univ _, ?_⟩
    have : (↑(u ^ (n - 1)) : D) = 1 := by rw [hu.2]; rfl
    rw [Units.val_pow_eq_pow_val] at this
    calc (↑u : D) ^ n = (↑u : D) ^ (n - 1) * ↑u := by
          rw [← pow_succ]
          congr 1
          omega
      _ = ↑u := by rw [this, one_mul]
  · intro u _ v _ huv
    exact Units.ext huv
  · intro y hy
    rw [Finset.mem_erase, Finset.mem_filter] at hy
    obtain ⟨hy0, _, hyn⟩ := hy
    refine ⟨Units.mk0 y hy0, ?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, Units.val_one]
    have hstep : y ^ (n - 1) * y = 1 * y := by
      rw [one_mul, ← pow_succ]
      rw [show n - 1 + 1 = n from by omega]
      exact hyn
    exact mul_right_cancel₀ hy0 hstep

/-- The Frobenius^m-fixed subfield `𝔽_{2^m} ⊆ D`, as an additive subgroup. -/
def frobFixed (D : Type*) [Field D] [CharP D 2] (m : ℕ) : AddSubgroup D where
  carrier := {y : D | y ^ 2 ^ m = y}
  zero_mem' := by
    show (0 : D) ^ 2 ^ m = 0
    exact zero_pow (Nat.pos_of_neZero _).ne'
  add_mem' := fun {a b} ha hb => by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    show (a + b) ^ 2 ^ m = a + b
    rw [add_pow_char_pow, ha, hb]
  neg_mem' := fun {a} ha => by
    show (-a) ^ 2 ^ m = -a
    rw [CharTwo.neg_eq, ha]

@[simp] theorem mem_frobFixed [CharP D 2] (m : ℕ) (y : D) :
    y ∈ frobFixed D m ↔ y ^ 2 ^ m = y := Iff.rfl

/-- `#𝔽_{2^m} = 2^m` inside `D = 𝔽_{2^{2m}}` (cyclic `gcd` count on the units). -/
theorem card_frobFixed {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [CharP D 2] : Nat.card ↥(frobFixed D m) = 2 ^ m := by
  classical
  have hq1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
  have h1 : Nat.card ↥(frobFixed D m) = Nat.card {y : D // y ^ 2 ^ m = y} := rfl
  rw [h1, card_pow_fixed (2 ^ m) (by
    calc 2 = 2 ^ 1 := (pow_one 2).symm
    _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm)]
  -- units with `u^{2^m − 1} = 1` = kernel of the power map, size `gcd`
  have hker : Nat.card {u : Dˣ // u ^ (2 ^ m - 1) = 1}
      = Nat.card ↥((powMonoidHom (2 ^ m - 1) : Dˣ →* Dˣ).ker) := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun u => by
      rw [MonoidHom.mem_ker, powMonoidHom_apply])
  have hcardU : Nat.card Dˣ = 2 ^ (2 * m) - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_units, hcard]
  have hdvd : (2 ^ m - 1) ∣ (2 ^ (2 * m) - 1) := by
    refine ⟨2 ^ m + 1, ?_⟩
    have h2m : 2 ^ (2 * m) = (2 ^ m) ^ 2 := by
      rw [← pow_mul, mul_comm]
    have hsq := Nat.sq_sub_sq (2 ^ m) 1
    rw [h2m]
    simpa [mul_comm] using hsq
  rw [hker, IsCyclic.card_powMonoidHom_ker, hcardU, Nat.gcd_eq_right hdvd]
  omega


/-- **Trace representation of `𝔽₂`-functionals**: every additive functional `D →+ ZMod 2` is
`x ↦ Tr(w·x)` for some `w` (the trace pairing is perfect, by nondegeneracy + counting). -/
theorem exists_trace_rep {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    [Algebra (ZMod (ringChar D)) D] (e2 : ZMod (ringChar D) ≃+ ZMod 2) (f : D →+ ZMod 2) :
    ∃ w : D, ∀ x : D, f x = e2 (Algebra.trace (ZMod (ringChar D)) D (w * x)) := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  have h2D : ∀ a : D, a + a = 0 := fun a => CharTwo.add_self_eq_zero a
  haveI : Finite (D →+ ZMod 2) :=
    Finite.of_injective (fun f => (f : D → ZMod 2)) DFunLike.coe_injective
  haveI : Fintype (D →+ ZMod 2) := Fintype.ofFinite _
  set Φ : D → (D →+ ZMod 2) := fun w => AddMonoidHom.mk'
    (fun x => e2 (Algebra.trace (ZMod (ringChar D)) D (w * x)))
    (fun x x' => by rw [mul_add, map_add, map_add]) with hΦ
  have hinj : Function.Injective Φ := by
    intro w₁ w₂ hw
    by_contra hne
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D (sub_ne_zero.mpr hne)
    apply hb
    have hpt := DFunLike.congr_fun hw b
    have hpt' : e2 (Algebra.trace (ZMod (ringChar D)) D (w₁ * b))
        = e2 (Algebra.trace (ZMod (ringChar D)) D (w₂ * b)) := hpt
    have htr : Algebra.trace (ZMod (ringChar D)) D (w₁ * b)
        = Algebra.trace (ZMod (ringChar D)) D (w₂ * b) := e2.injective hpt'
    rw [sub_mul, map_sub, htr, sub_self]
  haveI : Fintype D := Fintype.ofFinite D
  have hbij : Function.Bijective Φ := by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨hinj, ?_⟩
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, card_addHom_zmod2 D h2D]
  obtain ⟨w, hw⟩ := hbij.2 f
  refine ⟨w, fun x => ?_⟩
  rw [← hw]
  rfl

/-- **Artin–Schreier surjectivity onto the fixed field**: every `y` with `y^{2^m} = y` is
`c + c^{2^m}` for some `c` (the map `c ↦ c + c^{2^m}` has kernel and image the fixed field). -/
theorem exists_add_pow_eq {m : ℕ} (hm : 1 ≤ m) (hcard : Fintype.card D = 2 ^ (2 * m))
    {y : D} (hy : y ^ 2 ^ m = y) : ∃ c : D, c + c ^ 2 ^ m = y := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : D →+ D := AddMonoidHom.mk' (fun c => c + c ^ 2 ^ m)
    (fun a b => by rw [add_pow_char_pow]; abel) with hφ
  -- kernel = fixed field
  have hker : φ.ker = frobFixed D m := by
    ext c
    rw [AddMonoidHom.mem_ker, mem_frobFixed]
    show c + c ^ 2 ^ m = 0 ↔ c ^ 2 ^ m = c
    constructor
    · intro h
      have h1 : -(c ^ 2 ^ m) = c := neg_eq_of_add_eq_zero_left h
      rwa [CharTwo.neg_eq] at h1
    · intro h
      rw [h]
      exact CharTwo.add_self_eq_zero c
  -- range ⊆ fixed field
  have hrangele : φ.range ≤ frobFixed D m := by
    rintro _ ⟨c, rfl⟩
    rw [mem_frobFixed]
    show (c + c ^ 2 ^ m) ^ 2 ^ m = c + c ^ 2 ^ m
    have hcc : (c ^ 2 ^ m) ^ 2 ^ m = c := by
      rw [← pow_mul, show (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) from by rw [two_mul, pow_add],
        ← hcard]
      exact FiniteField.pow_card c
    rw [add_pow_char_pow, hcc, add_comm]
  -- equal cardinalities force equality
  have hrn : Nat.card ↥φ.range * Nat.card ↥φ.ker = Nat.card D := by
    rw [← Nat.card_congr (QuotientAddGroup.quotientKerEquivRange φ).toEquiv]
    exact (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup φ.ker).symm
  have hkercard : Nat.card ↥φ.ker = 2 ^ m := by rw [hker]; exact card_frobFixed hm hcard
  have hrangecard : Nat.card ↥φ.range = 2 ^ m := by
    have hD : Nat.card D = 2 ^ m * 2 ^ m := by
      rw [Nat.card_eq_fintype_card, hcard, two_mul, pow_add]
    rw [hkercard, hD] at hrn
    have hpos : 0 < 2 ^ m := Nat.pos_of_neZero _
    exact Nat.eq_of_mul_eq_mul_right hpos hrn
  have heq : (φ.range : Set D) = (frobFixed D m : Set D) := by
    refine Set.eq_of_subset_of_ncard_le (fun x hx => hrangele hx) ?_ (Set.toFinite _)
    rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    show Nat.card ↥(frobFixed D m) ≤ Nat.card ↥φ.range
    rw [card_frobFixed hm hcard, hrangecard]
  have : y ∈ (φ.range : Set D) := heq ▸ hy
  obtain ⟨c, hc⟩ := this
  exact ⟨c, hc⟩

/-- `2^s − 1 ∣ 2^t − 1` forces `s ∣ t` (Euclidean division on the exponents). -/
theorem dvd_of_two_pow_sub_one_dvd {s t : ℕ} (hs : 1 ≤ s)
    (h : (2 ^ s - 1) ∣ (2 ^ t - 1)) : s ∣ t := by
  by_contra hnd
  have hr0 : t % s ≠ 0 := fun h0 => hnd (Nat.dvd_of_mod_eq_zero h0)
  have hrlt : t % s < s := Nat.mod_lt _ (by omega)
  -- decompose `2^t − 1`
  have ht : s * (t / s) + t % s = t := Nat.div_add_mod t s
  have hdvd1 : (2 ^ s - 1) ∣ (2 ^ (s * (t / s)) - 1) := by
    have := Nat.sub_dvd_pow_sub_pow (2 ^ s) 1 (t / s)
    rwa [one_pow, ← pow_mul] at this
  have hdecomp : 2 ^ t - 1
      = 2 ^ (t % s) * (2 ^ (s * (t / s)) - 1) + (2 ^ (t % s) - 1) := by
    have hprod : 2 ^ t = 2 ^ (s * (t / s)) * 2 ^ (t % s) := by
      rw [← pow_add, ht]
    have hA : 1 ≤ 2 ^ (s * (t / s)) := Nat.one_le_two_pow
    have hB : 1 ≤ 2 ^ (t % s) := Nat.one_le_two_pow
    generalize hA' : 2 ^ (s * (t / s)) = A at *
    generalize hB' : 2 ^ (t % s) = B at *
    generalize hC' : 2 ^ t = C at *
    have hmul : B * (A - 1) = B * A - B := by
      rw [Nat.mul_sub, mul_one]
    have hBA : B * A = C := by rw [hprod]; ring
    have hCB : B ≤ C := by
      rw [hprod]
      exact Nat.le_mul_of_pos_left _ (by omega)
    rw [hmul, hBA]
    omega
  have hdvd2 : (2 ^ s - 1) ∣ (2 ^ (t % s) - 1) := by
    have hX : (2 ^ s - 1) ∣ 2 ^ (t % s) * (2 ^ (s * (t / s)) - 1) :=
      hdvd1.mul_left _
    have := Nat.dvd_sub h hX
    rwa [hdecomp, Nat.add_sub_cancel_left] at this
  have hlt : 2 ^ (t % s) - 1 < 2 ^ s - 1 := by
    have h1 := Nat.pow_lt_pow_right (a := 2) one_lt_two hrlt
    have h2 : 1 ≤ 2 ^ (t % s) := Nat.one_le_two_pow
    omega
  have hpos : 0 < 2 ^ (t % s) - 1 := by
    have h2r : 2 ≤ 2 ^ (t % s) := by
      calc 2 = 2 ^ 1 := (pow_one 2).symm
      _ ≤ 2 ^ (t % s) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact absurd (Nat.le_of_dvd hpos hdvd2) (Nat.not_le.mpr hlt)

/-- **A subring containing the norm-one circle is everything**: a subring of `D = 𝔽_{2^{2m}}`
containing all `2^m+1` norm-one units has 2-power order `> 2^m` whose predecessor divides
`2^{2m}−1` (Lagrange on its unit group), forcing order `2^{2m}`. -/
theorem subring_eq_top_of_normOne_le {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) (S : Subring D)
    (hU : ∀ u : Dˣ, u ^ (2 ^ m + 1) = 1 → (↑u : D) ∈ S) : S = ⊤ := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  have h2S : ∀ x : ↥S, x + x = 0 := fun x => Subtype.ext (CharTwo.add_self_eq_zero _)
  obtain ⟨s, hs⟩ := card_eq_two_pow_of_exp_two h2S
  -- the `2^m+2` elements `{0} ∪ U` inject into `S`
  have hUcount : Nat.card {u : Dˣ // u ^ (2 ^ m + 1) = 1} = 2 ^ m + 1 := by
    have he : Nat.card {u : Dˣ // u ^ (2 ^ m + 1) = 1}
        = Nat.card ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) :=
      Nat.card_congr (Equiv.subtypeEquivRight fun u => by
        rw [MonoidHom.mem_ker, powMonoidHom_apply])
    have hdvd : (2 ^ m + 1) ∣ (2 ^ (2 * m) - 1) := by
      refine ⟨2 ^ m - 1, ?_⟩
      have hsub := Nat.sq_sub_sq (2 ^ m) 1
      rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 from by rw [← pow_mul, mul_comm]]
      simpa using hsub
    rw [he, IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard, Nat.gcd_eq_right hdvd]
  have hinj : Function.Injective
      (fun o : Option {u : Dˣ // u ^ (2 ^ m + 1) = 1} =>
        (o.elim (⟨0, S.zero_mem⟩ : ↥S) (fun u => ⟨↑u.1, hU u.1 u.2⟩) : ↥S)) := by
    intro o₁ o₂ ho
    match o₁, o₂ with
    | none, none => rfl
    | none, some u =>
      exact absurd (congrArg Subtype.val ho).symm u.1.ne_zero
    | some u, none =>
      exact absurd (congrArg Subtype.val ho) u.1.ne_zero
    | some u, some v =>
      have : (↑u.1 : D) = ↑v.1 := congrArg Subtype.val ho
      rw [Option.some.injEq]
      exact Subtype.ext (Units.ext this)
  have hle : 2 ^ m + 2 ≤ 2 ^ s := by
    have hcardO := Nat.card_le_card_of_injective _ hinj
    haveI : Fintype {u : Dˣ // u ^ (2 ^ m + 1) = 1} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
      ← Nat.card_eq_fintype_card, hUcount, hs] at hcardO
    omega
  -- the unit group of `S`, Lagrange
  set T : Subgroup Dˣ :=
    { carrier := {u : Dˣ | (↑u : D) ∈ S}
      one_mem' := by
        show ((1 : Dˣ) : D) ∈ S
        rw [Units.val_one]
        exact S.one_mem
      mul_mem' := fun {a b} ha hb => by
        show ((a * b : Dˣ) : D) ∈ S
        rw [Units.val_mul]
        exact S.mul_mem ha hb
      inv_mem' := fun {u} hu => by
        show ((u⁻¹ : Dˣ) : D) ∈ S
        have hord : 0 < orderOf u := orderOf_pos u
        have h1 : u * u ^ (orderOf u - 1) = 1 := by
          rw [← pow_succ', show orderOf u - 1 + 1 = orderOf u from by omega,
            pow_orderOf_eq_one]
        rw [inv_eq_of_mul_eq_one_right h1, Units.val_pow_eq_pow_val]
        exact pow_mem hu _ } with hT
  have hTcard : Nat.card ↥T + 1 = 2 ^ s := by
    rw [← hs]
    have e : Option ↥T ≃ ↥S :=
      { toFun := fun o => o.elim ⟨0, S.zero_mem⟩ (fun u => ⟨↑u.1, u.2⟩)
        invFun := fun x => if hx : (x : D) = 0 then none
          else some ⟨Units.mk0 (x : D) hx, by
            show ((Units.mk0 (x : D) hx : Dˣ) : D) ∈ S
            rw [Units.val_mk0]
            exact x.2⟩
        left_inv := fun o => by
          match o with
          | none => simp
          | some u =>
            have hne : ((⟨↑u.1, u.2⟩ : ↥S) : D) ≠ 0 := u.1.ne_zero
            simp only [Option.elim_some]
            rw [dif_neg hne]
            congr 1
            exact Subtype.ext (Units.ext rfl)
        right_inv := fun x => by
          dsimp only
          by_cases hx : (x : D) = 0
          · rw [dif_pos hx]
            exact Subtype.ext hx.symm
          · rw [dif_neg hx]
            exact Subtype.ext rfl }
    haveI : Fintype ↥T := Fintype.ofFinite _
    rw [← Nat.card_congr e, Nat.card_eq_fintype_card (α := Option _), Fintype.card_option,
      ← Nat.card_eq_fintype_card]
  have hTdvd : Nat.card ↥T ∣ 2 ^ (2 * m) - 1 := by
    have := Subgroup.card_subgroup_dvd_card T
    rwa [Nat.card_eq_fintype_card (α := Dˣ), Fintype.card_units, hcard] at this
  -- pinch: `s ∣ 2m` and `s > m` force `s = 2m`
  have hs1 : 1 ≤ s := by
    by_contra hs0
    have hz : s = 0 := by omega
    rw [hz, pow_zero] at hle
    have := Nat.one_le_two_pow (n := m)
    omega
  have hsdvd : s ∣ 2 * m := by
    apply dvd_of_two_pow_sub_one_dvd hs1
    have : Nat.card ↥T = 2 ^ s - 1 := by omega
    rwa [← this]
  have hsm : m < s := by
    have h1 : 2 ^ m < 2 ^ s := by omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp h1
  have hs2m : s = 2 * m := by
    obtain ⟨k, hk⟩ := hsdvd
    match k with
    | 0 => omega
    | 1 => omega
    | (k + 2) =>
      have hexp : s * (k + 2) = s * k + 2 * s := by ring
      omega
  -- cardinality forces `S = ⊤`
  have hScard : Nat.card ↥S = Nat.card D := by
    rw [hs, hs2m, Nat.card_eq_fintype_card, hcard]
  have hcoe : (S : Set D) = Set.univ := by
    refine Set.eq_of_subset_of_ncard_le (Set.subset_univ _) ?_ (Set.toFinite _)
    rw [Set.ncard_univ, ← Nat.card_coe_set_eq]
    exact le_of_eq hScard.symm
  exact SetLike.ext' (by rw [hcoe]; rfl)

/-- Fibres of a group hom over range points have the size of the kernel. -/
theorem card_filter_eq_of_mem_range {G H : Type*} [Group G] [Fintype G] [DecidableEq G]
    [Group H] [DecidableEq H] (f : G →* H) {y : H} (hy : y ∈ f.range) :
    (Finset.univ.filter (fun u : G => f u = y)).card
      = (Finset.univ.filter (fun u : G => u ∈ f.ker)).card := by
  obtain ⟨u₀, rfl⟩ := hy
  refine Finset.card_bij (fun v _ => u₀⁻¹ * v) ?_ ?_ ?_
  · intro v hv
    rw [Finset.mem_filter] at hv ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [MonoidHom.mem_ker, map_mul, map_inv, hv.2, inv_mul_cancel]
  · intro v _ w _ hvw
    exact mul_left_cancel hvw
  · intro k hk
    rw [Finset.mem_filter, MonoidHom.mem_ker] at hk
    refine ⟨u₀ * k, ?_, by group⟩
    rw [Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [map_mul, hk.2, mul_one]⟩


/-- **Lemma 6.7 (invariant quadratic forms on a Hermitian line), existence form**: every
nonsingular quadratic form on `D = 𝔽_{2^{2m}}` invariant under the norm-one circle
`U = {u : u^{2^m+1} = 1}` is the Hermitian trace form of some `c` outside the fixed field.
(The adjoint identity holds on a subring containing `U`, hence everywhere; the polar form is
then trace-represented with Frobenius-fixed coefficient, an Artin–Schreier preimage matches the
polars, and the additive `U`-invariant difference vanishes.) -/
theorem hermitian_form_eq_trace_form {m : ℕ} (hm : 1 ≤ m)
    (hcard : Fintype.card D = 2 ^ (2 * m)) [Algebra (ZMod (ringChar D)) D]
    (e2 : ZMod (ringChar D) ≃+ ZMod 2)
    (Q : D → ZMod 2) (hQ : IsQuadraticFp2 Q) (hns : Nonsingular Q)
    (hU : ∀ u : Dˣ, u ^ (2 ^ m + 1) = 1 → ∀ x : D, Q (↑u * x) = Q x) :
    ∃ c : D, c ^ 2 ^ m ≠ c ∧
      ∀ x : D, Q x = e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1))) := by
  classical
  have hchar : ringChar D = 2 := ringChar_eq_two_of_card hm hcard
  haveI : CharP D 2 := hchar ▸ ringChar.charP D
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (ZMod (ringChar D)) 2 := hchar ▸ ZMod.charP (ringChar D)
  have hyq2 : ∀ y : D, (y ^ 2 ^ m) ^ 2 ^ m = y := fun y => by
    rw [← pow_mul, show (2 : ℕ) ^ m * 2 ^ m = 2 ^ (2 * m) from by rw [two_mul, pow_add],
      ← hcard]
    exact FiniteField.pow_card y
  have hpz_left : ∀ y : D, polar Q 0 y = 0 := fun y => by
    unfold GQ2.QuadraticFp2.polar
    rw [zero_add, hQ.map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  have hpz_right : ∀ x : D, polar Q x 0 = 0 := fun x => by
    unfold GQ2.QuadraticFp2.polar
    rw [add_zero, hQ.map_zero, add_zero]
    exact CharTwo.add_self_eq_zero _
  -- the polar form is `U`-invariant
  have hUB : ∀ (u : Dˣ), u ^ (2 ^ m + 1) = 1 → ∀ x y : D,
      polar Q (↑u * x) (↑u * y) = polar Q x y := by
    intro u hu x y
    unfold GQ2.QuadraticFp2.polar
    rw [← mul_add, hU u hu, hU u hu, hU u hu]
  -- the adjoint identity holds on a subring containing `U`, hence everywhere
  set S : Subring D :=
    { carrier := {d : D | ∀ x y : D, polar Q (d * x) y = polar Q x (d ^ 2 ^ m * y)}
      zero_mem' := fun x y => by
        rw [zero_mul, zero_pow (Nat.pos_of_neZero _).ne', zero_mul, hpz_left, hpz_right]
      one_mem' := fun x y => by rw [one_mul, one_pow, one_mul]
      add_mem' := fun {a b} ha hb x y => by
        rw [add_mul, hQ.polar_add_left, ha, hb, add_pow_char_pow, add_mul,
          ← hQ.polar_add_right]
      mul_mem' := fun {a b} ha hb x y => by
        rw [show a * b * x = a * (b * x) from by ring, ha, hb,
          show b ^ 2 ^ m * (a ^ 2 ^ m * y) = (a * b) ^ 2 ^ m * y from by
            rw [mul_pow]; ring]
      neg_mem' := fun {a} ha => by
        intro x y
        rw [CharTwo.neg_eq]
        exact ha x y } with hS
  have hStop : S = ⊤ := by
    apply subring_eq_top_of_normOne_le hm hcard
    intro u hu
    intro x y
    have hval : (↑u : D) * ((↑u : D) ^ 2 ^ m * y) = y := by
      rw [← mul_assoc, ← pow_succ', ← Units.val_pow_eq_pow_val, hu, Units.val_one, one_mul]
    calc polar Q (↑u * x) y
        = polar Q (↑u * x) (↑u * ((↑u : D) ^ 2 ^ m * y)) := by rw [hval]
      _ = polar Q x ((↑u : D) ^ 2 ^ m * y) := hUB u hu x _
  have hadj : ∀ d x y : D, polar Q (d * x) y = polar Q x (d ^ 2 ^ m * y) := by
    intro d x y
    have hd : d ∈ S := hStop ▸ Subring.mem_top d
    exact hd x y
  -- represent the polar form through the trace
  set ℓ : D →+ ZMod 2 := AddMonoidHom.mk' (fun y => polar Q 1 y)
    (fun y y' => hQ.polar_add_right 1 y y') with hℓ
  obtain ⟨c₀, hc₀⟩ := exists_trace_rep hm hcard e2 ℓ
  have hBrep : ∀ x y : D, polar Q x y
      = e2 (Algebra.trace (ZMod (ringChar D)) D (c₀ * (x ^ 2 ^ m * y))) := by
    intro x y
    have h1 : polar Q (x * 1) y = polar Q 1 (x ^ 2 ^ m * y) := hadj x 1 y
    rw [mul_one] at h1
    rw [h1]
    exact hc₀ _
  -- the coefficient is Frobenius-fixed (symmetry of the polar form)
  have hc₀fix : c₀ ^ 2 ^ m = c₀ := by
    have hsymTr : ∀ y : D, Algebra.trace (ZMod (ringChar D)) D (c₀ * y)
        = Algebra.trace (ZMod (ringChar D)) D (c₀ ^ 2 ^ m * y) := by
      intro y
      have h1 : polar Q 1 y = polar Q y 1 := polar_comm Q 1 y
      have h2 := hBrep 1 y
      have h3 := hBrep y 1
      rw [one_pow, one_mul] at h2
      rw [mul_one] at h3
      have h4 : Algebra.trace (ZMod (ringChar D)) D (c₀ * y ^ 2 ^ m)
          = Algebra.trace (ZMod (ringChar D)) D (c₀ ^ 2 ^ m * y) := by
        have h5 := trace_pow_pow hm hcard m (c₀ * y ^ 2 ^ m)
        rw [mul_pow, hyq2 y] at h5
        exact h5.symm
      have h6 : Algebra.trace (ZMod (ringChar D)) D (c₀ * y)
          = Algebra.trace (ZMod (ringChar D)) D (c₀ * y ^ 2 ^ m) :=
        e2.injective (h2.symm.trans (h1.trans h3))
      rw [h6, h4]
    by_contra hne
    have hsumne : c₀ + c₀ ^ 2 ^ m ≠ 0 := by
      intro h0
      apply hne
      have h1 : -(c₀ ^ 2 ^ m) = c₀ := neg_eq_of_add_eq_zero_left h0
      rwa [CharTwo.neg_eq] at h1
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D hsumne
    apply hb
    rw [add_mul, map_add, hsymTr b]
    exact CharTwo.add_self_eq_zero _
  obtain ⟨c, hc⟩ := exists_add_pow_eq hm hcard hc₀fix
  set Qc : D → ZMod 2 :=
    fun x => e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1))) with hQcdef
  -- the trace form has the same polar form
  have hQc_polar : ∀ x y : D, polar Qc x y = polar Q x y := by
    intro x y
    rw [hBrep x y]
    show e2 (Algebra.trace (ZMod (ringChar D)) D (c * (x + y) ^ (2 ^ m + 1)))
        + e2 (Algebra.trace (ZMod (ringChar D)) D (c * x ^ (2 ^ m + 1)))
        + e2 (Algebra.trace (ZMod (ringChar D)) D (c * y ^ (2 ^ m + 1)))
        = e2 (Algebra.trace (ZMod (ringChar D)) D (c₀ * (x ^ 2 ^ m * y)))
    rw [← map_add, ← map_add, ← map_add, ← map_add]
    congr 1
    have hexp : c * (x + y) ^ (2 ^ m + 1) + c * x ^ (2 ^ m + 1) + c * y ^ (2 ^ m + 1)
        = c * (x ^ 2 ^ m * y) + c * (x * y ^ 2 ^ m) := by
      have hfr : (x + y) ^ 2 ^ m = x ^ 2 ^ m + y ^ 2 ^ m := add_pow_char_pow x y 2 m
      rw [pow_succ, hfr]
      linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero]))
    rw [hexp, map_add]
    have hswap : Algebra.trace (ZMod (ringChar D)) D (c * (x * y ^ 2 ^ m))
        = Algebra.trace (ZMod (ringChar D)) D (c ^ 2 ^ m * (x ^ 2 ^ m * y)) := by
      have h5 := trace_pow_pow hm hcard m (c * (x * y ^ 2 ^ m))
      rw [mul_pow, mul_pow, hyq2 y] at h5
      exact h5.symm
    rw [hswap, ← map_add, show c * (x ^ 2 ^ m * y) + c ^ 2 ^ m * (x ^ 2 ^ m * y)
        = (c + c ^ 2 ^ m) * (x ^ 2 ^ m * y) from by ring, hc]
  -- the difference is an additive `U`-invariant functional, hence zero
  have hRadd : ∀ x y : D, Q (x + y) + Qc (x + y) = (Q x + Qc x) + (Q y + Qc y) := by
    intro x y
    have h1 : polar Q x y = polar Qc x y := (hQc_polar x y).symm
    unfold GQ2.QuadraticFp2.polar at h1
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) h1
  set R : D →+ ZMod 2 := AddMonoidHom.mk' (fun x => Q x + Qc x) hRadd with hR
  have hQcU : ∀ (u : Dˣ), u ^ (2 ^ m + 1) = 1 → ∀ x : D, Qc (↑u * x) = Qc x := by
    intro u hu x
    show e2 (Algebra.trace (ZMod (ringChar D)) D (c * (↑u * x) ^ (2 ^ m + 1))) = _
    rw [mul_pow, ← Units.val_pow_eq_pow_val, hu, Units.val_one, one_mul]
  obtain ⟨w, hw⟩ := exists_trace_rep hm hcard e2 R
  have hkercard : Nat.card ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) = 2 ^ m + 1 := by
    have hdvd : (2 ^ m + 1) ∣ (2 ^ (2 * m) - 1) := by
      refine ⟨2 ^ m - 1, ?_⟩
      have hsub := Nat.sq_sub_sq (2 ^ m) 1
      rw [show (2 : ℕ) ^ (2 * m) = (2 ^ m) ^ 2 from by rw [← pow_mul, mul_comm]]
      simpa using hsub
    rw [IsCyclic.card_powMonoidHom_ker, Nat.card_eq_fintype_card, Fintype.card_units,
      hcard, Nat.gcd_eq_right hdvd]
  have hkerne : Nontrivial ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker) := by
    rw [← Finite.one_lt_card_iff_nontrivial, hkercard]
    have := Nat.one_le_two_pow (n := m)
    omega
  obtain ⟨u₀, hu₀ne⟩ := exists_ne (1 : ↥((powMonoidHom (2 ^ m + 1) : Dˣ →* Dˣ).ker))
  have hu₀pow : (u₀ : Dˣ) ^ (2 ^ m + 1) = 1 := by
    have := u₀.2
    rwa [MonoidHom.mem_ker, powMonoidHom_apply] at this
  have hu₀ne1 : (u₀ : Dˣ) ≠ 1 := by
    intro h
    exact hu₀ne (Subtype.ext h)
  have hw0 : w = 0 := by
    by_contra hwne
    have huvne : ((u₀ : Dˣ) : D) + 1 ≠ 0 := by
      intro h0
      apply hu₀ne1
      apply Units.ext
      have h1 : -(1 : D) = ((u₀ : Dˣ) : D) := neg_eq_of_add_eq_zero_left h0
      rw [Units.val_one, ← h1, CharTwo.neg_eq]
    obtain ⟨b, hb⟩ := FiniteField.trace_to_zmod_nondegenerate D
      (mul_ne_zero hwne huvne)
    apply hb
    have h1 : R ((↑(u₀ : Dˣ) : D) * b) = R b := by
      show Q _ + Qc _ = Q b + Qc b
      rw [hU (u₀ : Dˣ) hu₀pow, hQcU (u₀ : Dˣ) hu₀pow]
    rw [hw, hw] at h1
    have h2 : Algebra.trace (ZMod (ringChar D)) D (w * ((↑(u₀ : Dˣ) : D) * b))
        = Algebra.trace (ZMod (ringChar D)) D (w * b) := e2.injective h1
    rw [show w * ((↑(u₀ : Dˣ) : D) + 1) * b
        = w * ((↑(u₀ : Dˣ) : D) * b) + w * b from by ring, map_add, h2]
    exact CharTwo.add_self_eq_zero _
  have hQeq : ∀ x : D, Q x = Qc x := by
    intro x
    have h0 : R x = 0 := by
      have := hw x
      rwa [hw0, zero_mul, map_zero, map_zero] at this
    have h1 : Q x + Qc x = 0 := h0
    have h2 : -(Qc x) = Q x := neg_eq_of_add_eq_zero_left h1
    rw [CharTwo.neg_eq] at h2
    exact h2.symm
  have hcne : c ^ 2 ^ m ≠ c := by
    intro hfix
    have hc₀0 : c₀ = 0 := by
      rw [← hc, hfix]
      exact CharTwo.add_self_eq_zero c
    haveI : Nontrivial D := by
      rw [← Fintype.one_lt_card_iff_nontrivial, hcard]
      have := Nat.one_le_two_pow (n := 2 * m)
      have h4 : (2 : ℕ) ^ 1 ≤ 2 ^ (2 * m) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    obtain ⟨v, hv⟩ := exists_ne (0 : D)
    obtain ⟨y, hy⟩ := hns v hv
    apply hy
    rw [show polar Q v y = e2 (Algebra.trace (ZMod (ringChar D)) D
        (c₀ * (v ^ 2 ^ m * y))) from hBrep v y, hc₀0, zero_mul, map_zero, map_zero]
  exact ⟨c, hcne, hQeq⟩


end HermitianCount

end GQ2.DeepPart

/-! ### Paper-tag ledger (auto-generated by paperforge; do not edit)

  * eq. (115) = ⟦eq-localzeros⟧
  * eq. (93) = ⟦eq-squareclassgraded⟧
  * Lemma 6.17 = ⟦lem-shapirodet⟧
  * Lemma 6.4 = ⟦lem-detnormalizationindependence⟧
  * Lemma 6.7 = ⟦lem-unitaryline⟧
  * Prop 6.18 = ⟦prop-localzero⟧
-/
