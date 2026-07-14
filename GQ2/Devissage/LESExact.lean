import GQ2.Devissage.LESCore

/-!
# §5.11 dévissage: exactness of the nine-term LES

Part of the §5.11 dévissage development (split from `GQ2/Devissage.lean`).
-/

namespace GQ2.FoxH

open scoped Pointwise

variable {C : Type*} [Group C]

section LES

variable {A' A A'' : Type*}
  [AddCommGroup A'] [DistribMulAction C A'] [Finite A']
  [AddCommGroup A] [DistribMulAction C A] [Finite A]
  [AddCommGroup A''] [DistribMulAction C A''] [Finite A''] [Finite C]
  (f : A' →+ A) (g : A →+ A'')
  (hf : ∀ (c : C) (a : A'), f (c • a) = c • f a) (hg : ∀ (c : C) (a : A), g (c • a) = c • g a)
  (hinj : Function.Injective f) (hsurj : Function.Surjective g) (hexact : f.range = g.ker)

/-! ### Exactness of the nine-term LES

Each spot is stated as `y ∈ ker(out) ↔ y ∈ range(in)` (equivalently at the ends, injectivity /
surjectivity), the usual snake-lemma bookkeeping. -/

include hsurj in
/-- Exactness at the right end: `H²wMap g` is surjective. -/
theorem H2wMap_g_surjective (t : Marking C) : Function.Surjective (H2wMap t g hg) := by
  intro y
  obtain ⟨p'', rfl⟩ := QuotientAddGroup.mk_surjective y
  obtain ⟨p, hp⟩ := prod_g_surjective g hsurj p''
  exact ⟨QuotientAddGroup.mk p, by
    rw [show H2wMap t g hg (QuotientAddGroup.mk p)
      = QuotientAddGroup.mk (g.prodMap g p) from rfl, hp]⟩

include hg hsurj hexact in
/-- Exactness at `H²w(A)`: `ker(H²wMap g) = range(H²wMap f)`. -/
theorem H2w_exact_mid (t : Marking C) (y : H2w (A := A) t) :
    y ∈ (H2wMap t g hg).ker ↔ y ∈ (H2wMap t f hf).range := by
  obtain ⟨p, rfl⟩ := QuotientAddGroup.mk_surjective y
  constructor
  · intro hy
    have hmem : (g.prodMap g) p ∈ (d1 (A := A'') t).range :=
      (QuotientAddGroup.eq_zero_iff _).mp (AddMonoidHom.mem_ker.mp hy)
    obtain ⟨x'', hx''⟩ := AddMonoidHom.mem_range.mp hmem   -- d¹ x'' = g×g p
    obtain ⟨x, hx⟩ := pi_g_surjective g hsurj x''          -- g∘x = x''
    have H : d1 t (fun i => g (x i)) = (g.prodMap g) (d1 t x) := by
      rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg x
    have hd1 : (g.prodMap g) (d1 t x) = d1 t x'' := by rw [← H]; exact congrArg (d1 t) hx
    have hker : (g.prodMap g) (p - d1 t x) = 0 := by rw [map_sub, hd1, hx'', sub_self]
    obtain ⟨q, hq⟩ := (prod_exact f g hexact (p - d1 t x)).mp hker  -- f×f q = p − d¹ x
    refine ⟨QuotientAddGroup.mk q, ?_⟩
    show (QuotientAddGroup.mk (f.prodMap f q) : H2w (A := A) t) = QuotientAddGroup.mk p
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff, hq,
      show (p - d1 t x) - p = -(d1 t x) from by abel]
    exact (AddSubgroup.neg_mem_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨x, rfl⟩)
  · rintro ⟨z, hz⟩
    obtain ⟨q, rfl⟩ := QuotientAddGroup.mk_surjective z
    have hgf : (g.prodMap g) (f.prodMap f q) = 0 := by
      rw [AddMonoidHom.coe_prodMap, AddMonoidHom.coe_prodMap]
      have hz0 : ∀ a', g (f a') = 0 := fun a' =>
        AddMonoidHom.mem_ker.mp (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨a', rfl⟩)
      show (g (f q.1), g (f q.2)) = 0
      rw [hz0, hz0]; rfl
    rw [AddMonoidHom.mem_ker, ← hz]
    show (QuotientAddGroup.mk (g.prodMap g (f.prodMap f q)) : H2w (A := A'') t) = 0
    rw [hgf]; exact QuotientAddGroup.mk_zero _


omit [Finite A'] [Finite A] [Finite A''] [Finite C] in
include hf hinj hexact in
/-- Exactness at `H⁰w(A)`: `ker(H⁰wMap g) = range(H⁰wMap f)`. -/
theorem H0w_exact_mid (t : Marking C) (a : H0w (A := A) t) :
    a ∈ (H0wMap t g hg).ker ↔ a ∈ (H0wMap t f hf).range := by
  constructor
  · intro ha
    have h1 : g a.1 = 0 := congrArg Subtype.val (AddMonoidHom.mem_ker.mp ha)
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.mp (hexact ▸ AddMonoidHom.mem_ker.mpr h1)
    have hd0 : d0 t a' = 0 := by
      funext i
      show d0 t a' i = 0
      apply hinj
      have h2 : d0 t (f a') i = f (d0 t a' i) := congrFun (d0_natural t f hf a') i
      have h3 : d0 t a.1 i = 0 := congrFun (AddMonoidHom.mem_ker.mp a.2) i
      rw [map_zero, ← h2, ha']
      exact h3
    exact ⟨⟨a', AddMonoidHom.mem_ker.mpr hd0⟩, Subtype.ext ha'⟩
  · rintro ⟨a', rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    apply Subtype.ext
    show g (f a'.1) = 0
    exact AddMonoidHom.mem_ker.mp (hexact ▸ AddMonoidHom.mem_range.mpr ⟨a'.1, rfl⟩)

include hf hg hinj hsurj hexact in
omit [Finite A''] in
/-- Exactness at `H⁰w(A'')`: `ker δ⁰ = range(H⁰wMap g)`. -/
theorem H0w_exact_right (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (a'' : H0w (A := A'') t) :
    a'' ∈ (delta0 f g hf hg hinj hsurj hexact t ht hw).ker ↔ a'' ∈ (H0wMap t g hg).range := by
  constructor
  · intro h0
    have h0' : (QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t a'',
        AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩ :
        H1w (A := A') t) = 0 := AddMonoidHom.mem_ker.mp h0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h0'
    obtain ⟨a', ha'⟩ := AddMonoidHom.mem_range.mp h0'
    have ha'' : d0 t a' = snake0Z' f g hg hsurj hexact t a'' := ha'
    refine ⟨⟨(hsurj a''.1).choose - f a', AddMonoidHom.mem_ker.mpr ?_⟩, Subtype.ext ?_⟩
    · funext i
      show d0 t ((hsurj a''.1).choose - f a') i = 0
      have h2 : d0 t (f a') i = f (d0 t a' i) := congrFun (d0_natural t f hf a') i
      have h4 : f (snake0Z' f g hg hsurj hexact t a'' i)
          = d0 t (hsurj a''.1).choose i := congrFun (snake0Z'_spec f g hg hsurj hexact t a'') i
      have h5 : d0 t a' i = snake0Z' f g hg hsurj hexact t a'' i := congrFun ha'' i
      rw [map_sub, Pi.sub_apply, h2, h5, h4, sub_self]
    · show g ((hsurj a''.1).choose - f a') = a''.1
      rw [map_sub, (hsurj a''.1).choose_spec,
        show g (f a') = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨a', rfl⟩), sub_zero]
  · rintro ⟨a, rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    have hwd := delta0_welldef f g hf hg hinj hsurj hexact t ht hw (H0wMap t g hg a) a.1 0
      (map_zero _) rfl
      (by funext i
          simp only [Pi.zero_apply, map_zero]
          exact (congrFun (AddMonoidHom.mem_ker.mp a.2) i).symm)
    show (QuotientAddGroup.mk ⟨snake0Z' f g hg hsurj hexact t (H0wMap t g hg a),
      AddMonoidHom.mem_ker.mpr
        (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw (H0wMap t g hg a))⟩ :
      H1w (A := A') t) = 0
    exact hwd.symm.trans (QuotientAddGroup.mk_zero _)

include hf hg hinj hsurj hexact in
omit [Finite A''] in
/-- Exactness at `H¹w(A')`: `ker(H¹wMap f) = range δ⁰`. -/
theorem H1w_exact_left (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H1w (A := A') t) :
    h ∈ (H1wMap t f hf).ker ↔ h ∈ (delta0 f g hf hg hinj hsurj hexact t ht hw).range := by
  constructor
  · intro hker
    obtain ⟨w', rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (Z1wMap t f hf w') : H1w (A := A) t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨a, ha⟩ := AddMonoidHom.mem_range.mp h1
    have ha' : d0 t a = fun i => f (w'.1 i) := ha
    -- `g a` is an `H⁰w(A'')`-element hitting `[w']` under `δ⁰`.
    have hga : d0 t (g a) = 0 := by
      funext i
      show d0 t (g a) i = 0
      have h2 : d0 t (g a) i = g (d0 t a i) := congrFun (d0_natural t g hg a) i
      have h3 : d0 t a i = f (w'.1 i) := congrFun ha' i
      rw [h2, h3]
      exact AddMonoidHom.mem_ker.mp (hexact ▸ AddMonoidHom.mem_range.mpr ⟨w'.1 i, rfl⟩)
    exact ⟨⟨g a, AddMonoidHom.mem_ker.mpr hga⟩,
      (delta0_welldef f g hf hg hinj hsurj hexact t ht hw ⟨g a, AddMonoidHom.mem_ker.mpr hga⟩
        a w'.1 (AddMonoidHom.mem_ker.mp w'.2) rfl ha'.symm).symm⟩
  · rintro ⟨a'', rfl⟩
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (Z1wMap t f hf ⟨snake0Z' f g hg hsurj hexact t a'',
      AddMonoidHom.mem_ker.mpr (snake0Z'_mem f g hf hg hinj hsurj hexact t ht hw a'')⟩) :
      H1w (A := A) t) = 0
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    exact AddMonoidHom.mem_range.mpr ⟨(hsurj a''.1).choose,
      (snake0Z'_spec f g hg hsurj hexact t a'').symm⟩

include hf hg hinj hsurj hexact in
/-- Exactness at `H¹w(A)`: `ker(H¹wMap g) = range(H¹wMap f)`. -/
theorem H1w_exact_mid (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (h : H1w (A := A) t) :
    h ∈ (H1wMap t g hg).ker ↔ h ∈ (H1wMap t f hf).range := by
  constructor
  · intro hker
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (Z1wMap t g hg x) : H1w (A := A'') t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    rw [QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf] at h1
    obtain ⟨a'', ha''⟩ := AddMonoidHom.mem_range.mp h1
    have ha : d0 t a'' = fun i => g (x.1 i) := ha''
    obtain ⟨a, rfl⟩ := hsurj a''
    -- `x − d⁰a` maps to `0` under `g`, hence is `f∘w'` for a cocycle `w'`.
    have hxa : (fun i => g ((x.1 - d0 t a) i)) = 0 := by
      funext i
      show g ((x.1 - d0 t a) i) = 0
      have h2 : d0 t (g a) i = g (d0 t a i) := congrFun (d0_natural t g hg a) i
      have h3 : d0 t (g a) i = g (x.1 i) := congrFun ha i
      rw [Pi.sub_apply, map_sub, ← h3, h2, sub_self]
    obtain ⟨w', hw'⟩ := (pi_exact f g hexact (x.1 - d0 t a)).mp hxa
    have hw'z : d1 t w' = 0 := by
      have hfinj : Function.Injective (f.prodMap f) := by
        rw [AddMonoidHom.coe_prodMap]; exact hinj.prodMap hinj
      apply hfinj
      have hnat : (f.prodMap f) (d1 t w') = d1 t (fun i => f (w' i)) := by
        rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w').symm
      rw [map_zero, hnat, hw', map_sub, AddMonoidHom.mem_ker.mp x.2,
        show d1 t (d0 t a) = 0 from d1Fun_comp_d0 t ht hw a, sub_zero]
    refine ⟨QuotientAddGroup.mk ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩, ?_⟩
    show (QuotientAddGroup.mk (Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩) :
      H1w (A := A) t) = QuotientAddGroup.mk x
    rw [← sub_eq_zero, ← QuotientAddGroup.mk_sub, QuotientAddGroup.eq_zero_iff,
      AddSubgroup.mem_addSubgroupOf]
    refine AddMonoidHom.mem_range.mpr ⟨-a, ?_⟩
    show d0 t (-a)
      = ((Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩ - x : Z1w (A := A) t) :
        Fin 4 → A)
    have hval : ((Z1wMap t f hf ⟨w', AddMonoidHom.mem_ker.mpr hw'z⟩ - x :
        Z1w (A := A) t) : Fin 4 → A) = (fun i => f (w' i)) - x.1 := rfl
    rw [hval, hw', map_neg]
    abel
  · rintro ⟨z, rfl⟩
    obtain ⟨w', rfl⟩ := QuotientAddGroup.mk_surjective z
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (Z1wMap t g hg (Z1wMap t f hf w')) : H1w (A := A'') t) = 0
    have hzero : Z1wMap t g hg (Z1wMap t f hf w') = 0 := by
      apply Subtype.ext
      funext i
      show g (f (w'.1 i)) = 0
      exact AddMonoidHom.mem_ker.mp (hexact ▸ AddMonoidHom.mem_range.mpr ⟨w'.1 i, rfl⟩)
    rw [hzero]
    exact QuotientAddGroup.mk_zero _

include hf hg hinj hsurj hexact in
/-- Exactness at `H¹w(A'')`: `ker δ¹ = range(H¹wMap g)`. -/
theorem H1w_exact_right (t : Marking C) (ht : t.TameRel) (hw : t.WildRel)
    (h : H1w (A := A'') t) :
    h ∈ (delta1 f g hf hg hinj hsurj hexact t ht hw).ker ↔ h ∈ (H1wMap t g hg).range := by
  constructor
  · intro hker
    obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective h
    have h1 : (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t c'') : H2w (A := A') t) = 0 :=
      AddMonoidHom.mem_ker.mp hker
    obtain ⟨w', hw'⟩ := AddMonoidHom.mem_range.mp ((QuotientAddGroup.eq_zero_iff _).mp h1)
    -- `x := (lift c'') − f∘w'` is a `Z¹w(A)`-cocycle mapping onto `c''`.
    have hd1x : d1 t (snakeLift g hsurj c''.1 - fun i => f (w' i)) = 0 := by
      have hnat : (f.prodMap f) (d1 t w') = d1 t (fun i => f (w' i)) := by
        rw [AddMonoidHom.coe_prodMap]; exact (d1_natural t f hf w').symm
      rw [map_sub, ← snakeZ_spec f g hg hsurj hexact t c'', ← hnat, hw', sub_self]
    refine ⟨QuotientAddGroup.mk ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
      AddMonoidHom.mem_ker.mpr hd1x⟩, ?_⟩
    show (QuotientAddGroup.mk (Z1wMap t g hg ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
      AddMonoidHom.mem_ker.mpr hd1x⟩) : H1w (A := A'') t) = QuotientAddGroup.mk c''
    have hval : Z1wMap t g hg ⟨snakeLift g hsurj c''.1 - fun i => f (w' i),
        AddMonoidHom.mem_ker.mpr hd1x⟩ = c'' := by
      apply Subtype.ext
      funext i
      show g ((snakeLift g hsurj c''.1 - fun i => f (w' i)) i) = c''.1 i
      rw [Pi.sub_apply, map_sub, snakeLift_spec g hsurj c''.1 i,
        show g (f (w' i)) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨w' i, rfl⟩), sub_zero]
    rw [hval]
  · rintro ⟨z, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk_surjective z
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t (Z1wMap t g hg x)) :
      H2w (A := A') t) = 0
    refine (snakeZ_welldef f g hf hg hinj hsurj hexact t (Z1wMap t g hg x) x.1 0 rfl ?_).symm.trans
      (QuotientAddGroup.mk_zero _)
    rw [map_zero]
    exact (AddMonoidHom.mem_ker.mp x.2).symm

include hf hg hinj hsurj hexact in
/-- Exactness at `H²w(A')`: `ker(H²wMap f) = range δ¹`. -/
theorem H2w_exact_left (t : Marking C) (ht : t.TameRel) (hw : t.WildRel) (y : H2w (A := A') t) :
    y ∈ (H2wMap t f hf).ker ↔ y ∈ (delta1 f g hf hg hinj hsurj hexact t ht hw).range := by
  constructor
  · intro hker
    obtain ⟨z, rfl⟩ := QuotientAddGroup.mk_surjective y
    have h1 : (f.prodMap f) z ∈ (d1 (A := A) t).range :=
      (QuotientAddGroup.eq_zero_iff _).mp (AddMonoidHom.mem_ker.mp hker)
    obtain ⟨x, hx⟩ := AddMonoidHom.mem_range.mp h1
    have hc'' : d1 t (fun i => g (x i)) = 0 := by
      have hnat : d1 t (fun i => g (x i)) = (g.prodMap g) (d1 t x) := by
        rw [AddMonoidHom.coe_prodMap]; exact d1_natural t g hg x
      rw [hnat, hx, AddMonoidHom.coe_prodMap, AddMonoidHom.coe_prodMap]
      show (g (f z.1), g (f z.2)) = 0
      rw [show g (f z.1) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨z.1, rfl⟩),
        show g (f z.2) = 0 from AddMonoidHom.mem_ker.mp
          (by rw [← hexact]; exact AddMonoidHom.mem_range.mpr ⟨z.2, rfl⟩)]
      rfl
    refine ⟨QuotientAddGroup.mk ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩, ?_⟩
    show (QuotientAddGroup.mk (snakeZ f g hg hsurj hexact t
      ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩) : H2w (A := A') t)
      = QuotientAddGroup.mk z
    exact (snakeZ_welldef f g hf hg hinj hsurj hexact t
      ⟨fun i => g (x i), AddMonoidHom.mem_ker.mpr hc''⟩ x z rfl hx.symm).symm
  · rintro ⟨hcls, rfl⟩
    obtain ⟨c'', rfl⟩ := QuotientAddGroup.mk_surjective hcls
    apply AddMonoidHom.mem_ker.mpr
    show (QuotientAddGroup.mk ((f.prodMap f) (snakeZ f g hg hsurj hexact t c'')) :
      H2w (A := A) t) = 0
    rw [snakeZ_spec f g hg hsurj hexact t c'']
    exact (QuotientAddGroup.eq_zero_iff _).mpr (AddMonoidHom.mem_range.mpr ⟨_, rfl⟩)


end LES

end GQ2.FoxH
