"""W61-WIDER step 9: splice the emitted soundness lemmas into the Lean file.

Reads `results/lean_soundness.txt` (generated, certified witnesses) and writes section 5 of
`GQ2/Dyadic/SqCore/GradedFiveGammaTwo.lean` between the markers.  Keeping this mechanical is
the point: a two-hundred-and-seventy-six-term witness must never be typed by hand.
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
LEAN = os.path.join(ROOT, "GQ2", "Dyadic", "SqCore", "GradedFiveGammaTwo.lean")

with open(os.path.join(HERE, "results", "lean_soundness.txt")) as fh:
    emitted = fh.read()

HEAD = r'''/-! ## 5 The quadratic block is even on the achievable lattice -/

section Soundness

/-- The `(3,4)`-column of the `x0`-slot Fox letter; `sqFoxX6_a` is committed, this one is not
and section 5 needs it. -/
@[simp] theorem sqFoxX6_c {R : Type} [CommRing R] (s x y : SqU6 R) :
    (sqFoxX6 s x y).c = 10 * x.c - s.c - 8 * y.c := rfl

/-- A strictly triangular cross-handle pairing with an even left factor is even. -/
theorem sqCross_even_left {R : Type} [CommRing R] {n : ℕ} {x y : Fin n → R}
    (hx : ∀ s, (2 : R) ∣ x s) : (2 : R) ∣ sqCross x y := by
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun s _ => ?_
  split_ifs
  · exact Dvd.dvd.mul_right (hx s) _
  · exact dvd_zero _

/-- …and with an even right factor. -/
theorem sqCross_even_right {R : Type} [CommRing R] {n : ℕ} {x y : Fin n → R}
    (hy : ∀ t, (2 : R) ∣ y t) : (2 : R) ∣ sqCross x y := by
  refine Finset.dvd_sum fun t _ => Finset.dvd_sum fun s _ => ?_
  split_ifs
  · exact Dvd.dvd.mul_left (hy t) _
  · exact dvd_zero _

/-- The handle block's first class-two coordinate is even when the letters' `(1,2)`-columns
are. -/
theorem sqU6BlockF_even {R : Type} [CommRing R] {n : ℕ} {u v : Fin n → SqU6 R}
    (hu : ∀ k, (2 : R) ∣ (u k).a) (hv : ∀ k, (2 : R) ∣ (v k).a) :
    (2 : R) ∣ sqU6BlockF u v :=
  Finset.dvd_sum fun k _ =>
    dvd_sub (Dvd.dvd.mul_right (hu k) _) (Dvd.dvd.mul_right (hv k) _)

'''

TAIL = r'''
/-- **The handle shift's class-three left row is even**, which is what kills the cross-handle
term and the collection element. -/
theorem SqU6.gaTwoHandle_j_even {R : Type} [CommRing R] {p q z w : SqU6 R}
    (hpa : (2 : R) ∣ p.a) (hqa : (2 : R) ∣ q.a) (hzf : (2 : R) ∣ z.f) (hwf : (2 : R) ∣ w.f) :
    (2 : R) ∣ (SqU6.gaTwoHandle p q z w).j :=
  dvd_sub (SqU6.gaTwoPairJ_even hzf hqa) (SqU6.gaTwoPairJ_even hwf hpa)

/-- ⭐⭐ **The core shift's class-five row is even modulo the three channels.**  Every block is:
the Frobenius weights are even outright, each Fox pairing is `SqU6.gaTwoPairO_channel_even`, the
correction is `SqU6.gaTwoCorrO_even`, and the quadratic block is `SqU6.gaTwoQuadO_even`. -/
theorem SqU6.gaTwoCore_o_channel_even {R : Type} [CommRing R] {s x y z₀ z₁ z₂ : SqU6 R}
    (hsa : (2 : R) ∣ s.a) (hsc : (2 : R) ∣ s.c) (hxa : (2 : R) ∣ x.a) (hxc : (2 : R) ∣ x.c)
    (hya : (2 : R) ∣ y.a) (hyc : (2 : R) ∣ y.c) (h0f : (2 : R) ∣ z₀.f) (h0h : (2 : R) ∣ z₀.h)
    (h0j : (2 : R) ∣ z₀.j) (h1f : (2 : R) ∣ z₁.f) (h1h : (2 : R) ∣ z₁.h) (h1j : (2 : R) ∣ z₁.j)
    (h2f : (2 : R) ∣ z₂.f) (h2h : (2 : R) ∣ z₂.h) (h2j : (2 : R) ∣ z₂.j) :
    (2 : R) ∣ ((SqU6.gaTwoCore s x y z₀ z₁ z₂).o
      - (SqU6.gaTwoChannel z₀ x + SqU6.gaTwoChannel z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoChannel z₂ y)) := by
  have hfa : (2 : R) ∣ (sqFoxX6 s x y).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxa 10) hsa) (Dvd.dvd.mul_left hya 8)
  have hfc : (2 : R) ∣ (sqFoxX6 s x y).c := by
    rw [sqFoxX6_c]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left hxc 10) hsc) (Dvd.dvd.mul_left hyc 8)
  have hrw : (SqU6.gaTwoCore s x y z₀ z₁ z₂).o
      - (SqU6.gaTwoChannel z₀ x + SqU6.gaTwoChannel z₁ (sqFoxX6 s x y)
        + SqU6.gaTwoChannel z₂ y)
      = -4 * z₁.o + 2 * z₂.o
        + (SqU6.gaTwoPairO z₀ x - SqU6.gaTwoChannel z₀ x)
        + (SqU6.gaTwoPairO z₁ (sqFoxX6 s x y) - SqU6.gaTwoChannel z₁ (sqFoxX6 s x y))
        + (SqU6.gaTwoPairO z₂ y - SqU6.gaTwoChannel z₂ y)
        + SqU6.gaTwoCorrO s x y z₀ z₁ z₂ + SqU6.gaTwoQuadO s x y z₀ z₁ z₂ := by
    simp only [SqU6.gaTwoCore]
    ring
  rw [hrw]
  refine dvd_add (dvd_add (dvd_add (dvd_add (dvd_add ⟨-2 * z₁.o + z₂.o, by ring⟩
    (SqU6.gaTwoPairO_channel_even hxa hxc h0f h0h h0j))
    (SqU6.gaTwoPairO_channel_even hfa hfc h1f h1h h1j))
    (SqU6.gaTwoPairO_channel_even hya hyc h2f h2h h2j))
    (SqU6.gaTwoCorrO_even hsa hsc hxa hxc hya hyc h0f h0h h0j h1f h1h h1j h2f h2h h2j))
    (SqU6.gaTwoQuadO_even hsa hsc hxa hxc hya hyc h0f h0h h0j h1f h1h h1j h2f h2h h2j)

/-- ⭐ **The handle block's summed class-five row is even modulo its channels**, cross-handle
term included. -/
theorem SqU6.gaTwoHandleSum_o_channel_even {R : Type} [CommRing R] {n : ℕ}
    {u v zu zv : Fin n → SqU6 R}
    (hua : ∀ k, (2 : R) ∣ (u k).a) (huc : ∀ k, (2 : R) ∣ (u k).c)
    (hva : ∀ k, (2 : R) ∣ (v k).a) (hvc : ∀ k, (2 : R) ∣ (v k).c)
    (hzu : ∀ k, (2 : R) ∣ (zu k).f ∧ (2 : R) ∣ (zu k).h ∧ (2 : R) ∣ (zu k).j)
    (hzv : ∀ k, (2 : R) ∣ (zv k).f ∧ (2 : R) ∣ (zv k).h ∧ (2 : R) ∣ (zv k).j) :
    (2 : R) ∣ ((SqU6.gaTwoHandleSum n u v zu zv).o
      - ∑ k : Fin n, (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))) := by
  have hrw : (SqU6.gaTwoHandleSum n u v zu zv).o
      - ∑ k : Fin n, (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))
      = (∑ k : Fin n, ((SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).o
          - (SqU6.gaTwoChannel (zu k) (v k) - SqU6.gaTwoChannel (zv k) (u k))))
        + sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).j)
            (fun k => (u k).d * (v k).e - (v k).d * (u k).e)
        - sqCross (fun k => (SqU6.gaTwoHandle (u k) (v k) (zu k) (zv k)).l)
            (fun k => (u k).a * (v k).b - (v k).a * (u k).b) := by
    simp only [SqU6.gaTwoHandleSum, Finset.sum_sub_distrib]
    ring
  rw [hrw]
  refine dvd_sub (dvd_add (Finset.dvd_sum fun k _ =>
      SqU6.gaTwoHandle_o_channel_even (hua k) (huc k) (hva k) (hvc k)
        (hzu k).1 (hzu k).2.1 (hzu k).2.2 (hzv k).1 (hzv k).2.1 (hzv k).2.2)
    (sqCross_even_left fun k =>
      SqU6.gaTwoHandle_j_even (hua k) (hva k) (hzu k).1 (hzv k).1))
    (sqCross_even_right fun k =>
      dvd_sub (Dvd.dvd.mul_right (hua k) _) (Dvd.dvd.mul_right (hva k) _))

variable {R : Type} [CommRing R] {h : ℕ} {m z : Fin (sqRank h) → SqU6 R}

/-- **The class-five row of the shift, unpacked** from the three-factor product: the core
shift's row, the handle sum's row, the collection element's row, and one cross term. -/
theorem SqU6.gaTwoShift_o (m z : Fin (sqRank h) → SqU6 R) :
    (SqU6.gaTwoShift h m z).o
      = (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
        + ((SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).o
          + (SqU6.gaTwoColl h m z).o)
        + (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
          * (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).l := by
  rw [SqU6.gaTwoShift, SqU6.gaThree_mul (SqU6.gaTwoHandleSum_isGaThree _ _ _ _ _)
    (SqU6.gaTwoColl_isGaFour m z).isGaThree, SqU6.mul_o]
  simp only [SqU6.gaTwoCore_a, SqU6.gaTwoColl]
  ring

/-- ⭐ **The collection element's class-five row is even** on the achievable lattice: its four
blocks meet the core shift's even class-two rows, its even class-three left row, and the handle
block's even `(a, b)`-pairing. -/
theorem SqU6.gaTwoColl_o_even
    (ha : ∀ i, (2 : R) ∣ (m i).a)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ (SqU6.gaTwoColl h m z).o := by
  have hcf : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f :=
    ⟨-2 * (z 1).f + (z 2).f, by rw [SqU6.gaTwoCore_f]; ring⟩
  have hci : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).i :=
    ⟨-2 * (z 1).i + (z 2).i, by rw [SqU6.gaTwoCore_i]; ring⟩
  have hfa : (2 : R) ∣ (sqFoxX6 (m 0) (m 1) (m 2)).a := by
    rw [sqFoxX6_a]
    exact dvd_sub (dvd_sub (Dvd.dvd.mul_left (ha 1) 10) (ha 0)) (Dvd.dvd.mul_left (ha 2) 8)
  have hcj : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).j := by
    have : (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).j
        = -4 * (z 1).j + 2 * (z 2).j + (SqU6.gaTwoPairJ (z 0) (m 1)
          + SqU6.gaTwoPairJ (z 1) (sqFoxX6 (m 0) (m 1) (m 2)) + SqU6.gaTwoPairJ (z 2) (m 2)) :=
      rfl
    rw [this]
    exact dvd_add ⟨-2 * (z 1).j + (z 2).j, by ring⟩
      (dvd_add (dvd_add (SqU6.gaTwoPairJ_even (hz 0).1 (ha 1))
        (SqU6.gaTwoPairJ_even (hz 1).1 hfa)) (SqU6.gaTwoPairJ_even (hz 2).1 (ha 2)))
  have hbf : (2 : R) ∣ sqU6BlockF (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k)) :=
    sqU6BlockF_even (fun k => ha _) (fun k => ha _)
  simp only [SqU6.gaTwoColl]
  exact dvd_sub (dvd_add (dvd_sub (Dvd.dvd.mul_right hcf _) (Dvd.dvd.mul_left hbf _))
    (Dvd.dvd.mul_right hcj _)) (Dvd.dvd.mul_right hci _)

variable (h) in
/-- **The three-channel functional**: the only part of the class-five row that survives mod two
on the achievable lattice.  Each slot's dressing is read against the PERMUTED letter, exactly as
in the Fox form, and each handle against the opposite handle letter. -/
def SqU6.gaTwoShiftChan (m z : Fin (sqRank h) → SqU6 R) : R :=
  SqU6.gaTwoChannel (z 0) (m 1) + SqU6.gaTwoChannel (z 1) (sqFoxX6 (m 0) (m 1) (m 2))
    + SqU6.gaTwoChannel (z 2) (m 2)
    + ∑ k : Fin h, (SqU6.gaTwoChannel (z (sqHandleIdxU k)) (m (sqHandleIdxV k))
        - SqU6.gaTwoChannel (z (sqHandleIdxV k)) (m (sqHandleIdxU k)))

/-- ⭐⭐⭐ **THE `gamma_2`-LEVEL SOUNDNESS AT CLASS FIVE.**  At any marking all of whose slots
have an even `(1,2)`-column and an even `(3,4)`-column, every five-slot `gamma_2`-dressing whose
slots have even `f`, `h` and `j` moves the relator's class-five row by the three-channel
functional `SqU6.gaTwoShiftChan`, **modulo two**.  Everything else - the whole quadratic block
included - is even.

This is the statement `GradedFiveStageFour` could not make.  The hypotheses are exactly its
`stageN1` on the frame and `stageN2` on the dressing, and `stageN2_of_commutator` proves that
the honest `gamma_2` of an image subgroup with `stageN1` letters satisfies them, so the lattice
here is achievable, not declared. -/
theorem SqU6.gaTwoShift_o_channel_even
    (ha : ∀ i, (2 : R) ∣ (m i).a) (hc : ∀ i, (2 : R) ∣ (m i).c)
    (hz : ∀ i, (2 : R) ∣ (z i).f ∧ (2 : R) ∣ (z i).h ∧ (2 : R) ∣ (z i).j) :
    (2 : R) ∣ ((SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z) := by
  have hcf : (2 : R) ∣ (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f :=
    ⟨-2 * (z 1).f + (z 2).f, by rw [SqU6.gaTwoCore_f]; ring⟩
  have hrw : (SqU6.gaTwoShift h m z).o - SqU6.gaTwoShiftChan h m z
      = ((SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).o
          - (SqU6.gaTwoChannel (z 0) (m 1)
            + SqU6.gaTwoChannel (z 1) (sqFoxX6 (m 0) (m 1) (m 2))
            + SqU6.gaTwoChannel (z 2) (m 2)))
        + ((SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).o
            - ∑ k : Fin h, (SqU6.gaTwoChannel (z (sqHandleIdxU k)) (m (sqHandleIdxV k))
              - SqU6.gaTwoChannel (z (sqHandleIdxV k)) (m (sqHandleIdxU k))))
        + (SqU6.gaTwoColl h m z).o
        + (SqU6.gaTwoCore (m 0) (m 1) (m 2) (z 0) (z 1) (z 2)).f
          * (SqU6.gaTwoHandleSum h (fun k => m (sqHandleIdxU k)) (fun k => m (sqHandleIdxV k))
              (fun k => z (sqHandleIdxU k)) (fun k => z (sqHandleIdxV k))).l := by
    rw [SqU6.gaTwoShift_o, SqU6.gaTwoShiftChan]
    ring
  rw [hrw]
  exact dvd_add (dvd_add (dvd_add
    (SqU6.gaTwoCore_o_channel_even (ha 0) (hc 0) (ha 1) (hc 1) (ha 2) (hc 2)
      (hz 0).1 (hz 0).2.1 (hz 0).2.2 (hz 1).1 (hz 1).2.1 (hz 1).2.2
      (hz 2).1 (hz 2).2.1 (hz 2).2.2)
    (SqU6.gaTwoHandleSum_o_channel_even (fun k => ha _) (fun k => hc _) (fun k => ha _)
      (fun k => hc _) (fun k => hz _) (fun k => hz _)))
    (SqU6.gaTwoColl_o_even ha hz)) (Dvd.dvd.mul_right hcf _)

end Soundness

end SqCore

end Dyadic

end GQ2
'''

with open(LEAN) as fh:
    src = fh.read()

marker = "end Transport\n"
head, sep, tail = src.partition(marker)
assert sep, "marker not found"
out = head + sep + "\n" + HEAD + emitted + TAIL

with open(LEAN, "w") as fh:
    fh.write(out)
print("spliced section 5 into %s (%d lines)" % (LEAN, out.count("\n") + 1))
