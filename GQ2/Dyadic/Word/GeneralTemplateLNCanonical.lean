/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, and OpenAI Codex
-/
import GQ2.Dyadic.Word.GeneralTemplateLN

/-!
# Exact denotation of the canonical legacy L/N export trees

The unchanged S1.1 serializer canonicalizes EtaHat's rational pair. These
rank-uniform bridges tie that actual exported tree to the original semantic
word, including nonreduced or negative-denominator odd displays. Nothing in
the old factories, canonicalization, serializer or frozen fixtures is changed.
-/

namespace GQ2.Dyadic.GeneralTemplateLN
open GQ2 GQ2.Dyadic Words Export

theorem canon_rawLsq (h : ℕ) : (LSq.rawLsq h).canon = LSq.rawLsq h := by
  cases h <;> rfl

theorem canon_rawNCompact (alpha h : ℕ) :
    (Words.rawNCompact alpha h).canon = Words.rawNCompact alpha h := rfl

theorem canon_rawNpc (alpha r h : ℕ) (num den : ℤ) :
    (Npc.rawNpc alpha r h num den).canon =
      Npc.rawNpc alpha r h (canonicalEtaHat ⟨num,den⟩).num
        (canonicalEtaHat ⟨num,den⟩).den := rfl

theorem npcW_canonicalEtaHat (alpha r h : ℕ) (e : EtaData) (hd : Odd e.den) :
    Npc.npcW alpha r h (canonicalEtaHat e) = Npc.npcW alpha r h e := by
  simp only [Npc.npcW, Npc.aW, Npc.dBlockW, Npc.eBlockW, EtaData.canonicalEtaHat_toZhat hd]

theorem denote_canon_rawLsq (h : ℕ) :
    denote (LSq.denoteCtx h) (LSq.rawLsq h).canon = some (LSq.lSqW h) := by
  rw [canon_rawLsq]
  exact denote_rawLsq h

theorem denote_canon_rawNCompact (alpha h : ℕ) :
    denote (Words.denoteCtx h) (Words.rawNCompact alpha h).canon =
      some (Words.nCompactW alpha h) := by
  rw [canon_rawNCompact]
  exact denote_rawNCompact alpha h

theorem denote_canon_rawNpc (alpha r h : ℕ) (num den : ℤ) (hd : Odd den) :
    denote (Words.denoteCtx h) (Npc.rawNpc alpha r h num den).canon =
      some (Npc.npcW alpha r h ⟨num,den⟩) := by
  rw [canon_rawNpc, denote_rawNpc]
  exact congrArg some (npcW_canonicalEtaHat alpha r h ⟨num,den⟩ hd)

theorem denote_canon_rawNpc_display (alpha r h : ℕ) {eta : ℤ_[2]ˣ}
    (d : NpcDisplayFor eta) :
    denote (Words.denoteCtx h) (Npc.rawNpc alpha r h d.data.num d.data.den).canon =
      some (Npc.npcWUnit alpha r h eta) := by
  rw [Npc.npcWUnit_eq_display alpha r h d]
  have hd : Odd d.data.den := by
    rw [Int.odd_iff]
    have := d.den_odd
    omega
  exact denote_canon_rawNpc alpha r h d.data.num d.data.den hd

#print axioms canon_rawLsq
#print axioms canon_rawNCompact
#print axioms canon_rawNpc
#print axioms npcW_canonicalEtaHat
#print axioms denote_canon_rawLsq
#print axioms denote_canon_rawNCompact
#print axioms denote_canon_rawNpc
#print axioms denote_canon_rawNpc_display

end GQ2.Dyadic.GeneralTemplateLN
