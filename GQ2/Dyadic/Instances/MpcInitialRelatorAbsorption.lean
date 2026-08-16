/-
Copyright (c) 2026 David Roe. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
Authors: David Roe, roed@mit.edu, using OpenAI Codex
-/

import GQ2.Dyadic.Instances.MpcInitialRelatorAbsorptionCore

/-!
# Uniform initial-relator absorption

Packages the five all-degree range theorems into the campaign proposition
`MpcMkInitialRelatorAbsorption`. The theorem is proved directly; it is not an axiom
or an assumed exactness hypothesis.
-/

namespace GQ2.Dyadic.Instances.MpcMk

open GQ2 GQ2.Dyadic GQ2.Dyadic.MarkedCore Multiplicative
open GQ2.Dyadic.Instances.MpcOrb
open GQ2.Roe.Labute

noncomputable section

theorem mpcMk_initialRelatorAbsorption (r : Nat) (hr : 2 ≤ r) :
    MpcMkInitialRelatorAbsorption r hr := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    change mpcMkRawCost (k + 2) _ 1 1
      (mpcMkRawUt (mpcMkTowerC a) ha) ∈
        MonoidHom.range (mpcMkCost (k + 2) _ 1 1)
    exact mpcMk_absorb_utC k a ha
  · intro a ha
    change mpcMkRawCost (k + 2) _ 1 1
      (mpcMkRawUt (mpcMkTowerD a) ha) ∈
        MonoidHom.range (mpcMkCost (k + 2) _ 1 1)
    exact mpcMk_absorb_utD k a ha
  · intro a ha
    change mpcMkRawCost (k + 2) _ 1 1
      (mpcMkRawUm (mpcMkTowerB a) ha) ∈
        MonoidHom.range (mpcMkCost (k + 2) _ 1 1)
    exact mpcMk_absorb_umB k a ha
  · intro a ha
    change mpcMkRawCost (k + 2) _ 1 1
      (mpcMkRawUm (mpcMkTowerC a) ha) ∈
        MonoidHom.range (mpcMkCost (k + 2) _ 1 1)
    exact mpcMk_absorb_umC k a ha
  · intro a ha
    change mpcMkRawCost (k + 2) _ 1 1
      (mpcMkRawUn (mpcMkTowerD a) ha) ∈
        MonoidHom.range (mpcMkCost (k + 2) _ 1 1)
    exact mpcMk_absorb_unD k a ha

#print axioms mpcMk_initialRelatorAbsorption

end
end GQ2.Dyadic.Instances.MpcMk
