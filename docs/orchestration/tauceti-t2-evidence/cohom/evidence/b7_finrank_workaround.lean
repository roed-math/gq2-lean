module

public import TauCeti.NumberTheory.ClassFieldTheory.Local.EulerCharacteristic.Theorem

example : Module.finrank ℚ_[2] ℚ_[2] = 1 :=
  @Module.finrank_self ℚ_[2] _ (@commRing_strongRankCondition ℚ_[2] _ DivisionRing.toNontrivial)

section
attribute [-instance] TauCeti.IsAdicComplete.henselianLocalRing
example : Module.finrank ℚ_[2] ℚ_[2] = 1 := Module.finrank_self ℚ_[2]
example : @Module.finrank ℚ_[2] ℚ_[2] _ _
    (@Algebra.toModule _ _ _ _ (TauCeti.FinitePadicExtension.toAlgebra ℚ_[2] 2)) = 1 :=
  Module.finrank_self ℚ_[2]
end
