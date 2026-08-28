import Wikipedia.NoExoticSixSphere.ModTwoDualShortExact

/-!
# Actual maps on the reversed mod-two dual sequences

A morphism of original chain rows gives a morphism of their reversed
dual cochain rows. Each component is the original precomposition map.
-/

noncomputable section

open CategoryTheory

namespace NoExoticSixSphere.ModTwoDualComplex

variable {S T : ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ)}

/-- Reverse an actual chain-row morphism by original mod-two precomposition. -/
def sequenceMap (φ : S ⟶ T) : sequence T ⟶ sequence S where
  τ₁ := map φ.τ₃
  τ₂ := map φ.τ₂
  τ₃ := map φ.τ₁
  comm₁₂ := by
    change map φ.τ₃ ≫ map S.g = map T.g ≫ map φ.τ₂
    rw [← map_comp, ← map_comp]
    exact congrArg map φ.comm₂₃.symm
  comm₂₃ := by
    change map φ.τ₂ ≫ map S.f = map T.f ≫ map φ.τ₁
    rw [← map_comp, ← map_comp]
    exact congrArg map φ.comm₁₂.symm

end NoExoticSixSphere.ModTwoDualComplex
