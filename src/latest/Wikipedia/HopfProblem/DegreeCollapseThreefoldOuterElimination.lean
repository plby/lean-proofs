import Wikipedia.HopfProblem.DegreeCollapseOuterIndexElimination
import Wikipedia.HopfProblem.DegreeCollapseHomotopyEquivalence

/-!
# The original threefold has an ordered Morse system without indices one and five

All manifold and homotopy-sphere hypotheses are discharged for the unchanged
threefold and its original real atlas. The middle handles still remain.
-/

noncomputable section

open Set Manifold
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.Threefold

open SpecialPeriods MorseCancellation

attribute [local instance] SpecialPeriods.Threefold.chartedSpace
  SpecialPeriods.Threefold.space_compact SpecialPeriods.Threefold.space_t2Space
  SpecialPeriods.Threefold.space_isSmoothRealManifold SpecialPeriods.Threefold.space_pathConnected

theorem exists_minimal_ordered_morse_without_outer_indices :
    ∃ f : SpecialPeriods.Threefold.Space → ℝ,
      ContMDiff 𝓘(ℝ, ℂ × ComplexPlane₂) 𝓘(ℝ, ℝ) ∞ f ∧ IsMorse (ℂ × ComplexPlane₂) f ∧
      ∃ S : AdaptedSurgeryWindows (ℂ × ComplexPlane₂) f,
        (∀ p q : criticalPoints (ℂ × ComplexPlane₂) f, f p < f q →
          nativeMorseIndex (ℂ × ComplexPlane₂) f p ≤ nativeMorseIndex (ℂ × ComplexPlane₂) f q) ∧
        nativeMorseCount (ℂ × ComplexPlane₂) f 0 = 1 ∧
        nativeMorseCount (ℂ × ComplexPlane₂) f 6 = 1 ∧
        nativeMorseCount (ℂ × ComplexPlane₂) f 1 = 0 ∧
        nativeMorseCount (ℂ × ComplexPlane₂) f 5 = 0 ∧
        ∀ g : SpecialPeriods.Threefold.Space → ℝ,
          ContMDiff 𝓘(ℝ, ℂ × ComplexPlane₂) 𝓘(ℝ, ℝ) ∞ g → IsMorse (ℂ × ComplexPlane₂) g →
          InjOn g (criticalPoints (ℂ × ComplexPlane₂) g) →
          (criticalPoints (ℂ × ComplexPlane₂) f).ncard ≤
            (criticalPoints (ℂ × ComplexPlane₂) g).ncard :=
  exists_minimal_ordered_morse_system_without_outer_indices
    (ℂ × ComplexPlane₂) SpecialPeriods.Threefold.Space threefoldHomotopyEquiv
    SpecialPeriods.Threefold.real_dimension

end Wikipedia.HopfProblem.DegreeCollapse.Threefold
