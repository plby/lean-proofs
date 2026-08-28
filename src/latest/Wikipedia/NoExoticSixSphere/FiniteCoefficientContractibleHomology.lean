import Wikipedia.HopfProblem.SphereHomologyCoefficientsSequence
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePoint

/-!
# Positive finite-coefficient homology of a contractible space

The original integral homology vanishes in positive degrees and its
degree-zero augmentation is an integral marking. Thus every preceding
integral group is torsion-free, and the actual coefficient sequence
transfers the vanishing to native finite-coefficient homology.
-/

noncomputable section

open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
  SphereHomologyCoefficients

namespace NoExoticSixSphere

variable (X : Type) [TopologicalSpace X] [ContractibleSpace X]

/-- Contractibility supplies actual torsion-freeness in every integral degree. -/
theorem contractible_integralHomology_torsionFree (k : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology X k) := by
  by_cases hk : k = 0
  · subst k
    let := Module.Free.of_equiv (connectedHomologyZeroEquiv X).symm
    infer_instance
  · let := contractible_homology_subsingleton X k hk
    infer_instance

/-- The original finite-coefficient homology vanishes in every positive degree. -/
theorem contractible_modHomology_subsingleton (p : ℕ) (hp : p ≠ 0) (k : ℕ) (hk : k ≠ 0) :
    Subsingleton (ModHomology p X k) := by
  let := contractible_homology_subsingleton X k hk
  let := contractible_integralHomology_torsionFree X (k - 1)
  exact modHomology_subsingleton p hp X k

end NoExoticSixSphere
