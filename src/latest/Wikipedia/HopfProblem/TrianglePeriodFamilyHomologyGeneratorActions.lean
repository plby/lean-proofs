import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyMeridianTransitions
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyOrientationAlgebra
import Wikipedia.HopfProblem.TrianglePeriodFamilyLattice
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCirclePointClass

/-!
# Actual generator actions in the regular-family difference complex

The normalized slit transitions are actual triangle-torus homeomorphisms.
Their singular-homology maps, including the inverse on one side, are
compared with the two literal source generator actions. An explicit
integral domain equivalence turns the slit difference map into the source
difference map, preserving cokernel representatives.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SpecialPeriods.Triangle RiemannMapping
open SingularMayerVietoris PeriodTorusHigherHomology TrianglePeriodFamilyHomologyAlgebra

/-- The actual all-degree singular-homology action of a triangle-torus homeomorphism. -/
def triangleHomologyEquiv (g : TriangleGroup) (n : ℕ) :
    SingularHomology RealTorus₄ n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  homeomorphHomologyEquiv (triangleTorusHomeomorph g) n

@[simp] theorem triangleHomologyEquiv_apply (g : TriangleGroup) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    triangleHomologyEquiv g n a =
      singularHomologyMap (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) n a := rfl

@[simp] theorem triangleHomologyEquiv_one (n : ℕ) :
    triangleHomologyEquiv 1 n = LinearEquiv.refl ℤ (SingularHomology RealTorus₄ n) := by
  rw [triangleHomologyEquiv, triangleTorusHomeomorph_one, homeomorphHomologyEquiv_refl]

@[simp] theorem triangleHomologyEquiv_inv (g : TriangleGroup) (n : ℕ) :
    triangleHomologyEquiv g⁻¹ n = (triangleHomologyEquiv g n).symm := by
  rw [triangleHomologyEquiv, triangleTorusHomeomorph_inv]
  exact (homeomorphHomologyEquiv_symm (triangleTorusHomeomorph g) n).symm

/-- Every actual triangle map acts identically on the connected torus's zero homology. -/
theorem triangleHomologyEquiv_zero (g : TriangleGroup) :
    triangleHomologyEquiv g 0 = LinearEquiv.refl ℤ (SingularHomology RealTorus₄ 0) := by
  apply LinearEquiv.ext
  intro a
  apply (connectedHomologyZeroEquiv RealTorus₄).injective
  exact connectedHomologyZeroEquiv_natural
    (triangleTorusHomeomorph g : C(RealTorus₄, RealTorus₄)) a

/-- The actual lower-overlap map in the chosen upper-chart marking. -/
def overlapHomologyAction (b : SlitBaseLift) (i : Fin 3) (n : ℕ) :
    SingularHomology RealTorus₄ n →ₗ[ℤ] SingularHomology RealTorus₄ n :=
  (triangleHomologyEquiv (overlapTransition b i) n).toLinearMap

@[simp] theorem overlapHomologyAction_apply (b : SlitBaseLift) (i : Fin 3) (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    overlapHomologyAction b i n a =
      singularHomologyMap
        (triangleTorusHomeomorph (overlapTransition b i) : C(RealTorus₄, RealTorus₄)) n a := rfl

@[simp] theorem overlapHomologyAction_middle (b : SlitBaseLift) (n : ℕ) :
    overlapHomologyAction b 1 n = LinearMap.id := by
  rw [overlapHomologyAction, overlapTransition_middle, triangleHomologyEquiv_one]
  rfl

/-- The two literal source generator actions on actual torus homology. -/
def generatorHomologyEquiv (j : Bool) (n : ℕ) :
    SingularHomology RealTorus₄ n ≃ₗ[ℤ] SingularHomology RealTorus₄ n :=
  triangleHomologyEquiv (if j then triangleGenerator₂ else triangleGenerator₁) n

@[simp] theorem generatorHomologyEquiv_false (n : ℕ) :
    generatorHomologyEquiv false n = triangleHomologyEquiv triangleGenerator₁ n := rfl

@[simp] theorem generatorHomologyEquiv_true (n : ℕ) :
    generatorHomologyEquiv true n = triangleHomologyEquiv triangleGenerator₂ n := rfl

/-- The genuine source-monodromy difference map in any degree. -/
def sourceDifference (n : ℕ) :
    (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularHomology RealTorus₄ n :=
  delta (generatorHomologyEquiv false n).toLinearMap (generatorHomologyEquiv true n).toLinearMap

/-- The actual slit-cover difference map, before adjusting meridian orientations. -/
def slitDifference (b : SlitBaseLift) (n : ℕ) :
    (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) →ₗ[ℤ]
      SingularHomology RealTorus₄ n :=
  delta (overlapHomologyAction b 0 n) (overlapHomologyAction b 2 n)

/-- The slit difference map with the literal normalized half-triangle base lift. -/
abbrev normalizedSlitDifference (n : ℕ) := slitDifference normalizedSlitBaseLift n

theorem normalizedSlitDifference_of_pos (n : ℕ) (ho : 0 < normalizationOrientation) :
    normalizedSlitDifference n =
      delta (generatorHomologyEquiv false n).symm.toLinearMap
        (generatorHomologyEquiv true n).toLinearMap := by
  change delta (triangleHomologyEquiv (normalizedOverlapTransition 0) n).toLinearMap
    (triangleHomologyEquiv (normalizedOverlapTransition 2) n).toLinearMap = _
  rw [normalizedOverlapTransition_left_of_pos ho,
    normalizedOverlapTransition_right_of_pos ho, triangleHomologyEquiv_inv]
  rfl

theorem normalizedSlitDifference_of_nonpos (n : ℕ) (ho : normalizationOrientation ≤ 0) :
    normalizedSlitDifference n =
      delta (generatorHomologyEquiv false n).toLinearMap
        (generatorHomologyEquiv true n).symm.toLinearMap := by
  change delta (triangleHomologyEquiv (normalizedOverlapTransition 0) n).toLinearMap
    (triangleHomologyEquiv (normalizedOverlapTransition 2) n).toLinearMap = _
  rw [normalizedOverlapTransition_left_of_nonpos ho,
    normalizedOverlapTransition_right_of_nonpos ho, triangleHomologyEquiv_inv]
  rfl

/-- The explicit integral change from slit-component cycles to source-oriented meridian cycles. -/
def normalizedSourceDomainEquiv (n : ℕ) :
    (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) ≃ₗ[ℤ]
      (SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :=
  if 0 < normalizationOrientation then inverseFirstCoordinate (generatorHomologyEquiv false n)
  else inverseSecondCoordinate (generatorHomologyEquiv true n)

/-- The source difference after the actual orientation change is exactly the slit difference. -/
theorem sourceDifference_coordinate_change (n : ℕ)
    (x : SingularHomology RealTorus₄ n × SingularHomology RealTorus₄ n) :
    sourceDifference n (normalizedSourceDomainEquiv n x) = normalizedSlitDifference n x := by
  by_cases ho : 0 < normalizationOrientation
  · rw [normalizedSourceDomainEquiv, if_pos ho, normalizedSlitDifference_of_pos n ho]
    exact delta_inverse_first (generatorHomologyEquiv false n)
      (generatorHomologyEquiv true n).toLinearMap x
  · rw [normalizedSourceDomainEquiv, if_neg ho,
      normalizedSlitDifference_of_nonpos n (le_of_not_gt ho)]
    exact delta_inverse_second (generatorHomologyEquiv false n).toLinearMap
      (generatorHomologyEquiv true n) x

theorem normalizedSlitDifference_range (n : ℕ) :
    LinearMap.range (normalizedSlitDifference n) = LinearMap.range (sourceDifference n) :=
  range_eq_of_coordinates _ _ (normalizedSourceDomainEquiv n)
    (sourceDifference_coordinate_change n)

/-- The kernel normalization retains the explicitly oriented two meridian coordinates. -/
def normalizedSlitKernelEquiv (n : ℕ) :
    LinearMap.ker (normalizedSlitDifference n) ≃ₗ[ℤ] LinearMap.ker (sourceDifference n) :=
  kernelEquivOfCoordinates _ _ (normalizedSourceDomainEquiv n)
    (sourceDifference_coordinate_change n)

@[simp] theorem normalizedSlitKernelEquiv_apply_val (n : ℕ)
    (x : LinearMap.ker (normalizedSlitDifference n)) :
    (normalizedSlitKernelEquiv n x : SingularHomology RealTorus₄ n ×
      SingularHomology RealTorus₄ n) = normalizedSourceDomainEquiv n x.val := rfl

/-- Cokernel normalization does not change the actual fibre-homology representative. -/
def normalizedSlitCokernelEquiv (n : ℕ) :
    (SingularHomology RealTorus₄ n ⧸ LinearMap.range (normalizedSlitDifference n)) ≃ₗ[ℤ]
      SingularHomology RealTorus₄ n ⧸ LinearMap.range (sourceDifference n) :=
  integralQuotientCongr (H := SingularHomology RealTorus₄ n)
    (LinearMap.range (normalizedSlitDifference n)) (LinearMap.range (sourceDifference n))
    (normalizedSlitDifference_range n)

@[simp] theorem normalizedSlitCokernelEquiv_mk (n : ℕ)
    (a : SingularHomology RealTorus₄ n) :
    normalizedSlitCokernelEquiv n (Submodule.Quotient.mk a) = Submodule.Quotient.mk a := rfl

/-- In degree zero both actual monodromies are the identity, so the source difference is zero. -/
@[simp] theorem sourceDifference_zero : sourceDifference 0 = 0 := by
  apply LinearMap.ext
  intro x
  change (triangleHomologyEquiv triangleGenerator₁ 0 x.1 - x.1) +
    (triangleHomologyEquiv triangleGenerator₂ 0 x.2 - x.2) = 0
  rw [triangleHomologyEquiv_zero, triangleHomologyEquiv_zero]
  simp

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
