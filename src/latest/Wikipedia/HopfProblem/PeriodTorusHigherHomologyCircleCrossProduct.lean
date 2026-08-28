import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleCrossProductConnecting
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleProductNaturality
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCrossProductProjection

/-!
# The actual cross-product isomorphism for a circle factor

Projection kills the positive-circle cross product, while the actual
signed connecting map is its left inverse. Consequently the canonical
circle-product splitting has inverse equal to the sum of the actual
zero-section map and the actual positive-loop cross product.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusHigherHomology

open FirstHurewicz SingularMayerVietoris CircleTopology CirclePaths

variable (X : Type) [TopologicalSpace X]

/-- The actual positive-circle cross product has zero unchanged-factor projection. -/
@[simp] theorem circleProjection_positiveCircleCross (n : ℕ) (b : SingularHomology X n) :
    circleProjectionHomology X (n + 1) (positiveCircleCross X n b) = 0 :=
  crossProductHomology_snd n (loopHomologyClass positiveLoop) b

/-- The actual positive-loop cross product is precisely the second summand
of the proved circle-product splitting. -/
@[simp] theorem circleProductHomologyEquiv_positiveCircleCross (n : ℕ)
    (b : SingularHomology X n) :
    circleProductHomologyEquiv X n (positiveCircleCross X n b) = (0, b) := by
  apply Prod.ext
  · exact circleProjection_positiveCircleCross X n b
  · exact circleBoundary_positiveCircleCross X n b

theorem positiveCircleCross_eq_symm (n : ℕ) (b : SingularHomology X n) :
    positiveCircleCross X n b = (circleProductHomologyEquiv X n).symm (0, b) := by
  apply (circleProductHomologyEquiv X n).injective
  rw [circleProductHomologyEquiv_positiveCircleCross, LinearEquiv.apply_symm_apply]

/-- The inverse is the actual section plus the actual cross product, not
an abstract inverse chosen solely from the ranks of the groups. -/
theorem circleProductHomologyEquiv_symm_eq_section_add_cross (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    (circleProductHomologyEquiv X n).symm a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2 := by
  apply (circleProductHomologyEquiv X n).injective
  rw [LinearEquiv.apply_symm_apply, map_add, circleProductHomologyEquiv_section,
    circleProductHomologyEquiv_positiveCircleCross]
  exact Prod.ext (add_zero _).symm (zero_add _).symm

/-- The genuine circle-factor cross-product isomorphism on actual integral homology. -/
def circleProductCrossEquiv (n : ℕ) :
    (SingularHomology X (n + 1) × SingularHomology X n) ≃ₗ[ℤ]
      SingularHomology (Circle × X) (n + 1) :=
  (circleProductHomologyEquiv X n).symm

@[simp] theorem circleProductCrossEquiv_apply (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    circleProductCrossEquiv X n a =
      circleSectionHomology X (n + 1) a.1 + positiveCircleCross X n a.2 :=
  circleProductHomologyEquiv_symm_eq_section_add_cross X n a

variable {X} {Y : Type} [TopologicalSpace Y]

/-- The actual positive-circle cross product is natural in the other factor. -/
theorem positiveCircleCross_naturality (f : C(X, Y)) (n : ℕ) (b : SingularHomology X n) :
    singularHomologyMap (circleProductMap f) (n + 1) (positiveCircleCross X n b) =
      positiveCircleCross Y n (singularHomologyMap f n b) := by
  calc
    _ = singularHomologyMap (circleProductMap f) (n + 1)
        ((circleProductHomologyEquiv X n).symm (0, b)) :=
      congrArg (singularHomologyMap (circleProductMap f) (n + 1))
        (positiveCircleCross_eq_symm X n b)
    _ = (circleProductHomologyEquiv Y n).symm (0, singularHomologyMap f n b) := by
      simpa only [map_zero] using circleProductHomologyEquiv_symm_naturality f n (0, b)
    _ = _ := (positiveCircleCross_eq_symm Y n (singularHomologyMap f n b)).symm

/-- Naturality of the full actual section-plus-cross-product isomorphism. -/
theorem circleProductCrossEquiv_naturality (f : C(X, Y)) (n : ℕ)
    (a : SingularHomology X (n + 1) × SingularHomology X n) :
    singularHomologyMap (circleProductMap f) (n + 1) (circleProductCrossEquiv X n a) =
      circleProductCrossEquiv Y n
        (singularHomologyMap f (n + 1) a.1, singularHomologyMap f n a.2) :=
  circleProductHomologyEquiv_symm_naturality f n a

end Wikipedia.HopfProblem.PeriodTorusHigherHomology
