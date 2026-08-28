import Wikipedia.HopfProblem.CuspCentralCohomologyCoordinatesFixed
import Wikipedia.HopfProblem.CuspCentralCohomologyTransport

/-!
# The integral image of actual specialization in period coordinates

The native cohomology pullback on an actual marked fibre has exactly
the displayed integral coefficient forms in degrees one, two and three.
The marking is the pullback of the actual fibre homeomorphism.  The
coordinate formulas follow from genuine singular-cochain pullback, its
proved evaluation naturality, and the actual homology markings.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction SingularCohomologyFree PeriodTorusHigherHomology
open CuspCentralHomology.SpecializationModel

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))
    {X : Type} [TopologicalSpace X] (E : ProductTorus 4 ≃ₜ X)
    (f : C(X, QuotientCentralFibre C r))
    (h : (markedCollapse C r hr).Homotopic (f.comp (E : C(ProductTorus 4, X))))

include hC h

/-- The first image is the full integral span of `γ,u`. -/
theorem markedSpecializationH1_mem_range_iff (a : SingularCohomology X 1) :
    a ∈ LinearMap.range (singularCohomologyPullback f 1) ↔
      ∃ b c : ℤ, coordinateTorusH1CohomologyCoordinates
        (homeomorphCohomologyEquiv E 1 a) = ![b, c, 0, 0] := by
  rw [markedSpecialization_mem_range_iff C r hr hC E f h 1,
    mem_singularCohomologyFixed_iff, coordinateTorusH1_pullback_fixed_iff_exists]

/-- In the order `γu,γw,γδ,uw,uδ,wδ`, the second image is the
full integral span of `γu,γδ,uw,γw-uδ`. -/
theorem markedSpecializationH2_mem_range_iff (a : SingularCohomology X 2) :
    a ∈ LinearMap.range (singularCohomologyPullback f 2) ↔
      ∃ b c d e : ℤ, coordinateTorusH2CohomologyCoordinates
        (homeomorphCohomologyEquiv E 2 a) = ![b, c, d, e, -c, 0] := by
  rw [markedSpecialization_mem_range_iff C r hr hC E f h 2,
    mem_singularCohomologyFixed_iff, coordinateTorusH2_pullback_fixed_iff_exists]

/-- The third image is the full integral span of `γuw,γuδ`. -/
theorem markedSpecializationH3_mem_range_iff (a : SingularCohomology X 3) :
    a ∈ LinearMap.range (singularCohomologyPullback f 3) ↔
      ∃ b c : ℤ, coordinateTorusH3CohomologyCoordinates
        (homeomorphCohomologyEquiv E 3 a) = ![b, c, 0, 0] := by
  rw [markedSpecialization_mem_range_iff C r hr hC E f h 3,
    mem_singularCohomologyFixed_iff, coordinateTorusH3_pullback_fixed_iff_exists]

end Wikipedia.HopfProblem.CuspCentralCohomology
