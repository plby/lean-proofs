import Wikipedia.HopfProblem.SingularCohomologyFreeFiniteIndex
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyMaps
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyProperties
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyInvariance
import Wikipedia.HopfProblem.EllipticHigherHomologyCoverIndicesLowDegrees

/-!
# Injectivity of the actual elliptic cohomology pullbacks

The proved finite-index images in homology force injectivity of the
native singular-cohomology pullback in degrees zero through four.
Above degree four the actual target cohomology vanishes.  The genuine
central-surface retraction then transfers injectivity to the actual map
from the period torus into the entire filling.  Restricting the period
cover's codomain to the already constructed deck-invariant submodule
retains injectivity; no claim about its index in that submodule is made.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris SingularCohomologyFree

/-- The actual main period cover has injective integral cohomology pullback in every degree. -/
theorem periodCover_cohomology_injective (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Function.Injective
      (singularCohomologyPullback (periodCover j p j.twist (mainTwist_admissible j)) n) := by
  by_cases hn : 4 < n
  · let := surface_cohomology_subsingleton j p hn
    intro a b _
    exact Subsingleton.elim a b
  · let (k : ℕ) : Module.Projective ℤ
        (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) k) :=
      Module.Projective.of_basis
        ((Pi.basisFun ℤ (Fin (ellipticBettiNumber k))).map
          (surfaceHomologyCoordinates j p k).symm)
    apply singularCohomologyPullback_injective_of_finiteIndex
      (periodCover j p j.twist (mainTwist_admissible j)) n
    have hn' : n ≤ 4 := le_of_not_gt hn
    interval_cases n
    · refine ⟨?_⟩
      rw [surfacePeriodCover_h0_range_index]
      exact Nat.one_ne_zero
    · exact surfacePeriodCover_h1_range_finiteIndex j p
    · exact surfacePeriodCover_h2_range_finiteIndex j p
    · exact surfacePeriodCover_h3_range_finiteIndex j p
    · exact surfacePeriodCover_h4_range_finiteIndex j p

/-- The actual period-torus map into the full filling also has injective
native cohomology pullback in every degree. -/
theorem periodTorusIntoFilling_cohomology_injective {j : Kind}
    (D : Equivariant.Data j) (n : ℕ) :
    Function.Injective
      (singularCohomologyPullback
        (periodTorusIntoFilling D j.twist (mainTwist_admissible j)) n) := by
  intro a b hab
  apply (centralSurfaceCohomologyEquiv D n).injective
  apply periodCover_cohomology_injective j D.centralPeriod n
  simpa only [centralSurfaceCohomologyEquiv_periodCover] using hab

/-- Restricting the actual pullback to the genuine deck-invariant
submodule preserves its proved injectivity. -/
theorem periodCoverCohomologyToInvariants_injective (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Function.Injective
      (periodCoverCohomologyToInvariants j p j.twist (mainTwist_admissible j) n) := by
  intro a b hab
  apply periodCover_cohomology_injective j p n
  exact congrArg Subtype.val hab

end Wikipedia.HopfProblem.Elliptic.HigherHomology
