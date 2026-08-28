import Wikipedia.HopfProblem.ThreefoldHomologyTopCohomologyAlgebra
import Wikipedia.HopfProblem.ThreefoldHomologyFifthKernel
import Wikipedia.HopfProblem.ThreefoldHomologyFreeProducts
import Mathlib.Algebra.Module.Torsion.Pi

/-!
# Actual fifth homology is free, before evaluating its remaining kernel

Each of the original three boundary monodromies acts identically on
fourth homology of the genuine fibre four-torus.  The original fibre map
in degree four is therefore injective, and the actual Wang sequence
proves that fourth homology of each overlap is torsion-free and free.

The actual fifth homology of the constructed threefold embeds, by its
genuine connecting map, in the product of these three groups.  This
proves its freeness without assuming a value for any remaining
attachment map, its rank, or any Poincaré-duality statement.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopCohomology

open SingularMayerVietoris MappingTorusHomology PeriodTorusHigherHomology
open ThreefoldOverlapMappingTorus TopDegree FifthDegree Finiteness
open ThreefoldHomologyTopCohomologyAlgebra

/-- The actual top fibre class injects into every original boundary. -/
theorem boundaryFibre_four_injective (i : Puncture) :
    Function.Injective (fibreHomologyMap (monodromy i) 4) := by
  apply LinearMap.ker_eq_bot.mp
  rw [← wang_exact_at_fibre]
  simp only [wangDifference, Algebra.difference, boundaryMonodromy_four_identity,
    sub_self, LinearMap.range_zero]

/-- The actual fourth boundary group has no integral torsion. -/
theorem boundaryHomology_four_torsionFree (i : Puncture) :
    Module.IsTorsionFree ℤ (SingularHomology (Boundary i) 4) := by
  have := realTorus_homology_torsionFree 4
  have := realTorus_homology_torsionFree 3
  exact torsionFree_of_injective_exact
    (fibreHomologyMap (monodromy i) 4) (wangBoundary (monodromy i) 3)
    (boundaryFibre_four_injective i)
    (ThreefoldHomologyFinitenessMappingTorus.fibre_wang_exact (monodromy i) 3)

theorem boundaryHomology_four_free (i : Puncture) :
    Module.Free ℤ (SingularHomology (Boundary i) 4) := by
  have := ThreefoldHomologyFinitenessMappingTorus.homology_finite (monodromy i) 4
  have := boundaryHomology_four_torsionFree i
  infer_instance

/-- Freeness is transported through the proved full-overlap equivalence. -/
theorem overlapHomology_four_free (i : Puncture) :
    Module.Free ℤ (SingularHomology (RegularOverlap i) 4) := by
  have := boundaryHomology_four_free i
  exact Module.Free.of_equiv (overlapHomologyEquiv i 4).symm

theorem overlapHomology_four_torsionFree (i : Puncture) :
    Module.IsTorsionFree ℤ (SingularHomology (RegularOverlap i) 4) := by
  have := overlapHomology_four_free i
  infer_instance

/-- The product is free for the original integer action in the actual
star sequence, not just for a separately chosen product action. -/
theorem starOverlapHomology_four_free : Module.Free ℤ (StarOverlapHomology 4) := by
  have (i : Puncture) := overlapHomology_four_free i
  exact ThreefoldHomologyFreeProducts.free_pi_int
    (fun i : Puncture => SingularHomology (RegularOverlap i) 4)

theorem starOverlapHomology_four_torsionFree :
    Module.IsTorsionFree ℤ (StarOverlapHomology 4) := by
  have := starOverlapHomology_four_free
  infer_instance

/-- Fifth homology has no torsion, independently of its remaining rank
calculation, because the original connecting map is injective. -/
theorem homologyFive_torsionFree : Module.IsTorsionFree ℤ (SingularHomology Space 5) := by
  have := starOverlapHomology_four_torsionFree
  exact Function.Injective.moduleIsTorsionFree
    (starConnectingHomomorphism 4) connecting_four_injective
    (fun r a => (starConnectingHomomorphism 4).map_smul r a)

theorem homologyFive_free : Module.Free ℤ (SingularHomology Space 5) := by
  have := homologyFive_torsionFree
  have := homology_finite 5
  infer_instance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.TopCohomology
