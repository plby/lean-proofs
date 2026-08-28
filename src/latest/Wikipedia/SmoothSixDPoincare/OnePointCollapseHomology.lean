import Wikipedia.SmoothSixDPoincare.OnePointCollapseCover
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# Actual homology of the one-point target through its two-chart cover

The connecting map followed by original radial normalization identifies
positive-dimensional overlap homology with compactification homology one
degree higher. The identification retains the actual connecting map.
-/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare.OnePointCover

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.CuspCentralHomology

variable {N : Type} [NormedAddCommGroup N] [NormedSpace ℝ N]

def overlapHomologyEquiv (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularHomology (sphere (0 : N) 1) k ≃ₗ[ℤ]
      SingularHomology ↥(oldPatch (N := N) ∩ finitePatch) k :=
  homotopyEquivHomologyEquiv (overlapSphereEquiv r hr) k

def sphereConnecting (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularHomology (OnePoint N) (k + 1) →ₗ[ℤ]
      SingularHomology (sphere (0 : N) 1) k :=
  (overlapHomologyEquiv r hr k).symm.toLinearMap.comp
    (connectingHomomorphism oldPatch finitePatch oldPatch_open finitePatch_open cover k)

variable [FiniteDimensional ℝ N]

theorem sphereConnecting_injective (r : ℝ) (hr : 0 < r) (k : ℕ) :
    Function.Injective (sphereConnecting (N := N) r hr k) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  have hi : Function.Injective
      (connectingHomomorphism (oldPatch (N := N)) finitePatch
        oldPatch_open finitePatch_open cover k) :=
    contractibleCoverConnecting_injective (oldPatch (N := N)) finitePatch
      oldPatch_open finitePatch_open cover k
  exact (overlapHomologyEquiv (N := N) r hr k).symm.injective.comp hi

/-- The actual target homology isomorphism, in ambient degrees at least two. -/
def sphereHomologyEquiv (r : ℝ) (hr : 0 < r) (k : ℕ) :
    SingularHomology (OnePoint N) (k + 2) ≃ₗ[ℤ]
      SingularHomology (sphere (0 : N) 1) (k + 1) := by
  let : ContractibleSpace (oldPatch (N := N)) := oldPatch_contractible
  let : ContractibleSpace (finitePatch (N := N)) := finitePatch_contractible
  exact (contractibleCoverHomologyHigherEquiv oldPatch finitePatch
    oldPatch_open finitePatch_open cover k).trans (overlapHomologyEquiv r hr (k + 1)).symm

theorem sphereHomologyEquiv_apply (r : ℝ) (hr : 0 < r) (k : ℕ)
    (a : SingularHomology (OnePoint N) (k + 2)) :
    sphereHomologyEquiv r hr k a = sphereConnecting r hr (k + 1) a := rfl

end Wikipedia.SmoothSixDPoincare.OnePointCover
