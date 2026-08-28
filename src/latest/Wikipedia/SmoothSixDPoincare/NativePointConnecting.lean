import Wikipedia.SmoothSixDPoincare.NativeDegreeNeighborhoodGeometry
import Wikipedia.HopfProblem.CuspCentralHomologySuspensionMayerVietoris
import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleHomotopy

/-!
# The actual single-point connecting map in a native chart

The complement of the original chart center and its constructed open
neighborhood cover the original space. Normalize the actual overlap
connecting class using the original inner sphere. When the punctured
ambient space is contractible this map is injective, and is an isomorphism
above degree one, by the proved contractible-cover sequence.
-/

noncomputable section

open Set Metric Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.NativeNeighborhood

open Wikipedia.HopfProblem.SingularMayerVietoris
  Wikipedia.HopfProblem.PeriodTorusHigherHomology
  Wikipedia.HopfProblem.CuspCentralHomology

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  (x : M) {f : M → F} {L : E ≃L[ℝ] F} {W : Set M}
  (d : NeighborhoodData (f ∘ NativeParametrization.centered (D := E) x) L
    ((NativeParametrization.centered (D := E) x).source ∩
      NativeParametrization.centered (D := E) x ⁻¹' W))

theorem singlePoint_cover : {x}ᶜ ∪ openSet x d = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases h : y = x
  · subst y
    exact Or.inr (center_mem_openSet x d)
  · exact Or.inl h

theorem openSet_contractible : ContractibleSpace (openSet x d) := by
  let : ContractibleSpace (ball (0 : E) d.radius) :=
    (convex_ball (0 : E) d.radius).contractibleSpace ⟨0, by simpa using d.radius_pos⟩
  exact (ChartPuncturedBall.ballHomeomorph
    (NativeParametrization.centered x).toOpenPartialHomeomorph d.radius
    (closedBall_subset_source x d)).symm.contractibleSpace

variable [T1Space M]

def sphereConnecting (k : ℕ) :
    SingularHomology M (k + 1) →ₗ[ℤ] SingularHomology (sphere (0 : E) 1) k :=
  (homotopyEquivHomologyEquiv (overlapSphereEquiv x d) k).symm.toLinearMap.comp
    (connectingHomomorphism {x}ᶜ (openSet x d) isClosed_singleton.isOpen_compl
      (isOpen_openSet x d) (singlePoint_cover x d) k)

variable [ContractibleSpace ({x}ᶜ : Set M)]

theorem sphereConnecting_injective (k : ℕ) : Function.Injective (sphereConnecting x d k) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact (homotopyEquivHomologyEquiv (overlapSphereEquiv x d) k).symm.injective.comp
    (contractibleCoverConnecting_injective {x}ᶜ (openSet x d) isClosed_singleton.isOpen_compl
      (isOpen_openSet x d) (singlePoint_cover x d) k)

def sphereHomologyEquiv (k : ℕ) :
    SingularHomology M (k + 2) ≃ₗ[ℤ] SingularHomology (sphere (0 : E) 1) (k + 1) := by
  let : ContractibleSpace (openSet x d) := openSet_contractible x d
  exact (contractibleCoverHomologyHigherEquiv {x}ᶜ (openSet x d)
    isClosed_singleton.isOpen_compl (isOpen_openSet x d) (singlePoint_cover x d) k).trans
      (homotopyEquivHomologyEquiv (overlapSphereEquiv x d) (k + 1)).symm

theorem sphereHomologyEquiv_apply (k : ℕ) (a : SingularHomology M (k + 2)) :
    sphereHomologyEquiv x d k a = sphereConnecting x d (k + 1) a := rfl

end Wikipedia.SmoothSixDPoincare.LocalDegree.NativeNeighborhood
