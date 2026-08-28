import Wikipedia.SmoothSixDPoincare.NativePointConnecting
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Single-point native connecting maps on the original Euclidean sphere

Actual stereographic projection makes the complement of any point a
Euclidean space. Together with the constructed native chart ball, this
discharges the contractibility hypotheses of the source connecting-map
isomorphism, without a homology-orientation assumption.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.SpherePoint

open Wikipedia.HopfProblem.SingularMayerVietoris

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  {n : ℕ} [hdim : Fact (Module.finrank ℝ V = n + 1)]

def punctureHomeomorph (x : sphere (0 : V) 1) :
    ↥({x}ᶜ : Set (sphere (0 : V) 1)) ≃ₜ EuclideanSpace ℝ (Fin n) :=
  (Homeomorph.setCongr (stereographic'_source (n := n) x).symm).trans
    ((stereographic' n x).toHomeomorphSourceTarget.trans
      ((Homeomorph.setCongr (stereographic'_target x)).trans (Homeomorph.Set.univ _)))

include hdim in
theorem puncture_contractible (x : sphere (0 : V) 1) :
    ContractibleSpace ({x}ᶜ : Set (sphere (0 : V) 1)) :=
  (punctureHomeomorph (n := n) x).contractibleSpace

variable {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
  (x : sphere (0 : V) 1) {f : sphere (0 : V) 1 → F}
  {L : EuclideanSpace ℝ (Fin n) ≃L[ℝ] F} {W : Set (sphere (0 : V) 1)}
  (d : LocalDegree.NeighborhoodData
    (f ∘ NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x) L
    ((NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x).source ∩
      NativeParametrization.centered (D := EuclideanSpace ℝ (Fin n)) x ⁻¹' W))

theorem connecting_injective (k : ℕ) :
    Function.Injective (LocalDegree.NativeNeighborhood.sphereConnecting x d k) := by
  let : ContractibleSpace ({x}ᶜ : Set (sphere (0 : V) 1)) := puncture_contractible (n := n) x
  exact LocalDegree.NativeNeighborhood.sphereConnecting_injective x d k

def connectingHomologyEquiv (k : ℕ) :
    SingularHomology (sphere (0 : V) 1) (k + 2) ≃ₗ[ℤ]
      SingularHomology (sphere (0 : EuclideanSpace ℝ (Fin n)) 1) (k + 1) := by
  let : ContractibleSpace ({x}ᶜ : Set (sphere (0 : V) 1)) := puncture_contractible (n := n) x
  exact LocalDegree.NativeNeighborhood.sphereHomologyEquiv x d k

theorem connectingHomologyEquiv_apply (k : ℕ)
    (a : SingularHomology (sphere (0 : V) 1) (k + 2)) :
    connectingHomologyEquiv x d k a =
      LocalDegree.NativeNeighborhood.sphereConnecting x d (k + 1) a :=
  rfl

end Wikipedia.SmoothSixDPoincare.SpherePoint
