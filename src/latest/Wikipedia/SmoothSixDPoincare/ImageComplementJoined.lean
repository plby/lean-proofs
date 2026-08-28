import Wikipedia.SmoothSixDPoincare.ImageComplementHomotopy
import Mathlib.Topology.Homotopy.Path

/-!
# Paths in the complement of a smooth image of codimension at least two

Apply the relative cylinder-avoidance theorem to maps from a single
zero-dimensional point. An ambient path with both endpoints in the actual
complement then yields a path in that same complement with fixed endpoints.
-/

noncomputable section

open Set ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.ImageComplement

variable {E G H K Y N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace K]
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ G K} [J.Boundaryless]
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [CompactSpace Y]
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

theorem joined_of_ambient_joined (g : C(Y, N)) (hg : ContMDiff I J ∞ g)
    (hdim : 1 + Module.finrank ℝ E < Module.finrank ℝ G)
    (x y : domain g) (h : Joined (x : N) (y : N)) : Joined x y := by
  let X := EuclideanSpace ℝ (Fin 0)
  have hh : (ContinuousMap.const X x).Homotopic (ContinuousMap.const X y) :=
    homotopic_of_ambient_homotopic (I := 𝓘(ℝ, X)) g hg
      (by simpa only [X, finrank_euclideanSpace_fin, zero_add] using hdim)
      (ContinuousMap.const X x) (ContinuousMap.const X y) ⟨h.somePath.toHomotopyConst⟩
  exact ContinuousMap.homotopic_const_iff.mp hh

end Wikipedia.SmoothSixDPoincare.ImageComplement
