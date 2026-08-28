import Wikipedia.HopfProblem.DegreeCollapseMiddleTailDerivative

/-!
# Exact native-coordinate differentials of both smooth middle spheres

The original split chart sends the retained germs to their complementary
linear coordinate planes. Differentiation retains the actual source-tail
isomorphism and the original positive handle radius.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap Topology
open scoped ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [Nonempty M] (D : SeparatedSystem E M)

def negativePlane (p : D.MiddleLabel) : Hemisphere.Ambient 3 →L[ℝ]
    (D.windows.data p.val).chart.NegativeCoordinates × (D.windows.data p.val).chart.PositiveCoordinates :=
  ((D.windows.data p.val).radius • (D.negativeLinear p.val p.property).toContinuousLinearMap).prod 0

def positivePlane (p : D.MiddleLabel) : Hemisphere.Ambient 3 →L[ℝ]
    (D.windows.data p.val).chart.NegativeCoordinates × (D.windows.data p.val).chart.PositiveCoordinates :=
  (0 : Hemisphere.Ambient 3 →L[ℝ] (D.windows.data p.val).chart.NegativeCoordinates).prod
    ((D.windows.data p.val).radius • (D.positiveLinear p.val p.property).toContinuousLinearMap)

theorem negativePlane_apply (p : D.MiddleLabel) (u : Hemisphere.Ambient 3) :
    D.negativePlane p u = ((D.windows.data p.val).radius • D.negativeLinear p.val p.property u, 0) := rfl

theorem positivePlane_apply (p : D.MiddleLabel) (u : Hemisphere.Ambient 3) :
    D.positivePlane p u = (0, (D.windows.data p.val).radius • D.positiveLinear p.val p.property u) := rfl

namespace SmoothMiddleFamilies

variable {D} (F : D.SmoothMiddleFamilies)

theorem descending_split_germ (p : D.MiddleLabel) :
    ((D.windows.data p.val).chart.splitChart ∘ F.descending p) =ᶠ[𝓝 middlePole]
      (D.negativePlane p ∘ Hemisphere.tail) := by
  filter_upwards [F.descending_core_germ p] with x hx
  change (D.windows.data p.val).chart.splitChart (F.descending p x) = _
  rw [hx]
  exact (D.windows.data p.val).chart.splitChart.right_inv'
    (CoreDisks.negative_target (D.windows.data p.val)
      (StandardDiskCoordinates.disk (D.negativeLinear p.val p.property) (Hemisphere.disk x)))

theorem ascending_split_germ (p : D.MiddleLabel) :
    ((D.windows.data p.val).chart.splitChart ∘ F.ascending p) =ᶠ[𝓝 middlePole]
      (D.positivePlane p ∘ Hemisphere.tail) := by
  filter_upwards [F.ascending_core_germ p] with x hx
  change (D.windows.data p.val).chart.splitChart (F.ascending p x) = _
  rw [hx]
  exact (D.windows.data p.val).chart.splitChart.right_inv'
    (CoreDisks.positive_target (D.windows.data p.val)
      (StandardDiskCoordinates.disk (D.positiveLinear p.val p.property) (Hemisphere.disk x)))

theorem descending_split_derivative (p : D.MiddleLabel) :
    (mfderiv (𝓡 3)
      𝓘(ℝ, (D.windows.data p.val).chart.NegativeCoordinates ×
        (D.windows.data p.val).chart.PositiveCoordinates)
      ((D.windows.data p.val).chart.splitChart ∘ F.descending p) middlePole :
        Hemisphere.Ambient 3 →L[ℝ] _) = (D.negativePlane p).comp tailDerivative := by
  rw [(F.descending_split_germ p).mfderiv_eq]
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 3)
      𝓘(ℝ, (D.windows.data p.val).chart.NegativeCoordinates ×
        (D.windows.data p.val).chart.PositiveCoordinates) ∞ (D.negativePlane p) :=
    (D.negativePlane p).contDiff.contMDiff
  rw [mfderiv_comp middlePole (hs.mdifferentiableAt (by simp))
    (smooth_tail.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, (D.negativePlane p).fderiv]
  rfl

theorem ascending_split_derivative (p : D.MiddleLabel) :
    (mfderiv (𝓡 3)
      𝓘(ℝ, (D.windows.data p.val).chart.NegativeCoordinates ×
        (D.windows.data p.val).chart.PositiveCoordinates)
      ((D.windows.data p.val).chart.splitChart ∘ F.ascending p) middlePole :
        Hemisphere.Ambient 3 →L[ℝ] _) = (D.positivePlane p).comp tailDerivative := by
  rw [(F.ascending_split_germ p).mfderiv_eq]
  have hs : ContMDiff 𝓘(ℝ, Hemisphere.Ambient 3)
      𝓘(ℝ, (D.windows.data p.val).chart.NegativeCoordinates ×
        (D.windows.data p.val).chart.PositiveCoordinates) ∞ (D.positivePlane p) :=
    (D.positivePlane p).contDiff.contMDiff
  rw [mfderiv_comp middlePole (hs.mdifferentiableAt (by simp))
    (smooth_tail.mdifferentiableAt (by simp)), mfderiv_eq_fderiv, (D.positivePlane p).fderiv]
  rfl

end SmoothMiddleFamilies
end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation.MiddleDuality.SeparatedSystem
