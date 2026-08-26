import ErdosProblems.Erdos633b.PointwiseEdgeCancellation

/-! Integrating actual edge indicators with Hausdorff length proves the
finite weighted boundary identity, with no edge-to-edge assumption and no
regularity assumption on the direction weight. -/

namespace Erdos633b

open MeasureTheory

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

namespace Triangle

theorem edgeWeightAt_integrable (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (w : Real.Angle → ℝ) :
    Integrable (S.edgeWeightAt o u w) edgeLengthMeasure :=
  integrable_finsetSum _ (fun j _ =>
    S.openEdge_integrable_indicator j (w (S.positiveEdgeDirection o u j)))

theorem integral_edgeWeightAt (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    (u : Plane) (w : Real.Angle → ℝ) :
    (∫ p, S.edgeWeightAt o u w p ∂edgeLengthMeasure) =
      ∑ j : Fin 3, S.side j * w (S.positiveEdgeDirection o u j) := by
  unfold edgeWeightAt
  rw [integral_finsetSum _ (fun j _ =>
    S.openEdge_integrable_indicator j (w (S.positiveEdgeDirection o u j)))]
  simp only [S.integral_openEdge_indicator]

end Triangle
namespace Tiling

theorem edgeWeightAt_cancellation_ae {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (w : Real.Angle → ℝ) (hw : ∀ x, w (x + (Real.pi : Real.Angle)) = -w x) :
    (fun p => ∑ a : Fin n, (d.tile.move (d.place a)).edgeWeightAt o u w p) =ᵐ[edgeLengthMeasure]
      T.edgeWeightAt o u w := by
  have hv := measure_eq_zero_iff_ae_notMem.mp (d.vertices_finite.measure_zero edgeLengthMeasure)
  filter_upwards [hv] with p hp
  exact d.edgeWeightAt_cancellation o hu w hw hp

theorem oriented_edge_length_cancellation {T : Triangle} {n : ℕ} (d : Tiling T n)
    (o : Orientation ℝ Plane (Fin 2)) {u : Plane} (hu : u ≠ 0)
    (w : Real.Angle → ℝ) (hw : ∀ x, w (x + (Real.pi : Real.Angle)) = -w x) :
    (∑ a : Fin n, ∑ j : Fin 3,
      d.tile.side j * w ((d.tile.move (d.place a)).positiveEdgeDirection o u j)) =
        ∑ j : Fin 3, T.side j * w (T.positiveEdgeDirection o u j) := by
  have h := integral_congr_ae (d.edgeWeightAt_cancellation_ae o hu w hw)
  rw [integral_finsetSum _ (fun a _ =>
    (d.tile.move (d.place a)).edgeWeightAt_integrable o u w)] at h
  simpa only [Triangle.integral_edgeWeightAt, Triangle.side_move] using h

end Tiling
end Erdos633b
