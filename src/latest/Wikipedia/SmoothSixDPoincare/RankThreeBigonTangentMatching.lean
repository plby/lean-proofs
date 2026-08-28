import Wikipedia.SmoothSixDPoincare.RankThreeBigonTangentChart
import Wikipedia.SmoothSixDPoincare.RetimedSheetTransition

/-! # Full tangent matching for the unequal-dimensional native Whitney sheets -/

noncomputable section

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.TubularBigon.RankThreeTangentAdaptedChart

open WhitneyPairModel (bigon lowerBoundaryArc upperBoundaryArc halfTimeDerivative
  halfTimeDerivative_apply)
open RankThreeWhitneyModel FrameField

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M} {h : ℝ}
  {k : CleanStripPatch (E := E) S T a k₀ k₁}
  {l : CleanStripPatch (E := E) T S b l₀ l₁}
  {tube : TubularBigon (E := E) S T a b k.map l.map h 3}
  {d : StripNormalData Lower (EuclideanSpace ℝ (Fin 3)) (E := E) S k.map}
  {e : StripNormalData Upper (EuclideanSpace ℝ (Fin 2)) (E := E) T l.map}
  (c : RankThreeTangentAdaptedChart tube d e)

theorem lower_model_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0))).comp
      firstSheetDerivative = (d.sheetDifferential tube.chart t).comp halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : d.sheetDifferential tube.chart t (v.1 / 2, 0) = ((v.1, 0), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2), tube.lower_sheetDifferential_arc d ht]
    ext <;> simp [smul_eq_mul]
  change shearedBlock _ _ (firstSheetDerivative v) =
    d.sheetDifferential tube.chart t (halfTimeDerivative v)
  rw [halfTimeDerivative_apply]
  calc
    shearedBlock _ _ (firstSheetDerivative v) =
        shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0)) ((v.1, 0), 0) +
          shearedBlock (c.base (2 * t - 1, 0)) (c.normal (2 * t - 1, 0)) (0, (v.2, 0)) := by
      rw [← map_add]
      congr 1
      simp only [firstSheetDerivative_apply, Prod.mk_add_mk, add_zero, zero_add]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, 0) +
        d.sheetDifferential tube.chart t (0, v.2) := by
      rw [shearedBlock_horizontal, c.lower_transverse t ht, harc]
    _ = d.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

theorem upper_model_tangent {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (shearedBlock (c.base (upperBoundaryArc h t)) (c.normal (upperBoundaryArc h t))).comp
      (secondSheetDerivative h (2 * t - 1)) =
        (e.sheetDifferential tube.chart t).comp halfTimeDerivative := by
  apply ContinuousLinearMap.ext
  intro v
  have harc : e.sheetDifferential tube.chart t (v.1 / 2, 0) =
      ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) := by
    rw [IntersectionCoordinates.map_first_axis _ (v.1 / 2), tube.upper_sheetDifferential_arc e ht]
    ext <;> simp [smul_eq_mul]
    ring
  change shearedBlock _ _ (secondSheetDerivative h (2 * t - 1) v) =
    e.sheetDifferential tube.chart t (halfTimeDerivative v)
  rw [halfTimeDerivative_apply]
  calc
    shearedBlock _ _ (secondSheetDerivative h (2 * t - 1) v) =
        shearedBlock (c.base (upperBoundaryArc h t)) (c.normal (upperBoundaryArc h t))
          ((v.1, (-2 * h * (2 * t - 1)) * v.1), 0) +
        shearedBlock (c.base (upperBoundaryArc h t)) (c.normal (upperBoundaryArc h t))
          (0, (0, v.2)) := by
      rw [← map_add]
      congr 1
      simp only [secondSheetDerivative_apply, Prod.mk_add_mk, add_zero, zero_add]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, 0) +
        e.sheetDifferential tube.chart t (0, v.2) := by
      rw [shearedBlock_horizontal, c.upper_transverse t ht, harc]
    _ = e.sheetDifferential tube.chart t (v.1 / 2, v.2) := by
      rw [← map_add]
      congr 1
      simp

/-- The actual lower model-sheet transition has the full original sheet derivative. -/
theorem hasFDerivAt_lower_model_transition {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt ((tube.chart.symm ∘ c.chart) ∘ firstSheet)
      ((d.sheetDifferential tube.chart t).comp halfTimeDerivative) (2 * t - 1, 0) := by
  have hd := (c.transition_derivative (2 * t - 1, 0)
    (tube.lowerBoundaryArc_mem_bigon ht)).comp (2 * t - 1, (0 : Lower))
      (hasFDerivAt_firstSheet (2 * t - 1, 0))
  rwa [c.lower_model_tangent ht] at hd

/-- The actual upper model-sheet transition likewise has the full original derivative. -/
theorem hasFDerivAt_upper_model_transition {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    HasFDerivAt ((tube.chart.symm ∘ c.chart) ∘ secondSheet h)
      ((e.sheetDifferential tube.chart t).comp halfTimeDerivative) (2 * t - 1, 0) := by
  have hd := (c.transition_derivative (upperBoundaryArc h t)
    (tube.upperBoundaryArc_mem_bigon ht)).comp (2 * t - 1, (0 : Upper))
      (hasFDerivAt_secondSheet h (2 * t - 1, 0))
  rwa [c.upper_model_tangent ht] at hd

end Wikipedia.SmoothSixDPoincare.TubularBigon.RankThreeTangentAdaptedChart
