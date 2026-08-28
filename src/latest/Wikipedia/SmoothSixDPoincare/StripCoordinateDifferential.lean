import Wikipedia.SmoothSixDPoincare.StripNormalData
import Wikipedia.SmoothSixDPoincare.StripNormalQuotient

/-!
# The actual differential of a strip in its retained sheet chart

The retained center identity gives a full straight-center germ in sheet
coordinates. The chart derivative factors the native strip derivative, and
the transverse coordinate derivative remains nonzero at every center point.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.StripNormalData

variable {A B E M : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {S : Set M} {k : (ℝ × ℝ) → M} (d : StripNormalData A B (E := E) S k)

def coordinateMap : (ℝ × ℝ) → StripCoordinates.Space A B := d.chart.symm ∘ k

theorem center_mem_target {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    k (t, 0) ∈ d.chart.target := by
  rw [d.center t]
  exact d.chart.map_source' (d.line ht)

theorem coordinate_center_germ {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    (fun s : ℝ => d.coordinateMap (s, 0)) =ᶠ[𝓝 t] StripCoordinates.center := by
  have hc : Continuous (StripCoordinates.center : ℝ → StripCoordinates.Space A B) :=
    (continuous_id.prodMk continuous_const).prodMk continuous_const
  filter_upwards [hc.continuousAt.preimage_mem_nhds
    (d.chart.open_source.mem_nhds (d.line ht))] with s hs
  change d.chart.invFun (k (s, 0)) = StripCoordinates.center s
  rw [d.center s, d.chart.left_inv' hs]

theorem coordinate_center {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    d.coordinateMap (t, 0) = StripCoordinates.center t :=
  (d.coordinate_center_germ ht).eq_of_nhds

theorem contDiffAt_coordinateMap {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    ContDiffAt ℝ ∞ d.coordinateMap (t, 0) :=
  ((d.chart.contMDiffOn_invFun.contMDiffAt
    (d.chart.open_target.mem_nhds (d.center_mem_target ht))).comp (t, 0) hk).contDiffAt

theorem horizontal_coordinateDerivative {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    fderiv ℝ d.coordinateMap (t, 0) (1, 0) = StripCoordinates.center 1 :=
  StripCoordinates.horizontal_derivative_of_center_germ
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp)) (d.coordinate_center_germ ht)

theorem normal_coordinateDerivative_nonzero {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    (fderiv ℝ d.coordinateMap (t, 0) (0, 1)).2 ≠ 0 := by
  rw [← StripCoordinates.normalDerivative_eq_snd_fderiv
    ((d.contDiffAt_coordinateMap ht hk).differentiableAt (by simp))]
  exact d.normal_nonzero t ht

/-- The actual native strip differential factors through its retained coordinate differential. -/
theorem native_derivative_factor {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hk : ContMDiffAt 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ k (t, 0)) :
    mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) k (t, 0) =
      (mfderiv 𝓘(ℝ, StripCoordinates.Space A B) 𝓘(ℝ, E) d.chart
        (StripCoordinates.center t)).comp (fderiv ℝ d.coordinateMap (t, 0)) := by
  have hcoords := d.contDiffAt_coordinateMap ht hk
  have heq : (d.chart ∘ d.coordinateMap) =ᶠ[𝓝 (t, 0)] k := by
    filter_upwards [hk.continuousAt.preimage_mem_nhds
      (d.chart.open_target.mem_nhds (d.center_mem_target ht))] with p hp
    change d.chart (d.chart.invFun (k p)) = k p
    exact d.chart.right_inv' hp
  have hcsource : d.coordinateMap (t, 0) ∈ d.chart.source := by
    rw [d.coordinate_center ht]
    exact d.line ht
  rw [← heq.mfderiv_eq, mfderiv_comp (t, 0)
    (d.chart.mdifferentiableAt (by simp) hcsource)
    (hcoords.contMDiffAt.mdifferentiableAt (by simp)),
    d.coordinate_center ht, mfderiv_eq_fderiv]
  rfl

end Wikipedia.SmoothSixDPoincare.StripNormalData
