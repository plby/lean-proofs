import Wikipedia.NoExoticSixSphere.WhitneySphereScaledChart
import Wikipedia.SmoothSixDPoincare.PartialDiffeomorphRestriction

/-!
# A convex reference chart inside any retained chart about its center

Openness supplies a genuine positive ball. An actual linear dilation and
open source restriction produce a chart whose source is exactly the radius-
three product-norm ball. It contains both embedded reference spheres and
has convex source, without imposing that property on the original chart.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.ProductChartCoordinates

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

theorem exists_convex_reference_chart (h0 : (0 : Vector 3 × Vector 3) ∈ Φ.source) :
    ∃ Ψ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
      (Vector 3 × Vector 3) M ∞,
      Ψ.source = ball (0 : Vector 3 × Vector 3) 3 ∧
      Convex ℝ Ψ.source ∧ closedBall (0 : Vector 3 × Vector 3) 2 ⊆ Ψ.source ∧
      Ψ.target ⊆ Φ.target ∧ Ψ 0 = Φ 0 := by
  obtain ⟨r, hr, hball⟩ := nhds_basis_closedBall.mem_iff.mp (Φ.open_source.mem_nhds h0)
  let δ := r / 4
  have hδ : 0 < δ := div_pos hr (by norm_num)
  let Q := WhitneySphere.scaledChart Φ δ hδ
  have hQ : closedBall (0 : Vector 3 × Vector 3) 3 ⊆ Q.source := by
    intro z hz
    refine ⟨mem_univ _, hball ?_⟩
    change δ • z ∈ closedBall (0 : Vector 3 × Vector 3) r
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hδ]
    have hz' : ‖z‖ ≤ 3 := mem_closedBall_zero_iff.mp hz
    dsimp only [δ]
    nlinarith
  let Ψ := Wikipedia.SmoothSixDPoincare.PartialChart.restrictSource Q
    (isOpen_ball : IsOpen (ball (0 : Vector 3 × Vector 3) 3))
  have hs : Ψ.source = ball (0 : Vector 3 × Vector 3) 3 := by
    change Q.source ∩ ball (0 : Vector 3 × Vector 3) 3 = _
    exact inter_eq_right.mpr (ball_subset_closedBall.trans hQ)
  refine ⟨Ψ, hs, ?_, ?_, ?_, ?_⟩
  · rw [hs]
    exact convex_ball _ _
  · rw [hs]
    exact closedBall_subset_ball (by norm_num)
  · intro x hx
    exact hx.1.1
  · change Φ (δ • (0 : Vector 3 × Vector 3)) = Φ 0
    rw [smul_zero]

end NoExoticSixSphere.ProductChartCoordinates
