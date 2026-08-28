import Wikipedia.NoExoticSixSphere.LocalInverse
import Wikipedia.NoExoticSixSphere.CorankOneChart

/-!
# Actual inverse-function coordinates for a regular Schur residual

The residual itself is the coordinate map. Its genuine source is restricted
to the invertible-leading-block domain, so every inverse-coordinate point
retains that block condition. A residual zero has a small closed ball around
zero inside the actual coordinate target.
-/

noncomputable section

open Set Function Metric
open scoped ContDiff Manifold Topology

namespace NoExoticSixSphere.ResidualCoordinates

open CorankOne

variable {X E F : Type}
  [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure Data (D : X → BlockMap E F) where
  coord : PartialDiffeomorph 𝓘(ℝ, X) 𝓘(ℝ, F) X F ∞
  source_chart : ∀ x ∈ coord.source, D x ∈ chart
  coord_apply : ∀ x, coord x = residual (D x)

theorem exists_data_on (D : X → BlockMap E F) {U : Set X} (hU : IsOpen U)
    (hD : ContDiffOn ℝ ∞ D U) (x : X) (hxU : x ∈ U)
    (hx : D x ∈ chart) (hb : Bijective (fderiv ℝ (fun y ↦ residual (D y)) x)) :
    ∃ d : Data D, x ∈ d.coord.source ∧ d.coord.source ⊆ U := by
  let W := U ∩ D ⁻¹' (chart (E := E) (F := F) : Set (BlockMap E F))
  have hW : IsOpen W := hD.continuousOn.isOpen_inter_preimage hU
    (chart (E := E) (F := F)).isOpen
  have hR : ContDiffOn ℝ ∞ (fun y ↦ residual (D y)) W :=
    contDiffOn_residual.comp (hD.mono inter_subset_left) (fun _ hy ↦ hy.2)
  have hi : (fderiv ℝ (fun y ↦ residual (D y)) x).IsInvertible :=
    ⟨(LinearEquiv.ofBijective _ hb).toContinuousLinearEquiv, rfl⟩
  obtain ⟨c, hcx, hcW, hc⟩ := exists_partialDiffeomorph_of_contDiffOn hW ⟨hxU, hx⟩ hR hi
  exact ⟨⟨c, fun _ hy ↦ (hcW hy).2, fun y ↦ congrFun hc y⟩,
    hcx, fun _ hy ↦ (hcW hy).1⟩

theorem exists_data (D : X → BlockMap E F) (hD : ContDiff ℝ ∞ D) (x : X)
    (hx : D x ∈ chart) (hb : Bijective (fderiv ℝ (fun y ↦ residual (D y)) x)) :
    ∃ d : Data D, x ∈ d.coord.source := by
  obtain ⟨d, hdx, _⟩ := exists_data_on D isOpen_univ hD.contDiffOn x (mem_univ _) hx hb
  exact ⟨d, hdx⟩

variable {D : X → BlockMap E F}

omit [FiniteDimensional ℝ X] in
theorem Data.residual_inverse (d : Data D) {y : F} (hy : y ∈ d.coord.target) :
    residual (D (d.coord.symm y)) = y :=
  (d.coord_apply _).symm.trans (d.coord.toOpenPartialHomeomorph.right_inv hy)

omit [FiniteDimensional ℝ X] in
theorem Data.leading_inverse (d : Data D) {y : F} (hy : y ∈ d.coord.target) :
    (leading (D (d.coord.symm y))).IsInvertible :=
  leading_invertible (d.source_chart _ (d.coord.toOpenPartialHomeomorph.map_target hy))

omit [FiniteDimensional ℝ X] in
theorem Data.inverse_zero (d : Data D) {x : X} (hx : x ∈ d.coord.source)
    (hz : residual (D x) = 0) : d.coord.symm 0 = x := by
  have hc : d.coord x = 0 := (d.coord_apply x).trans hz
  rw [← hc]
  exact d.coord.toOpenPartialHomeomorph.left_inv hx

omit [FiniteDimensional ℝ X] in
theorem Data.exists_radius (d : Data D) {x : X} (hx : x ∈ d.coord.source)
    (hz : residual (D x) = 0) : ∃ ε : ℝ, 0 < ε ∧ closedBall (0 : F) ε ⊆ d.coord.target := by
  have hzero : (0 : F) ∈ d.coord.target := by
    rw [← hz, ← d.coord_apply x]
    exact d.coord.toOpenPartialHomeomorph.map_source hx
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (d.coord.open_target.mem_nhds hzero)
  refine ⟨δ / 2, by linarith, ?_⟩
  intro y hy
  apply hball
  apply Metric.mem_ball.mpr
  exact lt_of_le_of_lt (Metric.mem_closedBall.mp hy) (by linarith)

end NoExoticSixSphere.ResidualCoordinates
