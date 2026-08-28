import Wikipedia.SmoothSixDPoincare.ChartDisk

/-!
# The boundary and complement of a coordinate disk
-/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare.ChartDisk

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] (d : ChartDisk E M)

theorem map_mem_core_iff (x : closedBall (0 : E) 1) :
    d.map x ∈ d.core ↔ ‖(x : E)‖ < 1 := by
  have ht := d.modelMap_mem_target x
  have hs : d.map x ∈ d.chart.source := d.chart.symm.map_source ht
  change (d.map x ∈ d.chart.source ∧
    d.chart (d.chart.symm (d.modelMap x)) ∈ ball d.center d.radius) ↔ _
  rw [and_iff_right hs, d.chart.right_inv ht, mem_ball_iff_norm]
  change ‖d.radius • (x : E) + d.center - d.center‖ < d.radius ↔ _
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos]
  simpa only [mul_one] using
    (mul_lt_mul_iff_right₀ d.radius_pos :
      d.radius * ‖(x : E)‖ < d.radius * 1 ↔ ‖(x : E)‖ < 1)

/-- The actual unit boundary sphere mapped into the manifold. -/
def boundaryMap : C(sphere (0 : E) 1, M) :=
  d.map.comp ⟨fun x => ⟨x, sphere_subset_closedBall x.property⟩,
    continuous_subtype_val.subtype_mk _⟩

theorem boundaryMap_injective : Function.Injective d.boundaryMap := by
  intro x y h
  have hh := d.map_injective h
  apply Subtype.ext
  exact congrArg (fun z : closedBall (0 : E) 1 => (z : E)) hh

theorem boundaryMap_not_mem_core (x : sphere (0 : E) 1) :
    d.boundaryMap x ∉ d.core := by
  rw [show d.boundaryMap x = d.map ⟨x, sphere_subset_closedBall x.property⟩ from rfl,
    d.map_mem_core_iff]
  simp [mem_sphere_zero_iff_norm.mp x.property]

theorem boundaryMap_mem_range (x : sphere (0 : E) 1) :
    d.boundaryMap x ∈ range d.map :=
  ⟨⟨x, sphere_subset_closedBall x.property⟩, rfl⟩

theorem range_boundaryMap : range d.boundaryMap = range d.map \ d.core := by
  apply Set.ext
  intro p
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨d.boundaryMap_mem_range x, d.boundaryMap_not_mem_core x⟩
  · rintro ⟨⟨x, rfl⟩, hx⟩
    have hle : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
    have hge : 1 ≤ ‖(x : E)‖ := not_lt.mp (fun h => hx ((d.map_mem_core_iff x).mpr h))
    exact ⟨⟨x, mem_sphere_zero_iff_norm.mpr (hle.antisymm hge)⟩, rfl⟩

theorem boundaryMap_isClosedEmbedding [FiniteDimensional ℝ E] [T2Space M] :
    IsClosedEmbedding d.boundaryMap :=
  d.boundaryMap.continuous.isClosedEmbedding d.boundaryMap_injective

end Wikipedia.SmoothSixDPoincare.ChartDisk
