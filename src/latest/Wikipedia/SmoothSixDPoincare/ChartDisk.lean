import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.ContinuousMap.Basic

/-!
# Closed coordinate disks in a manifold

These disks are constructed inside actual coordinate charts. In particular,
their embeddings are not supplied as sphere-recognition assumptions.
-/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare

variable (E M : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M]

/-- A closed coordinate disk whose whole closed model ball is inside the chart. -/
structure ChartDisk where
  chart : OpenPartialHomeomorph M E
  center : E
  radius : ℝ
  radius_pos : 0 < radius
  closedBall_subset : closedBall center radius ⊆ chart.target

namespace ChartDisk

variable {E M} (d : ChartDisk E M)

def modelMap (x : closedBall (0 : E) 1) : E := d.radius • (x : E) + d.center

theorem modelMap_mem (x : closedBall (0 : E) 1) :
    d.modelMap x ∈ closedBall d.center d.radius := by
  rw [mem_closedBall, dist_eq_norm]
  change ‖d.radius • (x : E) + d.center - d.center‖ ≤ d.radius
  rw [add_sub_cancel_right, norm_smul, Real.norm_eq_abs, abs_of_pos d.radius_pos]
  have hx : ‖(x : E)‖ ≤ 1 := mem_closedBall_zero_iff.mp x.property
  simpa using mul_le_mul_of_nonneg_left hx d.radius_pos.le

theorem modelMap_mem_target (x : closedBall (0 : E) 1) :
    d.modelMap x ∈ d.chart.target := d.closedBall_subset (d.modelMap_mem x)

theorem continuous_modelMap : Continuous d.modelMap :=
  (continuous_const.smul continuous_subtype_val).add continuous_const

/-- The actual continuous map of the closed unit disk into the chart. -/
def map : C(closedBall (0 : E) 1, M) where
  toFun x := d.chart.symm (d.modelMap x)
  continuous_toFun := d.chart.symm.continuousOn.comp_continuous
    d.continuous_modelMap d.modelMap_mem_target

theorem map_injective : Function.Injective d.map := by
  intro x y h
  have hh := d.chart.symm.injOn (d.modelMap_mem_target x) (d.modelMap_mem_target y) h
  have hs : d.radius • (x : E) = d.radius • (y : E) := add_right_cancel hh
  apply Subtype.ext
  simpa only [smul_smul, inv_mul_cancel₀ d.radius_pos.ne', one_smul] using
    congrArg (fun z : E => d.radius⁻¹ • z) hs

theorem map_isClosedEmbedding [FiniteDimensional ℝ E] [T2Space M] :
    IsClosedEmbedding d.map := d.map.continuous.isClosedEmbedding d.map_injective

@[simp] theorem map_zero : d.map ⟨0, by simp⟩ = d.chart.symm d.center := by
  simp [map, modelMap]

/-- The open coordinate ball inside the closed coordinate disk. -/
def core : Set M := d.chart.source ∩ d.chart ⁻¹' ball d.center d.radius

omit [NormedSpace ℝ E] in
theorem isOpen_core : IsOpen d.core := d.chart.isOpen_inter_preimage isOpen_ball

theorem core_subset_range : d.core ⊆ range d.map := by
  rintro p ⟨hp, hball⟩
  let x : E := d.radius⁻¹ • (d.chart p - d.center)
  have hx : x ∈ closedBall (0 : E) 1 := by
    rw [mem_closedBall_zero_iff]
    dsimp [x]
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos d.radius_pos]
    have hd : ‖d.chart p - d.center‖ ≤ d.radius := by
      exact (mem_ball_iff_norm.mp hball).le
    calc
      d.radius⁻¹ * ‖d.chart p - d.center‖ ≤ d.radius⁻¹ * d.radius :=
        mul_le_mul_of_nonneg_left hd (inv_nonneg.mpr d.radius_pos.le)
      _ = 1 := inv_mul_cancel₀ d.radius_pos.ne'
  refine ⟨⟨x, hx⟩, ?_⟩
  change d.chart.symm (d.radius • x + d.center) = p
  rw [show d.radius • x = d.chart p - d.center from
    smul_inv_smul₀ d.radius_pos.ne' (d.chart p - d.center), sub_add_cancel]
  exact d.chart.left_inv hp

end ChartDisk

variable [ChartedSpace E M]

/-- Every neighborhood of a manifold point contains a closed coordinate disk
centered at that point. Its open core is a neighborhood of the point. -/
theorem exists_chartDisk (p : M) {U : Set M} (hU : IsOpen U) (hp : p ∈ U) :
    ∃ d : ChartDisk E M,
      d.chart = chartAt E p ∧ d.center = chartAt E p p ∧
      d.map ⟨0, by simp⟩ = p ∧ p ∈ d.core ∧ range d.map ⊆ U := by
  let e := chartAt E p
  have hep : p ∈ e.source := mem_chart_source E p
  have ht : e p ∈ e.target ∩ e.symm ⁻¹' U :=
    ⟨e.map_source hep, by simpa only [mem_preimage, e.left_inv hep] using hp⟩
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp
    ((e.isOpen_inter_preimage_symm hU).mem_nhds ht)
  let d : ChartDisk E M := ⟨e, e p, r, hr, fun _ h => (hsub h).1⟩
  refine ⟨d, rfl, rfl, ?_, ?_, ?_⟩
  · exact (d.map_zero).trans (e.left_inv hep)
  · exact ⟨hep, by simpa [d] using hr⟩
  · rintro _ ⟨x, rfl⟩
    exact (hsub (d.modelMap_mem x)).2

/-- Distinct manifold points admit disjoint embedded closed coordinate disks. -/
theorem exists_disjoint_chartDisks [T2Space M] {p q : M} (hpq : p ≠ q) :
    ∃ d₁ d₂ : ChartDisk E M,
      p ∈ d₁.core ∧ q ∈ d₂.core ∧ Disjoint (range d₁.map) (range d₂.map) := by
  obtain ⟨U, V, hU, hV, hp, hq, hUV⟩ := t2_separation hpq
  obtain ⟨d₁, _, _, _, hp₁, hd₁⟩ := exists_chartDisk E M p hU hp
  obtain ⟨d₂, _, _, _, hq₂, hd₂⟩ := exists_chartDisk E M q hV hq
  exact ⟨d₁, d₂, hp₁, hq₂, hUV.mono hd₁ hd₂⟩

end Wikipedia.SmoothSixDPoincare
