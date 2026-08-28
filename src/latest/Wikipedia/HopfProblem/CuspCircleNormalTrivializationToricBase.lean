import Wikipedia.HopfProblem.RiemannSphere

/-!
# The two actual affine charts of the normal-coordinate product

These are the original Riemann-sphere affine maps times the identity on
the two complex normal coordinates. Their open-embedding and covering
properties let continuity and openness be checked on these literal maps.
-/

noncomputable section

open Set Topology Filter

namespace Wikipedia.HopfProblem.CuspCircleNormalTrivialization

/-- The actual affine base chart times the unchanged normal-coordinate space. -/
def baseProductChart (b : Bool) : (ℂ × (ℂ × ℂ)) → RiemannSphere × (ℂ × ℂ) :=
  Prod.map (RiemannSphere.standardCharts.affineMap b) id

@[simp] theorem baseProductChart_apply (b : Bool) (a : ℂ) (v : ℂ × ℂ) :
    baseProductChart b (a, v) = (RiemannSphere.standardCharts.affineMap b a, v) := rfl

theorem baseProductChart_isOpenEmbedding (b : Bool) : IsOpenEmbedding (baseProductChart b) :=
  (RiemannSphere.standardCharts.affineMap_isOpenEmbedding b).prodMap
    Topology.IsOpenEmbedding.id

/-- Every original product point belongs to one of the two affine charts. -/
theorem baseProductChart_cover (p : RiemannSphere × (ℂ × ℂ)) :
    ∃ b q, baseProductChart b q = p := by
  obtain ⟨a, ha⟩ := RiemannSphere.standardCharts.preferred_mem p.1
  exact ⟨RiemannSphere.standardCharts.preferredChart p.1, (a, p.2),
    Prod.ext ha rfl⟩

/-- Continuity on the product is detected by its two native affine charts. -/
theorem continuous_of_comp_baseProductChart {Y : Type*} [TopologicalSpace Y]
    (f : RiemannSphere × (ℂ × ℂ) → Y)
    (hf : ∀ b, Continuous (f ∘ baseProductChart b)) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  exact (baseProductChart_isOpenEmbedding b).continuousAt_iff.mp (hf b).continuousAt

/-- Openness on the product is detected by the same actual affine charts. -/
theorem isOpenMap_of_comp_baseProductChart {Y : Type*} [TopologicalSpace Y]
    (f : RiemannSphere × (ℂ × ℂ) → Y)
    (hf : ∀ b, IsOpenMap (f ∘ baseProductChart b)) : IsOpenMap f := by
  apply IsOpenMap.of_nhds_le
  intro p
  obtain ⟨b, q, rfl⟩ := baseProductChart_cover p
  calc
    𝓝 (f (baseProductChart b q)) ≤ map (f ∘ baseProductChart b) (𝓝 q) :=
      (hf b).nhds_le q
    _ = map f (𝓝 (baseProductChart b q)) := by
      rw [← Filter.map_map, (baseProductChart_isOpenEmbedding b).map_nhds_eq]

end Wikipedia.HopfProblem.CuspCircleNormalTrivialization
