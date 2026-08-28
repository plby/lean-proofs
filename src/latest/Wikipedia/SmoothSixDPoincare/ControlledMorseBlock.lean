import Wikipedia.SmoothSixDPoincare.MorseDescentField

/-!
# Choosing a handle block inside a prescribed field neighborhood

The closed coordinate block can be made small enough that the global
adapted field agrees with the exact Morse-coordinate field on an open
neighborhood of the whole block, including all its boundary faces.
-/

noncomputable section

open Set Metric Manifold Filter
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]
  {f : M → ℝ} {p : M} (c : SignedMorseChart (E := E) f p)

open Classical in
/-- A closed product block fits inside any prescribed open neighborhood of the critical point. -/
theorem exists_closed_productBlock_in {W : Set M} (hW : IsOpen W) (hpW : p ∈ W) :
    ∃ r > (0 : ℝ),
      closedBall (0 : c.NegativeCoordinates) r ×ˢ closedBall (0 : c.PositiveCoordinates) r ⊆
        c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  let e := c.splitChart.toOpenPartialHomeomorph
  have hzero : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target := by
    rw [← c.splitChart_center]
    exact e.map_source c.splitChart_mem_source
  have hinv : e.symm 0 = p := by
    rw [← c.splitChart_center]
    exact e.left_inv c.splitChart_mem_source
  have hmem : (0 : c.NegativeCoordinates × c.PositiveCoordinates) ∈ e.target ∩ e.symm ⁻¹' W :=
    ⟨hzero, by simpa only [mem_preimage, hinv] using hpW⟩
  obtain ⟨r, hr, hsub⟩ := nhds_basis_closedBall.mem_iff.mp
    ((e.isOpen_inter_preimage_symm hW).mem_nhds hmem)
  refine ⟨r, hr, ?_⟩
  rw [closedBall_prod_same]
  exact hsub

open Classical in
/-- Agreement near the critical point yields a full closed handle block inside an open agreement
neighborhood; the radius is in the convention used by `attachingHandleMap`. -/
theorem exists_fieldCompatibleBlock (V : (x : M) → TangentSpace 𝓘(ℝ, E) x)
    (heq : ∀ᶠ x in 𝓝 p, V x = c.descentField x) :
    ∃ ρ > (0 : ℝ), ∃ W : Set M, IsOpen W ∧ p ∈ W ∧
      (∀ x ∈ W, V x = c.descentField x) ∧
      closedBall (0 : c.NegativeCoordinates) (2 * ρ) ×ˢ
        closedBall (0 : c.PositiveCoordinates) (2 * ρ) ⊆
          c.splitChart.target ∩ c.splitChart.symm ⁻¹' W := by
  obtain ⟨W, hWeq, hW, hpW⟩ := mem_nhds_iff.mp heq
  obtain ⟨r, hr, hblock⟩ := c.exists_closed_productBlock_in hW hpW
  refine ⟨r / 2, half_pos hr, W, hW, hpW, hWeq, ?_⟩
  rw [show 2 * (r / 2) = r by ring]
  exact hblock

end Wikipedia.SmoothSixDPoincare.ManifoldMorse.SignedMorseChart
