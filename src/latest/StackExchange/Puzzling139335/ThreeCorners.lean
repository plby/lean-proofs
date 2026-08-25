import StackExchange.Puzzling139335.ThreeCorners.Ordered
import StackExchange.Puzzling139335.ThreeCorners.SupportFrames
import StackExchange.Puzzling139335.ThreeCorners.FullGerms
import StackExchange.Puzzling139335.ThreeCorners.AngleBounds

/-!
# Geometric ordering of three full right corners

An actual full square-corner placement normalizes the first corner to the
origin, including its full relative square neighborhood.  The pairwise
bisector inequalities then order the two remaining positively oriented
inward frames, without a boundary-curvature or polygonality assumption.
-/

open Set Metric

namespace Puzzling139335.ThreeCorners

/-- The inverse image of the square center in any actual placement at a
full corner is the corner plus half the sum of its two inward unit rays. -/
theorem symm_center_eq_of_bisector {P : Set Plane} {a : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P a) (h : SupportCorner P a)
    {θ : ℝ} (hθ : h.bisector = outwardBisector θ)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (j : Fin 4)
    (hSubset : e '' P ⊆ unitSquare) (hea : e a = corner j) :
    e.symm squareCenter = a + (1 / 2 : ℝ) • (ray θ + perpRay θ) := by
  rw [hfull.symm_center_eq h e j hSubset hea, hθ, outwardBisector,
    smul_neg, sub_neg_eq_add]

/-- Normalize one of three distinct actual full square-corner types and
order the inward frames at the remaining two.  All corner and neighborhood
information is transported by the same actual affine isometry. -/
theorem exists_normalized_ordered_frames {P : Set Plane} {a b c : Plane}
    (ha : UnitPairs.IsFullSquareCorner P a)
    (hb : UnitPairs.IsFullSquareCorner P b)
    (hc : UnitPairs.IsFullSquareCorner P c)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, ∃ ε : ℝ, ∃ b' c' : Plane, ∃ θ φ : ℝ,
      f a = 0 ∧ 0 < ε ∧ f '' P ⊆ unitSquare ∧
      ball (0 : Plane) ε ∩ unitSquare ⊆ f '' P ∧
      ((b' = f b ∧ c' = f c) ∨ (b' = f c ∧ c' = f b)) ∧
      θ ∈ Icc (Real.pi / 2) Real.pi ∧
      φ ∈ Icc (θ + Real.pi / 2) (3 * Real.pi / 2) ∧
      UnitPairs.IsFullSquareCorner (f '' P) b' ∧
      UnitPairs.IsFullSquareCorner (f '' P) c' ∧
      ∃ hB : SupportCorner (f '' P) b', ∃ hC : SupportCorner (f '' P) c',
        hB.bisector = outwardBisector θ ∧ hC.bisector = outwardBisector φ ∧
        f '' P ⊆ supportCone b' θ ∧ f '' P ⊆ supportCone c' φ := by
  obtain ⟨f, hfa, hSubset, ε, hε, hGerm⟩ := ha.exists_normalized
  have hzero : (0 : Plane) ∈ f '' P := by
    rw [← hfa]
    exact mem_image_of_mem f ha.mem
  have hb0 : f b ≠ 0 := by
    intro hfb
    exact hab (f.injective (hfa.trans hfb.symm))
  have hc0 : f c ≠ 0 := by
    intro hfc
    exact hac (f.injective (hfa.trans hfc.symm))
  have hbc' : f b ≠ f c := fun h => hbc (f.injective h)
  obtain ⟨b', c', θ, φ, horder, hθ, hφ, hBFull, hCFull,
      hB, hC, hBθ, hCφ, hPB, hPC⟩ :=
    exists_ordered_frames_of_full_corners hSubset hzero (hb.map f) (hc.map f)
      hb0 hc0 hbc'
  exact ⟨f, ε, b', c', θ, φ, hfa, hε, hSubset, hGerm, horder, hθ, hφ,
    hBFull, hCFull, hB, hC, hBθ, hCφ, hPB, hPC⟩

end Puzzling139335.ThreeCorners
