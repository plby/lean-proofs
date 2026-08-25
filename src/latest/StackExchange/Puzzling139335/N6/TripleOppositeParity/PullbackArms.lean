import StackExchange.Puzzling139335.ThreeCorners.FullBisector
import StackExchange.Puzzling139335.ThreeCorners.NormalUniqueness
import StackExchange.Puzzling139335.N7Geometry.TripleCornerBounds

/-!
# Pulling back the actual side arms at a full square corner

The full corner germ identifies the two transported supporting normals up
to interchange.  Thus actual endpoints on both sides through the top-right
corner pull back to endpoints on both original supporting rays.  No convex
hull segment is substituted for an actual point of the set.
-/

open Set

namespace Puzzling139335.N6.TripleOppositeParity

noncomputable section

/-- An actual square placement at a full top-right corner carries the two
supporting normals to the positive coordinate vectors, in some order. -/
theorem full_corner_normals_map_eq_or_swap {P : Set Plane} {C : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P C) (h : SupportCorner P C)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hsub : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) :
    (e.linearIsometryEquiv h.firstNormal = !₂[1, 0] ∧
      e.linearIsometryEquiv h.secondNormal = !₂[0, 1]) ∨
    (e.linearIsometryEquiv h.firstNormal = !₂[0, 1] ∧
      e.linearIsometryEquiv h.secondNormal = !₂[1, 0]) := by
  have hbis : (squareSupportCorner 2).bisector = (h.map e).bisector := by
    simpa only [SupportCorner.bisector, SupportCorner.map, map_add] using
      (hfull.map_bisector_eq_square h e 2 hsub heC).symm
  simpa [SupportCorner.map, squareSupportCorner] using
    ThreeCorners.normals_eq_or_swap_of_bisector_eq (squareSupportCorner 2) (h.map e) hbis

private theorem map_sub_smul (e : Plane ≃ᵃⁱ[ℝ] Plane) (C n : Plane) (L : ℝ) :
    e (C - L • n) = e C - L • e.linearIsometryEquiv n := by
  simpa only [vadd_eq_add, map_smul, map_neg, neg_smul, sub_eq_add_neg, add_comm] using
    e.map_vadd C ((-L) • n)

private theorem mem_of_image_mem {P : Set Plane} (e : Plane ≃ᵃⁱ[ℝ] Plane)
    {x : Plane} (hx : e x ∈ e '' P) : x ∈ P := by
  obtain ⟨y, hy, he⟩ := hx
  exact e.injective he ▸ hy

private theorem arm_mem_of_horizontal_normal {P : Set Plane} {C n : Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heC : e C = corner 2)
    (hen : e.linearIsometryEquiv n = !₂[1, 0]) {r : ℝ}
    (htop : (!₂[r, 1] : Plane) ∈ e '' P) :
    C - (1 - r) • n ∈ P := by
  have he : e (C - (1 - r) • n) = !₂[r, 1] := by
    rw [map_sub_smul, heC, hen]
    ext i
    fin_cases i <;> simp [corner]
  apply mem_of_image_mem e
  rw [he]
  exact htop

private theorem arm_mem_of_vertical_normal {P : Set Plane} {C n : Plane}
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (heC : e C = corner 2)
    (hen : e.linearIsometryEquiv n = !₂[0, 1]) {r : ℝ}
    (hright : (!₂[1, r] : Plane) ∈ e '' P) :
    C - (1 - r) • n ∈ P := by
  have he : e (C - (1 - r) • n) = !₂[1, r] := by
    rw [map_sub_smul, heC, hen]
    ext i
    fin_cases i <;> simp [corner]
  apply mem_of_image_mem e
  rw [he]
  exact hright

/-- Equal-length actual arms on the two square sides pull back to actual
points on both original supporting rays at the full corner. -/
theorem full_corner_arms_mem {P : Set Plane} {C : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P C) (h : SupportCorner P C)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hsub : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) {r : ℝ}
    (htop : (!₂[r, 1] : Plane) ∈ e '' P)
    (hright : (!₂[1, r] : Plane) ∈ e '' P) :
    C - (1 - r) • h.firstNormal ∈ P ∧
      C - (1 - r) • h.secondNormal ∈ P := by
  rcases full_corner_normals_map_eq_or_swap hfull h e hsub heC with
    ⟨hfirst, hsecond⟩ | ⟨hfirst, hsecond⟩
  · exact ⟨arm_mem_of_horizontal_normal e heC hfirst htop,
      arm_mem_of_vertical_normal e heC hsecond hright⟩
  · exact ⟨arm_mem_of_vertical_normal e heC hfirst hright,
      arm_mem_of_horizontal_normal e heC hsecond htop⟩

private theorem linear_apply_of_coordinate_images (L : Plane ≃ₗᵢ[ℝ] Plane)
    (p : Plane) :
    L p = p 0 • L !₂[1, 0] + p 1 • L !₂[0, 1] := by
  have hp : p = p 0 • (!₂[1, 0] : Plane) + p 1 • (!₂[0, 1] : Plane) := by
    ext i
    fin_cases i <;> simp
  calc
    L p = L (p 0 • (!₂[1, 0] : Plane) + p 1 • (!₂[0, 1] : Plane)) := congrArg L hp
    _ = _ := by rw [map_add, map_smul, map_smul]

private theorem affine_apply_relative (e : Plane ≃ᵃⁱ[ℝ] Plane) (p C : Plane) :
    e p = e.linearIsometryEquiv (p - C) + e C := by
  have he : e p - e C = e.linearIsometryEquiv (p - C) := (e.map_vsub p C).symm
  exact sub_eq_iff_eq_add.mp he

private theorem eq_straightPlacement_of_coordinate_images
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {H : ℝ} (heC : e !₂[1, H] = corner 2)
    (hex : e.linearIsometryEquiv !₂[1, 0] = !₂[1, 0])
    (hey : e.linearIsometryEquiv !₂[0, 1] = !₂[0, 1]) :
    (e : Plane → Plane) = TripleCornerBounds.straightPlacement H := by
  funext p
  rw [affine_apply_relative e p !₂[1, H], heC,
    linear_apply_of_coordinate_images, hex, hey]
  ext i
  fin_cases i <;> simp [TripleCornerBounds.straightPlacement, corner] <;> ring

private theorem eq_swappedPlacement_of_coordinate_images
    (e : Plane ≃ᵃⁱ[ℝ] Plane) {H : ℝ} (heC : e !₂[1, H] = corner 2)
    (hex : e.linearIsometryEquiv !₂[1, 0] = !₂[0, 1])
    (hey : e.linearIsometryEquiv !₂[0, 1] = !₂[1, 0]) :
    (e : Plane → Plane) = TripleCornerBounds.swappedPlacement H := by
  funext p
  rw [affine_apply_relative e p !₂[1, H], heC,
    linear_apply_of_coordinate_images, hex, hey]
  ext i
  fin_cases i <;> simp [TripleCornerBounds.swappedPlacement, corner] <;> ring

/-- At the zero-turn source frame the actual affine placement is one of
the two explicit exceptional placements, with no additional height hypothesis. -/
theorem full_corner_placement_eq_straight_or_swapped {P : Set Plane} {C : Plane}
    (hfull : UnitPairs.IsFullSquareCorner P C) (h : SupportCorner P C)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (hsub : e '' P ⊆ unitSquare)
    (heC : e C = corner 2) {H : ℝ} (hC : C = !₂[1, H])
    (hfirst : h.firstNormal = !₂[0, 1]) (hsecond : h.secondNormal = !₂[1, 0]) :
    (e : Plane → Plane) = TripleCornerBounds.straightPlacement H ∨
      (e : Plane → Plane) = TripleCornerBounds.swappedPlacement H := by
  have heC' : e !₂[1, H] = corner 2 := hC ▸ heC
  rcases full_corner_normals_map_eq_or_swap hfull h e hsub heC with
    ⟨hnfirst, hnsecond⟩ | ⟨hnfirst, hnsecond⟩
  · rw [hfirst] at hnfirst
    rw [hsecond] at hnsecond
    exact Or.inr (eq_swappedPlacement_of_coordinate_images e heC' hnsecond hnfirst)
  · rw [hfirst] at hnfirst
    rw [hsecond] at hnsecond
    exact Or.inl (eq_straightPlacement_of_coordinate_images e heC' hnsecond hnfirst)

end

end Puzzling139335.N6.TripleOppositeParity
