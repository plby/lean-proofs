import StackExchange.Puzzling139335.N8.Pairs
import Mathlib.Analysis.Convex.Hull

/-!
# Pulling actual side segments back to the prototype

An affine isometry carrying an unordered endpoint pair to another pair carries
their closed segments to one another. Thus an actual full side contained in a
piece gives the corresponding full intrinsic segment in the prototype.
-/

open Set

namespace Puzzling139335.N8

noncomputable section

/-- An image identity for unordered endpoint pairs determines the image segment;
no choice of endpoint order is needed. -/
theorem image_segment_of_pair_image (e : Plane ≃ᵃⁱ[ℝ] Plane) {a b c d : Plane}
    (hpair : e '' ({a, b} : Set Plane) = {c, d}) :
    e '' segment ℝ a b = segment ℝ c d := by
  calc
    e '' segment ℝ a b = e '' convexHull ℝ ({a, b} : Set Plane) := by
      rw [convexHull_pair]
    _ = convexHull ℝ (e '' ({a, b} : Set Plane)) :=
      e.toAffineEquiv.toAffineMap.image_convexHull {a, b}
    _ = convexHull ℝ ({c, d} : Set Plane) := congrArg (convexHull ℝ) hpair
    _ = segment ℝ c d := by rw [convexHull_pair]

/-- A whole assigned square side in a piece pulls back to the whole segment
between its two intrinsic corner types in the prototype. -/
theorem intrinsic_segment_subset_of_side_subset (d : SquareDissection)
    {s : Fin 4 → Fin 4} (hs : IsSideAssignment d s) (i : Fin 4) {a b : Plane}
    (hpair : intrinsicPair d i = {a, b})
    (hside : segment ℝ (corner (s i)) (corner (s i + 1)) ⊆ d.piece i) :
    segment ℝ a b ⊆ d.piece 0 := by
  classical
  have hpairImage : d.placement i '' ({a, b} : Set Plane) =
      {corner (s i), corner (s i + 1)} := by
    simpa only [hpair, Finset.coe_insert, Finset.coe_singleton] using
      placement_image_intrinsicPair d hs i
  have hsegmentImage := image_segment_of_pair_image (d.placement i) hpairImage
  intro x hx
  have hxPiece : d.placement i x ∈ d.piece i :=
    hside (hsegmentImage ▸ mem_image_of_mem (d.placement i) hx)
  rw [← d.placement_image i] at hxPiece
  obtain ⟨y, hy, hxy⟩ := hxPiece
  exact (d.placement i).injective hxy ▸ hy

end

end Puzzling139335.N8
