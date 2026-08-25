import StackExchange.Puzzling139335.CornerSupport.Frames

/-!
# The normals determined by a support bisector

In the plane, a sum of two orthonormal vectors determines the unordered pair
of summands. Consequently support-corner witnesses with the same outward
bisector have the same two outward normals, possibly in the opposite order.
-/

open Set

namespace Puzzling139335.ThreeCorners

/-- The outward bisector determines the unordered pair of support normals,
even when the witnesses concern different sets or different vertices. -/
theorem normals_eq_or_swap_of_bisector_eq {P Q : Set Plane} {v w : Plane}
    (h : SupportCorner P v) (k : SupportCorner Q w)
    (hbis : h.bisector = k.bisector) :
    (k.firstNormal = h.firstNormal ∧ k.secondNormal = h.secondNormal) ∨
      (k.firstNormal = h.secondNormal ∧ k.secondNormal = h.firstNormal) := by
  have hsum : inner ℝ h.firstNormal k.firstNormal +
      inner ℝ h.secondNormal k.firstNormal = 1 := by
    calc
      _ = inner ℝ h.bisector k.firstNormal := by
        rw [SupportCorner.bisector, inner_add_left]
      _ = inner ℝ k.bisector k.firstNormal := by rw [hbis]
      _ = 1 := by
        rw [SupportCorner.bisector, inner_add_left, real_inner_self_eq_norm_sq,
          k.norm_firstNormal, real_inner_comm k.firstNormal k.secondNormal, k.orthogonal]
        norm_num
  have hsq := h.normal_projections_sq k.firstNormal
  rw [k.norm_firstNormal] at hsq
  have hprod : inner ℝ h.firstNormal k.firstNormal *
      inner ℝ h.secondNormal k.firstNormal = 0 := by
    nlinarith [congrArg (fun t : ℝ => t ^ 2) hsum]
  have hnormals : h.firstNormal + h.secondNormal =
      k.firstNormal + k.secondNormal := hbis
  have hsecond : k.secondNormal =
      h.firstNormal + h.secondNormal - k.firstNormal := by
    rw [hnormals]
    abel
  rcases mul_eq_zero.mp hprod with hfirst_zero | hsecond_zero
  · have hfirst : k.firstNormal = h.secondNormal :=
      ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ)
        h.norm_secondNormal k.norm_firstNormal).mp (by linarith)).symm
    right
    refine ⟨hfirst, ?_⟩
    rw [hsecond, hfirst]
    abel
  · have hfirst : k.firstNormal = h.firstNormal :=
      ((inner_eq_one_iff_of_norm_eq_one (𝕜 := ℝ)
        h.norm_firstNormal k.norm_firstNormal).mp (by linarith)).symm
    left
    refine ⟨hfirst, ?_⟩
    rw [hsecond, hfirst]
    abel

end Puzzling139335.ThreeCorners
