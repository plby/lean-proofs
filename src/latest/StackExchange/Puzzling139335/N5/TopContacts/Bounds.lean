import StackExchange.Puzzling139335.N5.StrictFrame.Placement.Form
import StackExchange.Puzzling139335.N5.Normalized
import StackExchange.Puzzling139335.DissectionTopology
import StackExchange.Puzzling139335.N5Facet.Elementary

/-!
# Actual top-contact bounds for the surviving corner placement

Every top contact of the singleton-corner piece pulls back to its incoming
supporting line.  The source square bound and the actual right contact
then place that top contact strictly after the reflected pair's top end.
-/

open Set Metric

namespace Puzzling139335.N5

/-- In the surviving row order, the inverse image of a point on the top
side lies on the incoming supporting line through `C`. -/
theorem swapped_inverse_top_point
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s x : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1]) :
    e.symm (Schoenflies.Plane.mk x 1) =
      !₂[C 0 + (1 - x) * s, C 1 - (1 - x) * c] := by
  apply e.injective
  rw [e.apply_symm_apply, hform]
  apply PlaneIsometries.plane_ext
  · change x = 1 + s * C 0 - c * C 1 -
      s * (C 0 + (1 - x) * s) + c * (C 1 - (1 - x) * c)
    linear_combination (1 - x) * hunit
  · change (1 : ℝ) = 1 - c * C 0 - s * C 1 +
      c * (C 0 + (1 - x) * s) + s * (C 1 - (1 - x) * c)
    ring

/-- The coordinate formulation for an actual source point of a top
contact. -/
theorem top_preimage_coords_of_swapped_form
    {e : Plane ≃ᵃⁱ[ℝ] Plane} {C p : Plane} {c s x : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hform : ∀ q, e q =
      !₂[1 + s * C 0 - c * C 1 - s * q 0 + c * q 1,
         1 - c * C 0 - s * C 1 + c * q 0 + s * q 1])
    (hep : e p = Schoenflies.Plane.mk x 1) :
    p 0 = C 0 + s * (1 - x) ∧ p 1 = C 1 - c * (1 - x) := by
  have hp : p = e.symm (Schoenflies.Plane.mk x 1) := by
    rw [← hep, e.symm_apply_apply]
  rw [hp, swapped_inverse_top_point hunit hform]
  constructor <;> simp only [Matrix.cons_val_zero, Matrix.cons_val_one] <;> ring

/-- An actual top contact is strictly to the right of the source's right
contact height.  No completeness of either supporting face is assumed. -/
theorem top_contact_gt_base_height_of_swapped_form
    {P : Set Plane} {e : Plane ≃ᵃⁱ[ℝ] Plane} {C : Plane} {c s b x : ℝ}
    (hP : P ⊆ unitSquare) (he : e '' P ⊆ unitSquare)
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hc : 0 < c) (hs : 0 < s) (hc₁ : c < 1) (hb : 0 < b)
    (hk : C 1 < c)
    (hform : ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])
    (hE : Schoenflies.Plane.mk 1 b ∈ P)
    (hX : Schoenflies.Plane.mk x 1 ∈ e '' P) : b < x := by
  obtain ⟨p, hp, hep⟩ := hX
  have hcoords := top_preimage_coords_of_swapped_form hunit hform hep
  have hendpoint : C 0 + s * (1 - x) ≤ 1 := by
    rw [← hcoords.1]
    exact (hP hp).1.2
  have hf : CornerPlacementForm e C c s := Or.inr hform
  have hEbound := (hf.support he hE).1
  change c * 1 + s * b ≤ c * C 0 + s * C 1 at hEbound
  have hsupport : c * (1 - C 0) ≤ s * (C 1 - b) := by
    nlinarith only [hEbound]
  have hlength := N5Facet.top_hull_face_lt_remaining_length
    hc hs hc₁ hb (L := 1 - b) rfl hk hendpoint hsupport
  linarith only [hlength]

/-- The bound specialized to the actual singleton-corner piece. -/
theorem Normalized.singleton_top_contact_gt_base_height {d : SquareDissection}
    (h : Normalized d) (e : Plane ≃ᵃⁱ[ℝ] Plane)
    (he : e '' d.piece 0 = d.piece 2) {C : Plane} {c s b x : ℝ}
    (hunit : c ^ 2 + s ^ 2 = 1)
    (hc : 0 < c) (hs : 0 < s) (hc₁ : c < 1) (hb : 0 < b)
    (hk : C 1 < c)
    (hform : ∀ p, e p =
      !₂[1 + s * C 0 - c * C 1 - s * p 0 + c * p 1,
         1 - c * C 0 - s * C 1 + c * p 0 + s * p 1])
    (hE : Schoenflies.Plane.mk 1 b ∈ d.piece 0)
    (hX : Schoenflies.Plane.mk x 1 ∈ d.piece 2) : b < x := by
  have hfit : e '' d.piece 0 ⊆ unitSquare := by
    rw [he]
    exact d.piece_subset 2
  exact top_contact_gt_base_height_of_swapped_form (d.piece_subset 0) hfit
    hunit hc hs hc₁ hb hk hform hE (he.symm ▸ hX)

/-- Unique ownership of the top-right corner supplies a strictly earlier
top contact of the singleton-corner piece. -/
theorem Normalized.exists_singleton_top_contact_lt_one {d : SquareDissection}
    (h : Normalized d) :
    ∃ x : ℝ, x < 1 ∧ Schoenflies.Plane.mk x 1 ∈ d.piece 2 := by
  obtain ⟨ε, hε, hnear⟩ := d.unique_piece_relative_neighborhood 2 h.unique_top_right
  let δ : ℝ := min (1 / 2) (ε / 2)
  have hδ : 0 < δ := lt_min (by norm_num) (half_pos hε)
  have hδhalf : δ ≤ 1 / 2 := min_le_left _ _
  have hδε : δ ≤ ε / 2 := min_le_right _ _
  have hdist : dist (Schoenflies.Plane.mk (1 - δ) 1) (corner 2) = δ := by
    apply (sq_eq_sq₀ dist_nonneg hδ.le).mp
    norm_num [plane_dist_sq, Schoenflies.Plane.mk, corner, Fin.ext_iff] <;> ring
  have hball : Schoenflies.Plane.mk (1 - δ) 1 ∈ ball (corner 2) ε := by
    rw [mem_ball, hdist]
    linarith only [hδε, hε]
  have hunit : Schoenflies.Plane.mk (1 - δ) 1 ∈ unitSquare := by
    change (0 ≤ 1 - δ ∧ 1 - δ ≤ 1) ∧ (0 ≤ (1 : ℝ) ∧ (1 : ℝ) ≤ 1)
    constructor
    · constructor <;> linarith only [hδhalf, hδ]
    · exact ⟨zero_le_one, le_rfl⟩
  exact ⟨1 - δ, by linarith only [hδ], hnear ⟨hball, hunit⟩⟩

/-- The reflected piece's top interval is exactly the image of the base
piece's actual right interval. -/
theorem Normalized.top_contact_one_iff_of_right_interval {d : SquareDissection}
    (h : Normalized d) {b : ℝ}
    (hright : ∀ y : ℝ, Schoenflies.Plane.mk 1 y ∈ d.piece 0 ↔ 0 ≤ y ∧ y ≤ b)
    (x : ℝ) :
    Schoenflies.Plane.mk x 1 ∈ d.piece 1 ↔ 0 ≤ x ∧ x ≤ b := by
  constructor
  · intro hx
    obtain ⟨p, hp, hep⟩ := h.diagonal_image.symm ▸ hx
    have hpcoord : p = Schoenflies.Plane.mk 1 x := by
      calc
        p = ReflectionSeparation.diagonal (ReflectionSeparation.diagonal p) :=
          (ReflectionSeparation.diagonal_involutive p).symm
        _ = ReflectionSeparation.diagonal (Schoenflies.Plane.mk x 1) :=
          congrArg ReflectionSeparation.diagonal hep
        _ = Schoenflies.Plane.mk 1 x := by
          apply PlaneIsometries.plane_ext <;> rfl
    exact (hright x).mp (hpcoord ▸ hp)
  · intro hx
    rw [← h.diagonal_image]
    refine ⟨Schoenflies.Plane.mk 1 x, (hright x).mpr hx, ?_⟩
    apply PlaneIsometries.plane_ext <;> rfl

end Puzzling139335.N5
