import StackExchange.Puzzling139335.N4Midline.OrderedProof
import StackExchange.Puzzling139335.N4Midline.FullCorners

/-!
# The repeated midline reflection case with three intrinsic corner types

The theorem below has only actual dissection and placement hypotheses.
The square corners are labeled by their unique pieces. The two lower
pieces are exchanged by the vertical midline reflection, and the two
upper occupied corners have distinct nonzero preimages in the lower-left
prototype. These are precisely the normalized repeated-midline geometric
data; angular ordering, supporting-face contacts, bottom-edge coverage,
and the endpoint configurations are all proved internally.
-/

open Set

namespace Puzzling139335.N4Midline

open ThreeCorners

noncomputable section

/-- Four uniquely occupied square corners with a repeated lower midline
pair and two other distinct intrinsic corner types cannot protect the center. -/
theorem normalized_midline_not_protected (d : SquareDissection)
    (hcorners : ∀ j i : Fin 4, corner j ∈ d.piece i ↔ j = i)
    (hmirror : midlineReflection '' d.piece 0 = d.piece 1)
    (r t : Plane ≃ᵃⁱ[ℝ] Plane)
    (hr : r '' d.piece 0 = d.piece 2)
    (ht : t '' d.piece 0 = d.piece 3)
    (hrzero : r.symm (corner 2) ≠ 0)
    (htzero : t.symm (corner 3) ≠ 0)
    (hrt : r.symm (corner 2) ≠ t.symm (corner 3)) :
    ¬ d.HasProtectedCenter := by
  have hcorner0 : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> norm_num [corner, Fin.ext_iff]
  have hzero : (0 : Plane) ∈ d.piece 0 := by
    rw [← hcorner0]
    exact (hcorners 0 0).mpr rfl
  have hdis : Disjoint (interior (d.piece 0))
      (interior (midlineReflection '' d.piece 0)) := by
    rw [hmirror]
    exact d.disjoint_interiors (by decide : (0 : Fin 4) ≠ 1)
  have hleft := reflected_pair_subset_left (d.jordan 0) (d.piece_subset 0) hzero hdis
  have hBFull : UnitPairs.IsFullSquareCorner (d.piece 0) (r.symm (corner 2)) := by
    apply d.full_corner_preimage_of_unique_owner 0 2 2 r hr
    intro l hl hmem
    exact hl ((hcorners 2 l).mp hmem).symm
  have hCFull : UnitPairs.IsFullSquareCorner (d.piece 0) (t.symm (corner 3)) := by
    apply d.full_corner_preimage_of_unique_owner 0 3 3 t ht
    intro l hl hmem
    exact hl ((hcorners 3 l).mp hmem).symm
  obtain ⟨B, C, θ, φ, horder, hθ, hφ, hfullB, hfullC,
      hB, hC, hBθ, hCφ, hconeB, hconeC⟩ :=
    exists_ordered_frames_of_full_corners (d.piece_subset 0) hzero hBFull hCFull
      hrzero htzero hrt
  rcases horder with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ordered_not_protected d hmirror hzero hleft 2 3 (Or.inl ⟨rfl, rfl⟩)
      _ _ θ φ r t hr ht (r.apply_symm_apply _) (t.apply_symm_apply _)
      hfullB hfullC hB hC hBθ hCφ hconeB hconeC hθ hφ
  · exact ordered_not_protected d hmirror hzero hleft 3 2 (Or.inr ⟨rfl, rfl⟩)
      _ _ θ φ t r ht hr (t.apply_symm_apply _) (r.apply_symm_apply _)
      hfullB hfullC hB hC hBθ hCφ hconeB hconeC hθ hφ

end

end Puzzling139335.N4Midline
