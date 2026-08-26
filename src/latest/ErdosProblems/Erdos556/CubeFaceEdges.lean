import ErdosProblems.Erdos556.CubeFaceGeometry
import ErdosProblems.Erdos556.CubeFiniteWeights

/-!
# Edge weights inside a cube face
-/

namespace Erdos556

open Finset

noncomputable def faceEdgeProfiles (w : CubeProfile → ℝ) (i : Fin 3) (b : Bool) : Finset CubeProfile :=
  (positiveEdgeProfiles w).filter (fun p => profileVertices p ⊆ profileVertices (cubeFace i b))

theorem faceEdgeProfiles_subset (w : CubeProfile → ℝ) (i : Fin 3) (b : Bool) :
    faceEdgeProfiles w i b ⊆ positiveEdgeProfiles w := filter_subset _ _

theorem IsCubeWeight.face_edges_card_le_two {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (i : Fin 3) (b : Bool) : (faceEdgeProfiles w i b).card ≤ 2 := by
  have h := edge_profiles_packing_bound (faceEdgeProfiles w i b) (profileVertices (cubeFace i b))
    (fun p hp => (mem_filter.mp (mem_filter.mp hp).1).2.1)
    (hw.positive_edges_disjoint.mono (faceEdgeProfiles_subset w i b))
    (fun p hp => (mem_filter.mp hp).2)
  rw [profileVertices_card, cubeFace_dimension] at h
  norm_num at h
  omega

theorem faceEdgeProfiles_disjoint (w : CubeProfile → ℝ) (i : Fin 3) (b : Bool) :
    Disjoint (faceEdgeProfiles w i b) (faceEdgeProfiles w i (!b)) := by
  rw [Finset.disjoint_left]
  intro p hp hq
  have hd := (mem_filter.mp (mem_filter.mp hp).1).2.1
  exact edge_not_in_both_halves i b p hd ⟨(mem_filter.mp hp).2, (mem_filter.mp hq).2⟩

theorem faceEdgeProfiles_union {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (i : Fin 3) (b : Bool) (hb : 0 < w (cubeFace i b)) :
    faceEdgeProfiles w i b ∪ faceEdgeProfiles w i (!b) = positiveEdgeProfiles w := by
  apply Subset.antisymm
  · exact union_subset (faceEdgeProfiles_subset w i b) (faceEdgeProfiles_subset w i (!b))
  · intro p hp
    have hd := (mem_filter.mp hp).2.1
    have hwpos := (mem_filter.mp hp).2.2
    rcases compatible_edge_in_one_half i b p hd (hw.compatible p (cubeFace i b) hwpos hb) with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hp, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hp, h⟩)

theorem IsCubeWeight.face_edge_sum_bound {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (i : Fin 3) (b : Bool) : (∑ p ∈ faceEdgeProfiles w i b, w p) ≤ 2 := by
  apply (sum_weights_le_card (faceEdgeProfiles w i b) w ?_).trans
  · exact_mod_cast hw.face_edges_card_le_two i b
  · intro p hp
    exact hw.edge_le_one p (mem_filter.mp (mem_filter.mp hp).1).2.1

theorem IsCubeWeight.face_edge_sum_sq_bound {w : CubeProfile → ℝ} (hw : IsCubeWeight w)
    (i : Fin 3) (b : Bool) :
    (∑ p ∈ faceEdgeProfiles w i b, w p) ^ 2 ≤ 2 * ∑ p ∈ faceEdgeProfiles w i b, w p ^ 2 :=
  sum_sq_bound_of_card_le (faceEdgeProfiles w i b) w 2 (hw.face_edges_card_le_two i b)

theorem cubeGradient_face_of_edge_support (w x : CubeProfile → ℝ) (i : Fin 3) (b : Bool)
    (hx : ∀ p ∈ positiveEdgeProfiles w, x p = w p)
    (hzero : ∀ p, p ∉ positiveEdgeProfiles w → x p = 0)
    (hpart : ∀ p ∈ positiveEdgeProfiles w,
      profileVertices p ⊆ profileVertices (cubeFace i b) ∨
        profileVertices p ⊆ profileVertices (cubeFace i (!b))) :
    cubeGradient x (cubeFace i b) = 2 * (∑ p ∈ faceEdgeProfiles w i b, w p) - 2 := by
  classical
  have hsum : (∑ p, cubeOverlap (cubeFace i b) p * x p) = ∑ p ∈ faceEdgeProfiles w i b, w p := by
    calc
      (∑ p, cubeOverlap (cubeFace i b) p * x p) =
          ∑ p ∈ positiveEdgeProfiles w, cubeOverlap (cubeFace i b) p * x p := by
        symm
        apply sum_subset (subset_univ _)
        intro p _ hp
        rw [hzero p hp, mul_zero]
      _ = ∑ p ∈ faceEdgeProfiles w i b, w p := by
        rw [faceEdgeProfiles, sum_filter]
        apply sum_congr rfl
        intro p hp
        rw [hx p hp]
        by_cases hsub : profileVertices p ⊆ profileVertices (cubeFace i b)
        · rw [if_pos hsub, cubeOverlap_of_subset hsub, one_mul]
        · rw [if_neg hsub, cubeOverlap_face_of_subset_opposite i b p ((hpart p hp).resolve_left hsub), zero_mul]
  simp only [cubeGradient, hsum, cubeFace_dimension, Nat.cast_ofNat]

#print axioms IsCubeWeight.face_edges_card_le_two
#print axioms cubeGradient_face_of_edge_support

end Erdos556
