import ErdosProblems.Erdos556.CubeWeights

/-!
# Splitting compatible edge profiles between opposite cube faces
-/

namespace Erdos556

open Finset

theorem cubeFace_ne_opposite : ∀ (i : Fin 3) (b : Bool), cubeFace i b ≠ cubeFace i (!b) := by
  decide

theorem compatible_edge_in_one_half : ∀ (i : Fin 3) (b : Bool) (p : CubeProfile),
    profileDimension p = 1 →
    (profileVertices p ∩ profileVertices (cubeFace i b)).card ≠ 1 →
    profileVertices p ⊆ profileVertices (cubeFace i b) ∨
      profileVertices p ⊆ profileVertices (cubeFace i (!b)) := by
  decide

theorem edge_not_in_both_halves : ∀ (i : Fin 3) (b : Bool) (p : CubeProfile),
    profileDimension p = 1 →
    ¬ (profileVertices p ⊆ profileVertices (cubeFace i b) ∧
      profileVertices p ⊆ profileVertices (cubeFace i (!b))) := by
  decide

theorem cubeOverlap_of_subset {p q : CubeProfile} (hsub : profileVertices q ⊆ profileVertices p) :
    cubeOverlap p q = 1 := by
  have hnon : (profileVertices q).Nonempty := by
    apply card_pos.mp
    rw [profileVertices_card]
    positivity
  have hnot : ¬ Disjoint (profileVertices p) (profileVertices q) := by
    intro h
    obtain ⟨v, hv⟩ := hnon
    exact Finset.disjoint_left.mp h (hsub hv) hv
  simp only [cubeOverlap, if_neg hnot]

theorem cubeOverlap_opposite_faces (i : Fin 3) (b : Bool) :
    cubeOverlap (cubeFace i b) (cubeFace i (!b)) = 0 := by
  have hb : b ≠ !b := by cases b <;> decide
  have hdisj := (cube_faces_disjoint_iff i i b (!b)).mpr ⟨rfl, hb⟩
  simp only [cubeOverlap, if_pos hdisj]

theorem cubeOverlap_face_of_subset_opposite (i : Fin 3) (b : Bool) (p : CubeProfile)
    (hsub : profileVertices p ⊆ profileVertices (cubeFace i (!b))) :
    cubeOverlap (cubeFace i b) p = 0 := by
  have hb : b ≠ !b := by cases b <;> decide
  have hdisj := ((cube_faces_disjoint_iff i i b (!b)).mpr ⟨rfl, hb⟩).mono_right hsub
  simp only [cubeOverlap, if_pos hdisj]

#print axioms compatible_edge_in_one_half
#print axioms cubeOverlap_face_of_subset_opposite

end Erdos556
