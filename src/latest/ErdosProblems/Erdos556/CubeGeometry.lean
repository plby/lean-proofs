import ErdosProblems.Erdos556.CubeProfiles

/-!
# Exact intersection geometry of the cube profiles

These finite identities are checked by Lean's kernel decision procedure.
They express the matching and face restrictions used by the weighted
cube inequality.
-/

namespace Erdos556

theorem profileVertices_injective : Function.Injective profileVertices := by
  decide

theorem distinct_compatible_edges_disjoint : ∀ p q : CubeProfile,
    profileDimension p = 1 → profileDimension q = 1 → p ≠ q →
    ((profileVertices p) ∩ (profileVertices q)).card ≠ 1 →
    Disjoint (profileVertices p) (profileVertices q) := by
  decide

theorem compatible_edge_profile_disjoint_or_subset : ∀ p q : CubeProfile,
    profileDimension p = 1 →
    ((profileVertices p) ∩ (profileVertices q)).card ≠ 1 →
    Disjoint (profileVertices p) (profileVertices q) ∨ profileVertices p ⊆ profileVertices q := by
  decide

theorem cube_faces_disjoint_iff : ∀ (i j : Fin 3) (b c : Bool),
    Disjoint (profileVertices (cubeFace i b)) (profileVertices (cubeFace j c)) ↔
      i = j ∧ b ≠ c := by
  decide

theorem disjoint_high_dimension_profiles_are_faces : ∀ p q : CubeProfile,
    2 ≤ profileDimension p → 2 ≤ profileDimension q →
    Disjoint (profileVertices p) (profileVertices q) →
      profileDimension p = 2 ∧ profileDimension q = 2 := by
  decide

theorem cube_faces_partition : ∀ (i : Fin 3) (b : Bool),
    profileVertices (cubeFace i b) ∪ profileVertices (cubeFace i (!b)) = Finset.univ := by
  decide

#print axioms distinct_compatible_edges_disjoint
#print axioms compatible_edge_profile_disjoint_or_subset
#print axioms cube_faces_partition

end Erdos556
