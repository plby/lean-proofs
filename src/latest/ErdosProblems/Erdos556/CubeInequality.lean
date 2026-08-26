import ErdosProblems.Erdos556.CubeCompression
import ErdosProblems.Erdos556.CubeOnlyTerminal
import ErdosProblems.Erdos556.CubeFacesTerminal

/-!
# The weighted three-cube inequality

Every admissible weight vector has nonnegative energy. The proof
compresses intersecting higher-dimensional profiles and then applies
one of the two explicitly proved terminal inequalities.
-/

namespace Erdos556

open Finset

theorem high_profile_disjoint_from_face : ∀ (i : Fin 3) (b : Bool) (p : CubeProfile),
    2 ≤ profileDimension p → Disjoint (profileVertices (cubeFace i b)) (profileVertices p) →
      p = cubeFace i (!b) := by
  decide

theorem cube_energy_nonneg_of_disjoint_high_support (w : CubeProfile → ℝ) (hw : IsCubeWeight w)
    (hdisj : (positiveHighProfiles w : Set CubeProfile).Pairwise
      (fun p q => Disjoint (profileVertices p) (profileVertices q))) :
    0 ≤ cubeEnergy w := by
  classical
  by_cases hface : ∃ p : CubeProfile, profileDimension p = 2 ∧ 0 < w p
  · obtain ⟨p, hpdim, hp⟩ := hface
    obtain ⟨i, b, rfl⟩ := (profileDimension_two_iff p).mp hpdim
    apply hw.energy_nonneg_of_face_support i b hp
    intro r hr hrp hrq
    by_contra hrzero
    have hrpos : 0 < w r := lt_of_le_of_ne (hw.nonneg r) (Ne.symm hrzero)
    have hpH : cubeFace i b ∈ positiveHighProfiles w :=
      mem_filter.mpr ⟨mem_univ _, by rw [cubeFace_dimension], hp⟩
    have hrH : r ∈ positiveHighProfiles w := mem_filter.mpr ⟨mem_univ _, hr, hrpos⟩
    exact hrq (high_profile_disjoint_from_face i b r hr (hdisj hpH hrH hrp.symm))
  · have hhigh : ∀ p, 2 ≤ profileDimension p → p ≠ wholeCube → w p = 0 := by
      intro p hpdim hpne
      have hdim3 : profileDimension p ≠ 3 := fun h => hpne ((profileDimension_three_iff p).mp h)
      have hmax := profileDimension_le_three p
      have hdim2 : profileDimension p = 2 := by omega
      have hnot : ¬ 0 < w p := fun h => hface ⟨p, hdim2, h⟩
      exact le_antisymm (le_of_not_gt hnot) (hw.nonneg p)
    exact (hw.nonneg wholeCube).trans (hw.energy_ge_whole_of_high_support hhigh)

theorem cube_energy_nonneg (w : CubeProfile → ℝ) (hw : IsCubeWeight w) : 0 ≤ cubeEnergy w := by
  obtain ⟨v, hv, hdisj, henergy⟩ := exists_cube_compression w hw
  exact (cube_energy_nonneg_of_disjoint_high_support v hv hdisj).trans henergy

#print axioms cube_energy_nonneg

end Erdos556
