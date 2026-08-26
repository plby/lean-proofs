import ErdosProblems.Erdos556.CubeTilings

/-!
# Equality in the opposite-face terminal configuration
-/

namespace Erdos556

open Finset

theorem IsCubeWeight.tiling_of_zero_energy_face_support {w : CubeProfile → ℝ}
    (hw : IsCubeWeight w) (i : Fin 3) (b : Bool) (hface : 0 < w (cubeFace i b))
    (hhigh : ∀ r, 2 ≤ profileDimension r → r ≠ cubeFace i b → r ≠ cubeFace i (!b) → w r = 0)
    (hzero : cubeEnergy w = 0) : IsCubeTiling w := by
  classical
  let p := cubeFace i b
  let q := cubeFace i (!b)
  have hpq : p ≠ q := cubeFace_ne_opposite i b
  obtain ⟨hL₀, hL₁, hE₀, hE₁⟩ := (hw.face_support_energy_and_equality i b hface hhigh).2 hzero
  have hE₀zero : (∑ r ∈ faceEdgeProfiles w i b, w r) = 0 := by
    rcases hE₀ with h | h
    · exact h
    · rw [h] at hL₀
      linarith
  have hwp : w p = 2 := by
    rw [hE₀zero] at hL₀
    simpa only [add_zero] using hL₀
  have hwq : w q = 0 ∨ w q = 2 := by
    rcases hE₁ with h | h
    · right; rw [h] at hL₁; simpa only [add_zero] using hL₁
    · left; rw [h] at hL₁; change w q + 2 = 2 at hL₁; linarith
  have hedge (r : CubeProfile) (hrdim : profileDimension r = 1) (hr : 0 < w r) :
      w r = 1 ∧ profileVertices r ⊆ profileVertices q ∧ w q = 0 := by
    have hrE : r ∈ positiveEdgeProfiles w := mem_filter.mpr ⟨mem_univ r, hrdim, hr⟩
    have hnot : ¬ profileVertices r ⊆ profileVertices p := by
      intro hsub
      have hrF : r ∈ faceEdgeProfiles w i b := mem_filter.mpr ⟨hrE, hsub⟩
      have hle := single_le_sum (fun s _ => hw.nonneg s) hrF
      rw [hE₀zero] at hle
      linarith
    have hsub : profileVertices r ⊆ profileVertices q :=
      (compatible_edge_in_one_half i b r hrdim (hw.compatible r p hr hface)).resolve_left hnot
    have hrF : r ∈ faceEdgeProfiles w i (!b) := mem_filter.mpr ⟨hrE, hsub⟩
    have hmass : (∑ s ∈ faceEdgeProfiles w i (!b), w s) = 2 := by
      rcases hE₁ with h | h
      · have hle := single_le_sum (fun s _ => hw.nonneg s) hrF
        rw [h] at hle
        linarith
      · exact h
    obtain ⟨_, hones⟩ := weights_eq_one_of_maximal_sum (faceEdgeProfiles w i (!b)) w 2
      (hw.face_edges_card_le_two i (!b))
      (fun s hs => hw.edge_le_one s (mem_filter.mp (mem_filter.mp hs).1).2.1) hmass
    have hqzero : w q = 0 := by rw [hmass] at hL₁; change w q + 2 = 2 at hL₁; linarith
    exact ⟨hones r hrF, hsub, hqzero⟩
  have hcases (r : CubeProfile) (hr : 0 < w r) :
      r = p ∨ r = q ∨
        (profileDimension r = 1 ∧ w r = 1 ∧ profileVertices r ⊆ profileVertices q ∧ w q = 0) := by
    by_cases hrp : r = p
    · exact Or.inl hrp
    by_cases hrq : r = q
    · exact Or.inr (Or.inl hrq)
    have hrdim : profileDimension r = 1 := by
      by_contra hd
      by_cases hd0 : profileDimension r = 0
      · rw [hw.vertex_zero r hd0] at hr
        exact hr.false
      · rw [hhigh r (by omega) hrp hrq] at hr
        exact hr.false
    exact Or.inr (Or.inr ⟨hrdim, hedge r hrdim hr⟩)
  have hdisj : Disjoint (profileVertices p) (profileVertices q) :=
    (cube_faces_disjoint_iff i i b (!b)).mpr ⟨rfl, by cases b <;> decide⟩
  constructor
  · intro r hr
    rcases hcases r hr with rfl | rfl | ⟨hd, hw, _, _⟩
    · exact Or.inr ⟨cubeFace_dimension i b, hwp⟩
    · have hq2 : w q = 2 := hwq.resolve_left (ne_of_gt hr)
      exact Or.inr ⟨cubeFace_dimension i (!b), hq2⟩
    · exact Or.inl ⟨hd, hw⟩
  · intro r s hrs hr hs
    rcases hcases r hr with rfl | rfl | ⟨hrd, hrw, hrsub, hq0⟩
    · rcases hcases s hs with rfl | rfl | ⟨hsd, hsw, hssub, _⟩
      · exact (hrs rfl).elim
      · exact hdisj
      · exact hdisj.mono_right hssub
    · rcases hcases s hs with rfl | rfl | ⟨_, _, _, hq0⟩
      · exact hdisj.symm
      · exact (hrs rfl).elim
      · rw [hq0] at hr; exact hr.false.elim
    · rcases hcases s hs with rfl | rfl | ⟨hsd, _, _, _⟩
      · exact (hdisj.mono_right hrsub).symm
      · rw [hq0] at hs; exact hs.false.elim
      · exact distinct_compatible_edges_disjoint r s hrd hsd hrs (hw.compatible r s hr hs)

#print axioms IsCubeWeight.tiling_of_zero_energy_face_support

end Erdos556
