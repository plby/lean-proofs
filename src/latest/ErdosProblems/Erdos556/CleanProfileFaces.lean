import ErdosProblems.Erdos556.CleanProfileSystem
import ErdosProblems.Erdos556.TilingFacePartner
import ErdosProblems.Erdos556.DenseBipartiteOddCycle

/-! A cleaned face class uses only its two free colours internally. -/

namespace Erdos556

open SimpleGraph Finset

theorem CleanProfileSystem.positive_core_large {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {r : ℕ} {η : ℝ} (h : CleanProfileSystem c (2 * r + 1) η)
    (hr : 1 ≤ r) (hη : η ≤ 1 / 100) (p : CubeProfile) (hp : 0 < h.weight p) :
    r + 2 * h.defect + 1 ≤ (h.sets p).card := by
  have hw : 1 ≤ h.weight p := by
    rcases h.tiling.normalized p hp with ⟨_, he⟩ | ⟨_, he⟩ <;> rw [he] <;> norm_num
  have hsize := h.size_lower p
  have hd := h.defect_le
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hn : (0 : ℝ) ≤ 2 * r + 1 := by positivity
  have hws := mul_le_mul_of_nonneg_right hw hn
  have hηs := mul_le_mul_of_nonneg_right hη hn
  have hbound : (r : ℝ) + 2 * h.defect + 1 ≤ (h.sets p).card := by
    push_cast at hsize hd
    nlinarith
  exact_mod_cast hbound

theorem CleanProfileSystem.no_fixed_colour_in_face {V : Type*} [DecidableEq V]
    {c : ThreeColouring V} {r : ℕ} {η : ℝ} (h : CleanProfileSystem c (2 * r + 1) η)
    (hr : 1 ≤ r) (hη : η ≤ 1 / 100)
    (hno : ∀ i, ¬ cycleGraph (2 * r + 1) ⊑ c.graph i)
    (i : Fin 3) (b : Bool) (hp : 0 < h.weight (cubeFace i b)) :
    ∀ u ∈ h.sets (cubeFace i b), ∀ v ∈ h.sets (cubeFace i b), ¬ (c.graph i).Adj u v := by
  obtain ⟨q, hqp, hq, hsep⟩ := h.tiling.exists_face_partner h.admissible i b hp
  apply no_side_edges_of_forbidden_odd_cycle (c.graph i) (h.sets (cubeFace i b)) (h.sets q)
    r h.defect hr (h.disjoint _ _ hqp.symm) (h.dense _ _ i hsep)
    (h.positive_core_large hr hη _ hp) _ (hno i)
  have hh := h.positive_core_large hr hη q hq
  omega

#print axioms CleanProfileSystem.no_fixed_colour_in_face

end Erdos556
