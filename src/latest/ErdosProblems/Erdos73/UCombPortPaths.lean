import ErdosProblems.Erdos73.UCombPathContainment

/-! Actual simple paths between prescribed ports inside a U-shaped comb. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph

variable {c r : ℕ} {A B : Finset ℕ} {L M a b j : ℕ}

theorem exists_left_uComb_port_path {u v : ElementaryWallVertex c r}
    (hu : IsLeftUCombPort A L a b u) (hv : IsLeftUCombPort A L a b v)
    (hj : 0 < j) (hjM : j ≤ M) (hc : 2 * M + 3 ≤ c) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ rectangularUComb A B L M a b j := by
  have huc : u.val.2.val ≤ 2 * j + 1 := by have hh := hu.2.2.2.2; omega
  have hvc : v.val.2.val ≤ 2 * j + 1 := by have hh := hv.2.2.2.2; omega
  by_cases huv : u.val.1.val ≤ v.val.1.val
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_left_hook_path u v huv j hj (by omega) huc hvc
    have hP' : P.vertexSet ⊆ brickLeftHook u.val.1.val v.val.1.val j := by
      simpa only [Finset.subset_iff, GraphPath.vertexSet, List.mem_toFinset] using hP
    exact ⟨P, hs, ht, hP'.trans (leftHook_subset_rectangularUComb hu hv hjM)⟩
  · obtain ⟨P, hs, ht, hP⟩ :=
      exists_brick_left_hook_path v u (by omega) j hj (by omega) hvc huc
    refine ⟨P.reverse, ht, hs, ?_⟩
    rw [GraphPath.reverse_vertexSet]
    apply (leftHook_subset_rectangularUComb hv hu hjM).trans'
    simpa only [Finset.subset_iff, GraphPath.vertexSet, List.mem_toFinset] using hP

theorem exists_right_uComb_port_path {u v : ElementaryWallVertex c r}
    (hu : IsRightUCombPort B L M a b u) (hv : IsRightUCombPort B L M a b v)
    (hj : 0 < j) (hjM : j ≤ M) (hc : 2 * M + 3 ≤ c) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ rectangularUComb A B L M a b j := by
  have huc : 2 * (c - j - 1) ≤ u.val.2.val := by have hh := hu.2.2.2.2; omega
  have hvc : 2 * (c - j - 1) ≤ v.val.2.val := by have hh := hv.2.2.2.2; omega
  by_cases huv : u.val.1.val ≤ v.val.1.val
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_right_hook_path u v huv (c - j - 1)
      (by omega) (by omega) huc hvc
    have hP' : P.vertexSet ⊆ brickRightHook u.val.1.val v.val.1.val (c - j - 1) := by
      simpa only [Finset.subset_iff, GraphPath.vertexSet, List.mem_toFinset] using hP
    exact ⟨P, hs, ht, hP'.trans (rightHook_subset_rectangularUComb hu hv hjM hc)⟩
  · obtain ⟨P, hs, ht, hP⟩ := exists_brick_right_hook_path v u (by omega) (c - j - 1)
      (by omega) (by omega) hvc huc
    refine ⟨P.reverse, ht, hs, ?_⟩
    rw [GraphPath.reverse_vertexSet]
    apply (rightHook_subset_rectangularUComb hv hu hjM hc).trans'
    simpa only [Finset.subset_iff, GraphPath.vertexSet, List.mem_toFinset] using hP

theorem exists_cross_uComb_port_path {u v : ElementaryWallVertex c r}
    (hu : IsLeftUCombPort A L a b u) (hv : IsRightUCombPort B L M a b v)
    (hj : 0 < j) (hjM : j ≤ M) (hc : 2 * M + 3 ≤ c) (hr : uCombBase L M < r) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ rectangularUComb A B L M a b j := by
  have haB : a ≤ uCombBase L M := by
    dsimp only [IsLeftUCombPort, uCombBase] at *
    omega
  have hBb : uCombBase L M ≤ b := by
    dsimp only [IsRightUCombPort, uCombBase] at *
    omega
  have hub : u.val.1.val ≤ uCombBase L M - 2 * j := by
    have hh := hu.2.1
    dsimp only [uCombBase]
    omega
  have hvb : v.val.1.val ≤ uCombBase L M - 2 * j := by
    have hh := hv.2.1
    dsimp only [uCombBase]
    omega
  obtain ⟨P, hs, ht, hP⟩ := exists_brick_bottom_u_path u v (uCombBase L M - 2 * j) j
    hub hvb (by omega) hj (by omega)
    (by have hh := hu.2.2.2.2; omega) (by have hh := hv.2.2.2.2; omega)
  refine ⟨P, hs, ht, fun w hw => ?_⟩
  rcases hP w hw with hw | hw | hw
  · exact leftBoundaryArm_subset_rectangularUComb hu hBb hw
  · exact rightBoundaryArm_subset_rectangularUComb hv haB hjM hc hw
  · exact crossbar_mem_rectangularUComb haB hBb hw

def IsUCombPort (A B : Finset ℕ) (L M a b : ℕ) (u : ElementaryWallVertex c r) : Prop :=
  IsLeftUCombPort A L a b u ∨ IsRightUCombPort B L M a b u

theorem exists_uComb_port_path {u v : ElementaryWallVertex c r}
    (hu : IsUCombPort A B L M a b u) (hv : IsUCombPort A B L M a b v)
    (hj : 0 < j) (hjM : j ≤ M) (hc : 2 * M + 3 ≤ c) (hr : uCombBase L M < r) :
    ∃ P : GraphPath (elementaryWall c r), P.source = u ∧ P.target = v ∧
      P.vertexSet ⊆ rectangularUComb A B L M a b j := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact exists_left_uComb_port_path hu hv hj hjM hc
  · exact exists_cross_uComb_port_path hu hv hj hjM hc hr
  · obtain ⟨P, hs, ht, hP⟩ := exists_cross_uComb_port_path hv hu hj hjM hc hr
    exact ⟨P.reverse, ht, hs, by simpa only [GraphPath.reverse_vertexSet] using hP⟩
  · exact exists_right_uComb_port_path hu hv hj hjM hc

end
end Erdos73
