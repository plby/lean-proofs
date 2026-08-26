import ErdosProblems.Erdos73.ProjectiveGridCoverage
import ErdosProblems.Erdos73.TreeAntipodalWord

/-! Unconditional high-defect noncrossing antipodal words from the canonical projective grid. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open Equiv

def projectiveTreeSwitchSystem {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    TreeSwitchSystem (ProjectivePort n) (Fin n × Fin n) where
  label := projectivePortLabel hn
  rotation := projectiveRotation hn hnEven
  rotation_label := projectiveRotation_label hn hnEven
  rotation_fiber := projectiveRotation_fiber hn hnEven
  switch := projectivePortSwitch n
  switch_involutive := projectivePortSwitch_involutive n
  tree := projectiveDiagonalGraph hn
  isTree := projectiveDiagonal_isTree hn hnEven
  switch_adj := projectivePortSwitch_adj hn
  edge_port := projectivePortSwitch_edge_cover hn
  port_unique := projectivePortSwitch_port_unique hn hnEven

theorem exists_projective_antipodal_word {n : ℕ} (hn : 2 ≤ n) (hnEven : n % 2 = 0) :
    ∃ N : ℕ, 0 < N ∧ ∃ word : Fin (2 * N) → Fin n × Fin n,
      Function.Surjective word ∧ NoncrossingPortWord word ∧
        twistedGridGraph n ≤ antipodalPortGraph word := by
  let C := projectiveTreeSwitchSystem hn hnEven
  let N := 2 * Fintype.card (ProjectiveFace n)
  have hfour : 4 ≤ n * n := Nat.mul_le_mul hn hn
  have hfaces := card_projectiveFace_add_one hn
  have hN : 0 < N := by dsimp only [N]; omega
  have hcard : Fintype.card (ProjectivePort n) = 2 * N := by
    simp only [ProjectivePort, Fintype.card_prod, Fintype.card_fin]
    dsimp only [N]
    omega
  have hcomm : Function.Commute (projectivePortPair n) C.contour := by
    intro d
    exact congrArg (fun p : Perm (ProjectivePort n) => p d)
      (projectivePair_commutes_contour hn hnEven).eq
  obtain ⟨word, hsurj, hNC, hcover⟩ := C.exists_noncrossing_antipodal_word hN hcard
    (projectivePortLabel_surjective hn) (projectivePortPair n) (projectivePortPair_involutive n)
    projectivePortPair_free hcomm (twistedCoordinateGraph n) (projective_coordinate_edge_covered hn hnEven)
  exact ⟨N, hN, word, hsurj, hNC, (twistedGridGraph_le_coordinateGraph n).trans hcover⟩

theorem exists_high_defect_antipodal_word (r : ℕ) :
    ∃ N : ℕ, 0 < N ∧ ∃ word : Fin (2 * N) → Fin (2 * (r + 1)) × Fin (2 * (r + 1)),
      Function.Surjective word ∧ NoncrossingPortWord word ∧
        2 * (antipodalPortGraph word).indepNum + (r + 1) ≤
          Fintype.card (Fin (2 * (r + 1)) × Fin (2 * (r + 1))) := by
  obtain ⟨N, hN, word, hsurj, hNC, hcover⟩ :=
    exists_projective_antipodal_word (n := 2 * (r + 1)) (by omega) (by omega)
  have hα := indepNum_anti hcover
  have hF := twistedGrid_full_defect r
  exact ⟨N, hN, word, hsurj, hNC, by omega⟩

end
end Erdos73
