import ErdosProblems.Erdos73.ControlledOddCrossingWall
import ErdosProblems.Erdos73.CrossingPortWordDefect

/-! Quantitative original-haven defect extraction from a proved antipodal port word. -/

namespace Erdos73
noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq
open SimpleGraph Finset Erdos73Infrastructure.SimpleGraph ColumnHandleFamily

def portDefectHandleCount (N p : ℕ) : ℕ := 2 * (p + 5 * N + 4)

theorem crossingWallRowCount_odd_of_even {k : ℕ} (hk : Even k) (p : ℕ) :
    Odd (crossingWallRowCount k p) := by
  obtain ⟨a, ha⟩ := hk
  refine ⟨(6 * crossingWallStageCount k + 1) * a + 3 * crossingWallStageCount k +
    (2 * crossingWallPathCount k + p) + crossingWallStageCount k + 2, ?_⟩
  dsimp only [crossingWallRowCount]
  rw [ha]
  ring

variable {V U : Type*} [Fintype V] [Fintype U] [LinearOrder U]
variable {G : SimpleGraph V} {q ell N : ℕ}

theorem BrambleHaven.defect_of_antipodal_port_word
    (h : BrambleHaven G (lowOrderOddSides G ell) q) (p : ℕ)
    (horder : oddCrossingWallHavenBound (portDefectHandleCount N p) p ≤ q)
    (hno : ¬ HasOddCyclePacking p G) (hN : 0 < N)
    (label : Fin (2 * N) → U) (hsurj : Function.Surjective label)
    (hNC : NoncrossingPortWord label) (d : ℕ)
    (hF : 2 * (antipodalPortGraph label).indepNum + d ≤ Fintype.card U) :
    HasIndependenceDefectAtLeast d G := by
  obtain ⟨M, _, S, _, col, ⟨b, hb⟩, _, hhandles⟩ :=
    h.exists_controlled_odd_crossing_wall_of_order (portDefectHandleCount N p) p
      (by dsimp only [portDefectHandleCount]; omega) horder hno
  apply defect_of_crossing_handles hhandles b hb hN
    (by dsimp only [portDefectHandleCount]; omega)
    (by dsimp only [portDefectHandleCount]; omega)
    (crossingWallRowCount_odd_of_even ⟨p + 5 * N + 4, by
      dsimp only [portDefectHandleCount]; omega⟩ p) label hsurj hNC d hF

end
end Erdos73
