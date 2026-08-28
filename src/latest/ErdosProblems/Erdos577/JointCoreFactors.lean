import ErdosProblems.Erdos577.JointCoreFactors0
import ErdosProblems.Erdos577.JointCoreFactors1
import ErdosProblems.Erdos577.JointCoreFactors2
import ErdosProblems.Erdos577.JointCoreFactors3
import ErdosProblems.Erdos577.JointCoreFactors4
import ErdosProblems.Erdos577.JointCoreFactors5
import ErdosProblems.Erdos577.JointCoreFactors6
import ErdosProblems.Erdos577.JointCoreFactors7

/-! Every pair of distinct neighbors of an outside vertex yields a factor. -/

namespace Erdos577.JointCore

open Finset

theorem outside_factor_lt (tag : Fin 8) (i j : Fin 7) (h : i < j) :
    LocalFactor (outsideGraph tag i j) univ := by
  fin_cases tag
  · exact outside_factor_0 i j h
  · exact outside_factor_1 i j h
  · exact outside_factor_2 i j h
  · exact outside_factor_3 i j h
  · exact outside_factor_4 i j h
  · exact outside_factor_5 i j h
  · exact outside_factor_6 i j h
  · exact outside_factor_7 i j h

theorem outside_factor (tag : Fin 8) (i j : Fin 7) (h : i ≠ j) :
    LocalFactor (outsideGraph tag i j) univ := by
  rcases lt_or_gt_of_ne h with hij | hji
  · exact outside_factor_lt tag i j hij
  · rw [outsideGraph_comm]
    exact outside_factor_lt tag j i hji

end Erdos577.JointCore
