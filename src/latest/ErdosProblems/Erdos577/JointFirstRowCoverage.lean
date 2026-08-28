import ErdosProblems.Erdos577.JointFirstRowCoverage0
import ErdosProblems.Erdos577.JointFirstRowCoverage1
import ErdosProblems.Erdos577.JointFirstRowCoverage2
import ErdosProblems.Erdos577.JointFirstRowCoverage3

/-! The complete finite classification of the four independent rows. -/

namespace Erdos577.JointFirstRows

theorem coverage_diagonal (d : Fin 4) (hi lo : Fin 256)
    (h : Hypotheses (256 * hi.val + lo.val)) :
    covered d (256 * hi.val + lo.val) = true := by
  fin_cases d
  · exact coverage_diagonal_0 hi lo h
  · exact coverage_diagonal_1 hi lo h
  · exact coverage_diagonal_2 hi lo h
  · exact coverage_diagonal_3 hi lo h

theorem finite_classification (d : Fin 4) (m : Fin 65536) (h : Hypotheses m.val) :
    Classified d m.val := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : 256 * hi.val + lo.val = m.val := by dsimp [hi, lo]; omega
  apply covered_classified
  rw [← he]
  exact coverage_diagonal d hi lo (by rwa [he])

end Erdos577.JointFirstRows
