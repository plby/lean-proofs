import ErdosProblems.Erdos577.TripleCoreCoverage

/-! Discard only the outside row and classify every ten-contact triangle core. -/

namespace Erdos577.TripleCorePatterns

open Finset

lemma triangleCount_rows (m : ℕ) : DenseOutside.triangleCount m =
    PawNine.rowCount m 1 + PawNine.rowCount m 2 + PawNine.rowCount m 3 := by
  rw [DenseTriangle.triangleCount_eq_sum, Fin.sum_univ_three]
  rfl

lemma diamond_trimmed {d : Fin 4} {m : Fin 65536} (h : DenseTriangle.DiamondRows d m.val) :
    DenseTriangle.DiamondRows d (JointCore.trimmed m.val) := by
  obtain ⟨h0, h3, low, hrows⟩ := h
  refine ⟨h0, h3, low, ?_⟩
  intro i j
  rw [JointCore.trimmed_bit, decide_eq_true (by omega : 4 ≤ 4 * (i.val + 1) + j.val),
    Bool.true_and]
  exact hrows i j

lemma classified_of_trimmed (d : Fin 4) (m : Fin 65536)
    (h : Classified d (JointCore.trimmed m.val)) : Classified d m.val := by
  obtain ⟨tag, cols, hcyc, h0, h1, hrows⟩ := h
  refine ⟨tag, cols, hcyc, h0, h1, ?_⟩
  intro i j hi
  have hr := hrows i j hi
  change (JointCore.trimmed m.val).testBit (4 * i.val + (cols j).val) =
    (rows tag i).testBit j.val at hr
  rw [JointCore.trimmed_core_bit m i (cols j) hi] at hr
  exact hr

theorem finite_classification (d : Fin 4) (m : Fin 65536)
    (hcount : PawNine.rowCount m.val 1 + PawNine.rowCount m.val 2 +
      PawNine.rowCount m.val 3 = 10) :
    DenseTriangle.Positive d m.val ∨ Classified d m.val := by
  have hrows : JointCore.rowSize (JointCore.row m.val 1) +
      JointCore.rowSize (JointCore.row m.val 2) +
        JointCore.rowSize (JointCore.row m.val 3) = 10 := by
    simpa only [JointCore.rowSize_eq] using hcount
  by_cases hd : d = 3
  · exact Or.inr (classified_of_trimmed d m (rows_classified d
      (JointCore.row m.val 1) (JointCore.row m.val 2) (JointCore.row m.val 3) hrows (Or.inl hd)))
  · rcases DenseTriangle.finite_classification d hd m
      (by rw [triangleCount_rows]; omega) with hpos | hshape
    · exact Or.inl hpos
    · exact Or.inr (classified_of_trimmed d m (rows_classified d
        (JointCore.row m.val 1) (JointCore.row m.val 2) (JointCore.row m.val 3) hrows
        (Or.inr (diamond_trimmed hshape))))

end Erdos577.TripleCorePatterns
