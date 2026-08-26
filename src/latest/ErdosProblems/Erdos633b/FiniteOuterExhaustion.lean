import ErdosProblems.Erdos633b.ActualOuterAngleFilters
import ErdosProblems.Erdos633b.FiniteOuterTable01
import ErdosProblems.Erdos633b.FiniteOuterTable02
import ErdosProblems.Erdos633b.FiniteOuterTable03
import ErdosProblems.Erdos633b.FiniteOuterTable04
import ErdosProblems.Erdos633b.FiniteOuterTable05
import ErdosProblems.Erdos633b.FiniteOuterTable06
import ErdosProblems.Erdos633b.FiniteOuterTable07
import ErdosProblems.Erdos633b.FiniteOuterTable08
import ErdosProblems.Erdos633b.FiniteOuterTable09
import ErdosProblems.Erdos633b.FiniteOuterTable10
import ErdosProblems.Erdos633b.FiniteOuterTable11
import ErdosProblems.Erdos633b.FiniteOuterTable12
import ErdosProblems.Erdos633b.FiniteOuterTable13
import ErdosProblems.Erdos633b.FiniteOuterTable14
import ErdosProblems.Erdos633b.FiniteOuterTable15
import ErdosProblems.Erdos633b.FiniteOuterTable16
import ErdosProblems.Erdos633b.FiniteOuterTable17
import ErdosProblems.Erdos633b.FiniteOuterTable18
import ErdosProblems.Erdos633b.FiniteOuterTable19
import ErdosProblems.Erdos633b.FiniteOuterTable20
import ErdosProblems.Erdos633b.FiniteOuterTable21
import ErdosProblems.Erdos633b.FiniteOuterTable22
import ErdosProblems.Erdos633b.FiniteOuterTable23
import ErdosProblems.Erdos633b.FiniteOuterTable24
import ErdosProblems.Erdos633b.FiniteOuterTable25

/-! Complete 52-pair angle reduction for actual hypothetical counterexamples.
The remaining pairs still require their geometric exclusions. -/

namespace Erdos633b

theorem finite_outer_candidates_exhaustive (v : ℕ × ℕ × ℕ)
    (hv : v ∈ finiteAngleCandidates) (a b : Fin v.1)
    (ha : FiniteOuterAdmissible v a.val b.val) : (v, a.val, b.val) ∈ finiteOuterCandidates := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  fin_cases i
  · exact finite_outer_table_01_exhaustive v hi a b ha
  · exact finite_outer_table_02_exhaustive v hi a b ha
  · exact finite_outer_table_03_exhaustive v hi a b ha
  · exact finite_outer_table_04_exhaustive v hi a b ha
  · exact finite_outer_table_05_exhaustive v hi a b ha
  · exact finite_outer_table_06_exhaustive v hi a b ha
  · exact finite_outer_table_07_exhaustive v hi a b ha
  · exact finite_outer_table_08_exhaustive v hi a b ha
  · exact finite_outer_table_09_exhaustive v hi a b ha
  · exact finite_outer_table_10_exhaustive v hi a b ha
  · exact finite_outer_table_11_exhaustive v hi a b ha
  · exact finite_outer_table_12_exhaustive v hi a b ha
  · exact finite_outer_table_13_exhaustive v hi a b ha
  · exact finite_outer_table_14_exhaustive v hi a b ha
  · exact finite_outer_table_15_exhaustive v hi a b ha
  · exact finite_outer_table_16_exhaustive v hi a b ha
  · exact finite_outer_table_17_exhaustive v hi a b ha
  · exact finite_outer_table_18_exhaustive v hi a b ha
  · exact finite_outer_table_19_exhaustive v hi a b ha
  · exact finite_outer_table_20_exhaustive v hi a b ha
  · exact finite_outer_table_21_exhaustive v hi a b ha
  · exact finite_outer_table_22_exhaustive v hi a b ha
  · exact finite_outer_table_23_exhaustive v hi a b ha
  · exact finite_outer_table_24_exhaustive v hi a b ha
  · exact finite_outer_table_25_exhaustive v hi a b ha

namespace Tiling

theorem counterexample_finite_angle_pairs {T : Triangle} {n : ℕ}
    (d : Tiling T n) (hn : ¬ IsSquare n) (hnot : ¬ EightCases T) :
    ∃ e f : Equiv.Perm (Fin 3), ∃ p ∈ finiteOuterCandidates,
      (∀ i, Triangle.angle (d.tile.reindex e) i =
        (angleTableWeights p.1 i : ℝ) * (Real.pi / p.1.1)) ∧
      (∀ i, Triangle.angle (T.reindex f) i =
        (angleTableWeights (p.1.1, p.2.1, p.2.2) i : ℝ) * (Real.pi / p.1.1)) := by
  obtain ⟨e, f, v, hv, a, b, hw, ha, hf⟩ := d.counterexample_finite_outer_filters hn hnot
  exact ⟨e, f, (v, a.val, b.val), finite_outer_candidates_exhaustive v hv a b hf, hw, ha⟩

end Tiling
end Erdos633b
