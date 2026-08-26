import ErdosProblems.Erdos633b.FiniteAngleTable01
import ErdosProblems.Erdos633b.FiniteAngleTable02
import ErdosProblems.Erdos633b.FiniteAngleTable03
import ErdosProblems.Erdos633b.FiniteAngleTable04
import ErdosProblems.Erdos633b.FiniteAngleTable05
import ErdosProblems.Erdos633b.FiniteAngleTable06
import ErdosProblems.Erdos633b.FiniteAngleTable07
import ErdosProblems.Erdos633b.FiniteAngleTable08
import ErdosProblems.Erdos633b.FiniteAngleTable09
import ErdosProblems.Erdos633b.FiniteAngleTable10
import ErdosProblems.Erdos633b.FiniteAngleTable11
import ErdosProblems.Erdos633b.FiniteAngleTable12
import ErdosProblems.Erdos633b.FiniteAngleTable13
import ErdosProblems.Erdos633b.FiniteAngleTable14
import ErdosProblems.Erdos633b.FiniteAngleTable15
import ErdosProblems.Erdos633b.FiniteAngleTable16
import ErdosProblems.Erdos633b.FiniteAngleTable17
import ErdosProblems.Erdos633b.FiniteAngleTable18
import ErdosProblems.Erdos633b.FiniteAngleTable19
import ErdosProblems.Erdos633b.FiniteAngleTable20
import ErdosProblems.Erdos633b.FiniteAngleTable21
import ErdosProblems.Erdos633b.FiniteAngleTable22
import ErdosProblems.Erdos633b.FiniteAngleTable23
import ErdosProblems.Erdos633b.FiniteAngleTable24
import ErdosProblems.Erdos633b.FiniteAngleTable25

/-! Exact finite tile-angle intersection domain and its complete coverage. -/

namespace Erdos633b

def finiteAngleTables (i : Fin 25) : Finset (ℕ × ℕ × ℕ) :=
  match i.val with
  | 0 => finiteAngleTable01
  | 1 => finiteAngleTable02
  | 2 => finiteAngleTable03
  | 3 => finiteAngleTable04
  | 4 => finiteAngleTable05
  | 5 => finiteAngleTable06
  | 6 => finiteAngleTable07
  | 7 => finiteAngleTable08
  | 8 => finiteAngleTable09
  | 9 => finiteAngleTable10
  | 10 => finiteAngleTable11
  | 11 => finiteAngleTable12
  | 12 => finiteAngleTable13
  | 13 => finiteAngleTable14
  | 14 => finiteAngleTable15
  | 15 => finiteAngleTable16
  | 16 => finiteAngleTable17
  | 17 => finiteAngleTable18
  | 18 => finiteAngleTable19
  | 19 => finiteAngleTable20
  | 20 => finiteAngleTable21
  | 21 => finiteAngleTable22
  | 22 => finiteAngleTable23
  | 23 => finiteAngleTable24
  | _ => finiteAngleTable25

def finiteAngleCandidates : Finset (ℕ × ℕ × ℕ) :=
  Finset.univ.biUnion finiteAngleTables

theorem finite_angle_candidates_card : finiteAngleCandidates.card = 293 := by
  decide +kernel

theorem finite_angle_tables_total_entries : (∑ i : Fin 25, (finiteAngleTables i).card) = 323 := by
  decide +kernel

theorem finite_angle_candidates_primitive :
    ∀ v ∈ finiteAngleCandidates, Nat.gcd v.1 (Nat.gcd v.2.1 v.2.2) = 1 := by
  decide +kernel

theorem finite_angle_tables_subset (i : Fin 25) :
    finiteAngleTables i ⊆ finiteAngleCandidates := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hv⟩

theorem finite_angle_table_image_subset (i : Fin 25) :
    (finiteAngleTables i).image angleTablePair ⊆ finiteAngleCandidates.image angleTablePair :=
  Finset.image_subset_image (finite_angle_tables_subset i)

theorem finite_angle_candidates_valid (v : ℕ × ℕ × ℕ) (hv : v ∈ finiteAngleCandidates) :
    3 ≤ v.1 ∧ v.1 ≤ 140 ∧ 0 < v.2.1 ∧ v.2.1 < v.2.2 ∧
    v.2.1 + 2 * v.2.2 < v.1 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hv
  fin_cases i
  · exact finite_angle_table_01_valid v hi
  · exact finite_angle_table_02_valid v hi
  · exact finite_angle_table_03_valid v hi
  · exact finite_angle_table_04_valid v hi
  · exact finite_angle_table_05_valid v hi
  · exact finite_angle_table_06_valid v hi
  · exact finite_angle_table_07_valid v hi
  · exact finite_angle_table_08_valid v hi
  · exact finite_angle_table_09_valid v hi
  · exact finite_angle_table_10_valid v hi
  · exact finite_angle_table_11_valid v hi
  · exact finite_angle_table_12_valid v hi
  · exact finite_angle_table_13_valid v hi
  · exact finite_angle_table_14_valid v hi
  · exact finite_angle_table_15_valid v hi
  · exact finite_angle_table_16_valid v hi
  · exact finite_angle_table_17_valid v hi
  · exact finite_angle_table_18_valid v hi
  · exact finite_angle_table_19_valid v hi
  · exact finite_angle_table_20_valid v hi
  · exact finite_angle_table_21_valid v hi
  · exact finite_angle_table_22_valid v hi
  · exact finite_angle_table_23_valid v hi
  · exact finite_angle_table_24_valid v hi
  · exact finite_angle_table_25_valid v hi

theorem finite_angle_candidates_exhaustive (P Q R : ℕ) (hP : P ≤ 21)
    (hQ : Q ≤ 5) (hR : R ≤ 1) (t : ℤ × ℤ × ℤ)
    (ht : t ∈ orderedNonrightRelationTriples) (ha : AdmissibleCornerData P Q R t) :
    cornerAnglePair P Q R t ∈ finiteAngleCandidates.image angleTablePair := by
  have hlist : orderedNonrightRelationTriples =
    {(0, 3, 1),
     (0, 4, 1),
     (0, 5, 1),
     (0, 5, 2),
     (0, 7, 2),
     (0, 9, 2),
     (0, 11, 2),
     (1, -6, -1),
     (1, -5, -1),
     (1, -4, -1),
     (1, -3, -1),
     (1, 5, 2),
     (1, 6, 2),
     (1, 7, 2),
     (1, 8, 2),
     (1, 9, 2),
     (1, 10, 2),
     (2, -1, 0),
     (2, 3, 1),
     (3, 1, 1),
     (3, 2, 1),
     (3, 3, 1),
     (3, 4, 2),
     (4, 3, 2),
     (5, 5, 3)} := by decide
  rw [hlist] at ht
  simp only [Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact finite_angle_table_image_subset 0
      (finite_angle_table_01_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 1
      (finite_angle_table_02_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 2
      (finite_angle_table_03_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 3
      (finite_angle_table_04_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 4
      (finite_angle_table_05_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 5
      (finite_angle_table_06_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 6
      (finite_angle_table_07_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 7
      (finite_angle_table_08_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 8
      (finite_angle_table_09_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 9
      (finite_angle_table_10_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 10
      (finite_angle_table_11_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 11
      (finite_angle_table_12_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 12
      (finite_angle_table_13_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 13
      (finite_angle_table_14_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 14
      (finite_angle_table_15_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 15
      (finite_angle_table_16_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 16
      (finite_angle_table_17_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 17
      (finite_angle_table_18_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 18
      (finite_angle_table_19_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 19
      (finite_angle_table_20_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 20
      (finite_angle_table_21_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 21
      (finite_angle_table_22_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 22
      (finite_angle_table_23_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 23
      (finite_angle_table_24_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)
  · exact finite_angle_table_image_subset 24
      (finite_angle_table_25_exhaustive ⟨P, by omega⟩ ⟨Q, by omega⟩ ⟨R, by omega⟩ ha)

end Erdos633b
