import ErdosProblems.Erdos1148.NeighborLifting

/-!
# Triangularizing a matrix with a unit entry

Integral row operations put a primitive two-by-two matrix into one of two
triangular charts. The second chart differs by exchanging the columns.
-/

namespace Erdos1148.DukeArithmetic

def swapMatrix {R : Type*} [CommRing R] : Matrix (Fin 2) (Fin 2) R := !![0, 1; 1, 0]

lemma det_swapMatrix {R : Type*} [CommRing R] : (swapMatrix (R := R)).det = -1 := by
  simp [swapMatrix, Matrix.det_fin_two]

lemma swapMatrix_mul_self {R : Type*} [CommRing R] :
    (swapMatrix : Matrix (Fin 2) (Fin 2) R) * swapMatrix = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two]

def pivotRowMatrix {R : Type*} [CommRing R] (v c : R) : Matrix (Fin 2) (Fin 2) R :=
  !![v, 0; -c * v, 1]

lemma det_pivotRowMatrix {R : Type*} [CommRing R] (v c : R) :
    (pivotRowMatrix v c).det = v := by
  simp [pivotRowMatrix, Matrix.det_fin_two]

lemma pivotRowMatrix_mul {R : Type*} [CommRing R]
    (A : Matrix (Fin 2) (Fin 2) R) (v : R) (hv : v * A 0 0 = 1) :
    pivotRowMatrix v (A 1 0) * A =
      neighborMatrix (A 1 1 - A 1 0 * v * A 0 1) (v * A 0 1) := by
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  fin_cases i <;> fin_cases j
  · change v * A 0 0 + 0 * A 1 0 = 1
    simpa only [zero_mul, add_zero] using hv
  · change v * A 0 1 + 0 * A 1 1 = v * A 0 1
    ring
  · change (-A 1 0 * v) * A 0 0 + 1 * A 1 0 = 0
    linear_combination -(A 1 0) * hv
  · change (-A 1 0 * v) * A 0 1 + 1 * A 1 1 = A 1 1 - A 1 0 * v * A 0 1
    ring

lemma triangularize_unit_first {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (A : Matrix (Fin 2) (Fin 2) R) (hA : A.det ≠ 0) (ha : IsUnit (A 0 0)) :
    ∃ (U : Matrix (Fin 2) (Fin 2) R) (δ z : R),
      IsUnit U.det ∧ δ ≠ 0 ∧ U * A = neighborMatrix δ z := by
  let u := ha.unit
  have hu : (u : R) = A 0 0 := ha.unit_spec
  let U := pivotRowMatrix (↑u⁻¹ : R) (A 1 0)
  have hU : IsUnit U.det := by
    rw [det_pivotRowMatrix]
    exact Units.isUnit _
  have heq := pivotRowMatrix_mul A (↑u⁻¹ : R) (by rw [← hu, Units.inv_mul])
  have hδ : A 1 1 - A 1 0 * (↑u⁻¹ : R) * A 0 1 ≠ 0 := by
    have hdet := congrArg Matrix.det heq
    rw [Matrix.det_mul, det_neighborMatrix] at hdet
    rw [← hdet]
    exact mul_ne_zero hU.ne_zero hA
  exact ⟨U, _, _, hU, hδ, heq⟩

lemma triangularize_unit_first_column {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (A : Matrix (Fin 2) (Fin 2) R) (hA : A.det ≠ 0)
    (ha : IsUnit (A 0 0) ∨ IsUnit (A 1 0)) :
    ∃ (U : Matrix (Fin 2) (Fin 2) R) (δ z : R),
      IsUnit U.det ∧ δ ≠ 0 ∧ U * A = neighborMatrix δ z := by
  rcases ha with ha | ha
  · exact triangularize_unit_first A hA ha
  have hswap : (swapMatrix * A).det ≠ 0 := by
    rw [Matrix.det_mul, det_swapMatrix]
    simpa only [neg_one_mul, neg_ne_zero] using hA
  have hpivot : IsUnit (((swapMatrix : Matrix (Fin 2) (Fin 2) R) * A) 0 0) := by
    simpa [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] using ha
  obtain ⟨U, δ, z, hU, hδ, heq⟩ := triangularize_unit_first (swapMatrix * A) hswap hpivot
  refine ⟨U * swapMatrix, δ, z, ?_, hδ, ?_⟩
  · rw [Matrix.det_mul, det_swapMatrix]
    exact hU.mul isUnit_neg_one
  · simpa only [Matrix.mul_assoc] using heq

theorem triangularize_unit_entry {R : Type*} [CommRing R] [NoZeroDivisors R] [Nontrivial R]
    (A : Matrix (Fin 2) (Fin 2) R) (hA : A.det ≠ 0) (ha : ∃ i j, IsUnit (A i j)) :
    ∃ (U : Matrix (Fin 2) (Fin 2) R) (δ z : R), IsUnit U.det ∧ δ ≠ 0 ∧
      (U * A = neighborMatrix δ z ∨ U * A * swapMatrix = neighborMatrix δ z) := by
  have hfirst_or_second :
      (IsUnit (A 0 0) ∨ IsUnit (A 1 0)) ∨ (IsUnit (A 0 1) ∨ IsUnit (A 1 1)) := by
    obtain ⟨i, j, hij⟩ := ha
    fin_cases i <;> fin_cases j <;> tauto
  rcases hfirst_or_second with hfirst | hsecond
  · obtain ⟨U, δ, z, hU, hδ, heq⟩ := triangularize_unit_first_column A hA hfirst
    exact ⟨U, δ, z, hU, hδ, Or.inl heq⟩
  have hswap : (A * swapMatrix).det ≠ 0 := by
    rw [Matrix.det_mul, det_swapMatrix]
    simpa only [mul_neg_one, neg_ne_zero] using hA
  have hpivot : IsUnit ((A * (swapMatrix : Matrix (Fin 2) (Fin 2) R)) 0 0) ∨
      IsUnit ((A * (swapMatrix : Matrix (Fin 2) (Fin 2) R)) 1 0) := by
    simpa [swapMatrix, Matrix.mul_apply, Fin.sum_univ_two] using hsecond
  obtain ⟨U, δ, z, hU, hδ, heq⟩ := triangularize_unit_first_column (A * swapMatrix) hswap hpivot
  refine ⟨U, δ, z, hU, hδ, Or.inr ?_⟩
  simpa only [Matrix.mul_assoc] using heq

end Erdos1148.DukeArithmetic
