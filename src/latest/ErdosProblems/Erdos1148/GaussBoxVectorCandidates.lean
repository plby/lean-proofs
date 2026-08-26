import ErdosProblems.Erdos1148.GaussVectorEnergy
import ErdosProblems.Erdos1148.BoundedLatticeVectors
import ErdosProblems.Erdos1148.RotationEntryBounds

/-! # Uniformly finitely many short-vector candidates in a bounded Gauss box -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

lemma gaussFrame_abs_entries_le {r x h : ℝ} (hr : |r| ≤ 1) (hx : |x| ≤ 1)
    (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2) (i j : Fin 2) :
    |(unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) i j| ≤ 4 := by
  have hpos : 0 < h := by linarith
  have hU : ∀ i j : Fin 2, |unstableHorocycle r i j| ≤ 1 := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [unstableHorocycle, hr]
  have hB : ∀ i j : Fin 2, |upperTriangularFrame x h hpos.ne' i j| ≤ 2 := by
    intro i j
    fin_cases i <;> fin_cases j
    · change |h| ≤ 2
      rwa [abs_of_pos hpos]
    · change |x / h| ≤ 2
      rw [abs_div, abs_of_pos hpos]
      apply (div_le_iff₀ hpos).mpr
      linarith
    · change |(0 : ℝ)| ≤ 2
      norm_num
    · change |h⁻¹| ≤ 2
      rw [abs_inv, abs_of_pos hpos]
      rw [← one_div]
      exact (div_le_iff₀ hpos).mpr (by linarith)
  calc
    _ ≤ 2 * 1 * 2 := matrix_two_mul_entry_bound
      (unstableHorocycle r) (upperTriangularFrame x h hpos.ne')
      (by norm_num : (0 : ℝ) ≤ 1) (by norm_num : (0 : ℝ) ≤ 2) hU hB i j
    _ = 4 := by norm_num

lemma translated_gaussFrame_abs_entries_le (g : SL(2, ℝ)) {A : ℝ} (hA : 0 ≤ A)
    (hg : ∀ i j : Fin 2, |g i j| ≤ A) {r x h : ℝ}
    (hr : |r| ≤ 1) (hx : |x| ≤ 1) (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2) (i j : Fin 2) :
    |(g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) i j| ≤ 8 * A := by
  rw [mul_assoc]
  calc
    _ ≤ 2 * A * 4 := matrix_two_mul_entry_bound g
      (unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0))
      hA (by norm_num) hg (gaussFrame_abs_entries_le hr hx hh hh2) i j
    _ = _ := by ring

theorem exists_gaussBox_vector_candidates {A : ℝ} (hA : 0 ≤ A) :
    ∃ V : Finset (ℤ × ℤ), ∀ (g : SL(2, ℝ)), (∀ i j : Fin 2, |g i j| ≤ A) →
      ∀ (r x h : ℝ) (hr : |r| ≤ 1) (hx : |x| ≤ 1) (hh : 1 / 2 ≤ h) (hh2 : h ≤ 2)
        (u v : ℤ), modularVectorLengthSq
          (g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0)) u v ≤ 1 →
            (u, v) ∈ V := by
  classical
  let hfinite := finite_lattice_vectors_of_entry_bound (A := 8 * A) (by positivity)
    (R := 1) (by norm_num)
  refine ⟨hfinite.toFinset, ?_⟩
  intro g hg r x h hr hx hh hh2 u v hshort
  apply hfinite.mem_toFinset.mpr
  exact ⟨g * unstableHorocycle r * upperTriangularFrame x h (by linarith : h ≠ 0),
    translated_gaussFrame_abs_entries_le g hA hg hr hx hh hh2, hshort⟩

end Erdos1148.DukeArithmetic
