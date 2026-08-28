import Wikipedia.NoExoticSixSphere.RankSixUnitSpinor

/-! # Exact real homogeneity of the quadratic spinor matrix -/

noncomputable section

namespace NoExoticSixSphere.RankSixSkewMatrix

theorem spinorMatrix_real_smul_row0 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 0 j = (r ^ 2 • spinorMatrix q) 0 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul_row1 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 1 j = (r ^ 2 • spinorMatrix q) 1 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul_row2 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 2 j = (r ^ 2 • spinorMatrix q) 2 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul_row3 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 3 j = (r ^ 2 • spinorMatrix q) 3 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul_row4 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 4 j = (r ^ 2 • spinorMatrix q) 4 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul_row5 (r : ℝ) (q : Fin 4 → ℂ) (j : Fin 6) :
    spinorMatrix (fun k ↦ r • q k) 5 j = (r ^ 2 • spinorMatrix q) 5 j := by
  fin_cases j <;> simp [spinorMatrix, skew, Complex.real_smul] <;> ring

theorem spinorMatrix_real_smul (r : ℝ) (q : Fin 4 → ℂ) :
    spinorMatrix (fun i ↦ r • q i) = r ^ 2 • spinorMatrix q := by
  apply Matrix.ext
  intro i j
  fin_cases i
  · exact spinorMatrix_real_smul_row0 r q j
  · exact spinorMatrix_real_smul_row1 r q j
  · exact spinorMatrix_real_smul_row2 r q j
  · exact spinorMatrix_real_smul_row3 r q j
  · exact spinorMatrix_real_smul_row4 r q j
  · exact spinorMatrix_real_smul_row5 r q j

end NoExoticSixSphere.RankSixSkewMatrix
