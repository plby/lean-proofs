import ErdosProblems.Erdos1148.PellOrderUnit

/-! # The real embedding and the logarithm of a Pell unit -/

namespace Erdos1148.DukeArithmetic

noncomputable def quadraticRealEmbedding {d : ℤ} (hd : 0 < d) :
    QuadraticDiscrAlgebra d →ₐ[ℚ] ℝ :=
  QuadraticAlgebra.lift ⟨Real.sqrt (d : ℝ), by
    have hdR : (0 : ℝ) ≤ d := by exact_mod_cast hd.le
    simpa [Algebra.smul_def, pow_two] using Real.sq_sqrt hdR⟩

lemma quadraticRealEmbedding_apply {d : ℤ} (hd : 0 < d) (w : QuadraticDiscrAlgebra d) :
    quadraticRealEmbedding hd w = (w.re : ℝ) + (w.im : ℝ) * Real.sqrt (d : ℝ) := by
  change w.re • (1 : ℝ) + w.im • Real.sqrt (d : ℝ) = _
  simp [Algebra.smul_def]

lemma quadraticRealEmbedding_pell {d : ℤ} (hd : 0 < d) (T U : ℤ) :
    quadraticRealEmbedding hd (pellQuadraticElement d T U) =
      (T : ℝ) / 2 + (U : ℝ) / 2 * Real.sqrt (d : ℝ) := by
  rw [quadraticRealEmbedding_apply]
  simp [pellQuadraticElement]

theorem quadraticRealEmbedding_pell_period {d : ℤ} (hd : 0 < d) (T U : ℤ) (s : ℝ)
    (hT : (T : ℝ) = 2 * Real.cosh (s / 2))
    (hU : (U : ℝ) = -2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ)) :
    quadraticRealEmbedding hd (pellQuadraticElement d T U) = Real.exp (-(s / 2)) := by
  have hρ : Real.sqrt (d : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hd)).ne'
  rw [quadraticRealEmbedding_pell, hT, hU]
  have heq : 2 * Real.cosh (s / 2) / 2 +
      (-2 * Real.sinh (s / 2) / Real.sqrt (d : ℝ)) / 2 * Real.sqrt (d : ℝ) =
      Real.cosh (s / 2) - Real.sinh (s / 2) := by field_simp; ring
  rw [heq]
  simp [Real.cosh_eq, Real.sinh_eq]
  ring

end Erdos1148.DukeArithmetic
