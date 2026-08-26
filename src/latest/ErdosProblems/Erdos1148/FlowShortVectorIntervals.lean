import ErdosProblems.Erdos1148.FlowVectorLengths
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-! # A fixed lattice vector is short on a single interval of flow times -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem convexOn_modularVectorLengthSq_flow (g : SL(2, ℝ)) (u v : ℤ) :
    ConvexOn ℝ Set.univ (fun t => modularVectorLengthSq (g * diagonalFlow t) u v) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  have hneg := convexOn_exp.2 (Set.mem_univ (-x)) (Set.mem_univ (-y)) ha hb hab
  have hpos := convexOn_exp.2 (Set.mem_univ x) (Set.mem_univ y) ha hb hab
  change Real.exp (a * -x + b * -y) ≤ a * Real.exp (-x) + b * Real.exp (-y) at hneg
  change Real.exp (a * x + b * y) ≤ a * Real.exp x + b * Real.exp y at hpos
  simp only [smul_eq_mul, modularVectorLengthSq_flow]
  rw [show -(a * x + b * y) = a * -x + b * -y by ring]
  nlinarith [mul_le_mul_of_nonneg_right hneg (sq_nonneg (modularVector g u v).1),
    mul_le_mul_of_nonneg_right hpos (sq_nonneg (modularVector g u v).2)]

theorem convex_short_vector_times (g : SL(2, ℝ)) (u v : ℤ) (R : ℝ) :
    Convex ℝ {t : ℝ | modularVectorLengthSq (g * diagonalFlow t) u v < R} := by
  simpa only [Set.mem_univ, true_and] using (convexOn_modularVectorLengthSq_flow g u v).convex_lt R

end Erdos1148.DukeArithmetic
