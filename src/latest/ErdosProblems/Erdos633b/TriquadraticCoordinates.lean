import ErdosProblems.Erdos633b.Geometry
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Explicit coordinates for the case-(7) construction

The parameter is `s = a / c` in `(0,1)` and `d² = 4 - s²`.
These lemmas verify the algebraic layout from the TeX reconstruction.
The finite geometric partition and angle identification are separate obligations.
-/

namespace Erdos633b.TriquadraticCoordinates

noncomputable def z (s d : ℝ) : Plane := !₂[1 - s ^ 2 / 2, s * d / 2]
noncomputable def w (s d : ℝ) : Plane :=
  !₂[1 - 2 * s ^ 2 + s ^ 4 / 2, (2 - s ^ 2) * s * d / 2]
noncomputable def bigB (c s d : ℝ) : Plane := c ^ 2 • w s d
noncomputable def bigC (c s : ℝ) : Plane := !₂[c ^ 2 * (1 - s ^ 2), 0]
noncomputable def centerQ (c s d : ℝ) : Plane := (c * (1 - s ^ 2)) ^ 2 • z s d
noncomputable def sideD (c s d : ℝ) : Plane := (1 - s ^ 2) • bigB c s d
noncomputable def sideE (c s d : ℝ) : Plane :=
  bigC c s + (c ^ 2 * s) • !₂[-s / 2, d / 2]

theorem parameter_denominator_pos (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    0 < 1 - s ^ 2 ∧ 0 < 2 - s ^ 2 := by
  have h : s ^ 2 < 1 := by nlinarith
  constructor <;> linarith

theorem normalized_independent (c x y : ℝ) (hc : c ≠ 0) (hy : y ≠ 0) :
    AffineIndependent ℝ ![(0 : Plane), !₂[c, 0], !₂[x, y]] := by
  rw [affineIndependent_iff_of_fintype]
  intro f hf hv i
  rw [Finset.univ.weightedVSub_eq_linear_combination hf] at hv
  have hv0 : f 1 * c + f 2 * x = 0 := by
    simpa [Fin.sum_univ_three] using congrArg (fun p : Plane => p 0) hv
  have hv1 : f 2 * y = 0 := by
    simpa [Fin.sum_univ_three] using congrArg (fun p : Plane => p 1) hv
  have h2 : f 2 = 0 := (mul_eq_zero.mp hv1).resolve_right hy
  have h1 : f 1 = 0 := by
    rw [h2] at hv0
    simp only [zero_mul, add_zero] at hv0
    exact (mul_eq_zero.mp hv0).resolve_right hc
  have h0 : f 0 = 0 := by simpa [Fin.sum_univ_three, h1, h2] using hf
  fin_cases i
  · exact h0
  · exact h1
  · exact h2

/-- The reference tile is an actual nondegenerate Euclidean triangle. -/
noncomputable def reference (c s d : ℝ) (hc : 0 < c) (hs : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) : Triangle where
  points := ![0, !₂[c, 0], !₂[c * (1 - s ^ 2) * (1 - s ^ 2 / 2),
    c * (1 - s ^ 2) * (s * d / 2)]]
  independent := normalized_independent c _ _ hc.ne'
    (ne_of_gt (mul_pos (mul_pos hc (parameter_denominator_pos s hs hs1).1)
      (div_pos (mul_pos hs hd) (by norm_num))))

theorem unit_z (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) : ‖z s d‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [z, Fin.sum_univ_two]
  linear_combination (s ^ 2 / 4) * hd

theorem unit_w (s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) : ‖w s d‖ ^ 2 = 1 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [w, Fin.sum_univ_two]
  linear_combination (s ^ 2 * (2 - s ^ 2) ^ 2 / 4) * hd

theorem reference_third_side (c s d : ℝ) (hd : d ^ 2 = 4 - s ^ 2) :
    ‖(!₂[c, 0] : Plane) - (c * (1 - s ^ 2)) • z s d‖ ^ 2 = (c * s) ^ 2 := by
  rw [EuclideanSpace.real_norm_sq_eq]
  simp [z, Fin.sum_univ_two]
  linear_combination (c ^ 2 * (1 - s ^ 2) ^ 2 * s ^ 2 / 4) * hd

theorem center_barycentric (c s d : ℝ) (hs : 2 - s ^ 2 ≠ 0) :
    centerQ c s d = ((1 - s ^ 2) ^ 2 / (2 - s ^ 2)) • bigB c s d +
      ((1 - s ^ 2) / (2 - s ^ 2)) • bigC c s := by
  ext i
  fin_cases i
  · simp [centerQ, bigB, bigC, z, w]
    field_simp
    ring
  · simp [centerQ, bigB, bigC, z, w]
    field_simp

theorem sideE_barycentric (c s d : ℝ) (hs : 2 - s ^ 2 ≠ 0) :
    sideE c s d = (1 / (2 - s ^ 2)) • bigB c s d +
      ((1 - s ^ 2) / (2 - s ^ 2)) • bigC c s := by
  ext i
  fin_cases i
  · simp [sideE, bigB, bigC, w]
    field_simp
    ring
  · simp [sideE, bigB, bigC, w]
    field_simp

theorem center_coefficients (s : ℝ) (hs : 0 < s) (hs1 : s < 1) :
    0 < s ^ 2 ∧ 0 < (1 - s ^ 2) ^ 2 / (2 - s ^ 2) ∧
      0 < (1 - s ^ 2) / (2 - s ^ 2) ∧
      s ^ 2 + (1 - s ^ 2) ^ 2 / (2 - s ^ 2) + (1 - s ^ 2) / (2 - s ^ 2) = 1 := by
  obtain ⟨h1, h2⟩ := parameter_denominator_pos s hs hs1
  refine ⟨sq_pos_of_pos hs, div_pos (sq_pos_of_pos h1) h2, div_pos h1 h2, ?_⟩
  field_simp
  ring

theorem parallelogram_identity (c s d : ℝ) :
    bigB c s d = sideD c s d + sideE c s d - centerQ c s d := by
  ext i
  fin_cases i <;> simp [bigB, sideD, sideE, bigC, centerQ, z, w] <;> ring

theorem parallelogram_first_edge (c s d : ℝ) :
    sideE c s d - centerQ c s d = s ^ 2 • bigB c s d := by
  ext i
  fin_cases i <;> simp [sideE, centerQ, bigB, bigC, z, w] <;> ring

theorem parallelogram_second_edge (c s d : ℝ) (hs : 2 - s ^ 2 ≠ 0) :
    sideD c s d - centerQ c s d =
      ((1 - s ^ 2) / (2 - s ^ 2)) • (bigB c s d - bigC c s) := by
  ext i
  fin_cases i <;> simp [sideD, centerQ, bigB, bigC, z, w] <;> field_simp <;> ring

end Erdos633b.TriquadraticCoordinates
