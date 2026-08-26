import ErdosProblems.Erdos1148.UpperTriangularFrames
import ErdosProblems.Erdos1148.FlowVectorLengths

/-! # Unstable horocyclic coordinates and their action on lattice vectors -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

noncomputable def unstableHorocycle (r : ℝ) : SL(2, ℝ) :=
  ⟨!![1, 0; r, 1], by simp [Matrix.det_fin_two]⟩

lemma unstableHorocycle_add (r s : ℝ) :
    unstableHorocycle (r + s) = unstableHorocycle r * unstableHorocycle s := by
  apply Subtype.ext
  change (unstableHorocycle (r + s)).1 = (unstableHorocycle r).1 * (unstableHorocycle s).1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [unstableHorocycle, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

lemma frameRealVector_unstableHorocycle (r : ℝ) (v : Fin 2 → ℝ) :
    frameRealVector (unstableHorocycle r) v = ![v 0, v 1 - r * v 0] := by
  rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
  change (((unstableHorocycle r)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).mulVec v = _
  rw [Matrix.SpecialLinearGroup.coe_inv]
  ext i
  fin_cases i <;> simp [unstableHorocycle, Matrix.adjugate_fin_two, Matrix.mulVec,
    Matrix.vecHead, Matrix.vecTail, sub_eq_add_neg, add_comm] <;> ring

lemma frameRealVector_upperTriangularFrame_second (x h : ℝ) (hh : h ≠ 0) (v : Fin 2 → ℝ) :
    frameRealVector (upperTriangularFrame x h hh) v 1 = h * v 1 := by
  rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
  change (((upperTriangularFrame x h hh)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).mulVec v 1 = _
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [upperTriangularFrame, Matrix.adjugate_fin_two, Matrix.mulVec,
    Matrix.vecHead, Matrix.vecTail]

lemma frameRealVector_upperTriangularFrame_first (x h : ℝ) (hh : h ≠ 0) (v : Fin 2 → ℝ) :
    frameRealVector (upperTriangularFrame x h hh) v 0 = (v 0 - x * v 1) / h := by
  rw [frameRealVector, Matrix.SpecialLinearGroup.toLin'_symm_apply]
  change (((upperTriangularFrame x h hh)⁻¹ : SL(2, ℝ)) : Matrix (Fin 2) (Fin 2) ℝ).mulVec v 0 = _
  rw [Matrix.SpecialLinearGroup.coe_inv]
  simp [upperTriangularFrame, Matrix.adjugate_fin_two, Matrix.mulVec,
    Matrix.vecHead, Matrix.vecTail, div_eq_mul_inv]
  ring

theorem modularVector_horocycle_upper_first (g : SL(2, ℝ)) (r x h : ℝ) (hh : h ≠ 0)
    (u v : ℤ) :
    (modularVector (g * unstableHorocycle r * upperTriangularFrame x h hh) u v).1 =
      ((modularVector g u v).1 - x * ((modularVector g u v).2 - r * (modularVector g u v).1)) / h := by
  rw [← frameRealVector_pair, frameRealVector_comp, frameRealVector_upperTriangularFrame_first,
    frameRealVector_comp, frameRealVector_unstableHorocycle]
  have hp := frameRealVector_pair g u v
  have h0 := congrArg Prod.fst hp
  have h1 := congrArg Prod.snd hp
  dsimp only at h0 h1
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, h0, h1]

theorem modularVector_horocycle_upper_second (g : SL(2, ℝ)) (r x h : ℝ) (hh : h ≠ 0)
    (u v : ℤ) :
    (modularVector (g * unstableHorocycle r * upperTriangularFrame x h hh) u v).2 =
      h * ((modularVector g u v).2 - r * (modularVector g u v).1) := by
  rw [← frameRealVector_pair, frameRealVector_comp, frameRealVector_upperTriangularFrame_second,
    frameRealVector_comp, frameRealVector_unstableHorocycle]
  have hp := frameRealVector_pair g u v
  have h0 := congrArg Prod.fst hp
  have h1 := congrArg Prod.snd hp
  dsimp only at h0 h1
  simp only [Matrix.cons_val_one, Matrix.cons_val_fin_one, h0, h1]

end Erdos1148.DukeArithmetic
