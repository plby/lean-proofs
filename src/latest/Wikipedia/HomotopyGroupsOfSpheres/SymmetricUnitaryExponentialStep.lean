import Wikipedia.HomotopyGroupsOfSpheres.SymmetricUnitarySmoothness
import Wikipedia.HomotopyGroupsOfSpheres.ComplexSkewMatrices

/-! # Exponential motion in reversible trace-zero directions -/

noncomputable section

open scoped Matrix.Norms.Frobenius Manifold ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices

variable {N : Type*} [Fintype N] [DecidableEq N]

theorem exponential_reversible (B : unitary (Matrix N N ℂ)) (K : Matrix N N ℂ)
    (hrev : K.transpose * B.val = B.val * K) :
    (NormedSpace.exp K).transpose * B.val = B.val * NormedSpace.exp K := by
  have hconj : B.val * K * star B.val = K.transpose := by
    have h := congrArg (fun A : Matrix N N ℂ ↦ A * star B.val) hrev
    simpa only [mul_assoc, Unitary.mul_star_self_of_mem B.property, mul_one] using h.symm
  have hexp : NormedSpace.exp K.transpose = B.val * NormedSpace.exp K * star B.val := by
    rw [← hconj]
    exact Matrix.exp_units_conj (Unitary.toUnits B) K
  rw [← Matrix.exp_transpose, hexp, mul_assoc, Unitary.star_mul_self_of_mem B.property, mul_one]

def reversibleStep (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val)
    (t : ℝ) : SpecialSpace N :=
  ⟨⟨B.val.val * ComplexSkewMatrices.exponential (t • K), by
    change (B.val.val.val * NormedSpace.exp (t • K.val)).transpose =
      B.val.val.val * NormedSpace.exp (t • K.val)
    rw [Matrix.transpose_mul, B.val.property]
    apply exponential_reversible B.val.val
    rw [Matrix.transpose_smul, smul_mul_assoc, mul_smul_comm, hrev]⟩, by
    apply Circle.ext
    change (B.val.val.val * NormedSpace.exp (t • K.val)).det = 1
    have hb : B.val.val.val.det = 1 := congrArg (fun z : Circle ↦ (z : ℂ)) B.property
    have hk : star (t • K.val) = -(t • K.val) := (t • K).property
    rw [Matrix.det_mul, hb, one_mul, ComplexMatrixLocalLogarithm.det_exp_skew _ hk,
      Matrix.trace_smul, htrace, smul_zero, Complex.exp_zero]⟩

theorem reversibleStep_unitary (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val)
    (t : ℝ) : (reversibleStep B K htrace hrev t).val.val =
      B.val.val * ComplexSkewMatrices.exponential (t • K) := rfl

theorem reversibleStep_matrix (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val)
    (t : ℝ) : (reversibleStep B K htrace hrev t).val.val.val =
      B.val.val.val * NormedSpace.exp (t • K.val) := rfl

theorem reversibleStep_zero (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val) :
    reversibleStep B K htrace hrev 0 = B := by
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  rw [reversibleStep_matrix, zero_smul, NormedSpace.exp_zero, mul_one]

theorem contDiff_reversibleStep_matrix (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val) :
    ContDiff ℝ ∞ (fun t : ℝ ↦ (reversibleStep B K htrace hrev t).val.val.val) :=
  contDiff_const.mul (ComplexMatrixLocalLogarithm.contDiff_exp.comp
    (contDiff_id.smul contDiff_const))

theorem contMDiff_reversibleStep (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val) :
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, RealSymmetricMixing.DirectionSpace N) ∞
      (reversibleStep B K htrace hrev) := by
  apply Smoothness.contMDiff_iff_matrix.mpr
  simpa only [] using! (contDiff_reversibleStep_matrix B K htrace hrev).contMDiff

theorem hasDerivAt_reversibleStep_matrix (B : SpecialSpace N) (K : ComplexSkewMatrices.Space N)
    (htrace : K.val.trace = 0) (hrev : K.val.transpose * B.val.val.val = B.val.val.val * K.val)
    (t : ℝ) : HasDerivAt (fun s : ℝ ↦ (reversibleStep B K htrace hrev s).val.val.val)
      ((reversibleStep B K htrace hrev t).val.val.val * K.val) t := by
  simpa only [reversibleStep_matrix, mul_assoc] using!
    (hasDerivAt_exp_smul_const K.val t).const_mul B.val.val.val

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicSymmetricMatrices
