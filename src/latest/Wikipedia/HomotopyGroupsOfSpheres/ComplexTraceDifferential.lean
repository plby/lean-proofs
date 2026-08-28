import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductDifferential
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointTrace

/-! # The trace differential is nonsingular at every counted preimage

This computes one real two-dimensional factor of the derivative. It does
not by itself compute the local degree of the full seven-dimensional map.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def traceVariation (t v : ℂ) : ℂ := 2 * t * v + 2 * star v

def traceVariationMatrix (t : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (t.re + 1), -2 * t.im; 2 * t.im, 2 * (t.re - 1)]

theorem hasDerivAt_tracePolynomial (w : ℝ → ℂ) (v : ℂ) (x : ℝ)
    (hw : HasDerivAt w v x) :
    HasDerivAt (fun t ↦ w t ^ 2 + 2 * star (w t)) (traceVariation (w x) v) x := by
  convert (hw.mul hw).add (hw.star.const_mul 2) using 1 <;> try rfl
  · funext t
    simp only [pow_two, Pi.add_apply, Pi.mul_apply]
  · unfold traceVariation
    ring

theorem traceVariation_coordinates (t v : ℂ) :
    ![(traceVariation t v).re, (traceVariation t v).im] =
      traceVariationMatrix t *ᵥ ![v.re, v.im] := by
  funext r
  fin_cases r <;>
    simp [traceVariation, traceVariationMatrix, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two, Complex.mul_re, Complex.mul_im] <;> ring

theorem traceVariationMatrix_det (t : ℂ) :
    (traceVariationMatrix t).det = 4 * (Complex.normSq t - 1) := by
  simp [traceVariationMatrix, Matrix.det_fin_two, Complex.normSq_apply]
  ring

theorem traceVariationMatrix_det_neg (t : ℂ) (ht : Complex.normSq t < 1) :
    (traceVariationMatrix t).det < 0 := by
  rw [traceVariationMatrix_det]
  linarith

theorem traceVariation_eq_zero (t v : ℂ) (ht : Complex.normSq t < 1)
    (hv : traceVariation t v = 0) : v = 0 := by
  have he : t * v = -star v := by
    unfold traceVariation at hv
    linear_combination hv / 2
  have hn := congrArg Complex.normSq he
  simp only [map_mul, Complex.normSq_neg, Complex.star_def, Complex.normSq_conj] at hn
  have hp : (Complex.normSq t - 1) * Complex.normSq v = 0 := by
    linear_combination hn
  exact Complex.normSq_eq_zero.mp
    ((mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr (ne_of_lt ht)))

theorem squareSumVariation_eq_zero_of_symmetricVariation (z v : Vector)
    (hz : Complex.normSq (squareSum z) < 1) (hv : symmetricVariation z v = 0) :
    squareSumVariation z v = 0 := by
  apply traceVariation_eq_zero _ _ hz
  change 2 * squareSum z * squareSumVariation z v + 2 * star (squareSumVariation z v) = 0
  rw [← symmetricVariation_trace, hv, Matrix.trace_zero]

theorem traceRoot_normSq : Complex.normSq traceRoot = 2 - Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  simp only [traceRoot, Complex.normSq_apply]
  change (-(Real.sqrt 2 / 2)) * (-(Real.sqrt 2 / 2)) +
    (1 - Real.sqrt 2 / 2) * (1 - Real.sqrt 2 / 2) = _
  nlinarith

theorem traceRoot_normSq_lt_one : Complex.normSq traceRoot < 1 := by
  rw [traceRoot_normSq]
  have hs : 1 < Real.sqrt (2 : ℝ) :=
    (Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)).mpr (by norm_num)
  linarith

theorem midpoint_squareSum_normSq (z : UnitSphere) (u : unitary ℂ)
    (hu : u.val ^ 3 = -1)
    (hB : (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    Complex.normSq (squareSum z.val) = 2 - Real.sqrt 2 := by
  rw [midpoint_squareSum z u hu hB, Complex.normSq_eq_norm_sq,
    norm_mul, norm_neg, norm_star, unitary_complex_norm, one_mul,
    ← Complex.normSq_eq_norm_sq, traceRoot_normSq]

theorem midpoint_squareSum_normSq_lt_one (z : UnitSphere)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    Complex.normSq (squareSum z.val) < 1 := by
  obtain ⟨u, hu, hB⟩ := midpoint_target_forward (symmetricMap z) (symmetricMap_det z) h
  rw [midpoint_squareSum_normSq z u hu hB, ← traceRoot_normSq]
  exact traceRoot_normSq_lt_one

theorem midpoint_squareSumVariation_kernel (z : UnitSphere) (v : Vector)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn)
    (hv : symmetricVariation z.val v = 0) : squareSumVariation z.val v = 0 :=
  squareSumVariation_eq_zero_of_symmetricVariation z.val v
    (midpoint_squareSum_normSq_lt_one z h) hv

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
