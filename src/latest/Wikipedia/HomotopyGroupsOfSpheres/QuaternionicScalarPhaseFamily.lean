import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicProjectedLocalInverse

/-!
# A regular scalar-phase family through every target preimage

Scaling the symmetric matrix by any unit complex number keeps its midpoint
first column fixed. The full derivative remains injective along this family;
the matrix determinant is constant along source curves, but need not be one.
This family will compare orientations at the cube-root-related preimages.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres

namespace QuaternionicSymmetricMatrices

def circleUnitary (q : Circle) : unitary ℂ :=
  ⟨q, Unitary.mem_iff_self_mul_star.mpr (by
    rw [Complex.star_def, Complex.mul_conj, Circle.normSq_coe, Complex.ofReal_one])⟩

theorem circle_coe_ne_zero (q : Circle) : (q : ℂ) ≠ 0 :=
  ComplexCrossProductUnitary.unitary_complex_ne_zero (circleUnitary q)

theorem scale_val (q : Circle) (B : Space (Fin 3)) :
    (scale q B).val.val = (q : ℂ) • B.val.val := rfl

theorem scale_det (q : Circle) (B : Space (Fin 3)) :
    (scale q B).val.val.det = (q : ℂ) ^ 3 * B.val.val.det :=
  Matrix.det_smul B.val.val (q : ℂ)

end QuaternionicSymmetricMatrices

namespace ComplexCrossProductUnitary

open QuaternionicBottMatrix QuaternionicSymmetricMatrices

local notation "ℍ" => Quaternion ℝ

theorem midpoint_scaled_target (q : Circle) (z : UnitSphere)
    (hz : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn) :
    firstColumnFormula (Real.pi / 2) (Real.pi / 2) (scale q (symmetricMap z)) =
      targetColumn := by
  obtain ⟨u, _, hu⟩ := midpoint_target_forward (symmetricMap z) (symmetricMap_det z) hz
  apply midpoint_target_of_matrix _ (circleUnitary q * u)
  rw [scale_val, hu, smul_smul]
  rfl

theorem scaled_firstColumn_curve_kernel_midpoint (q : Circle)
    (s t : ℝ → ℝ) (z : ℝ → UnitSphere) (a b x : ℝ) (v : Vector)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hz : ∀ r, HasDerivAt (fun y ↦ (z y).val r) (v r) x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap (z x)) = targetColumn)
    (hF : ∀ r, HasDerivAt (fun y ↦
      firstColumnFormula (s y) (t y) (scale q (symmetricMap (z y))) r) (0 : ℍ) x) :
    a = 0 ∧ b = 0 ∧ v = 0 := by
  obtain ⟨u, _, hBx⟩ := midpoint_target_forward (symmetricMap (z x)) (symmetricMap_det (z x)) h
  let D := (q : ℂ) • symmetricVariation (z x).val v
  have hB (r k : Fin 3) :
      HasDerivAt (fun y ↦ (scale q (symmetricMap (z y))).val.val r k) (D r k) x :=
    (hasDerivAt_symmetricMap_entry z v x hz r k).const_mul (q : ℂ)
  have hscaled : (scale q (symmetricMap (z x))).val.val =
      (circleUnitary q * u).val • targetMatrix targetAlpha targetBeta := by
    rw [scale_val, hBx, smul_smul]
    rfl
  have hdet (y : ℝ) : (scale q (symmetricMap (z y))).val.val.det = (q : ℂ) ^ 3 := by
    rw [scale_det, symmetricMap_det, mul_one]
  have hV (r : Fin 2) : midpointColumnVariation (angularVelocity a b)
      (circleUnitary q * u) D r = 0 :=
    (hasDerivAt_firstColumn_midpoint s t (fun y ↦ scale q (symmetricMap (z y)))
      a b x D hs ht hB hsx htx (circleUnitary q * u) hscaled r).unique (hF r)
  obtain ⟨hw, hD⟩ := midpointColumnVariation_kernel_of_constant_det
    (fun y ↦ scale q (symmetricMap (z y))) D x hB ((q : ℂ) ^ 3) hdet
      (circleUnitary q * u) hscaled (angularVelocity a b) hV
  have hv : symmetricVariation (z x).val v = 0 := by
    apply Matrix.ext
    intro r k
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r k) hD
    exact (mul_eq_zero.mp he).resolve_left (circle_coe_ne_zero q)
  have ha : -a = 0 := congrArg Complex.re hw
  have hb : -b = 0 := congrArg Complex.im hw
  exact ⟨neg_eq_zero.mp ha, neg_eq_zero.mp hb,
    sphere_curve_midpoint_preimage_kernel z v x hz h hv⟩

end ComplexCrossProductUnitary
end Wikipedia.HomotopyGroupsOfSpheres
