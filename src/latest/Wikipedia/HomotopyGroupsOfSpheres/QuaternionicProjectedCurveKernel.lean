import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointVariationKernel
import Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductPreimageKernel
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicGlobalPreimages

/-!
# The full projected map kills no nonzero parameter-curve velocity

This combines the actual first-column derivative, symmetric-unitary
tangency, and the polynomial five-sphere kernel theorem. Both angular
velocities and the sphere velocity vanish when the projected derivative
vanishes at any preimage of the selected target in the parameter domain.
Local inverse charts and local degrees remain separate constructions.
-/

noncomputable section

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

local notation "ℍ" => Quaternion ℝ

theorem firstColumn_curve_kernel_midpoint (s t : ℝ → ℝ) (z : ℝ → UnitSphere)
    (a b x : ℝ) (v : Vector)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hz : ∀ r, HasDerivAt (fun y ↦ (z y).val r) (v r) x)
    (hsx : s x = Real.pi / 2) (htx : t x = Real.pi / 2)
    (h : firstColumnFormula (s x) (t x) (symmetricMap (z x)) = targetColumn)
    (hF : ∀ r, HasDerivAt (fun y ↦ firstColumnFormula (s y) (t y) (symmetricMap (z y)) r)
      (0 : ℍ) x) : a = 0 ∧ b = 0 ∧ v = 0 := by
  have hmid : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap (z x)) =
      targetColumn := by simpa only [hsx, htx] using h
  obtain ⟨u, hu, hBx⟩ := midpoint_target_forward (symmetricMap (z x)) (symmetricMap_det (z x)) hmid
  let D := symmetricVariation (z x).val v
  have hB (r q : Fin 3) : HasDerivAt (fun y ↦ (symmetricMap (z y)).val.val r q) (D r q) x :=
    hasDerivAt_symmetricMap_entry z v x hz r q
  have hV (r : Fin 2) : midpointColumnVariation (angularVelocity a b) u D r = 0 := by
    exact (hasDerivAt_firstColumn_midpoint s t (fun y ↦ symmetricMap (z y)) a b x D
      hs ht hB hsx htx u hBx r).unique (hF r)
  obtain ⟨hw, hD⟩ := midpointColumnVariation_kernel (fun y ↦ symmetricMap (z y)) D x hB
    (fun y ↦ symmetricMap_det (z y)) u hBx (angularVelocity a b) hV
  have ha : -a = 0 := congrArg Complex.re hw
  have hb : -b = 0 := congrArg Complex.im hw
  exact ⟨neg_eq_zero.mp ha, neg_eq_zero.mp hb,
    sphere_curve_midpoint_preimage_kernel z v x hz hmid hD⟩

theorem firstColumn_curve_kernel (s t : ℝ → ℝ) (z : ℝ → UnitSphere)
    (a b x : ℝ) (v : Vector)
    (hs : HasDerivAt s a x) (ht : HasDerivAt t b x)
    (hz : ∀ r, HasDerivAt (fun y ↦ (z y).val r) (v r) x)
    (hsx : s x ∈ Set.Icc 0 Real.pi) (htx : t x ∈ Set.Icc 0 Real.pi)
    (h : firstColumnFormula (s x) (t x) (symmetricMap (z x)) = targetColumn)
    (hF : ∀ r, HasDerivAt (fun y ↦ firstColumnFormula (s y) (t y) (symmetricMap (z y)) r)
      (0 : ℍ) x) : a = 0 ∧ b = 0 ∧ v = 0 := by
  obtain ⟨hs', ht'⟩ := target_parameter_midpoint (s x) (t x) (symmetricMap (z x)) hsx htx h
  exact firstColumn_curve_kernel_midpoint s t z a b x v hs ht hz hs' ht' h hF

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
