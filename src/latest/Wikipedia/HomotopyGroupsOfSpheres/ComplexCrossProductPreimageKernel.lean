import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicPreimageRadialDeterminant

/-! # No nonzero sphere-curve velocity is killed at a target preimage

The diagonal kernel calculation is transferred through the real rotation
and the explicit four-point parametrization of each phase fiber.
This concerns the polynomial symmetric map; the two Bott parameter
directions and the local degree of the full map remain separate.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

theorem hasDerivAt_rotationSphere_entry (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x) (r : Fin 3) :
    HasDerivAt (fun t ↦ (rotationSphere (z t)).val r) ((targetRotation *ᵥ v) r) x := by
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) ↦ (hz k).const_mul (targetRotation r k))

theorem hasDerivAt_matrix_congruence_entry
    (A : ℝ → Matrix (Fin 3) (Fin 3) ℂ) (D P Q : Matrix (Fin 3) (Fin 3) ℂ) (x : ℝ)
    (hA : ∀ r s, HasDerivAt (fun t ↦ A t r s) (D r s) x) (r s : Fin 3) :
    HasDerivAt (fun t ↦ (P * A t * Q) r s) ((P * D * Q) r s) x := by
  have he (k : Fin 3) : HasDerivAt (fun t ↦ (P * A t) r k) ((P * D) r k) x :=
    HasDerivAt.fun_sum (u := Finset.univ)
      (fun j (_ : j ∈ Finset.univ) ↦ (hA j k).const_mul (P r j))
  exact HasDerivAt.fun_sum (u := Finset.univ)
    (fun k (_ : k ∈ Finset.univ) ↦ (he k).mul_const (Q k s))

theorem sphere_curve_rotation_preserves_kernel (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0) :
    symmetricVariation (rotationSphere (z x)).val (targetRotation *ᵥ v) = 0 := by
  have hB (r s : Fin 3) : HasDerivAt (fun t ↦ (symmetricMap (z t)).val.val r s) 0 x := by
    simpa only [hv, Matrix.zero_apply] using hasDerivAt_symmetricMap_entry z v x hz r s
  apply Matrix.ext
  intro r s
  have he := hasDerivAt_matrix_congruence_entry (fun t ↦ (symmetricMap (z t)).val.val)
    0 targetRotation targetRotation x hB r s
  have hf : (fun t ↦ (targetRotation * (symmetricMap (z t)).val.val * targetRotation) r s) =
      fun t ↦ (symmetricMap (rotationSphere (z t))).val.val r s := by
    funext t
    exact (congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A r s)
      (symmetricMap_rotationSphere (z t))).symm
  rw [hf] at he
  have hr := hasDerivAt_symmetricMap_entry (fun t ↦ rotationSphere (z t))
    (targetRotation *ᵥ v) x (hasDerivAt_rotationSphere_entry z v x hz) r s
  simpa using hr.unique he

theorem sphere_curve_phaseInput_kernel (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (hv : symmetricVariation (z x).val v = 0)
    (u : unitary ℂ) (hu : u.val ^ 3 = -1) (b : Bool × Bool)
    (hx : z x = phaseInput u b) : v = 0 := by
  have he := sphere_curve_rotated_phaseInput_kernel (fun t ↦ rotationSphere (z t))
    (targetRotation *ᵥ v) x (hasDerivAt_rotationSphere_entry z v x hz)
    (sphere_curve_rotation_preserves_kernel z v x hz hv) u hu b (congrArg rotationSphere hx)
  have hr := congrArg (fun w : Vector ↦ targetRotation *ᵥ w) he
  simpa [Matrix.mulVec_mulVec, targetRotation_mul_self] using hr

theorem midpoint_fiber_eq_phaseInput (z : UnitSphere) (u : unitary ℂ)
    (hu : u.val ^ 3 = -1)
    (hB : (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta) :
    ∃ b : Bool × Bool, z = phaseInput u b := by
  let : Finite (midpointFiber u) := (midpointFiber_finite_card_le_four u hu).1
  have hc : Nat.card (midpointFiber u) ≤ Nat.card (Bool × Bool) := by
    rw [midpointFiber_card_eq_four u hu]
    norm_num
  have hb := (fourInputs u hu).injective.bijective_of_nat_card_le hc
  obtain ⟨b, he⟩ := hb.surjective (⟨z, hB⟩ : midpointFiber u)
  exact ⟨b, (congrArg Subtype.val he).symm⟩

theorem sphere_curve_midpoint_preimage_kernel (z : ℝ → UnitSphere) (v : Vector) (x : ℝ)
    (hz : ∀ r, HasDerivAt (fun t ↦ (z t).val r) (v r) x)
    (h : firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap (z x)) = targetColumn)
    (hv : symmetricVariation (z x).val v = 0) : v = 0 := by
  obtain ⟨u, hu, hB⟩ := midpoint_target_forward (symmetricMap (z x)) (symmetricMap_det (z x)) h
  obtain ⟨b, hb⟩ := midpoint_fiber_eq_phaseInput (z x) u hu hB
  exact sphere_curve_phaseInput_kernel z v x hz hv u hu b hb

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
