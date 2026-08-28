import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

/-!
# Reversing a meridian in the integral difference complex

Replacing one monodromy automorphism by its inverse changes the domain of
the difference map by an explicit integral automorphism. Its range is
unchanged, and the kernels are identified by that same domain map. This
retains the signs needed when the two actual slit transitions are read
in the normalized geometric meridian orientations.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra

variable {H : Type*} [AddCommGroup H] [Module ℤ H]

/-- Reverse the first oriented meridian coordinate. -/
def inverseFirstCoordinate (P : H ≃ₗ[ℤ] H) : (H × H) ≃ₗ[ℤ] (H × H) :=
  ({ toFun x := (-P.symm x.1, x.2)
     invFun x := (-P x.1, x.2)
     left_inv x := by simp
     right_inv x := by simp
     map_add' x y := by simp [map_add, add_comm]
   } : (H × H) ≃+ (H × H)).toIntLinearEquiv

/-- Reverse the second oriented meridian coordinate. -/
def inverseSecondCoordinate (Q : H ≃ₗ[ℤ] H) : (H × H) ≃ₗ[ℤ] (H × H) :=
  ({ toFun x := (x.1, -Q.symm x.2)
     invFun x := (x.1, -Q x.2)
     left_inv x := by simp
     right_inv x := by simp
     map_add' x y := by simp [map_add, add_comm]
   } : (H × H) ≃+ (H × H)).toIntLinearEquiv

@[simp] theorem inverseFirstCoordinate_apply (P : H ≃ₗ[ℤ] H) (x : H × H) :
    inverseFirstCoordinate P x = (-P.symm x.1, x.2) := rfl

@[simp] theorem inverseFirstCoordinate_symm_apply (P : H ≃ₗ[ℤ] H) (x : H × H) :
    (inverseFirstCoordinate P).symm x = (-P x.1, x.2) := rfl

@[simp] theorem inverseSecondCoordinate_apply (Q : H ≃ₗ[ℤ] H) (x : H × H) :
    inverseSecondCoordinate Q x = (x.1, -Q.symm x.2) := rfl

@[simp] theorem inverseSecondCoordinate_symm_apply (Q : H ≃ₗ[ℤ] H) (x : H × H) :
    (inverseSecondCoordinate Q).symm x = (x.1, -Q x.2) := rfl

/-- The first inverse-monodromy difference is the original difference in reversed coordinates. -/
theorem delta_inverse_first (P : H ≃ₗ[ℤ] H) (Q : H →ₗ[ℤ] H) (x : H × H) :
    delta P.toLinearMap Q (inverseFirstCoordinate P x) = delta P.symm.toLinearMap Q x := by
  simp only [delta_apply, inverseFirstCoordinate_apply, LinearEquiv.coe_coe,
    map_neg, LinearEquiv.apply_symm_apply]
  abel

/-- The second inverse-monodromy difference is the original difference in reversed coordinates. -/
theorem delta_inverse_second (P : H →ₗ[ℤ] H) (Q : H ≃ₗ[ℤ] H) (x : H × H) :
    delta P Q.toLinearMap (inverseSecondCoordinate Q x) = delta P Q.symm.toLinearMap x := by
  simp only [delta_apply, inverseSecondCoordinate_apply, LinearEquiv.coe_coe,
    map_neg, LinearEquiv.apply_symm_apply]
  abel

/-- A genuine domain coordinate change leaves the image of a linear map unchanged. -/
theorem range_eq_of_coordinates (f g : (H × H) →ₗ[ℤ] H)
    (e : (H × H) ≃ₗ[ℤ] (H × H)) (he : ∀ x, f (e x) = g x) :
    LinearMap.range g = LinearMap.range f := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨e x, he x⟩
  · rintro ⟨x, rfl⟩
    refine ⟨e.symm x, ?_⟩
    rw [← he, LinearEquiv.apply_symm_apply]

/-- The actual kernel equivalence induced by the specified domain change. -/
def kernelEquivOfCoordinates (f g : (H × H) →ₗ[ℤ] H)
    (e : (H × H) ≃ₗ[ℤ] (H × H)) (he : ∀ x, f (e x) = g x) :
    LinearMap.ker g ≃ₗ[ℤ] LinearMap.ker f :=
  ({ toFun x := ⟨e x.val, by rw [LinearMap.mem_ker, he]; exact x.property⟩
     invFun y := ⟨e.symm y.val, by
       rw [LinearMap.mem_ker, ← he, LinearEquiv.apply_symm_apply]
       exact y.property⟩
     left_inv x := Subtype.ext (e.symm_apply_apply x.val)
     right_inv y := Subtype.ext (e.apply_symm_apply y.val)
     map_add' x y := Subtype.ext (e.map_add x.val y.val)
   } : LinearMap.ker g ≃+ LinearMap.ker f).toIntLinearEquiv

@[simp] theorem kernelEquivOfCoordinates_apply_val (f g : (H × H) →ₗ[ℤ] H)
    (e : (H × H) ≃ₗ[ℤ] (H × H)) (he : ∀ x, f (e x) = g x)
    (x : LinearMap.ker g) :
    (kernelEquivOfCoordinates f g e he x : H × H) = e x.val := rfl

theorem delta_inverse_first_range (P : H ≃ₗ[ℤ] H) (Q : H →ₗ[ℤ] H) :
    LinearMap.range (delta P.symm.toLinearMap Q) =
      LinearMap.range (delta P.toLinearMap Q) :=
  range_eq_of_coordinates _ _ (inverseFirstCoordinate P) (delta_inverse_first P Q)

theorem delta_inverse_second_range (P : H →ₗ[ℤ] H) (Q : H ≃ₗ[ℤ] H) :
    LinearMap.range (delta P Q.symm.toLinearMap) =
      LinearMap.range (delta P Q.toLinearMap) :=
  range_eq_of_coordinates _ _ (inverseSecondCoordinate Q) (delta_inverse_second P Q)

/-- Reversing the first meridian identifies the actual integral kernels. -/
def deltaInverseFirstKernelEquiv (P : H ≃ₗ[ℤ] H) (Q : H →ₗ[ℤ] H) :
    LinearMap.ker (delta P.symm.toLinearMap Q) ≃ₗ[ℤ]
      LinearMap.ker (delta P.toLinearMap Q) :=
  kernelEquivOfCoordinates _ _ (inverseFirstCoordinate P) (delta_inverse_first P Q)

/-- Reversing the second meridian identifies the actual integral kernels. -/
def deltaInverseSecondKernelEquiv (P : H →ₗ[ℤ] H) (Q : H ≃ₗ[ℤ] H) :
    LinearMap.ker (delta P Q.symm.toLinearMap) ≃ₗ[ℤ]
      LinearMap.ker (delta P Q.toLinearMap) :=
  kernelEquivOfCoordinates _ _ (inverseSecondCoordinate Q) (delta_inverse_second P Q)

/-- Equal submodules give a quotient equivalence that is the identity
on representatives. -/
def integralQuotientCongr (S T : Submodule ℤ H) (h : S = T) :
    (H ⧸ S) ≃ₗ[ℤ] (H ⧸ T) :=
  ({ toEquiv := @Quotient.congr H H (Submodule.quotientRel S) (Submodule.quotientRel T)
       (Equiv.refl H) (fun _ _ => by rw [h]; rfl)
     map_add' := by
       rintro ⟨x⟩ ⟨y⟩
       rfl
   } : (H ⧸ S) ≃+ (H ⧸ T)).toIntLinearEquiv

@[simp] theorem integralQuotientCongr_mk (S T : Submodule ℤ H) (h : S = T) (x : H) :
    integralQuotientCongr S T h (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

/-- On the actual quotient cokernel, the first reversal is induced by the identity. -/
def deltaInverseFirstCokernelEquiv (P : H ≃ₗ[ℤ] H) (Q : H →ₗ[ℤ] H) :
    (H ⧸ LinearMap.range (delta P.symm.toLinearMap Q)) ≃ₗ[ℤ]
      H ⧸ LinearMap.range (delta P.toLinearMap Q) :=
  integralQuotientCongr _ _ (delta_inverse_first_range P Q)

/-- The same identity-on-representatives quotient comparison for the second reversal. -/
def deltaInverseSecondCokernelEquiv (P : H →ₗ[ℤ] H) (Q : H ≃ₗ[ℤ] H) :
    (H ⧸ LinearMap.range (delta P Q.symm.toLinearMap)) ≃ₗ[ℤ]
      H ⧸ LinearMap.range (delta P Q.toLinearMap) :=
  integralQuotientCongr _ _ (delta_inverse_second_range P Q)

@[simp] theorem deltaInverseFirstCokernelEquiv_mk (P : H ≃ₗ[ℤ] H)
    (Q : H →ₗ[ℤ] H) (x : H) :
    deltaInverseFirstCokernelEquiv P Q (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  integralQuotientCongr_mk _ _ _ x

@[simp] theorem deltaInverseSecondCokernelEquiv_mk (P : H →ₗ[ℤ] H)
    (Q : H ≃ₗ[ℤ] H) (x : H) :
    deltaInverseSecondCokernelEquiv P Q (Submodule.Quotient.mk x) = Submodule.Quotient.mk x :=
  integralQuotientCongr_mk _ _ _ x

end Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyAlgebra
