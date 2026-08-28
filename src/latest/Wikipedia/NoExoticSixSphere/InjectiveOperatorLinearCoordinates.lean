import Wikipedia.NoExoticSixSphere.InjectiveOperatorSphereParity

/-!
# General linear coordinate changes preserve the actual operator parity

Pre- and postcomposition by fixed continuous linear equivalences give a
genuine homeomorphism of the original injective-operator space. The exact
extension criterion therefore preserves the parity of its normalized frames.
The coordinate changes need not be isometries.
-/

noncomputable section

namespace NoExoticSixSphere.Stiefel.Monomorphism

open GLOrthonormalization

variable {N n : ℕ}

def linearChange (U : Vector N ≃L[ℝ] Vector N) (V : Vector n ≃L[ℝ] Vector n)
    (A : Space N n) : Space N n :=
  ⟨U.toContinuousLinearMap.comp (A.val.comp V.toContinuousLinearMap),
    U.injective.comp (A.property.comp V.injective)⟩

theorem linearChange_apply (U : Vector N ≃L[ℝ] Vector N) (V : Vector n ≃L[ℝ] Vector n)
    (A : Space N n) (w : Vector n) : (linearChange U V A).val w = U (A.val (V w)) := rfl

theorem continuous_linearChange (U : Vector N ≃L[ℝ] Vector N)
    (V : Vector n ≃L[ℝ] Vector n) : Continuous (linearChange U V) :=
  (continuous_const.clm_comp (continuous_subtype_val.clm_comp continuous_const)).subtype_mk _

def linearHomeomorph (U : Vector N ≃L[ℝ] Vector N) (V : Vector n ≃L[ℝ] Vector n) :
    Space N n ≃ₜ Space N n where
  toFun := linearChange U V
  invFun := linearChange U.symm V.symm
  left_inv A := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [linearChange_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  right_inv A := by
    apply Subtype.ext
    apply ContinuousLinearMap.ext
    intro w
    simp only [linearChange_apply, ContinuousLinearEquiv.apply_symm_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  continuous_toFun := continuous_linearChange U V
  continuous_invFun := continuous_linearChange U.symm V.symm

theorem sphereParity_linearCoordinates (r : ℕ)
    (U : Vector (3 + (r + 2)) ≃L[ℝ] Vector (3 + (r + 2)))
    (V : Vector (r + 2) ≃L[ℝ] Vector (r + 2))
    (f : C(Sphere 3, Space (3 + (r + 2)) (r + 2))) :
    sphereParity r ((linearHomeomorph U V : C(_, _)).comp f) = sphereParity r f :=
  sphereParity_homeomorph r (linearHomeomorph U V) f

end NoExoticSixSphere.Stiefel.Monomorphism
