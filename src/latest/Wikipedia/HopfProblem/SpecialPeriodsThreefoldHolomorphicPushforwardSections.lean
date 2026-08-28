import Wikipedia.HopfProblem.SpecialPeriodsThreefoldDirectImage

/-!
# The natural O-linear refinement of holomorphic descent

The previously proved pullback equivalence on every base open set is
linear for the actual action of base functions by their pullbacks.
The algebra structure below comes directly from the literal pullback
ring homomorphism.  Its inverse is the already constructed holomorphic
descended section, and commutes with actual restrictions.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- Base holomorphic functions act on sections over the full preimage
through the literal holomorphic pullback ring homomorphism. -/
instance preimageSectionAlgebra (U : Opens RiemannSphere) :
    Algebra (BaseSection U) (PreimageSection U) :=
  (pullbackSection U).toRingHom.toAlgebra

@[simp] theorem preimageSectionAlgebra_algebraMap (U : Opens RiemannSphere) :
    algebraMap (BaseSection U) (PreimageSection U) = (pullbackSection U).toRingHom := rfl

/-- This is the original pullback action, not a transported action. -/
theorem base_smul_eq_pullback_mul (U : Opens RiemannSphere)
    (a : BaseSection U) (s : PreimageSection U) :
    a • s = pullbackSection U a * s := rfl

@[simp] theorem base_smul_apply (U : Opens RiemannSphere)
    (a : BaseSection U) (s : PreimageSection U) (x : basePreimage U) :
    (a • s) x = a (baseProjection U x) * s x := rfl

instance preimageSectionScalarTower (U : Opens RiemannSphere) :
    IsScalarTower ℂ (BaseSection U) (PreimageSection U) where
  smul_assoc c a s := by
    apply ContMDiffMap.ext
    intro x
    exact mul_assoc c (a (baseProjection U x)) (s x)

instance preimageSectionSMulCommClass (U : Opens RiemannSphere) :
    SMulCommClass ℂ (BaseSection U) (PreimageSection U) where
  smul_comm c a s := by
    apply ContMDiffMap.ext
    intro x
    exact mul_left_comm c (a (baseProjection U x)) (s x)

/-- Uniqueness of the existing holomorphic descent gives the other
inverse identity for actual pullback. -/
@[simp] theorem descendedSection_pullbackSection (U : Opens RiemannSphere)
    (a : BaseSection U) : descendedSection U (pullbackSection U a) = a := by
  apply pullbackSection_injective U
  exact pullbackSection_descendedSection U (pullbackSection U a)

/-- The genuine O(U)-linear equivalence, with the already constructed
descended section as its literal inverse. -/
def pullbackSectionLinearEquiv (U : Opens RiemannSphere) :
    BaseSection U ≃ₗ[BaseSection U] PreimageSection U where
  toFun := pullbackSection U
  invFun := descendedSection U
  left_inv := descendedSection_pullbackSection U
  right_inv := pullbackSection_descendedSection U
  map_add' := (pullbackSection U).map_add
  map_smul' a s := (pullbackSection U).map_mul a s

@[simp] theorem pullbackSectionLinearEquiv_apply (U : Opens RiemannSphere)
    (a : BaseSection U) : pullbackSectionLinearEquiv U a = pullbackSection U a := rfl

@[simp] theorem pullbackSectionLinearEquiv_symm_apply (U : Opens RiemannSphere)
    (s : PreimageSection U) : (pullbackSectionLinearEquiv U).symm s = descendedSection U s := rfl

/-- The inverse is linear for multiplication by actual base functions. -/
theorem descendedSection_base_smul (U : Opens RiemannSphere)
    (a : BaseSection U) (s : PreimageSection U) :
    descendedSection U (a • s) = a * descendedSection U s :=
  (pullbackSectionLinearEquiv U).symm.map_smul a s

/-- Complex-linearity uses the original complex algebra equivalence. -/
theorem descendedSection_complex_smul (U : Opens RiemannSphere)
    (c : ℂ) (s : PreimageSection U) :
    descendedSection U (c • s) = c • descendedSection U s := by
  have h := (pullbackSectionEquiv U).symm.toLinearEquiv.map_smul c s
  change (pullbackSectionEquiv U).symm (c • s) =
    c • (pullbackSectionEquiv U).symm s at h
  simpa only [pullbackSectionEquiv_symm_apply] using h

theorem pullbackSectionLinearEquiv_complex_smul (U : Opens RiemannSphere)
    (c : ℂ) (a : BaseSection U) :
    pullbackSectionLinearEquiv U (c • a) = c • pullbackSectionLinearEquiv U a :=
  (pullbackSection U).toLinearMap.map_smul c a

/-- Restricting a genuinely descended section agrees with descending
the actual restricted section. -/
theorem descendedSection_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : PreimageSection V) :
    descendedSection U
        (HolomorphicFunctionSheaf.restrictionAlgHom IF Space (basePreimage_mono h) s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h (descendedSection V s) := by
  apply pullbackSection_injective U
  rw [pullbackSection_descendedSection, pullbackSection_restrict,
    pullbackSection_descendedSection]

/-- The natural base action commutes with the literal restriction maps. -/
theorem restrict_preimage_base_smul {U V : Opens RiemannSphere} (h : U ≤ V)
    (a : BaseSection V) (s : PreimageSection V) :
    HolomorphicFunctionSheaf.restrictionAlgHom IF Space (basePreimage_mono h) (a • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h a •
        HolomorphicFunctionSheaf.restrictionAlgHom IF Space (basePreimage_mono h) s := by
  apply ContMDiffMap.ext
  intro x
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicPushforward
