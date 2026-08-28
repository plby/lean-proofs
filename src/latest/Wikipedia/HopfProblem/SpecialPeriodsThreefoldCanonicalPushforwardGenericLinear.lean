import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardGeneric
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardSectionsLinear

/-!
# Linearity of the actual generic base coefficient

Native scalar division and the proved holomorphic direct-image equivalence
preserve addition, complex scalar multiplication, and multiplication by
actual holomorphic functions pulled back from the original base open.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic

open TrianglePeriodFamily.Canonical

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ Model

@[simp] theorem upstairsRatio_zero (U : Opens RiemannSphere) :
    upstairsRatio U 0 = 0 := by
  apply ContMDiffMap.ext
  intro x
  change (0 : ℂ) / _ = 0
  exact zero_div _

theorem upstairsRatio_add (U : Opens RiemannSphere) (s t : PreimageSection U) :
    upstairsRatio U (s + t) = upstairsRatio U s + upstairsRatio U t := by
  apply ContMDiffMap.ext
  intro x
  change (id (α := ℂ) (s (preimagePoint U x)) + id (α := ℂ) (t (preimagePoint U x))) / _ =
    id (α := ℂ) (s (preimagePoint U x)) / _ + id (α := ℂ) (t (preimagePoint U x)) / _
  exact add_div _ _ _

theorem upstairsRatio_complex_smul (U : Opens RiemannSphere)
    (c : ℂ) (s : PreimageSection U) : upstairsRatio U (c • s) = c • upstairsRatio U s := by
  apply ContMDiffMap.ext
  intro x
  change (c * id (α := ℂ) (s (preimagePoint U x))) / _ =
    c * (id (α := ℂ) (s (preimagePoint U x)) / _)
  exact mul_div_assoc _ _ _

@[simp] theorem baseCoefficient_zero (U : Opens RiemannSphere) :
    baseCoefficient U 0 = 0 := by
  rw [baseCoefficient, upstairsRatio_zero, map_zero]

theorem baseCoefficient_add (U : Opens RiemannSphere) (s t : PreimageSection U) :
    baseCoefficient U (s + t) = baseCoefficient U s + baseCoefficient U t := by
  rw [baseCoefficient, upstairsRatio_add, map_add]
  rfl

theorem baseCoefficient_complex_smul (U : Opens RiemannSphere)
    (c : ℂ) (s : PreimageSection U) : baseCoefficient U (c • s) = c • baseCoefficient U s := by
  rw [baseCoefficient, upstairsRatio_complex_smul, map_smul]
  rfl

/-- The actual generic coefficient is a complex-linear map on native section spaces. -/
def baseCoefficientLinearMap (U : Opens RiemannSphere) :
    PreimageSection U →ₗ[ℂ] Threefold.BaseSection (genericPart U) where
  toFun := baseCoefficient U
  map_add' := baseCoefficient_add U
  map_smul' := baseCoefficient_complex_smul U

@[simp] theorem baseCoefficientLinearMap_apply (U : Opens RiemannSphere)
    (s : PreimageSection U) : baseCoefficientLinearMap U s = baseCoefficient U s := rfl

/-- A base holomorphic multiplier pulls through actual native scalar division. -/
theorem upstairsRatio_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    upstairsRatio U ((Threefold.pullbackSection U f) • s) =
      Threefold.pullbackSection (genericPart U)
        (HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere (genericPart_le U) f) *
          upstairsRatio U s := by
  apply ContMDiffMap.ext
  intro x
  change (f (Threefold.baseProjection U (preimagePoint U x)) *
    id (α := ℂ) (s (preimagePoint U x))) / _ =
      f (Threefold.baseProjection U (preimagePoint U x)) *
        (id (α := ℂ) (s (preimagePoint U x)) / _)
  exact mul_div_assoc _ _ _

/-- Compatibility with the actual structure-sheaf action on every original base open. -/
theorem baseCoefficient_base_smul (U : Opens RiemannSphere)
    (f : Threefold.BaseSection U) (s : PreimageSection U) :
    baseCoefficient U ((Threefold.pullbackSection U f) • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere (genericPart_le U) f *
        baseCoefficient U s := by
  rw [baseCoefficient, upstairsRatio_base_smul, map_mul,
    ← Threefold.pullbackSectionEquiv_apply, AlgEquiv.symm_apply_apply]
  rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Generic
