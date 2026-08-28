import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardBaseIdealGluing

/-!
# The O-linear ideal identification on every sphere open

The globally glued maps preserve the original pointwise module
operations because their restrictions do so in each actual chart.
They give an O(U)-linear equivalence for every open U, natural in both
directions and with the exact original native-chart coefficient formula.
-/

noncomputable section

open Set TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal

open HolomorphicFunctionSheaf.SphereH1

local notation "𝒪" => HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere

theorem bundleRestrict_add {U V : Opens RiemannSphere} (h : U ≤ V)
    (s t : BundleSection V) :
    bundleRestrict h (s + t) = bundleRestrict h s + bundleRestrict h t :=
  NativeBundleSections.Section.restrict_add CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) h s t

theorem bundleRestrict_function_smul {U V : Opens RiemannSphere} (h : U ≤ V)
    (r : 𝒪 V) (s : BundleSection V) :
    bundleRestrict h (r • s) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h r • bundleRestrict h s :=
  NativeBundleSections.Section.restrict_function_smul
    CanonicalGlobal.BaseTwist.data.core 𝓘(ℂ) h r s

theorem negativeOneRestriction_function_smul {U V : Opens RiemannSphere} (h : U ≤ V)
    (r : 𝒪 V) (f : NegativeOneSection V) :
    negativeOneRestriction h (r • f) =
      HolomorphicFunctionSheaf.restrictionAlgHom 𝓘(ℂ) RiemannSphere h r •
        negativeOneRestriction h f := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rfl

theorem negativeOneRestriction_refl (U : Opens RiemannSphere) (f : NegativeOneSection U) :
    negativeOneRestriction (le_refl U) f = f := by
  apply Subtype.ext
  apply ContMDiffMap.ext
  intro p
  rfl

theorem toIdeal_add (U : Opens RiemannSphere) (s t : BundleSection U) :
    toIdeal U (s + t) = toIdeal U s + toIdeal U t := by
  apply idealSection_eq_of_chartCover U
  intro b
  rw [toIdeal_restrict_chartCover, (negativeOneRestriction (chartCover_le U b)).map_add,
    toIdeal_restrict_chartCover, toIdeal_restrict_chartCover]
  change localLinearEquiv b (chartCover U b) (chartCover_le_frame U b)
      (bundleRestrict (chartCover_le U b) (s + t)) = _
  rw [bundleRestrict_add, map_add]
  rfl

/-- O(U)-linearity follows from the actual chart restrictions of both
the fibrewise scalar action and the literal ideal scalar action. -/
theorem toIdeal_function_smul (U : Opens RiemannSphere) (r : 𝒪 U) (s : BundleSection U) :
    toIdeal U (r • s) = r • toIdeal U s := by
  apply idealSection_eq_of_chartCover U
  intro b
  rw [toIdeal_restrict_chartCover, negativeOneRestriction_function_smul,
    toIdeal_restrict_chartCover]
  change localLinearEquiv b (chartCover U b) (chartCover_le_frame U b)
      (bundleRestrict (chartCover_le U b) (r • s)) = _
  rw [bundleRestrict_function_smul, map_smul]
  rfl

/-- The genuine native base-bundle section module equals the actual
vanishing-ideal section module on every original sphere open. -/
def sectionLinearEquiv (U : Opens RiemannSphere) :
    BundleSection U ≃ₗ[𝒪 U] NegativeOneSection U where
  toFun := toIdeal U
  invFun := fromIdeal U
  left_inv := fromIdeal_toIdeal U
  right_inv := toIdeal_fromIdeal U
  map_add' := toIdeal_add U
  map_smul' := toIdeal_function_smul U

@[simp] theorem sectionLinearEquiv_apply (U : Opens RiemannSphere) (s : BundleSection U) :
    sectionLinearEquiv U s = toIdeal U s := rfl

@[simp] theorem sectionLinearEquiv_symm_apply (U : Opens RiemannSphere)
    (f : NegativeOneSection U) : (sectionLinearEquiv U).symm f = fromIdeal U f := rfl

/-- On each chart subopen this is precisely the pre-existing actual
native coefficient identification, not merely an abstract module equivalence. -/
theorem sectionLinearEquiv_agrees_local (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (s : BundleSection U) :
    sectionLinearEquiv U s = localLinearEquiv b U hU s := by
  have h := toIdeal_restrict_chart b (le_refl U) hU s
  rw [negativeOneRestriction_refl, bundleRestrict_refl] at h
  exact h

theorem sectionLinearEquiv_symm_agrees_local (b : Bool) (U : Opens RiemannSphere)
    (hU : U ≤ NegativeOneFrames.frameChart b) (f : NegativeOneSection U) :
    (sectionLinearEquiv U).symm f = (localLinearEquiv b U hU).symm f := by
  apply (sectionLinearEquiv U).injective
  rw [LinearEquiv.apply_symm_apply, sectionLinearEquiv_agrees_local b U hU,
    LinearEquiv.apply_symm_apply]

/-- At every point and in every valid original chart, the global map
multiplies the actual bundle coefficient by the actual ideal frame value. -/
theorem sectionLinearEquiv_value (U : Opens RiemannSphere) (s : BundleSection U)
    (b : Bool) (p : U) (hp : (p : RiemannSphere) ∈ NegativeOneFrames.frameChart b) :
    (sectionLinearEquiv U s).val p =
      (CanonicalGlobal.BaseTwist.bundle.localTriv b ⟨(p : RiemannSphere), s p⟩).2 *
        CanonicalGlobal.BaseTwist.idealFrameValue b p := by
  let q : chartCover U b := ⟨p, ⟨p.property, hp⟩⟩
  have he := congrArg (fun f : NegativeOneSection (chartCover U b) => f.val q)
    (toIdeal_restrict_chartCover U s b)
  exact he.trans (localLinearEquiv_value b (chartCover U b) (chartCover_le_frame U b)
    (bundleRestrict (chartCover_le U b) s) q)

/-- Naturality for all restrictions, including domains crossing infinity. -/
theorem sectionLinearEquiv_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (s : BundleSection V) :
    negativeOneRestriction h (sectionLinearEquiv V s) =
      sectionLinearEquiv U (bundleRestrict h s) := toIdeal_restrict h s

theorem sectionLinearEquiv_symm_restrict {U V : Opens RiemannSphere} (h : U ≤ V)
    (f : NegativeOneSection V) :
    (sectionLinearEquiv U).symm (negativeOneRestriction h f) =
      bundleRestrict h ((sectionLinearEquiv V).symm f) := fromIdeal_restrict h f

/-- Restricting scalars retains the same actual maps on sections. -/
def sectionComplexLinearEquiv (U : Opens RiemannSphere) :
    BundleSection U ≃ₗ[ℂ] NegativeOneSection U :=
  (sectionLinearEquiv U).restrictScalars ℂ

@[simp] theorem sectionComplexLinearEquiv_apply (U : Opens RiemannSphere)
    (s : BundleSection U) : sectionComplexLinearEquiv U s = sectionLinearEquiv U s := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.BaseIdeal
