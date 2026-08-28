import Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialFormsCovarianceBase

/-!
# Actual family self-maps and genuine local-form invariance

The family map is the original triangle action on the period torus,
restricted to the given invariant open base. Its compatibility with the
original complex-vector quotient follows from the proved period covariance.
The source's form-invariance hypothesis is equality of actual derivative
pullbacks on this native family, not a scalar coefficient condition.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance

open SpecialPeriods
open SpecialPeriods.Threefold.HolomorphicForms.RegularCover (fullGroupData)

attribute [local instance] familyChartedSpace coverChartedSpace family_isManifold cover_isManifold
  triangleGeometricAction

local notation "IF" => modelWithCornersSelf ℂ Model

variable (U : TopologicalSpace.Opens ℍ)

/-- The actual restricted triangle map on the original marked torus family. -/
def familyMap (g : TriangleGroup) (hg : Preserves U g) (x : Family U) : Family U :=
  (baseMap U g hg x.1, triangleTorusHomeomorph g x.2)

@[simp] theorem familyMap_apply (g : TriangleGroup) (hg : Preserves U g) (x : Family U) :
    familyMap U g hg x =
      (baseMap U g hg x.1, triangleTorusHomeomorph g x.2) := rfl

/-- The actual all-word period covariance identifies the original complex lift
with the original integral action on the actual quotient torus. -/
theorem familyMap_quotientMap (g : TriangleGroup) (hg : Preserves U g) (x : Cover U) :
    familyMap U g hg ((periods U).quotientMap x) =
      (periods U).quotientMap (complexLift U g hg x) := by
  apply Prod.ext
  · rfl
  · exact congrArg (fun y : fullGroupData.TotalSpace => y.2)
      (fullGroupData.complexLift_quotientMap g (x.1.val, x.2)).symm

/-- The original restricted family map is holomorphic in the actual quotient atlas. -/
theorem familyMap_holomorphic (g : TriangleGroup) (hg : Preserves U g) :
    ContMDiff IF IF ω (familyMap U g hg) := by
  let := (periods U).coveringAction
  apply CoveringQuotient.contMDiff_of_comp (E := Model)
    (periods U).quotientCoveringMap IF ω
  have h := (quotientMap_holomorphic U).comp (complexLift_holomorphic U g hg)
  convert h using 1
  funext x
  exact familyMap_quotientMap U g hg x

/-- Precisely the source's hypothesis: the genuine local form is fixed by
actual derivative pullback under the genuine restricted family map. -/
def IsInvariant {p : ℕ} (θ : Form U p) (g : TriangleGroup) (hg : Preserves U g) : Prop :=
  HolomorphicDifferentialForms.pullback (familyMap U g hg)
    (familyMap_holomorphic U g hg) θ = θ

/-- The actual commuting quotient square gives the full pullback square,
before imposing any invariance hypothesis. -/
theorem coverPullback_familyMap {p : ℕ} (θ : Form U p)
    (g : TriangleGroup) (hg : Preserves U g) :
    coverPullback U (HolomorphicDifferentialForms.pullback (familyMap U g hg)
        (familyMap_holomorphic U g hg) θ) =
      HolomorphicDifferentialForms.pullback (complexLift U g hg)
        (complexLift_holomorphic U g hg) (coverPullback U θ) := by
  change HolomorphicDifferentialForms.pullback (periods U).quotientMap
      (quotientMap_holomorphic U)
      (HolomorphicDifferentialForms.pullback (familyMap U g hg)
        (familyMap_holomorphic U g hg) θ) =
    HolomorphicDifferentialForms.pullback (complexLift U g hg)
      (complexLift_holomorphic U g hg)
      (HolomorphicDifferentialForms.pullback (periods U).quotientMap
        (quotientMap_holomorphic U) θ)
  rw [← HolomorphicDifferentialForms.pullback_comp,
    ← HolomorphicDifferentialForms.pullback_comp]
  rw [HolomorphicDifferentialForms.pullback_congr
    ((familyMap_holomorphic U g hg).comp (quotientMap_holomorphic U))
    ((quotientMap_holomorphic U).comp (complexLift_holomorphic U g hg))
    (funext (familyMap_quotientMap U g hg))]

/-- Native family invariance implies genuine form invariance on the actual
period-vector cover by functoriality, not by assuming a coefficient law. -/
theorem coverPullback_invariant {p : ℕ} (θ : Form U p)
    (g : TriangleGroup) (hg : Preserves U g) (hθ : IsInvariant U θ g hg) :
    HolomorphicDifferentialForms.pullback (complexLift U g hg)
      (complexLift_holomorphic U g hg) (coverPullback U θ) = coverPullback U θ := by
  rw [← coverPullback_familyMap]
  exact congrArg (fun η : Form U p => coverPullback U η) hθ

/-- Full invariance of the actual native alternating covector, using the
actual derivative of the actual restricted triangle lift. -/
theorem nativeCoefficients_complexLift {p : ℕ} (θ : Form U p)
    (g : TriangleGroup) (hg : Preserves U g) (hθ : IsInvariant U θ g hg)
    (x : Cover U) (v : Fin p → Model) :
    nativeCoefficients U θ (complexLift U g hg x)
        (fun i => mfderiv IF IF (complexLift U g hg) x (v i)) =
      nativeCoefficients U θ x v := by
  have h := congrArg
    (fun η : HolomorphicDifferentialForms.Form Model (Cover U) p => η x v)
    (coverPullback_invariant U θ g hg hθ)
  change coverPullback U θ (complexLift U g hg x)
      (fun i => mfderiv IF IF (complexLift U g hg) x (v i)) =
    coverPullback U θ x v at h
  exact (nativeCoefficients_apply U θ _ _).trans
    (h.trans (nativeCoefficients_apply U θ x v).symm)

theorem nativeCoefficients_complexLift_covector {p : ℕ} (θ : Form U p)
    (g : TriangleGroup) (hg : Preserves U g) (hθ : IsInvariant U θ g hg) (x : Cover U) :
    (nativeCoefficients U θ (complexLift U g hg x)).compContinuousLinearMap
      (mfderiv IF IF (complexLift U g hg) x) = nativeCoefficients U θ x := by
  ext v
  exact nativeCoefficients_complexLift U θ g hg hθ x v

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms.Covariance
