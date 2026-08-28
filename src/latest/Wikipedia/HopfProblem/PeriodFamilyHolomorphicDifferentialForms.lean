import Wikipedia.HopfProblem.HolomorphicDifferentialFormsPeriodLaws
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicFormsSpecial
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsEllipticRestriction

/-!
# Genuine local holomorphic forms on the special period family

For every open upper-half-plane subset, the family below is the original
varying-period quotient, with its original complex atlas. Its differential
forms are genuine holomorphic sections of the alternating cotangent bundle.
Their pullback to the original complex-vector cover is invariant under the
actual period translations because the quotient map identifies those points.
-/

noncomputable section

open Set Topology UpperHalfPlane
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms

open SpecialPeriods

abbrev Model := HolomorphicDifferentialForms.Coordinates.Model

local notation "I₁" => modelWithCornersSelf ℂ ℂ
local notation "IF" => modelWithCornersSelf ℂ Model

variable (U : TopologicalSpace.Opens ℍ)

/-- Restrict the actual constructed periods to the given open subset. -/
def periods : HolomorphicPeriodMap ℂ U where
  point z := specialPeriodMap.point z.val
  holomorphic_tau := specialPeriodMap.holomorphic_tau.comp contMDiff_subtype_val
  holomorphic_mu := specialPeriodMap.holomorphic_mu.comp contMDiff_subtype_val
  holomorphic_beta := specialPeriodMap.holomorphic_beta.comp contMDiff_subtype_val

@[simp] theorem periods_point (z : U) :
    (periods U).point z = specialPeriodMap.point z.val := rfl

/-- The actual varying-period torus family over this open base. -/
abbrev Family := (periods U).TotalSpace

/-- The original complex period-vector cover. -/
abbrev Cover := U × ComplexPlane₂

/-- The native quotient atlas, not the real-coordinate product atlas. -/
@[instance_reducible] def familyChartedSpace : ChartedSpace Model (Family U) :=
  (periods U).totalChartedSpace

/-- The inherited upper-half-plane coordinate and original fibre coordinates. -/
@[instance_reducible] def coverChartedSpace : ChartedSpace Model (Cover U) :=
  inferInstanceAs (ChartedSpace (ModelProd ℂ ComplexPlane₂) (U × ComplexPlane₂))

attribute [local instance] familyChartedSpace coverChartedSpace

theorem family_isManifold : IsManifold IF ω (Family U) :=
  (periods U).totalSpace_isManifold

theorem cover_isManifold : IsManifold IF ω (Cover U) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := I₁) (I' := 𝓘(ℂ, ComplexPlane₂)) U ComplexPlane₂

attribute [local instance] family_isManifold cover_isManifold

/-- Every form here is a genuine form on the original native quotient manifold. -/
abbrev Form (p : ℕ) := HolomorphicDifferentialForms.Form Model (Family U) p

/-- The preferred charts on the original vector cover are independent of the center. -/
theorem cover_chart_eq (x y : Cover U) : chartAt Model x = chartAt Model y := rfl

theorem cover_chart_apply (x y : Cover U) :
    chartAt Model x y = ((y.1.val : ℂ), y.2) := rfl

/-- The actual varying-lattice quotient is holomorphic in its native atlas. -/
theorem quotientMap_holomorphic :
    ContMDiff IF IF ω (periods U).quotientMap := (periods U).quotientMap_holomorphic

/-- Pullback of a local form by the actual derivative of the original quotient map. -/
def coverPullback {p : ℕ} (θ : Form U p) :
    HolomorphicDifferentialForms.Form Model (Cover U) p :=
  HolomorphicDifferentialForms.pullback (periods U).quotientMap
    (quotientMap_holomorphic U) θ

@[simp] theorem coverPullback_apply {p : ℕ} (θ : Form U p)
    (x : Cover U) (v : Fin p → Model) :
    coverPullback U θ x v = θ ((periods U).quotientMap x)
      (fun i => mfderiv IF IF (periods U).quotientMap x (v i)) := rfl

/-- The actual native coefficient covector of the genuine pulled-back form. -/
def nativeCoefficients {p : ℕ} (θ : Form U p) (x : Cover U) :
    Model [⋀^Fin p]→L[ℂ] ℂ :=
  HolomorphicDifferentialForms.nativeCoefficients Model (Cover U) (coverPullback U θ) x

@[simp] theorem nativeCoefficients_apply {p : ℕ} (θ : Form U p)
    (x : Cover U) (v : Fin p → Model) :
    nativeCoefficients U θ x v = coverPullback U θ x v :=
  HolomorphicDifferentialForms.nativeCoefficients_apply Model (Cover U)
    (coverPullback U θ) x v

/-- Analyticity follows in the unchanged inherited charts of the actual cover. -/
theorem nativeCoefficients_holomorphic {p : ℕ} (θ : Form U p) :
    ContMDiff IF 𝓘(ℂ, Model [⋀^Fin p]→L[ℂ] ℂ) ω (nativeCoefficients U θ) :=
  HolomorphicDifferentialForms.nativeCoefficients_holomorphic_of_constant_charts
    Model (Cover U) (cover_chart_eq U) (coverPullback U θ)

/-- Every integral original period represents the same point of the native family. -/
theorem quotientMap_add_period (z : U) (ℓ : Lattice) (ζ : ComplexPlane₂) :
    (periods U).quotientMap
        (z, ζ + PeriodFamilyHolomorphicForms.periodShift (periods U) z ℓ) =
      (periods U).quotientMap (z, ζ) := by
  rw [← (periods U).fibreInclusion_mkQ, ← (periods U).fibreInclusion_mkQ]
  apply congrArg ((periods U).fibreInclusion z)
  apply PeriodTorusQuasiperiodic.quotient_add_lattice
  rw [PeriodFamilyHolomorphicForms.periodShift_eq_matrix]
  exact PeriodTorusQuasiperiodic.integer_period_mem_lattice _ ℓ

/-- Genuine pullback invariance is proved from the actual quotient identity;
it is not an extra assumption on the given local form. -/
theorem coverPullback_isPeriodInvariant {p : ℕ} (θ : Form U p) :
    HolomorphicDifferentialForms.PeriodLaws.IsPeriodInvariant (periods U)
      (coverPullback U θ) := by
  intro ℓ
  apply HolomorphicDifferentialForms.pullback_deck
    (periods U).quotientMap (quotientMap_holomorphic U)
    (HolomorphicDifferentialForms.PeriodLaws.periodTranslation (periods U) ℓ)
    (HolomorphicDifferentialForms.PeriodLaws.periodTranslation_holomorphic (periods U) ℓ)
  funext x
  exact quotientMap_add_period U x.1 ℓ x.2

/-- Restriction preserves the original period vector itself. -/
theorem periodShift_eq (z : U) (ℓ : Lattice) :
    PeriodFamilyHolomorphicForms.periodShift (periods U) z ℓ =
      PeriodFamilyHolomorphicForms.periodShift specialPeriodMap z.val ℓ := rfl

/-- The inherited open inclusion has identity derivative, so the actual
restricted period derivative is the original upper-half-plane derivative. -/
theorem periodDerivative_eq (z : U) (ℓ : Lattice) :
    PeriodFamilyHolomorphicForms.periodDerivative (periods U) z ℓ =
      PeriodFamilyHolomorphicForms.periodDerivative specialPeriodMap z.val ℓ := by
  have hg :=
    (PeriodFamilyHolomorphicForms.periodShift_holomorphic specialPeriodMap ℓ).mdifferentiable
      (by simp) z.val
  have hf := (contMDiff_subtype_val (I := I₁) (n := ω) (U := U)).mdifferentiable
    (by simp) z
  have h := mfderiv_comp_apply z
    (g := fun b : ℍ => PeriodFamilyHolomorphicForms.periodShift specialPeriodMap b ℓ)
    (f := (Subtype.val : U → ℍ)) hg hf (1 : ℂ)
  rw [HolomorphicDifferentialForms.mfderiv_openSubtypeVal] at h
  exact h.trans rfl

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicDifferentialForms
