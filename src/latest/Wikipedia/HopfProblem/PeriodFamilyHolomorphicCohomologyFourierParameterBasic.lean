import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologySmoothOpen
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDerivativeBasic

/-!
# Genuine jointly smooth families on the fixed unit torus

The family is an actual function on an open complex base times the product
of unit additive circles. Joint smoothness means real smoothness of its
literal lift through the integer-lattice quotient, on the original open
base. The ambient representative is extended by zero only outside that
base; no regularity across its boundary is required.

Joint continuity and smoothness of each actual torus slice are consequences
of this one smooth-lift hypothesis. No Fourier estimate is part of the data.
-/

noncomputable section

open Function TopologicalSpace
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter

open PeriodTorusLineBundleClassification

variable {U : Opens ℂ} {d : Type*}

/-- The literal product of the original open base with the integer-lattice quotient. -/
def familyQuotient (x : U × (d → ℝ)) : U × UnitAddTorus d :=
  (x.1, torusQuotient x.2)

theorem familyQuotient_isOpenQuotientMap :
    IsOpenQuotientMap (familyQuotient (U := U) (d := d)) := by
  have hq : IsOpenQuotientMap (torusQuotient (d := d)) :=
    IsOpenQuotientMap.piMap
      (fun _ : d => (QuotientAddGroup.isOpenQuotientMap_mk :
        IsOpenQuotientMap (fun x : ℝ => (x : UnitAddCircle))))
  exact IsOpenQuotientMap.id.prodMap hq

/-- Ambient representative of the actual lift, used only on the original open base. -/
def ambientLift (f : U × UnitAddTorus d → ℂ) (x : ℂ × (d → ℝ)) : ℂ := by
  classical
  exact if hx : x.1 ∈ U then f (⟨x.1, hx⟩, torusQuotient x.2) else 0

@[simp] theorem ambientLift_apply (f : U × UnitAddTorus d → ℂ)
    (b : U) (x : d → ℝ) :
    ambientLift f ((b : ℂ), x) = f (b, torusQuotient x) := by
  simp only [ambientLift, dif_pos b.property]

variable [Fintype d]

/-- Smoothness of the actual joint lift implies joint continuity on the quotient. -/
theorem continuous_of_contDiffOn_lift {f : U × UnitAddTorus d → ℂ}
    (hf : ContDiffOn ℝ ∞ (ambientLift f) (Smooth.baseProductDomain U (d → ℝ))) :
    Continuous f := by
  apply familyQuotient_isOpenQuotientMap.isQuotientMap.continuous_iff.mpr
  have h : Continuous (fun x : U × (d → ℝ) => ambientLift f ((x.1 : ℂ), x.2)) :=
    hf.continuousOn.comp_continuous
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
      (fun x => x.1.property)
  simpa only [Function.comp_def, familyQuotient, ambientLift_apply] using h

/-- An actual jointly smooth scalar family on the original base and fixed unit torus. -/
structure SmoothFamily (U : Opens ℂ) (d : Type*) [Fintype d] where
  toFun : U × UnitAddTorus d → ℂ
  smooth_lift : ContDiffOn ℝ ∞ (ambientLift toFun) (Smooth.baseProductDomain U (d → ℝ))

instance : CoeFun (SmoothFamily U d) (fun _ => U × UnitAddTorus d → ℂ) :=
  ⟨SmoothFamily.toFun⟩

namespace SmoothFamily

variable (f : SmoothFamily U d)

theorem continuous : Continuous f := continuous_of_contDiffOn_lift f.smooth_lift

/-- The original jointly continuous quotient family, with no new continuity premise. -/
def toContinuousMap : C(U × UnitAddTorus d, ℂ) := ⟨f, f.continuous⟩

@[simp] theorem toContinuousMap_apply (x : U × UnitAddTorus d) :
    f.toContinuousMap x = f x := rfl

/-- The actual fibre is smooth because its lift is a slice of the joint lift. -/
theorem slice_contDiff (b : U) :
    ContDiff ℝ ∞ (fun x : d → ℝ => f (b, torusQuotient x)) := by
  rw [← contDiffOn_univ]
  have h : ContDiffOn ℝ ∞ (fun x : d → ℝ => ambientLift f ((b : ℂ), x)) Set.univ :=
    f.smooth_lift.comp (f := fun x : d → ℝ => ((b : ℂ), x))
    (contDiffOn_const.prodMk contDiffOn_id) (fun _ _ => b.property)
  simpa only [ambientLift_apply] using h

/-- The genuine smooth torus slice, using the frozen torus-function definition. -/
def slice (b : U) : SmoothTorusFunction d where
  toContinuousMap := ⟨fun t => f (b, t),
    f.continuous.comp (continuous_const.prodMk continuous_id)⟩
  smooth_lift := f.slice_contDiff b

@[simp] theorem slice_apply (b : U) (t : UnitAddTorus d) :
    f.slice b t = f (b, t) := rfl

@[simp] theorem slice_lift (b : U) (x : d → ℝ) :
    torusLift (f.slice b) x = ambientLift f ((b : ℂ), x) :=
  (ambientLift_apply f b x).symm

end SmoothFamily

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.FourierParameter
