import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarNative
import Mathlib.Algebra.Module.Defs

/-!
# Pointwise linear structure on actual smooth torus functions

The Fourier solver's existing functions are continuous maps on the real
quotient torus with genuinely smooth lifts. Their linear operations are
literal pointwise operations, and their coefficient maps are the actual
Haar Fourier coefficients. No cohomology group is defined in this file.
-/

noncomputable section

open UnitAddTorus
open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear

open PeriodTorusLineBundleClassification

variable {d : Type*} [Fintype d]

theorem continuousMap_injective : Function.Injective
    (SmoothTorusFunction.toContinuousMap : SmoothTorusFunction d → C(UnitAddTorus d, ℂ)) := by
  intro f g h
  cases f
  cases g
  cases h
  rfl

@[ext] theorem smooth_ext {f g : SmoothTorusFunction d}
    (h : ∀ t, f t = g t) : f = g :=
  continuousMap_injective (ContinuousMap.ext h)

instance : Zero (SmoothTorusFunction d) :=
  ⟨⟨0, contDiff_const⟩⟩

instance : Add (SmoothTorusFunction d) :=
  ⟨fun f g => ⟨f.toContinuousMap + g.toContinuousMap, f.smooth_lift.add g.smooth_lift⟩⟩

instance : Neg (SmoothTorusFunction d) :=
  ⟨fun f => ⟨-f.toContinuousMap, f.smooth_lift.neg⟩⟩

instance : Sub (SmoothTorusFunction d) :=
  ⟨fun f g => ⟨f.toContinuousMap - g.toContinuousMap, f.smooth_lift.sub g.smooth_lift⟩⟩

instance pointwiseSMul {R : Type*} [DistribSMul R ℂ] [SMulCommClass ℝ R ℂ]
    [ContinuousConstSMul R ℂ] : SMul R (SmoothTorusFunction d) :=
  ⟨fun c f => ⟨c • f.toContinuousMap, f.smooth_lift.const_smul c⟩⟩

instance : AddCommGroup (SmoothTorusFunction d) :=
  Function.Injective.addCommGroup SmoothTorusFunction.toContinuousMap continuousMap_injective
    rfl (fun _ _ => rfl) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl)

instance : Module ℂ (SmoothTorusFunction d) :=
  Function.Injective.module ℂ
    { toFun := SmoothTorusFunction.toContinuousMap
      map_zero' := rfl
      map_add' _ _ := rfl }
    continuousMap_injective (fun _ _ => rfl)

@[simp] theorem zero_apply (t : UnitAddTorus d) : (0 : SmoothTorusFunction d) t = 0 := rfl

@[simp] theorem add_apply (f g : SmoothTorusFunction d) (t : UnitAddTorus d) :
    (f + g) t = f t + g t := rfl

@[simp] theorem neg_apply (f : SmoothTorusFunction d) (t : UnitAddTorus d) :
    (-f) t = -f t := rfl

@[simp] theorem sub_apply (f g : SmoothTorusFunction d) (t : UnitAddTorus d) :
    (f - g) t = f t - g t := rfl

@[simp] theorem smul_apply (c : ℂ) (f : SmoothTorusFunction d) (t : UnitAddTorus d) :
    (c • f) t = c * f t := rfl

/-- The genuine forgetful map to continuous functions preserves pointwise complex operations. -/
def continuousLinear : SmoothTorusFunction d →ₗ[ℂ] C(UnitAddTorus d, ℂ) where
  toFun := SmoothTorusFunction.toContinuousMap
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The actual Haar Fourier coefficient as a complex-linear map on smooth functions. -/
def coefficientLinear (k : d → ℤ) : SmoothTorusFunction d →ₗ[ℂ] ℂ :=
  (torusFourierCoeffLinear k).comp continuousLinear

@[simp] theorem coefficientLinear_apply (k : d → ℤ) (f : SmoothTorusFunction d) :
    coefficientLinear k f = mFourierCoeff f k := rfl

/-- The actual probability Haar mean, with its pointwise complex linearity. -/
def meanLinear : SmoothTorusFunction d →ₗ[ℂ] ℂ := coefficientLinear 0

@[simp] theorem meanLinear_apply (f : SmoothTorusFunction d) :
    meanLinear f = torusFourierMean f := rfl

/-- Literal constant smooth functions, not chosen representatives of a quotient. -/
def constantLinear : ℂ →ₗ[ℂ] SmoothTorusFunction d where
  toFun := smoothTorusConst
  map_add' _ _ := smooth_ext fun _ => rfl
  map_smul' _ _ := smooth_ext fun _ => rfl

@[simp] theorem constantLinear_apply (c : ℂ) (t : UnitAddTorus d) :
    constantLinear c t = c := rfl

@[simp] theorem mean_constant (c : ℂ) :
    meanLinear (d := d) (constantLinear c) = c := by
  change mFourierCoeff (fun _ : UnitAddTorus d => c) 0 = c
  rw [mFourierCoeff_const]
  simp only [ite_true]

theorem removeMean_eq (f : SmoothTorusFunction d) :
    torusRemoveMean f = f - constantLinear (meanLinear f) := rfl

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.FourierLinear
