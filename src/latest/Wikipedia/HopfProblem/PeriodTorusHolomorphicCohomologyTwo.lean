import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyResolutionNative
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearCokernel

/-!
# Genuine degree-two holomorphic cohomology and Haar mean

The actual double Ext connecting map compares degree two with the last
global Dolbeault cokernel. The proved top Fourier primitive identifies
that actual cokernel by probability Haar mean. The original sheaf scalar
action is retained, and literal constant top forms give the inverse.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology

/-- Actual degree-two holomorphic cohomology is complex-linearly the scalar field. -/
def h2Equiv (p : PeriodDomain) : H p 2 ≃ₗ[ℂ] ℂ :=
  (h2FourierEquiv p).trans (FourierLinear.cokernelIso p).toLinearEquiv

/-- The actual Ext class represented by a smooth top Fourier coefficient. -/
def h2Class (p : PeriodDomain) : FourierLinear.Smooth →ₗ[ℂ] H p 2 :=
  (h2FourierEquiv p).symm.toLinearMap.comp (cokernel.π (FourierLinear.complex p).g).hom

/-- The degree-two coordinate is exactly the actual coefficient's probability Haar mean. -/
@[simp] theorem h2Equiv_class (p : PeriodDomain) (f : FourierLinear.Smooth) :
    h2Equiv p (h2Class p f) = FourierLinear.meanLinear f := by
  change (FourierLinear.cokernelIso p).hom
    (h2FourierEquiv p ((h2FourierEquiv p).symm
      (cokernel.π (FourierLinear.complex p).g f))) = _
  rw [LinearEquiv.apply_symm_apply]
  exact FourierLinear.cokernelIso_π_apply p f

/-- The actual cohomology classes of literal constant top coefficients. -/
def h2Constant (p : PeriodDomain) : ℂ →ₗ[ℂ] H p 2 :=
  (h2Class p).comp FourierLinear.constantLinear

@[simp] theorem h2Equiv_constant (p : PeriodDomain) (c : ℂ) :
    h2Equiv p (h2Constant p c) = c := by
  change h2Equiv p (h2Class p (FourierLinear.constantLinear c)) = c
  rw [h2Equiv_class, FourierLinear.mean_constant]

/-- The inverse is the actual class of the literal constant top form. -/
@[simp] theorem h2Equiv_symm_apply (p : PeriodDomain) (c : ℂ) :
    (h2Equiv p).symm c = h2Constant p c := by
  apply (h2Equiv p).injective
  rw [LinearEquiv.apply_symm_apply, h2Equiv_constant]

/-- Zero probability Haar mean is equivalent to vanishing of the original Ext class. -/
theorem h2Class_eq_zero_iff (p : PeriodDomain) (f : FourierLinear.Smooth) :
    h2Class p f = 0 ↔ FourierLinear.meanLinear f = 0 := by
  rw [← (h2Equiv p).map_eq_zero_iff, h2Equiv_class]

/-- Every top coefficient has the actual class of its literal constant Haar mean. -/
theorem h2Class_eq_constant (p : PeriodDomain) (f : FourierLinear.Smooth) :
    h2Class p f = h2Constant p (FourierLinear.meanLinear f) := by
  apply (h2Equiv p).injective
  rw [h2Equiv_class, h2Equiv_constant]

/-- The actual Ext class of a literal top coefficient on the original quotient torus. -/
def nativeH2Class (p : PeriodDomain) : Dolbeault.SmoothSection p ⊤ →ₗ[ℂ] H p 2 :=
  (h2Class p).comp (GlobalFourier.sectionEquiv p).toLinearMap

@[simp] theorem h2Equiv_nativeClass (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    h2Equiv p (nativeH2Class p s) = GlobalFourier.mean p s :=
  h2Equiv_class p (GlobalFourier.sectionEquiv p s)

/-- The dimension follows from the actual complex-linear mean comparison. -/
theorem h2_finrank (p : PeriodDomain) : Module.finrank ℂ (H p 2) = 1 :=
  (h2Equiv p).finrank_eq.trans (Module.finrank_self ℂ)

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology
