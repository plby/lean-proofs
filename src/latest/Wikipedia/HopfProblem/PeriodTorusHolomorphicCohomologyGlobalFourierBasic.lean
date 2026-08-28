import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyDolbeaultGlobalBasic
import Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomologyFourierLinearComplex

/-!
# Native global smooth sections and the actual Fourier functions

Pullback through the original period covering, followed by the actual
marked real-torus quotient, gives a complex-linear bijection. Its inverse
is the proved native smooth descent. Both inverse identities are equalities
of the literal functions, not choices of abstract vector-space markings.
-/

noncomputable section

open UnitAddTorus TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier

open PeriodTorusLineBundleClassification FourierLinear

/-- The covering lift distinguishes the actual marked smooth torus functions. -/
theorem periodLift_injective (p : PeriodDomain) : Function.Injective (periodTorusLift p) := by
  intro f g h
  apply smooth_ext
  intro t
  obtain ⟨x, rfl⟩ := torusQuotient_surjective t
  have hx := congrFun h (PeriodTorusTypeOneOne.periodEquiv p x)
  simpa only [periodTorusLift_periodEquiv, torusLift, Function.comp_apply] using hx

/-- The literal Fourier function obtained by lifting the native smooth section. -/
def toFourier (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) : Smooth :=
  smoothTorusOfLatticePeriodic p (Dolbeault.globalLift p s)
    (Dolbeault.globalLift_contDiff p s) (Dolbeault.globalLift_periodic p s)

/-- Descend the actual covering lift of a Fourier function in the original native atlas. -/
def fromFourier (p : PeriodDomain) (f : Smooth) : Dolbeault.SmoothSection p ⊤ :=
  Dolbeault.ofPeriodicSmooth p (periodTorusLift p f) (contDiff_periodTorusLift p f)
    (fun z l => periodTorusLift_add_lattice p f z l l.property)

@[simp] theorem lift_toFourier (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    periodTorusLift p (toFourier p s) = Dolbeault.globalLift p s :=
  funext (periodTorusLift_smoothTorusOfLatticePeriodic p _ _ _)

@[simp] theorem lift_fromFourier (p : PeriodDomain) (f : Smooth) :
    Dolbeault.globalLift p (fromFourier p f) = periodTorusLift p f :=
  Dolbeault.globalLift_ofPeriodicSmooth p _ _ _

@[simp] theorem fromFourier_toFourier (p : PeriodDomain)
    (s : Dolbeault.SmoothSection p ⊤) : fromFourier p (toFourier p s) = s := by
  apply Dolbeault.globalLift_injective p
  rw [lift_fromFourier, lift_toFourier]

@[simp] theorem toFourier_fromFourier (p : PeriodDomain) (f : Smooth) :
    toFourier p (fromFourier p f) = f := by
  apply periodLift_injective p
  rw [lift_toFourier, lift_fromFourier]

theorem toFourier_add (p : PeriodDomain) (s t : Dolbeault.SmoothSection p ⊤) :
    toFourier p (s + t) = toFourier p s + toFourier p t := by
  apply periodLift_injective p
  funext z
  change periodTorusLift p (toFourier p (s + t)) z =
    periodTorusLift p (toFourier p s) z + periodTorusLift p (toFourier p t) z
  rw [lift_toFourier, lift_toFourier, lift_toFourier]
  rfl

theorem toFourier_smul (p : PeriodDomain) (c : ℂ) (s : Dolbeault.SmoothSection p ⊤) :
    toFourier p (c • s) = c • toFourier p s := by
  apply periodLift_injective p
  funext z
  change periodTorusLift p (toFourier p (c • s)) z =
    c * periodTorusLift p (toFourier p s) z
  rw [lift_toFourier, lift_toFourier]
  rfl

/-- The genuine global-section/Fourier comparison, retaining pointwise complex linearity. -/
def sectionEquiv (p : PeriodDomain) : Dolbeault.SmoothSection p ⊤ ≃ₗ[ℂ] Smooth where
  toFun := toFourier p
  invFun := fromFourier p
  left_inv := fromFourier_toFourier p
  right_inv := toFourier_fromFourier p
  map_add' := toFourier_add p
  map_smul' := toFourier_smul p

@[simp] theorem sectionEquiv_apply (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    sectionEquiv p s = toFourier p s := rfl

@[simp] theorem sectionEquiv_symm_apply (p : PeriodDomain) (f : Smooth) :
    (sectionEquiv p).symm f = fromFourier p f := rfl

/-- The comparison has exactly the same values on every original covering point. -/
theorem sectionEquiv_lift (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤)
    (z : ComplexPlane₂) :
    periodTorusLift p (sectionEquiv p s) z = s ⟨p.lattice.mkQ z, by simp⟩ :=
  congrFun (lift_toFourier p s) z

/-- The comparison takes a literal constant native section to that same constant function. -/
@[simp] theorem sectionEquiv_constant (p : PeriodDomain) (c : ℂ) :
    sectionEquiv p (ContMDiffMap.const c) = constantLinear c := by
  apply periodLift_injective p
  funext z
  exact sectionEquiv_lift p (ContMDiffMap.const c) z

/-- Actual probability Haar integration on native global smooth functions. -/
def mean (p : PeriodDomain) : Dolbeault.SmoothSection p ⊤ →ₗ[ℂ] ℂ :=
  meanLinear.comp (sectionEquiv p).toLinearMap

@[simp] theorem mean_apply (p : PeriodDomain) (s : Dolbeault.SmoothSection p ⊤) :
    mean p s = torusFourierMean (sectionEquiv p s) := rfl

@[simp] theorem mean_constant (p : PeriodDomain) (c : ℂ) :
    mean p (ContMDiffMap.const c) = c := by
  change meanLinear (sectionEquiv p (ContMDiffMap.const c)) = c
  rw [sectionEquiv_constant, FourierLinear.mean_constant]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCohomology.GlobalFourier
