import Wikipedia.HopfProblem.HolomorphicFunctionSheafGlobal
import Wikipedia.HopfProblem.RiemannSphere
import Mathlib.Geometry.Manifold.Complex

/-!
# Constancy on the actual compact analytic sphere

The compact maximum principle applies to the constructed atlas on the
one-point compactification of the complex plane.  In particular, an
actual global holomorphic sheaf section takes the same value everywhere.
This will force every section of the ideal vanishing at infinity to be zero.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

/-- Actual complex-valued holomorphic functions on the constructed sphere
are constant, by the compact maximum principle. -/
theorem sphere_holomorphic_apply_eq {f : RiemannSphere → ℂ}
    (hf : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω f) (x y : RiemannSphere) :
    f x = f y :=
  (hf.mdifferentiable (by simp)).apply_eq_of_compactSpace x y

/-- Constancy is stated on literal global sections, not on a separately
defined space of constants. -/
theorem sphere_globalSection_apply_eq
    (f : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere ⊤)
    (x y : (⊤ : Opens RiemannSphere)) : f x = f y := by
  exact sphere_holomorphic_apply_eq
    (globalSectionToMap 𝓘(ℂ) RiemannSphere f).contMDiff x y

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
