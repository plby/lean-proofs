import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeault
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyBiholomorph
import Wikipedia.HopfProblem.ToricCharts

/-!
# Genuine affine holomorphic cohomology in the native toric coordinates

The continuous complex-linear coordinate equivalence sends `(z,w)` to
`![z,w]`. Its two directions are genuinely analytic. The proved actual
biholomorphic sheaf comparison transports the affine Dolbeault vanishing
to the native `CoordinateSpace 2 = Fin 2 → ℂ`, with its original norm.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts

open ToricCharts

/-- The actual continuous complex-linear product-to-native coordinate map. -/
def productNativeLinearEquiv : (ℂ × ℂ) ≃L[ℂ] CoordinateSpace 2 :=
  (ContinuousLinearEquiv.finTwoArrow ℂ ℂ).symm

@[simp] theorem productNativeLinearEquiv_apply (q : ℂ × ℂ) :
    productNativeLinearEquiv q = ![q.1, q.2] := rfl

@[simp] theorem productNativeLinearEquiv_symm_apply (z : CoordinateSpace 2) :
    productNativeLinearEquiv.symm z = (z 0, z 1) := rfl

/-- The actual coordinate equivalence, at analytic rather than merely smooth order. -/
def productNativeBiholomorph :
    Diffeomorph 𝓘(ℂ, ℂ × ℂ) 𝓘(ℂ, CoordinateSpace 2) (ℂ × ℂ) (CoordinateSpace 2) ω where
  toEquiv := productNativeLinearEquiv.toLinearEquiv.toEquiv
  contMDiff_toFun := productNativeLinearEquiv.contDiff.contMDiff
  contMDiff_invFun := productNativeLinearEquiv.symm.contDiff.contMDiff

@[simp] theorem productNativeBiholomorph_apply (q : ℂ × ℂ) :
    productNativeBiholomorph q = ![q.1, q.2] := rfl

@[simp] theorem productNativeBiholomorph_symm_apply (z : CoordinateSpace 2) :
    productNativeBiholomorph.symm z = (z 0, z 1) := rfl

/-- Genuine Ext-defined cohomology transported through the actual coordinate map. -/
def nativeCohomologyEquiv (n : ℕ) :
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (CoordinateSpace 2)) n ≃+
    CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ)) n :=
  Biholomorph.cohomologyEquiv productNativeBiholomorph n

/-- Every positive genuine holomorphic cohomology group of the native
affine two-space vanishes, without a coordinate-comparison premise. -/
theorem native_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (CoordinateSpace 2))
      (n + 1)) := by
  let e := nativeCohomologyEquiv (n + 1)
  exact ⟨fun a b => e.injective ((AffineDolbeault.affine_higher_subsingleton n).elim (e a) (e b))⟩

theorem native_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (CoordinateSpace 2))
      (n + 1)) : a = 0 :=
  (native_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.Charts
