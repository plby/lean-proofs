import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyComplex
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologyToricTopology
import Wikipedia.HopfProblem.ConstantSheafFirstCohomologySphereTopology

/-!
# Constant-sheaf first cohomology for the actual normalization components

These are the genuine constant complex sheaves and Mathlib's original
Ext-defined first cohomology groups on the toric ray surfaces and the
Riemann sphere appearing in §9.12 of `tex/s6.tex`. Their actual affine
charts prove simple connectedness, and the native sheaf-extension argument
then gives the unconditional vanishings needed by the normalization
resolution. No singular/sheaf comparison or acyclicity is assumed.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafFirstCohomology

open CuspNormalization.SheafConstants

/-- Actual constant complex first cohomology vanishes on every original
toric ray surface. -/
theorem rayDivisor_h1_subsingleton (v : Fin 2 → ℤ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor v))) 1) := by
  let : SimplyConnectedSpace (ToricSpace.rayDivisor v) :=
    ToricTopology.rayDivisor_simplyConnectedSpace v
  let : LocallyPathConnectedSpace (ToricSpace.rayDivisor v) :=
    ToricTopology.rayDivisor_locallyPathConnectedSpace v
  exact complex_h1_subsingleton

/-- The literal normalization component `E₀` has zero constant complex
first sheaf cohomology. -/
theorem zeroRay_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor (0 : Fin 2 → ℤ)))) 1) :=
  rayDivisor_h1_subsingleton 0

/-- Every actual first constant-sheaf cohomology class of `E₀` is zero. -/
theorem zeroRay_h1_eq_zero
    (ξ : CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor (0 : Fin 2 → ℤ)))) 1) : ξ = 0 :=
  zeroRay_h1_subsingleton.elim ξ 0

/-- The actual Riemann sphere has zero first constant complex sheaf cohomology. -/
theorem sphere_h1_subsingleton :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of RiemannSphere)) 1) := by
  let : SimplyConnectedSpace RiemannSphere := sphere_simplyConnectedSpace
  let : LocallyPathConnectedSpace RiemannSphere := sphere_locallyPathConnectedSpace
  exact complex_h1_subsingleton

/-- Every actual first constant-sheaf cohomology class of the Riemann sphere is zero. -/
theorem sphere_h1_eq_zero
    (ξ : CategoryTheory.Sheaf.H.{0}
      (complexAdditiveSheaf (TopCat.of RiemannSphere)) 1) : ξ = 0 :=
  sphere_h1_subsingleton.elim ξ 0

/-- The original first cohomology object of `E₀` is zero. -/
theorem zeroRay_h1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of (ToricSpace.rayDivisor (0 : Fin 2 → ℤ)))) 1).obj
        (complexAdditiveSheaf (TopCat.of (ToricSpace.rayDivisor (0 : Fin 2 → ℤ))))) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr zeroRay_h1_subsingleton

/-- The original first cohomology object of the Riemann sphere is zero. -/
theorem sphere_h1_isZero : Limits.IsZero
    ((CategoryTheory.Sheaf.functorH
      (Opens.grothendieckTopology (TopCat.of RiemannSphere)) 1).obj
        (complexAdditiveSheaf (TopCat.of RiemannSphere))) :=
  AddCommGrpCat.isZero_iff_subsingleton.mpr sphere_h1_subsingleton

end Wikipedia.HopfProblem.ConstantSheafFirstCohomology
