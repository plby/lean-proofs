import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereDolbeaultExact
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologySphereFormsFine
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1

/-!
# Genuine higher holomorphic sheaf cohomology of the sphere

For the actual holomorphic-function sheaf on the constructed Riemann
sphere, every positive Mathlib `Sheaf.H` group is zero. Degree one uses
the already proved actual Cousin construction. The higher degrees use
the newly proved genuine short exact Dolbeault sequence, actual smooth
and form-sheaf acyclicity, and the actual Ext connecting maps.

No Dolbeault comparison, Cartan theorem, Stein vanishing, or analytic
solvability statement is assumed. This supplies the sphere acyclicity
input needed for the actual double curves in the cusp resolution.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault

open HolomorphicFunctionSheaf.SphereH1
open CuspNormalization.SheafCohomologyResolution

/-- All positive genuine Ext-defined holomorphic sheaf-cohomology
groups of the actual analytic Riemann sphere vanish. -/
theorem holomorphic_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} holomorphicSheaf (n + 1)) := by
  cases n with
  | zero => exact sphere_h1_subsingleton
  | succ n =>
    have hs := @connecting_surjective
      (TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere)) _ _ _
      (constantIntegerSheaf (TopCat.of RiemannSphere))
      dolbeaultComplex dolbeaultComplex_shortExact (n + 1)
      (SphereForms.smooth_higher_subsingleton (n + 1))
    have hF := SphereForms.higher_subsingleton n
    refine ⟨fun a b => ?_⟩
    obtain ⟨a', rfl⟩ := hs a
    obtain ⟨b', rfl⟩ := hs b
    exact congrArg (connecting
      (C := TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere))
      (constantIntegerSheaf (TopCat.of RiemannSphere)) dolbeaultComplex_shortExact (n + 1))
      (hF.elim a' b')

/-- The additive structure is exactly the existing one on Mathlib Ext. -/
instance holomorphicCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} holomorphicSheaf n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- Every actual positive-degree holomorphic cohomology class on the
constructed sphere equals zero. -/
theorem holomorphic_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} holomorphicSheaf (n + 1)) : a = 0 :=
  (holomorphic_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.SphereDolbeault
