import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyHolomorphicRestrictionCohomology
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyCharts

/-!
# Genuine ambient-open holomorphic cohomology on the actual affine charts

These are Mathlib's original `Sheaf.H'` groups of the actual ambient
holomorphic function sheaves on the six zero-ray chart opens and the two
incidence-model chart opens. Actual open restriction and actual chart
biholomorphisms transfer the unconditional affine vanishing to precisely
the groups used by the genuine Mayer--Vietoris sequence.
-/

noncomputable section

open TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction

open ToricCharts ToricSpace ToricComponent

/-- Every actual toric affine chart has vanishing positive cohomology
for the ambient holomorphic sheaf in Mathlib's actual cohomology presheaf. -/
theorem affine_higher_subsingleton {v : Fin 2 → ℤ} (c : ChartIndex v) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor v))
      (n + 1) (Charts.affineOpen c)) := by
  let e := cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (Charts.affineOpen c) (n + 1)
  exact ⟨fun a b => e.injective ((Charts.affine_higher_subsingleton c n).elim (e a) (e b))⟩

/-- Actual positive `H'` of the ambient zero-ray holomorphic sheaf on
each of the six literal chart opens vanishes without any extra premise. -/
theorem zero_higher_subsingleton (i : Fin 6) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0))
      (n + 1) (Charts.zeroOpen i)) :=
  affine_higher_subsingleton (zeroChart i) n

theorem zero_higher_eq_zero (i : Fin 6) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) (rayDivisor 0))
      (n + 1) (Charts.zeroOpen i)) : a = 0 :=
  (zero_higher_subsingleton i n).elim a 0

/-- Actual positive `H'` of the ambient incidence-model holomorphic
sheaf vanishes on either of its actual affine chart opens. -/
theorem incidence_higher_subsingleton (b : Bool) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) AffineBlowup.Space)
      (n + 1) (Charts.incidenceOpen b)) := by
  let e := cohomologyEquiv 𝓘(ℂ, CoordinateSpace 2) (Charts.incidenceOpen b) (n + 1)
  exact ⟨fun a c => e.injective ((Charts.incidence_higher_subsingleton b n).elim (e a) (e c))⟩

theorem incidence_higher_eq_zero (b : Bool) (n : ℕ)
    (a : CategoryTheory.Sheaf.H'.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, CoordinateSpace 2) AffineBlowup.Space)
      (n + 1) (Charts.incidenceOpen b)) : a = 0 :=
  (incidence_higher_subsingleton b n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.HolomorphicRestriction
