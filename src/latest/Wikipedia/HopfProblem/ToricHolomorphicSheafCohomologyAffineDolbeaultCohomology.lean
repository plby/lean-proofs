import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultGlobal
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyAffineDolbeaultAcyclic

/-!
# Genuine positive holomorphic cohomology vanishing on `ℂ × ℂ`

The actual Dolbeault resolution has genuinely acyclic smooth terms. Its
actual global section complex is exact and its last map is surjective by
the constructed analytic primitives. The already proved Ext comparisons
identify degree one with its homology and degree two with its cokernel;
the actual two long exact sequences give every higher degree.

The result concerns Mathlib's original Ext-defined `Sheaf.H` of the actual
holomorphic function sheaf. There is no vanishing, solvability, exactness,
or comparison premise in the endpoint.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault

/-- Degree one vanishes by the genuine comparison with the actual exact
global section complex of the actual smooth resolution. -/
theorem h1_subsingleton : Subsingleton (CategoryTheory.Sheaf.H.{0} holomorphicSheaf 1) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} resolution.complex.X₁ 1) :=
    smooth_higher_subsingleton 0
  have hz := (resolution.globalComplex.exact_iff_isZero_homology).mp globalComplex_exact
  exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso resolution.h1Iso)

/-- Degree two vanishes because the literal global top derivative is
surjective, using the genuine degree-two Ext/cokernel comparison. -/
theorem h2_subsingleton : Subsingleton (CategoryTheory.Sheaf.H.{0} holomorphicSheaf 2) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} resolution.complex.X₁ 1) :=
    smooth_higher_subsingleton 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} resolution.complex.X₁ 2) :=
    smooth_higher_subsingleton 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} resolution.complex.X₂ 1) :=
    pair_higher_subsingleton 0
  exact AddCommGrpCat.subsingleton_of_isZero
    ((isZero_cokernel_of_epi resolution.globalComplex.g).of_iso resolution.h2Iso)

/-- Every positive genuine cohomology group of the actual holomorphic
function sheaf on the actual affine complex plane is zero. -/
theorem affine_higher_subsingleton (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ)) (n + 1)) := by
  cases n with
  | zero => exact h1_subsingleton
  | succ n =>
    cases n with
    | zero => exact h2_subsingleton
    | succ n =>
      exact resolution.h_subsingleton_above_two smooth_higher_subsingleton
        pair_higher_subsingleton smooth_higher_subsingleton n

/-- The vanishing assertion in the original additive group of actual
Ext classes, rather than in a replacement cohomology model. -/
theorem affine_higher_eq_zero (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) (ℂ × ℂ)) (n + 1)) : a = 0 :=
  (affine_higher_subsingleton n).elim a 0

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.AffineDolbeault
