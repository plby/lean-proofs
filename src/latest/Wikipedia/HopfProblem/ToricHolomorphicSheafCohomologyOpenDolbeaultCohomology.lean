import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultAcyclic
import Wikipedia.HopfProblem.ToricHolomorphicSheafCohomologyOpenDolbeaultGlobal

/-!
# Actual open-domain Dolbeault solvability implies genuine cohomology vanishing

The resolution is the exact restriction of the literal affine Dolbeault
resolution, and each smooth term is genuinely acyclic. The actual Ext
comparison in degree one and two therefore applies to its true global
section complex. The two required global solvability properties concern
only literal coordinate derivatives; the punctured-product application
proves both properties by the constructed analytic primitives.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault

/-- Actual global closed-pair solvability kills the genuine degree-one Ext group. -/
theorem restricted_h1_subsingleton (Ω : Opens (ℂ × ℂ)) (hOne : ClosedOneSolvable Ω) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedHolomorphicSheaf Ω) 1) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedResolution Ω).complex.X₁ 1) :=
    restricted_smooth_higher_subsingleton Ω 0
  have hz := ((restrictedResolution Ω).globalComplex.exact_iff_isZero_homology).mp
    (globalComplex_exact Ω hOne)
  exact AddCommGrpCat.subsingleton_of_isZero
    (hz.of_iso (restrictedResolution Ω).h1Iso)

/-- Actual global top solvability kills the genuine degree-two Ext group. -/
theorem restricted_h2_subsingleton (Ω : Opens (ℂ × ℂ)) (hTop : TopSolvable Ω) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedHolomorphicSheaf Ω) 2) := by
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedResolution Ω).complex.X₁ 1) :=
    restricted_smooth_higher_subsingleton Ω 0
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedResolution Ω).complex.X₁ 2) :=
    restricted_smooth_higher_subsingleton Ω 1
  let : Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedResolution Ω).complex.X₂ 1) :=
    restricted_pair_higher_subsingleton Ω 0
  let : Epi (restrictedResolution Ω).globalComplex.g := globalComplex_top_epi Ω hTop
  exact AddCommGrpCat.subsingleton_of_isZero
    ((isZero_cokernel_of_epi (restrictedResolution Ω).globalComplex.g).of_iso
      (restrictedResolution Ω).h2Iso)

/-- Genuine restricted holomorphic cohomology vanishes when the two literal
global differential equations have actual smooth-on-domain solutions. -/
theorem restricted_higher_subsingleton_of_solvable (Ω : Opens (ℂ × ℂ))
    (hOne : ClosedOneSolvable Ω) (hTop : TopSolvable Ω) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0} (restrictedHolomorphicSheaf Ω) (n + 1)) := by
  cases n with
  | zero => exact restricted_h1_subsingleton Ω hOne
  | succ n =>
    cases n with
    | zero => exact restricted_h2_subsingleton Ω hTop
    | succ n =>
      exact (restrictedResolution Ω).h_subsingleton_above_two
        (restricted_smooth_higher_subsingleton Ω)
        (restricted_pair_higher_subsingleton Ω)
        (restricted_smooth_higher_subsingleton Ω) n

/-- The actual holomorphic function sheaf of the open submanifold has no
positive genuine cohomology under literal global coordinate solvability. -/
theorem holomorphic_higher_subsingleton_of_solvable (Ω : Opens (ℂ × ℂ))
    (hOne : ClosedOneSolvable Ω) (hTop : TopSolvable Ω) (n : ℕ) :
    Subsingleton (CategoryTheory.Sheaf.H.{0}
      (HolomorphicFunctionSheaf.additiveSheaf 𝓘(ℂ, ℂ × ℂ) Ω) (n + 1)) := by
  let e := ((CategoryTheory.Sheaf.functorH _ (n + 1)).mapIso
    (holomorphicSheafIso Ω)).addCommGroupIsoToAddEquiv
  have hs := restricted_higher_subsingleton_of_solvable Ω hOne hTop n
  exact ⟨fun a b => e.symm.injective (hs.elim (e.symm a) (e.symm b))⟩

end Wikipedia.HopfProblem.HolomorphicSheafCohomology.OpenDolbeault
