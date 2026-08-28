import Wikipedia.HopfProblem.SheafLerayCurveSequenceNaturality
import Wikipedia.HopfProblem.SheafLerayLowDegreesScalarsBasic

/-!
# Complex-linearity of the genuine higher curve-type Leray maps

The source cohomology scalar action is induced by the original scalar
sheaf endomorphisms. The higher-direct-image actions apply the genuine
right-derived pushforward to those same endomorphisms. Coefficient
naturality proves that the two original Leray maps are complex linear.

The short exact assertion uses exactly the same finite cohomology
vanishing hypothesis as the native additive sequence. No splitting or
dimension conclusion is added.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayCurve.Scalars

open SheafHigherDirectImage
open CuspNormalization.SheafCohomology
open SheafLerayLowDegrees.Scalars (higherCohomologyModule)

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)
  (ρ : ℂ →+* End F) (n : ℕ)

/-- The original left Leray map with its genuine sheaf-induced complex scalar actions. -/
def inflationLinearMap (h : CohomologyVanishing f F (n + 3)) :
    letI := higherCohomologyModule f F ρ (n + 1) 1
    letI := cohomologyModule F ρ (n + 2)
    CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 1)) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} F (n + 2) := by
  letI := higherCohomologyModule f F ρ (n + 1) 1
  letI := cohomologyModule F ρ (n + 2)
  refine { __ := inflation f F n h, map_smul' := ?_ }
  intro c x
  exact inflation_naturality f (ρ c) n h h x

/-- The underlying map is exactly the original native additive inflation. -/
@[simp] theorem inflationLinearMap_apply (h : CohomologyVanishing f F (n + 3))
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 1)) 1) :
    letI := higherCohomologyModule f F ρ (n + 1) 1
    letI := cohomologyModule F ρ (n + 2)
    inflationLinearMap f F ρ n h x = inflation f F n h x := rfl

/-- The original right edge is complex linear without any vanishing hypothesis. -/
def edgeLinearMap :
    letI := cohomologyModule F ρ (n + 2)
    letI := higherCohomologyModule f F ρ (n + 2) 0
    CategoryTheory.Sheaf.H.{0} F (n + 2) →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (sheaf f F (n + 2)) 0 := by
  letI := cohomologyModule F ρ (n + 2)
  letI := higherCohomologyModule f F ρ (n + 2) 0
  refine { __ := edge f F n, map_smul' := ?_ }
  intro c x
  exact edge_naturality f (ρ c) n x

/-- The underlying map is exactly the original native additive edge. -/
@[simp] theorem edgeLinearMap_apply (x : CategoryTheory.Sheaf.H.{0} F (n + 2)) :
    letI := cohomologyModule F ρ (n + 2)
    letI := higherCohomologyModule f F ρ (n + 2) 0
    edgeLinearMap f F ρ n x = edge f F n x := rfl

/-- The original native short exact sequence, with its genuinely complex-linear maps
and exactly its original finite cohomology vanishing hypothesis. -/
theorem linear_short_exact (h : CohomologyVanishing f F (n + 3)) :
    letI := higherCohomologyModule f F ρ (n + 1) 1
    letI := cohomologyModule F ρ (n + 2)
    letI := higherCohomologyModule f F ρ (n + 2) 0
    Function.Injective (inflationLinearMap f F ρ n h) ∧
      Function.Exact (inflationLinearMap f F ρ n h) (edgeLinearMap f F ρ n) ∧
        Function.Surjective (edgeLinearMap f F ρ n) :=
  short_exact f F n h

end Wikipedia.HopfProblem.SheafLerayCurve.Scalars
