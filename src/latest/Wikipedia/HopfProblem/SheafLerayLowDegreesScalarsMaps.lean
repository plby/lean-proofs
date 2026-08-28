import Wikipedia.HopfProblem.SheafLerayLowDegreesScalarsBasic
import Wikipedia.HopfProblem.SheafLerayLowDegreesSequenceElementNaturality

/-!
# Complex-linearity of the genuine low-degree Leray maps

The coefficient naturality of inflation, the edge map, and
transgression proves their complex-linearity for scalar actions induced
by actual sheaf endomorphisms. The underlying additive maps remain the
original maps in the proved unconditional low-degree sequence.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars

open SheafHigherDirectImage
open CuspNormalization.SheafCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)
  (ρ : ℂ →+* End F)

/-- The original inflation map, linear for the native scalar actions. -/
def inflationLinearMap :
    letI := pushforwardCohomologyModule f F ρ 1
    letI := cohomologyModule F ρ 1
    CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} F 1 := by
  letI := pushforwardCohomologyModule f F ρ 1
  letI := cohomologyModule F ρ 1
  refine { __ := inflation f F, map_smul' := ?_ }
  intro c x
  exact inflation_naturality f (ρ c) x

@[simp] theorem inflationLinearMap_apply
    (x : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1) :
    letI := pushforwardCohomologyModule f F ρ 1
    letI := cohomologyModule F ρ 1
    inflationLinearMap f F ρ x = inflation f F x := rfl

/-- The original edge map, linear for the actual derived scalar action. -/
def edgeLinearMap :
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    CategoryTheory.Sheaf.H.{0} F 1 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 := by
  letI := cohomologyModule F ρ 1
  letI := higherCohomologyModule f F ρ 1 0
  refine { __ := edge f F, map_smul' := ?_ }
  intro c x
  exact edge_naturality f (ρ c) x

@[simp] theorem edgeLinearMap_apply (x : CategoryTheory.Sheaf.H.{0} F 1) :
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    edgeLinearMap f F ρ x = edge f F x := rfl

/-- The original transgression, linear for the native scalar actions. -/
def transgressionLinearMap :
    letI := higherCohomologyModule f F ρ 1 0
    letI := pushforwardCohomologyModule f F ρ 2
    CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 →ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 2 := by
  letI := higherCohomologyModule f F ρ 1 0
  letI := pushforwardCohomologyModule f F ρ 2
  refine { __ := transgression f F, map_smul' := ?_ }
  intro c x
  exact transgression_naturality f (ρ c) x

@[simp] theorem transgressionLinearMap_apply
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0) :
    letI := higherCohomologyModule f F ρ 1 0
    letI := pushforwardCohomologyModule f F ρ 2
    transgressionLinearMap f F ρ x = transgression f F x := rfl

/-- The same unconditional exactness, now for the complex-linear maps. -/
theorem linear_lowDegree_exact :
    letI := pushforwardCohomologyModule f F ρ 1
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    letI := pushforwardCohomologyModule f F ρ 2
    Function.Injective (inflationLinearMap f F ρ) ∧
      Function.Exact (inflationLinearMap f F ρ) (edgeLinearMap f F ρ) ∧
        Function.Exact (edgeLinearMap f F ρ) (transgressionLinearMap f F ρ) :=
  lowDegree_exact f F

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars
