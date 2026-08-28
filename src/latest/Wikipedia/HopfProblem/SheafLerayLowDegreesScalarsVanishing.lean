import Wikipedia.HopfProblem.SheafLerayLowDegreesScalarsMaps
import Wikipedia.HopfProblem.SheafLerayLowDegreesVanishing

/-!
# The complex-linear Leray edge equivalence after actual vanishing

When the two outer native cohomology groups vanish, the genuine edge
map is a complex-linear equivalence. Its scalar structures come from
the original sheaf scalar endomorphisms, and its underlying additive
equivalence is precisely the one obtained from the actual exact sequence.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars

open SheafHigherDirectImage
open CuspNormalization.SheafCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)
  (ρ : ℂ →+* End F)
  [Subsingleton (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 1)]
  [Subsingleton (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) 2)]

/-- The actual Leray edge map as a complex-linear equivalence, under
the two stated vanishings of genuine cohomology groups. -/
def edgeLinearEquivOfVanishing :
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    CategoryTheory.Sheaf.H.{0} F 1 ≃ₗ[ℂ]
      CategoryTheory.Sheaf.H.{0} (sheaf f F 1) 0 := by
  letI := cohomologyModule F ρ 1
  letI := higherCohomologyModule f F ρ 1 0
  refine { __ := edgeEquivOfVanishing f F, map_smul' := ?_ }
  intro c x
  exact edge_naturality f (ρ c) x

@[simp] theorem edgeLinearEquivOfVanishing_apply
    (x : CategoryTheory.Sheaf.H.{0} F 1) :
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    edgeLinearEquivOfVanishing f F ρ x = edge f F x := rfl

/-- No new choice of additive equivalence is made by the linear adapter. -/
@[simp] theorem edgeLinearEquivOfVanishing_toAddEquiv :
    letI := cohomologyModule F ρ 1
    letI := higherCohomologyModule f F ρ 1 0
    (edgeLinearEquivOfVanishing f F ρ).toAddEquiv = edgeEquivOfVanishing f F := rfl

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars
