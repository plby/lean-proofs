import Wikipedia.HopfProblem.SheafHigherDirectImageBasic
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Wikipedia.HopfProblem.SheafLerayLowDegreesScalarsDerivedAdditive

/-!
# The actual scalar actions on the terms of the Leray sequence

A complex scalar action on an abelian sheaf induces scalar actions on
its genuine pushforward and its genuine right-derived pushforwards.
The resulting modules on sheaf cohomology are the ones obtained by
applying the native cohomology functor to these actual endomorphisms.
No module is introduced by transporting a dimension calculation.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars

open SheafHigherDirectImage
open CuspNormalization.SheafCohomology

variable {X Y : TopCat.{0}} (f : X ⟶ Y) (F : AbelianSheaf X)
  (ρ : ℂ →+* End F)

/-- The scalar action obtained by the actual sheaf pushforward. -/
def pushforwardScalarEnd : ℂ →+* End ((pushforward f).obj F) :=
  (mapEndRingHom (pushforward f) F).comp ρ

@[simp] theorem pushforwardScalarEnd_apply (c : ℂ) :
    pushforwardScalarEnd f F ρ c = (pushforward f).map (ρ c) := rfl

/-- The scalar action obtained by the genuine right-derived functor. -/
def higherScalarEnd (q : ℕ) : ℂ →+* End (sheaf f F q) :=
  (mapEndRingHom (functor f q) F).comp ρ

@[simp] theorem higherScalarEnd_apply (q : ℕ) (c : ℂ) :
    higherScalarEnd f F ρ q c = (functor f q).map (ρ c) := rfl

/-- The module on genuine cohomology of the ordinary direct image. -/
@[instance_reducible] def pushforwardCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :=
  cohomologyModule ((pushforward f).obj F) (pushforwardScalarEnd f F ρ) n

/-- Scalars on pushforward cohomology are the original scalar maps
after the native pushforward and native cohomology functors. -/
theorem pushforwardCohomologyModule_smul (n : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} ((pushforward f).obj F) n) :
    letI := pushforwardCohomologyModule f F ρ n
    c • x = CategoryTheory.Sheaf.H.map ((pushforward f).map (ρ c)) n x := rfl

/-- The module on genuine cohomology of a genuine higher direct image. -/
@[instance_reducible] def higherCohomologyModule (q n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} (sheaf f F q) n) :=
  cohomologyModule (sheaf f F q) (higherScalarEnd f F ρ q) n

/-- Scalars on higher-direct-image cohomology are obtained by the
native right-derived and cohomology functors, in that order. -/
theorem higherCohomologyModule_smul (q n : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} (sheaf f F q) n) :
    letI := higherCohomologyModule f F ρ q n
    c • x = CategoryTheory.Sheaf.H.map ((functor f q).map (ρ c)) n x := rfl

end Wikipedia.HopfProblem.SheafLerayLowDegrees.Scalars
