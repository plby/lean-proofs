import Wikipedia.HopfProblem.HolomorphicDolbeaultThreeCohomologyAbstract
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars

/-!
# Linearity of the native connecting class for original scalar actions

The source module is an already specified module on the actual global
sections.  Its scalar multiplication is required to be literal evaluation of
the original sheaf scalar endomorphisms.  The target module is the existing
module induced by the original sheaf endomorphisms through genuine `Sheaf.H`.
No scalar action is transported through a quotient or a dimension formula.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract

open CuspNormalization.SheafCohomology

variable {X : TopCat.{0}}
variable {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
variable (ρ₁ : ℂ →+* End S.X₁) (ρ₂ : ℂ →+* End S.X₂) (ρ₃ : ℂ →+* End S.X₃)
variable (h₁ : ∀ c, ρ₁ c ≫ S.f = S.f ≫ ρ₂ c)
  (h₂ : ∀ c, ρ₂ c ≫ S.g = S.g ≫ ρ₃ c)

/-- The actual scalar endomorphisms form a morphism of the original short
complex precisely through their given commuting squares. -/
def scalarMorphism (c : ℂ) : S ⟶ S :=
  ShortComplex.homMk (ρ₁ c) (ρ₂ c) (ρ₃ c) (h₁ c) (h₂ c)

variable [Module ℂ (Sections S.X₃)]
variable (hρ₃ : ∀ (c : ℂ) (s : Sections S.X₃), sectionMap (ρ₃ c) s = c • s)

include h₁ h₂ hρ₃ in
/-- The genuine connecting class is complex-linear for the already existing
pointwise section action and the original cohomological scalar action. -/
theorem classMap_smul (hS : S.ShortExact) (c : ℂ) (s : Sections S.X₃) :
    letI := cohomologyModule S.X₁ ρ₁ 1
    classMap hS (c • s) = c • classMap hS s := by
  let := cohomologyModule S.X₁ ρ₁ 1
  change classMap hS (c • s) = CategoryTheory.Sheaf.H.map (ρ₁ c) 1 (classMap hS s)
  exact (congrArg (classMap hS) (hρ₃ c s).symm).trans
    (classMap_naturality hS hS (scalarMorphism ρ₁ ρ₂ ρ₃ h₁ h₂ c) s)

/-- The original positive connecting morphism as a linear map, without
changing either its forward map or the source module. -/
def classLinearMap (hS : S.ShortExact) :
    letI := cohomologyModule S.X₁ ρ₁ 1
    Sections S.X₃ →ₗ[ℂ] CategoryTheory.Sheaf.H.{0} S.X₁ 1 := by
  letI := cohomologyModule S.X₁ ρ₁ 1
  refine
    { __ := classMap hS
      map_smul' := ?_ }
  intro c s
  exact classMap_smul ρ₁ ρ₂ ρ₃ h₁ h₂ hρ₃ hS c s

@[simp] theorem classLinearMap_apply (hS : S.ShortExact) (s : Sections S.X₃) :
    letI := cohomologyModule S.X₁ ρ₁ 1
    classLinearMap ρ₁ ρ₂ ρ₃ h₁ h₂ hρ₃ hS s = classMap hS s := rfl

/-- Actual degree-one acyclicity of the middle sheaf makes the same native
linear map surjective. -/
theorem classLinearMap_surjective (hS : S.ShortExact)
    [Subsingleton (CategoryTheory.Sheaf.H.{0} S.X₂ 1)] :
    letI := cohomologyModule S.X₁ ρ₁ 1
    Function.Surjective (classLinearMap ρ₁ ρ₂ ρ₃ h₁ h₂ hρ₃ hS) := by
  let := cohomologyModule S.X₁ ρ₁ 1
  exact classMap_surjective hS

end Wikipedia.HopfProblem.HolomorphicDolbeaultThree.CohomologyAbstract
