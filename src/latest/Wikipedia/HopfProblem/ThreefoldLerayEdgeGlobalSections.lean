import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# Native degree-zero cohomology and actual scalar global sections

For an abelian sheaf with a complex scalar action, global sections are
its literal section group on the top open set. The module on that
group evaluates the original scalar sheaf endomorphisms there.
Mathlib's native `Sheaf.H.equiv₀` is linear for this action and for the
sheaf-induced action on its genuine Ext-defined degree-zero cohomology.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge.GlobalSections

open CuspNormalization.SheafCohomology
open CuspNormalization.SheafCohomologyResolution (globalSectionsFunctor)

variable {X : TopCat.{0}} (F : TopCat.Sheaf AddCommGrpCat.{0} X)
  (ρ : ℂ →+* End F)

/-- Literal sections of the original sheaf on the actual top open set. -/
abbrev sections : Type := F.obj.obj (op ⊤)

/-- The actual scalar endomorphisms evaluated on top-open sections. -/
def sectionsScalarEnd : ℂ →+* End ((globalSectionsFunctor X).obj F) :=
  (mapEndRingHom (globalSectionsFunctor X) F).comp ρ

@[simp] theorem sectionsScalarEnd_apply (c : ℂ) (s : sections F) :
    (sectionsScalarEnd F ρ c).asHom s = (ρ c).hom.app (op ⊤) s := rfl

/-- Scalar multiplication is defined by the original scalar maps on
the top section group, not by transport from a cohomology comparison. -/
@[instance_reducible] def sectionsModule : Module ℂ (sections F) :=
  moduleOfScalarEnd ((globalSectionsFunctor X).obj F) (sectionsScalarEnd F ρ)

/-- The actual section scalar action is literal evaluation of the
original sheaf endomorphism on the top open set. -/
theorem sectionsModule_smul (c : ℂ) (s : sections F) :
    letI := sectionsModule F ρ
    c • s = (ρ c).hom.app (op ⊤) s := rfl

/-- The original native degree-zero comparison, now complex linear for
the two scalar actions induced by the original sheaf endomorphisms. -/
def cohomologyZeroLinearEquiv :
    letI := cohomologyModule F ρ 0
    letI := sectionsModule F ρ
    CategoryTheory.Sheaf.H.{0} F 0 ≃ₗ[ℂ] sections F := by
  letI := cohomologyModule F ρ 0
  letI := sectionsModule F ρ
  refine
    { __ := CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens X) from isTerminalTop)
      map_smul' := ?_ }
  intro c x
  exact (CategoryTheory.Sheaf.H.equiv₀_naturality
    (hT := (show IsTerminal (⊤ : Opens X) from isTerminalTop)) (ρ c) x).symm

/-- The linear adapter retains the exact original native comparison. -/
@[simp] theorem cohomologyZeroLinearEquiv_apply (x : CategoryTheory.Sheaf.H.{0} F 0) :
    letI := cohomologyModule F ρ 0
    letI := sectionsModule F ρ
    cohomologyZeroLinearEquiv F ρ x = CategoryTheory.Sheaf.H.equiv₀ F
      (show IsTerminal (⊤ : Opens X) from isTerminalTop) x := rfl

/-- The inverse also retains the exact original native degree-zero map. -/
@[simp] theorem cohomologyZeroLinearEquiv_symm_apply (s : sections F) :
    letI := cohomologyModule F ρ 0
    letI := sectionsModule F ρ
    (cohomologyZeroLinearEquiv F ρ).symm s =
      (CategoryTheory.Sheaf.H.equiv₀ F
        (show IsTerminal (⊤ : Opens X) from isTerminalTop)).symm s := rfl

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge.GlobalSections
