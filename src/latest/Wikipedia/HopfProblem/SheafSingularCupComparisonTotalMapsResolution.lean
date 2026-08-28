import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsFirst
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalMapsLast
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalSheafExact
import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowExact

/-!
# Actual maps of the genuine partial resolutions into the total resolution

Both maps induce the identity on the original complex constant sheaf.
All their components are the actual first-column or last-row maps,
with the previously proved original differential squares.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps

open SheafCupProduct CuspNormalization

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- The genuine constant-sheaf Godement resolution maps into the first total column. -/
def first : (GodementExact.partialResolution (SheafConstants.complexSheaf X)).Hom
    (TotalSheaf.partialResolution X hLC) where
  augmentation := 𝟙 (SheafConstants.complexAdditiveSheaf X)
  τ₀ := first0 X
  τ₁ := first1 X
  τ₂ := first2 X
  τ₃ := first3 X
  commι := (Category.id_comp _).trans
    (GodementExact.augmentation_naturality (RingCochains.augmentation X))
  comm₀ := first_comm0 X
  comm₁ := first_comm1 X
  comm₂ := first_comm2 X

/-- The genuine ring-valued singular-cochain resolution maps into the last total row. -/
def last : (ResolutionRow.rowPartialResolution X hLC).Hom
    (TotalSheaf.partialResolution X hLC) where
  augmentation := 𝟙 (SheafConstants.complexAdditiveSheaf X)
  τ₀ := last0 X
  τ₁ := last1 X
  τ₂ := last2 X
  τ₃ := last3 X
  commι := Category.id_comp _
  comm₀ := last_comm0 X
  comm₁ := last_comm1 X
  comm₂ := last_comm2 X

@[simp] theorem first_augmentation :
    (first X hLC).augmentation = 𝟙 (SheafConstants.complexAdditiveSheaf X) := rfl

@[simp] theorem last_augmentation :
    (last X hLC).augmentation = 𝟙 (SheafConstants.complexAdditiveSheaf X) := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.TotalMaps
