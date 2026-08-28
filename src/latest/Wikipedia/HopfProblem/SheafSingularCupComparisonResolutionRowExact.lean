import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionRowBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonResolution

/-!
# Exactness of the actual ring-valued singular-cochain row

Local contractibility proves exactness of the original additive singular
complex. The original, termwise sheaf isomorphisms transfer that exactness
to the literal alternating ring-coface row. The resulting partial
resolution retains the original constant ring sheaf and its augmentation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow

open CuspNormalization ConstantSheafSingularComparison SheafCupProductResolution
open RingCochains

variable (X : TopCat.{0})

/-- The original singular-cochain resolution with complex coefficients. -/
abbrev originalResolution (hLC : LocallyContractibleSpace X) :=
  singularSheafResolution X (AddCommGrpCat.of ℂ) hLC

/-- The actual row augmentation is monomorphic on every topological space. -/
theorem rowAugmentation_mono : Mono (rowAugmentation X) := by
  have he : Mono (SheafConstants.complexAdditiveSheafIso X).hom :=
    ⟨fun g h w => (Iso.cancel_iso_hom_right g h
      (SheafConstants.complexAdditiveSheafIso X)).mp w⟩
  have hc : Mono ((SheafConstants.complexAdditiveSheafIso X).hom ≫
      sheafAugmentation X (AddCommGrpCat.of ℂ)) :=
    mono_comp' he (LocalExact.sheafAugmentation_mono X (AddCommGrpCat.of ℂ))
  exact @mono_of_mono_fac _ _ _ _ _ _ _ _ hc (augmentation_additive X)

/-- Actual exactness at the original degree-zero ring-cochain sheaf. -/
theorem rowInitialComplex_exact (hLC : LocallyContractibleSpace X) :
    (rowInitialComplex X).Exact :=
  (ShortComplex.exact_iff_of_iso (rowInitialIso X)).mpr
    (originalResolution X hLC).initial_exact

/-- Actual exactness at the original degree-one ring-cochain sheaf. -/
theorem rowOneComplex_exact (hLC : LocallyContractibleSpace X) :
    (rowOneComplex X).Exact :=
  (ShortComplex.exact_iff_of_iso (rowOneIso X)).mpr
    (Resolution.ofCochain (originalResolution X hLC)).exact₁

/-- Actual exactness at the original degree-two ring-cochain sheaf. -/
theorem rowTwoComplex_exact (hLC : LocallyContractibleSpace X) :
    (rowTwoComplex X).Exact :=
  (ShortComplex.exact_iff_of_iso (rowTwoIso X)).mpr
    (Resolution.ofCochain (originalResolution X hLC)).exact₂

/-- The genuine first four terms of the ring-valued singular-cochain resolution. -/
def rowPartialResolution (hLC : LocallyContractibleSpace X) :
    PartialResolution (TopCat.Sheaf AddCommGrpCat.{0} X) where
  F := SheafConstants.complexAdditiveSheaf X
  I₀ := rowTerm X 0
  I₁ := rowTerm X 1
  I₂ := rowTerm X 2
  I₃ := rowTerm X 3
  ι := rowAugmentation X
  d₀ := d0 X
  d₁ := d1 X
  d₂ := d2 X
  ι_d₀ := rowAugmentation_d0 X
  d₀_d₁ := row_d0_d1 X
  d₁_d₂ := row_d1_d2 X
  exact₀ := rowInitialComplex_exact X hLC
  exact₁ := rowOneComplex_exact X hLC
  exact₂ := rowTwoComplex_exact X hLC
  mono_ι := rowAugmentation_mono X

/-- The actual original constant and cochain comparisons give a map of resolutions. -/
def rowToOriginal (hLC : LocallyContractibleSpace X) :
    (rowPartialResolution X hLC).Hom
      (Resolution.ofCochain (originalResolution X hLC)) where
  augmentation := (SheafConstants.complexAdditiveSheafIso X).hom
  τ₀ := (forgetSheafIso X 0).hom
  τ₁ := (forgetSheafIso X 1).hom
  τ₂ := (forgetSheafIso X 2).hom
  τ₃ := (forgetSheafIso X 3).hom
  commι := (augmentation_additive X).symm
  comm₀ := (d0_additive X).symm
  comm₁ := (d1_additive X).symm
  comm₂ := (d2_additive X).symm

@[simp] theorem rowToOriginal_augmentation (hLC : LocallyContractibleSpace X) :
    (rowToOriginal X hLC).augmentation =
      (SheafConstants.complexAdditiveSheafIso X).hom := rfl

@[simp] theorem rowToOriginal_oneMap (hLC : LocallyContractibleSpace X) :
    (rowToOriginal X hLC).oneMap = (rowOneIso X).hom := rfl

@[simp] theorem rowToOriginal_twoMap (hLC : LocallyContractibleSpace X) :
    (rowToOriginal X hLC).twoMap = (rowTwoIso X).hom := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.ResolutionRow
