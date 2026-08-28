import Wikipedia.HopfProblem.ConstantSheafSingularComparisonResolution

/-!
# The original complex-coefficient singular resolution for the exponential comparison

This is the actual singular-cochain sheaf resolution, truncated at its
degree-two cycles. Its intermediate kernel is the target of the descended
logarithmic differential. No compactness or cohomology vanishing is needed
to construct this resolution or its two short exact sequences.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.DLog

open ConstantSheafSingularComparison CuspNormalization.SheafCohomologyResolution

variable (X : TopCat.{0}) (hLC : LocallyContractibleSpace X)

/-- The genuine constant-complex singular-cochain resolution, with its
original degree-two cycle kernel as the last term. -/
abbrev resolution : AugmentedResolution (TopCat.Sheaf AddCommGrpCat.{0} X) :=
  (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).truncation

/-- Including the first kernel restores the original degree-zero singular
cochain differential. -/
@[reassoc] theorem resolution_toK_ι :
    (resolution X hLC).toK ≫ kernel.ι (resolution X hLC).complex.g =
      sheafDifferential X (AddCommGrpCat.of ℂ) 0 1 :=
  (resolution X hLC).toK_ι

/-- Including the degree-two cycles restores the original degree-one
singular cochain differential. -/
@[reassoc] theorem resolution_g_ι :
    (resolution X hLC).complex.g ≫
        kernel.ι (sheafDifferential X (AddCommGrpCat.of ℂ) 2 3) =
      sheafDifferential X (AddCommGrpCat.of ℂ) 1 2 :=
  (singularSheafResolution X (AddCommGrpCat.of ℂ) hLC).toCycles₂_ι

end Wikipedia.HopfProblem.ExponentialChernComparison.DLog
