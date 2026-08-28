import Wikipedia.HopfProblem.PeriodFamilyHigherDirectImageLocalBaseActionCohomology
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionActions
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionHolomorphicCohomologyNested

/-!
# Original local-base multipliers commute with nested holomorphic pullback

A base function is required only on the larger original base open.
On every open of the smaller full preimage, the actual coefficient
square is literal multiplication by the same original base value.
Native holomorphic cohomology pullback consequently respects these
coefficient maps in every degree. No global extension is used.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction

open PeriodFamilyHolomorphicCohomology
open PeriodFamilyHolomorphicCohomology.OpenClassRestriction

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- Genuine holomorphic pullback between the original full-preimage open submanifolds. -/
def preimageHolomorphicPullback (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (q : ℕ) :
    CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P W) q →+
      CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P U) q := by
  letI := P.totalChartedSpace
  exact HolomorphicCohomology.pullback IT IT
    (nestedInclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h))
    (nestedEmbedding (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h))
    (contMDiff_inclusion (I := IT) (Zero.basePreimage_mono P h)) q

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The actual all-open coefficient square for a function defined only
on the larger base open commutes by its literal pointwise values. -/
theorem preimageCoefficientMap_baseMultiply (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (g : Zero.BaseSection P W) :
    letI := P.totalChartedSpace
    let i := nestedInclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h)
    let hi := nestedEmbedding (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h)
    let φ := HolomorphicEmbedding.coefficientMap IT IT i hi
      (contMDiff_inclusion (I := IT) (Zero.basePreimage_mono P h))
    (Embedding.restriction i hi).map (OpenBaseAction.preimageMultiplyEnd P W g) ≫ φ =
      φ ≫ OpenBaseAction.preimageMultiplyEnd P U (Zero.baseRestriction P h g) := by
  let := P.totalChartedSpace
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext A
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  apply ContMDiffMap.ext
  intro x
  rfl

/-- Actual full-preimage holomorphic cohomology pullback respects the
coefficient multiplier and its literal base restriction, in every degree. -/
theorem preimageHolomorphicPullback_baseMultiply (P : HolomorphicPeriodMap V B)
    {U W : Opens B} (h : U ≤ W) (q : ℕ) (g : Zero.BaseSection P W)
    (x : CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P W) q) :
    preimageHolomorphicPullback P h q
        (CategoryTheory.Sheaf.H.map (OpenBaseAction.preimageMultiplyEnd P W g) q x) =
      CategoryTheory.Sheaf.H.map
        (OpenBaseAction.preimageMultiplyEnd P U (Zero.baseRestriction P h g)) q
        (preimageHolomorphicPullback P h q x) := by
  let := P.totalChartedSpace
  exact holomorphicPullback_map IT IT
    (nestedInclusion (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h))
    (nestedEmbedding (X := TopCat.of P.TotalSpace) (Zero.basePreimage_mono P h))
    (contMDiff_inclusion (I := IT) (Zero.basePreimage_mono P h))
    (OpenBaseAction.preimageMultiplyEnd P W g)
    (OpenBaseAction.preimageMultiplyEnd P U (Zero.baseRestriction P h g))
    (preimageCoefficientMap_baseMultiply P h g) q x

end Wikipedia.HopfProblem.PeriodFamilyHigherDirectImage.LocalBaseAction
