import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtGlobal
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPullbackExtComparison

/-!
# Canonical constant-sheaf Ext--singular naturality for finite closed maps

The native Ext maps are defined independently of singular cohomology.
The actual resolution and global-unit squares prove that the comparison
isomorphisms intertwine them with the original singular pullbacks.
This applies to the genuine normalization and actual closed inclusions.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt

variable {X Y : TopCat.{0}} [CompactSpace X] [T2Space X]
  [CompactSpace Y] [T2Space Y] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (A : AddCommGrpCat.{0})

/-- Genuine degree-one Ext pullback is the original singular pullback
under the canonical constant-sheaf comparison. -/
theorem h1_naturality (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    constantCohomologyPullback f hf hfinite A 1 ≫ (constantSheafH1Iso X A hX).hom =
      (constantSheafH1Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback A f.hom) 1 :=
  h1_naturality_of_global f A hX hY (constantCohomologyPullback f hf hfinite A 1)
    (h1_global_naturality f hf hfinite A hX hY)

/-- The same canonical naturality square in degree two, without an
assumed cohomological comparison or assumed acyclicity of pushforward. -/
theorem h2_naturality (hX : LocallyContractibleSpace X) (hY : LocallyContractibleSpace Y) :
    constantCohomologyPullback f hf hfinite A 2 ≫ (constantSheafH2Iso X A hX).hom =
      (constantSheafH2Iso Y A hY).hom ≫
        HomologicalComplex.homologyMap (singularPullback A f.hom) 2 :=
  h2_naturality_of_global f A hX hY (constantCohomologyPullback f hf hfinite A 2)
    (h2_global_naturality f hf hfinite A hX hY)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PullbackExt
