import Wikipedia.HopfProblem.ExponentialChernComparisonLogarithmBridgeBasic
import Wikipedia.HopfProblem.ExponentialChernComparisonDLog

/-!
# Actual logarithms and local cochains compute the exponential boundary

Local one-cochains with the prescribed actual differential and overlap
differences are genuine lifts through the second sequence of the
constant-complex singular resolution. The original logarithmic
differential sends the original unit cocycle to their overlap cocycle.
Naturality of the actual connecting maps then computes the original
degree-one exponential boundary.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge

open ConstantSheafSingularComparison HolomorphicFunctionSheaf.SphereH1
open HolomorphicExponentialSheaf CuspNormalization.SheafCohomologyResolution

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (hLC : LocallyContractibleSpace M)
    {ι : Type} {U : ι → Opens M}

/-- An original logarithm and a literal overlap coboundary give exactly
the mapped unit-cocycle overlap in the original resolution. -/
theorem localSection_overlap (c : CechOneCocycle (unitsSheaf I M) U)
    (logs : ∀ i j : ι, HolomorphicFunctionSheaf.Section I M (U i ⊓ U j))
    (hlogs : ∀ i j : ι,
      (exponential I M).hom.app (op (U i ⊓ U j)) (logs i j) = c.value i j)
    (t : ∀ i : ι, Cochains (U i) (AddCommGrpCat.of ℂ) 1)
    (hdiff : ∀ i j : ι,
      (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (t j) -
        (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (t i) =
      (singularCochainComplex ↥(U i ⊓ U j) (AddCommGrpCat.of ℂ)).d 0 1
        (CochainZero.evaluateSections I M (U i ⊓ U j) (logs i j))) (i j : ι) :
    res (DLog.resolution (TopCat.of M) hLC).complex.X₂ inf_le_right
        (localSection (TopCat.of M) hLC (U j) (t j)) -
      res (DLog.resolution (TopCat.of M) hLC).complex.X₂ inf_le_left
        (localSection (TopCat.of M) hLC (U i) (t i)) =
      (DLog.resolution (TopCat.of M) hLC).second.f.hom.app (op (U i ⊓ U j))
        ((HolomorphicPicard.Cech.mapCocycle (DLog.complexMap I M hLC).τ₃ c).value i j) := by
  rw [localSection_restrict_sub, hdiff i j]
  change (cochainSheafUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 1).app (op (U i ⊓ U j))
      ((singularCochainComplex ↥(U i ⊓ U j) (AddCommGrpCat.of ℂ)).d 0 1
        (CochainZero.evaluateSections I M (U i ⊓ U j) (logs i j))) =
    (kernel.ι (DLog.resolution (TopCat.of M) hLC).complex.g).hom.app (op (U i ⊓ U j))
      ((DLog.dlog I M hLC).hom.app (op (U i ⊓ U j)) (c.value i j))
  rw [← hlogs i j]
  exact (DLog.dlog_exponential_app_ι I M hLC (U i ⊓ U j) (logs i j)).symm

/-- Explicit original logarithms and actual singular cochain lifts
compute the coefficient image of the genuine exponential connecting
class as the actual double connecting class of the original global
cycle section. -/
theorem map_connecting_classOf_eq_globalConnectingTwo
    (c : CechOneCocycle (unitsSheaf I M) U)
    (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
    (logs : ∀ i j : ι, HolomorphicFunctionSheaf.Section I M (U i ⊓ U j))
    (hlogs : ∀ i j : ι,
      (exponential I M).hom.app (op (U i ⊓ U j)) (logs i j) = c.value i j)
    (ζ : Cochains M (AddCommGrpCat.of ℂ) 2)
    (σ : Section (DLog.resolution (TopCat.of M) hLC).complex.X₃ ⊤)
    (hσ : (kernel.ι (sheafDifferential (TopCat.of M) (AddCommGrpCat.of ℂ) 2 3)).hom.app
        (op ⊤) σ = globalCochainUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 2 ζ)
    (t : ∀ i : ι, Cochains (U i) (AddCommGrpCat.of ℂ) 1)
    (ht : ∀ i : ι, (singularCochainComplex (U i) (AddCommGrpCat.of ℂ)).d 1 2 (t i) =
      restrictGlobalCochain (X := TopCat.of M) (AddCommGrpCat.of ℂ) 2 ζ (U i))
    (hdiff : ∀ i j : ι,
      (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (t j) -
        (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (t i) =
      (singularCochainComplex ↥(U i ⊓ U j) (AddCommGrpCat.of ℂ)).d 0 1
        (CochainZero.evaluateSections I M (U i ⊓ U j) (logs i j))) :
    CategoryTheory.Sheaf.H.map (CochainZero.integerCoefficientMap (TopCat.of M)) 2
        (connecting (unitSheaf (TopCat.of M)) (exponentialComplex_shortExact I M) 1
          (HolomorphicPicard.CechExtension.classOf c hU)) =
      (DLog.resolution (TopCat.of M) hLC).globalConnectingTwo σ := by
  exact ExponentialChernComparison.map_connecting_classOf_eq_globalConnectingTwo
    (exponentialComplex I M) (exponentialComplex_shortExact I M)
    (DLog.resolution (TopCat.of M) hLC) (DLog.complexMap I M hLC) c hU σ
    (fun i => localSection (TopCat.of M) hLC (U i) (t i))
    (fun i => localSection_lifts (TopCat.of M) hLC (U i) σ ζ hσ (t i) (ht i))
    (fun i j => localSection_overlap I M hLC c logs hlogs t hdiff i j)

end Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge
