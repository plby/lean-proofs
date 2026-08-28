import Wikipedia.HopfProblem.ExponentialChernComparisonLogarithmBridgeConnecting
import Wikipedia.HopfProblem.ExponentialChernComparisonLogarithmBridgeCohomology
import Wikipedia.HopfProblem.ExponentialChernComparisonGlobalCycle
import Wikipedia.HopfProblem.HolomorphicPicardChernBasic

/-!
# Original exponential classes represented by explicit local logarithmic cochains

This is a degree-one-to-degree-two comparison for the original
holomorphic exponential sequence. The hypotheses give actual
holomorphic logarithms on pairwise overlaps and actual local singular
one-cochains, whose differentials and later-minus-earlier differences
are the stated literal cochains. The conclusion is equality under the
canonical constant-sheaf/singular-cohomology comparison with the class
of the prescribed original closed singular two-cochain.

No equality of cohomology classes, Chern-class comparison, polarization,
or numerical cohomology model is among the hypotheses.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge

open ConstantSheafSingularComparison HolomorphicFunctionSheaf.SphereH1
open HolomorphicExponentialSheaf CuspNormalization.SheafCohomologyResolution

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    [CompactSpace M] [T2Space M] (hLC : LocallyContractibleSpace M)
    {ι : Type} {U : ι → Opens M}
    (c : CechOneCocycle (unitsSheaf I M) U)
    (hU : ∀ x : M, ∃ i : ι, x ∈ U i)
    (logs : ∀ i j : ι, HolomorphicFunctionSheaf.Section I M (U i ⊓ U j))
    (hlogs : ∀ i j : ι,
      (exponential I M).hom.app (op (U i ⊓ U j)) (logs i j) = c.value i j)
    (ζ : Cochains M (AddCommGrpCat.of ℂ) 2)
    (hζ : (singularCochainComplex M (AddCommGrpCat.of ℂ)).d 2 3 ζ = 0)
    (t : ∀ i : ι, Cochains (U i) (AddCommGrpCat.of ℂ) 1)
    (ht : ∀ i : ι, (singularCochainComplex (U i) (AddCommGrpCat.of ℂ)).d 1 2 (t i) =
      restrictGlobalCochain (X := TopCat.of M) (AddCommGrpCat.of ℂ) 2 ζ (U i))
    (hdiff : ∀ i j : ι,
      (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_right : U i ⊓ U j ≤ U j)).op (t j) -
        (cochainPresheaf (TopCat.of M) (AddCommGrpCat.of ℂ) 1).map
          (homOfLE (inf_le_left : U i ⊓ U j ≤ U i)).op (t i) =
      (singularCochainComplex ↥(U i ⊓ U j) (AddCommGrpCat.of ℂ)).d 0 1
        (CochainZero.evaluateSections I M (U i ⊓ U j) (logs i j)))

include logs hlogs t ht hdiff in
/-- The actual exponential connecting class, after the original integer
period coefficient map and the canonical sheaf/singular comparison,
is the native class of the prescribed closed singular two-cochain. -/
theorem constantSheafH2Iso_map_connecting_classOf :
    (constantSheafH2Iso (TopCat.of M) (AddCommGrpCat.of ℂ) hLC).hom
        (CategoryTheory.Sheaf.H.map (CochainZero.integerCoefficientMap (TopCat.of M)) 2
          (connecting (unitSheaf (TopCat.of M)) (exponentialComplex_shortExact I M) 1
            (HolomorphicPicard.CechExtension.classOf c hU))) =
      SheafHigherDirectImage.ExtBridge.cycleClass
        (singularCochainComplex M (AddCommGrpCat.of ℂ)) 2 ζ
        (GlobalCycle.closed_sc (singularCochainComplex M (AddCommGrpCat.of ℂ)) ζ hζ) := by
  let σ := GlobalCycle.sectionOfCochain (TopCat.of M) hLC ζ hζ
  have hb := map_connecting_classOf_eq_globalConnectingTwo I M hLC c hU logs hlogs ζ σ
    (GlobalCycle.sectionOfCochain_inclusion (TopCat.of M) hLC ζ hζ) t ht hdiff
  let := globalCochainComparison_homology_isIso (TopCat.of M) (AddCommGrpCat.of ℂ) 1
  apply (AddCommGrpCat.mono_iff_injective
    (HomologicalComplex.homologyMap
      (globalCochainComparison (TopCat.of M) (AddCommGrpCat.of ℂ)) 2)).mp inferInstance
  exact (congrArg (fun ξ =>
    HomologicalComplex.homologyMap
      (globalCochainComparison (TopCat.of M) (AddCommGrpCat.of ℂ)) 2
        ((constantSheafH2Iso (TopCat.of M) (AddCommGrpCat.of ℂ) hLC).hom ξ)) hb).trans
    ((constantSheafH2Iso_globalConnectingTwo (TopCat.of M) hLC σ).trans
      (GlobalCycle.sectionOfCochain_class (TopCat.of M) hLC ζ hζ))

include logs hlogs t ht hdiff in
/-- The same formula using the already defined original holomorphic
first-Chern connecting homomorphism, without changing its definition. -/
theorem constantSheafH2Iso_exponentialConnecting :
    (constantSheafH2Iso (TopCat.of M) (AddCommGrpCat.of ℂ) hLC).hom
        (CategoryTheory.Sheaf.H.map (CochainZero.integerCoefficientMap (TopCat.of M)) 2
          (HolomorphicPicard.Chern.exponentialConnecting I M 1
            (HolomorphicPicard.CechExtension.classOf c hU))) =
      SheafHigherDirectImage.ExtBridge.cycleClass
        (singularCochainComplex M (AddCommGrpCat.of ℂ)) 2 ζ
        (GlobalCycle.closed_sc (singularCochainComplex M (AddCommGrpCat.of ℂ)) ζ hζ) :=
  constantSheafH2Iso_map_connecting_classOf I M hLC c hU logs hlogs ζ hζ t ht hdiff

end Wikipedia.HopfProblem.ExponentialChernComparison.LogarithmBridge
