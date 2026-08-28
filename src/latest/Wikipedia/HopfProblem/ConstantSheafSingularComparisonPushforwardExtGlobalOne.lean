import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTruncation

/-!
# The actual degree-one global comparison commutes with pushforward
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward
open LowExt

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : CochainResolution (AbelianSheaf X))

/-- The native kernel comparison becomes the same actual inclusion
of global cycles into the original full cochain complex. -/
theorem globalTruncation_inclusion :
    (pushforwardTruncationMap f hf hfinite R).globalMap ≫
        (pushforwardResolution f hf hfinite R).globalShortInclusion =
      R.globalShortInclusion := by
  apply ShortComplex.hom_ext
  · exact Category.id_comp _
  · exact Category.id_comp _
  · change (globalSectionsFunctor Y).map (kernelComparison (R.K.d 2 3) (pushforward f)) ≫
        (globalSectionsFunctor Y).map (kernel.ι ((pushforward f).map (R.K.d 2 3))) =
      (globalSectionsFunctor Y).map ((pushforward f).map (kernel.ι (R.K.d 2 3)))
    exact ((globalSectionsFunctor Y).map_comp _ _).symm.trans
      (congrArg (globalSectionsFunctor Y).map
        (kernelComparison_comp_ι (R.K.d 2 3) (pushforward f)))

/-- The original degree-one full-complex homology comparison
commutes with the actual pushed-kernel map. -/
theorem globalFirstHomology_truncation :
    ShortComplex.homologyMap (pushforwardTruncationMap f hf hfinite R).globalMap ≫
        (pushforwardResolution f hf hfinite R).globalFirstHomologyIso.hom =
      R.globalFirstHomologyIso.hom := by
  let e := R.globalCochainComplex.isoSc' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))
  have h : ShortComplex.homologyMap (pushforwardTruncationMap f hf hfinite R).globalMap ≫
      ShortComplex.homologyMap (pushforwardResolution f hf hfinite R).globalShortInclusion =
    ShortComplex.homologyMap R.globalShortInclusion :=
    (ShortComplex.homologyMap_comp
      (pushforwardTruncationMap f hf hfinite R).globalMap
      (pushforwardResolution f hf hfinite R).globalShortInclusion).symm.trans
        (congrArg (fun k : R.truncation.globalComplex ⟶
            R.globalCochainComplex.sc' 0 1 2 => ShortComplex.homologyMap k)
          (globalTruncation_inclusion f hf hfinite R))
  change ShortComplex.homologyMap (pushforwardTruncationMap f hf hfinite R).globalMap ≫
      (ShortComplex.homologyMap (pushforwardResolution f hf hfinite R).globalShortInclusion ≫
        ShortComplex.homologyMap e.inv) =
    ShortComplex.homologyMap R.globalShortInclusion ≫ ShortComplex.homologyMap e.inv
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun k => k ≫ ShortComplex.homologyMap e.inv) h)

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
