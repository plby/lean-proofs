import Mathlib.MeasureTheory.Measure.Haar.OfBasis

attribute [local instance] Classical.propDecidable

noncomputable def Erdos206.EgyptianFractions.EventuallyGreedy :
    Real → Prop
  := by
  sorry

theorem Erdos206.EgyptianFractions.erdos_206 :
    @Eq.{1} ENNReal
      (@DFunLike.coe.{1, 1, 1}
        (@MeasureTheory.Measure.{0} Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (Set.{0} Real) (fun (x : Set.{0} Real) ↦ ENNReal)
        (@MeasureTheory.Measure.instFunLike.{0} Real
          (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
        (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
        (@setOf.{0} Real fun (x : Real) ↦ Erdos206.EgyptianFractions.EventuallyGreedy x))
      (@OfNat.ofNat.{0} ENNReal (nat_lit 0) (@Zero.toOfNat0.{0} ENNReal ENNReal.instZero))
  := by
  sorry
