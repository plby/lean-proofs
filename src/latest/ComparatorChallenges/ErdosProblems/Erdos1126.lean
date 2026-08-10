import Mathlib.MeasureTheory.Measure.Haar.OfBasis

attribute [local instance] Classical.propDecidable

theorem Erdos1126.erdos_1126 :
    ∀ (f : Real → Real),
      @Filter.Eventually.{0} (Prod.{0, 0} Real Real)
          (fun (p : Prod.{0, 0} Real Real) ↦
            @Eq.{1} Real
              (f
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                  (@Prod.fst.{0, 0} Real Real p) (@Prod.snd.{0, 0} Real Real p)))
              (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd)
                (f (@Prod.fst.{0, 0} Real Real p)) (f (@Prod.snd.{0, 0} Real Real p))))
          (@MeasureTheory.ae.{0, 0} (Prod.{0, 0} Real Real)
            (@MeasureTheory.Measure.{0} (Prod.{0, 0} Real Real)
              (@Prod.instMeasurableSpace.{0, 0} Real Real
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)))
            (@MeasureTheory.Measure.instFunLike.{0} (Prod.{0, 0} Real Real)
              (@Prod.instMeasurableSpace.{0, 0} Real Real
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)))
            (@MeasureTheory.Measure.instOuterMeasureClass.{0} (Prod.{0, 0} Real Real)
              (@Prod.instMeasurableSpace.{0, 0} Real Real
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
                (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)))
            (@MeasureTheory.Measure.prod.{0, 0} Real Real
              (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
              (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace)
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)
              (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace))) →
        @Exists.{1} (Real → Real) fun (h : Real → Real) ↦
          And
            (∀ (x y : Real),
              @Eq.{1} Real
                (h (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x y))
                (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (h x) (h y)))
            (@Filter.Eventually.{0} Real (fun (x : Real) ↦ @Eq.{1} Real (f x) (h x))
              (@MeasureTheory.ae.{0, 0} Real
                (@MeasureTheory.Measure.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (@MeasureTheory.Measure.instFunLike.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (@MeasureTheory.Measure.instOuterMeasureClass.{0} Real
                  (@MeasureTheory.MeasureSpace.toMeasurableSpace.{0} Real Real.measureSpace))
                (@MeasureTheory.MeasureSpace.volume.{0} Real Real.measureSpace)))
  := by
  sorry
