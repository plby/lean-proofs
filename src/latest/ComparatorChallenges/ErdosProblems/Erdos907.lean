import Mathlib.Topology.MetricSpace.Pseudo.Defs

attribute [local instance] Classical.propDecidable

noncomputable def Erdos907.IsAdditiveFn :
    (Real → Real) → Prop
  := by
  sorry

theorem Erdos907.erdos907 :
    ∀ (f : Real → Real),
      (∀ (h : Real),
          @LT.lt.{0} Real Real.instLT
              (@OfNat.ofNat.{0} Real (nat_lit 0) (@Zero.toOfNat0.{0} Real Real.instZero)) h →
            @Continuous.{0, 0} Real Real
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              (@UniformSpace.toTopologicalSpace.{0} Real
                (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
              fun (x : Real) ↦
              @HSub.hSub.{0, 0, 0} Real Real Real (@instHSub.{0} Real Real.instSub)
                (f (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) x h)) (f x)) →
        @Exists.{1} (Real → Real) fun (g : Real → Real) ↦
          @Exists.{1} (Real → Real) fun (H : Real → Real) ↦
            And
              (@Continuous.{0, 0} Real Real
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                (@UniformSpace.toTopologicalSpace.{0} Real
                  (@PseudoMetricSpace.toUniformSpace.{0} Real Real.pseudoMetricSpace))
                g)
              (And (Erdos907.IsAdditiveFn H)
                (∀ (x : Real),
                  @Eq.{1} Real (f x)
                    (@HAdd.hAdd.{0, 0, 0} Real Real Real (@instHAdd.{0} Real Real.instAdd) (g x)
                      (H x))))
  := by
  sorry
