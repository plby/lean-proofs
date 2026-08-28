import Wikipedia.NoExoticSixSphere.RelativeModTwoEvaluationReduction
import Wikipedia.NoExoticSixSphere.ModTwoLocalClass
import Wikipedia.NoExoticSixSphere.CyclicModTwoEvaluation
import Wikipedia.NoExoticSixSphere.SupportedModTwoCohomology

/-!
# Original point-supported cohomology and unit local evaluation

The proved integral local homology marking and actual universal-coefficient
evaluation compute singleton-supported top cohomology. A nonzero class
evaluates to one on the actual primitive. The same is true on every
integral class whose native mod-two reduction is the constructed local
fundamental class, using the original coefficient-reduction kernel.
-/

noncomputable section

namespace NoExoticSixSphere.PointSupportedCohomology

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]
  {M : Type} [TopologicalSpace M] [T1Space M] [ChartedSpace E M]

/-- Actual local cohomology evaluation on the original primitive class in the original chart. -/
def marking (x : M) : SupportedModTwoCohomology.Cohomology ({x} : Set M) (n + 3) ≃ₗ[ℤ]
    ZMod 2 := by
  let := ModTwoLocalClass.preceding_subsingleton n (chartAt E x) x (mem_chart_source E x)
  exact (RelativeModTwoCochains.evaluationSuccEquiv ({x}ᶜ : Set M) (n + 2)).trans
    (ModTwoCohomologyEvaluation.cyclicFunctionalEquiv
      (RelativeSingularHomology.chartLocalTopEquiv (n + 1) (chartAt E x) x (mem_chart_source E x)))

theorem marking_apply (x : M) (a : SupportedModTwoCohomology.Cohomology ({x} : Set M) (n + 3)) :
    marking (E := E) n x a = RelativeModTwoCochains.evaluation ({x}ᶜ : Set M) (n + 3) a
      (RelativeSingularHomology.chartLocalTopClass (n + 1) (chartAt E x) x
        (mem_chart_source E x)) := rfl

/-- The actual singleton-supported top group has a unique nonzero marking value. -/
theorem marking_eq_one_of_ne_zero (x : M)
    (a : SupportedModTwoCohomology.Cohomology ({x} : Set M) (n + 3)) (ha : a ≠ 0) :
    marking (E := E) n x a = 1 := by
  have hn : marking (E := E) n x a ≠ 0 := by
    intro he
    exact ha ((marking (E := E) n x).injective (he.trans (marking (E := E) n x).map_zero.symm))
  rcases (show ∀ z : ZMod 2, z = 0 ∨ z = 1 from by decide)
    (marking (E := E) n x a) with h | h
  · exact (hn h).elim
  · exact h

/-- Nonzero local cohomology evaluates to one on the original local fundamental reduction. -/
theorem evaluation_eq_one_of_reduction_eq_localClass (x : M)
    (a : SupportedModTwoCohomology.Cohomology ({x} : Set M) (n + 3)) (ha : a ≠ 0)
    (c : RelativeSingularHomology.LocalHomology x (n + 3))
    (hc : RelativeCoefficients.reductionMap 2 ({x}ᶜ : Set M) (n + 3) c =
      ModTwoLocalClass.manifoldClass (E := E) n x) :
    RelativeModTwoCochains.evaluation ({x}ᶜ : Set M) (n + 3) a c = 1 :=
  (RelativeModTwoCochains.evaluation_eq_of_reduction_eq ({x}ᶜ : Set M) (n + 3) a c
    (RelativeSingularHomology.chartLocalTopClass (n + 1) (chartAt E x) x
      (mem_chart_source E x)) hc).trans
        ((marking_apply (E := E) n x a).symm.trans (marking_eq_one_of_ne_zero (E := E) n x a ha))

end NoExoticSixSphere.PointSupportedCohomology
