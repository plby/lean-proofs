import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenMorse
import Wikipedia.HopfProblem.DegreeCollapseRegularTimeExcellentMorse

/-!
# The original collared half has an excellent native Morse presentation

The actual constructed presentation now has distinct native critical
values as well. It inherits the exact boundary germs, same-half identity,
and proved identity diffeomorphisms in the original native atlases.
Its critical set is finite by the genuine compact Morse theorem.
-/

noncomputable section

open Set
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare.ManifoldMorse

variable {B : Type} [TopologicalSpace B] (S : CollaredSevenState B)

structure ExcellentMorsePresentation extends S.MorsePresentation where
  distinct : InjOn function (criticalPoints (Vector 7) function)

theorem nonempty_excellentMorsePresentation : Nonempty S.ExcellentMorsePresentation := by
  obtain ⟨g, hg, hm, hinj, hgerm, hzero, hhalf, hpos, hreg⟩ :=
    RegularTimeMorse.exists_excellent_preserving_zero S.time_smooth S.time_regular
  exact ⟨
    { function := ⟨g, hg.continuous⟩
      smooth := hg
      morse := hm
      regular := hreg
      zero_iff := hzero
      nonnegative_iff := hhalf
      positive_iff := hpos
      boundary_germ := hgerm
      distinct := hinj }⟩

def excellentMorsePresentation : S.ExcellentMorsePresentation :=
  Classical.choice S.nonempty_excellentMorsePresentation

theorem ExcellentMorsePresentation.finite_criticalPoints (P : S.ExcellentMorsePresentation) :
    (criticalPoints (Vector 7) P.function).Finite :=
  Wikipedia.SmoothSixDPoincare.ManifoldMorse.finite_criticalPoints P.smooth P.morse

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState
