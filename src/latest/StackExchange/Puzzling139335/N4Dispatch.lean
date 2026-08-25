import StackExchange.Puzzling139335.N4Dispatch.OneCorner
import StackExchange.Puzzling139335.N4Dispatch.TwoOneOne
import StackExchange.Puzzling139335.N4Dispatch.DoublePair
import StackExchange.Puzzling139335.N4TwoOneOne

/-!
# The complete geometric dispatch of four square-corner incidences

Actual counting yields the three degree patterns `1111`, `2110`, and
`2200`. The first two are excluded by their geometric theorems. In the
last pattern, the actual central half-turn alternative is impossible and
the two corner-owning pieces normalize to the reflected outer pair.

No geometric classification is assumed: every alternative and every field
of the resulting outer-pair configuration is proved from the dissection.
-/

namespace Puzzling139335.N4Dispatch

/-- A putative four-incidence counterexample has a normalized actual
reflected outer-pair configuration. -/
theorem exists_outerPair_of_four_incidences (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4) :
    ∃ D : SquareDissection, D.HasProtectedCenter ∧ N4OuterPair.Configuration D := by
  rcases corner_pattern_cases_selected d hc hN with hone | hsingle | hdouble
  · exact (OneCorner.not_hasProtectedCenter_of_each_tile_one d hone hc).elim
  · obtain ⟨σ, h0, h1, h2, h3⟩ := hsingle
    obtain ⟨D, hD, hcfg⟩ := TwoOneOne.exists_configuration_of_permuted_degree2110
      d hc σ h0 h1 h2 h3
    exact (hcfg.not_protectedCenter hD).elim
  · exact DoublePair.exists_configuration_of_selected_double_pair d hc hN
      (fun _ _ hij hpair => d.not_hasProtectedCenter_of_halfTurn_pair hij hpair hc) hdouble

end Puzzling139335.N4Dispatch
