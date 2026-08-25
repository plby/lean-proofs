import StackExchange.Puzzling139335.N5.Reduction
import StackExchange.Puzzling139335.N5.Preparation
import StackExchange.Puzzling139335.N5.Final
import StackExchange.Puzzling139335.GeometricReduction

/-!
# Five square-corner incidences exclude a protected center

All finite incidence, intrinsic-type, local-corner, contact, and supporting
direction reductions are proved from the original Jordan-dissection
hypotheses.  Congruences of either orientation are included.
-/

namespace Puzzling139335.SquareDissection

/-- Five tile-corner incidences cannot occur in a square dissection having
a piece that contains an open neighborhood of its center. -/
theorem not_hasProtectedCenter_of_five (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 5) : ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨d', hc', hn⟩ := N5.exists_normalized_of_five d hc hN
    (d.usedCornerTypes_card_le_three hc)
  obtain ⟨d'', ⟨q⟩⟩ := hn.exists_prepared hc'
  exact q.impossible

theorem cornerIncidenceCount_ne_five (d : SquareDissection)
    (hc : d.HasProtectedCenter) : d.cornerIncidenceCount ≠ 5 :=
  fun hN => d.not_hasProtectedCenter_of_five hN hc

end Puzzling139335.SquareDissection
