import StackExchange.Puzzling139335.RemainingCases
import StackExchange.Puzzling139335.N5.Reduction
import StackExchange.Puzzling139335.N5.Preparation

/-!
# From an arbitrary counterexample to the final actual configuration

All corner-incidence alternatives and geometric normalizations are
discharged. A protected-center dissection would produce an actual
five-incidence configuration with the placements and contact intervals
needed by the final support-direction calculation.
-/

namespace Puzzling139335.SquareDissection

theorem exists_prepared_of_protected_center (d : SquareDissection)
    (hc : d.HasProtectedCenter) :
    ∃ D : SquareDissection, Nonempty (N5.Prepared D) := by
  obtain ⟨D, hD, hcfg⟩ := N5.exists_normalized_of_five d hc
    (d.remaining_incidence_case_five hc) (d.usedCornerTypes_card_le_three hc)
  exact hcfg.exists_prepared hD

end Puzzling139335.SquareDissection
