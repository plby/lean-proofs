import StackExchange.Puzzling139335.N4OuterPairMiddle
import StackExchange.Puzzling139335.N4HalfLeg
import StackExchange.Puzzling139335.N4OuterPair.SourceExtraction
import StackExchange.Puzzling139335.N4OuterPair.EqualNormals

/-!
# The reflected outer-pair configuration is impossible

Both actual outer side contacts have strict height below one half. The
remaining full side gaps therefore belong to distinct middle pieces and
determine their actual supported-source placements. Their common interface
is nontrivial by the Jordan-remainder theorem. Unequal source normals force
overlap of interiors; equal normals contradict the actual axial obstruction.
-/

open Set

namespace Puzzling139335.N4OuterPair.Configuration

/-- The last four-incidence configuration cannot protect the square center.
All contact, source-placement, and interface properties are derived here
from the actual dissection and its reflected outer pair. -/
theorem not_protectedCenter {d : SquareDissection} (h : Configuration d) :
    ¬ d.HasProtectedCenter := by
  intro hc
  obtain ⟨a, b, ha, hb, hleft, hright, _, _⟩ := h.exists_side_contact_heights_strict hc
  obtain ⟨iR, iL, howners, g, rev, σ, hsource, _, _, hφaxis, hψaxis, hR, hL⟩ :=
    h.exists_source_of_strict_contact_heights hc ha.1 ha.2 hb.1 hb.2 hleft hright
  have hij : iR ≠ iL := by
    rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hcommon : (d.piece iR ∩ d.piece iL).Nontrivial := by
    rcases howners with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h.middle_inter_nontrivial_of_protected hc
    · simpa only [inter_comm] using h.middle_inter_nontrivial_of_protected hc
  exact h.source_normals_ne hc howners g rev σ hsource hR hL
    (normal_angles_eq_of_actual_interface d hij hsource hφaxis hψaxis hR hL hcommon)

end Puzzling139335.N4OuterPair.Configuration
