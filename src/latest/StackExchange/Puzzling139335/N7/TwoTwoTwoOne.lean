import StackExchange.Puzzling139335.N7.TwoTwoTwoOne.Shared
import StackExchange.Puzzling139335.N7.TwoTwoTwoOne.Single

/-!
# Excluding the seven-incidence `2221` corner multiplicities

Every configuration here is derived from the actual dissection.  The two
repeated pairs use distinct adjacent physical sides, and their shared
corner has equal intrinsic preimages after excluding actual quarter-turn
pairs.  The double-corner support theorem and the actual singleton-corner
count then exclude a protected center.  No polygonal or angle-certificate
assumption is used.
-/

namespace Puzzling139335.N7

namespace PairConfiguration

variable {d : SquareDissection}

/-- The actual repeated-pair configuration cannot have exactly one
uniquely owned square corner and a protected center. -/
theorem not_one_unique_corner (C : PairConfiguration d)
    (hc : d.HasProtectedCenter)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    False := by
  obtain ⟨j, hi, hk, htype⟩ := C.exists_shared_repeated_occurrence hc hU
  exact C.no_same_type_repeated_shared_corner hc hU hi hk htype

end PairConfiguration

/-- Seven incidences, at most three intrinsic corner types, and exactly
one uniquely owned physical corner exclude a protected square center. -/
theorem not_hasProtectedCenter_of_one_unique_corner (d : SquareDissection)
    (hN : d.cornerIncidenceCount = 7) (htypes : d.usedCornerTypes.card ≤ 3)
    (hU : (Finset.univ.filter fun j : Fin 4 => d.cornerTileCount j = 1).card = 1) :
    ¬d.HasProtectedCenter := by
  intro hc
  obtain ⟨C⟩ := exists_pairConfiguration d hc hN htypes
  exact C.not_one_unique_corner hc hU

end Puzzling139335.N7
