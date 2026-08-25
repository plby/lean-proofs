import StackExchange.Puzzling139335.N4OuterPair.Defs
import StackExchange.Puzzling139335.N4OuterPair.Bases
import StackExchange.Puzzling139335.N4OuterPair.Midline
import StackExchange.Puzzling139335.N4OuterPair.Remainder
import StackExchange.Puzzling139335.N4OuterPair.AxisBand
import StackExchange.Puzzling139335.N4OuterPair.AxisNonzero
import StackExchange.Puzzling139335.N4OuterPair.SideIntervals
import StackExchange.Puzzling139335.N4OuterPair.SideGaps
import StackExchange.Puzzling139335.N4OuterPair.CornerLegs
import StackExchange.Puzzling139335.N4OuterPair.Contacts
import StackExchange.Puzzling139335.N4OuterPair.FullHeightLegs
import StackExchange.Puzzling139335.N4OuterPair.SideSupport
import StackExchange.Puzzling139335.N4OuterPair.IntervalOwnership
import StackExchange.Puzzling139335.N4OuterPair.GapOwnership

/-!
# Normalization of an actual reflected outer pair

`N4OuterPair.Configuration` records only the bottom corner memberships,
the actual reflected outer pair, and absence of corners from the middle
pieces.  With a protected center, the lemmas derive opposite half-square
containment, full outer sides, actual unit-base frontiers in all copies,
interior crossing of the midline by both middle pieces, avoidance of the
top and bottom sides, nonaxis middle bases, and positive interval-shaped
source-side contacts.  The actual middle union inherits the outer reflection.
The two side contacts cannot both reach the midline.  If both leave positive
gaps, those closed gaps are wholly owned by different middle pieces.

The module does not assume a middle-interface certificate.  Constructing
the final supported-source data and deriving a nontrivial interface remain
separate obligations of the global reduction.
-/
