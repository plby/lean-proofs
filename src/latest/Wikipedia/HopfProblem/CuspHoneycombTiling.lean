import Wikipedia.HopfProblem.CuspHoneycombTilingCover
import Wikipedia.HopfProblem.CuspHoneycombTilingTopology
import Wikipedia.HopfProblem.CuspHoneycombTilingIntersections

/-!
# The actual locally finite hexagonal covering of the real plane

The literal dual hexagons cover the real plane, are compact and closed,
and form a locally finite family.  In particular, continuity may be
checked on these actual closed cells when gluing the honeycomb charts.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombTiling

/-- The standard closed-cover gluing criterion applies to the actual
hexagons, not to an abstract model endowed with a quotient topology. -/
theorem continuous_of_cellwise {Y : Type*} [TopologicalSpace Y] {f : Plane → Y}
    (hf : ∀ v : Lattice, ContinuousOn f (cell v)) : Continuous f :=
  cell_locallyFinite.continuous iUnion_cell cell_isClosed hf

theorem continuous_iff_cellwise {Y : Type*} [TopologicalSpace Y] (f : Plane → Y) :
    Continuous f ↔ ∀ v : Lattice, ContinuousOn f (cell v) :=
  ⟨fun hf _ => hf.continuousOn, continuous_of_cellwise⟩

end Wikipedia.HopfProblem.CuspHoneycombTiling
