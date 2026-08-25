import StackExchange.Puzzling139335.CentralRotation.JordanCut

/-!
# The direct-isometry branch of a central two-piece Jordan cut

`JordanCrosscut.center_mem_of_direct_non_halfTurn` proves that the center is
on the actual common cut.  The only hypotheses are the Jordan crosscut and
its two outer arcs, central symmetry, and a direct non-half-turn isometry
mapping the two closed sides.  The multiplier version connects directly to
the exhaustive coordinate classification of plane isometries.

The proof derives compatible circle coordinates and their increasing lifts,
antipodal endpoints, the finite first overlap, the local reversed-arc
half-turn, and its center.  No boundary length, polygonality, or additional
orientation premise is assumed.
-/
