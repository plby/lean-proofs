import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingHomotopy
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingLocalHomotopy
import Wikipedia.HopfProblem.SpecialPeriodsCuspAttachingSurjectivity

/-!
# The actual cusp attachment: section contraction and fundamental-group surjectivity

The genuine cusp overlap identifies the toric section `(t,1,1)` with the
unchanged regular zero section.  Every based regular-section loop contained
in this cusp patch contracts, already in the actual cusp filling, and the
contraction remains based after gluing into the threefold.

The exact homomorphism from the full regular/cusp overlap to the filling
is surjective on fundamental groups: a genuine nonzero fibre factors
through that overlap and already surjects onto the cusp group.  This is
transported to the actual attachment basepoint through a path in the
proved path-connected overlap.

No identification of an arbitrarily tailed peripheral loop with a chosen
word in global generators is asserted here.
-/
