/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingErasedDecode

/-!
# Old controls and the residual relation

The source residual relation is `Y \ C_E`; it does not globally delete
edges leaving `C_V`.  An earlier draft of this module asserted such a
deletion in order to make every point of `BB` a sink.  That sink assertion
is false and is not required by first-hit pruning.  This compatibility
module is intentionally declaration-free; the valid local endpoint cuts
are the route-direction and forward-conflict cuts in
`GroundingErasedDecode`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingOldControlBoundary

end GroundingOldControlBoundary
end Erdos599
