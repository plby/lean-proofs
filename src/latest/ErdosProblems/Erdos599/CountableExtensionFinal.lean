/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableExtension
import ErdosProblems.Erdos599.SafeLinkPropositionComplete

/-!
# Final assembly of the countable extension clause

The queue construction in `CountableExtension` consumes Proposition 6.3.
This module supplies it from the source-faithful full-quotient proof of
Proposition 6.3.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- The countable extension clause, obtained from the unconditional
source-faithful proof of Proposition 6.3. -/
theorem extensionClauseAt_countable
    (G : DWeb V) (hG : G.IsUnhindered)
    {kappa : Cardinal.{u}} (hkappa : kappa ≤ ℵ₀) :
    ExtensionClauseAt G kappa :=
  extensionClauseAt_countable_of_proposition63
    SafeLink.proposition63 G hG hkappa

end CardinalInduction
end Erdos599
