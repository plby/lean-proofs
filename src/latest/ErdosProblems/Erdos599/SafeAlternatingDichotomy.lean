/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingFiniteMacroCompiler
import ErdosProblems.Erdos599.AlternatingInfiniteMacroCompiler

/-!
# The endpoint-pure safe alternating dichotomy

The deterministic macro orbit has a finite or infinite branch.  The two
edge-level compilers discharge those branches, so this module exposes the
unconditional statement consumed by simultaneous assignment.
-/

namespace Erdos599
namespace Alternating

open Set DirectedPath

universe u

variable {V : Type u}

/-- The corrected endpoint-pure form of the safe alternating dichotomy. -/
theorem safeAlternatingDichotomyStatement (Γ : DWeb V) :
    SafeAlternatingDichotomyStatement Γ := by
  exact safeAlternatingDichotomyStatement_of_macro_compilers
    finiteMacroCompiler infiniteMacroCompiler

end Alternating
end Erdos599
