/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.CountableExtensionFinal
import ErdosProblems.Erdos599.RegularExtension
import ErdosProblems.Erdos599.SingularTargetMachine

/-!
# Erdős Problem 599: assembly of the extension induction step

This file dispatches the extension half of Aharoni--Berger's simultaneous
cardinal induction to its three substantive constructions.  Cardinal zero is
already covered by the countable construction (and also has the elementary
proof `extensionClauseAt_zero`); a positive cardinal at most `aleph_0` uses
the countable safe-link recursion, and an uncountable cardinal is regular or
singular.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

universe u

variable {V : Type u}

/-- The extension clause at the current cardinal, uniformly for every
unhindered web.  All graph-theoretic work is discharged by the concrete
countable, regular, and singular branch theorems. -/
theorem extensionClauseStep (kappa : Cardinal.{u})
    (hlower : UniversalCardinalInductionBelow V kappa) :
    UniversalExtensionClauseAt V kappa := by
  intro Gamma hGamma
  cases extensionCardinalCase kappa with
  | zero hkappa =>
      subst kappa
      exact extensionClauseAt_zero Gamma
  | countable _ hkappa =>
      exact extensionClauseAt_countable Gamma hGamma hkappa
  | uncountableRegular hkappa hregular =>
      exact RegularExtension.regularExtensionClauseStep
        kappa hlower hregular hkappa Gamma hGamma
  | uncountableSingular hkappa hsingular =>
      exact singularExtensionClauseAt
        kappa hkappa hsingular hlower Gamma hGamma

end CardinalInduction
end Erdos599
