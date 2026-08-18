/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.FiniteHullDeterminant
import ErdosProblems.Erdos186.PZ.FullRankVolumeBridge

/-! # Unconditional PZ Lemma 7

The finite-hull determinant normalization, Mahler--Minkowski discrete John
theorem, intrinsic active-rank reduction, and the mixed-radius volume bridge
are all unconditional.  This module records their final source-shaped
composition.
-/

namespace Erdos186.PZ.OneStepAssembly

/-- The rank-sensitive discrete-John lemma used in the Pham--Zakharov
iteration, with no remaining geometric hypothesis. -/
theorem pzLemmaSeven : PZLemmaSevenStatement :=
  pzLemmaSeven_of_fullRankVolumeBridge fullRankVolumeBridge

end Erdos186.PZ.OneStepAssembly
