import ErdosProblems.Erdos1148.ModularOrbitSpace
import Mathlib.Topology.Compactness.LocallyCompact
import Mathlib.Topology.Metrizable.Urysohn

/-! # Local compactness of the modular orbit space -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

instance realSpecialLinearLocallyCompact : LocallyCompactSpace SL(2, ℝ) := by
  let : LocallyCompactSpace (Matrix (Fin 2) (Fin 2) ℝ) :=
    inferInstanceAs (LocallyCompactSpace (Fin 2 → Fin 2 → ℝ))
  exact Matrix.SpecialLinearGroup.isClosedEmbedding_val.locallyCompactSpace

instance modularOrbitSpaceLocallyCompact : LocallyCompactSpace ModularOrbitSpace :=
  (MulAction.isOpenQuotientMap_quotientMk (Γ := SL(2, ℤ))
    (T := SL(2, ℝ))).locallyCompactSpace

end Erdos1148.DukeArithmetic
