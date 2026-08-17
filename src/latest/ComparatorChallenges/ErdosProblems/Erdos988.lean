import Mathlib

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos988

abbrev E3 := EuclideanSpace ℝ (Fin 3)

end Erdos988

namespace Erdos988

abbrev S2 := Metric.sphere (0 : E3) 1

end Erdos988

namespace Erdos988

def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

end Erdos988

namespace Erdos988

def capArea (t : ℝ) : ℝ := (1 - t) / 2

end Erdos988

namespace Erdos988

noncomputable def signedCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact ((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    capArea t * P.card

end Erdos988

namespace Erdos988

noncomputable def capError (P : Finset S2) (u : S2) (t : ℝ) : ℝ :=
  |signedCapError P u t|

end Erdos988

namespace Erdos988

noncomputable def capErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ r = capError P u t}

end Erdos988

namespace Erdos988

noncomputable def sphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (capErrorSet P)

end Erdos988

namespace Erdos988

noncomputable def minimumDiscrepancy (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ P : Finset S2, P.card = n ∧ d = sphericalCapDiscrepancy P}

end Erdos988

namespace Erdos988

theorem erdos_988 : Tendsto minimumDiscrepancy atTop atTop := by
  sorry

end Erdos988

end
