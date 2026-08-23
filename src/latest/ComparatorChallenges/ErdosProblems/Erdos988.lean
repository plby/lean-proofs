/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter Finset MeasureTheory Metric Set
open scoped BigOperators ENNReal NNReal Pointwise Topology

noncomputable section


namespace Erdos988

open scoped Classical in
abbrev E3 := EuclideanSpace ℝ (Fin 3)

end Erdos988

namespace Erdos988

open scoped Classical in
abbrev S2 := Metric.sphere (0 : E3) 1

end Erdos988

namespace Erdos988

open scoped Classical in
def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

end Erdos988

namespace Erdos988

open scoped Classical in
def capArea (t : ℝ) : ℝ := (1 - t) / 2

end Erdos988

namespace Erdos988

open scoped Classical in
noncomputable def signedCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact ((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    capArea t * P.card

end Erdos988

namespace Erdos988

open scoped Classical in
noncomputable def capError (P : Finset S2) (u : S2) (t : ℝ) : ℝ :=
  |signedCapError P u t|

end Erdos988

namespace Erdos988

open scoped Classical in
noncomputable def capErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ r = capError P u t}

end Erdos988

namespace Erdos988

open scoped Classical in
noncomputable def sphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (capErrorSet P)

end Erdos988

namespace Erdos988

open scoped Classical in
noncomputable def minimumDiscrepancy (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ P : Finset S2, P.card = n ∧ d = sphericalCapDiscrepancy P}

end Erdos988

namespace Erdos988

open scoped Classical in
theorem erdos_988 : Tendsto minimumDiscrepancy atTop atTop := by
  sorry

end Erdos988

end
