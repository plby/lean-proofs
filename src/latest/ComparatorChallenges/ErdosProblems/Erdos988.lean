/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos988

abbrev E3 := EuclideanSpace ℝ (Fin 3)

abbrev S2 := Metric.sphere (0 : E3) 1

def sphericalCap (u : S2) (t : ℝ) : Set S2 :=
  {x | t ≤ inner ℝ (x : E3) (u : E3)}

noncomputable def capArea (t : ℝ) : ℝ := (1 - t) / 2

noncomputable def signedCapError (P : Finset S2) (u : S2) (t : ℝ) : ℝ := by
  classical
  exact ((P.filter fun x ↦ x ∈ sphericalCap u t).card : ℝ) -
    capArea t * P.card

noncomputable def capError (P : Finset S2) (u : S2) (t : ℝ) : ℝ :=
  |signedCapError P u t|

noncomputable def capErrorSet (P : Finset S2) : Set ℝ :=
  {r | ∃ u : S2, ∃ t : ℝ, t ∈ Set.Icc (-1 : ℝ) 1 ∧ r = capError P u t}

noncomputable def sphericalCapDiscrepancy (P : Finset S2) : ℝ :=
  sSup (capErrorSet P)

noncomputable def minimumDiscrepancy (n : ℕ) : ℝ :=
  sInf {d : ℝ | ∃ P : Finset S2, P.card = n ∧ d = sphericalCapDiscrepancy P}

theorem erdos_988 : Tendsto minimumDiscrepancy atTop atTop := by
  sorry

end Erdos988
