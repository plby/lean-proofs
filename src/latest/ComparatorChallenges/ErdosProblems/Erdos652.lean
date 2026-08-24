/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib

open Filter

namespace Erdos652

abbrev Point := EuclideanSpace ℝ (Fin 2)

noncomputable def distanceRadii (p : Point) (Q : Finset Point) : Finset ℝ := Q.image (dist p)

noncomputable def pinnedDistanceCount (p : Point) (S : Finset Point) : ℕ :=
  (distanceRadii p (S.erase p)).card

noncomputable def lowPinnedDistancePoints (S : Finset Point) (C : ℝ) : Finset Point :=
  S.filter fun p => (pinnedDistanceCount p S : ℝ) < C * Real.sqrt S.card

def AdmissiblePinnedConstant (k : ℕ) (a : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset Point, S.card = n ∧
      k ≤ (lowPinnedDistancePoints S a).card

def admissiblePinnedConstants (k : ℕ) : Set ℝ :=
  {a | AdmissiblePinnedConstant k a}

noncomputable def erdos652Alpha (k : ℕ) : ℝ :=
  sInf (admissiblePinnedConstants k)

theorem erdos_652 :
    Tendsto erdos652Alpha atTop atTop := by
  sorry

end Erdos652
