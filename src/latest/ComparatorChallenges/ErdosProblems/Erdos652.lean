import Mathlib

open Classical Filter
open scoped Real Topology

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Erdos652

abbrev Point := EuclideanSpace ℝ (Fin 2)

end Erdos652

namespace Erdos652

def distanceRadii (p : Point) (Q : Finset Point) : Finset ℝ := Q.image (dist p)

end Erdos652

namespace Erdos652

def pinnedDistanceCount (p : Point) (S : Finset Point) : ℕ :=
  (distanceRadii p (S.erase p)).card

end Erdos652

namespace Erdos652

def lowPinnedDistancePoints (S : Finset Point) (C : ℝ) : Finset Point :=
  S.filter fun p => (pinnedDistanceCount p S : ℝ) < C * Real.sqrt S.card

end Erdos652

namespace Erdos652

def AdmissiblePinnedConstant (k : ℕ) (a : ℝ) : Prop :=
  ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∃ S : Finset Point, S.card = n ∧
      k ≤ (lowPinnedDistancePoints S a).card

end Erdos652

namespace Erdos652

def admissiblePinnedConstants (k : ℕ) : Set ℝ :=
  {a | AdmissiblePinnedConstant k a}

end Erdos652

namespace Erdos652

def erdos652Alpha (k : ℕ) : ℝ :=
  sInf (admissiblePinnedConstants k)

end Erdos652

namespace Erdos652

theorem erdos_652 :
    Tendsto erdos652Alpha atTop atTop := by
  sorry

end Erdos652

end
