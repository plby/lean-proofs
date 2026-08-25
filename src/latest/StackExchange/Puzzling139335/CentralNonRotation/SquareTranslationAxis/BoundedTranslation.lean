import StackExchange.Puzzling139335.Definitions
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-! # A nonempty compact set admits no nonzero forward translation

It suffices that translation maps the set into itself; surjectivity on the
set is not needed. Coordinate minima and maxima force each displacement
coordinate to vanish.
-/

namespace Puzzling139335.CentralNonRotation

open Set

/-- A translation mapping a nonempty compact subset of the plane into itself
has zero displacement. -/
theorem translation_eq_zero_of_isCompact (K : Set Plane) (hK : IsCompact K)
    (hKne : K.Nonempty) (w : Plane) (hmap : ∀ x ∈ K, x + w ∈ K) :
    w = 0 := by
  ext i
  have hcoord : Continuous (fun x : Plane => x i) :=
    PiLp.continuous_apply 2 _ i
  obtain ⟨a, ha, hmin⟩ := hK.exists_isMinOn hKne hcoord.continuousOn
  obtain ⟨b, hb, hmax⟩ := hK.exists_isMaxOn hKne hcoord.continuousOn
  have hlow := hmin (hmap a ha)
  have hupp := hmax (hmap b hb)
  change a i ≤ a i + w i at hlow
  change b i + w i ≤ b i at hupp
  change w i = 0
  linarith

end Puzzling139335.CentralNonRotation
