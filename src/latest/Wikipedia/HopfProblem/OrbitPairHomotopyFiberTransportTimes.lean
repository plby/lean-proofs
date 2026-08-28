import Mathlib.Topology.UnitInterval
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Continuous time coordinates for homotopy-fibre transport

At deformation time s, the first segment reverses the base homotopy over a
path-time interval of length s/2. The original path occupies the rest. Its
denominator is always at least one, so this formula also handles s = 0.
-/

noncomputable section

namespace Wikipedia.HopfProblem.OrbitPair.HomotopyFiber

def reverseTime (s t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((s : ℝ) - 2 * (t : ℝ))

def remainingTime (s t : unitInterval) : unitInterval :=
  Set.projIcc 0 1 zero_le_one ((2 * (t : ℝ) - (s : ℝ)) / (2 - (s : ℝ)))

theorem time_denominator_pos (s : unitInterval) : 0 < 2 - (s : ℝ) := by
  have hs := s.property.2
  linarith

theorem continuous_reverseTime : Continuous (fun z : unitInterval × unitInterval ↦
    reverseTime z.1 z.2) :=
  continuous_projIcc.comp ((continuous_subtype_val.comp continuous_fst).sub
    ((continuous_subtype_val.comp continuous_snd).const_mul 2))

theorem continuous_remainingTime : Continuous (fun z : unitInterval × unitInterval ↦
    remainingTime z.1 z.2) :=
  continuous_projIcc.comp ((((continuous_subtype_val.comp continuous_snd).const_mul 2).sub
    (continuous_subtype_val.comp continuous_fst)).div
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst))
      (fun z ↦ (time_denominator_pos z.1).ne'))

theorem reverseTime_zero (s : unitInterval) : reverseTime s 0 = s := by
  simp [reverseTime]

theorem remainingTime_zero (t : unitInterval) : remainingTime 0 t = t := by
  simp [remainingTime]

theorem remainingTime_one (s : unitInterval) : remainingTime s 1 = 1 := by
  have hs := (time_denominator_pos s).ne'
  simp [remainingTime, hs]

theorem reverseTime_join (s t : unitInterval) (h : 2 * (t : ℝ) = (s : ℝ)) :
    reverseTime s t = 0 := by
  simp [reverseTime, h]

theorem remainingTime_join (s t : unitInterval) (h : 2 * (t : ℝ) = (s : ℝ)) :
    remainingTime s t = 0 := by
  simp [remainingTime, h]

end Wikipedia.HopfProblem.OrbitPair.HomotopyFiber
