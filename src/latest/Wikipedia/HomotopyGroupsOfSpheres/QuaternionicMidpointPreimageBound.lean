import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointFiberBound
import Mathlib.Data.Set.Card.Arithmetic

/-!
# A finite upper bound of twelve under the midpoint restriction

There are three possible symmetric matrices and at most four sphere inputs
for each. This does not exclude preimages away from the midpoint, prove
that twelve inputs exist, or compute any local or global degree.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

def midpointPhases : Fin 3 → unitary ℂ :=
  ![⟨-1, by constructor <;> norm_num⟩,
    ⟨targetPhasePlus, targetPhasePlus_unitary⟩,
    ⟨targetPhaseMinus, targetPhaseMinus_unitary⟩]

theorem midpointPhases_cube (r : Fin 3) : (midpointPhases r).val ^ 3 = -1 := by
  fin_cases r <;>
    norm_num [midpointPhases, Matrix.cons_val_two, targetPhasePlus_cube, targetPhaseMinus_cube]

def midpointPhaseSet (u : unitary ℂ) : Set UnitSphere :=
  {z | (symmetricMap z).val.val = u.val • targetMatrix targetAlpha targetBeta}

theorem midpointPhaseSet_finite (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    (midpointPhaseSet u).Finite :=
  Set.finite_coe_iff.mp (midpointFiber_finite_card_le_four u hu).1

theorem midpointPhaseSet_ncard_le_four (u : unitary ℂ) (hu : u.val ^ 3 = -1) :
    (midpointPhaseSet u).ncard ≤ 4 := by
  rw [← Nat.card_coe_set_eq]
  exact (midpointFiber_finite_card_le_four u hu).2

def midpointTargetPreimage : Set UnitSphere :=
  {z | firstColumnFormula (Real.pi / 2) (Real.pi / 2) (symmetricMap z) = targetColumn}

theorem midpointTargetPreimage_eq_union :
    midpointTargetPreimage = ⋃ r : Fin 3, midpointPhaseSet (midpointPhases r) := by
  ext z
  rw [Set.mem_iUnion]
  constructor
  · intro h
    rcases (midpoint_target_three_matrices (symmetricMap z) (symmetricMap_det z)).mp h with
      h0 | h1 | h2
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
  · rintro ⟨r, hr⟩
    exact midpoint_target_of_matrix (symmetricMap z) (midpointPhases r) hr

theorem midpointTargetPreimage_finite : midpointTargetPreimage.Finite := by
  rw [midpointTargetPreimage_eq_union]
  exact Set.finite_iUnion fun r ↦ midpointPhaseSet_finite _ (midpointPhases_cube r)

theorem midpointTargetPreimage_ncard_le_twelve : midpointTargetPreimage.ncard ≤ 12 := by
  rw [midpointTargetPreimage_eq_union]
  calc
    _ ≤ ∑ r : Fin 3, (midpointPhaseSet (midpointPhases r)).ncard :=
      Set.ncard_iUnion_le_of_fintype _
    _ ≤ ∑ _r : Fin 3, 4 := Finset.sum_le_sum fun r _ ↦
      midpointPhaseSet_ncard_le_four _ (midpointPhases_cube r)
    _ = 12 := by norm_num

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
