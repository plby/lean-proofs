import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicMidpointFourInputs

/-!
# Exactly twelve inputs at the parameter midpoint

This counts the actual five-sphere inputs for the selected column when
both parameters are `π/2`. It does not assert that all preimages occur at
that midpoint, nor establish local degrees or a generator property.
-/

noncomputable section

open scoped Matrix

namespace Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary

open QuaternionicBottMatrix

theorem midpointPhases_injective : Function.Injective midpointPhases := by
  intro r s h
  have hr := congrArg (fun u : unitary ℂ ↦ u.val.re) h
  have hi := congrArg (fun u : unitary ℂ ↦ u.val.im) h
  have hpos : 0 < Real.sqrt (3 : ℝ) := by positivity
  fin_cases r <;> fin_cases s <;> try rfl
  all_goals
    norm_num [midpointPhases, targetPhasePlus, targetPhaseMinus, targetBeta,
      Matrix.cons_val_two] at hr
  all_goals
    norm_num [midpointPhases, targetPhasePlus, targetPhaseMinus, targetBeta,
      Matrix.cons_val_two] at hi
  all_goals exfalso; linarith

theorem midpointPhaseSets_disjoint :
    Pairwise (fun r s : Fin 3 ↦ Disjoint (midpointPhaseSet (midpointPhases r))
      (midpointPhaseSet (midpointPhases s))) := by
  intro r s hrs
  apply Set.disjoint_left.mpr
  intro z hzr hzs
  have h : (midpointPhases r).val = (midpointPhases s).val := by
    have he := congrArg (fun A : Matrix (Fin 3) (Fin 3) ℂ ↦ A 1 1) (hzr.symm.trans hzs)
    simpa [targetMatrix] using he
  exact hrs (midpointPhases_injective (Subtype.ext h))

theorem midpointTargetPreimage_ncard_eq_twelve : midpointTargetPreimage.ncard = 12 := by
  rw [midpointTargetPreimage_eq_union,
    Set.ncard_iUnion_of_finite (fun r ↦ midpointPhaseSet_finite _ (midpointPhases_cube r))
      midpointPhaseSets_disjoint]
  simp [midpointPhaseSet_ncard_eq_four _ (midpointPhases_cube _), finsum_eq_sum_of_fintype]

end Wikipedia.HomotopyGroupsOfSpheres.ComplexCrossProductUnitary
