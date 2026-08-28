import Wikipedia.HopfProblem.PeriodTorusLineBundleChernWinding

/-!
# Winding and based-loop operations

The winding number defined by the exponential covering is additive under
concatenation and changes sign under reversal of genuine based loops.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern

open Topology unitInterval

/-- Concatenating based loops adds their winding numbers. -/
theorem windingNumber_trans (γ δ : BasedLoop) :
    windingNumber (γ.trans δ) = windingNumber γ + windingNumber δ := by
  let a : Path (0 : ℂ) (normalizedLoopLog γ 1) :=
    ⟨normalizedLoopLog γ, normalizedLoopLog_zero γ, rfl⟩
  let b : Path (normalizedLoopLog γ 1)
      (normalizedLoopLog γ 1 + normalizedLoopLog δ 1) :=
    { toFun := fun t => normalizedLoopLog γ 1 + normalizedLoopLog δ t
      continuous_toFun := continuous_const.add (normalizedLoopLog δ).continuous
      source' := by simp
      target' := rfl }
  refine windingNumber_of_logPath (γ.trans δ) (a.trans b) (a.trans b).continuous
    (a.trans b).source ?_ (windingNumber γ + windingNumber δ) ?_
  · intro t
    simp only [Path.trans_apply]
    split_ifs with h
    · exact normalizedLoopLog_exp γ _
    · change Complex.exp (normalizedLoopLog γ 1 + normalizedLoopLog δ _) = _
      rw [Complex.exp_add, normalizedLoopLog_exp_one, one_mul]
      exact normalizedLoopLog_exp δ _
  · rw [(a.trans b).target, normalizedLoopLog_endpoint, normalizedLoopLog_endpoint]
    push_cast
    ring

/-- Reversing a based loop negates its winding number. -/
@[simp] theorem windingNumber_symm (γ : BasedLoop) :
    windingNumber γ.symm = -windingNumber γ := by
  apply (windingNumber_eq_iff_of_logPath_difference γ.symm
    (fun t => normalizedLoopLog γ (σ t))
    ((normalizedLoopLog γ).continuous.comp unitInterval.continuous_symm)
    (fun t => normalizedLoopLog_exp γ (σ t)) (-windingNumber γ)).mpr
  simp [normalizedLoopLog_endpoint]

end Wikipedia.HopfProblem.PeriodTorusLineBundle.Chern
