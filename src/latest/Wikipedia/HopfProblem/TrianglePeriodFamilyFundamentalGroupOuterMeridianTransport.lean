import Wikipedia.HopfProblem.TriangleRegularBaseFundamentalGroupFreeCoverMonodromy

/-!
# Reading a lower-upper-lower planar loop in the actual free covering

A loop based between the two punctures can leave in the lower slit
chart, cross from right to left in the upper chart, and return in the
lower chart. The actual covering transitions determine its free word.
This computation does not identify any loop in a source cusp chart.
-/

noncomputable section

open Set

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

attribute [local instance] discreteFreeGroup

/-- The precise covering computation for a loop with three pieces lying
successively in the lower, upper, and lower slit domains. -/
theorem meridianFreeWordHom_lower_upper_lower {c d : TwicePuncturedPlane}
    (hc : c ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V)
    (hd : d ∈ (freeGroupCover.U : Set TwicePuncturedPlane) ∩ freeGroupCover.V)
    (α : Path meridianBasepoint c) (β : Path c d) (γ : Path d meridianBasepoint)
    (hα : ∀ s, α s ∈ freeGroupCover.V)
    (hβ : ∀ s, β s ∈ freeGroupCover.U)
    (hγ : ∀ s, γ s ∈ freeGroupCover.V) :
    meridianFreeWordHom (.mk (α.trans (β.trans γ))) =
      (freeGroupTransition d)⁻¹ * freeGroupTransition c := by
  have hm : freeGroupCover.isCoveringMap.monodromy (.mk (α.trans (β.trans γ)))
      (freeGroupCover.fiberPointU meridianBasepoint 1) =
      freeGroupCover.fiberPointU meridianBasepoint
        ((freeGroupTransition c)⁻¹ * freeGroupTransition d) := by
    rw [Path.Homotopic.Quotient.mk_trans,
      freeGroupCover.isCoveringMap.monodromy_trans_apply,
      freeGroupCover.fiberPointU_eq_fiberPointV meridianBasepoint 1
        freeGroupCover_basepoint_mem,
      freeGroupCover.monodromy_of_path_V α hα,
      freeGroupCover.fiberPointV_eq_fiberPointU c _ hc,
      Path.Homotopic.Quotient.mk_trans,
      freeGroupCover.isCoveringMap.monodromy_trans_apply,
      freeGroupCover.monodromy_of_path_U β hβ,
      freeGroupCover.fiberPointU_eq_fiberPointV d _ hd,
      freeGroupCover.monodromy_of_path_V γ hγ,
      freeGroupCover.fiberPointV_eq_fiberPointU meridianBasepoint _
        freeGroupCover_basepoint_mem]
    simp only [freeGroupCover_transition, freeGroupTransition_basepoint,
      one_mul, inv_one, mul_one]
  have hop : freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
      freeGroupCover_basepoint_mem.1 (.mk (α.trans (β.trans γ))) =
      MulOpposite.op ((freeGroupTransition c)⁻¹ * freeGroupTransition d) := by
    apply (freeGroupCover.isQuotientCoveringMap.fundamentalGroupToMulOpposite_apply_eq_Iff).mpr
    have hm' := congrArg Subtype.val hm
    simpa only [MulOpposite.unop_op, TwoOpenTransition.basepointU_eq_fiberPointU,
      TwoOpenTransition.fiberPointU_val, TwoOpenTransition.smul_pointU, mul_one]
      using hm'.symm
  change (MulEquiv.inv' (FreeGroup Bool)).symm
    (freeGroupCover.fundamentalGroupToMulOpposite meridianBasepoint
      freeGroupCover_basepoint_mem.1 (.mk (α.trans (β.trans γ)))) = _
  rw [hop]
  change ((freeGroupTransition c)⁻¹ * freeGroupTransition d)⁻¹ = _
  simp only [mul_inv_rev, inv_inv]

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
