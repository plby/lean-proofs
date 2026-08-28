import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows

/-!
# Small native windows below a cut, retaining the actual flow

Every critical point below the cut gets an upper surgery level below it.
The cut itself need not be regular. Critical points at or above the cut
receive independent positive radius bounds, with no restriction there.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_same_flow_windows_below_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (a : ℝ) :
    ∃ T : AdaptedSurgeryWindows E f, T.field = S.field ∧ T.flow = S.flow ∧
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
      ∀ p : criticalPoints E f, f p < a → T.toSurgeryWindows.upper p < a := by
  let ε : criticalPoints E f → ℝ := fun p => if f p < a then Real.sqrt (a - f p) else 1
  have hε (p : criticalPoints E f) : 0 < ε p := by
    dsimp [ε]
    split_ifs with hp
    · exact Real.sqrt_pos.mpr (sub_pos.mpr hp)
    · exact zero_lt_one
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ := exists_adapted_windows_with_prescribed_flow_lt
    hf hm S.distinct S.smooth S.flow S.integral S.zero S.descent
      (fun p => (S.data p).chart) S.critical_model_germ ε hε
  refine ⟨T, hfield, hflow, hcharts, ?_⟩
  intro p hp
  have hsq : (ε p) ^ 2 = a - f p := by
    simp only [ε, if_pos hp]
    exact Real.sq_sqrt (sub_nonneg.mpr hp.le)
  have hprod := mul_pos (sub_pos.mpr (hsmall p)) (add_pos (hε p) (T.data p).radius_pos)
  change f p + (T.data p).radius ^ 2 < a
  nlinarith

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
