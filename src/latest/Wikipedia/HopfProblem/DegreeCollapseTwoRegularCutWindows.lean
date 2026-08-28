import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows

/-!
# Shrink the original native windows to avoid two regular cuts simultaneously

One positive radius bound at each original critical point is chosen below
the old radius and both distances to the cuts. The prescribed-flow window
construction retains the entire original field, complete flow, and signed
critical charts. Neither previously protected cut is lost by the shrinking.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.exists_same_flow_windows_avoiding_two_levels
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) {a b : ℝ}
    (ha : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hb : ∀ y, f y = b → y ∉ criticalPoints E f) :
    ∃ T : AdaptedSurgeryWindows E f, T.field = S.field ∧ T.flow = S.flow ∧
      (∀ p, (T.data p).chart = (S.data p).chart) ∧
      (∀ p, (T.data p).radius < (S.data p).radius) ∧
      (∀ p : criticalPoints E f, f p < a → T.toSurgeryWindows.upper p < a) ∧
      (∀ p : criticalPoints E f, a < f p → a < T.toSurgeryWindows.lower p) ∧
      (∀ p : criticalPoints E f, f p < b → T.toSurgeryWindows.upper p < b) ∧
      ∀ p : criticalPoints E f, b < f p → b < T.toSurgeryWindows.lower p := by
  let ε : criticalPoints E f → ℝ := fun p =>
    min (S.data p).radius (min (Real.sqrt |f p - a|) (Real.sqrt |f p - b|))
  have hroot (t : ℝ) (ht : ∀ y, f y = t → y ∉ criticalPoints E f)
      (p : criticalPoints E f) : 0 < Real.sqrt |f p - t| :=
    Real.sqrt_pos.mpr (abs_pos.mpr (sub_ne_zero.mpr (fun h => ht p.val h p.property)))
  have hε (p : criticalPoints E f) : 0 < ε p :=
    lt_min (S.data p).radius_pos (lt_min (hroot a ha p) (hroot b hb p))
  obtain ⟨T, hfield, hflow, hcharts, hsmall⟩ := exists_adapted_windows_with_prescribed_flow_lt
    hf hm S.distinct S.smooth S.flow S.integral S.zero S.descent
      (fun p => (S.data p).chart) S.critical_model_germ ε hε
  have hold (p : criticalPoints E f) : (T.data p).radius < (S.data p).radius :=
    (hsmall p).trans_le (min_le_left _ _)
  have hsmallA (p : criticalPoints E f) : (T.data p).radius < Real.sqrt |f p - a| :=
    (hsmall p).trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hsmallB (p : criticalPoints E f) : (T.data p).radius < Real.sqrt |f p - b| :=
    (hsmall p).trans_le ((min_le_right _ _).trans (min_le_right _ _))
  have hcuts (t : ℝ) (ht : ∀ y, f y = t → y ∉ criticalPoints E f)
      (hsmallT : ∀ p : criticalPoints E f, (T.data p).radius < Real.sqrt |f p - t|) :
      (∀ p : criticalPoints E f, f p < t → T.toSurgeryWindows.upper p < t) ∧
      (∀ p : criticalPoints E f, t < f p → t < T.toSurgeryWindows.lower p) := by
    have hsq (p : criticalPoints E f) : (T.data p).radius ^ 2 < |f p - t| := by
      have hp := mul_pos (sub_pos.mpr (hsmallT p))
        (add_pos (hroot t ht p) (T.data p).radius_pos)
      have heq := Real.sq_sqrt (abs_nonneg (f p - t))
      nlinarith
    constructor
    · intro p hp
      have hh := hsq p
      rw [abs_of_neg (sub_neg.mpr hp)] at hh
      change f p + (T.data p).radius ^ 2 < t
      linarith
    · intro p hp
      have hh := hsq p
      rw [abs_of_pos (sub_pos.mpr hp)] at hh
      change t < f p - (T.data p).radius ^ 2
      linarith
  exact ⟨T, hfield, hflow, hcharts, hold, (hcuts a ha hsmallA).1,
    (hcuts a ha hsmallA).2, (hcuts b hb hsmallB).1, (hcuts b hb hsmallB).2⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
