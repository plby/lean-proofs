import Wikipedia.HopfProblem.DegreeCollapseOneHandleBasinUniqueness

/-!
# Actual minimum endpoints below the first positive-index handle

If every lower critical point has index zero, compact strict descent gives
each lower-level point an actual minimum endpoint. Distinct attaching
components force distinct endpoints for the two branches. No endpoint or
connection is supplied to this theorem.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.lower_level_forward_minimum
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (x : (S.data q).LowerLevel) :
    ∃ p : criticalPoints E f, nativeMorseIndex E f p = 0 ∧
      f p < S.toSurgeryWindows.lower q ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val) := by
  obtain ⟨r, hr, p, hp, -, hlim, hheight⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct (x : M)
  have hx : (x : M) ∉ criticalPoints E f := (S.data q).lower_regular x x.property
  have hlow : f p < S.toSurgeryWindows.lower q := by
    change f p < f q - (S.data q).radius ^ 2
    have hh := (hheight hx).1
    simpa only [x.property] using hh
  exact ⟨⟨p, hp⟩, hbefore ⟨p, hp⟩ (hlow.trans (S.toSurgeryWindows.lower_lt_value q)),
    hlow, hlim⟩

theorem AdaptedSurgeryWindows.first_one_distinct_minimum_endpoints
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (q : criticalPoints E f)
    (hbefore : ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0)
    (u v : sphere (0 : (S.data q).chart.NegativeCoordinates) 1)
    (hnot : ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v)) :
    ∃ p r : criticalPoints E f, nativeMorseIndex E f p = 0 ∧ nativeMorseIndex E f r = 0 ∧
      p ≠ r ∧ f p < S.toSurgeryWindows.lower q ∧ f r < S.toSurgeryWindows.lower q ∧
      Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap u).val) atTop (𝓝 p.val) ∧
      Tendsto (fun t => S.flow t ((S.data q).coreBoundaryMap v).val) atTop (𝓝 r.val) := by
  obtain ⟨p, hp, hpq, hpu⟩ := S.lower_level_forward_minimum hf q hbefore
    ((S.data q).surgery.attachingSphere u)
  obtain ⟨r, hr, hrq, hrv⟩ := S.lower_level_forward_minimum hf q hbefore
    ((S.data q).surgery.attachingSphere v)
  refine ⟨p, r, hp, hr, ?_, hpq, hrq, hpu, hrv⟩
  intro heq
  subst r
  let : LocallyPathConnectedSpace M := ChartedSpace.locallyPathConnectedSpace E M
  exact hnot (joined_sublevel_of_common_forward_limit S.flow hf.continuous
    (FlowConstruction.antitone_flow_height hf S.flow S.integral S.zero S.descent)
    ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v) hpq hpu hrv)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
