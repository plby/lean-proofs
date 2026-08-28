import Wikipedia.HopfProblem.DegreeCollapseOneThreeHandleTrade

/-!
# Construct the birth location for a one-to-three trade

An actual belt point crosses the regular middle cut. A short reverse-time
flow segment from that point supplies a nonempty regular birth band above
the cut. Thus the handle trade needs no separately supplied birth location.
-/

noncomputable section

open Set Function Filter Metric Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f : M → ℝ}

theorem exists_one_to_three_handle_trade_at_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    (m q : criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 0 → z = m)
    {a : ℝ} (hreg : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 2)
    (hqa : f q < a) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧ (criticalPoints E h).ncard = (criticalPoints E f).ncard ∧
      nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
      nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
      ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  have hneg : Module.finrank ℝ (S.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (S.data q).chart).symm.trans hq1
  have hsplit := (S.data q).chart.finrank_negative_add_positive
  let _ : Fact (Module.finrank ℝ (S.data q).chart.PositiveCoordinates = 4 + 1) := ⟨by
    omega⟩
  obtain ⟨v, t, ht⟩ := S.exists_belt_point_reaching_level hf q 4 hqa hlow (by omega)
  let z := S.flow t ((S.data q).surgery.beltSphere v).val
  have hz : f z = a := ht
  obtain ⟨l₀, u, hl₀, hau, hband⟩ := S.regular_interval_around_level hreg
  have hc : Continuous (fun s : ℝ => f (S.flow s z)) :=
    hf.continuous.comp (S.flow.continuous continuous_id continuous_const)
  have h0 : (fun s : ℝ => f (S.flow s z)) 0 ∈ Iio u := by
    simpa only [Flow.map_zero_apply, hz, mem_Iio] using hau
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp
    (hc.continuousAt.preimage_mem_nhds (isOpen_Iio.mem_nhds h0))
  let x := S.flow (-ε / 2) z
  have hxu : f x < u := hεball (by
    rw [mem_ball, Real.dist_eq, sub_zero, abs_lt]
    constructor <;> linarith)
  have hax : a < f x := by
    have hh := FlowConstruction.strictAnti_flow_height hf (S.smooth.of_le (by simp))
      S.flow S.integral S.zero S.descent (hreg z hz) (show -ε / 2 < 0 by linarith)
    simpa only [Flow.map_zero_apply, hz] using hh
  exact exists_one_to_three_handle_trade S hf hm e hdim m q hm0 hq1 hminimum
    hreg hhigh hlow hqa (show a < (a + f x) / 2 by linarith)
    (fun y hy => hband y ⟨hl₀.le.trans hy.1.le, hy.2.le⟩)
    (show f x ∈ Ioo ((a + f x) / 2) u from ⟨by linarith, hxu⟩)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
