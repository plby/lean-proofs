import Wikipedia.HopfProblem.DegreeCollapseAdaptedSurgeryBasins
import Wikipedia.HopfProblem.DegreeCollapseOrbitPreservingBandBridge
import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# The actual next attaching sphere in the common flow's regular level

The regular-band bridge is constructed along the same flow that agrees
with every Morse block. Consequently its pulled-back attaching sphere is
exactly the entire backward basin section in the preceding upper level.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_orbit_bandBridge (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : criticalPoints E f)
    (hpq : f p < f q)
    (hconsecutive : ∀ r : criticalPoints E f, ¬(f p < f r ∧ f r < f q)) :
    letI := RegularLevel.chartedSpace hf (S.data p).upper_regular
    letI := RegularLevel.chartedSpace hf (S.data q).lower_regular
    ∃ D : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞,
      ∃ e : Diffeomorph 𝓘(ℝ, RegularLevel.Model E) 𝓘(ℝ, RegularLevel.Model E)
        (S.data p).UpperLevel (S.data q).LowerLevel ∞,
        D '' {x : M | f x ≤ f p + (S.data p).radius ^ 2} =
          {x : M | f x ≤ f q - (S.data q).radius ^ 2} ∧
        (∀ x, (e x : M) = D x) ∧ ∀ x, ∃ t, S.flow t x = D x :=
  FlowTimeChange.exists_orbit_preserving_native_band_bridge hf S.smooth S.descent S.flow S.integral
    (S.separated p q hpq).le (S.toSurgeryWindows.regular_between p q hconsecutive)
    (S.data p).upper_regular (S.data q).lower_regular

open Classical in
theorem AdaptedSurgeryWindows.transported_attaching_basin_iff (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (p q : criticalPoints E f)
    (n : ℕ) [Fact (Module.finrank ℝ (S.data q).chart.NegativeCoordinates = n + 1)]
    (e : (S.data p).UpperLevel ≃ₜ (S.data q).LowerLevel)
    (horbit : ∀ x : (S.data p).UpperLevel, ∃ t, S.flow t x = (e x : M))
    (x : (S.data p).UpperLevel) :
    Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ↔
      x ∈ range ((S.data p).transportedAttachingSphere (S.data q) n e) := by
  rw [(S.data p).range_transportedAttachingSphere (S.data q) n e]
  change Tendsto (fun t => S.flow t x) atBot (𝓝 q.val) ↔
    e x ∈ range (S.data q).surgery.attachingSphere
  rw [← S.attaching_basin_iff hf q (e x)]
  obtain ⟨t, ht⟩ := horbit x
  rw [← ht]
  exact (flow_time_atBot_limit_iff S.flow t (x : M) q.val).symm

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
