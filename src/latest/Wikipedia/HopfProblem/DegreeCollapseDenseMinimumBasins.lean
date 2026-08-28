import Wikipedia.HopfProblem.DegreeCollapseNonminimumBasinsMeagre
import Wikipedia.HopfProblem.DegreeCollapseNativeNoReturn
import Mathlib.Topology.Baire.LocallyCompactRegular

/-!
# Open minimum basins with dense union for the actual native flow

The zero-index model gives an entire basin neighborhood. Flow invariance
propagates that openness to every basin point. The other finitely many
critical basins are meagre, while every actual trajectory has a critical
forward endpoint. Baire's theorem therefore makes the union of minimum
basins dense, without any Morse--Smale condition.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

theorem AdaptedSurgeryWindows.isOpen_minimum_forward_basin
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (p : criticalPoints E f) (hindex : nativeMorseIndex E f p = 0) :
    IsOpen {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} := by
  let c := (S.data p).chart
  have hi : Module.finrank ℝ c.NegativeCoordinates = 0 :=
    (nativeMorseIndex_eq_chart c).symm.trans hindex
  let : Subsingleton c.NegativeCoordinates :=
    (Module.finrank_eq_zero_iff_of_free ℝ c.NegativeCoordinates).mp hi
  obtain ⟨r, hr, -, hbasin⟩ := exists_descending_morse_basin_block c hf
    (S.smooth.of_le (by simp)) S.flow S.integral S.zero S.descent (S.critical_model_germ p)
  have hnear : ∀ᶠ y in 𝓝 p.val, Tendsto (fun t => S.flow t y) atTop (𝓝 p.val) := by
    filter_upwards [morse_coordinate_neighborhood c hr hr] with y hy
    exact ((hbasin y hy.1 hy.2.1 hy.2.2).1).mpr (Subsingleton.elim _ _)
  apply isOpen_iff_mem_nhds.mpr
  intro x hx
  obtain ⟨t, ht⟩ := (hx.eventually (eventually_eventually_nhds.mpr hnear)).exists
  have hc : Continuous (fun y => S.flow t y) := S.flow.continuous continuous_const continuous_id
  filter_upwards [hc.continuousAt.tendsto.eventually ht] with y hy
  exact (flow_time_atTop_limit_iff S.flow t y p.val).mp hy

theorem AdaptedSurgeryWindows.dense_minimum_forward_basins
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) :
    Dense {x : M | ∃ p : criticalPoints E f, nativeMorseIndex E f p = 0 ∧
      Tendsto (fun t => S.flow t x) atTop (𝓝 p.val)} := by
  let : Finite (criticalPoints E f) := S.finite.to_subtype
  let I := {p : criticalPoints E f // 0 < nativeMorseIndex E f p}
  let B := ⋃ p : I, {x : M | Tendsto (fun t => S.flow t x) atTop (𝓝 p.val.val)}
  have hm : IsMeagre B := isMeagre_iUnion
    (fun p : I => S.nonminimum_forward_basin_meagre hf p.val p.property)
  have hd : Dense Bᶜ := dense_of_mem_residual hm
  apply hd.mono
  intro x hx
  obtain ⟨r, hr, p, hp, -, hlim, -⟩ := FlowCancellation.exists_native_descent_endpoints
    hf S.smooth S.flow S.integral S.zero S.descent S.distinct x
  have hi : nativeMorseIndex E f p = 0 := by
    by_contra hi
    apply hx
    exact mem_iUnion.mpr ⟨(⟨⟨p, hp⟩, Nat.pos_of_ne_zero hi⟩ : I), hlim⟩
  exact ⟨⟨p, hp⟩, hi, hlim⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
