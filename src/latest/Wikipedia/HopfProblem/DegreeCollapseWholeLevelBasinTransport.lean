import Wikipedia.HopfProblem.DegreeCollapseClockNormalizedBasins

/-!
# Exact endpoint-basin transport under prescribed level holonomy

The unchanged exterior half-orbits and exact time-one transition identify
the new backward basin with the old one and the new forward basin with
the inverse image under the prescribed level map. Only actual flows and
their proved endpoint formulas are used.
-/

noncomputable section

open Set Function Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {X M : Type*} [TopologicalSpace M]

theorem whole_level_basins_of_holonomy
    (F H G : Flow ℝ M) (ι : X → M) (D : X → X)
    (hHtop : ∀ x p, Tendsto (fun t => H t x) atTop (𝓝 p) ↔
      Tendsto (fun t => F t x) atTop (𝓝 p))
    (hHbot : ∀ x p, Tendsto (fun t => H t x) atBot (𝓝 p) ↔
      Tendsto (fun t => F t x) atBot (𝓝 p))
    (hend : ∀ x, G 1 (ι x) = H 1 (ι (D x)))
    (hleft : ∀ x, ∀ t : ℝ, t ≤ 0 → G t (ι x) = H t (ι x))
    (hright : ∀ x, ∀ t : ℝ, 0 ≤ t → G t (H 1 (ι x)) = H t (H 1 (ι x))) :
    (∀ x p, Tendsto (fun t => G t (ι x)) atBot (𝓝 p) ↔
      Tendsto (fun t => F t (ι x)) atBot (𝓝 p)) ∧
    ∀ x p, Tendsto (fun t => G t (ι x)) atTop (𝓝 p) ↔
      Tendsto (fun t => F t (ι (D x))) atTop (𝓝 p) := by
  constructor
  · intro x p
    have heq : (fun t => G t (ι x)) =ᶠ[atBot] (fun t => H t (ι x)) := by
      filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
      exact hleft x t ht
    exact (tendsto_congr' heq).trans (hHbot (ι x) p)
  · intro x p
    have heq : (fun t => G t (H 1 (ι (D x)))) =ᶠ[atTop]
        (fun t => H t (H 1 (ι (D x)))) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      exact hright (D x) t ht
    calc
      Tendsto (fun t => G t (ι x)) atTop (𝓝 p) ↔
          Tendsto (fun t => G t (G 1 (ι x))) atTop (𝓝 p) :=
        (MorseCancellation.flow_time_atTop_limit_iff G 1 (ι x) p).symm
      _ ↔ Tendsto (fun t => G t (H 1 (ι (D x)))) atTop (𝓝 p) := by rw [hend]
      _ ↔ Tendsto (fun t => H t (H 1 (ι (D x)))) atTop (𝓝 p) := tendsto_congr' heq
      _ ↔ Tendsto (fun t => H t (ι (D x))) atTop (𝓝 p) :=
        MorseCancellation.flow_time_atTop_limit_iff H 1 (ι (D x)) p
      _ ↔ Tendsto (fun t => F t (ι (D x))) atTop (𝓝 p) := hHtop (ι (D x)) p

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
