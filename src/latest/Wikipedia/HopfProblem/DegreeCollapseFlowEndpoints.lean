import Wikipedia.HopfProblem.DegreeCollapseFlowLimitPoints
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# Both actual endpoints of a compact strict-descent trajectory

Compactness bounds the height, so monotone convergence supplies its two
limiting values. The limit-point theorem constructs actual stationary
endpoints. A nonstationary trajectory has strictly ordered endpoint heights.
-/

noncomputable section

open Set Filter
open scoped Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation

variable {X : Type*} [TopologicalSpace X] [CompactSpace X]

/-- Every original trajectory converges at both ends; regular ones have distinct endpoints. -/
theorem exists_strict_descent_flow_endpoints (F : Flow ℝ X) {f : X → ℝ}
    (hf : Continuous f) {S : Set X} (hinj : InjOn f S)
    (hmono : ∀ x, Antitone (fun t : ℝ => f (F t x)))
    (hstrict : ∀ x ∉ S, StrictAnti (fun t : ℝ => f (F t x))) (x : X) :
    ∃ p ∈ S, ∃ q ∈ S,
      Tendsto (fun t : ℝ => F t x) atBot (𝓝 p) ∧
      Tendsto (fun t : ℝ => F t x) atTop (𝓝 q) ∧
      (x ∉ S → f q < f x ∧ f x < f p) := by
  have hrange : range (fun t : ℝ => f (F t x)) ⊆ range f := by
    rintro y ⟨t, rfl⟩
    exact ⟨F t x, rfl⟩
  have hbelow : BddBelow (range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddBelow.mono hrange
  have habove : BddAbove (range (fun t : ℝ => f (F t x))) :=
    (isCompact_range hf).bddAbove.mono hrange
  have htop := tendsto_atTop_ciInf (hmono x) hbelow
  have hbot := tendsto_atBot_ciSup (hmono x) habove
  have hshiftTop (t : ℝ) : Tendsto (t + ·) atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop (b - t)] with s hs
    linarith
  have hshiftBot (t : ℝ) : Tendsto (t + ·) atBot atBot := by
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [eventually_le_atBot (b - t)] with s hs
    linarith
  have hstep (y : X) (hy : y ∉ S) : f (F 1 y) < f y := by
    have hh := hstrict y hy (show (0 : ℝ) < 1 by norm_num)
    simpa only [F.map_zero_apply] using hh
  obtain ⟨p, hp, hfp, hplim⟩ := exists_flow_limit_of_injective_exceptional_height
    F hf hshiftBot hstep hinj hbot
  obtain ⟨q, hq, hfq, hqlim⟩ := exists_flow_limit_of_injective_exceptional_height
    F hf hshiftTop hstep hinj htop
  refine ⟨p, hp, q, hq, hplim, hqlim, ?_⟩
  intro hx
  have hlow : f q ≤ f (F 1 x) := by
    rw [hfq]
    exact ciInf_le hbelow 1
  have hhigh : f (F (-1) x) ≤ f p := by
    rw [hfp]
    exact le_ciSup habove (-1)
  have hdec : f (F 1 x) < f x := hstep x hx
  have hinc : f x < f (F (-1) x) := by
    have hh := hstrict x hx (show (-1 : ℝ) < 0 by norm_num)
    simpa only [F.map_zero_apply] using hh
  exact ⟨hlow.trans_lt hdec, hinc.trans_le hhigh⟩

end Wikipedia.HopfProblem.DegreeCollapse.FlowCancellation
