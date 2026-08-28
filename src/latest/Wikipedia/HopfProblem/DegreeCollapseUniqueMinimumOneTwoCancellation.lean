import Wikipedia.HopfProblem.DegreeCollapseOneTwoMiddleCutCancellation
import Wikipedia.HopfProblem.DegreeCollapseBoundedPrescribedFlowWindows
import Wikipedia.HopfProblem.DegreeCollapseSingleMinimumFlowRealization

/-!
# One/two cancellation from a unique minimum and a preserved middle cut

The new function's adapted system is constructed from its Morse and excellent
properties. Actual holonomy puts both one-handle branches at the unique
minimum. Fresh smaller windows avoid the cut while retaining that same flow,
so the whole-basin endpoint theorem preserves the branches. The geometric
middle-cut cancellation now applies without any field or surgery-window input.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PathConnectedSpace M] {f g : M → ℝ}

open Classical in
theorem cancel_one_two_pair_at_unchanged_cut_of_unique_minimum
    (S : AdaptedSurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hg : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g)
    (hmg : IsMorse E g) (hinjg : InjOn g (criticalPoints E g))
    (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    {a : ℝ} (hfr : ∀ y, f y = a → y ∉ criticalPoints E f)
    (hgr : ∀ y, g y = a → y ∉ criticalPoints E g) (heq : ∀ y, g y = a ↔ f y = a)
    (hhigh : ∀ z : criticalPoints E f, a ≤ f z → 3 ≤ nativeMorseIndex E f z)
    (hlow : ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ 3)
    (m q r : criticalPoints E g) (hm : nativeMorseIndex E g m = 0)
    (hq : nativeMorseIndex E g q = 1) (hr : nativeMorseIndex E g r = 2)
    (hminimum : ∀ z : criticalPoints E g, nativeMorseIndex E g z = 0 → z = m)
    (hqa : g q < a) (har : a < g r)
    (hgap : ∀ z : criticalPoints E g, g z < g r → g z < a)
    (hnewlow : ∀ z : criticalPoints E g, g z ≤ a → nativeMorseIndex E g z ≤ 2) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧
      (criticalPoints E h).ncard + 2 = (criticalPoints E g).ncard ∧
      (∀ w, w ∈ criticalPoints E h ↔ w ∈ criticalPoints E g ∧ w ≠ q.val ∧ w ≠ r.val) ∧
      ∀ w ∈ criticalPoints E h, nativeMorseIndex E h w = nativeMorseIndex E g w := by
  obtain ⟨T₀⟩ := nonempty_adaptedSurgeryWindows hg hmg hinjg
  obtain ⟨U, -, -, hbranchesU, -⟩ :=
    T₀.realize_unique_minimum_one_handle_branches hg hmg m q hq hminimum
  obtain ⟨T, -, hflow, -, hbelow, -⟩ := U.exists_same_flow_windows_avoiding_level hg hmg hgr
  have hbranches := U.attaching_branches_of_same_flow T hg m q hflow hbranchesU
  have hneg : Module.finrank ℝ (T.data q).chart.NegativeCoordinates = 1 :=
    (nativeMorseIndex_eq_chart (T.data q).chart).symm.trans hq
  obtain ⟨u, v, huv⟩ := exists_distinct_unitSphere_points_of_finrank_one hneg
  exact cancel_one_two_pair_at_preserved_middle_cut S T hf hg hmg e hdim hfr hgr heq
    hhigh hlow m q r hm hq hr u hbranches (hbelow q hqa).le har hgap hnewlow

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
