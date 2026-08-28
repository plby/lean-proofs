import Wikipedia.HopfProblem.DegreeCollapseSublevelOneHandleSelection
import Wikipedia.HopfProblem.DegreeCollapseSublevelZeroOneCancellation
import Wikipedia.HopfProblem.DegreeCollapseMinimumBranchRealization

/-!
# Two minima in a connected sublevel give an actual supported reduction

The merging handle, branch placement, complete flow, distinct endpoints,
and unique cancellation orbit are all constructed. The result has two
fewer critical points, keeps all surviving indices, fixes the whole
original closed upper germ, and retains the exact strict sublevel.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] [PreconnectedSpace M] {f : M → ℝ}

theorem exists_reduction_of_two_minima_below_cut
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hm : IsMorse E f)
    (hinj : InjOn f (criticalPoints E f)) {a : ℝ}
    (ha : ∀ x, f x = a → x ∉ criticalPoints E f)
    [PathConnectedSpace {x : M // f x ≤ a}]
    (p₀ p₁ : criticalPoints E f) (hp₀ : f p₀ < a) (hp₁ : f p₁ < a)
    (hzero₀ : nativeMorseIndex E f p₀ = 0) (hzero₁ : nativeMorseIndex E f p₁ = 0)
    (hne : p₀ ≠ p₁) :
    ∃ g : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ g ∧ IsMorse E g ∧
      InjOn g (criticalPoints E g) ∧
      (criticalPoints E g).ncard + 2 = (criticalPoints E f).ncard ∧
      (∀ x ∈ criticalPoints E g, x ∈ criticalPoints E f ∧
        nativeMorseIndex E g x = nativeMorseIndex E f x) ∧
      (∀ x, a ≤ f x → g =ᶠ[𝓝 x] f) ∧ ∀ x, g x < a ↔ f x < a := by
  obtain ⟨A₀⟩ := nonempty_adaptedSurgeryWindows hf hm hinj
  obtain ⟨A, _, _, _, hcut⟩ := A₀.exists_same_flow_windows_below_cut hf hm a
  obtain ⟨q, hqa, hqone, u, v, hnot⟩ :=
    exists_native_merging_one_handle_below_cut A.toSurgeryWindows hf ha hcut
      p₀ p₁ hp₀ hp₁ hzero₀ hzero₁ hne
  obtain ⟨V, G, p, r, hV, hG, hzero, hdesc, hgerms, hpzero, hrzero, hpr,
      hpq, hrq, hback, hu, hv, _, hnoconnection⟩ :=
    A.realize_one_handle_minimum_branches hf q hqone u v hnot
  have hmodels (x : M) (hx : x ∈ criticalPoints E f) :
      ∃ c : SignedMorseChart (E := E) f x, ∀ᶠ y in 𝓝 x, V y = c.descentField y := by
    refine ⟨(A.data ⟨x, hx⟩).chart, ?_⟩
    filter_upwards [hgerms x hx, A.critical_model_germ ⟨x, hx⟩] with y h₁ h₂
    exact h₁.trans h₂
  have hvalues : f p ≠ f r := fun h => hpr (Subtype.ext (hinj p.property r.property h))
  rcases lt_or_gt_of_ne hvalues with hlt | hgt
  · obtain ⟨g, hg, hmg, hinjg, hcount, hcrit, hindices, hkeep, hlevel⟩ :=
      cancel_realized_higher_minimum_below_cut hf hm hinj A.toSurgeryWindows
        hV G hG hzero hdesc hmodels r p q hrzero hqone hlt hrq hqa v u hback hv hu
        (fun j hjq hjr hjp => hnoconnection j hjq hjp hjr)
    exact ⟨g, hg, hmg, hinjg, hcount,
      (fun x hx => ⟨((hcrit x).mp hx).1, hindices x hx⟩), hkeep, hlevel⟩
  · obtain ⟨g, hg, hmg, hinjg, hcount, hcrit, hindices, hkeep, hlevel⟩ :=
      cancel_realized_higher_minimum_below_cut hf hm hinj A.toSurgeryWindows
        hV G hG hzero hdesc hmodels p r q hpzero hqone hgt hpq hqa u v hback hu hv
        hnoconnection
    exact ⟨g, hg, hmg, hinjg, hcount,
      (fun x hx => ⟨((hcrit x).mp hx).1, hindices x hx⟩), hkeep, hlevel⟩

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
