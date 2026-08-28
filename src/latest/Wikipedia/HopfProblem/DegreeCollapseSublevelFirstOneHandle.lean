import Wikipedia.HopfProblem.DegreeCollapseSublevelIndexCut
import Wikipedia.HopfProblem.DegreeCollapseFirstOneHandleBranches

/-!
# The first index-one handle below a cut has actual minimum branches

Ordering only below the cut selects an index-one point with no earlier
positive-index critical point. If the index-zero point below the cut is
unique, each original attaching direction converges to that very point.
Critical points at or above the cut require no ordering or index bounds.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

omit [FiniteDimensional ℝ E] [T2Space M] [CompactSpace M] in
theorem AdaptedSurgeryWindows.exists_first_index_one_below_cut
    (S : AdaptedSurgeryWindows E f) (b : ℝ)
    (horder : ∀ p q : criticalPoints E f, f q < b → f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (q₀ : criticalPoints E f) (hq₀b : f q₀ < b) (hq₀ : nativeMorseIndex E f q₀ = 1) :
    ∃ q : criticalPoints E f, f q < b ∧ nativeMorseIndex E f q = 1 ∧
      ∀ p : criticalPoints E f, f p < f q → nativeMorseIndex E f p = 0 := by
  classical
  let _ := S.finite.fintype
  let K := Finset.univ.filter (fun p : criticalPoints E f =>
    f p < b ∧ nativeMorseIndex E f p = 1)
  have hq₀K : q₀ ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq₀b, hq₀⟩
  obtain ⟨q, hqK, hmin⟩ := K.exists_min_image (fun p : criticalPoints E f => f p) ⟨q₀, hq₀K⟩
  obtain ⟨hqb, hq⟩ := (Finset.mem_filter.mp hqK).2
  refine ⟨q, hqb, hq, ?_⟩
  intro p hp
  have hle := horder p q hqb hp
  have hne : nativeMorseIndex E f p ≠ 1 := by
    intro h
    have hpK : p ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp.trans hqb, h⟩
    exact (not_le_of_gt hp) (hmin p hpK)
  omega

theorem AdaptedSurgeryWindows.first_one_branches_to_unique_minimum_below_cut
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    {b : ℝ} (p q : criticalPoints E f) (hqb : f q < b)
    (hbefore : ∀ r : criticalPoints E f, f r < f q → nativeMorseIndex E f r = 0)
    (hunique : ∀ r : criticalPoints E f, f r < b → nativeMorseIndex E f r = 0 → r = p)
    (u : sphere (0 : (S.data q).chart.NegativeCoordinates) 1) :
    Tendsto (fun t => S.flow t ((S.data q).surgery.attachingSphere u).val) atTop (𝓝 p.val) := by
  obtain ⟨r, hr, hrq, hlim⟩ := S.lower_level_forward_minimum hf q hbefore
    ((S.data q).surgery.attachingSphere u)
  exact hunique r ((hrq.trans (S.toSurgeryWindows.lower_lt_value q)).trans hqb) hr ▸ hlim

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
