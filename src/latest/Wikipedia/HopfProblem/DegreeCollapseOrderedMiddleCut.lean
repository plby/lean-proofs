import Wikipedia.HopfProblem.DegreeCollapseOneThreeTradeAtCut

/-!
# The middle cut of an index-ordered Morse system

The upper surgery level of the last critical point of index at most two
is a regular cut separating those indices from all larger ones. This
constructs the cut needed for the one-to-three trade from index ordering.
-/

noncomputable section

open Set Function Filter Manifold ContinuousMap
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_ordered_index_cut
    (S : AdaptedSurgeryWindows E f)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    {k : ℕ} (q : criticalPoints E f) (hq : nativeMorseIndex E f q ≤ k) :
    ∃ a : ℝ, (∀ y, f y = a → y ∉ criticalPoints E f) ∧ f q < a ∧
      (∀ z : criticalPoints E f, a ≤ f z → k + 1 ≤ nativeMorseIndex E f z) ∧
      ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k := by
  let _ := S.finite.fintype
  let K := Finset.univ.filter (fun z : criticalPoints E f => nativeMorseIndex E f z ≤ k)
  have hqK : q ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image (fun z : criticalPoints E f => f z) ⟨q, hqK⟩
  have hrk : nativeMorseIndex E f r ≤ k := (Finset.mem_filter.mp hr).2
  let a := S.toSurgeryWindows.upper r
  have hra : f r < a := S.toSurgeryWindows.value_lt_upper r
  refine ⟨a, (S.data r).upper_regular, (hmax q hqK).trans_lt hra, ?_, ?_⟩
  · intro z haz
    by_contra hnot
    have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    exact (not_lt_of_ge (haz.trans (hmax z hzK))) hra
  · intro z hza
    rcases lt_trichotomy (f z) (f r) with hzr | hzr | hrz
    · exact (horder z r hzr).trans hrk
    · have he : z = r := Subtype.ext (S.distinct z.property r.property hzr)
      simpa only [he] using hrk
    · have he : z = r := Subtype.ext (S.toSurgeryWindows.isolated r z.val z.property
        ⟨(S.toSurgeryWindows.lower_lt_value r).le.trans hrz.le, hza⟩)
      simpa only [he] using hrk

variable [PathConnectedSpace M]

theorem exists_one_to_three_handle_trade_of_ordered_indices
    (S : AdaptedSurgeryWindows E f) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hm : IsMorse E f) (e : M ≃ₕ SixSphere) (hdim : Module.finrank ℝ E = 6)
    (horder : ∀ p q : criticalPoints E f, f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (m q : criticalPoints E f) (hm0 : nativeMorseIndex E f m = 0)
    (hq1 : nativeMorseIndex E f q = 1)
    (hminimum : ∀ z : criticalPoints E f, nativeMorseIndex E f z = 0 → z = m) :
    ∃ h : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ h ∧ IsMorse E h ∧
      InjOn h (criticalPoints E h) ∧ (criticalPoints E h).ncard = (criticalPoints E f).ncard ∧
      nativeMorseCount E h 1 + 1 = nativeMorseCount E f 1 ∧
      nativeMorseCount E h 3 = nativeMorseCount E f 3 + 1 ∧
      ∀ j, j ≠ 1 → j ≠ 3 → nativeMorseCount E h j = nativeMorseCount E f j := by
  obtain ⟨a, hreg, hqa, hhigh, hlow⟩ := S.exists_ordered_index_cut horder q
    (show nativeMorseIndex E f q ≤ 2 by omega)
  exact exists_one_to_three_handle_trade_at_cut S hf hm e hdim m q hm0 hq1 hminimum
    hreg hhigh hlow hqa

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
