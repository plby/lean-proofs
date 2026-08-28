import Wikipedia.HopfProblem.DegreeCollapsePositiveIndexCut

/-!
# An ordered index cut strictly below an untouched upper level

Only the critical points below the upper cut are ordered. The actual
upper surgery level of their last index-at-most-k point separates these
indices from the larger ones. Windows below the upper cut guarantee that
the selected level itself stays strictly below it.
-/

noncomputable section

open Set Function Filter Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M] {f : M → ℝ}

open Classical in
theorem AdaptedSurgeryWindows.exists_ordered_index_cut_below
    (S : AdaptedSurgeryWindows E f) (b : ℝ)
    (horder : ∀ p q : criticalPoints E f, f q < b → f p < f q →
      nativeMorseIndex E f p ≤ nativeMorseIndex E f q)
    (hcut : ∀ p : criticalPoints E f, f p < b → S.toSurgeryWindows.upper p < b)
    {k : ℕ} (q : criticalPoints E f) (hqb : f q < b) (hq : nativeMorseIndex E f q ≤ k) :
    ∃ a : ℝ, a < b ∧ (∀ y, f y = a → y ∉ criticalPoints E f) ∧ f q < a ∧
      (∀ z : criticalPoints E f, a ≤ f z → f z < b → k + 1 ≤ nativeMorseIndex E f z) ∧
      ∀ z : criticalPoints E f, f z ≤ a → nativeMorseIndex E f z ≤ k := by
  let _ := S.finite.fintype
  let K := Finset.univ.filter (fun z : criticalPoints E f =>
    f z < b ∧ nativeMorseIndex E f z ≤ k)
  have hqK : q ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hqb, hq⟩
  obtain ⟨r, hr, hmax⟩ := K.exists_max_image (fun z : criticalPoints E f => f z) ⟨q, hqK⟩
  have hrb : f r < b := (Finset.mem_filter.mp hr).2.1
  have hrk : nativeMorseIndex E f r ≤ k := (Finset.mem_filter.mp hr).2.2
  let a := S.toSurgeryWindows.upper r
  have hra : f r < a := S.toSurgeryWindows.value_lt_upper r
  refine ⟨a, hcut r hrb, (S.data r).upper_regular,
    (hmax q hqK).trans_lt hra, ?_, ?_⟩
  · intro z haz hzb
    by_contra hnot
    have hzK : z ∈ K := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzb, by omega⟩
    exact (not_lt_of_ge (haz.trans (hmax z hzK))) hra
  · intro z hza
    rcases lt_trichotomy (f z) (f r) with hzr | hzr | hrz
    · exact (horder z r hrb hzr).trans hrk
    · have he : z = r := Subtype.ext (S.distinct z.property r.property hzr)
      simpa only [he] using hrk
    · have he : z = r := Subtype.ext (S.toSurgeryWindows.isolated r z.val z.property
        ⟨(S.toSurgeryWindows.lower_lt_value r).le.trans hrz.le, hza⟩)
      simpa only [he] using hrk

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
