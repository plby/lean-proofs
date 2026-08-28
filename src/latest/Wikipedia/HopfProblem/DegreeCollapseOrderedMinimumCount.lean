import Wikipedia.HopfProblem.DegreeCollapseOrderedSublevelComponents
import Wikipedia.HopfProblem.DegreeCollapseZeroHandleComponents
import Wikipedia.HopfProblem.DegreeCollapseNativeOrderedLevelContractions
import Wikipedia.HopfProblem.DegreeCollapseNativeAttachingComponents

/-!
# No index-one critical points implies exactly one minimum

Choose the last actual index-zero critical point. Every later handle has
index at least two, so its upper sublevel is connected by reverse induction.
The zero-handle theorem forces its lower sublevel to be empty. Thus this
point is first and is the only minimum. No ordering by Morse index is needed.
-/

noncomputable section

open Set Function ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

open Wikipedia.SmoothSixDPoincare ManifoldMorse

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  {f : M → ℝ} (S : SurgeryWindows E f)

include S

theorem native_minimum_count_one_of_one_handle_components
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hcomponents : ∀ p : criticalPoints E f, nativeMorseIndex E f p = 1 →
      ∃ a : {z : M // f z ≤ f p - (S.data p).radius ^ 2},
        ∀ u, Joined ((S.data p).coreBoundaryMap u) a) :
    nativeMorseCount E f 0 = 1 := by
  classical
  have hn := S.count_pos hf
  have hfirst : nativeMorseIndex E f (S.first hn) = 0 :=
    (nativeMorseIndex_eq_chart (S.data (S.first hn)).chart).trans (S.first_index_zero hf hn)
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hK : K.Nonempty := ⟨⟨0, hn⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hfirst⟩⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 :=
    (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have htail (i : Fin S.count) (hji : j.val < i.val)
      (hupper : PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)}) :
      PathConnectedSpace {x : M // f x ≤ S.lower (S.point i)} := by
    let : PathConnectedSpace
        {x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2} := hupper
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · obtain ⟨a, ha⟩ := hcomponents (S.point i) hone
      exact native_lower_pathConnected_of_attaching_component (S.data (S.point i))
        hf.continuous a ha
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace
      {x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2} :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2} :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  have hjfirst : j.val = 0 := by
    by_contra hj
    have hlt : (⟨0, hn⟩ : Fin S.count) < j := by change 0 < j.val; omega
    have hbelow : f (S.first hn) ≤ S.lower (S.point j) :=
      (S.value_lt_upper (S.first hn)).le.trans (S.ordered_windows _ _ hlt).le
    exact isEmptyElim (⟨S.first hn, hbelow⟩ :
      {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2})
  have hset : {x : M | x ∈ criticalPoints E f ∧ nativeMorseIndex E f x = 0} =
      {(S.first hn).val} := by
    ext x
    constructor
    · rintro ⟨hx, hi⟩
      obtain ⟨i, he⟩ := S.point.surjective ⟨x, hx⟩
      have hi0 : nativeMorseIndex E f (S.point i) = 0 := by simpa only [he] using hi
      have hle : i.val ≤ j.val := hmax i hi0
      have hi0' : i.val = 0 := by omega
      have hip : S.point i = S.first hn := congrArg S.point (Fin.ext hi0')
      exact mem_singleton_iff.mpr (congrArg Subtype.val (he.symm.trans hip))
    · intro hx
      rw [mem_singleton_iff] at hx
      exact hx ▸ ⟨(S.first hn).property, hfirst⟩
  exact Set.ncard_eq_one.mpr ⟨(S.first hn).val, hset⟩

theorem native_minimum_count_one_of_no_index_one
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f)
    (hone : ∀ p : criticalPoints E f, nativeMorseIndex E f p ≠ 1) :
    nativeMorseCount E f 0 = 1 :=
  native_minimum_count_one_of_one_handle_components S hf
    (fun p hp => False.elim (hone p hp))

theorem native_minimum_count_one_of_index_one_count_zero
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (hone : nativeMorseCount E f 1 = 0) :
    nativeMorseCount E f 0 = 1 :=
  native_minimum_count_one_of_no_index_one S hf
    (fun p => native_index_one_excluded S hone p p.property)

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
