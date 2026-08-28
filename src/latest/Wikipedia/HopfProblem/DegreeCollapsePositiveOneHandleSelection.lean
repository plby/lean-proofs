import Wikipedia.HopfProblem.DegreeCollapseCollaredSevenPositiveOrdering
import Wikipedia.HopfProblem.DegreeCollapseOrderedMinimumCount

/-!
# A positive birth forces an actual positive component-merging one-handle

Choose the last zero-handle, which lies above the regular cut if any
zero-handle does. If every later one-handle attached within one old path
component, connectedness of the final manifold would descend to the
upper sublevel of that birth. The actual zero-handle would then force its
old lower sublevel to be empty, contradicting a point below the cut.
The selected one-handle and its two attaching points are original native
Morse data; no abstract chain rearrangement is used.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology
open Wikipedia.SmoothSixDPoincare ManifoldMorse

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {E M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M] [PathConnectedSpace M]
  {f : M → ℝ}

theorem exists_native_merging_one_handle_above_cut (S : SurgeryWindows E f)
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) (a : ℝ)
    (x₀ : {x : M // f x ≤ a})
    (hcut : ∀ p : criticalPoints E f, a < f p → a < S.lower p)
    (p₀ : criticalPoints E f) (hp₀ : a < f p₀) (hzero₀ : nativeMorseIndex E f p₀ = 0) :
    ∃ q : criticalPoints E f, a < f q ∧ nativeMorseIndex E f q = 1 ∧
      ∃ u v, ¬Joined ((S.data q).coreBoundaryMap u) ((S.data q).coreBoundaryMap v) := by
  classical
  by_contra hnot
  let K : Finset (Fin S.count) :=
    Finset.univ.filter (fun i => nativeMorseIndex E f (S.point i) = 0)
  have hp₀K : S.point.symm p₀ ∈ K := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa using hzero₀⟩
  have hK : K.Nonempty := ⟨S.point.symm p₀, hp₀K⟩
  let j : Fin S.count := K.max' hK
  have hjzero : nativeMorseIndex E f (S.point j) = 0 :=
    (Finset.mem_filter.mp (K.max'_mem hK)).2
  have hmax (i : Fin S.count) (hi : nativeMorseIndex E f (S.point i) = 0) : i ≤ j :=
    K.le_max' i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩)
  have hpj : S.point.symm p₀ ≤ j := K.le_max' _ hp₀K
  have hjpositive : a < f (S.point j) := by
    have hle := S.point_strictMono.monotone hpj
    rw [S.point.apply_symm_apply] at hle
    exact hp₀.trans_le hle
  have htail (i : Fin S.count) (hji : j.val < i.val)
      (hupper : PathConnectedSpace {x : M // f x ≤ S.upper (S.point i)}) :
      PathConnectedSpace {x : M // f x ≤ S.lower (S.point i)} := by
    let : PathConnectedSpace
        {x : M // f x ≤ f (S.point i) + (S.data (S.point i)).radius ^ 2} := hupper
    have hiPositive : a < f (S.point i) := hjpositive.trans (S.point_strictMono hji)
    have hne : nativeMorseIndex E f (S.point i) ≠ 0 := by
      intro hi
      have hm : i.val ≤ j.val := hmax i hi
      omega
    have heq := nativeMorseIndex_eq_chart (S.data (S.point i)).chart
    by_cases hone : nativeMorseIndex E f (S.point i) = 1
    · have hjoined : ∀ u v,
          Joined ((S.data (S.point i)).coreBoundaryMap u)
            ((S.data (S.point i)).coreBoundaryMap v) := by
        intro u v
        by_contra huv
        exact hnot ⟨S.point i, hiPositive, hone, u, v, huv⟩
      obtain ⟨z, hz⟩ := native_attaching_component_of_pairwise_joined
        (S.data (S.point i)) (by omega) hjoined
      exact native_lower_pathConnected_of_attaching_component (S.data (S.point i))
        hf.continuous z hz
    · exact native_lower_pathConnected_of_upper (S.data (S.point i)) hf.continuous (by omega)
  let : PathConnectedSpace
      {x : M // f x ≤ f (S.point j) + (S.data (S.point j)).radius ^ 2} :=
    ordered_upper_pathConnected_of_later_transfers S hf j htail
  let : IsEmpty {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2} :=
    native_zero_handle_lower_isEmpty (S.data (S.point j)) hf.continuous
      ((nativeMorseIndex_eq_chart (S.data (S.point j)).chart).symm.trans hjzero)
  exact isEmptyElim (⟨x₀.val, x₀.property.trans (hcut (S.point j) hjpositive).le⟩ :
    {x : M // f x ≤ f (S.point j) - (S.data (S.point j)).radius ^ 2})

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

namespace Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation

open NoExoticSixSphere GLOrthonormalization MorseCancellation

variable {B : Type} [TopologicalSpace B] [Nonempty B] {S : CollaredSevenState B}

theorem exists_positive_merging_one_handle (P : S.ExcellentMorsePresentation)
    (p : criticalPoints (Vector 7) P.function) (hp : 0 < P.function p)
    (hzero : nativeMorseIndex (Vector 7) P.function p = 0) :
    ∃ A : AdaptedSurgeryWindows (Vector 7) P.function,
      (∀ r : criticalPoints (Vector 7) P.function, 0 < P.function r →
        0 < A.toSurgeryWindows.lower r) ∧
      ∃ q : criticalPoints (Vector 7) P.function,
        0 < P.function q ∧ nativeMorseIndex (Vector 7) P.function q = 1 ∧
        ∃ u v, ¬Joined ((A.data q).coreBoundaryMap u) ((A.data q).coreBoundaryMap v) := by
  obtain ⟨A₀⟩ := nonempty_adaptedSurgeryWindows P.smooth P.morse P.distinct
  obtain ⟨A, _, _, _, _, hcut⟩ := A₀.exists_same_flow_windows_avoiding_level P.smooth P.morse
    (RegularTimeMorse.regular_zero_not_critical P.regular)
  let b : B := Classical.choice (inferInstance : Nonempty B)
  let x := (S.collar.zeroPoint b).val
  have hx : P.function x = 0 := (P.zero_iff x).mpr (S.collar.zeroPoint_time b)
  obtain ⟨q, hq, hqone, u, v, huv⟩ := exists_native_merging_one_handle_above_cut
    A.toSurgeryWindows P.smooth 0 ⟨x, hx.le⟩ hcut p hp hzero
  exact ⟨A, hcut, q, hq, hqone, u, v, huv⟩

end Wikipedia.HopfProblem.DegreeCollapse.CollaredSevenState.ExcellentMorsePresentation
