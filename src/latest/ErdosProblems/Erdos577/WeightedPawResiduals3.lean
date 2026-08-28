import ErdosProblems.Erdos577.WeightedPawMasks3

/-! Exact row and diagonal certificates for weighted source patterns (9)–(20). -/

namespace Erdos577.WeightedPaw.D3

private theorem residual_0 : Classified 3 1807 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_1 : Classified 3 1935 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_2 : Classified 3 2831 := by
  refine ⟨false, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_3 : Classified 3 2895 := by
  refine ⟨false, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_4 : Classified 3 3343 := by
  refine ⟨false, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_5 : Classified 3 3375 := by
  refine ⟨false, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_6 : Classified 3 3599 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_7 : Classified 3 3615 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_8 : Classified 3 3847 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_9 : Classified 3 3851 := by
  refine ⟨false, ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 3 3853 := by
  refine ⟨false, ⟨![0, 2, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 3 3854 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_12 : Classified 3 3855 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_13 : Classified 3 7694 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_14 : Classified 3 11533 := by
  refine ⟨false, ⟨![0, 2, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_15 : Classified 3 19211 := by
  refine ⟨false, ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_16 : Classified 3 28687 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_17 : Classified 3 28815 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_18 : Classified 3 30472 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_19 : Classified 3 30600 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_20 : Classified 3 30727 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_21 : Classified 3 34567 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_22 : Classified 3 45071 := by
  refine ⟨true, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_23 : Classified 3 45135 := by
  refine ⟨true, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_24 : Classified 3 46091 := by
  refine ⟨true, ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_25 : Classified 3 47876 := by
  refine ⟨false, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_26 : Classified 3 47940 := by
  refine ⟨false, ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_27 : Classified 3 53263 := by
  refine ⟨true, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_28 : Classified 3 53295 := by
  refine ⟨true, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_29 : Classified 3 53773 := by
  refine ⟨true, ⟨![0, 2, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_30 : Classified 3 56578 := by
  refine ⟨false, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_31 : Classified 3 56610 := by
  refine ⟨false, ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_32 : Classified 3 57359 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_33 : Classified 3 57375 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_34 : Classified 3 57614 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_35 : Classified 3 60929 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_36 : Classified 3 60945 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_37 : Classified 3 61447 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 3 61451 := by
  refine ⟨true, ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_39 : Classified 3 61453 := by
  refine ⟨true, ⟨![0, 2, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_40 : Classified 3 61454 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_41 : Classified 3 61455 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private def residual_group_0 : List ℕ := [
  1807, 1935, 2831, 2895, 3343, 3375, 3599, 3615,
  3847, 3851, 3853, 3854, 3855, 7694, 11533, 19211,
  28687, 28815, 30472, 30600, 30727, 34567, 45071, 45135,
  46091, 47876, 47940, 53263, 53295, 53773, 56578, 56610]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) :
    Classified 3 m := by
  simp only [residual_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_0
  · exact residual_1
  · exact residual_2
  · exact residual_3
  · exact residual_4
  · exact residual_5
  · exact residual_6
  · exact residual_7
  · exact residual_8
  · exact residual_9
  · exact residual_10
  · exact residual_11
  · exact residual_12
  · exact residual_13
  · exact residual_14
  · exact residual_15
  · exact residual_16
  · exact residual_17
  · exact residual_18
  · exact residual_19
  · exact residual_20
  · exact residual_21
  · exact residual_22
  · exact residual_23
  · exact residual_24
  · exact residual_25
  · exact residual_26
  · exact residual_27
  · exact residual_28
  · exact residual_29
  · exact residual_30
  · exact residual_31

private def residual_group_1 : List ℕ := [
  57359, 57375, 57614, 60929, 60945, 61447, 61451, 61453,
  61454, 61455]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) :
    Classified 3 m := by
  simp only [residual_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_32
  · exact residual_33
  · exact residual_34
  · exact residual_35
  · exact residual_36
  · exact residual_37
  · exact residual_38
  · exact residual_39
  · exact residual_40
  · exact residual_41

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) :
    Classified 3 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    residual_group_0, residual_group_1] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact residual_group_0_sound hm
  · exact residual_group_1_sound hm

end Erdos577.WeightedPaw.D3
