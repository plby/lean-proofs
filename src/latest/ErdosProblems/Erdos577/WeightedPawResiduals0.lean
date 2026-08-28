import ErdosProblems.Erdos577.WeightedPawMasks0

/-! Exact row and diagonal certificates for weighted source patterns (9)–(20). -/

namespace Erdos577.WeightedPaw.D0

private theorem residual_0 : Classified 0 15621 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_1 : Classified 0 15625 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_2 : Classified 0 15878 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_3 : Classified 0 15882 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_4 : Classified 0 22277 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_5 : Classified 0 23813 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_6 : Classified 0 27395 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_7 : Classified 0 27402 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_8 : Classified 0 27909 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_9 : Classified 0 27916 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 0 29957 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 0 30979 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_12 : Classified 0 30981 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_13 : Classified 0 31749 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_14 : Classified 0 31750 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_15 : Classified 0 32001 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_16 : Classified 0 32004 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_17 : Classified 0 32005 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_18 : Classified 0 38659 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_19 : Classified 0 38661 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_20 : Classified 0 40458 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_21 : Classified 0 40460 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_22 : Classified 0 43786 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_23 : Classified 0 44554 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_24 : Classified 0 46595 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_25 : Classified 0 46602 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_26 : Classified 0 47626 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_27 : Classified 0 48137 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_28 : Classified 0 48138 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_29 : Classified 0 48642 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_30 : Classified 0 48648 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_31 : Classified 0 48650 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_32 : Classified 0 50949 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_33 : Classified 0 50950 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_34 : Classified 0 51977 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_35 : Classified 0 51978 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_36 : Classified 0 54021 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_37 : Classified 0 54025 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 0 54533 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_39 : Classified 0 54789 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_40 : Classified 0 54796 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_41 : Classified 0 55041 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_42 : Classified 0 55044 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_43 : Classified 0 55045 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_44 : Classified 0 58118 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_45 : Classified 0 58122 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_46 : Classified 0 59658 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_47 : Classified 0 59660 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_48 : Classified 0 59914 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_49 : Classified 0 60162 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_50 : Classified 0 60168 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_51 : Classified 0 60170 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private def residual_group_0 : List ℕ := [
  15621, 15625, 15878, 15882, 22277, 23813, 27395, 27402,
  27909, 27916, 29957, 30979, 30981, 31749, 31750, 32001,
  32004, 32005, 38659, 38661, 40458, 40460, 43786, 44554,
  46595, 46602, 47626, 48137, 48138, 48642, 48648, 48650]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) :
    Classified 0 m := by
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
  50949, 50950, 51977, 51978, 54021, 54025, 54533, 54789,
  54796, 55041, 55044, 55045, 58118, 58122, 59658, 59660,
  59914, 60162, 60168, 60170]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) :
    Classified 0 m := by
  simp only [residual_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact residual_42
  · exact residual_43
  · exact residual_44
  · exact residual_45
  · exact residual_46
  · exact residual_47
  · exact residual_48
  · exact residual_49
  · exact residual_50
  · exact residual_51

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) :
    Classified 0 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    residual_group_0, residual_group_1] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl
  · exact residual_group_0_sound hm
  · exact residual_group_1_sound hm

end Erdos577.WeightedPaw.D0
