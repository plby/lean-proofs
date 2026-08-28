import ErdosProblems.Erdos577.FirstPawMasks3

/-! Exact cyclic row and diagonal certificates for source patterns (3)–(8). -/

namespace Erdos577.FirstPaw.D3

private theorem residual_0 : Classified 3 4081 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_1 : Classified 3 4082 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_2 : Classified 3 4084 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_3 : Classified 3 4088 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_4 : Classified 3 5107 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_5 : Classified 3 5621 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_6 : Classified 3 6649 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_7 : Classified 3 9203 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_8 : Classified 3 9974 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_9 : Classified 3 11002 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_10 : Classified 3 12787 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_11 : Classified 3 13043 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_12 : Classified 3 13171 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_13 : Classified 3 13235 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_14 : Classified 3 13267 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_15 : Classified 3 13283 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_16 : Classified 3 13297 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_17 : Classified 3 13298 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_18 : Classified 3 13299 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 2, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_19 : Classified 3 17909 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_20 : Classified 3 18166 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_21 : Classified 3 19708 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_22 : Classified 3 20981 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_23 : Classified 3 21749 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_24 : Classified 3 21877 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_25 : Classified 3 21941 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_26 : Classified 3 21973 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_27 : Classified 3 21989 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_28 : Classified 3 22001 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_29 : Classified 3 22004 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_30 : Classified 3 22005 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_31 : Classified 3 25334 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_32 : Classified 3 25846 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_33 : Classified 3 26230 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_34 : Classified 3 26294 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_35 : Classified 3 26326 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_36 : Classified 3 26342 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_37 : Classified 3 26354 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_38 : Classified 3 26356 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_39 : Classified 3 26358 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_40 : Classified 3 35321 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_41 : Classified 3 35578 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_42 : Classified 3 36092 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_43 : Classified 3 37369 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_44 : Classified 3 39161 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_45 : Classified 3 39289 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_46 : Classified 3 39353 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_47 : Classified 3 39385 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_48 : Classified 3 39401 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_49 : Classified 3 39409 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_50 : Classified 3 39416 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_51 : Classified 3 39417 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_52 : Classified 3 41722 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_53 : Classified 3 43258 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_54 : Classified 3 43642 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_55 : Classified 3 43706 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_56 : Classified 3 43738 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_57 : Classified 3 43754 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_58 : Classified 3 43762 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_59 : Classified 3 43768 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_60 : Classified 3 43770 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_61 : Classified 3 50428 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_62 : Classified 3 51452 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_63 : Classified 3 52348 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_64 : Classified 3 52412 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_65 : Classified 3 52444 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_66 : Classified 3 52460 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_67 : Classified 3 52468 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_68 : Classified 3 52472 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_69 : Classified 3 52476 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 0, 3, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_70 : Classified 3 61681 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_71 : Classified 3 61682 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_72 : Classified 3 61684 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 0, 1, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_73 : Classified 3 61688 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private def residual_group_0 : List ℕ := [
  4081, 4082, 4084, 4088, 5107, 5621, 6649, 9203,
  9974, 11002, 12787, 13043, 13171, 13235, 13267, 13283]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) : Classified 3 m := by
  simp only [residual_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_1 : List ℕ := [
  13297, 13298, 13299, 17909, 18166, 19708, 20981, 21749,
  21877, 21941, 21973, 21989, 22001, 22004, 22005, 25334]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) : Classified 3 m := by
  simp only [residual_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_2 : List ℕ := [
  25846, 26230, 26294, 26326, 26342, 26354, 26356, 26358,
  35321, 35578, 36092, 37369, 39161, 39289, 39353, 39385]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) : Classified 3 m := by
  simp only [residual_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_3 : List ℕ := [
  39401, 39409, 39416, 39417, 41722, 43258, 43642, 43706,
  43738, 43754, 43762, 43768, 43770, 50428, 51452, 52348]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) : Classified 3 m := by
  simp only [residual_group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_48
  · exact residual_49
  · exact residual_50
  · exact residual_51
  · exact residual_52
  · exact residual_53
  · exact residual_54
  · exact residual_55
  · exact residual_56
  · exact residual_57
  · exact residual_58
  · exact residual_59
  · exact residual_60
  · exact residual_61
  · exact residual_62
  · exact residual_63

private def residual_group_4 : List ℕ := [
  52412, 52444, 52460, 52468, 52472, 52476, 61681, 61682,
  61684, 61688]

private theorem residual_group_4_sound {m : ℕ} (h : m ∈ residual_group_4) : Classified 3 m := by
  simp only [residual_group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_64
  · exact residual_65
  · exact residual_66
  · exact residual_67
  · exact residual_68
  · exact residual_69
  · exact residual_70
  · exact residual_71
  · exact residual_72
  · exact residual_73

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) : Classified 3 m := by
  have hg :
      m ∈ residual_group_0 ∨
      m ∈ residual_group_1 ∨
      m ∈ residual_group_2 ∨
      m ∈ residual_group_3 ∨
      m ∈ residual_group_4 := by
    change m ∈
      residual_group_0 ++
      residual_group_1 ++
      residual_group_2 ++
      residual_group_3 ++
      residual_group_4 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg
  · exact residual_group_0_sound hg
  · exact residual_group_1_sound hg
  · exact residual_group_2_sound hg
  · exact residual_group_3_sound hg
  · exact residual_group_4_sound hg

end Erdos577.FirstPaw.D3
