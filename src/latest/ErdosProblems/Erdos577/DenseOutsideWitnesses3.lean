import ErdosProblems.Erdos577.DenseOutsideMasks3

/-! Explicit factors or strict edge gains for diagonal mask 3. -/

namespace Erdos577.DenseOutside.D3

open Finset Unattached

private theorem witness_0 : Positive 3 278 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_1 : Positive 3 282 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_2 : Positive 3 284 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_3 : Positive 3 549 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_4 : Positive 3 553 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_5 : Positive 3 556 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 3 1091 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_7 : Positive 3 1097 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_8 : Positive 3 1098 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_9 : Positive 3 2179 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_10 : Positive 3 2181 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_11 : Positive 3 2182 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_12 : Positive 3 4118 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_13 : Positive 3 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_14 : Positive 3 4124 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_15 : Positive 3 4358 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_16 : Positive 3 4362 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_17 : Positive 3 4364 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_18 : Positive 3 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_19 : Positive 3 8233 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_20 : Positive 3 8236 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_21 : Positive 3 8709 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_22 : Positive 3 8713 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_23 : Positive 3 8716 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_24 : Positive 3 16451 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_25 : Positive 3 16457 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_26 : Positive 3 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_27 : Positive 3 17411 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_28 : Positive 3 17417 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_29 : Positive 3 17418 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_30 : Positive 3 32899 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_31 : Positive 3 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_32 : Positive 3 32902 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_33 : Positive 3 34819 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_34 : Positive 3 34821 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_35 : Positive 3 34822 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_36 : Positive 3 4812 := by
  left
  refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_37 : Positive 3 5290 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_38 : Positive 3 5766 := by
  left
  refine ⟨{0, 5, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_39 : Positive 3 6246 := by
  left
  refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_40 : Positive 3 6730 := by
  left
  refine ⟨{0, 5, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_41 : Positive 3 7212 := by
  left
  refine ⟨{0, 6, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_42 : Positive 3 8652 := by
  left
  refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_43 : Positive 3 9369 := by
  left
  refine ⟨{0, 4, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_44 : Positive 3 9605 := by
  left
  refine ⟨{0, 4, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_45 : Positive 3 10325 := by
  left
  refine ⟨{0, 4, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_46 : Positive 3 10569 := by
  left
  refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_47 : Positive 3 11292 := by
  left
  refine ⟨{0, 6, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_48 : Positive 3 13443 := by
  left
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_49 : Positive 3 14403 := by
  left
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_50 : Positive 3 16810 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_51 : Positive 3 17049 := by
  left
  refine ⟨{0, 4, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_52 : Positive 3 17283 := by
  left
  refine ⟨{0, 4, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_53 : Positive 3 18483 := by
  left
  refine ⟨{0, 4, 1, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_54 : Positive 3 18729 := by
  left
  refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_55 : Positive 3 18970 := by
  left
  refine ⟨{0, 5, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_56 : Positive 3 21125 := by
  left
  refine ⟨{0, 4, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_57 : Positive 3 22565 := by
  left
  refine ⟨{0, 4, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_58 : Positive 3 24966 := by
  left
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_59 : Positive 3 26646 := by
  left
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_60 : Positive 3 33126 := by
  left
  refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_61 : Positive 3 33365 := by
  left
  refine ⟨{0, 4, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_62 : Positive 3 33603 := by
  left
  refine ⟨{0, 4, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_63 : Positive 3 33843 := by
  left
  refine ⟨{0, 4, 1, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_64 : Positive 3 34085 := by
  left
  refine ⟨{0, 4, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_65 : Positive 3 34326 := by
  left
  refine ⟨{0, 5, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_66 : Positive 3 37449 := by
  left
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_67 : Positive 3 37929 := by
  left
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_68 : Positive 3 41290 := by
  left
  refine ⟨{0, 5, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_69 : Positive 3 42010 := by
  left
  refine ⟨{0, 5, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_70 : Positive 3 49452 := by
  left
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_71 : Positive 3 49692 := by
  left
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private def group_0 : List ℕ := [
  278, 282, 284, 549, 553, 556, 1091, 1097,
  1098, 2179, 2181, 2182, 4118, 4122, 4124, 4358]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) :
    Positive 3 m := by
  simp only [group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_0
  · exact witness_1
  · exact witness_2
  · exact witness_3
  · exact witness_4
  · exact witness_5
  · exact witness_6
  · exact witness_7
  · exact witness_8
  · exact witness_9
  · exact witness_10
  · exact witness_11
  · exact witness_12
  · exact witness_13
  · exact witness_14
  · exact witness_15

private def group_1 : List ℕ := [
  4362, 4364, 8229, 8233, 8236, 8709, 8713, 8716,
  16451, 16457, 16458, 17411, 17417, 17418, 32899, 32901]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) :
    Positive 3 m := by
  simp only [group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_16
  · exact witness_17
  · exact witness_18
  · exact witness_19
  · exact witness_20
  · exact witness_21
  · exact witness_22
  · exact witness_23
  · exact witness_24
  · exact witness_25
  · exact witness_26
  · exact witness_27
  · exact witness_28
  · exact witness_29
  · exact witness_30
  · exact witness_31

private def group_2 : List ℕ := [
  32902, 34819, 34821, 34822, 4812, 5290, 5766, 6246,
  6730, 7212, 8652, 9369, 9605, 10325, 10569, 11292]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) :
    Positive 3 m := by
  simp only [group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_32
  · exact witness_33
  · exact witness_34
  · exact witness_35
  · exact witness_36
  · exact witness_37
  · exact witness_38
  · exact witness_39
  · exact witness_40
  · exact witness_41
  · exact witness_42
  · exact witness_43
  · exact witness_44
  · exact witness_45
  · exact witness_46
  · exact witness_47

private def group_3 : List ℕ := [
  13443, 14403, 16810, 17049, 17283, 18483, 18729, 18970,
  21125, 22565, 24966, 26646, 33126, 33365, 33603, 33843]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) :
    Positive 3 m := by
  simp only [group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_48
  · exact witness_49
  · exact witness_50
  · exact witness_51
  · exact witness_52
  · exact witness_53
  · exact witness_54
  · exact witness_55
  · exact witness_56
  · exact witness_57
  · exact witness_58
  · exact witness_59
  · exact witness_60
  · exact witness_61
  · exact witness_62
  · exact witness_63

private def group_4 : List ℕ := [
  34085, 34326, 37449, 37929, 41290, 42010, 49452, 49692]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) :
    Positive 3 m := by
  simp only [group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_64
  · exact witness_65
  · exact witness_66
  · exact witness_67
  · exact witness_68
  · exact witness_69
  · exact witness_70
  · exact witness_71

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 3 m := by
  have hg :
      m ∈ group_0 ∨
      m ∈ group_1 ∨
      m ∈ group_2 ∨
      m ∈ group_3 ∨
      m ∈ group_4 := by
    change m ∈
      group_0 ++
      group_1 ++
      group_2 ++
      group_3 ++
      group_4 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg
  · exact group_sound_0 hg
  · exact group_sound_1 hg
  · exact group_sound_2 hg
  · exact group_sound_3 hg
  · exact group_sound_4 hg

theorem finite_positive (m : Fin 65536) (hz : 2 ≤ terminalCount m.val)
    (ht : 9 ≤ triangleCount m.val) : Positive 3 m.val := by
  have hc := coverage m hz ht
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.DenseOutside.D3
