import ErdosProblems.Erdos577.PathLossMasks1

/-! Explicit factors or five-edge reductions for diagonal mask 1. -/

namespace Erdos577.PathLoss.D1

open Finset

private theorem witness_0 : Positive 1 546 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {4, 6, 7}
    block := {0, 1, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_1 : Positive 1 2184 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {4, 5, 6}
    block := {0, 1, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_2 : Positive 1 8736 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_3 : Positive 1 34944 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_4 : Positive 1 549 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 5}
    block := {0, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_5 : Positive 1 553 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 5}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_6 : Positive 1 556 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 5}
    block := {0, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_7 : Positive 1 904 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 7}
    block := {2, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_8 : Positive 1 1314 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 5}
    block := {2, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_9 : Positive 1 1416 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 7}
    block := {2, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_10 : Positive 1 1672 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 7}
    block := {2, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_11 : Positive 1 2179 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 7}
    block := {0, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_12 : Positive 1 2181 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 7}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_13 : Positive 1 2182 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 7}
    block := {0, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_14 : Positive 1 2338 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 5}
    block := {2, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_15 : Positive 1 3106 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 5}
    block := {2, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_16 : Positive 1 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_17 : Positive 1 4680 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_18 : Positive 1 4740 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_19 : Positive 1 6180 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_20 : Positive 1 6210 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_21 : Positive 1 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_22 : Positive 1 8233 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_23 : Positive 1 8236 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_24 : Positive 1 8520 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_25 : Positive 1 8580 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_26 : Positive 1 8709 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 5}
    block := {0, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_27 : Positive 1 8713 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 5}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_28 : Positive 1 8716 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 5}
    block := {0, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_29 : Positive 1 8784 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_30 : Positive 1 8848 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_31 : Positive 1 8896 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_32 : Positive 1 9240 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_33 : Positive 1 9345 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_34 : Positive 1 12424 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 7}
    block := {3, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_35 : Positive 1 14344 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_36 : Positive 1 14464 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_37 : Positive 1 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_38 : Positive 1 16920 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_39 : Positive 1 17025 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_40 : Positive 1 18450 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_41 : Positive 1 18465 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_42 : Positive 1 20514 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 5}
    block := {3, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_43 : Positive 1 20616 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 7}
    block := {3, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_44 : Positive 1 20994 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_45 : Positive 1 21024 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_46 : Positive 1 22536 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_47 : Positive 1 22656 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_48 : Positive 1 24712 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 7}
    block := {3, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_49 : Positive 1 26632 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_50 : Positive 1 26752 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_51 : Positive 1 32899 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_52 : Positive 1 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_53 : Positive 1 32902 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_54 : Positive 1 33060 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_55 : Positive 1 33090 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_56 : Positive 1 33810 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_57 : Positive 1 33825 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_58 : Positive 1 34819 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 7}
    block := {0, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_59 : Positive 1 34821 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 7}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_60 : Positive 1 34822 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 7}
    block := {0, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_61 : Positive 1 34864 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_62 : Positive 1 34896 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_63 : Positive 1 34912 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_64 : Positive 1 36898 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 5}
    block := {3, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_65 : Positive 1 37378 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_66 : Positive 1 37408 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_67 : Positive 1 41217 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_68 : Positive 1 41988 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_69 : Positive 1 49186 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 5}
    block := {3, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_70 : Positive 1 49666 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_71 : Positive 1 49696 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_72 : Positive 1 286 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 4}
    block := {0, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_73 : Positive 1 316 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_74 : Positive 1 406 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_75 : Positive 1 796 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_76 : Positive 1 844 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 5}
    block := {0, 1, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_77 : Positive 1 964 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 5}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_78 : Positive 1 1099 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 6}
    block := {0, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_79 : Positive 1 1129 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_80 : Positive 1 1219 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_81 : Positive 1 1561 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 5, 6}
    block := {0, 1, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_82 : Positive 1 1609 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_83 : Positive 1 1681 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 5, 6}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_84 : Positive 1 2326 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_85 : Positive 1 2374 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 7}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_86 : Positive 1 2404 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 7}
    block := {0, 1, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_87 : Positive 1 2884 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 6}
    block := {2, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_88 : Positive 1 3091 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 6, 7}
    block := {0, 1, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_89 : Positive 1 3121 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 6, 7}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_90 : Positive 1 3139 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_91 : Positive 1 3601 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 4}
    block := {2, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_92 : Positive 1 4366 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 4}
    block := {0, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_93 : Positive 1 4374 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_94 : Positive 1 4380 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_95 : Positive 1 4390 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 4}
    block := {0, 1, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_96 : Positive 1 4422 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 4}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_97 : Positive 1 4428 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 4}
    block := {0, 1, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_98 : Positive 1 4450 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 4}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_99 : Positive 1 4452 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 4}
    block := {0, 1, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_100 : Positive 1 4492 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 4}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_101 : Positive 1 4548 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 4}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_102 : Positive 1 4552 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 4}
    block := {0, 1, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_103 : Positive 1 4576 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 4}
    block := {1, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_104 : Positive 1 4876 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_105 : Positive 1 4932 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 6}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_106 : Positive 1 5056 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_107 : Positive 1 6406 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_108 : Positive 1 6468 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_109 : Positive 1 6496 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_110 : Positive 1 9028 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 6}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_111 : Positive 1 9745 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 4}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_112 : Positive 1 12364 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 5}
    block := {0, 1, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_113 : Positive 1 12484 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 5}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_114 : Positive 1 12556 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_115 : Positive 1 12612 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 6}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_116 : Positive 1 12736 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_117 : Positive 1 12868 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 6}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_118 : Positive 1 13380 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {3, 4, 5}
    block := {0, 1, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_119 : Positive 1 13504 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_120 : Positive 1 15424 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_121 : Positive 1 17419 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 6}
    block := {0, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_122 : Positive 1 17427 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 6}
    block := {0, 1, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_123 : Positive 1 17433 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 6}
    block := {0, 1, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_124 : Positive 1 17443 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 6}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_125 : Positive 1 17457 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 6}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_126 : Positive 1 17458 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 6}
    block := {0, 1, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_127 : Positive 1 17475 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_128 : Positive 1 17481 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_129 : Positive 1 17545 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 6}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_130 : Positive 1 17553 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 6}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_131 : Positive 1 17560 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 6}
    block := {0, 1, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_132 : Positive 1 17584 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_133 : Positive 1 17929 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_134 : Positive 1 17937 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 4}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_135 : Positive 1 18064 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_136 : Positive 1 19459 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_137 : Positive 1 19473 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 4}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_138 : Positive 1 19504 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_139 : Positive 1 24601 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 5, 6}
    block := {0, 1, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_140 : Positive 1 24721 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 5, 6}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_141 : Positive 1 24849 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {3, 5, 6}
    block := {0, 1, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_142 : Positive 1 24976 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_143 : Positive 1 25105 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 4}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_144 : Positive 1 25609 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_145 : Positive 1 25617 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 4}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_146 : Positive 1 25744 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_147 : Positive 1 26896 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_148 : Positive 1 35140 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_149 : Positive 1 35857 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 4}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_150 : Positive 1 36934 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 7}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_151 : Positive 1 36964 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 7}
    block := {0, 1, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_152 : Positive 1 37126 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_153 : Positive 1 37188 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_154 : Positive 1 37216 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_155 : Positive 1 37956 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {3, 4, 7}
    block := {0, 1, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_156 : Positive 1 37984 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_157 : Positive 1 38464 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_158 : Positive 1 38980 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_159 : Positive 1 45124 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 6}
    block := {3, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_160 : Positive 1 46144 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_161 : Positive 1 49171 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 6, 7}
    block := {0, 1, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_162 : Positive 1 49201 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 6, 7}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_163 : Positive 1 49425 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {3, 6, 7}
    block := {0, 1, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_164 : Positive 1 49456 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_165 : Positive 1 49936 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_166 : Positive 1 50179 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_167 : Positive 1 50193 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 4}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_168 : Positive 1 50224 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_169 : Positive 1 51217 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 4}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_170 : Positive 1 57361 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 4}
    block := {3, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_171 : Positive 1 57616 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 4}
    block := {3, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_172 : Positive 1 963 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 6, 7}
    block := {0, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_173 : Positive 1 1686 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 4, 7}
    block := {0, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_174 : Positive 1 2409 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 5, 6}
    block := {0, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_175 : Positive 1 3132 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 4, 5}
    block := {0, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_176 : Positive 1 4522 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 4}
    block := {0, 5, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_177 : Positive 1 5290 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_178 : Positive 1 12483 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 6, 7}
    block := {0, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_179 : Positive 1 13379 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 6}
    block := {0, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_180 : Positive 1 15363 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 6, 7}
    block := {0, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_181 : Positive 1 15408 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_182 : Positive 1 16810 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_183 : Positive 1 17578 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 6}
    block := {0, 5, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_184 : Positive 1 24726 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 4, 7}
    block := {0, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_185 : Positive 1 24854 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 4}
    block := {0, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_186 : Positive 1 26886 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 4, 7}
    block := {0, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_187 : Positive 1 26976 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_188 : Positive 1 36969 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 5, 6}
    block := {0, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_189 : Positive 1 37961 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 6}
    block := {0, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_190 : Positive 1 38409 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 5, 6}
    block := {0, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_191 : Positive 1 38544 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_192 : Positive 1 43537 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 4}
    block := {2, 5, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_193 : Positive 1 43540 := by
  left
  refine ⟨{0, 1, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_194 : Positive 1 43585 := by
  left
  refine ⟨{0, 1, 6, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_195 : Positive 1 43588 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 6}
    block := {2, 5, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_196 : Positive 1 49212 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 4, 5}
    block := {0, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_197 : Positive 1 49436 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 4}
    block := {0, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_198 : Positive 1 49932 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 4, 5}
    block := {0, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_199 : Positive 1 50112 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private def group_0 : List ℕ := [
  546, 2184, 8736, 34944, 549, 553, 556, 904,
  1314, 1416, 1672, 2179, 2181, 2182, 2338, 3106]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) :
    Positive 1 m := by
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
  4122, 4680, 4740, 6180, 6210, 8229, 8233, 8236,
  8520, 8580, 8709, 8713, 8716, 8784, 8848, 8896]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) :
    Positive 1 m := by
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
  9240, 9345, 12424, 14344, 14464, 16458, 16920, 17025,
  18450, 18465, 20514, 20616, 20994, 21024, 22536, 22656]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) :
    Positive 1 m := by
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
  24712, 26632, 26752, 32899, 32901, 32902, 33060, 33090,
  33810, 33825, 34819, 34821, 34822, 34864, 34896, 34912]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) :
    Positive 1 m := by
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
  36898, 37378, 37408, 41217, 41988, 49186, 49666, 49696,
  286, 316, 406, 796, 844, 964, 1099, 1129]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) :
    Positive 1 m := by
  simp only [group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_64
  · exact witness_65
  · exact witness_66
  · exact witness_67
  · exact witness_68
  · exact witness_69
  · exact witness_70
  · exact witness_71
  · exact witness_72
  · exact witness_73
  · exact witness_74
  · exact witness_75
  · exact witness_76
  · exact witness_77
  · exact witness_78
  · exact witness_79

private def group_5 : List ℕ := [
  1219, 1561, 1609, 1681, 2326, 2374, 2404, 2884,
  3091, 3121, 3139, 3601, 4366, 4374, 4380, 4390]

private theorem group_sound_5 {m : ℕ} (h : m ∈ group_5) :
    Positive 1 m := by
  simp only [group_5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_80
  · exact witness_81
  · exact witness_82
  · exact witness_83
  · exact witness_84
  · exact witness_85
  · exact witness_86
  · exact witness_87
  · exact witness_88
  · exact witness_89
  · exact witness_90
  · exact witness_91
  · exact witness_92
  · exact witness_93
  · exact witness_94
  · exact witness_95

private def group_6 : List ℕ := [
  4422, 4428, 4450, 4452, 4492, 4548, 4552, 4576,
  4876, 4932, 5056, 6406, 6468, 6496, 9028, 9745]

private theorem group_sound_6 {m : ℕ} (h : m ∈ group_6) :
    Positive 1 m := by
  simp only [group_6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_96
  · exact witness_97
  · exact witness_98
  · exact witness_99
  · exact witness_100
  · exact witness_101
  · exact witness_102
  · exact witness_103
  · exact witness_104
  · exact witness_105
  · exact witness_106
  · exact witness_107
  · exact witness_108
  · exact witness_109
  · exact witness_110
  · exact witness_111

private def group_7 : List ℕ := [
  12364, 12484, 12556, 12612, 12736, 12868, 13380, 13504,
  15424, 17419, 17427, 17433, 17443, 17457, 17458, 17475]

private theorem group_sound_7 {m : ℕ} (h : m ∈ group_7) :
    Positive 1 m := by
  simp only [group_7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_112
  · exact witness_113
  · exact witness_114
  · exact witness_115
  · exact witness_116
  · exact witness_117
  · exact witness_118
  · exact witness_119
  · exact witness_120
  · exact witness_121
  · exact witness_122
  · exact witness_123
  · exact witness_124
  · exact witness_125
  · exact witness_126
  · exact witness_127

private def group_8 : List ℕ := [
  17481, 17545, 17553, 17560, 17584, 17929, 17937, 18064,
  19459, 19473, 19504, 24601, 24721, 24849, 24976, 25105]

private theorem group_sound_8 {m : ℕ} (h : m ∈ group_8) :
    Positive 1 m := by
  simp only [group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_128
  · exact witness_129
  · exact witness_130
  · exact witness_131
  · exact witness_132
  · exact witness_133
  · exact witness_134
  · exact witness_135
  · exact witness_136
  · exact witness_137
  · exact witness_138
  · exact witness_139
  · exact witness_140
  · exact witness_141
  · exact witness_142
  · exact witness_143

private def group_9 : List ℕ := [
  25609, 25617, 25744, 26896, 35140, 35857, 36934, 36964,
  37126, 37188, 37216, 37956, 37984, 38464, 38980, 45124]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) :
    Positive 1 m := by
  simp only [group_9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_144
  · exact witness_145
  · exact witness_146
  · exact witness_147
  · exact witness_148
  · exact witness_149
  · exact witness_150
  · exact witness_151
  · exact witness_152
  · exact witness_153
  · exact witness_154
  · exact witness_155
  · exact witness_156
  · exact witness_157
  · exact witness_158
  · exact witness_159

private def group_10 : List ℕ := [
  46144, 49171, 49201, 49425, 49456, 49936, 50179, 50193,
  50224, 51217, 57361, 57616, 963, 1686, 2409, 3132]

private theorem group_sound_10 {m : ℕ} (h : m ∈ group_10) :
    Positive 1 m := by
  simp only [group_10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_160
  · exact witness_161
  · exact witness_162
  · exact witness_163
  · exact witness_164
  · exact witness_165
  · exact witness_166
  · exact witness_167
  · exact witness_168
  · exact witness_169
  · exact witness_170
  · exact witness_171
  · exact witness_172
  · exact witness_173
  · exact witness_174
  · exact witness_175

private def group_11 : List ℕ := [
  4522, 5290, 12483, 13379, 15363, 15408, 16810, 17578,
  24726, 24854, 26886, 26976, 36969, 37961, 38409, 38544]

private theorem group_sound_11 {m : ℕ} (h : m ∈ group_11) :
    Positive 1 m := by
  simp only [group_11, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_176
  · exact witness_177
  · exact witness_178
  · exact witness_179
  · exact witness_180
  · exact witness_181
  · exact witness_182
  · exact witness_183
  · exact witness_184
  · exact witness_185
  · exact witness_186
  · exact witness_187
  · exact witness_188
  · exact witness_189
  · exact witness_190
  · exact witness_191

private def group_12 : List ℕ := [
  43537, 43540, 43585, 43588, 49212, 49436, 49932, 50112]

private theorem group_sound_12 {m : ℕ} (h : m ∈ group_12) :
    Positive 1 m := by
  simp only [group_12, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_192
  · exact witness_193
  · exact witness_194
  · exact witness_195
  · exact witness_196
  · exact witness_197
  · exact witness_198
  · exact witness_199

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 1 m := by
  have hg :
      m ∈ group_0 ∨
      m ∈ group_1 ∨
      m ∈ group_2 ∨
      m ∈ group_3 ∨
      m ∈ group_4 ∨
      m ∈ group_5 ∨
      m ∈ group_6 ∨
      m ∈ group_7 ∨
      m ∈ group_8 ∨
      m ∈ group_9 ∨
      m ∈ group_10 ∨
      m ∈ group_11 ∨
      m ∈ group_12 := by
    change m ∈
      group_0 ++
      group_1 ++
      group_2 ++
      group_3 ++
      group_4 ++
      group_5 ++
      group_6 ++
      group_7 ++
      group_8 ++
      group_9 ++
      group_10 ++
      group_11 ++
      group_12 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
  · exact group_sound_0 hg
  · exact group_sound_1 hg
  · exact group_sound_2 hg
  · exact group_sound_3 hg
  · exact group_sound_4 hg
  · exact group_sound_5 hg
  · exact group_sound_6 hg
  · exact group_sound_7 hg
  · exact group_sound_8 hg
  · exact group_sound_9 hg
  · exact group_sound_10 hg
  · exact group_sound_11 hg
  · exact group_sound_12 hg

theorem finite_positive (m : Fin 65536) (h : 9 ≤ PathExchange.crossCount m.val) :
    Positive 1 m.val := by
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp (coverage m h)
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.PathLoss.D1
