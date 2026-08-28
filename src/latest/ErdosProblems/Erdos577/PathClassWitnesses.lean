import ErdosProblems.Erdos577.PathClassMasks

/-! Explicit factors or triangle/complete-block conversions for Wang 3.5. -/

namespace Erdos577.PathClass

open Finset

private theorem positive_0 : Positive 4118 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_1 : Positive 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_2 : Positive 4124 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_3 : Positive 4680 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_4 : Positive 4740 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_5 : Positive 5160 := by
  left
  refine ⟨{0, 1, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_6 : Positive 5250 := by
  left
  refine ⟨{0, 1, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_7 : Positive 6180 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_8 : Positive 6210 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_9 : Positive 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_10 : Positive 8233 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_11 : Positive 8236 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_12 : Positive 8520 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_13 : Positive 8580 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_14 : Positive 9240 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_15 : Positive 9345 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_16 : Positive 10260 := by
  left
  refine ⟨{0, 1, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_17 : Positive 10305 := by
  left
  refine ⟨{0, 1, 6, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_18 : Positive 13316 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_19 : Positive 14344 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_20 : Positive 16451 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_21 : Positive 16457 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_22 : Positive 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_23 : Positive 16680 := by
  left
  refine ⟨{0, 1, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_24 : Positive 16770 := by
  left
  refine ⟨{0, 1, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_25 : Positive 16920 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_26 : Positive 17025 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_27 : Positive 18450 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_28 : Positive 18465 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_29 : Positive 20994 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_30 : Positive 22536 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_31 : Positive 24833 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_32 : Positive 26632 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_33 : Positive 32899 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_34 : Positive 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_35 : Positive 32902 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_36 : Positive 33060 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_37 : Positive 33090 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_38 : Positive 33300 := by
  left
  refine ⟨{0, 1, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_39 : Positive 33345 := by
  left
  refine ⟨{0, 1, 6, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_40 : Positive 33810 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_41 : Positive 33825 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_42 : Positive 37378 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_43 : Positive 37892 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_44 : Positive 41217 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_45 : Positive 41988 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_46 : Positive 49409 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_47 : Positive 49666 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_48 : Positive 286 := by
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

private theorem positive_49 : Positive 557 := by
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

private theorem positive_50 : Positive 1099 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 2, 6}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_51 : Positive 1928 := by
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

private theorem positive_52 : Positive 2183 := by
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

private theorem positive_53 : Positive 2884 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 1, 6}
    block := {2, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_54 : Positive 3362 := by
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

private theorem positive_55 : Positive 3601 := by
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

private theorem positive_56 : Positive 4366 := by
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

private theorem positive_57 : Positive 4576 := by
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

private theorem positive_58 : Positive 8717 := by
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

private theorem positive_59 : Positive 8912 := by
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

private theorem positive_60 : Positive 17419 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 3, 6}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_61 : Positive 17584 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_62 : Positive 28808 := by
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

private theorem positive_63 : Positive 30848 := by
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

private theorem positive_64 : Positive 34823 := by
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

private theorem positive_65 : Positive 34928 := by
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

private theorem positive_66 : Positive 45124 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 1, 6}
    block := {3, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_67 : Positive 46144 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_68 : Positive 53282 := by
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

private theorem positive_69 : Positive 53792 := by
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

private theorem positive_70 : Positive 57361 := by
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

private theorem positive_71 : Positive 57616 := by
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

private theorem positive_72 : Positive 828 := by
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

private theorem positive_73 : Positive 972 := by
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

private theorem positive_74 : Positive 1370 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 7}
    block := {1, 2, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_75 : Positive 1450 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 6}
    block := {0, 1, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_76 : Positive 1641 := by
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

private theorem positive_77 : Positive 1689 := by
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

private theorem positive_78 : Positive 2406 := by
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

private theorem positive_79 : Positive 2454 := by
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

private theorem positive_80 : Positive 2645 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 5, 7}
    block := {0, 1, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_81 : Positive 2725 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 6}
    block := {1, 2, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_82 : Positive 3123 := by
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

private theorem positive_83 : Positive 3267 := by
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

private theorem positive_84 : Positive 4454 := by
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

private theorem positive_85 : Positive 4522 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 4}
    block := {0, 1, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_86 : Positive 4556 := by
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

private theorem positive_87 : Positive 8789 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 5}
    block := {0, 1, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_88 : Positive 8857 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 5}
    block := {0, 1, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_89 : Positive 8908 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 5}
    block := {0, 1, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_90 : Positive 12492 := by
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

private theorem positive_91 : Positive 13068 := by
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

private theorem positive_92 : Positive 13124 := by
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

private theorem positive_93 : Positive 13192 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_94 : Positive 13248 := by
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

private theorem positive_95 : Positive 15552 := by
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

private theorem positive_96 : Positive 17459 := by
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

private theorem positive_97 : Positive 17561 := by
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

private theorem positive_98 : Positive 17578 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 6}
    block := {0, 1, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_99 : Positive 20650 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 6}
    block := {0, 1, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_100 : Positive 21770 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 7}
    block := {2, 3, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_101 : Positive 21794 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 5}
    block := {2, 3, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_102 : Positive 21896 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 7}
    block := {2, 3, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_103 : Positive 21920 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 7}
    block := {2, 3, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_104 : Positive 23200 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 6}
    block := {1, 2, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_105 : Positive 24729 := by
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

private theorem positive_106 : Positive 26121 := by
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

private theorem positive_107 : Positive 26129 := by
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

private theorem positive_108 : Positive 26248 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_109 : Positive 26256 := by
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

private theorem positive_110 : Positive 27024 := by
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

private theorem positive_111 : Positive 34867 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 7}
    block := {0, 1, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_112 : Positive 34901 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 7}
    block := {0, 1, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_113 : Positive 34918 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 7}
    block := {0, 1, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_114 : Positive 36966 := by
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

private theorem positive_115 : Positive 38496 := by
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

private theorem positive_116 : Positive 39174 := by
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

private theorem positive_117 : Positive 39202 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 5}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_118 : Positive 39236 := by
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

private theorem positive_119 : Positive 39264 := by
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

private theorem positive_120 : Positive 41045 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 5, 7}
    block := {0, 1, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_121 : Positive 42320 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 7}
    block := {1, 2, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_122 : Positive 43525 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 6}
    block := {2, 3, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_123 : Positive 43537 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 4}
    block := {2, 3, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_124 : Positive 43588 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 6}
    block := {2, 3, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_125 : Positive 43600 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 6}
    block := {2, 3, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_126 : Positive 49203 := by
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

private theorem positive_127 : Positive 49968 := by
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

private theorem positive_128 : Positive 52227 := by
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

private theorem positive_129 : Positive 52241 := by
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

private theorem positive_130 : Positive 52258 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_131 : Positive 52272 := by
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

private def positive_group_0 : List ℕ := [
  4118, 4122, 4124, 4680, 4740, 5160, 5250, 6180,
  6210, 8229, 8233, 8236, 8520, 8580, 9240, 9345]

private theorem positive_group_0_sound {m : ℕ} (h : m ∈ positive_group_0) : Positive m := by
  simp only [positive_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_0
  · exact positive_1
  · exact positive_2
  · exact positive_3
  · exact positive_4
  · exact positive_5
  · exact positive_6
  · exact positive_7
  · exact positive_8
  · exact positive_9
  · exact positive_10
  · exact positive_11
  · exact positive_12
  · exact positive_13
  · exact positive_14
  · exact positive_15

private def positive_group_1 : List ℕ := [
  10260, 10305, 13316, 14344, 16451, 16457, 16458, 16680,
  16770, 16920, 17025, 18450, 18465, 20994, 22536, 24833]

private theorem positive_group_1_sound {m : ℕ} (h : m ∈ positive_group_1) : Positive m := by
  simp only [positive_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_16
  · exact positive_17
  · exact positive_18
  · exact positive_19
  · exact positive_20
  · exact positive_21
  · exact positive_22
  · exact positive_23
  · exact positive_24
  · exact positive_25
  · exact positive_26
  · exact positive_27
  · exact positive_28
  · exact positive_29
  · exact positive_30
  · exact positive_31

private def positive_group_2 : List ℕ := [
  26632, 32899, 32901, 32902, 33060, 33090, 33300, 33345,
  33810, 33825, 37378, 37892, 41217, 41988, 49409, 49666]

private theorem positive_group_2_sound {m : ℕ} (h : m ∈ positive_group_2) : Positive m := by
  simp only [positive_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_32
  · exact positive_33
  · exact positive_34
  · exact positive_35
  · exact positive_36
  · exact positive_37
  · exact positive_38
  · exact positive_39
  · exact positive_40
  · exact positive_41
  · exact positive_42
  · exact positive_43
  · exact positive_44
  · exact positive_45
  · exact positive_46
  · exact positive_47

private def positive_group_3 : List ℕ := [
  286, 557, 1099, 1928, 2183, 2884, 3362, 3601,
  4366, 4576, 8717, 8912, 17419, 17584, 28808, 30848]

private theorem positive_group_3_sound {m : ℕ} (h : m ∈ positive_group_3) : Positive m := by
  simp only [positive_group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_48
  · exact positive_49
  · exact positive_50
  · exact positive_51
  · exact positive_52
  · exact positive_53
  · exact positive_54
  · exact positive_55
  · exact positive_56
  · exact positive_57
  · exact positive_58
  · exact positive_59
  · exact positive_60
  · exact positive_61
  · exact positive_62
  · exact positive_63

private def positive_group_4 : List ℕ := [
  34823, 34928, 45124, 46144, 53282, 53792, 57361, 57616,
  828, 972, 1370, 1450, 1641, 1689, 2406, 2454]

private theorem positive_group_4_sound {m : ℕ} (h : m ∈ positive_group_4) : Positive m := by
  simp only [positive_group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_64
  · exact positive_65
  · exact positive_66
  · exact positive_67
  · exact positive_68
  · exact positive_69
  · exact positive_70
  · exact positive_71
  · exact positive_72
  · exact positive_73
  · exact positive_74
  · exact positive_75
  · exact positive_76
  · exact positive_77
  · exact positive_78
  · exact positive_79

private def positive_group_5 : List ℕ := [
  2645, 2725, 3123, 3267, 4454, 4522, 4556, 8789,
  8857, 8908, 12492, 13068, 13124, 13192, 13248, 15552]

private theorem positive_group_5_sound {m : ℕ} (h : m ∈ positive_group_5) : Positive m := by
  simp only [positive_group_5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_80
  · exact positive_81
  · exact positive_82
  · exact positive_83
  · exact positive_84
  · exact positive_85
  · exact positive_86
  · exact positive_87
  · exact positive_88
  · exact positive_89
  · exact positive_90
  · exact positive_91
  · exact positive_92
  · exact positive_93
  · exact positive_94
  · exact positive_95

private def positive_group_6 : List ℕ := [
  17459, 17561, 17578, 20650, 21770, 21794, 21896, 21920,
  23200, 24729, 26121, 26129, 26248, 26256, 27024, 34867]

private theorem positive_group_6_sound {m : ℕ} (h : m ∈ positive_group_6) : Positive m := by
  simp only [positive_group_6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_96
  · exact positive_97
  · exact positive_98
  · exact positive_99
  · exact positive_100
  · exact positive_101
  · exact positive_102
  · exact positive_103
  · exact positive_104
  · exact positive_105
  · exact positive_106
  · exact positive_107
  · exact positive_108
  · exact positive_109
  · exact positive_110
  · exact positive_111

private def positive_group_7 : List ℕ := [
  34901, 34918, 36966, 38496, 39174, 39202, 39236, 39264,
  41045, 42320, 43525, 43537, 43588, 43600, 49203, 49968]

private theorem positive_group_7_sound {m : ℕ} (h : m ∈ positive_group_7) : Positive m := by
  simp only [positive_group_7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_112
  · exact positive_113
  · exact positive_114
  · exact positive_115
  · exact positive_116
  · exact positive_117
  · exact positive_118
  · exact positive_119
  · exact positive_120
  · exact positive_121
  · exact positive_122
  · exact positive_123
  · exact positive_124
  · exact positive_125
  · exact positive_126
  · exact positive_127

private def positive_group_8 : List ℕ := [
  52227, 52241, 52258, 52272]

private theorem positive_group_8_sound {m : ℕ} (h : m ∈ positive_group_8) : Positive m := by
  simp only [positive_group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl
  · exact positive_128
  · exact positive_129
  · exact positive_130
  · exact positive_131

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive m := by
  have hg :
      m ∈ positive_group_0 ∨
      m ∈ positive_group_1 ∨
      m ∈ positive_group_2 ∨
      m ∈ positive_group_3 ∨
      m ∈ positive_group_4 ∨
      m ∈ positive_group_5 ∨
      m ∈ positive_group_6 ∨
      m ∈ positive_group_7 ∨
      m ∈ positive_group_8 := by
    change m ∈
      positive_group_0 ++
      positive_group_1 ++
      positive_group_2 ++
      positive_group_3 ++
      positive_group_4 ++
      positive_group_5 ++
      positive_group_6 ++
      positive_group_7 ++
      positive_group_8 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg
  · exact positive_group_0_sound hg
  · exact positive_group_1_sound hg
  · exact positive_group_2_sound hg
  · exact positive_group_3_sound hg
  · exact positive_group_4_sound hg
  · exact positive_group_5_sound hg
  · exact positive_group_6_sound hg
  · exact positive_group_7_sound hg
  · exact positive_group_8_sound hg

end Erdos577.PathClass
