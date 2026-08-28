import ErdosProblems.Erdos577.UnattachedMasks1

/-! Explicit cycle and score-improvement witnesses for diagonal mask 1. -/

namespace Erdos577.Unattached.D1

open Finset

private theorem witness_0 : Positive 1 7 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_1 : Positive 1 13 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_2 : Positive 1 37 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_3 : Positive 1 41 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_4 : Positive 1 44 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_5 : Positive 1 131 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_6 : Positive 1 133 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_7 : Positive 1 134 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_8 : Positive 1 517 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_9 : Positive 1 521 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_10 : Positive 1 524 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_11 : Positive 1 545 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_12 : Positive 1 548 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_13 : Positive 1 552 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_14 : Positive 1 2051 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_15 : Positive 1 2053 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_16 : Positive 1 2054 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_17 : Positive 1 2177 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_18 : Positive 1 2178 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_19 : Positive 1 2180 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_20 : Positive 1 8197 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_21 : Positive 1 8201 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_22 : Positive 1 8204 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {1, 2, 3}
    block := {0, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_23 : Positive 1 8225 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_24 : Positive 1 8228 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_25 : Positive 1 8232 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_26 : Positive 1 8705 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_27 : Positive 1 8708 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_28 : Positive 1 8712 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_29 : Positive 1 8736 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_30 : Positive 1 32771 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_31 : Positive 1 32773 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_32 : Positive 1 32774 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {1, 2, 3}
    block := {0, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_33 : Positive 1 32897 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_34 : Positive 1 32898 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_35 : Positive 1 32900 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_36 : Positive 1 34817 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_37 : Positive 1 34818 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_38 : Positive 1 34820 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_39 : Positive 1 34944 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_40 : Positive 1 30 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_41 : Positive 1 75 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_42 : Positive 1 270 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_43 : Positive 1 278 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_44 : Positive 1 282 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_45 : Positive 1 284 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_46 : Positive 1 1035 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_47 : Positive 1 1091 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_48 : Positive 1 1097 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_49 : Positive 1 1098 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_50 : Positive 1 4110 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_51 : Positive 1 4118 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_52 : Positive 1 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_53 : Positive 1 4124 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_54 : Positive 1 4358 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_55 : Positive 1 4362 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_56 : Positive 1 4364 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_57 : Positive 1 16395 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_58 : Positive 1 16451 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_59 : Positive 1 16457 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_60 : Positive 1 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_61 : Positive 1 17411 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_62 : Positive 1 17417 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_63 : Positive 1 17418 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_64 : Positive 1 8786 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_65 : Positive 1 8850 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_66 : Positive 1 8898 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_67 : Positive 1 8912 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 5}
    block := {1, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_68 : Positive 1 9506 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 5}
    block := {2, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_69 : Positive 1 10530 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 5}
    block := {2, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_70 : Positive 1 11298 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 5}
    block := {2, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_71 : Positive 1 11552 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 5}
    block := {2, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_72 : Positive 1 14472 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_73 : Positive 1 21026 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_74 : Positive 1 22664 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_75 : Positive 1 26760 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_76 : Positive 1 30848 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 7}
    block := {3, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_77 : Positive 1 33672 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 7}
    block := {2, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_78 : Positive 1 34184 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 7}
    block := {2, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_79 : Positive 1 34440 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 7}
    block := {2, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_80 : Positive 1 34688 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 7}
    block := {2, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_81 : Positive 1 34872 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 4, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_82 : Positive 1 34904 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_83 : Positive 1 34920 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 5, 4, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_84 : Positive 1 34928 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 7}
    block := {1, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_85 : Positive 1 37410 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_86 : Positive 1 49698 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 6, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_87 : Positive 1 53792 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 5}
    block := {3, 4, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_88 : Positive 1 4577 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 4}
    block := {1, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_89 : Positive 1 5060 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_90 : Positive 1 5064 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_91 : Positive 1 5290 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_92 : Positive 1 5778 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_93 : Positive 1 5780 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_94 : Positive 1 6498 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_95 : Positive 1 6500 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_96 : Positive 1 6730 := by
  left
  refine ⟨{0, 5, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_97 : Positive 1 7220 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_98 : Positive 1 7224 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_99 : Positive 1 7697 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 4}
    block := {2, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_100 : Positive 1 12740 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_101 : Positive 1 12744 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_102 : Positive 1 13248 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_103 : Positive 1 13505 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_104 : Positive 1 13506 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_105 : Positive 1 15380 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_106 : Positive 1 15384 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_107 : Positive 1 15408 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_108 : Positive 1 15425 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_109 : Positive 1 15426 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_110 : Positive 1 15552 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_111 : Positive 1 16810 := by
  left
  refine ⟨{0, 5, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_112 : Positive 1 17345 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_113 : Positive 1 17346 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_114 : Positive 1 17588 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_115 : Positive 1 18065 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_116 : Positive 1 18072 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_117 : Positive 1 18785 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_118 : Positive 1 18792 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_119 : Positive 1 18970 := by
  left
  refine ⟨{0, 5, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_120 : Positive 1 19268 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 6}
    block := {2, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_121 : Positive 1 19505 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_122 : Positive 1 19506 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_123 : Positive 1 24978 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_124 : Positive 1 24980 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_125 : Positive 1 25745 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_126 : Positive 1 25752 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_127 : Positive 1 26256 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_128 : Positive 1 26898 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_129 : Positive 1 26900 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_130 : Positive 1 26945 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_131 : Positive 1 26952 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_132 : Positive 1 26976 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_133 : Positive 1 27024 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_134 : Positive 1 37218 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_135 : Positive 1 37220 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_136 : Positive 1 37985 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_137 : Positive 1 37992 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_138 : Positive 1 38418 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_139 : Positive 1 38420 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_140 : Positive 1 38465 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_141 : Positive 1 38472 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_142 : Positive 1 38496 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_143 : Positive 1 38544 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_144 : Positive 1 39264 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_145 : Positive 1 41290 := by
  left
  refine ⟨{0, 5, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_146 : Positive 1 42010 := by
  left
  refine ⟨{0, 5, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_147 : Positive 1 46148 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_148 : Positive 1 49460 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_149 : Positive 1 49464 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_150 : Positive 1 49940 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_151 : Positive 1 49944 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_152 : Positive 1 49968 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_153 : Positive 1 49985 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_154 : Positive 1 49986 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_155 : Positive 1 50112 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_156 : Positive 1 50225 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_157 : Positive 1 50226 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_158 : Positive 1 52272 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_159 : Positive 1 57617 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 4}
    block := {3, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private def group_0 : List ℕ := [
  7, 13, 37, 41, 44, 131, 133, 134,
  517, 521, 524, 545, 548, 552, 2051, 2053]

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
  2054, 2177, 2178, 2180, 8197, 8201, 8204, 8225,
  8228, 8232, 8705, 8708, 8712, 8736, 32771, 32773]

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
  32774, 32897, 32898, 32900, 34817, 34818, 34820, 34944,
  30, 75, 270, 278, 282, 284, 1035, 1091]

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
  1097, 1098, 4110, 4118, 4122, 4124, 4358, 4362,
  4364, 16395, 16451, 16457, 16458, 17411, 17417, 17418]

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
  8786, 8850, 8898, 8912, 9506, 10530, 11298, 11552,
  14472, 21026, 22664, 26760, 30848, 33672, 34184, 34440]

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
  34688, 34872, 34904, 34920, 34928, 37410, 49698, 53792,
  4577, 5060, 5064, 5290, 5778, 5780, 6498, 6500]

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
  6730, 7220, 7224, 7697, 12740, 12744, 13248, 13505,
  13506, 15380, 15384, 15408, 15425, 15426, 15552, 16810]

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
  17345, 17346, 17588, 18065, 18072, 18785, 18792, 18970,
  19268, 19505, 19506, 24978, 24980, 25745, 25752, 26256]

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
  26898, 26900, 26945, 26952, 26976, 27024, 37218, 37220,
  37985, 37992, 38418, 38420, 38465, 38472, 38496, 38544]

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
  39264, 41290, 42010, 46148, 49460, 49464, 49940, 49944,
  49968, 49985, 49986, 50112, 50225, 50226, 52272, 57617]

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
      m ∈ group_9 := by
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
      group_9 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
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

theorem finite_positive (m : Fin 65536) (h : 13 ≤ weightedCount m.val) :
    Positive 1 m.val := by
  have hc := coverage m h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.Unattached.D1
