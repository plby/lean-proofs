import ErdosProblems.Erdos577.UnattachedMasks2

/-! Explicit cycle and score-improvement witnesses for diagonal mask 2. -/

namespace Erdos577.Unattached.D2

open Finset

private theorem witness_0 : Positive 2 11 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_1 : Positive 2 14 := by
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
  · left
    decide +kernel

private theorem witness_2 : Positive 2 22 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_3 : Positive 2 26 := by
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

private theorem witness_4 : Positive 2 28 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_5 : Positive 2 67 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_6 : Positive 2 73 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_7 : Positive 2 74 := by
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

private theorem witness_8 : Positive 2 262 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_9 : Positive 2 266 := by
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

private theorem witness_10 : Positive 2 268 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_11 : Positive 2 274 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_12 : Positive 2 276 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_13 : Positive 2 280 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_14 : Positive 2 1027 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_15 : Positive 2 1033 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_16 : Positive 2 1034 := by
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

private theorem witness_17 : Positive 2 1089 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_18 : Positive 2 1090 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_19 : Positive 2 1096 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_20 : Positive 2 4102 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_21 : Positive 2 4106 := by
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

private theorem witness_22 : Positive 2 4108 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {1, 2, 3}
    block := {0, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_23 : Positive 2 4114 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_24 : Positive 2 4116 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_25 : Positive 2 4120 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_26 : Positive 2 4354 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_27 : Positive 2 4356 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_28 : Positive 2 4360 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_29 : Positive 2 4368 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {5, 6, 7}
    block := {1, 2, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_30 : Positive 2 16387 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_31 : Positive 2 16393 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {1, 2, 3}
    block := {0, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_32 : Positive 2 16394 := by
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

private theorem witness_33 : Positive 2 16449 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_34 : Positive 2 16450 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_35 : Positive 2 16456 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_36 : Positive 2 17409 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_37 : Positive 2 17410 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_38 : Positive 2 17416 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_39 : Positive 2 17472 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {4, 5, 7}
    block := {1, 2, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_40 : Positive 2 45 := by
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

private theorem witness_41 : Positive 2 135 := by
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

private theorem witness_42 : Positive 2 525 := by
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

private theorem witness_43 : Positive 2 549 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_44 : Positive 2 553 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_45 : Positive 2 556 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_46 : Positive 2 2055 := by
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

private theorem witness_47 : Positive 2 2179 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_48 : Positive 2 2181 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_49 : Positive 2 2182 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 5, 6}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_50 : Positive 2 8205 := by
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

private theorem witness_51 : Positive 2 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_52 : Positive 2 8233 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_53 : Positive 2 8236 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_54 : Positive 2 8709 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_55 : Positive 2 8713 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_56 : Positive 2 8716 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_57 : Positive 2 32775 := by
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

private theorem witness_58 : Positive 2 32899 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_59 : Positive 2 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_60 : Positive 2 32902 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_61 : Positive 2 34819 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_62 : Positive 2 34821 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_63 : Positive 2 34822 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 5, 6}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_64 : Positive 2 4449 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 4}
    block := {1, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_65 : Positive 2 4513 := by
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

private theorem witness_66 : Positive 2 4545 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 4}
    block := {1, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_67 : Positive 2 4576 := by
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
  · left
    decide +kernel

private theorem witness_68 : Positive 2 5649 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 4}
    block := {2, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_69 : Positive 2 6673 := by
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

private theorem witness_70 : Positive 2 7185 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 4}
    block := {2, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_71 : Positive 2 7696 := by
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
  · left
    decide +kernel

private theorem witness_72 : Positive 2 13380 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_73 : Positive 2 17220 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 6}
    block := {2, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_74 : Positive 2 17460 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 4, 7, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_75 : Positive 2 17556 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_76 : Positive 2 17572 := by
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

private theorem witness_77 : Positive 2 17584 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 3, 6}
    block := {1, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_78 : Positive 2 18756 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 6}
    block := {2, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_79 : Positive 2 19012 := by
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

private theorem witness_80 : Positive 2 19264 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 6}
    block := {2, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_81 : Positive 2 24849 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 4}
    block := {3, 5, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_82 : Positive 2 37956 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_83 : Positive 2 41233 := by
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

private theorem witness_84 : Positive 2 42052 := by
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

private theorem witness_85 : Positive 2 46144 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 6}
    block := {3, 4, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_86 : Positive 2 49425 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 2, 4}
    block := {3, 6, 5, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_87 : Positive 2 57616 := by
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
  · left
    decide +kernel

private theorem witness_88 : Positive 2 8914 := by
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

private theorem witness_89 : Positive 2 9156 := by
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

private theorem witness_90 : Positive 2 9160 := by
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

private theorem witness_91 : Positive 2 9605 := by
  left
  refine ⟨{0, 4, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_92 : Positive 2 9873 := by
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

private theorem witness_93 : Positive 2 9880 := by
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

private theorem witness_94 : Positive 2 10325 := by
  left
  refine ⟨{0, 4, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_95 : Positive 2 10593 := by
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

private theorem witness_96 : Positive 2 10600 := by
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

private theorem witness_97 : Positive 2 11316 := by
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

private theorem witness_98 : Positive 2 11320 := by
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

private theorem witness_99 : Positive 2 11554 := by
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

private theorem witness_100 : Positive 2 12996 := by
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

private theorem witness_101 : Positive 2 13000 := by
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

private theorem witness_102 : Positive 2 13248 := by
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

private theorem witness_103 : Positive 2 14529 := by
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

private theorem witness_104 : Positive 2 14530 := by
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

private theorem witness_105 : Positive 2 15396 := by
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

private theorem witness_106 : Positive 2 15400 := by
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

private theorem witness_107 : Positive 2 15408 := by
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

private theorem witness_108 : Positive 2 15489 := by
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

private theorem witness_109 : Positive 2 15490 := by
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

private theorem witness_110 : Positive 2 15552 := by
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

private theorem witness_111 : Positive 2 21125 := by
  left
  refine ⟨{0, 4, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_112 : Positive 2 22565 := by
  left
  refine ⟨{0, 4, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_113 : Positive 2 25233 := by
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

private theorem witness_114 : Positive 2 25240 := by
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

private theorem witness_115 : Positive 2 26256 := by
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

private theorem witness_116 : Positive 2 26770 := by
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

private theorem witness_117 : Positive 2 26772 := by
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

private theorem witness_118 : Positive 2 26913 := by
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

private theorem witness_119 : Positive 2 26920 := by
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

private theorem witness_120 : Positive 2 26976 := by
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

private theorem witness_121 : Positive 2 27010 := by
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

private theorem witness_122 : Positive 2 27012 := by
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

private theorem witness_123 : Positive 2 27024 := by
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

private theorem witness_124 : Positive 2 30856 := by
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

private theorem witness_125 : Positive 2 33365 := by
  left
  refine ⟨{0, 4, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_126 : Positive 2 33729 := by
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

private theorem witness_127 : Positive 2 33730 := by
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

private theorem witness_128 : Positive 2 34085 := by
  left
  refine ⟨{0, 4, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_129 : Positive 2 34450 := by
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

private theorem witness_130 : Positive 2 34452 := by
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

private theorem witness_131 : Positive 2 34696 := by
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

private theorem witness_132 : Positive 2 34936 := by
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

private theorem witness_133 : Positive 2 35170 := by
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

private theorem witness_134 : Positive 2 35172 := by
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

private theorem witness_135 : Positive 2 35889 := by
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

private theorem witness_136 : Positive 2 35890 := by
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

private theorem witness_137 : Positive 2 37473 := by
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

private theorem witness_138 : Positive 2 37480 := by
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

private theorem witness_139 : Positive 2 38433 := by
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

private theorem witness_140 : Positive 2 38440 := by
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

private theorem witness_141 : Positive 2 38496 := by
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

private theorem witness_142 : Positive 2 38530 := by
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

private theorem witness_143 : Positive 2 38532 := by
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

private theorem witness_144 : Positive 2 38544 := by
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

private theorem witness_145 : Positive 2 39010 := by
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

private theorem witness_146 : Positive 2 39012 := by
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

private theorem witness_147 : Positive 2 39264 := by
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

private theorem witness_148 : Positive 2 49716 := by
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

private theorem witness_149 : Positive 2 49720 := by
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

private theorem witness_150 : Positive 2 49956 := by
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

private theorem witness_151 : Positive 2 49960 := by
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

private theorem witness_152 : Positive 2 49968 := by
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

private theorem witness_153 : Positive 2 50049 := by
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

private theorem witness_154 : Positive 2 50050 := by
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

private theorem witness_155 : Positive 2 50112 := by
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

private theorem witness_156 : Positive 2 51249 := by
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

private theorem witness_157 : Positive 2 51250 := by
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

private theorem witness_158 : Positive 2 52272 := by
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

private theorem witness_159 : Positive 2 53794 := by
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

private def group_0 : List ℕ := [
  11, 14, 22, 26, 28, 67, 73, 74,
  262, 266, 268, 274, 276, 280, 1027, 1033]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) :
    Positive 2 m := by
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
  1034, 1089, 1090, 1096, 4102, 4106, 4108, 4114,
  4116, 4120, 4354, 4356, 4360, 4368, 16387, 16393]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) :
    Positive 2 m := by
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
  16394, 16449, 16450, 16456, 17409, 17410, 17416, 17472,
  45, 135, 525, 549, 553, 556, 2055, 2179]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) :
    Positive 2 m := by
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
  2181, 2182, 8205, 8229, 8233, 8236, 8709, 8713,
  8716, 32775, 32899, 32901, 32902, 34819, 34821, 34822]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) :
    Positive 2 m := by
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
  4449, 4513, 4545, 4576, 5649, 6673, 7185, 7696,
  13380, 17220, 17460, 17556, 17572, 17584, 18756, 19012]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) :
    Positive 2 m := by
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
  19264, 24849, 37956, 41233, 42052, 46144, 49425, 57616,
  8914, 9156, 9160, 9605, 9873, 9880, 10325, 10593]

private theorem group_sound_5 {m : ℕ} (h : m ∈ group_5) :
    Positive 2 m := by
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
  10600, 11316, 11320, 11554, 12996, 13000, 13248, 14529,
  14530, 15396, 15400, 15408, 15489, 15490, 15552, 21125]

private theorem group_sound_6 {m : ℕ} (h : m ∈ group_6) :
    Positive 2 m := by
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
  22565, 25233, 25240, 26256, 26770, 26772, 26913, 26920,
  26976, 27010, 27012, 27024, 30856, 33365, 33729, 33730]

private theorem group_sound_7 {m : ℕ} (h : m ∈ group_7) :
    Positive 2 m := by
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
  34085, 34450, 34452, 34696, 34936, 35170, 35172, 35889,
  35890, 37473, 37480, 38433, 38440, 38496, 38530, 38532]

private theorem group_sound_8 {m : ℕ} (h : m ∈ group_8) :
    Positive 2 m := by
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
  38544, 39010, 39012, 39264, 49716, 49720, 49956, 49960,
  49968, 50049, 50050, 50112, 51249, 51250, 52272, 53794]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) :
    Positive 2 m := by
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

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 2 m := by
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
    Positive 2 m.val := by
  have hc := coverage m h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.Unattached.D2
