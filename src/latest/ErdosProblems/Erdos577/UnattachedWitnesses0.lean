import ErdosProblems.Erdos577.UnattachedMasks0

/-! Explicit cycle and score-improvement witnesses for diagonal mask 0. -/

namespace Erdos577.Unattached.D0

open Finset

private theorem witness_0 : Positive 0 7 := by
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

private theorem witness_1 : Positive 0 11 := by
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
  · left
    decide +kernel

private theorem witness_2 : Positive 0 13 := by
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
  · left
    decide +kernel

private theorem witness_3 : Positive 0 14 := by
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

private theorem witness_4 : Positive 0 26 := by
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

private theorem witness_5 : Positive 0 37 := by
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

private theorem witness_6 : Positive 0 74 := by
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

private theorem witness_7 : Positive 0 133 := by
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

private theorem witness_8 : Positive 0 266 := by
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

private theorem witness_9 : Positive 0 517 := by
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

private theorem witness_10 : Positive 0 1034 := by
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

private theorem witness_11 : Positive 0 2053 := by
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

private theorem witness_12 : Positive 0 4106 := by
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

private theorem witness_13 : Positive 0 8197 := by
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

private theorem witness_14 : Positive 0 16394 := by
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

private theorem witness_15 : Positive 0 32773 := by
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

private theorem witness_16 : Positive 0 278 := by
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
  · left
    decide +kernel

private theorem witness_17 : Positive 0 284 := by
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
  · left
    decide +kernel

private theorem witness_18 : Positive 0 553 := by
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
  · left
    decide +kernel

private theorem witness_19 : Positive 0 556 := by
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
  · left
    decide +kernel

private theorem witness_20 : Positive 0 1091 := by
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
  · left
    decide +kernel

private theorem witness_21 : Positive 0 1097 := by
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
  · left
    decide +kernel

private theorem witness_22 : Positive 0 2179 := by
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
  · left
    decide +kernel

private theorem witness_23 : Positive 0 2182 := by
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
  · left
    decide +kernel

private theorem witness_24 : Positive 0 4118 := by
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
  · left
    decide +kernel

private theorem witness_25 : Positive 0 4124 := by
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
  · left
    decide +kernel

private theorem witness_26 : Positive 0 4358 := by
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
  · left
    decide +kernel

private theorem witness_27 : Positive 0 4364 := by
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
  · left
    decide +kernel

private theorem witness_28 : Positive 0 8233 := by
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
  · left
    decide +kernel

private theorem witness_29 : Positive 0 8236 := by
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
  · left
    decide +kernel

private theorem witness_30 : Positive 0 8713 := by
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
  · left
    decide +kernel

private theorem witness_31 : Positive 0 8716 := by
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
  · left
    decide +kernel

private theorem witness_32 : Positive 0 16451 := by
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
  · left
    decide +kernel

private theorem witness_33 : Positive 0 16457 := by
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
  · left
    decide +kernel

private theorem witness_34 : Positive 0 17411 := by
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
  · left
    decide +kernel

private theorem witness_35 : Positive 0 17417 := by
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
  · left
    decide +kernel

private theorem witness_36 : Positive 0 32899 := by
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
  · left
    decide +kernel

private theorem witness_37 : Positive 0 32902 := by
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
  · left
    decide +kernel

private theorem witness_38 : Positive 0 34819 := by
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
  · left
    decide +kernel

private theorem witness_39 : Positive 0 34822 := by
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
  · left
    decide +kernel

private theorem witness_40 : Positive 0 4513 := by
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

private theorem witness_41 : Positive 0 4576 := by
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

private theorem witness_42 : Positive 0 4681 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_43 : Positive 0 4684 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_44 : Positive 0 4742 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_45 : Positive 0 4748 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_46 : Positive 0 4804 := by
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

private theorem witness_47 : Positive 0 4808 := by
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

private theorem witness_48 : Positive 0 5056 := by
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

private theorem witness_49 : Positive 0 5161 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_50 : Positive 0 5164 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_51 : Positive 0 5251 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_52 : Positive 0 5254 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_53 : Positive 0 5762 := by
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

private theorem witness_54 : Positive 0 5764 := by
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

private theorem witness_55 : Positive 0 5776 := by
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

private theorem witness_56 : Positive 0 6182 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_57 : Positive 0 6188 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_58 : Positive 0 6211 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_59 : Positive 0 6214 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_60 : Positive 0 6242 := by
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

private theorem witness_61 : Positive 0 6244 := by
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

private theorem witness_62 : Positive 0 6496 := by
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

private theorem witness_63 : Positive 0 6673 := by
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

private theorem witness_64 : Positive 0 7204 := by
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

private theorem witness_65 : Positive 0 7208 := by
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

private theorem witness_66 : Positive 0 7216 := by
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

private theorem witness_67 : Positive 0 7696 := by
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

private theorem witness_68 : Positive 0 8521 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_69 : Positive 0 8524 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_70 : Positive 0 8582 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_71 : Positive 0 8588 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 6, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_72 : Positive 0 8644 := by
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

private theorem witness_73 : Positive 0 8648 := by
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

private theorem witness_74 : Positive 0 8786 := by
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

private theorem witness_75 : Positive 0 8912 := by
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
  · left
    decide +kernel

private theorem witness_76 : Positive 0 9152 := by
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
  · left
    decide +kernel

private theorem witness_77 : Positive 0 9241 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_78 : Positive 0 9244 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_79 : Positive 0 9347 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_80 : Positive 0 9353 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_81 : Positive 0 9361 := by
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

private theorem witness_82 : Positive 0 9368 := by
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

private theorem witness_83 : Positive 0 9506 := by
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

private theorem witness_84 : Positive 0 9872 := by
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

private theorem witness_85 : Positive 0 10262 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_86 : Positive 0 10268 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_87 : Positive 0 10307 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 2, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_88 : Positive 0 10313 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_89 : Positive 0 10561 := by
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

private theorem witness_90 : Positive 0 10568 := by
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

private theorem witness_91 : Positive 0 10592 := by
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

private theorem witness_92 : Positive 0 11284 := by
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

private theorem witness_93 : Positive 0 11288 := by
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

private theorem witness_94 : Positive 0 11312 := by
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
  · left
    decide +kernel

private theorem witness_95 : Positive 0 11552 := by
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
  · left
    decide +kernel

private theorem witness_96 : Positive 0 12736 := by
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
  · left
    decide +kernel

private theorem witness_97 : Positive 0 12992 := by
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

private theorem witness_98 : Positive 0 13441 := by
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

private theorem witness_99 : Positive 0 13442 := by
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

private theorem witness_100 : Positive 0 13504 := by
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

private theorem witness_101 : Positive 0 14401 := by
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

private theorem witness_102 : Positive 0 14402 := by
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

private theorem witness_103 : Positive 0 14528 := by
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
  · left
    decide +kernel

private theorem witness_104 : Positive 0 15376 := by
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
  · left
    decide +kernel

private theorem witness_105 : Positive 0 15392 := by
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

private theorem witness_106 : Positive 0 15424 := by
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
  · left
    decide +kernel

private theorem witness_107 : Positive 0 15488 := by
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

private theorem witness_108 : Positive 0 16681 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_109 : Positive 0 16684 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_110 : Positive 0 16771 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_111 : Positive 0 16774 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_112 : Positive 0 16921 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_113 : Positive 0 16924 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_114 : Positive 0 17027 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_115 : Positive 0 17033 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_116 : Positive 0 17041 := by
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

private theorem witness_117 : Positive 0 17048 := by
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

private theorem witness_118 : Positive 0 17281 := by
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

private theorem witness_119 : Positive 0 17282 := by
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

private theorem witness_120 : Positive 0 17344 := by
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

private theorem witness_121 : Positive 0 17572 := by
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

private theorem witness_122 : Positive 0 17584 := by
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
  · left
    decide +kernel

private theorem witness_123 : Positive 0 18064 := by
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
  · left
    decide +kernel

private theorem witness_124 : Positive 0 18451 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_125 : Positive 0 18454 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 2, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_126 : Positive 0 18467 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_127 : Positive 0 18473 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_128 : Positive 0 18481 := by
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

private theorem witness_129 : Positive 0 18482 := by
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

private theorem witness_130 : Positive 0 18721 := by
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

private theorem witness_131 : Positive 0 18728 := by
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

private theorem witness_132 : Positive 0 18784 := by
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
  · left
    decide +kernel

private theorem witness_133 : Positive 0 19012 := by
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

private theorem witness_134 : Positive 0 19264 := by
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
  · left
    decide +kernel

private theorem witness_135 : Positive 0 19504 := by
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

private theorem witness_136 : Positive 0 21026 := by
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

private theorem witness_137 : Positive 0 22664 := by
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

private theorem witness_138 : Positive 0 24962 := by
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

private theorem witness_139 : Positive 0 24964 := by
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

private theorem witness_140 : Positive 0 24976 := by
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

private theorem witness_141 : Positive 0 25232 := by
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
  · left
    decide +kernel

private theorem witness_142 : Positive 0 25744 := by
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

private theorem witness_143 : Positive 0 26642 := by
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

private theorem witness_144 : Positive 0 26644 := by
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

private theorem witness_145 : Positive 0 26768 := by
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
  · left
    decide +kernel

private theorem witness_146 : Positive 0 26896 := by
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
  · left
    decide +kernel

private theorem witness_147 : Positive 0 26912 := by
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
  · left
    decide +kernel

private theorem witness_148 : Positive 0 26944 := by
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

private theorem witness_149 : Positive 0 27008 := by
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

private theorem witness_150 : Positive 0 30848 := by
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

private theorem witness_151 : Positive 0 33062 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_152 : Positive 0 33068 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_153 : Positive 0 33091 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_154 : Positive 0 33094 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 5, 6}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_155 : Positive 0 33122 := by
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

private theorem witness_156 : Positive 0 33124 := by
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

private theorem witness_157 : Positive 0 33302 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_158 : Positive 0 33308 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 2, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_159 : Positive 0 33347 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_160 : Positive 0 33353 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_161 : Positive 0 33601 := by
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

private theorem witness_162 : Positive 0 33602 := by
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

private theorem witness_163 : Positive 0 33728 := by
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
  · left
    decide +kernel

private theorem witness_164 : Positive 0 33811 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_165 : Positive 0 33814 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_166 : Positive 0 33827 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {0, 4, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_167 : Positive 0 33833 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 2, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · right
    decide +kernel

private theorem witness_168 : Positive 0 33841 := by
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

private theorem witness_169 : Positive 0 33842 := by
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

private theorem witness_170 : Positive 0 34184 := by
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

private theorem witness_171 : Positive 0 34322 := by
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

private theorem witness_172 : Positive 0 34324 := by
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

private theorem witness_173 : Positive 0 34448 := by
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
  · left
    decide +kernel

private theorem witness_174 : Positive 0 34688 := by
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

private theorem witness_175 : Positive 0 34904 := by
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

private theorem witness_176 : Positive 0 34928 := by
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

private theorem witness_177 : Positive 0 35168 := by
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
  · left
    decide +kernel

private theorem witness_178 : Positive 0 35888 := by
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
  · left
    decide +kernel

private theorem witness_179 : Positive 0 37216 := by
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
  · left
    decide +kernel

private theorem witness_180 : Positive 0 37441 := by
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

private theorem witness_181 : Positive 0 37448 := by
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

private theorem witness_182 : Positive 0 37472 := by
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

private theorem witness_183 : Positive 0 37921 := by
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

private theorem witness_184 : Positive 0 37928 := by
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

private theorem witness_185 : Positive 0 37984 := by
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
  · left
    decide +kernel

private theorem witness_186 : Positive 0 38416 := by
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
  · left
    decide +kernel

private theorem witness_187 : Positive 0 38432 := by
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
  · left
    decide +kernel

private theorem witness_188 : Positive 0 38464 := by
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

private theorem witness_189 : Positive 0 38528 := by
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

private theorem witness_190 : Positive 0 39008 := by
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

private theorem witness_191 : Positive 0 41233 := by
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

private theorem witness_192 : Positive 0 42052 := by
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

private theorem witness_193 : Positive 0 46144 := by
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
  · left
    decide +kernel

private theorem witness_194 : Positive 0 49444 := by
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

private theorem witness_195 : Positive 0 49448 := by
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

private theorem witness_196 : Positive 0 49456 := by
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

private theorem witness_197 : Positive 0 49684 := by
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

private theorem witness_198 : Positive 0 49688 := by
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

private theorem witness_199 : Positive 0 49712 := by
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
  · left
    decide +kernel

private theorem witness_200 : Positive 0 49936 := by
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
  · left
    decide +kernel

private theorem witness_201 : Positive 0 49952 := by
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

private theorem witness_202 : Positive 0 49984 := by
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
  · left
    decide +kernel

private theorem witness_203 : Positive 0 50048 := by
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

private theorem witness_204 : Positive 0 50224 := by
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
  · left
    decide +kernel

private theorem witness_205 : Positive 0 51248 := by
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

private theorem witness_206 : Positive 0 53792 := by
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
  · left
    decide +kernel

private theorem witness_207 : Positive 0 57616 := by
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

private theorem witness_208 : Positive 0 963 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 6, 7}
    block := {0, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_209 : Positive 0 972 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 5}
    block := {0, 6, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_210 : Positive 0 1686 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 4, 7}
    block := {0, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_211 : Positive 0 1689 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 5, 6}
    block := {0, 4, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_212 : Positive 0 2406 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 7}
    block := {0, 5, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_213 : Positive 0 2409 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 5, 6}
    block := {0, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_214 : Positive 0 3123 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 6, 7}
    block := {0, 4, 1, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_215 : Positive 0 3132 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {1, 4, 5}
    block := {0, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_216 : Positive 0 12483 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 6, 7}
    block := {0, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_217 : Positive 0 12492 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 5}
    block := {0, 6, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_218 : Positive 0 15363 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 6, 7}
    block := {0, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_219 : Positive 0 15372 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 4, 5}
    block := {0, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_220 : Positive 0 24726 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 4, 7}
    block := {0, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_221 : Positive 0 24729 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 5, 6}
    block := {0, 4, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_222 : Positive 0 26886 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 4, 7}
    block := {0, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_223 : Positive 0 26889 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 5, 6}
    block := {0, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_224 : Positive 0 36966 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 7}
    block := {0, 5, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_225 : Positive 0 36969 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 5, 6}
    block := {0, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_226 : Positive 0 38406 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 4, 7}
    block := {0, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_227 : Positive 0 38409 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 5, 6}
    block := {0, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_228 : Positive 0 49203 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 6, 7}
    block := {0, 4, 1, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_229 : Positive 0 49212 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {1, 4, 5}
    block := {0, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_230 : Positive 0 49923 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 6, 7}
    block := {0, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private theorem witness_231 : Positive 0 49932 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {2, 4, 5}
    block := {0, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_, ?_⟩
  · decide +kernel
  · left
    decide +kernel

private def group_0 : List ℕ := [
  7, 11, 13, 14, 26, 37, 74, 133,
  266, 517, 1034, 2053, 4106, 8197, 16394, 32773]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) :
    Positive 0 m := by
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
  278, 284, 553, 556, 1091, 1097, 2179, 2182,
  4118, 4124, 4358, 4364, 8233, 8236, 8713, 8716]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) :
    Positive 0 m := by
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
  16451, 16457, 17411, 17417, 32899, 32902, 34819, 34822,
  4513, 4576, 4681, 4684, 4742, 4748, 4804, 4808]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) :
    Positive 0 m := by
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
  5056, 5161, 5164, 5251, 5254, 5762, 5764, 5776,
  6182, 6188, 6211, 6214, 6242, 6244, 6496, 6673]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) :
    Positive 0 m := by
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
  7204, 7208, 7216, 7696, 8521, 8524, 8582, 8588,
  8644, 8648, 8786, 8912, 9152, 9241, 9244, 9347]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) :
    Positive 0 m := by
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
  9353, 9361, 9368, 9506, 9872, 10262, 10268, 10307,
  10313, 10561, 10568, 10592, 11284, 11288, 11312, 11552]

private theorem group_sound_5 {m : ℕ} (h : m ∈ group_5) :
    Positive 0 m := by
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
  12736, 12992, 13441, 13442, 13504, 14401, 14402, 14528,
  15376, 15392, 15424, 15488, 16681, 16684, 16771, 16774]

private theorem group_sound_6 {m : ℕ} (h : m ∈ group_6) :
    Positive 0 m := by
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
  16921, 16924, 17027, 17033, 17041, 17048, 17281, 17282,
  17344, 17572, 17584, 18064, 18451, 18454, 18467, 18473]

private theorem group_sound_7 {m : ℕ} (h : m ∈ group_7) :
    Positive 0 m := by
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
  18481, 18482, 18721, 18728, 18784, 19012, 19264, 19504,
  21026, 22664, 24962, 24964, 24976, 25232, 25744, 26642]

private theorem group_sound_8 {m : ℕ} (h : m ∈ group_8) :
    Positive 0 m := by
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
  26644, 26768, 26896, 26912, 26944, 27008, 30848, 33062,
  33068, 33091, 33094, 33122, 33124, 33302, 33308, 33347]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) :
    Positive 0 m := by
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
  33353, 33601, 33602, 33728, 33811, 33814, 33827, 33833,
  33841, 33842, 34184, 34322, 34324, 34448, 34688, 34904]

private theorem group_sound_10 {m : ℕ} (h : m ∈ group_10) :
    Positive 0 m := by
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
  34928, 35168, 35888, 37216, 37441, 37448, 37472, 37921,
  37928, 37984, 38416, 38432, 38464, 38528, 39008, 41233]

private theorem group_sound_11 {m : ℕ} (h : m ∈ group_11) :
    Positive 0 m := by
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
  42052, 46144, 49444, 49448, 49456, 49684, 49688, 49712,
  49936, 49952, 49984, 50048, 50224, 51248, 53792, 57616]

private theorem group_sound_12 {m : ℕ} (h : m ∈ group_12) :
    Positive 0 m := by
  simp only [group_12, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_192
  · exact witness_193
  · exact witness_194
  · exact witness_195
  · exact witness_196
  · exact witness_197
  · exact witness_198
  · exact witness_199
  · exact witness_200
  · exact witness_201
  · exact witness_202
  · exact witness_203
  · exact witness_204
  · exact witness_205
  · exact witness_206
  · exact witness_207

private def group_13 : List ℕ := [
  963, 972, 1686, 1689, 2406, 2409, 3123, 3132,
  12483, 12492, 15363, 15372, 24726, 24729, 26886, 26889]

private theorem group_sound_13 {m : ℕ} (h : m ∈ group_13) :
    Positive 0 m := by
  simp only [group_13, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_208
  · exact witness_209
  · exact witness_210
  · exact witness_211
  · exact witness_212
  · exact witness_213
  · exact witness_214
  · exact witness_215
  · exact witness_216
  · exact witness_217
  · exact witness_218
  · exact witness_219
  · exact witness_220
  · exact witness_221
  · exact witness_222
  · exact witness_223

private def group_14 : List ℕ := [
  36966, 36969, 38406, 38409, 49203, 49212, 49923, 49932]

private theorem group_sound_14 {m : ℕ} (h : m ∈ group_14) :
    Positive 0 m := by
  simp only [group_14, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact witness_224
  · exact witness_225
  · exact witness_226
  · exact witness_227
  · exact witness_228
  · exact witness_229
  · exact witness_230
  · exact witness_231

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 0 m := by
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
      m ∈ group_12 ∨
      m ∈ group_13 ∨
      m ∈ group_14 := by
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
      group_12 ++
      group_13 ++
      group_14 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
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
  · exact group_sound_13 hg
  · exact group_sound_14 hg

theorem finite_positive (m : Fin 65536) (h : 13 ≤ weightedCount m.val) :
    Positive 0 m.val := by
  have hc := coverage m h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.Unattached.D0
