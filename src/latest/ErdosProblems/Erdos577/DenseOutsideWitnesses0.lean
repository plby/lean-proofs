import ErdosProblems.Erdos577.DenseOutsideMasks0

/-! Explicit factors or strict edge gains for diagonal mask 0. -/

namespace Erdos577.DenseOutside.D0

open Finset Unattached

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
    cover := by decide +kernel }, ?_⟩
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
    cover := by decide +kernel }, ?_⟩
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
    cover := by decide +kernel }, ?_⟩
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
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_4 : Positive 0 278 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_5 : Positive 0 282 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 0 284 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 3, 2, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_7 : Positive 0 549 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_8 : Positive 0 553 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_9 : Positive 0 556 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 3, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_10 : Positive 0 1091 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_11 : Positive 0 1097 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 3, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_12 : Positive 0 1098 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_13 : Positive 0 2179 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_14 : Positive 0 2181 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_15 : Positive 0 2182 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 5, 6}
    block := {1, 3, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_16 : Positive 0 4118 := by
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

private theorem witness_17 : Positive 0 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_18 : Positive 0 4124 := by
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

private theorem witness_19 : Positive 0 4358 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 5, 6}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_20 : Positive 0 4362 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_21 : Positive 0 4364 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 6, 7}
    block := {1, 2, 4, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_22 : Positive 0 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_23 : Positive 0 8233 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_24 : Positive 0 8236 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 2, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_25 : Positive 0 8709 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_26 : Positive 0 8713 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_27 : Positive 0 8716 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 6, 7}
    block := {1, 2, 5, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_28 : Positive 0 16451 := by
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

private theorem witness_29 : Positive 0 16457 := by
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

private theorem witness_30 : Positive 0 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_31 : Positive 0 17411 := by
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 4, 5}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_32 : Positive 0 17417 := by
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 4, 7}
    block := {1, 2, 6, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_33 : Positive 0 17418 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_34 : Positive 0 32899 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_35 : Positive 0 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_36 : Positive 0 32902 := by
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 5, 6}
    block := {1, 2, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_37 : Positive 0 34819 := by
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 4, 5}
    block := {1, 2, 7, 3}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_38 : Positive 0 34821 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

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
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_40 : Positive 0 4576 := by
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

private theorem witness_41 : Positive 0 5056 := by
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

private theorem witness_42 : Positive 0 5776 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_43 : Positive 0 6496 := by
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

private theorem witness_44 : Positive 0 7216 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_45 : Positive 0 7696 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 4}
    block := {2, 5, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_46 : Positive 0 8912 := by
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

private theorem witness_47 : Positive 0 9152 := by
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

private theorem witness_48 : Positive 0 9872 := by
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

private theorem witness_49 : Positive 0 10592 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_50 : Positive 0 11312 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_51 : Positive 0 11552 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 5}
    block := {2, 4, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_52 : Positive 0 12736 := by
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

private theorem witness_53 : Positive 0 12992 := by
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

private theorem witness_54 : Positive 0 13504 := by
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

private theorem witness_55 : Positive 0 14528 := by
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

private theorem witness_56 : Positive 0 15376 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_57 : Positive 0 15392 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 6, 7}
    block := {1, 3, 4, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_58 : Positive 0 15424 := by
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

private theorem witness_59 : Positive 0 15488 := by
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

private theorem witness_60 : Positive 0 17344 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_61 : Positive 0 17584 := by
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

private theorem witness_62 : Positive 0 18064 := by
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

private theorem witness_63 : Positive 0 18784 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_64 : Positive 0 19264 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 6}
    block := {2, 5, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_65 : Positive 0 19504 := by
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

private theorem witness_66 : Positive 0 24976 := by
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

private theorem witness_67 : Positive 0 25232 := by
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

private theorem witness_68 : Positive 0 25744 := by
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

private theorem witness_69 : Positive 0 26768 := by
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

private theorem witness_70 : Positive 0 26896 := by
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

private theorem witness_71 : Positive 0 26912 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_72 : Positive 0 26944 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 7}
    block := {1, 3, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_73 : Positive 0 27008 := by
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

private theorem witness_74 : Positive 0 30848 := by
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

private theorem witness_75 : Positive 0 33728 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_76 : Positive 0 34448 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_77 : Positive 0 34688 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {1, 3, 7}
    block := {2, 4, 5, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_78 : Positive 0 34928 := by
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

private theorem witness_79 : Positive 0 35168 := by
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

private theorem witness_80 : Positive 0 35888 := by
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

private theorem witness_81 : Positive 0 37216 := by
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

private theorem witness_82 : Positive 0 37472 := by
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

private theorem witness_83 : Positive 0 37984 := by
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

private theorem witness_84 : Positive 0 38416 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_85 : Positive 0 38432 := by
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

private theorem witness_86 : Positive 0 38464 := by
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

private theorem witness_87 : Positive 0 38528 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 5, 6}
    block := {1, 3, 4, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_88 : Positive 0 39008 := by
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

private theorem witness_89 : Positive 0 46144 := by
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

private theorem witness_90 : Positive 0 49456 := by
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

private theorem witness_91 : Positive 0 49712 := by
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

private theorem witness_92 : Positive 0 49936 := by
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

private theorem witness_93 : Positive 0 49952 := by
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

private theorem witness_94 : Positive 0 49984 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_95 : Positive 0 50048 := by
  right
  refine ⟨{
    terminal := 0
    triangle := {2, 4, 5}
    block := {1, 3, 6, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_96 : Positive 0 50224 := by
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

private theorem witness_97 : Positive 0 51248 := by
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

private theorem witness_98 : Positive 0 53792 := by
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

private theorem witness_99 : Positive 0 57616 := by
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

private theorem witness_100 : Positive 0 963 := by
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

private theorem witness_101 : Positive 0 972 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 5}
    block := {0, 6, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_102 : Positive 0 1686 := by
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

private theorem witness_103 : Positive 0 1689 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 5, 6}
    block := {0, 4, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_104 : Positive 0 2406 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 4, 7}
    block := {0, 5, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_105 : Positive 0 2409 := by
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

private theorem witness_106 : Positive 0 3123 := by
  right
  refine ⟨{
    terminal := 3
    triangle := {2, 6, 7}
    block := {0, 4, 1, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_107 : Positive 0 3132 := by
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

private theorem witness_108 : Positive 0 4812 := by
  left
  refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_109 : Positive 0 5766 := by
  left
  refine ⟨{0, 5, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_110 : Positive 0 6246 := by
  left
  refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_111 : Positive 0 7212 := by
  left
  refine ⟨{0, 6, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_112 : Positive 0 8652 := by
  left
  refine ⟨{0, 6, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_113 : Positive 0 9369 := by
  left
  refine ⟨{0, 4, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_114 : Positive 0 10569 := by
  left
  refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_115 : Positive 0 11292 := by
  left
  refine ⟨{0, 6, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_116 : Positive 0 12483 := by
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

private theorem witness_117 : Positive 0 12492 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 5}
    block := {0, 6, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_118 : Positive 0 13443 := by
  left
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_119 : Positive 0 14403 := by
  left
  refine ⟨{0, 4, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_120 : Positive 0 15363 := by
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

private theorem witness_121 : Positive 0 15372 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 4, 5}
    block := {0, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_122 : Positive 0 17049 := by
  left
  refine ⟨{0, 4, 1, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_123 : Positive 0 17283 := by
  left
  refine ⟨{0, 4, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_124 : Positive 0 18483 := by
  left
  refine ⟨{0, 4, 1, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_125 : Positive 0 18729 := by
  left
  refine ⟨{0, 4, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_126 : Positive 0 24726 := by
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

private theorem witness_127 : Positive 0 24729 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 5, 6}
    block := {0, 4, 1, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_128 : Positive 0 24966 := by
  left
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_129 : Positive 0 26646 := by
  left
  refine ⟨{0, 5, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_130 : Positive 0 26886 := by
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

private theorem witness_131 : Positive 0 26889 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 5, 6}
    block := {0, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_132 : Positive 0 33126 := by
  left
  refine ⟨{0, 5, 1, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_133 : Positive 0 33603 := by
  left
  refine ⟨{0, 4, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_134 : Positive 0 33843 := by
  left
  refine ⟨{0, 4, 1, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_135 : Positive 0 34326 := by
  left
  refine ⟨{0, 5, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_136 : Positive 0 36966 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 4, 7}
    block := {0, 5, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_137 : Positive 0 36969 := by
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

private theorem witness_138 : Positive 0 37449 := by
  left
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_139 : Positive 0 37929 := by
  left
  refine ⟨{0, 4, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_140 : Positive 0 38406 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 4, 7}
    block := {0, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_141 : Positive 0 38409 := by
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

private theorem witness_142 : Positive 0 49203 := by
  right
  refine ⟨{
    terminal := 2
    triangle := {3, 6, 7}
    block := {0, 4, 1, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_143 : Positive 0 49212 := by
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

private theorem witness_144 : Positive 0 49452 := by
  left
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_145 : Positive 0 49692 := by
  left
  refine ⟨{0, 6, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_146 : Positive 0 49923 := by
  right
  refine ⟨{
    terminal := 1
    triangle := {3, 6, 7}
    block := {0, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_147 : Positive 0 49932 := by
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

private def group_0 : List ℕ := [
  7, 11, 13, 14, 278, 282, 284, 549,
  553, 556, 1091, 1097, 1098, 2179, 2181, 2182]

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
  4118, 4122, 4124, 4358, 4362, 4364, 8229, 8233,
  8236, 8709, 8713, 8716, 16451, 16457, 16458, 17411]

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
  17417, 17418, 32899, 32901, 32902, 34819, 34821, 34822,
  4576, 5056, 5776, 6496, 7216, 7696, 8912, 9152]

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
  9872, 10592, 11312, 11552, 12736, 12992, 13504, 14528,
  15376, 15392, 15424, 15488, 17344, 17584, 18064, 18784]

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
  19264, 19504, 24976, 25232, 25744, 26768, 26896, 26912,
  26944, 27008, 30848, 33728, 34448, 34688, 34928, 35168]

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
  35888, 37216, 37472, 37984, 38416, 38432, 38464, 38528,
  39008, 46144, 49456, 49712, 49936, 49952, 49984, 50048]

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
  50224, 51248, 53792, 57616, 963, 972, 1686, 1689,
  2406, 2409, 3123, 3132, 4812, 5766, 6246, 7212]

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
  8652, 9369, 10569, 11292, 12483, 12492, 13443, 14403,
  15363, 15372, 17049, 17283, 18483, 18729, 24726, 24729]

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
  24966, 26646, 26886, 26889, 33126, 33603, 33843, 34326,
  36966, 36969, 37449, 37929, 38406, 38409, 49203, 49212]

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
  49452, 49692, 49923, 49932]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) :
    Positive 0 m := by
  simp only [group_9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl
  · exact witness_144
  · exact witness_145
  · exact witness_146
  · exact witness_147

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

theorem finite_positive (m : Fin 65536) (hz : 2 ≤ terminalCount m.val)
    (ht : 9 ≤ triangleCount m.val) : Positive 0 m.val := by
  have hc := coverage m hz ht
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hc
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.DenseOutside.D0
