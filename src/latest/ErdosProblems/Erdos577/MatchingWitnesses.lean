import ErdosProblems.Erdos577.MatchingMasks

/-! Explicit factors, five-edge triangle reductions, and six-edge path reductions. -/

namespace Erdos577.MatchingExchange

open Finset

private theorem witness_0 : Positive 4680 := by
  left
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_1 : Positive 4740 := by
  left
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_2 : Positive 6180 := by
  left
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_3 : Positive 6210 := by
  left
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_4 : Positive 8520 := by
  left
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_5 : Positive 8580 := by
  left
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_6 : Positive 9240 := by
  left
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_7 : Positive 9345 := by
  left
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_8 : Positive 16920 := by
  left
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_9 : Positive 17025 := by
  left
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_10 : Positive 18450 := by
  left
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_11 : Positive 18465 := by
  left
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_12 : Positive 33060 := by
  left
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_13 : Positive 33090 := by
  left
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_14 : Positive 33810 := by
  left
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_15 : Positive 33825 := by
  left
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem witness_16 : Positive 358 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 4, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_17 : Positive 460 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 4, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_18 : Positive 665 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 5, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_19 : Positive 716 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 5, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_20 : Positive 844 := by
  left
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

private theorem witness_21 : Positive 908 := by
  left
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

private theorem witness_22 : Positive 964 := by
  left
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

private theorem witness_23 : Positive 968 := by
  left
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

private theorem witness_24 : Positive 1075 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 6, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_25 : Positive 1177 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 6, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_26 : Positive 1561 := by
  left
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

private theorem witness_27 : Positive 1673 := by
  left
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

private theorem witness_28 : Positive 1681 := by
  left
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

private theorem witness_29 : Positive 1688 := by
  left
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

private theorem witness_30 : Positive 1928 := by
  left
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

private theorem witness_31 : Positive 2099 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 7, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_32 : Positive 2150 := by
  right
  refine ⟨{
    vertices := { toFun := ![3, 2, 7, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_33 : Positive 2342 := by
  left
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

private theorem witness_34 : Positive 2374 := by
  left
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

private theorem witness_35 : Positive 2402 := by
  left
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

private theorem witness_36 : Positive 2404 := by
  left
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

private theorem witness_37 : Positive 2884 := by
  left
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

private theorem witness_38 : Positive 3091 := by
  left
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

private theorem witness_39 : Positive 3107 := by
  left
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

private theorem witness_40 : Positive 3121 := by
  left
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

private theorem witness_41 : Positive 3122 := by
  left
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

private theorem witness_42 : Positive 3362 := by
  left
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

private theorem witness_43 : Positive 3601 := by
  left
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

private theorem witness_44 : Positive 4198 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 4, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_45 : Positive 4300 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 4, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_46 : Positive 4366 := by
  left
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

private theorem witness_47 : Positive 4390 := by
  left
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

private theorem witness_48 : Positive 4422 := by
  left
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

private theorem witness_49 : Positive 4428 := by
  left
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

private theorem witness_50 : Positive 4450 := by
  left
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

private theorem witness_51 : Positive 4452 := by
  left
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

private theorem witness_52 : Positive 4492 := by
  left
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

private theorem witness_53 : Positive 4548 := by
  left
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

private theorem witness_54 : Positive 4552 := by
  left
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

private theorem witness_55 : Positive 4576 := by
  left
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

private theorem witness_56 : Positive 4876 := by
  left
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

private theorem witness_57 : Positive 4932 := by
  left
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

private theorem witness_58 : Positive 5000 := by
  left
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

private theorem witness_59 : Positive 5056 := by
  left
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

private theorem witness_60 : Positive 6406 := by
  left
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

private theorem witness_61 : Positive 6434 := by
  left
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

private theorem witness_62 : Positive 6468 := by
  left
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

private theorem witness_63 : Positive 6496 := by
  left
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

private theorem witness_64 : Positive 8345 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 5, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_65 : Positive 8396 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 5, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_66 : Positive 8717 := by
  left
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

private theorem witness_67 : Positive 8729 := by
  left
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

private theorem witness_68 : Positive 8780 := by
  left
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

private theorem witness_69 : Positive 8841 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 5}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_70 : Positive 8844 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 5}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_71 : Positive 8849 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 5}
    block := {0, 1, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_72 : Positive 8856 := by
  left
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

private theorem witness_73 : Positive 8900 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 5}
    block := {0, 1, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_74 : Positive 8904 := by
  left
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

private theorem witness_75 : Positive 8912 := by
  left
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

private theorem witness_76 : Positive 8972 := by
  left
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

private theorem witness_77 : Positive 9028 := by
  left
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

private theorem witness_78 : Positive 9096 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_79 : Positive 9152 := by
  left
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

private theorem witness_80 : Positive 9737 := by
  left
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

private theorem witness_81 : Positive 9745 := by
  left
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

private theorem witness_82 : Positive 9864 := by
  left
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

private theorem witness_83 : Positive 9872 := by
  left
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

private theorem witness_84 : Positive 12364 := by
  left
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

private theorem witness_85 : Positive 12428 := by
  left
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

private theorem witness_86 : Positive 12484 := by
  left
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

private theorem witness_87 : Positive 12488 := by
  left
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

private theorem witness_88 : Positive 12556 := by
  left
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

private theorem witness_89 : Positive 12612 := by
  left
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

private theorem witness_90 : Positive 12680 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 7}
    block := {2, 3, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_91 : Positive 12736 := by
  left
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

private theorem witness_92 : Positive 12812 := by
  left
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

private theorem witness_93 : Positive 12868 := by
  left
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

private theorem witness_94 : Positive 12936 := by
  left
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

private theorem witness_95 : Positive 12992 := by
  left
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

private theorem witness_96 : Positive 13060 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 6, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_97 : Positive 13064 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 7, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_98 : Positive 13120 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 6, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_99 : Positive 13184 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 7, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_100 : Positive 16435 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 6, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_101 : Positive 16537 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 6, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_102 : Positive 17419 := by
  left
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

private theorem witness_103 : Positive 17427 := by
  left
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

private theorem witness_104 : Positive 17433 := by
  left
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

private theorem witness_105 : Positive 17443 := by
  left
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

private theorem witness_106 : Positive 17457 := by
  left
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

private theorem witness_107 : Positive 17458 := by
  left
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

private theorem witness_108 : Positive 17545 := by
  left
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

private theorem witness_109 : Positive 17553 := by
  left
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

private theorem witness_110 : Positive 17560 := by
  left
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

private theorem witness_111 : Positive 17584 := by
  left
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

private theorem witness_112 : Positive 17929 := by
  left
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

private theorem witness_113 : Positive 17937 := by
  left
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

private theorem witness_114 : Positive 18056 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_115 : Positive 18064 := by
  left
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

private theorem witness_116 : Positive 19459 := by
  left
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

private theorem witness_117 : Positive 19473 := by
  left
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

private theorem witness_118 : Positive 19490 := by
  left
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

private theorem witness_119 : Positive 19504 := by
  left
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

private theorem witness_120 : Positive 24601 := by
  left
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

private theorem witness_121 : Positive 24713 := by
  left
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

private theorem witness_122 : Positive 24721 := by
  left
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

private theorem witness_123 : Positive 24728 := by
  left
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

private theorem witness_124 : Positive 25097 := by
  left
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

private theorem witness_125 : Positive 25105 := by
  left
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

private theorem witness_126 : Positive 25224 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 7}
    block := {2, 3, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_127 : Positive 25232 := by
  left
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

private theorem witness_128 : Positive 25609 := by
  left
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

private theorem witness_129 : Positive 25617 := by
  left
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

private theorem witness_130 : Positive 25736 := by
  left
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

private theorem witness_131 : Positive 25744 := by
  left
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

private theorem witness_132 : Positive 26113 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 4, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_133 : Positive 26120 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 7, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_134 : Positive 26128 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 4, 7], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_135 : Positive 26240 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 7, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_136 : Positive 28808 := by
  left
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

private theorem witness_137 : Positive 32819 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 7, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_138 : Positive 32870 := by
  right
  refine ⟨{
    vertices := { toFun := ![2, 3, 7, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_139 : Positive 34823 := by
  left
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

private theorem witness_140 : Positive 34835 := by
  left
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

private theorem witness_141 : Positive 34851 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 7}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_142 : Positive 34854 := by
  left
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

private theorem witness_143 : Positive 34865 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {2, 3, 7}
    block := {0, 1, 5, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_144 : Positive 34866 := by
  left
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

private theorem witness_145 : Positive 34886 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 7}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_146 : Positive 34914 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {2, 3, 7}
    block := {0, 1, 6, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_147 : Positive 34916 := by
  left
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

private theorem witness_148 : Positive 34928 := by
  left
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

private theorem witness_149 : Positive 35078 := by
  left
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

private theorem witness_150 : Positive 35106 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 5}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_151 : Positive 35140 := by
  left
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

private theorem witness_152 : Positive 35168 := by
  left
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

private theorem witness_153 : Positive 35843 := by
  left
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

private theorem witness_154 : Positive 35857 := by
  left
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

private theorem witness_155 : Positive 35874 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_156 : Positive 35888 := by
  left
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

private theorem witness_157 : Positive 36902 := by
  left
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

private theorem witness_158 : Positive 36934 := by
  left
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

private theorem witness_159 : Positive 36962 := by
  left
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

private theorem witness_160 : Positive 36964 := by
  left
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

private theorem witness_161 : Positive 37126 := by
  left
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

private theorem witness_162 : Positive 37154 := by
  left
  right
  refine ⟨{
    terminal := 6
    triangle := {0, 1, 5}
    block := {2, 3, 7, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_163 : Positive 37188 := by
  left
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

private theorem witness_164 : Positive 37216 := by
  left
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

private theorem witness_165 : Positive 38918 := by
  left
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

private theorem witness_166 : Positive 38946 := by
  left
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

private theorem witness_167 : Positive 38980 := by
  left
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

private theorem witness_168 : Positive 39008 := by
  left
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

private theorem witness_169 : Positive 39170 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 5, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_170 : Positive 39172 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 6, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_171 : Positive 39200 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 5, 6], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_172 : Positive 39232 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 6, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_173 : Positive 45124 := by
  left
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

private theorem witness_174 : Positive 49171 := by
  left
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

private theorem witness_175 : Positive 49187 := by
  left
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

private theorem witness_176 : Positive 49201 := by
  left
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

private theorem witness_177 : Positive 49202 := by
  left
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

private theorem witness_178 : Positive 50179 := by
  left
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

private theorem witness_179 : Positive 50193 := by
  left
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

private theorem witness_180 : Positive 50210 := by
  left
  right
  refine ⟨{
    terminal := 4
    triangle := {0, 1, 5}
    block := {2, 3, 7, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_181 : Positive 50224 := by
  left
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

private theorem witness_182 : Positive 51203 := by
  left
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

private theorem witness_183 : Positive 51217 := by
  left
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

private theorem witness_184 : Positive 51234 := by
  left
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

private theorem witness_185 : Positive 51248 := by
  left
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

private theorem witness_186 : Positive 52225 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 4, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_187 : Positive 52226 := by
  right
  refine ⟨{
    vertices := { toFun := ![1, 0, 5, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_188 : Positive 52240 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 4, 5], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_189 : Positive 52256 := by
  right
  refine ⟨{
    vertices := { toFun := ![0, 1, 5, 4], inj' := by decide +kernel }
    adjacent := by decide +kernel }, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · decide +kernel

private theorem witness_190 : Positive 53282 := by
  left
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

private theorem witness_191 : Positive 57361 := by
  left
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

private theorem witness_192 : Positive 828 := by
  left
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 6, 7}
    block := {1, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_193 : Positive 963 := by
  left
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

private theorem witness_194 : Positive 1641 := by
  left
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 7}
    block := {1, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_195 : Positive 1686 := by
  left
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

private theorem witness_196 : Positive 2409 := by
  left
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

private theorem witness_197 : Positive 2454 := by
  left
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 5, 6}
    block := {1, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_198 : Positive 3132 := by
  left
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

private theorem witness_199 : Positive 3267 := by
  left
  right
  refine ⟨{
    terminal := 3
    triangle := {0, 4, 5}
    block := {1, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_200 : Positive 4522 := by
  left
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

private theorem witness_201 : Positive 8789 := by
  left
  right
  refine ⟨{
    terminal := 7
    triangle := {2, 3, 5}
    block := {0, 4, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_202 : Positive 12348 := by
  left
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 6, 7}
    block := {1, 4, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_203 : Positive 12483 := by
  left
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

private theorem witness_204 : Positive 15363 := by
  left
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

private theorem witness_205 : Positive 15372 := by
  left
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

private theorem witness_206 : Positive 15408 := by
  left
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

private theorem witness_207 : Positive 15552 := by
  left
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 5}
    block := {1, 6, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_208 : Positive 17578 := by
  left
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

private theorem witness_209 : Positive 21794 := by
  left
  right
  refine ⟨{
    terminal := 7
    triangle := {0, 1, 5}
    block := {2, 4, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_210 : Positive 21896 := by
  left
  right
  refine ⟨{
    terminal := 5
    triangle := {0, 1, 7}
    block := {2, 4, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_211 : Positive 24681 := by
  left
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 7}
    block := {1, 5, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_212 : Positive 24726 := by
  left
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

private theorem witness_213 : Positive 26886 := by
  left
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

private theorem witness_214 : Positive 26889 := by
  left
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

private theorem witness_215 : Positive 26976 := by
  left
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

private theorem witness_216 : Positive 27024 := by
  left
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 5, 6}
    block := {1, 4, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_217 : Positive 34901 := by
  left
  right
  refine ⟨{
    terminal := 5
    triangle := {2, 3, 7}
    block := {0, 4, 1, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_218 : Positive 36969 := by
  left
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

private theorem witness_219 : Positive 37014 := by
  left
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 5, 6}
    block := {1, 4, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_220 : Positive 38406 := by
  left
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

private theorem witness_221 : Positive 38409 := by
  left
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

private theorem witness_222 : Positive 38496 := by
  left
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 4, 7}
    block := {1, 5, 2, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_223 : Positive 38544 := by
  left
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

private theorem witness_224 : Positive 43537 := by
  left
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

private theorem witness_225 : Positive 43588 := by
  left
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

private theorem witness_226 : Positive 49212 := by
  left
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

private theorem witness_227 : Positive 49347 := by
  left
  right
  refine ⟨{
    terminal := 2
    triangle := {0, 4, 5}
    block := {1, 6, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_228 : Positive 49923 := by
  left
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

private theorem witness_229 : Positive 49932 := by
  left
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

private theorem witness_230 : Positive 49968 := by
  left
  right
  refine ⟨{
    terminal := 0
    triangle := {3, 6, 7}
    block := {1, 4, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem witness_231 : Positive 50112 := by
  left
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
  4680, 4740, 6180, 6210, 8520, 8580, 9240, 9345,
  16920, 17025, 18450, 18465, 33060, 33090, 33810, 33825]

private theorem group_sound_0 {m : ℕ} (h : m ∈ group_0) : Positive m := by
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
  358, 460, 665, 716, 844, 908, 964, 968,
  1075, 1177, 1561, 1673, 1681, 1688, 1928, 2099]

private theorem group_sound_1 {m : ℕ} (h : m ∈ group_1) : Positive m := by
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
  2150, 2342, 2374, 2402, 2404, 2884, 3091, 3107,
  3121, 3122, 3362, 3601, 4198, 4300, 4366, 4390]

private theorem group_sound_2 {m : ℕ} (h : m ∈ group_2) : Positive m := by
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
  4422, 4428, 4450, 4452, 4492, 4548, 4552, 4576,
  4876, 4932, 5000, 5056, 6406, 6434, 6468, 6496]

private theorem group_sound_3 {m : ℕ} (h : m ∈ group_3) : Positive m := by
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
  8345, 8396, 8717, 8729, 8780, 8841, 8844, 8849,
  8856, 8900, 8904, 8912, 8972, 9028, 9096, 9152]

private theorem group_sound_4 {m : ℕ} (h : m ∈ group_4) : Positive m := by
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
  9737, 9745, 9864, 9872, 12364, 12428, 12484, 12488,
  12556, 12612, 12680, 12736, 12812, 12868, 12936, 12992]

private theorem group_sound_5 {m : ℕ} (h : m ∈ group_5) : Positive m := by
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
  13060, 13064, 13120, 13184, 16435, 16537, 17419, 17427,
  17433, 17443, 17457, 17458, 17545, 17553, 17560, 17584]

private theorem group_sound_6 {m : ℕ} (h : m ∈ group_6) : Positive m := by
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
  17929, 17937, 18056, 18064, 19459, 19473, 19490, 19504,
  24601, 24713, 24721, 24728, 25097, 25105, 25224, 25232]

private theorem group_sound_7 {m : ℕ} (h : m ∈ group_7) : Positive m := by
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
  25609, 25617, 25736, 25744, 26113, 26120, 26128, 26240,
  28808, 32819, 32870, 34823, 34835, 34851, 34854, 34865]

private theorem group_sound_8 {m : ℕ} (h : m ∈ group_8) : Positive m := by
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
  34866, 34886, 34914, 34916, 34928, 35078, 35106, 35140,
  35168, 35843, 35857, 35874, 35888, 36902, 36934, 36962]

private theorem group_sound_9 {m : ℕ} (h : m ∈ group_9) : Positive m := by
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
  36964, 37126, 37154, 37188, 37216, 38918, 38946, 38980,
  39008, 39170, 39172, 39200, 39232, 45124, 49171, 49187]

private theorem group_sound_10 {m : ℕ} (h : m ∈ group_10) : Positive m := by
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
  49201, 49202, 50179, 50193, 50210, 50224, 51203, 51217,
  51234, 51248, 52225, 52226, 52240, 52256, 53282, 57361]

private theorem group_sound_11 {m : ℕ} (h : m ∈ group_11) : Positive m := by
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
  828, 963, 1641, 1686, 2409, 2454, 3132, 3267,
  4522, 8789, 12348, 12483, 15363, 15372, 15408, 15552]

private theorem group_sound_12 {m : ℕ} (h : m ∈ group_12) : Positive m := by
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
  17578, 21794, 21896, 24681, 24726, 26886, 26889, 26976,
  27024, 34901, 36969, 37014, 38406, 38409, 38496, 38544]

private theorem group_sound_13 {m : ℕ} (h : m ∈ group_13) : Positive m := by
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
  43537, 43588, 49212, 49347, 49923, 49932, 49968, 50112]

private theorem group_sound_14 {m : ℕ} (h : m ∈ group_14) : Positive m := by
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

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive m := by
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

theorem finite_positive (m : Fin 65536) (h : 9 ≤ PathExchange.crossCount m.val) :
    Positive m.val := by
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp (coverage m h)
  exact (masks_sound hw).mono (beq_iff_eq.mp hsub)

end Erdos577.MatchingExchange
