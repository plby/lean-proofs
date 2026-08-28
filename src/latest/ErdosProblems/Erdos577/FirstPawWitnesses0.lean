import ErdosProblems.Erdos577.FirstPawMasks0

/-! Explicit factors, strict triangle gains, and two-edge-remainder gains. -/

namespace Erdos577.FirstPaw.D0

open Finset

private theorem positive_0 : Positive 0 7 := by
  right
  left
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

private theorem positive_1 : Positive 0 11 := by
  right
  left
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

private theorem positive_2 : Positive 0 13 := by
  right
  left
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

private theorem positive_3 : Positive 0 14 := by
  right
  left
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

private theorem positive_4 : Positive 0 51 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 51) := {
    vertices := ⟨![2, 3, 6, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_5 : Positive 0 102 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 102) := {
    vertices := ⟨![2, 3, 4, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_6 : Positive 0 153 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 153) := {
    vertices := ⟨![2, 3, 5, 6], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_7 : Positive 0 204 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 204) := {
    vertices := ⟨![2, 3, 4, 5], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_8 : Positive 0 278 := by
  right
  left
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

private theorem positive_9 : Positive 0 282 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_10 : Positive 0 284 := by
  right
  left
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

private theorem positive_11 : Positive 0 549 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_12 : Positive 0 553 := by
  right
  left
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

private theorem positive_13 : Positive 0 556 := by
  right
  left
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

private theorem positive_14 : Positive 0 1091 := by
  right
  left
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

private theorem positive_15 : Positive 0 1097 := by
  right
  left
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

private theorem positive_16 : Positive 0 1098 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_17 : Positive 0 2179 := by
  right
  left
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

private theorem positive_18 : Positive 0 2181 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_19 : Positive 0 2182 := by
  right
  left
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

private theorem positive_20 : Positive 0 4118 := by
  right
  left
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

private theorem positive_21 : Positive 0 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_22 : Positive 0 4124 := by
  right
  left
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

private theorem positive_23 : Positive 0 4358 := by
  right
  left
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

private theorem positive_24 : Positive 0 4362 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_25 : Positive 0 4364 := by
  right
  left
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

private theorem positive_26 : Positive 0 4370 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 4370) := {
    vertices := ⟨![0, 5, 6, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_27 : Positive 0 4376 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 4376) := {
    vertices := ⟨![0, 7, 5, 6], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_28 : Positive 0 4680 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_29 : Positive 0 4740 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_30 : Positive 0 6180 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_31 : Positive 0 6210 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_32 : Positive 0 6657 := by
  left
  refine ⟨{0, 1, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_33 : Positive 0 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_34 : Positive 0 8233 := by
  right
  left
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

private theorem positive_35 : Positive 0 8236 := by
  right
  left
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

private theorem positive_36 : Positive 0 8520 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_37 : Positive 0 8580 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_38 : Positive 0 8709 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_39 : Positive 0 8713 := by
  right
  left
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

private theorem positive_40 : Positive 0 8716 := by
  right
  left
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

private theorem positive_41 : Positive 0 8737 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 8737) := {
    vertices := ⟨![0, 4, 6, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_42 : Positive 0 8740 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 8740) := {
    vertices := ⟨![0, 6, 4, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_43 : Positive 0 9240 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_44 : Positive 0 9345 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_45 : Positive 0 9474 := by
  left
  refine ⟨{0, 1, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_46 : Positive 0 13056 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 13056) := {
    vertices := ⟨![0, 1, 6, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_47 : Positive 0 16451 := by
  right
  left
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

private theorem positive_48 : Positive 0 16457 := by
  right
  left
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

private theorem positive_49 : Positive 0 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_50 : Positive 0 16920 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_51 : Positive 0 17025 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_52 : Positive 0 17411 := by
  right
  left
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

private theorem positive_53 : Positive 0 17417 := by
  right
  left
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

private theorem positive_54 : Positive 0 17418 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_55 : Positive 0 17474 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 17474) := {
    vertices := ⟨![0, 5, 4, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_56 : Positive 0 17480 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 17480) := {
    vertices := ⟨![0, 7, 4, 5], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_57 : Positive 0 18450 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_58 : Positive 0 18465 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_59 : Positive 0 18948 := by
  left
  refine ⟨{0, 1, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_60 : Positive 0 20994 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_61 : Positive 0 22536 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_62 : Positive 0 26112 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 26112) := {
    vertices := ⟨![0, 1, 4, 7], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_63 : Positive 0 32899 := by
  right
  left
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

private theorem positive_64 : Positive 0 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_65 : Positive 0 32902 := by
  right
  left
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

private theorem positive_66 : Positive 0 33060 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_67 : Positive 0 33090 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_68 : Positive 0 33810 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_69 : Positive 0 33825 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_70 : Positive 0 34056 := by
  left
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_71 : Positive 0 34819 := by
  right
  left
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

private theorem positive_72 : Positive 0 34821 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_73 : Positive 0 34822 := by
  right
  left
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

private theorem positive_74 : Positive 0 34945 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 34945) := {
    vertices := ⟨![0, 4, 5, 6], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_75 : Positive 0 34948 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 34948) := {
    vertices := ⟨![0, 6, 4, 5], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_76 : Positive 0 39168 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 39168) := {
    vertices := ⟨![0, 1, 5, 6], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_77 : Positive 0 41217 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_78 : Positive 0 41988 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_79 : Positive 0 52224 := by
  right
  right
  let p : TwoEdges (PawModel.graph 0 52224) := {
    vertices := ⟨![0, 1, 4, 5], by decide +kernel⟩
    firstEdge := by decide +kernel
    secondEdge := by decide +kernel }
  refine ⟨p, subset_univ _, ?_, by decide +kernel⟩
  exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_80 : Positive 0 844 := by
  right
  left
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

private theorem positive_81 : Positive 0 908 := by
  right
  left
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

private theorem positive_82 : Positive 0 964 := by
  right
  left
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

private theorem positive_83 : Positive 0 968 := by
  right
  left
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

private theorem positive_84 : Positive 0 1561 := by
  right
  left
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

private theorem positive_85 : Positive 0 1673 := by
  right
  left
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

private theorem positive_86 : Positive 0 1681 := by
  right
  left
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

private theorem positive_87 : Positive 0 1688 := by
  right
  left
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

private theorem positive_88 : Positive 0 1928 := by
  right
  left
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

private theorem positive_89 : Positive 0 2342 := by
  right
  left
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

private theorem positive_90 : Positive 0 2374 := by
  right
  left
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

private theorem positive_91 : Positive 0 2402 := by
  right
  left
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

private theorem positive_92 : Positive 0 2404 := by
  right
  left
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

private theorem positive_93 : Positive 0 2884 := by
  right
  left
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

private theorem positive_94 : Positive 0 3091 := by
  right
  left
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

private theorem positive_95 : Positive 0 3107 := by
  right
  left
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

private theorem positive_96 : Positive 0 3121 := by
  right
  left
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

private theorem positive_97 : Positive 0 3122 := by
  right
  left
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

private theorem positive_98 : Positive 0 3362 := by
  right
  left
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

private theorem positive_99 : Positive 0 3601 := by
  right
  left
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

private theorem positive_100 : Positive 0 4450 := by
  right
  left
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

private theorem positive_101 : Positive 0 4452 := by
  right
  left
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

private theorem positive_102 : Positive 0 4548 := by
  right
  left
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

private theorem positive_103 : Positive 0 4552 := by
  right
  left
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

private theorem positive_104 : Positive 0 4576 := by
  right
  left
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

private theorem positive_105 : Positive 0 4932 := by
  right
  left
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

private theorem positive_106 : Positive 0 5000 := by
  right
  left
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

private theorem positive_107 : Positive 0 5056 := by
  right
  left
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

private theorem positive_108 : Positive 0 5649 := by
  right
  left
  refine ⟨{
    terminal := 7
    triangle := {2, 5, 6}
    block := {0, 1, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_109 : Positive 0 5776 := by
  right
  left
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

private theorem positive_110 : Positive 0 6434 := by
  right
  left
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

private theorem positive_111 : Positive 0 6468 := by
  right
  left
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

private theorem positive_112 : Positive 0 6496 := by
  right
  left
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

private theorem positive_113 : Positive 0 7185 := by
  right
  left
  refine ⟨{
    terminal := 5
    triangle := {2, 6, 7}
    block := {0, 1, 3, 4}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_114 : Positive 0 7216 := by
  right
  left
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

private theorem positive_115 : Positive 0 7696 := by
  right
  left
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

private theorem positive_116 : Positive 0 8849 := by
  right
  left
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

private theorem positive_117 : Positive 0 8856 := by
  right
  left
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

private theorem positive_118 : Positive 0 8900 := by
  right
  left
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

private theorem positive_119 : Positive 0 8904 := by
  right
  left
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

private theorem positive_120 : Positive 0 8912 := by
  right
  left
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

private theorem positive_121 : Positive 0 9028 := by
  right
  left
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

private theorem positive_122 : Positive 0 9096 := by
  right
  left
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

private theorem positive_123 : Positive 0 9152 := by
  right
  left
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

private theorem positive_124 : Positive 0 9745 := by
  right
  left
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

private theorem positive_125 : Positive 0 9864 := by
  right
  left
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

private theorem positive_126 : Positive 0 9872 := by
  right
  left
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

private theorem positive_127 : Positive 0 10530 := by
  right
  left
  refine ⟨{
    terminal := 6
    triangle := {2, 4, 7}
    block := {0, 1, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_128 : Positive 0 10592 := by
  right
  left
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

private theorem positive_129 : Positive 0 11298 := by
  right
  left
  refine ⟨{
    terminal := 4
    triangle := {2, 6, 7}
    block := {0, 1, 3, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_130 : Positive 0 11312 := by
  right
  left
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

private theorem positive_131 : Positive 0 11552 := by
  right
  left
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

private theorem positive_132 : Positive 0 12364 := by
  right
  left
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

private theorem positive_133 : Positive 0 12428 := by
  right
  left
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

private theorem positive_134 : Positive 0 12484 := by
  right
  left
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

private theorem positive_135 : Positive 0 12488 := by
  right
  left
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

private theorem positive_136 : Positive 0 12612 := by
  right
  left
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

private theorem positive_137 : Positive 0 12680 := by
  right
  left
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

private theorem positive_138 : Positive 0 12736 := by
  right
  left
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

private theorem positive_139 : Positive 0 12868 := by
  right
  left
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

private theorem positive_140 : Positive 0 12936 := by
  right
  left
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

private theorem positive_141 : Positive 0 12992 := by
  right
  left
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

private theorem positive_142 : Positive 0 13380 := by
  right
  left
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

private theorem positive_143 : Positive 0 13504 := by
  right
  left
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

private theorem positive_144 : Positive 0 14472 := by
  right
  left
  refine ⟨{
    terminal := 6
    triangle := {3, 4, 5}
    block := {0, 1, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_145 : Positive 0 14528 := by
  right
  left
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

private theorem positive_146 : Positive 0 15376 := by
  right
  left
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

private theorem positive_147 : Positive 0 15392 := by
  right
  left
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

private theorem positive_148 : Positive 0 15424 := by
  right
  left
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

private theorem positive_149 : Positive 0 15488 := by
  right
  left
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

private theorem positive_150 : Positive 0 17220 := by
  right
  left
  refine ⟨{
    terminal := 7
    triangle := {2, 4, 5}
    block := {0, 1, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_151 : Positive 0 17344 := by
  right
  left
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

private theorem positive_152 : Positive 0 17457 := by
  right
  left
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

private theorem positive_153 : Positive 0 17458 := by
  right
  left
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

private theorem positive_154 : Positive 0 17553 := by
  right
  left
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

private theorem positive_155 : Positive 0 17560 := by
  right
  left
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

private theorem positive_156 : Positive 0 17584 := by
  right
  left
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

private theorem positive_157 : Positive 0 17937 := by
  right
  left
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

private theorem positive_158 : Positive 0 18056 := by
  right
  left
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

private theorem positive_159 : Positive 0 18064 := by
  right
  left
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

private theorem positive_160 : Positive 0 18756 := by
  right
  left
  refine ⟨{
    terminal := 5
    triangle := {2, 4, 7}
    block := {0, 1, 3, 6}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_161 : Positive 0 18784 := by
  right
  left
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

private theorem positive_162 : Positive 0 19264 := by
  right
  left
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

private theorem positive_163 : Positive 0 19473 := by
  right
  left
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

private theorem positive_164 : Positive 0 19490 := by
  right
  left
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

private theorem positive_165 : Positive 0 19504 := by
  right
  left
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

private theorem positive_166 : Positive 0 24601 := by
  right
  left
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

private theorem positive_167 : Positive 0 24713 := by
  right
  left
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

private theorem positive_168 : Positive 0 24721 := by
  right
  left
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

private theorem positive_169 : Positive 0 24728 := by
  right
  left
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

private theorem positive_170 : Positive 0 24849 := by
  right
  left
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

private theorem positive_171 : Positive 0 24976 := by
  right
  left
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

private theorem positive_172 : Positive 0 25105 := by
  right
  left
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

private theorem positive_173 : Positive 0 25224 := by
  right
  left
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

private theorem positive_174 : Positive 0 25232 := by
  right
  left
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

private theorem positive_175 : Positive 0 25617 := by
  right
  left
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

private theorem positive_176 : Positive 0 25736 := by
  right
  left
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

private theorem positive_177 : Positive 0 25744 := by
  right
  left
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

private theorem positive_178 : Positive 0 26760 := by
  right
  left
  refine ⟨{
    terminal := 4
    triangle := {3, 5, 6}
    block := {0, 1, 2, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_179 : Positive 0 26768 := by
  right
  left
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

private theorem positive_180 : Positive 0 26896 := by
  right
  left
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

private theorem positive_181 : Positive 0 26912 := by
  right
  left
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

private theorem positive_182 : Positive 0 26944 := by
  right
  left
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

private theorem positive_183 : Positive 0 27008 := by
  right
  left
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

private theorem positive_184 : Positive 0 28808 := by
  right
  left
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

private theorem positive_185 : Positive 0 30848 := by
  right
  left
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

private theorem positive_186 : Positive 0 33672 := by
  right
  left
  refine ⟨{
    terminal := 6
    triangle := {2, 4, 5}
    block := {0, 1, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_187 : Positive 0 33728 := by
  right
  left
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

private theorem positive_188 : Positive 0 34440 := by
  right
  left
  refine ⟨{
    terminal := 4
    triangle := {2, 5, 6}
    block := {0, 1, 3, 7}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_189 : Positive 0 34448 := by
  right
  left
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

private theorem positive_190 : Positive 0 34688 := by
  right
  left
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

private theorem positive_191 : Positive 0 34865 := by
  right
  left
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

private theorem positive_192 : Positive 0 34866 := by
  right
  left
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

private theorem positive_193 : Positive 0 34914 := by
  right
  left
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

private theorem positive_194 : Positive 0 34916 := by
  right
  left
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

private theorem positive_195 : Positive 0 34928 := by
  right
  left
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

private theorem positive_196 : Positive 0 35106 := by
  right
  left
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

private theorem positive_197 : Positive 0 35140 := by
  right
  left
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

private theorem positive_198 : Positive 0 35168 := by
  right
  left
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

private theorem positive_199 : Positive 0 35857 := by
  right
  left
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

private theorem positive_200 : Positive 0 35874 := by
  right
  left
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

private theorem positive_201 : Positive 0 35888 := by
  right
  left
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

private theorem positive_202 : Positive 0 36902 := by
  right
  left
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

private theorem positive_203 : Positive 0 36934 := by
  right
  left
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

private theorem positive_204 : Positive 0 36962 := by
  right
  left
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

private theorem positive_205 : Positive 0 36964 := by
  right
  left
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

private theorem positive_206 : Positive 0 37154 := by
  right
  left
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

private theorem positive_207 : Positive 0 37188 := by
  right
  left
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

private theorem positive_208 : Positive 0 37216 := by
  right
  left
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

private theorem positive_209 : Positive 0 37410 := by
  right
  left
  refine ⟨{
    terminal := 6
    triangle := {3, 4, 7}
    block := {0, 1, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_210 : Positive 0 37472 := by
  right
  left
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

private theorem positive_211 : Positive 0 37956 := by
  right
  left
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

private theorem positive_212 : Positive 0 37984 := by
  right
  left
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

private theorem positive_213 : Positive 0 38416 := by
  right
  left
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

private theorem positive_214 : Positive 0 38432 := by
  right
  left
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

private theorem positive_215 : Positive 0 38464 := by
  right
  left
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

private theorem positive_216 : Positive 0 38528 := by
  right
  left
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

private theorem positive_217 : Positive 0 38946 := by
  right
  left
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

private theorem positive_218 : Positive 0 38980 := by
  right
  left
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

private theorem positive_219 : Positive 0 39008 := by
  right
  left
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

private theorem positive_220 : Positive 0 45124 := by
  right
  left
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

private theorem positive_221 : Positive 0 46144 := by
  right
  left
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

private theorem positive_222 : Positive 0 49171 := by
  right
  left
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

private theorem positive_223 : Positive 0 49187 := by
  right
  left
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

private theorem positive_224 : Positive 0 49201 := by
  right
  left
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

private theorem positive_225 : Positive 0 49202 := by
  right
  left
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

private theorem positive_226 : Positive 0 49425 := by
  right
  left
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

private theorem positive_227 : Positive 0 49456 := by
  right
  left
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

private theorem positive_228 : Positive 0 49698 := by
  right
  left
  refine ⟨{
    terminal := 4
    triangle := {3, 6, 7}
    block := {0, 1, 2, 5}
    triangle_clique := by decide +kernel
    terminal_not_mem := by decide +kernel
    quad := QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
    disjoint := by decide +kernel
    cover := by decide +kernel }, ?_⟩
  decide +kernel

private theorem positive_229 : Positive 0 49712 := by
  right
  left
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

private theorem positive_230 : Positive 0 49936 := by
  right
  left
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

private theorem positive_231 : Positive 0 49952 := by
  right
  left
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

private theorem positive_232 : Positive 0 49984 := by
  right
  left
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

private theorem positive_233 : Positive 0 50048 := by
  right
  left
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

private theorem positive_234 : Positive 0 50193 := by
  right
  left
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

private theorem positive_235 : Positive 0 50210 := by
  right
  left
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

private theorem positive_236 : Positive 0 50224 := by
  right
  left
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

private theorem positive_237 : Positive 0 51217 := by
  right
  left
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

private theorem positive_238 : Positive 0 51234 := by
  right
  left
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

private theorem positive_239 : Positive 0 51248 := by
  right
  left
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

private theorem positive_240 : Positive 0 53282 := by
  right
  left
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

private theorem positive_241 : Positive 0 53792 := by
  right
  left
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

private theorem positive_242 : Positive 0 57361 := by
  right
  left
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

private theorem positive_243 : Positive 0 57616 := by
  right
  left
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

private theorem positive_244 : Positive 0 963 := by
  right
  left
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

private theorem positive_245 : Positive 0 1686 := by
  right
  left
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

private theorem positive_246 : Positive 0 2409 := by
  right
  left
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

private theorem positive_247 : Positive 0 3132 := by
  right
  left
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

private theorem positive_248 : Positive 0 12483 := by
  right
  left
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

private theorem positive_249 : Positive 0 15363 := by
  right
  left
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

private theorem positive_250 : Positive 0 15372 := by
  right
  left
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

private theorem positive_251 : Positive 0 21794 := by
  right
  left
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

private theorem positive_252 : Positive 0 21896 := by
  right
  left
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

private theorem positive_253 : Positive 0 24726 := by
  right
  left
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

private theorem positive_254 : Positive 0 26886 := by
  right
  left
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

private theorem positive_255 : Positive 0 26889 := by
  right
  left
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

private theorem positive_256 : Positive 0 36969 := by
  right
  left
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

private theorem positive_257 : Positive 0 38406 := by
  right
  left
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

private theorem positive_258 : Positive 0 38409 := by
  right
  left
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

private theorem positive_259 : Positive 0 43537 := by
  right
  left
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

private theorem positive_260 : Positive 0 43588 := by
  right
  left
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

private theorem positive_261 : Positive 0 49212 := by
  right
  left
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

private theorem positive_262 : Positive 0 49923 := by
  right
  left
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

private theorem positive_263 : Positive 0 49932 := by
  right
  left
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

private def positive_group_0 : List ℕ := [
  7, 11, 13, 14, 51, 102, 153, 204,
  278, 282, 284, 549, 553, 556, 1091, 1097,
  1098, 2179, 2181, 2182, 4118, 4122, 4124, 4358,
  4362, 4364, 4370, 4376, 4680, 4740, 6180, 6210]

private theorem positive_group_0_sound {m : ℕ} (h : m ∈ positive_group_0) :
    Positive 0 m := by
  simp only [positive_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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

private def positive_group_1 : List ℕ := [
  6657, 8229, 8233, 8236, 8520, 8580, 8709, 8713,
  8716, 8737, 8740, 9240, 9345, 9474, 13056, 16451,
  16457, 16458, 16920, 17025, 17411, 17417, 17418, 17474,
  17480, 18450, 18465, 18948, 20994, 22536, 26112, 32899]

private theorem positive_group_1_sound {m : ℕ} (h : m ∈ positive_group_1) :
    Positive 0 m := by
  simp only [positive_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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

private def positive_group_2 : List ℕ := [
  32901, 32902, 33060, 33090, 33810, 33825, 34056, 34819,
  34821, 34822, 34945, 34948, 39168, 41217, 41988, 52224,
  844, 908, 964, 968, 1561, 1673, 1681, 1688,
  1928, 2342, 2374, 2402, 2404, 2884, 3091, 3107]

private theorem positive_group_2_sound {m : ℕ} (h : m ∈ positive_group_2) :
    Positive 0 m := by
  simp only [positive_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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

private def positive_group_3 : List ℕ := [
  3121, 3122, 3362, 3601, 4450, 4452, 4548, 4552,
  4576, 4932, 5000, 5056, 5649, 5776, 6434, 6468,
  6496, 7185, 7216, 7696, 8849, 8856, 8900, 8904,
  8912, 9028, 9096, 9152, 9745, 9864, 9872, 10530]

private theorem positive_group_3_sound {m : ℕ} (h : m ∈ positive_group_3) :
    Positive 0 m := by
  simp only [positive_group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
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

private def positive_group_4 : List ℕ := [
  10592, 11298, 11312, 11552, 12364, 12428, 12484, 12488,
  12612, 12680, 12736, 12868, 12936, 12992, 13380, 13504,
  14472, 14528, 15376, 15392, 15424, 15488, 17220, 17344,
  17457, 17458, 17553, 17560, 17584, 17937, 18056, 18064]

private theorem positive_group_4_sound {m : ℕ} (h : m ∈ positive_group_4) :
    Positive 0 m := by
  simp only [positive_group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_128
  · exact positive_129
  · exact positive_130
  · exact positive_131
  · exact positive_132
  · exact positive_133
  · exact positive_134
  · exact positive_135
  · exact positive_136
  · exact positive_137
  · exact positive_138
  · exact positive_139
  · exact positive_140
  · exact positive_141
  · exact positive_142
  · exact positive_143
  · exact positive_144
  · exact positive_145
  · exact positive_146
  · exact positive_147
  · exact positive_148
  · exact positive_149
  · exact positive_150
  · exact positive_151
  · exact positive_152
  · exact positive_153
  · exact positive_154
  · exact positive_155
  · exact positive_156
  · exact positive_157
  · exact positive_158
  · exact positive_159

private def positive_group_5 : List ℕ := [
  18756, 18784, 19264, 19473, 19490, 19504, 24601, 24713,
  24721, 24728, 24849, 24976, 25105, 25224, 25232, 25617,
  25736, 25744, 26760, 26768, 26896, 26912, 26944, 27008,
  28808, 30848, 33672, 33728, 34440, 34448, 34688, 34865]

private theorem positive_group_5_sound {m : ℕ} (h : m ∈ positive_group_5) :
    Positive 0 m := by
  simp only [positive_group_5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_160
  · exact positive_161
  · exact positive_162
  · exact positive_163
  · exact positive_164
  · exact positive_165
  · exact positive_166
  · exact positive_167
  · exact positive_168
  · exact positive_169
  · exact positive_170
  · exact positive_171
  · exact positive_172
  · exact positive_173
  · exact positive_174
  · exact positive_175
  · exact positive_176
  · exact positive_177
  · exact positive_178
  · exact positive_179
  · exact positive_180
  · exact positive_181
  · exact positive_182
  · exact positive_183
  · exact positive_184
  · exact positive_185
  · exact positive_186
  · exact positive_187
  · exact positive_188
  · exact positive_189
  · exact positive_190
  · exact positive_191

private def positive_group_6 : List ℕ := [
  34866, 34914, 34916, 34928, 35106, 35140, 35168, 35857,
  35874, 35888, 36902, 36934, 36962, 36964, 37154, 37188,
  37216, 37410, 37472, 37956, 37984, 38416, 38432, 38464,
  38528, 38946, 38980, 39008, 45124, 46144, 49171, 49187]

private theorem positive_group_6_sound {m : ℕ} (h : m ∈ positive_group_6) :
    Positive 0 m := by
  simp only [positive_group_6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_192
  · exact positive_193
  · exact positive_194
  · exact positive_195
  · exact positive_196
  · exact positive_197
  · exact positive_198
  · exact positive_199
  · exact positive_200
  · exact positive_201
  · exact positive_202
  · exact positive_203
  · exact positive_204
  · exact positive_205
  · exact positive_206
  · exact positive_207
  · exact positive_208
  · exact positive_209
  · exact positive_210
  · exact positive_211
  · exact positive_212
  · exact positive_213
  · exact positive_214
  · exact positive_215
  · exact positive_216
  · exact positive_217
  · exact positive_218
  · exact positive_219
  · exact positive_220
  · exact positive_221
  · exact positive_222
  · exact positive_223

private def positive_group_7 : List ℕ := [
  49201, 49202, 49425, 49456, 49698, 49712, 49936, 49952,
  49984, 50048, 50193, 50210, 50224, 51217, 51234, 51248,
  53282, 53792, 57361, 57616, 963, 1686, 2409, 3132,
  12483, 15363, 15372, 21794, 21896, 24726, 26886, 26889]

private theorem positive_group_7_sound {m : ℕ} (h : m ∈ positive_group_7) :
    Positive 0 m := by
  simp only [positive_group_7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_224
  · exact positive_225
  · exact positive_226
  · exact positive_227
  · exact positive_228
  · exact positive_229
  · exact positive_230
  · exact positive_231
  · exact positive_232
  · exact positive_233
  · exact positive_234
  · exact positive_235
  · exact positive_236
  · exact positive_237
  · exact positive_238
  · exact positive_239
  · exact positive_240
  · exact positive_241
  · exact positive_242
  · exact positive_243
  · exact positive_244
  · exact positive_245
  · exact positive_246
  · exact positive_247
  · exact positive_248
  · exact positive_249
  · exact positive_250
  · exact positive_251
  · exact positive_252
  · exact positive_253
  · exact positive_254
  · exact positive_255

private def positive_group_8 : List ℕ := [
  36969, 38406, 38409, 43537, 43588, 49212, 49923, 49932]

private theorem positive_group_8_sound {m : ℕ} (h : m ∈ positive_group_8) :
    Positive 0 m := by
  simp only [positive_group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_256
  · exact positive_257
  · exact positive_258
  · exact positive_259
  · exact positive_260
  · exact positive_261
  · exact positive_262
  · exact positive_263

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 0 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    positive_group_0, positive_group_1, positive_group_2, positive_group_3,
    positive_group_4, positive_group_5, positive_group_6, positive_group_7,
    positive_group_8] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact positive_group_0_sound hm
  · exact positive_group_1_sound hm
  · exact positive_group_2_sound hm
  · exact positive_group_3_sound hm
  · exact positive_group_4_sound hm
  · exact positive_group_5_sound hm
  · exact positive_group_6_sound hm
  · exact positive_group_7_sound hm
  · exact positive_group_8_sound hm

theorem covered_sound {m : ℕ} (h : covered m = true) : Positive 0 m := by
  obtain ⟨group, hg, hgroup⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hgroup
  have hwm : w ∈ masks := List.mem_flatten.mpr ⟨group, hg, hw⟩
  exact (masks_sound hwm).mono (beq_iff_eq.mp hsub)

end Erdos577.FirstPaw.D0
