import ErdosProblems.Erdos577.FirstPawMasks3

/-! Explicit factors, strict triangle gains, and two-edge-remainder gains. -/

namespace Erdos577.FirstPaw.D3

open Finset

private theorem positive_0 : Positive 3 278 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_1 : Positive 3 282 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_2 : Positive 3 284 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_3 : Positive 3 549 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_4 : Positive 3 553 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_5 : Positive 3 556 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_6 : Positive 3 1091 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_7 : Positive 3 1097 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_8 : Positive 3 1098 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_9 : Positive 3 2179 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_10 : Positive 3 2181 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_11 : Positive 3 2182 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_12 : Positive 3 4118 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_13 : Positive 3 4122 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_14 : Positive 3 4124 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_15 : Positive 3 4358 := by
  left
  refine ⟨{0, 5, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_16 : Positive 3 4362 := by
  left
  refine ⟨{0, 5, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_17 : Positive 3 4364 := by
  left
  refine ⟨{0, 6, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_18 : Positive 3 4680 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_19 : Positive 3 4740 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_20 : Positive 3 5160 := by
  left
  refine ⟨{0, 1, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_21 : Positive 3 5250 := by
  left
  refine ⟨{0, 1, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_22 : Positive 3 5633 := by
  left
  refine ⟨{0, 1, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_23 : Positive 3 6180 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_24 : Positive 3 6210 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_25 : Positive 3 6657 := by
  left
  refine ⟨{0, 1, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_26 : Positive 3 7169 := by
  left
  refine ⟨{0, 1, 3, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_27 : Positive 3 8229 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_28 : Positive 3 8233 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_29 : Positive 3 8236 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_30 : Positive 3 8520 := by
  left
  refine ⟨{0, 1, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_31 : Positive 3 8580 := by
  left
  refine ⟨{0, 1, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_32 : Positive 3 8709 := by
  left
  refine ⟨{0, 4, 7, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_33 : Positive 3 8713 := by
  left
  refine ⟨{0, 4, 6, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_34 : Positive 3 8716 := by
  left
  refine ⟨{0, 6, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_35 : Positive 3 9240 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_36 : Positive 3 9345 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_37 : Positive 3 9474 := by
  left
  refine ⟨{0, 1, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_38 : Positive 3 10260 := by
  left
  refine ⟨{0, 1, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_39 : Positive 3 10305 := by
  left
  refine ⟨{0, 1, 6, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_40 : Positive 3 10498 := by
  left
  refine ⟨{0, 1, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_41 : Positive 3 11266 := by
  left
  refine ⟨{0, 1, 3, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_42 : Positive 3 13316 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_43 : Positive 3 14344 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_44 : Positive 3 16451 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_45 : Positive 3 16457 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_46 : Positive 3 16458 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_47 : Positive 3 16680 := by
  left
  refine ⟨{0, 1, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_48 : Positive 3 16770 := by
  left
  refine ⟨{0, 1, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_49 : Positive 3 16920 := by
  left
  refine ⟨{0, 1, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_50 : Positive 3 17025 := by
  left
  refine ⟨{0, 1, 7, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_51 : Positive 3 17156 := by
  left
  refine ⟨{0, 1, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_52 : Positive 3 17411 := by
  left
  refine ⟨{0, 4, 7, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_53 : Positive 3 17417 := by
  left
  refine ⟨{0, 4, 5, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_54 : Positive 3 17418 := by
  left
  refine ⟨{0, 5, 4, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_55 : Positive 3 18450 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_56 : Positive 3 18465 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_57 : Positive 3 18692 := by
  left
  refine ⟨{0, 1, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_58 : Positive 3 18948 := by
  left
  refine ⟨{0, 1, 3, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_59 : Positive 3 20994 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_60 : Positive 3 22536 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_61 : Positive 3 24833 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_62 : Positive 3 26632 := by
  left
  refine ⟨{0, 1, 2, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_63 : Positive 3 32899 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_64 : Positive 3 32901 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_65 : Positive 3 32902 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_66 : Positive 3 33060 := by
  left
  refine ⟨{0, 1, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_67 : Positive 3 33090 := by
  left
  refine ⟨{0, 1, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_68 : Positive 3 33300 := by
  left
  refine ⟨{0, 1, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_69 : Positive 3 33345 := by
  left
  refine ⟨{0, 1, 6, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_70 : Positive 3 33544 := by
  left
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_71 : Positive 3 33810 := by
  left
  refine ⟨{0, 1, 4, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_72 : Positive 3 33825 := by
  left
  refine ⟨{0, 1, 5, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_73 : Positive 3 34056 := by
  left
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_74 : Positive 3 34312 := by
  left
  refine ⟨{0, 1, 3, 7}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_75 : Positive 3 34819 := by
  left
  refine ⟨{0, 4, 6, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_76 : Positive 3 34821 := by
  left
  refine ⟨{0, 4, 5, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_77 : Positive 3 34822 := by
  left
  refine ⟨{0, 5, 4, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_78 : Positive 3 37378 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_79 : Positive 3 37892 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_80 : Positive 3 41217 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_81 : Positive 3 41988 := by
  left
  refine ⟨{0, 1, 2, 6}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_82 : Positive 3 49409 := by
  left
  refine ⟨{0, 1, 2, 4}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private theorem positive_83 : Positive 3 49666 := by
  left
  refine ⟨{0, 1, 2, 5}, subset_univ _, ?_, ?_⟩
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)
  · exact QuadOn.of_degreeIn (by decide +kernel) (by decide +kernel)

private def positive_group_0 : List ℕ := [
  278, 282, 284, 549, 553, 556, 1091, 1097,
  1098, 2179, 2181, 2182, 4118, 4122, 4124, 4358,
  4362, 4364, 4680, 4740, 5160, 5250, 5633, 6180,
  6210, 6657, 7169, 8229, 8233, 8236, 8520, 8580]

private theorem positive_group_0_sound {m : ℕ} (h : m ∈ positive_group_0) :
    Positive 3 m := by
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
  8709, 8713, 8716, 9240, 9345, 9474, 10260, 10305,
  10498, 11266, 13316, 14344, 16451, 16457, 16458, 16680,
  16770, 16920, 17025, 17156, 17411, 17417, 17418, 18450,
  18465, 18692, 18948, 20994, 22536, 24833, 26632, 32899]

private theorem positive_group_1_sound {m : ℕ} (h : m ∈ positive_group_1) :
    Positive 3 m := by
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
  32901, 32902, 33060, 33090, 33300, 33345, 33544, 33810,
  33825, 34056, 34312, 34819, 34821, 34822, 37378, 37892,
  41217, 41988, 49409, 49666]

private theorem positive_group_2_sound {m : ℕ} (h : m ∈ positive_group_2) :
    Positive 3 m := by
  simp only [positive_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
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

theorem masks_sound {m : ℕ} (h : m ∈ masks) : Positive 3 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    positive_group_0, positive_group_1, positive_group_2] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · exact positive_group_0_sound hm
  · exact positive_group_1_sound hm
  · exact positive_group_2_sound hm

theorem covered_sound {m : ℕ} (h : covered m = true) : Positive 3 m := by
  obtain ⟨group, hg, hgroup⟩ := List.any_eq_true.mp h
  obtain ⟨w, hw, hsub⟩ := List.any_eq_true.mp hgroup
  have hwm : w ∈ masks := List.mem_flatten.mpr ⟨group, hg, hw⟩
  exact (masks_sound hwm).mono (beq_iff_eq.mp hsub)

end Erdos577.FirstPaw.D3
