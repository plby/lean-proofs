import ErdosProblems.Erdos577.WeightedPawMasks1

/-! Exact row and diagonal certificates for weighted source patterns (9)–(20). -/

namespace Erdos577.WeightedPaw.D1

private theorem residual_0 : Classified 1 3851 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_1 : Classified 1 3854 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_2 : Classified 1 7694 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_3 : Classified 1 7942 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_4 : Classified 1 7948 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_5 : Classified 1 15621 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_6 : Classified 1 15637 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_7 : Classified 1 15685 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_8 : Classified 1 15701 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_9 : Classified 1 16132 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 1 16148 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 1 19211 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_12 : Classified 1 20227 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_13 : Classified 1 20233 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_14 : Classified 1 22277 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_15 : Classified 1 22281 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_16 : Classified 1 22284 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_17 : Classified 1 22293 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_18 : Classified 1 22341 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_19 : Classified 1 22357 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_20 : Classified 1 23811 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_21 : Classified 1 23813 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_22 : Classified 1 23814 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_23 : Classified 1 23829 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_24 : Classified 1 23877 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_25 : Classified 1 23893 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_26 : Classified 1 27909 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_27 : Classified 1 27925 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_28 : Classified 1 27973 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_29 : Classified 1 27989 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_30 : Classified 1 28417 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_31 : Classified 1 28481 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_32 : Classified 1 29957 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_33 : Classified 1 29961 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_34 : Classified 1 29964 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_35 : Classified 1 29973 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_36 : Classified 1 30021 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_37 : Classified 1 30037 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 1 30465 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_39 : Classified 1 30468 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_40 : Classified 1 30472 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_41 : Classified 1 30484 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_42 : Classified 1 30529 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_43 : Classified 1 30981 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_44 : Classified 1 30997 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_45 : Classified 1 31045 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_46 : Classified 1 31061 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_47 : Classified 1 31749 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_48 : Classified 1 31765 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_49 : Classified 1 31813 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_50 : Classified 1 31829 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_51 : Classified 1 32001 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_52 : Classified 1 32004 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_53 : Classified 1 32005 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_54 : Classified 1 32017 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_55 : Classified 1 32020 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_56 : Classified 1 32021 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_57 : Classified 1 32065 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_58 : Classified 1 32068 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_59 : Classified 1 32069 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_60 : Classified 1 32081 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_61 : Classified 1 32084 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_62 : Classified 1 32085 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_63 : Classified 1 38661 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_64 : Classified 1 38677 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_65 : Classified 1 38725 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_66 : Classified 1 38741 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_67 : Classified 1 40708 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_68 : Classified 1 40724 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_69 : Classified 1 46091 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_70 : Classified 1 47876 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_71 : Classified 1 50949 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_72 : Classified 1 50965 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_73 : Classified 1 51013 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_74 : Classified 1 51029 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_75 : Classified 1 52993 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_76 : Classified 1 53057 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_77 : Classified 1 54021 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_78 : Classified 1 54037 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_79 : Classified 1 54085 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_80 : Classified 1 54101 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_81 : Classified 1 54531 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_82 : Classified 1 54533 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_83 : Classified 1 54534 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_84 : Classified 1 54549 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_85 : Classified 1 54597 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_86 : Classified 1 54613 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_87 : Classified 1 54789 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_88 : Classified 1 54805 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_89 : Classified 1 54853 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_90 : Classified 1 54869 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_91 : Classified 1 55041 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_92 : Classified 1 55044 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_93 : Classified 1 55045 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_94 : Classified 1 55057 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_95 : Classified 1 55060 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_96 : Classified 1 55061 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_97 : Classified 1 55105 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_98 : Classified 1 55108 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_99 : Classified 1 55109 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_100 : Classified 1 55121 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_101 : Classified 1 55124 := by
  refine ⟨false, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_102 : Classified 1 55125 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_103 : Classified 1 56577 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_104 : Classified 1 56578 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_105 : Classified 1 56580 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_106 : Classified 1 56596 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_107 : Classified 1 56641 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_108 : Classified 1 57614 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_109 : Classified 1 60929 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_110 : Classified 1 61451 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_111 : Classified 1 61454 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_112 : Classified 1 61702 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_113 : Classified 1 61708 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_114 : Classified 1 62212 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_115 : Classified 1 62228 := by
  refine ⟨true, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_116 : Classified 1 62467 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_117 : Classified 1 62473 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_118 : Classified 1 62977 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_119 : Classified 1 63041 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_120 : Classified 1 63748 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_121 : Classified 1 63764 := by
  refine ⟨true, ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_122 : Classified 1 64513 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_123 : Classified 1 64577 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private def residual_group_0 : List ℕ := [
  3851, 3854, 7694, 7942, 7948, 15621, 15637, 15685,
  15701, 16132, 16148, 19211, 20227, 20233, 22277, 22281,
  22284, 22293, 22341, 22357, 23811, 23813, 23814, 23829,
  23877, 23893, 27909, 27925, 27973, 27989, 28417, 28481]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) :
    Classified 1 m := by
  simp only [residual_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_0
  · exact residual_1
  · exact residual_2
  · exact residual_3
  · exact residual_4
  · exact residual_5
  · exact residual_6
  · exact residual_7
  · exact residual_8
  · exact residual_9
  · exact residual_10
  · exact residual_11
  · exact residual_12
  · exact residual_13
  · exact residual_14
  · exact residual_15
  · exact residual_16
  · exact residual_17
  · exact residual_18
  · exact residual_19
  · exact residual_20
  · exact residual_21
  · exact residual_22
  · exact residual_23
  · exact residual_24
  · exact residual_25
  · exact residual_26
  · exact residual_27
  · exact residual_28
  · exact residual_29
  · exact residual_30
  · exact residual_31

private def residual_group_1 : List ℕ := [
  29957, 29961, 29964, 29973, 30021, 30037, 30465, 30468,
  30472, 30484, 30529, 30981, 30997, 31045, 31061, 31749,
  31765, 31813, 31829, 32001, 32004, 32005, 32017, 32020,
  32021, 32065, 32068, 32069, 32081, 32084, 32085, 38661]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) :
    Classified 1 m := by
  simp only [residual_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_32
  · exact residual_33
  · exact residual_34
  · exact residual_35
  · exact residual_36
  · exact residual_37
  · exact residual_38
  · exact residual_39
  · exact residual_40
  · exact residual_41
  · exact residual_42
  · exact residual_43
  · exact residual_44
  · exact residual_45
  · exact residual_46
  · exact residual_47
  · exact residual_48
  · exact residual_49
  · exact residual_50
  · exact residual_51
  · exact residual_52
  · exact residual_53
  · exact residual_54
  · exact residual_55
  · exact residual_56
  · exact residual_57
  · exact residual_58
  · exact residual_59
  · exact residual_60
  · exact residual_61
  · exact residual_62
  · exact residual_63

private def residual_group_2 : List ℕ := [
  38677, 38725, 38741, 40708, 40724, 46091, 47876, 50949,
  50965, 51013, 51029, 52993, 53057, 54021, 54037, 54085,
  54101, 54531, 54533, 54534, 54549, 54597, 54613, 54789,
  54805, 54853, 54869, 55041, 55044, 55045, 55057, 55060]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) :
    Classified 1 m := by
  simp only [residual_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_64
  · exact residual_65
  · exact residual_66
  · exact residual_67
  · exact residual_68
  · exact residual_69
  · exact residual_70
  · exact residual_71
  · exact residual_72
  · exact residual_73
  · exact residual_74
  · exact residual_75
  · exact residual_76
  · exact residual_77
  · exact residual_78
  · exact residual_79
  · exact residual_80
  · exact residual_81
  · exact residual_82
  · exact residual_83
  · exact residual_84
  · exact residual_85
  · exact residual_86
  · exact residual_87
  · exact residual_88
  · exact residual_89
  · exact residual_90
  · exact residual_91
  · exact residual_92
  · exact residual_93
  · exact residual_94
  · exact residual_95

private def residual_group_3 : List ℕ := [
  55061, 55105, 55108, 55109, 55121, 55124, 55125, 56577,
  56578, 56580, 56596, 56641, 57614, 60929, 61451, 61454,
  61702, 61708, 62212, 62228, 62467, 62473, 62977, 63041,
  63748, 63764, 64513, 64577]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) :
    Classified 1 m := by
  simp only [residual_group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  · exact residual_96
  · exact residual_97
  · exact residual_98
  · exact residual_99
  · exact residual_100
  · exact residual_101
  · exact residual_102
  · exact residual_103
  · exact residual_104
  · exact residual_105
  · exact residual_106
  · exact residual_107
  · exact residual_108
  · exact residual_109
  · exact residual_110
  · exact residual_111
  · exact residual_112
  · exact residual_113
  · exact residual_114
  · exact residual_115
  · exact residual_116
  · exact residual_117
  · exact residual_118
  · exact residual_119
  · exact residual_120
  · exact residual_121
  · exact residual_122
  · exact residual_123

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) :
    Classified 1 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    residual_group_0, residual_group_1, residual_group_2, residual_group_3] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact residual_group_0_sound hm
  · exact residual_group_1_sound hm
  · exact residual_group_2_sound hm
  · exact residual_group_3_sound hm

end Erdos577.WeightedPaw.D1
