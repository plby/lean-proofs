import ErdosProblems.Erdos577.WeightedPawMasks2

/-! Exact row and diagonal certificates for weighted source patterns (9)–(20). -/

namespace Erdos577.WeightedPaw.D2

private theorem residual_0 : Classified 2 3847 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_1 : Classified 2 3853 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_2 : Classified 2 11533 := by
  refine ⟨false, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_3 : Classified 2 12041 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_4 : Classified 2 12044 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_5 : Classified 2 15882 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_6 : Classified 2 15914 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_7 : Classified 2 16010 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_8 : Classified 2 16042 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_9 : Classified 2 16136 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 2 16168 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 2 27402 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_12 : Classified 2 27434 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_13 : Classified 2 27530 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_14 : Classified 2 27562 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_15 : Classified 2 28424 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_16 : Classified 2 28456 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_17 : Classified 2 30472 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_18 : Classified 2 30727 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_19 : Classified 2 34567 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_20 : Classified 2 36611 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_21 : Classified 2 36614 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_22 : Classified 2 40458 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_23 : Classified 2 40490 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_24 : Classified 2 40586 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_25 : Classified 2 40618 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_26 : Classified 2 40706 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_27 : Classified 2 40834 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_28 : Classified 2 43782 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_29 : Classified 2 43786 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_30 : Classified 2 43788 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_31 : Classified 2 43818 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_32 : Classified 2 43914 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_33 : Classified 2 43946 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_34 : Classified 2 44547 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_35 : Classified 2 44553 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_36 : Classified 2 44554 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_37 : Classified 2 44586 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 2 44682 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_39 : Classified 2 44714 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_40 : Classified 2 46602 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_41 : Classified 2 46634 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_42 : Classified 2 46730 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_43 : Classified 2 46762 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_44 : Classified 2 47622 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_45 : Classified 2 47626 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_46 : Classified 2 47628 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_47 : Classified 2 47658 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_48 : Classified 2 47754 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_49 : Classified 2 47786 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_50 : Classified 2 47874 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_51 : Classified 2 47876 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_52 : Classified 2 47880 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_53 : Classified 2 47912 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_54 : Classified 2 48002 := by
  refine ⟨false, ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_55 : Classified 2 48138 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_56 : Classified 2 48170 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_57 : Classified 2 48266 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_58 : Classified 2 48298 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_59 : Classified 2 48642 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_60 : Classified 2 48648 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_61 : Classified 2 48650 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_62 : Classified 2 48674 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_63 : Classified 2 48680 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_64 : Classified 2 48682 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_65 : Classified 2 48770 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_66 : Classified 2 48776 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_67 : Classified 2 48778 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_68 : Classified 2 48802 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_69 : Classified 2 48808 := by
  refine ⟨false, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_70 : Classified 2 48810 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_71 : Classified 2 51978 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_72 : Classified 2 52010 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_73 : Classified 2 52106 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_74 : Classified 2 52138 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_75 : Classified 2 52994 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_76 : Classified 2 53122 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_77 : Classified 2 53773 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_78 : Classified 2 56578 := by
  refine ⟨false, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_79 : Classified 2 58122 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_80 : Classified 2 58154 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_81 : Classified 2 58250 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_82 : Classified 2 58282 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_83 : Classified 2 59658 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_84 : Classified 2 59690 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_85 : Classified 2 59786 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_86 : Classified 2 59818 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_87 : Classified 2 59907 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_88 : Classified 2 59913 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_89 : Classified 2 59914 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_90 : Classified 2 59946 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_91 : Classified 2 60042 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_92 : Classified 2 60074 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_93 : Classified 2 60162 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_94 : Classified 2 60168 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_95 : Classified 2 60170 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_96 : Classified 2 60194 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_97 : Classified 2 60200 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_98 : Classified 2 60202 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_99 : Classified 2 60290 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_100 : Classified 2 60296 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_101 : Classified 2 60298 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_102 : Classified 2 60322 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_103 : Classified 2 60328 := by
  refine ⟨false, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_104 : Classified 2 60330 := by
  refine ⟨false, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_105 : Classified 2 60929 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_106 : Classified 2 60930 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_107 : Classified 2 60936 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_108 : Classified 2 60968 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_109 : Classified 2 61058 := by
  refine ⟨false, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_110 : Classified 2 61447 := by
  refine ⟨true, ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_111 : Classified 2 61453 := by
  refine ⟨true, ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_112 : Classified 2 61961 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_113 : Classified 2 61964 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_114 : Classified 2 62216 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_115 : Classified 2 62248 := by
  refine ⟨true, ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_116 : Classified 2 62984 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_117 : Classified 2 63016 := by
  refine ⟨true, ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_118 : Classified 2 63491 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_119 : Classified 2 63494 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
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

private theorem residual_120 : Classified 2 63746 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_121 : Classified 2 63874 := by
  refine ⟨true, ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_122 : Classified 2 64514 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_123 : Classified 2 64642 := by
  refine ⟨true, ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  right
  left
  decide +kernel

private def residual_group_0 : List ℕ := [
  3847, 3853, 11533, 12041, 12044, 15882, 15914, 16010,
  16042, 16136, 16168, 27402, 27434, 27530, 27562, 28424,
  28456, 30472, 30727, 34567, 36611, 36614, 40458, 40490,
  40586, 40618, 40706, 40834, 43782, 43786, 43788, 43818]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) :
    Classified 2 m := by
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
  43914, 43946, 44547, 44553, 44554, 44586, 44682, 44714,
  46602, 46634, 46730, 46762, 47622, 47626, 47628, 47658,
  47754, 47786, 47874, 47876, 47880, 47912, 48002, 48138,
  48170, 48266, 48298, 48642, 48648, 48650, 48674, 48680]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) :
    Classified 2 m := by
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
  48682, 48770, 48776, 48778, 48802, 48808, 48810, 51978,
  52010, 52106, 52138, 52994, 53122, 53773, 56578, 58122,
  58154, 58250, 58282, 59658, 59690, 59786, 59818, 59907,
  59913, 59914, 59946, 60042, 60074, 60162, 60168, 60170]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) :
    Classified 2 m := by
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
  60194, 60200, 60202, 60290, 60296, 60298, 60322, 60328,
  60330, 60929, 60930, 60936, 60968, 61058, 61447, 61453,
  61961, 61964, 62216, 62248, 62984, 63016, 63491, 63494,
  63746, 63874, 64514, 64642]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) :
    Classified 2 m := by
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
    Classified 2 m := by
  obtain ⟨group, hg, hm⟩ := List.mem_flatten.mp h
  change group ∈ [
    residual_group_0, residual_group_1, residual_group_2, residual_group_3] at hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact residual_group_0_sound hm
  · exact residual_group_1_sound hm
  · exact residual_group_2_sound hm
  · exact residual_group_3_sound hm

end Erdos577.WeightedPaw.D2
