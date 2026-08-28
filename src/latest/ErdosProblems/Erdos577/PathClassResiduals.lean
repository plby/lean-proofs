import ErdosProblems.Erdos577.PathClassMasks

/-! Exact normalized path rows, contact bounds, and common-column witnesses. -/

namespace Erdos577.PathClass

private theorem residual_0 : Classified 1015 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_1 : Classified 1019 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_2 : Classified 1527 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_3 : Classified 1533 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_4 : Classified 1783 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_5 : Classified 1790 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_6 : Classified 1911 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_7 : Classified 1975 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_8 : Classified 2007 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_9 : Classified 2023 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_10 : Classified 2035 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_11 : Classified 2037 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_12 : Classified 2038 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_13 : Classified 2039 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_14 : Classified 2555 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_15 : Classified 2557 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_16 : Classified 2811 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_17 : Classified 2814 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_18 : Classified 2939 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_19 : Classified 3003 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_20 : Classified 3035 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_21 : Classified 3051 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_22 : Classified 3059 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_23 : Classified 3065 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_24 : Classified 3066 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_25 : Classified 3067 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_26 : Classified 3325 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_27 : Classified 3326 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_28 : Classified 3453 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_29 : Classified 3517 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_30 : Classified 3549 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_31 : Classified 3565 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_32 : Classified 3573 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_33 : Classified 3577 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_34 : Classified 3580 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_35 : Classified 3581 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_36 : Classified 3710 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_37 : Classified 3774 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_38 : Classified 3806 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_39 : Classified 3822 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_40 : Classified 3830 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_41 : Classified 3834 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_42 : Classified 3836 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_43 : Classified 3838 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_44 : Classified 6003 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_45 : Classified 6005 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_46 : Classified 7091 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_47 : Classified 7097 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_48 : Classified 7637 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_49 : Classified 7641 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_50 : Classified 10099 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_51 : Classified 10102 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_52 : Classified 11187 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_53 : Classified 11194 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_54 : Classified 12006 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_55 : Classified 12010 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_56 : Classified 13171 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_57 : Classified 13235 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_58 : Classified 13683 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_59 : Classified 13939 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_60 : Classified 14131 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_61 : Classified 14163 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_62 : Classified 14179 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_63 : Classified 14193 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_64 : Classified 14194 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_65 : Classified 14195 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_66 : Classified 14771 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_67 : Classified 15027 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_68 : Classified 15155 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_69 : Classified 15251 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_70 : Classified 15267 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_71 : Classified 15281 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_72 : Classified 15282 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_73 : Classified 15283 := by
  refine ⟨by decide +kernel, false, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_74 : Classified 16240 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_75 : Classified 16304 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_76 : Classified 18293 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_77 : Classified 18294 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_78 : Classified 19925 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_79 : Classified 19932 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_80 : Classified 20198 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_81 : Classified 20204 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_82 : Classified 21365 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_83 : Classified 21877 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_84 : Classified 21973 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_85 : Classified 22133 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_86 : Classified 22325 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_87 : Classified 22357 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_88 : Classified 22373 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_89 : Classified 22385 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_90 : Classified 22388 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_91 : Classified 22389 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 1, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_92 : Classified 22997 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_93 : Classified 23765 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_94 : Classified 23893 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_95 : Classified 23957 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_96 : Classified 24005 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_97 : Classified 24017 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_98 : Classified 24020 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_99 : Classified 24021 := by
  refine ⟨by decide +kernel, false, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_100 : Classified 24432 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_101 : Classified 24528 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_102 : Classified 25462 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_103 : Classified 25974 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_104 : Classified 26230 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_105 : Classified 26342 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_106 : Classified 26422 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_107 : Classified 26454 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_108 : Classified 26470 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_109 : Classified 26482 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_110 : Classified 26484 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_111 : Classified 26486 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 0, 3], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_112 : Classified 27366 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_113 : Classified 27878 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_114 : Classified 28262 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_115 : Classified 28326 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_116 : Classified 28358 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_117 : Classified 28386 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_118 : Classified 28388 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_119 : Classified 28390 := by
  refine ⟨by decide +kernel, false, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_120 : Classified 28528 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_121 : Classified 28640 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_122 : Classified 30576 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_123 : Classified 31600 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_124 : Classified 32112 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_125 : Classified 32368 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_126 : Classified 32560 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_127 : Classified 32592 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_128 : Classified 32608 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_129 : Classified 32624 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 2, 3], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_130 : Classified 35769 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_131 : Classified 35770 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_132 : Classified 36313 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_133 : Classified 36316 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_134 : Classified 36586 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_135 : Classified 36588 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_136 : Classified 37817 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_137 : Classified 38361 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_138 : Classified 39353 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_139 : Classified 39385 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_140 : Classified 39609 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_141 : Classified 39737 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_142 : Classified 39833 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_143 : Classified 39849 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_144 : Classified 39857 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_145 : Classified 39864 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_146 : Classified 39865 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 1, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_147 : Classified 40153 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_148 : Classified 40281 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_149 : Classified 40345 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_150 : Classified 40393 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_151 : Classified 40401 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_152 : Classified 40408 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_153 : Classified 40409 := by
  refine ⟨by decide +kernel, false, ⟨![0, 3, 2, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_154 : Classified 40880 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_155 : Classified 40912 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_156 : Classified 41914 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_157 : Classified 42730 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_158 : Classified 43450 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_159 : Classified 43706 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_160 : Classified 43754 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_161 : Classified 43834 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_162 : Classified 43930 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_163 : Classified 43946 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_164 : Classified 43954 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_165 : Classified 43960 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_166 : Classified 43962 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 0, 2], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_167 : Classified 44266 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_168 : Classified 44650 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_169 : Classified 44714 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_170 : Classified 44746 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_171 : Classified 44770 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_172 : Classified 44776 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_173 : Classified 44778 := by
  refine ⟨by decide +kernel, false, ⟨![1, 3, 2, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_174 : Classified 44976 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_175 : Classified 45024 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_176 : Classified 47024 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_177 : Classified 48048 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_178 : Classified 48560 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_179 : Classified 48816 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_180 : Classified 48944 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_181 : Classified 49040 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_182 : Classified 49056 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_183 : Classified 49072 := by
  refine ⟨by decide +kernel, true, ⟨![0, 1, 3, 2], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_184 : Classified 50652 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_185 : Classified 50924 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_186 : Classified 51676 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_187 : Classified 51948 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_188 : Classified 52444 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_189 : Classified 52460 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_190 : Classified 52572 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_191 : Classified 52636 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_192 : Classified 52684 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_193 : Classified 52692 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_194 : Classified 52696 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_195 : Classified 52700 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 0, 1], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_196 : Classified 52844 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_197 : Classified 52908 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_198 : Classified 52940 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_199 : Classified 52964 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_200 : Classified 52968 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_201 : Classified 52972 := by
  refine ⟨by decide +kernel, false, ⟨![2, 3, 1, 0], by decide +kernel⟩, ?_⟩
  right
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_202 : Classified 53200 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_203 : Classified 53216 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_204 : Classified 55248 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_205 : Classified 56272 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_206 : Classified 56784 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_207 : Classified 57040 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_208 : Classified 57168 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_209 : Classified 57232 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_210 : Classified 57280 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_211 : Classified 57296 := by
  refine ⟨by decide +kernel, true, ⟨![0, 2, 3, 1], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_212 : Classified 59360 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_213 : Classified 60384 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_214 : Classified 60896 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_215 : Classified 61152 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_216 : Classified 61280 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_217 : Classified 61344 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_218 : Classified 61376 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private theorem residual_219 : Classified 61408 := by
  refine ⟨by decide +kernel, true, ⟨![1, 2, 3, 0], by decide +kernel⟩, ?_⟩
  left
  exact ⟨by decide +kernel, by decide +kernel⟩

private def residual_group_0 : List ℕ := [
  1015, 1019, 1527, 1533, 1783, 1790, 1911, 1975,
  2007, 2023, 2035, 2037, 2038, 2039, 2555, 2557]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) : Classified m := by
  simp only [residual_group_0, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_1 : List ℕ := [
  2811, 2814, 2939, 3003, 3035, 3051, 3059, 3065,
  3066, 3067, 3325, 3326, 3453, 3517, 3549, 3565]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) : Classified m := by
  simp only [residual_group_1, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_2 : List ℕ := [
  3573, 3577, 3580, 3581, 3710, 3774, 3806, 3822,
  3830, 3834, 3836, 3838, 6003, 6005, 7091, 7097]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) : Classified m := by
  simp only [residual_group_2, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_3 : List ℕ := [
  7637, 7641, 10099, 10102, 11187, 11194, 12006, 12010,
  13171, 13235, 13683, 13939, 14131, 14163, 14179, 14193]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) : Classified m := by
  simp only [residual_group_3, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_4 : List ℕ := [
  14194, 14195, 14771, 15027, 15155, 15251, 15267, 15281,
  15282, 15283, 16240, 16304, 18293, 18294, 19925, 19932]

private theorem residual_group_4_sound {m : ℕ} (h : m ∈ residual_group_4) : Classified m := by
  simp only [residual_group_4, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_5 : List ℕ := [
  20198, 20204, 21365, 21877, 21973, 22133, 22325, 22357,
  22373, 22385, 22388, 22389, 22997, 23765, 23893, 23957]

private theorem residual_group_5_sound {m : ℕ} (h : m ∈ residual_group_5) : Classified m := by
  simp only [residual_group_5, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_6 : List ℕ := [
  24005, 24017, 24020, 24021, 24432, 24528, 25462, 25974,
  26230, 26342, 26422, 26454, 26470, 26482, 26484, 26486]

private theorem residual_group_6_sound {m : ℕ} (h : m ∈ residual_group_6) : Classified m := by
  simp only [residual_group_6, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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

private def residual_group_7 : List ℕ := [
  27366, 27878, 28262, 28326, 28358, 28386, 28388, 28390,
  28528, 28640, 30576, 31600, 32112, 32368, 32560, 32592]

private theorem residual_group_7_sound {m : ℕ} (h : m ∈ residual_group_7) : Classified m := by
  simp only [residual_group_7, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
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
  · exact residual_124
  · exact residual_125
  · exact residual_126
  · exact residual_127

private def residual_group_8 : List ℕ := [
  32608, 32624, 35769, 35770, 36313, 36316, 36586, 36588,
  37817, 38361, 39353, 39385, 39609, 39737, 39833, 39849]

private theorem residual_group_8_sound {m : ℕ} (h : m ∈ residual_group_8) : Classified m := by
  simp only [residual_group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_128
  · exact residual_129
  · exact residual_130
  · exact residual_131
  · exact residual_132
  · exact residual_133
  · exact residual_134
  · exact residual_135
  · exact residual_136
  · exact residual_137
  · exact residual_138
  · exact residual_139
  · exact residual_140
  · exact residual_141
  · exact residual_142
  · exact residual_143

private def residual_group_9 : List ℕ := [
  39857, 39864, 39865, 40153, 40281, 40345, 40393, 40401,
  40408, 40409, 40880, 40912, 41914, 42730, 43450, 43706]

private theorem residual_group_9_sound {m : ℕ} (h : m ∈ residual_group_9) : Classified m := by
  simp only [residual_group_9, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_144
  · exact residual_145
  · exact residual_146
  · exact residual_147
  · exact residual_148
  · exact residual_149
  · exact residual_150
  · exact residual_151
  · exact residual_152
  · exact residual_153
  · exact residual_154
  · exact residual_155
  · exact residual_156
  · exact residual_157
  · exact residual_158
  · exact residual_159

private def residual_group_10 : List ℕ := [
  43754, 43834, 43930, 43946, 43954, 43960, 43962, 44266,
  44650, 44714, 44746, 44770, 44776, 44778, 44976, 45024]

private theorem residual_group_10_sound {m : ℕ} (h : m ∈ residual_group_10) : Classified m := by
  simp only [residual_group_10, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_160
  · exact residual_161
  · exact residual_162
  · exact residual_163
  · exact residual_164
  · exact residual_165
  · exact residual_166
  · exact residual_167
  · exact residual_168
  · exact residual_169
  · exact residual_170
  · exact residual_171
  · exact residual_172
  · exact residual_173
  · exact residual_174
  · exact residual_175

private def residual_group_11 : List ℕ := [
  47024, 48048, 48560, 48816, 48944, 49040, 49056, 49072,
  50652, 50924, 51676, 51948, 52444, 52460, 52572, 52636]

private theorem residual_group_11_sound {m : ℕ} (h : m ∈ residual_group_11) : Classified m := by
  simp only [residual_group_11, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_176
  · exact residual_177
  · exact residual_178
  · exact residual_179
  · exact residual_180
  · exact residual_181
  · exact residual_182
  · exact residual_183
  · exact residual_184
  · exact residual_185
  · exact residual_186
  · exact residual_187
  · exact residual_188
  · exact residual_189
  · exact residual_190
  · exact residual_191

private def residual_group_12 : List ℕ := [
  52684, 52692, 52696, 52700, 52844, 52908, 52940, 52964,
  52968, 52972, 53200, 53216, 55248, 56272, 56784, 57040]

private theorem residual_group_12_sound {m : ℕ} (h : m ∈ residual_group_12) : Classified m := by
  simp only [residual_group_12, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_192
  · exact residual_193
  · exact residual_194
  · exact residual_195
  · exact residual_196
  · exact residual_197
  · exact residual_198
  · exact residual_199
  · exact residual_200
  · exact residual_201
  · exact residual_202
  · exact residual_203
  · exact residual_204
  · exact residual_205
  · exact residual_206
  · exact residual_207

private def residual_group_13 : List ℕ := [
  57168, 57232, 57280, 57296, 59360, 60384, 60896, 61152,
  61280, 61344, 61376, 61408]

private theorem residual_group_13_sound {m : ℕ} (h : m ∈ residual_group_13) : Classified m := by
  simp only [residual_group_13, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_208
  · exact residual_209
  · exact residual_210
  · exact residual_211
  · exact residual_212
  · exact residual_213
  · exact residual_214
  · exact residual_215
  · exact residual_216
  · exact residual_217
  · exact residual_218
  · exact residual_219

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) : Classified m := by
  have hg :
      m ∈ residual_group_0 ∨
      m ∈ residual_group_1 ∨
      m ∈ residual_group_2 ∨
      m ∈ residual_group_3 ∨
      m ∈ residual_group_4 ∨
      m ∈ residual_group_5 ∨
      m ∈ residual_group_6 ∨
      m ∈ residual_group_7 ∨
      m ∈ residual_group_8 ∨
      m ∈ residual_group_9 ∨
      m ∈ residual_group_10 ∨
      m ∈ residual_group_11 ∨
      m ∈ residual_group_12 ∨
      m ∈ residual_group_13 := by
    change m ∈
      residual_group_0 ++
      residual_group_1 ++
      residual_group_2 ++
      residual_group_3 ++
      residual_group_4 ++
      residual_group_5 ++
      residual_group_6 ++
      residual_group_7 ++
      residual_group_8 ++
      residual_group_9 ++
      residual_group_10 ++
      residual_group_11 ++
      residual_group_12 ++
      residual_group_13 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg | hg
  · exact residual_group_0_sound hg
  · exact residual_group_1_sound hg
  · exact residual_group_2_sound hg
  · exact residual_group_3_sound hg
  · exact residual_group_4_sound hg
  · exact residual_group_5_sound hg
  · exact residual_group_6_sound hg
  · exact residual_group_7_sound hg
  · exact residual_group_8_sound hg
  · exact residual_group_9_sound hg
  · exact residual_group_10_sound hg
  · exact residual_group_11_sound hg
  · exact residual_group_12_sound hg
  · exact residual_group_13_sound hg

end Erdos577.PathClass
