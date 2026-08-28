import ErdosProblems.Erdos577.FirstPawMasks1

/-! Exact cyclic row and diagonal certificates for source patterns (3)–(8). -/

namespace Erdos577.FirstPaw.D1

private theorem residual_0 : Classified 1 2035 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_1 : Classified 1 2038 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_2 : Classified 1 3577 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_3 : Classified 1 3580 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_4 : Classified 1 4081 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_5 : Classified 1 4084 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_6 : Classified 1 5107 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_7 : Classified 1 5619 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_8 : Classified 1 5621 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_9 : Classified 1 5625 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 1 5875 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 1 6003 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_12 : Classified 1 6067 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_13 : Classified 1 6099 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_14 : Classified 1 6115 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_15 : Classified 1 6129 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_16 : Classified 1 6130 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_17 : Classified 1 6131 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_18 : Classified 1 6649 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_19 : Classified 1 7417 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_20 : Classified 1 7545 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_21 : Classified 1 7609 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_22 : Classified 1 7641 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_23 : Classified 1 7657 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_24 : Classified 1 7665 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_25 : Classified 1 7672 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_26 : Classified 1 7673 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_27 : Classified 1 12787 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_28 : Classified 1 13558 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_29 : Classified 1 14833 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_30 : Classified 1 15701 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_31 : Classified 1 17398 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_32 : Classified 1 17909 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_33 : Classified 1 17910 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_34 : Classified 1 17916 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_35 : Classified 1 18166 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_36 : Classified 1 18294 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_37 : Classified 1 18358 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 1 18390 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_39 : Classified 1 18406 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_40 : Classified 1 18418 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_41 : Classified 1 18420 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_42 : Classified 1 18422 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_43 : Classified 1 18940 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_44 : Classified 1 19708 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_45 : Classified 1 19836 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_46 : Classified 1 19900 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_47 : Classified 1 19932 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_48 : Classified 1 19948 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_49 : Classified 1 19956 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_50 : Classified 1 19960 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_51 : Classified 1 19964 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_52 : Classified 1 20979 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_53 : Classified 1 20981 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_54 : Classified 1 20985 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_55 : Classified 1 21749 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_56 : Classified 1 21750 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_57 : Classified 1 21756 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_58 : Classified 1 21877 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_59 : Classified 1 21941 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_60 : Classified 1 21973 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_61 : Classified 1 21989 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_62 : Classified 1 22001 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_63 : Classified 1 22004 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_64 : Classified 1 22005 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_65 : Classified 1 22357 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_66 : Classified 1 22385 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_67 : Classified 1 22388 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_68 : Classified 1 23893 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_69 : Classified 1 24017 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_70 : Classified 1 24020 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_71 : Classified 1 25075 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_72 : Classified 1 25846 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_73 : Classified 1 27892 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_74 : Classified 1 27989 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_75 : Classified 1 28915 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_76 : Classified 1 28918 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_77 : Classified 1 29043 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_78 : Classified 1 29107 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_79 : Classified 1 29139 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_80 : Classified 1 29155 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_81 : Classified 1 29169 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_82 : Classified 1 29170 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_83 : Classified 1 29171 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_84 : Classified 1 29814 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_85 : Classified 1 29878 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_86 : Classified 1 29910 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_87 : Classified 1 29926 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_88 : Classified 1 29938 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_89 : Classified 1 29940 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_90 : Classified 1 29942 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_91 : Classified 1 30037 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_92 : Classified 1 30065 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_93 : Classified 1 30068 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_94 : Classified 1 31061 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_95 : Classified 1 31829 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_96 : Classified 1 32021 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_97 : Classified 1 32069 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_98 : Classified 1 32081 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_99 : Classified 1 32084 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_100 : Classified 1 32085 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_101 : Classified 1 37369 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_102 : Classified 1 37873 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_103 : Classified 1 38140 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_104 : Classified 1 38741 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_105 : Classified 1 49657 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_106 : Classified 1 50428 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_107 : Classified 1 50932 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_108 : Classified 1 51029 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_109 : Classified 1 53497 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_110 : Classified 1 53500 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_111 : Classified 1 53625 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_112 : Classified 1 53689 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_113 : Classified 1 53721 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_114 : Classified 1 53737 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_115 : Classified 1 53745 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_116 : Classified 1 53752 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_117 : Classified 1 53753 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_118 : Classified 1 54101 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_119 : Classified 1 54396 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_120 : Classified 1 54460 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_121 : Classified 1 54492 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_122 : Classified 1 54508 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_123 : Classified 1 54516 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_124 : Classified 1 54520 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_125 : Classified 1 54524 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_126 : Classified 1 54613 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_127 : Classified 1 54737 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_128 : Classified 1 54740 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 3, 0, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_129 : Classified 1 54869 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_130 : Classified 1 55061 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_131 : Classified 1 55109 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_132 : Classified 1 55121 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_133 : Classified 1 55124 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_134 : Classified 1 55125 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![0, 3, 2, 1], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_135 : Classified 1 61681 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![0, 1, 2, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_136 : Classified 1 61684 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![2, 1, 0, 3], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private def residual_group_0 : List ℕ := [
  2035, 2038, 3577, 3580, 4081, 4084, 5107, 5619,
  5621, 5625, 5875, 6003, 6067, 6099, 6115, 6129]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) : Classified 1 m := by
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
  6130, 6131, 6649, 7417, 7545, 7609, 7641, 7657,
  7665, 7672, 7673, 12787, 13558, 14833, 15701, 17398]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) : Classified 1 m := by
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
  17909, 17910, 17916, 18166, 18294, 18358, 18390, 18406,
  18418, 18420, 18422, 18940, 19708, 19836, 19900, 19932]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) : Classified 1 m := by
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
  19948, 19956, 19960, 19964, 20979, 20981, 20985, 21749,
  21750, 21756, 21877, 21941, 21973, 21989, 22001, 22004]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) : Classified 1 m := by
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
  22005, 22357, 22385, 22388, 23893, 24017, 24020, 25075,
  25846, 27892, 27989, 28915, 28918, 29043, 29107, 29139]

private theorem residual_group_4_sound {m : ℕ} (h : m ∈ residual_group_4) : Classified 1 m := by
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
  29155, 29169, 29170, 29171, 29814, 29878, 29910, 29926,
  29938, 29940, 29942, 30037, 30065, 30068, 31061, 31829]

private theorem residual_group_5_sound {m : ℕ} (h : m ∈ residual_group_5) : Classified 1 m := by
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
  32021, 32069, 32081, 32084, 32085, 37369, 37873, 38140,
  38741, 49657, 50428, 50932, 51029, 53497, 53500, 53625]

private theorem residual_group_6_sound {m : ℕ} (h : m ∈ residual_group_6) : Classified 1 m := by
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
  53689, 53721, 53737, 53745, 53752, 53753, 54101, 54396,
  54460, 54492, 54508, 54516, 54520, 54524, 54613, 54737]

private theorem residual_group_7_sound {m : ℕ} (h : m ∈ residual_group_7) : Classified 1 m := by
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
  54740, 54869, 55061, 55109, 55121, 55124, 55125, 61681,
  61684]

private theorem residual_group_8_sound {m : ℕ} (h : m ∈ residual_group_8) : Classified 1 m := by
  simp only [residual_group_8, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact residual_128
  · exact residual_129
  · exact residual_130
  · exact residual_131
  · exact residual_132
  · exact residual_133
  · exact residual_134
  · exact residual_135
  · exact residual_136

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) : Classified 1 m := by
  have hg :
      m ∈ residual_group_0 ∨
      m ∈ residual_group_1 ∨
      m ∈ residual_group_2 ∨
      m ∈ residual_group_3 ∨
      m ∈ residual_group_4 ∨
      m ∈ residual_group_5 ∨
      m ∈ residual_group_6 ∨
      m ∈ residual_group_7 ∨
      m ∈ residual_group_8 := by
    change m ∈
      residual_group_0 ++
      residual_group_1 ++
      residual_group_2 ++
      residual_group_3 ++
      residual_group_4 ++
      residual_group_5 ++
      residual_group_6 ++
      residual_group_7 ++
      residual_group_8 at h
    simpa only [List.mem_append, or_assoc] using h
  rcases hg with
    hg | hg | hg | hg | hg | hg | hg | hg | hg
  · exact residual_group_0_sound hg
  · exact residual_group_1_sound hg
  · exact residual_group_2_sound hg
  · exact residual_group_3_sound hg
  · exact residual_group_4_sound hg
  · exact residual_group_5_sound hg
  · exact residual_group_6_sound hg
  · exact residual_group_7_sound hg
  · exact residual_group_8_sound hg

end Erdos577.FirstPaw.D1
