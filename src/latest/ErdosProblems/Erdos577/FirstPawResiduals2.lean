import ErdosProblems.Erdos577.FirstPawMasks2

/-! Exact cyclic row and diagonal certificates for source patterns (3)–(8). -/

namespace Erdos577.FirstPaw.D2

private theorem residual_0 : Classified 2 3059 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_1 : Classified 2 3065 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_2 : Classified 2 3830 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_3 : Classified 2 3836 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_4 : Classified 2 4082 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_5 : Classified 2 4088 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_6 : Classified 2 9203 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_7 : Classified 2 9974 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_8 : Classified 2 10739 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_9 : Classified 2 10995 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_10 : Classified 2 10998 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_11 : Classified 2 11002 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_12 : Classified 2 11123 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_13 : Classified 2 11187 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_14 : Classified 2 11219 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_15 : Classified 2 11235 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_16 : Classified 2 11249 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_17 : Classified 2 11250 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_18 : Classified 2 11251 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_19 : Classified 2 11510 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_20 : Classified 2 11894 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_21 : Classified 2 11958 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_22 : Classified 2 11990 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_23 : Classified 2 12006 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_24 : Classified 2 12018 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_25 : Classified 2 12020 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_26 : Classified 2 12022 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_27 : Classified 2 13043 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_28 : Classified 2 14066 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_29 : Classified 2 14585 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_30 : Classified 2 16042 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_31 : Classified 2 25334 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_32 : Classified 2 25586 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_33 : Classified 2 26876 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_34 : Classified 2 27562 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_35 : Classified 2 33785 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_36 : Classified 2 34556 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_37 : Classified 2 35321 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_38 : Classified 2 35577 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_39 : Classified 2 35578 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_40 : Classified 2 35580 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_41 : Classified 2 35705 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_42 : Classified 2 35769 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_43 : Classified 2 35801 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_44 : Classified 2 35817 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_45 : Classified 2 35825 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_46 : Classified 2 35832 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_47 : Classified 2 35833 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_48 : Classified 2 36092 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_49 : Classified 2 36476 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_50 : Classified 2 36540 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_51 : Classified 2 36572 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_52 : Classified 2 36588 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_53 : Classified 2 36596 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_54 : Classified 2 36600 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_55 : Classified 2 36604 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_56 : Classified 2 37619 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_57 : Classified 2 39161 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_58 : Classified 2 40184 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_59 : Classified 2 40618 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_60 : Classified 2 41715 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_61 : Classified 2 41718 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_62 : Classified 2 41722 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_63 : Classified 2 43257 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_64 : Classified 2 43258 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_65 : Classified 2 43260 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_66 : Classified 2 43642 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_67 : Classified 2 43706 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_68 : Classified 2 43738 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_69 : Classified 2 43754 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_70 : Classified 2 43762 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_71 : Classified 2 43768 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_72 : Classified 2 43770 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  left
  decide +kernel

private theorem residual_73 : Classified 2 43946 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_74 : Classified 2 43954 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_75 : Classified 2 43960 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_76 : Classified 2 44714 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_77 : Classified 2 44770 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_78 : Classified 2 44776 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_79 : Classified 2 45299 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_80 : Classified 2 45305 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_81 : Classified 2 45683 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_82 : Classified 2 45747 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_83 : Classified 2 45779 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_84 : Classified 2 45795 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_85 : Classified 2 45809 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_86 : Classified 2 45810 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_87 : Classified 2 45811 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_88 : Classified 2 46762 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_89 : Classified 2 47225 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_90 : Classified 2 47289 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_91 : Classified 2 47321 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_92 : Classified 2 47337 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_93 : Classified 2 47345 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_94 : Classified 2 47352 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_95 : Classified 2 47353 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_96 : Classified 2 47786 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_97 : Classified 2 47794 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_98 : Classified 2 47800 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_99 : Classified 2 48298 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_100 : Classified 2 48682 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_101 : Classified 2 48778 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_102 : Classified 2 48802 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_103 : Classified 2 48808 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_104 : Classified 2 48810 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_105 : Classified 2 49910 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_106 : Classified 2 51452 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_107 : Classified 2 51704 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  left
  decide +kernel

private theorem residual_108 : Classified 2 52138 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_109 : Classified 2 57590 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_110 : Classified 2 57596 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_111 : Classified 2 57974 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_112 : Classified 2 58038 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_113 : Classified 2 58070 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_114 : Classified 2 58086 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_115 : Classified 2 58098 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_116 : Classified 2 58100 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_117 : Classified 2 58102 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_118 : Classified 2 58282 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_119 : Classified 2 59516 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_120 : Classified 2 59580 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_121 : Classified 2 59612 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_122 : Classified 2 59628 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_123 : Classified 2 59636 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_124 : Classified 2 59640 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_125 : Classified 2 59644 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  left
  decide +kernel

private theorem residual_126 : Classified 2 59818 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_127 : Classified 2 60074 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_128 : Classified 2 60130 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_129 : Classified 2 60136 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 2, 1, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  left
  decide +kernel

private theorem residual_130 : Classified 2 60202 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_131 : Classified 2 60298 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_132 : Classified 2 60322 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_133 : Classified 2 60328 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_134 : Classified 2 60330 := by
  refine ⟨by decide +kernel, by decide +kernel, false,
    ⟨![1, 2, 3, 0], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  left
  decide +kernel

private theorem residual_135 : Classified 2 61682 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![1, 0, 3, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private theorem residual_136 : Classified 2 61688 := by
  refine ⟨by decide +kernel, by decide +kernel, true,
    ⟨![3, 0, 1, 2], by decide +kernel⟩, by decide +kernel, ?_⟩
  right
  right
  right
  right
  right
  decide +kernel

private def residual_group_0 : List ℕ := [
  3059, 3065, 3830, 3836, 4082, 4088, 9203, 9974,
  10739, 10995, 10998, 11002, 11123, 11187, 11219, 11235]

private theorem residual_group_0_sound {m : ℕ} (h : m ∈ residual_group_0) : Classified 2 m := by
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
  11249, 11250, 11251, 11510, 11894, 11958, 11990, 12006,
  12018, 12020, 12022, 13043, 14066, 14585, 16042, 25334]

private theorem residual_group_1_sound {m : ℕ} (h : m ∈ residual_group_1) : Classified 2 m := by
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
  25586, 26876, 27562, 33785, 34556, 35321, 35577, 35578,
  35580, 35705, 35769, 35801, 35817, 35825, 35832, 35833]

private theorem residual_group_2_sound {m : ℕ} (h : m ∈ residual_group_2) : Classified 2 m := by
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
  36092, 36476, 36540, 36572, 36588, 36596, 36600, 36604,
  37619, 39161, 40184, 40618, 41715, 41718, 41722, 43257]

private theorem residual_group_3_sound {m : ℕ} (h : m ∈ residual_group_3) : Classified 2 m := by
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
  43258, 43260, 43642, 43706, 43738, 43754, 43762, 43768,
  43770, 43946, 43954, 43960, 44714, 44770, 44776, 45299]

private theorem residual_group_4_sound {m : ℕ} (h : m ∈ residual_group_4) : Classified 2 m := by
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
  45305, 45683, 45747, 45779, 45795, 45809, 45810, 45811,
  46762, 47225, 47289, 47321, 47337, 47345, 47352, 47353]

private theorem residual_group_5_sound {m : ℕ} (h : m ∈ residual_group_5) : Classified 2 m := by
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
  47786, 47794, 47800, 48298, 48682, 48778, 48802, 48808,
  48810, 49910, 51452, 51704, 52138, 57590, 57596, 57974]

private theorem residual_group_6_sound {m : ℕ} (h : m ∈ residual_group_6) : Classified 2 m := by
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
  58038, 58070, 58086, 58098, 58100, 58102, 58282, 59516,
  59580, 59612, 59628, 59636, 59640, 59644, 59818, 60074]

private theorem residual_group_7_sound {m : ℕ} (h : m ∈ residual_group_7) : Classified 2 m := by
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
  60130, 60136, 60202, 60298, 60322, 60328, 60330, 61682,
  61688]

private theorem residual_group_8_sound {m : ℕ} (h : m ∈ residual_group_8) : Classified 2 m := by
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

theorem residuals_sound {m : ℕ} (h : m ∈ residualMasks) : Classified 2 m := by
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

end Erdos577.FirstPaw.D2
