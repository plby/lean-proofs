import ErdosProblems.Erdos577.UnattachedModel

/-! Kernel-checked weighted coverage for diagonal mask 0. -/

namespace Erdos577.Unattached.D0

def masks : List ℕ := [
  7, 11, 13, 14, 26, 37, 74, 133, 266, 517,
  1034, 2053, 4106, 8197, 16394, 32773, 278, 284, 553, 556,
  1091, 1097, 2179, 2182, 4118, 4124, 4358, 4364, 8233, 8236,
  8713, 8716, 16451, 16457, 17411, 17417, 32899, 32902, 34819, 34822,
  4513, 4576, 4681, 4684, 4742, 4748, 4804, 4808, 5056, 5161,
  5164, 5251, 5254, 5762, 5764, 5776, 6182, 6188, 6211, 6214,
  6242, 6244, 6496, 6673, 7204, 7208, 7216, 7696, 8521, 8524,
  8582, 8588, 8644, 8648, 8786, 8912, 9152, 9241, 9244, 9347,
  9353, 9361, 9368, 9506, 9872, 10262, 10268, 10307, 10313, 10561,
  10568, 10592, 11284, 11288, 11312, 11552, 12736, 12992, 13441, 13442,
  13504, 14401, 14402, 14528, 15376, 15392, 15424, 15488, 16681, 16684,
  16771, 16774, 16921, 16924, 17027, 17033, 17041, 17048, 17281, 17282,
  17344, 17572, 17584, 18064, 18451, 18454, 18467, 18473, 18481, 18482,
  18721, 18728, 18784, 19012, 19264, 19504, 21026, 22664, 24962, 24964,
  24976, 25232, 25744, 26642, 26644, 26768, 26896, 26912, 26944, 27008,
  30848, 33062, 33068, 33091, 33094, 33122, 33124, 33302, 33308, 33347,
  33353, 33601, 33602, 33728, 33811, 33814, 33827, 33833, 33841, 33842,
  34184, 34322, 34324, 34448, 34688, 34904, 34928, 35168, 35888, 37216,
  37441, 37448, 37472, 37921, 37928, 37984, 38416, 38432, 38464, 38528,
  39008, 41233, 42052, 46144, 49444, 49448, 49456, 49684, 49688, 49712,
  49936, 49952, 49984, 50048, 50224, 51248, 53792, 57616, 963, 972,
  1686, 1689, 2406, 2409, 3123, 3132, 12483, 12492, 15363, 15372,
  24726, 24729, 26886, 26889, 36966, 36969, 38406, 38409, 49203, 49212,
  49923, 49932]

def covered (m : ℕ) : Bool := masks.any fun w ↦ m &&& w == w

private theorem coverage_0 : ∀ lo : Fin 256,
    13 ≤ weightedCount (0 * 256 + lo.val) → covered (0 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    13 ≤ weightedCount (1 * 256 + lo.val) → covered (1 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    13 ≤ weightedCount (2 * 256 + lo.val) → covered (2 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    13 ≤ weightedCount (3 * 256 + lo.val) → covered (3 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    13 ≤ weightedCount (4 * 256 + lo.val) → covered (4 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    13 ≤ weightedCount (5 * 256 + lo.val) → covered (5 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    13 ≤ weightedCount (6 * 256 + lo.val) → covered (6 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    13 ≤ weightedCount (7 * 256 + lo.val) → covered (7 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    13 ≤ weightedCount (8 * 256 + lo.val) → covered (8 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    13 ≤ weightedCount (9 * 256 + lo.val) → covered (9 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    13 ≤ weightedCount (10 * 256 + lo.val) → covered (10 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    13 ≤ weightedCount (11 * 256 + lo.val) → covered (11 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    13 ≤ weightedCount (12 * 256 + lo.val) → covered (12 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    13 ≤ weightedCount (13 * 256 + lo.val) → covered (13 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    13 ≤ weightedCount (14 * 256 + lo.val) → covered (14 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    13 ≤ weightedCount (15 * 256 + lo.val) → covered (15 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    13 ≤ weightedCount (16 * 256 + lo.val) → covered (16 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    13 ≤ weightedCount (17 * 256 + lo.val) → covered (17 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    13 ≤ weightedCount (18 * 256 + lo.val) → covered (18 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    13 ≤ weightedCount (19 * 256 + lo.val) → covered (19 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    13 ≤ weightedCount (20 * 256 + lo.val) → covered (20 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    13 ≤ weightedCount (21 * 256 + lo.val) → covered (21 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    13 ≤ weightedCount (22 * 256 + lo.val) → covered (22 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    13 ≤ weightedCount (23 * 256 + lo.val) → covered (23 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    13 ≤ weightedCount (24 * 256 + lo.val) → covered (24 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    13 ≤ weightedCount (25 * 256 + lo.val) → covered (25 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    13 ≤ weightedCount (26 * 256 + lo.val) → covered (26 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    13 ≤ weightedCount (27 * 256 + lo.val) → covered (27 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    13 ≤ weightedCount (28 * 256 + lo.val) → covered (28 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    13 ≤ weightedCount (29 * 256 + lo.val) → covered (29 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    13 ≤ weightedCount (30 * 256 + lo.val) → covered (30 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    13 ≤ weightedCount (31 * 256 + lo.val) → covered (31 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    13 ≤ weightedCount (32 * 256 + lo.val) → covered (32 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    13 ≤ weightedCount (33 * 256 + lo.val) → covered (33 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    13 ≤ weightedCount (34 * 256 + lo.val) → covered (34 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    13 ≤ weightedCount (35 * 256 + lo.val) → covered (35 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    13 ≤ weightedCount (36 * 256 + lo.val) → covered (36 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    13 ≤ weightedCount (37 * 256 + lo.val) → covered (37 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    13 ≤ weightedCount (38 * 256 + lo.val) → covered (38 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    13 ≤ weightedCount (39 * 256 + lo.val) → covered (39 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    13 ≤ weightedCount (40 * 256 + lo.val) → covered (40 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    13 ≤ weightedCount (41 * 256 + lo.val) → covered (41 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    13 ≤ weightedCount (42 * 256 + lo.val) → covered (42 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    13 ≤ weightedCount (43 * 256 + lo.val) → covered (43 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    13 ≤ weightedCount (44 * 256 + lo.val) → covered (44 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    13 ≤ weightedCount (45 * 256 + lo.val) → covered (45 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    13 ≤ weightedCount (46 * 256 + lo.val) → covered (46 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    13 ≤ weightedCount (47 * 256 + lo.val) → covered (47 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    13 ≤ weightedCount (48 * 256 + lo.val) → covered (48 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    13 ≤ weightedCount (49 * 256 + lo.val) → covered (49 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    13 ≤ weightedCount (50 * 256 + lo.val) → covered (50 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    13 ≤ weightedCount (51 * 256 + lo.val) → covered (51 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    13 ≤ weightedCount (52 * 256 + lo.val) → covered (52 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    13 ≤ weightedCount (53 * 256 + lo.val) → covered (53 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    13 ≤ weightedCount (54 * 256 + lo.val) → covered (54 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    13 ≤ weightedCount (55 * 256 + lo.val) → covered (55 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    13 ≤ weightedCount (56 * 256 + lo.val) → covered (56 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    13 ≤ weightedCount (57 * 256 + lo.val) → covered (57 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    13 ≤ weightedCount (58 * 256 + lo.val) → covered (58 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    13 ≤ weightedCount (59 * 256 + lo.val) → covered (59 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    13 ≤ weightedCount (60 * 256 + lo.val) → covered (60 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    13 ≤ weightedCount (61 * 256 + lo.val) → covered (61 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    13 ≤ weightedCount (62 * 256 + lo.val) → covered (62 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    13 ≤ weightedCount (63 * 256 + lo.val) → covered (63 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    13 ≤ weightedCount (64 * 256 + lo.val) → covered (64 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    13 ≤ weightedCount (65 * 256 + lo.val) → covered (65 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    13 ≤ weightedCount (66 * 256 + lo.val) → covered (66 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    13 ≤ weightedCount (67 * 256 + lo.val) → covered (67 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    13 ≤ weightedCount (68 * 256 + lo.val) → covered (68 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    13 ≤ weightedCount (69 * 256 + lo.val) → covered (69 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    13 ≤ weightedCount (70 * 256 + lo.val) → covered (70 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    13 ≤ weightedCount (71 * 256 + lo.val) → covered (71 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    13 ≤ weightedCount (72 * 256 + lo.val) → covered (72 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    13 ≤ weightedCount (73 * 256 + lo.val) → covered (73 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    13 ≤ weightedCount (74 * 256 + lo.val) → covered (74 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    13 ≤ weightedCount (75 * 256 + lo.val) → covered (75 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    13 ≤ weightedCount (76 * 256 + lo.val) → covered (76 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    13 ≤ weightedCount (77 * 256 + lo.val) → covered (77 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    13 ≤ weightedCount (78 * 256 + lo.val) → covered (78 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    13 ≤ weightedCount (79 * 256 + lo.val) → covered (79 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    13 ≤ weightedCount (80 * 256 + lo.val) → covered (80 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    13 ≤ weightedCount (81 * 256 + lo.val) → covered (81 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    13 ≤ weightedCount (82 * 256 + lo.val) → covered (82 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    13 ≤ weightedCount (83 * 256 + lo.val) → covered (83 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    13 ≤ weightedCount (84 * 256 + lo.val) → covered (84 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    13 ≤ weightedCount (85 * 256 + lo.val) → covered (85 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    13 ≤ weightedCount (86 * 256 + lo.val) → covered (86 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    13 ≤ weightedCount (87 * 256 + lo.val) → covered (87 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    13 ≤ weightedCount (88 * 256 + lo.val) → covered (88 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    13 ≤ weightedCount (89 * 256 + lo.val) → covered (89 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    13 ≤ weightedCount (90 * 256 + lo.val) → covered (90 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    13 ≤ weightedCount (91 * 256 + lo.val) → covered (91 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    13 ≤ weightedCount (92 * 256 + lo.val) → covered (92 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    13 ≤ weightedCount (93 * 256 + lo.val) → covered (93 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    13 ≤ weightedCount (94 * 256 + lo.val) → covered (94 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    13 ≤ weightedCount (95 * 256 + lo.val) → covered (95 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    13 ≤ weightedCount (96 * 256 + lo.val) → covered (96 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    13 ≤ weightedCount (97 * 256 + lo.val) → covered (97 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    13 ≤ weightedCount (98 * 256 + lo.val) → covered (98 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    13 ≤ weightedCount (99 * 256 + lo.val) → covered (99 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    13 ≤ weightedCount (100 * 256 + lo.val) → covered (100 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    13 ≤ weightedCount (101 * 256 + lo.val) → covered (101 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    13 ≤ weightedCount (102 * 256 + lo.val) → covered (102 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    13 ≤ weightedCount (103 * 256 + lo.val) → covered (103 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    13 ≤ weightedCount (104 * 256 + lo.val) → covered (104 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    13 ≤ weightedCount (105 * 256 + lo.val) → covered (105 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    13 ≤ weightedCount (106 * 256 + lo.val) → covered (106 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    13 ≤ weightedCount (107 * 256 + lo.val) → covered (107 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    13 ≤ weightedCount (108 * 256 + lo.val) → covered (108 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    13 ≤ weightedCount (109 * 256 + lo.val) → covered (109 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    13 ≤ weightedCount (110 * 256 + lo.val) → covered (110 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    13 ≤ weightedCount (111 * 256 + lo.val) → covered (111 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    13 ≤ weightedCount (112 * 256 + lo.val) → covered (112 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    13 ≤ weightedCount (113 * 256 + lo.val) → covered (113 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    13 ≤ weightedCount (114 * 256 + lo.val) → covered (114 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    13 ≤ weightedCount (115 * 256 + lo.val) → covered (115 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    13 ≤ weightedCount (116 * 256 + lo.val) → covered (116 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    13 ≤ weightedCount (117 * 256 + lo.val) → covered (117 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    13 ≤ weightedCount (118 * 256 + lo.val) → covered (118 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    13 ≤ weightedCount (119 * 256 + lo.val) → covered (119 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    13 ≤ weightedCount (120 * 256 + lo.val) → covered (120 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    13 ≤ weightedCount (121 * 256 + lo.val) → covered (121 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    13 ≤ weightedCount (122 * 256 + lo.val) → covered (122 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    13 ≤ weightedCount (123 * 256 + lo.val) → covered (123 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    13 ≤ weightedCount (124 * 256 + lo.val) → covered (124 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    13 ≤ weightedCount (125 * 256 + lo.val) → covered (125 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    13 ≤ weightedCount (126 * 256 + lo.val) → covered (126 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    13 ≤ weightedCount (127 * 256 + lo.val) → covered (127 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    13 ≤ weightedCount (128 * 256 + lo.val) → covered (128 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    13 ≤ weightedCount (129 * 256 + lo.val) → covered (129 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    13 ≤ weightedCount (130 * 256 + lo.val) → covered (130 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    13 ≤ weightedCount (131 * 256 + lo.val) → covered (131 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    13 ≤ weightedCount (132 * 256 + lo.val) → covered (132 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    13 ≤ weightedCount (133 * 256 + lo.val) → covered (133 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    13 ≤ weightedCount (134 * 256 + lo.val) → covered (134 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    13 ≤ weightedCount (135 * 256 + lo.val) → covered (135 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    13 ≤ weightedCount (136 * 256 + lo.val) → covered (136 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    13 ≤ weightedCount (137 * 256 + lo.val) → covered (137 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    13 ≤ weightedCount (138 * 256 + lo.val) → covered (138 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    13 ≤ weightedCount (139 * 256 + lo.val) → covered (139 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    13 ≤ weightedCount (140 * 256 + lo.val) → covered (140 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    13 ≤ weightedCount (141 * 256 + lo.val) → covered (141 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    13 ≤ weightedCount (142 * 256 + lo.val) → covered (142 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    13 ≤ weightedCount (143 * 256 + lo.val) → covered (143 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    13 ≤ weightedCount (144 * 256 + lo.val) → covered (144 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    13 ≤ weightedCount (145 * 256 + lo.val) → covered (145 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    13 ≤ weightedCount (146 * 256 + lo.val) → covered (146 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    13 ≤ weightedCount (147 * 256 + lo.val) → covered (147 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    13 ≤ weightedCount (148 * 256 + lo.val) → covered (148 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    13 ≤ weightedCount (149 * 256 + lo.val) → covered (149 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    13 ≤ weightedCount (150 * 256 + lo.val) → covered (150 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    13 ≤ weightedCount (151 * 256 + lo.val) → covered (151 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    13 ≤ weightedCount (152 * 256 + lo.val) → covered (152 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    13 ≤ weightedCount (153 * 256 + lo.val) → covered (153 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    13 ≤ weightedCount (154 * 256 + lo.val) → covered (154 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    13 ≤ weightedCount (155 * 256 + lo.val) → covered (155 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    13 ≤ weightedCount (156 * 256 + lo.val) → covered (156 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    13 ≤ weightedCount (157 * 256 + lo.val) → covered (157 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    13 ≤ weightedCount (158 * 256 + lo.val) → covered (158 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    13 ≤ weightedCount (159 * 256 + lo.val) → covered (159 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    13 ≤ weightedCount (160 * 256 + lo.val) → covered (160 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    13 ≤ weightedCount (161 * 256 + lo.val) → covered (161 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    13 ≤ weightedCount (162 * 256 + lo.val) → covered (162 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    13 ≤ weightedCount (163 * 256 + lo.val) → covered (163 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    13 ≤ weightedCount (164 * 256 + lo.val) → covered (164 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    13 ≤ weightedCount (165 * 256 + lo.val) → covered (165 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    13 ≤ weightedCount (166 * 256 + lo.val) → covered (166 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    13 ≤ weightedCount (167 * 256 + lo.val) → covered (167 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    13 ≤ weightedCount (168 * 256 + lo.val) → covered (168 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    13 ≤ weightedCount (169 * 256 + lo.val) → covered (169 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    13 ≤ weightedCount (170 * 256 + lo.val) → covered (170 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    13 ≤ weightedCount (171 * 256 + lo.val) → covered (171 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    13 ≤ weightedCount (172 * 256 + lo.val) → covered (172 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    13 ≤ weightedCount (173 * 256 + lo.val) → covered (173 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    13 ≤ weightedCount (174 * 256 + lo.val) → covered (174 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    13 ≤ weightedCount (175 * 256 + lo.val) → covered (175 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    13 ≤ weightedCount (176 * 256 + lo.val) → covered (176 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    13 ≤ weightedCount (177 * 256 + lo.val) → covered (177 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    13 ≤ weightedCount (178 * 256 + lo.val) → covered (178 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    13 ≤ weightedCount (179 * 256 + lo.val) → covered (179 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    13 ≤ weightedCount (180 * 256 + lo.val) → covered (180 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    13 ≤ weightedCount (181 * 256 + lo.val) → covered (181 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    13 ≤ weightedCount (182 * 256 + lo.val) → covered (182 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    13 ≤ weightedCount (183 * 256 + lo.val) → covered (183 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    13 ≤ weightedCount (184 * 256 + lo.val) → covered (184 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    13 ≤ weightedCount (185 * 256 + lo.val) → covered (185 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    13 ≤ weightedCount (186 * 256 + lo.val) → covered (186 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    13 ≤ weightedCount (187 * 256 + lo.val) → covered (187 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    13 ≤ weightedCount (188 * 256 + lo.val) → covered (188 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    13 ≤ weightedCount (189 * 256 + lo.val) → covered (189 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    13 ≤ weightedCount (190 * 256 + lo.val) → covered (190 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    13 ≤ weightedCount (191 * 256 + lo.val) → covered (191 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    13 ≤ weightedCount (192 * 256 + lo.val) → covered (192 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    13 ≤ weightedCount (193 * 256 + lo.val) → covered (193 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    13 ≤ weightedCount (194 * 256 + lo.val) → covered (194 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    13 ≤ weightedCount (195 * 256 + lo.val) → covered (195 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    13 ≤ weightedCount (196 * 256 + lo.val) → covered (196 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    13 ≤ weightedCount (197 * 256 + lo.val) → covered (197 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    13 ≤ weightedCount (198 * 256 + lo.val) → covered (198 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    13 ≤ weightedCount (199 * 256 + lo.val) → covered (199 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    13 ≤ weightedCount (200 * 256 + lo.val) → covered (200 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    13 ≤ weightedCount (201 * 256 + lo.val) → covered (201 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    13 ≤ weightedCount (202 * 256 + lo.val) → covered (202 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    13 ≤ weightedCount (203 * 256 + lo.val) → covered (203 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    13 ≤ weightedCount (204 * 256 + lo.val) → covered (204 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    13 ≤ weightedCount (205 * 256 + lo.val) → covered (205 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    13 ≤ weightedCount (206 * 256 + lo.val) → covered (206 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    13 ≤ weightedCount (207 * 256 + lo.val) → covered (207 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    13 ≤ weightedCount (208 * 256 + lo.val) → covered (208 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    13 ≤ weightedCount (209 * 256 + lo.val) → covered (209 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    13 ≤ weightedCount (210 * 256 + lo.val) → covered (210 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    13 ≤ weightedCount (211 * 256 + lo.val) → covered (211 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    13 ≤ weightedCount (212 * 256 + lo.val) → covered (212 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    13 ≤ weightedCount (213 * 256 + lo.val) → covered (213 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    13 ≤ weightedCount (214 * 256 + lo.val) → covered (214 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    13 ≤ weightedCount (215 * 256 + lo.val) → covered (215 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    13 ≤ weightedCount (216 * 256 + lo.val) → covered (216 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    13 ≤ weightedCount (217 * 256 + lo.val) → covered (217 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    13 ≤ weightedCount (218 * 256 + lo.val) → covered (218 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    13 ≤ weightedCount (219 * 256 + lo.val) → covered (219 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    13 ≤ weightedCount (220 * 256 + lo.val) → covered (220 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    13 ≤ weightedCount (221 * 256 + lo.val) → covered (221 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    13 ≤ weightedCount (222 * 256 + lo.val) → covered (222 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    13 ≤ weightedCount (223 * 256 + lo.val) → covered (223 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    13 ≤ weightedCount (224 * 256 + lo.val) → covered (224 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    13 ≤ weightedCount (225 * 256 + lo.val) → covered (225 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    13 ≤ weightedCount (226 * 256 + lo.val) → covered (226 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    13 ≤ weightedCount (227 * 256 + lo.val) → covered (227 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    13 ≤ weightedCount (228 * 256 + lo.val) → covered (228 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    13 ≤ weightedCount (229 * 256 + lo.val) → covered (229 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    13 ≤ weightedCount (230 * 256 + lo.val) → covered (230 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    13 ≤ weightedCount (231 * 256 + lo.val) → covered (231 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    13 ≤ weightedCount (232 * 256 + lo.val) → covered (232 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    13 ≤ weightedCount (233 * 256 + lo.val) → covered (233 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    13 ≤ weightedCount (234 * 256 + lo.val) → covered (234 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    13 ≤ weightedCount (235 * 256 + lo.val) → covered (235 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    13 ≤ weightedCount (236 * 256 + lo.val) → covered (236 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    13 ≤ weightedCount (237 * 256 + lo.val) → covered (237 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    13 ≤ weightedCount (238 * 256 + lo.val) → covered (238 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    13 ≤ weightedCount (239 * 256 + lo.val) → covered (239 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    13 ≤ weightedCount (240 * 256 + lo.val) → covered (240 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    13 ≤ weightedCount (241 * 256 + lo.val) → covered (241 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    13 ≤ weightedCount (242 * 256 + lo.val) → covered (242 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    13 ≤ weightedCount (243 * 256 + lo.val) → covered (243 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    13 ≤ weightedCount (244 * 256 + lo.val) → covered (244 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    13 ≤ weightedCount (245 * 256 + lo.val) → covered (245 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    13 ≤ weightedCount (246 * 256 + lo.val) → covered (246 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    13 ≤ weightedCount (247 * 256 + lo.val) → covered (247 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    13 ≤ weightedCount (248 * 256 + lo.val) → covered (248 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    13 ≤ weightedCount (249 * 256 + lo.val) → covered (249 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    13 ≤ weightedCount (250 * 256 + lo.val) → covered (250 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    13 ≤ weightedCount (251 * 256 + lo.val) → covered (251 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    13 ≤ weightedCount (252 * 256 + lo.val) → covered (252 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    13 ≤ weightedCount (253 * 256 + lo.val) → covered (253 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    13 ≤ weightedCount (254 * 256 + lo.val) → covered (254 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    13 ≤ weightedCount (255 * 256 + lo.val) → covered (255 * 256 + lo.val) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (h : 13 ≤ weightedCount (hi.val * 256 + lo.val)) :
    covered (hi.val * 256 + lo.val) = true := by
  fin_cases hi
  · exact coverage_0 lo h
  · exact coverage_1 lo h
  · exact coverage_2 lo h
  · exact coverage_3 lo h
  · exact coverage_4 lo h
  · exact coverage_5 lo h
  · exact coverage_6 lo h
  · exact coverage_7 lo h
  · exact coverage_8 lo h
  · exact coverage_9 lo h
  · exact coverage_10 lo h
  · exact coverage_11 lo h
  · exact coverage_12 lo h
  · exact coverage_13 lo h
  · exact coverage_14 lo h
  · exact coverage_15 lo h
  · exact coverage_16 lo h
  · exact coverage_17 lo h
  · exact coverage_18 lo h
  · exact coverage_19 lo h
  · exact coverage_20 lo h
  · exact coverage_21 lo h
  · exact coverage_22 lo h
  · exact coverage_23 lo h
  · exact coverage_24 lo h
  · exact coverage_25 lo h
  · exact coverage_26 lo h
  · exact coverage_27 lo h
  · exact coverage_28 lo h
  · exact coverage_29 lo h
  · exact coverage_30 lo h
  · exact coverage_31 lo h
  · exact coverage_32 lo h
  · exact coverage_33 lo h
  · exact coverage_34 lo h
  · exact coverage_35 lo h
  · exact coverage_36 lo h
  · exact coverage_37 lo h
  · exact coverage_38 lo h
  · exact coverage_39 lo h
  · exact coverage_40 lo h
  · exact coverage_41 lo h
  · exact coverage_42 lo h
  · exact coverage_43 lo h
  · exact coverage_44 lo h
  · exact coverage_45 lo h
  · exact coverage_46 lo h
  · exact coverage_47 lo h
  · exact coverage_48 lo h
  · exact coverage_49 lo h
  · exact coverage_50 lo h
  · exact coverage_51 lo h
  · exact coverage_52 lo h
  · exact coverage_53 lo h
  · exact coverage_54 lo h
  · exact coverage_55 lo h
  · exact coverage_56 lo h
  · exact coverage_57 lo h
  · exact coverage_58 lo h
  · exact coverage_59 lo h
  · exact coverage_60 lo h
  · exact coverage_61 lo h
  · exact coverage_62 lo h
  · exact coverage_63 lo h
  · exact coverage_64 lo h
  · exact coverage_65 lo h
  · exact coverage_66 lo h
  · exact coverage_67 lo h
  · exact coverage_68 lo h
  · exact coverage_69 lo h
  · exact coverage_70 lo h
  · exact coverage_71 lo h
  · exact coverage_72 lo h
  · exact coverage_73 lo h
  · exact coverage_74 lo h
  · exact coverage_75 lo h
  · exact coverage_76 lo h
  · exact coverage_77 lo h
  · exact coverage_78 lo h
  · exact coverage_79 lo h
  · exact coverage_80 lo h
  · exact coverage_81 lo h
  · exact coverage_82 lo h
  · exact coverage_83 lo h
  · exact coverage_84 lo h
  · exact coverage_85 lo h
  · exact coverage_86 lo h
  · exact coverage_87 lo h
  · exact coverage_88 lo h
  · exact coverage_89 lo h
  · exact coverage_90 lo h
  · exact coverage_91 lo h
  · exact coverage_92 lo h
  · exact coverage_93 lo h
  · exact coverage_94 lo h
  · exact coverage_95 lo h
  · exact coverage_96 lo h
  · exact coverage_97 lo h
  · exact coverage_98 lo h
  · exact coverage_99 lo h
  · exact coverage_100 lo h
  · exact coverage_101 lo h
  · exact coverage_102 lo h
  · exact coverage_103 lo h
  · exact coverage_104 lo h
  · exact coverage_105 lo h
  · exact coverage_106 lo h
  · exact coverage_107 lo h
  · exact coverage_108 lo h
  · exact coverage_109 lo h
  · exact coverage_110 lo h
  · exact coverage_111 lo h
  · exact coverage_112 lo h
  · exact coverage_113 lo h
  · exact coverage_114 lo h
  · exact coverage_115 lo h
  · exact coverage_116 lo h
  · exact coverage_117 lo h
  · exact coverage_118 lo h
  · exact coverage_119 lo h
  · exact coverage_120 lo h
  · exact coverage_121 lo h
  · exact coverage_122 lo h
  · exact coverage_123 lo h
  · exact coverage_124 lo h
  · exact coverage_125 lo h
  · exact coverage_126 lo h
  · exact coverage_127 lo h
  · exact coverage_128 lo h
  · exact coverage_129 lo h
  · exact coverage_130 lo h
  · exact coverage_131 lo h
  · exact coverage_132 lo h
  · exact coverage_133 lo h
  · exact coverage_134 lo h
  · exact coverage_135 lo h
  · exact coverage_136 lo h
  · exact coverage_137 lo h
  · exact coverage_138 lo h
  · exact coverage_139 lo h
  · exact coverage_140 lo h
  · exact coverage_141 lo h
  · exact coverage_142 lo h
  · exact coverage_143 lo h
  · exact coverage_144 lo h
  · exact coverage_145 lo h
  · exact coverage_146 lo h
  · exact coverage_147 lo h
  · exact coverage_148 lo h
  · exact coverage_149 lo h
  · exact coverage_150 lo h
  · exact coverage_151 lo h
  · exact coverage_152 lo h
  · exact coverage_153 lo h
  · exact coverage_154 lo h
  · exact coverage_155 lo h
  · exact coverage_156 lo h
  · exact coverage_157 lo h
  · exact coverage_158 lo h
  · exact coverage_159 lo h
  · exact coverage_160 lo h
  · exact coverage_161 lo h
  · exact coverage_162 lo h
  · exact coverage_163 lo h
  · exact coverage_164 lo h
  · exact coverage_165 lo h
  · exact coverage_166 lo h
  · exact coverage_167 lo h
  · exact coverage_168 lo h
  · exact coverage_169 lo h
  · exact coverage_170 lo h
  · exact coverage_171 lo h
  · exact coverage_172 lo h
  · exact coverage_173 lo h
  · exact coverage_174 lo h
  · exact coverage_175 lo h
  · exact coverage_176 lo h
  · exact coverage_177 lo h
  · exact coverage_178 lo h
  · exact coverage_179 lo h
  · exact coverage_180 lo h
  · exact coverage_181 lo h
  · exact coverage_182 lo h
  · exact coverage_183 lo h
  · exact coverage_184 lo h
  · exact coverage_185 lo h
  · exact coverage_186 lo h
  · exact coverage_187 lo h
  · exact coverage_188 lo h
  · exact coverage_189 lo h
  · exact coverage_190 lo h
  · exact coverage_191 lo h
  · exact coverage_192 lo h
  · exact coverage_193 lo h
  · exact coverage_194 lo h
  · exact coverage_195 lo h
  · exact coverage_196 lo h
  · exact coverage_197 lo h
  · exact coverage_198 lo h
  · exact coverage_199 lo h
  · exact coverage_200 lo h
  · exact coverage_201 lo h
  · exact coverage_202 lo h
  · exact coverage_203 lo h
  · exact coverage_204 lo h
  · exact coverage_205 lo h
  · exact coverage_206 lo h
  · exact coverage_207 lo h
  · exact coverage_208 lo h
  · exact coverage_209 lo h
  · exact coverage_210 lo h
  · exact coverage_211 lo h
  · exact coverage_212 lo h
  · exact coverage_213 lo h
  · exact coverage_214 lo h
  · exact coverage_215 lo h
  · exact coverage_216 lo h
  · exact coverage_217 lo h
  · exact coverage_218 lo h
  · exact coverage_219 lo h
  · exact coverage_220 lo h
  · exact coverage_221 lo h
  · exact coverage_222 lo h
  · exact coverage_223 lo h
  · exact coverage_224 lo h
  · exact coverage_225 lo h
  · exact coverage_226 lo h
  · exact coverage_227 lo h
  · exact coverage_228 lo h
  · exact coverage_229 lo h
  · exact coverage_230 lo h
  · exact coverage_231 lo h
  · exact coverage_232 lo h
  · exact coverage_233 lo h
  · exact coverage_234 lo h
  · exact coverage_235 lo h
  · exact coverage_236 lo h
  · exact coverage_237 lo h
  · exact coverage_238 lo h
  · exact coverage_239 lo h
  · exact coverage_240 lo h
  · exact coverage_241 lo h
  · exact coverage_242 lo h
  · exact coverage_243 lo h
  · exact coverage_244 lo h
  · exact coverage_245 lo h
  · exact coverage_246 lo h
  · exact coverage_247 lo h
  · exact coverage_248 lo h
  · exact coverage_249 lo h
  · exact coverage_250 lo h
  · exact coverage_251 lo h
  · exact coverage_252 lo h
  · exact coverage_253 lo h
  · exact coverage_254 lo h
  · exact coverage_255 lo h

theorem coverage (m : Fin 65536) (h : 13 ≤ weightedCount m.val) : covered m.val = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at h ⊢
  exact coverage_rows hi lo h

end Erdos577.Unattached.D0
