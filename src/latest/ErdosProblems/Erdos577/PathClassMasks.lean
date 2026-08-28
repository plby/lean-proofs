import ErdosProblems.Erdos577.PathClassModel

/-! Kernel-checked positive coverage or exact residual masks for Wang 3.5. -/

namespace Erdos577.PathClass

def masks : List ℕ := [
  4118, 4122, 4124, 4680, 4740, 5160, 5250, 6180,
  6210, 8229, 8233, 8236, 8520, 8580, 9240, 9345,
  10260, 10305, 13316, 14344, 16451, 16457, 16458, 16680,
  16770, 16920, 17025, 18450, 18465, 20994, 22536, 24833,
  26632, 32899, 32901, 32902, 33060, 33090, 33300, 33345,
  33810, 33825, 37378, 37892, 41217, 41988, 49409, 49666,
  286, 557, 1099, 1928, 2183, 2884, 3362, 3601,
  4366, 4576, 8717, 8912, 17419, 17584, 28808, 30848,
  34823, 34928, 45124, 46144, 53282, 53792, 57361, 57616,
  828, 972, 1370, 1450, 1641, 1689, 2406, 2454,
  2645, 2725, 3123, 3267, 4454, 4522, 4556, 8789,
  8857, 8908, 12492, 13068, 13124, 13192, 13248, 15552,
  17459, 17561, 17578, 20650, 21770, 21794, 21896, 21920,
  23200, 24729, 26121, 26129, 26248, 26256, 27024, 34867,
  34901, 34918, 36966, 38496, 39174, 39202, 39236, 39264,
  41045, 42320, 43525, 43537, 43588, 43600, 49203, 49968,
  52227, 52241, 52258, 52272]

def residualMasks : List ℕ := [
  1015, 1019, 1527, 1533, 1783, 1790, 1911, 1975,
  2007, 2023, 2035, 2037, 2038, 2039, 2555, 2557,
  2811, 2814, 2939, 3003, 3035, 3051, 3059, 3065,
  3066, 3067, 3325, 3326, 3453, 3517, 3549, 3565,
  3573, 3577, 3580, 3581, 3710, 3774, 3806, 3822,
  3830, 3834, 3836, 3838, 6003, 6005, 7091, 7097,
  7637, 7641, 10099, 10102, 11187, 11194, 12006, 12010,
  13171, 13235, 13683, 13939, 14131, 14163, 14179, 14193,
  14194, 14195, 14771, 15027, 15155, 15251, 15267, 15281,
  15282, 15283, 16240, 16304, 18293, 18294, 19925, 19932,
  20198, 20204, 21365, 21877, 21973, 22133, 22325, 22357,
  22373, 22385, 22388, 22389, 22997, 23765, 23893, 23957,
  24005, 24017, 24020, 24021, 24432, 24528, 25462, 25974,
  26230, 26342, 26422, 26454, 26470, 26482, 26484, 26486,
  27366, 27878, 28262, 28326, 28358, 28386, 28388, 28390,
  28528, 28640, 30576, 31600, 32112, 32368, 32560, 32592,
  32608, 32624, 35769, 35770, 36313, 36316, 36586, 36588,
  37817, 38361, 39353, 39385, 39609, 39737, 39833, 39849,
  39857, 39864, 39865, 40153, 40281, 40345, 40393, 40401,
  40408, 40409, 40880, 40912, 41914, 42730, 43450, 43706,
  43754, 43834, 43930, 43946, 43954, 43960, 43962, 44266,
  44650, 44714, 44746, 44770, 44776, 44778, 44976, 45024,
  47024, 48048, 48560, 48816, 48944, 49040, 49056, 49072,
  50652, 50924, 51676, 51948, 52444, 52460, 52572, 52636,
  52684, 52692, 52696, 52700, 52844, 52908, 52940, 52964,
  52968, 52972, 53200, 53216, 55248, 56272, 56784, 57040,
  57168, 57232, 57280, 57296, 59360, 60384, 60896, 61152,
  61280, 61344, 61376, 61408]

def covered (m : ℕ) : Bool := masks.any fun w ↦ m &&& w == w

def exceptional (m : ℕ) : Bool := residualMasks.contains m

private theorem coverage_0 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (0 * 256 + lo.val) →
    (covered (0 * 256 + lo.val) || exceptional (0 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_1 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (1 * 256 + lo.val) →
    (covered (1 * 256 + lo.val) || exceptional (1 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_2 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (2 * 256 + lo.val) →
    (covered (2 * 256 + lo.val) || exceptional (2 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_3 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (3 * 256 + lo.val) →
    (covered (3 * 256 + lo.val) || exceptional (3 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_4 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (4 * 256 + lo.val) →
    (covered (4 * 256 + lo.val) || exceptional (4 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_5 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (5 * 256 + lo.val) →
    (covered (5 * 256 + lo.val) || exceptional (5 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_6 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (6 * 256 + lo.val) →
    (covered (6 * 256 + lo.val) || exceptional (6 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_7 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (7 * 256 + lo.val) →
    (covered (7 * 256 + lo.val) || exceptional (7 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_8 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (8 * 256 + lo.val) →
    (covered (8 * 256 + lo.val) || exceptional (8 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_9 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (9 * 256 + lo.val) →
    (covered (9 * 256 + lo.val) || exceptional (9 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_10 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (10 * 256 + lo.val) →
    (covered (10 * 256 + lo.val) || exceptional (10 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_11 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (11 * 256 + lo.val) →
    (covered (11 * 256 + lo.val) || exceptional (11 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_12 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (12 * 256 + lo.val) →
    (covered (12 * 256 + lo.val) || exceptional (12 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_13 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (13 * 256 + lo.val) →
    (covered (13 * 256 + lo.val) || exceptional (13 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_14 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (14 * 256 + lo.val) →
    (covered (14 * 256 + lo.val) || exceptional (14 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_15 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (15 * 256 + lo.val) →
    (covered (15 * 256 + lo.val) || exceptional (15 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_16 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (16 * 256 + lo.val) →
    (covered (16 * 256 + lo.val) || exceptional (16 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_17 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (17 * 256 + lo.val) →
    (covered (17 * 256 + lo.val) || exceptional (17 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_18 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (18 * 256 + lo.val) →
    (covered (18 * 256 + lo.val) || exceptional (18 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_19 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (19 * 256 + lo.val) →
    (covered (19 * 256 + lo.val) || exceptional (19 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_20 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (20 * 256 + lo.val) →
    (covered (20 * 256 + lo.val) || exceptional (20 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_21 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (21 * 256 + lo.val) →
    (covered (21 * 256 + lo.val) || exceptional (21 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_22 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (22 * 256 + lo.val) →
    (covered (22 * 256 + lo.val) || exceptional (22 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_23 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (23 * 256 + lo.val) →
    (covered (23 * 256 + lo.val) || exceptional (23 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_24 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (24 * 256 + lo.val) →
    (covered (24 * 256 + lo.val) || exceptional (24 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_25 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (25 * 256 + lo.val) →
    (covered (25 * 256 + lo.val) || exceptional (25 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_26 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (26 * 256 + lo.val) →
    (covered (26 * 256 + lo.val) || exceptional (26 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_27 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (27 * 256 + lo.val) →
    (covered (27 * 256 + lo.val) || exceptional (27 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_28 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (28 * 256 + lo.val) →
    (covered (28 * 256 + lo.val) || exceptional (28 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_29 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (29 * 256 + lo.val) →
    (covered (29 * 256 + lo.val) || exceptional (29 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_30 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (30 * 256 + lo.val) →
    (covered (30 * 256 + lo.val) || exceptional (30 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_31 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (31 * 256 + lo.val) →
    (covered (31 * 256 + lo.val) || exceptional (31 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_32 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (32 * 256 + lo.val) →
    (covered (32 * 256 + lo.val) || exceptional (32 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_33 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (33 * 256 + lo.val) →
    (covered (33 * 256 + lo.val) || exceptional (33 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_34 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (34 * 256 + lo.val) →
    (covered (34 * 256 + lo.val) || exceptional (34 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_35 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (35 * 256 + lo.val) →
    (covered (35 * 256 + lo.val) || exceptional (35 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_36 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (36 * 256 + lo.val) →
    (covered (36 * 256 + lo.val) || exceptional (36 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_37 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (37 * 256 + lo.val) →
    (covered (37 * 256 + lo.val) || exceptional (37 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_38 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (38 * 256 + lo.val) →
    (covered (38 * 256 + lo.val) || exceptional (38 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_39 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (39 * 256 + lo.val) →
    (covered (39 * 256 + lo.val) || exceptional (39 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_40 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (40 * 256 + lo.val) →
    (covered (40 * 256 + lo.val) || exceptional (40 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_41 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (41 * 256 + lo.val) →
    (covered (41 * 256 + lo.val) || exceptional (41 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_42 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (42 * 256 + lo.val) →
    (covered (42 * 256 + lo.val) || exceptional (42 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_43 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (43 * 256 + lo.val) →
    (covered (43 * 256 + lo.val) || exceptional (43 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_44 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (44 * 256 + lo.val) →
    (covered (44 * 256 + lo.val) || exceptional (44 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_45 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (45 * 256 + lo.val) →
    (covered (45 * 256 + lo.val) || exceptional (45 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_46 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (46 * 256 + lo.val) →
    (covered (46 * 256 + lo.val) || exceptional (46 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_47 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (47 * 256 + lo.val) →
    (covered (47 * 256 + lo.val) || exceptional (47 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_48 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (48 * 256 + lo.val) →
    (covered (48 * 256 + lo.val) || exceptional (48 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_49 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (49 * 256 + lo.val) →
    (covered (49 * 256 + lo.val) || exceptional (49 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_50 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (50 * 256 + lo.val) →
    (covered (50 * 256 + lo.val) || exceptional (50 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_51 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (51 * 256 + lo.val) →
    (covered (51 * 256 + lo.val) || exceptional (51 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_52 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (52 * 256 + lo.val) →
    (covered (52 * 256 + lo.val) || exceptional (52 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_53 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (53 * 256 + lo.val) →
    (covered (53 * 256 + lo.val) || exceptional (53 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_54 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (54 * 256 + lo.val) →
    (covered (54 * 256 + lo.val) || exceptional (54 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_55 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (55 * 256 + lo.val) →
    (covered (55 * 256 + lo.val) || exceptional (55 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_56 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (56 * 256 + lo.val) →
    (covered (56 * 256 + lo.val) || exceptional (56 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_57 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (57 * 256 + lo.val) →
    (covered (57 * 256 + lo.val) || exceptional (57 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_58 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (58 * 256 + lo.val) →
    (covered (58 * 256 + lo.val) || exceptional (58 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_59 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (59 * 256 + lo.val) →
    (covered (59 * 256 + lo.val) || exceptional (59 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_60 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (60 * 256 + lo.val) →
    (covered (60 * 256 + lo.val) || exceptional (60 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_61 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (61 * 256 + lo.val) →
    (covered (61 * 256 + lo.val) || exceptional (61 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_62 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (62 * 256 + lo.val) →
    (covered (62 * 256 + lo.val) || exceptional (62 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_63 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (63 * 256 + lo.val) →
    (covered (63 * 256 + lo.val) || exceptional (63 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_64 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (64 * 256 + lo.val) →
    (covered (64 * 256 + lo.val) || exceptional (64 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_65 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (65 * 256 + lo.val) →
    (covered (65 * 256 + lo.val) || exceptional (65 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_66 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (66 * 256 + lo.val) →
    (covered (66 * 256 + lo.val) || exceptional (66 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_67 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (67 * 256 + lo.val) →
    (covered (67 * 256 + lo.val) || exceptional (67 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_68 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (68 * 256 + lo.val) →
    (covered (68 * 256 + lo.val) || exceptional (68 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_69 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (69 * 256 + lo.val) →
    (covered (69 * 256 + lo.val) || exceptional (69 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_70 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (70 * 256 + lo.val) →
    (covered (70 * 256 + lo.val) || exceptional (70 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_71 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (71 * 256 + lo.val) →
    (covered (71 * 256 + lo.val) || exceptional (71 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_72 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (72 * 256 + lo.val) →
    (covered (72 * 256 + lo.val) || exceptional (72 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_73 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (73 * 256 + lo.val) →
    (covered (73 * 256 + lo.val) || exceptional (73 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_74 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (74 * 256 + lo.val) →
    (covered (74 * 256 + lo.val) || exceptional (74 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_75 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (75 * 256 + lo.val) →
    (covered (75 * 256 + lo.val) || exceptional (75 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_76 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (76 * 256 + lo.val) →
    (covered (76 * 256 + lo.val) || exceptional (76 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_77 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (77 * 256 + lo.val) →
    (covered (77 * 256 + lo.val) || exceptional (77 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_78 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (78 * 256 + lo.val) →
    (covered (78 * 256 + lo.val) || exceptional (78 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_79 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (79 * 256 + lo.val) →
    (covered (79 * 256 + lo.val) || exceptional (79 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_80 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (80 * 256 + lo.val) →
    (covered (80 * 256 + lo.val) || exceptional (80 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_81 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (81 * 256 + lo.val) →
    (covered (81 * 256 + lo.val) || exceptional (81 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_82 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (82 * 256 + lo.val) →
    (covered (82 * 256 + lo.val) || exceptional (82 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_83 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (83 * 256 + lo.val) →
    (covered (83 * 256 + lo.val) || exceptional (83 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_84 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (84 * 256 + lo.val) →
    (covered (84 * 256 + lo.val) || exceptional (84 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_85 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (85 * 256 + lo.val) →
    (covered (85 * 256 + lo.val) || exceptional (85 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_86 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (86 * 256 + lo.val) →
    (covered (86 * 256 + lo.val) || exceptional (86 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_87 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (87 * 256 + lo.val) →
    (covered (87 * 256 + lo.val) || exceptional (87 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_88 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (88 * 256 + lo.val) →
    (covered (88 * 256 + lo.val) || exceptional (88 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_89 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (89 * 256 + lo.val) →
    (covered (89 * 256 + lo.val) || exceptional (89 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_90 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (90 * 256 + lo.val) →
    (covered (90 * 256 + lo.val) || exceptional (90 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_91 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (91 * 256 + lo.val) →
    (covered (91 * 256 + lo.val) || exceptional (91 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_92 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (92 * 256 + lo.val) →
    (covered (92 * 256 + lo.val) || exceptional (92 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_93 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (93 * 256 + lo.val) →
    (covered (93 * 256 + lo.val) || exceptional (93 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_94 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (94 * 256 + lo.val) →
    (covered (94 * 256 + lo.val) || exceptional (94 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_95 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (95 * 256 + lo.val) →
    (covered (95 * 256 + lo.val) || exceptional (95 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_96 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (96 * 256 + lo.val) →
    (covered (96 * 256 + lo.val) || exceptional (96 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_97 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (97 * 256 + lo.val) →
    (covered (97 * 256 + lo.val) || exceptional (97 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_98 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (98 * 256 + lo.val) →
    (covered (98 * 256 + lo.val) || exceptional (98 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_99 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (99 * 256 + lo.val) →
    (covered (99 * 256 + lo.val) || exceptional (99 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_100 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (100 * 256 + lo.val) →
    (covered (100 * 256 + lo.val) || exceptional (100 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_101 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (101 * 256 + lo.val) →
    (covered (101 * 256 + lo.val) || exceptional (101 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_102 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (102 * 256 + lo.val) →
    (covered (102 * 256 + lo.val) || exceptional (102 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_103 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (103 * 256 + lo.val) →
    (covered (103 * 256 + lo.val) || exceptional (103 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_104 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (104 * 256 + lo.val) →
    (covered (104 * 256 + lo.val) || exceptional (104 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_105 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (105 * 256 + lo.val) →
    (covered (105 * 256 + lo.val) || exceptional (105 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_106 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (106 * 256 + lo.val) →
    (covered (106 * 256 + lo.val) || exceptional (106 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_107 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (107 * 256 + lo.val) →
    (covered (107 * 256 + lo.val) || exceptional (107 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_108 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (108 * 256 + lo.val) →
    (covered (108 * 256 + lo.val) || exceptional (108 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_109 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (109 * 256 + lo.val) →
    (covered (109 * 256 + lo.val) || exceptional (109 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_110 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (110 * 256 + lo.val) →
    (covered (110 * 256 + lo.val) || exceptional (110 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_111 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (111 * 256 + lo.val) →
    (covered (111 * 256 + lo.val) || exceptional (111 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_112 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (112 * 256 + lo.val) →
    (covered (112 * 256 + lo.val) || exceptional (112 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_113 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (113 * 256 + lo.val) →
    (covered (113 * 256 + lo.val) || exceptional (113 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_114 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (114 * 256 + lo.val) →
    (covered (114 * 256 + lo.val) || exceptional (114 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_115 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (115 * 256 + lo.val) →
    (covered (115 * 256 + lo.val) || exceptional (115 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_116 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (116 * 256 + lo.val) →
    (covered (116 * 256 + lo.val) || exceptional (116 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_117 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (117 * 256 + lo.val) →
    (covered (117 * 256 + lo.val) || exceptional (117 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_118 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (118 * 256 + lo.val) →
    (covered (118 * 256 + lo.val) || exceptional (118 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_119 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (119 * 256 + lo.val) →
    (covered (119 * 256 + lo.val) || exceptional (119 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_120 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (120 * 256 + lo.val) →
    (covered (120 * 256 + lo.val) || exceptional (120 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_121 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (121 * 256 + lo.val) →
    (covered (121 * 256 + lo.val) || exceptional (121 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_122 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (122 * 256 + lo.val) →
    (covered (122 * 256 + lo.val) || exceptional (122 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_123 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (123 * 256 + lo.val) →
    (covered (123 * 256 + lo.val) || exceptional (123 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_124 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (124 * 256 + lo.val) →
    (covered (124 * 256 + lo.val) || exceptional (124 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_125 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (125 * 256 + lo.val) →
    (covered (125 * 256 + lo.val) || exceptional (125 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_126 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (126 * 256 + lo.val) →
    (covered (126 * 256 + lo.val) || exceptional (126 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_127 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (127 * 256 + lo.val) →
    (covered (127 * 256 + lo.val) || exceptional (127 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_128 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (128 * 256 + lo.val) →
    (covered (128 * 256 + lo.val) || exceptional (128 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_129 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (129 * 256 + lo.val) →
    (covered (129 * 256 + lo.val) || exceptional (129 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_130 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (130 * 256 + lo.val) →
    (covered (130 * 256 + lo.val) || exceptional (130 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_131 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (131 * 256 + lo.val) →
    (covered (131 * 256 + lo.val) || exceptional (131 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_132 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (132 * 256 + lo.val) →
    (covered (132 * 256 + lo.val) || exceptional (132 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_133 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (133 * 256 + lo.val) →
    (covered (133 * 256 + lo.val) || exceptional (133 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_134 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (134 * 256 + lo.val) →
    (covered (134 * 256 + lo.val) || exceptional (134 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_135 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (135 * 256 + lo.val) →
    (covered (135 * 256 + lo.val) || exceptional (135 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_136 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (136 * 256 + lo.val) →
    (covered (136 * 256 + lo.val) || exceptional (136 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_137 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (137 * 256 + lo.val) →
    (covered (137 * 256 + lo.val) || exceptional (137 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_138 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (138 * 256 + lo.val) →
    (covered (138 * 256 + lo.val) || exceptional (138 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_139 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (139 * 256 + lo.val) →
    (covered (139 * 256 + lo.val) || exceptional (139 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_140 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (140 * 256 + lo.val) →
    (covered (140 * 256 + lo.val) || exceptional (140 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_141 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (141 * 256 + lo.val) →
    (covered (141 * 256 + lo.val) || exceptional (141 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_142 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (142 * 256 + lo.val) →
    (covered (142 * 256 + lo.val) || exceptional (142 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_143 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (143 * 256 + lo.val) →
    (covered (143 * 256 + lo.val) || exceptional (143 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_144 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (144 * 256 + lo.val) →
    (covered (144 * 256 + lo.val) || exceptional (144 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_145 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (145 * 256 + lo.val) →
    (covered (145 * 256 + lo.val) || exceptional (145 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_146 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (146 * 256 + lo.val) →
    (covered (146 * 256 + lo.val) || exceptional (146 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_147 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (147 * 256 + lo.val) →
    (covered (147 * 256 + lo.val) || exceptional (147 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_148 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (148 * 256 + lo.val) →
    (covered (148 * 256 + lo.val) || exceptional (148 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_149 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (149 * 256 + lo.val) →
    (covered (149 * 256 + lo.val) || exceptional (149 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_150 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (150 * 256 + lo.val) →
    (covered (150 * 256 + lo.val) || exceptional (150 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_151 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (151 * 256 + lo.val) →
    (covered (151 * 256 + lo.val) || exceptional (151 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_152 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (152 * 256 + lo.val) →
    (covered (152 * 256 + lo.val) || exceptional (152 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_153 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (153 * 256 + lo.val) →
    (covered (153 * 256 + lo.val) || exceptional (153 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_154 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (154 * 256 + lo.val) →
    (covered (154 * 256 + lo.val) || exceptional (154 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_155 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (155 * 256 + lo.val) →
    (covered (155 * 256 + lo.val) || exceptional (155 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_156 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (156 * 256 + lo.val) →
    (covered (156 * 256 + lo.val) || exceptional (156 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_157 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (157 * 256 + lo.val) →
    (covered (157 * 256 + lo.val) || exceptional (157 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_158 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (158 * 256 + lo.val) →
    (covered (158 * 256 + lo.val) || exceptional (158 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_159 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (159 * 256 + lo.val) →
    (covered (159 * 256 + lo.val) || exceptional (159 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_160 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (160 * 256 + lo.val) →
    (covered (160 * 256 + lo.val) || exceptional (160 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_161 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (161 * 256 + lo.val) →
    (covered (161 * 256 + lo.val) || exceptional (161 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_162 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (162 * 256 + lo.val) →
    (covered (162 * 256 + lo.val) || exceptional (162 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_163 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (163 * 256 + lo.val) →
    (covered (163 * 256 + lo.val) || exceptional (163 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_164 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (164 * 256 + lo.val) →
    (covered (164 * 256 + lo.val) || exceptional (164 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_165 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (165 * 256 + lo.val) →
    (covered (165 * 256 + lo.val) || exceptional (165 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_166 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (166 * 256 + lo.val) →
    (covered (166 * 256 + lo.val) || exceptional (166 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_167 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (167 * 256 + lo.val) →
    (covered (167 * 256 + lo.val) || exceptional (167 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_168 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (168 * 256 + lo.val) →
    (covered (168 * 256 + lo.val) || exceptional (168 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_169 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (169 * 256 + lo.val) →
    (covered (169 * 256 + lo.val) || exceptional (169 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_170 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (170 * 256 + lo.val) →
    (covered (170 * 256 + lo.val) || exceptional (170 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_171 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (171 * 256 + lo.val) →
    (covered (171 * 256 + lo.val) || exceptional (171 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_172 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (172 * 256 + lo.val) →
    (covered (172 * 256 + lo.val) || exceptional (172 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_173 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (173 * 256 + lo.val) →
    (covered (173 * 256 + lo.val) || exceptional (173 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_174 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (174 * 256 + lo.val) →
    (covered (174 * 256 + lo.val) || exceptional (174 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_175 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (175 * 256 + lo.val) →
    (covered (175 * 256 + lo.val) || exceptional (175 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_176 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (176 * 256 + lo.val) →
    (covered (176 * 256 + lo.val) || exceptional (176 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_177 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (177 * 256 + lo.val) →
    (covered (177 * 256 + lo.val) || exceptional (177 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_178 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (178 * 256 + lo.val) →
    (covered (178 * 256 + lo.val) || exceptional (178 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_179 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (179 * 256 + lo.val) →
    (covered (179 * 256 + lo.val) || exceptional (179 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_180 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (180 * 256 + lo.val) →
    (covered (180 * 256 + lo.val) || exceptional (180 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_181 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (181 * 256 + lo.val) →
    (covered (181 * 256 + lo.val) || exceptional (181 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_182 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (182 * 256 + lo.val) →
    (covered (182 * 256 + lo.val) || exceptional (182 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_183 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (183 * 256 + lo.val) →
    (covered (183 * 256 + lo.val) || exceptional (183 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_184 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (184 * 256 + lo.val) →
    (covered (184 * 256 + lo.val) || exceptional (184 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_185 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (185 * 256 + lo.val) →
    (covered (185 * 256 + lo.val) || exceptional (185 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_186 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (186 * 256 + lo.val) →
    (covered (186 * 256 + lo.val) || exceptional (186 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_187 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (187 * 256 + lo.val) →
    (covered (187 * 256 + lo.val) || exceptional (187 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_188 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (188 * 256 + lo.val) →
    (covered (188 * 256 + lo.val) || exceptional (188 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_189 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (189 * 256 + lo.val) →
    (covered (189 * 256 + lo.val) || exceptional (189 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_190 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (190 * 256 + lo.val) →
    (covered (190 * 256 + lo.val) || exceptional (190 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_191 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (191 * 256 + lo.val) →
    (covered (191 * 256 + lo.val) || exceptional (191 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_192 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (192 * 256 + lo.val) →
    (covered (192 * 256 + lo.val) || exceptional (192 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_193 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (193 * 256 + lo.val) →
    (covered (193 * 256 + lo.val) || exceptional (193 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_194 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (194 * 256 + lo.val) →
    (covered (194 * 256 + lo.val) || exceptional (194 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_195 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (195 * 256 + lo.val) →
    (covered (195 * 256 + lo.val) || exceptional (195 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_196 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (196 * 256 + lo.val) →
    (covered (196 * 256 + lo.val) || exceptional (196 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_197 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (197 * 256 + lo.val) →
    (covered (197 * 256 + lo.val) || exceptional (197 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_198 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (198 * 256 + lo.val) →
    (covered (198 * 256 + lo.val) || exceptional (198 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_199 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (199 * 256 + lo.val) →
    (covered (199 * 256 + lo.val) || exceptional (199 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_200 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (200 * 256 + lo.val) →
    (covered (200 * 256 + lo.val) || exceptional (200 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_201 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (201 * 256 + lo.val) →
    (covered (201 * 256 + lo.val) || exceptional (201 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_202 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (202 * 256 + lo.val) →
    (covered (202 * 256 + lo.val) || exceptional (202 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_203 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (203 * 256 + lo.val) →
    (covered (203 * 256 + lo.val) || exceptional (203 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_204 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (204 * 256 + lo.val) →
    (covered (204 * 256 + lo.val) || exceptional (204 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_205 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (205 * 256 + lo.val) →
    (covered (205 * 256 + lo.val) || exceptional (205 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_206 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (206 * 256 + lo.val) →
    (covered (206 * 256 + lo.val) || exceptional (206 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_207 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (207 * 256 + lo.val) →
    (covered (207 * 256 + lo.val) || exceptional (207 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_208 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (208 * 256 + lo.val) →
    (covered (208 * 256 + lo.val) || exceptional (208 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_209 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (209 * 256 + lo.val) →
    (covered (209 * 256 + lo.val) || exceptional (209 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_210 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (210 * 256 + lo.val) →
    (covered (210 * 256 + lo.val) || exceptional (210 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_211 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (211 * 256 + lo.val) →
    (covered (211 * 256 + lo.val) || exceptional (211 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_212 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (212 * 256 + lo.val) →
    (covered (212 * 256 + lo.val) || exceptional (212 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_213 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (213 * 256 + lo.val) →
    (covered (213 * 256 + lo.val) || exceptional (213 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_214 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (214 * 256 + lo.val) →
    (covered (214 * 256 + lo.val) || exceptional (214 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_215 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (215 * 256 + lo.val) →
    (covered (215 * 256 + lo.val) || exceptional (215 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_216 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (216 * 256 + lo.val) →
    (covered (216 * 256 + lo.val) || exceptional (216 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_217 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (217 * 256 + lo.val) →
    (covered (217 * 256 + lo.val) || exceptional (217 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_218 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (218 * 256 + lo.val) →
    (covered (218 * 256 + lo.val) || exceptional (218 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_219 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (219 * 256 + lo.val) →
    (covered (219 * 256 + lo.val) || exceptional (219 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_220 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (220 * 256 + lo.val) →
    (covered (220 * 256 + lo.val) || exceptional (220 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_221 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (221 * 256 + lo.val) →
    (covered (221 * 256 + lo.val) || exceptional (221 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_222 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (222 * 256 + lo.val) →
    (covered (222 * 256 + lo.val) || exceptional (222 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_223 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (223 * 256 + lo.val) →
    (covered (223 * 256 + lo.val) || exceptional (223 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_224 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (224 * 256 + lo.val) →
    (covered (224 * 256 + lo.val) || exceptional (224 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_225 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (225 * 256 + lo.val) →
    (covered (225 * 256 + lo.val) || exceptional (225 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_226 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (226 * 256 + lo.val) →
    (covered (226 * 256 + lo.val) || exceptional (226 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_227 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (227 * 256 + lo.val) →
    (covered (227 * 256 + lo.val) || exceptional (227 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_228 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (228 * 256 + lo.val) →
    (covered (228 * 256 + lo.val) || exceptional (228 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_229 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (229 * 256 + lo.val) →
    (covered (229 * 256 + lo.val) || exceptional (229 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_230 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (230 * 256 + lo.val) →
    (covered (230 * 256 + lo.val) || exceptional (230 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_231 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (231 * 256 + lo.val) →
    (covered (231 * 256 + lo.val) || exceptional (231 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_232 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (232 * 256 + lo.val) →
    (covered (232 * 256 + lo.val) || exceptional (232 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_233 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (233 * 256 + lo.val) →
    (covered (233 * 256 + lo.val) || exceptional (233 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_234 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (234 * 256 + lo.val) →
    (covered (234 * 256 + lo.val) || exceptional (234 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_235 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (235 * 256 + lo.val) →
    (covered (235 * 256 + lo.val) || exceptional (235 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_236 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (236 * 256 + lo.val) →
    (covered (236 * 256 + lo.val) || exceptional (236 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_237 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (237 * 256 + lo.val) →
    (covered (237 * 256 + lo.val) || exceptional (237 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_238 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (238 * 256 + lo.val) →
    (covered (238 * 256 + lo.val) || exceptional (238 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_239 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (239 * 256 + lo.val) →
    (covered (239 * 256 + lo.val) || exceptional (239 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_240 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (240 * 256 + lo.val) →
    (covered (240 * 256 + lo.val) || exceptional (240 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_241 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (241 * 256 + lo.val) →
    (covered (241 * 256 + lo.val) || exceptional (241 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_242 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (242 * 256 + lo.val) →
    (covered (242 * 256 + lo.val) || exceptional (242 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_243 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (243 * 256 + lo.val) →
    (covered (243 * 256 + lo.val) || exceptional (243 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_244 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (244 * 256 + lo.val) →
    (covered (244 * 256 + lo.val) || exceptional (244 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_245 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (245 * 256 + lo.val) →
    (covered (245 * 256 + lo.val) || exceptional (245 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_246 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (246 * 256 + lo.val) →
    (covered (246 * 256 + lo.val) || exceptional (246 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_247 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (247 * 256 + lo.val) →
    (covered (247 * 256 + lo.val) || exceptional (247 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_248 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (248 * 256 + lo.val) →
    (covered (248 * 256 + lo.val) || exceptional (248 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_249 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (249 * 256 + lo.val) →
    (covered (249 * 256 + lo.val) || exceptional (249 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_250 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (250 * 256 + lo.val) →
    (covered (250 * 256 + lo.val) || exceptional (250 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_251 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (251 * 256 + lo.val) →
    (covered (251 * 256 + lo.val) || exceptional (251 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_252 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (252 * 256 + lo.val) →
    (covered (252 * 256 + lo.val) || exceptional (252 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_253 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (253 * 256 + lo.val) →
    (covered (253 * 256 + lo.val) || exceptional (253 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_254 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (254 * 256 + lo.val) →
    (covered (254 * 256 + lo.val) || exceptional (254 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_255 : ∀ lo : Fin 256,
    9 ≤ PathExchange.crossCount (255 * 256 + lo.val) →
    (covered (255 * 256 + lo.val) || exceptional (255 * 256 + lo.val)) = true := by
  decide +kernel

private theorem coverage_rows (hi lo : Fin 256)
    (hh : 9 ≤ PathExchange.crossCount (hi.val * 256 + lo.val)) :
    (covered (hi.val * 256 + lo.val) || exceptional (hi.val * 256 + lo.val)) = true := by
  fin_cases hi
  · exact coverage_0 lo hh
  · exact coverage_1 lo hh
  · exact coverage_2 lo hh
  · exact coverage_3 lo hh
  · exact coverage_4 lo hh
  · exact coverage_5 lo hh
  · exact coverage_6 lo hh
  · exact coverage_7 lo hh
  · exact coverage_8 lo hh
  · exact coverage_9 lo hh
  · exact coverage_10 lo hh
  · exact coverage_11 lo hh
  · exact coverage_12 lo hh
  · exact coverage_13 lo hh
  · exact coverage_14 lo hh
  · exact coverage_15 lo hh
  · exact coverage_16 lo hh
  · exact coverage_17 lo hh
  · exact coverage_18 lo hh
  · exact coverage_19 lo hh
  · exact coverage_20 lo hh
  · exact coverage_21 lo hh
  · exact coverage_22 lo hh
  · exact coverage_23 lo hh
  · exact coverage_24 lo hh
  · exact coverage_25 lo hh
  · exact coverage_26 lo hh
  · exact coverage_27 lo hh
  · exact coverage_28 lo hh
  · exact coverage_29 lo hh
  · exact coverage_30 lo hh
  · exact coverage_31 lo hh
  · exact coverage_32 lo hh
  · exact coverage_33 lo hh
  · exact coverage_34 lo hh
  · exact coverage_35 lo hh
  · exact coverage_36 lo hh
  · exact coverage_37 lo hh
  · exact coverage_38 lo hh
  · exact coverage_39 lo hh
  · exact coverage_40 lo hh
  · exact coverage_41 lo hh
  · exact coverage_42 lo hh
  · exact coverage_43 lo hh
  · exact coverage_44 lo hh
  · exact coverage_45 lo hh
  · exact coverage_46 lo hh
  · exact coverage_47 lo hh
  · exact coverage_48 lo hh
  · exact coverage_49 lo hh
  · exact coverage_50 lo hh
  · exact coverage_51 lo hh
  · exact coverage_52 lo hh
  · exact coverage_53 lo hh
  · exact coverage_54 lo hh
  · exact coverage_55 lo hh
  · exact coverage_56 lo hh
  · exact coverage_57 lo hh
  · exact coverage_58 lo hh
  · exact coverage_59 lo hh
  · exact coverage_60 lo hh
  · exact coverage_61 lo hh
  · exact coverage_62 lo hh
  · exact coverage_63 lo hh
  · exact coverage_64 lo hh
  · exact coverage_65 lo hh
  · exact coverage_66 lo hh
  · exact coverage_67 lo hh
  · exact coverage_68 lo hh
  · exact coverage_69 lo hh
  · exact coverage_70 lo hh
  · exact coverage_71 lo hh
  · exact coverage_72 lo hh
  · exact coverage_73 lo hh
  · exact coverage_74 lo hh
  · exact coverage_75 lo hh
  · exact coverage_76 lo hh
  · exact coverage_77 lo hh
  · exact coverage_78 lo hh
  · exact coverage_79 lo hh
  · exact coverage_80 lo hh
  · exact coverage_81 lo hh
  · exact coverage_82 lo hh
  · exact coverage_83 lo hh
  · exact coverage_84 lo hh
  · exact coverage_85 lo hh
  · exact coverage_86 lo hh
  · exact coverage_87 lo hh
  · exact coverage_88 lo hh
  · exact coverage_89 lo hh
  · exact coverage_90 lo hh
  · exact coverage_91 lo hh
  · exact coverage_92 lo hh
  · exact coverage_93 lo hh
  · exact coverage_94 lo hh
  · exact coverage_95 lo hh
  · exact coverage_96 lo hh
  · exact coverage_97 lo hh
  · exact coverage_98 lo hh
  · exact coverage_99 lo hh
  · exact coverage_100 lo hh
  · exact coverage_101 lo hh
  · exact coverage_102 lo hh
  · exact coverage_103 lo hh
  · exact coverage_104 lo hh
  · exact coverage_105 lo hh
  · exact coverage_106 lo hh
  · exact coverage_107 lo hh
  · exact coverage_108 lo hh
  · exact coverage_109 lo hh
  · exact coverage_110 lo hh
  · exact coverage_111 lo hh
  · exact coverage_112 lo hh
  · exact coverage_113 lo hh
  · exact coverage_114 lo hh
  · exact coverage_115 lo hh
  · exact coverage_116 lo hh
  · exact coverage_117 lo hh
  · exact coverage_118 lo hh
  · exact coverage_119 lo hh
  · exact coverage_120 lo hh
  · exact coverage_121 lo hh
  · exact coverage_122 lo hh
  · exact coverage_123 lo hh
  · exact coverage_124 lo hh
  · exact coverage_125 lo hh
  · exact coverage_126 lo hh
  · exact coverage_127 lo hh
  · exact coverage_128 lo hh
  · exact coverage_129 lo hh
  · exact coverage_130 lo hh
  · exact coverage_131 lo hh
  · exact coverage_132 lo hh
  · exact coverage_133 lo hh
  · exact coverage_134 lo hh
  · exact coverage_135 lo hh
  · exact coverage_136 lo hh
  · exact coverage_137 lo hh
  · exact coverage_138 lo hh
  · exact coverage_139 lo hh
  · exact coverage_140 lo hh
  · exact coverage_141 lo hh
  · exact coverage_142 lo hh
  · exact coverage_143 lo hh
  · exact coverage_144 lo hh
  · exact coverage_145 lo hh
  · exact coverage_146 lo hh
  · exact coverage_147 lo hh
  · exact coverage_148 lo hh
  · exact coverage_149 lo hh
  · exact coverage_150 lo hh
  · exact coverage_151 lo hh
  · exact coverage_152 lo hh
  · exact coverage_153 lo hh
  · exact coverage_154 lo hh
  · exact coverage_155 lo hh
  · exact coverage_156 lo hh
  · exact coverage_157 lo hh
  · exact coverage_158 lo hh
  · exact coverage_159 lo hh
  · exact coverage_160 lo hh
  · exact coverage_161 lo hh
  · exact coverage_162 lo hh
  · exact coverage_163 lo hh
  · exact coverage_164 lo hh
  · exact coverage_165 lo hh
  · exact coverage_166 lo hh
  · exact coverage_167 lo hh
  · exact coverage_168 lo hh
  · exact coverage_169 lo hh
  · exact coverage_170 lo hh
  · exact coverage_171 lo hh
  · exact coverage_172 lo hh
  · exact coverage_173 lo hh
  · exact coverage_174 lo hh
  · exact coverage_175 lo hh
  · exact coverage_176 lo hh
  · exact coverage_177 lo hh
  · exact coverage_178 lo hh
  · exact coverage_179 lo hh
  · exact coverage_180 lo hh
  · exact coverage_181 lo hh
  · exact coverage_182 lo hh
  · exact coverage_183 lo hh
  · exact coverage_184 lo hh
  · exact coverage_185 lo hh
  · exact coverage_186 lo hh
  · exact coverage_187 lo hh
  · exact coverage_188 lo hh
  · exact coverage_189 lo hh
  · exact coverage_190 lo hh
  · exact coverage_191 lo hh
  · exact coverage_192 lo hh
  · exact coverage_193 lo hh
  · exact coverage_194 lo hh
  · exact coverage_195 lo hh
  · exact coverage_196 lo hh
  · exact coverage_197 lo hh
  · exact coverage_198 lo hh
  · exact coverage_199 lo hh
  · exact coverage_200 lo hh
  · exact coverage_201 lo hh
  · exact coverage_202 lo hh
  · exact coverage_203 lo hh
  · exact coverage_204 lo hh
  · exact coverage_205 lo hh
  · exact coverage_206 lo hh
  · exact coverage_207 lo hh
  · exact coverage_208 lo hh
  · exact coverage_209 lo hh
  · exact coverage_210 lo hh
  · exact coverage_211 lo hh
  · exact coverage_212 lo hh
  · exact coverage_213 lo hh
  · exact coverage_214 lo hh
  · exact coverage_215 lo hh
  · exact coverage_216 lo hh
  · exact coverage_217 lo hh
  · exact coverage_218 lo hh
  · exact coverage_219 lo hh
  · exact coverage_220 lo hh
  · exact coverage_221 lo hh
  · exact coverage_222 lo hh
  · exact coverage_223 lo hh
  · exact coverage_224 lo hh
  · exact coverage_225 lo hh
  · exact coverage_226 lo hh
  · exact coverage_227 lo hh
  · exact coverage_228 lo hh
  · exact coverage_229 lo hh
  · exact coverage_230 lo hh
  · exact coverage_231 lo hh
  · exact coverage_232 lo hh
  · exact coverage_233 lo hh
  · exact coverage_234 lo hh
  · exact coverage_235 lo hh
  · exact coverage_236 lo hh
  · exact coverage_237 lo hh
  · exact coverage_238 lo hh
  · exact coverage_239 lo hh
  · exact coverage_240 lo hh
  · exact coverage_241 lo hh
  · exact coverage_242 lo hh
  · exact coverage_243 lo hh
  · exact coverage_244 lo hh
  · exact coverage_245 lo hh
  · exact coverage_246 lo hh
  · exact coverage_247 lo hh
  · exact coverage_248 lo hh
  · exact coverage_249 lo hh
  · exact coverage_250 lo hh
  · exact coverage_251 lo hh
  · exact coverage_252 lo hh
  · exact coverage_253 lo hh
  · exact coverage_254 lo hh
  · exact coverage_255 lo hh

theorem coverage (m : Fin 65536) (hh : 9 ≤ PathExchange.crossCount m.val) :
    (covered m.val || exceptional m.val) = true := by
  let hi : Fin 256 := ⟨m.val / 256, by omega⟩
  let lo : Fin 256 := ⟨m.val % 256, Nat.mod_lt _ (by decide)⟩
  have he : hi.val * 256 + lo.val = m.val := by dsimp [hi, lo]; omega
  rw [← he] at hh ⊢
  exact coverage_rows hi lo hh

end Erdos577.PathClass
