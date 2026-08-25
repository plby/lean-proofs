/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock19_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights19, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt19 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 1052680 (9467715) =
      weightedMaskMass a 2621568 (9467715) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052680, 2621568, 9467715) (by decide)]
  have h001 : weightedMaskMass a 1052708 (53268080) =
      weightedMaskMass a 4194882 (53268080) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052708, 4194882, 53268080) (by decide)]
  have h002 : weightedMaskMass a 1052736 (53928802) =
      weightedMaskMass a 1212416 (53928802) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052736, 1212416, 53928802) (by decide)]
  have h003 : weightedMaskMass a 1052738 (-55489481) =
      weightedMaskMass a 1212420 (-55489481) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052738, 1212420, -55489481) (by decide)]
  have h004 : weightedMaskMass a 1052928 (43775107) =
      weightedMaskMass a 4325440 (43775107) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052928, 4325440, 43775107) (by decide)]
  have h005 : weightedMaskMass a 1052928 (-65106055) =
      weightedMaskMass a 4358144 (-65106055) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052928, 4358144, -65106055) (by decide)]
  have h006 : weightedMaskMass a 1052932 (-14684391) =
      weightedMaskMass a 4325442 (-14684391) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052932, 4325442, -14684391) (by decide)]
  have h007 : weightedMaskMass a 1052960 (16225856) =
      weightedMaskMass a 4325952 (16225856) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052960, 4325952, 16225856) (by decide)]
  have h008 : weightedMaskMass a 1052964 (-45316572) =
      weightedMaskMass a 4325954 (-45316572) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052964, 4325954, -45316572) (by decide)]
  have h009 : weightedMaskMass a 1054724 (105571547) =
      weightedMaskMass a 1345536 (105571547) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1054724, 1345536, 105571547) (by decide)]
  have h010 : weightedMaskMass a 1054724 (-111229747) =
      weightedMaskMass a 4196392 (-111229747) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1054724, 4196392, -111229747) (by decide)]
  have h011 : weightedMaskMass a 1054784 (-64757635) =
      weightedMaskMass a 1212417 (-64757635) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1054784, 1212417, -64757635) (by decide)]
  have h012 : weightedMaskMass a 1057042 (30639701) =
      weightedMaskMass a 2656260 (30639701) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057042, 2656260, 30639701) (by decide)]
  have h013 : weightedMaskMass a 1057058 (99645501) =
      weightedMaskMass a 2656264 (99645501) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057058, 2656264, 99645501) (by decide)]
  have h014 : weightedMaskMass a 1057058 (-312410781) =
      weightedMaskMass a 3672096 (-312410781) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057058, 3672096, -312410781) (by decide)]
  have h015 : weightedMaskMass a 1057060 (-166269323) =
      weightedMaskMass a 3670560 (-166269323) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057060, 3670560, -166269323) (by decide)]
  have h016 : weightedMaskMass a 1057064 (-135144951) =
      weightedMaskMass a 3686432 (-135144951) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057064, 3686432, -135144951) (by decide)]
  have h017 : weightedMaskMass a 1057314 (-128653024) =
      weightedMaskMass a 1574948 (-128653024) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057314, 1574948, -128653024) (by decide)]
  have h018 : weightedMaskMass a 1057316 (-93600310) =
      weightedMaskMass a 1573412 (-93600310) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057316, 1573412, -93600310) (by decide)]
  have h019 : weightedMaskMass a 1057320 (-3679867) =
      weightedMaskMass a 1589284 (-3679867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057320, 1589284, -3679867) (by decide)]
  have h020 : weightedMaskMass a 1057538 (1647175) =
      weightedMaskMass a 2623524 (1647175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057538, 2623524, 1647175) (by decide)]
  have h021 : weightedMaskMass a 1057540 (-53525755) =
      weightedMaskMass a 2621988 (-53525755) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057540, 2621988, -53525755) (by decide)]
  have h022 : weightedMaskMass a 1057570 (299561171) =
      weightedMaskMass a 3672100 (299561171) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057570, 3672100, 299561171) (by decide)]
  have h023 : weightedMaskMass a 1057572 (167814579) =
      weightedMaskMass a 3670564 (167814579) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057572, 3670564, 167814579) (by decide)]
  have h024 : weightedMaskMass a 1057576 (168780328) =
      weightedMaskMass a 3686436 (168780328) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1057576, 3686436, 168780328) (by decide)]
  have h025 : weightedMaskMass a 1060864 (5035160) =
      weightedMaskMass a 4325384 (5035160) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1060864, 4325384, 5035160) (by decide)]
  have h026 : weightedMaskMass a 1060868 (-8644951) =
      weightedMaskMass a 4325416 (-8644951) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1060868, 4325416, -8644951) (by decide)]
  have h027 : weightedMaskMass a 1064978 (52873365) =
      weightedMaskMass a 1083396 (52873365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1064978, 1083396, 52873365) (by decide)]
  have h028 : weightedMaskMass a 1064980 (167022923) =
      weightedMaskMass a 1065220 (167022923) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1064980, 1065220, 167022923) (by decide)]
  have h029 : weightedMaskMass a 1064980 (-84794639) =
      weightedMaskMass a 1097732 (-84794639) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1064980, 1097732, -84794639) (by decide)]
  have h030 : weightedMaskMass a 1064980 (-78144335) =
      weightedMaskMass a 2097704 (-78144335) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1064980, 2097704, -78144335) (by decide)]
  have h031 : weightedMaskMass a 1065234 (-83046979) =
      weightedMaskMass a 1083412 (-83046979) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065234, 1083412, -83046979) (by decide)]
  have h032 : weightedMaskMass a 1065234 (-72088433) =
      weightedMaskMass a 1607684 (-72088433) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065234, 1607684, -72088433) (by decide)]
  have h033 : weightedMaskMass a 1065236 (74260118) =
      weightedMaskMass a 1097748 (74260118) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065236, 1097748, 74260118) (by decide)]
  have h034 : weightedMaskMass a 1065236 (-49428958) =
      weightedMaskMass a 1097988 (-49428958) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065236, 1097988, -49428958) (by decide)]
  have h035 : weightedMaskMass a 1065250 (-128494038) =
      weightedMaskMass a 1607688 (-128494038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065250, 1607688, -128494038) (by decide)]
  have h036 : weightedMaskMass a 1065250 (18539041) =
      weightedMaskMass a 3147816 (18539041) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065250, 3147816, 18539041) (by decide)]
  have h037 : weightedMaskMass a 1065252 (44358762) =
      weightedMaskMass a 1097860 (44358762) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065252, 1097860, 44358762) (by decide)]
  have h038 : weightedMaskMass a 1065252 (68930850) =
      weightedMaskMass a 3146280 (68930850) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065252, 3146280, 68930850) (by decide)]
  have h039 : weightedMaskMass a 1065256 (3518159) =
      weightedMaskMass a 3162152 (3518159) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1065256, 3162152, 3518159) (by decide)]
  have h040 : weightedMaskMass a 1069058 (61695120) =
      weightedMaskMass a 1575040 (61695120) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1069058, 1575040, 61695120) (by decide)]
  have h041 : weightedMaskMass a 1069060 (558318) =
      weightedMaskMass a 4194856 (558318) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1069060, 4194856, 558318) (by decide)]
  have h042 : weightedMaskMass a 1073170 (86696464) =
      weightedMaskMass a 3180548 (86696464) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073170, 3180548, 86696464) (by decide)]
  have h043 : weightedMaskMass a 1073172 (-46769860) =
      weightedMaskMass a 2228776 (-46769860) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073172, 2228776, -46769860) (by decide)]
  have h044 : weightedMaskMass a 1073184 (110948265) =
      weightedMaskMass a 1572904 (110948265) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073184, 1572904, 110948265) (by decide)]
  have h045 : weightedMaskMass a 1073184 (-96337064) =
      weightedMaskMass a 3178504 (-96337064) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073184, 3178504, -96337064) (by decide)]
  have h046 : weightedMaskMass a 1073186 (-91116704) =
      weightedMaskMass a 1574952 (-91116704) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073186, 1574952, -91116704) (by decide)]
  have h047 : weightedMaskMass a 1073186 (155034188) =
      weightedMaskMass a 3180552 (155034188) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073186, 3180552, 155034188) (by decide)]
  have h048 : weightedMaskMass a 1073188 (-122246560) =
      weightedMaskMass a 1573416 (-122246560) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073188, 1573416, -122246560) (by decide)]
  have h049 : weightedMaskMass a 1073192 (19505633) =
      weightedMaskMass a 1589288 (19505633) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073192, 1589288, 19505633) (by decide)]
  have h050 : weightedMaskMass a 1073410 (57132571) =
      weightedMaskMass a 2623528 (57132571) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073410, 2623528, 57132571) (by decide)]
  have h051 : weightedMaskMass a 1073410 (43418708) =
      weightedMaskMass a 3704832 (43418708) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073410, 3704832, 43418708) (by decide)]
  have h052 : weightedMaskMass a 1073412 (-57107442) =
      weightedMaskMass a 2621992 (-57107442) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073412, 2621992, -57107442) (by decide)]
  have h053 : weightedMaskMass a 1073426 (-68305186) =
      weightedMaskMass a 3704836 (-68305186) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073426, 3704836, -68305186) (by decide)]
  have h054 : weightedMaskMass a 1073440 (-241745177) =
      weightedMaskMass a 3670056 (-241745177) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073440, 3670056, -241745177) (by decide)]
  have h055 : weightedMaskMass a 1073440 (7537053) =
      weightedMaskMass a 3702792 (7537053) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073440, 3702792, 7537053) (by decide)]
  have h056 : weightedMaskMass a 1073442 (313957475) =
      weightedMaskMass a 3672104 (313957475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073442, 3672104, 313957475) (by decide)]
  have h057 : weightedMaskMass a 1073442 (-137763847) =
      weightedMaskMass a 3704840 (-137763847) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073442, 3704840, -137763847) (by decide)]
  have h058 : weightedMaskMass a 1073444 (208501794) =
      weightedMaskMass a 3670568 (208501794) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073444, 3670568, 208501794) (by decide)]
  have h059 : weightedMaskMass a 1073448 (187398958) =
      weightedMaskMass a 3686440 (187398958) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1073448, 3686440, 187398958) (by decide)]
  have h060 : weightedMaskMass a 1077248 (45656696) =
      weightedMaskMass a 4325896 (45656696) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1077248, 4325896, 45656696) (by decide)]
  have h061 : weightedMaskMass a 1077252 (-48561897) =
      weightedMaskMass a 4325928 (-48561897) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1077252, 4325928, -48561897) (by decide)]
  have h062 : weightedMaskMass a 1081353 (100849343) =
      weightedMaskMass a 2244610 (100849343) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1081353, 2244610, 100849343) (by decide)]
  have h063 : weightedMaskMass a 1083401 (14295815) =
      weightedMaskMass a 2244642 (14295815) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1083401, 2244642, 14295815) (by decide)]
  have h064 : weightedMaskMass a 1083521 (-53237565) =
      weightedMaskMass a 2228770 (-53237565) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1083521, 2228770, -53237565) (by decide)]
  have h065 : weightedMaskMass a 1083652 (66386036) =
      weightedMaskMass a 1097746 (66386036) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1083652, 1097746, 66386036) (by decide)]
  have h066 : weightedMaskMass a 1083668 (-213817762) =
      weightedMaskMass a 1098002 (-213817762) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1083668, 1098002, -213817762) (by decide)]
  have h067 : weightedMaskMass a 1085441 (30204581) =
      weightedMaskMass a 4200512 (30204581) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085441, 4200512, 30204581) (by decide)]
  have h068 : weightedMaskMass a 1085442 (28171725) =
      weightedMaskMass a 1311236 (28171725) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085442, 1311236, 28171725) (by decide)]
  have h069 : weightedMaskMass a 1085442 (128462546) =
      weightedMaskMass a 1572993 (128462546) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085442, 1572993, 128462546) (by decide)]
  have h070 : weightedMaskMass a 1085444 (7938838) =
      weightedMaskMass a 1343492 (7938838) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085444, 1343492, 7938838) (by decide)]
  have h071 : weightedMaskMass a 1085444 (60564682) =
      weightedMaskMass a 4198466 (60564682) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085444, 4198466, 60564682) (by decide)]
  have h072 : weightedMaskMass a 1085696 (44632160) =
      weightedMaskMass a 4329536 (44632160) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085696, 4329536, 44632160) (by decide)]
  have h073 : weightedMaskMass a 1085700 (-28732962) =
      weightedMaskMass a 4329538 (-28732962) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1085700, 4329538, -28732962) (by decide)]
  have h074 : weightedMaskMass a 1087492 (-26468995) =
      weightedMaskMass a 1345540 (-26468995) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1087492, 1345540, -26468995) (by decide)]
  have h075 : weightedMaskMass a 1089537 (42801977) =
      weightedMaskMass a 2260994 (42801977) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1089537, 2260994, 42801977) (by decide)]
  have h076 : weightedMaskMass a 1089538 (-19512249) =
      weightedMaskMass a 1327105 (-19512249) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1089538, 1327105, -19512249) (by decide)]
  have h077 : weightedMaskMass a 1089540 (-50400780) =
      weightedMaskMass a 1327120 (-50400780) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1089540, 1327120, -50400780) (by decide)]
  have h078 : weightedMaskMass a 1089545 (49685983) =
      weightedMaskMass a 2277378 (49685983) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1089545, 2277378, 49685983) (by decide)]
  have h079 : weightedMaskMass a 1097737 (-172863047) =
      weightedMaskMass a 2244674 (-172863047) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1097737, 2244674, -172863047) (by decide)]
  have h080 : weightedMaskMass a 1101826 (-166080906) =
      weightedMaskMass a 1575041 (-166080906) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1101826, 1575041, -166080906) (by decide)]
  have h081 : weightedMaskMass a 1105921 (-42470647) =
      weightedMaskMass a 2261058 (-42470647) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1105921, 2261058, -42470647) (by decide)]
  have h082 : weightedMaskMass a 1105929 (50286440) =
      weightedMaskMass a 2277442 (50286440) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1105929, 2277442, 50286440) (by decide)]
  have h083 : weightedMaskMass a 1179682 (73515647) =
      weightedMaskMass a 1179780 (73515647) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179682, 1179780, 73515647) (by decide)]
  have h084 : weightedMaskMass a 1179688 (10697824) =
      weightedMaskMass a 1179777 (10697824) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179688, 1179777, 10697824) (by decide)]
  have h085 : weightedMaskMass a 1179712 (-2289039) =
      weightedMaskMass a 1179904 (-2289039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179712, 1179904, -2289039) (by decide)]
  have h086 : weightedMaskMass a 1179713 (-6937879) =
      weightedMaskMass a 1179912 (-6937879) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179713, 1179912, -6937879) (by decide)]
  have h087 : weightedMaskMass a 1179714 (85904551) =
      weightedMaskMass a 1179908 (85904551) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179714, 1179908, 85904551) (by decide)]
  have h088 : weightedMaskMass a 1179716 (-64597065) =
      weightedMaskMass a 1179906 (-64597065) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179716, 1179906, -64597065) (by decide)]
  have h089 : weightedMaskMass a 1179810 (-28746755) =
      weightedMaskMass a 1179812 (-28746755) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179810, 1179812, -28746755) (by decide)]
  have h090 : weightedMaskMass a 1179840 (-826234) =
      weightedMaskMass a 1179936 (-826234) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179840, 1179936, -826234) (by decide)]
  have h091 : weightedMaskMass a 1179840 (3417293) =
      weightedMaskMass a 1180224 (3417293) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179840, 1180224, 3417293) (by decide)]
  have h092 : weightedMaskMass a 1179841 (9914663) =
      weightedMaskMass a 1179944 (9914663) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179841, 1179944, 9914663) (by decide)]
  have h093 : weightedMaskMass a 1179842 (-84519078) =
      weightedMaskMass a 1179940 (-84519078) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179842, 1179940, -84519078) (by decide)]
  have h094 : weightedMaskMass a 1179842 (-1687494) =
      weightedMaskMass a 1180226 (-1687494) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179842, 1180226, -1687494) (by decide)]
  have h095 : weightedMaskMass a 1179844 (2260252) =
      weightedMaskMass a 1179938 (2260252) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179844, 1179938, 2260252) (by decide)]
  have h096 : weightedMaskMass a 1179970 (-92529130) =
      weightedMaskMass a 1179972 (-92529130) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1179970, 1179972, -92529130) (by decide)]
  have h097 : weightedMaskMass a 1180161 (54532363) =
      weightedMaskMass a 3147840 (54532363) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180161, 3147840, 54532363) (by decide)]
  have h098 : weightedMaskMass a 1180164 (48156438) =
      weightedMaskMass a 3145794 (48156438) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180164, 3145794, 48156438) (by decide)]
  have h099 : weightedMaskMass a 1180192 (58983307) =
      weightedMaskMass a 3146304 (58983307) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180192, 3146304, 58983307) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt19 s.val : ℝ)) = (((((((weightedMaskMass a 1052680 (9467715) + (-weightedMaskMass a 2621568 (9467715) + weightedMaskMass a 1052708 (53268080))) + (-weightedMaskMass a 4194882 (53268080) + (weightedMaskMass a 1052736 (53928802) + -weightedMaskMass a 1212416 (53928802)))) + ((weightedMaskMass a 1052738 (-55489481) + (-weightedMaskMass a 1212420 (-55489481) + weightedMaskMass a 1052928 (43775107))) + (-weightedMaskMass a 4325440 (43775107) + (weightedMaskMass a 1052928 (-65106055) + -weightedMaskMass a 4358144 (-65106055))))) + (((weightedMaskMass a 1052932 (-14684391) + (-weightedMaskMass a 4325442 (-14684391) + weightedMaskMass a 1052960 (16225856))) + (-weightedMaskMass a 4325952 (16225856) + (weightedMaskMass a 1052964 (-45316572) + -weightedMaskMass a 4325954 (-45316572)))) + ((weightedMaskMass a 1054724 (105571547) + (-weightedMaskMass a 1345536 (105571547) + weightedMaskMass a 1054724 (-111229747))) + ((-weightedMaskMass a 4196392 (-111229747) + weightedMaskMass a 1054784 (-64757635)) + (-weightedMaskMass a 1212417 (-64757635) + weightedMaskMass a 1057042 (30639701)))))) + ((((-weightedMaskMass a 2656260 (30639701) + (weightedMaskMass a 1057058 (99645501) + -weightedMaskMass a 2656264 (99645501))) + (weightedMaskMass a 1057058 (-312410781) + (-weightedMaskMass a 3672096 (-312410781) + weightedMaskMass a 1057060 (-166269323)))) + ((-weightedMaskMass a 3670560 (-166269323) + (weightedMaskMass a 1057064 (-135144951) + -weightedMaskMass a 3686432 (-135144951))) + (weightedMaskMass a 1057314 (-128653024) + (-weightedMaskMass a 1574948 (-128653024) + weightedMaskMass a 1057316 (-93600310))))) + (((-weightedMaskMass a 1573412 (-93600310) + (weightedMaskMass a 1057320 (-3679867) + -weightedMaskMass a 1589284 (-3679867))) + (weightedMaskMass a 1057538 (1647175) + (-weightedMaskMass a 2623524 (1647175) + weightedMaskMass a 1057540 (-53525755)))) + ((-weightedMaskMass a 2621988 (-53525755) + (weightedMaskMass a 1057570 (299561171) + -weightedMaskMass a 3672100 (299561171))) + ((weightedMaskMass a 1057572 (167814579) + -weightedMaskMass a 3670564 (167814579)) + (weightedMaskMass a 1057576 (168780328) + -weightedMaskMass a 3686436 (168780328))))))) + (((((weightedMaskMass a 1060864 (5035160) + (-weightedMaskMass a 4325384 (5035160) + weightedMaskMass a 1060868 (-8644951))) + (-weightedMaskMass a 4325416 (-8644951) + (weightedMaskMass a 1064978 (52873365) + -weightedMaskMass a 1083396 (52873365)))) + ((weightedMaskMass a 1064980 (167022923) + (-weightedMaskMass a 1065220 (167022923) + weightedMaskMass a 1064980 (-84794639))) + (-weightedMaskMass a 1097732 (-84794639) + (weightedMaskMass a 1064980 (-78144335) + -weightedMaskMass a 2097704 (-78144335))))) + (((weightedMaskMass a 1065234 (-83046979) + (-weightedMaskMass a 1083412 (-83046979) + weightedMaskMass a 1065234 (-72088433))) + (-weightedMaskMass a 1607684 (-72088433) + (weightedMaskMass a 1065236 (74260118) + -weightedMaskMass a 1097748 (74260118)))) + ((weightedMaskMass a 1065236 (-49428958) + (-weightedMaskMass a 1097988 (-49428958) + weightedMaskMass a 1065250 (-128494038))) + ((-weightedMaskMass a 1607688 (-128494038) + weightedMaskMass a 1065250 (18539041)) + (-weightedMaskMass a 3147816 (18539041) + weightedMaskMass a 1065252 (44358762)))))) + ((((-weightedMaskMass a 1097860 (44358762) + (weightedMaskMass a 1065252 (68930850) + -weightedMaskMass a 3146280 (68930850))) + (weightedMaskMass a 1065256 (3518159) + (-weightedMaskMass a 3162152 (3518159) + weightedMaskMass a 1069058 (61695120)))) + ((-weightedMaskMass a 1575040 (61695120) + (weightedMaskMass a 1069060 (558318) + -weightedMaskMass a 4194856 (558318))) + (weightedMaskMass a 1073170 (86696464) + (-weightedMaskMass a 3180548 (86696464) + weightedMaskMass a 1073172 (-46769860))))) + (((-weightedMaskMass a 2228776 (-46769860) + (weightedMaskMass a 1073184 (110948265) + -weightedMaskMass a 1572904 (110948265))) + (weightedMaskMass a 1073184 (-96337064) + (-weightedMaskMass a 3178504 (-96337064) + weightedMaskMass a 1073186 (-91116704)))) + ((-weightedMaskMass a 1574952 (-91116704) + (weightedMaskMass a 1073186 (155034188) + -weightedMaskMass a 3180552 (155034188))) + ((weightedMaskMass a 1073188 (-122246560) + -weightedMaskMass a 1573416 (-122246560)) + (weightedMaskMass a 1073192 (19505633) + -weightedMaskMass a 1589288 (19505633)))))))) + ((((((weightedMaskMass a 1073410 (57132571) + (-weightedMaskMass a 2623528 (57132571) + weightedMaskMass a 1073410 (43418708))) + (-weightedMaskMass a 3704832 (43418708) + (weightedMaskMass a 1073412 (-57107442) + -weightedMaskMass a 2621992 (-57107442)))) + ((weightedMaskMass a 1073426 (-68305186) + (-weightedMaskMass a 3704836 (-68305186) + weightedMaskMass a 1073440 (-241745177))) + (-weightedMaskMass a 3670056 (-241745177) + (weightedMaskMass a 1073440 (7537053) + -weightedMaskMass a 3702792 (7537053))))) + (((weightedMaskMass a 1073442 (313957475) + (-weightedMaskMass a 3672104 (313957475) + weightedMaskMass a 1073442 (-137763847))) + (-weightedMaskMass a 3704840 (-137763847) + (weightedMaskMass a 1073444 (208501794) + -weightedMaskMass a 3670568 (208501794)))) + ((weightedMaskMass a 1073448 (187398958) + (-weightedMaskMass a 3686440 (187398958) + weightedMaskMass a 1077248 (45656696))) + ((-weightedMaskMass a 4325896 (45656696) + weightedMaskMass a 1077252 (-48561897)) + (-weightedMaskMass a 4325928 (-48561897) + weightedMaskMass a 1081353 (100849343)))))) + ((((-weightedMaskMass a 2244610 (100849343) + (weightedMaskMass a 1083401 (14295815) + -weightedMaskMass a 2244642 (14295815))) + (weightedMaskMass a 1083521 (-53237565) + (-weightedMaskMass a 2228770 (-53237565) + weightedMaskMass a 1083652 (66386036)))) + ((-weightedMaskMass a 1097746 (66386036) + (weightedMaskMass a 1083668 (-213817762) + -weightedMaskMass a 1098002 (-213817762))) + (weightedMaskMass a 1085441 (30204581) + (-weightedMaskMass a 4200512 (30204581) + weightedMaskMass a 1085442 (28171725))))) + (((-weightedMaskMass a 1311236 (28171725) + (weightedMaskMass a 1085442 (128462546) + -weightedMaskMass a 1572993 (128462546))) + (weightedMaskMass a 1085444 (7938838) + (-weightedMaskMass a 1343492 (7938838) + weightedMaskMass a 1085444 (60564682)))) + ((-weightedMaskMass a 4198466 (60564682) + (weightedMaskMass a 1085696 (44632160) + -weightedMaskMass a 4329536 (44632160))) + ((weightedMaskMass a 1085700 (-28732962) + -weightedMaskMass a 4329538 (-28732962)) + (weightedMaskMass a 1087492 (-26468995) + -weightedMaskMass a 1345540 (-26468995))))))) + (((((weightedMaskMass a 1089537 (42801977) + (-weightedMaskMass a 2260994 (42801977) + weightedMaskMass a 1089538 (-19512249))) + (-weightedMaskMass a 1327105 (-19512249) + (weightedMaskMass a 1089540 (-50400780) + -weightedMaskMass a 1327120 (-50400780)))) + ((weightedMaskMass a 1089545 (49685983) + (-weightedMaskMass a 2277378 (49685983) + weightedMaskMass a 1097737 (-172863047))) + (-weightedMaskMass a 2244674 (-172863047) + (weightedMaskMass a 1101826 (-166080906) + -weightedMaskMass a 1575041 (-166080906))))) + (((weightedMaskMass a 1105921 (-42470647) + (-weightedMaskMass a 2261058 (-42470647) + weightedMaskMass a 1105929 (50286440))) + (-weightedMaskMass a 2277442 (50286440) + (weightedMaskMass a 1179682 (73515647) + -weightedMaskMass a 1179780 (73515647)))) + ((weightedMaskMass a 1179688 (10697824) + (-weightedMaskMass a 1179777 (10697824) + weightedMaskMass a 1179712 (-2289039))) + ((-weightedMaskMass a 1179904 (-2289039) + weightedMaskMass a 1179713 (-6937879)) + (-weightedMaskMass a 1179912 (-6937879) + weightedMaskMass a 1179714 (85904551)))))) + ((((-weightedMaskMass a 1179908 (85904551) + (weightedMaskMass a 1179716 (-64597065) + -weightedMaskMass a 1179906 (-64597065))) + (weightedMaskMass a 1179810 (-28746755) + (-weightedMaskMass a 1179812 (-28746755) + weightedMaskMass a 1179840 (-826234)))) + ((-weightedMaskMass a 1179936 (-826234) + (weightedMaskMass a 1179840 (3417293) + -weightedMaskMass a 1180224 (3417293))) + (weightedMaskMass a 1179841 (9914663) + (-weightedMaskMass a 1179944 (9914663) + weightedMaskMass a 1179842 (-84519078))))) + (((-weightedMaskMass a 1179940 (-84519078) + (weightedMaskMass a 1179842 (-1687494) + -weightedMaskMass a 1180226 (-1687494))) + (weightedMaskMass a 1179844 (2260252) + (-weightedMaskMass a 1179938 (2260252) + weightedMaskMass a 1179970 (-92529130)))) + ((-weightedMaskMass a 1179972 (-92529130) + (weightedMaskMass a 1180161 (54532363) + -weightedMaskMass a 3147840 (54532363))) + ((weightedMaskMass a 1180164 (48156438) + -weightedMaskMass a 3145794 (48156438)) + (weightedMaskMass a 1180192 (58983307) + -weightedMaskMass a 3146304 (58983307))))))))) := by
      simp only [atomCongruenceContributionInt19, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
