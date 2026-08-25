/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock12_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights12, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt12 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 102466 (-30304120) =
      weightedMaskMass a 3702788 (-30304120) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (102466, 3702788, -30304120) (by decide)]
  have h001 : weightedMaskMass a 106496 (-91196820) =
      weightedMaskMass a 163841 (-91196820) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106496, 163841, -91196820) (by decide)]
  have h002 : weightedMaskMass a 106496 (5998653) =
      weightedMaskMass a 262276 (5998653) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106496, 262276, 5998653) (by decide)]
  have h003 : weightedMaskMass a 106496 (44744847) =
      weightedMaskMass a 1054720 (44744847) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106496, 1054720, 44744847) (by decide)]
  have h004 : weightedMaskMass a 106496 (-51186567) =
      weightedMaskMass a 1312768 (-51186567) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106496, 1312768, -51186567) (by decide)]
  have h005 : weightedMaskMass a 106496 (14338117) =
      weightedMaskMass a 4196360 (14338117) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106496, 4196360, 14338117) (by decide)]
  have h006 : weightedMaskMass a 106497 (12366898) =
      weightedMaskMass a 2260993 (12366898) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106497, 2260993, 12366898) (by decide)]
  have h007 : weightedMaskMass a 106498 (-16970097) =
      weightedMaskMass a 1312769 (-16970097) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106498, 1312769, -16970097) (by decide)]
  have h008 : weightedMaskMass a 106500 (-4620865) =
      weightedMaskMass a 1312784 (-4620865) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106500, 1312784, -4620865) (by decide)]
  have h009 : weightedMaskMass a 106500 (-38899852) =
      weightedMaskMass a 1579008 (-38899852) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106500, 1579008, -38899852) (by decide)]
  have h010 : weightedMaskMass a 106504 (115451989) =
      weightedMaskMass a 180225 (115451989) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106504, 180225, 115451989) (by decide)]
  have h011 : weightedMaskMass a 106504 (-83010066) =
      weightedMaskMass a 262308 (-83010066) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106504, 262308, -83010066) (by decide)]
  have h012 : weightedMaskMass a 106504 (-673286) =
      weightedMaskMass a 1312800 (-673286) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106504, 1312800, -673286) (by decide)]
  have h013 : weightedMaskMass a 106504 (21506129) =
      weightedMaskMass a 4229128 (21506129) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106504, 4229128, 21506129) (by decide)]
  have h014 : weightedMaskMass a 106505 (57167935) =
      weightedMaskMass a 2277377 (57167935) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106505, 2277377, 57167935) (by decide)]
  have h015 : weightedMaskMass a 106512 (62685275) =
      weightedMaskMass a 167937 (62685275) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106512, 167937, 62685275) (by decide)]
  have h016 : weightedMaskMass a 106512 (2609000) =
      weightedMaskMass a 5249024 (2609000) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106512, 5249024, 2609000) (by decide)]
  have h017 : weightedMaskMass a 106516 (45538993) =
      weightedMaskMass a 5773312 (45538993) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106516, 5773312, 45538993) (by decide)]
  have h018 : weightedMaskMass a 106520 (1772082) =
      weightedMaskMass a 184321 (1772082) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106520, 184321, 1772082) (by decide)]
  have h019 : weightedMaskMass a 106560 (143648145) =
      weightedMaskMass a 295044 (143648145) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106560, 295044, 143648145) (by decide)]
  have h020 : weightedMaskMass a 106752 (119830981) =
      weightedMaskMass a 229377 (119830981) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106752, 229377, 119830981) (by decide)]
  have h021 : weightedMaskMass a 106760 (-19393284) =
      weightedMaskMass a 245761 (-19393284) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106760, 245761, -19393284) (by decide)]
  have h022 : weightedMaskMass a 106768 (-99902041) =
      weightedMaskMass a 233473 (-99902041) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106768, 233473, -99902041) (by decide)]
  have h023 : weightedMaskMass a 106776 (-15397280) =
      weightedMaskMass a 249857 (-15397280) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (106776, 249857, -15397280) (by decide)]
  have h024 : weightedMaskMass a 114690 (-26779305) =
      weightedMaskMass a 1057032 (-26779305) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114690, 1057032, -26779305) (by decide)]
  have h025 : weightedMaskMass a 114690 (-6238343) =
      weightedMaskMass a 2637856 (-6238343) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114690, 2637856, -6238343) (by decide)]
  have h026 : weightedMaskMass a 114692 (-8966115) =
      weightedMaskMass a 2637840 (-8966115) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114692, 2637840, -8966115) (by decide)]
  have h027 : weightedMaskMass a 114696 (14958184) =
      weightedMaskMass a 147521 (14958184) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114696, 147521, 14958184) (by decide)]
  have h028 : weightedMaskMass a 114696 (-183868611) =
      weightedMaskMass a 2637888 (-183868611) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114696, 2637888, -183868611) (by decide)]
  have h029 : weightedMaskMass a 114697 (-206830098) =
      weightedMaskMass a 2244673 (-206830098) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114697, 2244673, -206830098) (by decide)]
  have h030 : weightedMaskMass a 114697 (229524156) =
      weightedMaskMass a 2637889 (229524156) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114697, 2637889, 229524156) (by decide)]
  have h031 : weightedMaskMass a 114706 (6604554) =
      weightedMaskMass a 1057544 (6604554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114706, 1057544, 6604554) (by decide)]
  have h032 : weightedMaskMass a 114706 (-108581106) =
      weightedMaskMass a 2637860 (-108581106) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114706, 2637860, -108581106) (by decide)]
  have h033 : weightedMaskMass a 114708 (-189519175) =
      weightedMaskMass a 2637844 (-189519175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114708, 2637844, -189519175) (by decide)]
  have h034 : weightedMaskMass a 114712 (1117148) =
      weightedMaskMass a 151617 (1117148) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114712, 151617, 1117148) (by decide)]
  have h035 : weightedMaskMass a 114712 (13379764) =
      weightedMaskMass a 2637892 (13379764) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114712, 2637892, 13379764) (by decide)]
  have h036 : weightedMaskMass a 114754 (68152340) =
      weightedMaskMass a 1073416 (68152340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114754, 1073416, 68152340) (by decide)]
  have h037 : weightedMaskMass a 114754 (14597934) =
      weightedMaskMass a 2637864 (14597934) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114754, 2637864, 14597934) (by decide)]
  have h038 : weightedMaskMass a 114756 (39336893) =
      weightedMaskMass a 2637848 (39336893) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114756, 2637848, 39336893) (by decide)]
  have h039 : weightedMaskMass a 114816 (8221453) =
      weightedMaskMass a 131649 (8221453) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114816, 131649, 8221453) (by decide)]
  have h040 : weightedMaskMass a 114817 (-154289239) =
      weightedMaskMass a 2228801 (-154289239) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114817, 2228801, -154289239) (by decide)]
  have h041 : weightedMaskMass a 114944 (70096339) =
      weightedMaskMass a 196673 (70096339) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114944, 196673, 70096339) (by decide)]
  have h042 : weightedMaskMass a 114952 (-119906939) =
      weightedMaskMass a 213057 (-119906939) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114952, 213057, -119906939) (by decide)]
  have h043 : weightedMaskMass a 114960 (-41294764) =
      weightedMaskMass a 200769 (-41294764) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114960, 200769, -41294764) (by decide)]
  have h044 : weightedMaskMass a 114968 (25816052) =
      weightedMaskMass a 217153 (25816052) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (114968, 217153, 25816052) (by decide)]
  have h045 : weightedMaskMass a 118786 (-144757141) =
      weightedMaskMass a 1057048 (-144757141) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (118786, 1057048, -144757141) (by decide)]
  have h046 : weightedMaskMass a 118850 (189626670) =
      weightedMaskMass a 1073432 (189626670) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (118850, 1073432, 189626670) (by decide)]
  have h047 : weightedMaskMass a 122880 (49528838) =
      weightedMaskMass a 163905 (49528838) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122880, 163905, 49528838) (by decide)]
  have h048 : weightedMaskMass a 122881 (-194769078) =
      weightedMaskMass a 2261057 (-194769078) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122881, 2261057, -194769078) (by decide)]
  have h049 : weightedMaskMass a 122888 (69439039) =
      weightedMaskMass a 180289 (69439039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122888, 180289, 69439039) (by decide)]
  have h050 : weightedMaskMass a 122889 (32922786) =
      weightedMaskMass a 2277441 (32922786) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122889, 2277441, 32922786) (by decide)]
  have h051 : weightedMaskMass a 122896 (-44032836) =
      weightedMaskMass a 168001 (-44032836) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122896, 168001, -44032836) (by decide)]
  have h052 : weightedMaskMass a 122904 (-43905421) =
      weightedMaskMass a 184385 (-43905421) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (122904, 184385, -43905421) (by decide)]
  have h053 : weightedMaskMass a 123136 (-108616093) =
      weightedMaskMass a 229441 (-108616093) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (123136, 229441, -108616093) (by decide)]
  have h054 : weightedMaskMass a 123144 (93987458) =
      weightedMaskMass a 245825 (93987458) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (123144, 245825, 93987458) (by decide)]
  have h055 : weightedMaskMass a 123152 (67505513) =
      weightedMaskMass a 233537 (67505513) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (123152, 233537, 67505513) (by decide)]
  have h056 : weightedMaskMass a 123160 (-25376839) =
      weightedMaskMass a 249921 (-25376839) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (123160, 249921, -25376839) (by decide)]
  have h057 : weightedMaskMass a 131232 (-123581608) =
      weightedMaskMass a 524864 (-123581608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131232, 524864, -123581608) (by decide)]
  have h058 : weightedMaskMass a 131232 (43906732) =
      weightedMaskMass a 1048736 (43906732) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131232, 1048736, 43906732) (by decide)]
  have h059 : weightedMaskMass a 131234 (-71067690) =
      weightedMaskMass a 1048740 (-71067690) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131234, 1048740, -71067690) (by decide)]
  have h060 : weightedMaskMass a 131234 (-65323770) =
      weightedMaskMass a 1050784 (-65323770) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131234, 1050784, -65323770) (by decide)]
  have h061 : weightedMaskMass a 131234 (69631929) =
      weightedMaskMass a 2622016 (69631929) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131234, 2622016, 69631929) (by decide)]
  have h062 : weightedMaskMass a 131236 (-148705776) =
      weightedMaskMass a 1048738 (-148705776) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131236, 1048738, -148705776) (by decide)]
  have h063 : weightedMaskMass a 131265 (76541146) =
      weightedMaskMass a 1048872 (76541146) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131265, 1048872, 76541146) (by decide)]
  have h064 : weightedMaskMass a 131265 (-72331096) =
      weightedMaskMass a 3162144 (-72331096) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131265, 3162144, -72331096) (by decide)]
  have h065 : weightedMaskMass a 131266 (20681894) =
      weightedMaskMass a 131650 (20681894) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131266, 131650, 20681894) (by decide)]
  have h066 : weightedMaskMass a 131266 (-22712865) =
      weightedMaskMass a 1048868 (-22712865) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131266, 1048868, -22712865) (by decide)]
  have h067 : weightedMaskMass a 131266 (-81421472) =
      weightedMaskMass a 1097856 (-81421472) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131266, 1097856, -81421472) (by decide)]
  have h068 : weightedMaskMass a 131266 (-12993442) =
      weightedMaskMass a 3146272 (-12993442) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131266, 3146272, -12993442) (by decide)]
  have h069 : weightedMaskMass a 131268 (21719365) =
      weightedMaskMass a 559112 (21719365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131268, 559112, 21719365) (by decide)]
  have h070 : weightedMaskMass a 131268 (-112362324) =
      weightedMaskMass a 1048866 (-112362324) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131268, 1048866, -112362324) (by decide)]
  have h071 : weightedMaskMass a 131268 (-4611919) =
      weightedMaskMass a 3147808 (-4611919) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131268, 3147808, -4611919) (by decide)]
  have h072 : weightedMaskMass a 131328 (64069867) =
      weightedMaskMass a 1048640 (64069867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131328, 1048640, 64069867) (by decide)]
  have h073 : weightedMaskMass a 131328 (-53556320) =
      weightedMaskMass a 1179648 (-53556320) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131328, 1179648, -53556320) (by decide)]
  have h074 : weightedMaskMass a 131330 (104721081) =
      weightedMaskMass a 1048644 (104721081) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131330, 1048644, 104721081) (by decide)]
  have h075 : weightedMaskMass a 131332 (21904954) =
      weightedMaskMass a 1048642 (21904954) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131332, 1048642, 21904954) (by decide)]
  have h076 : weightedMaskMass a 131332 (129379926) =
      weightedMaskMass a 1179650 (129379926) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131332, 1179650, 129379926) (by decide)]
  have h077 : weightedMaskMass a 131332 (-46529769) =
      weightedMaskMass a 1179652 (-46529769) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131332, 1179652, -46529769) (by decide)]
  have h078 : weightedMaskMass a 131336 (-8493195) =
      weightedMaskMass a 1048641 (-8493195) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131336, 1048641, -8493195) (by decide)]
  have h079 : weightedMaskMass a 131360 (-5726220) =
      weightedMaskMass a 1048768 (-5726220) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131360, 1048768, -5726220) (by decide)]
  have h080 : weightedMaskMass a 131360 (60731407) =
      weightedMaskMass a 1180160 (60731407) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131360, 1180160, 60731407) (by decide)]
  have h081 : weightedMaskMass a 131360 (-48156438) =
      weightedMaskMass a 3145792 (-48156438) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131360, 3145792, -48156438) (by decide)]
  have h082 : weightedMaskMass a 131362 (-117160205) =
      weightedMaskMass a 1048772 (-117160205) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131362, 1048772, -117160205) (by decide)]
  have h083 : weightedMaskMass a 131364 (-62195515) =
      weightedMaskMass a 1048770 (-62195515) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131364, 1048770, -62195515) (by decide)]
  have h084 : weightedMaskMass a 131364 (-69719946) =
      weightedMaskMass a 1180162 (-69719946) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131364, 1180162, -69719946) (by decide)]
  have h085 : weightedMaskMass a 131368 (977242) =
      weightedMaskMass a 1048769 (977242) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131368, 1048769, 977242) (by decide)]
  have h086 : weightedMaskMass a 131392 (-10741762) =
      weightedMaskMass a 1048896 (-10741762) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131392, 1048896, -10741762) (by decide)]
  have h087 : weightedMaskMass a 131394 (-89670437) =
      weightedMaskMass a 1048900 (-89670437) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131394, 1048900, -89670437) (by decide)]
  have h088 : weightedMaskMass a 131396 (-49482906) =
      weightedMaskMass a 1048898 (-49482906) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131396, 1048898, -49482906) (by decide)]
  have h089 : weightedMaskMass a 131618 (-58640434) =
      weightedMaskMass a 1083520 (-58640434) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131618, 1083520, -58640434) (by decide)]
  have h090 : weightedMaskMass a 131624 (163171357) =
      weightedMaskMass a 524840 (163171357) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131624, 524840, 163171357) (by decide)]
  have h091 : weightedMaskMass a 131624 (-49769785) =
      weightedMaskMass a 1073156 (-49769785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131624, 1073156, -49769785) (by decide)]
  have h092 : weightedMaskMass a 131652 (31483988) =
      weightedMaskMass a 559168 (31483988) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131652, 559168, 31483988) (by decide)]
  have h093 : weightedMaskMass a 131840 (228215) =
      weightedMaskMass a 3276800 (228215) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131840, 3276800, 228215) (by decide)]
  have h094 : weightedMaskMass a 131844 (-18631674) =
      weightedMaskMass a 3276802 (-18631674) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131844, 3276802, -18631674) (by decide)]
  have h095 : weightedMaskMass a 131872 (-5151387) =
      weightedMaskMass a 3277312 (-5151387) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131872, 3277312, -5151387) (by decide)]
  have h096 : weightedMaskMass a 131876 (67383751) =
      weightedMaskMass a 3277314 (67383751) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (131876, 3277314, 67383751) (by decide)]
  have h097 : weightedMaskMass a 132672 (-36907083) =
      weightedMaskMass a 196800 (-36907083) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132672, 196800, -36907083) (by decide)]
  have h098 : weightedMaskMass a 132672 (148171446) =
      weightedMaskMass a 557080 (148171446) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132672, 557080, 148171446) (by decide)]
  have h099 : weightedMaskMass a 132672 (85155618) =
      weightedMaskMass a 557124 (85155618) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132672, 557124, 85155618) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt12 s.val : ℝ)) = (((((((weightedMaskMass a 102466 (-30304120) + (-weightedMaskMass a 3702788 (-30304120) + weightedMaskMass a 106496 (-91196820))) + (-weightedMaskMass a 163841 (-91196820) + (weightedMaskMass a 106496 (5998653) + -weightedMaskMass a 262276 (5998653)))) + ((weightedMaskMass a 106496 (44744847) + (-weightedMaskMass a 1054720 (44744847) + weightedMaskMass a 106496 (-51186567))) + (-weightedMaskMass a 1312768 (-51186567) + (weightedMaskMass a 106496 (14338117) + -weightedMaskMass a 4196360 (14338117))))) + (((weightedMaskMass a 106497 (12366898) + (-weightedMaskMass a 2260993 (12366898) + weightedMaskMass a 106498 (-16970097))) + (-weightedMaskMass a 1312769 (-16970097) + (weightedMaskMass a 106500 (-4620865) + -weightedMaskMass a 1312784 (-4620865)))) + ((weightedMaskMass a 106500 (-38899852) + (-weightedMaskMass a 1579008 (-38899852) + weightedMaskMass a 106504 (115451989))) + ((-weightedMaskMass a 180225 (115451989) + weightedMaskMass a 106504 (-83010066)) + (-weightedMaskMass a 262308 (-83010066) + weightedMaskMass a 106504 (-673286)))))) + ((((-weightedMaskMass a 1312800 (-673286) + (weightedMaskMass a 106504 (21506129) + -weightedMaskMass a 4229128 (21506129))) + (weightedMaskMass a 106505 (57167935) + (-weightedMaskMass a 2277377 (57167935) + weightedMaskMass a 106512 (62685275)))) + ((-weightedMaskMass a 167937 (62685275) + (weightedMaskMass a 106512 (2609000) + -weightedMaskMass a 5249024 (2609000))) + (weightedMaskMass a 106516 (45538993) + (-weightedMaskMass a 5773312 (45538993) + weightedMaskMass a 106520 (1772082))))) + (((-weightedMaskMass a 184321 (1772082) + (weightedMaskMass a 106560 (143648145) + -weightedMaskMass a 295044 (143648145))) + (weightedMaskMass a 106752 (119830981) + (-weightedMaskMass a 229377 (119830981) + weightedMaskMass a 106760 (-19393284)))) + ((-weightedMaskMass a 245761 (-19393284) + (weightedMaskMass a 106768 (-99902041) + -weightedMaskMass a 233473 (-99902041))) + ((weightedMaskMass a 106776 (-15397280) + -weightedMaskMass a 249857 (-15397280)) + (weightedMaskMass a 114690 (-26779305) + -weightedMaskMass a 1057032 (-26779305))))))) + (((((weightedMaskMass a 114690 (-6238343) + (-weightedMaskMass a 2637856 (-6238343) + weightedMaskMass a 114692 (-8966115))) + (-weightedMaskMass a 2637840 (-8966115) + (weightedMaskMass a 114696 (14958184) + -weightedMaskMass a 147521 (14958184)))) + ((weightedMaskMass a 114696 (-183868611) + (-weightedMaskMass a 2637888 (-183868611) + weightedMaskMass a 114697 (-206830098))) + (-weightedMaskMass a 2244673 (-206830098) + (weightedMaskMass a 114697 (229524156) + -weightedMaskMass a 2637889 (229524156))))) + (((weightedMaskMass a 114706 (6604554) + (-weightedMaskMass a 1057544 (6604554) + weightedMaskMass a 114706 (-108581106))) + (-weightedMaskMass a 2637860 (-108581106) + (weightedMaskMass a 114708 (-189519175) + -weightedMaskMass a 2637844 (-189519175)))) + ((weightedMaskMass a 114712 (1117148) + (-weightedMaskMass a 151617 (1117148) + weightedMaskMass a 114712 (13379764))) + ((-weightedMaskMass a 2637892 (13379764) + weightedMaskMass a 114754 (68152340)) + (-weightedMaskMass a 1073416 (68152340) + weightedMaskMass a 114754 (14597934)))))) + ((((-weightedMaskMass a 2637864 (14597934) + (weightedMaskMass a 114756 (39336893) + -weightedMaskMass a 2637848 (39336893))) + (weightedMaskMass a 114816 (8221453) + (-weightedMaskMass a 131649 (8221453) + weightedMaskMass a 114817 (-154289239)))) + ((-weightedMaskMass a 2228801 (-154289239) + (weightedMaskMass a 114944 (70096339) + -weightedMaskMass a 196673 (70096339))) + (weightedMaskMass a 114952 (-119906939) + (-weightedMaskMass a 213057 (-119906939) + weightedMaskMass a 114960 (-41294764))))) + (((-weightedMaskMass a 200769 (-41294764) + (weightedMaskMass a 114968 (25816052) + -weightedMaskMass a 217153 (25816052))) + (weightedMaskMass a 118786 (-144757141) + (-weightedMaskMass a 1057048 (-144757141) + weightedMaskMass a 118850 (189626670)))) + ((-weightedMaskMass a 1073432 (189626670) + (weightedMaskMass a 122880 (49528838) + -weightedMaskMass a 163905 (49528838))) + ((weightedMaskMass a 122881 (-194769078) + -weightedMaskMass a 2261057 (-194769078)) + (weightedMaskMass a 122888 (69439039) + -weightedMaskMass a 180289 (69439039)))))))) + ((((((weightedMaskMass a 122889 (32922786) + (-weightedMaskMass a 2277441 (32922786) + weightedMaskMass a 122896 (-44032836))) + (-weightedMaskMass a 168001 (-44032836) + (weightedMaskMass a 122904 (-43905421) + -weightedMaskMass a 184385 (-43905421)))) + ((weightedMaskMass a 123136 (-108616093) + (-weightedMaskMass a 229441 (-108616093) + weightedMaskMass a 123144 (93987458))) + (-weightedMaskMass a 245825 (93987458) + (weightedMaskMass a 123152 (67505513) + -weightedMaskMass a 233537 (67505513))))) + (((weightedMaskMass a 123160 (-25376839) + (-weightedMaskMass a 249921 (-25376839) + weightedMaskMass a 131232 (-123581608))) + (-weightedMaskMass a 524864 (-123581608) + (weightedMaskMass a 131232 (43906732) + -weightedMaskMass a 1048736 (43906732)))) + ((weightedMaskMass a 131234 (-71067690) + (-weightedMaskMass a 1048740 (-71067690) + weightedMaskMass a 131234 (-65323770))) + ((-weightedMaskMass a 1050784 (-65323770) + weightedMaskMass a 131234 (69631929)) + (-weightedMaskMass a 2622016 (69631929) + weightedMaskMass a 131236 (-148705776)))))) + ((((-weightedMaskMass a 1048738 (-148705776) + (weightedMaskMass a 131265 (76541146) + -weightedMaskMass a 1048872 (76541146))) + (weightedMaskMass a 131265 (-72331096) + (-weightedMaskMass a 3162144 (-72331096) + weightedMaskMass a 131266 (20681894)))) + ((-weightedMaskMass a 131650 (20681894) + (weightedMaskMass a 131266 (-22712865) + -weightedMaskMass a 1048868 (-22712865))) + (weightedMaskMass a 131266 (-81421472) + (-weightedMaskMass a 1097856 (-81421472) + weightedMaskMass a 131266 (-12993442))))) + (((-weightedMaskMass a 3146272 (-12993442) + (weightedMaskMass a 131268 (21719365) + -weightedMaskMass a 559112 (21719365))) + (weightedMaskMass a 131268 (-112362324) + (-weightedMaskMass a 1048866 (-112362324) + weightedMaskMass a 131268 (-4611919)))) + ((-weightedMaskMass a 3147808 (-4611919) + (weightedMaskMass a 131328 (64069867) + -weightedMaskMass a 1048640 (64069867))) + ((weightedMaskMass a 131328 (-53556320) + -weightedMaskMass a 1179648 (-53556320)) + (weightedMaskMass a 131330 (104721081) + -weightedMaskMass a 1048644 (104721081))))))) + (((((weightedMaskMass a 131332 (21904954) + (-weightedMaskMass a 1048642 (21904954) + weightedMaskMass a 131332 (129379926))) + (-weightedMaskMass a 1179650 (129379926) + (weightedMaskMass a 131332 (-46529769) + -weightedMaskMass a 1179652 (-46529769)))) + ((weightedMaskMass a 131336 (-8493195) + (-weightedMaskMass a 1048641 (-8493195) + weightedMaskMass a 131360 (-5726220))) + (-weightedMaskMass a 1048768 (-5726220) + (weightedMaskMass a 131360 (60731407) + -weightedMaskMass a 1180160 (60731407))))) + (((weightedMaskMass a 131360 (-48156438) + (-weightedMaskMass a 3145792 (-48156438) + weightedMaskMass a 131362 (-117160205))) + (-weightedMaskMass a 1048772 (-117160205) + (weightedMaskMass a 131364 (-62195515) + -weightedMaskMass a 1048770 (-62195515)))) + ((weightedMaskMass a 131364 (-69719946) + (-weightedMaskMass a 1180162 (-69719946) + weightedMaskMass a 131368 (977242))) + ((-weightedMaskMass a 1048769 (977242) + weightedMaskMass a 131392 (-10741762)) + (-weightedMaskMass a 1048896 (-10741762) + weightedMaskMass a 131394 (-89670437)))))) + ((((-weightedMaskMass a 1048900 (-89670437) + (weightedMaskMass a 131396 (-49482906) + -weightedMaskMass a 1048898 (-49482906))) + (weightedMaskMass a 131618 (-58640434) + (-weightedMaskMass a 1083520 (-58640434) + weightedMaskMass a 131624 (163171357)))) + ((-weightedMaskMass a 524840 (163171357) + (weightedMaskMass a 131624 (-49769785) + -weightedMaskMass a 1073156 (-49769785))) + (weightedMaskMass a 131652 (31483988) + (-weightedMaskMass a 559168 (31483988) + weightedMaskMass a 131840 (228215))))) + (((-weightedMaskMass a 3276800 (228215) + (weightedMaskMass a 131844 (-18631674) + -weightedMaskMass a 3276802 (-18631674))) + (weightedMaskMass a 131872 (-5151387) + (-weightedMaskMass a 3277312 (-5151387) + weightedMaskMass a 131876 (67383751)))) + ((-weightedMaskMass a 3277314 (67383751) + (weightedMaskMass a 132672 (-36907083) + -weightedMaskMass a 196800 (-36907083))) + ((weightedMaskMass a 132672 (148171446) + -weightedMaskMass a 557080 (148171446)) + (weightedMaskMass a 132672 (85155618) + -weightedMaskMass a 557124 (85155618))))))))) := by
      simp only [atomCongruenceContributionInt12, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
