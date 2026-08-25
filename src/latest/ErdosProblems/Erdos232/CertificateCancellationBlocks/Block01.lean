/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock01_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights01, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt01 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 40 (51216491) =
      weightedMaskMass a 4160 (51216491) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 4160, 51216491) (by decide)]
  have h001 : weightedMaskMass a 40 (-33511326) =
      weightedMaskMass a 16388 (-33511326) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 16388, -33511326) (by decide)]
  have h002 : weightedMaskMass a 40 (47736480) =
      weightedMaskMass a 16400 (47736480) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 16400, 47736480) (by decide)]
  have h003 : weightedMaskMass a 40 (130619639) =
      weightedMaskMass a 131074 (130619639) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 131074, 130619639) (by decide)]
  have h004 : weightedMaskMass a 40 (-56271073) =
      weightedMaskMass a 1048580 (-56271073) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 1048580, -56271073) (by decide)]
  have h005 : weightedMaskMass a 40 (-34847450) =
      weightedMaskMass a 1064960 (-34847450) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 1064960, -34847450) (by decide)]
  have h006 : weightedMaskMass a 40 (-158354959) =
      weightedMaskMass a 1081344 (-158354959) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 1081344, -158354959) (by decide)]
  have h007 : weightedMaskMass a 40 (141210688) =
      weightedMaskMass a 2097664 (141210688) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40, 2097664, 141210688) (by decide)]
  have h008 : weightedMaskMass a 160 (64985467) =
      weightedMaskMass a 576 (64985467) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 576, 64985467) (by decide)]
  have h009 : weightedMaskMass a 160 (98674147) =
      weightedMaskMass a 16512 (98674147) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 16512, 98674147) (by decide)]
  have h010 : weightedMaskMass a 160 (76817659) =
      weightedMaskMass a 32776 (76817659) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 32776, 76817659) (by decide)]
  have h011 : weightedMaskMass a 160 (-113199774) =
      weightedMaskMass a 131200 (-113199774) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 131200, -113199774) (by decide)]
  have h012 : weightedMaskMass a 160 (2706443) =
      weightedMaskMass a 147456 (2706443) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 147456, 2706443) (by decide)]
  have h013 : weightedMaskMass a 160 (123581608) =
      weightedMaskMass a 524352 (123581608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 524352, 123581608) (by decide)]
  have h014 : weightedMaskMass a 160 (-62845156) =
      weightedMaskMass a 1048608 (-62845156) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (160, 1048608, -62845156) (by decide)]
  have h015 : weightedMaskMass a 162 (-1751861) =
      weightedMaskMass a 164 (-1751861) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 164, -1751861) (by decide)]
  have h016 : weightedMaskMass a 162 (-61775565) =
      weightedMaskMass a 16514 (-61775565) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 16514, -61775565) (by decide)]
  have h017 : weightedMaskMass a 162 (-109658575) =
      weightedMaskMass a 34824 (-109658575) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 34824, -109658575) (by decide)]
  have h018 : weightedMaskMass a 162 (13287079) =
      weightedMaskMass a 98312 (13287079) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 98312, 13287079) (by decide)]
  have h019 : weightedMaskMass a 162 (-151940772) =
      weightedMaskMass a 131204 (-151940772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 131204, -151940772) (by decide)]
  have h020 : weightedMaskMass a 162 (-38403844) =
      weightedMaskMass a 147457 (-38403844) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 147457, -38403844) (by decide)]
  have h021 : weightedMaskMass a 162 (10225406) =
      weightedMaskMass a 147488 (10225406) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 147488, 10225406) (by decide)]
  have h022 : weightedMaskMass a 162 (167644200) =
      weightedMaskMass a 1048610 (167644200) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 1048610, 167644200) (by decide)]
  have h023 : weightedMaskMass a 162 (71897990) =
      weightedMaskMass a 1050656 (71897990) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 1050656, 71897990) (by decide)]
  have h024 : weightedMaskMass a 162 (64995550) =
      weightedMaskMass a 2621504 (64995550) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (162, 2621504, 64995550) (by decide)]
  have h025 : weightedMaskMass a 192 (-80803076) =
      weightedMaskMass a 288 (-80803076) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 288, -80803076) (by decide)]
  have h026 : weightedMaskMass a 192 (82380868) =
      weightedMaskMass a 24576 (82380868) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 24576, 82380868) (by decide)]
  have h027 : weightedMaskMass a 192 (79617300) =
      weightedMaskMass a 32832 (79617300) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 32832, 79617300) (by decide)]
  have h028 : weightedMaskMass a 192 (-14483455) =
      weightedMaskMass a 32896 (-14483455) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 32896, -14483455) (by decide)]
  have h029 : weightedMaskMass a 192 (-84381320) =
      weightedMaskMass a 131584 (-84381320) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 131584, -84381320) (by decide)]
  have h030 : weightedMaskMass a 192 (80422761) =
      weightedMaskMass a 524296 (80422761) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 524296, 80422761) (by decide)]
  have h031 : weightedMaskMass a 192 (68148503) =
      weightedMaskMass a 3145728 (68148503) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (192, 3145728, 68148503) (by decide)]
  have h032 : weightedMaskMass a 193 (22723110) =
      weightedMaskMass a 296 (22723110) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (193, 296, 22723110) (by decide)]
  have h033 : weightedMaskMass a 193 (-33237679) =
      weightedMaskMass a 4288 (-33237679) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (193, 4288, -33237679) (by decide)]
  have h034 : weightedMaskMass a 193 (24746623) =
      weightedMaskMass a 3162112 (24746623) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (193, 3162112, 24746623) (by decide)]
  have h035 : weightedMaskMass a 194 (-50010403) =
      weightedMaskMass a 292 (-50010403) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 292, -50010403) (by decide)]
  have h036 : weightedMaskMass a 194 (19613130) =
      weightedMaskMass a 24580 (19613130) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 24580, 19613130) (by decide)]
  have h037 : weightedMaskMass a 194 (-17339741) =
      weightedMaskMass a 34944 (-17339741) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 34944, -17339741) (by decide)]
  have h038 : weightedMaskMass a 194 (-15215279) =
      weightedMaskMass a 131586 (-15215279) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 131586, -15215279) (by decide)]
  have h039 : weightedMaskMass a 194 (108928011) =
      weightedMaskMass a 131616 (108928011) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 131616, 108928011) (by decide)]
  have h040 : weightedMaskMass a 194 (-195783356) =
      weightedMaskMass a 524808 (-195783356) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 524808, -195783356) (by decide)]
  have h041 : weightedMaskMass a 194 (165784965) =
      weightedMaskMass a 1081472 (165784965) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 1081472, 165784965) (by decide)]
  have h042 : weightedMaskMass a 194 (-3390816) =
      weightedMaskMass a 3146240 (-3390816) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (194, 3146240, -3390816) (by decide)]
  have h043 : weightedMaskMass a 196 (-5456114) =
      weightedMaskMass a 290 (-5456114) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 290, -5456114) (by decide)]
  have h044 : weightedMaskMass a 196 (-69607978) =
      weightedMaskMass a 24578 (-69607978) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 24578, -69607978) (by decide)]
  have h045 : weightedMaskMass a 196 (76293652) =
      weightedMaskMass a 98432 (76293652) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 98432, 76293652) (by decide)]
  have h046 : weightedMaskMass a 196 (-13302044) =
      weightedMaskMass a 131585 (-13302044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 131585, -13302044) (by decide)]
  have h047 : weightedMaskMass a 196 (7224482) =
      weightedMaskMass a 526344 (7224482) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 526344, 7224482) (by decide)]
  have h048 : weightedMaskMass a 196 (-1500456) =
      weightedMaskMass a 3147776 (-1500456) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196, 3147776, -1500456) (by decide)]
  have h049 : weightedMaskMass a 272 (-87486392) =
      weightedMaskMass a 1088 (-87486392) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 1088, -87486392) (by decide)]
  have h050 : weightedMaskMass a 272 (-127139804) =
      weightedMaskMass a 8704 (-127139804) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 8704, -127139804) (by decide)]
  have h051 : weightedMaskMass a 272 (-56238339) =
      weightedMaskMass a 32784 (-56238339) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 32784, -56238339) (by decide)]
  have h052 : weightedMaskMass a 272 (70480730) =
      weightedMaskMass a 33024 (70480730) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 33024, 70480730) (by decide)]
  have h053 : weightedMaskMass a 272 (34155377) =
      weightedMaskMass a 69632 (34155377) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 69632, 34155377) (by decide)]
  have h054 : weightedMaskMass a 272 (4608616) =
      weightedMaskMass a 135168 (4608616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 135168, 4608616) (by decide)]
  have h055 : weightedMaskMass a 272 (62360318) =
      weightedMaskMass a 196608 (62360318) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 196608, 62360318) (by decide)]
  have h056 : weightedMaskMass a 272 (19216333) =
      weightedMaskMass a 262152 (19216333) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 262152, 19216333) (by decide)]
  have h057 : weightedMaskMass a 272 (2485469) =
      weightedMaskMass a 524292 (2485469) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 524292, 2485469) (by decide)]
  have h058 : weightedMaskMass a 272 (164803181) =
      weightedMaskMass a 5242880 (164803181) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (272, 5242880, 164803181) (by decide)]
  have h059 : weightedMaskMass a 274 (63138262) =
      weightedMaskMass a 1092 (63138262) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 1092, 63138262) (by decide)]
  have h060 : weightedMaskMass a 274 (-45851013) =
      weightedMaskMass a 8706 (-45851013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 8706, -45851013) (by decide)]
  have h061 : weightedMaskMass a 274 (113979607) =
      weightedMaskMass a 9728 (113979607) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 9728, 113979607) (by decide)]
  have h062 : weightedMaskMass a 274 (-39602176) =
      weightedMaskMass a 34832 (-39602176) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 34832, -39602176) (by decide)]
  have h063 : weightedMaskMass a 274 (14322879) =
      weightedMaskMass a 135200 (14322879) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 135200, 14322879) (by decide)]
  have h064 : weightedMaskMass a 274 (21666085) =
      weightedMaskMass a 196612 (21666085) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 196612, 21666085) (by decide)]
  have h065 : weightedMaskMass a 274 (-22036211) =
      weightedMaskMass a 262168 (-22036211) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 262168, -22036211) (by decide)]
  have h066 : weightedMaskMass a 274 (-44283837) =
      weightedMaskMass a 397312 (-44283837) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 397312, -44283837) (by decide)]
  have h067 : weightedMaskMass a 274 (-112304291) =
      weightedMaskMass a 526340 (-112304291) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 526340, -112304291) (by decide)]
  have h068 : weightedMaskMass a 274 (82316922) =
      weightedMaskMass a 5243392 (82316922) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274, 5243392, 82316922) (by decide)]
  have h069 : weightedMaskMass a 276 (-56001698) =
      weightedMaskMass a 1090 (-56001698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 1090, -56001698) (by decide)]
  have h070 : weightedMaskMass a 276 (11584867) =
      weightedMaskMass a 8712 (11584867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 8712, 11584867) (by decide)]
  have h071 : weightedMaskMass a 276 (5102043) =
      weightedMaskMass a 49168 (5102043) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 49168, 5102043) (by decide)]
  have h072 : weightedMaskMass a 276 (-26147334) =
      weightedMaskMass a 135232 (-26147334) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 135232, -26147334) (by decide)]
  have h073 : weightedMaskMass a 276 (-68946328) =
      weightedMaskMass a 196610 (-68946328) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 196610, -68946328) (by decide)]
  have h074 : weightedMaskMass a 276 (-101099607) =
      weightedMaskMass a 262184 (-101099607) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 262184, -101099607) (by decide)]
  have h075 : weightedMaskMass a 276 (165173142) =
      weightedMaskMass a 540676 (165173142) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 540676, 165173142) (by decide)]
  have h076 : weightedMaskMass a 276 (228741690) =
      weightedMaskMass a 1081600 (228741690) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 1081600, 228741690) (by decide)]
  have h077 : weightedMaskMass a 276 (-40781428) =
      weightedMaskMass a 5275648 (-40781428) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (276, 5275648, -40781428) (by decide)]
  have h078 : weightedMaskMass a 280 (20996756) =
      weightedMaskMass a 1089 (20996756) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (280, 1089, 20996756) (by decide)]
  have h079 : weightedMaskMass a 280 (13315743) =
      weightedMaskMass a 69760 (13315743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (280, 69760, 13315743) (by decide)]
  have h080 : weightedMaskMass a 280 (-29525313) =
      weightedMaskMass a 86016 (-29525313) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (280, 86016, -29525313) (by decide)]
  have h081 : weightedMaskMass a 280 (-20659072) =
      weightedMaskMass a 262153 (-20659072) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (280, 262153, -20659072) (by decide)]
  have h082 : weightedMaskMass a 322 (-44971265) =
      weightedMaskMass a 324 (-44971265) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (322, 324, -44971265) (by decide)]
  have h083 : weightedMaskMass a 516 (-177893509) =
      weightedMaskMass a 2112 (-177893509) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 2112, -177893509) (by decide)]
  have h084 : weightedMaskMass a 516 (89407911) =
      weightedMaskMass a 2304 (89407911) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 2304, 89407911) (by decide)]
  have h085 : weightedMaskMass a 516 (-31367471) =
      weightedMaskMass a 8193 (-31367471) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 8193, -31367471) (by decide)]
  have h086 : weightedMaskMass a 516 (91225239) =
      weightedMaskMass a 17408 (91225239) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 17408, 91225239) (by decide)]
  have h087 : weightedMaskMass a 516 (56553812) =
      weightedMaskMass a 32770 (56553812) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 32770, 56553812) (by decide)]
  have h088 : weightedMaskMass a 516 (39838001) =
      weightedMaskMass a 65568 (39838001) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 65568, 39838001) (by decide)]
  have h089 : weightedMaskMass a 516 (-86664798) =
      weightedMaskMass a 131080 (-86664798) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 131080, -86664798) (by decide)]
  have h090 : weightedMaskMass a 516 (59943708) =
      weightedMaskMass a 278528 (59943708) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 278528, 59943708) (by decide)]
  have h091 : weightedMaskMass a 516 (5379889) =
      weightedMaskMass a 524320 (5379889) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 524320, 5379889) (by decide)]
  have h092 : weightedMaskMass a 516 (-57753110) =
      weightedMaskMass a 589824 (-57753110) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 589824, -57753110) (by decide)]
  have h093 : weightedMaskMass a 516 (-36360845) =
      weightedMaskMass a 1048577 (-36360845) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 1048577, -36360845) (by decide)]
  have h094 : weightedMaskMass a 516 (-73250092) =
      weightedMaskMass a 1056768 (-73250092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 1056768, -73250092) (by decide)]
  have h095 : weightedMaskMass a 516 (105958653) =
      weightedMaskMass a 2097154 (105958653) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 2097154, 105958653) (by decide)]
  have h096 : weightedMaskMass a 516 (12513092) =
      weightedMaskMass a 2129920 (12513092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (516, 2129920, 12513092) (by decide)]
  have h097 : weightedMaskMass a 521 (-39452115) =
      weightedMaskMass a 4136 (-39452115) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (521, 4136, -39452115) (by decide)]
  have h098 : weightedMaskMass a 521 (138218121) =
      weightedMaskMass a 81924 (138218121) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (521, 81924, 138218121) (by decide)]
  have h099 : weightedMaskMass a 521 (-32432289) =
      weightedMaskMass a 2099328 (-32432289) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (521, 2099328, -32432289) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt01 s.val : ℝ)) = (((((((weightedMaskMass a 40 (51216491) + (-weightedMaskMass a 4160 (51216491) + weightedMaskMass a 40 (-33511326))) + (-weightedMaskMass a 16388 (-33511326) + (weightedMaskMass a 40 (47736480) + -weightedMaskMass a 16400 (47736480)))) + ((weightedMaskMass a 40 (130619639) + (-weightedMaskMass a 131074 (130619639) + weightedMaskMass a 40 (-56271073))) + (-weightedMaskMass a 1048580 (-56271073) + (weightedMaskMass a 40 (-34847450) + -weightedMaskMass a 1064960 (-34847450))))) + (((weightedMaskMass a 40 (-158354959) + (-weightedMaskMass a 1081344 (-158354959) + weightedMaskMass a 40 (141210688))) + (-weightedMaskMass a 2097664 (141210688) + (weightedMaskMass a 160 (64985467) + -weightedMaskMass a 576 (64985467)))) + ((weightedMaskMass a 160 (98674147) + (-weightedMaskMass a 16512 (98674147) + weightedMaskMass a 160 (76817659))) + ((-weightedMaskMass a 32776 (76817659) + weightedMaskMass a 160 (-113199774)) + (-weightedMaskMass a 131200 (-113199774) + weightedMaskMass a 160 (2706443)))))) + ((((-weightedMaskMass a 147456 (2706443) + (weightedMaskMass a 160 (123581608) + -weightedMaskMass a 524352 (123581608))) + (weightedMaskMass a 160 (-62845156) + (-weightedMaskMass a 1048608 (-62845156) + weightedMaskMass a 162 (-1751861)))) + ((-weightedMaskMass a 164 (-1751861) + (weightedMaskMass a 162 (-61775565) + -weightedMaskMass a 16514 (-61775565))) + (weightedMaskMass a 162 (-109658575) + (-weightedMaskMass a 34824 (-109658575) + weightedMaskMass a 162 (13287079))))) + (((-weightedMaskMass a 98312 (13287079) + (weightedMaskMass a 162 (-151940772) + -weightedMaskMass a 131204 (-151940772))) + (weightedMaskMass a 162 (-38403844) + (-weightedMaskMass a 147457 (-38403844) + weightedMaskMass a 162 (10225406)))) + ((-weightedMaskMass a 147488 (10225406) + (weightedMaskMass a 162 (167644200) + -weightedMaskMass a 1048610 (167644200))) + ((weightedMaskMass a 162 (71897990) + -weightedMaskMass a 1050656 (71897990)) + (weightedMaskMass a 162 (64995550) + -weightedMaskMass a 2621504 (64995550))))))) + (((((weightedMaskMass a 192 (-80803076) + (-weightedMaskMass a 288 (-80803076) + weightedMaskMass a 192 (82380868))) + (-weightedMaskMass a 24576 (82380868) + (weightedMaskMass a 192 (79617300) + -weightedMaskMass a 32832 (79617300)))) + ((weightedMaskMass a 192 (-14483455) + (-weightedMaskMass a 32896 (-14483455) + weightedMaskMass a 192 (-84381320))) + (-weightedMaskMass a 131584 (-84381320) + (weightedMaskMass a 192 (80422761) + -weightedMaskMass a 524296 (80422761))))) + (((weightedMaskMass a 192 (68148503) + (-weightedMaskMass a 3145728 (68148503) + weightedMaskMass a 193 (22723110))) + (-weightedMaskMass a 296 (22723110) + (weightedMaskMass a 193 (-33237679) + -weightedMaskMass a 4288 (-33237679)))) + ((weightedMaskMass a 193 (24746623) + (-weightedMaskMass a 3162112 (24746623) + weightedMaskMass a 194 (-50010403))) + ((-weightedMaskMass a 292 (-50010403) + weightedMaskMass a 194 (19613130)) + (-weightedMaskMass a 24580 (19613130) + weightedMaskMass a 194 (-17339741)))))) + ((((-weightedMaskMass a 34944 (-17339741) + (weightedMaskMass a 194 (-15215279) + -weightedMaskMass a 131586 (-15215279))) + (weightedMaskMass a 194 (108928011) + (-weightedMaskMass a 131616 (108928011) + weightedMaskMass a 194 (-195783356)))) + ((-weightedMaskMass a 524808 (-195783356) + (weightedMaskMass a 194 (165784965) + -weightedMaskMass a 1081472 (165784965))) + (weightedMaskMass a 194 (-3390816) + (-weightedMaskMass a 3146240 (-3390816) + weightedMaskMass a 196 (-5456114))))) + (((-weightedMaskMass a 290 (-5456114) + (weightedMaskMass a 196 (-69607978) + -weightedMaskMass a 24578 (-69607978))) + (weightedMaskMass a 196 (76293652) + (-weightedMaskMass a 98432 (76293652) + weightedMaskMass a 196 (-13302044)))) + ((-weightedMaskMass a 131585 (-13302044) + (weightedMaskMass a 196 (7224482) + -weightedMaskMass a 526344 (7224482))) + ((weightedMaskMass a 196 (-1500456) + -weightedMaskMass a 3147776 (-1500456)) + (weightedMaskMass a 272 (-87486392) + -weightedMaskMass a 1088 (-87486392)))))))) + ((((((weightedMaskMass a 272 (-127139804) + (-weightedMaskMass a 8704 (-127139804) + weightedMaskMass a 272 (-56238339))) + (-weightedMaskMass a 32784 (-56238339) + (weightedMaskMass a 272 (70480730) + -weightedMaskMass a 33024 (70480730)))) + ((weightedMaskMass a 272 (34155377) + (-weightedMaskMass a 69632 (34155377) + weightedMaskMass a 272 (4608616))) + (-weightedMaskMass a 135168 (4608616) + (weightedMaskMass a 272 (62360318) + -weightedMaskMass a 196608 (62360318))))) + (((weightedMaskMass a 272 (19216333) + (-weightedMaskMass a 262152 (19216333) + weightedMaskMass a 272 (2485469))) + (-weightedMaskMass a 524292 (2485469) + (weightedMaskMass a 272 (164803181) + -weightedMaskMass a 5242880 (164803181)))) + ((weightedMaskMass a 274 (63138262) + (-weightedMaskMass a 1092 (63138262) + weightedMaskMass a 274 (-45851013))) + ((-weightedMaskMass a 8706 (-45851013) + weightedMaskMass a 274 (113979607)) + (-weightedMaskMass a 9728 (113979607) + weightedMaskMass a 274 (-39602176)))))) + ((((-weightedMaskMass a 34832 (-39602176) + (weightedMaskMass a 274 (14322879) + -weightedMaskMass a 135200 (14322879))) + (weightedMaskMass a 274 (21666085) + (-weightedMaskMass a 196612 (21666085) + weightedMaskMass a 274 (-22036211)))) + ((-weightedMaskMass a 262168 (-22036211) + (weightedMaskMass a 274 (-44283837) + -weightedMaskMass a 397312 (-44283837))) + (weightedMaskMass a 274 (-112304291) + (-weightedMaskMass a 526340 (-112304291) + weightedMaskMass a 274 (82316922))))) + (((-weightedMaskMass a 5243392 (82316922) + (weightedMaskMass a 276 (-56001698) + -weightedMaskMass a 1090 (-56001698))) + (weightedMaskMass a 276 (11584867) + (-weightedMaskMass a 8712 (11584867) + weightedMaskMass a 276 (5102043)))) + ((-weightedMaskMass a 49168 (5102043) + (weightedMaskMass a 276 (-26147334) + -weightedMaskMass a 135232 (-26147334))) + ((weightedMaskMass a 276 (-68946328) + -weightedMaskMass a 196610 (-68946328)) + (weightedMaskMass a 276 (-101099607) + -weightedMaskMass a 262184 (-101099607))))))) + (((((weightedMaskMass a 276 (165173142) + (-weightedMaskMass a 540676 (165173142) + weightedMaskMass a 276 (228741690))) + (-weightedMaskMass a 1081600 (228741690) + (weightedMaskMass a 276 (-40781428) + -weightedMaskMass a 5275648 (-40781428)))) + ((weightedMaskMass a 280 (20996756) + (-weightedMaskMass a 1089 (20996756) + weightedMaskMass a 280 (13315743))) + (-weightedMaskMass a 69760 (13315743) + (weightedMaskMass a 280 (-29525313) + -weightedMaskMass a 86016 (-29525313))))) + (((weightedMaskMass a 280 (-20659072) + (-weightedMaskMass a 262153 (-20659072) + weightedMaskMass a 322 (-44971265))) + (-weightedMaskMass a 324 (-44971265) + (weightedMaskMass a 516 (-177893509) + -weightedMaskMass a 2112 (-177893509)))) + ((weightedMaskMass a 516 (89407911) + (-weightedMaskMass a 2304 (89407911) + weightedMaskMass a 516 (-31367471))) + ((-weightedMaskMass a 8193 (-31367471) + weightedMaskMass a 516 (91225239)) + (-weightedMaskMass a 17408 (91225239) + weightedMaskMass a 516 (56553812)))))) + ((((-weightedMaskMass a 32770 (56553812) + (weightedMaskMass a 516 (39838001) + -weightedMaskMass a 65568 (39838001))) + (weightedMaskMass a 516 (-86664798) + (-weightedMaskMass a 131080 (-86664798) + weightedMaskMass a 516 (59943708)))) + ((-weightedMaskMass a 278528 (59943708) + (weightedMaskMass a 516 (5379889) + -weightedMaskMass a 524320 (5379889))) + (weightedMaskMass a 516 (-57753110) + (-weightedMaskMass a 589824 (-57753110) + weightedMaskMass a 516 (-36360845))))) + (((-weightedMaskMass a 1048577 (-36360845) + (weightedMaskMass a 516 (-73250092) + -weightedMaskMass a 1056768 (-73250092))) + (weightedMaskMass a 516 (105958653) + (-weightedMaskMass a 2097154 (105958653) + weightedMaskMass a 516 (12513092)))) + ((-weightedMaskMass a 2129920 (12513092) + (weightedMaskMass a 521 (-39452115) + -weightedMaskMass a 4136 (-39452115))) + ((weightedMaskMass a 521 (138218121) + -weightedMaskMass a 81924 (138218121)) + (weightedMaskMass a 521 (-32432289) + -weightedMaskMass a 2099328 (-32432289))))))))) := by
      simp only [atomCongruenceContributionInt01, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
