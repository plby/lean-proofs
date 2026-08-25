/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock15_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights15, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt15 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 286720 (171319150) =
      weightedMaskMass a 524576 (171319150) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286720, 524576, 171319150) (by decide)]
  have h001 : weightedMaskMass a 286720 (-99873099) =
      weightedMaskMass a 3153920 (-99873099) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286720, 3153920, -99873099) (by decide)]
  have h002 : weightedMaskMass a 286721 (-178307546) =
      weightedMaskMass a 526624 (-178307546) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286721, 526624, -178307546) (by decide)]
  have h003 : weightedMaskMass a 286721 (108084048) =
      weightedMaskMass a 3153922 (108084048) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286721, 3153922, 108084048) (by decide)]
  have h004 : weightedMaskMass a 286736 (-193247340) =
      weightedMaskMass a 525088 (-193247340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286736, 525088, -193247340) (by decide)]
  have h005 : weightedMaskMass a 286736 (86901057) =
      weightedMaskMass a 3153924 (86901057) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286736, 3153924, 86901057) (by decide)]
  have h006 : weightedMaskMass a 286752 (-373162341) =
      weightedMaskMass a 540960 (-373162341) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286752, 540960, -373162341) (by decide)]
  have h007 : weightedMaskMass a 286752 (328150829) =
      weightedMaskMass a 3153928 (328150829) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286752, 3153928, 328150829) (by decide)]
  have h008 : weightedMaskMass a 286976 (-152811787) =
      weightedMaskMass a 532768 (-152811787) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286976, 532768, -152811787) (by decide)]
  have h009 : weightedMaskMass a 286976 (61230567) =
      weightedMaskMass a 3678208 (61230567) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286976, 3678208, 61230567) (by decide)]
  have h010 : weightedMaskMass a 286992 (174739976) =
      weightedMaskMass a 533280 (174739976) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286992, 533280, 174739976) (by decide)]
  have h011 : weightedMaskMass a 286992 (-84260055) =
      weightedMaskMass a 3678212 (-84260055) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (286992, 3678212, -84260055) (by decide)]
  have h012 : weightedMaskMass a 287008 (372093750) =
      weightedMaskMass a 549152 (372093750) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (287008, 549152, 372093750) (by decide)]
  have h013 : weightedMaskMass a 287008 (-313685014) =
      weightedMaskMass a 3678216 (-313685014) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (287008, 3678216, -313685014) (by decide)]
  have h014 : weightedMaskMass a 291072 (17401821) =
      weightedMaskMass a 536864 (17401821) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (291072, 536864, 17401821) (by decide)]
  have h015 : weightedMaskMass a 291104 (-10650749) =
      weightedMaskMass a 553248 (-10650749) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (291104, 553248, -10650749) (by decide)]
  have h016 : weightedMaskMass a 294913 (15312316) =
      weightedMaskMass a 327684 (15312316) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (294913, 327684, 15312316) (by decide)]
  have h017 : weightedMaskMass a 294913 (-20743145) =
      weightedMaskMass a 525313 (-20743145) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (294913, 525313, -20743145) (by decide)]
  have h018 : weightedMaskMass a 294913 (-75641375) =
      weightedMaskMass a 2098192 (-75641375) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (294913, 2098192, -75641375) (by decide)]
  have h019 : weightedMaskMass a 294913 (-36007756) =
      weightedMaskMass a 4198432 (-36007756) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (294913, 4198432, -36007756) (by decide)]
  have h020 : weightedMaskMass a 294921 (84143157) =
      weightedMaskMass a 525377 (84143157) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (294921, 525377, 84143157) (by decide)]
  have h021 : weightedMaskMass a 296961 (-6805381) =
      weightedMaskMass a 327700 (-6805381) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296961, 327700, -6805381) (by decide)]
  have h022 : weightedMaskMass a 296961 (2820016) =
      weightedMaskMass a 2098196 (2820016) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296961, 2098196, 2820016) (by decide)]
  have h023 : weightedMaskMass a 296968 (-101706439) =
      weightedMaskMass a 5244960 (-101706439) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296968, 5244960, -101706439) (by decide)]
  have h024 : weightedMaskMass a 296976 (-10897742) =
      weightedMaskMass a 327704 (-10897742) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296976, 327704, -10897742) (by decide)]
  have h025 : weightedMaskMass a 296976 (-21083556) =
      weightedMaskMass a 397316 (-21083556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296976, 397316, -21083556) (by decide)]
  have h026 : weightedMaskMass a 296976 (-70256319) =
      weightedMaskMass a 530436 (-70256319) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296976, 530436, -70256319) (by decide)]
  have h027 : weightedMaskMass a 296976 (105368678) =
      weightedMaskMass a 2098244 (105368678) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296976, 2098244, 105368678) (by decide)]
  have h028 : weightedMaskMass a 296980 (53705126) =
      weightedMaskMass a 563204 (53705126) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296980, 563204, 53705126) (by decide)]
  have h029 : weightedMaskMass a 296980 (41389798) =
      weightedMaskMass a 2229316 (41389798) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (296980, 2229316, 41389798) (by decide)]
  have h030 : weightedMaskMass a 299009 (4466220) =
      weightedMaskMass a 4200480 (4466220) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (299009, 4200480, 4466220) (by decide)]
  have h031 : weightedMaskMass a 311296 (11223945) =
      weightedMaskMass a 327712 (11223945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 327712, 11223945) (by decide)]
  have h032 : weightedMaskMass a 311296 (128113622) =
      weightedMaskMass a 541696 (128113622) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 541696, 128113622) (by decide)]
  have h033 : weightedMaskMass a 311296 (64230423) =
      weightedMaskMass a 590848 (64230423) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 590848, 64230423) (by decide)]
  have h034 : weightedMaskMass a 311296 (-58037492) =
      weightedMaskMass a 2098178 (-58037492) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 2098178, -58037492) (by decide)]
  have h035 : weightedMaskMass a 311296 (-75785206) =
      weightedMaskMass a 2392064 (-75785206) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 2392064, -75785206) (by decide)]
  have h036 : weightedMaskMass a 311296 (9664681) =
      weightedMaskMass a 4227074 (9664681) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 4227074, 9664681) (by decide)]
  have h037 : weightedMaskMass a 311296 (-138933818) =
      weightedMaskMass a 4718624 (-138933818) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311296, 4718624, -138933818) (by decide)]
  have h038 : weightedMaskMass a 311297 (-71270219) =
      weightedMaskMass a 327716 (-71270219) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311297, 327716, -71270219) (by decide)]
  have h039 : weightedMaskMass a 311297 (-113284382) =
      weightedMaskMass a 541697 (-113284382) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311297, 541697, -113284382) (by decide)]
  have h040 : weightedMaskMass a 311297 (54958297) =
      weightedMaskMass a 2098194 (54958297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311297, 2098194, 54958297) (by decide)]
  have h041 : weightedMaskMass a 311297 (115603293) =
      weightedMaskMass a 4722720 (115603293) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311297, 4722720, 115603293) (by decide)]
  have h042 : weightedMaskMass a 315392 (161925911) =
      weightedMaskMass a 2394112 (161925911) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (315392, 2394112, 161925911) (by decide)]
  have h043 : weightedMaskMass a 315392 (-16578896) =
      weightedMaskMass a 4720672 (-16578896) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (315392, 4720672, -16578896) (by decide)]
  have h044 : weightedMaskMass a 311300 (-74321680) =
      weightedMaskMass a 541712 (-74321680) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311300, 541712, -74321680) (by decide)]
  have h045 : weightedMaskMass a 311300 (71859912) =
      weightedMaskMass a 2229250 (71859912) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311300, 2229250, 71859912) (by decide)]
  have h046 : weightedMaskMass a 311304 (-37335033) =
      weightedMaskMass a 541760 (-37335033) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311304, 541760, -37335033) (by decide)]
  have h047 : weightedMaskMass a 311305 (51739693) =
      weightedMaskMass a 541761 (51739693) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311305, 541761, 51739693) (by decide)]
  have h048 : weightedMaskMass a 311312 (61356291) =
      weightedMaskMass a 327720 (61356291) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311312, 327720, 61356291) (by decide)]
  have h049 : weightedMaskMass a 311312 (-9297208) =
      weightedMaskMass a 541700 (-9297208) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311312, 541700, -9297208) (by decide)]
  have h050 : weightedMaskMass a 311312 (19192654) =
      weightedMaskMass a 2098242 (19192654) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311312, 2098242, 19192654) (by decide)]
  have h051 : weightedMaskMass a 311312 (67239651) =
      weightedMaskMass a 5275650 (67239651) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311312, 5275650, 67239651) (by decide)]
  have h052 : weightedMaskMass a 311316 (-185604294) =
      weightedMaskMass a 541716 (-185604294) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311316, 541716, -185604294) (by decide)]
  have h053 : weightedMaskMass a 311316 (-18647044) =
      weightedMaskMass a 2229314 (-18647044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311316, 2229314, -18647044) (by decide)]
  have h054 : weightedMaskMass a 311320 (-11169290) =
      weightedMaskMass a 541764 (-11169290) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (311320, 541764, -11169290) (by decide)]
  have h055 : weightedMaskMass a 315393 (-89803152) =
      weightedMaskMass a 4724768 (-89803152) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (315393, 4724768, -89803152) (by decide)]
  have h056 : weightedMaskMass a 327681 (-45393469) =
      weightedMaskMass a 2098177 (-45393469) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327681, 2098177, -45393469) (by decide)]
  have h057 : weightedMaskMass a 327689 (1063459) =
      weightedMaskMass a 2098241 (1063459) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327689, 2098241, 1063459) (by decide)]
  have h058 : weightedMaskMass a 327808 (18537876) =
      weightedMaskMass a 425984 (18537876) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327808, 425984, 18537876) (by decide)]
  have h059 : weightedMaskMass a 327812 (-39215026) =
      weightedMaskMass a 425985 (-39215026) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327812, 425985, -39215026) (by decide)]
  have h060 : weightedMaskMass a 327840 (34341898) =
      weightedMaskMass a 442368 (34341898) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327840, 442368, 34341898) (by decide)]
  have h061 : weightedMaskMass a 327844 (-76660022) =
      weightedMaskMass a 442369 (-76660022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (327844, 442369, -76660022) (by decide)]
  have h062 : weightedMaskMass a 328704 (-53994609) =
      weightedMaskMass a 2360320 (-53994609) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328704, 2360320, -53994609) (by decide)]
  have h063 : weightedMaskMass a 328704 (-34806904) =
      weightedMaskMass a 4195330 (-34806904) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328704, 4195330, -34806904) (by decide)]
  have h064 : weightedMaskMass a 328704 (53744311) =
      weightedMaskMass a 4456480 (53744311) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328704, 4456480, 53744311) (by decide)]
  have h065 : weightedMaskMass a 328704 (96163945) =
      weightedMaskMass a 4489216 (96163945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328704, 4489216, 96163945) (by decide)]
  have h066 : weightedMaskMass a 328704 (-78880100) =
      weightedMaskMass a 4719616 (-78880100) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328704, 4719616, -78880100) (by decide)]
  have h067 : weightedMaskMass a 328705 (20294132) =
      weightedMaskMass a 2360321 (20294132) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328705, 2360321, 20294132) (by decide)]
  have h068 : weightedMaskMass a 328708 (-6910073) =
      weightedMaskMass a 2360336 (-6910073) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328708, 2360336, -6910073) (by decide)]
  have h069 : weightedMaskMass a 328708 (42145575) =
      weightedMaskMass a 4460576 (42145575) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328708, 4460576, 42145575) (by decide)]
  have h070 : weightedMaskMass a 2362368 (-54660613) =
      weightedMaskMass a 4721664 (-54660613) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2362368, 4721664, -54660613) (by decide)]
  have h071 : weightedMaskMass a 328720 (35023426) =
      weightedMaskMass a 2360324 (35023426) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328720, 2360324, 35023426) (by decide)]
  have h072 : weightedMaskMass a 328720 (52309952) =
      weightedMaskMass a 4493312 (52309952) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328720, 4493312, 52309952) (by decide)]
  have h073 : weightedMaskMass a 4458528 (89839475) =
      weightedMaskMass a 4491264 (89839475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4458528, 4491264, 89839475) (by decide)]
  have h074 : weightedMaskMass a 328724 (-20282143) =
      weightedMaskMass a 2360340 (-20282143) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (328724, 2360340, -20282143) (by decide)]
  have h075 : weightedMaskMass a 331784 (-42670610) =
      weightedMaskMass a 659460 (-42670610) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (331784, 659460, -42670610) (by decide)]
  have h076 : weightedMaskMass a 331808 (102722981) =
      weightedMaskMass a 590852 (102722981) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (331808, 590852, 102722981) (by decide)]
  have h077 : weightedMaskMass a 331808 (-92384774) =
      weightedMaskMass a 2392080 (-92384774) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (331808, 2392080, -92384774) (by decide)]
  have h078 : weightedMaskMass a 332800 (-138971412) =
      weightedMaskMass a 4489232 (-138971412) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (332800, 4489232, -138971412) (by decide)]
  have h079 : weightedMaskMass a 332800 (155685543) =
      weightedMaskMass a 4719620 (155685543) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (332800, 4719620, 155685543) (by decide)]
  have h080 : weightedMaskMass a 335872 (3706570) =
      weightedMaskMass a 4198404 (3706570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (335872, 4198404, 3706570) (by decide)]
  have h081 : weightedMaskMass a 529409 (41056351) =
      weightedMaskMass a 2106384 (41056351) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (529409, 2106384, 41056351) (by decide)]
  have h082 : weightedMaskMass a 335880 (28070379) =
      weightedMaskMass a 4722692 (28070379) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (335880, 4722692, 28070379) (by decide)]
  have h083 : weightedMaskMass a 335888 (40055824) =
      weightedMaskMass a 4200452 (40055824) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (335888, 4200452, 40055824) (by decide)]
  have h084 : weightedMaskMass a 335896 (-38233256) =
      weightedMaskMass a 4724740 (-38233256) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (335896, 4724740, -38233256) (by decide)]
  have h085 : weightedMaskMass a 4195346 (-40042013) =
      weightedMaskMass a 4456484 (-40042013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195346, 4456484, -40042013) (by decide)]
  have h086 : weightedMaskMass a 4195346 (57634528) =
      weightedMaskMass a 4723712 (57634528) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195346, 4723712, 57634528) (by decide)]
  have h087 : weightedMaskMass a 339968 (-33793389) =
      weightedMaskMass a 4329476 (-33793389) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (339968, 4329476, -33793389) (by decide)]
  have h088 : weightedMaskMass a 339976 (24879652) =
      weightedMaskMass a 4853764 (24879652) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (339976, 4853764, 24879652) (by decide)]
  have h089 : weightedMaskMass a 344065 (61125630) =
      weightedMaskMass a 2114561 (61125630) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344065, 2114561, 61125630) (by decide)]
  have h090 : weightedMaskMass a 344068 (107644802) =
      weightedMaskMass a 2114576 (107644802) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344068, 2114576, 107644802) (by decide)]
  have h091 : weightedMaskMass a 344072 (141652296) =
      weightedMaskMass a 2114624 (141652296) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344072, 2114624, 141652296) (by decide)]
  have h092 : weightedMaskMass a 344073 (-113996042) =
      weightedMaskMass a 2114625 (-113996042) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344073, 2114625, -113996042) (by decide)]
  have h093 : weightedMaskMass a 344080 (150422087) =
      weightedMaskMass a 2114564 (150422087) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344080, 2114564, 150422087) (by decide)]
  have h094 : weightedMaskMass a 344084 (-156186670) =
      weightedMaskMass a 2114580 (-156186670) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344084, 2114580, -156186670) (by decide)]
  have h095 : weightedMaskMass a 344088 (-168373094) =
      weightedMaskMass a 2114628 (-168373094) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344088, 2114628, -168373094) (by decide)]
  have h096 : weightedMaskMass a 344096 (72254698) =
      weightedMaskMass a 2114562 (72254698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344096, 2114562, 72254698) (by decide)]
  have h097 : weightedMaskMass a 344100 (-118210399) =
      weightedMaskMass a 2114578 (-118210399) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344100, 2114578, -118210399) (by decide)]
  have h098 : weightedMaskMass a 344104 (-59209790) =
      weightedMaskMass a 2114626 (-59209790) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (344104, 2114626, -59209790) (by decide)]
  have h099 : weightedMaskMass a 345088 (124454044) =
      weightedMaskMass a 2376704 (124454044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (345088, 2376704, 124454044) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt15 s.val : ℝ)) = (((((((weightedMaskMass a 286720 (171319150) + (-weightedMaskMass a 524576 (171319150) + weightedMaskMass a 286720 (-99873099))) + (-weightedMaskMass a 3153920 (-99873099) + (weightedMaskMass a 286721 (-178307546) + -weightedMaskMass a 526624 (-178307546)))) + ((weightedMaskMass a 286721 (108084048) + (-weightedMaskMass a 3153922 (108084048) + weightedMaskMass a 286736 (-193247340))) + (-weightedMaskMass a 525088 (-193247340) + (weightedMaskMass a 286736 (86901057) + -weightedMaskMass a 3153924 (86901057))))) + (((weightedMaskMass a 286752 (-373162341) + (-weightedMaskMass a 540960 (-373162341) + weightedMaskMass a 286752 (328150829))) + (-weightedMaskMass a 3153928 (328150829) + (weightedMaskMass a 286976 (-152811787) + -weightedMaskMass a 532768 (-152811787)))) + ((weightedMaskMass a 286976 (61230567) + (-weightedMaskMass a 3678208 (61230567) + weightedMaskMass a 286992 (174739976))) + ((-weightedMaskMass a 533280 (174739976) + weightedMaskMass a 286992 (-84260055)) + (-weightedMaskMass a 3678212 (-84260055) + weightedMaskMass a 287008 (372093750)))))) + ((((-weightedMaskMass a 549152 (372093750) + (weightedMaskMass a 287008 (-313685014) + -weightedMaskMass a 3678216 (-313685014))) + (weightedMaskMass a 291072 (17401821) + (-weightedMaskMass a 536864 (17401821) + weightedMaskMass a 291104 (-10650749)))) + ((-weightedMaskMass a 553248 (-10650749) + (weightedMaskMass a 294913 (15312316) + -weightedMaskMass a 327684 (15312316))) + (weightedMaskMass a 294913 (-20743145) + (-weightedMaskMass a 525313 (-20743145) + weightedMaskMass a 294913 (-75641375))))) + (((-weightedMaskMass a 2098192 (-75641375) + (weightedMaskMass a 294913 (-36007756) + -weightedMaskMass a 4198432 (-36007756))) + (weightedMaskMass a 294921 (84143157) + (-weightedMaskMass a 525377 (84143157) + weightedMaskMass a 296961 (-6805381)))) + ((-weightedMaskMass a 327700 (-6805381) + (weightedMaskMass a 296961 (2820016) + -weightedMaskMass a 2098196 (2820016))) + ((weightedMaskMass a 296968 (-101706439) + -weightedMaskMass a 5244960 (-101706439)) + (weightedMaskMass a 296976 (-10897742) + -weightedMaskMass a 327704 (-10897742))))))) + (((((weightedMaskMass a 296976 (-21083556) + (-weightedMaskMass a 397316 (-21083556) + weightedMaskMass a 296976 (-70256319))) + (-weightedMaskMass a 530436 (-70256319) + (weightedMaskMass a 296976 (105368678) + -weightedMaskMass a 2098244 (105368678)))) + ((weightedMaskMass a 296980 (53705126) + (-weightedMaskMass a 563204 (53705126) + weightedMaskMass a 296980 (41389798))) + (-weightedMaskMass a 2229316 (41389798) + (weightedMaskMass a 299009 (4466220) + -weightedMaskMass a 4200480 (4466220))))) + (((weightedMaskMass a 311296 (11223945) + (-weightedMaskMass a 327712 (11223945) + weightedMaskMass a 311296 (128113622))) + (-weightedMaskMass a 541696 (128113622) + (weightedMaskMass a 311296 (64230423) + -weightedMaskMass a 590848 (64230423)))) + ((weightedMaskMass a 311296 (-58037492) + (-weightedMaskMass a 2098178 (-58037492) + weightedMaskMass a 311296 (-75785206))) + ((-weightedMaskMass a 2392064 (-75785206) + weightedMaskMass a 311296 (9664681)) + (-weightedMaskMass a 4227074 (9664681) + weightedMaskMass a 311296 (-138933818)))))) + ((((-weightedMaskMass a 4718624 (-138933818) + (weightedMaskMass a 311297 (-71270219) + -weightedMaskMass a 327716 (-71270219))) + (weightedMaskMass a 311297 (-113284382) + (-weightedMaskMass a 541697 (-113284382) + weightedMaskMass a 311297 (54958297)))) + ((-weightedMaskMass a 2098194 (54958297) + (weightedMaskMass a 311297 (115603293) + -weightedMaskMass a 4722720 (115603293))) + (weightedMaskMass a 315392 (161925911) + (-weightedMaskMass a 2394112 (161925911) + weightedMaskMass a 315392 (-16578896))))) + (((-weightedMaskMass a 4720672 (-16578896) + (weightedMaskMass a 311300 (-74321680) + -weightedMaskMass a 541712 (-74321680))) + (weightedMaskMass a 311300 (71859912) + (-weightedMaskMass a 2229250 (71859912) + weightedMaskMass a 311304 (-37335033)))) + ((-weightedMaskMass a 541760 (-37335033) + (weightedMaskMass a 311305 (51739693) + -weightedMaskMass a 541761 (51739693))) + ((weightedMaskMass a 311312 (61356291) + -weightedMaskMass a 327720 (61356291)) + (weightedMaskMass a 311312 (-9297208) + -weightedMaskMass a 541700 (-9297208)))))))) + ((((((weightedMaskMass a 311312 (19192654) + (-weightedMaskMass a 2098242 (19192654) + weightedMaskMass a 311312 (67239651))) + (-weightedMaskMass a 5275650 (67239651) + (weightedMaskMass a 311316 (-185604294) + -weightedMaskMass a 541716 (-185604294)))) + ((weightedMaskMass a 311316 (-18647044) + (-weightedMaskMass a 2229314 (-18647044) + weightedMaskMass a 311320 (-11169290))) + (-weightedMaskMass a 541764 (-11169290) + (weightedMaskMass a 315393 (-89803152) + -weightedMaskMass a 4724768 (-89803152))))) + (((weightedMaskMass a 327681 (-45393469) + (-weightedMaskMass a 2098177 (-45393469) + weightedMaskMass a 327689 (1063459))) + (-weightedMaskMass a 2098241 (1063459) + (weightedMaskMass a 327808 (18537876) + -weightedMaskMass a 425984 (18537876)))) + ((weightedMaskMass a 327812 (-39215026) + (-weightedMaskMass a 425985 (-39215026) + weightedMaskMass a 327840 (34341898))) + ((-weightedMaskMass a 442368 (34341898) + weightedMaskMass a 327844 (-76660022)) + (-weightedMaskMass a 442369 (-76660022) + weightedMaskMass a 328704 (-53994609)))))) + ((((-weightedMaskMass a 2360320 (-53994609) + (weightedMaskMass a 328704 (-34806904) + -weightedMaskMass a 4195330 (-34806904))) + (weightedMaskMass a 328704 (53744311) + (-weightedMaskMass a 4456480 (53744311) + weightedMaskMass a 328704 (96163945)))) + ((-weightedMaskMass a 4489216 (96163945) + (weightedMaskMass a 328704 (-78880100) + -weightedMaskMass a 4719616 (-78880100))) + (weightedMaskMass a 328705 (20294132) + (-weightedMaskMass a 2360321 (20294132) + weightedMaskMass a 328708 (-6910073))))) + (((-weightedMaskMass a 2360336 (-6910073) + (weightedMaskMass a 328708 (42145575) + -weightedMaskMass a 4460576 (42145575))) + (weightedMaskMass a 2362368 (-54660613) + (-weightedMaskMass a 4721664 (-54660613) + weightedMaskMass a 328720 (35023426)))) + ((-weightedMaskMass a 2360324 (35023426) + (weightedMaskMass a 328720 (52309952) + -weightedMaskMass a 4493312 (52309952))) + ((weightedMaskMass a 4458528 (89839475) + -weightedMaskMass a 4491264 (89839475)) + (weightedMaskMass a 328724 (-20282143) + -weightedMaskMass a 2360340 (-20282143))))))) + (((((weightedMaskMass a 331784 (-42670610) + (-weightedMaskMass a 659460 (-42670610) + weightedMaskMass a 331808 (102722981))) + (-weightedMaskMass a 590852 (102722981) + (weightedMaskMass a 331808 (-92384774) + -weightedMaskMass a 2392080 (-92384774)))) + ((weightedMaskMass a 332800 (-138971412) + (-weightedMaskMass a 4489232 (-138971412) + weightedMaskMass a 332800 (155685543))) + (-weightedMaskMass a 4719620 (155685543) + (weightedMaskMass a 335872 (3706570) + -weightedMaskMass a 4198404 (3706570))))) + (((weightedMaskMass a 529409 (41056351) + (-weightedMaskMass a 2106384 (41056351) + weightedMaskMass a 335880 (28070379))) + (-weightedMaskMass a 4722692 (28070379) + (weightedMaskMass a 335888 (40055824) + -weightedMaskMass a 4200452 (40055824)))) + ((weightedMaskMass a 335896 (-38233256) + (-weightedMaskMass a 4724740 (-38233256) + weightedMaskMass a 4195346 (-40042013))) + ((-weightedMaskMass a 4456484 (-40042013) + weightedMaskMass a 4195346 (57634528)) + (-weightedMaskMass a 4723712 (57634528) + weightedMaskMass a 339968 (-33793389)))))) + ((((-weightedMaskMass a 4329476 (-33793389) + (weightedMaskMass a 339976 (24879652) + -weightedMaskMass a 4853764 (24879652))) + (weightedMaskMass a 344065 (61125630) + (-weightedMaskMass a 2114561 (61125630) + weightedMaskMass a 344068 (107644802)))) + ((-weightedMaskMass a 2114576 (107644802) + (weightedMaskMass a 344072 (141652296) + -weightedMaskMass a 2114624 (141652296))) + (weightedMaskMass a 344073 (-113996042) + (-weightedMaskMass a 2114625 (-113996042) + weightedMaskMass a 344080 (150422087))))) + (((-weightedMaskMass a 2114564 (150422087) + (weightedMaskMass a 344084 (-156186670) + -weightedMaskMass a 2114580 (-156186670))) + (weightedMaskMass a 344088 (-168373094) + (-weightedMaskMass a 2114628 (-168373094) + weightedMaskMass a 344096 (72254698)))) + ((-weightedMaskMass a 2114562 (72254698) + (weightedMaskMass a 344100 (-118210399) + -weightedMaskMass a 2114578 (-118210399))) + ((weightedMaskMass a 344104 (-59209790) + -weightedMaskMass a 2114626 (-59209790)) + (weightedMaskMass a 345088 (124454044) + -weightedMaskMass a 2376704 (124454044))))))))) := by
      simp only [atomCongruenceContributionInt15, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
