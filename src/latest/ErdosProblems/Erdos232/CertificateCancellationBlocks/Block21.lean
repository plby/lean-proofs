/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock21_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights21, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt21 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 1597732 (-861707228) =
      weightedMaskMass a 3678760 (-861707228) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597732, 3678760, -861707228) (by decide)]
  have h001 : weightedMaskMass a 1597736 (-269843409) =
      weightedMaskMass a 3694632 (-269843409) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597736, 3694632, -269843409) (by decide)]
  have h002 : weightedMaskMass a 1605633 (22556890) =
      weightedMaskMass a 2359812 (22556890) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1605633, 2359812, 22556890) (by decide)]
  have h003 : weightedMaskMass a 1605761 (88500468) =
      weightedMaskMass a 3408388 (88500468) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1605761, 3408388, 88500468) (by decide)]
  have h004 : weightedMaskMass a 1622016 (88344827) =
      weightedMaskMass a 2359840 (88344827) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622016, 2359840, 88344827) (by decide)]
  have h005 : weightedMaskMass a 1622017 (-60006134) =
      weightedMaskMass a 2359844 (-60006134) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622017, 2359844, -60006134) (by decide)]
  have h006 : weightedMaskMass a 1622020 (-66182867) =
      weightedMaskMass a 2359848 (-66182867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622020, 2359848, -66182867) (by decide)]
  have h007 : weightedMaskMass a 1622144 (54202529) =
      weightedMaskMass a 3408416 (54202529) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622144, 3408416, 54202529) (by decide)]
  have h008 : weightedMaskMass a 1622145 (-192497556) =
      weightedMaskMass a 3408420 (-192497556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622145, 3408420, -192497556) (by decide)]
  have h009 : weightedMaskMass a 1622148 (-121363022) =
      weightedMaskMass a 3408424 (-121363022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1622148, 3408424, -121363022) (by decide)]
  have h010 : weightedMaskMass a 2097410 (18194022) =
      weightedMaskMass a 2099456 (18194022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097410, 2099456, 18194022) (by decide)]
  have h011 : weightedMaskMass a 2097412 (-25603950) =
      weightedMaskMass a 2097920 (-25603950) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097412, 2097920, -25603950) (by decide)]
  have h012 : weightedMaskMass a 2097416 (8389286) =
      weightedMaskMass a 2113792 (8389286) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097416, 2113792, 8389286) (by decide)]
  have h013 : weightedMaskMass a 2097440 (-17361911) =
      weightedMaskMass a 3145984 (-17361911) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097440, 3145984, -17361911) (by decide)]
  have h014 : weightedMaskMass a 2097442 (-27543838) =
      weightedMaskMass a 3148032 (-27543838) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097442, 3148032, -27543838) (by decide)]
  have h015 : weightedMaskMass a 2097444 (17361911) =
      weightedMaskMass a 3146496 (17361911) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097444, 3146496, 17361911) (by decide)]
  have h016 : weightedMaskMass a 2097448 (24730232) =
      weightedMaskMass a 3162368 (24730232) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097448, 3162368, 24730232) (by decide)]
  have h017 : weightedMaskMass a 2097922 (9554990) =
      weightedMaskMass a 2099460 (9554990) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097922, 2099460, 9554990) (by decide)]
  have h018 : weightedMaskMass a 2097928 (15461870) =
      weightedMaskMass a 2113796 (15461870) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097928, 2113796, 15461870) (by decide)]
  have h019 : weightedMaskMass a 2097952 (39633708) =
      weightedMaskMass a 3145988 (39633708) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097952, 3145988, 39633708) (by decide)]
  have h020 : weightedMaskMass a 2097954 (-22476970) =
      weightedMaskMass a 3148036 (-22476970) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097954, 3148036, -22476970) (by decide)]
  have h021 : weightedMaskMass a 2097956 (-14029758) =
      weightedMaskMass a 3146500 (-14029758) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097956, 3146500, -14029758) (by decide)]
  have h022 : weightedMaskMass a 2097960 (-75776356) =
      weightedMaskMass a 3162372 (-75776356) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2097960, 3162372, -75776356) (by decide)]
  have h023 : weightedMaskMass a 2098690 (42117041) =
      weightedMaskMass a 4719136 (42117041) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2098690, 4719136, 42117041) (by decide)]
  have h024 : weightedMaskMass a 2099220 (53703896) =
      weightedMaskMass a 2361360 (53703896) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099220, 2361360, 53703896) (by decide)]
  have h025 : weightedMaskMass a 2099224 (13172412) =
      weightedMaskMass a 2623504 (13172412) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099224, 2623504, 13172412) (by decide)]
  have h026 : weightedMaskMass a 2099464 (2105700) =
      weightedMaskMass a 2113794 (2105700) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099464, 2113794, 2105700) (by decide)]
  have h027 : weightedMaskMass a 2099488 (56200577) =
      weightedMaskMass a 3145986 (56200577) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099488, 3145986, 56200577) (by decide)]
  have h028 : weightedMaskMass a 2099492 (-28451565) =
      weightedMaskMass a 3146498 (-28451565) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099492, 3146498, -28451565) (by decide)]
  have h029 : weightedMaskMass a 2099496 (-9930941) =
      weightedMaskMass a 3162370 (-9930941) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2099496, 3162370, -9930941) (by decide)]
  have h030 : weightedMaskMass a 2105368 (-42355273) =
      weightedMaskMass a 4720656 (-42355273) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105368, 4720656, -42355273) (by decide)]
  have h031 : weightedMaskMass a 2105600 (34068422) =
      weightedMaskMass a 2621696 (34068422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105600, 2621696, 34068422) (by decide)]
  have h032 : weightedMaskMass a 2105602 (-60940874) =
      weightedMaskMass a 2623744 (-60940874) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105602, 2623744, -60940874) (by decide)]
  have h033 : weightedMaskMass a 2105604 (-34068422) =
      weightedMaskMass a 2622208 (-34068422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105604, 2622208, -34068422) (by decide)]
  have h034 : weightedMaskMass a 2105608 (-91617491) =
      weightedMaskMass a 2638080 (-91617491) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105608, 2638080, -91617491) (by decide)]
  have h035 : weightedMaskMass a 2105632 (-29208074) =
      weightedMaskMass a 3670272 (-29208074) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105632, 3670272, -29208074) (by decide)]
  have h036 : weightedMaskMass a 2105634 (-59831666) =
      weightedMaskMass a 3672320 (-59831666) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105634, 3672320, -59831666) (by decide)]
  have h037 : weightedMaskMass a 2105636 (15318148) =
      weightedMaskMass a 3670784 (15318148) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105636, 3670784, 15318148) (by decide)]
  have h038 : weightedMaskMass a 2105640 (75284928) =
      weightedMaskMass a 3686656 (75284928) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105640, 3686656, 75284928) (by decide)]
  have h039 : weightedMaskMass a 2105922 (-71798168) =
      weightedMaskMass a 5243428 (-71798168) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2105922, 5243428, -71798168) (by decide)]
  have h040 : weightedMaskMass a 2106112 (-9499644) =
      weightedMaskMass a 2621700 (-9499644) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106112, 2621700, -9499644) (by decide)]
  have h041 : weightedMaskMass a 2106114 (21088949) =
      weightedMaskMass a 2623748 (21088949) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106114, 2623748, 21088949) (by decide)]
  have h042 : weightedMaskMass a 2106116 (35103593) =
      weightedMaskMass a 2622212 (35103593) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106116, 2622212, 35103593) (by decide)]
  have h043 : weightedMaskMass a 2106120 (-56926588) =
      weightedMaskMass a 2638084 (-56926588) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106120, 2638084, -56926588) (by decide)]
  have h044 : weightedMaskMass a 2106144 (-75306074) =
      weightedMaskMass a 3670276 (-75306074) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106144, 3670276, -75306074) (by decide)]
  have h045 : weightedMaskMass a 2106146 (170366067) =
      weightedMaskMass a 3672324 (170366067) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106146, 3672324, 170366067) (by decide)]
  have h046 : weightedMaskMass a 2106148 (-4497080) =
      weightedMaskMass a 3670788 (-4497080) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106148, 3670788, -4497080) (by decide)]
  have h047 : weightedMaskMass a 2106152 (80804879) =
      weightedMaskMass a 3686660 (80804879) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2106152, 3686660, 80804879) (by decide)]
  have h048 : weightedMaskMass a 2113824 (77254830) =
      weightedMaskMass a 3145992 (77254830) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113824, 3145992, 77254830) (by decide)]
  have h049 : weightedMaskMass a 2113826 (-62565225) =
      weightedMaskMass a 3148040 (-62565225) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113826, 3148040, -62565225) (by decide)]
  have h050 : weightedMaskMass a 2113828 (-46760302) =
      weightedMaskMass a 3146504 (-46760302) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113828, 3146504, -46760302) (by decide)]
  have h051 : weightedMaskMass a 2113832 (-22440323) =
      weightedMaskMass a 3162376 (-22440323) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113832, 3162376, -22440323) (by decide)]
  have h052 : weightedMaskMass a 2121984 (-62508518) =
      weightedMaskMass a 2621704 (-62508518) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2121984, 2621704, -62508518) (by decide)]
  have h053 : weightedMaskMass a 2121986 (52067846) =
      weightedMaskMass a 2623752 (52067846) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2121986, 2623752, 52067846) (by decide)]
  have h054 : weightedMaskMass a 2121988 (-32494145) =
      weightedMaskMass a 2622216 (-32494145) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2121988, 2622216, -32494145) (by decide)]
  have h055 : weightedMaskMass a 2121992 (-16983295) =
      weightedMaskMass a 2638088 (-16983295) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2121992, 2638088, -16983295) (by decide)]
  have h056 : weightedMaskMass a 2122016 (79688125) =
      weightedMaskMass a 3670280 (79688125) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2122016, 3670280, 79688125) (by decide)]
  have h057 : weightedMaskMass a 2122018 (131684378) =
      weightedMaskMass a 3672328 (131684378) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2122018, 3672328, 131684378) (by decide)]
  have h058 : weightedMaskMass a 2122020 (-2168886) =
      weightedMaskMass a 3670792 (-2168886) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2122020, 3670792, -2168886) (by decide)]
  have h059 : weightedMaskMass a 2122024 (-1021745) =
      weightedMaskMass a 3686664 (-1021745) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2122024, 3686664, -1021745) (by decide)]
  have h060 : weightedMaskMass a 2360832 (-74006118) =
      weightedMaskMass a 4456992 (-74006118) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2360832, 4456992, -74006118) (by decide)]
  have h061 : weightedMaskMass a 2361368 (20560368) =
      weightedMaskMass a 2623508 (20560368) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2361368, 2623508, 20560368) (by decide)]
  have h062 : weightedMaskMass a 2361380 (-18298831) =
      weightedMaskMass a 2490404 (-18298831) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2361380, 2490404, -18298831) (by decide)]
  have h063 : weightedMaskMass a 2361384 (20556380) =
      weightedMaskMass a 5801984 (20556380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2361384, 5801984, 20556380) (by decide)]
  have h064 : weightedMaskMass a 2367488 (20929933) =
      weightedMaskMass a 4194324 (20929933) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2367488, 4194324, 20929933) (by decide)]
  have h065 : weightedMaskMass a 2367496 (-149783095) =
      weightedMaskMass a 4227092 (-149783095) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2367496, 4227092, -149783095) (by decide)]
  have h066 : weightedMaskMass a 2367496 (192395234) =
      weightedMaskMass a 4718612 (192395234) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2367496, 4718612, 192395234) (by decide)]
  have h067 : weightedMaskMass a 2367504 (-20929933) =
      weightedMaskMass a 4196372 (-20929933) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2367504, 4196372, -20929933) (by decide)]
  have h068 : weightedMaskMass a 2367512 (-36736044) =
      weightedMaskMass a 4720660 (-36736044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2367512, 4720660, -36736044) (by decide)]
  have h069 : weightedMaskMass a 2368000 (-4914383) =
      weightedMaskMass a 5242900 (-4914383) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2368000, 5242900, -4914383) (by decide)]
  have h070 : weightedMaskMass a 2368008 (-28812039) =
      weightedMaskMass a 5275668 (-28812039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2368008, 5275668, -28812039) (by decide)]
  have h071 : weightedMaskMass a 2394120 (78417598) =
      weightedMaskMass a 5769248 (78417598) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2394120, 5769248, 78417598) (by decide)]
  have h072 : weightedMaskMass a 2490880 (-55713169) =
      weightedMaskMass a 3145748 (-55713169) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2490880, 3145748, -55713169) (by decide)]
  have h073 : weightedMaskMass a 2490888 (-68685793) =
      weightedMaskMass a 3178516 (-68685793) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2490888, 3178516, -68685793) (by decide)]
  have h074 : weightedMaskMass a 2506753 (124107863) =
      weightedMaskMass a 2623553 (124107863) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2506753, 2623553, 124107863) (by decide)]
  have h075 : weightedMaskMass a 2621728 (45059106) =
      weightedMaskMass a 3154176 (45059106) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2621728, 3154176, 45059106) (by decide)]
  have h076 : weightedMaskMass a 2621732 (-3027868) =
      weightedMaskMass a 3154688 (-3027868) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2621732, 3154688, -3027868) (by decide)]
  have h077 : weightedMaskMass a 2621736 (-22193415) =
      weightedMaskMass a 3170560 (-22193415) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2621736, 3170560, -22193415) (by decide)]
  have h078 : weightedMaskMass a 2622240 (-79770027) =
      weightedMaskMass a 3154180 (-79770027) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2622240, 3154180, -79770027) (by decide)]
  have h079 : weightedMaskMass a 2622244 (29311887) =
      weightedMaskMass a 3154692 (29311887) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2622244, 3154692, 29311887) (by decide)]
  have h080 : weightedMaskMass a 2622248 (-38098327) =
      weightedMaskMass a 3170564 (-38098327) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2622248, 3170564, -38098327) (by decide)]
  have h081 : weightedMaskMass a 2622976 (-20355610) =
      weightedMaskMass a 4194850 (-20355610) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2622976, 4194850, -20355610) (by decide)]
  have h082 : weightedMaskMass a 2623776 (-118180152) =
      weightedMaskMass a 3154178 (-118180152) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2623776, 3154178, -118180152) (by decide)]
  have h083 : weightedMaskMass a 2623780 (119675515) =
      weightedMaskMass a 3154690 (119675515) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2623780, 3154690, 119675515) (by decide)]
  have h084 : weightedMaskMass a 2623784 (18519142) =
      weightedMaskMass a 3170562 (18519142) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2623784, 3170562, 18519142) (by decide)]
  have h085 : weightedMaskMass a 2629696 (-67266305) =
      weightedMaskMass a 4194468 (-67266305) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629696, 4194468, -67266305) (by decide)]
  have h086 : weightedMaskMass a 2629892 (37524075) =
      weightedMaskMass a 2630400 (37524075) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629892, 2630400, 37524075) (by decide)]
  have h087 : weightedMaskMass a 2629896 (107641549) =
      weightedMaskMass a 2646272 (107641549) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629896, 2646272, 107641549) (by decide)]
  have h088 : weightedMaskMass a 2629920 (27114828) =
      weightedMaskMass a 3678464 (27114828) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629920, 3678464, 27114828) (by decide)]
  have h089 : weightedMaskMass a 2629924 (-17003538) =
      weightedMaskMass a 3678976 (-17003538) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629924, 3678976, -17003538) (by decide)]
  have h090 : weightedMaskMass a 2629928 (-104961687) =
      weightedMaskMass a 3694848 (-104961687) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2629928, 3694848, -104961687) (by decide)]
  have h091 : weightedMaskMass a 2630208 (94547934) =
      weightedMaskMass a 5243044 (94547934) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2630208, 5243044, 94547934) (by decide)]
  have h092 : weightedMaskMass a 2630408 (-152688350) =
      weightedMaskMass a 2646276 (-152688350) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2630408, 2646276, -152688350) (by decide)]
  have h093 : weightedMaskMass a 2630432 (102793740) =
      weightedMaskMass a 3678468 (102793740) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2630432, 3678468, 102793740) (by decide)]
  have h094 : weightedMaskMass a 2630436 (-95195822) =
      weightedMaskMass a 3678980 (-95195822) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2630436, 3678980, -95195822) (by decide)]
  have h095 : weightedMaskMass a 2630440 (83738908) =
      weightedMaskMass a 3694852 (83738908) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2630440, 3694852, 83738908) (by decide)]
  have h096 : weightedMaskMass a 2638112 (-389776072) =
      weightedMaskMass a 3154184 (-389776072) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2638112, 3154184, -389776072) (by decide)]
  have h097 : weightedMaskMass a 2638116 (268334061) =
      weightedMaskMass a 3154696 (268334061) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2638116, 3154696, 268334061) (by decide)]
  have h098 : weightedMaskMass a 2638120 (210850166) =
      weightedMaskMass a 3170568 (210850166) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2638120, 3170568, 210850166) (by decide)]
  have h099 : weightedMaskMass a 2646304 (318959033) =
      weightedMaskMass a 3678472 (318959033) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2646304, 3678472, 318959033) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt21 s.val : ℝ)) = (((((((weightedMaskMass a 1597732 (-861707228) + (-weightedMaskMass a 3678760 (-861707228) + weightedMaskMass a 1597736 (-269843409))) + (-weightedMaskMass a 3694632 (-269843409) + (weightedMaskMass a 1605633 (22556890) + -weightedMaskMass a 2359812 (22556890)))) + ((weightedMaskMass a 1605761 (88500468) + (-weightedMaskMass a 3408388 (88500468) + weightedMaskMass a 1622016 (88344827))) + (-weightedMaskMass a 2359840 (88344827) + (weightedMaskMass a 1622017 (-60006134) + -weightedMaskMass a 2359844 (-60006134))))) + (((weightedMaskMass a 1622020 (-66182867) + (-weightedMaskMass a 2359848 (-66182867) + weightedMaskMass a 1622144 (54202529))) + (-weightedMaskMass a 3408416 (54202529) + (weightedMaskMass a 1622145 (-192497556) + -weightedMaskMass a 3408420 (-192497556)))) + ((weightedMaskMass a 1622148 (-121363022) + (-weightedMaskMass a 3408424 (-121363022) + weightedMaskMass a 2097410 (18194022))) + ((-weightedMaskMass a 2099456 (18194022) + weightedMaskMass a 2097412 (-25603950)) + (-weightedMaskMass a 2097920 (-25603950) + weightedMaskMass a 2097416 (8389286)))))) + ((((-weightedMaskMass a 2113792 (8389286) + (weightedMaskMass a 2097440 (-17361911) + -weightedMaskMass a 3145984 (-17361911))) + (weightedMaskMass a 2097442 (-27543838) + (-weightedMaskMass a 3148032 (-27543838) + weightedMaskMass a 2097444 (17361911)))) + ((-weightedMaskMass a 3146496 (17361911) + (weightedMaskMass a 2097448 (24730232) + -weightedMaskMass a 3162368 (24730232))) + (weightedMaskMass a 2097922 (9554990) + (-weightedMaskMass a 2099460 (9554990) + weightedMaskMass a 2097928 (15461870))))) + (((-weightedMaskMass a 2113796 (15461870) + (weightedMaskMass a 2097952 (39633708) + -weightedMaskMass a 3145988 (39633708))) + (weightedMaskMass a 2097954 (-22476970) + (-weightedMaskMass a 3148036 (-22476970) + weightedMaskMass a 2097956 (-14029758)))) + ((-weightedMaskMass a 3146500 (-14029758) + (weightedMaskMass a 2097960 (-75776356) + -weightedMaskMass a 3162372 (-75776356))) + ((weightedMaskMass a 2098690 (42117041) + -weightedMaskMass a 4719136 (42117041)) + (weightedMaskMass a 2099220 (53703896) + -weightedMaskMass a 2361360 (53703896))))))) + (((((weightedMaskMass a 2099224 (13172412) + (-weightedMaskMass a 2623504 (13172412) + weightedMaskMass a 2099464 (2105700))) + (-weightedMaskMass a 2113794 (2105700) + (weightedMaskMass a 2099488 (56200577) + -weightedMaskMass a 3145986 (56200577)))) + ((weightedMaskMass a 2099492 (-28451565) + (-weightedMaskMass a 3146498 (-28451565) + weightedMaskMass a 2099496 (-9930941))) + (-weightedMaskMass a 3162370 (-9930941) + (weightedMaskMass a 2105368 (-42355273) + -weightedMaskMass a 4720656 (-42355273))))) + (((weightedMaskMass a 2105600 (34068422) + (-weightedMaskMass a 2621696 (34068422) + weightedMaskMass a 2105602 (-60940874))) + (-weightedMaskMass a 2623744 (-60940874) + (weightedMaskMass a 2105604 (-34068422) + -weightedMaskMass a 2622208 (-34068422)))) + ((weightedMaskMass a 2105608 (-91617491) + (-weightedMaskMass a 2638080 (-91617491) + weightedMaskMass a 2105632 (-29208074))) + ((-weightedMaskMass a 3670272 (-29208074) + weightedMaskMass a 2105634 (-59831666)) + (-weightedMaskMass a 3672320 (-59831666) + weightedMaskMass a 2105636 (15318148)))))) + ((((-weightedMaskMass a 3670784 (15318148) + (weightedMaskMass a 2105640 (75284928) + -weightedMaskMass a 3686656 (75284928))) + (weightedMaskMass a 2105922 (-71798168) + (-weightedMaskMass a 5243428 (-71798168) + weightedMaskMass a 2106112 (-9499644)))) + ((-weightedMaskMass a 2621700 (-9499644) + (weightedMaskMass a 2106114 (21088949) + -weightedMaskMass a 2623748 (21088949))) + (weightedMaskMass a 2106116 (35103593) + (-weightedMaskMass a 2622212 (35103593) + weightedMaskMass a 2106120 (-56926588))))) + (((-weightedMaskMass a 2638084 (-56926588) + (weightedMaskMass a 2106144 (-75306074) + -weightedMaskMass a 3670276 (-75306074))) + (weightedMaskMass a 2106146 (170366067) + (-weightedMaskMass a 3672324 (170366067) + weightedMaskMass a 2106148 (-4497080)))) + ((-weightedMaskMass a 3670788 (-4497080) + (weightedMaskMass a 2106152 (80804879) + -weightedMaskMass a 3686660 (80804879))) + ((weightedMaskMass a 2113824 (77254830) + -weightedMaskMass a 3145992 (77254830)) + (weightedMaskMass a 2113826 (-62565225) + -weightedMaskMass a 3148040 (-62565225)))))))) + ((((((weightedMaskMass a 2113828 (-46760302) + (-weightedMaskMass a 3146504 (-46760302) + weightedMaskMass a 2113832 (-22440323))) + (-weightedMaskMass a 3162376 (-22440323) + (weightedMaskMass a 2121984 (-62508518) + -weightedMaskMass a 2621704 (-62508518)))) + ((weightedMaskMass a 2121986 (52067846) + (-weightedMaskMass a 2623752 (52067846) + weightedMaskMass a 2121988 (-32494145))) + (-weightedMaskMass a 2622216 (-32494145) + (weightedMaskMass a 2121992 (-16983295) + -weightedMaskMass a 2638088 (-16983295))))) + (((weightedMaskMass a 2122016 (79688125) + (-weightedMaskMass a 3670280 (79688125) + weightedMaskMass a 2122018 (131684378))) + (-weightedMaskMass a 3672328 (131684378) + (weightedMaskMass a 2122020 (-2168886) + -weightedMaskMass a 3670792 (-2168886)))) + ((weightedMaskMass a 2122024 (-1021745) + (-weightedMaskMass a 3686664 (-1021745) + weightedMaskMass a 2360832 (-74006118))) + ((-weightedMaskMass a 4456992 (-74006118) + weightedMaskMass a 2361368 (20560368)) + (-weightedMaskMass a 2623508 (20560368) + weightedMaskMass a 2361380 (-18298831)))))) + ((((-weightedMaskMass a 2490404 (-18298831) + (weightedMaskMass a 2361384 (20556380) + -weightedMaskMass a 5801984 (20556380))) + (weightedMaskMass a 2367488 (20929933) + (-weightedMaskMass a 4194324 (20929933) + weightedMaskMass a 2367496 (-149783095)))) + ((-weightedMaskMass a 4227092 (-149783095) + (weightedMaskMass a 2367496 (192395234) + -weightedMaskMass a 4718612 (192395234))) + (weightedMaskMass a 2367504 (-20929933) + (-weightedMaskMass a 4196372 (-20929933) + weightedMaskMass a 2367512 (-36736044))))) + (((-weightedMaskMass a 4720660 (-36736044) + (weightedMaskMass a 2368000 (-4914383) + -weightedMaskMass a 5242900 (-4914383))) + (weightedMaskMass a 2368008 (-28812039) + (-weightedMaskMass a 5275668 (-28812039) + weightedMaskMass a 2394120 (78417598)))) + ((-weightedMaskMass a 5769248 (78417598) + (weightedMaskMass a 2490880 (-55713169) + -weightedMaskMass a 3145748 (-55713169))) + ((weightedMaskMass a 2490888 (-68685793) + -weightedMaskMass a 3178516 (-68685793)) + (weightedMaskMass a 2506753 (124107863) + -weightedMaskMass a 2623553 (124107863))))))) + (((((weightedMaskMass a 2621728 (45059106) + (-weightedMaskMass a 3154176 (45059106) + weightedMaskMass a 2621732 (-3027868))) + (-weightedMaskMass a 3154688 (-3027868) + (weightedMaskMass a 2621736 (-22193415) + -weightedMaskMass a 3170560 (-22193415)))) + ((weightedMaskMass a 2622240 (-79770027) + (-weightedMaskMass a 3154180 (-79770027) + weightedMaskMass a 2622244 (29311887))) + (-weightedMaskMass a 3154692 (29311887) + (weightedMaskMass a 2622248 (-38098327) + -weightedMaskMass a 3170564 (-38098327))))) + (((weightedMaskMass a 2622976 (-20355610) + (-weightedMaskMass a 4194850 (-20355610) + weightedMaskMass a 2623776 (-118180152))) + (-weightedMaskMass a 3154178 (-118180152) + (weightedMaskMass a 2623780 (119675515) + -weightedMaskMass a 3154690 (119675515)))) + ((weightedMaskMass a 2623784 (18519142) + (-weightedMaskMass a 3170562 (18519142) + weightedMaskMass a 2629696 (-67266305))) + ((-weightedMaskMass a 4194468 (-67266305) + weightedMaskMass a 2629892 (37524075)) + (-weightedMaskMass a 2630400 (37524075) + weightedMaskMass a 2629896 (107641549)))))) + ((((-weightedMaskMass a 2646272 (107641549) + (weightedMaskMass a 2629920 (27114828) + -weightedMaskMass a 3678464 (27114828))) + (weightedMaskMass a 2629924 (-17003538) + (-weightedMaskMass a 3678976 (-17003538) + weightedMaskMass a 2629928 (-104961687)))) + ((-weightedMaskMass a 3694848 (-104961687) + (weightedMaskMass a 2630208 (94547934) + -weightedMaskMass a 5243044 (94547934))) + (weightedMaskMass a 2630408 (-152688350) + (-weightedMaskMass a 2646276 (-152688350) + weightedMaskMass a 2630432 (102793740))))) + (((-weightedMaskMass a 3678468 (102793740) + (weightedMaskMass a 2630436 (-95195822) + -weightedMaskMass a 3678980 (-95195822))) + (weightedMaskMass a 2630440 (83738908) + (-weightedMaskMass a 3694852 (83738908) + weightedMaskMass a 2638112 (-389776072)))) + ((-weightedMaskMass a 3154184 (-389776072) + (weightedMaskMass a 2638116 (268334061) + -weightedMaskMass a 3154696 (268334061))) + ((weightedMaskMass a 2638120 (210850166) + -weightedMaskMass a 3170568 (210850166)) + (weightedMaskMass a 2646304 (318959033) + -weightedMaskMass a 3678472 (318959033))))))))) := by
      simp only [atomCongruenceContributionInt21, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
