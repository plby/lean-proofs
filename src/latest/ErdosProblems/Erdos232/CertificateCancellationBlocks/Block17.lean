/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock17_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights17, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt17 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 544833 (-31501190) =
      weightedMaskMass a 2244676 (-31501190) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (544833, 2244676, -31501190) (by decide)]
  have h001 : weightedMaskMass a 545792 (60425400) =
      weightedMaskMass a 2106370 (60425400) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (545792, 2106370, 60425400) (by decide)]
  have h002 : weightedMaskMass a 545793 (-47067159) =
      weightedMaskMass a 2106386 (-47067159) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (545793, 2106386, -47067159) (by decide)]
  have h003 : weightedMaskMass a 545796 (-70616451) =
      weightedMaskMass a 2106434 (-70616451) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (545796, 2106434, -70616451) (by decide)]
  have h004 : weightedMaskMass a 548873 (-8205531) =
      weightedMaskMass a 614408 (-8205531) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548873, 614408, -8205531) (by decide)]
  have h005 : weightedMaskMass a 548900 (-132833775) =
      weightedMaskMass a 1581576 (-132833775) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548900, 1581576, -132833775) (by decide)]
  have h006 : weightedMaskMass a 548904 (-75943119) =
      weightedMaskMass a 1597448 (-75943119) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548904, 1597448, -75943119) (by decide)]
  have h007 : weightedMaskMass a 549124 (-283013733) =
      weightedMaskMass a 2630152 (-283013733) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549124, 2630152, -283013733) (by decide)]
  have h008 : weightedMaskMass a 549124 (87681353) =
      weightedMaskMass a 5275780 (87681353) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549124, 5275780, 87681353) (by decide)]
  have h009 : weightedMaskMass a 549128 (-65063959) =
      weightedMaskMass a 2646024 (-65063959) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549128, 2646024, -65063959) (by decide)]
  have h010 : weightedMaskMass a 549156 (442188685) =
      weightedMaskMass a 3678728 (442188685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549156, 3678728, 442188685) (by decide)]
  have h011 : weightedMaskMass a 549160 (319238600) =
      weightedMaskMass a 3694600 (319238600) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549160, 3694600, 319238600) (by decide)]
  have h012 : weightedMaskMass a 549888 (7396385) =
      weightedMaskMass a 4227202 (7396385) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549888, 4227202, 7396385) (by decide)]
  have h013 : weightedMaskMass a 549892 (40799038) =
      weightedMaskMass a 5275778 (40799038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (549892, 5275778, 40799038) (by decide)]
  have h014 : weightedMaskMass a 557065 (91506070) =
      weightedMaskMass a 557121 (91506070) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (557065, 557121, 91506070) (by decide)]
  have h015 : weightedMaskMass a 557185 (-7311044) =
      weightedMaskMass a 3407876 (-7311044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (557185, 3407876, -7311044) (by decide)]
  have h016 : weightedMaskMass a 557185 (36911019) =
      weightedMaskMass a 4231232 (36911019) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (557185, 4231232, 36911019) (by decide)]
  have h017 : weightedMaskMass a 559232 (-49060233) =
      weightedMaskMass a 4719112 (-49060233) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (559232, 4719112, -49060233) (by decide)]
  have h018 : weightedMaskMass a 559236 (51737878) =
      weightedMaskMass a 5767688 (51737878) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (559236, 5767688, 51737878) (by decide)]
  have h019 : weightedMaskMass a 559360 (-32303039) =
      weightedMaskMass a 4719108 (-32303039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (559360, 4719108, -32303039) (by decide)]
  have h020 : weightedMaskMass a 559364 (102114563) =
      weightedMaskMass a 5767684 (102114563) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (559364, 5767684, 102114563) (by decide)]
  have h021 : weightedMaskMass a 561160 (36755565) =
      weightedMaskMass a 2228416 (36755565) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (561160, 2228416, 36755565) (by decide)]
  have h022 : weightedMaskMass a 561220 (-59013063) =
      weightedMaskMass a 2229824 (-59013063) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (561220, 2229824, -59013063) (by decide)]
  have h023 : weightedMaskMass a 563208 (-46149022) =
      weightedMaskMass a 2228420 (-46149022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (563208, 2228420, -46149022) (by decide)]
  have h024 : weightedMaskMass a 563264 (11714616) =
      weightedMaskMass a 2228804 (11714616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (563264, 2228804, 11714616) (by decide)]
  have h025 : weightedMaskMass a 563268 (42028529) =
      weightedMaskMass a 2229828 (42028529) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (563268, 2229828, 42028529) (by decide)]
  have h026 : weightedMaskMass a 565248 (-32140952) =
      weightedMaskMass a 1310976 (-32140952) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565248, 1310976, -32140952) (by decide)]
  have h027 : weightedMaskMass a 565248 (90479175) =
      weightedMaskMass a 4718720 (90479175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565248, 4718720, 90479175) (by decide)]
  have h028 : weightedMaskMass a 565252 (28136506) =
      weightedMaskMass a 1310992 (28136506) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565252, 1310992, 28136506) (by decide)]
  have h029 : weightedMaskMass a 565252 (-66844302) =
      weightedMaskMass a 5767296 (-66844302) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565252, 5767296, -66844302) (by decide)]
  have h030 : weightedMaskMass a 565256 (46030814) =
      weightedMaskMass a 1311008 (46030814) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565256, 1311008, 46030814) (by decide)]
  have h031 : weightedMaskMass a 565504 (-38588123) =
      weightedMaskMass a 4718724 (-38588123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565504, 4718724, -38588123) (by decide)]
  have h032 : weightedMaskMass a 565508 (-23751116) =
      weightedMaskMass a 5767300 (-23751116) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (565508, 5767300, -23751116) (by decide)]
  have h033 : weightedMaskMass a 573448 (68550328) =
      weightedMaskMass a 573504 (68550328) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573448, 573504, 68550328) (by decide)]
  have h034 : weightedMaskMass a 573449 (-124890860) =
      weightedMaskMass a 573505 (-124890860) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573449, 573505, -124890860) (by decide)]
  have h035 : weightedMaskMass a 573464 (-111879445) =
      weightedMaskMass a 573508 (-111879445) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573464, 573508, -111879445) (by decide)]
  have h036 : weightedMaskMass a 573568 (15453807) =
      weightedMaskMass a 3407904 (15453807) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573568, 3407904, 15453807) (by decide)]
  have h037 : weightedMaskMass a 573568 (-98037854) =
      weightedMaskMass a 4751368 (-98037854) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573568, 4751368, -98037854) (by decide)]
  have h038 : weightedMaskMass a 573568 (97521971) =
      weightedMaskMass a 4751424 (97521971) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573568, 4751424, 97521971) (by decide)]
  have h039 : weightedMaskMass a 573569 (62039892) =
      weightedMaskMass a 3407908 (62039892) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573569, 3407908, 62039892) (by decide)]
  have h040 : weightedMaskMass a 573569 (-82672373) =
      weightedMaskMass a 4755520 (-82672373) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573569, 4755520, -82672373) (by decide)]
  have h041 : weightedMaskMass a 573572 (70581305) =
      weightedMaskMass a 3407912 (70581305) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573572, 3407912, 70581305) (by decide)]
  have h042 : weightedMaskMass a 573572 (-137935146) =
      weightedMaskMass a 5799944 (-137935146) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (573572, 5799944, -137935146) (by decide)]
  have h043 : weightedMaskMass a 581632 (-75623152) =
      weightedMaskMass a 4751488 (-75623152) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (581632, 4751488, -75623152) (by decide)]
  have h044 : weightedMaskMass a 581636 (84356081) =
      weightedMaskMass a 5800064 (84356081) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (581636, 5800064, 84356081) (by decide)]
  have h045 : weightedMaskMass a 581888 (88241565) =
      weightedMaskMass a 4751492 (88241565) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (581888, 4751492, 88241565) (by decide)]
  have h046 : weightedMaskMass a 581892 (5152574) =
      weightedMaskMass a 5800068 (5152574) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (581892, 5800068, 5152574) (by decide)]
  have h047 : weightedMaskMass a 589844 (-33073763) =
      weightedMaskMass a 2129940 (-33073763) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589844, 2129940, -33073763) (by decide)]
  have h048 : weightedMaskMass a 589844 (-63589318) =
      weightedMaskMass a 2490376 (-63589318) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589844, 2490376, -63589318) (by decide)]
  have h049 : weightedMaskMass a 589856 (60548526) =
      weightedMaskMass a 1056769 (60548526) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589856, 1056769, 60548526) (by decide)]
  have h050 : weightedMaskMass a 589856 (-6806797) =
      weightedMaskMass a 2129922 (-6806797) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589856, 2129922, -6806797) (by decide)]
  have h051 : weightedMaskMass a 589860 (12832657) =
      weightedMaskMass a 593952 (12832657) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589860, 593952, 12832657) (by decide)]
  have h052 : weightedMaskMass a 589860 (-28788789) =
      weightedMaskMass a 1057281 (-28788789) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589860, 1057281, -28788789) (by decide)]
  have h053 : weightedMaskMass a 589860 (-35672137) =
      weightedMaskMass a 2129938 (-35672137) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589860, 2129938, -35672137) (by decide)]
  have h054 : weightedMaskMass a 589864 (108665340) =
      weightedMaskMass a 1073153 (108665340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589864, 1073153, 108665340) (by decide)]
  have h055 : weightedMaskMass a 589864 (-114067455) =
      weightedMaskMass a 2129986 (-114067455) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589864, 2129986, -114067455) (by decide)]
  have h056 : weightedMaskMass a 589864 (-41826993) =
      weightedMaskMass a 3178498 (-41826993) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589864, 3178498, -41826993) (by decide)]
  have h057 : weightedMaskMass a 589889 (-73335506) =
      weightedMaskMass a 2129929 (-73335506) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589889, 2129929, -73335506) (by decide)]
  have h058 : weightedMaskMass a 589892 (7675817) =
      weightedMaskMass a 2129944 (7675817) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (589892, 2129944, 7675817) (by decide)]
  have h059 : weightedMaskMass a 590080 (-75700325) =
      weightedMaskMass a 2105345 (-75700325) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590080, 2105345, -75700325) (by decide)]
  have h060 : weightedMaskMass a 590084 (74373859) =
      weightedMaskMass a 2105857 (74373859) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590084, 2105857, 74373859) (by decide)]
  have h061 : weightedMaskMass a 590088 (121983997) =
      weightedMaskMass a 2121729 (121983997) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590088, 2121729, 121983997) (by decide)]
  have h062 : weightedMaskMass a 590112 (172600105) =
      weightedMaskMass a 3153921 (172600105) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590112, 3153921, 172600105) (by decide)]
  have h063 : weightedMaskMass a 590116 (-114490118) =
      weightedMaskMass a 3154433 (-114490118) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590116, 3154433, -114490118) (by decide)]
  have h064 : weightedMaskMass a 590120 (-167577990) =
      weightedMaskMass a 3170305 (-167577990) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590120, 3170305, -167577990) (by decide)]
  have h065 : weightedMaskMass a 590849 (14993111) =
      weightedMaskMass a 2392065 (14993111) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590849, 2392065, 14993111) (by decide)]
  have h066 : weightedMaskMass a 590864 (-32312432) =
      weightedMaskMass a 2392068 (-32312432) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590864, 2392068, -32312432) (by decide)]
  have h067 : weightedMaskMass a 590864 (40629961) =
      weightedMaskMass a 4231170 (40629961) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590864, 4231170, 40629961) (by decide)]
  have h068 : weightedMaskMass a 590868 (110715173) =
      weightedMaskMass a 2392084 (110715173) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590868, 2392084, 110715173) (by decide)]
  have h069 : weightedMaskMass a 590912 (-17003199) =
      weightedMaskMass a 2392072 (-17003199) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590912, 2392072, -17003199) (by decide)]
  have h070 : weightedMaskMass a 590912 (18902640) =
      weightedMaskMass a 5767200 (18902640) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590912, 5767200, 18902640) (by decide)]
  have h071 : weightedMaskMass a 590913 (-45238731) =
      weightedMaskMass a 2392073 (-45238731) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590913, 2392073, -45238731) (by decide)]
  have h072 : weightedMaskMass a 590916 (65579978) =
      weightedMaskMass a 2392088 (65579978) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (590916, 2392088, 65579978) (by decide)]
  have h073 : weightedMaskMass a 593928 (-70389438) =
      weightedMaskMass a 655876 (-70389438) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (593928, 655876, -70389438) (by decide)]
  have h074 : weightedMaskMass a 593984 (-156347531) =
      weightedMaskMass a 1057312 (-156347531) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (593984, 1057312, -156347531) (by decide)]
  have h075 : weightedMaskMass a 593984 (101315597) =
      weightedMaskMass a 1572900 (101315597) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (593984, 1572900, 101315597) (by decide)]
  have h076 : weightedMaskMass a 594944 (-119392289) =
      weightedMaskMass a 4227090 (-119392289) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (594944, 4227090, -119392289) (by decide)]
  have h077 : weightedMaskMass a 594944 (122917174) =
      weightedMaskMass a 4718628 (122917174) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (594944, 4718628, 122917174) (by decide)]
  have h078 : weightedMaskMass a 595008 (-41518962) =
      weightedMaskMass a 5767204 (-41518962) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (595008, 5767204, -41518962) (by decide)]
  have h079 : weightedMaskMass a 598025 (52190380) =
      weightedMaskMass a 614401 (52190380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598025, 614401, 52190380) (by decide)]
  have h080 : weightedMaskMass a 598048 (19968934) =
      weightedMaskMass a 1581057 (19968934) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598048, 1581057, 19968934) (by decide)]
  have h081 : weightedMaskMass a 598052 (-92186945) =
      weightedMaskMass a 1581569 (-92186945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598052, 1581569, -92186945) (by decide)]
  have h082 : weightedMaskMass a 598056 (10861208) =
      weightedMaskMass a 1597441 (10861208) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598056, 1597441, 10861208) (by decide)]
  have h083 : weightedMaskMass a 598272 (102265232) =
      weightedMaskMass a 2629633 (102265232) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598272, 2629633, 102265232) (by decide)]
  have h084 : weightedMaskMass a 598276 (-114726063) =
      weightedMaskMass a 2630145 (-114726063) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598276, 2630145, -114726063) (by decide)]
  have h085 : weightedMaskMass a 598280 (-91682200) =
      weightedMaskMass a 2646017 (-91682200) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598280, 2646017, -91682200) (by decide)]
  have h086 : weightedMaskMass a 598304 (-133509158) =
      weightedMaskMass a 3678209 (-133509158) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598304, 3678209, -133509158) (by decide)]
  have h087 : weightedMaskMass a 598308 (127900585) =
      weightedMaskMass a 3678721 (127900585) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598308, 3678721, 127900585) (by decide)]
  have h088 : weightedMaskMass a 598312 (104741867) =
      weightedMaskMass a 3694593 (104741867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (598312, 3694593, 104741867) (by decide)]
  have h089 : weightedMaskMass a 606224 (136931181) =
      weightedMaskMass a 2146308 (136931181) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606224, 2146308, 136931181) (by decide)]
  have h090 : weightedMaskMass a 606228 (23251092) =
      weightedMaskMass a 2146324 (23251092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606228, 2146324, 23251092) (by decide)]
  have h091 : weightedMaskMass a 606232 (-71495772) =
      weightedMaskMass a 2146372 (-71495772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606232, 2146372, -71495772) (by decide)]
  have h092 : weightedMaskMass a 606240 (159186475) =
      weightedMaskMass a 1056777 (159186475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606240, 1056777, 159186475) (by decide)]
  have h093 : weightedMaskMass a 606240 (-51939690) =
      weightedMaskMass a 2146306 (-51939690) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606240, 2146306, -51939690) (by decide)]
  have h094 : weightedMaskMass a 606244 (-200637413) =
      weightedMaskMass a 1057289 (-200637413) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606244, 1057289, -200637413) (by decide)]
  have h095 : weightedMaskMass a 606244 (146692050) =
      weightedMaskMass a 2146322 (146692050) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606244, 2146322, 146692050) (by decide)]
  have h096 : weightedMaskMass a 606248 (-147696378) =
      weightedMaskMass a 1073161 (-147696378) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606248, 1073161, -147696378) (by decide)]
  have h097 : weightedMaskMass a 606248 (218039743) =
      weightedMaskMass a 2146370 (218039743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606248, 2146370, 218039743) (by decide)]
  have h098 : weightedMaskMass a 606272 (-1879928) =
      weightedMaskMass a 2146312 (-1879928) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606272, 2146312, -1879928) (by decide)]
  have h099 : weightedMaskMass a 606273 (-35512012) =
      weightedMaskMass a 2146313 (-35512012) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606273, 2146313, -35512012) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt17 s.val : ℝ)) = (((((((weightedMaskMass a 544833 (-31501190) + (-weightedMaskMass a 2244676 (-31501190) + weightedMaskMass a 545792 (60425400))) + (-weightedMaskMass a 2106370 (60425400) + (weightedMaskMass a 545793 (-47067159) + -weightedMaskMass a 2106386 (-47067159)))) + ((weightedMaskMass a 545796 (-70616451) + (-weightedMaskMass a 2106434 (-70616451) + weightedMaskMass a 548873 (-8205531))) + (-weightedMaskMass a 614408 (-8205531) + (weightedMaskMass a 548900 (-132833775) + -weightedMaskMass a 1581576 (-132833775))))) + (((weightedMaskMass a 548904 (-75943119) + (-weightedMaskMass a 1597448 (-75943119) + weightedMaskMass a 549124 (-283013733))) + (-weightedMaskMass a 2630152 (-283013733) + (weightedMaskMass a 549124 (87681353) + -weightedMaskMass a 5275780 (87681353)))) + ((weightedMaskMass a 549128 (-65063959) + (-weightedMaskMass a 2646024 (-65063959) + weightedMaskMass a 549156 (442188685))) + ((-weightedMaskMass a 3678728 (442188685) + weightedMaskMass a 549160 (319238600)) + (-weightedMaskMass a 3694600 (319238600) + weightedMaskMass a 549888 (7396385)))))) + ((((-weightedMaskMass a 4227202 (7396385) + (weightedMaskMass a 549892 (40799038) + -weightedMaskMass a 5275778 (40799038))) + (weightedMaskMass a 557065 (91506070) + (-weightedMaskMass a 557121 (91506070) + weightedMaskMass a 557185 (-7311044)))) + ((-weightedMaskMass a 3407876 (-7311044) + (weightedMaskMass a 557185 (36911019) + -weightedMaskMass a 4231232 (36911019))) + (weightedMaskMass a 559232 (-49060233) + (-weightedMaskMass a 4719112 (-49060233) + weightedMaskMass a 559236 (51737878))))) + (((-weightedMaskMass a 5767688 (51737878) + (weightedMaskMass a 559360 (-32303039) + -weightedMaskMass a 4719108 (-32303039))) + (weightedMaskMass a 559364 (102114563) + (-weightedMaskMass a 5767684 (102114563) + weightedMaskMass a 561160 (36755565)))) + ((-weightedMaskMass a 2228416 (36755565) + (weightedMaskMass a 561220 (-59013063) + -weightedMaskMass a 2229824 (-59013063))) + ((weightedMaskMass a 563208 (-46149022) + -weightedMaskMass a 2228420 (-46149022)) + (weightedMaskMass a 563264 (11714616) + -weightedMaskMass a 2228804 (11714616))))))) + (((((weightedMaskMass a 563268 (42028529) + (-weightedMaskMass a 2229828 (42028529) + weightedMaskMass a 565248 (-32140952))) + (-weightedMaskMass a 1310976 (-32140952) + (weightedMaskMass a 565248 (90479175) + -weightedMaskMass a 4718720 (90479175)))) + ((weightedMaskMass a 565252 (28136506) + (-weightedMaskMass a 1310992 (28136506) + weightedMaskMass a 565252 (-66844302))) + (-weightedMaskMass a 5767296 (-66844302) + (weightedMaskMass a 565256 (46030814) + -weightedMaskMass a 1311008 (46030814))))) + (((weightedMaskMass a 565504 (-38588123) + (-weightedMaskMass a 4718724 (-38588123) + weightedMaskMass a 565508 (-23751116))) + (-weightedMaskMass a 5767300 (-23751116) + (weightedMaskMass a 573448 (68550328) + -weightedMaskMass a 573504 (68550328)))) + ((weightedMaskMass a 573449 (-124890860) + (-weightedMaskMass a 573505 (-124890860) + weightedMaskMass a 573464 (-111879445))) + ((-weightedMaskMass a 573508 (-111879445) + weightedMaskMass a 573568 (15453807)) + (-weightedMaskMass a 3407904 (15453807) + weightedMaskMass a 573568 (-98037854)))))) + ((((-weightedMaskMass a 4751368 (-98037854) + (weightedMaskMass a 573568 (97521971) + -weightedMaskMass a 4751424 (97521971))) + (weightedMaskMass a 573569 (62039892) + (-weightedMaskMass a 3407908 (62039892) + weightedMaskMass a 573569 (-82672373)))) + ((-weightedMaskMass a 4755520 (-82672373) + (weightedMaskMass a 573572 (70581305) + -weightedMaskMass a 3407912 (70581305))) + (weightedMaskMass a 573572 (-137935146) + (-weightedMaskMass a 5799944 (-137935146) + weightedMaskMass a 581632 (-75623152))))) + (((-weightedMaskMass a 4751488 (-75623152) + (weightedMaskMass a 581636 (84356081) + -weightedMaskMass a 5800064 (84356081))) + (weightedMaskMass a 581888 (88241565) + (-weightedMaskMass a 4751492 (88241565) + weightedMaskMass a 581892 (5152574)))) + ((-weightedMaskMass a 5800068 (5152574) + (weightedMaskMass a 589844 (-33073763) + -weightedMaskMass a 2129940 (-33073763))) + ((weightedMaskMass a 589844 (-63589318) + -weightedMaskMass a 2490376 (-63589318)) + (weightedMaskMass a 589856 (60548526) + -weightedMaskMass a 1056769 (60548526)))))))) + ((((((weightedMaskMass a 589856 (-6806797) + (-weightedMaskMass a 2129922 (-6806797) + weightedMaskMass a 589860 (12832657))) + (-weightedMaskMass a 593952 (12832657) + (weightedMaskMass a 589860 (-28788789) + -weightedMaskMass a 1057281 (-28788789)))) + ((weightedMaskMass a 589860 (-35672137) + (-weightedMaskMass a 2129938 (-35672137) + weightedMaskMass a 589864 (108665340))) + (-weightedMaskMass a 1073153 (108665340) + (weightedMaskMass a 589864 (-114067455) + -weightedMaskMass a 2129986 (-114067455))))) + (((weightedMaskMass a 589864 (-41826993) + (-weightedMaskMass a 3178498 (-41826993) + weightedMaskMass a 589889 (-73335506))) + (-weightedMaskMass a 2129929 (-73335506) + (weightedMaskMass a 589892 (7675817) + -weightedMaskMass a 2129944 (7675817)))) + ((weightedMaskMass a 590080 (-75700325) + (-weightedMaskMass a 2105345 (-75700325) + weightedMaskMass a 590084 (74373859))) + ((-weightedMaskMass a 2105857 (74373859) + weightedMaskMass a 590088 (121983997)) + (-weightedMaskMass a 2121729 (121983997) + weightedMaskMass a 590112 (172600105)))))) + ((((-weightedMaskMass a 3153921 (172600105) + (weightedMaskMass a 590116 (-114490118) + -weightedMaskMass a 3154433 (-114490118))) + (weightedMaskMass a 590120 (-167577990) + (-weightedMaskMass a 3170305 (-167577990) + weightedMaskMass a 590849 (14993111)))) + ((-weightedMaskMass a 2392065 (14993111) + (weightedMaskMass a 590864 (-32312432) + -weightedMaskMass a 2392068 (-32312432))) + (weightedMaskMass a 590864 (40629961) + (-weightedMaskMass a 4231170 (40629961) + weightedMaskMass a 590868 (110715173))))) + (((-weightedMaskMass a 2392084 (110715173) + (weightedMaskMass a 590912 (-17003199) + -weightedMaskMass a 2392072 (-17003199))) + (weightedMaskMass a 590912 (18902640) + (-weightedMaskMass a 5767200 (18902640) + weightedMaskMass a 590913 (-45238731)))) + ((-weightedMaskMass a 2392073 (-45238731) + (weightedMaskMass a 590916 (65579978) + -weightedMaskMass a 2392088 (65579978))) + ((weightedMaskMass a 593928 (-70389438) + -weightedMaskMass a 655876 (-70389438)) + (weightedMaskMass a 593984 (-156347531) + -weightedMaskMass a 1057312 (-156347531))))))) + (((((weightedMaskMass a 593984 (101315597) + (-weightedMaskMass a 1572900 (101315597) + weightedMaskMass a 594944 (-119392289))) + (-weightedMaskMass a 4227090 (-119392289) + (weightedMaskMass a 594944 (122917174) + -weightedMaskMass a 4718628 (122917174)))) + ((weightedMaskMass a 595008 (-41518962) + (-weightedMaskMass a 5767204 (-41518962) + weightedMaskMass a 598025 (52190380))) + (-weightedMaskMass a 614401 (52190380) + (weightedMaskMass a 598048 (19968934) + -weightedMaskMass a 1581057 (19968934))))) + (((weightedMaskMass a 598052 (-92186945) + (-weightedMaskMass a 1581569 (-92186945) + weightedMaskMass a 598056 (10861208))) + (-weightedMaskMass a 1597441 (10861208) + (weightedMaskMass a 598272 (102265232) + -weightedMaskMass a 2629633 (102265232)))) + ((weightedMaskMass a 598276 (-114726063) + (-weightedMaskMass a 2630145 (-114726063) + weightedMaskMass a 598280 (-91682200))) + ((-weightedMaskMass a 2646017 (-91682200) + weightedMaskMass a 598304 (-133509158)) + (-weightedMaskMass a 3678209 (-133509158) + weightedMaskMass a 598308 (127900585)))))) + ((((-weightedMaskMass a 3678721 (127900585) + (weightedMaskMass a 598312 (104741867) + -weightedMaskMass a 3694593 (104741867))) + (weightedMaskMass a 606224 (136931181) + (-weightedMaskMass a 2146308 (136931181) + weightedMaskMass a 606228 (23251092)))) + ((-weightedMaskMass a 2146324 (23251092) + (weightedMaskMass a 606232 (-71495772) + -weightedMaskMass a 2146372 (-71495772))) + (weightedMaskMass a 606240 (159186475) + (-weightedMaskMass a 1056777 (159186475) + weightedMaskMass a 606240 (-51939690))))) + (((-weightedMaskMass a 2146306 (-51939690) + (weightedMaskMass a 606244 (-200637413) + -weightedMaskMass a 1057289 (-200637413))) + (weightedMaskMass a 606244 (146692050) + (-weightedMaskMass a 2146322 (146692050) + weightedMaskMass a 606248 (-147696378)))) + ((-weightedMaskMass a 1073161 (-147696378) + (weightedMaskMass a 606248 (218039743) + -weightedMaskMass a 2146370 (218039743))) + ((weightedMaskMass a 606272 (-1879928) + -weightedMaskMass a 2146312 (-1879928)) + (weightedMaskMass a 606273 (-35512012) + -weightedMaskMass a 2146313 (-35512012))))))))) := by
      simp only [atomCongruenceContributionInt17, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
