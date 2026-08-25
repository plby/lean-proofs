/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock16_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights16, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt16 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 345089 (-81518734) =
      weightedMaskMass a 2376705 (-81518734) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (345089, 2376705, -81518734) (by decide)]
  have h001 : weightedMaskMass a 345092 (58055786) =
      weightedMaskMass a 2376720 (58055786) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (345092, 2376720, 58055786) (by decide)]
  have h002 : weightedMaskMass a 345104 (-227587375) =
      weightedMaskMass a 2376708 (-227587375) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (345104, 2376708, -227587375) (by decide)]
  have h003 : weightedMaskMass a 345108 (-39404760) =
      weightedMaskMass a 2376724 (-39404760) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (345108, 2376724, -39404760) (by decide)]
  have h004 : weightedMaskMass a 360448 (-29783029) =
      weightedMaskMass a 2622464 (-29783029) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360448, 2622464, -29783029) (by decide)]
  have h005 : weightedMaskMass a 360448 (37974092) =
      weightedMaskMass a 4194338 (37974092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360448, 4194338, 37974092) (by decide)]
  have h006 : weightedMaskMass a 360449 (27557619) =
      weightedMaskMass a 2622465 (27557619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360449, 2622465, 27557619) (by decide)]
  have h007 : weightedMaskMass a 360452 (1865106) =
      weightedMaskMass a 2622480 (1865106) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360452, 2622480, 1865106) (by decide)]
  have h008 : weightedMaskMass a 360452 (45591035) =
      weightedMaskMass a 4198434 (45591035) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360452, 4198434, 45591035) (by decide)]
  have h009 : weightedMaskMass a 360456 (45249341) =
      weightedMaskMass a 2622528 (45249341) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360456, 2622528, 45249341) (by decide)]
  have h010 : weightedMaskMass a 360456 (-10733195) =
      weightedMaskMass a 5242914 (-10733195) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360456, 5242914, -10733195) (by decide)]
  have h011 : weightedMaskMass a 360457 (-53229344) =
      weightedMaskMass a 2622529 (-53229344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360457, 2622529, -53229344) (by decide)]
  have h012 : weightedMaskMass a 360464 (750150) =
      weightedMaskMass a 364544 (750150) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360464, 364544, 750150) (by decide)]
  have h013 : weightedMaskMass a 360464 (76021459) =
      weightedMaskMass a 2622468 (76021459) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360464, 2622468, 76021459) (by decide)]
  have h014 : weightedMaskMass a 360468 (-45035625) =
      weightedMaskMass a 2622484 (-45035625) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360468, 2622484, -45035625) (by decide)]
  have h015 : weightedMaskMass a 360472 (-84936028) =
      weightedMaskMass a 2622532 (-84936028) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (360472, 2622532, -84936028) (by decide)]
  have h016 : weightedMaskMass a 376832 (205219826) =
      weightedMaskMass a 2638848 (205219826) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376832, 2638848, 205219826) (by decide)]
  have h017 : weightedMaskMass a 376833 (-146483913) =
      weightedMaskMass a 2638849 (-146483913) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376833, 2638849, -146483913) (by decide)]
  have h018 : weightedMaskMass a 376836 (-80581880) =
      weightedMaskMass a 2638864 (-80581880) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376836, 2638864, -80581880) (by decide)]
  have h019 : weightedMaskMass a 376840 (-193660215) =
      weightedMaskMass a 2638912 (-193660215) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376840, 2638912, -193660215) (by decide)]
  have h020 : weightedMaskMass a 376841 (132425952) =
      weightedMaskMass a 2638913 (132425952) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376841, 2638913, 132425952) (by decide)]
  have h021 : weightedMaskMass a 376848 (-429910775) =
      weightedMaskMass a 2638852 (-429910775) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376848, 2638852, -429910775) (by decide)]
  have h022 : weightedMaskMass a 376852 (356164466) =
      weightedMaskMass a 2638868 (356164466) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376852, 2638868, 356164466) (by decide)]
  have h023 : weightedMaskMass a 376856 (387887946) =
      weightedMaskMass a 2638916 (387887946) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (376856, 2638916, 387887946) (by decide)]
  have h024 : weightedMaskMass a 393344 (0) =
      weightedMaskMass a 1052704 (0) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393344, 1052704, 0) (by decide)]
  have h025 : weightedMaskMass a 393344 (-1469047) =
      weightedMaskMass a 4194880 (-1469047) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393344, 4194880, -1469047) (by decide)]
  have h026 : weightedMaskMass a 393345 (-17902422) =
      weightedMaskMass a 1069088 (-17902422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393345, 1069088, -17902422) (by decide)]
  have h027 : weightedMaskMass a 393348 (5866000) =
      weightedMaskMass a 1054752 (5866000) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393348, 1054752, 5866000) (by decide)]
  have h028 : weightedMaskMass a 393376 (-16974608) =
      weightedMaskMass a 4719168 (-16974608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393376, 4719168, -16974608) (by decide)]
  have h029 : weightedMaskMass a 393732 (61508937) =
      weightedMaskMass a 589848 (61508937) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393732, 589848, 61508937) (by decide)]
  have h030 : weightedMaskMass a 393732 (-55610079) =
      weightedMaskMass a 2129988 (-55610079) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393732, 2129988, -55610079) (by decide)]
  have h031 : weightedMaskMass a 393736 (14443013) =
      weightedMaskMass a 3178512 (14443013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (393736, 3178512, 14443013) (by decide)]
  have h032 : weightedMaskMass a 397320 (-18940515) =
      weightedMaskMass a 720900 (-18940515) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (397320, 720900, -18940515) (by decide)]
  have h033 : weightedMaskMass a 409604 (7937264) =
      weightedMaskMass a 530496 (7937264) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (409604, 530496, 7937264) (by decide)]
  have h034 : weightedMaskMass a 409604 (-683662) =
      weightedMaskMass a 2097732 (-683662) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (409604, 2097732, -683662) (by decide)]
  have h035 : weightedMaskMass a 413697 (99138126) =
      weightedMaskMass a 2623556 (99138126) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (413697, 2623556, 99138126) (by decide)]
  have h036 : weightedMaskMass a 413700 (152194145) =
      weightedMaskMass a 530500 (152194145) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (413700, 530500, 152194145) (by decide)]
  have h037 : weightedMaskMass a 413700 (-163295084) =
      weightedMaskMass a 2098756 (-163295084) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (413700, 2098756, -163295084) (by decide)]
  have h038 : weightedMaskMass a 458760 (-3995125) =
      weightedMaskMass a 593924 (-3995125) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (458760, 593924, -3995125) (by decide)]
  have h039 : weightedMaskMass a 462856 (6925759) =
      weightedMaskMass a 724996 (6925759) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (462856, 724996, 6925759) (by decide)]
  have h040 : weightedMaskMass a 524552 (-96178631) =
      weightedMaskMass a 2121728 (-96178631) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (524552, 2121728, -96178631) (by decide)]
  have h041 : weightedMaskMass a 524580 (107171119) =
      weightedMaskMass a 3154432 (107171119) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (524580, 3154432, 107171119) (by decide)]
  have h042 : weightedMaskMass a 524584 (106862441) =
      weightedMaskMass a 3170304 (106862441) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (524584, 3170304, 106862441) (by decide)]
  have h043 : weightedMaskMass a 525064 (-19181964) =
      weightedMaskMass a 2121732 (-19181964) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525064, 2121732, -19181964) (by decide)]
  have h044 : weightedMaskMass a 525092 (-120672407) =
      weightedMaskMass a 3154436 (-120672407) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525092, 3154436, -120672407) (by decide)]
  have h045 : weightedMaskMass a 525096 (-13430035) =
      weightedMaskMass a 3170308 (-13430035) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525096, 3170308, -13430035) (by decide)]
  have h046 : weightedMaskMass a 525825 (53584324) =
      weightedMaskMass a 2100240 (53584324) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525825, 2100240, 53584324) (by decide)]
  have h047 : weightedMaskMass a 525828 (-160809205) =
      weightedMaskMass a 528420 (-160809205) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525828, 528420, -160809205) (by decide)]
  have h048 : weightedMaskMass a 525828 (58999136) =
      weightedMaskMass a 2100288 (58999136) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (525828, 2100288, 58999136) (by decide)]
  have h049 : weightedMaskMass a 526401 (101593637) =
      weightedMaskMass a 2506752 (101593637) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526401, 2506752, 101593637) (by decide)]
  have h050 : weightedMaskMass a 526468 (-79618608) =
      weightedMaskMass a 5243400 (-79618608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526468, 5243400, -79618608) (by decide)]
  have h051 : weightedMaskMass a 526596 (97974831) =
      weightedMaskMass a 2105858 (97974831) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526596, 2105858, 97974831) (by decide)]
  have h052 : weightedMaskMass a 526596 (-71311610) =
      weightedMaskMass a 5243396 (-71311610) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526596, 5243396, -71311610) (by decide)]
  have h053 : weightedMaskMass a 526600 (96178631) =
      weightedMaskMass a 2121730 (96178631) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526600, 2121730, 96178631) (by decide)]
  have h054 : weightedMaskMass a 526628 (-141664647) =
      weightedMaskMass a 3154434 (-141664647) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526628, 3154434, -141664647) (by decide)]
  have h055 : weightedMaskMass a 526632 (-127493217) =
      weightedMaskMass a 3170306 (-127493217) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (526632, 3170306, -127493217) (by decide)]
  have h056 : weightedMaskMass a 528392 (-20522264) =
      weightedMaskMass a 655872 (-20522264) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (528392, 655872, -20522264) (by decide)]
  have h057 : weightedMaskMass a 528392 (-67489199) =
      weightedMaskMass a 2097344 (-67489199) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (528392, 2097344, -67489199) (by decide)]
  have h058 : weightedMaskMass a 528392 (54214426) =
      weightedMaskMass a 3145856 (54214426) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (528392, 3145856, 54214426) (by decide)]
  have h059 : weightedMaskMass a 528424 (29573944) =
      weightedMaskMass a 2099392 (29573944) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (528424, 2099392, 29573944) (by decide)]
  have h060 : weightedMaskMass a 528449 (9971524) =
      weightedMaskMass a 2244612 (9971524) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (528449, 2244612, 9971524) (by decide)]
  have h061 : weightedMaskMass a 529412 (123679897) =
      weightedMaskMass a 2106432 (123679897) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (529412, 2106432, 123679897) (by decide)]
  have h062 : weightedMaskMass a 529472 (98194451) =
      weightedMaskMass a 2105920 (98194451) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (529472, 2105920, 98194451) (by decide)]
  have h063 : weightedMaskMass a 529472 (51564325) =
      weightedMaskMass a 5242916 (51564325) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (529472, 5242916, 51564325) (by decide)]
  have h064 : weightedMaskMass a 529476 (-95464995) =
      weightedMaskMass a 2106944 (-95464995) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (529476, 2106944, -95464995) (by decide)]
  have h065 : weightedMaskMass a 530440 (14911091) =
      weightedMaskMass a 655873 (14911091) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (530440, 655873, 14911091) (by decide)]
  have h066 : weightedMaskMass a 530440 (-3153924) =
      weightedMaskMass a 2097348 (-3153924) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (530440, 2097348, -3153924) (by decide)]
  have h067 : weightedMaskMass a 530468 (-122889273) =
      weightedMaskMass a 2100292 (-122889273) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (530468, 2100292, -122889273) (by decide)]
  have h068 : weightedMaskMass a 530472 (2655941) =
      weightedMaskMass a 2099396 (2655941) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (530472, 2099396, 2655941) (by decide)]
  have h069 : weightedMaskMass a 530497 (-71299771) =
      weightedMaskMass a 2506756 (-71299771) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (530497, 2506756, -71299771) (by decide)]
  have h070 : weightedMaskMass a 531456 (136320069) =
      weightedMaskMass a 2105412 (136320069) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (531456, 2105412, 136320069) (by decide)]
  have h071 : weightedMaskMass a 531460 (-157377788) =
      weightedMaskMass a 2106436 (-157377788) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (531460, 2106436, -157377788) (by decide)]
  have h072 : weightedMaskMass a 531520 (-134589361) =
      weightedMaskMass a 2105924 (-134589361) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (531520, 2105924, -134589361) (by decide)]
  have h073 : weightedMaskMass a 531524 (199137167) =
      weightedMaskMass a 2106948 (199137167) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (531524, 2106948, 199137167) (by decide)]
  have h074 : weightedMaskMass a 532489 (-101106595) =
      weightedMaskMass a 614400 (-101106595) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532489, 614400, -101106595) (by decide)]
  have h075 : weightedMaskMass a 532516 (45809088) =
      weightedMaskMass a 1581568 (45809088) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532516, 1581568, 45809088) (by decide)]
  have h076 : weightedMaskMass a 532520 (64125608) =
      weightedMaskMass a 1597440 (64125608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532520, 1597440, 64125608) (by decide)]
  have h077 : weightedMaskMass a 532544 (-69413267) =
      weightedMaskMass a 4194464 (-69413267) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532544, 4194464, -69413267) (by decide)]
  have h078 : weightedMaskMass a 532740 (124771958) =
      weightedMaskMass a 2630144 (124771958) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532740, 2630144, 124771958) (by decide)]
  have h079 : weightedMaskMass a 532740 (-63849989) =
      weightedMaskMass a 5243012 (-63849989) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532740, 5243012, -63849989) (by decide)]
  have h080 : weightedMaskMass a 532744 (25430570) =
      weightedMaskMass a 2646016 (25430570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532744, 2646016, 25430570) (by decide)]
  have h081 : weightedMaskMass a 532772 (-164488091) =
      weightedMaskMass a 3678720 (-164488091) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532772, 3678720, -164488091) (by decide)]
  have h082 : weightedMaskMass a 532776 (-100641207) =
      weightedMaskMass a 3694592 (-100641207) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (532776, 3694592, -100641207) (by decide)]
  have h083 : weightedMaskMass a 533000 (-113992140) =
      weightedMaskMass a 548868 (-113992140) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533000, 548868, -113992140) (by decide)]
  have h084 : weightedMaskMass a 533000 (-52818984) =
      weightedMaskMass a 5275776 (-52818984) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533000, 5275776, -52818984) (by decide)]
  have h085 : weightedMaskMass a 533001 (260531065) =
      weightedMaskMass a 614404 (260531065) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533001, 614404, 260531065) (by decide)]
  have h086 : weightedMaskMass a 533028 (-28971390) =
      weightedMaskMass a 1581572 (-28971390) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533028, 1581572, -28971390) (by decide)]
  have h087 : weightedMaskMass a 533032 (69672297) =
      weightedMaskMass a 1597444 (69672297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533032, 1597444, 69672297) (by decide)]
  have h088 : weightedMaskMass a 533056 (66433737) =
      weightedMaskMass a 5243040 (66433737) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533056, 5243040, 66433737) (by decide)]
  have h089 : weightedMaskMass a 533252 (-61809067) =
      weightedMaskMass a 2630148 (-61809067) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533252, 2630148, -61809067) (by decide)]
  have h090 : weightedMaskMass a 533256 (127315994) =
      weightedMaskMass a 2646020 (127315994) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533256, 2646020, 127315994) (by decide)]
  have h091 : weightedMaskMass a 533284 (133570209) =
      weightedMaskMass a 3678724 (133570209) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533284, 3678724, 133570209) (by decide)]
  have h092 : weightedMaskMass a 533288 (-30177168) =
      weightedMaskMass a 3694596 (-30177168) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533288, 3694596, -30177168) (by decide)]
  have h093 : weightedMaskMass a 533504 (7459639) =
      weightedMaskMass a 4194434 (7459639) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533504, 4194434, 7459639) (by decide)]
  have h094 : weightedMaskMass a 533508 (-34366992) =
      weightedMaskMass a 5243010 (-34366992) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (533508, 5243010, -34366992) (by decide)]
  have h095 : weightedMaskMass a 540804 (17761082) =
      weightedMaskMass a 1310760 (17761082) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (540804, 1310760, 17761082) (by decide)]
  have h096 : weightedMaskMass a 540804 (94830295) =
      weightedMaskMass a 5275656 (94830295) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (540804, 5275656, 94830295) (by decide)]
  have h097 : weightedMaskMass a 540936 (104381524) =
      weightedMaskMass a 2121736 (104381524) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (540936, 2121736, 104381524) (by decide)]
  have h098 : weightedMaskMass a 540964 (-256038076) =
      weightedMaskMass a 3154440 (-256038076) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (540964, 3154440, -256038076) (by decide)]
  have h099 : weightedMaskMass a 540968 (-254853616) =
      weightedMaskMass a 3170312 (-254853616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (540968, 3170312, -254853616) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt16 s.val : ℝ)) = (((((((weightedMaskMass a 345089 (-81518734) + (-weightedMaskMass a 2376705 (-81518734) + weightedMaskMass a 345092 (58055786))) + (-weightedMaskMass a 2376720 (58055786) + (weightedMaskMass a 345104 (-227587375) + -weightedMaskMass a 2376708 (-227587375)))) + ((weightedMaskMass a 345108 (-39404760) + (-weightedMaskMass a 2376724 (-39404760) + weightedMaskMass a 360448 (-29783029))) + (-weightedMaskMass a 2622464 (-29783029) + (weightedMaskMass a 360448 (37974092) + -weightedMaskMass a 4194338 (37974092))))) + (((weightedMaskMass a 360449 (27557619) + (-weightedMaskMass a 2622465 (27557619) + weightedMaskMass a 360452 (1865106))) + (-weightedMaskMass a 2622480 (1865106) + (weightedMaskMass a 360452 (45591035) + -weightedMaskMass a 4198434 (45591035)))) + ((weightedMaskMass a 360456 (45249341) + (-weightedMaskMass a 2622528 (45249341) + weightedMaskMass a 360456 (-10733195))) + ((-weightedMaskMass a 5242914 (-10733195) + weightedMaskMass a 360457 (-53229344)) + (-weightedMaskMass a 2622529 (-53229344) + weightedMaskMass a 360464 (750150)))))) + ((((-weightedMaskMass a 364544 (750150) + (weightedMaskMass a 360464 (76021459) + -weightedMaskMass a 2622468 (76021459))) + (weightedMaskMass a 360468 (-45035625) + (-weightedMaskMass a 2622484 (-45035625) + weightedMaskMass a 360472 (-84936028)))) + ((-weightedMaskMass a 2622532 (-84936028) + (weightedMaskMass a 376832 (205219826) + -weightedMaskMass a 2638848 (205219826))) + (weightedMaskMass a 376833 (-146483913) + (-weightedMaskMass a 2638849 (-146483913) + weightedMaskMass a 376836 (-80581880))))) + (((-weightedMaskMass a 2638864 (-80581880) + (weightedMaskMass a 376840 (-193660215) + -weightedMaskMass a 2638912 (-193660215))) + (weightedMaskMass a 376841 (132425952) + (-weightedMaskMass a 2638913 (132425952) + weightedMaskMass a 376848 (-429910775)))) + ((-weightedMaskMass a 2638852 (-429910775) + (weightedMaskMass a 376852 (356164466) + -weightedMaskMass a 2638868 (356164466))) + ((weightedMaskMass a 376856 (387887946) + -weightedMaskMass a 2638916 (387887946)) + (weightedMaskMass a 393344 (0) + -weightedMaskMass a 1052704 (0))))))) + (((((weightedMaskMass a 393344 (-1469047) + (-weightedMaskMass a 4194880 (-1469047) + weightedMaskMass a 393345 (-17902422))) + (-weightedMaskMass a 1069088 (-17902422) + (weightedMaskMass a 393348 (5866000) + -weightedMaskMass a 1054752 (5866000)))) + ((weightedMaskMass a 393376 (-16974608) + (-weightedMaskMass a 4719168 (-16974608) + weightedMaskMass a 393732 (61508937))) + (-weightedMaskMass a 589848 (61508937) + (weightedMaskMass a 393732 (-55610079) + -weightedMaskMass a 2129988 (-55610079))))) + (((weightedMaskMass a 393736 (14443013) + (-weightedMaskMass a 3178512 (14443013) + weightedMaskMass a 397320 (-18940515))) + (-weightedMaskMass a 720900 (-18940515) + (weightedMaskMass a 409604 (7937264) + -weightedMaskMass a 530496 (7937264)))) + ((weightedMaskMass a 409604 (-683662) + (-weightedMaskMass a 2097732 (-683662) + weightedMaskMass a 413697 (99138126))) + ((-weightedMaskMass a 2623556 (99138126) + weightedMaskMass a 413700 (152194145)) + (-weightedMaskMass a 530500 (152194145) + weightedMaskMass a 413700 (-163295084)))))) + ((((-weightedMaskMass a 2098756 (-163295084) + (weightedMaskMass a 458760 (-3995125) + -weightedMaskMass a 593924 (-3995125))) + (weightedMaskMass a 462856 (6925759) + (-weightedMaskMass a 724996 (6925759) + weightedMaskMass a 524552 (-96178631)))) + ((-weightedMaskMass a 2121728 (-96178631) + (weightedMaskMass a 524580 (107171119) + -weightedMaskMass a 3154432 (107171119))) + (weightedMaskMass a 524584 (106862441) + (-weightedMaskMass a 3170304 (106862441) + weightedMaskMass a 525064 (-19181964))))) + (((-weightedMaskMass a 2121732 (-19181964) + (weightedMaskMass a 525092 (-120672407) + -weightedMaskMass a 3154436 (-120672407))) + (weightedMaskMass a 525096 (-13430035) + (-weightedMaskMass a 3170308 (-13430035) + weightedMaskMass a 525825 (53584324)))) + ((-weightedMaskMass a 2100240 (53584324) + (weightedMaskMass a 525828 (-160809205) + -weightedMaskMass a 528420 (-160809205))) + ((weightedMaskMass a 525828 (58999136) + -weightedMaskMass a 2100288 (58999136)) + (weightedMaskMass a 526401 (101593637) + -weightedMaskMass a 2506752 (101593637)))))))) + ((((((weightedMaskMass a 526468 (-79618608) + (-weightedMaskMass a 5243400 (-79618608) + weightedMaskMass a 526596 (97974831))) + (-weightedMaskMass a 2105858 (97974831) + (weightedMaskMass a 526596 (-71311610) + -weightedMaskMass a 5243396 (-71311610)))) + ((weightedMaskMass a 526600 (96178631) + (-weightedMaskMass a 2121730 (96178631) + weightedMaskMass a 526628 (-141664647))) + (-weightedMaskMass a 3154434 (-141664647) + (weightedMaskMass a 526632 (-127493217) + -weightedMaskMass a 3170306 (-127493217))))) + (((weightedMaskMass a 528392 (-20522264) + (-weightedMaskMass a 655872 (-20522264) + weightedMaskMass a 528392 (-67489199))) + (-weightedMaskMass a 2097344 (-67489199) + (weightedMaskMass a 528392 (54214426) + -weightedMaskMass a 3145856 (54214426)))) + ((weightedMaskMass a 528424 (29573944) + (-weightedMaskMass a 2099392 (29573944) + weightedMaskMass a 528449 (9971524))) + ((-weightedMaskMass a 2244612 (9971524) + weightedMaskMass a 529412 (123679897)) + (-weightedMaskMass a 2106432 (123679897) + weightedMaskMass a 529472 (98194451)))))) + ((((-weightedMaskMass a 2105920 (98194451) + (weightedMaskMass a 529472 (51564325) + -weightedMaskMass a 5242916 (51564325))) + (weightedMaskMass a 529476 (-95464995) + (-weightedMaskMass a 2106944 (-95464995) + weightedMaskMass a 530440 (14911091)))) + ((-weightedMaskMass a 655873 (14911091) + (weightedMaskMass a 530440 (-3153924) + -weightedMaskMass a 2097348 (-3153924))) + (weightedMaskMass a 530468 (-122889273) + (-weightedMaskMass a 2100292 (-122889273) + weightedMaskMass a 530472 (2655941))))) + (((-weightedMaskMass a 2099396 (2655941) + (weightedMaskMass a 530497 (-71299771) + -weightedMaskMass a 2506756 (-71299771))) + (weightedMaskMass a 531456 (136320069) + (-weightedMaskMass a 2105412 (136320069) + weightedMaskMass a 531460 (-157377788)))) + ((-weightedMaskMass a 2106436 (-157377788) + (weightedMaskMass a 531520 (-134589361) + -weightedMaskMass a 2105924 (-134589361))) + ((weightedMaskMass a 531524 (199137167) + -weightedMaskMass a 2106948 (199137167)) + (weightedMaskMass a 532489 (-101106595) + -weightedMaskMass a 614400 (-101106595))))))) + (((((weightedMaskMass a 532516 (45809088) + (-weightedMaskMass a 1581568 (45809088) + weightedMaskMass a 532520 (64125608))) + (-weightedMaskMass a 1597440 (64125608) + (weightedMaskMass a 532544 (-69413267) + -weightedMaskMass a 4194464 (-69413267)))) + ((weightedMaskMass a 532740 (124771958) + (-weightedMaskMass a 2630144 (124771958) + weightedMaskMass a 532740 (-63849989))) + (-weightedMaskMass a 5243012 (-63849989) + (weightedMaskMass a 532744 (25430570) + -weightedMaskMass a 2646016 (25430570))))) + (((weightedMaskMass a 532772 (-164488091) + (-weightedMaskMass a 3678720 (-164488091) + weightedMaskMass a 532776 (-100641207))) + (-weightedMaskMass a 3694592 (-100641207) + (weightedMaskMass a 533000 (-113992140) + -weightedMaskMass a 548868 (-113992140)))) + ((weightedMaskMass a 533000 (-52818984) + (-weightedMaskMass a 5275776 (-52818984) + weightedMaskMass a 533001 (260531065))) + ((-weightedMaskMass a 614404 (260531065) + weightedMaskMass a 533028 (-28971390)) + (-weightedMaskMass a 1581572 (-28971390) + weightedMaskMass a 533032 (69672297)))))) + ((((-weightedMaskMass a 1597444 (69672297) + (weightedMaskMass a 533056 (66433737) + -weightedMaskMass a 5243040 (66433737))) + (weightedMaskMass a 533252 (-61809067) + (-weightedMaskMass a 2630148 (-61809067) + weightedMaskMass a 533256 (127315994)))) + ((-weightedMaskMass a 2646020 (127315994) + (weightedMaskMass a 533284 (133570209) + -weightedMaskMass a 3678724 (133570209))) + (weightedMaskMass a 533288 (-30177168) + (-weightedMaskMass a 3694596 (-30177168) + weightedMaskMass a 533504 (7459639))))) + (((-weightedMaskMass a 4194434 (7459639) + (weightedMaskMass a 533508 (-34366992) + -weightedMaskMass a 5243010 (-34366992))) + (weightedMaskMass a 540804 (17761082) + (-weightedMaskMass a 1310760 (17761082) + weightedMaskMass a 540804 (94830295)))) + ((-weightedMaskMass a 5275656 (94830295) + (weightedMaskMass a 540936 (104381524) + -weightedMaskMass a 2121736 (104381524))) + ((weightedMaskMass a 540964 (-256038076) + -weightedMaskMass a 3154440 (-256038076)) + (weightedMaskMass a 540968 (-254853616) + -weightedMaskMass a 3170312 (-254853616))))))))) := by
      simp only [atomCongruenceContributionInt16, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
