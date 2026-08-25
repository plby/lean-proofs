/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock06_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights06, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt06 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 8482 (117946394) =
      weightedMaskMass a 3672064 (117946394) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8482, 3672064, 117946394) (by decide)]
  have h001 : weightedMaskMass a 8484 (-105468340) =
      weightedMaskMass a 24612 (-105468340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8484, 24612, -105468340) (by decide)]
  have h002 : weightedMaskMass a 8484 (42184464) =
      weightedMaskMass a 34948 (42184464) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8484, 34948, 42184464) (by decide)]
  have h003 : weightedMaskMass a 8484 (81339673) =
      weightedMaskMass a 1573384 (81339673) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8484, 1573384, 81339673) (by decide)]
  have h004 : weightedMaskMass a 8484 (54923612) =
      weightedMaskMass a 3670528 (54923612) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8484, 3670528, 54923612) (by decide)]
  have h005 : weightedMaskMass a 8488 (-2513039) =
      weightedMaskMass a 3686400 (-2513039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8488, 3686400, -2513039) (by decide)]
  have h006 : weightedMaskMass a 8713 (-36656385) =
      weightedMaskMass a 606212 (-36656385) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8713, 606212, -36656385) (by decide)]
  have h007 : weightedMaskMass a 8713 (-86460639) =
      weightedMaskMass a 2146320 (-86460639) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8713, 2146320, -86460639) (by decide)]
  have h008 : weightedMaskMass a 8736 (-51876611) =
      weightedMaskMass a 16656 (-51876611) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 16656, -51876611) (by decide)]
  have h009 : weightedMaskMass a 8736 (11680769) =
      weightedMaskMass a 33028 (11680769) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 33028, 11680769) (by decide)]
  have h010 : weightedMaskMass a 8736 (-30383746) =
      weightedMaskMass a 69696 (-30383746) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 69696, -30383746) (by decide)]
  have h011 : weightedMaskMass a 8736 (-42942289) =
      weightedMaskMass a 135170 (-42942289) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 135170, -42942289) (by decide)]
  have h012 : weightedMaskMass a 8736 (-13510000) =
      weightedMaskMass a 262664 (-13510000) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 262664, -13510000) (by decide)]
  have h013 : weightedMaskMass a 8736 (-19445780) =
      weightedMaskMass a 1081360 (-19445780) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 1081360, -19445780) (by decide)]
  have h014 : weightedMaskMass a 8736 (-41691540) =
      weightedMaskMass a 1572868 (-41691540) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8736, 1572868, -41691540) (by decide)]
  have h015 : weightedMaskMass a 8738 (-94513844) =
      weightedMaskMass a 16658 (-94513844) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8738, 16658, -94513844) (by decide)]
  have h016 : weightedMaskMass a 8738 (21132814) =
      weightedMaskMass a 135202 (21132814) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8738, 135202, 21132814) (by decide)]
  have h017 : weightedMaskMass a 8738 (78486492) =
      weightedMaskMass a 1083408 (78486492) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8738, 1083408, 78486492) (by decide)]
  have h018 : weightedMaskMass a 8738 (86711789) =
      weightedMaskMass a 1574916 (86711789) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8738, 1574916, 86711789) (by decide)]
  have h019 : weightedMaskMass a 8740 (31594331) =
      weightedMaskMass a 35076 (31594331) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8740, 35076, 31594331) (by decide)]
  have h020 : weightedMaskMass a 8740 (-29886867) =
      weightedMaskMass a 1081362 (-29886867) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8740, 1081362, -29886867) (by decide)]
  have h021 : weightedMaskMass a 8740 (31251698) =
      weightedMaskMass a 1573380 (31251698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8740, 1573380, 31251698) (by decide)]
  have h022 : weightedMaskMass a 8744 (95393274) =
      weightedMaskMass a 262696 (95393274) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8744, 262696, 95393274) (by decide)]
  have h023 : weightedMaskMass a 8744 (-22779014) =
      weightedMaskMass a 1589252 (-22779014) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8744, 1589252, -22779014) (by decide)]
  have h024 : weightedMaskMass a 16660 (-8809710) =
      weightedMaskMass a 135234 (-8809710) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16660, 135234, -8809710) (by decide)]
  have h025 : weightedMaskMass a 16660 (19862691) =
      weightedMaskMass a 1081604 (19862691) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16660, 1081604, 19862691) (by decide)]
  have h026 : weightedMaskMass a 16660 (17252909) =
      weightedMaskMass a 1097744 (17252909) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16660, 1097744, 17252909) (by decide)]
  have h027 : weightedMaskMass a 8768 (-51904005) =
      weightedMaskMass a 294920 (-51904005) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8768, 294920, -51904005) (by decide)]
  have h028 : weightedMaskMass a 8768 (-88039468) =
      weightedMaskMass a 525376 (-88039468) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8768, 525376, -88039468) (by decide)]
  have h029 : weightedMaskMass a 8768 (-14971146) =
      weightedMaskMass a 5242912 (-14971146) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8768, 5242912, -14971146) (by decide)]
  have h030 : weightedMaskMass a 8770 (45253726) =
      weightedMaskMass a 5243424 (45253726) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8770, 5243424, 45253726) (by decide)]
  have h031 : weightedMaskMass a 151556 (-103460622) =
      weightedMaskMass a 528452 (-103460622) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151556, 528452, -103460622) (by decide)]
  have h032 : weightedMaskMass a 151556 (112089053) =
      weightedMaskMass a 2098752 (112089053) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151556, 2098752, 112089053) (by decide)]
  have h033 : weightedMaskMass a 8772 (-79057483) =
      weightedMaskMass a 527424 (-79057483) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8772, 527424, -79057483) (by decide)]
  have h034 : weightedMaskMass a 8964 (42904103) =
      weightedMaskMass a 2621956 (42904103) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8964, 2621956, 42904103) (by decide)]
  have h035 : weightedMaskMass a 8968 (-118595457) =
      weightedMaskMass a 114704 (-118595457) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8968, 114704, -118595457) (by decide)]
  have h036 : weightedMaskMass a 8968 (-23752685) =
      weightedMaskMass a 135233 (-23752685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8968, 135233, -23752685) (by decide)]
  have h037 : weightedMaskMass a 8968 (110128344) =
      weightedMaskMass a 2637828 (110128344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8968, 2637828, 110128344) (by decide)]
  have h038 : weightedMaskMass a 8992 (-8587632) =
      weightedMaskMass a 24848 (-8587632) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8992, 24848, -8587632) (by decide)]
  have h039 : weightedMaskMass a 8992 (329553) =
      weightedMaskMass a 102464 (329553) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8992, 102464, 329553) (by decide)]
  have h040 : weightedMaskMass a 8992 (125319442) =
      weightedMaskMass a 3670020 (125319442) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8992, 3670020, 125319442) (by decide)]
  have h041 : weightedMaskMass a 8994 (-389031) =
      weightedMaskMass a 24850 (-389031) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8994, 24850, -389031) (by decide)]
  have h042 : weightedMaskMass a 8994 (-195766498) =
      weightedMaskMass a 3672068 (-195766498) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8994, 3672068, -195766498) (by decide)]
  have h043 : weightedMaskMass a 8996 (-52211010) =
      weightedMaskMass a 3670532 (-52211010) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8996, 3670532, -52211010) (by decide)]
  have h044 : weightedMaskMass a 9000 (-28809595) =
      weightedMaskMass a 3686404 (-28809595) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9000, 3686404, -28809595) (by decide)]
  have h045 : weightedMaskMass a 9232 (-11156654) =
      weightedMaskMass a 38912 (-11156654) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9232, 38912, -11156654) (by decide)]
  have h046 : weightedMaskMass a 9232 (-26985920) =
      weightedMaskMass a 264196 (-26985920) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9232, 264196, -26985920) (by decide)]
  have h047 : weightedMaskMass a 9232 (-71659654) =
      weightedMaskMass a 268288 (-71659654) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9232, 268288, -71659654) (by decide)]
  have h048 : weightedMaskMass a 9232 (40526868) =
      weightedMaskMass a 528385 (40526868) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9232, 528385, 40526868) (by decide)]
  have h049 : weightedMaskMass a 9232 (14617654) =
      weightedMaskMass a 2228228 (14617654) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9232, 2228228, 14617654) (by decide)]
  have h050 : weightedMaskMass a 9234 (20539495) =
      weightedMaskMass a 264212 (20539495) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9234, 264212, 20539495) (by decide)]
  have h051 : weightedMaskMass a 9234 (-51160985) =
      weightedMaskMass a 268320 (-51160985) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9234, 268320, -51160985) (by decide)]
  have h052 : weightedMaskMass a 9234 (-45566307) =
      weightedMaskMass a 544769 (-45566307) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9234, 544769, -45566307) (by decide)]
  have h053 : weightedMaskMass a 9234 (47231875) =
      weightedMaskMass a 563200 (47231875) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9234, 563200, 47231875) (by decide)]
  have h054 : weightedMaskMass a 9234 (-60794216) =
      weightedMaskMass a 2228292 (-60794216) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9234, 2228292, -60794216) (by decide)]
  have h055 : weightedMaskMass a 9236 (-7322105) =
      weightedMaskMass a 264228 (-7322105) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9236, 264228, -7322105) (by decide)]
  have h056 : weightedMaskMass a 9236 (-45069380) =
      weightedMaskMass a 2228260 (-45069380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9236, 2228260, -45069380) (by decide)]
  have h057 : weightedMaskMass a 9280 (75376785) =
      weightedMaskMass a 135172 (75376785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 135172, 75376785) (by decide)]
  have h058 : weightedMaskMass a 9280 (45209722) =
      weightedMaskMass a 294928 (45209722) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 294928, 45209722) (by decide)]
  have h059 : weightedMaskMass a 9280 (9480028) =
      weightedMaskMass a 327688 (9480028) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 327688, 9480028) (by decide)]
  have h060 : weightedMaskMass a 9280 (-55102951) =
      weightedMaskMass a 331776 (-55102951) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 331776, -55102951) (by decide)]
  have h061 : weightedMaskMass a 9280 (-134505344) =
      weightedMaskMass a 525316 (-134505344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 525316, -134505344) (by decide)]
  have h062 : weightedMaskMass a 9280 (160157043) =
      weightedMaskMass a 528388 (160157043) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 528388, 160157043) (by decide)]
  have h063 : weightedMaskMass a 9280 (-104362161) =
      weightedMaskMass a 2098240 (-104362161) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 2098240, -104362161) (by decide)]
  have h064 : weightedMaskMass a 9280 (-34237020) =
      weightedMaskMass a 5242882 (-34237020) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9280, 5242882, -34237020) (by decide)]
  have h065 : weightedMaskMass a 9281 (-18359348) =
      weightedMaskMass a 348160 (-18359348) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9281, 348160, -18359348) (by decide)]
  have h066 : weightedMaskMass a 9282 (-67946115) =
      weightedMaskMass a 135236 (-67946115) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9282, 135236, -67946115) (by decide)]
  have h067 : weightedMaskMass a 9282 (20045920) =
      weightedMaskMass a 544772 (20045920) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9282, 544772, 20045920) (by decide)]
  have h068 : weightedMaskMass a 9284 (-50719729) =
      weightedMaskMass a 135204 (-50719729) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9284, 135204, -50719729) (by decide)]
  have h069 : weightedMaskMass a 9284 (59311757) =
      weightedMaskMass a 527364 (59311757) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9284, 527364, 59311757) (by decide)]
  have h070 : weightedMaskMass a 9284 (-30254247) =
      weightedMaskMass a 5243394 (-30254247) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9284, 5243394, -30254247) (by decide)]
  have h071 : weightedMaskMass a 9729 (14804630) =
      weightedMaskMass a 2131984 (14804630) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9729, 2131984, 14804630) (by decide)]
  have h072 : weightedMaskMass a 9730 (-59011210) =
      weightedMaskMass a 397344 (-59011210) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9730, 397344, -59011210) (by decide)]
  have h073 : weightedMaskMass a 9792 (1484124) =
      weightedMaskMass a 294936 (1484124) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9792, 294936, 1484124) (by decide)]
  have h074 : weightedMaskMass a 9792 (84399971) =
      weightedMaskMass a 525380 (84399971) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9792, 525380, 84399971) (by decide)]
  have h075 : weightedMaskMass a 9796 (69931264) =
      weightedMaskMass a 527428 (69931264) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (9796, 527428, 69931264) (by decide)]
  have h076 : weightedMaskMass a 12292 (12245690) =
      weightedMaskMass a 4325408 (12245690) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12292, 4325408, 12245690) (by decide)]
  have h077 : weightedMaskMass a 12296 (62563955) =
      weightedMaskMass a 4849664 (62563955) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12296, 4849664, 62563955) (by decide)]
  have h078 : weightedMaskMass a 12322 (-12964826) =
      weightedMaskMass a 20738 (-12964826) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12322, 20738, -12964826) (by decide)]
  have h079 : weightedMaskMass a 12354 (7938939) =
      weightedMaskMass a 20740 (7938939) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12354, 20740, 7938939) (by decide)]
  have h080 : weightedMaskMass a 12576 (-8125297) =
      weightedMaskMass a 28928 (-8125297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12576, 28928, -8125297) (by decide)]
  have h081 : weightedMaskMass a 12578 (32442482) =
      weightedMaskMass a 28930 (32442482) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (12578, 28930, 32442482) (by decide)]
  have h082 : weightedMaskMass a 13312 (-50127171) =
      weightedMaskMass a 274432 (-50127171) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13312, 274432, -50127171) (by decide)]
  have h083 : weightedMaskMass a 13312 (94911324) =
      weightedMaskMass a 528640 (94911324) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13312, 528640, 94911324) (by decide)]
  have h084 : weightedMaskMass a 13312 (-27252032) =
      weightedMaskMass a 4325380 (-27252032) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13312, 4325380, -27252032) (by decide)]
  have h085 : weightedMaskMass a 274433 (-22216042) =
      weightedMaskMass a 530688 (-22216042) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274433, 530688, -22216042) (by decide)]
  have h086 : weightedMaskMass a 13314 (9334311) =
      weightedMaskMass a 274464 (9334311) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13314, 274464, 9334311) (by decide)]
  have h087 : weightedMaskMass a 13314 (-51369275) =
      weightedMaskMass a 545024 (-51369275) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13314, 545024, -51369275) (by decide)]
  have h088 : weightedMaskMass a 13316 (-8159914) =
      weightedMaskMass a 4325412 (-8159914) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13316, 4325412, -8159914) (by decide)]
  have h089 : weightedMaskMass a 13376 (-102238879) =
      weightedMaskMass a 528644 (-102238879) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13376, 528644, -102238879) (by decide)]
  have h090 : weightedMaskMass a 13378 (1596693) =
      weightedMaskMass a 545028 (1596693) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (13378, 545028, 1596693) (by decide)]
  have h091 : weightedMaskMass a 16392 (-107002353) =
      weightedMaskMass a 16448 (-107002353) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16392, 16448, -107002353) (by decide)]
  have h092 : weightedMaskMass a 16393 (54775580) =
      weightedMaskMass a 16449 (54775580) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16393, 16449, 54775580) (by decide)]
  have h093 : weightedMaskMass a 16393 (-150242554) =
      weightedMaskMass a 81928 (-150242554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16393, 81928, -150242554) (by decide)]
  have h094 : weightedMaskMass a 16393 (182137931) =
      weightedMaskMass a 2113600 (182137931) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16393, 2113600, 182137931) (by decide)]
  have h095 : weightedMaskMass a 16408 (92266622) =
      weightedMaskMass a 16452 (92266622) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16408, 16452, 92266622) (by decide)]
  have h096 : weightedMaskMass a 16408 (5730072) =
      weightedMaskMass a 20544 (5730072) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16408, 20544, 5730072) (by decide)]
  have h097 : weightedMaskMass a 16418 (-98837320) =
      weightedMaskMass a 1050632 (-98837320) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16418, 1050632, -98837320) (by decide)]
  have h098 : weightedMaskMass a 16424 (62452433) =
      weightedMaskMass a 16450 (62452433) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16424, 16450, 62452433) (by decide)]
  have h099 : weightedMaskMass a 16424 (-30305784) =
      weightedMaskMass a 1064968 (-30305784) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16424, 1064968, -30305784) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt06 s.val : ℝ)) = (((((((weightedMaskMass a 8482 (117946394) + (-weightedMaskMass a 3672064 (117946394) + weightedMaskMass a 8484 (-105468340))) + (-weightedMaskMass a 24612 (-105468340) + (weightedMaskMass a 8484 (42184464) + -weightedMaskMass a 34948 (42184464)))) + ((weightedMaskMass a 8484 (81339673) + (-weightedMaskMass a 1573384 (81339673) + weightedMaskMass a 8484 (54923612))) + (-weightedMaskMass a 3670528 (54923612) + (weightedMaskMass a 8488 (-2513039) + -weightedMaskMass a 3686400 (-2513039))))) + (((weightedMaskMass a 8713 (-36656385) + (-weightedMaskMass a 606212 (-36656385) + weightedMaskMass a 8713 (-86460639))) + (-weightedMaskMass a 2146320 (-86460639) + (weightedMaskMass a 8736 (-51876611) + -weightedMaskMass a 16656 (-51876611)))) + ((weightedMaskMass a 8736 (11680769) + (-weightedMaskMass a 33028 (11680769) + weightedMaskMass a 8736 (-30383746))) + ((-weightedMaskMass a 69696 (-30383746) + weightedMaskMass a 8736 (-42942289)) + (-weightedMaskMass a 135170 (-42942289) + weightedMaskMass a 8736 (-13510000)))))) + ((((-weightedMaskMass a 262664 (-13510000) + (weightedMaskMass a 8736 (-19445780) + -weightedMaskMass a 1081360 (-19445780))) + (weightedMaskMass a 8736 (-41691540) + (-weightedMaskMass a 1572868 (-41691540) + weightedMaskMass a 8738 (-94513844)))) + ((-weightedMaskMass a 16658 (-94513844) + (weightedMaskMass a 8738 (21132814) + -weightedMaskMass a 135202 (21132814))) + (weightedMaskMass a 8738 (78486492) + (-weightedMaskMass a 1083408 (78486492) + weightedMaskMass a 8738 (86711789))))) + (((-weightedMaskMass a 1574916 (86711789) + (weightedMaskMass a 8740 (31594331) + -weightedMaskMass a 35076 (31594331))) + (weightedMaskMass a 8740 (-29886867) + (-weightedMaskMass a 1081362 (-29886867) + weightedMaskMass a 8740 (31251698)))) + ((-weightedMaskMass a 1573380 (31251698) + (weightedMaskMass a 8744 (95393274) + -weightedMaskMass a 262696 (95393274))) + ((weightedMaskMass a 8744 (-22779014) + -weightedMaskMass a 1589252 (-22779014)) + (weightedMaskMass a 16660 (-8809710) + -weightedMaskMass a 135234 (-8809710))))))) + (((((weightedMaskMass a 16660 (19862691) + (-weightedMaskMass a 1081604 (19862691) + weightedMaskMass a 16660 (17252909))) + (-weightedMaskMass a 1097744 (17252909) + (weightedMaskMass a 8768 (-51904005) + -weightedMaskMass a 294920 (-51904005)))) + ((weightedMaskMass a 8768 (-88039468) + (-weightedMaskMass a 525376 (-88039468) + weightedMaskMass a 8768 (-14971146))) + (-weightedMaskMass a 5242912 (-14971146) + (weightedMaskMass a 8770 (45253726) + -weightedMaskMass a 5243424 (45253726))))) + (((weightedMaskMass a 151556 (-103460622) + (-weightedMaskMass a 528452 (-103460622) + weightedMaskMass a 151556 (112089053))) + (-weightedMaskMass a 2098752 (112089053) + (weightedMaskMass a 8772 (-79057483) + -weightedMaskMass a 527424 (-79057483)))) + ((weightedMaskMass a 8964 (42904103) + (-weightedMaskMass a 2621956 (42904103) + weightedMaskMass a 8968 (-118595457))) + ((-weightedMaskMass a 114704 (-118595457) + weightedMaskMass a 8968 (-23752685)) + (-weightedMaskMass a 135233 (-23752685) + weightedMaskMass a 8968 (110128344)))))) + ((((-weightedMaskMass a 2637828 (110128344) + (weightedMaskMass a 8992 (-8587632) + -weightedMaskMass a 24848 (-8587632))) + (weightedMaskMass a 8992 (329553) + (-weightedMaskMass a 102464 (329553) + weightedMaskMass a 8992 (125319442)))) + ((-weightedMaskMass a 3670020 (125319442) + (weightedMaskMass a 8994 (-389031) + -weightedMaskMass a 24850 (-389031))) + (weightedMaskMass a 8994 (-195766498) + (-weightedMaskMass a 3672068 (-195766498) + weightedMaskMass a 8996 (-52211010))))) + (((-weightedMaskMass a 3670532 (-52211010) + (weightedMaskMass a 9000 (-28809595) + -weightedMaskMass a 3686404 (-28809595))) + (weightedMaskMass a 9232 (-11156654) + (-weightedMaskMass a 38912 (-11156654) + weightedMaskMass a 9232 (-26985920)))) + ((-weightedMaskMass a 264196 (-26985920) + (weightedMaskMass a 9232 (-71659654) + -weightedMaskMass a 268288 (-71659654))) + ((weightedMaskMass a 9232 (40526868) + -weightedMaskMass a 528385 (40526868)) + (weightedMaskMass a 9232 (14617654) + -weightedMaskMass a 2228228 (14617654)))))))) + ((((((weightedMaskMass a 9234 (20539495) + (-weightedMaskMass a 264212 (20539495) + weightedMaskMass a 9234 (-51160985))) + (-weightedMaskMass a 268320 (-51160985) + (weightedMaskMass a 9234 (-45566307) + -weightedMaskMass a 544769 (-45566307)))) + ((weightedMaskMass a 9234 (47231875) + (-weightedMaskMass a 563200 (47231875) + weightedMaskMass a 9234 (-60794216))) + (-weightedMaskMass a 2228292 (-60794216) + (weightedMaskMass a 9236 (-7322105) + -weightedMaskMass a 264228 (-7322105))))) + (((weightedMaskMass a 9236 (-45069380) + (-weightedMaskMass a 2228260 (-45069380) + weightedMaskMass a 9280 (75376785))) + (-weightedMaskMass a 135172 (75376785) + (weightedMaskMass a 9280 (45209722) + -weightedMaskMass a 294928 (45209722)))) + ((weightedMaskMass a 9280 (9480028) + (-weightedMaskMass a 327688 (9480028) + weightedMaskMass a 9280 (-55102951))) + ((-weightedMaskMass a 331776 (-55102951) + weightedMaskMass a 9280 (-134505344)) + (-weightedMaskMass a 525316 (-134505344) + weightedMaskMass a 9280 (160157043)))))) + ((((-weightedMaskMass a 528388 (160157043) + (weightedMaskMass a 9280 (-104362161) + -weightedMaskMass a 2098240 (-104362161))) + (weightedMaskMass a 9280 (-34237020) + (-weightedMaskMass a 5242882 (-34237020) + weightedMaskMass a 9281 (-18359348)))) + ((-weightedMaskMass a 348160 (-18359348) + (weightedMaskMass a 9282 (-67946115) + -weightedMaskMass a 135236 (-67946115))) + (weightedMaskMass a 9282 (20045920) + (-weightedMaskMass a 544772 (20045920) + weightedMaskMass a 9284 (-50719729))))) + (((-weightedMaskMass a 135204 (-50719729) + (weightedMaskMass a 9284 (59311757) + -weightedMaskMass a 527364 (59311757))) + (weightedMaskMass a 9284 (-30254247) + (-weightedMaskMass a 5243394 (-30254247) + weightedMaskMass a 9729 (14804630)))) + ((-weightedMaskMass a 2131984 (14804630) + (weightedMaskMass a 9730 (-59011210) + -weightedMaskMass a 397344 (-59011210))) + ((weightedMaskMass a 9792 (1484124) + -weightedMaskMass a 294936 (1484124)) + (weightedMaskMass a 9792 (84399971) + -weightedMaskMass a 525380 (84399971))))))) + (((((weightedMaskMass a 9796 (69931264) + (-weightedMaskMass a 527428 (69931264) + weightedMaskMass a 12292 (12245690))) + (-weightedMaskMass a 4325408 (12245690) + (weightedMaskMass a 12296 (62563955) + -weightedMaskMass a 4849664 (62563955)))) + ((weightedMaskMass a 12322 (-12964826) + (-weightedMaskMass a 20738 (-12964826) + weightedMaskMass a 12354 (7938939))) + (-weightedMaskMass a 20740 (7938939) + (weightedMaskMass a 12576 (-8125297) + -weightedMaskMass a 28928 (-8125297))))) + (((weightedMaskMass a 12578 (32442482) + (-weightedMaskMass a 28930 (32442482) + weightedMaskMass a 13312 (-50127171))) + (-weightedMaskMass a 274432 (-50127171) + (weightedMaskMass a 13312 (94911324) + -weightedMaskMass a 528640 (94911324)))) + ((weightedMaskMass a 13312 (-27252032) + (-weightedMaskMass a 4325380 (-27252032) + weightedMaskMass a 274433 (-22216042))) + ((-weightedMaskMass a 530688 (-22216042) + weightedMaskMass a 13314 (9334311)) + (-weightedMaskMass a 274464 (9334311) + weightedMaskMass a 13314 (-51369275)))))) + ((((-weightedMaskMass a 545024 (-51369275) + (weightedMaskMass a 13316 (-8159914) + -weightedMaskMass a 4325412 (-8159914))) + (weightedMaskMass a 13376 (-102238879) + (-weightedMaskMass a 528644 (-102238879) + weightedMaskMass a 13378 (1596693)))) + ((-weightedMaskMass a 545028 (1596693) + (weightedMaskMass a 16392 (-107002353) + -weightedMaskMass a 16448 (-107002353))) + (weightedMaskMass a 16393 (54775580) + (-weightedMaskMass a 16449 (54775580) + weightedMaskMass a 16393 (-150242554))))) + (((-weightedMaskMass a 81928 (-150242554) + (weightedMaskMass a 16393 (182137931) + -weightedMaskMass a 2113600 (182137931))) + (weightedMaskMass a 16408 (92266622) + (-weightedMaskMass a 16452 (92266622) + weightedMaskMass a 16408 (5730072)))) + ((-weightedMaskMass a 20544 (5730072) + (weightedMaskMass a 16418 (-98837320) + -weightedMaskMass a 1050632 (-98837320))) + ((weightedMaskMass a 16424 (62452433) + -weightedMaskMass a 16450 (62452433)) + (weightedMaskMass a 16424 (-30305784) + -weightedMaskMass a 1064968 (-30305784))))))))) := by
      simp only [atomCongruenceContributionInt06, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
