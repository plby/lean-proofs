/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock08_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights08, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt08 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 32836 (143241969) =
      weightedMaskMass a 132608 (143241969) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32836, 132608, 143241969) (by decide)]
  have h001 : weightedMaskMass a 32836 (-41819812) =
      weightedMaskMass a 393728 (-41819812) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32836, 393728, -41819812) (by decide)]
  have h002 : weightedMaskMass a 32836 (-103425970) =
      weightedMaskMass a 524312 (-103425970) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32836, 524312, -103425970) (by decide)]
  have h003 : weightedMaskMass a 32836 (20643385) =
      weightedMaskMass a 3145744 (20643385) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32836, 3145744, 20643385) (by decide)]
  have h004 : weightedMaskMass a 32961 (-84686719) =
      weightedMaskMass a 37056 (-84686719) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32961, 37056, -84686719) (by decide)]
  have h005 : weightedMaskMass a 32962 (-62755972) =
      weightedMaskMass a 35008 (-62755972) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32962, 35008, -62755972) (by decide)]
  have h006 : weightedMaskMass a 32964 (-17325644) =
      weightedMaskMass a 98496 (-17325644) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32964, 98496, -17325644) (by decide)]
  have h007 : weightedMaskMass a 33032 (28300802) =
      weightedMaskMass a 135296 (28300802) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33032, 135296, 28300802) (by decide)]
  have h008 : weightedMaskMass a 33032 (-22596851) =
      weightedMaskMass a 212992 (-22596851) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33032, 212992, -22596851) (by decide)]
  have h009 : weightedMaskMass a 33040 (-42918810) =
      weightedMaskMass a 200704 (-42918810) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33040, 200704, -42918810) (by decide)]
  have h010 : weightedMaskMass a 33042 (24528811) =
      weightedMaskMass a 35088 (24528811) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33042, 35088, 24528811) (by decide)]
  have h011 : weightedMaskMass a 33042 (38536410) =
      weightedMaskMass a 200736 (38536410) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33042, 200736, 38536410) (by decide)]
  have h012 : weightedMaskMass a 33044 (-22266047) =
      weightedMaskMass a 49424 (-22266047) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33044, 49424, -22266047) (by decide)]
  have h013 : weightedMaskMass a 33044 (52951681) =
      weightedMaskMass a 200706 (52951681) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33044, 200706, 52951681) (by decide)]
  have h014 : weightedMaskMass a 33044 (88654953) =
      weightedMaskMass a 200768 (88654953) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33044, 200768, 88654953) (by decide)]
  have h015 : weightedMaskMass a 33044 (-70070135) =
      weightedMaskMass a 1081616 (-70070135) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33044, 1081616, -70070135) (by decide)]
  have h016 : weightedMaskMass a 33048 (0) =
      weightedMaskMass a 200832 (0) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33048, 200832, 0) (by decide)]
  have h017 : weightedMaskMass a 33048 (51362600) =
      weightedMaskMass a 217088 (51362600) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (33048, 217088, 51362600) (by decide)]
  have h018 : weightedMaskMass a 34825 (-55372211) =
      weightedMaskMass a 2244640 (-55372211) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34825, 2244640, -55372211) (by decide)]
  have h019 : weightedMaskMass a 671745 (-99313404) =
      weightedMaskMass a 2097316 (-99313404) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (671745, 2097316, -99313404) (by decide)]
  have h020 : weightedMaskMass a 671745 (-42832888) =
      weightedMaskMass a 2752576 (-42832888) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (671745, 2752576, -42832888) (by decide)]
  have h021 : weightedMaskMass a 34836 (-6954135) =
      weightedMaskMass a 132164 (-6954135) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34836, 132164, -6954135) (by decide)]
  have h022 : weightedMaskMass a 34836 (-149807171) =
      weightedMaskMass a 197636 (-149807171) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34836, 197636, -149807171) (by decide)]
  have h023 : weightedMaskMass a 34836 (232229622) =
      weightedMaskMass a 559108 (232229622) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34836, 559108, 232229622) (by decide)]
  have h024 : weightedMaskMass a 34836 (-139481929) =
      weightedMaskMass a 1048850 (-139481929) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34836, 1048850, -139481929) (by decide)]
  have h025 : weightedMaskMass a 34836 (-12922608) =
      weightedMaskMass a 5767680 (-12922608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34836, 5767680, -12922608) (by decide)]
  have h026 : weightedMaskMass a 34840 (-65597170) =
      weightedMaskMass a 151584 (-65597170) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34840, 151584, -65597170) (by decide)]
  have h027 : weightedMaskMass a 34840 (-850326) =
      weightedMaskMass a 196740 (-850326) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34840, 196740, -850326) (by decide)]
  have h028 : weightedMaskMass a 34881 (1225337) =
      weightedMaskMass a 91136 (1225337) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34881, 91136, 1225337) (by decide)]
  have h029 : weightedMaskMass a 34884 (-58252250) =
      weightedMaskMass a 132612 (-58252250) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34884, 132612, -58252250) (by decide)]
  have h030 : weightedMaskMass a 34884 (13904685) =
      weightedMaskMass a 3145746 (13904685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (34884, 3145746, 13904685) (by decide)]
  have h031 : weightedMaskMass a 35080 (-1589008) =
      weightedMaskMass a 213024 (-1589008) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (35080, 213024, -1589008) (by decide)]
  have h032 : weightedMaskMass a 35092 (20048265) =
      weightedMaskMass a 1081618 (20048265) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (35092, 1081618, 20048265) (by decide)]
  have h033 : weightedMaskMass a 35096 (38360774) =
      weightedMaskMass a 217120 (38360774) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (35096, 217120, 38360774) (by decide)]
  have h034 : weightedMaskMass a 36865 (10368978) =
      weightedMaskMass a 73744 (10368978) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36865, 73744, 10368978) (by decide)]
  have h035 : weightedMaskMass a 36865 (738330) =
      weightedMaskMass a 4200448 (738330) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36865, 4200448, 738330) (by decide)]
  have h036 : weightedMaskMass a 36866 (85518675) =
      weightedMaskMass a 73760 (85518675) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 73760, 85518675) (by decide)]
  have h037 : weightedMaskMass a 36866 (-14071683) =
      weightedMaskMass a 262660 (-14071683) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 262660, -14071683) (by decide)]
  have h038 : weightedMaskMass a 36866 (-98851701) =
      weightedMaskMass a 589840 (-98851701) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 589840, -98851701) (by decide)]
  have h039 : weightedMaskMass a 36866 (88070402) =
      weightedMaskMass a 1056784 (88070402) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 1056784, 88070402) (by decide)]
  have h040 : weightedMaskMass a 36866 (-34644159) =
      weightedMaskMass a 1572865 (-34644159) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 1572865, -34644159) (by decide)]
  have h041 : weightedMaskMass a 36866 (-36198983) =
      weightedMaskMass a 2129924 (-36198983) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 2129924, -36198983) (by decide)]
  have h042 : weightedMaskMass a 36866 (-57688974) =
      weightedMaskMass a 2228232 (-57688974) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36866, 2228232, -57688974) (by decide)]
  have h043 : weightedMaskMass a 36868 (109912946) =
      weightedMaskMass a 73792 (109912946) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36868, 73792, 109912946) (by decide)]
  have h044 : weightedMaskMass a 36868 (-15865947) =
      weightedMaskMass a 294916 (-15865947) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36868, 294916, -15865947) (by decide)]
  have h045 : weightedMaskMass a 36868 (-18810878) =
      weightedMaskMass a 525328 (-18810878) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36868, 525328, -18810878) (by decide)]
  have h046 : weightedMaskMass a 36868 (-90529031) =
      weightedMaskMass a 2229248 (-90529031) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36868, 2229248, -90529031) (by decide)]
  have h047 : weightedMaskMass a 36868 (-31548085) =
      weightedMaskMass a 4198402 (-31548085) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36868, 4198402, -31548085) (by decide)]
  have h048 : weightedMaskMass a 36929 (-30422801) =
      weightedMaskMass a 36993 (-30422801) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36929, 36993, -30422801) (by decide)]
  have h049 : weightedMaskMass a 36929 (19745894) =
      weightedMaskMass a 90128 (19745894) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36929, 90128, 19745894) (by decide)]
  have h050 : weightedMaskMass a 36930 (6199660) =
      weightedMaskMass a 1073168 (6199660) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36930, 1073168, 6199660) (by decide)]
  have h051 : weightedMaskMass a 36930 (47005696) =
      weightedMaskMass a 2228744 (47005696) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36930, 2228744, 47005696) (by decide)]
  have h052 : weightedMaskMass a 36930 (-38509091) =
      weightedMaskMass a 3178500 (-38509091) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36930, 3178500, -38509091) (by decide)]
  have h053 : weightedMaskMass a 36932 (18669119) =
      weightedMaskMass a 2229760 (18669119) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (36932, 2229760, 18669119) (by decide)]
  have h054 : weightedMaskMass a 37120 (-51141936) =
      weightedMaskMass a 77824 (-51141936) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (37120, 77824, -51141936) (by decide)]
  have h055 : weightedMaskMass a 37120 (-25092057) =
      weightedMaskMass a 4329472 (-25092057) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (37120, 4329472, -25092057) (by decide)]
  have h056 : weightedMaskMass a 37122 (24131443) =
      weightedMaskMass a 77856 (24131443) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (37122, 77856, 24131443) (by decide)]
  have h057 : weightedMaskMass a 37124 (41563185) =
      weightedMaskMass a 77888 (41563185) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (37124, 77888, 41563185) (by decide)]
  have h058 : weightedMaskMass a 37124 (40559202) =
      weightedMaskMass a 4329474 (40559202) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (37124, 4329474, 40559202) (by decide)]
  have h059 : weightedMaskMass a 38913 (31494903) =
      weightedMaskMass a 74768 (31494903) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38913, 74768, 31494903) (by decide)]
  have h060 : weightedMaskMass a 38913 (-131840926) =
      weightedMaskMass a 561153 (-131840926) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38913, 561153, -131840926) (by decide)]
  have h061 : weightedMaskMass a 38913 (43545730) =
      weightedMaskMass a 4233216 (43545730) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38913, 4233216, 43545730) (by decide)]
  have h062 : weightedMaskMass a 38916 (83148194) =
      weightedMaskMass a 296964 (83148194) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38916, 296964, 83148194) (by decide)]
  have h063 : weightedMaskMass a 38916 (-74716175) =
      weightedMaskMass a 2229252 (-74716175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38916, 2229252, -74716175) (by decide)]
  have h064 : weightedMaskMass a 38920 (443058) =
      weightedMaskMass a 2228356 (443058) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38920, 2228356, 443058) (by decide)]
  have h065 : weightedMaskMass a 38977 (4030904) =
      weightedMaskMass a 91152 (4030904) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38977, 91152, 4030904) (by decide)]
  have h066 : weightedMaskMass a 38980 (42102447) =
      weightedMaskMass a 2229764 (42102447) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (38980, 2229764, 42102447) (by decide)]
  have h067 : weightedMaskMass a 40960 (37021901) =
      weightedMaskMass a 163840 (37021901) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 163840, 37021901) (by decide)]
  have h068 : weightedMaskMass a 40960 (67730521) =
      weightedMaskMass a 262272 (67730521) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 262272, 67730521) (by decide)]
  have h069 : weightedMaskMass a 40960 (12329801) =
      weightedMaskMass a 524416 (12329801) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 524416, 12329801) (by decide)]
  have h070 : weightedMaskMass a 40960 (-46248223) =
      weightedMaskMass a 1052672 (-46248223) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 1052672, -46248223) (by decide)]
  have h071 : weightedMaskMass a 40960 (56859856) =
      weightedMaskMass a 1310720 (56859856) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 1310720, 56859856) (by decide)]
  have h072 : weightedMaskMass a 40960 (-18000002) =
      weightedMaskMass a 4194312 (-18000002) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 4194312, -18000002) (by decide)]
  have h073 : weightedMaskMass a 40960 (-151247873) =
      weightedMaskMass a 4194368 (-151247873) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40960, 4194368, -151247873) (by decide)]
  have h074 : weightedMaskMass a 40961 (-822759) =
      weightedMaskMass a 1052673 (-822759) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40961, 1052673, -822759) (by decide)]
  have h075 : weightedMaskMass a 40961 (18886271) =
      weightedMaskMass a 2260992 (18886271) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40961, 2260992, 18886271) (by decide)]
  have h076 : weightedMaskMass a 40961 (7293476) =
      weightedMaskMass a 4196416 (7293476) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40961, 4196416, 7293476) (by decide)]
  have h077 : weightedMaskMass a 40962 (111494839) =
      weightedMaskMass a 589952 (111494839) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40962, 589952, 111494839) (by decide)]
  have h078 : weightedMaskMass a 40962 (-13131065) =
      weightedMaskMass a 1310721 (-13131065) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40962, 1310721, -13131065) (by decide)]
  have h079 : weightedMaskMass a 40964 (-55564846) =
      weightedMaskMass a 163844 (-55564846) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 163844, -55564846) (by decide)]
  have h080 : weightedMaskMass a 40964 (50610847) =
      weightedMaskMass a 1052674 (50610847) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 1052674, 50610847) (by decide)]
  have h081 : weightedMaskMass a 40964 (8462574) =
      weightedMaskMass a 1310736 (8462574) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 1310736, 8462574) (by decide)]
  have h082 : weightedMaskMass a 40964 (-19012570) =
      weightedMaskMass a 1311232 (-19012570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 1311232, -19012570) (by decide)]
  have h083 : weightedMaskMass a 40964 (94649820) =
      weightedMaskMass a 1572992 (94649820) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 1572992, 94649820) (by decide)]
  have h084 : weightedMaskMass a 40964 (-3708889) =
      weightedMaskMass a 1576960 (-3708889) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40964, 1576960, -3708889) (by decide)]
  have h085 : weightedMaskMass a 40968 (-26798352) =
      weightedMaskMass a 180224 (-26798352) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 180224, -26798352) (by decide)]
  have h086 : weightedMaskMass a 40968 (-1509546) =
      weightedMaskMass a 262304 (-1509546) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 262304, -1509546) (by decide)]
  have h087 : weightedMaskMass a 40968 (101934195) =
      weightedMaskMass a 540800 (101934195) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 540800, 101934195) (by decide)]
  have h088 : weightedMaskMass a 40968 (-49157495) =
      weightedMaskMass a 1310752 (-49157495) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 1310752, -49157495) (by decide)]
  have h089 : weightedMaskMass a 40968 (84898071) =
      weightedMaskMass a 4227080 (84898071) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 4227080, 84898071) (by decide)]
  have h090 : weightedMaskMass a 40968 (-88881112) =
      weightedMaskMass a 4718656 (-88881112) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40968, 4718656, -88881112) (by decide)]
  have h091 : weightedMaskMass a 40969 (-49796559) =
      weightedMaskMass a 2277376 (-49796559) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40969, 2277376, -49796559) (by decide)]
  have h092 : weightedMaskMass a 40976 (-30328255) =
      weightedMaskMass a 167936 (-30328255) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40976, 167936, -30328255) (by decide)]
  have h093 : weightedMaskMass a 40976 (2496092) =
      weightedMaskMass a 5246976 (2496092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40976, 5246976, 2496092) (by decide)]
  have h094 : weightedMaskMass a 40980 (-42976483) =
      weightedMaskMass a 5771264 (-42976483) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40980, 5771264, -42976483) (by decide)]
  have h095 : weightedMaskMass a 40984 (5861069) =
      weightedMaskMass a 184320 (5861069) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (40984, 184320, 5861069) (by decide)]
  have h096 : weightedMaskMass a 41024 (-104923082) =
      weightedMaskMass a 295040 (-104923082) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41024, 295040, -104923082) (by decide)]
  have h097 : weightedMaskMass a 41216 (-57454958) =
      weightedMaskMass a 229376 (-57454958) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41216, 229376, -57454958) (by decide)]
  have h098 : weightedMaskMass a 41216 (-30405382) =
      weightedMaskMass a 524420 (-30405382) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41216, 524420, -30405382) (by decide)]
  have h099 : weightedMaskMass a 41216 (14187751) =
      weightedMaskMass a 1310728 (14187751) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (41216, 1310728, 14187751) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt08 s.val : ℝ)) = (((((((weightedMaskMass a 32836 (143241969) + (-weightedMaskMass a 132608 (143241969) + weightedMaskMass a 32836 (-41819812))) + (-weightedMaskMass a 393728 (-41819812) + (weightedMaskMass a 32836 (-103425970) + -weightedMaskMass a 524312 (-103425970)))) + ((weightedMaskMass a 32836 (20643385) + (-weightedMaskMass a 3145744 (20643385) + weightedMaskMass a 32961 (-84686719))) + (-weightedMaskMass a 37056 (-84686719) + (weightedMaskMass a 32962 (-62755972) + -weightedMaskMass a 35008 (-62755972))))) + (((weightedMaskMass a 32964 (-17325644) + (-weightedMaskMass a 98496 (-17325644) + weightedMaskMass a 33032 (28300802))) + (-weightedMaskMass a 135296 (28300802) + (weightedMaskMass a 33032 (-22596851) + -weightedMaskMass a 212992 (-22596851)))) + ((weightedMaskMass a 33040 (-42918810) + (-weightedMaskMass a 200704 (-42918810) + weightedMaskMass a 33042 (24528811))) + ((-weightedMaskMass a 35088 (24528811) + weightedMaskMass a 33042 (38536410)) + (-weightedMaskMass a 200736 (38536410) + weightedMaskMass a 33044 (-22266047)))))) + ((((-weightedMaskMass a 49424 (-22266047) + (weightedMaskMass a 33044 (52951681) + -weightedMaskMass a 200706 (52951681))) + (weightedMaskMass a 33044 (88654953) + (-weightedMaskMass a 200768 (88654953) + weightedMaskMass a 33044 (-70070135)))) + ((-weightedMaskMass a 1081616 (-70070135) + (weightedMaskMass a 33048 (0) + -weightedMaskMass a 200832 (0))) + (weightedMaskMass a 33048 (51362600) + (-weightedMaskMass a 217088 (51362600) + weightedMaskMass a 34825 (-55372211))))) + (((-weightedMaskMass a 2244640 (-55372211) + (weightedMaskMass a 671745 (-99313404) + -weightedMaskMass a 2097316 (-99313404))) + (weightedMaskMass a 671745 (-42832888) + (-weightedMaskMass a 2752576 (-42832888) + weightedMaskMass a 34836 (-6954135)))) + ((-weightedMaskMass a 132164 (-6954135) + (weightedMaskMass a 34836 (-149807171) + -weightedMaskMass a 197636 (-149807171))) + ((weightedMaskMass a 34836 (232229622) + -weightedMaskMass a 559108 (232229622)) + (weightedMaskMass a 34836 (-139481929) + -weightedMaskMass a 1048850 (-139481929))))))) + (((((weightedMaskMass a 34836 (-12922608) + (-weightedMaskMass a 5767680 (-12922608) + weightedMaskMass a 34840 (-65597170))) + (-weightedMaskMass a 151584 (-65597170) + (weightedMaskMass a 34840 (-850326) + -weightedMaskMass a 196740 (-850326)))) + ((weightedMaskMass a 34881 (1225337) + (-weightedMaskMass a 91136 (1225337) + weightedMaskMass a 34884 (-58252250))) + (-weightedMaskMass a 132612 (-58252250) + (weightedMaskMass a 34884 (13904685) + -weightedMaskMass a 3145746 (13904685))))) + (((weightedMaskMass a 35080 (-1589008) + (-weightedMaskMass a 213024 (-1589008) + weightedMaskMass a 35092 (20048265))) + (-weightedMaskMass a 1081618 (20048265) + (weightedMaskMass a 35096 (38360774) + -weightedMaskMass a 217120 (38360774)))) + ((weightedMaskMass a 36865 (10368978) + (-weightedMaskMass a 73744 (10368978) + weightedMaskMass a 36865 (738330))) + ((-weightedMaskMass a 4200448 (738330) + weightedMaskMass a 36866 (85518675)) + (-weightedMaskMass a 73760 (85518675) + weightedMaskMass a 36866 (-14071683)))))) + ((((-weightedMaskMass a 262660 (-14071683) + (weightedMaskMass a 36866 (-98851701) + -weightedMaskMass a 589840 (-98851701))) + (weightedMaskMass a 36866 (88070402) + (-weightedMaskMass a 1056784 (88070402) + weightedMaskMass a 36866 (-34644159)))) + ((-weightedMaskMass a 1572865 (-34644159) + (weightedMaskMass a 36866 (-36198983) + -weightedMaskMass a 2129924 (-36198983))) + (weightedMaskMass a 36866 (-57688974) + (-weightedMaskMass a 2228232 (-57688974) + weightedMaskMass a 36868 (109912946))))) + (((-weightedMaskMass a 73792 (109912946) + (weightedMaskMass a 36868 (-15865947) + -weightedMaskMass a 294916 (-15865947))) + (weightedMaskMass a 36868 (-18810878) + (-weightedMaskMass a 525328 (-18810878) + weightedMaskMass a 36868 (-90529031)))) + ((-weightedMaskMass a 2229248 (-90529031) + (weightedMaskMass a 36868 (-31548085) + -weightedMaskMass a 4198402 (-31548085))) + ((weightedMaskMass a 36929 (-30422801) + -weightedMaskMass a 36993 (-30422801)) + (weightedMaskMass a 36929 (19745894) + -weightedMaskMass a 90128 (19745894)))))))) + ((((((weightedMaskMass a 36930 (6199660) + (-weightedMaskMass a 1073168 (6199660) + weightedMaskMass a 36930 (47005696))) + (-weightedMaskMass a 2228744 (47005696) + (weightedMaskMass a 36930 (-38509091) + -weightedMaskMass a 3178500 (-38509091)))) + ((weightedMaskMass a 36932 (18669119) + (-weightedMaskMass a 2229760 (18669119) + weightedMaskMass a 37120 (-51141936))) + (-weightedMaskMass a 77824 (-51141936) + (weightedMaskMass a 37120 (-25092057) + -weightedMaskMass a 4329472 (-25092057))))) + (((weightedMaskMass a 37122 (24131443) + (-weightedMaskMass a 77856 (24131443) + weightedMaskMass a 37124 (41563185))) + (-weightedMaskMass a 77888 (41563185) + (weightedMaskMass a 37124 (40559202) + -weightedMaskMass a 4329474 (40559202)))) + ((weightedMaskMass a 38913 (31494903) + (-weightedMaskMass a 74768 (31494903) + weightedMaskMass a 38913 (-131840926))) + ((-weightedMaskMass a 561153 (-131840926) + weightedMaskMass a 38913 (43545730)) + (-weightedMaskMass a 4233216 (43545730) + weightedMaskMass a 38916 (83148194)))))) + ((((-weightedMaskMass a 296964 (83148194) + (weightedMaskMass a 38916 (-74716175) + -weightedMaskMass a 2229252 (-74716175))) + (weightedMaskMass a 38920 (443058) + (-weightedMaskMass a 2228356 (443058) + weightedMaskMass a 38977 (4030904)))) + ((-weightedMaskMass a 91152 (4030904) + (weightedMaskMass a 38980 (42102447) + -weightedMaskMass a 2229764 (42102447))) + (weightedMaskMass a 40960 (37021901) + (-weightedMaskMass a 163840 (37021901) + weightedMaskMass a 40960 (67730521))))) + (((-weightedMaskMass a 262272 (67730521) + (weightedMaskMass a 40960 (12329801) + -weightedMaskMass a 524416 (12329801))) + (weightedMaskMass a 40960 (-46248223) + (-weightedMaskMass a 1052672 (-46248223) + weightedMaskMass a 40960 (56859856)))) + ((-weightedMaskMass a 1310720 (56859856) + (weightedMaskMass a 40960 (-18000002) + -weightedMaskMass a 4194312 (-18000002))) + ((weightedMaskMass a 40960 (-151247873) + -weightedMaskMass a 4194368 (-151247873)) + (weightedMaskMass a 40961 (-822759) + -weightedMaskMass a 1052673 (-822759))))))) + (((((weightedMaskMass a 40961 (18886271) + (-weightedMaskMass a 2260992 (18886271) + weightedMaskMass a 40961 (7293476))) + (-weightedMaskMass a 4196416 (7293476) + (weightedMaskMass a 40962 (111494839) + -weightedMaskMass a 589952 (111494839)))) + ((weightedMaskMass a 40962 (-13131065) + (-weightedMaskMass a 1310721 (-13131065) + weightedMaskMass a 40964 (-55564846))) + (-weightedMaskMass a 163844 (-55564846) + (weightedMaskMass a 40964 (50610847) + -weightedMaskMass a 1052674 (50610847))))) + (((weightedMaskMass a 40964 (8462574) + (-weightedMaskMass a 1310736 (8462574) + weightedMaskMass a 40964 (-19012570))) + (-weightedMaskMass a 1311232 (-19012570) + (weightedMaskMass a 40964 (94649820) + -weightedMaskMass a 1572992 (94649820)))) + ((weightedMaskMass a 40964 (-3708889) + (-weightedMaskMass a 1576960 (-3708889) + weightedMaskMass a 40968 (-26798352))) + ((-weightedMaskMass a 180224 (-26798352) + weightedMaskMass a 40968 (-1509546)) + (-weightedMaskMass a 262304 (-1509546) + weightedMaskMass a 40968 (101934195)))))) + ((((-weightedMaskMass a 540800 (101934195) + (weightedMaskMass a 40968 (-49157495) + -weightedMaskMass a 1310752 (-49157495))) + (weightedMaskMass a 40968 (84898071) + (-weightedMaskMass a 4227080 (84898071) + weightedMaskMass a 40968 (-88881112)))) + ((-weightedMaskMass a 4718656 (-88881112) + (weightedMaskMass a 40969 (-49796559) + -weightedMaskMass a 2277376 (-49796559))) + (weightedMaskMass a 40976 (-30328255) + (-weightedMaskMass a 167936 (-30328255) + weightedMaskMass a 40976 (2496092))))) + (((-weightedMaskMass a 5246976 (2496092) + (weightedMaskMass a 40980 (-42976483) + -weightedMaskMass a 5771264 (-42976483))) + (weightedMaskMass a 40984 (5861069) + (-weightedMaskMass a 184320 (5861069) + weightedMaskMass a 41024 (-104923082)))) + ((-weightedMaskMass a 295040 (-104923082) + (weightedMaskMass a 41216 (-57454958) + -weightedMaskMass a 229376 (-57454958))) + ((weightedMaskMass a 41216 (-30405382) + -weightedMaskMass a 524420 (-30405382)) + (weightedMaskMass a 41216 (14187751) + -weightedMaskMass a 1310728 (14187751))))))))) := by
      simp only [atomCongruenceContributionInt08, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
