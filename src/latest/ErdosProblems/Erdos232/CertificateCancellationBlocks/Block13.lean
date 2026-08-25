/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock13_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights13, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt13 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 132674 (-54652895) =
      weightedMaskMass a 196802 (-54652895) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132674, 196802, -54652895) (by decide)]
  have h001 : weightedMaskMass a 132676 (-89005170) =
      weightedMaskMass a 559172 (-89005170) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132676, 559172, -89005170) (by decide)]
  have h002 : weightedMaskMass a 135176 (-4389642) =
      weightedMaskMass a 720896 (-4389642) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (135176, 720896, -4389642) (by decide)]
  have h003 : weightedMaskMass a 135424 (1465096) =
      weightedMaskMass a 5373952 (1465096) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (135424, 5373952, 1465096) (by decide)]
  have h004 : weightedMaskMass a 135428 (7882197) =
      weightedMaskMass a 5373954 (7882197) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (135428, 5373954, 7882197) (by decide)]
  have h005 : weightedMaskMass a 135456 (-41424854) =
      weightedMaskMass a 5374464 (-41424854) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (135456, 5374464, -41424854) (by decide)]
  have h006 : weightedMaskMass a 135460 (-17991001) =
      weightedMaskMass a 5374466 (-17991001) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (135460, 5374466, -17991001) (by decide)]
  have h007 : weightedMaskMass a 136192 (-7662483) =
      weightedMaskMass a 270848 (-7662483) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136192, 270848, -7662483) (by decide)]
  have h008 : weightedMaskMass a 136192 (37669991) =
      weightedMaskMass a 524560 (37669991) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136192, 524560, 37669991) (by decide)]
  have h009 : weightedMaskMass a 136192 (-20666657) =
      weightedMaskMass a 5242896 (-20666657) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136192, 5242896, -20666657) (by decide)]
  have h010 : weightedMaskMass a 136193 (33678580) =
      weightedMaskMass a 5244944 (33678580) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136193, 5244944, 33678580) (by decide)]
  have h011 : weightedMaskMass a 136194 (-56627809) =
      weightedMaskMass a 270880 (-56627809) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136194, 270880, -56627809) (by decide)]
  have h012 : weightedMaskMass a 136194 (8953284) =
      weightedMaskMass a 540944 (8953284) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136194, 540944, 8953284) (by decide)]
  have h013 : weightedMaskMass a 136196 (6344395) =
      weightedMaskMass a 5242898 (6344395) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136196, 5242898, 6344395) (by decide)]
  have h014 : weightedMaskMass a 136258 (93590268) =
      weightedMaskMass a 540948 (93590268) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136258, 540948, 93590268) (by decide)]
  have h015 : weightedMaskMass a 147490 (-10373725) =
      weightedMaskMass a 1050664 (-10373725) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147490, 1050664, -10373725) (by decide)]
  have h016 : weightedMaskMass a 147490 (-94225593) =
      weightedMaskMass a 1064994 (-94225593) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147490, 1064994, -94225593) (by decide)]
  have h017 : weightedMaskMass a 147490 (101475423) =
      weightedMaskMass a 1083400 (101475423) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147490, 1083400, 101475423) (by decide)]
  have h018 : weightedMaskMass a 147522 (-69042213) =
      weightedMaskMass a 1097736 (-69042213) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147522, 1097736, -69042213) (by decide)]
  have h019 : weightedMaskMass a 147524 (-16452179) =
      weightedMaskMass a 544832 (-16452179) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147524, 544832, -16452179) (by decide)]
  have h020 : weightedMaskMass a 147585 (67592016) =
      weightedMaskMass a 147586 (67592016) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147585, 147586, 67592016) (by decide)]
  have h021 : weightedMaskMass a 147585 (37201265) =
      weightedMaskMass a 147588 (37201265) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147585, 147588, 37201265) (by decide)]
  have h022 : weightedMaskMass a 147712 (-20638787) =
      weightedMaskMass a 1572928 (-20638787) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147712, 1572928, -20638787) (by decide)]
  have h023 : weightedMaskMass a 147744 (28707041) =
      weightedMaskMass a 3670080 (28707041) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (147744, 3670080, 28707041) (by decide)]
  have h024 : weightedMaskMass a 148480 (-103121022) =
      weightedMaskMass a 589888 (-103121022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148480, 589888, -103121022) (by decide)]
  have h025 : weightedMaskMass a 148480 (112351296) =
      weightedMaskMass a 1056800 (112351296) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148480, 1056800, 112351296) (by decide)]
  have h026 : weightedMaskMass a 148480 (-30723307) =
      weightedMaskMass a 1572896 (-30723307) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148480, 1572896, -30723307) (by decide)]
  have h027 : weightedMaskMass a 148480 (48238576) =
      weightedMaskMass a 2129928 (48238576) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148480, 2129928, 48238576) (by decide)]
  have h028 : weightedMaskMass a 148481 (-41857133) =
      weightedMaskMass a 1056802 (-41857133) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148481, 1056802, -41857133) (by decide)]
  have h029 : weightedMaskMass a 148481 (38422243) =
      weightedMaskMass a 1574944 (38422243) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148481, 1574944, 38422243) (by decide)]
  have h030 : weightedMaskMass a 148481 (-26073574) =
      weightedMaskMass a 2131976 (-26073574) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148481, 2131976, -26073574) (by decide)]
  have h031 : weightedMaskMass a 148482 (29955509) =
      weightedMaskMass a 1056808 (29955509) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148482, 1056808, 29955509) (by decide)]
  have h032 : weightedMaskMass a 148482 (-91343143) =
      weightedMaskMass a 1589280 (-91343143) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148482, 1589280, -91343143) (by decide)]
  have h033 : weightedMaskMass a 148484 (-68064166) =
      weightedMaskMass a 1056804 (-68064166) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148484, 1056804, -68064166) (by decide)]
  have h034 : weightedMaskMass a 148484 (28710244) =
      weightedMaskMass a 1573408 (28710244) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (148484, 1573408, 28710244) (by decide)]
  have h035 : weightedMaskMass a 151554 (42685727) =
      weightedMaskMass a 1081368 (42685727) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151554, 1081368, 42685727) (by decide)]
  have h036 : weightedMaskMass a 151586 (-93017055) =
      weightedMaskMass a 1083416 (-93017055) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151586, 1083416, -93017055) (by decide)]
  have h037 : weightedMaskMass a 151618 (-460537) =
      weightedMaskMass a 1097752 (-460537) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151618, 1097752, -460537) (by decide)]
  have h038 : weightedMaskMass a 151620 (-49868738) =
      weightedMaskMass a 544836 (-49868738) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151620, 544836, -49868738) (by decide)]
  have h039 : weightedMaskMass a 151680 (-89529501) =
      weightedMaskMass a 213120 (-89529501) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (151680, 213120, -89529501) (by decide)]
  have h040 : weightedMaskMass a 163842 (77471688) =
      weightedMaskMass a 1089536 (77471688) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163842, 1089536, 77471688) (by decide)]
  have h041 : weightedMaskMass a 163842 (32968083) =
      weightedMaskMass a 1327104 (32968083) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163842, 1327104, 32968083) (by decide)]
  have h042 : weightedMaskMass a 163848 (-91343811) =
      weightedMaskMass a 278656 (-91343811) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163848, 278656, -91343811) (by decide)]
  have h043 : weightedMaskMass a 163848 (49659795) =
      weightedMaskMass a 524448 (49659795) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163848, 524448, 49659795) (by decide)]
  have h044 : weightedMaskMass a 163906 (-28538376) =
      weightedMaskMass a 1105920 (-28538376) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163906, 1105920, -28538376) (by decide)]
  have h045 : weightedMaskMass a 163908 (-26837476) =
      weightedMaskMass a 3407888 (-26837476) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163908, 3407888, -26837476) (by decide)]
  have h046 : weightedMaskMass a 163968 (-50342801) =
      weightedMaskMass a 524480 (-50342801) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (163968, 524480, -50342801) (by decide)]
  have h047 : weightedMaskMass a 164032 (142713812) =
      weightedMaskMass a 557248 (142713812) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (164032, 557248, 142713812) (by decide)]
  have h048 : weightedMaskMass a 164096 (35788376) =
      weightedMaskMass a 1183744 (35788376) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (164096, 1183744, 35788376) (by decide)]
  have h049 : weightedMaskMass a 164096 (-20393678) =
      weightedMaskMass a 5242944 (-20393678) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (164096, 5242944, -20393678) (by decide)]
  have h050 : weightedMaskMass a 164100 (-44646735) =
      weightedMaskMass a 1183746 (-44646735) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (164100, 1183746, -44646735) (by decide)]
  have h051 : weightedMaskMass a 167938 (-68006344) =
      weightedMaskMass a 1089552 (-68006344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (167938, 1089552, -68006344) (by decide)]
  have h052 : weightedMaskMass a 167940 (4604284) =
      weightedMaskMass a 5246978 (4604284) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (167940, 5246978, 4604284) (by decide)]
  have h053 : weightedMaskMass a 168002 (-47361422) =
      weightedMaskMass a 1105936 (-47361422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (168002, 1105936, -47361422) (by decide)]
  have h054 : weightedMaskMass a 168192 (5268143) =
      weightedMaskMass a 5378048 (5268143) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (168192, 5378048, 5268143) (by decide)]
  have h055 : weightedMaskMass a 168196 (-26861126) =
      weightedMaskMass a 5378050 (-26861126) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (168196, 5378050, -26861126) (by decide)]
  have h056 : weightedMaskMass a 180226 (15289893) =
      weightedMaskMass a 1089544 (15289893) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180226, 1089544, 15289893) (by decide)]
  have h057 : weightedMaskMass a 180226 (-100962860) =
      weightedMaskMass a 1327136 (-100962860) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180226, 1327136, -100962860) (by decide)]
  have h058 : weightedMaskMass a 180228 (-2579651) =
      weightedMaskMass a 1311264 (-2579651) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180228, 1311264, -2579651) (by decide)]
  have h059 : weightedMaskMass a 180228 (12201913) =
      weightedMaskMass a 1589376 (12201913) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180228, 1589376, 12201913) (by decide)]
  have h060 : weightedMaskMass a 180290 (78140884) =
      weightedMaskMass a 1105928 (78140884) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180290, 1105928, 78140884) (by decide)]
  have h061 : weightedMaskMass a 180480 (28869239) =
      weightedMaskMass a 5767232 (28869239) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (180480, 5767232, 28869239) (by decide)]
  have h062 : weightedMaskMass a 184322 (83279372) =
      weightedMaskMass a 1089560 (83279372) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (184322, 1089560, 83279372) (by decide)]
  have h063 : weightedMaskMass a 184386 (-88672406) =
      weightedMaskMass a 1105944 (-88672406) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (184386, 1105944, -88672406) (by decide)]
  have h064 : weightedMaskMass a 196648 (15079561) =
      weightedMaskMass a 524836 (15079561) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196648, 524836, 15079561) (by decide)]
  have h065 : weightedMaskMass a 196648 (-10456079) =
      weightedMaskMass a 1057284 (-10456079) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196648, 1057284, -10456079) (by decide)]
  have h066 : weightedMaskMass a 196768 (-57115854) =
      weightedMaskMass a 524868 (-57115854) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196768, 524868, -57115854) (by decide)]
  have h067 : weightedMaskMass a 196804 (-65869709) =
      weightedMaskMass a 559128 (-65869709) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (196804, 559128, -65869709) (by decide)]
  have h068 : weightedMaskMass a 197696 (52077447) =
      weightedMaskMass a 557076 (52077447) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (197696, 557076, 52077447) (by decide)]
  have h069 : weightedMaskMass a 197698 (73266182) =
      weightedMaskMass a 573460 (73266182) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (197698, 573460, 73266182) (by decide)]
  have h070 : weightedMaskMass a 197700 (-170184975) =
      weightedMaskMass a 559124 (-170184975) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (197700, 559124, -170184975) (by decide)]
  have h071 : weightedMaskMass a 200708 (40153775) =
      weightedMaskMass a 462848 (40153775) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (200708, 462848, 40153775) (by decide)]
  have h072 : weightedMaskMass a 200712 (12413005) =
      weightedMaskMass a 724992 (12413005) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (200712, 724992, 12413005) (by decide)]
  have h073 : weightedMaskMass a 201728 (-13450458) =
      weightedMaskMass a 557328 (-13450458) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (201728, 557328, -13450458) (by decide)]
  have h074 : weightedMaskMass a 201730 (57266980) =
      weightedMaskMass a 573712 (57266980) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (201730, 573712, 57266980) (by decide)]
  have h075 : weightedMaskMass a 201792 (3825236) =
      weightedMaskMass a 557332 (3825236) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (201792, 557332, 3825236) (by decide)]
  have h076 : weightedMaskMass a 201794 (-133307884) =
      weightedMaskMass a 573716 (-133307884) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (201794, 573716, -133307884) (by decide)]
  have h077 : weightedMaskMass a 212994 (-41484815) =
      weightedMaskMass a 1081608 (-41484815) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (212994, 1081608, -41484815) (by decide)]
  have h078 : weightedMaskMass a 213026 (-3371030) =
      weightedMaskMass a 1083656 (-3371030) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (213026, 1083656, -3371030) (by decide)]
  have h079 : weightedMaskMass a 213058 (145398004) =
      weightedMaskMass a 1097992 (145398004) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (213058, 1097992, 145398004) (by decide)]
  have h080 : weightedMaskMass a 217090 (-37175592) =
      weightedMaskMass a 1081624 (-37175592) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (217090, 1081624, -37175592) (by decide)]
  have h081 : weightedMaskMass a 217122 (45638456) =
      weightedMaskMass a 1083672 (45638456) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (217122, 1083672, 45638456) (by decide)]
  have h082 : weightedMaskMass a 217154 (-31679797) =
      weightedMaskMass a 1098008 (-31679797) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (217154, 1098008, -31679797) (by decide)]
  have h083 : weightedMaskMass a 229378 (-212933861) =
      weightedMaskMass a 1089792 (-212933861) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229378, 1089792, -212933861) (by decide)]
  have h084 : weightedMaskMass a 229380 (-27575369) =
      weightedMaskMass a 1310744 (-27575369) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229380, 1310744, -27575369) (by decide)]
  have h085 : weightedMaskMass a 229384 (-13949019) =
      weightedMaskMass a 524452 (-13949019) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229384, 524452, -13949019) (by decide)]
  have h086 : weightedMaskMass a 229442 (178435982) =
      weightedMaskMass a 1106176 (178435982) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229442, 1106176, 178435982) (by decide)]
  have h087 : weightedMaskMass a 229444 (69763294) =
      weightedMaskMass a 3407896 (69763294) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229444, 3407896, 69763294) (by decide)]
  have h088 : weightedMaskMass a 229504 (31650339) =
      weightedMaskMass a 524484 (31650339) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229504, 524484, 31650339) (by decide)]
  have h089 : weightedMaskMass a 229568 (-89991555) =
      weightedMaskMass a 557252 (-89991555) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (229568, 557252, -89991555) (by decide)]
  have h090 : weightedMaskMass a 233474 (170500435) =
      weightedMaskMass a 1089808 (170500435) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (233474, 1089808, 170500435) (by decide)]
  have h091 : weightedMaskMass a 233538 (-105192321) =
      weightedMaskMass a 1106192 (-105192321) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (233538, 1106192, -105192321) (by decide)]
  have h092 : weightedMaskMass a 245762 (95313954) =
      weightedMaskMass a 1089800 (95313954) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (245762, 1089800, 95313954) (by decide)]
  have h093 : weightedMaskMass a 245826 (-206760945) =
      weightedMaskMass a 1106184 (-206760945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (245826, 1106184, -206760945) (by decide)]
  have h094 : weightedMaskMass a 249858 (-36353729) =
      weightedMaskMass a 1089816 (-36353729) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (249858, 1089816, -36353729) (by decide)]
  have h095 : weightedMaskMass a 249922 (-12689630) =
      weightedMaskMass a 1106200 (-12689630) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (249922, 1106200, -12689630) (by decide)]
  have h096 : weightedMaskMass a 262273 (-82943214) =
      weightedMaskMass a 526464 (-82943214) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262273, 526464, -82943214) (by decide)]
  have h097 : weightedMaskMass a 262273 (79597541) =
      weightedMaskMass a 1069056 (79597541) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262273, 1069056, 79597541) (by decide)]
  have h098 : weightedMaskMass a 262273 (21108500) =
      weightedMaskMass a 4194824 (21108500) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262273, 4194824, 21108500) (by decide)]
  have h099 : weightedMaskMass a 262400 (29841824) =
      weightedMaskMass a 532480 (29841824) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262400, 532480, 29841824) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt13 s.val : ℝ)) = (((((((weightedMaskMass a 132674 (-54652895) + (-weightedMaskMass a 196802 (-54652895) + weightedMaskMass a 132676 (-89005170))) + (-weightedMaskMass a 559172 (-89005170) + (weightedMaskMass a 135176 (-4389642) + -weightedMaskMass a 720896 (-4389642)))) + ((weightedMaskMass a 135424 (1465096) + (-weightedMaskMass a 5373952 (1465096) + weightedMaskMass a 135428 (7882197))) + (-weightedMaskMass a 5373954 (7882197) + (weightedMaskMass a 135456 (-41424854) + -weightedMaskMass a 5374464 (-41424854))))) + (((weightedMaskMass a 135460 (-17991001) + (-weightedMaskMass a 5374466 (-17991001) + weightedMaskMass a 136192 (-7662483))) + (-weightedMaskMass a 270848 (-7662483) + (weightedMaskMass a 136192 (37669991) + -weightedMaskMass a 524560 (37669991)))) + ((weightedMaskMass a 136192 (-20666657) + (-weightedMaskMass a 5242896 (-20666657) + weightedMaskMass a 136193 (33678580))) + ((-weightedMaskMass a 5244944 (33678580) + weightedMaskMass a 136194 (-56627809)) + (-weightedMaskMass a 270880 (-56627809) + weightedMaskMass a 136194 (8953284)))))) + ((((-weightedMaskMass a 540944 (8953284) + (weightedMaskMass a 136196 (6344395) + -weightedMaskMass a 5242898 (6344395))) + (weightedMaskMass a 136258 (93590268) + (-weightedMaskMass a 540948 (93590268) + weightedMaskMass a 147490 (-10373725)))) + ((-weightedMaskMass a 1050664 (-10373725) + (weightedMaskMass a 147490 (-94225593) + -weightedMaskMass a 1064994 (-94225593))) + (weightedMaskMass a 147490 (101475423) + (-weightedMaskMass a 1083400 (101475423) + weightedMaskMass a 147522 (-69042213))))) + (((-weightedMaskMass a 1097736 (-69042213) + (weightedMaskMass a 147524 (-16452179) + -weightedMaskMass a 544832 (-16452179))) + (weightedMaskMass a 147585 (67592016) + (-weightedMaskMass a 147586 (67592016) + weightedMaskMass a 147585 (37201265)))) + ((-weightedMaskMass a 147588 (37201265) + (weightedMaskMass a 147712 (-20638787) + -weightedMaskMass a 1572928 (-20638787))) + ((weightedMaskMass a 147744 (28707041) + -weightedMaskMass a 3670080 (28707041)) + (weightedMaskMass a 148480 (-103121022) + -weightedMaskMass a 589888 (-103121022))))))) + (((((weightedMaskMass a 148480 (112351296) + (-weightedMaskMass a 1056800 (112351296) + weightedMaskMass a 148480 (-30723307))) + (-weightedMaskMass a 1572896 (-30723307) + (weightedMaskMass a 148480 (48238576) + -weightedMaskMass a 2129928 (48238576)))) + ((weightedMaskMass a 148481 (-41857133) + (-weightedMaskMass a 1056802 (-41857133) + weightedMaskMass a 148481 (38422243))) + (-weightedMaskMass a 1574944 (38422243) + (weightedMaskMass a 148481 (-26073574) + -weightedMaskMass a 2131976 (-26073574))))) + (((weightedMaskMass a 148482 (29955509) + (-weightedMaskMass a 1056808 (29955509) + weightedMaskMass a 148482 (-91343143))) + (-weightedMaskMass a 1589280 (-91343143) + (weightedMaskMass a 148484 (-68064166) + -weightedMaskMass a 1056804 (-68064166)))) + ((weightedMaskMass a 148484 (28710244) + (-weightedMaskMass a 1573408 (28710244) + weightedMaskMass a 151554 (42685727))) + ((-weightedMaskMass a 1081368 (42685727) + weightedMaskMass a 151586 (-93017055)) + (-weightedMaskMass a 1083416 (-93017055) + weightedMaskMass a 151618 (-460537)))))) + ((((-weightedMaskMass a 1097752 (-460537) + (weightedMaskMass a 151620 (-49868738) + -weightedMaskMass a 544836 (-49868738))) + (weightedMaskMass a 151680 (-89529501) + (-weightedMaskMass a 213120 (-89529501) + weightedMaskMass a 163842 (77471688)))) + ((-weightedMaskMass a 1089536 (77471688) + (weightedMaskMass a 163842 (32968083) + -weightedMaskMass a 1327104 (32968083))) + (weightedMaskMass a 163848 (-91343811) + (-weightedMaskMass a 278656 (-91343811) + weightedMaskMass a 163848 (49659795))))) + (((-weightedMaskMass a 524448 (49659795) + (weightedMaskMass a 163906 (-28538376) + -weightedMaskMass a 1105920 (-28538376))) + (weightedMaskMass a 163908 (-26837476) + (-weightedMaskMass a 3407888 (-26837476) + weightedMaskMass a 163968 (-50342801)))) + ((-weightedMaskMass a 524480 (-50342801) + (weightedMaskMass a 164032 (142713812) + -weightedMaskMass a 557248 (142713812))) + ((weightedMaskMass a 164096 (35788376) + -weightedMaskMass a 1183744 (35788376)) + (weightedMaskMass a 164096 (-20393678) + -weightedMaskMass a 5242944 (-20393678)))))))) + ((((((weightedMaskMass a 164100 (-44646735) + (-weightedMaskMass a 1183746 (-44646735) + weightedMaskMass a 167938 (-68006344))) + (-weightedMaskMass a 1089552 (-68006344) + (weightedMaskMass a 167940 (4604284) + -weightedMaskMass a 5246978 (4604284)))) + ((weightedMaskMass a 168002 (-47361422) + (-weightedMaskMass a 1105936 (-47361422) + weightedMaskMass a 168192 (5268143))) + (-weightedMaskMass a 5378048 (5268143) + (weightedMaskMass a 168196 (-26861126) + -weightedMaskMass a 5378050 (-26861126))))) + (((weightedMaskMass a 180226 (15289893) + (-weightedMaskMass a 1089544 (15289893) + weightedMaskMass a 180226 (-100962860))) + (-weightedMaskMass a 1327136 (-100962860) + (weightedMaskMass a 180228 (-2579651) + -weightedMaskMass a 1311264 (-2579651)))) + ((weightedMaskMass a 180228 (12201913) + (-weightedMaskMass a 1589376 (12201913) + weightedMaskMass a 180290 (78140884))) + ((-weightedMaskMass a 1105928 (78140884) + weightedMaskMass a 180480 (28869239)) + (-weightedMaskMass a 5767232 (28869239) + weightedMaskMass a 184322 (83279372)))))) + ((((-weightedMaskMass a 1089560 (83279372) + (weightedMaskMass a 184386 (-88672406) + -weightedMaskMass a 1105944 (-88672406))) + (weightedMaskMass a 196648 (15079561) + (-weightedMaskMass a 524836 (15079561) + weightedMaskMass a 196648 (-10456079)))) + ((-weightedMaskMass a 1057284 (-10456079) + (weightedMaskMass a 196768 (-57115854) + -weightedMaskMass a 524868 (-57115854))) + (weightedMaskMass a 196804 (-65869709) + (-weightedMaskMass a 559128 (-65869709) + weightedMaskMass a 197696 (52077447))))) + (((-weightedMaskMass a 557076 (52077447) + (weightedMaskMass a 197698 (73266182) + -weightedMaskMass a 573460 (73266182))) + (weightedMaskMass a 197700 (-170184975) + (-weightedMaskMass a 559124 (-170184975) + weightedMaskMass a 200708 (40153775)))) + ((-weightedMaskMass a 462848 (40153775) + (weightedMaskMass a 200712 (12413005) + -weightedMaskMass a 724992 (12413005))) + ((weightedMaskMass a 201728 (-13450458) + -weightedMaskMass a 557328 (-13450458)) + (weightedMaskMass a 201730 (57266980) + -weightedMaskMass a 573712 (57266980))))))) + (((((weightedMaskMass a 201792 (3825236) + (-weightedMaskMass a 557332 (3825236) + weightedMaskMass a 201794 (-133307884))) + (-weightedMaskMass a 573716 (-133307884) + (weightedMaskMass a 212994 (-41484815) + -weightedMaskMass a 1081608 (-41484815)))) + ((weightedMaskMass a 213026 (-3371030) + (-weightedMaskMass a 1083656 (-3371030) + weightedMaskMass a 213058 (145398004))) + (-weightedMaskMass a 1097992 (145398004) + (weightedMaskMass a 217090 (-37175592) + -weightedMaskMass a 1081624 (-37175592))))) + (((weightedMaskMass a 217122 (45638456) + (-weightedMaskMass a 1083672 (45638456) + weightedMaskMass a 217154 (-31679797))) + (-weightedMaskMass a 1098008 (-31679797) + (weightedMaskMass a 229378 (-212933861) + -weightedMaskMass a 1089792 (-212933861)))) + ((weightedMaskMass a 229380 (-27575369) + (-weightedMaskMass a 1310744 (-27575369) + weightedMaskMass a 229384 (-13949019))) + ((-weightedMaskMass a 524452 (-13949019) + weightedMaskMass a 229442 (178435982)) + (-weightedMaskMass a 1106176 (178435982) + weightedMaskMass a 229444 (69763294)))))) + ((((-weightedMaskMass a 3407896 (69763294) + (weightedMaskMass a 229504 (31650339) + -weightedMaskMass a 524484 (31650339))) + (weightedMaskMass a 229568 (-89991555) + (-weightedMaskMass a 557252 (-89991555) + weightedMaskMass a 233474 (170500435)))) + ((-weightedMaskMass a 1089808 (170500435) + (weightedMaskMass a 233538 (-105192321) + -weightedMaskMass a 1106192 (-105192321))) + (weightedMaskMass a 245762 (95313954) + (-weightedMaskMass a 1089800 (95313954) + weightedMaskMass a 245826 (-206760945))))) + (((-weightedMaskMass a 1106184 (-206760945) + (weightedMaskMass a 249858 (-36353729) + -weightedMaskMass a 1089816 (-36353729))) + (weightedMaskMass a 249922 (-12689630) + (-weightedMaskMass a 1106200 (-12689630) + weightedMaskMass a 262273 (-82943214)))) + ((-weightedMaskMass a 526464 (-82943214) + (weightedMaskMass a 262273 (79597541) + -weightedMaskMass a 1069056 (79597541))) + ((weightedMaskMass a 262273 (21108500) + -weightedMaskMass a 4194824 (21108500)) + (weightedMaskMass a 262400 (29841824) + -weightedMaskMass a 532480 (29841824))))))))) := by
      simp only [atomCongruenceContributionInt13, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
