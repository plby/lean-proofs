/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock03_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights03, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt03 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 1042 (-20036047) =
      weightedMaskMass a 262164 (-20036047) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 262164, -20036047) (by decide)]
  have h001 : weightedMaskMass a 1042 (-1983902) =
      weightedMaskMass a 262180 (-1983902) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 262180, -1983902) (by decide)]
  have h002 : weightedMaskMass a 1042 (21515549) =
      weightedMaskMass a 264224 (21515549) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 264224, 21515549) (by decide)]
  have h003 : weightedMaskMass a 1042 (163938698) =
      weightedMaskMass a 540673 (163938698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 540673, 163938698) (by decide)]
  have h004 : weightedMaskMass a 1042 (23477841) =
      weightedMaskMass a 561152 (23477841) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 561152, 23477841) (by decide)]
  have h005 : weightedMaskMass a 1042 (129895489) =
      weightedMaskMass a 1049344 (129895489) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 1049344, 129895489) (by decide)]
  have h006 : weightedMaskMass a 1042 (-4345683) =
      weightedMaskMass a 2097188 (-4345683) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 2097188, -4345683) (by decide)]
  have h007 : weightedMaskMass a 1042 (-61907302) =
      weightedMaskMass a 2228256 (-61907302) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 2228256, -61907302) (by decide)]
  have h008 : weightedMaskMass a 1042 (-83713936) =
      weightedMaskMass a 2228288 (-83713936) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 2228288, -83713936) (by decide)]
  have h009 : weightedMaskMass a 1042 (-4187886) =
      weightedMaskMass a 4229120 (-4187886) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 4229120, -4187886) (by decide)]
  have h010 : weightedMaskMass a 1042 (73494146) =
      weightedMaskMass a 4722688 (73494146) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 4722688, 73494146) (by decide)]
  have h011 : weightedMaskMass a 1537 (-81423618) =
      weightedMaskMass a 2099216 (-81423618) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1537, 2099216, -81423618) (by decide)]
  have h012 : weightedMaskMass a 1538 (-102083583) =
      weightedMaskMass a 2068 (-102083583) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 2068, -102083583) (by decide)]
  have h013 : weightedMaskMass a 1538 (-27099418) =
      weightedMaskMass a 3073 (-27099418) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 3073, -27099418) (by decide)]
  have h014 : weightedMaskMass a 1538 (-160310755) =
      weightedMaskMass a 9218 (-160310755) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 9218, -160310755) (by decide)]
  have h015 : weightedMaskMass a 1538 (-5212527) =
      weightedMaskMass a 65666 (-5212527) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 65666, -5212527) (by decide)]
  have h016 : weightedMaskMass a 1538 (124756563) =
      weightedMaskMass a 66564 (124756563) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 66564, 124756563) (by decide)]
  have h017 : weightedMaskMass a 1538 (-34106666) =
      weightedMaskMass a 131140 (-34106666) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 131140, -34106666) (by decide)]
  have h018 : weightedMaskMass a 1538 (10517679) =
      weightedMaskMass a 266272 (10517679) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 266272, 10517679) (by decide)]
  have h019 : weightedMaskMass a 1538 (-31020614) =
      weightedMaskMass a 393248 (-31020614) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 393248, -31020614) (by decide)]
  have h020 : weightedMaskMass a 1538 (43553322) =
      weightedMaskMass a 544768 (43553322) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 544768, 43553322) (by decide)]
  have h021 : weightedMaskMass a 1538 (-61645683) =
      weightedMaskMass a 559104 (-61645683) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 559104, -61645683) (by decide)]
  have h022 : weightedMaskMass a 1538 (67910200) =
      weightedMaskMass a 1048834 (67910200) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 1048834, 67910200) (by decide)]
  have h023 : weightedMaskMass a 1538 (59867555) =
      weightedMaskMass a 2099232 (59867555) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 2099232, 59867555) (by decide)]
  have h024 : weightedMaskMass a 1538 (-40744812) =
      weightedMaskMass a 2359312 (-40744812) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 2359312, -40744812) (by decide)]
  have h025 : weightedMaskMass a 1538 (103433668) =
      weightedMaskMass a 4719104 (103433668) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1538, 4719104, 103433668) (by decide)]
  have h026 : weightedMaskMass a 1540 (1969036) =
      weightedMaskMass a 2116 (1969036) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 2116, 1969036) (by decide)]
  have h027 : weightedMaskMass a 1540 (8123874) =
      weightedMaskMass a 9217 (8123874) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 9217, 8123874) (by decide)]
  have h028 : weightedMaskMass a 1540 (-54756719) =
      weightedMaskMass a 17409 (-54756719) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 17409, -54756719) (by decide)]
  have h029 : weightedMaskMass a 1540 (-76527889) =
      weightedMaskMass a 65572 (-76527889) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 65572, -76527889) (by decide)]
  have h030 : weightedMaskMass a 1540 (-117146388) =
      weightedMaskMass a 278529 (-117146388) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 278529, -117146388) (by decide)]
  have h031 : weightedMaskMass a 1540 (-62946685) =
      weightedMaskMass a 282624 (-62946685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 282624, -62946685) (by decide)]
  have h032 : weightedMaskMass a 1540 (139071305) =
      weightedMaskMass a 526368 (139071305) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 526368, 139071305) (by decide)]
  have h033 : weightedMaskMass a 1540 (91098418) =
      weightedMaskMass a 528416 (91098418) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 528416, 91098418) (by decide)]
  have h034 : weightedMaskMass a 1540 (30371902) =
      weightedMaskMass a 1049089 (30371902) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 1049089, 30371902) (by decide)]
  have h035 : weightedMaskMass a 1540 (-73882941) =
      weightedMaskMass a 1056770 (-73882941) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 1056770, -73882941) (by decide)]
  have h036 : weightedMaskMass a 1540 (-60688348) =
      weightedMaskMass a 2097170 (-60688348) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 2097170, -60688348) (by decide)]
  have h037 : weightedMaskMass a 1540 (122669937) =
      weightedMaskMass a 2099264 (122669937) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 2099264, 122669937) (by decide)]
  have h038 : weightedMaskMass a 1540 (-23963211) =
      weightedMaskMass a 2131968 (-23963211) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1540, 2131968, -23963211) (by decide)]
  have h039 : weightedMaskMass a 1600 (8945179) =
      weightedMaskMass a 32792 (8945179) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1600, 32792, 8945179) (by decide)]
  have h040 : weightedMaskMass a 1600 (-55722090) =
      weightedMaskMass a 151552 (-55722090) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1600, 151552, -55722090) (by decide)]
  have h041 : weightedMaskMass a 1600 (-23590956) =
      weightedMaskMass a 196736 (-23590956) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1600, 196736, -23590956) (by decide)]
  have h042 : weightedMaskMass a 1600 (29419472) =
      weightedMaskMass a 524356 (29419472) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1600, 524356, 29419472) (by decide)]
  have h043 : weightedMaskMass a 1602 (30176965) =
      weightedMaskMass a 196738 (30176965) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1602, 196738, 30176965) (by decide)]
  have h044 : weightedMaskMass a 1604 (118114056) =
      weightedMaskMass a 413696 (118114056) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1604, 413696, 118114056) (by decide)]
  have h045 : weightedMaskMass a 1604 (-3380188) =
      weightedMaskMass a 526404 (-3380188) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1604, 526404, -3380188) (by decide)]
  have h046 : weightedMaskMass a 2057 (-41614244) =
      weightedMaskMass a 8456 (-41614244) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 8456, -41614244) (by decide)]
  have h047 : weightedMaskMass a 2057 (57147288) =
      weightedMaskMass a 81922 (57147288) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 81922, 57147288) (by decide)]
  have h048 : weightedMaskMass a 2057 (-24585466) =
      weightedMaskMass a 114688 (-24585466) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 114688, -24585466) (by decide)]
  have h049 : weightedMaskMass a 2057 (41012344) =
      weightedMaskMass a 131137 (41012344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 131137, 41012344) (by decide)]
  have h050 : weightedMaskMass a 2057 (-34886684) =
      weightedMaskMass a 1048840 (-34886684) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 1048840, -34886684) (by decide)]
  have h051 : weightedMaskMass a 2057 (17939823) =
      weightedMaskMass a 2113568 (17939823) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 2113568, 17939823) (by decide)]
  have h052 : weightedMaskMass a 2057 (-32521578) =
      weightedMaskMass a 2637824 (-32521578) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2057, 2637824, -32521578) (by decide)]
  have h053 : weightedMaskMass a 2072 (-59933691) =
      weightedMaskMass a 8450 (-59933691) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2072, 8450, -59933691) (by decide)]
  have h054 : weightedMaskMass a 2072 (94155519) =
      weightedMaskMass a 20512 (94155519) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2072, 20512, 94155519) (by decide)]
  have h055 : weightedMaskMass a 2072 (45811493) =
      weightedMaskMass a 65668 (45811493) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2072, 65668, 45811493) (by decide)]
  have h056 : weightedMaskMass a 2072 (-12387456) =
      weightedMaskMass a 393217 (-12387456) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2072, 393217, -12387456) (by decide)]
  have h057 : weightedMaskMass a 2072 (-20318065) =
      weightedMaskMass a 2623488 (-20318065) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2072, 2623488, -20318065) (by decide)]
  have h058 : weightedMaskMass a 2084 (-90903533) =
      weightedMaskMass a 3076 (-90903533) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2084, 3076, -90903533) (by decide)]
  have h059 : weightedMaskMass a 2084 (-53651606) =
      weightedMaskMass a 9220 (-53651606) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2084, 9220, -53651606) (by decide)]
  have h060 : weightedMaskMass a 2084 (-45335968) =
      weightedMaskMass a 131108 (-45335968) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2084, 131108, -45335968) (by decide)]
  have h061 : weightedMaskMass a 2084 (138522392) =
      weightedMaskMass a 1048706 (138522392) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2084, 1048706, 138522392) (by decide)]
  have h062 : weightedMaskMass a 2084 (122629123) =
      weightedMaskMass a 1049090 (122629123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2084, 1049090, 122629123) (by decide)]
  have h063 : weightedMaskMass a 2113 (-128813093) =
      weightedMaskMass a 8201 (-128813093) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113, 8201, -128813093) (by decide)]
  have h064 : weightedMaskMass a 2113 (48323019) =
      weightedMaskMass a 82944 (48323019) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113, 82944, 48323019) (by decide)]
  have h065 : weightedMaskMass a 2113 (89061020) =
      weightedMaskMass a 606208 (89061020) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113, 606208, 89061020) (by decide)]
  have h066 : weightedMaskMass a 2113 (-45169227) =
      weightedMaskMass a 2146304 (-45169227) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113, 2146304, -45169227) (by decide)]
  have h067 : weightedMaskMass a 2113 (-84442055) =
      weightedMaskMass a 2375680 (-84442055) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2113, 2375680, -84442055) (by decide)]
  have h068 : weightedMaskMass a 2177 (71567799) =
      weightedMaskMass a 16404 (71567799) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2177, 16404, 71567799) (by decide)]
  have h069 : weightedMaskMass a 2177 (-121035609) =
      weightedMaskMass a 131138 (-121035609) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2177, 131138, -121035609) (by decide)]
  have h070 : weightedMaskMass a 2177 (414770) =
      weightedMaskMass a 1048836 (414770) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2177, 1048836, 414770) (by decide)]
  have h071 : weightedMaskMass a 2177 (85809507) =
      weightedMaskMass a 1097728 (85809507) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2177, 1097728, 85809507) (by decide)]
  have h072 : weightedMaskMass a 2177 (-65293623) =
      weightedMaskMass a 2097696 (-65293623) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2177, 2097696, -65293623) (by decide)]
  have h073 : weightedMaskMass a 2212 (-10797842) =
      weightedMaskMass a 147492 (-10797842) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2212, 147492, -10797842) (by decide)]
  have h074 : weightedMaskMass a 2212 (-84066215) =
      weightedMaskMass a 1049122 (-84066215) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2212, 1049122, -84066215) (by decide)]
  have h075 : weightedMaskMass a 2212 (33884051) =
      weightedMaskMass a 1050660 (33884051) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2212, 1050660, 33884051) (by decide)]
  have h076 : weightedMaskMass a 2212 (4761786) =
      weightedMaskMass a 1065090 (4761786) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2212, 1065090, 4761786) (by decide)]
  have h077 : weightedMaskMass a 2240 (-108582903) =
      weightedMaskMass a 32834 (-108582903) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2240, 32834, -108582903) (by decide)]
  have h078 : weightedMaskMass a 2240 (88854882) =
      weightedMaskMass a 131592 (88854882) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2240, 131592, 88854882) (by decide)]
  have h079 : weightedMaskMass a 2240 (-69738951) =
      weightedMaskMass a 524328 (-69738951) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2240, 524328, -69738951) (by decide)]
  have h080 : weightedMaskMass a 2240 (-61677134) =
      weightedMaskMass a 1073152 (-61677134) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2240, 1073152, -61677134) (by decide)]
  have h081 : weightedMaskMass a 2240 (8211670) =
      weightedMaskMass a 3178496 (8211670) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2240, 3178496, 8211670) (by decide)]
  have h082 : weightedMaskMass a 2241 (43211038) =
      weightedMaskMass a 3194880 (43211038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2241, 3194880, 43211038) (by decide)]
  have h083 : weightedMaskMass a 2244 (-99304215) =
      weightedMaskMass a 526376 (-99304215) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2244, 526376, -99304215) (by decide)]
  have h084 : weightedMaskMass a 2244 (181703674) =
      weightedMaskMass a 1073154 (181703674) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2244, 1073154, 181703674) (by decide)]
  have h085 : weightedMaskMass a 2244 (-59240725) =
      weightedMaskMass a 3180544 (-59240725) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2244, 3180544, -59240725) (by decide)]
  have h086 : weightedMaskMass a 2312 (7068803) =
      weightedMaskMass a 81952 (7068803) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2312, 81952, 7068803) (by decide)]
  have h087 : weightedMaskMass a 2312 (21375313) =
      weightedMaskMass a 131081 (21375313) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2312, 131081, 21375313) (by decide)]
  have h088 : weightedMaskMass a 2312 (11257475) =
      weightedMaskMass a 1048585 (11257475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2312, 1048585, 11257475) (by decide)]
  have h089 : weightedMaskMass a 2312 (-58784049) =
      weightedMaskMass a 2113538 (-58784049) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2312, 2113538, -58784049) (by decide)]
  have h090 : weightedMaskMass a 2320 (27669096) =
      weightedMaskMass a 8705 (27669096) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 8705, 27669096) (by decide)]
  have h091 : weightedMaskMass a 2320 (-52235627) =
      weightedMaskMass a 33026 (-52235627) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 33026, -52235627) (by decide)]
  have h092 : weightedMaskMass a 2320 (38261414) =
      weightedMaskMass a 69664 (38261414) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 69664, 38261414) (by decide)]
  have h093 : weightedMaskMass a 2320 (-1946598) =
      weightedMaskMass a 393224 (-1946598) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 393224, -1946598) (by decide)]
  have h094 : weightedMaskMass a 2320 (51033073) =
      weightedMaskMass a 589828 (51033073) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 589828, 51033073) (by decide)]
  have h095 : weightedMaskMass a 2320 (2889558) =
      weightedMaskMass a 2129936 (2889558) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2320, 2129936, 2889558) (by decide)]
  have h096 : weightedMaskMass a 2324 (18831662) =
      weightedMaskMass a 393256 (18831662) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2324, 393256, 18831662) (by decide)]
  have h097 : weightedMaskMass a 2324 (-130569918) =
      weightedMaskMass a 1081602 (-130569918) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2324, 1081602, -130569918) (by decide)]
  have h098 : weightedMaskMass a 2328 (-33137611) =
      weightedMaskMass a 86048 (-33137611) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2328, 86048, -33137611) (by decide)]
  have h099 : weightedMaskMass a 2328 (9386648) =
      weightedMaskMass a 393225 (9386648) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2328, 393225, 9386648) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt03 s.val : ℝ)) = (((((((weightedMaskMass a 1042 (-20036047) + (-weightedMaskMass a 262164 (-20036047) + weightedMaskMass a 1042 (-1983902))) + (-weightedMaskMass a 262180 (-1983902) + (weightedMaskMass a 1042 (21515549) + -weightedMaskMass a 264224 (21515549)))) + ((weightedMaskMass a 1042 (163938698) + (-weightedMaskMass a 540673 (163938698) + weightedMaskMass a 1042 (23477841))) + (-weightedMaskMass a 561152 (23477841) + (weightedMaskMass a 1042 (129895489) + -weightedMaskMass a 1049344 (129895489))))) + (((weightedMaskMass a 1042 (-4345683) + (-weightedMaskMass a 2097188 (-4345683) + weightedMaskMass a 1042 (-61907302))) + (-weightedMaskMass a 2228256 (-61907302) + (weightedMaskMass a 1042 (-83713936) + -weightedMaskMass a 2228288 (-83713936)))) + ((weightedMaskMass a 1042 (-4187886) + (-weightedMaskMass a 4229120 (-4187886) + weightedMaskMass a 1042 (73494146))) + ((-weightedMaskMass a 4722688 (73494146) + weightedMaskMass a 1537 (-81423618)) + (-weightedMaskMass a 2099216 (-81423618) + weightedMaskMass a 1538 (-102083583)))))) + ((((-weightedMaskMass a 2068 (-102083583) + (weightedMaskMass a 1538 (-27099418) + -weightedMaskMass a 3073 (-27099418))) + (weightedMaskMass a 1538 (-160310755) + (-weightedMaskMass a 9218 (-160310755) + weightedMaskMass a 1538 (-5212527)))) + ((-weightedMaskMass a 65666 (-5212527) + (weightedMaskMass a 1538 (124756563) + -weightedMaskMass a 66564 (124756563))) + (weightedMaskMass a 1538 (-34106666) + (-weightedMaskMass a 131140 (-34106666) + weightedMaskMass a 1538 (10517679))))) + (((-weightedMaskMass a 266272 (10517679) + (weightedMaskMass a 1538 (-31020614) + -weightedMaskMass a 393248 (-31020614))) + (weightedMaskMass a 1538 (43553322) + (-weightedMaskMass a 544768 (43553322) + weightedMaskMass a 1538 (-61645683)))) + ((-weightedMaskMass a 559104 (-61645683) + (weightedMaskMass a 1538 (67910200) + -weightedMaskMass a 1048834 (67910200))) + ((weightedMaskMass a 1538 (59867555) + -weightedMaskMass a 2099232 (59867555)) + (weightedMaskMass a 1538 (-40744812) + -weightedMaskMass a 2359312 (-40744812))))))) + (((((weightedMaskMass a 1538 (103433668) + (-weightedMaskMass a 4719104 (103433668) + weightedMaskMass a 1540 (1969036))) + (-weightedMaskMass a 2116 (1969036) + (weightedMaskMass a 1540 (8123874) + -weightedMaskMass a 9217 (8123874)))) + ((weightedMaskMass a 1540 (-54756719) + (-weightedMaskMass a 17409 (-54756719) + weightedMaskMass a 1540 (-76527889))) + (-weightedMaskMass a 65572 (-76527889) + (weightedMaskMass a 1540 (-117146388) + -weightedMaskMass a 278529 (-117146388))))) + (((weightedMaskMass a 1540 (-62946685) + (-weightedMaskMass a 282624 (-62946685) + weightedMaskMass a 1540 (139071305))) + (-weightedMaskMass a 526368 (139071305) + (weightedMaskMass a 1540 (91098418) + -weightedMaskMass a 528416 (91098418)))) + ((weightedMaskMass a 1540 (30371902) + (-weightedMaskMass a 1049089 (30371902) + weightedMaskMass a 1540 (-73882941))) + ((-weightedMaskMass a 1056770 (-73882941) + weightedMaskMass a 1540 (-60688348)) + (-weightedMaskMass a 2097170 (-60688348) + weightedMaskMass a 1540 (122669937)))))) + ((((-weightedMaskMass a 2099264 (122669937) + (weightedMaskMass a 1540 (-23963211) + -weightedMaskMass a 2131968 (-23963211))) + (weightedMaskMass a 1600 (8945179) + (-weightedMaskMass a 32792 (8945179) + weightedMaskMass a 1600 (-55722090)))) + ((-weightedMaskMass a 151552 (-55722090) + (weightedMaskMass a 1600 (-23590956) + -weightedMaskMass a 196736 (-23590956))) + (weightedMaskMass a 1600 (29419472) + (-weightedMaskMass a 524356 (29419472) + weightedMaskMass a 1602 (30176965))))) + (((-weightedMaskMass a 196738 (30176965) + (weightedMaskMass a 1604 (118114056) + -weightedMaskMass a 413696 (118114056))) + (weightedMaskMass a 1604 (-3380188) + (-weightedMaskMass a 526404 (-3380188) + weightedMaskMass a 2057 (-41614244)))) + ((-weightedMaskMass a 8456 (-41614244) + (weightedMaskMass a 2057 (57147288) + -weightedMaskMass a 81922 (57147288))) + ((weightedMaskMass a 2057 (-24585466) + -weightedMaskMass a 114688 (-24585466)) + (weightedMaskMass a 2057 (41012344) + -weightedMaskMass a 131137 (41012344)))))))) + ((((((weightedMaskMass a 2057 (-34886684) + (-weightedMaskMass a 1048840 (-34886684) + weightedMaskMass a 2057 (17939823))) + (-weightedMaskMass a 2113568 (17939823) + (weightedMaskMass a 2057 (-32521578) + -weightedMaskMass a 2637824 (-32521578)))) + ((weightedMaskMass a 2072 (-59933691) + (-weightedMaskMass a 8450 (-59933691) + weightedMaskMass a 2072 (94155519))) + (-weightedMaskMass a 20512 (94155519) + (weightedMaskMass a 2072 (45811493) + -weightedMaskMass a 65668 (45811493))))) + (((weightedMaskMass a 2072 (-12387456) + (-weightedMaskMass a 393217 (-12387456) + weightedMaskMass a 2072 (-20318065))) + (-weightedMaskMass a 2623488 (-20318065) + (weightedMaskMass a 2084 (-90903533) + -weightedMaskMass a 3076 (-90903533)))) + ((weightedMaskMass a 2084 (-53651606) + (-weightedMaskMass a 9220 (-53651606) + weightedMaskMass a 2084 (-45335968))) + ((-weightedMaskMass a 131108 (-45335968) + weightedMaskMass a 2084 (138522392)) + (-weightedMaskMass a 1048706 (138522392) + weightedMaskMass a 2084 (122629123)))))) + ((((-weightedMaskMass a 1049090 (122629123) + (weightedMaskMass a 2113 (-128813093) + -weightedMaskMass a 8201 (-128813093))) + (weightedMaskMass a 2113 (48323019) + (-weightedMaskMass a 82944 (48323019) + weightedMaskMass a 2113 (89061020)))) + ((-weightedMaskMass a 606208 (89061020) + (weightedMaskMass a 2113 (-45169227) + -weightedMaskMass a 2146304 (-45169227))) + (weightedMaskMass a 2113 (-84442055) + (-weightedMaskMass a 2375680 (-84442055) + weightedMaskMass a 2177 (71567799))))) + (((-weightedMaskMass a 16404 (71567799) + (weightedMaskMass a 2177 (-121035609) + -weightedMaskMass a 131138 (-121035609))) + (weightedMaskMass a 2177 (414770) + (-weightedMaskMass a 1048836 (414770) + weightedMaskMass a 2177 (85809507)))) + ((-weightedMaskMass a 1097728 (85809507) + (weightedMaskMass a 2177 (-65293623) + -weightedMaskMass a 2097696 (-65293623))) + ((weightedMaskMass a 2212 (-10797842) + -weightedMaskMass a 147492 (-10797842)) + (weightedMaskMass a 2212 (-84066215) + -weightedMaskMass a 1049122 (-84066215))))))) + (((((weightedMaskMass a 2212 (33884051) + (-weightedMaskMass a 1050660 (33884051) + weightedMaskMass a 2212 (4761786))) + (-weightedMaskMass a 1065090 (4761786) + (weightedMaskMass a 2240 (-108582903) + -weightedMaskMass a 32834 (-108582903)))) + ((weightedMaskMass a 2240 (88854882) + (-weightedMaskMass a 131592 (88854882) + weightedMaskMass a 2240 (-69738951))) + (-weightedMaskMass a 524328 (-69738951) + (weightedMaskMass a 2240 (-61677134) + -weightedMaskMass a 1073152 (-61677134))))) + (((weightedMaskMass a 2240 (8211670) + (-weightedMaskMass a 3178496 (8211670) + weightedMaskMass a 2241 (43211038))) + (-weightedMaskMass a 3194880 (43211038) + (weightedMaskMass a 2244 (-99304215) + -weightedMaskMass a 526376 (-99304215)))) + ((weightedMaskMass a 2244 (181703674) + (-weightedMaskMass a 1073154 (181703674) + weightedMaskMass a 2244 (-59240725))) + ((-weightedMaskMass a 3180544 (-59240725) + weightedMaskMass a 2312 (7068803)) + (-weightedMaskMass a 81952 (7068803) + weightedMaskMass a 2312 (21375313)))))) + ((((-weightedMaskMass a 131081 (21375313) + (weightedMaskMass a 2312 (11257475) + -weightedMaskMass a 1048585 (11257475))) + (weightedMaskMass a 2312 (-58784049) + (-weightedMaskMass a 2113538 (-58784049) + weightedMaskMass a 2320 (27669096)))) + ((-weightedMaskMass a 8705 (27669096) + (weightedMaskMass a 2320 (-52235627) + -weightedMaskMass a 33026 (-52235627))) + (weightedMaskMass a 2320 (38261414) + (-weightedMaskMass a 69664 (38261414) + weightedMaskMass a 2320 (-1946598))))) + (((-weightedMaskMass a 393224 (-1946598) + (weightedMaskMass a 2320 (51033073) + -weightedMaskMass a 589828 (51033073))) + (weightedMaskMass a 2320 (2889558) + (-weightedMaskMass a 2129936 (2889558) + weightedMaskMass a 2324 (18831662)))) + ((-weightedMaskMass a 393256 (18831662) + (weightedMaskMass a 2324 (-130569918) + -weightedMaskMass a 1081602 (-130569918))) + ((weightedMaskMass a 2328 (-33137611) + -weightedMaskMass a 86048 (-33137611)) + (weightedMaskMass a 2328 (9386648) + -weightedMaskMass a 393225 (9386648))))))))) := by
      simp only [atomCongruenceContributionInt03, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
