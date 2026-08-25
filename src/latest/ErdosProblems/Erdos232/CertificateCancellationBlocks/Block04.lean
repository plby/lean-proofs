/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock04_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights04, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt04 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 2336 (-26830587) =
      weightedMaskMass a 24577 (-26830587) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 24577, -26830587) (by decide)]
  have h001 : weightedMaskMass a 2336 (-57977543) =
      weightedMaskMass a 25600 (-57977543) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 25600, -57977543) (by decide)]
  have h002 : weightedMaskMass a 2336 (-44059898) =
      weightedMaskMass a 32898 (-44059898) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 32898, -44059898) (by decide)]
  have h003 : weightedMaskMass a 2336 (-8797926) =
      weightedMaskMass a 34880 (-8797926) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 34880, -8797926) (by decide)]
  have h004 : weightedMaskMass a 2336 (3138543) =
      weightedMaskMass a 131588 (3138543) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 131588, 3138543) (by decide)]
  have h005 : weightedMaskMass a 2336 (115571518) =
      weightedMaskMass a 589832 (115571518) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 589832, 115571518) (by decide)]
  have h006 : weightedMaskMass a 2336 (154415608) =
      weightedMaskMass a 2129984 (154415608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 2129984, 154415608) (by decide)]
  have h007 : weightedMaskMass a 2336 (-40961152) =
      weightedMaskMass a 3145730 (-40961152) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2336, 3145730, -40961152) (by decide)]
  have h008 : weightedMaskMass a 2340 (107958942) =
      weightedMaskMass a 25604 (107958942) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2340, 25604, 107958942) (by decide)]
  have h009 : weightedMaskMass a 2340 (-26279794) =
      weightedMaskMass a 131620 (-26279794) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2340, 131620, -26279794) (by decide)]
  have h010 : weightedMaskMass a 2340 (-145376996) =
      weightedMaskMass a 1081474 (-145376996) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2340, 1081474, -145376996) (by decide)]
  have h011 : weightedMaskMass a 2340 (-3329257) =
      weightedMaskMass a 3146242 (-3329257) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2340, 3146242, -3329257) (by decide)]
  have h012 : weightedMaskMass a 2344 (-6343164) =
      weightedMaskMass a 3162114 (-6343164) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2344, 3162114, -6343164) (by decide)]
  have h013 : weightedMaskMass a 3092 (-67721330) =
      weightedMaskMass a 74756 (-67721330) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3092, 74756, -67721330) (by decide)]
  have h014 : weightedMaskMass a 3092 (15232435) =
      weightedMaskMass a 393252 (15232435) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3092, 393252, 15232435) (by decide)]
  have h015 : weightedMaskMass a 3092 (-74108370) =
      weightedMaskMass a 1049346 (-74108370) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3092, 1049346, -74108370) (by decide)]
  have h016 : weightedMaskMass a 3092 (-3825732) =
      weightedMaskMass a 2099236 (-3825732) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3092, 2099236, -3825732) (by decide)]
  have h017 : weightedMaskMass a 3136 (-26664792) =
      weightedMaskMass a 8708 (-26664792) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 8708, -26664792) (by decide)]
  have h018 : weightedMaskMass a 3136 (101225971) =
      weightedMaskMass a 32786 (101225971) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 32786, 101225971) (by decide)]
  have h019 : weightedMaskMass a 3136 (-50645962) =
      weightedMaskMass a 35072 (-50645962) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 35072, -50645962) (by decide)]
  have h020 : weightedMaskMass a 3136 (-29832472) =
      weightedMaskMass a 196616 (-29832472) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 196616, -29832472) (by decide)]
  have h021 : weightedMaskMass a 3136 (-50252752) =
      weightedMaskMass a 196640 (-50252752) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 196640, -50252752) (by decide)]
  have h022 : weightedMaskMass a 3136 (-25938244) =
      weightedMaskMass a 524324 (-25938244) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 524324, -25938244) (by decide)]
  have h023 : weightedMaskMass a 3136 (20475876) =
      weightedMaskMass a 524804 (20475876) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 524804, 20475876) (by decide)]
  have h024 : weightedMaskMass a 3136 (-106505247) =
      weightedMaskMass a 593920 (-106505247) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 593920, -106505247) (by decide)]
  have h025 : weightedMaskMass a 3136 (86131512) =
      weightedMaskMass a 1057280 (86131512) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3136, 1057280, 86131512) (by decide)]
  have h026 : weightedMaskMass a 3137 (54544398) =
      weightedMaskMass a 610304 (54544398) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3137, 610304, 54544398) (by decide)]
  have h027 : weightedMaskMass a 3140 (59219447) =
      weightedMaskMass a 9732 (59219447) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3140, 9732, 59219447) (by decide)]
  have h028 : weightedMaskMass a 3140 (-89666918) =
      weightedMaskMass a 196644 (-89666918) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3140, 196644, -89666918) (by decide)]
  have h029 : weightedMaskMass a 3140 (83241823) =
      weightedMaskMass a 526372 (83241823) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3140, 526372, 83241823) (by decide)]
  have h030 : weightedMaskMass a 3140 (18201865) =
      weightedMaskMass a 1057282 (18201865) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3140, 1057282, 18201865) (by decide)]
  have h031 : weightedMaskMass a 4098 (-166241008) =
      weightedMaskMass a 8224 (-166241008) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 8224, -166241008) (by decide)]
  have h032 : weightedMaskMass a 4098 (108912255) =
      weightedMaskMass a 16640 (108912255) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 16640, 108912255) (by decide)]
  have h033 : weightedMaskMass a 4098 (62603856) =
      weightedMaskMass a 32772 (62603856) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 32772, 62603856) (by decide)]
  have h034 : weightedMaskMass a 4098 (51449249) =
      weightedMaskMass a 65600 (51449249) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 65600, 51449249) (by decide)]
  have h035 : weightedMaskMass a 4098 (-12779718) =
      weightedMaskMass a 132096 (-12779718) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 132096, -12779718) (by decide)]
  have h036 : weightedMaskMass a 4098 (65221785) =
      weightedMaskMass a 262656 (65221785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 262656, 65221785) (by decide)]
  have h037 : weightedMaskMass a 4098 (69897050) =
      weightedMaskMass a 524304 (69897050) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 524304, 69897050) (by decide)]
  have h038 : weightedMaskMass a 4098 (-69287569) =
      weightedMaskMass a 1048592 (-69287569) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 1048592, -69287569) (by decide)]
  have h039 : weightedMaskMass a 4098 (-92210155) =
      weightedMaskMass a 1572864 (-92210155) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 1572864, -92210155) (by decide)]
  have h040 : weightedMaskMass a 4098 (-52631930) =
      weightedMaskMass a 2097160 (-52631930) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4098, 2097160, -52631930) (by decide)]
  have h041 : weightedMaskMass a 4100 (-154914619) =
      weightedMaskMass a 8256 (-154914619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 8256, -154914619) (by decide)]
  have h042 : weightedMaskMass a 4100 (39752950) =
      weightedMaskMass a 294912 (39752950) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 294912, 39752950) (by decide)]
  have h043 : weightedMaskMass a 4100 (11897633) =
      weightedMaskMass a 327680 (11897633) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 327680, 11897633) (by decide)]
  have h044 : weightedMaskMass a 4100 (8109319) =
      weightedMaskMass a 525312 (8109319) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 525312, 8109319) (by decide)]
  have h045 : weightedMaskMass a 4100 (115654171) =
      weightedMaskMass a 2098176 (115654171) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 2098176, 115654171) (by decide)]
  have h046 : weightedMaskMass a 4100 (13239155) =
      weightedMaskMass a 4194306 (13239155) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 4194306, 13239155) (by decide)]
  have h047 : weightedMaskMass a 4100 (-5459407) =
      weightedMaskMass a 4194336 (-5459407) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4100, 4194336, -5459407) (by decide)]
  have h048 : weightedMaskMass a 4130 (27089405) =
      weightedMaskMass a 8226 (27089405) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 8226, 27089405) (by decide)]
  have h049 : weightedMaskMass a 4130 (-35555430) =
      weightedMaskMass a 16642 (-35555430) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 16642, -35555430) (by decide)]
  have h050 : weightedMaskMass a 4130 (50111246) =
      weightedMaskMass a 20482 (50111246) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 20482, 50111246) (by decide)]
  have h051 : weightedMaskMass a 4130 (-107973688) =
      weightedMaskMass a 98308 (-107973688) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 98308, -107973688) (by decide)]
  have h052 : weightedMaskMass a 4130 (1494290) =
      weightedMaskMass a 132097 (1494290) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 132097, 1494290) (by decide)]
  have h053 : weightedMaskMass a 4130 (-11769785) =
      weightedMaskMass a 1048600 (-11769785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 1048600, -11769785) (by decide)]
  have h054 : weightedMaskMass a 4130 (-19817139) =
      weightedMaskMass a 1050640 (-19817139) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 1050640, -19817139) (by decide)]
  have h055 : weightedMaskMass a 4130 (-21429929) =
      weightedMaskMass a 1574912 (-21429929) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 1574912, -21429929) (by decide)]
  have h056 : weightedMaskMass a 4130 (92839224) =
      weightedMaskMass a 2099208 (92839224) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 2099208, 92839224) (by decide)]
  have h057 : weightedMaskMass a 4130 (-27163587) =
      weightedMaskMass a 2621456 (-27163587) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4130, 2621456, -27163587) (by decide)]
  have h058 : weightedMaskMass a 4132 (-57992556) =
      weightedMaskMass a 8260 (-57992556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4132, 8260, -57992556) (by decide)]
  have h059 : weightedMaskMass a 4132 (1318100) =
      weightedMaskMass a 525824 (1318100) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4132, 525824, 1318100) (by decide)]
  have h060 : weightedMaskMass a 4132 (42673308) =
      weightedMaskMass a 527360 (42673308) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4132, 527360, 42673308) (by decide)]
  have h061 : weightedMaskMass a 4132 (13044878) =
      weightedMaskMass a 2100224 (13044878) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4132, 2100224, 13044878) (by decide)]
  have h062 : weightedMaskMass a 4132 (-67337521) =
      weightedMaskMass a 4194818 (-67337521) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4132, 4194818, -67337521) (by decide)]
  have h063 : weightedMaskMass a 4162 (-84476561) =
      weightedMaskMass a 16644 (-84476561) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4162, 16644, -84476561) (by decide)]
  have h064 : weightedMaskMass a 4162 (31625625) =
      weightedMaskMass a 1064976 (31625625) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4162, 1064976, 31625625) (by decide)]
  have h065 : weightedMaskMass a 4162 (-4092658) =
      weightedMaskMass a 1081348 (-4092658) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4162, 1081348, -4092658) (by decide)]
  have h066 : weightedMaskMass a 4162 (76483086) =
      weightedMaskMass a 2097672 (76483086) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4162, 2097672, 76483086) (by decide)]
  have h067 : weightedMaskMass a 4164 (45253726) =
      weightedMaskMass a 8258 (45253726) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4164, 8258, 45253726) (by decide)]
  have h068 : weightedMaskMass a 4164 (-34950525) =
      weightedMaskMass a 20484 (-34950525) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4164, 20484, -34950525) (by decide)]
  have h069 : weightedMaskMass a 4164 (13351307) =
      weightedMaskMass a 2098688 (13351307) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4164, 2098688, 13351307) (by decide)]
  have h070 : weightedMaskMass a 4164 (-16284319) =
      weightedMaskMass a 4194848 (-16284319) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4164, 4194848, -16284319) (by decide)]
  have h071 : weightedMaskMass a 4258 (-41340851) =
      weightedMaskMass a 20610 (-41340851) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4258, 20610, -41340851) (by decide)]
  have h072 : weightedMaskMass a 4352 (33493907) =
      weightedMaskMass a 12288 (33493907) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4352, 12288, 33493907) (by decide)]
  have h073 : weightedMaskMass a 4352 (-21567749) =
      weightedMaskMass a 4325376 (-21567749) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4352, 4325376, -21567749) (by decide)]
  have h074 : weightedMaskMass a 4354 (-57996750) =
      weightedMaskMass a 12290 (-57996750) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4354, 12290, -57996750) (by decide)]
  have h075 : weightedMaskMass a 4354 (16875179) =
      weightedMaskMass a 12320 (16875179) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4354, 12320, 16875179) (by decide)]
  have h076 : weightedMaskMass a 4354 (19623111) =
      weightedMaskMass a 20736 (19623111) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4354, 20736, 19623111) (by decide)]
  have h077 : weightedMaskMass a 4356 (-68926448) =
      weightedMaskMass a 12352 (-68926448) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4356, 12352, -68926448) (by decide)]
  have h078 : weightedMaskMass a 4356 (6100603) =
      weightedMaskMass a 4325378 (6100603) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4356, 4325378, 6100603) (by decide)]
  have h079 : weightedMaskMass a 4384 (7705295) =
      weightedMaskMass a 28672 (7705295) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4384, 28672, 7705295) (by decide)]
  have h080 : weightedMaskMass a 4384 (-49032909) =
      weightedMaskMass a 4325888 (-49032909) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4384, 4325888, -49032909) (by decide)]
  have h081 : weightedMaskMass a 4386 (-21247203) =
      weightedMaskMass a 28674 (-21247203) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4386, 28674, -21247203) (by decide)]
  have h082 : weightedMaskMass a 20768 (-1937379) =
      weightedMaskMass a 28704 (-1937379) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20768, 28704, -1937379) (by decide)]
  have h083 : weightedMaskMass a 4388 (64500054) =
      weightedMaskMass a 4325890 (64500054) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4388, 4325890, 64500054) (by decide)]
  have h084 : weightedMaskMass a 28676 (2306004) =
      weightedMaskMass a 4325920 (2306004) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (28676, 4325920, 2306004) (by decide)]
  have h085 : weightedMaskMass a 5120 (82325604) =
      weightedMaskMass a 270336 (82325604) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 270336, 82325604) (by decide)]
  have h086 : weightedMaskMass a 5120 (-109329554) =
      weightedMaskMass a 524544 (-109329554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 524544, -109329554) (by decide)]
  have h087 : weightedMaskMass a 5120 (116620062) =
      weightedMaskMass a 2105344 (116620062) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 2105344, 116620062) (by decide)]
  have h088 : weightedMaskMass a 5120 (-18408697) =
      weightedMaskMass a 4194308 (-18408697) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 4194308, -18408697) (by decide)]
  have h089 : weightedMaskMass a 5120 (-11901819) =
      weightedMaskMass a 4194320 (-11901819) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 4194320, -11901819) (by decide)]
  have h090 : weightedMaskMass a 5120 (36898582) =
      weightedMaskMass a 4210688 (36898582) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5120, 4210688, 36898582) (by decide)]
  have h091 : weightedMaskMass a 5121 (-79405340) =
      weightedMaskMass a 2105360 (-79405340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5121, 2105360, -79405340) (by decide)]
  have h092 : weightedMaskMass a 5121 (13505420) =
      weightedMaskMass a 4196368 (13505420) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5121, 4196368, 13505420) (by decide)]
  have h093 : weightedMaskMass a 5121 (-16683655) =
      weightedMaskMass a 4214784 (-16683655) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5121, 4214784, -16683655) (by decide)]
  have h094 : weightedMaskMass a 5122 (-17691706) =
      weightedMaskMass a 270368 (-17691706) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 270368, -17691706) (by decide)]
  have h095 : weightedMaskMass a 5122 (164854398) =
      weightedMaskMass a 540928 (164854398) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 540928, 164854398) (by decide)]
  have h096 : weightedMaskMass a 5122 (175157785) =
      weightedMaskMass a 1573120 (175157785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 1573120, 175157785) (by decide)]
  have h097 : weightedMaskMass a 5122 (-226626721) =
      weightedMaskMass a 2105352 (-226626721) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 2105352, -226626721) (by decide)]
  have h098 : weightedMaskMass a 5122 (-167485469) =
      weightedMaskMass a 2105376 (-167485469) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 2105376, -167485469) (by decide)]
  have h099 : weightedMaskMass a 5122 (91428999) =
      weightedMaskMass a 4227076 (91428999) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 4227076, 91428999) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt04 s.val : ℝ)) = (((((((weightedMaskMass a 2336 (-26830587) + (-weightedMaskMass a 24577 (-26830587) + weightedMaskMass a 2336 (-57977543))) + (-weightedMaskMass a 25600 (-57977543) + (weightedMaskMass a 2336 (-44059898) + -weightedMaskMass a 32898 (-44059898)))) + ((weightedMaskMass a 2336 (-8797926) + (-weightedMaskMass a 34880 (-8797926) + weightedMaskMass a 2336 (3138543))) + (-weightedMaskMass a 131588 (3138543) + (weightedMaskMass a 2336 (115571518) + -weightedMaskMass a 589832 (115571518))))) + (((weightedMaskMass a 2336 (154415608) + (-weightedMaskMass a 2129984 (154415608) + weightedMaskMass a 2336 (-40961152))) + (-weightedMaskMass a 3145730 (-40961152) + (weightedMaskMass a 2340 (107958942) + -weightedMaskMass a 25604 (107958942)))) + ((weightedMaskMass a 2340 (-26279794) + (-weightedMaskMass a 131620 (-26279794) + weightedMaskMass a 2340 (-145376996))) + ((-weightedMaskMass a 1081474 (-145376996) + weightedMaskMass a 2340 (-3329257)) + (-weightedMaskMass a 3146242 (-3329257) + weightedMaskMass a 2344 (-6343164)))))) + ((((-weightedMaskMass a 3162114 (-6343164) + (weightedMaskMass a 3092 (-67721330) + -weightedMaskMass a 74756 (-67721330))) + (weightedMaskMass a 3092 (15232435) + (-weightedMaskMass a 393252 (15232435) + weightedMaskMass a 3092 (-74108370)))) + ((-weightedMaskMass a 1049346 (-74108370) + (weightedMaskMass a 3092 (-3825732) + -weightedMaskMass a 2099236 (-3825732))) + (weightedMaskMass a 3136 (-26664792) + (-weightedMaskMass a 8708 (-26664792) + weightedMaskMass a 3136 (101225971))))) + (((-weightedMaskMass a 32786 (101225971) + (weightedMaskMass a 3136 (-50645962) + -weightedMaskMass a 35072 (-50645962))) + (weightedMaskMass a 3136 (-29832472) + (-weightedMaskMass a 196616 (-29832472) + weightedMaskMass a 3136 (-50252752)))) + ((-weightedMaskMass a 196640 (-50252752) + (weightedMaskMass a 3136 (-25938244) + -weightedMaskMass a 524324 (-25938244))) + ((weightedMaskMass a 3136 (20475876) + -weightedMaskMass a 524804 (20475876)) + (weightedMaskMass a 3136 (-106505247) + -weightedMaskMass a 593920 (-106505247))))))) + (((((weightedMaskMass a 3136 (86131512) + (-weightedMaskMass a 1057280 (86131512) + weightedMaskMass a 3137 (54544398))) + (-weightedMaskMass a 610304 (54544398) + (weightedMaskMass a 3140 (59219447) + -weightedMaskMass a 9732 (59219447)))) + ((weightedMaskMass a 3140 (-89666918) + (-weightedMaskMass a 196644 (-89666918) + weightedMaskMass a 3140 (83241823))) + (-weightedMaskMass a 526372 (83241823) + (weightedMaskMass a 3140 (18201865) + -weightedMaskMass a 1057282 (18201865))))) + (((weightedMaskMass a 4098 (-166241008) + (-weightedMaskMass a 8224 (-166241008) + weightedMaskMass a 4098 (108912255))) + (-weightedMaskMass a 16640 (108912255) + (weightedMaskMass a 4098 (62603856) + -weightedMaskMass a 32772 (62603856)))) + ((weightedMaskMass a 4098 (51449249) + (-weightedMaskMass a 65600 (51449249) + weightedMaskMass a 4098 (-12779718))) + ((-weightedMaskMass a 132096 (-12779718) + weightedMaskMass a 4098 (65221785)) + (-weightedMaskMass a 262656 (65221785) + weightedMaskMass a 4098 (69897050)))))) + ((((-weightedMaskMass a 524304 (69897050) + (weightedMaskMass a 4098 (-69287569) + -weightedMaskMass a 1048592 (-69287569))) + (weightedMaskMass a 4098 (-92210155) + (-weightedMaskMass a 1572864 (-92210155) + weightedMaskMass a 4098 (-52631930)))) + ((-weightedMaskMass a 2097160 (-52631930) + (weightedMaskMass a 4100 (-154914619) + -weightedMaskMass a 8256 (-154914619))) + (weightedMaskMass a 4100 (39752950) + (-weightedMaskMass a 294912 (39752950) + weightedMaskMass a 4100 (11897633))))) + (((-weightedMaskMass a 327680 (11897633) + (weightedMaskMass a 4100 (8109319) + -weightedMaskMass a 525312 (8109319))) + (weightedMaskMass a 4100 (115654171) + (-weightedMaskMass a 2098176 (115654171) + weightedMaskMass a 4100 (13239155)))) + ((-weightedMaskMass a 4194306 (13239155) + (weightedMaskMass a 4100 (-5459407) + -weightedMaskMass a 4194336 (-5459407))) + ((weightedMaskMass a 4130 (27089405) + -weightedMaskMass a 8226 (27089405)) + (weightedMaskMass a 4130 (-35555430) + -weightedMaskMass a 16642 (-35555430)))))))) + ((((((weightedMaskMass a 4130 (50111246) + (-weightedMaskMass a 20482 (50111246) + weightedMaskMass a 4130 (-107973688))) + (-weightedMaskMass a 98308 (-107973688) + (weightedMaskMass a 4130 (1494290) + -weightedMaskMass a 132097 (1494290)))) + ((weightedMaskMass a 4130 (-11769785) + (-weightedMaskMass a 1048600 (-11769785) + weightedMaskMass a 4130 (-19817139))) + (-weightedMaskMass a 1050640 (-19817139) + (weightedMaskMass a 4130 (-21429929) + -weightedMaskMass a 1574912 (-21429929))))) + (((weightedMaskMass a 4130 (92839224) + (-weightedMaskMass a 2099208 (92839224) + weightedMaskMass a 4130 (-27163587))) + (-weightedMaskMass a 2621456 (-27163587) + (weightedMaskMass a 4132 (-57992556) + -weightedMaskMass a 8260 (-57992556)))) + ((weightedMaskMass a 4132 (1318100) + (-weightedMaskMass a 525824 (1318100) + weightedMaskMass a 4132 (42673308))) + ((-weightedMaskMass a 527360 (42673308) + weightedMaskMass a 4132 (13044878)) + (-weightedMaskMass a 2100224 (13044878) + weightedMaskMass a 4132 (-67337521)))))) + ((((-weightedMaskMass a 4194818 (-67337521) + (weightedMaskMass a 4162 (-84476561) + -weightedMaskMass a 16644 (-84476561))) + (weightedMaskMass a 4162 (31625625) + (-weightedMaskMass a 1064976 (31625625) + weightedMaskMass a 4162 (-4092658)))) + ((-weightedMaskMass a 1081348 (-4092658) + (weightedMaskMass a 4162 (76483086) + -weightedMaskMass a 2097672 (76483086))) + (weightedMaskMass a 4164 (45253726) + (-weightedMaskMass a 8258 (45253726) + weightedMaskMass a 4164 (-34950525))))) + (((-weightedMaskMass a 20484 (-34950525) + (weightedMaskMass a 4164 (13351307) + -weightedMaskMass a 2098688 (13351307))) + (weightedMaskMass a 4164 (-16284319) + (-weightedMaskMass a 4194848 (-16284319) + weightedMaskMass a 4258 (-41340851)))) + ((-weightedMaskMass a 20610 (-41340851) + (weightedMaskMass a 4352 (33493907) + -weightedMaskMass a 12288 (33493907))) + ((weightedMaskMass a 4352 (-21567749) + -weightedMaskMass a 4325376 (-21567749)) + (weightedMaskMass a 4354 (-57996750) + -weightedMaskMass a 12290 (-57996750))))))) + (((((weightedMaskMass a 4354 (16875179) + (-weightedMaskMass a 12320 (16875179) + weightedMaskMass a 4354 (19623111))) + (-weightedMaskMass a 20736 (19623111) + (weightedMaskMass a 4356 (-68926448) + -weightedMaskMass a 12352 (-68926448)))) + ((weightedMaskMass a 4356 (6100603) + (-weightedMaskMass a 4325378 (6100603) + weightedMaskMass a 4384 (7705295))) + (-weightedMaskMass a 28672 (7705295) + (weightedMaskMass a 4384 (-49032909) + -weightedMaskMass a 4325888 (-49032909))))) + (((weightedMaskMass a 4386 (-21247203) + (-weightedMaskMass a 28674 (-21247203) + weightedMaskMass a 20768 (-1937379))) + (-weightedMaskMass a 28704 (-1937379) + (weightedMaskMass a 4388 (64500054) + -weightedMaskMass a 4325890 (64500054)))) + ((weightedMaskMass a 28676 (2306004) + (-weightedMaskMass a 4325920 (2306004) + weightedMaskMass a 5120 (82325604))) + ((-weightedMaskMass a 270336 (82325604) + weightedMaskMass a 5120 (-109329554)) + (-weightedMaskMass a 524544 (-109329554) + weightedMaskMass a 5120 (116620062)))))) + ((((-weightedMaskMass a 2105344 (116620062) + (weightedMaskMass a 5120 (-18408697) + -weightedMaskMass a 4194308 (-18408697))) + (weightedMaskMass a 5120 (-11901819) + (-weightedMaskMass a 4194320 (-11901819) + weightedMaskMass a 5120 (36898582)))) + ((-weightedMaskMass a 4210688 (36898582) + (weightedMaskMass a 5121 (-79405340) + -weightedMaskMass a 2105360 (-79405340))) + (weightedMaskMass a 5121 (13505420) + (-weightedMaskMass a 4196368 (13505420) + weightedMaskMass a 5121 (-16683655))))) + (((-weightedMaskMass a 4214784 (-16683655) + (weightedMaskMass a 5122 (-17691706) + -weightedMaskMass a 270368 (-17691706))) + (weightedMaskMass a 5122 (164854398) + (-weightedMaskMass a 540928 (164854398) + weightedMaskMass a 5122 (175157785)))) + ((-weightedMaskMass a 1573120 (175157785) + (weightedMaskMass a 5122 (-226626721) + -weightedMaskMass a 2105352 (-226626721))) + ((weightedMaskMass a 5122 (-167485469) + -weightedMaskMass a 2105376 (-167485469)) + (weightedMaskMass a 5122 (91428999) + -weightedMaskMass a 4227076 (91428999))))))))) := by
      simp only [atomCongruenceContributionInt04, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
