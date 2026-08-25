/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock14_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights14, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt14 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 262400 (-63131493) =
      weightedMaskMass a 4194432 (-63131493) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262400, 4194432, -63131493) (by decide)]
  have h001 : weightedMaskMass a 262404 (-38895352) =
      weightedMaskMass a 4196480 (-38895352) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262404, 4196480, -38895352) (by decide)]
  have h002 : weightedMaskMass a 262416 (4735036) =
      weightedMaskMass a 532484 (4735036) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262416, 532484, 4735036) (by decide)]
  have h003 : weightedMaskMass a 262416 (-32821355) =
      weightedMaskMass a 532992 (-32821355) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262416, 532992, -32821355) (by decide)]
  have h004 : weightedMaskMass a 262416 (65613579) =
      weightedMaskMass a 5243008 (65613579) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262416, 5243008, 65613579) (by decide)]
  have h005 : weightedMaskMass a 262432 (-11085028) =
      weightedMaskMass a 532488 (-11085028) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262432, 532488, -11085028) (by decide)]
  have h006 : weightedMaskMass a 262432 (-10459004) =
      weightedMaskMass a 548864 (-10459004) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262432, 548864, -10459004) (by decide)]
  have h007 : weightedMaskMass a 262432 (687349) =
      weightedMaskMass a 4227200 (687349) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262432, 4227200, 687349) (by decide)]
  have h008 : weightedMaskMass a 262436 (39238959) =
      weightedMaskMass a 4229248 (39238959) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262436, 4229248, 39238959) (by decide)]
  have h009 : weightedMaskMass a 262912 (1718849) =
      weightedMaskMass a 532496 (1718849) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262912, 532496, 1718849) (by decide)]
  have h010 : weightedMaskMass a 262944 (52083896) =
      weightedMaskMass a 548880 (52083896) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (262944, 548880, 52083896) (by decide)]
  have h011 : weightedMaskMass a 263168 (-41872552) =
      weightedMaskMass a 4195328 (-41872552) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263168, 4195328, -41872552) (by decide)]
  have h012 : weightedMaskMass a 263168 (-8062329) =
      weightedMaskMass a 4456448 (-8062329) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263168, 4456448, -8062329) (by decide)]
  have h013 : weightedMaskMass a 263169 (26489900) =
      weightedMaskMass a 4195840 (26489900) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263169, 4195840, 26489900) (by decide)]
  have h014 : weightedMaskMass a 263172 (15387549) =
      weightedMaskMass a 263184 (15387549) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263172, 263184, 15387549) (by decide)]
  have h015 : weightedMaskMass a 263172 (-28236534) =
      weightedMaskMass a 265216 (-28236534) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263172, 265216, -28236534) (by decide)]
  have h016 : weightedMaskMass a 263172 (-38938665) =
      weightedMaskMass a 4197376 (-38938665) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263172, 4197376, -38938665) (by decide)]
  have h017 : weightedMaskMass a 263172 (6187843) =
      weightedMaskMass a 4460544 (6187843) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263172, 4460544, 6187843) (by decide)]
  have h018 : weightedMaskMass a 263680 (-19442087) =
      weightedMaskMass a 394240 (-19442087) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263680, 394240, -19442087) (by decide)]
  have h019 : weightedMaskMass a 263680 (28667743) =
      weightedMaskMass a 4456960 (28667743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (263680, 4456960, 28667743) (by decide)]
  have h020 : weightedMaskMass a 264320 (-12043702) =
      weightedMaskMass a 524417 (-12043702) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264320, 524417, -12043702) (by decide)]
  have h021 : weightedMaskMass a 264320 (114310568) =
      weightedMaskMass a 1085440 (114310568) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264320, 1085440, 114310568) (by decide)]
  have h022 : weightedMaskMass a 264320 (12945748) =
      weightedMaskMass a 1310724 (12945748) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264320, 1310724, 12945748) (by decide)]
  have h023 : weightedMaskMass a 264320 (-45380431) =
      weightedMaskMass a 4198464 (-45380431) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264320, 4198464, -45380431) (by decide)]
  have h024 : weightedMaskMass a 264321 (37448275) =
      weightedMaskMass a 526465 (37448275) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264321, 526465, 37448275) (by decide)]
  have h025 : weightedMaskMass a 264321 (-63706913) =
      weightedMaskMass a 1101824 (-63706913) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264321, 1101824, -63706913) (by decide)]
  have h026 : weightedMaskMass a 264324 (-71904430) =
      weightedMaskMass a 1087488 (-71904430) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264324, 1087488, -71904430) (by decide)]
  have h027 : weightedMaskMass a 264324 (47411767) =
      weightedMaskMass a 1312772 (47411767) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264324, 1312772, 47411767) (by decide)]
  have h028 : weightedMaskMass a 264352 (-19619635) =
      weightedMaskMass a 540801 (-19619635) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264352, 540801, -19619635) (by decide)]
  have h029 : weightedMaskMass a 264352 (47787389) =
      weightedMaskMass a 1310756 (47787389) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264352, 1310756, 47787389) (by decide)]
  have h030 : weightedMaskMass a 264352 (-40944444) =
      weightedMaskMass a 4722752 (-40944444) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264352, 4722752, -40944444) (by decide)]
  have h031 : weightedMaskMass a 264356 (-66956395) =
      weightedMaskMass a 1312804 (-66956395) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264356, 1312804, -66956395) (by decide)]
  have h032 : weightedMaskMass a 264448 (-62317213) =
      weightedMaskMass a 532481 (-62317213) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264448, 532481, -62317213) (by decide)]
  have h033 : weightedMaskMass a 264448 (84764877) =
      weightedMaskMass a 598016 (84764877) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264448, 598016, 84764877) (by decide)]
  have h034 : weightedMaskMass a 264464 (68995119) =
      weightedMaskMass a 532993 (68995119) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264464, 532993, 68995119) (by decide)]
  have h035 : weightedMaskMass a 264464 (-147967940) =
      weightedMaskMass a 598020 (-147967940) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264464, 598020, -147967940) (by decide)]
  have h036 : weightedMaskMass a 264480 (46460035) =
      weightedMaskMass a 548865 (46460035) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264480, 548865, 46460035) (by decide)]
  have h037 : weightedMaskMass a 264480 (-105240522) =
      weightedMaskMass a 598024 (-105240522) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (264480, 598024, -105240522) (by decide)]
  have h038 : weightedMaskMass a 266368 (22381689) =
      weightedMaskMass a 528512 (22381689) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266368, 528512, 22381689) (by decide)]
  have h039 : weightedMaskMass a 266368 (-4362624) =
      weightedMaskMass a 1052800 (-4362624) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266368, 1052800, -4362624) (by decide)]
  have h040 : weightedMaskMass a 266369 (10521554) =
      weightedMaskMass a 530560 (10521554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266369, 530560, 10521554) (by decide)]
  have h041 : weightedMaskMass a 266400 (-67774229) =
      weightedMaskMass a 544896 (-67774229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266400, 544896, -67774229) (by decide)]
  have h042 : weightedMaskMass a 266496 (2601158) =
      weightedMaskMass a 536576 (2601158) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266496, 536576, 2601158) (by decide)]
  have h043 : weightedMaskMass a 266528 (-4775176) =
      weightedMaskMass a 552960 (-4775176) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (266528, 552960, -4775176) (by decide)]
  have h044 : weightedMaskMass a 267264 (-90120605) =
      weightedMaskMass a 271360 (-90120605) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (267264, 271360, -90120605) (by decide)]
  have h045 : weightedMaskMass a 267264 (58395366) =
      weightedMaskMass a 4195332 (58395366) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (267264, 4195332, 58395366) (by decide)]
  have h046 : weightedMaskMass a 267264 (16696391) =
      weightedMaskMass a 4456464 (16696391) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (267264, 4456464, 16696391) (by decide)]
  have h047 : weightedMaskMass a 268292 (-36284129) =
      weightedMaskMass a 301056 (-36284129) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268292, 301056, -36284129) (by decide)]
  have h048 : weightedMaskMass a 268296 (47526105) =
      weightedMaskMass a 659457 (47526105) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268296, 659457, 47526105) (by decide)]
  have h049 : weightedMaskMass a 268296 (-67741606) =
      weightedMaskMass a 2752516 (-67741606) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268296, 2752516, -67741606) (by decide)]
  have h050 : weightedMaskMass a 268416 (36517993) =
      weightedMaskMass a 528513 (36517993) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268416, 528513, 36517993) (by decide)]
  have h051 : weightedMaskMass a 268417 (-22181659) =
      weightedMaskMass a 530561 (-22181659) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268417, 530561, -22181659) (by decide)]
  have h052 : weightedMaskMass a 268448 (22566773) =
      weightedMaskMass a 544897 (22566773) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268448, 544897, 22566773) (by decide)]
  have h053 : weightedMaskMass a 268544 (12518689) =
      weightedMaskMass a 536577 (12518689) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268544, 536577, 12518689) (by decide)]
  have h054 : weightedMaskMass a 268576 (-64528058) =
      weightedMaskMass a 552961 (-64528058) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (268576, 552961, -64528058) (by decide)]
  have h055 : weightedMaskMass a 269312 (103100731) =
      weightedMaskMass a 271376 (103100731) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (269312, 271376, 103100731) (by decide)]
  have h056 : weightedMaskMass a 270360 (-25979651) =
      weightedMaskMass a 4720644 (-25979651) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270360, 4720644, -25979651) (by decide)]
  have h057 : weightedMaskMass a 270372 (-144866471) =
      weightedMaskMass a 1573632 (-144866471) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270372, 1573632, -144866471) (by decide)]
  have h058 : weightedMaskMass a 270372 (114908560) =
      weightedMaskMass a 2105380 (114908560) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270372, 2105380, 114908560) (by decide)]
  have h059 : weightedMaskMass a 270372 (38903747) =
      weightedMaskMass a 4229124 (38903747) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270372, 4229124, 38903747) (by decide)]
  have h060 : weightedMaskMass a 270376 (-1393907) =
      weightedMaskMass a 1605888 (-1393907) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270376, 1605888, -1393907) (by decide)]
  have h061 : weightedMaskMass a 270592 (26295364) =
      weightedMaskMass a 532736 (26295364) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270592, 532736, 26295364) (by decide)]
  have h062 : weightedMaskMass a 270592 (-34793982) =
      weightedMaskMass a 2629632 (-34793982) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270592, 2629632, -34793982) (by decide)]
  have h063 : weightedMaskMass a 270592 (61367903) =
      weightedMaskMass a 4194436 (61367903) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270592, 4194436, 61367903) (by decide)]
  have h064 : weightedMaskMass a 270596 (5898402) =
      weightedMaskMass a 4196484 (5898402) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270596, 4196484, 5898402) (by decide)]
  have h065 : weightedMaskMass a 270608 (-26295364) =
      weightedMaskMass a 533248 (-26295364) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270608, 533248, -26295364) (by decide)]
  have h066 : weightedMaskMass a 270608 (2185437) =
      weightedMaskMass a 2629636 (2185437) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270608, 2629636, 2185437) (by decide)]
  have h067 : weightedMaskMass a 270624 (-61548362) =
      weightedMaskMass a 549120 (-61548362) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270624, 549120, -61548362) (by decide)]
  have h068 : weightedMaskMass a 270624 (136965049) =
      weightedMaskMass a 2629640 (136965049) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270624, 2629640, 136965049) (by decide)]
  have h069 : weightedMaskMass a 270624 (-74139620) =
      weightedMaskMass a 4227204 (-74139620) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270624, 4227204, -74139620) (by decide)]
  have h070 : weightedMaskMass a 270628 (-39784242) =
      weightedMaskMass a 4229252 (-39784242) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270628, 4229252, -39784242) (by decide)]
  have h071 : weightedMaskMass a 270849 (-33812059) =
      weightedMaskMass a 526608 (-33812059) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270849, 526608, -33812059) (by decide)]
  have h072 : weightedMaskMass a 271104 (16087504) =
      weightedMaskMass a 532752 (16087504) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (271104, 532752, 16087504) (by decide)]
  have h073 : weightedMaskMass a 271136 (-69890249) =
      weightedMaskMass a 549136 (-69890249) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (271136, 549136, -69890249) (by decide)]
  have h074 : weightedMaskMass a 271361 (-100096060) =
      weightedMaskMass a 4195844 (-100096060) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (271361, 4195844, -100096060) (by decide)]
  have h075 : weightedMaskMass a 271364 (-33073039) =
      weightedMaskMass a 4197380 (-33073039) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (271364, 4197380, -33073039) (by decide)]
  have h076 : weightedMaskMass a 271872 (14534050) =
      weightedMaskMass a 398336 (14534050) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (271872, 398336, 14534050) (by decide)]
  have h077 : weightedMaskMass a 274440 (-21450465) =
      weightedMaskMass a 4849668 (-21450465) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274440, 4849668, -21450465) (by decide)]
  have h078 : weightedMaskMass a 274688 (-23155351) =
      weightedMaskMass a 536832 (-23155351) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274688, 536832, -23155351) (by decide)]
  have h079 : weightedMaskMass a 274720 (5629445) =
      weightedMaskMass a 553216 (5629445) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (274720, 553216, 5629445) (by decide)]
  have h080 : weightedMaskMass a 278657 (-77858094) =
      weightedMaskMass a 526496 (-77858094) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278657, 526496, -77858094) (by decide)]
  have h081 : weightedMaskMass a 278688 (-70831590) =
      weightedMaskMass a 540832 (-70831590) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278688, 540832, -70831590) (by decide)]
  have h082 : weightedMaskMass a 278784 (96674599) =
      weightedMaskMass a 532512 (96674599) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278784, 532512, 96674599) (by decide)]
  have h083 : weightedMaskMass a 278784 (58406635) =
      weightedMaskMass a 1581056 (58406635) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278784, 1581056, 58406635) (by decide)]
  have h084 : weightedMaskMass a 278800 (-115623258) =
      weightedMaskMass a 533024 (-115623258) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278800, 533024, -115623258) (by decide)]
  have h085 : weightedMaskMass a 278800 (-71353629) =
      weightedMaskMass a 1581060 (-71353629) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278800, 1581060, -71353629) (by decide)]
  have h086 : weightedMaskMass a 278816 (-88845571) =
      weightedMaskMass a 548896 (-88845571) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278816, 548896, -88845571) (by decide)]
  have h087 : weightedMaskMass a 278816 (-24578579) =
      weightedMaskMass a 1581064 (-24578579) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (278816, 1581064, -24578579) (by decide)]
  have h088 : weightedMaskMass a 279556 (-78302555) =
      weightedMaskMass a 279568 (-78302555) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (279556, 279568, -78302555) (by decide)]
  have h089 : weightedMaskMass a 282625 (-13339382) =
      weightedMaskMass a 530464 (-13339382) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282625, 530464, -13339382) (by decide)]
  have h090 : weightedMaskMass a 282625 (-73452979) =
      weightedMaskMass a 2099268 (-73452979) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282625, 2099268, -73452979) (by decide)]
  have h091 : weightedMaskMass a 282656 (-92329805) =
      weightedMaskMass a 544800 (-92329805) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282656, 544800, -92329805) (by decide)]
  have h092 : weightedMaskMass a 282656 (57328251) =
      weightedMaskMass a 1057026 (57328251) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282656, 1057026, 57328251) (by decide)]
  have h093 : weightedMaskMass a 282656 (-3175274) =
      weightedMaskMass a 2623520 (-3175274) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282656, 2623520, -3175274) (by decide)]
  have h094 : weightedMaskMass a 282656 (30032864) =
      weightedMaskMass a 2656256 (30032864) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282656, 2656256, 30032864) (by decide)]
  have h095 : weightedMaskMass a 282752 (41699610) =
      weightedMaskMass a 528544 (41699610) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282752, 528544, 41699610) (by decide)]
  have h096 : weightedMaskMass a 282753 (-103348365) =
      weightedMaskMass a 530592 (-103348365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282753, 530592, -103348365) (by decide)]
  have h097 : weightedMaskMass a 282784 (36200581) =
      weightedMaskMass a 544928 (36200581) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282784, 544928, 36200581) (by decide)]
  have h098 : weightedMaskMass a 282880 (-3660804) =
      weightedMaskMass a 536608 (-3660804) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282880, 536608, -3660804) (by decide)]
  have h099 : weightedMaskMass a 282912 (66907) =
      weightedMaskMass a 552992 (66907) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (282912, 552992, 66907) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt14 s.val : ℝ)) = (((((((weightedMaskMass a 262400 (-63131493) + (-weightedMaskMass a 4194432 (-63131493) + weightedMaskMass a 262404 (-38895352))) + (-weightedMaskMass a 4196480 (-38895352) + (weightedMaskMass a 262416 (4735036) + -weightedMaskMass a 532484 (4735036)))) + ((weightedMaskMass a 262416 (-32821355) + (-weightedMaskMass a 532992 (-32821355) + weightedMaskMass a 262416 (65613579))) + (-weightedMaskMass a 5243008 (65613579) + (weightedMaskMass a 262432 (-11085028) + -weightedMaskMass a 532488 (-11085028))))) + (((weightedMaskMass a 262432 (-10459004) + (-weightedMaskMass a 548864 (-10459004) + weightedMaskMass a 262432 (687349))) + (-weightedMaskMass a 4227200 (687349) + (weightedMaskMass a 262436 (39238959) + -weightedMaskMass a 4229248 (39238959)))) + ((weightedMaskMass a 262912 (1718849) + (-weightedMaskMass a 532496 (1718849) + weightedMaskMass a 262944 (52083896))) + ((-weightedMaskMass a 548880 (52083896) + weightedMaskMass a 263168 (-41872552)) + (-weightedMaskMass a 4195328 (-41872552) + weightedMaskMass a 263168 (-8062329)))))) + ((((-weightedMaskMass a 4456448 (-8062329) + (weightedMaskMass a 263169 (26489900) + -weightedMaskMass a 4195840 (26489900))) + (weightedMaskMass a 263172 (15387549) + (-weightedMaskMass a 263184 (15387549) + weightedMaskMass a 263172 (-28236534)))) + ((-weightedMaskMass a 265216 (-28236534) + (weightedMaskMass a 263172 (-38938665) + -weightedMaskMass a 4197376 (-38938665))) + (weightedMaskMass a 263172 (6187843) + (-weightedMaskMass a 4460544 (6187843) + weightedMaskMass a 263680 (-19442087))))) + (((-weightedMaskMass a 394240 (-19442087) + (weightedMaskMass a 263680 (28667743) + -weightedMaskMass a 4456960 (28667743))) + (weightedMaskMass a 264320 (-12043702) + (-weightedMaskMass a 524417 (-12043702) + weightedMaskMass a 264320 (114310568)))) + ((-weightedMaskMass a 1085440 (114310568) + (weightedMaskMass a 264320 (12945748) + -weightedMaskMass a 1310724 (12945748))) + ((weightedMaskMass a 264320 (-45380431) + -weightedMaskMass a 4198464 (-45380431)) + (weightedMaskMass a 264321 (37448275) + -weightedMaskMass a 526465 (37448275))))))) + (((((weightedMaskMass a 264321 (-63706913) + (-weightedMaskMass a 1101824 (-63706913) + weightedMaskMass a 264324 (-71904430))) + (-weightedMaskMass a 1087488 (-71904430) + (weightedMaskMass a 264324 (47411767) + -weightedMaskMass a 1312772 (47411767)))) + ((weightedMaskMass a 264352 (-19619635) + (-weightedMaskMass a 540801 (-19619635) + weightedMaskMass a 264352 (47787389))) + (-weightedMaskMass a 1310756 (47787389) + (weightedMaskMass a 264352 (-40944444) + -weightedMaskMass a 4722752 (-40944444))))) + (((weightedMaskMass a 264356 (-66956395) + (-weightedMaskMass a 1312804 (-66956395) + weightedMaskMass a 264448 (-62317213))) + (-weightedMaskMass a 532481 (-62317213) + (weightedMaskMass a 264448 (84764877) + -weightedMaskMass a 598016 (84764877)))) + ((weightedMaskMass a 264464 (68995119) + (-weightedMaskMass a 532993 (68995119) + weightedMaskMass a 264464 (-147967940))) + ((-weightedMaskMass a 598020 (-147967940) + weightedMaskMass a 264480 (46460035)) + (-weightedMaskMass a 548865 (46460035) + weightedMaskMass a 264480 (-105240522)))))) + ((((-weightedMaskMass a 598024 (-105240522) + (weightedMaskMass a 266368 (22381689) + -weightedMaskMass a 528512 (22381689))) + (weightedMaskMass a 266368 (-4362624) + (-weightedMaskMass a 1052800 (-4362624) + weightedMaskMass a 266369 (10521554)))) + ((-weightedMaskMass a 530560 (10521554) + (weightedMaskMass a 266400 (-67774229) + -weightedMaskMass a 544896 (-67774229))) + (weightedMaskMass a 266496 (2601158) + (-weightedMaskMass a 536576 (2601158) + weightedMaskMass a 266528 (-4775176))))) + (((-weightedMaskMass a 552960 (-4775176) + (weightedMaskMass a 267264 (-90120605) + -weightedMaskMass a 271360 (-90120605))) + (weightedMaskMass a 267264 (58395366) + (-weightedMaskMass a 4195332 (58395366) + weightedMaskMass a 267264 (16696391)))) + ((-weightedMaskMass a 4456464 (16696391) + (weightedMaskMass a 268292 (-36284129) + -weightedMaskMass a 301056 (-36284129))) + ((weightedMaskMass a 268296 (47526105) + -weightedMaskMass a 659457 (47526105)) + (weightedMaskMass a 268296 (-67741606) + -weightedMaskMass a 2752516 (-67741606)))))))) + ((((((weightedMaskMass a 268416 (36517993) + (-weightedMaskMass a 528513 (36517993) + weightedMaskMass a 268417 (-22181659))) + (-weightedMaskMass a 530561 (-22181659) + (weightedMaskMass a 268448 (22566773) + -weightedMaskMass a 544897 (22566773)))) + ((weightedMaskMass a 268544 (12518689) + (-weightedMaskMass a 536577 (12518689) + weightedMaskMass a 268576 (-64528058))) + (-weightedMaskMass a 552961 (-64528058) + (weightedMaskMass a 269312 (103100731) + -weightedMaskMass a 271376 (103100731))))) + (((weightedMaskMass a 270360 (-25979651) + (-weightedMaskMass a 4720644 (-25979651) + weightedMaskMass a 270372 (-144866471))) + (-weightedMaskMass a 1573632 (-144866471) + (weightedMaskMass a 270372 (114908560) + -weightedMaskMass a 2105380 (114908560)))) + ((weightedMaskMass a 270372 (38903747) + (-weightedMaskMass a 4229124 (38903747) + weightedMaskMass a 270376 (-1393907))) + ((-weightedMaskMass a 1605888 (-1393907) + weightedMaskMass a 270592 (26295364)) + (-weightedMaskMass a 532736 (26295364) + weightedMaskMass a 270592 (-34793982)))))) + ((((-weightedMaskMass a 2629632 (-34793982) + (weightedMaskMass a 270592 (61367903) + -weightedMaskMass a 4194436 (61367903))) + (weightedMaskMass a 270596 (5898402) + (-weightedMaskMass a 4196484 (5898402) + weightedMaskMass a 270608 (-26295364)))) + ((-weightedMaskMass a 533248 (-26295364) + (weightedMaskMass a 270608 (2185437) + -weightedMaskMass a 2629636 (2185437))) + (weightedMaskMass a 270624 (-61548362) + (-weightedMaskMass a 549120 (-61548362) + weightedMaskMass a 270624 (136965049))))) + (((-weightedMaskMass a 2629640 (136965049) + (weightedMaskMass a 270624 (-74139620) + -weightedMaskMass a 4227204 (-74139620))) + (weightedMaskMass a 270628 (-39784242) + (-weightedMaskMass a 4229252 (-39784242) + weightedMaskMass a 270849 (-33812059)))) + ((-weightedMaskMass a 526608 (-33812059) + (weightedMaskMass a 271104 (16087504) + -weightedMaskMass a 532752 (16087504))) + ((weightedMaskMass a 271136 (-69890249) + -weightedMaskMass a 549136 (-69890249)) + (weightedMaskMass a 271361 (-100096060) + -weightedMaskMass a 4195844 (-100096060))))))) + (((((weightedMaskMass a 271364 (-33073039) + (-weightedMaskMass a 4197380 (-33073039) + weightedMaskMass a 271872 (14534050))) + (-weightedMaskMass a 398336 (14534050) + (weightedMaskMass a 274440 (-21450465) + -weightedMaskMass a 4849668 (-21450465)))) + ((weightedMaskMass a 274688 (-23155351) + (-weightedMaskMass a 536832 (-23155351) + weightedMaskMass a 274720 (5629445))) + (-weightedMaskMass a 553216 (5629445) + (weightedMaskMass a 278657 (-77858094) + -weightedMaskMass a 526496 (-77858094))))) + (((weightedMaskMass a 278688 (-70831590) + (-weightedMaskMass a 540832 (-70831590) + weightedMaskMass a 278784 (96674599))) + (-weightedMaskMass a 532512 (96674599) + (weightedMaskMass a 278784 (58406635) + -weightedMaskMass a 1581056 (58406635)))) + ((weightedMaskMass a 278800 (-115623258) + (-weightedMaskMass a 533024 (-115623258) + weightedMaskMass a 278800 (-71353629))) + ((-weightedMaskMass a 1581060 (-71353629) + weightedMaskMass a 278816 (-88845571)) + (-weightedMaskMass a 548896 (-88845571) + weightedMaskMass a 278816 (-24578579)))))) + ((((-weightedMaskMass a 1581064 (-24578579) + (weightedMaskMass a 279556 (-78302555) + -weightedMaskMass a 279568 (-78302555))) + (weightedMaskMass a 282625 (-13339382) + (-weightedMaskMass a 530464 (-13339382) + weightedMaskMass a 282625 (-73452979)))) + ((-weightedMaskMass a 2099268 (-73452979) + (weightedMaskMass a 282656 (-92329805) + -weightedMaskMass a 544800 (-92329805))) + (weightedMaskMass a 282656 (57328251) + (-weightedMaskMass a 1057026 (57328251) + weightedMaskMass a 282656 (-3175274))))) + (((-weightedMaskMass a 2623520 (-3175274) + (weightedMaskMass a 282656 (30032864) + -weightedMaskMass a 2656256 (30032864))) + (weightedMaskMass a 282752 (41699610) + (-weightedMaskMass a 528544 (41699610) + weightedMaskMass a 282753 (-103348365)))) + ((-weightedMaskMass a 530592 (-103348365) + (weightedMaskMass a 282784 (36200581) + -weightedMaskMass a 544928 (36200581))) + ((weightedMaskMass a 282880 (-3660804) + -weightedMaskMass a 536608 (-3660804)) + (weightedMaskMass a 282912 (66907) + -weightedMaskMass a 552992 (66907))))))))) := by
      simp only [atomCongruenceContributionInt14, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
