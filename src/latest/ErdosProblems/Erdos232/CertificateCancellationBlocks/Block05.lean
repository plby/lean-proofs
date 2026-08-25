/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock05_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights05, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt05 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 5122 (-73968543) =
      weightedMaskMass a 4718608 (-73968543) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5122, 4718608, -73968543) (by decide)]
  have h001 : weightedMaskMass a 5124 (179750837) =
      weightedMaskMass a 529408 (179750837) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5124, 529408, 179750837) (by decide)]
  have h002 : weightedMaskMass a 5124 (-138987112) =
      weightedMaskMass a 2105408 (-138987112) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5124, 2105408, -138987112) (by decide)]
  have h003 : weightedMaskMass a 5124 (-22048440) =
      weightedMaskMass a 2106368 (-22048440) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5124, 2106368, -22048440) (by decide)]
  have h004 : weightedMaskMass a 5124 (39160263) =
      weightedMaskMass a 4194322 (39160263) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5124, 4194322, 39160263) (by decide)]
  have h005 : weightedMaskMass a 5124 (-75345577) =
      weightedMaskMass a 4194340 (-75345577) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5124, 4194340, -75345577) (by decide)]
  have h006 : weightedMaskMass a 5184 (81950810) =
      weightedMaskMass a 524548 (81950810) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5184, 524548, 81950810) (by decide)]
  have h007 : weightedMaskMass a 5184 (-102049589) =
      weightedMaskMass a 2105856 (-102049589) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5184, 2105856, -102049589) (by decide)]
  have h008 : weightedMaskMass a 5184 (59030882) =
      weightedMaskMass a 5242884 (59030882) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5184, 5242884, 59030882) (by decide)]
  have h009 : weightedMaskMass a 5184 (-14915616) =
      weightedMaskMass a 5259264 (-14915616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5184, 5259264, -14915616) (by decide)]
  have h010 : weightedMaskMass a 5186 (-99018767) =
      weightedMaskMass a 540932 (-99018767) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5186, 540932, -99018767) (by decide)]
  have h011 : weightedMaskMass a 5186 (110767810) =
      weightedMaskMass a 2105864 (110767810) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5186, 2105864, 110767810) (by decide)]
  have h012 : weightedMaskMass a 5186 (-4088531) =
      weightedMaskMass a 5275652 (-4088531) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5186, 5275652, -4088531) (by decide)]
  have h013 : weightedMaskMass a 1573124 (111672038) =
      weightedMaskMass a 2105888 (111672038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573124, 2105888, 111672038) (by decide)]
  have h014 : weightedMaskMass a 5188 (-23093813) =
      weightedMaskMass a 2106880 (-23093813) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (5188, 2106880, -23093813) (by decide)]
  have h015 : weightedMaskMass a 6145 (-730628) =
      weightedMaskMass a 66576 (-730628) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6145, 66576, -730628) (by decide)]
  have h016 : weightedMaskMass a 6145 (110368297) =
      weightedMaskMass a 557057 (110368297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6145, 557057, 110368297) (by decide)]
  have h017 : weightedMaskMass a 6145 (3714029) =
      weightedMaskMass a 2359300 (3714029) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6145, 2359300, 3714029) (by decide)]
  have h018 : weightedMaskMass a 6145 (-81225683) =
      weightedMaskMass a 4231168 (-81225683) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6145, 4231168, -81225683) (by decide)]
  have h019 : weightedMaskMass a 6148 (4812429) =
      weightedMaskMass a 266244 (4812429) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 266244, 4812429) (by decide)]
  have h020 : weightedMaskMass a 6148 (-97033279) =
      weightedMaskMass a 296960 (-97033279) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 296960, -97033279) (by decide)]
  have h021 : weightedMaskMass a 6148 (-7715012) =
      weightedMaskMass a 299008 (-7715012) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 299008, -7715012) (by decide)]
  have h022 : weightedMaskMass a 6148 (57662388) =
      weightedMaskMass a 327696 (57662388) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 327696, 57662388) (by decide)]
  have h023 : weightedMaskMass a 6148 (-10239042) =
      weightedMaskMass a 2098180 (-10239042) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 2098180, -10239042) (by decide)]
  have h024 : weightedMaskMass a 6148 (104112771) =
      weightedMaskMass a 4196384 (104112771) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6148, 4196384, 104112771) (by decide)]
  have h025 : weightedMaskMass a 6152 (-42556021) =
      weightedMaskMass a 655361 (-42556021) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6152, 655361, -42556021) (by decide)]
  have h026 : weightedMaskMass a 6152 (113532413) =
      weightedMaskMass a 2097284 (113532413) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6152, 2097284, 113532413) (by decide)]
  have h027 : weightedMaskMass a 6152 (10017538) =
      weightedMaskMass a 2752512 (10017538) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6152, 2752512, 10017538) (by decide)]
  have h028 : weightedMaskMass a 6180 (27836683) =
      weightedMaskMass a 2100228 (27836683) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6180, 2100228, 27836683) (by decide)]
  have h029 : weightedMaskMass a 6184 (-47432312) =
      weightedMaskMass a 2099332 (-47432312) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6184, 2099332, -47432312) (by decide)]
  have h030 : weightedMaskMass a 6209 (-108637105) =
      weightedMaskMass a 82960 (-108637105) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6209, 82960, -108637105) (by decide)]
  have h031 : weightedMaskMass a 6209 (194812359) =
      weightedMaskMass a 2375684 (194812359) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6209, 2375684, 194812359) (by decide)]
  have h032 : weightedMaskMass a 6212 (35592453) =
      weightedMaskMass a 282628 (35592453) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6212, 282628, 35592453) (by decide)]
  have h033 : weightedMaskMass a 6212 (12876175) =
      weightedMaskMass a 2098692 (12876175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6212, 2098692, 12876175) (by decide)]
  have h034 : weightedMaskMass a 6304 (-114578432) =
      weightedMaskMass a 20609 (-114578432) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6304, 20609, -114578432) (by decide)]
  have h035 : weightedMaskMass a 6400 (12474697) =
      weightedMaskMass a 12289 (12474697) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6400, 12289, 12474697) (by decide)]
  have h036 : weightedMaskMass a 6432 (-35194826) =
      weightedMaskMass a 28673 (-35194826) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (6432, 28673, -35194826) (by decide)]
  have h037 : weightedMaskMass a 7168 (-5237685) =
      weightedMaskMass a 270340 (-5237685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7168, 270340, -5237685) (by decide)]
  have h038 : weightedMaskMass a 7168 (-79378689) =
      weightedMaskMass a 270352 (-79378689) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7168, 270352, -79378689) (by decide)]
  have h039 : weightedMaskMass a 7168 (109329554) =
      weightedMaskMass a 525056 (109329554) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7168, 525056, 109329554) (by decide)]
  have h040 : weightedMaskMass a 7168 (-33741535) =
      weightedMaskMass a 2105348 (-33741535) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7168, 2105348, -33741535) (by decide)]
  have h041 : weightedMaskMass a 7168 (-9181734) =
      weightedMaskMass a 4196356 (-9181734) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7168, 4196356, -9181734) (by decide)]
  have h042 : weightedMaskMass a 7172 (-55604907) =
      weightedMaskMass a 2106372 (-55604907) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7172, 2106372, -55604907) (by decide)]
  have h043 : weightedMaskMass a 7172 (49200955) =
      weightedMaskMass a 4196388 (49200955) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7172, 4196388, 49200955) (by decide)]
  have h044 : weightedMaskMass a 7232 (-107554760) =
      weightedMaskMass a 525060 (-107554760) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7232, 525060, -107554760) (by decide)]
  have h045 : weightedMaskMass a 7232 (105763018) =
      weightedMaskMass a 2105860 (105763018) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7232, 2105860, 105763018) (by decide)]
  have h046 : weightedMaskMass a 7236 (-20090516) =
      weightedMaskMass a 2106884 (-20090516) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (7236, 2106884, -20090516) (by decide)]
  have h047 : weightedMaskMass a 8216 (-27239267) =
      weightedMaskMass a 53248 (-27239267) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 53248, -27239267) (by decide)]
  have h048 : weightedMaskMass a 8216 (-9360332) =
      weightedMaskMass a 65556 (-9360332) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 65556, -9360332) (by decide)]
  have h049 : weightedMaskMass a 8216 (27258152) =
      weightedMaskMass a 73730 (27258152) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 73730, 27258152) (by decide)]
  have h050 : weightedMaskMass a 8216 (10837394) =
      weightedMaskMass a 264193 (10837394) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 264193, 10837394) (by decide)]
  have h051 : weightedMaskMass a 8216 (59998238) =
      weightedMaskMass a 526337 (59998238) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 526337, 59998238) (by decide)]
  have h052 : weightedMaskMass a 8216 (31198930) =
      weightedMaskMass a 2097172 (31198930) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 2097172, 31198930) (by decide)]
  have h053 : weightedMaskMass a 8216 (-117019848) =
      weightedMaskMass a 2361344 (-117019848) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 2361344, -117019848) (by decide)]
  have h054 : weightedMaskMass a 8216 (-81810608) =
      weightedMaskMass a 2490368 (-81810608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 2490368, -81810608) (by decide)]
  have h055 : weightedMaskMass a 8216 (88841891) =
      weightedMaskMass a 4720640 (88841891) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8216, 4720640, 88841891) (by decide)]
  have h056 : weightedMaskMass a 8228 (-149473517) =
      weightedMaskMass a 34820 (-149473517) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8228, 34820, -149473517) (by decide)]
  have h057 : weightedMaskMass a 8228 (-62015314) =
      weightedMaskMass a 132100 (-62015314) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8228, 132100, -62015314) (by decide)]
  have h058 : weightedMaskMass a 8228 (168830371) =
      weightedMaskMass a 1048594 (168830371) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8228, 1048594, 168830371) (by decide)]
  have h059 : weightedMaskMass a 8228 (8633219) =
      weightedMaskMass a 1573376 (8633219) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8228, 1573376, 8633219) (by decide)]
  have h060 : weightedMaskMass a 8232 (208901773) =
      weightedMaskMass a 49156 (208901773) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 49156, 208901773) (by decide)]
  have h061 : weightedMaskMass a 8232 (-62060474) =
      weightedMaskMass a 65602 (-62060474) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 65602, -62060474) (by decide)]
  have h062 : weightedMaskMass a 8232 (-202279724) =
      weightedMaskMass a 132098 (-202279724) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 132098, -202279724) (by decide)]
  have h063 : weightedMaskMass a 8232 (655583) =
      weightedMaskMass a 262688 (655583) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 262688, 655583) (by decide)]
  have h064 : weightedMaskMass a 8232 (67507382) =
      weightedMaskMass a 540688 (67507382) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 540688, 67507382) (by decide)]
  have h065 : weightedMaskMass a 8232 (26661368) =
      weightedMaskMass a 1048596 (26661368) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 1048596, 26661368) (by decide)]
  have h066 : weightedMaskMass a 8232 (115499229) =
      weightedMaskMass a 1065216 (115499229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 1065216, 115499229) (by decide)]
  have h067 : weightedMaskMass a 8232 (22808051) =
      weightedMaskMass a 1589248 (22808051) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 1589248, 22808051) (by decide)]
  have h068 : weightedMaskMass a 8232 (-185449243) =
      weightedMaskMass a 1605632 (-185449243) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 1605632, -185449243) (by decide)]
  have h069 : weightedMaskMass a 8232 (71062930) =
      weightedMaskMass a 2097192 (71062930) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 2097192, 71062930) (by decide)]
  have h070 : weightedMaskMass a 8232 (-104598501) =
      weightedMaskMass a 2359808 (-104598501) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8232, 2359808, -104598501) (by decide)]
  have h071 : weightedMaskMass a 8257 (91051151) =
      weightedMaskMass a 344064 (91051151) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8257, 344064, 91051151) (by decide)]
  have h072 : weightedMaskMass a 8257 (-88071621) =
      weightedMaskMass a 2114560 (-88071621) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8257, 2114560, -88071621) (by decide)]
  have h073 : weightedMaskMass a 8464 (56031968) =
      weightedMaskMass a 8960 (56031968) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 8960, 56031968) (by decide)]
  have h074 : weightedMaskMass a 8464 (6984657) =
      weightedMaskMass a 98320 (6984657) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 98320, 6984657) (by decide)]
  have h075 : weightedMaskMass a 8464 (2120149) =
      weightedMaskMass a 102400 (2120149) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 102400, 2120149) (by decide)]
  have h076 : weightedMaskMass a 8464 (-6469208) =
      weightedMaskMass a 135169 (-6469208) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 135169, -6469208) (by decide)]
  have h077 : weightedMaskMass a 8464 (-9783616) =
      weightedMaskMass a 264200 (-9783616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 264200, -9783616) (by decide)]
  have h078 : weightedMaskMass a 8464 (3506902) =
      weightedMaskMass a 2621444 (3506902) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 2621444, 3506902) (by decide)]
  have h079 : weightedMaskMass a 8464 (-47002674) =
      weightedMaskMass a 5244928 (-47002674) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8464, 5244928, -47002674) (by decide)]
  have h080 : weightedMaskMass a 8466 (17134035) =
      weightedMaskMass a 8962 (17134035) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8466, 8962, 17134035) (by decide)]
  have h081 : weightedMaskMass a 8466 (-2598175) =
      weightedMaskMass a 264216 (-2598175) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8466, 264216, -2598175) (by decide)]
  have h082 : weightedMaskMass a 8466 (-20909598) =
      weightedMaskMass a 397313 (-20909598) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8466, 397313, -20909598) (by decide)]
  have h083 : weightedMaskMass a 8466 (-49091170) =
      weightedMaskMass a 2623492 (-49091170) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8466, 2623492, -49091170) (by decide)]
  have h084 : weightedMaskMass a 8468 (-42969778) =
      weightedMaskMass a 264232 (-42969778) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8468, 264232, -42969778) (by decide)]
  have h085 : weightedMaskMass a 8468 (-21240608) =
      weightedMaskMass a 5277696 (-21240608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8468, 5277696, -21240608) (by decide)]
  have h086 : weightedMaskMass a 8472 (-55288889) =
      weightedMaskMass a 118784 (-55288889) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8472, 118784, -55288889) (by decide)]
  have h087 : weightedMaskMass a 8472 (-19567772) =
      weightedMaskMass a 264201 (-19567772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8472, 264201, -19567772) (by decide)]
  have h088 : weightedMaskMass a 8480 (7947658) =
      weightedMaskMass a 16672 (7947658) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 16672, 7947658) (by decide)]
  have h089 : weightedMaskMass a 8480 (35380610) =
      weightedMaskMass a 24608 (35380610) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 24608, 35380610) (by decide)]
  have h090 : weightedMaskMass a 8480 (-6011076) =
      weightedMaskMass a 24832 (-6011076) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 24832, -6011076) (by decide)]
  have h091 : weightedMaskMass a 8480 (-25115112) =
      weightedMaskMass a 32900 (-25115112) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 32900, -25115112) (by decide)]
  have h092 : weightedMaskMass a 8480 (-58054687) =
      weightedMaskMass a 98368 (-58054687) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 98368, -58054687) (by decide)]
  have h093 : weightedMaskMass a 8480 (-8427241) =
      weightedMaskMass a 1572872 (-8427241) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 1572872, -8427241) (by decide)]
  have h094 : weightedMaskMass a 8480 (51517551) =
      weightedMaskMass a 2621448 (51517551) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 2621448, 51517551) (by decide)]
  have h095 : weightedMaskMass a 8480 (-50287357) =
      weightedMaskMass a 3145736 (-50287357) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 3145736, -50287357) (by decide)]
  have h096 : weightedMaskMass a 8480 (-42083519) =
      weightedMaskMass a 3670016 (-42083519) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8480, 3670016, -42083519) (by decide)]
  have h097 : weightedMaskMass a 8482 (54385914) =
      weightedMaskMass a 24834 (54385914) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8482, 24834, 54385914) (by decide)]
  have h098 : weightedMaskMass a 8482 (23643950) =
      weightedMaskMass a 98436 (23643950) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8482, 98436, 23643950) (by decide)]
  have h099 : weightedMaskMass a 8482 (-64548574) =
      weightedMaskMass a 2623496 (-64548574) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (8482, 2623496, -64548574) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt05 s.val : ℝ)) = (((((((weightedMaskMass a 5122 (-73968543) + (-weightedMaskMass a 4718608 (-73968543) + weightedMaskMass a 5124 (179750837))) + (-weightedMaskMass a 529408 (179750837) + (weightedMaskMass a 5124 (-138987112) + -weightedMaskMass a 2105408 (-138987112)))) + ((weightedMaskMass a 5124 (-22048440) + (-weightedMaskMass a 2106368 (-22048440) + weightedMaskMass a 5124 (39160263))) + (-weightedMaskMass a 4194322 (39160263) + (weightedMaskMass a 5124 (-75345577) + -weightedMaskMass a 4194340 (-75345577))))) + (((weightedMaskMass a 5184 (81950810) + (-weightedMaskMass a 524548 (81950810) + weightedMaskMass a 5184 (-102049589))) + (-weightedMaskMass a 2105856 (-102049589) + (weightedMaskMass a 5184 (59030882) + -weightedMaskMass a 5242884 (59030882)))) + ((weightedMaskMass a 5184 (-14915616) + (-weightedMaskMass a 5259264 (-14915616) + weightedMaskMass a 5186 (-99018767))) + ((-weightedMaskMass a 540932 (-99018767) + weightedMaskMass a 5186 (110767810)) + (-weightedMaskMass a 2105864 (110767810) + weightedMaskMass a 5186 (-4088531)))))) + ((((-weightedMaskMass a 5275652 (-4088531) + (weightedMaskMass a 1573124 (111672038) + -weightedMaskMass a 2105888 (111672038))) + (weightedMaskMass a 5188 (-23093813) + (-weightedMaskMass a 2106880 (-23093813) + weightedMaskMass a 6145 (-730628)))) + ((-weightedMaskMass a 66576 (-730628) + (weightedMaskMass a 6145 (110368297) + -weightedMaskMass a 557057 (110368297))) + (weightedMaskMass a 6145 (3714029) + (-weightedMaskMass a 2359300 (3714029) + weightedMaskMass a 6145 (-81225683))))) + (((-weightedMaskMass a 4231168 (-81225683) + (weightedMaskMass a 6148 (4812429) + -weightedMaskMass a 266244 (4812429))) + (weightedMaskMass a 6148 (-97033279) + (-weightedMaskMass a 296960 (-97033279) + weightedMaskMass a 6148 (-7715012)))) + ((-weightedMaskMass a 299008 (-7715012) + (weightedMaskMass a 6148 (57662388) + -weightedMaskMass a 327696 (57662388))) + ((weightedMaskMass a 6148 (-10239042) + -weightedMaskMass a 2098180 (-10239042)) + (weightedMaskMass a 6148 (104112771) + -weightedMaskMass a 4196384 (104112771))))))) + (((((weightedMaskMass a 6152 (-42556021) + (-weightedMaskMass a 655361 (-42556021) + weightedMaskMass a 6152 (113532413))) + (-weightedMaskMass a 2097284 (113532413) + (weightedMaskMass a 6152 (10017538) + -weightedMaskMass a 2752512 (10017538)))) + ((weightedMaskMass a 6180 (27836683) + (-weightedMaskMass a 2100228 (27836683) + weightedMaskMass a 6184 (-47432312))) + (-weightedMaskMass a 2099332 (-47432312) + (weightedMaskMass a 6209 (-108637105) + -weightedMaskMass a 82960 (-108637105))))) + (((weightedMaskMass a 6209 (194812359) + (-weightedMaskMass a 2375684 (194812359) + weightedMaskMass a 6212 (35592453))) + (-weightedMaskMass a 282628 (35592453) + (weightedMaskMass a 6212 (12876175) + -weightedMaskMass a 2098692 (12876175)))) + ((weightedMaskMass a 6304 (-114578432) + (-weightedMaskMass a 20609 (-114578432) + weightedMaskMass a 6400 (12474697))) + ((-weightedMaskMass a 12289 (12474697) + weightedMaskMass a 6432 (-35194826)) + (-weightedMaskMass a 28673 (-35194826) + weightedMaskMass a 7168 (-5237685)))))) + ((((-weightedMaskMass a 270340 (-5237685) + (weightedMaskMass a 7168 (-79378689) + -weightedMaskMass a 270352 (-79378689))) + (weightedMaskMass a 7168 (109329554) + (-weightedMaskMass a 525056 (109329554) + weightedMaskMass a 7168 (-33741535)))) + ((-weightedMaskMass a 2105348 (-33741535) + (weightedMaskMass a 7168 (-9181734) + -weightedMaskMass a 4196356 (-9181734))) + (weightedMaskMass a 7172 (-55604907) + (-weightedMaskMass a 2106372 (-55604907) + weightedMaskMass a 7172 (49200955))))) + (((-weightedMaskMass a 4196388 (49200955) + (weightedMaskMass a 7232 (-107554760) + -weightedMaskMass a 525060 (-107554760))) + (weightedMaskMass a 7232 (105763018) + (-weightedMaskMass a 2105860 (105763018) + weightedMaskMass a 7236 (-20090516)))) + ((-weightedMaskMass a 2106884 (-20090516) + (weightedMaskMass a 8216 (-27239267) + -weightedMaskMass a 53248 (-27239267))) + ((weightedMaskMass a 8216 (-9360332) + -weightedMaskMass a 65556 (-9360332)) + (weightedMaskMass a 8216 (27258152) + -weightedMaskMass a 73730 (27258152)))))))) + ((((((weightedMaskMass a 8216 (10837394) + (-weightedMaskMass a 264193 (10837394) + weightedMaskMass a 8216 (59998238))) + (-weightedMaskMass a 526337 (59998238) + (weightedMaskMass a 8216 (31198930) + -weightedMaskMass a 2097172 (31198930)))) + ((weightedMaskMass a 8216 (-117019848) + (-weightedMaskMass a 2361344 (-117019848) + weightedMaskMass a 8216 (-81810608))) + (-weightedMaskMass a 2490368 (-81810608) + (weightedMaskMass a 8216 (88841891) + -weightedMaskMass a 4720640 (88841891))))) + (((weightedMaskMass a 8228 (-149473517) + (-weightedMaskMass a 34820 (-149473517) + weightedMaskMass a 8228 (-62015314))) + (-weightedMaskMass a 132100 (-62015314) + (weightedMaskMass a 8228 (168830371) + -weightedMaskMass a 1048594 (168830371)))) + ((weightedMaskMass a 8228 (8633219) + (-weightedMaskMass a 1573376 (8633219) + weightedMaskMass a 8232 (208901773))) + ((-weightedMaskMass a 49156 (208901773) + weightedMaskMass a 8232 (-62060474)) + (-weightedMaskMass a 65602 (-62060474) + weightedMaskMass a 8232 (-202279724)))))) + ((((-weightedMaskMass a 132098 (-202279724) + (weightedMaskMass a 8232 (655583) + -weightedMaskMass a 262688 (655583))) + (weightedMaskMass a 8232 (67507382) + (-weightedMaskMass a 540688 (67507382) + weightedMaskMass a 8232 (26661368)))) + ((-weightedMaskMass a 1048596 (26661368) + (weightedMaskMass a 8232 (115499229) + -weightedMaskMass a 1065216 (115499229))) + (weightedMaskMass a 8232 (22808051) + (-weightedMaskMass a 1589248 (22808051) + weightedMaskMass a 8232 (-185449243))))) + (((-weightedMaskMass a 1605632 (-185449243) + (weightedMaskMass a 8232 (71062930) + -weightedMaskMass a 2097192 (71062930))) + (weightedMaskMass a 8232 (-104598501) + (-weightedMaskMass a 2359808 (-104598501) + weightedMaskMass a 8257 (91051151)))) + ((-weightedMaskMass a 344064 (91051151) + (weightedMaskMass a 8257 (-88071621) + -weightedMaskMass a 2114560 (-88071621))) + ((weightedMaskMass a 8464 (56031968) + -weightedMaskMass a 8960 (56031968)) + (weightedMaskMass a 8464 (6984657) + -weightedMaskMass a 98320 (6984657))))))) + (((((weightedMaskMass a 8464 (2120149) + (-weightedMaskMass a 102400 (2120149) + weightedMaskMass a 8464 (-6469208))) + (-weightedMaskMass a 135169 (-6469208) + (weightedMaskMass a 8464 (-9783616) + -weightedMaskMass a 264200 (-9783616)))) + ((weightedMaskMass a 8464 (3506902) + (-weightedMaskMass a 2621444 (3506902) + weightedMaskMass a 8464 (-47002674))) + (-weightedMaskMass a 5244928 (-47002674) + (weightedMaskMass a 8466 (17134035) + -weightedMaskMass a 8962 (17134035))))) + (((weightedMaskMass a 8466 (-2598175) + (-weightedMaskMass a 264216 (-2598175) + weightedMaskMass a 8466 (-20909598))) + (-weightedMaskMass a 397313 (-20909598) + (weightedMaskMass a 8466 (-49091170) + -weightedMaskMass a 2623492 (-49091170)))) + ((weightedMaskMass a 8468 (-42969778) + (-weightedMaskMass a 264232 (-42969778) + weightedMaskMass a 8468 (-21240608))) + ((-weightedMaskMass a 5277696 (-21240608) + weightedMaskMass a 8472 (-55288889)) + (-weightedMaskMass a 118784 (-55288889) + weightedMaskMass a 8472 (-19567772)))))) + ((((-weightedMaskMass a 264201 (-19567772) + (weightedMaskMass a 8480 (7947658) + -weightedMaskMass a 16672 (7947658))) + (weightedMaskMass a 8480 (35380610) + (-weightedMaskMass a 24608 (35380610) + weightedMaskMass a 8480 (-6011076)))) + ((-weightedMaskMass a 24832 (-6011076) + (weightedMaskMass a 8480 (-25115112) + -weightedMaskMass a 32900 (-25115112))) + (weightedMaskMass a 8480 (-58054687) + (-weightedMaskMass a 98368 (-58054687) + weightedMaskMass a 8480 (-8427241))))) + (((-weightedMaskMass a 1572872 (-8427241) + (weightedMaskMass a 8480 (51517551) + -weightedMaskMass a 2621448 (51517551))) + (weightedMaskMass a 8480 (-50287357) + (-weightedMaskMass a 3145736 (-50287357) + weightedMaskMass a 8480 (-42083519)))) + ((-weightedMaskMass a 3670016 (-42083519) + (weightedMaskMass a 8482 (54385914) + -weightedMaskMass a 24834 (54385914))) + ((weightedMaskMass a 8482 (23643950) + -weightedMaskMass a 98436 (23643950)) + (weightedMaskMass a 8482 (-64548574) + -weightedMaskMass a 2623496 (-64548574))))))))) := by
      simp only [atomCongruenceContributionInt05, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
