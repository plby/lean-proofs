/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock10_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights10, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt10 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 65537 (-64095762) =
      weightedMaskMass a 65792 (-64095762) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65537, 65792, -64095762) (by decide)]
  have h001 : weightedMaskMass a 65537 (91127267) =
      weightedMaskMass a 2097153 (91127267) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65537, 2097153, 91127267) (by decide)]
  have h002 : weightedMaskMass a 65545 (43177351) =
      weightedMaskMass a 65800 (43177351) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65545, 65800, 43177351) (by decide)]
  have h003 : weightedMaskMass a 65545 (-16452192) =
      weightedMaskMass a 81921 (-16452192) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65545, 81921, -16452192) (by decide)]
  have h004 : weightedMaskMass a 65545 (42006827) =
      weightedMaskMass a 2097217 (42006827) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65545, 2097217, 42006827) (by decide)]
  have h005 : weightedMaskMass a 65545 (-12779237) =
      weightedMaskMass a 2113537 (-12779237) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65545, 2113537, -12779237) (by decide)]
  have h006 : weightedMaskMass a 65601 (-105128242) =
      weightedMaskMass a 82176 (-105128242) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65601, 82176, -105128242) (by decide)]
  have h007 : weightedMaskMass a 65601 (84381228) =
      weightedMaskMass a 2097161 (84381228) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65601, 2097161, 84381228) (by decide)]
  have h008 : weightedMaskMass a 65604 (-13200092) =
      weightedMaskMass a 262657 (-13200092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65604, 262657, -13200092) (by decide)]
  have h009 : weightedMaskMass a 65604 (-29448860) =
      weightedMaskMass a 526352 (-29448860) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65604, 526352, -29448860) (by decide)]
  have h010 : weightedMaskMass a 65604 (-10295827) =
      weightedMaskMass a 2097176 (-10295827) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65604, 2097176, -10295827) (by decide)]
  have h011 : weightedMaskMass a 65665 (92362374) =
      weightedMaskMass a 65796 (92362374) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65665, 65796, 92362374) (by decide)]
  have h012 : weightedMaskMass a 65665 (-73117672) =
      weightedMaskMass a 2097665 (-73117672) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65665, 2097665, -73117672) (by decide)]
  have h013 : weightedMaskMass a 65698 (17761534) =
      weightedMaskMass a 409632 (17761534) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65698, 409632, 17761534) (by decide)]
  have h014 : weightedMaskMass a 65700 (72291025) =
      weightedMaskMass a 409601 (72291025) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65700, 409601, 72291025) (by decide)]
  have h015 : weightedMaskMass a 65700 (-73849302) =
      weightedMaskMass a 2623552 (-73849302) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65700, 2623552, -73849302) (by decide)]
  have h016 : weightedMaskMass a 65730 (-43645370) =
      weightedMaskMass a 132610 (-43645370) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65730, 132610, -43645370) (by decide)]
  have h017 : weightedMaskMass a 65730 (12188952) =
      weightedMaskMass a 393760 (12188952) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65730, 393760, 12188952) (by decide)]
  have h018 : weightedMaskMass a 65732 (37919832) =
      weightedMaskMass a 393729 (37919832) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65732, 393729, 37919832) (by decide)]
  have h019 : weightedMaskMass a 65732 (67317479) =
      weightedMaskMass a 526360 (67317479) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65732, 526360, 67317479) (by decide)]
  have h020 : weightedMaskMass a 132609 (45260163) =
      weightedMaskMass a 3147792 (45260163) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (132609, 3147792, 45260163) (by decide)]
  have h021 : weightedMaskMass a 65794 (38648502) =
      weightedMaskMass a 66561 (38648502) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65794, 66561, 38648502) (by decide)]
  have h022 : weightedMaskMass a 65794 (11345189) =
      weightedMaskMass a 2099201 (11345189) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65794, 2099201, 11345189) (by decide)]
  have h023 : weightedMaskMass a 65794 (-20432964) =
      weightedMaskMass a 2359297 (-20432964) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65794, 2359297, -20432964) (by decide)]
  have h024 : weightedMaskMass a 65808 (-49350144) =
      weightedMaskMass a 69633 (-49350144) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65808, 69633, -49350144) (by decide)]
  have h025 : weightedMaskMass a 65816 (15138097) =
      weightedMaskMass a 86017 (15138097) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65816, 86017, 15138097) (by decide)]
  have h026 : weightedMaskMass a 65824 (-27623185) =
      weightedMaskMass a 3145729 (-27623185) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65824, 3145729, -27623185) (by decide)]
  have h027 : weightedMaskMass a 65826 (-17633620) =
      weightedMaskMass a 3147777 (-17633620) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65826, 3147777, -17633620) (by decide)]
  have h028 : weightedMaskMass a 65828 (27623185) =
      weightedMaskMass a 3146241 (27623185) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65828, 3146241, 27623185) (by decide)]
  have h029 : weightedMaskMass a 65832 (6704773) =
      weightedMaskMass a 3162113 (6704773) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (65832, 3162113, 6704773) (by decide)]
  have h030 : weightedMaskMass a 66562 (14683190) =
      weightedMaskMass a 573440 (14683190) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66562, 573440, 14683190) (by decide)]
  have h031 : weightedMaskMass a 66562 (-50086440) =
      weightedMaskMass a 2359328 (-50086440) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66562, 2359328, -50086440) (by decide)]
  have h032 : weightedMaskMass a 66562 (58376995) =
      weightedMaskMass a 4751360 (58376995) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66562, 4751360, 58376995) (by decide)]
  have h033 : weightedMaskMass a 66578 (-44169977) =
      weightedMaskMass a 573441 (-44169977) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66578, 573441, -44169977) (by decide)]
  have h034 : weightedMaskMass a 66578 (-10229504) =
      weightedMaskMass a 2359332 (-10229504) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66578, 2359332, -10229504) (by decide)]
  have h035 : weightedMaskMass a 66578 (88062747) =
      weightedMaskMass a 4755456 (88062747) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66578, 4755456, 88062747) (by decide)]
  have h036 : weightedMaskMass a 66580 (28391727) =
      weightedMaskMass a 559105 (28391727) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66580, 559105, 28391727) (by decide)]
  have h037 : weightedMaskMass a 66580 (33492532) =
      weightedMaskMass a 2359316 (33492532) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66580, 2359316, 33492532) (by decide)]
  have h038 : weightedMaskMass a 66625 (60074581) =
      weightedMaskMass a 2359305 (60074581) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66625, 2359305, 60074581) (by decide)]
  have h039 : weightedMaskMass a 66626 (74302611) =
      weightedMaskMass a 197634 (74302611) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66626, 197634, 74302611) (by decide)]
  have h040 : weightedMaskMass a 66626 (1278090) =
      weightedMaskMass a 573444 (1278090) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66626, 573444, 1278090) (by decide)]
  have h041 : weightedMaskMass a 66626 (-105886562) =
      weightedMaskMass a 573456 (-105886562) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66626, 573456, -105886562) (by decide)]
  have h042 : weightedMaskMass a 66626 (27924481) =
      weightedMaskMass a 2359336 (27924481) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66626, 2359336, 27924481) (by decide)]
  have h043 : weightedMaskMass a 66626 (-18591357) =
      weightedMaskMass a 5799936 (-18591357) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66626, 5799936, -18591357) (by decide)]
  have h044 : weightedMaskMass a 66628 (2070424) =
      weightedMaskMass a 196676 (2070424) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66628, 196676, 2070424) (by decide)]
  have h045 : weightedMaskMass a 66628 (176842372) =
      weightedMaskMass a 526356 (176842372) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66628, 526356, 176842372) (by decide)]
  have h046 : weightedMaskMass a 66628 (49803060) =
      weightedMaskMass a 559120 (49803060) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66628, 559120, 49803060) (by decide)]
  have h047 : weightedMaskMass a 66628 (-2518000) =
      weightedMaskMass a 2359320 (-2518000) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (66628, 2359320, -2518000) (by decide)]
  have h048 : weightedMaskMass a 69636 (-15874268) =
      weightedMaskMass a 458752 (-15874268) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (69636, 458752, -15874268) (by decide)]
  have h049 : weightedMaskMass a 69640 (-30405516) =
      weightedMaskMass a 266248 (-30405516) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (69640, 266248, -30405516) (by decide)]
  have h050 : weightedMaskMass a 69640 (46293692) =
      weightedMaskMass a 655364 (46293692) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (69640, 655364, 46293692) (by decide)]
  have h051 : weightedMaskMass a 69640 (-1881773) =
      weightedMaskMass a 659456 (-1881773) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (69640, 659456, -1881773) (by decide)]
  have h052 : weightedMaskMass a 69697 (43855006) =
      weightedMaskMass a 82192 (43855006) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (69697, 82192, 43855006) (by decide)]
  have h053 : weightedMaskMass a 70656 (4672952) =
      weightedMaskMass a 270344 (4672952) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70656, 270344, 4672952) (by decide)]
  have h054 : weightedMaskMass a 70656 (-9742325) =
      weightedMaskMass a 557312 (-9742325) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70656, 557312, -9742325) (by decide)]
  have h055 : weightedMaskMass a 70656 (45472644) =
      weightedMaskMass a 4227088 (45472644) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70656, 4227088, 45472644) (by decide)]
  have h056 : weightedMaskMass a 70656 (-90580241) =
      weightedMaskMass a 4718596 (-90580241) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70656, 4718596, -90580241) (by decide)]
  have h057 : weightedMaskMass a 70658 (11897151) =
      weightedMaskMass a 573696 (11897151) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70658, 573696, 11897151) (by decide)]
  have h058 : weightedMaskMass a 70658 (-68351888) =
      weightedMaskMass a 4751364 (-68351888) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70658, 4751364, -68351888) (by decide)]
  have h059 : weightedMaskMass a 70658 (59532314) =
      weightedMaskMass a 4751376 (59532314) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70658, 4751376, 59532314) (by decide)]
  have h060 : weightedMaskMass a 70720 (28586390) =
      weightedMaskMass a 557316 (28586390) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70720, 557316, 28586390) (by decide)]
  have h061 : weightedMaskMass a 70720 (-16046508) =
      weightedMaskMass a 5767172 (-16046508) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70720, 5767172, -16046508) (by decide)]
  have h062 : weightedMaskMass a 136256 (-20966431) =
      weightedMaskMass a 524564 (-20966431) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (136256, 524564, -20966431) (by decide)]
  have h063 : weightedMaskMass a 270856 (10379285) =
      weightedMaskMass a 5275664 (10379285) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (270856, 5275664, 10379285) (by decide)]
  have h064 : weightedMaskMass a 70722 (62967150) =
      weightedMaskMass a 573700 (62967150) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70722, 573700, 62967150) (by decide)]
  have h065 : weightedMaskMass a 70722 (-40162700) =
      weightedMaskMass a 5799940 (-40162700) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (70722, 5799940, -40162700) (by decide)]
  have h066 : weightedMaskMass a 73729 (15706161) =
      weightedMaskMass a 589825 (15706161) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73729, 589825, 15706161) (by decide)]
  have h067 : weightedMaskMass a 73729 (13495857) =
      weightedMaskMass a 2129921 (13495857) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73729, 2129921, 13495857) (by decide)]
  have h068 : weightedMaskMass a 73737 (-163859407) =
      weightedMaskMass a 606209 (-163859407) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73737, 606209, -163859407) (by decide)]
  have h069 : weightedMaskMass a 73737 (-13048478) =
      weightedMaskMass a 2146305 (-13048478) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73737, 2146305, -13048478) (by decide)]
  have h070 : weightedMaskMass a 73764 (-12319997) =
      weightedMaskMass a 1056786 (-12319997) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73764, 1056786, -12319997) (by decide)]
  have h071 : weightedMaskMass a 73764 (69098386) =
      weightedMaskMass a 1573377 (69098386) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73764, 1573377, 69098386) (by decide)]
  have h072 : weightedMaskMass a 73764 (4716623) =
      weightedMaskMass a 2131972 (4716623) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73764, 2131972, 4716623) (by decide)]
  have h073 : weightedMaskMass a 73768 (35516528) =
      weightedMaskMass a 262692 (35516528) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73768, 262692, 35516528) (by decide)]
  have h074 : weightedMaskMass a 73768 (-16851303) =
      weightedMaskMass a 1056788 (-16851303) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73768, 1056788, -16851303) (by decide)]
  have h075 : weightedMaskMass a 73768 (-84366219) =
      weightedMaskMass a 1589249 (-84366219) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73768, 1589249, -84366219) (by decide)]
  have h076 : weightedMaskMass a 73768 (67276909) =
      weightedMaskMass a 2228264 (67276909) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73768, 2228264, 67276909) (by decide)]
  have h077 : weightedMaskMass a 73796 (-29699641) =
      weightedMaskMass a 527376 (-29699641) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73796, 527376, -29699641) (by decide)]
  have h078 : weightedMaskMass a 73984 (17796818) =
      weightedMaskMass a 98305 (17796818) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73984, 98305, 17796818) (by decide)]
  have h079 : weightedMaskMass a 73984 (-58691155) =
      weightedMaskMass a 2228225 (-58691155) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73984, 2228225, -58691155) (by decide)]
  have h080 : weightedMaskMass a 73984 (-76223411) =
      weightedMaskMass a 2621441 (-76223411) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73984, 2621441, -76223411) (by decide)]
  have h081 : weightedMaskMass a 73986 (-1907711) =
      weightedMaskMass a 2490369 (-1907711) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73986, 2490369, -1907711) (by decide)]
  have h082 : weightedMaskMass a 73986 (-8413195) =
      weightedMaskMass a 2623489 (-8413195) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73986, 2623489, -8413195) (by decide)]
  have h083 : weightedMaskMass a 73988 (81976879) =
      weightedMaskMass a 2621953 (81976879) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73988, 2621953, 81976879) (by decide)]
  have h084 : weightedMaskMass a 73992 (-42877202) =
      weightedMaskMass a 114689 (-42877202) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73992, 114689, -42877202) (by decide)]
  have h085 : weightedMaskMass a 73992 (88803558) =
      weightedMaskMass a 2228289 (88803558) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73992, 2228289, 88803558) (by decide)]
  have h086 : weightedMaskMass a 73992 (-58446101) =
      weightedMaskMass a 2637825 (-58446101) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (73992, 2637825, -58446101) (by decide)]
  have h087 : weightedMaskMass a 74000 (61549726) =
      weightedMaskMass a 102401 (61549726) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74000, 102401, 61549726) (by decide)]
  have h088 : weightedMaskMass a 74008 (39910038) =
      weightedMaskMass a 118785 (39910038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74008, 118785, 39910038) (by decide)]
  have h089 : weightedMaskMass a 74016 (145171998) =
      weightedMaskMass a 3670017 (145171998) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74016, 3670017, 145171998) (by decide)]
  have h090 : weightedMaskMass a 74018 (-141754328) =
      weightedMaskMass a 3672065 (-141754328) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74018, 3672065, -141754328) (by decide)]
  have h091 : weightedMaskMass a 74020 (-116957637) =
      weightedMaskMass a 3670529 (-116957637) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74020, 3670529, -116957637) (by decide)]
  have h092 : weightedMaskMass a 74024 (-15534505) =
      weightedMaskMass a 3686401 (-15534505) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74024, 3686401, -15534505) (by decide)]
  have h093 : weightedMaskMass a 74753 (22878165) =
      weightedMaskMass a 2131969 (22878165) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74753, 2131969, 22878165) (by decide)]
  have h094 : weightedMaskMass a 74754 (30470219) =
      weightedMaskMass a 577536 (30470219) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74754, 577536, 30470219) (by decide)]
  have h095 : weightedMaskMass a 74754 (32599055) =
      weightedMaskMass a 2361376 (32599055) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74754, 2361376, 32599055) (by decide)]
  have h096 : weightedMaskMass a 74754 (21000964) =
      weightedMaskMass a 2490400 (21000964) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74754, 2490400, 21000964) (by decide)]
  have h097 : weightedMaskMass a 74754 (-116532578) =
      weightedMaskMass a 4753408 (-116532578) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74754, 4753408, -116532578) (by decide)]
  have h098 : weightedMaskMass a 74770 (29239093) =
      weightedMaskMass a 577537 (29239093) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74770, 577537, 29239093) (by decide)]
  have h099 : weightedMaskMass a 74770 (1644082) =
      weightedMaskMass a 4757504 (1644082) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74770, 4757504, 1644082) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt10 s.val : ℝ)) = (((((((weightedMaskMass a 65537 (-64095762) + (-weightedMaskMass a 65792 (-64095762) + weightedMaskMass a 65537 (91127267))) + (-weightedMaskMass a 2097153 (91127267) + (weightedMaskMass a 65545 (43177351) + -weightedMaskMass a 65800 (43177351)))) + ((weightedMaskMass a 65545 (-16452192) + (-weightedMaskMass a 81921 (-16452192) + weightedMaskMass a 65545 (42006827))) + (-weightedMaskMass a 2097217 (42006827) + (weightedMaskMass a 65545 (-12779237) + -weightedMaskMass a 2113537 (-12779237))))) + (((weightedMaskMass a 65601 (-105128242) + (-weightedMaskMass a 82176 (-105128242) + weightedMaskMass a 65601 (84381228))) + (-weightedMaskMass a 2097161 (84381228) + (weightedMaskMass a 65604 (-13200092) + -weightedMaskMass a 262657 (-13200092)))) + ((weightedMaskMass a 65604 (-29448860) + (-weightedMaskMass a 526352 (-29448860) + weightedMaskMass a 65604 (-10295827))) + ((-weightedMaskMass a 2097176 (-10295827) + weightedMaskMass a 65665 (92362374)) + (-weightedMaskMass a 65796 (92362374) + weightedMaskMass a 65665 (-73117672)))))) + ((((-weightedMaskMass a 2097665 (-73117672) + (weightedMaskMass a 65698 (17761534) + -weightedMaskMass a 409632 (17761534))) + (weightedMaskMass a 65700 (72291025) + (-weightedMaskMass a 409601 (72291025) + weightedMaskMass a 65700 (-73849302)))) + ((-weightedMaskMass a 2623552 (-73849302) + (weightedMaskMass a 65730 (-43645370) + -weightedMaskMass a 132610 (-43645370))) + (weightedMaskMass a 65730 (12188952) + (-weightedMaskMass a 393760 (12188952) + weightedMaskMass a 65732 (37919832))))) + (((-weightedMaskMass a 393729 (37919832) + (weightedMaskMass a 65732 (67317479) + -weightedMaskMass a 526360 (67317479))) + (weightedMaskMass a 132609 (45260163) + (-weightedMaskMass a 3147792 (45260163) + weightedMaskMass a 65794 (38648502)))) + ((-weightedMaskMass a 66561 (38648502) + (weightedMaskMass a 65794 (11345189) + -weightedMaskMass a 2099201 (11345189))) + ((weightedMaskMass a 65794 (-20432964) + -weightedMaskMass a 2359297 (-20432964)) + (weightedMaskMass a 65808 (-49350144) + -weightedMaskMass a 69633 (-49350144))))))) + (((((weightedMaskMass a 65816 (15138097) + (-weightedMaskMass a 86017 (15138097) + weightedMaskMass a 65824 (-27623185))) + (-weightedMaskMass a 3145729 (-27623185) + (weightedMaskMass a 65826 (-17633620) + -weightedMaskMass a 3147777 (-17633620)))) + ((weightedMaskMass a 65828 (27623185) + (-weightedMaskMass a 3146241 (27623185) + weightedMaskMass a 65832 (6704773))) + (-weightedMaskMass a 3162113 (6704773) + (weightedMaskMass a 66562 (14683190) + -weightedMaskMass a 573440 (14683190))))) + (((weightedMaskMass a 66562 (-50086440) + (-weightedMaskMass a 2359328 (-50086440) + weightedMaskMass a 66562 (58376995))) + (-weightedMaskMass a 4751360 (58376995) + (weightedMaskMass a 66578 (-44169977) + -weightedMaskMass a 573441 (-44169977)))) + ((weightedMaskMass a 66578 (-10229504) + (-weightedMaskMass a 2359332 (-10229504) + weightedMaskMass a 66578 (88062747))) + ((-weightedMaskMass a 4755456 (88062747) + weightedMaskMass a 66580 (28391727)) + (-weightedMaskMass a 559105 (28391727) + weightedMaskMass a 66580 (33492532)))))) + ((((-weightedMaskMass a 2359316 (33492532) + (weightedMaskMass a 66625 (60074581) + -weightedMaskMass a 2359305 (60074581))) + (weightedMaskMass a 66626 (74302611) + (-weightedMaskMass a 197634 (74302611) + weightedMaskMass a 66626 (1278090)))) + ((-weightedMaskMass a 573444 (1278090) + (weightedMaskMass a 66626 (-105886562) + -weightedMaskMass a 573456 (-105886562))) + (weightedMaskMass a 66626 (27924481) + (-weightedMaskMass a 2359336 (27924481) + weightedMaskMass a 66626 (-18591357))))) + (((-weightedMaskMass a 5799936 (-18591357) + (weightedMaskMass a 66628 (2070424) + -weightedMaskMass a 196676 (2070424))) + (weightedMaskMass a 66628 (176842372) + (-weightedMaskMass a 526356 (176842372) + weightedMaskMass a 66628 (49803060)))) + ((-weightedMaskMass a 559120 (49803060) + (weightedMaskMass a 66628 (-2518000) + -weightedMaskMass a 2359320 (-2518000))) + ((weightedMaskMass a 69636 (-15874268) + -weightedMaskMass a 458752 (-15874268)) + (weightedMaskMass a 69640 (-30405516) + -weightedMaskMass a 266248 (-30405516)))))))) + ((((((weightedMaskMass a 69640 (46293692) + (-weightedMaskMass a 655364 (46293692) + weightedMaskMass a 69640 (-1881773))) + (-weightedMaskMass a 659456 (-1881773) + (weightedMaskMass a 69697 (43855006) + -weightedMaskMass a 82192 (43855006)))) + ((weightedMaskMass a 70656 (4672952) + (-weightedMaskMass a 270344 (4672952) + weightedMaskMass a 70656 (-9742325))) + (-weightedMaskMass a 557312 (-9742325) + (weightedMaskMass a 70656 (45472644) + -weightedMaskMass a 4227088 (45472644))))) + (((weightedMaskMass a 70656 (-90580241) + (-weightedMaskMass a 4718596 (-90580241) + weightedMaskMass a 70658 (11897151))) + (-weightedMaskMass a 573696 (11897151) + (weightedMaskMass a 70658 (-68351888) + -weightedMaskMass a 4751364 (-68351888)))) + ((weightedMaskMass a 70658 (59532314) + (-weightedMaskMass a 4751376 (59532314) + weightedMaskMass a 70720 (28586390))) + ((-weightedMaskMass a 557316 (28586390) + weightedMaskMass a 70720 (-16046508)) + (-weightedMaskMass a 5767172 (-16046508) + weightedMaskMass a 136256 (-20966431)))))) + ((((-weightedMaskMass a 524564 (-20966431) + (weightedMaskMass a 270856 (10379285) + -weightedMaskMass a 5275664 (10379285))) + (weightedMaskMass a 70722 (62967150) + (-weightedMaskMass a 573700 (62967150) + weightedMaskMass a 70722 (-40162700)))) + ((-weightedMaskMass a 5799940 (-40162700) + (weightedMaskMass a 73729 (15706161) + -weightedMaskMass a 589825 (15706161))) + (weightedMaskMass a 73729 (13495857) + (-weightedMaskMass a 2129921 (13495857) + weightedMaskMass a 73737 (-163859407))))) + (((-weightedMaskMass a 606209 (-163859407) + (weightedMaskMass a 73737 (-13048478) + -weightedMaskMass a 2146305 (-13048478))) + (weightedMaskMass a 73764 (-12319997) + (-weightedMaskMass a 1056786 (-12319997) + weightedMaskMass a 73764 (69098386)))) + ((-weightedMaskMass a 1573377 (69098386) + (weightedMaskMass a 73764 (4716623) + -weightedMaskMass a 2131972 (4716623))) + ((weightedMaskMass a 73768 (35516528) + -weightedMaskMass a 262692 (35516528)) + (weightedMaskMass a 73768 (-16851303) + -weightedMaskMass a 1056788 (-16851303))))))) + (((((weightedMaskMass a 73768 (-84366219) + (-weightedMaskMass a 1589249 (-84366219) + weightedMaskMass a 73768 (67276909))) + (-weightedMaskMass a 2228264 (67276909) + (weightedMaskMass a 73796 (-29699641) + -weightedMaskMass a 527376 (-29699641)))) + ((weightedMaskMass a 73984 (17796818) + (-weightedMaskMass a 98305 (17796818) + weightedMaskMass a 73984 (-58691155))) + (-weightedMaskMass a 2228225 (-58691155) + (weightedMaskMass a 73984 (-76223411) + -weightedMaskMass a 2621441 (-76223411))))) + (((weightedMaskMass a 73986 (-1907711) + (-weightedMaskMass a 2490369 (-1907711) + weightedMaskMass a 73986 (-8413195))) + (-weightedMaskMass a 2623489 (-8413195) + (weightedMaskMass a 73988 (81976879) + -weightedMaskMass a 2621953 (81976879)))) + ((weightedMaskMass a 73992 (-42877202) + (-weightedMaskMass a 114689 (-42877202) + weightedMaskMass a 73992 (88803558))) + ((-weightedMaskMass a 2228289 (88803558) + weightedMaskMass a 73992 (-58446101)) + (-weightedMaskMass a 2637825 (-58446101) + weightedMaskMass a 74000 (61549726)))))) + ((((-weightedMaskMass a 102401 (61549726) + (weightedMaskMass a 74008 (39910038) + -weightedMaskMass a 118785 (39910038))) + (weightedMaskMass a 74016 (145171998) + (-weightedMaskMass a 3670017 (145171998) + weightedMaskMass a 74018 (-141754328)))) + ((-weightedMaskMass a 3672065 (-141754328) + (weightedMaskMass a 74020 (-116957637) + -weightedMaskMass a 3670529 (-116957637))) + (weightedMaskMass a 74024 (-15534505) + (-weightedMaskMass a 3686401 (-15534505) + weightedMaskMass a 74753 (22878165))))) + (((-weightedMaskMass a 2131969 (22878165) + (weightedMaskMass a 74754 (30470219) + -weightedMaskMass a 577536 (30470219))) + (weightedMaskMass a 74754 (32599055) + (-weightedMaskMass a 2361376 (32599055) + weightedMaskMass a 74754 (21000964)))) + ((-weightedMaskMass a 2490400 (21000964) + (weightedMaskMass a 74754 (-116532578) + -weightedMaskMass a 4753408 (-116532578))) + ((weightedMaskMass a 74770 (29239093) + -weightedMaskMass a 577537 (29239093)) + (weightedMaskMass a 74770 (1644082) + -weightedMaskMass a 4757504 (1644082))))))))) := by
      simp only [atomCongruenceContributionInt10, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
