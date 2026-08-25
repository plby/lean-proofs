/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock11_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights11, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt11 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 74816 (20670514) =
      weightedMaskMass a 294932 (20670514) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74816, 294932, 20670514) (by decide)]
  have h001 : weightedMaskMass a 74816 (142490568) =
      weightedMaskMass a 525332 (142490568) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74816, 525332, 142490568) (by decide)]
  have h002 : weightedMaskMass a 74816 (-120897020) =
      weightedMaskMass a 561156 (-120897020) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74816, 561156, -120897020) (by decide)]
  have h003 : weightedMaskMass a 74816 (50740562) =
      weightedMaskMass a 2229312 (50740562) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74816, 2229312, 50740562) (by decide)]
  have h004 : weightedMaskMass a 74818 (-30037051) =
      weightedMaskMass a 577540 (-30037051) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74818, 577540, -30037051) (by decide)]
  have h005 : weightedMaskMass a 74820 (-93011788) =
      weightedMaskMass a 527380 (-93011788) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (74820, 527380, -93011788) (by decide)]
  have h006 : weightedMaskMass a 77832 (-39205362) =
      weightedMaskMass a 4853760 (-39205362) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (77832, 4853760, -39205362) (by decide)]
  have h007 : weightedMaskMass a 78848 (-39265927) =
      weightedMaskMass a 561408 (-39265927) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (78848, 561408, -39265927) (by decide)]
  have h008 : weightedMaskMass a 78850 (53018166) =
      weightedMaskMass a 577792 (53018166) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (78850, 577792, 53018166) (by decide)]
  have h009 : weightedMaskMass a 78912 (86226409) =
      weightedMaskMass a 561412 (86226409) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (78912, 561412, 86226409) (by decide)]
  have h010 : weightedMaskMass a 78914 (-32090602) =
      weightedMaskMass a 577796 (-32090602) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (78914, 577796, -32090602) (by decide)]
  have h011 : weightedMaskMass a 81929 (-29806013) =
      weightedMaskMass a 2113601 (-29806013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81929, 2113601, -29806013) (by decide)]
  have h012 : weightedMaskMass a 81938 (47759538) =
      weightedMaskMass a 1049352 (47759538) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81938, 1049352, 47759538) (by decide)]
  have h013 : weightedMaskMass a 81938 (62578461) =
      weightedMaskMass a 2113572 (62578461) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81938, 2113572, 62578461) (by decide)]
  have h014 : weightedMaskMass a 81940 (111540339) =
      weightedMaskMass a 2113556 (111540339) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81940, 2113556, 111540339) (by decide)]
  have h015 : weightedMaskMass a 81954 (46583232) =
      weightedMaskMass a 1050633 (46583232) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81954, 1050633, 46583232) (by decide)]
  have h016 : weightedMaskMass a 81954 (19249356) =
      weightedMaskMass a 1050888 (19249356) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81954, 1050888, 19249356) (by decide)]
  have h017 : weightedMaskMass a 81954 (9500466) =
      weightedMaskMass a 2113570 (9500466) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81954, 2113570, 9500466) (by decide)]
  have h018 : weightedMaskMass a 81956 (7862533) =
      weightedMaskMass a 1049097 (7862533) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81956, 1049097, 7862533) (by decide)]
  have h019 : weightedMaskMass a 81956 (82699415) =
      weightedMaskMass a 2113554 (82699415) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81956, 2113554, 82699415) (by decide)]
  have h020 : weightedMaskMass a 81960 (10639400) =
      weightedMaskMass a 1064969 (10639400) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81960, 1064969, 10639400) (by decide)]
  have h021 : weightedMaskMass a 81960 (-173101102) =
      weightedMaskMass a 2113602 (-173101102) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81960, 2113602, -173101102) (by decide)]
  have h022 : weightedMaskMass a 81985 (41627687) =
      weightedMaskMass a 82184 (41627687) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81985, 82184, 41627687) (by decide)]
  have h023 : weightedMaskMass a 81985 (-53547933) =
      weightedMaskMass a 2113545 (-53547933) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81985, 2113545, -53547933) (by decide)]
  have h024 : weightedMaskMass a 81986 (14290941) =
      weightedMaskMass a 1065224 (14290941) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81986, 1065224, 14290941) (by decide)]
  have h025 : weightedMaskMass a 81986 (-16904430) =
      weightedMaskMass a 2113576 (-16904430) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81986, 2113576, -16904430) (by decide)]
  have h026 : weightedMaskMass a 81988 (58726874) =
      weightedMaskMass a 2113560 (58726874) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (81988, 2113560, 58726874) (by decide)]
  have h027 : weightedMaskMass a 82049 (-10685726) =
      weightedMaskMass a 2097729 (-10685726) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82049, 2097729, -10685726) (by decide)]
  have h028 : weightedMaskMass a 82178 (-79322569) =
      weightedMaskMass a 2099209 (-79322569) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82178, 2099209, -79322569) (by decide)]
  have h029 : weightedMaskMass a 82180 (-127386742) =
      weightedMaskMass a 2097673 (-127386742) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82180, 2097673, -127386742) (by decide)]
  have h030 : weightedMaskMass a 82200 (13081051) =
      weightedMaskMass a 86081 (13081051) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82200, 86081, 13081051) (by decide)]
  have h031 : weightedMaskMass a 82208 (5406728) =
      weightedMaskMass a 3145737 (5406728) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82208, 3145737, 5406728) (by decide)]
  have h032 : weightedMaskMass a 82210 (-5743877) =
      weightedMaskMass a 3147785 (-5743877) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82210, 3147785, -5743877) (by decide)]
  have h033 : weightedMaskMass a 82212 (26012385) =
      weightedMaskMass a 3146249 (26012385) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82212, 3146249, 26012385) (by decide)]
  have h034 : weightedMaskMass a 82216 (-26903075) =
      weightedMaskMass a 3162121 (-26903075) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82216, 3162121, -26903075) (by decide)]
  have h035 : weightedMaskMass a 82945 (-30432551) =
      weightedMaskMass a 2099265 (-30432551) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82945, 2099265, -30432551) (by decide)]
  have h036 : weightedMaskMass a 82945 (141916425) =
      weightedMaskMass a 2375681 (141916425) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82945, 2375681, 141916425) (by decide)]
  have h037 : weightedMaskMass a 82946 (16853616) =
      weightedMaskMass a 638976 (16853616) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82946, 638976, 16853616) (by decide)]
  have h038 : weightedMaskMass a 82946 (42382495) =
      weightedMaskMass a 2375712 (42382495) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82946, 2375712, 42382495) (by decide)]
  have h039 : weightedMaskMass a 82946 (86621908) =
      weightedMaskMass a 2670592 (86621908) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82946, 2670592, 86621908) (by decide)]
  have h040 : weightedMaskMass a 82948 (-23929480) =
      weightedMaskMass a 2375696 (-23929480) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82948, 2375696, -23929480) (by decide)]
  have h041 : weightedMaskMass a 82962 (-187233140) =
      weightedMaskMass a 2375716 (-187233140) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82962, 2375716, -187233140) (by decide)]
  have h042 : weightedMaskMass a 82964 (39545341) =
      weightedMaskMass a 2375700 (39545341) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (82964, 2375700, 39545341) (by decide)]
  have h043 : weightedMaskMass a 83008 (134218080) =
      weightedMaskMass a 2375688 (134218080) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (83008, 2375688, 134218080) (by decide)]
  have h044 : weightedMaskMass a 83009 (-194260056) =
      weightedMaskMass a 2375689 (-194260056) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (83009, 2375689, -194260056) (by decide)]
  have h045 : weightedMaskMass a 83010 (-220153785) =
      weightedMaskMass a 2375720 (-220153785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (83010, 2375720, -220153785) (by decide)]
  have h046 : weightedMaskMass a 83012 (-120318462) =
      weightedMaskMass a 2375704 (-120318462) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (83012, 2375704, -120318462) (by decide)]
  have h047 : weightedMaskMass a 86018 (33166180) =
      weightedMaskMass a 132161 (33166180) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (86018, 132161, 33166180) (by decide)]
  have h048 : weightedMaskMass a 86018 (67163530) =
      weightedMaskMass a 1048856 (67163530) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (86018, 1048856, 67163530) (by decide)]
  have h049 : weightedMaskMass a 86050 (-63190556) =
      weightedMaskMass a 1050904 (-63190556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (86050, 1050904, -63190556) (by decide)]
  have h050 : weightedMaskMass a 86082 (-93757850) =
      weightedMaskMass a 1065240 (-93757850) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (86082, 1065240, -93757850) (by decide)]
  have h051 : weightedMaskMass a 87040 (20493836) =
      weightedMaskMass a 270345 (20493836) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (87040, 270345, 20493836) (by decide)]
  have h052 : weightedMaskMass a 90113 (-51738660) =
      weightedMaskMass a 589833 (-51738660) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90113, 589833, -51738660) (by decide)]
  have h053 : weightedMaskMass a 90113 (3833045) =
      weightedMaskMass a 2129985 (3833045) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90113, 2129985, 3833045) (by decide)]
  have h054 : weightedMaskMass a 90114 (-27742629) =
      weightedMaskMass a 526345 (-27742629) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90114, 526345, -27742629) (by decide)]
  have h055 : weightedMaskMass a 90116 (45343700) =
      weightedMaskMass a 524809 (45343700) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90116, 524809, 45343700) (by decide)]
  have h056 : weightedMaskMass a 90121 (65186852) =
      weightedMaskMass a 606217 (65186852) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90121, 606217, 65186852) (by decide)]
  have h057 : weightedMaskMass a 90121 (-20294563) =
      weightedMaskMass a 2146369 (-20294563) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90121, 2146369, -20294563) (by decide)]
  have h058 : weightedMaskMass a 90144 (30465936) =
      weightedMaskMass a 1572873 (30465936) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90144, 1572873, 30465936) (by decide)]
  have h059 : weightedMaskMass a 2130052 (21032811) =
      weightedMaskMass a 2752520 (21032811) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2130052, 2752520, 21032811) (by decide)]
  have h060 : weightedMaskMass a 90146 (-80767359) =
      weightedMaskMass a 1574921 (-80767359) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90146, 1574921, -80767359) (by decide)]
  have h061 : weightedMaskMass a 90148 (-98191688) =
      weightedMaskMass a 1573385 (-98191688) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90148, 1573385, -98191688) (by decide)]
  have h062 : weightedMaskMass a 90152 (47009474) =
      weightedMaskMass a 1589257 (47009474) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90152, 1589257, 47009474) (by decide)]
  have h063 : weightedMaskMass a 90368 (19524667) =
      weightedMaskMass a 98369 (19524667) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90368, 98369, 19524667) (by decide)]
  have h064 : weightedMaskMass a 90368 (-30837427) =
      weightedMaskMass a 2621449 (-30837427) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90368, 2621449, -30837427) (by decide)]
  have h065 : weightedMaskMass a 90370 (40368496) =
      weightedMaskMass a 2623497 (40368496) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90370, 2623497, 40368496) (by decide)]
  have h066 : weightedMaskMass a 90372 (-42273772) =
      weightedMaskMass a 2621961 (-42273772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90372, 2621961, -42273772) (by decide)]
  have h067 : weightedMaskMass a 90376 (-119195659) =
      weightedMaskMass a 114753 (-119195659) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90376, 114753, -119195659) (by decide)]
  have h068 : weightedMaskMass a 90376 (89867871) =
      weightedMaskMass a 2637833 (89867871) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90376, 2637833, 89867871) (by decide)]
  have h069 : weightedMaskMass a 90384 (-9138072) =
      weightedMaskMass a 102465 (-9138072) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90384, 102465, -9138072) (by decide)]
  have h070 : weightedMaskMass a 90392 (-11603435) =
      weightedMaskMass a 118849 (-11603435) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90392, 118849, -11603435) (by decide)]
  have h071 : weightedMaskMass a 90400 (8249228) =
      weightedMaskMass a 3670025 (8249228) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90400, 3670025, 8249228) (by decide)]
  have h072 : weightedMaskMass a 90402 (49746393) =
      weightedMaskMass a 3672073 (49746393) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90402, 3672073, 49746393) (by decide)]
  have h073 : weightedMaskMass a 90404 (45150374) =
      weightedMaskMass a 3670537 (45150374) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90404, 3670537, 45150374) (by decide)]
  have h074 : weightedMaskMass a 90408 (8287552) =
      weightedMaskMass a 3686409 (8287552) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (90408, 3686409, 8287552) (by decide)]
  have h075 : weightedMaskMass a 91137 (-96656858) =
      weightedMaskMass a 2132033 (-96656858) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (91137, 2132033, -96656858) (by decide)]
  have h076 : weightedMaskMass a 98313 (148567995) =
      weightedMaskMass a 2244609 (148567995) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98313, 2244609, 148567995) (by decide)]
  have h077 : weightedMaskMass a 98313 (-28341570) =
      weightedMaskMass a 2621505 (-28341570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98313, 2621505, -28341570) (by decide)]
  have h078 : weightedMaskMass a 98322 (120891576) =
      weightedMaskMass a 626688 (120891576) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98322, 626688, 120891576) (by decide)]
  have h079 : weightedMaskMass a 98322 (-169208484) =
      weightedMaskMass a 1057536 (-169208484) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98322, 1057536, -169208484) (by decide)]
  have h080 : weightedMaskMass a 98322 (50766853) =
      weightedMaskMass a 2621476 (50766853) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98322, 2621476, 50766853) (by decide)]
  have h081 : weightedMaskMass a 98324 (-53329937) =
      weightedMaskMass a 2361352 (-53329937) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98324, 2361352, -53329937) (by decide)]
  have h082 : weightedMaskMass a 98324 (-5961934) =
      weightedMaskMass a 2621460 (-5961934) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98324, 2621460, -5961934) (by decide)]
  have h083 : weightedMaskMass a 98324 (7989011) =
      weightedMaskMass a 5769216 (7989011) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98324, 5769216, 7989011) (by decide)]
  have h084 : weightedMaskMass a 98328 (76910016) =
      weightedMaskMass a 151553 (76910016) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98328, 151553, 76910016) (by decide)]
  have h085 : weightedMaskMass a 98328 (-93160948) =
      weightedMaskMass a 2621508 (-93160948) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98328, 2621508, -93160948) (by decide)]
  have h086 : weightedMaskMass a 98370 (-84050088) =
      weightedMaskMass a 1073408 (-84050088) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98370, 1073408, -84050088) (by decide)]
  have h087 : weightedMaskMass a 98370 (-52049619) =
      weightedMaskMass a 2621480 (-52049619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98370, 2621480, -52049619) (by decide)]
  have h088 : weightedMaskMass a 98370 (-6243750) =
      weightedMaskMass a 3702784 (-6243750) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98370, 3702784, -6243750) (by decide)]
  have h089 : weightedMaskMass a 98372 (22426224) =
      weightedMaskMass a 2621464 (22426224) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98372, 2621464, 22426224) (by decide)]
  have h090 : weightedMaskMass a 98372 (-73247734) =
      weightedMaskMass a 3145752 (-73247734) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98372, 3145752, -73247734) (by decide)]
  have h091 : weightedMaskMass a 98433 (74846141) =
      weightedMaskMass a 2228737 (74846141) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98433, 2228737, 74846141) (by decide)]
  have h092 : weightedMaskMass a 98560 (-61648320) =
      weightedMaskMass a 196609 (-61648320) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98560, 196609, -61648320) (by decide)]
  have h093 : weightedMaskMass a 98568 (125572547) =
      weightedMaskMass a 212993 (125572547) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98568, 212993, 125572547) (by decide)]
  have h094 : weightedMaskMass a 98576 (59747011) =
      weightedMaskMass a 200705 (59747011) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98576, 200705, 59747011) (by decide)]
  have h095 : weightedMaskMass a 98584 (-67338251) =
      weightedMaskMass a 217089 (-67338251) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (98584, 217089, -67338251) (by decide)]
  have h096 : weightedMaskMass a 102402 (128447847) =
      weightedMaskMass a 622608 (128447847) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (102402, 622608, 128447847) (by decide)]
  have h097 : weightedMaskMass a 102402 (-94622199) =
      weightedMaskMass a 1057040 (-94622199) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (102402, 1057040, -94622199) (by decide)]
  have h098 : weightedMaskMass a 102402 (-62475752) =
      weightedMaskMass a 2654212 (-62475752) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (102402, 2654212, -62475752) (by decide)]
  have h099 : weightedMaskMass a 102466 (103727629) =
      weightedMaskMass a 1073424 (103727629) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (102466, 1073424, 103727629) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt11 s.val : ℝ)) = (((((((weightedMaskMass a 74816 (20670514) + (-weightedMaskMass a 294932 (20670514) + weightedMaskMass a 74816 (142490568))) + (-weightedMaskMass a 525332 (142490568) + (weightedMaskMass a 74816 (-120897020) + -weightedMaskMass a 561156 (-120897020)))) + ((weightedMaskMass a 74816 (50740562) + (-weightedMaskMass a 2229312 (50740562) + weightedMaskMass a 74818 (-30037051))) + (-weightedMaskMass a 577540 (-30037051) + (weightedMaskMass a 74820 (-93011788) + -weightedMaskMass a 527380 (-93011788))))) + (((weightedMaskMass a 77832 (-39205362) + (-weightedMaskMass a 4853760 (-39205362) + weightedMaskMass a 78848 (-39265927))) + (-weightedMaskMass a 561408 (-39265927) + (weightedMaskMass a 78850 (53018166) + -weightedMaskMass a 577792 (53018166)))) + ((weightedMaskMass a 78912 (86226409) + (-weightedMaskMass a 561412 (86226409) + weightedMaskMass a 78914 (-32090602))) + ((-weightedMaskMass a 577796 (-32090602) + weightedMaskMass a 81929 (-29806013)) + (-weightedMaskMass a 2113601 (-29806013) + weightedMaskMass a 81938 (47759538)))))) + ((((-weightedMaskMass a 1049352 (47759538) + (weightedMaskMass a 81938 (62578461) + -weightedMaskMass a 2113572 (62578461))) + (weightedMaskMass a 81940 (111540339) + (-weightedMaskMass a 2113556 (111540339) + weightedMaskMass a 81954 (46583232)))) + ((-weightedMaskMass a 1050633 (46583232) + (weightedMaskMass a 81954 (19249356) + -weightedMaskMass a 1050888 (19249356))) + (weightedMaskMass a 81954 (9500466) + (-weightedMaskMass a 2113570 (9500466) + weightedMaskMass a 81956 (7862533))))) + (((-weightedMaskMass a 1049097 (7862533) + (weightedMaskMass a 81956 (82699415) + -weightedMaskMass a 2113554 (82699415))) + (weightedMaskMass a 81960 (10639400) + (-weightedMaskMass a 1064969 (10639400) + weightedMaskMass a 81960 (-173101102)))) + ((-weightedMaskMass a 2113602 (-173101102) + (weightedMaskMass a 81985 (41627687) + -weightedMaskMass a 82184 (41627687))) + ((weightedMaskMass a 81985 (-53547933) + -weightedMaskMass a 2113545 (-53547933)) + (weightedMaskMass a 81986 (14290941) + -weightedMaskMass a 1065224 (14290941))))))) + (((((weightedMaskMass a 81986 (-16904430) + (-weightedMaskMass a 2113576 (-16904430) + weightedMaskMass a 81988 (58726874))) + (-weightedMaskMass a 2113560 (58726874) + (weightedMaskMass a 82049 (-10685726) + -weightedMaskMass a 2097729 (-10685726)))) + ((weightedMaskMass a 82178 (-79322569) + (-weightedMaskMass a 2099209 (-79322569) + weightedMaskMass a 82180 (-127386742))) + (-weightedMaskMass a 2097673 (-127386742) + (weightedMaskMass a 82200 (13081051) + -weightedMaskMass a 86081 (13081051))))) + (((weightedMaskMass a 82208 (5406728) + (-weightedMaskMass a 3145737 (5406728) + weightedMaskMass a 82210 (-5743877))) + (-weightedMaskMass a 3147785 (-5743877) + (weightedMaskMass a 82212 (26012385) + -weightedMaskMass a 3146249 (26012385)))) + ((weightedMaskMass a 82216 (-26903075) + (-weightedMaskMass a 3162121 (-26903075) + weightedMaskMass a 82945 (-30432551))) + ((-weightedMaskMass a 2099265 (-30432551) + weightedMaskMass a 82945 (141916425)) + (-weightedMaskMass a 2375681 (141916425) + weightedMaskMass a 82946 (16853616)))))) + ((((-weightedMaskMass a 638976 (16853616) + (weightedMaskMass a 82946 (42382495) + -weightedMaskMass a 2375712 (42382495))) + (weightedMaskMass a 82946 (86621908) + (-weightedMaskMass a 2670592 (86621908) + weightedMaskMass a 82948 (-23929480)))) + ((-weightedMaskMass a 2375696 (-23929480) + (weightedMaskMass a 82962 (-187233140) + -weightedMaskMass a 2375716 (-187233140))) + (weightedMaskMass a 82964 (39545341) + (-weightedMaskMass a 2375700 (39545341) + weightedMaskMass a 83008 (134218080))))) + (((-weightedMaskMass a 2375688 (134218080) + (weightedMaskMass a 83009 (-194260056) + -weightedMaskMass a 2375689 (-194260056))) + (weightedMaskMass a 83010 (-220153785) + (-weightedMaskMass a 2375720 (-220153785) + weightedMaskMass a 83012 (-120318462)))) + ((-weightedMaskMass a 2375704 (-120318462) + (weightedMaskMass a 86018 (33166180) + -weightedMaskMass a 132161 (33166180))) + ((weightedMaskMass a 86018 (67163530) + -weightedMaskMass a 1048856 (67163530)) + (weightedMaskMass a 86050 (-63190556) + -weightedMaskMass a 1050904 (-63190556)))))))) + ((((((weightedMaskMass a 86082 (-93757850) + (-weightedMaskMass a 1065240 (-93757850) + weightedMaskMass a 87040 (20493836))) + (-weightedMaskMass a 270345 (20493836) + (weightedMaskMass a 90113 (-51738660) + -weightedMaskMass a 589833 (-51738660)))) + ((weightedMaskMass a 90113 (3833045) + (-weightedMaskMass a 2129985 (3833045) + weightedMaskMass a 90114 (-27742629))) + (-weightedMaskMass a 526345 (-27742629) + (weightedMaskMass a 90116 (45343700) + -weightedMaskMass a 524809 (45343700))))) + (((weightedMaskMass a 90121 (65186852) + (-weightedMaskMass a 606217 (65186852) + weightedMaskMass a 90121 (-20294563))) + (-weightedMaskMass a 2146369 (-20294563) + (weightedMaskMass a 90144 (30465936) + -weightedMaskMass a 1572873 (30465936)))) + ((weightedMaskMass a 2130052 (21032811) + (-weightedMaskMass a 2752520 (21032811) + weightedMaskMass a 90146 (-80767359))) + ((-weightedMaskMass a 1574921 (-80767359) + weightedMaskMass a 90148 (-98191688)) + (-weightedMaskMass a 1573385 (-98191688) + weightedMaskMass a 90152 (47009474)))))) + ((((-weightedMaskMass a 1589257 (47009474) + (weightedMaskMass a 90368 (19524667) + -weightedMaskMass a 98369 (19524667))) + (weightedMaskMass a 90368 (-30837427) + (-weightedMaskMass a 2621449 (-30837427) + weightedMaskMass a 90370 (40368496)))) + ((-weightedMaskMass a 2623497 (40368496) + (weightedMaskMass a 90372 (-42273772) + -weightedMaskMass a 2621961 (-42273772))) + (weightedMaskMass a 90376 (-119195659) + (-weightedMaskMass a 114753 (-119195659) + weightedMaskMass a 90376 (89867871))))) + (((-weightedMaskMass a 2637833 (89867871) + (weightedMaskMass a 90384 (-9138072) + -weightedMaskMass a 102465 (-9138072))) + (weightedMaskMass a 90392 (-11603435) + (-weightedMaskMass a 118849 (-11603435) + weightedMaskMass a 90400 (8249228)))) + ((-weightedMaskMass a 3670025 (8249228) + (weightedMaskMass a 90402 (49746393) + -weightedMaskMass a 3672073 (49746393))) + ((weightedMaskMass a 90404 (45150374) + -weightedMaskMass a 3670537 (45150374)) + (weightedMaskMass a 90408 (8287552) + -weightedMaskMass a 3686409 (8287552))))))) + (((((weightedMaskMass a 91137 (-96656858) + (-weightedMaskMass a 2132033 (-96656858) + weightedMaskMass a 98313 (148567995))) + (-weightedMaskMass a 2244609 (148567995) + (weightedMaskMass a 98313 (-28341570) + -weightedMaskMass a 2621505 (-28341570)))) + ((weightedMaskMass a 98322 (120891576) + (-weightedMaskMass a 626688 (120891576) + weightedMaskMass a 98322 (-169208484))) + (-weightedMaskMass a 1057536 (-169208484) + (weightedMaskMass a 98322 (50766853) + -weightedMaskMass a 2621476 (50766853))))) + (((weightedMaskMass a 98324 (-53329937) + (-weightedMaskMass a 2361352 (-53329937) + weightedMaskMass a 98324 (-5961934))) + (-weightedMaskMass a 2621460 (-5961934) + (weightedMaskMass a 98324 (7989011) + -weightedMaskMass a 5769216 (7989011)))) + ((weightedMaskMass a 98328 (76910016) + (-weightedMaskMass a 151553 (76910016) + weightedMaskMass a 98328 (-93160948))) + ((-weightedMaskMass a 2621508 (-93160948) + weightedMaskMass a 98370 (-84050088)) + (-weightedMaskMass a 1073408 (-84050088) + weightedMaskMass a 98370 (-52049619)))))) + ((((-weightedMaskMass a 2621480 (-52049619) + (weightedMaskMass a 98370 (-6243750) + -weightedMaskMass a 3702784 (-6243750))) + (weightedMaskMass a 98372 (22426224) + (-weightedMaskMass a 2621464 (22426224) + weightedMaskMass a 98372 (-73247734)))) + ((-weightedMaskMass a 3145752 (-73247734) + (weightedMaskMass a 98433 (74846141) + -weightedMaskMass a 2228737 (74846141))) + (weightedMaskMass a 98560 (-61648320) + (-weightedMaskMass a 196609 (-61648320) + weightedMaskMass a 98568 (125572547))))) + (((-weightedMaskMass a 212993 (125572547) + (weightedMaskMass a 98576 (59747011) + -weightedMaskMass a 200705 (59747011))) + (weightedMaskMass a 98584 (-67338251) + (-weightedMaskMass a 217089 (-67338251) + weightedMaskMass a 102402 (128447847)))) + ((-weightedMaskMass a 622608 (128447847) + (weightedMaskMass a 102402 (-94622199) + -weightedMaskMass a 1057040 (-94622199))) + ((weightedMaskMass a 102402 (-62475752) + -weightedMaskMass a 2654212 (-62475752)) + (weightedMaskMass a 102466 (103727629) + -weightedMaskMass a 1073424 (103727629))))))))) := by
      simp only [atomCongruenceContributionInt11, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
