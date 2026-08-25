/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock22_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights22, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt22 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 2646308 (-380267850) =
      weightedMaskMass a 3678984 (-380267850) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2646308, 3678984, -380267850) (by decide)]
  have h001 : weightedMaskMass a 2646312 (-295309054) =
      weightedMaskMass a 3694856 (-295309054) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2646312, 3694856, -295309054) (by decide)]
  have h002 : weightedMaskMass a 2752577 (-74552364) =
      weightedMaskMass a 2768897 (-74552364) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2752577, 2768897, -74552364) (by decide)]
  have h003 : weightedMaskMass a 2753024 (-94258938) =
      weightedMaskMass a 3145860 (-94258938) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2753024, 3145860, -94258938) (by decide)]
  have h004 : weightedMaskMass a 2753032 (98809120) =
      weightedMaskMass a 3178628 (98809120) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2753032, 3178628, 98809120) (by decide)]
  have h005 : weightedMaskMass a 2753088 (104233715) =
      weightedMaskMass a 3145892 (104233715) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (2753088, 3145892, 104233715) (by decide)]
  have h006 : weightedMaskMass a 3146018 (49414159) =
      weightedMaskMass a 3148064 (49414159) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3146018, 3148064, 49414159) (by decide)]
  have h007 : weightedMaskMass a 3146020 (73479696) =
      weightedMaskMass a 3146528 (73479696) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3146020, 3146528, 73479696) (by decide)]
  have h008 : weightedMaskMass a 3146024 (127572960) =
      weightedMaskMass a 3162400 (127572960) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3146024, 3162400, 127572960) (by decide)]
  have h009 : weightedMaskMass a 3146530 (-24377932) =
      weightedMaskMass a 3148068 (-24377932) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3146530, 3148068, -24377932) (by decide)]
  have h010 : weightedMaskMass a 3146536 (-11782306) =
      weightedMaskMass a 3162404 (-11782306) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3146536, 3162404, -11782306) (by decide)]
  have h011 : weightedMaskMass a 3148072 (-128709916) =
      weightedMaskMass a 3162402 (-128709916) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3148072, 3162402, -128709916) (by decide)]
  have h012 : weightedMaskMass a 3154208 (-174384866) =
      weightedMaskMass a 3670304 (-174384866) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154208, 3670304, -174384866) (by decide)]
  have h013 : weightedMaskMass a 3154210 (281072492) =
      weightedMaskMass a 3672352 (281072492) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154210, 3672352, 281072492) (by decide)]
  have h014 : weightedMaskMass a 3154212 (64697531) =
      weightedMaskMass a 3670816 (64697531) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154212, 3670816, 64697531) (by decide)]
  have h015 : weightedMaskMass a 3154216 (-217500160) =
      weightedMaskMass a 3686688 (-217500160) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154216, 3686688, -217500160) (by decide)]
  have h016 : weightedMaskMass a 3154720 (157580656) =
      weightedMaskMass a 3670308 (157580656) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154720, 3670308, 157580656) (by decide)]
  have h017 : weightedMaskMass a 3154722 (-135286308) =
      weightedMaskMass a 3672356 (-135286308) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154722, 3672356, -135286308) (by decide)]
  have h018 : weightedMaskMass a 3154724 (0) =
      weightedMaskMass a 3670820 (0) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154724, 3670820, 0) (by decide)]
  have h019 : weightedMaskMass a 3154728 (54634533) =
      weightedMaskMass a 3686692 (54634533) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3154728, 3686692, 54634533) (by decide)]
  have h020 : weightedMaskMass a 3170592 (331216741) =
      weightedMaskMass a 3670312 (331216741) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3170592, 3670312, 331216741) (by decide)]
  have h021 : weightedMaskMass a 3170594 (-566327120) =
      weightedMaskMass a 3672360 (-566327120) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3170594, 3672360, -566327120) (by decide)]
  have h022 : weightedMaskMass a 3170596 (-285933022) =
      weightedMaskMass a 3670824 (-285933022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3170596, 3670824, -285933022) (by decide)]
  have h023 : weightedMaskMass a 3170600 (-57490333) =
      weightedMaskMass a 3686696 (-57490333) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3170600, 3686696, -57490333) (by decide)]
  have h024 : weightedMaskMass a 3409920 (-72673012) =
      weightedMaskMass a 4720648 (-72673012) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3409920, 4720648, -72673012) (by decide)]
  have h025 : weightedMaskMass a 3409928 (45511335) =
      weightedMaskMass a 5769224 (45511335) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3409928, 5769224, 45511335) (by decide)]
  have h026 : weightedMaskMass a 3409952 (39415713) =
      weightedMaskMass a 4753416 (39415713) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3409952, 4753416, 39415713) (by decide)]
  have h027 : weightedMaskMass a 3409960 (45667639) =
      weightedMaskMass a 5801992 (45667639) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3409960, 5801992, 45667639) (by decide)]
  have h028 : weightedMaskMass a 3440640 (-46185856) =
      weightedMaskMass a 4227138 (-46185856) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3440640, 4227138, -46185856) (by decide)]
  have h029 : weightedMaskMass a 3440640 (26359903) =
      weightedMaskMass a 4718632 (26359903) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3440640, 4718632, 26359903) (by decide)]
  have h030 : weightedMaskMass a 3440644 (-21467068) =
      weightedMaskMass a 4231234 (-21467068) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3440644, 4231234, -21467068) (by decide)]
  have h031 : weightedMaskMass a 3440648 (-38862806) =
      weightedMaskMass a 5767208 (-38862806) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3440648, 5767208, -38862806) (by decide)]
  have h032 : weightedMaskMass a 3442688 (82415492) =
      weightedMaskMass a 4720680 (82415492) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3442688, 4720680, 82415492) (by decide)]
  have h033 : weightedMaskMass a 3442696 (-45109675) =
      weightedMaskMass a 5769256 (-45109675) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3442696, 5769256, -45109675) (by decide)]
  have h034 : weightedMaskMass a 3678500 (-298818745) =
      weightedMaskMass a 3679008 (-298818745) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3678500, 3679008, -298818745) (by decide)]
  have h035 : weightedMaskMass a 3678504 (536713459) =
      weightedMaskMass a 3694880 (536713459) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3678504, 3694880, 536713459) (by decide)]
  have h036 : weightedMaskMass a 3679016 (-886178907) =
      weightedMaskMass a 3694884 (-886178907) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (3679016, 3694884, -886178907) (by decide)]
  have h037 : weightedMaskMass a 4194313 (35931123) =
      weightedMaskMass a 4194369 (35931123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4194313, 4194369, 35931123) (by decide)]
  have h038 : weightedMaskMass a 4194328 (983208) =
      weightedMaskMass a 4194372 (983208) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4194328, 4194372, 983208) (by decide)]
  have h039 : weightedMaskMass a 4195329 (1874486) =
      weightedMaskMass a 4456449 (1874486) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195329, 4456449, 1874486) (by decide)]
  have h040 : weightedMaskMass a 4195344 (-40348743) =
      weightedMaskMass a 4199424 (-40348743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195344, 4199424, -40348743) (by decide)]
  have h041 : weightedMaskMass a 4195344 (50014672) =
      weightedMaskMass a 4456452 (50014672) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195344, 4456452, 50014672) (by decide)]
  have h042 : weightedMaskMass a 4195348 (-2268105) =
      weightedMaskMass a 4456468 (-2268105) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195348, 4456468, -2268105) (by decide)]
  have h043 : weightedMaskMass a 4195392 (10965406) =
      weightedMaskMass a 4456456 (10965406) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195392, 4456456, 10965406) (by decide)]
  have h044 : weightedMaskMass a 4195392 (-18874619) =
      weightedMaskMass a 5505024 (-18874619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195392, 5505024, -18874619) (by decide)]
  have h045 : weightedMaskMass a 4195393 (18206660) =
      weightedMaskMass a 4456457 (18206660) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195393, 4456457, 18206660) (by decide)]
  have h046 : weightedMaskMass a 4195394 (-10965406) =
      weightedMaskMass a 4456488 (-10965406) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195394, 4456488, -10965406) (by decide)]
  have h047 : weightedMaskMass a 4195394 (57050080) =
      weightedMaskMass a 5537792 (57050080) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195394, 5537792, 57050080) (by decide)]
  have h048 : weightedMaskMass a 4195396 (15482647) =
      weightedMaskMass a 4456472 (15482647) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195396, 4456472, 15482647) (by decide)]
  have h049 : weightedMaskMass a 4195842 (-28060735) =
      weightedMaskMass a 4720128 (-28060735) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4195842, 4720128, -28060735) (by decide)]
  have h050 : weightedMaskMass a 4196353 (51581855) =
      weightedMaskMass a 4227073 (51581855) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4196353, 4227073, 51581855) (by decide)]
  have h051 : weightedMaskMass a 4196353 (-101196221) =
      weightedMaskMass a 4718593 (-101196221) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4196353, 4718593, -101196221) (by decide)]
  have h052 : weightedMaskMass a 4199426 (-236431452) =
      weightedMaskMass a 4489220 (-236431452) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4199426, 4489220, -236431452) (by decide)]
  have h053 : weightedMaskMass a 4199426 (196082709) =
      weightedMaskMass a 4719632 (196082709) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4199426, 4719632, 196082709) (by decide)]
  have h054 : weightedMaskMass a 4199488 (-56658168) =
      weightedMaskMass a 5505028 (-56658168) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4199488, 5505028, -56658168) (by decide)]
  have h055 : weightedMaskMass a 4199490 (40905443) =
      weightedMaskMass a 5537796 (40905443) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4199490, 5537796, 40905443) (by decide)]
  have h056 : weightedMaskMass a 4200449 (36890589) =
      weightedMaskMass a 4231169 (36890589) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4200449, 4231169, 36890589) (by decide)]
  have h057 : weightedMaskMass a 4202504 (40598419) =
      weightedMaskMass a 4235264 (40598419) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4202504, 4235264, 40598419) (by decide)]
  have h058 : weightedMaskMass a 4210690 (-20664321) =
      weightedMaskMass a 4210720 (-20664321) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210690, 4210720, -20664321) (by decide)]
  have h059 : weightedMaskMass a 4210692 (-122399668) =
      weightedMaskMass a 4210704 (-122399668) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210692, 4210704, -122399668) (by decide)]
  have h060 : weightedMaskMass a 4210696 (36130800) =
      weightedMaskMass a 4210752 (36130800) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210696, 4210752, 36130800) (by decide)]
  have h061 : weightedMaskMass a 4210697 (-61161920) =
      weightedMaskMass a 4210753 (-61161920) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210697, 4210753, -61161920) (by decide)]
  have h062 : weightedMaskMass a 4210706 (-83775730) =
      weightedMaskMass a 4210724 (-83775730) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210706, 4210724, -83775730) (by decide)]
  have h063 : weightedMaskMass a 4210712 (-180518311) =
      weightedMaskMass a 4210756 (-180518311) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210712, 4210756, -180518311) (by decide)]
  have h064 : weightedMaskMass a 4210728 (-80070132) =
      weightedMaskMass a 4210754 (-80070132) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4210728, 4210754, -80070132) (by decide)]
  have h065 : weightedMaskMass a 4211712 (-759255) =
      weightedMaskMass a 4472832 (-759255) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211712, 4472832, -759255) (by decide)]
  have h066 : weightedMaskMass a 4211713 (-3882156) =
      weightedMaskMass a 4472833 (-3882156) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211713, 4472833, -3882156) (by decide)]
  have h067 : weightedMaskMass a 4211714 (41638502) =
      weightedMaskMass a 4472864 (41638502) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211714, 4472864, 41638502) (by decide)]
  have h068 : weightedMaskMass a 4211716 (-48089197) =
      weightedMaskMass a 4472848 (-48089197) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211716, 4472848, -48089197) (by decide)]
  have h069 : weightedMaskMass a 4211728 (-96557421) =
      weightedMaskMass a 4472836 (-96557421) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211728, 4472836, -96557421) (by decide)]
  have h070 : weightedMaskMass a 4211730 (74617138) =
      weightedMaskMass a 4472868 (74617138) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211730, 4472868, 74617138) (by decide)]
  have h071 : weightedMaskMass a 4211732 (308145792) =
      weightedMaskMass a 4472852 (308145792) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211732, 4472852, 308145792) (by decide)]
  have h072 : weightedMaskMass a 4211776 (46580592) =
      weightedMaskMass a 4472840 (46580592) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211776, 4472840, 46580592) (by decide)]
  have h073 : weightedMaskMass a 4211777 (-68491099) =
      weightedMaskMass a 4472841 (-68491099) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211777, 4472841, -68491099) (by decide)]
  have h074 : weightedMaskMass a 4211778 (-125635301) =
      weightedMaskMass a 4472872 (-125635301) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211778, 4472872, -125635301) (by decide)]
  have h075 : weightedMaskMass a 4211780 (26633686) =
      weightedMaskMass a 4472856 (26633686) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4211780, 4472856, 26633686) (by decide)]
  have h076 : weightedMaskMass a 4227081 (128078650) =
      weightedMaskMass a 4718657 (128078650) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4227081, 4718657, 128078650) (by decide)]
  have h077 : weightedMaskMass a 4227096 (145577454) =
      weightedMaskMass a 4718660 (145577454) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4227096, 4718660, 145577454) (by decide)]
  have h078 : weightedMaskMass a 4227137 (30739346) =
      weightedMaskMass a 4718601 (30739346) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4227137, 4718601, 30739346) (by decide)]
  have h079 : weightedMaskMass a 4227140 (34804855) =
      weightedMaskMass a 4718616 (34804855) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4227140, 4718616, 34804855) (by decide)]
  have h080 : weightedMaskMass a 4227328 (22397719) =
      weightedMaskMass a 5243136 (22397719) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4227328, 5243136, 22397719) (by decide)]
  have h081 : weightedMaskMass a 4243456 (-4410853) =
      weightedMaskMass a 4734976 (-4410853) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243456, 4734976, -4410853) (by decide)]
  have h082 : weightedMaskMass a 4243457 (-31710606) =
      weightedMaskMass a 4734977 (-31710606) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243457, 4734977, -31710606) (by decide)]
  have h083 : weightedMaskMass a 4243458 (19587044) =
      weightedMaskMass a 4735008 (19587044) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243458, 4735008, 19587044) (by decide)]
  have h084 : weightedMaskMass a 4243460 (88053049) =
      weightedMaskMass a 4734992 (88053049) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243460, 4734992, 88053049) (by decide)]
  have h085 : weightedMaskMass a 4243464 (29271143) =
      weightedMaskMass a 4735040 (29271143) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243464, 4735040, 29271143) (by decide)]
  have h086 : weightedMaskMass a 4243465 (53864402) =
      weightedMaskMass a 4735041 (53864402) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243465, 4735041, 53864402) (by decide)]
  have h087 : weightedMaskMass a 4243472 (77551420) =
      weightedMaskMass a 4734980 (77551420) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243472, 4734980, 77551420) (by decide)]
  have h088 : weightedMaskMass a 4243474 (-75283976) =
      weightedMaskMass a 4735012 (-75283976) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243474, 4735012, -75283976) (by decide)]
  have h089 : weightedMaskMass a 4243476 (-161388020) =
      weightedMaskMass a 4734996 (-161388020) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243476, 4734996, -161388020) (by decide)]
  have h090 : weightedMaskMass a 4243480 (-76785703) =
      weightedMaskMass a 4735044 (-76785703) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243480, 4735044, -76785703) (by decide)]
  have h091 : weightedMaskMass a 4243520 (36367572) =
      weightedMaskMass a 4734984 (36367572) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243520, 4734984, 36367572) (by decide)]
  have h092 : weightedMaskMass a 4243521 (22475575) =
      weightedMaskMass a 4734985 (22475575) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243521, 4734985, 22475575) (by decide)]
  have h093 : weightedMaskMass a 4243522 (-69519463) =
      weightedMaskMass a 4735016 (-69519463) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243522, 4735016, -69519463) (by decide)]
  have h094 : weightedMaskMass a 4243524 (-56812928) =
      weightedMaskMass a 4735000 (-56812928) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4243524, 4735000, -56812928) (by decide)]
  have h095 : weightedMaskMass a 4457476 (-8634063) =
      weightedMaskMass a 4457488 (-8634063) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4457476, 4457488, -8634063) (by decide)]
  have h096 : weightedMaskMass a 4457476 (56380630) =
      weightedMaskMass a 4461568 (56380630) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4457476, 4461568, 56380630) (by decide)]
  have h097 : weightedMaskMass a 4458504 (24670728) =
      weightedMaskMass a 5507072 (24670728) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4458504, 5507072, 24670728) (by decide)]
  have h098 : weightedMaskMass a 4458536 (-165157365) =
      weightedMaskMass a 5539840 (-165157365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4458536, 5539840, -165157365) (by decide)]
  have h099 : weightedMaskMass a 4473860 (99675723) =
      weightedMaskMass a 4473872 (99675723) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (4473860, 4473872, 99675723) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt22 s.val : ℝ)) = (((((((weightedMaskMass a 2646308 (-380267850) + (-weightedMaskMass a 3678984 (-380267850) + weightedMaskMass a 2646312 (-295309054))) + (-weightedMaskMass a 3694856 (-295309054) + (weightedMaskMass a 2752577 (-74552364) + -weightedMaskMass a 2768897 (-74552364)))) + ((weightedMaskMass a 2753024 (-94258938) + (-weightedMaskMass a 3145860 (-94258938) + weightedMaskMass a 2753032 (98809120))) + (-weightedMaskMass a 3178628 (98809120) + (weightedMaskMass a 2753088 (104233715) + -weightedMaskMass a 3145892 (104233715))))) + (((weightedMaskMass a 3146018 (49414159) + (-weightedMaskMass a 3148064 (49414159) + weightedMaskMass a 3146020 (73479696))) + (-weightedMaskMass a 3146528 (73479696) + (weightedMaskMass a 3146024 (127572960) + -weightedMaskMass a 3162400 (127572960)))) + ((weightedMaskMass a 3146530 (-24377932) + (-weightedMaskMass a 3148068 (-24377932) + weightedMaskMass a 3146536 (-11782306))) + ((-weightedMaskMass a 3162404 (-11782306) + weightedMaskMass a 3148072 (-128709916)) + (-weightedMaskMass a 3162402 (-128709916) + weightedMaskMass a 3154208 (-174384866)))))) + ((((-weightedMaskMass a 3670304 (-174384866) + (weightedMaskMass a 3154210 (281072492) + -weightedMaskMass a 3672352 (281072492))) + (weightedMaskMass a 3154212 (64697531) + (-weightedMaskMass a 3670816 (64697531) + weightedMaskMass a 3154216 (-217500160)))) + ((-weightedMaskMass a 3686688 (-217500160) + (weightedMaskMass a 3154720 (157580656) + -weightedMaskMass a 3670308 (157580656))) + (weightedMaskMass a 3154722 (-135286308) + (-weightedMaskMass a 3672356 (-135286308) + weightedMaskMass a 3154724 (0))))) + (((-weightedMaskMass a 3670820 (0) + (weightedMaskMass a 3154728 (54634533) + -weightedMaskMass a 3686692 (54634533))) + (weightedMaskMass a 3170592 (331216741) + (-weightedMaskMass a 3670312 (331216741) + weightedMaskMass a 3170594 (-566327120)))) + ((-weightedMaskMass a 3672360 (-566327120) + (weightedMaskMass a 3170596 (-285933022) + -weightedMaskMass a 3670824 (-285933022))) + ((weightedMaskMass a 3170600 (-57490333) + -weightedMaskMass a 3686696 (-57490333)) + (weightedMaskMass a 3409920 (-72673012) + -weightedMaskMass a 4720648 (-72673012))))))) + (((((weightedMaskMass a 3409928 (45511335) + (-weightedMaskMass a 5769224 (45511335) + weightedMaskMass a 3409952 (39415713))) + (-weightedMaskMass a 4753416 (39415713) + (weightedMaskMass a 3409960 (45667639) + -weightedMaskMass a 5801992 (45667639)))) + ((weightedMaskMass a 3440640 (-46185856) + (-weightedMaskMass a 4227138 (-46185856) + weightedMaskMass a 3440640 (26359903))) + (-weightedMaskMass a 4718632 (26359903) + (weightedMaskMass a 3440644 (-21467068) + -weightedMaskMass a 4231234 (-21467068))))) + (((weightedMaskMass a 3440648 (-38862806) + (-weightedMaskMass a 5767208 (-38862806) + weightedMaskMass a 3442688 (82415492))) + (-weightedMaskMass a 4720680 (82415492) + (weightedMaskMass a 3442696 (-45109675) + -weightedMaskMass a 5769256 (-45109675)))) + ((weightedMaskMass a 3678500 (-298818745) + (-weightedMaskMass a 3679008 (-298818745) + weightedMaskMass a 3678504 (536713459))) + ((-weightedMaskMass a 3694880 (536713459) + weightedMaskMass a 3679016 (-886178907)) + (-weightedMaskMass a 3694884 (-886178907) + weightedMaskMass a 4194313 (35931123)))))) + ((((-weightedMaskMass a 4194369 (35931123) + (weightedMaskMass a 4194328 (983208) + -weightedMaskMass a 4194372 (983208))) + (weightedMaskMass a 4195329 (1874486) + (-weightedMaskMass a 4456449 (1874486) + weightedMaskMass a 4195344 (-40348743)))) + ((-weightedMaskMass a 4199424 (-40348743) + (weightedMaskMass a 4195344 (50014672) + -weightedMaskMass a 4456452 (50014672))) + (weightedMaskMass a 4195348 (-2268105) + (-weightedMaskMass a 4456468 (-2268105) + weightedMaskMass a 4195392 (10965406))))) + (((-weightedMaskMass a 4456456 (10965406) + (weightedMaskMass a 4195392 (-18874619) + -weightedMaskMass a 5505024 (-18874619))) + (weightedMaskMass a 4195393 (18206660) + (-weightedMaskMass a 4456457 (18206660) + weightedMaskMass a 4195394 (-10965406)))) + ((-weightedMaskMass a 4456488 (-10965406) + (weightedMaskMass a 4195394 (57050080) + -weightedMaskMass a 5537792 (57050080))) + ((weightedMaskMass a 4195396 (15482647) + -weightedMaskMass a 4456472 (15482647)) + (weightedMaskMass a 4195842 (-28060735) + -weightedMaskMass a 4720128 (-28060735)))))))) + ((((((weightedMaskMass a 4196353 (51581855) + (-weightedMaskMass a 4227073 (51581855) + weightedMaskMass a 4196353 (-101196221))) + (-weightedMaskMass a 4718593 (-101196221) + (weightedMaskMass a 4199426 (-236431452) + -weightedMaskMass a 4489220 (-236431452)))) + ((weightedMaskMass a 4199426 (196082709) + (-weightedMaskMass a 4719632 (196082709) + weightedMaskMass a 4199488 (-56658168))) + (-weightedMaskMass a 5505028 (-56658168) + (weightedMaskMass a 4199490 (40905443) + -weightedMaskMass a 5537796 (40905443))))) + (((weightedMaskMass a 4200449 (36890589) + (-weightedMaskMass a 4231169 (36890589) + weightedMaskMass a 4202504 (40598419))) + (-weightedMaskMass a 4235264 (40598419) + (weightedMaskMass a 4210690 (-20664321) + -weightedMaskMass a 4210720 (-20664321)))) + ((weightedMaskMass a 4210692 (-122399668) + (-weightedMaskMass a 4210704 (-122399668) + weightedMaskMass a 4210696 (36130800))) + ((-weightedMaskMass a 4210752 (36130800) + weightedMaskMass a 4210697 (-61161920)) + (-weightedMaskMass a 4210753 (-61161920) + weightedMaskMass a 4210706 (-83775730)))))) + ((((-weightedMaskMass a 4210724 (-83775730) + (weightedMaskMass a 4210712 (-180518311) + -weightedMaskMass a 4210756 (-180518311))) + (weightedMaskMass a 4210728 (-80070132) + (-weightedMaskMass a 4210754 (-80070132) + weightedMaskMass a 4211712 (-759255)))) + ((-weightedMaskMass a 4472832 (-759255) + (weightedMaskMass a 4211713 (-3882156) + -weightedMaskMass a 4472833 (-3882156))) + (weightedMaskMass a 4211714 (41638502) + (-weightedMaskMass a 4472864 (41638502) + weightedMaskMass a 4211716 (-48089197))))) + (((-weightedMaskMass a 4472848 (-48089197) + (weightedMaskMass a 4211728 (-96557421) + -weightedMaskMass a 4472836 (-96557421))) + (weightedMaskMass a 4211730 (74617138) + (-weightedMaskMass a 4472868 (74617138) + weightedMaskMass a 4211732 (308145792)))) + ((-weightedMaskMass a 4472852 (308145792) + (weightedMaskMass a 4211776 (46580592) + -weightedMaskMass a 4472840 (46580592))) + ((weightedMaskMass a 4211777 (-68491099) + -weightedMaskMass a 4472841 (-68491099)) + (weightedMaskMass a 4211778 (-125635301) + -weightedMaskMass a 4472872 (-125635301))))))) + (((((weightedMaskMass a 4211780 (26633686) + (-weightedMaskMass a 4472856 (26633686) + weightedMaskMass a 4227081 (128078650))) + (-weightedMaskMass a 4718657 (128078650) + (weightedMaskMass a 4227096 (145577454) + -weightedMaskMass a 4718660 (145577454)))) + ((weightedMaskMass a 4227137 (30739346) + (-weightedMaskMass a 4718601 (30739346) + weightedMaskMass a 4227140 (34804855))) + (-weightedMaskMass a 4718616 (34804855) + (weightedMaskMass a 4227328 (22397719) + -weightedMaskMass a 5243136 (22397719))))) + (((weightedMaskMass a 4243456 (-4410853) + (-weightedMaskMass a 4734976 (-4410853) + weightedMaskMass a 4243457 (-31710606))) + (-weightedMaskMass a 4734977 (-31710606) + (weightedMaskMass a 4243458 (19587044) + -weightedMaskMass a 4735008 (19587044)))) + ((weightedMaskMass a 4243460 (88053049) + (-weightedMaskMass a 4734992 (88053049) + weightedMaskMass a 4243464 (29271143))) + ((-weightedMaskMass a 4735040 (29271143) + weightedMaskMass a 4243465 (53864402)) + (-weightedMaskMass a 4735041 (53864402) + weightedMaskMass a 4243472 (77551420)))))) + ((((-weightedMaskMass a 4734980 (77551420) + (weightedMaskMass a 4243474 (-75283976) + -weightedMaskMass a 4735012 (-75283976))) + (weightedMaskMass a 4243476 (-161388020) + (-weightedMaskMass a 4734996 (-161388020) + weightedMaskMass a 4243480 (-76785703)))) + ((-weightedMaskMass a 4735044 (-76785703) + (weightedMaskMass a 4243520 (36367572) + -weightedMaskMass a 4734984 (36367572))) + (weightedMaskMass a 4243521 (22475575) + (-weightedMaskMass a 4734985 (22475575) + weightedMaskMass a 4243522 (-69519463))))) + (((-weightedMaskMass a 4735016 (-69519463) + (weightedMaskMass a 4243524 (-56812928) + -weightedMaskMass a 4735000 (-56812928))) + (weightedMaskMass a 4457476 (-8634063) + (-weightedMaskMass a 4457488 (-8634063) + weightedMaskMass a 4457476 (56380630)))) + ((-weightedMaskMass a 4461568 (56380630) + (weightedMaskMass a 4458504 (24670728) + -weightedMaskMass a 5507072 (24670728))) + ((weightedMaskMass a 4458536 (-165157365) + -weightedMaskMass a 5539840 (-165157365)) + (weightedMaskMass a 4473860 (99675723) + -weightedMaskMass a 4473872 (99675723))))))))) := by
      simp only [atomCongruenceContributionInt22, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
