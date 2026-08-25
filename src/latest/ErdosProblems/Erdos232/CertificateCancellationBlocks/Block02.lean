/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock02_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights02, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt02 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 521 (-28876607) =
      weightedMaskMass a 2113552 (-28876607) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (521, 2113552, -28876607) (by decide)]
  have h001 : weightedMaskMass a 546 (76221363) =
      weightedMaskMass a 2088 (76221363) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 2088, 76221363) (by decide)]
  have h002 : weightedMaskMass a 546 (-77855654) =
      weightedMaskMass a 2180 (-77855654) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 2180, -77855654) (by decide)]
  have h003 : weightedMaskMass a 546 (31867521) =
      weightedMaskMass a 8452 (31867521) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 8452, 31867521) (by decide)]
  have h004 : weightedMaskMass a 546 (67829109) =
      weightedMaskMass a 16402 (67829109) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 16402, 67829109) (by decide)]
  have h005 : weightedMaskMass a 546 (179732621) =
      weightedMaskMass a 16420 (179732621) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 16420, 179732621) (by decide)]
  have h006 : weightedMaskMass a 546 (-186483918) =
      weightedMaskMass a 131106 (-186483918) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 131106, -186483918) (by decide)]
  have h007 : weightedMaskMass a 546 (67656693) =
      weightedMaskMass a 1048708 (67656693) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1048708, 67656693) (by decide)]
  have h008 : weightedMaskMass a 546 (-5659429) =
      weightedMaskMass a 1049096 (-5659429) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1049096, -5659429) (by decide)]
  have h009 : weightedMaskMass a 546 (-87444082) =
      weightedMaskMass a 1050628 (-87444082) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1050628, -87444082) (by decide)]
  have h010 : weightedMaskMass a 546 (-23192383) =
      weightedMaskMass a 1050752 (-23192383) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1050752, -23192383) (by decide)]
  have h011 : weightedMaskMass a 546 (30248177) =
      weightedMaskMass a 1064962 (30248177) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1064962, 30248177) (by decide)]
  have h012 : weightedMaskMass a 546 (25907526) =
      weightedMaskMass a 1083392 (25907526) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 1083392, 25907526) (by decide)]
  have h013 : weightedMaskMass a 546 (-154064516) =
      weightedMaskMass a 2621952 (-154064516) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (546, 2621952, -154064516) (by decide)]
  have h014 : weightedMaskMass a 548 (-27775363) =
      weightedMaskMass a 2308 (-27775363) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 2308, -27775363) (by decide)]
  have h015 : weightedMaskMass a 548 (-159294854) =
      weightedMaskMass a 17412 (-159294854) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 17412, -159294854) (by decide)]
  have h016 : weightedMaskMass a 548 (-128511678) =
      weightedMaskMass a 65576 (-128511678) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 65576, -128511678) (by decide)]
  have h017 : weightedMaskMass a 548 (98772365) =
      weightedMaskMass a 131112 (98772365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 131112, 98772365) (by decide)]
  have h018 : weightedMaskMass a 548 (-32468424) =
      weightedMaskMass a 278544 (-32468424) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 278544, -32468424) (by decide)]
  have h019 : weightedMaskMass a 548 (16548301) =
      weightedMaskMass a 524832 (16548301) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 524832, 16548301) (by decide)]
  have h020 : weightedMaskMass a 548 (25894234) =
      weightedMaskMass a 1048705 (25894234) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 1048705, 25894234) (by decide)]
  have h021 : weightedMaskMass a 548 (-50651418) =
      weightedMaskMass a 1049092 (-50651418) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 1049092, -50651418) (by decide)]
  have h022 : weightedMaskMass a 548 (12657489) =
      weightedMaskMass a 1056772 (12657489) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 1056772, 12657489) (by decide)]
  have h023 : weightedMaskMass a 548 (-33183827) =
      weightedMaskMass a 1064961 (-33183827) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 1064961, -33183827) (by decide)]
  have h024 : weightedMaskMass a 548 (178710014) =
      weightedMaskMass a 1081346 (178710014) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 1081346, 178710014) (by decide)]
  have h025 : weightedMaskMass a 548 (184885197) =
      weightedMaskMass a 2097218 (184885197) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 2097218, 184885197) (by decide)]
  have h026 : weightedMaskMass a 548 (-78209641) =
      weightedMaskMass a 2097666 (-78209641) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (548, 2097666, -78209641) (by decide)]
  have h027 : weightedMaskMass a 552 (86248061) =
      weightedMaskMass a 1064964 (86248061) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (552, 1064964, 86248061) (by decide)]
  have h028 : weightedMaskMass a 577 (15452511) =
      weightedMaskMass a 4256 (15452511) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (577, 4256, 15452511) (by decide)]
  have h029 : weightedMaskMass a 577 (48617812) =
      weightedMaskMass a 20608 (48617812) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (577, 20608, 48617812) (by decide)]
  have h030 : weightedMaskMass a 577 (-11599294) =
      weightedMaskMass a 82048 (-11599294) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (577, 82048, -11599294) (by decide)]
  have h031 : weightedMaskMass a 578 (89789030) =
      weightedMaskMass a 2208 (89789030) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 2208, 89789030) (by decide)]
  have h032 : weightedMaskMass a 578 (-54411698) =
      weightedMaskMass a 16513 (-54411698) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 16513, -54411698) (by decide)]
  have h033 : weightedMaskMass a 578 (-101859668) =
      weightedMaskMass a 131202 (-101859668) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 131202, -101859668) (by decide)]
  have h034 : weightedMaskMass a 578 (25074905) =
      weightedMaskMass a 147460 (25074905) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 147460, 25074905) (by decide)]
  have h035 : weightedMaskMass a 578 (45697015) =
      weightedMaskMass a 528448 (45697015) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 528448, 45697015) (by decide)]
  have h036 : weightedMaskMass a 578 (30767863) =
      weightedMaskMass a 1048612 (30767863) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 1048612, 30767863) (by decide)]
  have h037 : weightedMaskMass a 578 (-3307818) =
      weightedMaskMass a 1049120 (-3307818) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 1049120, -3307818) (by decide)]
  have h038 : weightedMaskMass a 578 (-162514) =
      weightedMaskMass a 1065088 (-162514) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 1065088, -162514) (by decide)]
  have h039 : weightedMaskMass a 578 (44169782) =
      weightedMaskMass a 2097728 (44169782) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (578, 2097728, 44169782) (by decide)]
  have h040 : weightedMaskMass a 580 (-27433067) =
      weightedMaskMass a 65696 (-27433067) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (580, 65696, -27433067) (by decide)]
  have h041 : weightedMaskMass a 580 (-26540814) =
      weightedMaskMass a 409600 (-26540814) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (580, 409600, -26540814) (by decide)]
  have h042 : weightedMaskMass a 580 (40094905) =
      weightedMaskMass a 526400 (40094905) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (580, 526400, 40094905) (by decide)]
  have h043 : weightedMaskMass a 768 (-156346722) =
      weightedMaskMass a 1040 (-156346722) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 1040, -156346722) (by decide)]
  have h044 : weightedMaskMass a 768 (-13566971) =
      weightedMaskMass a 4097 (-13566971) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 4097, -13566971) (by decide)]
  have h045 : weightedMaskMass a 768 (79249681) =
      weightedMaskMass a 6144 (79249681) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 6144, 79249681) (by decide)]
  have h046 : weightedMaskMass a 768 (-142244832) =
      weightedMaskMass a 8208 (-142244832) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 8208, -142244832) (by decide)]
  have h047 : weightedMaskMass a 768 (-4299785) =
      weightedMaskMass a 32769 (-4299785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 32769, -4299785) (by decide)]
  have h048 : weightedMaskMass a 768 (-87107772) =
      weightedMaskMass a 36864 (-87107772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 36864, -87107772) (by decide)]
  have h049 : weightedMaskMass a 768 (29157997) =
      weightedMaskMass a 65552 (29157997) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 65552, 29157997) (by decide)]
  have h050 : weightedMaskMass a 768 (-64245401) =
      weightedMaskMass a 73728 (-64245401) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 73728, -64245401) (by decide)]
  have h051 : weightedMaskMass a 768 (-19117336) =
      weightedMaskMass a 262148 (-19117336) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 262148, -19117336) (by decide)]
  have h052 : weightedMaskMass a 768 (107328037) =
      weightedMaskMass a 264192 (107328037) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 264192, 107328037) (by decide)]
  have h053 : weightedMaskMass a 768 (-2364504) =
      weightedMaskMass a 524289 (-2364504) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 524289, -2364504) (by decide)]
  have h054 : weightedMaskMass a 768 (13618695) =
      weightedMaskMass a 2097156 (13618695) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 2097156, 13618695) (by decide)]
  have h055 : weightedMaskMass a 768 (131498356) =
      weightedMaskMass a 2228224 (131498356) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 2228224, 131498356) (by decide)]
  have h056 : weightedMaskMass a 768 (25433245) =
      weightedMaskMass a 4196352 (25433245) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 4196352, 25433245) (by decide)]
  have h057 : weightedMaskMass a 768 (31548085) =
      weightedMaskMass a 4198400 (31548085) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (768, 4198400, 31548085) (by decide)]
  have h058 : weightedMaskMass a 770 (-32024679) =
      weightedMaskMass a 3088 (-32024679) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 3088, -32024679) (by decide)]
  have h059 : weightedMaskMass a 770 (17827415) =
      weightedMaskMass a 6176 (17827415) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 6176, 17827415) (by decide)]
  have h060 : weightedMaskMass a 770 (-2163013) =
      weightedMaskMass a 8210 (-2163013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 8210, -2163013) (by decide)]
  have h061 : weightedMaskMass a 770 (58812708) =
      weightedMaskMass a 20481 (58812708) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 20481, 58812708) (by decide)]
  have h062 : weightedMaskMass a 770 (-117831674) =
      weightedMaskMass a 65560 (-117831674) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 65560, -117831674) (by decide)]
  have h063 : weightedMaskMass a 770 (37948317) =
      weightedMaskMass a 73732 (37948317) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 73732, 37948317) (by decide)]
  have h064 : weightedMaskMass a 770 (-60626386) =
      weightedMaskMass a 264208 (-60626386) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 264208, -60626386) (by decide)]
  have h065 : weightedMaskMass a 770 (-1015742) =
      weightedMaskMass a 266241 (-1015742) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 266241, -1015742) (by decide)]
  have h066 : weightedMaskMass a 770 (-6891526) =
      weightedMaskMass a 393220 (-6891526) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 393220, -6891526) (by decide)]
  have h067 : weightedMaskMass a 770 (71025816) =
      weightedMaskMass a 524801 (71025816) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 524801, 71025816) (by decide)]
  have h068 : weightedMaskMass a 770 (-14499163) =
      weightedMaskMass a 530432 (-14499163) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 530432, -14499163) (by decide)]
  have h069 : weightedMaskMass a 770 (119810283) =
      weightedMaskMass a 2097220 (119810283) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 2097220, 119810283) (by decide)]
  have h070 : weightedMaskMass a 770 (-11531386) =
      weightedMaskMass a 2099204 (-11531386) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (770, 2099204, -11531386) (by decide)]
  have h071 : weightedMaskMass a 772 (-32412184) =
      weightedMaskMass a 6208 (-32412184) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 6208, -32412184) (by decide)]
  have h072 : weightedMaskMass a 772 (-35148744) =
      weightedMaskMass a 17424 (-35148744) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 17424, -35148744) (by decide)]
  have h073 : weightedMaskMass a 772 (132303270) =
      weightedMaskMass a 278532 (132303270) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 278532, 132303270) (by decide)]
  have h074 : weightedMaskMass a 772 (83738273) =
      weightedMaskMass a 1081345 (83738273) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 1081345, 83738273) (by decide)]
  have h075 : weightedMaskMass a 772 (-88055737) =
      weightedMaskMass a 2097668 (-88055737) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 2097668, -88055737) (by decide)]
  have h076 : weightedMaskMass a 772 (-103656249) =
      weightedMaskMass a 2228226 (-103656249) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (772, 2228226, -103656249) (by decide)]
  have h077 : weightedMaskMass a 776 (44977265) =
      weightedMaskMass a 4161 (44977265) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (776, 4161, 44977265) (by decide)]
  have h078 : weightedMaskMass a 776 (48633156) =
      weightedMaskMass a 4225 (48633156) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (776, 4225, 48633156) (by decide)]
  have h079 : weightedMaskMass a 776 (-29750123) =
      weightedMaskMass a 6272 (-29750123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (776, 6272, -29750123) (by decide)]
  have h080 : weightedMaskMass a 776 (49413419) =
      weightedMaskMass a 81936 (49413419) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (776, 81936, 49413419) (by decide)]
  have h081 : weightedMaskMass a 776 (-30514938) =
      weightedMaskMass a 2113540 (-30514938) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (776, 2113540, -30514938) (by decide)]
  have h082 : weightedMaskMass a 800 (19599454) =
      weightedMaskMass a 24592 (19599454) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (800, 24592, 19599454) (by decide)]
  have h083 : weightedMaskMass a 800 (43208515) =
      weightedMaskMass a 32897 (43208515) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (800, 32897, 43208515) (by decide)]
  have h084 : weightedMaskMass a 800 (71723445) =
      weightedMaskMass a 36928 (71723445) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (800, 36928, 71723445) (by decide)]
  have h085 : weightedMaskMass a 800 (-120815078) =
      weightedMaskMass a 2228736 (-120815078) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (800, 2228736, -120815078) (by decide)]
  have h086 : weightedMaskMass a 800 (61240323) =
      weightedMaskMass a 3145732 (61240323) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (800, 3145732, 61240323) (by decide)]
  have h087 : weightedMaskMass a 802 (-27116103) =
      weightedMaskMass a 24594 (-27116103) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (802, 24594, -27116103) (by decide)]
  have h088 : weightedMaskMass a 802 (41416570) =
      weightedMaskMass a 3147780 (41416570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (802, 3147780, 41416570) (by decide)]
  have h089 : weightedMaskMass a 804 (-70128417) =
      weightedMaskMass a 1081473 (-70128417) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (804, 1081473, -70128417) (by decide)]
  have h090 : weightedMaskMass a 804 (92972970) =
      weightedMaskMass a 2228738 (92972970) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (804, 2228738, 92972970) (by decide)]
  have h091 : weightedMaskMass a 804 (-28949772) =
      weightedMaskMass a 3146244 (-28949772) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (804, 3146244, -28949772) (by decide)]
  have h092 : weightedMaskMass a 808 (-86256212) =
      weightedMaskMass a 3162116 (-86256212) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (808, 3162116, -86256212) (by decide)]
  have h093 : weightedMaskMass a 1042 (-84798995) =
      weightedMaskMass a 1044 (-84798995) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 1044, -84798995) (by decide)]
  have h094 : weightedMaskMass a 1042 (-1091901) =
      weightedMaskMass a 8212 (-1091901) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 8212, -1091901) (by decide)]
  have h095 : weightedMaskMass a 1042 (-158541441) =
      weightedMaskMass a 34817 (-158541441) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 34817, -158541441) (by decide)]
  have h096 : weightedMaskMass a 1042 (-14351855) =
      weightedMaskMass a 49153 (-14351855) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 49153, -14351855) (by decide)]
  have h097 : weightedMaskMass a 1042 (39019549) =
      weightedMaskMass a 65554 (39019549) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 65554, 39019549) (by decide)]
  have h098 : weightedMaskMass a 1042 (-19697359) =
      weightedMaskMass a 73736 (-19697359) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 73736, -19697359) (by decide)]
  have h099 : weightedMaskMass a 1042 (38308560) =
      weightedMaskMass a 74752 (38308560) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1042, 74752, 38308560) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt02 s.val : ℝ)) = (((((((weightedMaskMass a 521 (-28876607) + (-weightedMaskMass a 2113552 (-28876607) + weightedMaskMass a 546 (76221363))) + (-weightedMaskMass a 2088 (76221363) + (weightedMaskMass a 546 (-77855654) + -weightedMaskMass a 2180 (-77855654)))) + ((weightedMaskMass a 546 (31867521) + (-weightedMaskMass a 8452 (31867521) + weightedMaskMass a 546 (67829109))) + (-weightedMaskMass a 16402 (67829109) + (weightedMaskMass a 546 (179732621) + -weightedMaskMass a 16420 (179732621))))) + (((weightedMaskMass a 546 (-186483918) + (-weightedMaskMass a 131106 (-186483918) + weightedMaskMass a 546 (67656693))) + (-weightedMaskMass a 1048708 (67656693) + (weightedMaskMass a 546 (-5659429) + -weightedMaskMass a 1049096 (-5659429)))) + ((weightedMaskMass a 546 (-87444082) + (-weightedMaskMass a 1050628 (-87444082) + weightedMaskMass a 546 (-23192383))) + ((-weightedMaskMass a 1050752 (-23192383) + weightedMaskMass a 546 (30248177)) + (-weightedMaskMass a 1064962 (30248177) + weightedMaskMass a 546 (25907526)))))) + ((((-weightedMaskMass a 1083392 (25907526) + (weightedMaskMass a 546 (-154064516) + -weightedMaskMass a 2621952 (-154064516))) + (weightedMaskMass a 548 (-27775363) + (-weightedMaskMass a 2308 (-27775363) + weightedMaskMass a 548 (-159294854)))) + ((-weightedMaskMass a 17412 (-159294854) + (weightedMaskMass a 548 (-128511678) + -weightedMaskMass a 65576 (-128511678))) + (weightedMaskMass a 548 (98772365) + (-weightedMaskMass a 131112 (98772365) + weightedMaskMass a 548 (-32468424))))) + (((-weightedMaskMass a 278544 (-32468424) + (weightedMaskMass a 548 (16548301) + -weightedMaskMass a 524832 (16548301))) + (weightedMaskMass a 548 (25894234) + (-weightedMaskMass a 1048705 (25894234) + weightedMaskMass a 548 (-50651418)))) + ((-weightedMaskMass a 1049092 (-50651418) + (weightedMaskMass a 548 (12657489) + -weightedMaskMass a 1056772 (12657489))) + ((weightedMaskMass a 548 (-33183827) + -weightedMaskMass a 1064961 (-33183827)) + (weightedMaskMass a 548 (178710014) + -weightedMaskMass a 1081346 (178710014))))))) + (((((weightedMaskMass a 548 (184885197) + (-weightedMaskMass a 2097218 (184885197) + weightedMaskMass a 548 (-78209641))) + (-weightedMaskMass a 2097666 (-78209641) + (weightedMaskMass a 552 (86248061) + -weightedMaskMass a 1064964 (86248061)))) + ((weightedMaskMass a 577 (15452511) + (-weightedMaskMass a 4256 (15452511) + weightedMaskMass a 577 (48617812))) + (-weightedMaskMass a 20608 (48617812) + (weightedMaskMass a 577 (-11599294) + -weightedMaskMass a 82048 (-11599294))))) + (((weightedMaskMass a 578 (89789030) + (-weightedMaskMass a 2208 (89789030) + weightedMaskMass a 578 (-54411698))) + (-weightedMaskMass a 16513 (-54411698) + (weightedMaskMass a 578 (-101859668) + -weightedMaskMass a 131202 (-101859668)))) + ((weightedMaskMass a 578 (25074905) + (-weightedMaskMass a 147460 (25074905) + weightedMaskMass a 578 (45697015))) + ((-weightedMaskMass a 528448 (45697015) + weightedMaskMass a 578 (30767863)) + (-weightedMaskMass a 1048612 (30767863) + weightedMaskMass a 578 (-3307818)))))) + ((((-weightedMaskMass a 1049120 (-3307818) + (weightedMaskMass a 578 (-162514) + -weightedMaskMass a 1065088 (-162514))) + (weightedMaskMass a 578 (44169782) + (-weightedMaskMass a 2097728 (44169782) + weightedMaskMass a 580 (-27433067)))) + ((-weightedMaskMass a 65696 (-27433067) + (weightedMaskMass a 580 (-26540814) + -weightedMaskMass a 409600 (-26540814))) + (weightedMaskMass a 580 (40094905) + (-weightedMaskMass a 526400 (40094905) + weightedMaskMass a 768 (-156346722))))) + (((-weightedMaskMass a 1040 (-156346722) + (weightedMaskMass a 768 (-13566971) + -weightedMaskMass a 4097 (-13566971))) + (weightedMaskMass a 768 (79249681) + (-weightedMaskMass a 6144 (79249681) + weightedMaskMass a 768 (-142244832)))) + ((-weightedMaskMass a 8208 (-142244832) + (weightedMaskMass a 768 (-4299785) + -weightedMaskMass a 32769 (-4299785))) + ((weightedMaskMass a 768 (-87107772) + -weightedMaskMass a 36864 (-87107772)) + (weightedMaskMass a 768 (29157997) + -weightedMaskMass a 65552 (29157997)))))))) + ((((((weightedMaskMass a 768 (-64245401) + (-weightedMaskMass a 73728 (-64245401) + weightedMaskMass a 768 (-19117336))) + (-weightedMaskMass a 262148 (-19117336) + (weightedMaskMass a 768 (107328037) + -weightedMaskMass a 264192 (107328037)))) + ((weightedMaskMass a 768 (-2364504) + (-weightedMaskMass a 524289 (-2364504) + weightedMaskMass a 768 (13618695))) + (-weightedMaskMass a 2097156 (13618695) + (weightedMaskMass a 768 (131498356) + -weightedMaskMass a 2228224 (131498356))))) + (((weightedMaskMass a 768 (25433245) + (-weightedMaskMass a 4196352 (25433245) + weightedMaskMass a 768 (31548085))) + (-weightedMaskMass a 4198400 (31548085) + (weightedMaskMass a 770 (-32024679) + -weightedMaskMass a 3088 (-32024679)))) + ((weightedMaskMass a 770 (17827415) + (-weightedMaskMass a 6176 (17827415) + weightedMaskMass a 770 (-2163013))) + ((-weightedMaskMass a 8210 (-2163013) + weightedMaskMass a 770 (58812708)) + (-weightedMaskMass a 20481 (58812708) + weightedMaskMass a 770 (-117831674)))))) + ((((-weightedMaskMass a 65560 (-117831674) + (weightedMaskMass a 770 (37948317) + -weightedMaskMass a 73732 (37948317))) + (weightedMaskMass a 770 (-60626386) + (-weightedMaskMass a 264208 (-60626386) + weightedMaskMass a 770 (-1015742)))) + ((-weightedMaskMass a 266241 (-1015742) + (weightedMaskMass a 770 (-6891526) + -weightedMaskMass a 393220 (-6891526))) + (weightedMaskMass a 770 (71025816) + (-weightedMaskMass a 524801 (71025816) + weightedMaskMass a 770 (-14499163))))) + (((-weightedMaskMass a 530432 (-14499163) + (weightedMaskMass a 770 (119810283) + -weightedMaskMass a 2097220 (119810283))) + (weightedMaskMass a 770 (-11531386) + (-weightedMaskMass a 2099204 (-11531386) + weightedMaskMass a 772 (-32412184)))) + ((-weightedMaskMass a 6208 (-32412184) + (weightedMaskMass a 772 (-35148744) + -weightedMaskMass a 17424 (-35148744))) + ((weightedMaskMass a 772 (132303270) + -weightedMaskMass a 278532 (132303270)) + (weightedMaskMass a 772 (83738273) + -weightedMaskMass a 1081345 (83738273))))))) + (((((weightedMaskMass a 772 (-88055737) + (-weightedMaskMass a 2097668 (-88055737) + weightedMaskMass a 772 (-103656249))) + (-weightedMaskMass a 2228226 (-103656249) + (weightedMaskMass a 776 (44977265) + -weightedMaskMass a 4161 (44977265)))) + ((weightedMaskMass a 776 (48633156) + (-weightedMaskMass a 4225 (48633156) + weightedMaskMass a 776 (-29750123))) + (-weightedMaskMass a 6272 (-29750123) + (weightedMaskMass a 776 (49413419) + -weightedMaskMass a 81936 (49413419))))) + (((weightedMaskMass a 776 (-30514938) + (-weightedMaskMass a 2113540 (-30514938) + weightedMaskMass a 800 (19599454))) + (-weightedMaskMass a 24592 (19599454) + (weightedMaskMass a 800 (43208515) + -weightedMaskMass a 32897 (43208515)))) + ((weightedMaskMass a 800 (71723445) + (-weightedMaskMass a 36928 (71723445) + weightedMaskMass a 800 (-120815078))) + ((-weightedMaskMass a 2228736 (-120815078) + weightedMaskMass a 800 (61240323)) + (-weightedMaskMass a 3145732 (61240323) + weightedMaskMass a 802 (-27116103)))))) + ((((-weightedMaskMass a 24594 (-27116103) + (weightedMaskMass a 802 (41416570) + -weightedMaskMass a 3147780 (41416570))) + (weightedMaskMass a 804 (-70128417) + (-weightedMaskMass a 1081473 (-70128417) + weightedMaskMass a 804 (92972970)))) + ((-weightedMaskMass a 2228738 (92972970) + (weightedMaskMass a 804 (-28949772) + -weightedMaskMass a 3146244 (-28949772))) + (weightedMaskMass a 808 (-86256212) + (-weightedMaskMass a 3162116 (-86256212) + weightedMaskMass a 1042 (-84798995))))) + (((-weightedMaskMass a 1044 (-84798995) + (weightedMaskMass a 1042 (-1091901) + -weightedMaskMass a 8212 (-1091901))) + (weightedMaskMass a 1042 (-158541441) + (-weightedMaskMass a 34817 (-158541441) + weightedMaskMass a 1042 (-14351855)))) + ((-weightedMaskMass a 49153 (-14351855) + (weightedMaskMass a 1042 (39019549) + -weightedMaskMass a 65554 (39019549))) + ((weightedMaskMass a 1042 (-19697359) + -weightedMaskMass a 73736 (-19697359)) + (weightedMaskMass a 1042 (38308560) + -weightedMaskMass a 74752 (38308560))))))))) := by
      simp only [atomCongruenceContributionInt02, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
