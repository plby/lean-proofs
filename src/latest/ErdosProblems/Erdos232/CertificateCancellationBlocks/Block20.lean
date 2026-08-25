/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock20_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights20, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt20 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 1180196 (-30575976) =
      weightedMaskMass a 3146306 (-30575976) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180196, 3146306, -30575976) (by decide)]
  have h001 : weightedMaskMass a 1180416 (10592380) =
      weightedMaskMass a 3276864 (10592380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180416, 3276864, 10592380) (by decide)]
  have h002 : weightedMaskMass a 1180420 (-10592380) =
      weightedMaskMass a 3276866 (-10592380) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180420, 3276866, -10592380) (by decide)]
  have h003 : weightedMaskMass a 1180448 (148013) =
      weightedMaskMass a 3277376 (148013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180448, 3277376, 148013) (by decide)]
  have h004 : weightedMaskMass a 1180452 (-39198761) =
      weightedMaskMass a 3277378 (-39198761) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1180452, 3277378, -39198761) (by decide)]
  have h005 : weightedMaskMass a 1183745 (50600853) =
      weightedMaskMass a 5244992 (50600853) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183745, 5244992, 50600853) (by decide)]
  have h006 : weightedMaskMass a 1183748 (21801661) =
      weightedMaskMass a 5242946 (21801661) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183748, 5242946, 21801661) (by decide)]
  have h007 : weightedMaskMass a 1183776 (-11736340) =
      weightedMaskMass a 5243456 (-11736340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183776, 5243456, -11736340) (by decide)]
  have h008 : weightedMaskMass a 1183780 (-12422963) =
      weightedMaskMass a 5243458 (-12422963) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183780, 5243458, -12422963) (by decide)]
  have h009 : weightedMaskMass a 1183808 (-28293344) =
      weightedMaskMass a 1212672 (-28293344) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183808, 1212672, -28293344) (by decide)]
  have h010 : weightedMaskMass a 1183810 (6717448) =
      weightedMaskMass a 1212676 (6717448) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1183810, 1212676, 6717448) (by decide)]
  have h011 : weightedMaskMass a 1184000 (23539081) =
      weightedMaskMass a 5374016 (23539081) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1184000, 5374016, 23539081) (by decide)]
  have h012 : weightedMaskMass a 1184004 (-8480578) =
      weightedMaskMass a 5374018 (-8480578) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1184004, 5374018, -8480578) (by decide)]
  have h013 : weightedMaskMass a 1184032 (-10942881) =
      weightedMaskMass a 5374528 (-10942881) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1184032, 5374528, -10942881) (by decide)]
  have h014 : weightedMaskMass a 1184036 (15373121) =
      weightedMaskMass a 5374530 (15373121) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1184036, 5374530, 15373121) (by decide)]
  have h015 : weightedMaskMass a 1216512 (66646338) =
      weightedMaskMass a 5247040 (66646338) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1216512, 5247040, 66646338) (by decide)]
  have h016 : weightedMaskMass a 1216513 (-78443850) =
      weightedMaskMass a 5249088 (-78443850) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1216513, 5249088, -78443850) (by decide)]
  have h017 : weightedMaskMass a 1216516 (-63779195) =
      weightedMaskMass a 5247042 (-63779195) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1216516, 5247042, -63779195) (by decide)]
  have h018 : weightedMaskMass a 1216768 (-30272319) =
      weightedMaskMass a 5378112 (-30272319) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1216768, 5378112, -30272319) (by decide)]
  have h019 : weightedMaskMass a 1216772 (27619567) =
      weightedMaskMass a 5378114 (27619567) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1216772, 5378114, 27619567) (by decide)]
  have h020 : weightedMaskMass a 1310740 (21901721) =
      weightedMaskMass a 1609728 (21901721) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1310740, 1609728, 21901721) (by decide)]
  have h021 : weightedMaskMass a 1310848 (0) =
      weightedMaskMass a 1314816 (0) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1310848, 1314816, 0) (by decide)]
  have h022 : weightedMaskMass a 1310852 (18631764) =
      weightedMaskMass a 1312896 (18631764) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1310852, 1312896, 18631764) (by decide)]
  have h023 : weightedMaskMass a 1310884 (25525729) =
      weightedMaskMass a 1312928 (25525729) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1310884, 1312928, 25525729) (by decide)]
  have h024 : weightedMaskMass a 1311268 (-4328096) =
      weightedMaskMass a 1589377 (-4328096) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1311268, 1589377, -4328096) (by decide)]
  have h025 : weightedMaskMass a 1311272 (11919480) =
      weightedMaskMass a 1589380 (11919480) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1311272, 1589380, 11919480) (by decide)]
  have h026 : weightedMaskMass a 1312776 (-39952689) =
      weightedMaskMass a 5244936 (-39952689) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1312776, 5244936, -39952689) (by decide)]
  have h027 : weightedMaskMass a 1312788 (-29196340) =
      weightedMaskMass a 1611776 (-29196340) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1312788, 1611776, -29196340) (by decide)]
  have h028 : weightedMaskMass a 1312808 (-62735147) =
      weightedMaskMass a 5277704 (-62735147) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1312808, 5277704, -62735147) (by decide)]
  have h029 : weightedMaskMass a 1314820 (-7850155) =
      weightedMaskMass a 1347584 (-7850155) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1314820, 1347584, -7850155) (by decide)]
  have h030 : weightedMaskMass a 1316868 (44572367) =
      weightedMaskMass a 1349632 (44572367) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1316868, 1349632, 44572367) (by decide)]
  have h031 : weightedMaskMass a 1318912 (28565819) =
      weightedMaskMass a 2138112 (28565819) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1318912, 2138112, 28565819) (by decide)]
  have h032 : weightedMaskMass a 1318913 (-19517167) =
      weightedMaskMass a 2138114 (-19517167) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1318913, 2138114, -19517167) (by decide)]
  have h033 : weightedMaskMass a 1318928 (-25903622) =
      weightedMaskMass a 2138116 (-25903622) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1318928, 2138116, -25903622) (by decide)]
  have h034 : weightedMaskMass a 1318944 (-13385218) =
      weightedMaskMass a 2138120 (-13385218) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1318944, 2138120, -13385218) (by decide)]
  have h035 : weightedMaskMass a 1319168 (-19399459) =
      weightedMaskMass a 2662400 (-19399459) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1319168, 2662400, -19399459) (by decide)]
  have h036 : weightedMaskMass a 1319184 (254608) =
      weightedMaskMass a 2662404 (254608) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1319184, 2662404, 254608) (by decide)]
  have h037 : weightedMaskMass a 1319200 (29458696) =
      weightedMaskMass a 2662408 (29458696) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1319200, 2662408, 29458696) (by decide)]
  have h038 : weightedMaskMass a 1327360 (240338685) =
      weightedMaskMass a 1613824 (240338685) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1327360, 1613824, 240338685) (by decide)]
  have h039 : weightedMaskMass a 1327376 (-213702314) =
      weightedMaskMass a 1613828 (-213702314) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1327376, 1613828, -213702314) (by decide)]
  have h040 : weightedMaskMass a 1327392 (-196781006) =
      weightedMaskMass a 1613832 (-196781006) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1327392, 1613832, -196781006) (by decide)]
  have h041 : weightedMaskMass a 1335296 (-22426791) =
      weightedMaskMass a 3186688 (-22426791) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335296, 3186688, -22426791) (by decide)]
  have h042 : weightedMaskMass a 1335297 (83781935) =
      weightedMaskMass a 3186690 (83781935) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335297, 3186690, 83781935) (by decide)]
  have h043 : weightedMaskMass a 1335312 (52374056) =
      weightedMaskMass a 3186692 (52374056) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335312, 3186692, 52374056) (by decide)]
  have h044 : weightedMaskMass a 1335328 (33776717) =
      weightedMaskMass a 3186696 (33776717) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335328, 3186696, 33776717) (by decide)]
  have h045 : weightedMaskMass a 1335552 (-22752166) =
      weightedMaskMass a 3710976 (-22752166) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335552, 3710976, -22752166) (by decide)]
  have h046 : weightedMaskMass a 1335568 (44253150) =
      weightedMaskMass a 3710980 (44253150) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335568, 3710980, 44253150) (by decide)]
  have h047 : weightedMaskMass a 1335584 (2906526) =
      weightedMaskMass a 3710984 (2906526) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1335584, 3710984, 2906526) (by decide)]
  have h048 : weightedMaskMass a 1343496 (-30952239) =
      weightedMaskMass a 5242920 (-30952239) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1343496, 5242920, -30952239) (by decide)]
  have h049 : weightedMaskMass a 1343504 (33330650) =
      weightedMaskMass a 1576964 (33330650) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1343504, 1576964, 33330650) (by decide)]
  have h050 : weightedMaskMass a 1343508 (-20440694) =
      weightedMaskMass a 1609732 (-20440694) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1343508, 1609732, -20440694) (by decide)]
  have h051 : weightedMaskMass a 1345544 (120418658) =
      weightedMaskMass a 5244968 (120418658) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1345544, 5244968, 120418658) (by decide)]
  have h052 : weightedMaskMass a 1345552 (-30038422) =
      weightedMaskMass a 1579012 (-30038422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1345552, 1579012, -30038422) (by decide)]
  have h053 : weightedMaskMass a 1345556 (55260402) =
      weightedMaskMass a 1611780 (55260402) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1345556, 1611780, 55260402) (by decide)]
  have h054 : weightedMaskMass a 1572884 (7443141) =
      weightedMaskMass a 1605648 (7443141) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1572884, 1605648, 7443141) (by decide)]
  have h055 : weightedMaskMass a 1572888 (12131394) =
      weightedMaskMass a 3670032 (12131394) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1572888, 3670032, 12131394) (by decide)]
  have h056 : weightedMaskMass a 1573128 (270602205) =
      weightedMaskMass a 2121760 (270602205) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573128, 2121760, 270602205) (by decide)]
  have h057 : weightedMaskMass a 1573136 (13815631) =
      weightedMaskMass a 5767184 (13815631) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573136, 5767184, 13815631) (by decide)]
  have h058 : weightedMaskMass a 1573152 (104472915) =
      weightedMaskMass a 3153952 (104472915) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573152, 3153952, 104472915) (by decide)]
  have h059 : weightedMaskMass a 1573156 (-186621933) =
      weightedMaskMass a 3154464 (-186621933) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573156, 3154464, -186621933) (by decide)]
  have h060 : weightedMaskMass a 1573160 (-87283336) =
      weightedMaskMass a 3170336 (-87283336) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573160, 3170336, -87283336) (by decide)]
  have h061 : weightedMaskMass a 1573636 (-175073804) =
      weightedMaskMass a 2105892 (-175073804) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573636, 2105892, -175073804) (by decide)]
  have h062 : weightedMaskMass a 1573640 (-201236435) =
      weightedMaskMass a 2121764 (-201236435) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573640, 2121764, -201236435) (by decide)]
  have h063 : weightedMaskMass a 1573664 (-159771601) =
      weightedMaskMass a 3153956 (-159771601) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573664, 3153956, -159771601) (by decide)]
  have h064 : weightedMaskMass a 1573668 (289813940) =
      weightedMaskMass a 3154468 (289813940) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573668, 3154468, 289813940) (by decide)]
  have h065 : weightedMaskMass a 1573672 (79531703) =
      weightedMaskMass a 3170340 (79531703) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1573672, 3170340, 79531703) (by decide)]
  have h066 : weightedMaskMass a 1574932 (-38140977) =
      weightedMaskMass a 1607696 (-38140977) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1574932, 1607696, -38140977) (by decide)]
  have h067 : weightedMaskMass a 1575172 (42595847) =
      weightedMaskMass a 2105890 (42595847) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1575172, 2105890, 42595847) (by decide)]
  have h068 : weightedMaskMass a 1575176 (-42606420) =
      weightedMaskMass a 2121762 (-42606420) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1575176, 2121762, -42606420) (by decide)]
  have h069 : weightedMaskMass a 1575200 (63124945) =
      weightedMaskMass a 3153954 (63124945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1575200, 3153954, 63124945) (by decide)]
  have h070 : weightedMaskMass a 1575204 (98398450) =
      weightedMaskMass a 3154466 (98398450) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1575204, 3154466, 98398450) (by decide)]
  have h071 : weightedMaskMass a 1575208 (-135405831) =
      weightedMaskMass a 3170338 (-135405831) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1575208, 3170338, -135405831) (by decide)]
  have h072 : weightedMaskMass a 1576961 (-33502192) =
      weightedMaskMass a 2260996 (-33502192) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1576961, 2260996, -33502192) (by decide)]
  have h073 : weightedMaskMass a 1576968 (-87625142) =
      weightedMaskMass a 3670144 (-87625142) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1576968, 3670144, -87625142) (by decide)]
  have h074 : weightedMaskMass a 1577216 (4723518) =
      weightedMaskMass a 4358148 (4723518) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1577216, 4358148, 4723518) (by decide)]
  have h075 : weightedMaskMass a 1581092 (-92639459) =
      weightedMaskMass a 1581600 (-92639459) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581092, 1581600, -92639459) (by decide)]
  have h076 : weightedMaskMass a 1581096 (13415619) =
      weightedMaskMass a 1597472 (13415619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581096, 1597472, 13415619) (by decide)]
  have h077 : weightedMaskMass a 1581312 (194849800) =
      weightedMaskMass a 2629664 (194849800) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581312, 2629664, 194849800) (by decide)]
  have h078 : weightedMaskMass a 1581316 (-121522078) =
      weightedMaskMass a 2630176 (-121522078) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581316, 2630176, -121522078) (by decide)]
  have h079 : weightedMaskMass a 1581320 (-196584522) =
      weightedMaskMass a 2646048 (-196584522) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581320, 2646048, -196584522) (by decide)]
  have h080 : weightedMaskMass a 1581344 (-274185038) =
      weightedMaskMass a 3678240 (-274185038) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581344, 3678240, -274185038) (by decide)]
  have h081 : weightedMaskMass a 1581348 (592177530) =
      weightedMaskMass a 3678752 (592177530) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581348, 3678752, 592177530) (by decide)]
  have h082 : weightedMaskMass a 1581352 (163285760) =
      weightedMaskMass a 3694624 (163285760) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581352, 3694624, 163285760) (by decide)]
  have h083 : weightedMaskMass a 1581608 (-183227571) =
      weightedMaskMass a 1597476 (-183227571) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581608, 1597476, -183227571) (by decide)]
  have h084 : weightedMaskMass a 1581824 (-146899229) =
      weightedMaskMass a 2629668 (-146899229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581824, 2629668, -146899229) (by decide)]
  have h085 : weightedMaskMass a 1581828 (44910821) =
      weightedMaskMass a 2630180 (44910821) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581828, 2630180, 44910821) (by decide)]
  have h086 : weightedMaskMass a 1581832 (45698360) =
      weightedMaskMass a 2646052 (45698360) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581832, 2646052, 45698360) (by decide)]
  have h087 : weightedMaskMass a 1581856 (237810731) =
      weightedMaskMass a 3678244 (237810731) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581856, 3678244, 237810731) (by decide)]
  have h088 : weightedMaskMass a 1581860 (-473409367) =
      weightedMaskMass a 3678756 (-473409367) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581860, 3678756, -473409367) (by decide)]
  have h089 : weightedMaskMass a 1581864 (0) =
      weightedMaskMass a 3694628 (0) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1581864, 3694628, 0) (by decide)]
  have h090 : weightedMaskMass a 1589504 (14080709) =
      weightedMaskMass a 2105384 (14080709) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589504, 2105384, 14080709) (by decide)]
  have h091 : weightedMaskMass a 1589508 (29244388) =
      weightedMaskMass a 2105896 (29244388) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589508, 2105896, 29244388) (by decide)]
  have h092 : weightedMaskMass a 1589512 (-27820592) =
      weightedMaskMass a 2121768 (-27820592) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589512, 2121768, -27820592) (by decide)]
  have h093 : weightedMaskMass a 1589536 (-339002536) =
      weightedMaskMass a 3153960 (-339002536) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589536, 3153960, -339002536) (by decide)]
  have h094 : weightedMaskMass a 1589540 (241284083) =
      weightedMaskMass a 3154472 (241284083) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589540, 3154472, 241284083) (by decide)]
  have h095 : weightedMaskMass a 1589544 (298939962) =
      weightedMaskMass a 3170344 (298939962) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1589544, 3170344, 298939962) (by decide)]
  have h096 : weightedMaskMass a 1597696 (-36606053) =
      weightedMaskMass a 2629672 (-36606053) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597696, 2629672, -36606053) (by decide)]
  have h097 : weightedMaskMass a 1597700 (136028113) =
      weightedMaskMass a 2630184 (136028113) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597700, 2630184, 136028113) (by decide)]
  have h098 : weightedMaskMass a 1597704 (2885197) =
      weightedMaskMass a 2646056 (2885197) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597704, 2646056, 2885197) (by decide)]
  have h099 : weightedMaskMass a 1597728 (446043324) =
      weightedMaskMass a 3678248 (446043324) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1597728, 3678248, 446043324) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt20 s.val : ℝ)) = (((((((weightedMaskMass a 1180196 (-30575976) + (-weightedMaskMass a 3146306 (-30575976) + weightedMaskMass a 1180416 (10592380))) + (-weightedMaskMass a 3276864 (10592380) + (weightedMaskMass a 1180420 (-10592380) + -weightedMaskMass a 3276866 (-10592380)))) + ((weightedMaskMass a 1180448 (148013) + (-weightedMaskMass a 3277376 (148013) + weightedMaskMass a 1180452 (-39198761))) + (-weightedMaskMass a 3277378 (-39198761) + (weightedMaskMass a 1183745 (50600853) + -weightedMaskMass a 5244992 (50600853))))) + (((weightedMaskMass a 1183748 (21801661) + (-weightedMaskMass a 5242946 (21801661) + weightedMaskMass a 1183776 (-11736340))) + (-weightedMaskMass a 5243456 (-11736340) + (weightedMaskMass a 1183780 (-12422963) + -weightedMaskMass a 5243458 (-12422963)))) + ((weightedMaskMass a 1183808 (-28293344) + (-weightedMaskMass a 1212672 (-28293344) + weightedMaskMass a 1183810 (6717448))) + ((-weightedMaskMass a 1212676 (6717448) + weightedMaskMass a 1184000 (23539081)) + (-weightedMaskMass a 5374016 (23539081) + weightedMaskMass a 1184004 (-8480578)))))) + ((((-weightedMaskMass a 5374018 (-8480578) + (weightedMaskMass a 1184032 (-10942881) + -weightedMaskMass a 5374528 (-10942881))) + (weightedMaskMass a 1184036 (15373121) + (-weightedMaskMass a 5374530 (15373121) + weightedMaskMass a 1216512 (66646338)))) + ((-weightedMaskMass a 5247040 (66646338) + (weightedMaskMass a 1216513 (-78443850) + -weightedMaskMass a 5249088 (-78443850))) + (weightedMaskMass a 1216516 (-63779195) + (-weightedMaskMass a 5247042 (-63779195) + weightedMaskMass a 1216768 (-30272319))))) + (((-weightedMaskMass a 5378112 (-30272319) + (weightedMaskMass a 1216772 (27619567) + -weightedMaskMass a 5378114 (27619567))) + (weightedMaskMass a 1310740 (21901721) + (-weightedMaskMass a 1609728 (21901721) + weightedMaskMass a 1310848 (0)))) + ((-weightedMaskMass a 1314816 (0) + (weightedMaskMass a 1310852 (18631764) + -weightedMaskMass a 1312896 (18631764))) + ((weightedMaskMass a 1310884 (25525729) + -weightedMaskMass a 1312928 (25525729)) + (weightedMaskMass a 1311268 (-4328096) + -weightedMaskMass a 1589377 (-4328096))))))) + (((((weightedMaskMass a 1311272 (11919480) + (-weightedMaskMass a 1589380 (11919480) + weightedMaskMass a 1312776 (-39952689))) + (-weightedMaskMass a 5244936 (-39952689) + (weightedMaskMass a 1312788 (-29196340) + -weightedMaskMass a 1611776 (-29196340)))) + ((weightedMaskMass a 1312808 (-62735147) + (-weightedMaskMass a 5277704 (-62735147) + weightedMaskMass a 1314820 (-7850155))) + (-weightedMaskMass a 1347584 (-7850155) + (weightedMaskMass a 1316868 (44572367) + -weightedMaskMass a 1349632 (44572367))))) + (((weightedMaskMass a 1318912 (28565819) + (-weightedMaskMass a 2138112 (28565819) + weightedMaskMass a 1318913 (-19517167))) + (-weightedMaskMass a 2138114 (-19517167) + (weightedMaskMass a 1318928 (-25903622) + -weightedMaskMass a 2138116 (-25903622)))) + ((weightedMaskMass a 1318944 (-13385218) + (-weightedMaskMass a 2138120 (-13385218) + weightedMaskMass a 1319168 (-19399459))) + ((-weightedMaskMass a 2662400 (-19399459) + weightedMaskMass a 1319184 (254608)) + (-weightedMaskMass a 2662404 (254608) + weightedMaskMass a 1319200 (29458696)))))) + ((((-weightedMaskMass a 2662408 (29458696) + (weightedMaskMass a 1327360 (240338685) + -weightedMaskMass a 1613824 (240338685))) + (weightedMaskMass a 1327376 (-213702314) + (-weightedMaskMass a 1613828 (-213702314) + weightedMaskMass a 1327392 (-196781006)))) + ((-weightedMaskMass a 1613832 (-196781006) + (weightedMaskMass a 1335296 (-22426791) + -weightedMaskMass a 3186688 (-22426791))) + (weightedMaskMass a 1335297 (83781935) + (-weightedMaskMass a 3186690 (83781935) + weightedMaskMass a 1335312 (52374056))))) + (((-weightedMaskMass a 3186692 (52374056) + (weightedMaskMass a 1335328 (33776717) + -weightedMaskMass a 3186696 (33776717))) + (weightedMaskMass a 1335552 (-22752166) + (-weightedMaskMass a 3710976 (-22752166) + weightedMaskMass a 1335568 (44253150)))) + ((-weightedMaskMass a 3710980 (44253150) + (weightedMaskMass a 1335584 (2906526) + -weightedMaskMass a 3710984 (2906526))) + ((weightedMaskMass a 1343496 (-30952239) + -weightedMaskMass a 5242920 (-30952239)) + (weightedMaskMass a 1343504 (33330650) + -weightedMaskMass a 1576964 (33330650)))))))) + ((((((weightedMaskMass a 1343508 (-20440694) + (-weightedMaskMass a 1609732 (-20440694) + weightedMaskMass a 1345544 (120418658))) + (-weightedMaskMass a 5244968 (120418658) + (weightedMaskMass a 1345552 (-30038422) + -weightedMaskMass a 1579012 (-30038422)))) + ((weightedMaskMass a 1345556 (55260402) + (-weightedMaskMass a 1611780 (55260402) + weightedMaskMass a 1572884 (7443141))) + (-weightedMaskMass a 1605648 (7443141) + (weightedMaskMass a 1572888 (12131394) + -weightedMaskMass a 3670032 (12131394))))) + (((weightedMaskMass a 1573128 (270602205) + (-weightedMaskMass a 2121760 (270602205) + weightedMaskMass a 1573136 (13815631))) + (-weightedMaskMass a 5767184 (13815631) + (weightedMaskMass a 1573152 (104472915) + -weightedMaskMass a 3153952 (104472915)))) + ((weightedMaskMass a 1573156 (-186621933) + (-weightedMaskMass a 3154464 (-186621933) + weightedMaskMass a 1573160 (-87283336))) + ((-weightedMaskMass a 3170336 (-87283336) + weightedMaskMass a 1573636 (-175073804)) + (-weightedMaskMass a 2105892 (-175073804) + weightedMaskMass a 1573640 (-201236435)))))) + ((((-weightedMaskMass a 2121764 (-201236435) + (weightedMaskMass a 1573664 (-159771601) + -weightedMaskMass a 3153956 (-159771601))) + (weightedMaskMass a 1573668 (289813940) + (-weightedMaskMass a 3154468 (289813940) + weightedMaskMass a 1573672 (79531703)))) + ((-weightedMaskMass a 3170340 (79531703) + (weightedMaskMass a 1574932 (-38140977) + -weightedMaskMass a 1607696 (-38140977))) + (weightedMaskMass a 1575172 (42595847) + (-weightedMaskMass a 2105890 (42595847) + weightedMaskMass a 1575176 (-42606420))))) + (((-weightedMaskMass a 2121762 (-42606420) + (weightedMaskMass a 1575200 (63124945) + -weightedMaskMass a 3153954 (63124945))) + (weightedMaskMass a 1575204 (98398450) + (-weightedMaskMass a 3154466 (98398450) + weightedMaskMass a 1575208 (-135405831)))) + ((-weightedMaskMass a 3170338 (-135405831) + (weightedMaskMass a 1576961 (-33502192) + -weightedMaskMass a 2260996 (-33502192))) + ((weightedMaskMass a 1576968 (-87625142) + -weightedMaskMass a 3670144 (-87625142)) + (weightedMaskMass a 1577216 (4723518) + -weightedMaskMass a 4358148 (4723518))))))) + (((((weightedMaskMass a 1581092 (-92639459) + (-weightedMaskMass a 1581600 (-92639459) + weightedMaskMass a 1581096 (13415619))) + (-weightedMaskMass a 1597472 (13415619) + (weightedMaskMass a 1581312 (194849800) + -weightedMaskMass a 2629664 (194849800)))) + ((weightedMaskMass a 1581316 (-121522078) + (-weightedMaskMass a 2630176 (-121522078) + weightedMaskMass a 1581320 (-196584522))) + (-weightedMaskMass a 2646048 (-196584522) + (weightedMaskMass a 1581344 (-274185038) + -weightedMaskMass a 3678240 (-274185038))))) + (((weightedMaskMass a 1581348 (592177530) + (-weightedMaskMass a 3678752 (592177530) + weightedMaskMass a 1581352 (163285760))) + (-weightedMaskMass a 3694624 (163285760) + (weightedMaskMass a 1581608 (-183227571) + -weightedMaskMass a 1597476 (-183227571)))) + ((weightedMaskMass a 1581824 (-146899229) + (-weightedMaskMass a 2629668 (-146899229) + weightedMaskMass a 1581828 (44910821))) + ((-weightedMaskMass a 2630180 (44910821) + weightedMaskMass a 1581832 (45698360)) + (-weightedMaskMass a 2646052 (45698360) + weightedMaskMass a 1581856 (237810731)))))) + ((((-weightedMaskMass a 3678244 (237810731) + (weightedMaskMass a 1581860 (-473409367) + -weightedMaskMass a 3678756 (-473409367))) + (weightedMaskMass a 1581864 (0) + (-weightedMaskMass a 3694628 (0) + weightedMaskMass a 1589504 (14080709)))) + ((-weightedMaskMass a 2105384 (14080709) + (weightedMaskMass a 1589508 (29244388) + -weightedMaskMass a 2105896 (29244388))) + (weightedMaskMass a 1589512 (-27820592) + (-weightedMaskMass a 2121768 (-27820592) + weightedMaskMass a 1589536 (-339002536))))) + (((-weightedMaskMass a 3153960 (-339002536) + (weightedMaskMass a 1589540 (241284083) + -weightedMaskMass a 3154472 (241284083))) + (weightedMaskMass a 1589544 (298939962) + (-weightedMaskMass a 3170344 (298939962) + weightedMaskMass a 1597696 (-36606053)))) + ((-weightedMaskMass a 2629672 (-36606053) + (weightedMaskMass a 1597700 (136028113) + -weightedMaskMass a 2630184 (136028113))) + ((weightedMaskMass a 1597704 (2885197) + -weightedMaskMass a 2646056 (2885197)) + (weightedMaskMass a 1597728 (446043324) + -weightedMaskMass a 3678248 (446043324))))))))) := by
      simp only [atomCongruenceContributionInt20, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
