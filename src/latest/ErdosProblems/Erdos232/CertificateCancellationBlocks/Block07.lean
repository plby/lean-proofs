/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock07_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights07, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt07 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 16516 (27651820) =
      weightedMaskMass a 131201 (27651820) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16516, 131201, 27651820) (by decide)]
  have h001 : weightedMaskMass a 16516 (-14788245) =
      weightedMaskMass a 147458 (-14788245) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16516, 147458, -14788245) (by decide)]
  have h002 : weightedMaskMass a 16516 (-18212198) =
      weightedMaskMass a 1048616 (-18212198) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16516, 1048616, -18212198) (by decide)]
  have h003 : weightedMaskMass a 16516 (94225593) =
      weightedMaskMass a 1064992 (94225593) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16516, 1064992, 94225593) (by decide)]
  have h004 : weightedMaskMass a 16516 (41810229) =
      weightedMaskMass a 1081352 (41810229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16516, 1081352, 41810229) (by decide)]
  have h005 : weightedMaskMass a 16648 (-70877740) =
      weightedMaskMass a 81984 (-70877740) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16648, 81984, -70877740) (by decide)]
  have h006 : weightedMaskMass a 16648 (83378714) =
      weightedMaskMass a 2113544 (83378714) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16648, 2113544, 83378714) (by decide)]
  have h007 : weightedMaskMass a 16664 (53999594) =
      weightedMaskMass a 86080 (53999594) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16664, 86080, 53999594) (by decide)]
  have h008 : weightedMaskMass a 16674 (-48153499) =
      weightedMaskMass a 24610 (-48153499) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16674, 24610, -48153499) (by decide)]
  have h009 : weightedMaskMass a 16674 (48153956) =
      weightedMaskMass a 1574920 (48153956) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16674, 1574920, 48153956) (by decide)]
  have h010 : weightedMaskMass a 16674 (44405444) =
      weightedMaskMass a 3147784 (44405444) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16674, 3147784, 44405444) (by decide)]
  have h011 : weightedMaskMass a 16676 (-81505253) =
      weightedMaskMass a 24836 (-81505253) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16676, 24836, -81505253) (by decide)]
  have h012 : weightedMaskMass a 16676 (-55968462) =
      weightedMaskMass a 1081476 (-55968462) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16676, 1081476, -55968462) (by decide)]
  have h013 : weightedMaskMass a 16676 (108822296) =
      weightedMaskMass a 2621960 (108822296) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16676, 2621960, 108822296) (by decide)]
  have h014 : weightedMaskMass a 16676 (36436919) =
      weightedMaskMass a 3146248 (36436919) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16676, 3146248, 36436919) (by decide)]
  have h015 : weightedMaskMass a 16680 (62354731) =
      weightedMaskMass a 3162120 (62354731) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (16680, 3162120, 62354731) (by decide)]
  have h016 : weightedMaskMass a 17410 (91924163) =
      weightedMaskMass a 49154 (91924163) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 49154, 91924163) (by decide)]
  have h017 : weightedMaskMass a 17410 (5356600) =
      weightedMaskMass a 65570 (5356600) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 65570, 5356600) (by decide)]
  have h018 : weightedMaskMass a 17410 (-40028988) =
      weightedMaskMass a 98306 (-40028988) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 98306, -40028988) (by decide)]
  have h019 : weightedMaskMass a 17410 (-28469745) =
      weightedMaskMass a 278560 (-28469745) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 278560, -28469745) (by decide)]
  have h020 : weightedMaskMass a 17410 (158538032) =
      weightedMaskMass a 540704 (158538032) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 540704, 158538032) (by decide)]
  have h021 : weightedMaskMass a 17410 (-30952758) =
      weightedMaskMass a 622592 (-30952758) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 622592, -30952758) (by decide)]
  have h022 : weightedMaskMass a 17410 (-23879132) =
      weightedMaskMass a 1050625 (-23879132) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 1050625, -23879132) (by decide)]
  have h023 : weightedMaskMass a 17410 (-5183957) =
      weightedMaskMass a 1050880 (-5183957) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 1050880, -5183957) (by decide)]
  have h024 : weightedMaskMass a 17410 (-69056714) =
      weightedMaskMass a 1056776 (-69056714) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 1056776, -69056714) (by decide)]
  have h025 : weightedMaskMass a 17410 (156327064) =
      weightedMaskMass a 1057024 (156327064) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 1057024, 156327064) (by decide)]
  have h026 : weightedMaskMass a 17410 (-72353422) =
      weightedMaskMass a 2097186 (-72353422) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 2097186, -72353422) (by decide)]
  have h027 : weightedMaskMass a 17410 (-51120724) =
      weightedMaskMass a 2621472 (-51120724) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 2621472, -51120724) (by decide)]
  have h028 : weightedMaskMass a 17410 (-110602935) =
      weightedMaskMass a 2654208 (-110602935) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17410, 2654208, -110602935) (by decide)]
  have h029 : weightedMaskMass a 17426 (-118347644) =
      weightedMaskMass a 278564 (-118347644) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17426, 278564, -118347644) (by decide)]
  have h030 : weightedMaskMass a 17426 (73802673) =
      weightedMaskMass a 1083393 (73802673) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17426, 1083393, 73802673) (by decide)]
  have h031 : weightedMaskMass a 17426 (101185018) =
      weightedMaskMass a 2228258 (101185018) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17426, 2228258, 101185018) (by decide)]
  have h032 : weightedMaskMass a 17428 (-268332022) =
      weightedMaskMass a 278548 (-268332022) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17428, 278548, -268332022) (by decide)]
  have h033 : weightedMaskMass a 17428 (59683915) =
      weightedMaskMass a 1049348 (59683915) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17428, 1049348, 59683915) (by decide)]
  have h034 : weightedMaskMass a 17428 (-63788662) =
      weightedMaskMass a 1097729 (-63788662) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17428, 1097729, -63788662) (by decide)]
  have h035 : weightedMaskMass a 17428 (100475648) =
      weightedMaskMass a 2097700 (100475648) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17428, 2097700, 100475648) (by decide)]
  have h036 : weightedMaskMass a 17428 (-9304979) =
      weightedMaskMass a 2228290 (-9304979) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17428, 2228290, -9304979) (by decide)]
  have h037 : weightedMaskMass a 17472 (-35693805) =
      weightedMaskMass a 278536 (-35693805) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17472, 278536, -35693805) (by decide)]
  have h038 : weightedMaskMass a 17473 (56666189) =
      weightedMaskMass a 278537 (56666189) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17473, 278537, 56666189) (by decide)]
  have h039 : weightedMaskMass a 17474 (109522978) =
      weightedMaskMass a 278568 (109522978) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17474, 278568, 109522978) (by decide)]
  have h040 : weightedMaskMass a 17476 (5968427) =
      weightedMaskMass a 278552 (5968427) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (17476, 278552, 5968427) (by decide)]
  have h041 : weightedMaskMass a 20514 (114283216) =
      weightedMaskMass a 1050648 (114283216) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20514, 1050648, 114283216) (by decide)]
  have h042 : weightedMaskMass a 20545 (69312069) =
      weightedMaskMass a 81944 (69312069) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20545, 81944, 69312069) (by decide)]
  have h043 : weightedMaskMass a 20545 (-1713628) =
      weightedMaskMass a 2113604 (-1713628) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20545, 2113604, -1713628) (by decide)]
  have h044 : weightedMaskMass a 20546 (43760191) =
      weightedMaskMass a 1064984 (43760191) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20546, 1064984, 43760191) (by decide)]
  have h045 : weightedMaskMass a 20770 (10786419) =
      weightedMaskMass a 28706 (10786419) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (20770, 28706, 10786419) (by decide)]
  have h046 : weightedMaskMass a 21504 (-81436686) =
      weightedMaskMass a 270337 (-81436686) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21504, 270337, -81436686) (by decide)]
  have h047 : weightedMaskMass a 21504 (56204979) =
      weightedMaskMass a 526592 (56204979) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21504, 526592, 56204979) (by decide)]
  have h048 : weightedMaskMass a 21504 (-105141588) =
      weightedMaskMass a 2105346 (-105141588) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21504, 2105346, -105141588) (by decide)]
  have h049 : weightedMaskMass a 21504 (64009137) =
      weightedMaskMass a 4194820 (64009137) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21504, 4194820, 64009137) (by decide)]
  have h050 : weightedMaskMass a 21505 (58247577) =
      weightedMaskMass a 2105362 (58247577) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21505, 2105362, 58247577) (by decide)]
  have h051 : weightedMaskMass a 21506 (3836682) =
      weightedMaskMass a 1575168 (3836682) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21506, 1575168, 3836682) (by decide)]
  have h052 : weightedMaskMass a 21506 (51601412) =
      weightedMaskMass a 2105378 (51601412) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21506, 2105378, 51601412) (by decide)]
  have h053 : weightedMaskMass a 21508 (-16551826) =
      weightedMaskMass a 2105410 (-16551826) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21508, 2105410, -16551826) (by decide)]
  have h054 : weightedMaskMass a 21508 (31531533) =
      weightedMaskMass a 4194852 (31531533) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (21508, 4194852, 31531533) (by decide)]
  have h055 : weightedMaskMass a 24584 (-64261013) =
      weightedMaskMass a 49216 (-64261013) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24584, 49216, -64261013) (by decide)]
  have h056 : weightedMaskMass a 24584 (95517139) =
      weightedMaskMass a 540680 (95517139) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24584, 540680, 95517139) (by decide)]
  have h057 : weightedMaskMass a 24585 (63702570) =
      weightedMaskMass a 606216 (63702570) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24585, 606216, 63702570) (by decide)]
  have h058 : weightedMaskMass a 24585 (-161623225) =
      weightedMaskMass a 2146368 (-161623225) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24585, 2146368, -161623225) (by decide)]
  have h059 : weightedMaskMass a 24596 (-5190336) =
      weightedMaskMass a 34945 (-5190336) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24596, 34945, -5190336) (by decide)]
  have h060 : weightedMaskMass a 24596 (46323425) =
      weightedMaskMass a 2228768 (46323425) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24596, 2228768, 46323425) (by decide)]
  have h061 : weightedMaskMass a 24600 (33821717) =
      weightedMaskMass a 53312 (33821717) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24600, 53312, 33821717) (by decide)]
  have h062 : weightedMaskMass a 24616 (45966248) =
      weightedMaskMass a 1589256 (45966248) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24616, 1589256, 45966248) (by decide)]
  have h063 : weightedMaskMass a 24840 (83343311) =
      weightedMaskMass a 114752 (83343311) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24840, 114752, 83343311) (by decide)]
  have h064 : weightedMaskMass a 24840 (-63894571) =
      weightedMaskMass a 2637832 (-63894571) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24840, 2637832, -63894571) (by decide)]
  have h065 : weightedMaskMass a 24856 (-14856916) =
      weightedMaskMass a 118848 (-14856916) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24856, 118848, -14856916) (by decide)]
  have h066 : weightedMaskMass a 24864 (116355661) =
      weightedMaskMass a 3670024 (116355661) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24864, 3670024, 116355661) (by decide)]
  have h067 : weightedMaskMass a 24866 (-143602123) =
      weightedMaskMass a 3672072 (-143602123) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24866, 3672072, -143602123) (by decide)]
  have h068 : weightedMaskMass a 24868 (-166873689) =
      weightedMaskMass a 3670536 (-166873689) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24868, 3670536, -166873689) (by decide)]
  have h069 : weightedMaskMass a 24872 (-101276373) =
      weightedMaskMass a 3686408 (-101276373) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (24872, 3686408, -101276373) (by decide)]
  have h070 : weightedMaskMass a 25601 (-23627334) =
      weightedMaskMass a 2132032 (-23627334) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (25601, 2132032, -23627334) (by decide)]
  have h071 : weightedMaskMass a 25602 (-68981452) =
      weightedMaskMass a 98434 (-68981452) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (25602, 98434, -68981452) (by decide)]
  have h072 : weightedMaskMass a 25616 (22003108) =
      weightedMaskMass a 38976 (22003108) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (25616, 38976, 22003108) (by decide)]
  have h073 : weightedMaskMass a 25616 (-5742959) =
      weightedMaskMass a 2228740 (-5742959) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (25616, 2228740, -5742959) (by decide)]
  have h074 : weightedMaskMass a 25620 (41095284) =
      weightedMaskMass a 2228772 (41095284) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (25620, 2228772, 41095284) (by decide)]
  have h075 : weightedMaskMass a 29696 (10234890) =
      weightedMaskMass a 4325892 (10234890) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (29696, 4325892, 10234890) (by decide)]
  have h076 : weightedMaskMass a 290816 (-97199518) =
      weightedMaskMass a 528672 (-97199518) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (290816, 528672, -97199518) (by decide)]
  have h077 : weightedMaskMass a 290817 (62619960) =
      weightedMaskMass a 530720 (62619960) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (290817, 530720, 62619960) (by decide)]
  have h078 : weightedMaskMass a 290848 (109900611) =
      weightedMaskMass a 545056 (109900611) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (290848, 545056, 109900611) (by decide)]
  have h079 : weightedMaskMass a 29700 (47195167) =
      weightedMaskMass a 4325924 (47195167) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (29700, 4325924, 47195167) (by decide)]
  have h080 : weightedMaskMass a 32777 (15834788) =
      weightedMaskMass a 36872 (15834788) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32777, 36872, 15834788) (by decide)]
  have h081 : weightedMaskMass a 32777 (-58061619) =
      weightedMaskMass a 524353 (-58061619) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32777, 524353, -58061619) (by decide)]
  have h082 : weightedMaskMass a 32777 (-27842107) =
      weightedMaskMass a 2228352 (-27842107) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32777, 2228352, -27842107) (by decide)]
  have h083 : weightedMaskMass a 32777 (-31313297) =
      weightedMaskMass a 2244608 (-31313297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32777, 2244608, -31313297) (by decide)]
  have h084 : weightedMaskMass a 32788 (90901070) =
      weightedMaskMass a 49408 (90901070) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 49408, 90901070) (by decide)]
  have h085 : weightedMaskMass a 32788 (23422139) =
      weightedMaskMass a 66624 (23422139) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 66624, 23422139) (by decide)]
  have h086 : weightedMaskMass a 32788 (-47471120) =
      weightedMaskMass a 69634 (-47471120) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 69634, -47471120) (by decide)]
  have h087 : weightedMaskMass a 32788 (76557424) =
      weightedMaskMass a 132160 (76557424) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 132160, 76557424) (by decide)]
  have h088 : weightedMaskMass a 32788 (-62212530) =
      weightedMaskMass a 196672 (-62212530) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 196672, -62212530) (by decide)]
  have h089 : weightedMaskMass a 32788 (-33932950) =
      weightedMaskMass a 197632 (-33932950) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 197632, -33932950) (by decide)]
  have h090 : weightedMaskMass a 32788 (-41308743) =
      weightedMaskMass a 524308 (-41308743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 524308, -41308743) (by decide)]
  have h091 : weightedMaskMass a 32788 (-119294649) =
      weightedMaskMass a 557060 (-119294649) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 557060, -119294649) (by decide)]
  have h092 : weightedMaskMass a 32788 (-105550445) =
      weightedMaskMass a 557072 (-105550445) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 557072, -105550445) (by decide)]
  have h093 : weightedMaskMass a 32788 (87289098) =
      weightedMaskMass a 1048848 (87289098) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 1048848, 87289098) (by decide)]
  have h094 : weightedMaskMass a 32788 (70164236) =
      weightedMaskMass a 2359304 (70164236) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 2359304, 70164236) (by decide)]
  have h095 : weightedMaskMass a 32788 (32163866) =
      weightedMaskMass a 5767168 (32163866) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32788, 5767168, 32163866) (by decide)]
  have h096 : weightedMaskMass a 32833 (89224593) =
      weightedMaskMass a 36992 (89224593) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32833, 36992, 89224593) (by decide)]
  have h097 : weightedMaskMass a 32833 (-52744765) =
      weightedMaskMass a 90112 (-52744765) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32833, 90112, -52744765) (by decide)]
  have h098 : weightedMaskMass a 32833 (1355582) =
      weightedMaskMass a 524297 (1355582) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32833, 524297, 1355582) (by decide)]
  have h099 : weightedMaskMass a 32836 (-20845193) =
      weightedMaskMass a 65728 (-20845193) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (32836, 65728, -20845193) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt07 s.val : ℝ)) = (((((((weightedMaskMass a 16516 (27651820) + (-weightedMaskMass a 131201 (27651820) + weightedMaskMass a 16516 (-14788245))) + (-weightedMaskMass a 147458 (-14788245) + (weightedMaskMass a 16516 (-18212198) + -weightedMaskMass a 1048616 (-18212198)))) + ((weightedMaskMass a 16516 (94225593) + (-weightedMaskMass a 1064992 (94225593) + weightedMaskMass a 16516 (41810229))) + (-weightedMaskMass a 1081352 (41810229) + (weightedMaskMass a 16648 (-70877740) + -weightedMaskMass a 81984 (-70877740))))) + (((weightedMaskMass a 16648 (83378714) + (-weightedMaskMass a 2113544 (83378714) + weightedMaskMass a 16664 (53999594))) + (-weightedMaskMass a 86080 (53999594) + (weightedMaskMass a 16674 (-48153499) + -weightedMaskMass a 24610 (-48153499)))) + ((weightedMaskMass a 16674 (48153956) + (-weightedMaskMass a 1574920 (48153956) + weightedMaskMass a 16674 (44405444))) + ((-weightedMaskMass a 3147784 (44405444) + weightedMaskMass a 16676 (-81505253)) + (-weightedMaskMass a 24836 (-81505253) + weightedMaskMass a 16676 (-55968462)))))) + ((((-weightedMaskMass a 1081476 (-55968462) + (weightedMaskMass a 16676 (108822296) + -weightedMaskMass a 2621960 (108822296))) + (weightedMaskMass a 16676 (36436919) + (-weightedMaskMass a 3146248 (36436919) + weightedMaskMass a 16680 (62354731)))) + ((-weightedMaskMass a 3162120 (62354731) + (weightedMaskMass a 17410 (91924163) + -weightedMaskMass a 49154 (91924163))) + (weightedMaskMass a 17410 (5356600) + (-weightedMaskMass a 65570 (5356600) + weightedMaskMass a 17410 (-40028988))))) + (((-weightedMaskMass a 98306 (-40028988) + (weightedMaskMass a 17410 (-28469745) + -weightedMaskMass a 278560 (-28469745))) + (weightedMaskMass a 17410 (158538032) + (-weightedMaskMass a 540704 (158538032) + weightedMaskMass a 17410 (-30952758)))) + ((-weightedMaskMass a 622592 (-30952758) + (weightedMaskMass a 17410 (-23879132) + -weightedMaskMass a 1050625 (-23879132))) + ((weightedMaskMass a 17410 (-5183957) + -weightedMaskMass a 1050880 (-5183957)) + (weightedMaskMass a 17410 (-69056714) + -weightedMaskMass a 1056776 (-69056714))))))) + (((((weightedMaskMass a 17410 (156327064) + (-weightedMaskMass a 1057024 (156327064) + weightedMaskMass a 17410 (-72353422))) + (-weightedMaskMass a 2097186 (-72353422) + (weightedMaskMass a 17410 (-51120724) + -weightedMaskMass a 2621472 (-51120724)))) + ((weightedMaskMass a 17410 (-110602935) + (-weightedMaskMass a 2654208 (-110602935) + weightedMaskMass a 17426 (-118347644))) + (-weightedMaskMass a 278564 (-118347644) + (weightedMaskMass a 17426 (73802673) + -weightedMaskMass a 1083393 (73802673))))) + (((weightedMaskMass a 17426 (101185018) + (-weightedMaskMass a 2228258 (101185018) + weightedMaskMass a 17428 (-268332022))) + (-weightedMaskMass a 278548 (-268332022) + (weightedMaskMass a 17428 (59683915) + -weightedMaskMass a 1049348 (59683915)))) + ((weightedMaskMass a 17428 (-63788662) + (-weightedMaskMass a 1097729 (-63788662) + weightedMaskMass a 17428 (100475648))) + ((-weightedMaskMass a 2097700 (100475648) + weightedMaskMass a 17428 (-9304979)) + (-weightedMaskMass a 2228290 (-9304979) + weightedMaskMass a 17472 (-35693805)))))) + ((((-weightedMaskMass a 278536 (-35693805) + (weightedMaskMass a 17473 (56666189) + -weightedMaskMass a 278537 (56666189))) + (weightedMaskMass a 17474 (109522978) + (-weightedMaskMass a 278568 (109522978) + weightedMaskMass a 17476 (5968427)))) + ((-weightedMaskMass a 278552 (5968427) + (weightedMaskMass a 20514 (114283216) + -weightedMaskMass a 1050648 (114283216))) + (weightedMaskMass a 20545 (69312069) + (-weightedMaskMass a 81944 (69312069) + weightedMaskMass a 20545 (-1713628))))) + (((-weightedMaskMass a 2113604 (-1713628) + (weightedMaskMass a 20546 (43760191) + -weightedMaskMass a 1064984 (43760191))) + (weightedMaskMass a 20770 (10786419) + (-weightedMaskMass a 28706 (10786419) + weightedMaskMass a 21504 (-81436686)))) + ((-weightedMaskMass a 270337 (-81436686) + (weightedMaskMass a 21504 (56204979) + -weightedMaskMass a 526592 (56204979))) + ((weightedMaskMass a 21504 (-105141588) + -weightedMaskMass a 2105346 (-105141588)) + (weightedMaskMass a 21504 (64009137) + -weightedMaskMass a 4194820 (64009137)))))))) + ((((((weightedMaskMass a 21505 (58247577) + (-weightedMaskMass a 2105362 (58247577) + weightedMaskMass a 21506 (3836682))) + (-weightedMaskMass a 1575168 (3836682) + (weightedMaskMass a 21506 (51601412) + -weightedMaskMass a 2105378 (51601412)))) + ((weightedMaskMass a 21508 (-16551826) + (-weightedMaskMass a 2105410 (-16551826) + weightedMaskMass a 21508 (31531533))) + (-weightedMaskMass a 4194852 (31531533) + (weightedMaskMass a 24584 (-64261013) + -weightedMaskMass a 49216 (-64261013))))) + (((weightedMaskMass a 24584 (95517139) + (-weightedMaskMass a 540680 (95517139) + weightedMaskMass a 24585 (63702570))) + (-weightedMaskMass a 606216 (63702570) + (weightedMaskMass a 24585 (-161623225) + -weightedMaskMass a 2146368 (-161623225)))) + ((weightedMaskMass a 24596 (-5190336) + (-weightedMaskMass a 34945 (-5190336) + weightedMaskMass a 24596 (46323425))) + ((-weightedMaskMass a 2228768 (46323425) + weightedMaskMass a 24600 (33821717)) + (-weightedMaskMass a 53312 (33821717) + weightedMaskMass a 24616 (45966248)))))) + ((((-weightedMaskMass a 1589256 (45966248) + (weightedMaskMass a 24840 (83343311) + -weightedMaskMass a 114752 (83343311))) + (weightedMaskMass a 24840 (-63894571) + (-weightedMaskMass a 2637832 (-63894571) + weightedMaskMass a 24856 (-14856916)))) + ((-weightedMaskMass a 118848 (-14856916) + (weightedMaskMass a 24864 (116355661) + -weightedMaskMass a 3670024 (116355661))) + (weightedMaskMass a 24866 (-143602123) + (-weightedMaskMass a 3672072 (-143602123) + weightedMaskMass a 24868 (-166873689))))) + (((-weightedMaskMass a 3670536 (-166873689) + (weightedMaskMass a 24872 (-101276373) + -weightedMaskMass a 3686408 (-101276373))) + (weightedMaskMass a 25601 (-23627334) + (-weightedMaskMass a 2132032 (-23627334) + weightedMaskMass a 25602 (-68981452)))) + ((-weightedMaskMass a 98434 (-68981452) + (weightedMaskMass a 25616 (22003108) + -weightedMaskMass a 38976 (22003108))) + ((weightedMaskMass a 25616 (-5742959) + -weightedMaskMass a 2228740 (-5742959)) + (weightedMaskMass a 25620 (41095284) + -weightedMaskMass a 2228772 (41095284))))))) + (((((weightedMaskMass a 29696 (10234890) + (-weightedMaskMass a 4325892 (10234890) + weightedMaskMass a 290816 (-97199518))) + (-weightedMaskMass a 528672 (-97199518) + (weightedMaskMass a 290817 (62619960) + -weightedMaskMass a 530720 (62619960)))) + ((weightedMaskMass a 290848 (109900611) + (-weightedMaskMass a 545056 (109900611) + weightedMaskMass a 29700 (47195167))) + (-weightedMaskMass a 4325924 (47195167) + (weightedMaskMass a 32777 (15834788) + -weightedMaskMass a 36872 (15834788))))) + (((weightedMaskMass a 32777 (-58061619) + (-weightedMaskMass a 524353 (-58061619) + weightedMaskMass a 32777 (-27842107))) + (-weightedMaskMass a 2228352 (-27842107) + (weightedMaskMass a 32777 (-31313297) + -weightedMaskMass a 2244608 (-31313297)))) + ((weightedMaskMass a 32788 (90901070) + (-weightedMaskMass a 49408 (90901070) + weightedMaskMass a 32788 (23422139))) + ((-weightedMaskMass a 66624 (23422139) + weightedMaskMass a 32788 (-47471120)) + (-weightedMaskMass a 69634 (-47471120) + weightedMaskMass a 32788 (76557424)))))) + ((((-weightedMaskMass a 132160 (76557424) + (weightedMaskMass a 32788 (-62212530) + -weightedMaskMass a 196672 (-62212530))) + (weightedMaskMass a 32788 (-33932950) + (-weightedMaskMass a 197632 (-33932950) + weightedMaskMass a 32788 (-41308743)))) + ((-weightedMaskMass a 524308 (-41308743) + (weightedMaskMass a 32788 (-119294649) + -weightedMaskMass a 557060 (-119294649))) + (weightedMaskMass a 32788 (-105550445) + (-weightedMaskMass a 557072 (-105550445) + weightedMaskMass a 32788 (87289098))))) + (((-weightedMaskMass a 1048848 (87289098) + (weightedMaskMass a 32788 (70164236) + -weightedMaskMass a 2359304 (70164236))) + (weightedMaskMass a 32788 (32163866) + (-weightedMaskMass a 5767168 (32163866) + weightedMaskMass a 32833 (89224593)))) + ((-weightedMaskMass a 36992 (89224593) + (weightedMaskMass a 32833 (-52744765) + -weightedMaskMass a 90112 (-52744765))) + ((weightedMaskMass a 32833 (1355582) + -weightedMaskMass a 524297 (1355582)) + (weightedMaskMass a 32836 (-20845193) + -weightedMaskMass a 65728 (-20845193))))))))) := by
      simp only [atomCongruenceContributionInt07, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
