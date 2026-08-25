/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CertificateCancellationBase

namespace Erdos232

theorem congruenceBlock18_expectation_zero
    (a : AtomIndex → ℝ)
    (hmass : ∀ c ∈ atomCongruenceWeights18, maskMass a c.1 = maskMass a c.2.1) :
    (∑ s, a s * (atomCongruenceContributionInt18 s.val : ℝ)) = 0 := by
  have h000 : weightedMaskMass a 606276 (51622852) =
      weightedMaskMass a 2146328 (51622852) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606276, 2146328, 51622852) (by decide)]
  have h001 : weightedMaskMass a 606464 (210635350) =
      weightedMaskMass a 2105353 (210635350) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606464, 2105353, 210635350) (by decide)]
  have h002 : weightedMaskMass a 606468 (-84188822) =
      weightedMaskMass a 2105865 (-84188822) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606468, 2105865, -84188822) (by decide)]
  have h003 : weightedMaskMass a 606472 (-161018958) =
      weightedMaskMass a 2121737 (-161018958) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606472, 2121737, -161018958) (by decide)]
  have h004 : weightedMaskMass a 606496 (-398781337) =
      weightedMaskMass a 3153929 (-398781337) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606496, 3153929, -398781337) (by decide)]
  have h005 : weightedMaskMass a 606500 (260335992) =
      weightedMaskMass a 3154441 (260335992) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606500, 3154441, 260335992) (by decide)]
  have h006 : weightedMaskMass a 606504 (346308501) =
      weightedMaskMass a 3170313 (346308501) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (606504, 3170313, 346308501) (by decide)]
  have h007 : weightedMaskMass a 607232 (64394214) =
      weightedMaskMass a 2408448 (64394214) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607232, 2408448, 64394214) (by decide)]
  have h008 : weightedMaskMass a 607233 (-81663157) =
      weightedMaskMass a 2408449 (-81663157) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607233, 2408449, -81663157) (by decide)]
  have h009 : weightedMaskMass a 607236 (102039482) =
      weightedMaskMass a 2408464 (102039482) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607236, 2408464, 102039482) (by decide)]
  have h010 : weightedMaskMass a 607248 (-229298011) =
      weightedMaskMass a 2408452 (-229298011) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607248, 2408452, -229298011) (by decide)]
  have h011 : weightedMaskMass a 607252 (-54328949) =
      weightedMaskMass a 2408468 (-54328949) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607252, 2408468, -54328949) (by decide)]
  have h012 : weightedMaskMass a 607296 (-183264630) =
      weightedMaskMass a 2408456 (-183264630) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607296, 2408456, -183264630) (by decide)]
  have h013 : weightedMaskMass a 607297 (273256547) =
      weightedMaskMass a 2408457 (273256547) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607297, 2408457, 273256547) (by decide)]
  have h014 : weightedMaskMass a 607300 (104254742) =
      weightedMaskMass a 2408472 (104254742) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (607300, 2408472, 104254742) (by decide)]
  have h015 : weightedMaskMass a 614432 (-138208139) =
      weightedMaskMass a 1581065 (-138208139) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614432, 1581065, -138208139) (by decide)]
  have h016 : weightedMaskMass a 614436 (307558809) =
      weightedMaskMass a 1581577 (307558809) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614436, 1581577, 307558809) (by decide)]
  have h017 : weightedMaskMass a 614440 (5534556) =
      weightedMaskMass a 1597449 (5534556) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614440, 1597449, 5534556) (by decide)]
  have h018 : weightedMaskMass a 614656 (-146211714) =
      weightedMaskMass a 2629641 (-146211714) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614656, 2629641, -146211714) (by decide)]
  have h019 : weightedMaskMass a 614660 (213598490) =
      weightedMaskMass a 2630153 (213598490) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614660, 2630153, 213598490) (by decide)]
  have h020 : weightedMaskMass a 614664 (117638519) =
      weightedMaskMass a 2646025 (117638519) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614664, 2646025, 117638519) (by decide)]
  have h021 : weightedMaskMass a 614688 (326213125) =
      weightedMaskMass a 3678217 (326213125) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614688, 3678217, 326213125) (by decide)]
  have h022 : weightedMaskMass a 614692 (-389786728) =
      weightedMaskMass a 3678729 (-389786728) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614692, 3678729, -389786728) (by decide)]
  have h023 : weightedMaskMass a 614696 (-278457306) =
      weightedMaskMass a 3694601 (-278457306) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (614696, 3694601, -278457306) (by decide)]
  have h024 : weightedMaskMass a 622593 (34595748) =
      weightedMaskMass a 2654209 (34595748) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622593, 2654209, 34595748) (by decide)]
  have h025 : weightedMaskMass a 622601 (-104246922) =
      weightedMaskMass a 2654273 (-104246922) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622601, 2654273, -104246922) (by decide)]
  have h026 : weightedMaskMass a 622612 (115886947) =
      weightedMaskMass a 2654228 (115886947) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622612, 2654228, 115886947) (by decide)]
  have h027 : weightedMaskMass a 622616 (31600475) =
      weightedMaskMass a 2654276 (31600475) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622616, 2654276, 31600475) (by decide)]
  have h028 : weightedMaskMass a 622656 (-264692710) =
      weightedMaskMass a 1057056 (-264692710) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622656, 1057056, -264692710) (by decide)]
  have h029 : weightedMaskMass a 622656 (-73603874) =
      weightedMaskMass a 2654216 (-73603874) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622656, 2654216, -73603874) (by decide)]
  have h030 : weightedMaskMass a 622656 (237964941) =
      weightedMaskMass a 3670048 (237964941) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622656, 3670048, 237964941) (by decide)]
  have h031 : weightedMaskMass a 622657 (70477171) =
      weightedMaskMass a 2654217 (70477171) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622657, 2654217, 70477171) (by decide)]
  have h032 : weightedMaskMass a 622660 (-7030092) =
      weightedMaskMass a 2654232 (-7030092) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (622660, 2654232, -7030092) (by decide)]
  have h033 : weightedMaskMass a 626752 (308688945) =
      weightedMaskMass a 1057568 (308688945) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (626752, 1057568, 308688945) (by decide)]
  have h034 : weightedMaskMass a 626752 (-237144167) =
      weightedMaskMass a 3670052 (-237144167) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (626752, 3670052, -237144167) (by decide)]
  have h035 : weightedMaskMass a 630784 (-9792365) =
      weightedMaskMass a 1313024 (-9792365) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (630784, 1313024, -9792365) (by decide)]
  have h036 : weightedMaskMass a 630788 (-51558953) =
      weightedMaskMass a 1313040 (-51558953) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (630788, 1313040, -51558953) (by decide)]
  have h037 : weightedMaskMass a 630792 (-94576671) =
      weightedMaskMass a 1313056 (-94576671) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (630792, 1313056, -94576671) (by decide)]
  have h038 : weightedMaskMass a 638977 (-7049297) =
      weightedMaskMass a 2670593 (-7049297) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638977, 2670593, -7049297) (by decide)]
  have h039 : weightedMaskMass a 638980 (104033100) =
      weightedMaskMass a 2670608 (104033100) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638980, 2670608, 104033100) (by decide)]
  have h040 : weightedMaskMass a 638984 (55758547) =
      weightedMaskMass a 2670656 (55758547) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638984, 2670656, 55758547) (by decide)]
  have h041 : weightedMaskMass a 638985 (19666290) =
      weightedMaskMass a 2670657 (19666290) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638985, 2670657, 19666290) (by decide)]
  have h042 : weightedMaskMass a 638992 (-370784702) =
      weightedMaskMass a 2670596 (-370784702) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638992, 2670596, -370784702) (by decide)]
  have h043 : weightedMaskMass a 638996 (274193813) =
      weightedMaskMass a 2670612 (274193813) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (638996, 2670612, 274193813) (by decide)]
  have h044 : weightedMaskMass a 639000 (359628666) =
      weightedMaskMass a 2670660 (359628666) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (639000, 2670660, 359628666) (by decide)]
  have h045 : weightedMaskMass a 639040 (112761800) =
      weightedMaskMass a 2670600 (112761800) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (639040, 2670600, 112761800) (by decide)]
  have h046 : weightedMaskMass a 639041 (-95103870) =
      weightedMaskMass a 2670601 (-95103870) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (639041, 2670601, -95103870) (by decide)]
  have h047 : weightedMaskMass a 639044 (-178467979) =
      weightedMaskMass a 2670616 (-178467979) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (639044, 2670616, -178467979) (by decide)]
  have h048 : weightedMaskMass a 655368 (-5291424) =
      weightedMaskMass a 2130048 (-5291424) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655368, 2130048, -5291424) (by decide)]
  have h049 : weightedMaskMass a 655392 (3693497) =
      weightedMaskMass a 2097282 (3693497) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655392, 2097282, 3693497) (by decide)]
  have h050 : weightedMaskMass a 655424 (22110063) =
      weightedMaskMass a 671744 (22110063) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655424, 671744, 22110063) (by decide)]
  have h051 : weightedMaskMass a 655424 (34953633) =
      weightedMaskMass a 2097312 (34953633) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655424, 2097312, 34953633) (by decide)]
  have h052 : weightedMaskMass a 655425 (34919024) =
      weightedMaskMass a 2768896 (34919024) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655425, 2768896, 34919024) (by decide)]
  have h053 : weightedMaskMass a 655428 (-2505242) =
      weightedMaskMass a 675840 (-2505242) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655428, 675840, -2505242) (by decide)]
  have h054 : weightedMaskMass a 655880 (-7147701) =
      weightedMaskMass a 3178624 (-7147701) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655880, 3178624, -7147701) (by decide)]
  have h055 : weightedMaskMass a 655904 (-3693497) =
      weightedMaskMass a 2097346 (-3693497) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655904, 2097346, -3693497) (by decide)]
  have h056 : weightedMaskMass a 655936 (-69502820) =
      weightedMaskMass a 3145888 (-69502820) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (655936, 3145888, -69502820) (by decide)]
  have h057 : weightedMaskMass a 659520 (-69317521) =
      weightedMaskMass a 671748 (-69317521) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (659520, 671748, -69317521) (by decide)]
  have h058 : weightedMaskMass a 659521 (39202060) =
      weightedMaskMass a 2768900 (39202060) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (659521, 2768900, 39202060) (by decide)]
  have h059 : weightedMaskMass a 659524 (41372229) =
      weightedMaskMass a 675844 (41372229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (659524, 675844, 41372229) (by decide)]
  have h060 : weightedMaskMass a 671776 (-6200911) =
      weightedMaskMass a 2097314 (-6200911) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (671776, 2097314, -6200911) (by decide)]
  have h061 : weightedMaskMass a 671809 (11144932) =
      weightedMaskMass a 2768960 (11144932) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (671809, 2768960, 11144932) (by decide)]
  have h062 : weightedMaskMass a 671812 (-12573271) =
      weightedMaskMass a 675904 (-12573271) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (671812, 675904, -12573271) (by decide)]
  have h063 : weightedMaskMass a 675841 (140817089) =
      weightedMaskMass a 2752580 (140817089) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (675841, 2752580, 140817089) (by decide)]
  have h064 : weightedMaskMass a 675905 (-105495515) =
      weightedMaskMass a 2768964 (-105495515) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (675905, 2768964, -105495515) (by decide)]
  have h065 : weightedMaskMass a 688128 (-32593761) =
      weightedMaskMass a 2359424 (-32593761) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (688128, 2359424, -32593761) (by decide)]
  have h066 : weightedMaskMass a 688129 (-18102048) =
      weightedMaskMass a 2359428 (-18102048) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (688129, 2359428, -18102048) (by decide)]
  have h067 : weightedMaskMass a 704512 (3473184) =
      weightedMaskMass a 2359456 (3473184) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (704512, 2359456, 3473184) (by decide)]
  have h068 : weightedMaskMass a 704513 (99238153) =
      weightedMaskMass a 2359460 (99238153) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (704513, 2359460, 99238153) (by decide)]
  have h069 : weightedMaskMass a 1049124 (23286560) =
      weightedMaskMass a 1065089 (23286560) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049124, 1065089, 23286560) (by decide)]
  have h070 : weightedMaskMass a 1049124 (-142272024) =
      weightedMaskMass a 2097730 (-142272024) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049124, 2097730, -142272024) (by decide)]
  have h071 : weightedMaskMass a 1049128 (-115609592) =
      weightedMaskMass a 1064996 (-115609592) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049128, 1064996, -115609592) (by decide)]
  have h072 : weightedMaskMass a 1049128 (17443697) =
      weightedMaskMass a 1065092 (17443697) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049128, 1065092, 17443697) (by decide)]
  have h073 : weightedMaskMass a 1049152 (65663887) =
      weightedMaskMass a 1179680 (65663887) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049152, 1179680, 65663887) (by decide)]
  have h074 : weightedMaskMass a 1049152 (-30388868) =
      weightedMaskMass a 1179776 (-30388868) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049152, 1179776, -30388868) (by decide)]
  have h075 : weightedMaskMass a 1049154 (17856787) =
      weightedMaskMass a 1179684 (17856787) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049154, 1179684, 17856787) (by decide)]
  have h076 : weightedMaskMass a 1049154 (-45434738) =
      weightedMaskMass a 1179778 (-45434738) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049154, 1179778, -45434738) (by decide)]
  have h077 : weightedMaskMass a 1049378 (-28784338) =
      weightedMaskMass a 3147812 (-28784338) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049378, 3147812, -28784338) (by decide)]
  have h078 : weightedMaskMass a 1049380 (88417229) =
      weightedMaskMass a 1097857 (88417229) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049380, 1097857, 88417229) (by decide)]
  have h079 : weightedMaskMass a 1049380 (-22624917) =
      weightedMaskMass a 2228802 (-22624917) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049380, 2228802, -22624917) (by decide)]
  have h080 : weightedMaskMass a 1049380 (121004465) =
      weightedMaskMass a 3146276 (121004465) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049380, 3146276, 121004465) (by decide)]
  have h081 : weightedMaskMass a 1049384 (156494843) =
      weightedMaskMass a 3162148 (156494843) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1049384, 3162148, 156494843) (by decide)]
  have h082 : weightedMaskMass a 1050644 (-52738706) =
      weightedMaskMass a 1065218 (-52738706) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050644, 1065218, -52738706) (by decide)]
  have h083 : weightedMaskMass a 1050644 (99979764) =
      weightedMaskMass a 1607680 (99979764) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050644, 1607680, 99979764) (by decide)]
  have h084 : weightedMaskMass a 1050644 (-110178347) =
      weightedMaskMass a 2099240 (-110178347) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050644, 2099240, -110178347) (by decide)]
  have h085 : weightedMaskMass a 1050688 (62076623) =
      weightedMaskMass a 1179649 (62076623) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050688, 1179649, 62076623) (by decide)]
  have h086 : weightedMaskMass a 1050688 (-1409743) =
      weightedMaskMass a 1179656 (-1409743) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050688, 1179656, -1409743) (by decide)]
  have h087 : weightedMaskMass a 1050753 (51864636) =
      weightedMaskMass a 1050884 (51864636) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050753, 1050884, 51864636) (by decide)]
  have h088 : weightedMaskMass a 1050753 (-41131052) =
      weightedMaskMass a 1057028 (-41131052) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050753, 1057028, -41131052) (by decide)]
  have h089 : weightedMaskMass a 1050753 (-137720113) =
      weightedMaskMass a 1097730 (-137720113) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050753, 1097730, -137720113) (by decide)]
  have h090 : weightedMaskMass a 1050753 (33933759) =
      weightedMaskMass a 2097698 (33933759) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050753, 2097698, 33933759) (by decide)]
  have h091 : weightedMaskMass a 1050753 (65275122) =
      weightedMaskMass a 2621984 (65275122) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050753, 2621984, 65275122) (by decide)]
  have h092 : weightedMaskMass a 1050816 (14053954) =
      weightedMaskMass a 1180168 (14053954) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050816, 1180168, 14053954) (by decide)]
  have h093 : weightedMaskMass a 1050900 (109837350) =
      weightedMaskMass a 1097986 (109837350) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050900, 1097986, 109837350) (by decide)]
  have h094 : weightedMaskMass a 1050916 (36192238) =
      weightedMaskMass a 1097858 (36192238) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050916, 1097858, 36192238) (by decide)]
  have h095 : weightedMaskMass a 1050916 (-39403785) =
      weightedMaskMass a 3146274 (-39403785) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050916, 3146274, -39403785) (by decide)]
  have h096 : weightedMaskMass a 1050920 (51436102) =
      weightedMaskMass a 3162146 (51436102) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1050920, 3162146, 51436102) (by decide)]
  have h097 : weightedMaskMass a 1052676 (-46894203) =
      weightedMaskMass a 1343488 (-46894203) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052676, 1343488, -46894203) (by decide)]
  have h098 : weightedMaskMass a 1052676 (-25595005) =
      weightedMaskMass a 4194344 (-25595005) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052676, 4194344, -25595005) (by decide)]
  have h099 : weightedMaskMass a 1052676 (43061435) =
      weightedMaskMass a 4194370 (43061435) := by
    rw [weightedMaskMass_eq, weightedMaskMass_eq, hmass (1052676, 4194370, 43061435) (by decide)]
  calc
    (∑ s, a s * (atomCongruenceContributionInt18 s.val : ℝ)) = (((((((weightedMaskMass a 606276 (51622852) + (-weightedMaskMass a 2146328 (51622852) + weightedMaskMass a 606464 (210635350))) + (-weightedMaskMass a 2105353 (210635350) + (weightedMaskMass a 606468 (-84188822) + -weightedMaskMass a 2105865 (-84188822)))) + ((weightedMaskMass a 606472 (-161018958) + (-weightedMaskMass a 2121737 (-161018958) + weightedMaskMass a 606496 (-398781337))) + (-weightedMaskMass a 3153929 (-398781337) + (weightedMaskMass a 606500 (260335992) + -weightedMaskMass a 3154441 (260335992))))) + (((weightedMaskMass a 606504 (346308501) + (-weightedMaskMass a 3170313 (346308501) + weightedMaskMass a 607232 (64394214))) + (-weightedMaskMass a 2408448 (64394214) + (weightedMaskMass a 607233 (-81663157) + -weightedMaskMass a 2408449 (-81663157)))) + ((weightedMaskMass a 607236 (102039482) + (-weightedMaskMass a 2408464 (102039482) + weightedMaskMass a 607248 (-229298011))) + ((-weightedMaskMass a 2408452 (-229298011) + weightedMaskMass a 607252 (-54328949)) + (-weightedMaskMass a 2408468 (-54328949) + weightedMaskMass a 607296 (-183264630)))))) + ((((-weightedMaskMass a 2408456 (-183264630) + (weightedMaskMass a 607297 (273256547) + -weightedMaskMass a 2408457 (273256547))) + (weightedMaskMass a 607300 (104254742) + (-weightedMaskMass a 2408472 (104254742) + weightedMaskMass a 614432 (-138208139)))) + ((-weightedMaskMass a 1581065 (-138208139) + (weightedMaskMass a 614436 (307558809) + -weightedMaskMass a 1581577 (307558809))) + (weightedMaskMass a 614440 (5534556) + (-weightedMaskMass a 1597449 (5534556) + weightedMaskMass a 614656 (-146211714))))) + (((-weightedMaskMass a 2629641 (-146211714) + (weightedMaskMass a 614660 (213598490) + -weightedMaskMass a 2630153 (213598490))) + (weightedMaskMass a 614664 (117638519) + (-weightedMaskMass a 2646025 (117638519) + weightedMaskMass a 614688 (326213125)))) + ((-weightedMaskMass a 3678217 (326213125) + (weightedMaskMass a 614692 (-389786728) + -weightedMaskMass a 3678729 (-389786728))) + ((weightedMaskMass a 614696 (-278457306) + -weightedMaskMass a 3694601 (-278457306)) + (weightedMaskMass a 622593 (34595748) + -weightedMaskMass a 2654209 (34595748))))))) + (((((weightedMaskMass a 622601 (-104246922) + (-weightedMaskMass a 2654273 (-104246922) + weightedMaskMass a 622612 (115886947))) + (-weightedMaskMass a 2654228 (115886947) + (weightedMaskMass a 622616 (31600475) + -weightedMaskMass a 2654276 (31600475)))) + ((weightedMaskMass a 622656 (-264692710) + (-weightedMaskMass a 1057056 (-264692710) + weightedMaskMass a 622656 (-73603874))) + (-weightedMaskMass a 2654216 (-73603874) + (weightedMaskMass a 622656 (237964941) + -weightedMaskMass a 3670048 (237964941))))) + (((weightedMaskMass a 622657 (70477171) + (-weightedMaskMass a 2654217 (70477171) + weightedMaskMass a 622660 (-7030092))) + (-weightedMaskMass a 2654232 (-7030092) + (weightedMaskMass a 626752 (308688945) + -weightedMaskMass a 1057568 (308688945)))) + ((weightedMaskMass a 626752 (-237144167) + (-weightedMaskMass a 3670052 (-237144167) + weightedMaskMass a 630784 (-9792365))) + ((-weightedMaskMass a 1313024 (-9792365) + weightedMaskMass a 630788 (-51558953)) + (-weightedMaskMass a 1313040 (-51558953) + weightedMaskMass a 630792 (-94576671)))))) + ((((-weightedMaskMass a 1313056 (-94576671) + (weightedMaskMass a 638977 (-7049297) + -weightedMaskMass a 2670593 (-7049297))) + (weightedMaskMass a 638980 (104033100) + (-weightedMaskMass a 2670608 (104033100) + weightedMaskMass a 638984 (55758547)))) + ((-weightedMaskMass a 2670656 (55758547) + (weightedMaskMass a 638985 (19666290) + -weightedMaskMass a 2670657 (19666290))) + (weightedMaskMass a 638992 (-370784702) + (-weightedMaskMass a 2670596 (-370784702) + weightedMaskMass a 638996 (274193813))))) + (((-weightedMaskMass a 2670612 (274193813) + (weightedMaskMass a 639000 (359628666) + -weightedMaskMass a 2670660 (359628666))) + (weightedMaskMass a 639040 (112761800) + (-weightedMaskMass a 2670600 (112761800) + weightedMaskMass a 639041 (-95103870)))) + ((-weightedMaskMass a 2670601 (-95103870) + (weightedMaskMass a 639044 (-178467979) + -weightedMaskMass a 2670616 (-178467979))) + ((weightedMaskMass a 655368 (-5291424) + -weightedMaskMass a 2130048 (-5291424)) + (weightedMaskMass a 655392 (3693497) + -weightedMaskMass a 2097282 (3693497)))))))) + ((((((weightedMaskMass a 655424 (22110063) + (-weightedMaskMass a 671744 (22110063) + weightedMaskMass a 655424 (34953633))) + (-weightedMaskMass a 2097312 (34953633) + (weightedMaskMass a 655425 (34919024) + -weightedMaskMass a 2768896 (34919024)))) + ((weightedMaskMass a 655428 (-2505242) + (-weightedMaskMass a 675840 (-2505242) + weightedMaskMass a 655880 (-7147701))) + (-weightedMaskMass a 3178624 (-7147701) + (weightedMaskMass a 655904 (-3693497) + -weightedMaskMass a 2097346 (-3693497))))) + (((weightedMaskMass a 655936 (-69502820) + (-weightedMaskMass a 3145888 (-69502820) + weightedMaskMass a 659520 (-69317521))) + (-weightedMaskMass a 671748 (-69317521) + (weightedMaskMass a 659521 (39202060) + -weightedMaskMass a 2768900 (39202060)))) + ((weightedMaskMass a 659524 (41372229) + (-weightedMaskMass a 675844 (41372229) + weightedMaskMass a 671776 (-6200911))) + ((-weightedMaskMass a 2097314 (-6200911) + weightedMaskMass a 671809 (11144932)) + (-weightedMaskMass a 2768960 (11144932) + weightedMaskMass a 671812 (-12573271)))))) + ((((-weightedMaskMass a 675904 (-12573271) + (weightedMaskMass a 675841 (140817089) + -weightedMaskMass a 2752580 (140817089))) + (weightedMaskMass a 675905 (-105495515) + (-weightedMaskMass a 2768964 (-105495515) + weightedMaskMass a 688128 (-32593761)))) + ((-weightedMaskMass a 2359424 (-32593761) + (weightedMaskMass a 688129 (-18102048) + -weightedMaskMass a 2359428 (-18102048))) + (weightedMaskMass a 704512 (3473184) + (-weightedMaskMass a 2359456 (3473184) + weightedMaskMass a 704513 (99238153))))) + (((-weightedMaskMass a 2359460 (99238153) + (weightedMaskMass a 1049124 (23286560) + -weightedMaskMass a 1065089 (23286560))) + (weightedMaskMass a 1049124 (-142272024) + (-weightedMaskMass a 2097730 (-142272024) + weightedMaskMass a 1049128 (-115609592)))) + ((-weightedMaskMass a 1064996 (-115609592) + (weightedMaskMass a 1049128 (17443697) + -weightedMaskMass a 1065092 (17443697))) + ((weightedMaskMass a 1049152 (65663887) + -weightedMaskMass a 1179680 (65663887)) + (weightedMaskMass a 1049152 (-30388868) + -weightedMaskMass a 1179776 (-30388868))))))) + (((((weightedMaskMass a 1049154 (17856787) + (-weightedMaskMass a 1179684 (17856787) + weightedMaskMass a 1049154 (-45434738))) + (-weightedMaskMass a 1179778 (-45434738) + (weightedMaskMass a 1049378 (-28784338) + -weightedMaskMass a 3147812 (-28784338)))) + ((weightedMaskMass a 1049380 (88417229) + (-weightedMaskMass a 1097857 (88417229) + weightedMaskMass a 1049380 (-22624917))) + (-weightedMaskMass a 2228802 (-22624917) + (weightedMaskMass a 1049380 (121004465) + -weightedMaskMass a 3146276 (121004465))))) + (((weightedMaskMass a 1049384 (156494843) + (-weightedMaskMass a 3162148 (156494843) + weightedMaskMass a 1050644 (-52738706))) + (-weightedMaskMass a 1065218 (-52738706) + (weightedMaskMass a 1050644 (99979764) + -weightedMaskMass a 1607680 (99979764)))) + ((weightedMaskMass a 1050644 (-110178347) + (-weightedMaskMass a 2099240 (-110178347) + weightedMaskMass a 1050688 (62076623))) + ((-weightedMaskMass a 1179649 (62076623) + weightedMaskMass a 1050688 (-1409743)) + (-weightedMaskMass a 1179656 (-1409743) + weightedMaskMass a 1050753 (51864636)))))) + ((((-weightedMaskMass a 1050884 (51864636) + (weightedMaskMass a 1050753 (-41131052) + -weightedMaskMass a 1057028 (-41131052))) + (weightedMaskMass a 1050753 (-137720113) + (-weightedMaskMass a 1097730 (-137720113) + weightedMaskMass a 1050753 (33933759)))) + ((-weightedMaskMass a 2097698 (33933759) + (weightedMaskMass a 1050753 (65275122) + -weightedMaskMass a 2621984 (65275122))) + (weightedMaskMass a 1050816 (14053954) + (-weightedMaskMass a 1180168 (14053954) + weightedMaskMass a 1050900 (109837350))))) + (((-weightedMaskMass a 1097986 (109837350) + (weightedMaskMass a 1050916 (36192238) + -weightedMaskMass a 1097858 (36192238))) + (weightedMaskMass a 1050916 (-39403785) + (-weightedMaskMass a 3146274 (-39403785) + weightedMaskMass a 1050920 (51436102)))) + ((-weightedMaskMass a 3162146 (51436102) + (weightedMaskMass a 1052676 (-46894203) + -weightedMaskMass a 1343488 (-46894203))) + ((weightedMaskMass a 1052676 (-25595005) + -weightedMaskMass a 4194344 (-25595005)) + (weightedMaskMass a 1052676 (43061435) + -weightedMaskMass a 4194370 (43061435))))))))) := by
      simp only [atomCongruenceContributionInt18, weightedMaskMass, Int.cast_add, Int.cast_neg,
        Int.cast_ite, Int.cast_ofNat, Int.cast_negSucc, mul_add, mul_neg,
        Finset.sum_add_distrib, Finset.sum_neg_distrib]
    _ = 0 := by
      rw [h000, h001, h002, h003, h004, h005, h006, h007, h008, h009, h010, h011, h012, h013, h014, h015, h016, h017, h018, h019, h020, h021, h022, h023, h024, h025, h026, h027, h028, h029, h030, h031, h032, h033, h034, h035, h036, h037, h038, h039, h040, h041, h042, h043, h044, h045, h046, h047, h048, h049, h050, h051, h052, h053, h054, h055, h056, h057, h058, h059, h060, h061, h062, h063, h064, h065, h066, h067, h068, h069, h070, h071, h072, h073, h074, h075, h076, h077, h078, h079, h080, h081, h082, h083, h084, h085, h086, h087, h088, h089, h090, h091, h092, h093, h094, h095, h096, h097, h098, h099]
      ring

end Erdos232
