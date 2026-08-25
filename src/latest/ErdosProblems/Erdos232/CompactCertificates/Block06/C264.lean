/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate264 : CompactCertificate where
  left := 138
  right := 139
  center := 277 / 2
  grid := fun i =>
    match i.val with
    | 0 => 44
    | 1 => 32
    | 2 => 53
    | 3 => 9
    | 4 => 25
    | 5 => 69
    | 6 => 51
    | 7 => 87
    | 8 => 64
    | 9 => 99
    | 10 => 57
    | 11 => 101
    | 12 => 94
    | 13 => 67
    | 14 => 76
    | 15 => 64
    | 16 => 56
    | 17 => 82
    | 18 => 45
    | 19 => 38
    | 20 => 24
    | 21 => 13
    | 22 => 35
    | 23 => 48
    | 24 => 20
    | 25 => 82
    | _ => 55
  point := fun i =>
    match i.val with
    | 0 => 277 / 2
    | 1 => 408073892568577 / 4000000000000
    | 2 => 131962712449441 / 800000000000
    | 3 => 119074944100739 / 4000000000000
    | 4 => 319852049130983 / 4000000000000
    | 5 => 868460533475211 / 4000000000000
    | 6 => 639704098262243 / 4000000000000
    | 7 => 1096143875779439 / 4000000000000
    | 8 => 807414617697101 / 4000000000000
    | 9 => 1238781659534723 / 4000000000000
    | 10 => 715210924599467 / 4000000000000
    | 11 => 1269154336454503 / 4000000000000
    | 12 => 1185808611486307 / 4000000000000
    | 13 => 846248978334931 / 4000000000000
    | 14 => 959556147392949 / 4000000000000
    | 15 => 799977876938981 / 4000000000000
    | 16 => 706804715170601 / 4000000000000
    | 17 => 204859555493499 / 800000000000
    | 18 => 566652311662753 / 4000000000000
    | 19 => 480357440099033 / 4000000000000
    | 20 => 300585382302899 / 4000000000000
    | 21 => 161655818304333 / 4000000000000
    | 22 => 438926993231999 / 4000000000000
    | 23 => 599317284235423 / 4000000000000
    | 24 => 253414617697101 / 4000000000000
    | 25 => 1030116351779821 / 4000000000000
    | _ => 688069983211139 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
    | 1 => (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
    | 2 => (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000))
    | 3 => (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
    | 4 => (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
    | 5 => (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000))
    | 6 => (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
    | 7 => (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
    | 8 => (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000))
    | 9 => (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
    | 10 => (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
    | 11 => (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000))
    | 12 => (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
    | 13 => (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
    | 14 => (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))
    | 15 => (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
    | 16 => (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
    | 17 => (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000))
    | 18 => (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
    | 19 => (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
    | 20 => (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000))
    | 21 => (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
    | 22 => (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
    | 23 => (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000))
    | 24 => (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
    | 25 => (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
    | _ => (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (26459570868 / 1000000000000) (26459574426 / 1000000000000)
      | 1 => orderedInterval (2069705285 / 1000000000000) (2069707683 / 1000000000000)
      | 2 => orderedInterval (2840397252 / 1000000000000) (2840397264 / 1000000000000)
      | 3 => orderedInterval (-10752095978 / 1000000000000) (-10752095508 / 1000000000000)
      | 4 => orderedInterval (-6000910816 / 1000000000000) (-6000910339 / 1000000000000)
      | 5 => orderedInterval (-4487679028 / 1000000000000) (-4487678322 / 1000000000000)
      | 6 => orderedInterval (6843684618 / 1000000000000) (6843684654 / 1000000000000)
      | 7 => orderedInterval (2631967884 / 1000000000000) (2631967907 / 1000000000000)
      | _ => orderedInterval (-1868412320 / 1000000000000) (-1868412281 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (9694826443 / 1000000000000) (9694830312 / 1000000000000)
      | 1 => orderedInterval (3463508264 / 1000000000000) (3463509393 / 1000000000000)
      | 2 => orderedInterval (179632206 / 1000000000000) (179632226 / 1000000000000)
      | 3 => orderedInterval (107693086 / 1000000000000) (107694126 / 1000000000000)
      | 4 => orderedInterval (3060659119 / 1000000000000) (3060659953 / 1000000000000)
      | 5 => orderedInterval (2582853934 / 1000000000000) (2582855232 / 1000000000000)
      | 6 => orderedInterval (6306283036 / 1000000000000) (6306283069 / 1000000000000)
      | 7 => orderedInterval (-3530228384 / 1000000000000) (-3530228363 / 1000000000000)
      | _ => orderedInterval (8515060833 / 1000000000000) (8515060888 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (-27330269572 / 1000000000000) (-27330265208 / 1000000000000)
      | 1 => orderedInterval (-7763179795 / 1000000000000) (-7763179176 / 1000000000000)
      | 2 => orderedInterval (-8690554531 / 1000000000000) (-8690554497 / 1000000000000)
      | 3 => orderedInterval (47583454106 / 1000000000000) (47583456428 / 1000000000000)
      | 4 => orderedInterval (15906230122 / 1000000000000) (15906231629 / 1000000000000)
      | 5 => orderedInterval (8929550972 / 1000000000000) (8929553369 / 1000000000000)
      | 6 => orderedInterval (-7272444936 / 1000000000000) (-7272444904 / 1000000000000)
      | 7 => orderedInterval (-1681025353 / 1000000000000) (-1681025331 / 1000000000000)
      | _ => orderedInterval (8610919366 / 1000000000000) (8610919448 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-8345066360 / 1000000000000) (-8345061366 / 1000000000000)
      | 1 => orderedInterval (-6604412914 / 1000000000000) (-6604412545 / 1000000000000)
      | 2 => orderedInterval (-669467725 / 1000000000000) (-669467664 / 1000000000000)
      | 3 => orderedInterval (-14809393082 / 1000000000000) (-14809387903 / 1000000000000)
      | 4 => orderedInterval (-8769613579 / 1000000000000) (-8769610795 / 1000000000000)
      | 5 => orderedInterval (-7776863647 / 1000000000000) (-7776859229 / 1000000000000)
      | 6 => orderedInterval (-5572620734 / 1000000000000) (-5572620702 / 1000000000000)
      | 7 => orderedInterval (5455614464 / 1000000000000) (5455614487 / 1000000000000)
      | _ => orderedInterval (-2131040211 / 1000000000000) (-2131040086 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (28740512601 / 1000000000000) (28740518436 / 1000000000000)
      | 1 => orderedInterval (20831647725 / 1000000000000) (20831647976 / 1000000000000)
      | 2 => orderedInterval (28863815517 / 1000000000000) (28863815627 / 1000000000000)
      | 3 => orderedInterval (-231362374440 / 1000000000000) (-231362362836 / 1000000000000)
      | 4 => orderedInterval (-45604648798 / 1000000000000) (-45604643499 / 1000000000000)
      | 5 => orderedInterval (-19959900706 / 1000000000000) (-19959892524 / 1000000000000)
      | 6 => orderedInterval (8213874342 / 1000000000000) (8213874372 / 1000000000000)
      | 7 => orderedInterval (1530961892 / 1000000000000) (1530961917 / 1000000000000)
      | _ => orderedInterval (-30840540446 / 1000000000000) (-30840540246 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (17736227765 / 1000000000000) (17736235484 / 1000000000000)
    | 1 => orderedInterval (30380288537 / 1000000000000) (30380296836 / 1000000000000)
    | 2 => orderedInterval (28292680379 / 1000000000000) (28292691758 / 1000000000000)
    | 3 => orderedInterval (-49222863788 / 1000000000000) (-49222845803 / 1000000000000)
    | _ => orderedInterval (-239586652313 / 1000000000000) (-239586620777 / 1000000000000)

theorem compactCertificate264_stateChecks0 :
    compactCertificate264.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (277 / 2)) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 32 12 (408073892568577 / 4000000000000)) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 53 12 (131962712449441 / 800000000000)) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks1 :
    compactCertificate264.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 9 12 (119074944100739 / 4000000000000)) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 25 12 (319852049130983 / 4000000000000)) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 69 12 (868460533475211 / 4000000000000)) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks2 :
    compactCertificate264.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 51 12 (639704098262243 / 4000000000000)) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 87 12 (1096143875779439 / 4000000000000)) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (807414617697101 / 4000000000000)) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks3 :
    compactCertificate264.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 99 12 (1238781659534723 / 4000000000000)) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 57 12 (715210924599467 / 4000000000000)) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 101 12 (1269154336454503 / 4000000000000)) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks4 :
    compactCertificate264.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 94 12 (1185808611486307 / 4000000000000)) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 67 12 (846248978334931 / 4000000000000)) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 76 12 (959556147392949 / 4000000000000)) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks5 :
    compactCertificate264.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 64 12 (799977876938981 / 4000000000000)) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 56 12 (706804715170601 / 4000000000000)) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (204859555493499 / 800000000000)) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks6 :
    compactCertificate264.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (566652311662753 / 4000000000000)) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (480357440099033 / 4000000000000)) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 24 12 (300585382302899 / 4000000000000)) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks7 :
    compactCertificate264.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 13 12 (161655818304333 / 4000000000000)) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 35 12 (438926993231999 / 4000000000000)) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (599317284235423 / 4000000000000)) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_stateChecks8 :
    compactCertificate264.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (253414617697101 / 4000000000000)) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 82 12 (1030116351779821 / 4000000000000)) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (688069983211139 / 4000000000000)) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState009, besselGridState013, besselGridState020, besselGridState024, besselGridState025, besselGridState032, besselGridState035, besselGridState038, besselGridState044, besselGridState045, besselGridState048, besselGridState051, besselGridState053, besselGridState055, besselGridState056, besselGridState057, besselGridState064, besselGridState067, besselGridState069, besselGridState076, besselGridState082, besselGridState087, besselGridState094, besselGridState099, besselGridState101, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate264_states : ∀ j,
    BesselStateValid (compactCertificate264.point j) (compactCertificate264.state j) :=
  compactCertificate264.statesValid_of_checks3 compactCertificate264_stateChecks0
    compactCertificate264_stateChecks1 compactCertificate264_stateChecks2
    compactCertificate264_stateChecks3 compactCertificate264_stateChecks4
    compactCertificate264_stateChecks5 compactCertificate264_stateChecks6
    compactCertificate264_stateChecks7 compactCertificate264_stateChecks8

theorem compactCertificate264_chunkChecks0_0 :
    compactCertificate264.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (277 / 2) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (408073892568577 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (131962712449441 / 800000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000)))) (orderedInterval (26459570868 / 1000000000000) (26459574426 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (119074944100739 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (319852049130983 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (868460533475211 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000)))) (orderedInterval (2069705285 / 1000000000000) (2069707683 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (639704098262243 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (1096143875779439 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (807414617697101 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000)))) (orderedInterval (2840397252 / 1000000000000) (2840397264 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks0_1 :
    compactCertificate264.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1238781659534723 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (715210924599467 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1269154336454503 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000)))) (orderedInterval (-10752095978 / 1000000000000) (-10752095508 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1185808611486307 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (846248978334931 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000)))) (orderedInterval (-6000910816 / 1000000000000) (-6000910339 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (799977876938981 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (706804715170601 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (204859555493499 / 800000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000)))) (orderedInterval (-4487679028 / 1000000000000) (-4487678322 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks0_2 :
    compactCertificate264.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (566652311662753 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (480357440099033 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (300585382302899 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000)))) (orderedInterval (6843684618 / 1000000000000) (6843684654 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (161655818304333 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (438926993231999 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (599317284235423 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000)))) (orderedInterval (2631967884 / 1000000000000) (2631967907 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (253414617697101 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (1030116351779821 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (688069983211139 / 4000000000000) 0 (IntervalRat.scale (277 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000)))) (orderedInterval (-1868412320 / 1000000000000) (-1868412281 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks0 :
    compactCertificate264.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate264.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate264_chunkChecks0_0
    compactCertificate264_chunkChecks0_1 compactCertificate264_chunkChecks0_2

theorem compactCertificate264_chunkChecks1_0 :
    compactCertificate264.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (277 / 2) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (408073892568577 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (131962712449441 / 800000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000)))) (orderedInterval (9694826443 / 1000000000000) (9694830312 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (119074944100739 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (319852049130983 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (868460533475211 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000)))) (orderedInterval (3463508264 / 1000000000000) (3463509393 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (639704098262243 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (1096143875779439 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (807414617697101 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000)))) (orderedInterval (179632206 / 1000000000000) (179632226 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks1_1 :
    compactCertificate264.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1238781659534723 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (715210924599467 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1269154336454503 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000)))) (orderedInterval (107693086 / 1000000000000) (107694126 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1185808611486307 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (846248978334931 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000)))) (orderedInterval (3060659119 / 1000000000000) (3060659953 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (799977876938981 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (706804715170601 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (204859555493499 / 800000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000)))) (orderedInterval (2582853934 / 1000000000000) (2582855232 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks1_2 :
    compactCertificate264.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (566652311662753 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (480357440099033 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (300585382302899 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000)))) (orderedInterval (6306283036 / 1000000000000) (6306283069 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (161655818304333 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (438926993231999 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (599317284235423 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000)))) (orderedInterval (-3530228384 / 1000000000000) (-3530228363 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (253414617697101 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (1030116351779821 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (688069983211139 / 4000000000000) 1 (IntervalRat.scale (277 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000)))) (orderedInterval (8515060833 / 1000000000000) (8515060888 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks1 :
    compactCertificate264.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate264.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate264_chunkChecks1_0
    compactCertificate264_chunkChecks1_1 compactCertificate264_chunkChecks1_2

theorem compactCertificate264_chunkChecks2_0 :
    compactCertificate264.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (277 / 2) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (408073892568577 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (131962712449441 / 800000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000)))) (orderedInterval (-27330269572 / 1000000000000) (-27330265208 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (119074944100739 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (319852049130983 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (868460533475211 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000)))) (orderedInterval (-7763179795 / 1000000000000) (-7763179176 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (639704098262243 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (1096143875779439 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (807414617697101 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000)))) (orderedInterval (-8690554531 / 1000000000000) (-8690554497 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks2_1 :
    compactCertificate264.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1238781659534723 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (715210924599467 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1269154336454503 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000)))) (orderedInterval (47583454106 / 1000000000000) (47583456428 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1185808611486307 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (846248978334931 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000)))) (orderedInterval (15906230122 / 1000000000000) (15906231629 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (799977876938981 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (706804715170601 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (204859555493499 / 800000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000)))) (orderedInterval (8929550972 / 1000000000000) (8929553369 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks2_2 :
    compactCertificate264.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (566652311662753 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (480357440099033 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (300585382302899 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000)))) (orderedInterval (-7272444936 / 1000000000000) (-7272444904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (161655818304333 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (438926993231999 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (599317284235423 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000)))) (orderedInterval (-1681025353 / 1000000000000) (-1681025331 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (253414617697101 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (1030116351779821 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (688069983211139 / 4000000000000) 2 (IntervalRat.scale (277 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000)))) (orderedInterval (8610919366 / 1000000000000) (8610919448 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks2 :
    compactCertificate264.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate264.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate264_chunkChecks2_0
    compactCertificate264_chunkChecks2_1 compactCertificate264_chunkChecks2_2

theorem compactCertificate264_chunkChecks3_0 :
    compactCertificate264.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (277 / 2) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (408073892568577 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (131962712449441 / 800000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000)))) (orderedInterval (-8345066360 / 1000000000000) (-8345061366 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (119074944100739 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (319852049130983 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (868460533475211 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000)))) (orderedInterval (-6604412914 / 1000000000000) (-6604412545 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (639704098262243 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (1096143875779439 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (807414617697101 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000)))) (orderedInterval (-669467725 / 1000000000000) (-669467664 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks3_1 :
    compactCertificate264.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1238781659534723 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (715210924599467 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1269154336454503 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000)))) (orderedInterval (-14809393082 / 1000000000000) (-14809387903 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1185808611486307 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (846248978334931 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000)))) (orderedInterval (-8769613579 / 1000000000000) (-8769610795 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (799977876938981 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (706804715170601 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (204859555493499 / 800000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000)))) (orderedInterval (-7776863647 / 1000000000000) (-7776859229 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks3_2 :
    compactCertificate264.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (566652311662753 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (480357440099033 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (300585382302899 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000)))) (orderedInterval (-5572620734 / 1000000000000) (-5572620702 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (161655818304333 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (438926993231999 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (599317284235423 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000)))) (orderedInterval (5455614464 / 1000000000000) (5455614487 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (253414617697101 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (1030116351779821 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (688069983211139 / 4000000000000) 3 (IntervalRat.scale (277 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000)))) (orderedInterval (-2131040211 / 1000000000000) (-2131040086 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks3 :
    compactCertificate264.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate264.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate264_chunkChecks3_0
    compactCertificate264_chunkChecks3_1 compactCertificate264_chunkChecks3_2

theorem compactCertificate264_chunkChecks4_0 :
    compactCertificate264.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (277 / 2) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (58957629947 / 1000000000000) (58957629948 / 1000000000000), orderedInterval (33261256423 / 1000000000000) (33261256424 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (408073892568577 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (60373392285 / 1000000000000) (60373479166 / 1000000000000), orderedInterval (-51239775298 / 1000000000000) (-51239688417 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (131962712449441 / 800000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (43084837820 / 1000000000000) (43084884469 / 1000000000000), orderedInterval (-44886480226 / 1000000000000) (-44886433576 / 1000000000000)))) (orderedInterval (28740512601 / 1000000000000) (28740518436 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (119074944100739 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (-111386893513 / 1000000000000) (-111386826102 / 1000000000000), orderedInterval (96622612995 / 1000000000000) (96622680405 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (319852049130983 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (-71767916223 / 1000000000000) (-71767871039 / 1000000000000), orderedInterval (53465237322 / 1000000000000) (53465282506 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (868460533475211 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-48974915089 / 1000000000000) (-48974915088 / 1000000000000), orderedInterval (-22987619699 / 1000000000000) (-22987619698 / 1000000000000)))) (orderedInterval (20831647725 / 1000000000000) (20831647976 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (639704098262243 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-29660552848 / 1000000000000) (-29660552847 / 1000000000000), orderedInterval (-55593681028 / 1000000000000) (-55593681027 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (1096143875779439 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (-48085906735 / 1000000000000) (-48085906692 / 1000000000000), orderedInterval (-3208717405 / 1000000000000) (-3208717361 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (807414617697101 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (56158307932 / 1000000000000) (56158308007 / 1000000000000), orderedInterval (-459615628 / 1000000000000) (-459615553 / 1000000000000)))) (orderedInterval (28863815517 / 1000000000000) (28863815627 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks4_1 :
    compactCertificate264.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1238781659534723 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (23203922915 / 1000000000000) (23203925244 / 1000000000000), orderedInterval (-38988857283 / 1000000000000) (-38988854954 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (715210924599467 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (-29474881703 / 1000000000000) (-29474881702 / 1000000000000), orderedInterval (-51799148245 / 1000000000000) (-51799148244 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1269154336454503 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (-31269842918 / 1000000000000) (-31269842917 / 1000000000000), orderedInterval (-32023058467 / 1000000000000) (-32023058466 / 1000000000000)))) (orderedInterval (-231362374440 / 1000000000000) (-231362362836 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1185808611486307 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (43424966006 / 1000000000000) (43424974998 / 1000000000000), orderedInterval (-16251370807 / 1000000000000) (-16251361815 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (846248978334931 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-52572059723 / 1000000000000) (-52572056891 / 1000000000000), orderedInterval (15786576332 / 1000000000000) (15786579164 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (959556147392949 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (48530311715 / 1000000000000) (48530317500 / 1000000000000), orderedInterval (-17381589437 / 1000000000000) (-17381583652 / 1000000000000)))) (orderedInterval (-45604648798 / 1000000000000) (-45604643499 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (799977876938981 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (-15737552191 / 1000000000000) (-15737551986 / 1000000000000), orderedInterval (54219827661 / 1000000000000) (54219827865 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (706804715170601 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (60017265188 / 1000000000000) (60017265235 / 1000000000000), orderedInterval (677399831 / 1000000000000) (677399878 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (204859555493499 / 800000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-34032182917 / 1000000000000) (-34032156076 / 1000000000000), orderedInterval (36506588917 / 1000000000000) (36506615757 / 1000000000000)))) (orderedInterval (-19959900706 / 1000000000000) (-19959892524 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks4_2 :
    compactCertificate264.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (566652311662753 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (-58993967353 / 1000000000000) (-58993967352 / 1000000000000), orderedInterval (-31628820278 / 1000000000000) (-31628820277 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (480357440099033 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (72590033536 / 1000000000000) (72590033548 / 1000000000000), orderedInterval (5342128989 / 1000000000000) (5342129001 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (300585382302899 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (46677167484 / 1000000000000) (46677167485 / 1000000000000), orderedInterval (79018286088 / 1000000000000) (79018286089 / 1000000000000)))) (orderedInterval (8213874342 / 1000000000000) (8213874372 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (161655818304333 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-43689453241 / 1000000000000) (-43689453240 / 1000000000000), orderedInterval (-117122714296 / 1000000000000) (-117122714295 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (438926993231999 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (-40476374984 / 1000000000000) (-40476374983 / 1000000000000), orderedInterval (-64339130852 / 1000000000000) (-64339130851 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (599317284235423 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-11834139769 / 1000000000000) (-11834139697 / 1000000000000), orderedInterval (64140519492 / 1000000000000) (64140519565 / 1000000000000)))) (orderedInterval (1530961892 / 1000000000000) (1530961917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (253414617697101 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (96727329442 / 1000000000000) (96727329443 / 1000000000000), orderedInterval (25546747845 / 1000000000000) (25546747846 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (1030116351779821 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (32159390403 / 1000000000000) (32159390404 / 1000000000000), orderedInterval (37855960008 / 1000000000000) (37855960009 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (688069983211139 / 4000000000000) 4 (IntervalRat.scale (277 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-886416010 / 1000000000000) (-886416007 / 1000000000000), orderedInterval (-60826127120 / 1000000000000) (-60826127117 / 1000000000000)))) (orderedInterval (-30840540446 / 1000000000000) (-30840540246 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate264_chunkChecks4 :
    compactCertificate264.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate264.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate264_chunkChecks4_0
    compactCertificate264_chunkChecks4_1 compactCertificate264_chunkChecks4_2

theorem compactCertificate264_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate264.chunkCheck r b = true :=
  compactCertificate264.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate264_chunkChecks0
    · exact compactCertificate264_chunkChecks1
    · exact compactCertificate264_chunkChecks2
    · exact compactCertificate264_chunkChecks3
    · exact compactCertificate264_chunkChecks4)

theorem compactCertificate264_coefficient0 :
    compactCertificate264.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate264, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate264_coefficient1 :
    compactCertificate264.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate264, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate264_coefficient2 :
    compactCertificate264.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate264, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate264_coefficient3 :
    compactCertificate264.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate264, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate264_coefficient4 :
    compactCertificate264.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate264, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate264_coefficients : ∀ r : Fin 5,
    compactCertificate264.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate264_coefficient0
  · exact compactCertificate264_coefficient1
  · exact compactCertificate264_coefficient2
  · exact compactCertificate264_coefficient3
  · exact compactCertificate264_coefficient4

theorem compactCertificate264_lower : (1 : ℚ) ≤ compactCertificate264.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate264, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate264_proves {t : ℝ} (ht : t ∈ compactCertificate264.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate264.proves compactCertificate264_states compactCertificate264_chunks
    compactCertificate264_coefficients compactCertificate264_lower ht

end Erdos232
