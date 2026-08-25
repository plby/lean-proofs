/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CompactBase

open LeanCert.Core
namespace Erdos232

def compactCertificate243 : CompactCertificate where
  left := 118
  right := 119
  center := 237 / 2
  grid := fun i =>
    match i.val with
    | 0 => 38
    | 1 => 28
    | 2 => 45
    | 3 => 8
    | 4 => 22
    | 5 => 59
    | 6 => 44
    | 7 => 75
    | 8 => 55
    | 9 => 84
    | 10 => 49
    | 11 => 86
    | 12 => 81
    | 13 => 58
    | 14 => 65
    | 15 => 54
    | 16 => 48
    | 17 => 70
    | 18 => 39
    | 19 => 33
    | 20 => 20
    | 21 => 11
    | 22 => 30
    | 23 => 41
    | 24 => 17
    | 25 => 70
    | _ => 47
  point := fun i =>
    match i.val with
    | 0 => 237 / 2
    | 1 => 349146254652537 / 4000000000000
    | 2 => 112906725092121 / 800000000000
    | 3 => 101880006324459 / 4000000000000
    | 4 => 273664027595823 / 4000000000000
    | 5 => 743051070157491 / 4000000000000
    | 6 => 547328055191883 / 4000000000000
    | 7 => 937855951479159 / 4000000000000
    | 8 => 690820449076581 / 4000000000000
    | 9 => 1059896221334763 / 4000000000000
    | 10 => 611931368700627 / 4000000000000
    | 11 => 1085882952128943 / 4000000000000
    | 12 => 1014572710910667 / 4000000000000
    | 13 => 724046959802811 / 4000000000000
    | 14 => 820992082787469 / 4000000000000
    | 15 => 684457605900861 / 4000000000000
    | 16 => 604739052330081 / 4000000000000
    | 17 => 175276948202019 / 800000000000
    | 18 => 484825263047193 / 4000000000000
    | 19 => 410991744777873 / 4000000000000
    | 20 => 257179550923419 / 4000000000000
    | 21 => 138312017827173 / 4000000000000
    | 22 => 375544033920519 / 4000000000000
    | 23 => 512773272071463 / 4000000000000
    | 24 => 216820449076581 / 4000000000000
    | 25 => 881363087984901 / 4000000000000
    | _ => 588709696826859 / 4000000000000
  state := fun i =>
    match i.val with
    | 0 => (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
    | 1 => (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
    | 2 => (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000))
    | 3 => (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
    | 4 => (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
    | 5 => (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000))
    | 6 => (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
    | 7 => (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
    | 8 => (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000))
    | 9 => (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
    | 10 => (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
    | 11 => (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000))
    | 12 => (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
    | 13 => (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
    | 14 => (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))
    | 15 => (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
    | 16 => (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
    | 17 => (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000))
    | 18 => (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
    | 19 => (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
    | 20 => (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000))
    | 21 => (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
    | 22 => (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
    | 23 => (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000))
    | 24 => (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
    | 25 => (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
    | _ => (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000))
  chunkTarget := fun r b =>
    match r.val with
    | 0 =>
      match b.val with
      | 0 => orderedInterval (-4753057986 / 1000000000000) (-4753057967 / 1000000000000)
      | 1 => orderedInterval (2624311388 / 1000000000000) (2624311404 / 1000000000000)
      | 2 => orderedInterval (-1529820685 / 1000000000000) (-1529820661 / 1000000000000)
      | 3 => orderedInterval (-1508302680 / 1000000000000) (-1508297111 / 1000000000000)
      | 4 => orderedInterval (-2030360665 / 1000000000000) (-2030360524 / 1000000000000)
      | 5 => orderedInterval (-2918748239 / 1000000000000) (-2918747080 / 1000000000000)
      | 6 => orderedInterval (-3968355283 / 1000000000000) (-3968352332 / 1000000000000)
      | 7 => orderedInterval (1962230516 / 1000000000000) (1962230531 / 1000000000000)
      | _ => orderedInterval (-1022833448 / 1000000000000) (-1022833414 / 1000000000000)
    | 1 =>
      match b.val with
      | 0 => orderedInterval (25509951193 / 1000000000000) (25509951213 / 1000000000000)
      | 1 => orderedInterval (4257059374 / 1000000000000) (4257059391 / 1000000000000)
      | 2 => orderedInterval (1337976261 / 1000000000000) (1337976305 / 1000000000000)
      | 3 => orderedInterval (-8093468385 / 1000000000000) (-8093455682 / 1000000000000)
      | 4 => orderedInterval (9654088658 / 1000000000000) (9654088876 / 1000000000000)
      | 5 => orderedInterval (85743133 / 1000000000000) (85744807 / 1000000000000)
      | 6 => orderedInterval (12960350058 / 1000000000000) (12960352139 / 1000000000000)
      | 7 => orderedInterval (4905747836 / 1000000000000) (4905747850 / 1000000000000)
      | _ => orderedInterval (11775828695 / 1000000000000) (11775828742 / 1000000000000)
    | 2 =>
      match b.val with
      | 0 => orderedInterval (5433054848 / 1000000000000) (5433054870 / 1000000000000)
      | 1 => orderedInterval (-9571559744 / 1000000000000) (-9571559720 / 1000000000000)
      | 2 => orderedInterval (4280565499 / 1000000000000) (4280565582 / 1000000000000)
      | 3 => orderedInterval (8822005636 / 1000000000000) (8822034736 / 1000000000000)
      | 4 => orderedInterval (4557574246 / 1000000000000) (4557574586 / 1000000000000)
      | 5 => orderedInterval (4575412571 / 1000000000000) (4575415002 / 1000000000000)
      | 6 => orderedInterval (5759028594 / 1000000000000) (5759030230 / 1000000000000)
      | 7 => orderedInterval (-798658570 / 1000000000000) (-798658557 / 1000000000000)
      | _ => orderedInterval (8458497479 / 1000000000000) (8458497548 / 1000000000000)
    | 3 =>
      match b.val with
      | 0 => orderedInterval (-23612670565 / 1000000000000) (-23612670542 / 1000000000000)
      | 1 => orderedInterval (-6452584256 / 1000000000000) (-6452584221 / 1000000000000)
      | 2 => orderedInterval (-8190480032 / 1000000000000) (-8190479872 / 1000000000000)
      | 3 => orderedInterval (22021359142 / 1000000000000) (22021425582 / 1000000000000)
      | 4 => orderedInterval (-26829020651 / 1000000000000) (-26829020120 / 1000000000000)
      | 5 => orderedInterval (-4451614234 / 1000000000000) (-4451610721 / 1000000000000)
      | 6 => orderedInterval (-13314469308 / 1000000000000) (-13314467917 / 1000000000000)
      | 7 => orderedInterval (-5921622812 / 1000000000000) (-5921622798 / 1000000000000)
      | _ => orderedInterval (-12821321380 / 1000000000000) (-12821321274 / 1000000000000)
    | _ =>
      match b.val with
      | 0 => orderedInterval (-6485640930 / 1000000000000) (-6485640904 / 1000000000000)
      | 1 => orderedInterval (23502560469 / 1000000000000) (23502560522 / 1000000000000)
      | 2 => orderedInterval (-13058507708 / 1000000000000) (-13058507395 / 1000000000000)
      | 3 => orderedInterval (-40813410384 / 1000000000000) (-40813258105 / 1000000000000)
      | 4 => orderedInterval (-10207471642 / 1000000000000) (-10207470803 / 1000000000000)
      | 5 => orderedInterval (-7109206640 / 1000000000000) (-7109201533 / 1000000000000)
      | 6 => orderedInterval (-6335786090 / 1000000000000) (-6335784809 / 1000000000000)
      | 7 => orderedInterval (1080450356 / 1000000000000) (1080450370 / 1000000000000)
      | _ => orderedInterval (-39946461289 / 1000000000000) (-39946461119 / 1000000000000)
  coefficientTarget := fun i =>
    match i.val with
    | 0 => orderedInterval (-13144937082 / 1000000000000) (-13144927154 / 1000000000000)
    | 1 => orderedInterval (62393276823 / 1000000000000) (62393293641 / 1000000000000)
    | 2 => orderedInterval (31515920559 / 1000000000000) (31515954277 / 1000000000000)
    | 3 => orderedInterval (-79572424096 / 1000000000000) (-79572351883 / 1000000000000)
    | _ => orderedInterval (-99373473858 / 1000000000000) (-99373313776 / 1000000000000)

theorem compactCertificate243_stateChecks0 :
    compactCertificate243.stateChecks 0 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 38 12 (237 / 2)) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 28 12 (349146254652537 / 4000000000000)) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 45 12 (112906725092121 / 800000000000)) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks1 :
    compactCertificate243.stateChecks 3 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 8 12 (101880006324459 / 4000000000000)) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 22 12 (273664027595823 / 4000000000000)) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 59 12 (743051070157491 / 4000000000000)) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks2 :
    compactCertificate243.stateChecks 6 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 44 12 (547328055191883 / 4000000000000)) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 75 12 (937855951479159 / 4000000000000)) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 55 12 (690820449076581 / 4000000000000)) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks3 :
    compactCertificate243.stateChecks 9 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 84 12 (1059896221334763 / 4000000000000)) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 49 12 (611931368700627 / 4000000000000)) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 86 12 (1085882952128943 / 4000000000000)) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks4 :
    compactCertificate243.stateChecks 12 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 81 12 (1014572710910667 / 4000000000000)) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 58 12 (724046959802811 / 4000000000000)) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 65 12 (820992082787469 / 4000000000000)) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks5 :
    compactCertificate243.stateChecks 15 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 54 12 (684457605900861 / 4000000000000)) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 48 12 (604739052330081 / 4000000000000)) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (175276948202019 / 800000000000)) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks6 :
    compactCertificate243.stateChecks 18 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 39 12 (484825263047193 / 4000000000000)) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 33 12 (410991744777873 / 4000000000000)) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 20 12 (257179550923419 / 4000000000000)) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks7 :
    compactCertificate243.stateChecks 21 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 11 12 (138312017827173 / 4000000000000)) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 30 12 (375544033920519 / 4000000000000)) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 41 12 (512773272071463 / 4000000000000)) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_stateChecks8 :
    compactCertificate243.stateChecks 24 3 = true := by
  change (((true &&
      besselStateSubset (besselStateAtRationalPoint 17 12 (216820449076581 / 4000000000000)) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 70 12 (881363087984901 / 4000000000000)) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))) &&
      besselStateSubset (besselStateAtRationalPoint 47 12 (588709696826859 / 4000000000000)) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000))) = true
  norm_num [besselStateAtRationalPoint, besselIntervalStepZero,
    besselIntervalStep, besselTransitionFast, besselTransitionLoop,
    besselCoefficientStateStep, besselCoefficientState, besselZeroTransition,
    besselInitial, besselGridStateAt, besselGridStateBlock00, besselGridStateBlock01,
    besselGridStateBlock02, besselGridStateBlock03, besselGridStateBlock04,
    besselGridStateBlock05, besselGridStateBlock06, besselGridStateBlock07,
    besselGridStateBlock08, besselGridStateBlock09, besselGridStateBlock10,
    besselGridStateBlock11, besselGridStateBlock12, besselGridStateBlock13,
    besselGridStateBlock14, besselGridState008, besselGridState011, besselGridState017, besselGridState020, besselGridState022, besselGridState028, besselGridState030, besselGridState033, besselGridState038, besselGridState039, besselGridState041, besselGridState044, besselGridState045, besselGridState047, besselGridState048, besselGridState049, besselGridState054, besselGridState055, besselGridState058, besselGridState059, besselGridState065, besselGridState070, besselGridState075, besselGridState081, besselGridState084, besselGridState086, besselStateSubset, linearInterval, widenInterval,
    rationalErrorInterval, rationalIntervalSubset, orderedInterval, Finset.sum_range_succ,
    IntervalRat.add, IntervalRat.mul, IntervalRat.scale, IntervalRat.singleton]

theorem compactCertificate243_states : ∀ j,
    BesselStateValid (compactCertificate243.point j) (compactCertificate243.state j) :=
  compactCertificate243.statesValid_of_checks3 compactCertificate243_stateChecks0
    compactCertificate243_stateChecks1 compactCertificate243_stateChecks2
    compactCertificate243_stateChecks3 compactCertificate243_stateChecks4
    compactCertificate243_stateChecks5 compactCertificate243_stateChecks6
    compactCertificate243_stateChecks7 compactCertificate243_stateChecks8

theorem compactCertificate243_chunkChecks0_0 :
    compactCertificate243.chunkChecks (0 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 0) <| besselDerivativeNearFromState (237 / 2) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 0) <| besselDerivativeNearFromState (349146254652537 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 0) <| besselDerivativeNearFromState (112906725092121 / 800000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000)))) (orderedInterval (-4753057986 / 1000000000000) (-4753057967 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 0) <| besselDerivativeNearFromState (101880006324459 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 0) <| besselDerivativeNearFromState (273664027595823 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 0) <| besselDerivativeNearFromState (743051070157491 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000)))) (orderedInterval (2624311388 / 1000000000000) (2624311404 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 0) <| besselDerivativeNearFromState (547328055191883 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 0) <| besselDerivativeNearFromState (937855951479159 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 0) <| besselDerivativeNearFromState (690820449076581 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000)))) (orderedInterval (-1529820685 / 1000000000000) (-1529820661 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks0_1 :
    compactCertificate243.chunkChecks (0 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 0) <| besselDerivativeNearFromState (1059896221334763 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 0) <| besselDerivativeNearFromState (611931368700627 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 0) <| besselDerivativeNearFromState (1085882952128943 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000)))) (orderedInterval (-1508302680 / 1000000000000) (-1508297111 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 0) <| besselDerivativeNearFromState (1014572710910667 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 0) <| besselDerivativeNearFromState (724046959802811 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 0) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000)))) (orderedInterval (-2030360665 / 1000000000000) (-2030360524 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 0) <| besselDerivativeNearFromState (684457605900861 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 0) <| besselDerivativeNearFromState (604739052330081 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 0) <| besselDerivativeNearFromState (175276948202019 / 800000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000)))) (orderedInterval (-2918748239 / 1000000000000) (-2918747080 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks0_2 :
    compactCertificate243.chunkChecks (0 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 0) <| besselDerivativeNearFromState (484825263047193 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 0) <| besselDerivativeNearFromState (410991744777873 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 0) <| besselDerivativeNearFromState (257179550923419 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000)))) (orderedInterval (-3968355283 / 1000000000000) (-3968352332 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 0) <| besselDerivativeNearFromState (138312017827173 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 0) <| besselDerivativeNearFromState (375544033920519 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 0) <| besselDerivativeNearFromState (512773272071463 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000)))) (orderedInterval (1962230516 / 1000000000000) (1962230531 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 0) <| besselDerivativeNearFromState (216820449076581 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 0) <| besselDerivativeNearFromState (881363087984901 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 0) <| besselDerivativeNearFromState (588709696826859 / 4000000000000) 0 (IntervalRat.scale (237 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000)))) (orderedInterval (-1022833448 / 1000000000000) (-1022833414 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks0 :
    compactCertificate243.chunkChecks (0 : Fin 5) 0 9 = true :=
  compactCertificate243.chunkChecks_nine_of_three (0 : Fin 5) compactCertificate243_chunkChecks0_0
    compactCertificate243_chunkChecks0_1 compactCertificate243_chunkChecks0_2

theorem compactCertificate243_chunkChecks1_0 :
    compactCertificate243.chunkChecks (1 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 1) <| besselDerivativeNearFromState (237 / 2) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 1) <| besselDerivativeNearFromState (349146254652537 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 1) <| besselDerivativeNearFromState (112906725092121 / 800000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000)))) (orderedInterval (25509951193 / 1000000000000) (25509951213 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 1) <| besselDerivativeNearFromState (101880006324459 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 1) <| besselDerivativeNearFromState (273664027595823 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 1) <| besselDerivativeNearFromState (743051070157491 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000)))) (orderedInterval (4257059374 / 1000000000000) (4257059391 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 1) <| besselDerivativeNearFromState (547328055191883 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 1) <| besselDerivativeNearFromState (937855951479159 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 1) <| besselDerivativeNearFromState (690820449076581 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000)))) (orderedInterval (1337976261 / 1000000000000) (1337976305 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks1_1 :
    compactCertificate243.chunkChecks (1 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 1) <| besselDerivativeNearFromState (1059896221334763 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 1) <| besselDerivativeNearFromState (611931368700627 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 1) <| besselDerivativeNearFromState (1085882952128943 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000)))) (orderedInterval (-8093468385 / 1000000000000) (-8093455682 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 1) <| besselDerivativeNearFromState (1014572710910667 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 1) <| besselDerivativeNearFromState (724046959802811 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 1) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000)))) (orderedInterval (9654088658 / 1000000000000) (9654088876 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 1) <| besselDerivativeNearFromState (684457605900861 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 1) <| besselDerivativeNearFromState (604739052330081 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 1) <| besselDerivativeNearFromState (175276948202019 / 800000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000)))) (orderedInterval (85743133 / 1000000000000) (85744807 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks1_2 :
    compactCertificate243.chunkChecks (1 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 1) <| besselDerivativeNearFromState (484825263047193 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 1) <| besselDerivativeNearFromState (410991744777873 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 1) <| besselDerivativeNearFromState (257179550923419 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000)))) (orderedInterval (12960350058 / 1000000000000) (12960352139 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 1) <| besselDerivativeNearFromState (138312017827173 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 1) <| besselDerivativeNearFromState (375544033920519 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 1) <| besselDerivativeNearFromState (512773272071463 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000)))) (orderedInterval (4905747836 / 1000000000000) (4905747850 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 1) <| besselDerivativeNearFromState (216820449076581 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 1) <| besselDerivativeNearFromState (881363087984901 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 1) <| besselDerivativeNearFromState (588709696826859 / 4000000000000) 1 (IntervalRat.scale (237 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000)))) (orderedInterval (11775828695 / 1000000000000) (11775828742 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks1 :
    compactCertificate243.chunkChecks (1 : Fin 5) 0 9 = true :=
  compactCertificate243.chunkChecks_nine_of_three (1 : Fin 5) compactCertificate243_chunkChecks1_0
    compactCertificate243_chunkChecks1_1 compactCertificate243_chunkChecks1_2

theorem compactCertificate243_chunkChecks2_0 :
    compactCertificate243.chunkChecks (2 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 2) <| besselDerivativeNearFromState (237 / 2) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 2) <| besselDerivativeNearFromState (349146254652537 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 2) <| besselDerivativeNearFromState (112906725092121 / 800000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000)))) (orderedInterval (5433054848 / 1000000000000) (5433054870 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 2) <| besselDerivativeNearFromState (101880006324459 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 2) <| besselDerivativeNearFromState (273664027595823 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 2) <| besselDerivativeNearFromState (743051070157491 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000)))) (orderedInterval (-9571559744 / 1000000000000) (-9571559720 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 2) <| besselDerivativeNearFromState (547328055191883 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 2) <| besselDerivativeNearFromState (937855951479159 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 2) <| besselDerivativeNearFromState (690820449076581 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000)))) (orderedInterval (4280565499 / 1000000000000) (4280565582 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks2_1 :
    compactCertificate243.chunkChecks (2 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 2) <| besselDerivativeNearFromState (1059896221334763 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 2) <| besselDerivativeNearFromState (611931368700627 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 2) <| besselDerivativeNearFromState (1085882952128943 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000)))) (orderedInterval (8822005636 / 1000000000000) (8822034736 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 2) <| besselDerivativeNearFromState (1014572710910667 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 2) <| besselDerivativeNearFromState (724046959802811 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 2) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000)))) (orderedInterval (4557574246 / 1000000000000) (4557574586 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 2) <| besselDerivativeNearFromState (684457605900861 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 2) <| besselDerivativeNearFromState (604739052330081 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 2) <| besselDerivativeNearFromState (175276948202019 / 800000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000)))) (orderedInterval (4575412571 / 1000000000000) (4575415002 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks2_2 :
    compactCertificate243.chunkChecks (2 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 2) <| besselDerivativeNearFromState (484825263047193 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 2) <| besselDerivativeNearFromState (410991744777873 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 2) <| besselDerivativeNearFromState (257179550923419 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000)))) (orderedInterval (5759028594 / 1000000000000) (5759030230 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 2) <| besselDerivativeNearFromState (138312017827173 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 2) <| besselDerivativeNearFromState (375544033920519 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 2) <| besselDerivativeNearFromState (512773272071463 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000)))) (orderedInterval (-798658570 / 1000000000000) (-798658557 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 2) <| besselDerivativeNearFromState (216820449076581 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 2) <| besselDerivativeNearFromState (881363087984901 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 2) <| besselDerivativeNearFromState (588709696826859 / 4000000000000) 2 (IntervalRat.scale (237 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000)))) (orderedInterval (8458497479 / 1000000000000) (8458497548 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks2 :
    compactCertificate243.chunkChecks (2 : Fin 5) 0 9 = true :=
  compactCertificate243.chunkChecks_nine_of_three (2 : Fin 5) compactCertificate243_chunkChecks2_0
    compactCertificate243_chunkChecks2_1 compactCertificate243_chunkChecks2_2

theorem compactCertificate243_chunkChecks3_0 :
    compactCertificate243.chunkChecks (3 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 3) <| besselDerivativeNearFromState (237 / 2) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 3) <| besselDerivativeNearFromState (349146254652537 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 3) <| besselDerivativeNearFromState (112906725092121 / 800000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000)))) (orderedInterval (-23612670565 / 1000000000000) (-23612670542 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 3) <| besselDerivativeNearFromState (101880006324459 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 3) <| besselDerivativeNearFromState (273664027595823 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 3) <| besselDerivativeNearFromState (743051070157491 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000)))) (orderedInterval (-6452584256 / 1000000000000) (-6452584221 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 3) <| besselDerivativeNearFromState (547328055191883 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 3) <| besselDerivativeNearFromState (937855951479159 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 3) <| besselDerivativeNearFromState (690820449076581 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000)))) (orderedInterval (-8190480032 / 1000000000000) (-8190479872 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks3_1 :
    compactCertificate243.chunkChecks (3 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 3) <| besselDerivativeNearFromState (1059896221334763 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 3) <| besselDerivativeNearFromState (611931368700627 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 3) <| besselDerivativeNearFromState (1085882952128943 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000)))) (orderedInterval (22021359142 / 1000000000000) (22021425582 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 3) <| besselDerivativeNearFromState (1014572710910667 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 3) <| besselDerivativeNearFromState (724046959802811 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 3) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000)))) (orderedInterval (-26829020651 / 1000000000000) (-26829020120 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 3) <| besselDerivativeNearFromState (684457605900861 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 3) <| besselDerivativeNearFromState (604739052330081 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 3) <| besselDerivativeNearFromState (175276948202019 / 800000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000)))) (orderedInterval (-4451614234 / 1000000000000) (-4451610721 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks3_2 :
    compactCertificate243.chunkChecks (3 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 3) <| besselDerivativeNearFromState (484825263047193 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 3) <| besselDerivativeNearFromState (410991744777873 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 3) <| besselDerivativeNearFromState (257179550923419 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000)))) (orderedInterval (-13314469308 / 1000000000000) (-13314467917 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 3) <| besselDerivativeNearFromState (138312017827173 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 3) <| besselDerivativeNearFromState (375544033920519 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 3) <| besselDerivativeNearFromState (512773272071463 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000)))) (orderedInterval (-5921622812 / 1000000000000) (-5921622798 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 3) <| besselDerivativeNearFromState (216820449076581 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 3) <| besselDerivativeNearFromState (881363087984901 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 3) <| besselDerivativeNearFromState (588709696826859 / 4000000000000) 3 (IntervalRat.scale (237 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000)))) (orderedInterval (-12821321380 / 1000000000000) (-12821321274 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks3 :
    compactCertificate243.chunkChecks (3 : Fin 5) 0 9 = true :=
  compactCertificate243.chunkChecks_nine_of_three (3 : Fin 5) compactCertificate243_chunkChecks3_0
    compactCertificate243_chunkChecks3_1 compactCertificate243_chunkChecks3_2

theorem compactCertificate243_chunkChecks4_0 :
    compactCertificate243.chunkChecks (4 : Fin 5) 0 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (0 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (0 : Fin 27)) 4) <| besselDerivativeNearFromState (237 / 2) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (0 : Fin 27))) (orderedInterval (-7038540669 / 1000000000000) (-7038540643 / 1000000000000), orderedInterval (72987388662 / 1000000000000) (72987388687 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (1 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (1 : Fin 27)) 4) <| besselDerivativeNearFromState (349146254652537 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (1 : Fin 27))) (orderedInterval (9030087545 / 1000000000000) (9030087546 / 1000000000000), orderedInterval (84871886108 / 1000000000000) (84871886109 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (2 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (2 : Fin 27)) 4) <| besselDerivativeNearFromState (112906725092121 / 800000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (2 : Fin 27))) (orderedInterval (-34889740662 / 1000000000000) (-34889740661 / 1000000000000), orderedInterval (-57265288974 / 1000000000000) (-57265288973 / 1000000000000)))) (orderedInterval (-6485640930 / 1000000000000) (-6485640904 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (3 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (3 : Fin 27)) 4) <| besselDerivativeNearFromState (101880006324459 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (3 : Fin 27))) (orderedInterval (142135141450 / 1000000000000) (142135141451 / 1000000000000), orderedInterval (66417211590 / 1000000000000) (66417211591 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (4 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (4 : Fin 27)) 4) <| besselDerivativeNearFromState (273664027595823 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (4 : Fin 27))) (orderedInterval (8145154517 / 1000000000000) (8145154519 / 1000000000000), orderedInterval (96060351472 / 1000000000000) (96060351474 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (5 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (5 : Fin 27)) 4) <| besselDerivativeNearFromState (743051070157491 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (5 : Fin 27))) (orderedInterval (-54424006644 / 1000000000000) (-54424006643 / 1000000000000), orderedInterval (-21419143728 / 1000000000000) (-21419143727 / 1000000000000)))) (orderedInterval (23502560469 / 1000000000000) (23502560522 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (6 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (6 : Fin 27)) 4) <| besselDerivativeNearFromState (547328055191883 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (6 : Fin 27))) (orderedInterval (-39274803065 / 1000000000000) (-39274790232 / 1000000000000), orderedInterval (55911465526 / 1000000000000) (55911478358 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (7 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (7 : Fin 27)) 4) <| besselDerivativeNearFromState (937855951479159 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (7 : Fin 27))) (orderedInterval (18871886981 / 1000000000000) (18871887491 / 1000000000000), orderedInterval (-48610501876 / 1000000000000) (-48610501367 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (8 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (8 : Fin 27)) 4) <| besselDerivativeNearFromState (690820449076581 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (8 : Fin 27))) (orderedInterval (-39214461499 / 1000000000000) (-39214461498 / 1000000000000), orderedInterval (-46237251984 / 1000000000000) (-46237251983 / 1000000000000)))) (orderedInterval (-13058507708 / 1000000000000) (-13058507395 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks4_1 :
    compactCertificate243.chunkChecks (4 : Fin 5) 3 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (9 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (9 : Fin 27)) 4) <| besselDerivativeNearFromState (1059896221334763 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (9 : Fin 27))) (orderedInterval (46907132067 / 1000000000000) (46907136066 / 1000000000000), orderedInterval (-14311425272 / 1000000000000) (-14311421273 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (10 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (10 : Fin 27)) 4) <| besselDerivativeNearFromState (611931368700627 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (10 : Fin 27))) (orderedInterval (10952924849 / 1000000000000) (10952924908 / 1000000000000), orderedInterval (-63608076026 / 1000000000000) (-63608075966 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (11 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (11 : Fin 27)) 4) <| besselDerivativeNearFromState (1085882952128943 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (11 : Fin 27))) (orderedInterval (42312755255 / 1000000000000) (42312789065 / 1000000000000), orderedInterval (-23630106073 / 1000000000000) (-23630072263 / 1000000000000)))) (orderedInterval (-40813410384 / 1000000000000) (-40813258105 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (12 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (12 : Fin 27)) 4) <| besselDerivativeNearFromState (1014572710910667 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (12 : Fin 27))) (orderedInterval (2049567548 / 1000000000000) (2049567552 / 1000000000000), orderedInterval (-50061079027 / 1000000000000) (-50061079023 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (13 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (13 : Fin 27)) 4) <| besselDerivativeNearFromState (724046959802811 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (13 : Fin 27))) (orderedInterval (-23961142224 / 1000000000000) (-23961141001 / 1000000000000), orderedInterval (54314511995 / 1000000000000) (54314513218 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (14 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (14 : Fin 27)) 4) <| besselDerivativeNearFromState (820992082787469 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (14 : Fin 27))) (orderedInterval (-53842616561 / 1000000000000) (-53842614627 / 1000000000000), orderedInterval (14367539638 / 1000000000000) (14367541571 / 1000000000000)))) (orderedInterval (-10207471642 / 1000000000000) (-10207470803 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (15 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (15 : Fin 27)) 4) <| besselDerivativeNearFromState (684457605900861 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (15 : Fin 27))) (orderedInterval (47341006939 / 1000000000000) (47341106268 / 1000000000000), orderedInterval (-38599456052 / 1000000000000) (-38599356723 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (16 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (16 : Fin 27)) 4) <| besselDerivativeNearFromState (604739052330081 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (16 : Fin 27))) (orderedInterval (59821325783 / 1000000000000) (59821325784 / 1000000000000), orderedInterval (24947049385 / 1000000000000) (24947049386 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (17 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (17 : Fin 27)) 4) <| besselDerivativeNearFromState (175276948202019 / 800000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (17 : Fin 27))) (orderedInterval (-1642358701 / 1000000000000) (-1642358697 / 1000000000000), orderedInterval (53882998528 / 1000000000000) (53882998532 / 1000000000000)))) (orderedInterval (-7109206640 / 1000000000000) (-7109201533 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks4_2 :
    compactCertificate243.chunkChecks (4 : Fin 5) 6 3 = true := by
  change (((true &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (18 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (18 : Fin 27)) 4) <| besselDerivativeNearFromState (484825263047193 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (18 : Fin 27))) (orderedInterval (36726892065 / 1000000000000) (36726898136 / 1000000000000), orderedInterval (-62629674861 / 1000000000000) (-62629668789 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (19 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (19 : Fin 27)) 4) <| besselDerivativeNearFromState (410991744777873 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (19 : Fin 27))) (orderedInterval (11018242592 / 1000000000000) (11018242647 / 1000000000000), orderedInterval (-77993376181 / 1000000000000) (-77993376126 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (20 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (20 : Fin 27)) 4) <| besselDerivativeNearFromState (257179550923419 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (20 : Fin 27))) (orderedInterval (77641197081 / 1000000000000) (77641256877 / 1000000000000), orderedInterval (-62839910216 / 1000000000000) (-62839850421 / 1000000000000)))) (orderedInterval (-6335786090 / 1000000000000) (-6335784809 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (21 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (21 : Fin 27)) 4) <| besselDerivativeNearFromState (138312017827173 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (21 : Fin 27))) (orderedInterval (-97545561025 / 1000000000000) (-97545561024 / 1000000000000), orderedInterval (-92907955297 / 1000000000000) (-92907955296 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (22 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (22 : Fin 27)) 4) <| besselDerivativeNearFromState (375544033920519 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (22 : Fin 27))) (orderedInterval (33749503084 / 1000000000000) (33749503085 / 1000000000000), orderedInterval (74932241798 / 1000000000000) (74932241799 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (23 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (23 : Fin 27)) 4) <| besselDerivativeNearFromState (512773272071463 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (23 : Fin 27))) (orderedInterval (-12091914261 / 1000000000000) (-12091914260 / 1000000000000), orderedInterval (-69378430120 / 1000000000000) (-69378430119 / 1000000000000)))) (orderedInterval (1080450356 / 1000000000000) (1080450370 / 1000000000000))) &&
      rationalIntervalSubset (intervalFinSumHull 3 (fun z => match z.val with
        | 0 => IntervalRat.scale (dualWeight (24 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (24 : Fin 27)) 4) <| besselDerivativeNearFromState (216820449076581 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (24 : Fin 27))) (orderedInterval (-108364621249 / 1000000000000) (-108364621222 / 1000000000000), orderedInterval (2119351134 / 1000000000000) (2119351161 / 1000000000000))
        | 1 => IntervalRat.scale (dualWeight (25 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (25 : Fin 27)) 4) <| besselDerivativeNearFromState (881363087984901 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (25 : Fin 27))) (orderedInterval (50368632312 / 1000000000000) (50368632313 / 1000000000000), orderedInterval (18653925215 / 1000000000000) (18653925216 / 1000000000000))
        | _ => IntervalRat.scale (dualWeight (26 : Fin 27)) <| IntervalRat.mul (intervalPow (dualDistanceInterval (26 : Fin 27)) 4) <| besselDerivativeNearFromState (588709696826859 / 4000000000000) 4 (IntervalRat.scale (237 / 2) (dualDistanceInterval (26 : Fin 27))) (orderedInterval (-19882690814 / 1000000000000) (-19882690813 / 1000000000000), orderedInterval (-62623960590 / 1000000000000) (-62623960589 / 1000000000000)))) (orderedInterval (-39946461289 / 1000000000000) (-39946461119 / 1000000000000))) = true
  norm_num [intervalFinSumHull, besselDerivativeNearFromState, besselCoefficients,
    besselCoefficientState, dualWeight, dualDistanceInterval, intervalPow, intervalSub,
    intervalMaxAbs, linearInterval, widenInterval, rationalErrorInterval,
    rationalIntervalSubset, orderedInterval, IntervalRat.add, IntervalRat.mul,
    IntervalRat.scale, IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4,
    Fin.sum_univ_succ]

theorem compactCertificate243_chunkChecks4 :
    compactCertificate243.chunkChecks (4 : Fin 5) 0 9 = true :=
  compactCertificate243.chunkChecks_nine_of_three (4 : Fin 5) compactCertificate243_chunkChecks4_0
    compactCertificate243_chunkChecks4_1 compactCertificate243_chunkChecks4_2

theorem compactCertificate243_chunks :
    ∀ r : Fin 5, ∀ b, compactCertificate243.chunkCheck r b = true :=
  compactCertificate243.chunkChecks_all (by
    intro r
    fin_cases r
    · exact compactCertificate243_chunkChecks0
    · exact compactCertificate243_chunkChecks1
    · exact compactCertificate243_chunkChecks2
    · exact compactCertificate243_chunkChecks3
    · exact compactCertificate243_chunkChecks4)

theorem compactCertificate243_coefficient0 :
    compactCertificate243.coefficientCheck (0 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate243, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate243_coefficient1 :
    compactCertificate243.coefficientCheck (1 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate243, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate243_coefficient2 :
    compactCertificate243.coefficientCheck (2 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate243, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate243_coefficient3 :
    compactCertificate243.coefficientCheck (3 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate243, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate243_coefficient4 :
    compactCertificate243.coefficientCheck (4 : Fin 5) = true := by
  norm_num [CompactCertificate.coefficientCheck, intervalFinSumHull,
    compactCertificate243, rationalIntervalSubset, orderedInterval, Fin.sum_univ_succ]

theorem compactCertificate243_coefficients : ∀ r : Fin 5,
    compactCertificate243.coefficientCheck r = true := by
  intro r
  fin_cases r
  · exact compactCertificate243_coefficient0
  · exact compactCertificate243_coefficient1
  · exact compactCertificate243_coefficient2
  · exact compactCertificate243_coefficient3
  · exact compactCertificate243_coefficient4

theorem compactCertificate243_lower : (1 : ℚ) ≤ compactCertificate243.output.lo := by
  norm_num [CompactCertificate.output, CompactCertificate.interval,
    CompactCertificate.coefficientTargetNat, compactCertificate243, dualConstant,
    intervalTaylorSum, intervalPow, intervalSub, intervalMaxAbs, widenInterval,
    rationalErrorInterval, orderedInterval, IntervalRat.add, IntervalRat.mul, IntervalRat.scale,
    IntervalRat.singleton, IntervalRat.min4, IntervalRat.max4]

theorem compactCertificate243_proves {t : ℝ} (ht : t ∈ compactCertificate243.interval) :
    1 ≤ (dualConstant : ℝ) + spectralSum dualWeight dualDistance t :=
  compactCertificate243.proves compactCertificate243_states compactCertificate243_chunks
    compactCertificate243_coefficients compactCertificate243_lower ht

end Erdos232
